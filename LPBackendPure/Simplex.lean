/-
  Pure-Lean two-phase primal simplex on `Rat`.

  This module implements a tableau-based primal simplex with
  Bland's anti-cycling rule. The whole computation runs on `Rat`
  — no Float relaxation, even for pivot selection — because the
  verifier consumes exact-rational certificates and any rounding
  here would be wasted at the boundary.

  "Revised simplex" in the issue title refers to the exact-Rat
  requirement, not specifically to the `B⁻¹`-maintaining
  data-structure variant of simplex. A dense tableau is mathematically
  identical (same pivot rule, same primal/dual, same ray) and
  considerably simpler to get correct; on toy LPs (the only use
  case for the zero-deps backend) the difference is negligible.

  Scope of the simplex core (rejected with `SolveError.bridge` otherwise):
  * Inequality form only: every row must be `(none, some hi)`.
  * Non-negative variables only: every column must be `(some 0, none)`.

  Rows whose `hi < 0` are handled by a phase 1 / phase 2 startup:
  each negative-rhs row is sign-flipped (so the rhs becomes `|hi|`)
  and an artificial variable is added in that row. Phase 1 minimises
  the sum of the artificials. If phase 1 reaches `0`, the artificial
  columns are excluded from phase 2's entering choices and we proceed
  to the standard min-form simplex. If phase 1's optimum is strictly
  positive, the LP is infeasible and we return `SolveStatus.infeasible`
  with a Farkas dual read directly off row 0 of the final tableau:
  `yᵢ = tab[0, n+i]`, `zL[j] = tab[0, j]`. The sign convention matches
  `LPVerify.checkInfeasible`'s `DualBundle` layout (`rowUpper = y ≥ 0`,
  `colLower = zL ≥ 0`).

  The public solver accepts every column-bound shape by first
  preprocessing columns into that core form: free variables are split,
  lower bounds are shifted, upper-only bounds are flipped, and boxed
  variables get an added upper-bound row.

  Likewise, every row-bound shape is accepted by row preprocessing:
  `(none, some hi)` stays as one upper row; `(some lo, none)` is
  sign-flipped to `-a · x ≤ -lo`; `(some lo, some hi)` (equality or
  proper range) splits into two upper rows `a · x ≤ hi` and
  `-a · x ≤ -lo`; `(none, none)` is dropped. The dual multipliers from
  the preprocessed problem are recombined into the original
  `(rowLower, rowUpper)` split by `translateDual`.

  Maximisation is handled by canonicalising to minimisation
  (`Soplex.canonicalize`) before solving — the resulting certificate
  is for the canonical (min) form, which matches the verifier's
  `IsOptimal` definition. The user-facing `Solution.objective` is
  restored to the caller's original sense by negation.

  Out-of-scope inputs use `SolveError.bridge` for now, since
  `ProblemError` has no "unsupported feature" variant. When LPCore
  grows one, we can switch to `SolveError.invalidProblem` without
  changing the user experience.
-/

import LPCore

namespace Soplex.Backend.Pure

open Soplex

namespace Simplex

/-! ## Scope check. -/

/-- Why a problem falls outside this backend's scope. -/
private inductive ScopeError where
  /-- Row `i` is not of the form `(none, some hi)`. -/
  | rowNotUpperOnly (i : Nat)
  /-- Column `j` is not of the form `(some 0, none)`. -/
  | colNotNonNegOnly (j : Nat)

private def ScopeError.toMsg : ScopeError → String
  | .rowNotUpperOnly i =>
      s!"pure-Lean backend: row {i} is outside scope " ++
      "(expected `none ≤ Ax ≤ some hi`); see " ++
      "kim-em/lp-backend-pure `LPBackendPure/Simplex.lean`"
  | .colNotNonNegOnly j =>
      s!"pure-Lean backend: column {j} is outside scope " ++
      "(expected `some 0 ≤ x ≤ none`)"

/-- Verify the (canonicalised) problem is in the supported scope. -/
private def checkScope {m n : Nat} (p : Problem m n) :
    Except ScopeError Unit := do
  for i in [:m] do
    match p.rowBounds.toArray[i]! with
    | (none, some _) => pure ()
    | _ => throw (.rowNotUpperOnly i)
  for j in [:n] do
    match p.colBounds.toArray[j]! with
    | (some lo, none) =>
        if lo ≠ 0 then throw (.colNotNonNegOnly j)
    | _ => throw (.colNotNonNegOnly j)

/-! ## Per-row setup. -/

/-- Per-row info computed up front. A row with `rhs ≥ 0` keeps its
    sign and uses its slack as the basic variable; a row with `rhs < 0`
    is multiplied through by `-1` (so the new rhs is `|rhs|`) and an
    artificial variable is added at column `artCol`, which becomes the
    basic variable for that row. -/
private structure RowInfo where
  /-- Artificial column index for this row, if added (only when
      `rhs < 0`). -/
  artCol : Option Nat
  /-- Row scaling: `-1` for sign-flipped rows, `+1` otherwise. -/
  sign   : Rat
  /-- Rhs after row scaling. Always `≥ 0`. -/
  rhs    : Rat
  deriving Inhabited

/-- Walk the rows once, decide which need an artificial, and assign
    column indices. Artificial columns occupy
    `n + m .. n + m + numArt - 1` in the order rows are visited. -/
private def computeRowInfos {m n : Nat} (p : Problem m n) :
    Array RowInfo × Nat := Id.run do
  let mut infos : Array RowInfo := Array.mkEmpty m
  let mut numArt := 0
  for i in [:m] do
    let hi := (p.rowBounds.toArray[i]!).2.getD 0
    if hi < 0 then
      infos := infos.push
        { artCol := some (n + m + numArt), sign := -1, rhs := -hi }
      numArt := numArt + 1
    else
      infos := infos.push
        { artCol := none, sign := 1, rhs := hi }
  pure (infos, numArt)

/-! ## Tableau state. -/

/-- Dense simplex-tableau state.

    Columns:
    * `0 .. n-1`           structural variables;
    * `n .. n+m-1`          slack variables (slack `n+i` matches row `i`);
    * `n+m .. n+m+k-1`     artificial variables (one per negative-rhs
                            row, where `k = numArt`);
    * `n+m+k`              right-hand side.

    Rows:
    * `0`          objective / reduced-cost row;
    * `1 .. m`     constraint rows.

    `basis[i]` is the column index that is basic in constraint
    row `i+1`; its length is `m`. -/
private structure State where
  tab   : Array (Array Rat)
  basis : Array Nat
  deriving Inhabited

/-- Build the initial constraint rows. The objective row (row 0) is
    left at zero; callers (`setupPhase1` / `setupPhase2`) fill it in
    according to which phase is starting. -/
private def initialState {m n : Nat} (p : Problem m n)
    (infos : Array RowInfo) (numArt : Nat) : State := Id.run do
  let totalVars := n + m + numArt
  let colCount := totalVars + 1
  let zeroRow : Array Rat := Array.replicate colCount 0
  let mut tab : Array (Array Rat) := Array.replicate (m + 1) zeroRow
  let mut basis : Array Nat := Array.replicate m 0
  for i in [:m] do
    let info := infos[i]!
    let mut row := zeroRow
    row := row.set! (n + i) info.sign
    row := row.set! totalVars info.rhs
    match info.artCol with
    | some ac =>
        row := row.set! ac 1
        basis := basis.set! i ac
    | none =>
        basis := basis.set! i (n + i)
    tab := tab.set! (i + 1) row
  -- Sum the sparse `A` entries (scaled by `sign`) into the constraint
  -- rows. `validate` already deduplicates so the addition is identical
  -- to overwriting on the intended path; doing it additively keeps the
  -- semantics the same as `LPVerify.evalAx` for direct callers (e.g.
  -- tests) that bypass `validate`.
  for entry in p.a do
    let (r, c, v) := entry
    let i := r.val
    let sign := infos[i]!.sign
    let row := tab[i + 1]!
    tab := tab.set! (i + 1) (row.set! c.val (row[c.val]! + sign * v))
  pure { tab := tab, basis := basis }

/-- Subtract `c * row src` from `row dst` (componentwise). -/
private def subRow (tab : Array (Array Rat)) (dst src : Nat) (c : Rat)
    (colCount : Nat) : Array (Array Rat) := Id.run do
  let mut out := tab
  let srcRow := out[src]!
  let mut dstRow := out[dst]!
  for j in [:colCount] do
    dstRow := dstRow.set! j (dstRow[j]! - c * srcRow[j]!)
  out := out.set! dst dstRow
  pure out

/-- Set up the phase 1 objective row (`1` on each artificial column),
    then price out by subtracting each artificial-basic constraint row.
    Has no effect when there are no artificials. -/
private def setupPhase1 (st : State) (infos : Array RowInfo)
    (colCount : Nat) : State := Id.run do
  let m := infos.size
  let mut tab := st.tab
  let mut row0 := tab[0]!
  for i in [:m] do
    match infos[i]!.artCol with
    | some ac => row0 := row0.set! ac 1
    | none    => ()
  tab := tab.set! 0 row0
  for i in [:m] do
    if infos[i]!.artCol.isSome then
      tab := subRow tab 0 (i + 1) 1 colCount
  pure { tab := tab, basis := st.basis }

/-- Reset row 0 to the phase 2 objective (`c` on structural columns)
    and price out the current basis. Artificials get cost `0` so they
    are locked out of phase 2's `chooseEntering` (which restricts to
    columns `< n + m`). -/
private def setupPhase2 {m n : Nat} (st : State) (p : Problem m n)
    (colCount : Nat) : State := Id.run do
  let mut tab := st.tab
  let mut row0 : Array Rat := Array.replicate colCount 0
  for j in [:n] do
    row0 := row0.set! j p.c.toArray[j]!
  tab := tab.set! 0 row0
  -- Price out: the basic column in row `i+1` is in canonical form
  -- (`tab[i+1][basis[i]] = 1`), so a single subtraction zeros it out.
  for i in [:m] do
    let bv := st.basis[i]!
    let coeff := tab[0]![bv]!
    if coeff ≠ 0 then
      tab := subRow tab 0 (i + 1) coeff colCount
  pure { tab := tab, basis := st.basis }

/-! ## Pivot selection. -/

/-- Pick the entering column by Bland's rule: smallest column index
    `j < entBound` whose reduced cost is strictly negative. The bound
    is `n + m + numArt` in phase 1 (any column may enter) and `n + m`
    in phase 2 (artificials are locked out). Returns `none` when the
    current basis is already optimal within the bound. -/
private def chooseEntering (tab : Array (Array Rat)) (entBound : Nat) :
    Option Nat := Id.run do
  for j in [:entBound] do
    if tab[0]![j]! < 0 then return some j
  pure none

/-- Pick the leaving row by the standard ratio test with Bland's
    tie-break (smallest basis-variable index among ties). Returns
    the *1-based* tableau row index, or `none` if every coefficient
    in the entering column is `≤ 0` (the LP is unbounded along
    this direction). `rhsCol` is the column index of the rhs. -/
private def chooseLeaving (st : State) (enter rhsCol : Nat) :
    Option Nat := Id.run do
  let mut best : Option (Rat × Nat × Nat) := none
  for i in [1:st.basis.size + 1] do
    let aij := st.tab[i]![enter]!
    if aij > 0 then
      let ratio := st.tab[i]![rhsCol]! / aij
      let bv := st.basis[i - 1]!
      let take : Bool :=
        match best with
        | none                  => true
        | some (br, bbv, _) => ratio < br || (ratio = br && bv < bbv)
      if take then best := some (ratio, bv, i)
  pure (best.map (·.2.2))

/-- Pivot at entry `(row, col)`: normalise the pivot row and
    eliminate `col` from every other row. -/
private def pivot (st : State) (row col colCount : Nat) : State := Id.run do
  let mut tab := st.tab
  let pivotVal := tab[row]![col]!
  let pr : Array Rat := tab[row]!.map (· / pivotVal)
  tab := tab.set! row pr
  for i in [:tab.size] do
    if i ≠ row then
      let coeff := tab[i]![col]!
      if coeff ≠ 0 then
        let ri := tab[i]!
        let mut ri' := ri
        for j in [:colCount] do
          ri' := ri'.set! j (ri[j]! - coeff * pr[j]!)
        tab := tab.set! i ri'
  pure { tab := tab, basis := st.basis.set! (row - 1) col }

/-! ## Simplex loop. -/

/-- Outcome of `simplexLoop`. -/
private inductive Outcome where
  | optimal   (st : State)
  | unbounded (st : State) (enter : Nat)
  | iterLimit (st : State)
  deriving Inhabited

/-- Driver loop. Bland's rule guarantees termination in finitely
    many pivots, but we still take an explicit `fuel` argument so
    callers can honour `Options.iterLimit` and so the recursion is
    structurally guaranteed to terminate.

    Optimality and unboundedness are checked before fuel is consumed:
    an already-optimal LP returns `.optimal` even with `fuel = 0`,
    and only an actual pivot draws from the budget. The loop returns
    the remaining fuel so callers can share a budget across phases. -/
private def simplexLoop (st : State) (entBound rhsCol : Nat) (fuel : Nat) :
    Outcome × Nat :=
  match chooseEntering st.tab entBound with
  | none   => (.optimal st, fuel)
  | some j =>
    match chooseLeaving st j rhsCol with
    | none   => (.unbounded st j, fuel)
    | some i =>
      match fuel with
      | 0        => (.iterLimit st, 0)
      | fuel + 1 => simplexLoop (pivot st i j (rhsCol + 1)) entBound rhsCol fuel

/-! ## Phase 1 helpers. -/

/-- Sum of basic-artificial rhs values: this is the phase 1 objective
    at the current basis. Equals `0` exactly when no artificial is
    basic at a positive value (i.e., the original LP has a feasible
    starting basis). -/
private def phase1ObjValue (st : State) (n m rhsCol : Nat) : Rat := Id.run do
  let mut acc : Rat := 0
  for i in [:m] do
    let bv := st.basis[i]!
    if bv ≥ n + m then
      -- Basic artificial.
      acc := acc + st.tab[i + 1]![rhsCol]!
  pure acc

/-- After phase 1, drive any artificial that is still basic (at value
    `0`, since phase 1 reached optimum `0`) out of the basis. If the
    artificial's row has a nonzero entry in any non-artificial column,
    pivot on the smallest such column. Otherwise the row is redundant
    (zero coefficients on all real variables) and the artificial is
    left basic at `0`; phase 2 will not pick it. -/
private def driveOutArtificials (st : State) (n m rhsCol : Nat) : State :=
  Id.run do
    let nonArtBound := n + m
    let colCount := rhsCol + 1
    let mut st := st
    for i in [:m] do
      let bv := st.basis[i]!
      if bv ≥ nonArtBound then
        -- Find a pivot column among non-artificial columns.
        let mut pivotCol : Option Nat := none
        for j in [:nonArtBound] do
          if pivotCol.isNone ∧ st.tab[i + 1]![j]! ≠ 0 then
            pivotCol := some j
        match pivotCol with
        | some j => st := pivot st (i + 1) j colCount
        | none   => ()
    pure st

/-! ## Certificate extraction. -/

/-- Primal solution `x ∈ ℚⁿ`: basic structural variables read their
    rhs, non-basic ones are zero. -/
private def extractPrimal (st : State) (n rhsCol : Nat) : Array Rat :=
  Id.run do
    let mut x : Array Rat := Array.replicate n 0
    for i in [:st.basis.size] do
      let bv := st.basis[i]!
      if bv < n then
        x := x.set! bv st.tab[i + 1]![rhsCol]!
    pure x

/-- Row-dual multipliers `y ∈ ℚᵐ` for `Ax ≤ b`. They are read straight
    off the slack columns of the final reduced-cost row: `yᵢ = tab[0,
    n+i]`. The same formula gives the optimal dual in phase 2 and the
    Farkas multipliers in phase 1 (this is exactly the sign-convention
    match the verifier asks for: `DualBundle.rowUpper ≥ 0`). -/
private def extractDualRow (st : State) (n m : Nat) : Array Rat :=
  Id.run do
    let mut u : Array Rat := Array.mkEmpty m
    for i in [:m] do
      u := u.push st.tab[0]![n + i]!
    pure u

/-- Reduced costs `z ∈ ℚⁿ` of the structural variables, read off
    the final row 0. `≥ 0` at optimum (phase 2) or under Farkas
    feasibility (phase 1); the verifier consumes them as `colLower`. -/
private def extractRedCost (st : State) (n : Nat) : Array Rat :=
  Id.run do
    let mut z : Array Rat := Array.mkEmpty n
    for j in [:n] do
      z := z.push st.tab[0]![j]!
    pure z

/-- Recession ray in `x`-space, built from the column of the
    entering variable that exposed unboundedness. -/
private def extractRay (st : State) (enter n : Nat) : Array Rat :=
  Id.run do
    let mut r : Array Rat := Array.replicate n 0
    if enter < n then r := r.set! enter 1
    for i in [:st.basis.size] do
      let k := st.basis[i]!
      if k < n then
        r := r.set! k (-(st.tab[i + 1]![enter]!))
    pure r

/-! ## Small helpers. -/

private def toVec (a : Array Rat) (n : Nat) : Vector Rat n :=
  Vector.ofFn (fun j : Fin n => a[j.val]!)

private def zeroVec (n : Nat) : Vector Rat n := Vector.replicate n 0

private def dotArr (xs ys : Array Rat) : Rat := Id.run do
  let mut acc : Rat := 0
  for i in [:xs.size] do
    acc := acc + xs[i]! * ys[i]!
  pure acc

/-! ## Column-bound preprocessing. -/

private inductive ColMap where
  | lower (col : Nat)
  | upperFlip (col : Nat)
  | free (pos neg : Nat)
  | boxed (col row : Nat)
  deriving Inhabited

/-- How an original row was encoded as 0–2 upper-only rows in the
    preprocessed problem. Used by `translateDual` to recombine the
    preprocessed multipliers back into the original (lower, upper)
    split.

    * `upperOnly r`        — original `(none, some hi)`, kept as one row.
    * `lowerOnly r`        — original `(some lo, none)`, sign-flipped.
    * `ranged rUp rLo`     — original `(some lo, some hi)` (equality or
                              proper range), split into two rows.
    * `dropped`            — original `(none, none)`, no constraint. -/
private inductive RowMap where
  | upperOnly (row : Nat)
  | lowerOnly (row : Nat)
  | ranged    (rowUp rowLo : Nat)
  | dropped
  deriving Inhabited

private structure Preprocessed (m n : Nat) where
  m'       : Nat
  n'       : Nat
  problem  : Problem m' n'
  colMap   : Array ColMap
  rowMap   : Array RowMap

private def addEntry (entries : Array (Nat × Nat × Rat)) (row col : Nat)
    (value : Rat) : Array (Nat × Nat × Rat) :=
  if value = 0 then entries else entries.push (row, col, value)

private def sparseEntries (m' n' : Nat)
    (raw : Array (Nat × Nat × Rat)) : Array (Fin m' × Fin n' × Rat) :=
  raw.filterMap fun (r, c, v) =>
    if hr : r < m' then
      if hc : c < n' then some (⟨r, hr⟩, ⟨c, hc⟩, v) else none
    else none

private def colCoeff (maps : Array ColMap) (j k : Nat) : Rat :=
  match maps[j]! with
  | .lower col      => if k = col then 1 else 0
  | .upperFlip col  => if k = col then -1 else 0
  | .free pos neg   => if k = pos then 1 else if k = neg then -1 else 0
  | .boxed col _    => if k = col then 1 else 0

private def colShift (bounds : Array (Option Rat × Option Rat)) (j : Nat) : Rat :=
  match bounds[j]! with
  | (some lo, _) => lo
  | (none, some hi) => hi
  | (none, none) => 0

private def preprocess {m n : Nat} (p : Problem m n) :
    Except ScopeError (Preprocessed m n) := do
  -- Row preprocessing: each original `(lo, hi)` row maps to 0–2
  -- upper-only rows in the preprocessed problem.
  let mut rowMaps : Array RowMap := Array.mkEmpty m
  -- `rowSpecs[k] = (origRow, sign, rhsRaw)` for new row `k`:
  -- the new constraint is `sign · aᵢ · x ≤ rhsRaw` (before column shift).
  let mut rowSpecs : Array (Nat × Rat × Rat) := #[]
  for i in [:m] do
    match p.rowBounds.toArray[i]! with
    | (none, some hi) =>
        let r := rowSpecs.size
        rowSpecs := rowSpecs.push (i, 1, hi)
        rowMaps := rowMaps.push (.upperOnly r)
    | (some lo, none) =>
        let r := rowSpecs.size
        rowSpecs := rowSpecs.push (i, -1, -lo)
        rowMaps := rowMaps.push (.lowerOnly r)
    | (some lo, some hi) =>
        let rUp := rowSpecs.size
        rowSpecs := rowSpecs.push (i, 1, hi)
        let rLo := rowSpecs.size
        rowSpecs := rowSpecs.push (i, -1, -lo)
        rowMaps := rowMaps.push (.ranged rUp rLo)
    | (none, none) =>
        rowMaps := rowMaps.push .dropped
  let mFromRows := rowSpecs.size
  -- For each original row, list its `(newRow, sign)` children so we
  -- can dispatch sparse-matrix entries with a single pass over `p.a`.
  let mut rowOrigToNew : Array (Array (Nat × Rat)) := Array.replicate m #[]
  for r in [:rowSpecs.size] do
    let (origRow, sign, _) := rowSpecs[r]!
    rowOrigToNew := rowOrigToNew.set! origRow
      ((rowOrigToNew[origRow]!).push (r, sign))

  let colBounds := p.colBounds.toArray
  let mut maps : Array ColMap := #[]
  let mut cRaw : Array Rat := #[]
  let mut shift : Array Rat := #[]
  let mut addedRows : Array (Nat × Nat × Rat) := #[]
  let mut nextCol : Nat := 0
  let mut nextExtraRow : Nat := 0

  for j in [:n] do
    let cj := p.c.toArray[j]!
    match colBounds[j]! with
    | (some lo, none) =>
        let col := nextCol
        nextCol := nextCol + 1
        maps := maps.push (.lower col)
        cRaw := cRaw.push cj
        shift := shift.push lo
    | (none, some hi) =>
        let col := nextCol
        nextCol := nextCol + 1
        maps := maps.push (.upperFlip col)
        cRaw := cRaw.push (-cj)
        shift := shift.push hi
    | (none, none) =>
        let pos := nextCol
        let neg := nextCol + 1
        nextCol := nextCol + 2
        maps := maps.push (.free pos neg)
        cRaw := cRaw.push cj
        cRaw := cRaw.push (-cj)
        shift := shift.push 0
    | (some lo, some hi) =>
        let col := nextCol
        let row := mFromRows + nextExtraRow
        nextCol := nextCol + 1
        nextExtraRow := nextExtraRow + 1
        maps := maps.push (.boxed col row)
        cRaw := cRaw.push cj
        shift := shift.push lo
        addedRows := addedRows.push (row, col, hi - lo)

  let m' := mFromRows + nextExtraRow
  let n' := nextCol
  -- `rowShiftOrig[i] = Σ_c a_{i,c} · shift[c]`; the new row's rhs is
  -- `rhsRaw - sign · rowShiftOrig[origRow]`.
  let mut rowShiftOrig : Array Rat := Array.replicate m 0
  let mut entries : Array (Nat × Nat × Rat) := #[]
  for entry in p.a do
    let (r, c, v) := entry
    let i := r.val
    let j := c.val
    rowShiftOrig := rowShiftOrig.set! i (rowShiftOrig[i]! + v * shift[j]!)
    for nr in rowOrigToNew[i]! do
      let (newRow, sign) := nr
      let signedV := sign * v
      match maps[j]! with
      | .lower col | .upperFlip col | .boxed col _ =>
          entries := addEntry entries newRow col (signedV * colCoeff maps j col)
      | .free pos neg =>
          entries := addEntry entries newRow pos signedV
          entries := addEntry entries newRow neg (-signedV)

  for added in addedRows do
    let (row, col, _) := added
    entries := addEntry entries row col 1

  let cVec : Vector Rat n' := Vector.ofFn (fun j => cRaw[j.val]!)
  let objOffset := p.objOffset + dotArr p.c.toArray shift
  let rb : Vector (Option Rat × Option Rat) m' := Vector.ofFn fun i =>
    if i.val < mFromRows then
      let (origRow, sign, rhsRaw) := rowSpecs[i.val]!
      (none, some (rhsRaw - sign * rowShiftOrig[origRow]!))
    else
      let extra := i.val - mFromRows
      let rhs := addedRows[extra]!.2.2
      (none, some rhs)
  let cb : Vector (Option Rat × Option Rat) n' :=
    Vector.replicate n' (some (0 : Rat), none)
  let p' : Problem m' n' :=
    { c := cVec
      objOffset := objOffset
      a := sparseEntries m' n' entries
      rowBounds := rb
      colBounds := cb }
  pure { m' := m', n' := n', problem := p', colMap := maps, rowMap := rowMaps }

private def translatePrimal (maps : Array ColMap) (bounds : Array (Option Rat × Option Rat))
    (y : Array Rat) : Array Rat := Id.run do
  let mut x : Array Rat := Array.mkEmpty maps.size
  for j in [:maps.size] do
    let value :=
      match maps[j]! with
      | .lower col      => colShift bounds j + y[col]!
      | .upperFlip col  => colShift bounds j - y[col]!
      | .free pos neg   => y[pos]! - y[neg]!
      | .boxed col _    => colShift bounds j + y[col]!
    x := x.push value
  pure x

private def translateRay (maps : Array ColMap) (r : Array Rat) : Array Rat := Id.run do
  let mut x : Array Rat := Array.mkEmpty maps.size
  for j in [:maps.size] do
    let value :=
      match maps[j]! with
      | .lower col      => r[col]!
      | .upperFlip col  => -r[col]!
      | .free pos neg   => r[pos]! - r[neg]!
      | .boxed col _    => r[col]!
    x := x.push value
  pure x

private def translateDual {m n m' n' : Nat} (pp : Preprocessed m n)
    (d : DualBundle m' n') : DualBundle m n :=
  let rowLower : Vector Rat m := Vector.ofFn fun i =>
    match pp.rowMap[i.val]! with
    | .upperOnly _ | .dropped => 0
    | .lowerOnly r            => d.rowUpper.toArray[r]!
    | .ranged _ rLo           => d.rowUpper.toArray[rLo]!
  let rowUpper : Vector Rat m := Vector.ofFn fun i =>
    match pp.rowMap[i.val]! with
    | .lowerOnly _ | .dropped => 0
    | .upperOnly r            => d.rowUpper.toArray[r]!
    | .ranged rUp _           => d.rowUpper.toArray[rUp]!
  let colLower : Vector Rat n := Vector.ofFn fun j =>
    match pp.colMap[j.val]! with
    | .lower col | .boxed col _ => d.colLower.toArray[col]!
    | .upperFlip _ | .free _ _  => 0
  let colUpper : Vector Rat n := Vector.ofFn fun j =>
    match pp.colMap[j.val]! with
    | .upperFlip col => d.colLower.toArray[col]!
    | .boxed _ row   => d.rowUpper.toArray[row]!
    | .lower _ | .free _ _ => 0
  { rowLower := rowLower
    rowUpper := rowUpper
    colLower := colLower
    colUpper := colUpper }

private def translateSolution {m n : Nat} (p : Problem m n)
    (pp : Preprocessed m n) (sol : Solution pp.m' pp.n') : Solution m n :=
  match sol.status with
  | .optimal =>
      match sol.certificate.primal, sol.certificate.dual with
      | some y, some d =>
          let xArr := translatePrimal pp.colMap p.colBounds.toArray y.toArray
          let dual := translateDual pp d
          { status      := .optimal
            objective   := some (dotArr p.c.toArray xArr + p.objOffset)
            certificate := { primal := some (toVec xArr n), dual := some dual, ray := none }
            log         := sol.log }
      | _, _ => { sol with certificate := default }
  | .unbounded =>
      match sol.certificate.primal, sol.certificate.ray with
      | some y, some r =>
          let xArr := translatePrimal pp.colMap p.colBounds.toArray y.toArray
          let rArr := translateRay pp.colMap r.toArray
          { status      := .unbounded
            objective   := none
            certificate := { primal := some (toVec xArr n), dual := none, ray := some (toVec rArr n) }
            log         := sol.log }
      | _, _ => { sol with certificate := default }
  | .infeasible =>
      match sol.certificate.dual with
      | some d =>
          let dual := translateDual pp d
          { status      := .infeasible
            objective   := none
            certificate := { primal := none, dual := some dual, ray := none }
            log         := sol.log }
      | none => { sol with certificate := default }
  | _ =>
      { status      := sol.status
        objective   := sol.objective
        certificate := default
        log         := sol.log }

/-! ## Public entry point. -/

/-- Build the optimal-solution `Certificate`. -/
private def optimalSolution {m n : Nat} (p : Problem m n) (st : State)
    (n_ m_ rhsCol : Nat) : Solution m n :=
  let xArr := extractPrimal st n_ rhsCol
  let uArr := extractDualRow st n_ m_
  let zArr := extractRedCost st n_
  let dual : DualBundle m n :=
    { rowLower := zeroVec m
      rowUpper := toVec uArr m
      colLower := toVec zArr n
      colUpper := zeroVec n }
  let cert : Certificate m n :=
    { primal := some (toVec xArr n)
      dual   := some dual
      ray    := none }
  { status      := .optimal
    objective   := some (dotArr p.c.toArray xArr + p.objOffset)
    certificate := cert
    log         := "" }

/-- Build the unbounded-solution `Certificate`. -/
private def unboundedSolution {m n : Nat} (st : State) (enter n_ rhsCol : Nat) :
    Solution m n :=
  let xArr := extractPrimal st n_ rhsCol
  let rArr := extractRay st enter n_
  let cert : Certificate m n :=
    { primal := some (toVec xArr n)
      dual   := none
      ray    := some (toVec rArr n) }
  { status      := .unbounded
    objective   := none
    certificate := cert
    log         := "" }

/-- Build the infeasible (Farkas) `Certificate` from phase 1's final
    tableau. The Farkas multipliers `yᵢ ≥ 0` live in `rowUpper`; the
    `zL ≥ 0` slack on `x ≥ 0` lives in `colLower`. Together they
    satisfy `Aᵀy + (-zL) = 0` (stationarity) and `bᵀy < 0`, which
    `LPVerify.checkInfeasible` re-derives directly. -/
private def infeasibleSolution {m n : Nat} (st : State) (n_ m_ : Nat) :
    Solution m n :=
  let yArr := extractDualRow st n_ m_
  let zArr := extractRedCost st n_
  let dual : DualBundle m n :=
    { rowLower := zeroVec m
      rowUpper := toVec yArr m
      colLower := toVec zArr n
      colUpper := zeroVec n }
  let cert : Certificate m n :=
    { primal := none
      dual   := some dual
      ray    := none }
  { status      := .infeasible
    objective   := none
    certificate := cert
    log         := "" }

/-- Iteration-limit solution. -/
private def iterLimitSolution {m n : Nat} : Solution m n :=
  { status      := .iterLimit
    objective   := none
    certificate := default
    log         := "" }

/-- Solve a min-form standard problem and produce a certificate against it. -/
private def solveStandard {m n : Nat} (p : Problem m n) (fuel : Nat) :
    Except SolveError (Solution m n) :=
  match checkScope p with
  | .error e => .error (.bridge e.toMsg)
  | .ok () =>
    let (infos, numArt) := computeRowInfos p
    let totalVars := n + m + numArt
    let rhsCol := totalVars
    let colCount := totalVars + 1
    let st0 := initialState p infos numArt
    -- Phase 1 (skipped when there are no artificials).
    if numArt = 0 then
      let stP2 := setupPhase2 st0 p colCount
      match (simplexLoop stP2 (n + m) rhsCol fuel).1 with
      | .iterLimit _      => .ok iterLimitSolution
      | .unbounded st enter => .ok (unboundedSolution st enter n rhsCol)
      | .optimal st       => .ok (optimalSolution p st n m rhsCol)
    else
      let stP1 := setupPhase1 st0 infos colCount
      let (out1, fuel1) := simplexLoop stP1 totalVars rhsCol fuel
      match out1 with
      | .iterLimit _ => .ok iterLimitSolution
      | .unbounded _ _ =>
        -- Phase 1 minimises a sum of nonneg variables, bounded below
        -- by `0`. Unboundedness here is a bridge-invariant violation.
        .error (.bridge "pure-Lean backend: phase 1 reported unbounded (internal bug)")
      | .optimal st1 =>
        if phase1ObjValue st1 n m rhsCol > 0 then
          .ok (infeasibleSolution st1 n m)
        else
          let stClean := driveOutArtificials st1 n m rhsCol
          let stP2 := setupPhase2 stClean p colCount
          match (simplexLoop stP2 (n + m) rhsCol fuel1).1 with
          | .iterLimit _      => .ok iterLimitSolution
          | .unbounded st enter => .ok (unboundedSolution st enter n rhsCol)
          | .optimal st       => .ok (optimalSolution p st n m rhsCol)

/-- Solve a min-form problem and produce a certificate against it. -/
private def solveCanon {m n : Nat} (p : Problem m n) (fuel : Nat) :
    Except SolveError (Solution m n) :=
  match preprocess p with
  | .error e => .error (.bridge e.toMsg)
  | .ok pp =>
      match solveStandard pp.problem fuel with
      | .error e => .error e
      | .ok sol => .ok (translateSolution p pp sol)

/-- Pure-Lean simplex driver. Canonicalises to minimisation,
    solves, and restores the caller's original sense in
    `Solution.objective`. The certificate is against the
    canonical (min) problem, matching `Soplex.Verify.IsOptimal`. -/
def solve {m n : Nat} (opts : Options) (p : Problem m n) :
    Except SolveError (Solution m n) :=
  let pCanon := canonicalize opts.sense p
  let fuel := opts.iterLimit.getD 100000
  match solveCanon pCanon fuel with
  | .error e => .error e
  | .ok sol =>
    let objective := sol.objective.map fun v =>
      match opts.sense with
      | .minimize => v
      | .maximize => -v
    .ok { sol with objective := objective }

end Simplex

end Soplex.Backend.Pure
