/-
  Pure-Lean primal simplex on `Rat`.

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
  * Primal-feasible starting basis: every `hi ≥ 0` so the slack basis
    is feasible at `x = 0`. (No two-phase / Big-M yet.)

  The public solver accepts every column-bound shape by first
  preprocessing columns into that core form: free variables are split,
  lower bounds are shifted, upper-only bounds are flipped, and boxed
  variables get an added upper-bound row.

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

/-- Why a problem falls outside this backend's first-cut scope. -/
private inductive ScopeError where
  /-- Row `i` is not of the form `(none, some hi)`. -/
  | rowNotUpperOnly (i : Nat)
  /-- Row `i` has `hi < 0`; we have no two-phase yet, so the slack
      basis is infeasible. -/
  | rowRhsNegative (i : Nat) (rhs : Rat)
  /-- Column `j` is not of the form `(some 0, none)`. -/
  | colNotNonNegOnly (j : Nat)

private def ScopeError.toMsg : ScopeError → String
  | .rowNotUpperOnly i =>
      s!"pure-Lean backend: row {i} is outside first-cut scope " ++
      "(expected `none ≤ Ax ≤ some hi`); see " ++
      "kim-em/lp-backend-pure `LPBackendPure/Simplex.lean`"
  | .rowRhsNegative i rhs =>
      s!"pure-Lean backend: row {i} has rhs {rhs} < 0 " ++
      "(first-cut requires a primal-feasible slack basis; " ++
      "two-phase support is not yet implemented)"
  | .colNotNonNegOnly j =>
      s!"pure-Lean backend: column {j} is outside first-cut scope " ++
      "(expected `some 0 ≤ x ≤ none`)"

/-- Verify the (canonicalised) problem is in the supported scope. -/
private def checkScope {m n : Nat} (p : Problem m n) :
    Except ScopeError Unit := do
  for i in [:m] do
    match p.rowBounds.toArray[i]! with
    | (none, some hi) =>
        if hi < 0 then throw (.rowRhsNegative i hi)
    | _ => throw (.rowNotUpperOnly i)
  for j in [:n] do
    match p.colBounds.toArray[j]! with
    | (some lo, none) =>
        if lo ≠ 0 then throw (.colNotNonNegOnly j)
    | _ => throw (.colNotNonNegOnly j)

/-! ## Tableau state. -/

/-- Dense simplex-tableau state.

    Columns:
    * `0 .. n-1`   structural variables;
    * `n .. n+m-1` slack variables (slack `n+i` matches row `i`);
    * `n+m`        right-hand side.

    Rows:
    * `0`          objective / reduced-cost row;
    * `1 .. m`     constraint rows.

    `basis[i]` is the column index that is basic in constraint
    row `i+1`; its length is `m`. -/
private structure State where
  tab   : Array (Array Rat)
  basis : Array Nat
  deriving Inhabited

/-- Build the initial slack-basis tableau. Assumes `checkScope`
    has already accepted the problem. -/
private def initialState {m n : Nat} (p : Problem m n) : State := Id.run do
  let totalVars := n + m
  let colCount := totalVars + 1
  let zeroRow : Array Rat := Array.replicate colCount 0
  let mut tab : Array (Array Rat) := Array.replicate (m + 1) zeroRow
  -- Objective row: c on structural columns; zeros on slacks and rhs.
  let mut row0 := zeroRow
  for j in [:n] do
    row0 := row0.set! j p.c.toArray[j]!
  tab := tab.set! 0 row0
  -- Constraint rows: slack identity (1 on column `n+i`) and rhs `hi`.
  for i in [:m] do
    let mut row := zeroRow
    row := row.set! (n + i) 1
    row := row.set! totalVars ((p.rowBounds.toArray[i]!).2.getD 0)
    tab := tab.set! (i + 1) row
  -- Sum the sparse `A` entries into the constraint rows. `validate`
  -- already deduplicates, so the addition is identical to overwriting
  -- on the intended path; doing it additively keeps the semantics
  -- the same as `LPVerify.evalAx` for direct callers (e.g. tests)
  -- that bypass `validate`.
  for entry in p.a do
    let (r, c, v) := entry
    let row := tab[r.val + 1]!
    tab := tab.set! (r.val + 1) (row.set! c.val (row[c.val]! + v))
  pure { tab := tab, basis := (Array.range m).map (· + n) }

/-- Pick the entering column by Bland's rule: smallest column index
    whose reduced cost is strictly negative. Returns `none` when
    the current basis is already optimal. -/
private def chooseEntering (tab : Array (Array Rat)) (totalVars : Nat) :
    Option Nat := Id.run do
  for j in [:totalVars] do
    if tab[0]![j]! < 0 then return some j
  pure none

/-- Pick the leaving row by the standard ratio test with Bland's
    tie-break (smallest basis-variable index among ties). Returns
    the *1-based* tableau row index, or `none` if every coefficient
    in the entering column is `≤ 0` (the LP is unbounded along
    this direction). -/
private def chooseLeaving (st : State) (enter totalVars : Nat) :
    Option Nat := Id.run do
  let mut best : Option (Rat × Nat × Nat) := none
  for i in [1:st.basis.size + 1] do
    let aij := st.tab[i]![enter]!
    if aij > 0 then
      let ratio := st.tab[i]![totalVars]! / aij
      let bv := st.basis[i - 1]!
      let take : Bool :=
        match best with
        | none                  => true
        | some (br, bbv, _) => ratio < br || (ratio = br && bv < bbv)
      if take then best := some (ratio, bv, i)
  pure (best.map (·.2.2))

/-- Pivot at entry `(row, col)`: normalise the pivot row and
    eliminate `col` from every other row. -/
private def pivot (st : State) (row col : Nat) : State := Id.run do
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
        for j in [:ri.size] do
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
    and only an actual pivot draws from the budget. -/
private def simplexLoop (st : State) (totalVars : Nat) (fuel : Nat) :
    Outcome :=
  match chooseEntering st.tab totalVars with
  | none   => .optimal st
  | some j =>
    match chooseLeaving st j totalVars with
    | none   => .unbounded st j
    | some i =>
      match fuel with
      | 0        => .iterLimit st
      | fuel + 1 => simplexLoop (pivot st i j) totalVars fuel

/-! ## Certificate extraction. -/

/-- Primal solution `x ∈ ℚⁿ`: basic structural variables read their
    rhs, non-basic ones are zero. -/
private def extractPrimal (st : State) (n totalVars : Nat) : Array Rat :=
  Id.run do
    let mut x : Array Rat := Array.replicate n 0
    for i in [:st.basis.size] do
      let bv := st.basis[i]!
      if bv < n then
        x := x.set! bv st.tab[i + 1]![totalVars]!
    pure x

/-- Row-dual multipliers `u ∈ ℚᵐ` for `Ax ≤ b`. They are read
    straight off the slack columns of the final reduced-cost row:
    `uᵢ = tab[0, n+i]`. These are `≥ 0` at optimum (the simplex
    optimality condition translated through `u = -y`, where `y`
    are the textbook simplex multipliers). -/
private def extractDualRow (st : State) (n m : Nat) : Array Rat :=
  Id.run do
    let mut u : Array Rat := Array.mkEmpty m
    for i in [:m] do
      u := u.push st.tab[0]![n + i]!
    pure u

/-- Reduced costs `z ∈ ℚⁿ` of the structural variables, read off
    the final row 0. `≥ 0` at optimum; the verifier consumes them
    as `colLower`. -/
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

private structure Preprocessed (m n : Nat) where
  m'       : Nat
  n'       : Nat
  problem  : Problem m' n'
  colMap   : Array ColMap

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
  for i in [:m] do
    match p.rowBounds.toArray[i]! with
    | (none, some _) => pure ()
    | _ => throw (.rowNotUpperOnly i)

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
        let row := m + nextExtraRow
        nextCol := nextCol + 1
        nextExtraRow := nextExtraRow + 1
        maps := maps.push (.boxed col row)
        cRaw := cRaw.push cj
        shift := shift.push lo
        addedRows := addedRows.push (row, col, hi - lo)

  let m' := m + nextExtraRow
  let n' := nextCol
  let mut rowShift : Array Rat := Array.replicate m 0
  let mut entries : Array (Nat × Nat × Rat) := #[]
  for entry in p.a do
    let (r, c, v) := entry
    let i := r.val
    let j := c.val
    rowShift := rowShift.set! i (rowShift[i]! + v * shift[j]!)
    match maps[j]! with
    | .lower col | .upperFlip col | .boxed col _ =>
        entries := addEntry entries i col (v * colCoeff maps j col)
    | .free pos neg =>
        entries := addEntry entries i pos v
        entries := addEntry entries i neg (-v)

  for added in addedRows do
    let (row, col, _) := added
    entries := addEntry entries row col 1

  let cVec : Vector Rat n' := Vector.ofFn (fun j => cRaw[j.val]!)
  let objOffset := p.objOffset + dotArr p.c.toArray shift
  let rb : Vector (Option Rat × Option Rat) m' := Vector.ofFn fun i =>
    if i.val < m then
      let hi := (p.rowBounds.toArray[i.val]!).2.getD 0
      (none, some (hi - rowShift[i.val]!))
    else
      let extra := i.val - m
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
  pure { m' := m', n' := n', problem := p', colMap := maps }

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
  let rowLower : Vector Rat m := zeroVec m
  let rowUpper : Vector Rat m := Vector.ofFn (fun i => d.rowUpper.toArray[i.val]!)
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
  | _ =>
      { status      := sol.status
        objective   := sol.objective
        certificate := default
        log         := sol.log }

/-! ## Public entry point. -/

/-- Solve a min-form standard problem and produce a certificate against it. -/
private def solveStandard {m n : Nat} (p : Problem m n) (fuel : Nat) :
    Except SolveError (Solution m n) :=
  match checkScope p with
  | .error e => .error (.bridge e.toMsg)
  | .ok () =>
    let totalVars := n + m
    match simplexLoop (initialState p) totalVars fuel with
    | .iterLimit _ =>
      .ok { status      := .iterLimit
            objective   := none
            certificate := default
            log         := "" }
    | .optimal st =>
      let xArr := extractPrimal st n totalVars
      let uArr := extractDualRow st n m
      let zArr := extractRedCost st n
      let dual : DualBundle m n :=
        { rowLower := zeroVec m
          rowUpper := toVec uArr m
          colLower := toVec zArr n
          colUpper := zeroVec n }
      let cert : Certificate m n :=
        { primal := some (toVec xArr n)
          dual   := some dual
          ray    := none }
      .ok { status      := .optimal
            objective   := some (dotArr p.c.toArray xArr + p.objOffset)
            certificate := cert
            log         := "" }
    | .unbounded st enter =>
      let xArr := extractPrimal st n totalVars
      let rArr := extractRay st enter n
      let cert : Certificate m n :=
        { primal := some (toVec xArr n)
          dual   := none
          ray    := some (toVec rArr n) }
      .ok { status      := .unbounded
            objective   := none
            certificate := cert
            log         := "" }

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
