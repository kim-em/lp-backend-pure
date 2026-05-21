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

  Scope of this first cut (rejected with `SolveError.bridge` otherwise):
  * Inequality form only: every row must be `(none, some hi)`.
  * Non-negative variables only: every column must be `(some 0, none)`.
  * Primal-feasible starting basis: every `hi ≥ 0` so the slack basis
    is feasible at `x = 0`. (No two-phase / Big-M yet.)

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

/-! ## Public entry point. -/

/-- Solve a min-form problem and produce a certificate against it. -/
private def solveCanon {m n : Nat} (p : Problem m n) (fuel : Nat) :
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
