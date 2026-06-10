/-
  Behavioral tests for the pure-Lean primal simplex.

  Every case solves a toy LP and re-runs the resulting certificate
  through `LPVerify`'s `checkOptimal` / `checkUnbounded`, so we
  exercise both the solver and its dual / ray construction at
  once. Cases include `min`, `max`, multi-row, degenerate, and an
  unbounded direction (with the recession-ray check). One case is
  out-of-scope and must come back as
  `SolveError.invalidProblem (.unsupportedFeature _)`.

  Run via `lake test` or `lake exe simplex-tests`.
-/

import LPBackendPure
import LPTactic
import LPVerify

namespace LPBackendPureTest.Simplex

open LP LP.Verify

/-- Construct a `Problem` in this backend's first-cut scope:
    `c·x` objective, sparse `A`, `Ax ≤ b`, `x ≥ 0`. -/
private def mkLE (m n : Nat) (c : List Rat) (a : List (Nat × Nat × Rat))
    (b : List Rat) : Problem m n :=
  let cVec : Vector Rat n :=
    Vector.ofFn (fun j => (c[j.val]?).getD 0)
  let aArr : Array (Fin m × Fin n × Rat) :=
    a.toArray.filterMap fun (r, k, v) =>
      if hr : r < m then
        if hk : k < n then some (⟨r, hr⟩, ⟨k, hk⟩, v) else none
      else none
  let rb : Vector (Option Rat × Option Rat) m :=
    Vector.ofFn (fun i => (none, some ((b[i.val]?).getD 0)))
  let cb : Vector (Option Rat × Option Rat) n :=
    Vector.replicate n (some 0, none)
  { c := cVec, objOffset := 0, a := aArr,
    rowBounds := rb, colBounds := cb }

/-- Construct a problem with caller-provided column bounds and
    upper-only rows. -/
private def mkLEWithCols (m n : Nat) (c : List Rat) (a : List (Nat × Nat × Rat))
    (b : List Rat) (cols : List (Option Rat × Option Rat)) : Problem m n :=
  let cVec : Vector Rat n :=
    Vector.ofFn (fun j => (c[j.val]?).getD 0)
  let aArr : Array (Fin m × Fin n × Rat) :=
    a.toArray.filterMap fun (r, k, v) =>
      if hr : r < m then
        if hk : k < n then some (⟨r, hr⟩, ⟨k, hk⟩, v) else none
      else none
  let rb : Vector (Option Rat × Option Rat) m :=
    Vector.ofFn (fun i => (none, some ((b[i.val]?).getD 0)))
  let cb : Vector (Option Rat × Option Rat) n :=
    Vector.ofFn (fun j => (cols[j.val]?).getD (some 0, none))
  { c := cVec, objOffset := 0, a := aArr,
    rowBounds := rb, colBounds := cb }

/-- Construct a problem with caller-provided row and column bounds. -/
private def mkRowsCols (m n : Nat) (c : List Rat) (a : List (Nat × Nat × Rat))
    (rows : List (Option Rat × Option Rat))
    (cols : List (Option Rat × Option Rat)) : Problem m n :=
  let cVec : Vector Rat n :=
    Vector.ofFn (fun j => (c[j.val]?).getD 0)
  let aArr : Array (Fin m × Fin n × Rat) :=
    a.toArray.filterMap fun (r, k, v) =>
      if hr : r < m then
        if hk : k < n then some (⟨r, hr⟩, ⟨k, hk⟩, v) else none
      else none
  let rb : Vector (Option Rat × Option Rat) m :=
    Vector.ofFn (fun i => (rows[i.val]?).getD (none, none))
  let cb : Vector (Option Rat × Option Rat) n :=
    Vector.ofFn (fun j => (cols[j.val]?).getD (some 0, none))
  { c := cVec, objOffset := 0, a := aArr,
    rowBounds := rb, colBounds := cb }

private def assertM (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw (IO.userError msg)

/-- Solve `p` and verify the certificate against `canonicalize sense p`.
    Asserts the expected status and objective. -/
private def runCase {m n : Nat} (label : String) (opts : Options)
    (p : Problem m n) (expectedStatus : SolveStatus)
    (expectedObj : Option Rat) : IO Unit := do
  match Backend.Pure.Simplex.solve opts p with
  | .error e =>
      throw (IO.userError s!"[{label}] solve returned error: {repr e}")
  | .ok sol =>
      assertM (sol.status = expectedStatus)
        s!"[{label}] status: got {repr sol.status}, want {repr expectedStatus}"
      assertM (sol.objective = expectedObj)
        s!"[{label}] objective: got {repr sol.objective}, want {repr expectedObj}"
      let pCanon := canonicalize opts.sense p
      match sol.status with
      | .optimal =>
          match sol.certificate.primal, sol.certificate.dual with
          | some x, some d =>
              assertM (checkOptimal pCanon x d)
                s!"[{label}] checkOptimal rejected the certificate"
          | _, _ =>
              throw (IO.userError s!"[{label}] optimal but missing primal/dual")
      | .unbounded =>
          match sol.certificate.primal, sol.certificate.ray with
          | some x, some r =>
              assertM (checkUnbounded pCanon x r)
                s!"[{label}] checkUnbounded rejected the certificate"
          | _, _ =>
              throw (IO.userError s!"[{label}] unbounded but missing primal/ray")
      | .infeasible =>
          match sol.certificate.dual with
          | some d =>
              assertM (checkInfeasible pCanon d)
                s!"[{label}] checkInfeasible rejected the Farkas certificate"
          | none =>
              throw (IO.userError s!"[{label}] infeasible but missing dual")
      | s =>
          throw (IO.userError s!"[{label}] unexpected status {repr s}")

/-! ## Cases. -/

-- min -x s.t. x ≤ 5, x ≥ 0 → x=5, obj=-5
private def case_minNegX : IO Unit :=
  runCase "min -x ≤ 5" {} (mkLE 1 1 [-1] [(0,0,1)] [5]) .optimal (some (-5))

-- min x s.t. x ≤ 5, x ≥ 0 → x=0 (no pivots)
private def case_minXTrivial : IO Unit :=
  runCase "min x ≤ 5" {} (mkLE 1 1 [1] [(0,0,1)] [5]) .optimal (some 0)

-- max x s.t. x ≤ 5 → x=5 (sense canonicalisation)
private def case_maxX : IO Unit :=
  runCase "max x ≤ 5" { sense := .maximize }
    (mkLE 1 1 [1] [(0,0,1)] [5]) .optimal (some 5)

-- min -x - y s.t. x+y ≤ 3, x ≤ 2, y ≤ 2 → obj=-3
private def case_minTwoVar : IO Unit :=
  runCase "min -x-y" {}
    (mkLE 3 2 [-1, -1] [(0,0,1),(0,1,1),(1,0,1),(2,1,1)] [3, 2, 2])
    .optimal (some (-3))

-- min -x s.t. (no rows) → unbounded
private def case_unbounded : IO Unit :=
  runCase "min -x (no rows)" {} (mkLE 0 1 [-1] [] []) .unbounded none

-- min x s.t. x ≤ 0 → x=0 (degenerate rhs)
private def case_degenerate : IO Unit :=
  runCase "min x ≤ 0" {} (mkLE 1 1 [1] [(0,0,1)] [0]) .optimal (some 0)

-- min -3a -2b s.t. a+b ≤ 4, 2a+b ≤ 5 → a=1, b=3, obj=-9
private def case_classic : IO Unit :=
  runCase "min -3a-2b" {}
    (mkLE 2 2 [-3, -2] [(0,0,1),(0,1,1),(1,0,2),(1,1,1)] [4, 5])
    .optimal (some (-9))

-- `min -x ≤ 5` needs exactly one pivot. With `iterLimit = 1` and
-- optimality-checked-before-fuel, this returns `.optimal`. Old
-- "match on fuel first" shape would burn the last pivot and report
-- `.iterLimit` even though the next iteration would have found the
-- optimum.
private def case_iterLimitJustEnough : IO Unit :=
  runCase "min -x ≤ 5, iterLimit=1" { iterLimit := some 1 }
    (mkLE 1 1 [-1] [(0,0,1)] [5]) .optimal (some (-5))

-- Free column: min -x s.t. x ≤ 3, -x ≤ 2, x free → x=3.
private def case_freeColumn : IO Unit :=
  runCase "free column" {}
    (mkLEWithCols 2 1 [-1] [(0,0,1),(1,0,-1)] [3, 2] [(none, none)])
    .optimal (some (-3))

-- Negative lower: min -x s.t. x ≤ 4, -2 ≤ x → x=4.
private def case_negativeLowerColumn : IO Unit :=
  runCase "negative-lower column" {}
    (mkLEWithCols 1 1 [-1] [(0,0,1)] [4] [(some (-2), none)])
    .optimal (some (-4))

-- Upper-only: min x s.t. -x ≤ 3, x ≤ 2 → x=-3.
private def case_upperOnlyColumn : IO Unit :=
  runCase "upper-only column" {}
    (mkLEWithCols 1 1 [1] [(0,0,-1)] [3] [(none, some 2)])
    .optimal (some (-3))

-- Boxed: min -x s.t. 0 ≤ x ≤ 2 → x=2.
private def case_boxedColumn : IO Unit :=
  runCase "boxed column" {}
    (mkLEWithCols 0 1 [-1] [] [] [(some 0, some 2)])
    .optimal (some (-2))

-- Two-phase startup: `-x + y ≤ -1` with `x, y ≥ 0` is feasible
-- (only at `x ≥ 1`); minimising `x` is the textbook two-phase
-- example. The slack basis has `s = -1 < 0`, so phase 1 has to
-- drive an artificial to 0 before phase 2 finds `x = 1, y = 0`.
private def case_twoPhaseFeasible : IO Unit :=
  runCase "min x s.t. -x+y ≤ -1" {}
    (mkLE 1 2 [1, 0] [(0,0,-1),(0,1,1)] [-1]) .optimal (some 1)

-- Two-phase startup with two flipped rows: minimise `x + y` subject
-- to `-x - y ≤ -3` and `-x ≤ -1` (i.e., `x + y ≥ 3, x ≥ 1`). Both
-- rows are negative-rhs, so phase 1 adds two artificials and drives
-- both to zero before phase 2 finds `x = 3, y = 0` with obj = 3.
private def case_twoPhaseMultiFlip : IO Unit :=
  runCase "min x+y, two negative-rhs rows" {}
    (mkLE 2 2 [1, 1] [(0,0,-1),(0,1,-1),(1,0,-1)] [-3, -1])
    .optimal (some 3)

-- Genuinely infeasible: `x ≤ 0 ∧ -x ≤ -1` with `x ≥ 0`. No feasible
-- `x`. Phase 1's optimum is strictly positive, so the backend must
-- return `SolveStatus.infeasible` with a Farkas dual `y ≥ 0` such
-- that `Aᵀy ≥ 0` and `bᵀy < 0`. `LPVerify.checkInfeasible` re-checks.
private def case_infeasibleSimple : IO Unit :=
  runCase "infeasible: x ≤ 0 ∧ -x ≤ -1" {}
    (mkLE 2 1 [0] [(0,0,1),(1,0,-1)] [0, -1]) .infeasible none

-- The example from issue #5: `x ≤ 0 ∧ 1 ≤ x` for a free `x`,
-- exercising both the column-bound preprocessing (free column splits
-- to `x⁺ - x⁻`) and the two-flipped-row infeasibility path. The
-- Farkas dual that comes back is the one the `lp` tactic threads into
-- `direct_infeasible_close`.
private def case_infeasibleFreeVar : IO Unit :=
  runCase "infeasible: x ≤ 0 ∧ 1 ≤ x (free x)" {}
    (mkLEWithCols 2 1 [0] [(0,0,1),(1,0,-1)] [0, -1] [(none, none)])
    .infeasible none

-- Equality row: `x + y = 3, 0 ≤ x ≤ 5, 0 ≤ y ≤ 5`, minimise `-x` →
-- `x = 3, y = 0, obj = -3`. Exercises the `(some 3, some 3)` row
-- shape, which splits into two upper-only rows.
private def case_equalityRow : IO Unit :=
  runCase "equality row x+y=3, min -x" {}
    (mkRowsCols 1 2 [-1, 0] [(0,0,1),(0,1,1)]
      [(some 3, some 3)] [(some 0, none), (some 0, none)])
    .optimal (some (-3))

-- ≥-row: `x + y ≥ 2, x, y ≥ 0`, minimise `x + y` → obj = 2.
-- The lower-only row sign-flips to `-x - y ≤ -2`, exercising the
-- two-phase startup from #5.
private def case_geRow : IO Unit :=
  runCase "≥-row x+y≥2, min x+y" {}
    (mkRowsCols 1 2 [1, 1] [(0,0,1),(0,1,1)]
      [(some 2, none)] [(some 0, none), (some 0, none)])
    .optimal (some 2)

-- Ranged row: `1 ≤ x + y ≤ 4, x, y ≥ 0`, minimise `-x - y` → obj = -4.
-- The ranged row splits into `x+y ≤ 4` and `-(x+y) ≤ -1`.
private def case_rangedRow : IO Unit :=
  runCase "ranged 1≤x+y≤4, min -x-y" {}
    (mkRowsCols 1 2 [-1, -1] [(0,0,1),(0,1,1)]
      [(some 1, some 4)] [(some 0, none), (some 0, none)])
    .optimal (some (-4))

-- Lower-only row in conjunction with an upper-only row:
-- `x + y ≥ 2, x ≤ 3, x, y ≥ 0`, minimise `x + y` → obj=2.
private def case_lowerOnlyMixed : IO Unit :=
  runCase "lower-only + upper-only, min x+y" {}
    (mkRowsCols 2 2 [1, 1] [(0,0,1),(0,1,1),(1,0,1)]
      [(some 2, none), (none, some 3)] [(some 0, none), (some 0, none)])
    .optimal (some 2)

-- (none, none) row: trivially satisfied, no constraint.
-- `min x s.t. (no row constraint on row 0), x ≤ 5, x ≥ 0` → x=0.
private def case_freeRow : IO Unit :=
  runCase "free row + upper row, min x" {}
    (mkRowsCols 2 1 [1] [(0,0,1),(1,0,1)] [(none, none), (none, some 5)]
      [(some 0, none)])
    .optimal (some 0)

-- Infeasible equality row: `x = 2, x ≤ 1, x ≥ 0` → infeasible.
private def case_equalityInfeasible : IO Unit :=
  runCase "infeasible equality x=2, x≤1" {}
    (mkRowsCols 2 1 [0] [(0,0,1),(1,0,1)]
      [(some 2, some 2), (none, some 1)] [(some 0, none)])
    .infeasible none

-- Issue #12: when `simplexLoop` runs out of fuel, the result should
-- include a usable partial primal (read off the current basis), the
-- pivot count, and a short diagnostic log — not the bare `Inhabited`
-- default. `min -x s.t. x ≤ 5, x ≥ 0` needs exactly one pivot; with
-- `iterLimit = 0` the loop returns `.iterLimit` after burning zero
-- pivots and the partial primal should be `x = 0` (the slack basis).
private def case_iterLimitPhase2Partial : IO Unit := do
  let opts : Options := { iterLimit := some 0 }
  let p := mkLE 1 1 [-1] [(0,0,1)] [5]
  match Backend.Pure.Simplex.solve opts p with
  | .error e => throw (IO.userError s!"[iterLimit phase2] solve error: {repr e}")
  | .ok sol =>
      assertM (sol.status = .iterLimit)
        s!"[iterLimit phase2] status: got {repr sol.status}, want iterLimit"
      match sol.certificate.primal with
      | none   => throw (IO.userError "[iterLimit phase2] expected partial primal, got none")
      | some x =>
          assertM (x.toArray = #[0])
            s!"[iterLimit phase2] partial primal: got {repr x.toArray}, want #[0]"
      assertM (sol.log.startsWith "iteration limit reached")
        s!"[iterLimit phase2] log: got {repr sol.log}"
      assertM (sol.log.endsWith "0 simplex pivot(s)")
        s!"[iterLimit phase2] log should mention pivot count: got {repr sol.log}"

-- Phase 1 iterLimit: `min x s.t. -x+y ≤ -1, x, y ≥ 0` triggers a
-- phase-1 startup. With `iterLimit = 0`, phase 1 stops before any
-- pivot and the partial primal is the (infeasible) starting point.
-- The log should attribute the stop to phase 1.
private def case_iterLimitPhase1Partial : IO Unit := do
  let opts : Options := { iterLimit := some 0 }
  let p := mkLE 1 2 [1, 0] [(0,0,-1),(0,1,1)] [-1]
  match Backend.Pure.Simplex.solve opts p with
  | .error e => throw (IO.userError s!"[iterLimit phase1] solve error: {repr e}")
  | .ok sol =>
      assertM (sol.status = .iterLimit)
        s!"[iterLimit phase1] status: got {repr sol.status}, want iterLimit"
      assertM sol.certificate.primal.isSome
        "[iterLimit phase1] expected partial primal, got none"
      assertM (sol.log = "iteration limit reached during phase 1 after 0 simplex pivot(s)")
        s!"[iterLimit phase1] log: got {repr sol.log}"

-- Phase 1 iterLimit with a nontrivial column map: `min 0 s.t. -x ≤
-- -1` with `x` free. Preprocessing splits `x` into `x⁺ - x⁻` (so
-- `pp.n' = 2`), and the negative rhs forces a phase 1 startup. With
-- `iterLimit = 0`, the partial primal is in the *preprocessed* `2`-vector
-- space; `translateSolution` must map it back through `pp.colMap`
-- and return a primal of length `1` (the original `n`).
private def case_iterLimitTranslatesDimensions : IO Unit := do
  let opts : Options := { iterLimit := some 0 }
  let p := mkLEWithCols 1 1 [0] [(0,0,-1)] [-1] [(none, none)]
  match Backend.Pure.Simplex.solve opts p with
  | .error e =>
      throw (IO.userError s!"[iterLimit translate] solve error: {repr e}")
  | .ok sol =>
      assertM (sol.status = .iterLimit)
        s!"[iterLimit translate] status: got {repr sol.status}, want iterLimit"
      match sol.certificate.primal with
      | none   =>
          throw (IO.userError "[iterLimit translate] expected partial primal, got none")
      | some x =>
          assertM (x.toArray.size = 1)
            s!"[iterLimit translate] primal length: got {x.toArray.size}, want 1 (original n)"

-- Equality on a free variable: `x = 5` with `x` free, minimise `0` →
-- x = 5. Exercises the row equality split together with the free-column
-- split.
private def case_equalityFreeVar : IO Unit :=
  runCase "equality x=5 with free x" {}
    (mkRowsCols 1 1 [0] [(0,0,1)] [(some 5, some 5)] [(none, none)])
    .optimal (some 0)

example (a b : Rat) (h₁ : 2*a + b ≤ 5) (h₂ : a - b ≤ 1) : 3*a ≤ 6 := by
  lp

-- Equality hypothesis routed through the pure backend.
example (x : Rat) (h : x = 5) : 2*x = 10 := by lp

-- Two-sided (ranged) hypothesis combination via the pure backend:
-- both bounds are needed to conclude `x = 1`.
example (x : Rat) (h₁ : 1 ≤ x) (h₂ : x ≤ 1) : x = 1 := by lp

-- The `lp` tactic's contradictory-hypotheses example from issue #5,
-- routed end-to-end through the pure-Lean backend's `solveStandard`
-- (which returns `SolveStatus.infeasible` + Farkas dual on
-- contradictory hypotheses) and `direct_infeasible_close`.
example (x : Rat) (h₁ : x ≤ 0) (h₂ : 1 ≤ x) : x = 5 := by lp

def main : IO UInt32 := do
  try
    case_minNegX
    case_minXTrivial
    case_maxX
    case_minTwoVar
    case_unbounded
    case_degenerate
    case_classic
    case_iterLimitJustEnough
    case_iterLimitPhase2Partial
    case_iterLimitPhase1Partial
    case_iterLimitTranslatesDimensions
    case_freeColumn
    case_negativeLowerColumn
    case_upperOnlyColumn
    case_boxedColumn
    case_twoPhaseFeasible
    case_twoPhaseMultiFlip
    case_infeasibleSimple
    case_infeasibleFreeVar
    case_equalityRow
    case_geRow
    case_rangedRow
    case_lowerOnlyMixed
    case_freeRow
    case_equalityInfeasible
    case_equalityFreeVar
    IO.println "all simplex tests passed"
    pure 0
  catch e =>
    IO.eprintln s!"FAIL: {e}"
    pure 1

end LPBackendPureTest.Simplex
