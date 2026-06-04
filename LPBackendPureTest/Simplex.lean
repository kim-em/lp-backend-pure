/-
  Behavioral tests for the pure-Lean primal simplex.

  Every case solves a toy LP and re-runs the resulting certificate
  through `LPVerify`'s `checkOptimal` / `checkUnbounded`, so we
  exercise both the solver and its dual / ray construction at
  once. Cases include `min`, `max`, multi-row, degenerate, and an
  unbounded direction (with the recession-ray check). One case is
  out-of-scope and must come back as a `SolveError.bridge`.

  Run via `lake test` or `lake exe simplex-tests`.
-/

import LPBackendPure
import LPTactic
import LPVerify

namespace LPBackendPureTest.Simplex

open Soplex Soplex.Verify

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

example (a b : Rat) (h₁ : 2*a + b ≤ 5) (h₂ : a - b ≤ 1) : 3*a ≤ 6 := by
  lp

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
    case_freeColumn
    case_negativeLowerColumn
    case_upperOnlyColumn
    case_boxedColumn
    IO.println "all simplex tests passed"
    pure 0
  catch e =>
    IO.eprintln s!"FAIL: {e}"
    pure 1

end LPBackendPureTest.Simplex
