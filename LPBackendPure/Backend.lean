/-
  Pure-Lean `LPBackend` adapter.

  Self-registers under priority 100 ("pure tier") on import. With
  the FFI backend (priority 10) or JSON backend (priority 50) also
  imported, those are preferred by `dispatchSolveExact` because
  they have lower priorities. With only this one imported, this is
  the default — what a zero-deps demo or CI lane uses.

  Today the backend ships a working (trivially-`.ok ()`) probe and
  a placeholder `solveExact` that returns a structured error.
  `LPBackendPure.Simplex` (the actual revised-simplex
  implementation) is the follow-up.
-/

import LPCore
import LPTactic.Registry
import LPBackendPure.Simplex

namespace Soplex.Backend.Pure

open Soplex Soplex.LP

/-- Pure-Lean backend probe: nothing to check, no external state.
    The probe always succeeds; the LP solve itself may still fail
    (and reports through `SolveError`). -/
def probe : IO (Except String Unit) :=
  pure (.ok ())

/-- Pure-Lean LP solve. Dispatches to `LPBackendPure.Simplex.solve`,
    which runs a tableau-based primal simplex on `Rat` (Dantzig's rule
    with a Bland fallback on suspected cycling). See
    `LPBackendPure/Simplex.lean` for the accepted first-cut scope
    (upper-only rows, arbitrary column bounds via preprocessing,
    primal-feasible starting basis after preprocessing). -/
def solveExact {m n : Nat} (opts : Options) (p : Problem m n) :
    IO (Except SolveError (Solution m n)) :=
  pure (Simplex.solve opts p)

/-- The `LPBackend` value registered with the tactic registry. -/
def backend : LPBackend where
  name := "pure"
  defaultPriority := 100
  solveExact := solveExact
  probe := probe

initialize registerBackend backend

end Soplex.Backend.Pure
