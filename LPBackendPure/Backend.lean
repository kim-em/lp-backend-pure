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

/-- Pure-Lean LP solve.

    TODO: dispatch to `LPBackendPure.Simplex` once the revised
    simplex implementation lands. Until then the backend
    self-registers (so `availableBackends` lists it) but reports a
    structured "not yet wired" error from `solveExact`. -/
def solveExact {m n : Nat} (_opts : Options) (_p : Problem m n) :
    IO (Except SolveError (Solution m n)) := do
  return Except.error
    (SolveError.bridge
      "pure-Lean backend: simplex implementation not yet wired; \
       see kim-em/lp-backend-pure `LPBackendPure/Simplex.lean`")

/-- The `LPBackend` value registered with the tactic registry. -/
def backend : LPBackend where
  name := "pure"
  defaultPriority := 100
  solveExact := solveExact
  probe := probe

initialize registerBackend backend

end Soplex.Backend.Pure
