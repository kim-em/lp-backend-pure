/-
  Pure-Lean `LPBackend` adapter.

  Self-registers under priority 100 ("pure tier") on import. With
  the FFI backend (priority 10) or JSON backend (priority 50) also
  imported, those are preferred by `dispatchSolveExact` because
  they have lower priorities. With only this one imported, this is
  the default — what a zero-deps demo or CI lane uses.

  `solveExact` runs the two-phase tableau simplex in
  `LPBackendPure.Simplex` on exact rationals; see that module (and
  the README) for scope and performance caveats.
-/
module

public import LPCore
public import LPTactic.Registry
public import LPBackendPure.Simplex

@[expose] public section

namespace LP.Backend.Pure

open LP

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

end LP.Backend.Pure
