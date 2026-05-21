/-
  Pure-Lean primal simplex on `Rat`.

  TODO: implement revised simplex with Bland's rule for cycle
  avoidance. The verifier consumes exact rationals, so the entire
  pivot must run on `Rat` — no Float relaxation. Performance is
  expected to be poor; this exists for zero-deps CI and demos, not
  for production solves.

  Scope (deliberately tiny first cut):
  - Inequality form only (no equality rows, no ranged constraints).
  - Non-negative variables only (no free / bounded columns).
  - Primal-feasible starting point only (no two-phase yet).

  The validator in `LPCore.Validate` accepts a wider class; this
  backend should report `SolveError.invalidProblem` for the
  out-of-scope cases until full coverage lands.
-/

import LPCore.Types

namespace Soplex.Backend.Pure

end Soplex.Backend.Pure
