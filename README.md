# LPBackendPure

[![Lean](https://img.shields.io/badge/Lean-4.29.1-blue.svg)](./lean-toolchain)
[![License](https://img.shields.io/github/license/kim-em/lp-backend-pure.svg)](./LICENSE)

Pure-Lean `LPBackend` adapter for the `by lp` tactic registry.
Zero native deps, zero subprocess calls. Self-registers with the
[`kim-em/lp-tactic`](https://github.com/kim-em/lp-tactic) registry
under priority 100 ("pure tier") on import.

The point is to let a downstream user get `by lp` working with a
single `import` and zero install steps — no SoPlex, no Boost, no
GMP. This is the backend for CI lanes and demos, not for
production solves: the verifier consumes exact rationals (`Rat`),
so the simplex runs on arbitrary-precision arithmetic the whole
way through. Expect performance to be poor on anything beyond
toy LPs. Use
[`kim-em/lp-backend-soplex-ffi`](https://github.com/kim-em/lp-backend-soplex-ffi)
for production.

## Quickstart

```lean
require LPBackendPure from git
  "https://github.com/kim-em/lp-backend-pure" @ "main"
```

```lean
import LPTactic
import LPBackendPure  -- registers "pure" at priority 100

-- No system deps required; this works in a fresh container with
-- only Lean installed.
example (a b : Rat) (_ : 2 * a + b ≤ 5) (_ : a - b ≤ 1) :
    3 * a ≤ 6 := by lp
```

## Status

The backend runs a tableau-based primal simplex on `Rat` with
Bland's anti-cycling rule, and the produced certificates re-verify
under [`kim-em/lp-verify`](https://github.com/kim-em/lp-verify).
The first-cut scope is still deliberately small:

- Upper-only rows (every row is `(none, some hi)`).
- Arbitrary column-bound shapes, preprocessed into nonnegative
  standard-form variables before simplex.
- Primal-feasible starting basis after preprocessing (every transformed
  row rhs is `≥ 0`).

Anything outside that — equality rows, ranged constraints, or negative
right-hand sides after preprocessing — is rejected with a structured
`SolveError.bridge` carrying an actionable message. Coverage will grow
incrementally; two-phase / Big-M is the next step.

Maximisation is handled by canonicalising to minimisation. The
certificate is against the canonical (min) problem, matching
`Soplex.Verify.IsOptimal`. `Solution.objective` is restored to
the caller's original sense.

## Layout

```
LPBackendPure.lean         # top-level import
LPBackendPure/
  Backend.lean             # LPBackend value, probe, solveExact wrapper
  Simplex.lean             # primal simplex on Rat with Bland's rule
LPBackendPureTest/
  Simplex.lean             # behavioral tests; re-verifies certificates
  Runner.lean              # `lake test` entry point
```

The backend lives under `namespace Soplex.Backend.Pure`, mirroring
the other backend repos.

## Licence

[Apache License 2.0](./LICENSE).
