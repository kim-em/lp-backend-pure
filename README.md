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

Today the backend ships a trivially-passing `probe` and a
placeholder `solveExact` that reports a structured "simplex not
yet wired" error. The revised-simplex implementation in
`LPBackendPure/Simplex.lean` is the follow-up work. Importing the
module today is already meaningful: it registers the backend so
`availableBackends` lists it, and `set_option lp.backend "pure"`
switches dispatch to it (where the error message tells the user
the algorithm is still landing).

Scope of the eventual simplex (deliberately tiny first cut):
- Inequality form only (no equality rows, no ranged constraints).
- Non-negative variables only (no free / bounded columns).
- Primal-feasible starting point only (no two-phase).

Wider coverage will land incrementally as the verifier's existing
test corpus exercises edge cases.

## Layout

```
LPBackendPure.lean         # top-level import
LPBackendPure/
  Backend.lean             # def backend : LPBackend, probe, solveExact
  Simplex.lean             # revised-simplex implementation (TODO)
```

The backend lives under `namespace Soplex.Backend.Pure`, mirroring
the other backend repos.

## Licence

[Apache License 2.0](./LICENSE).
