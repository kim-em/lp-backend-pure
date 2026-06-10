# LPBackendPure

[![Lean](https://img.shields.io/badge/Lean-4.31.0--rc1-blue.svg)](./lean-toolchain)
[![License](https://img.shields.io/github/license/leanprover/lp-backend-pure.svg)](./LICENSE)

> **New here? Start at [`leanprover/lp`](https://github.com/leanprover/lp)** — the entry
> point for the `lp` / `maximize` tactics and the verified LP solver. This repository is one
> package of that family: the pure-Lean backend.

Pure-Lean `LPBackend` adapter for the `by lp` tactic registry.
Zero native deps, zero subprocess calls. Self-registers with the
[`leanprover/lp-tactic`](https://github.com/leanprover/lp-tactic) registry
under priority 100 ("pure tier") on import.

The point is to let a downstream user get `by lp` working with a
single `import` and zero install steps — no SoPlex, no Boost, no
GMP. This is the backend for CI lanes and demos, not for
production solves: the verifier consumes exact rationals (`Rat`),
so the simplex runs on arbitrary-precision arithmetic the whole
way through. Expect performance to be poor on anything beyond
toy LPs. Use
[`leanprover/lp-backend-soplex-ffi`](https://github.com/leanprover/lp-backend-soplex-ffi)
for production.

## Quickstart

```lean
require LPBackendPure from git
  "https://github.com/leanprover/lp-backend-pure" @ "main"
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

The backend runs a two-phase tableau-based primal simplex on `Rat`
(Dantzig's rule with a Bland fallback on suspected cycling), and
the produced certificates re-verify under
[`leanprover/lp-verify`](https://github.com/leanprover/lp-verify).
The supported scope now matches the FFI backend on the `by lp`
examples in `LPTest/LP.lean` (see
`LPBackendPureTest/LPParity.lean`):

- Row shapes — `(none, some hi)`, `(some lo, none)`, `(some lo, some hi)`
  (equality or proper range), `(none, none)` — preprocessed into upper-only
  rows.
- Column shapes — free, lower-bounded, upper-only, boxed, negative-lower —
  preprocessed into nonnegative standard-form variables.
- `SolveStatus.optimal`, `SolveStatus.unbounded` (with recession ray),
  and `SolveStatus.infeasible` (with Farkas dual read off phase 1's
  final tableau).

Maximisation is handled by canonicalising to minimisation. The
certificate is against the canonical (min) problem, matching
`LP.Verify.IsOptimal`. `Solution.objective` is restored to
the caller's original sense.

Performance is expected to be poor — this is a dense `Rat` tableau,
no presolve, no sparse data structures. Use the FFI backend in
production; this backend is for CI lanes, demos, and downstream
projects that want `by lp` working with a single `import`.

## Layout

```
LPBackendPure.lean         # top-level import
LPBackendPure/
  Backend.lean             # LPBackend value, probe, solveExact wrapper
  Simplex.lean             # primal simplex on Rat with Bland's rule
LPBackendPureTest/
  Simplex.lean             # behavioral tests; re-verifies certificates
  LPParity.lean            # `by lp` parity sweep against LPTest/LP.lean
  Runner.lean              # `lake test` entry point
```

The backend lives under `namespace LP.Backend.Pure`, mirroring
the other backend repos.

## Licence

[Apache License 2.0](./LICENSE).
