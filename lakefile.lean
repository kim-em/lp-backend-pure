import Lake
open Lake DSL

/-! # `LPBackendPure` build configuration

  Pure-Lean LP backend: zero native deps, zero subprocess calls.
  Self-registers with the `lp-tactic` registry under priority 100
  ("pure tier") on import.

  This is the zero-deps backend for CI and demos. Performance is
  expected to be poor — the verifier needs exact rationals
  (`Rat`), not Floats, so the simplex runs on arbitrary-precision
  arithmetic the whole way through. The point is to let users get
  `by lp` working with a single `import` and zero install steps.
-/

require LPCore from git "https://github.com/kim-em/lp-core" @
  "60fca2313ea3be14f578258dc6390f2fa07b26e7"

require LPTactic from git "https://github.com/kim-em/lp-tactic" @
  "eacb9b2270a9e9a810536f2c04e4f4ab7905dadf"

package LPBackendPure

@[default_target]
lean_lib LPBackendPure where
  roots := #[`LPBackendPure]
  globs := #[`LPBackendPure, `LPBackendPure.Simplex, `LPBackendPure.Backend]
