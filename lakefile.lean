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
  "8b694db5f88c65b06714de5488edefd238185f60"

require LPTactic from git "https://github.com/kim-em/lp-tactic" @
  "1f67bd79223e988a7bef32b8c075963f3c32036c"

-- `LPVerify` is only used by the test suite (to re-check
-- certificates the backend produces). It is reachable transitively
-- through `LPTactic`'s lake-manifest, but listing it explicitly
-- keeps the test target's intent obvious.
require LPVerify from git "https://github.com/kim-em/lp-verify" @
  "b53657cc4743764487bbd02b7b333991825e4aec"

package LPBackendPure

@[default_target]
lean_lib LPBackendPure where
  roots := #[`LPBackendPure]
  globs := #[`LPBackendPure, `LPBackendPure.Simplex, `LPBackendPure.Backend]

/-- Behavioral tests for the simplex. Build via
    `lake build LPBackendPureTest` or run via `lake test`. -/
lean_lib LPBackendPureTest where
  roots := #[`LPBackendPureTest.Simplex, `LPBackendPureTest.Runner]

lean_exe «simplex-tests» where
  root := `LPBackendPureTest.Simplex

/-- `lake test` entry point. Runs every test exe. -/
@[test_driver]
lean_exe «test-runner» where
  root := `LPBackendPureTest.Runner
