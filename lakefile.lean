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

require LPCore from git "https://github.com/leanprover/lp-core" @
  "8b6d241bc84e54357aa6628f1b18ff795d53de7e"

require LPTactic from git "https://github.com/leanprover/lp-tactic" @
  "86634295a1fa2b45110a680215e208b16f40cd33"

-- `LPVerify` is only used by the test suite (to re-check
-- certificates the backend produces). It is reachable transitively
-- through `LPTactic`'s lake-manifest, but listing it explicitly
-- keeps the test target's intent obvious.
require LPVerify from git "https://github.com/leanprover/lp-verify" @
  "1131b0a11c683d4833cd735c83157a32952ad3aa"

package LPBackendPure

@[default_target]
lean_lib LPBackendPure where
  roots := #[`LPBackendPure]
  globs := #[`LPBackendPure, `LPBackendPure.Simplex, `LPBackendPure.Backend]

/-- Behavioral tests for the simplex. Build via
    `lake build LPBackendPureTest` or run via `lake test`. -/
lean_lib LPBackendPureTest where
  roots := #[`LPBackendPureTest.Simplex, `LPBackendPureTest.LPParity, `LPBackendPureTest.Runner]

lean_exe «simplex-tests» where
  root := `LPBackendPureTest.Simplex

/-- Throwaway perf benchmark; not run by `lake test`, not part of the
    `LPBackendPureTest` library — its root is reached only via this exe. -/
lean_exe «simplex-bench» where
  root := `LPBackendPureTest.Bench

/-- `lake test` entry point. Runs every test exe. -/
@[test_driver]
lean_exe «test-runner» where
  root := `LPBackendPureTest.Runner
