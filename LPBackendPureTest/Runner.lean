/-
  `lake test` entry point for `kim-em/lp-backend-pure`. Runs every
  test suite in the package; today just `LPBackendPureTest.Simplex`.
-/

import LPBackendPureTest.Simplex

def main : IO UInt32 :=
  LPBackendPureTest.Simplex.main
