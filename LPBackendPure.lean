/-
  Top-level entry point for `LPBackendPure`.

  Self-registers the pure-Lean backend with the `lp-tactic`
  registry on import.
-/
module

public import LPBackendPure.Backend

@[expose] public section
