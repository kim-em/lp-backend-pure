/-
  Parity tests for the `by lp` tactic against the pure-Lean
  backend. Each `example` below mirrors one in `kim-em/soplex`'s
  `SoplexTest/LP.lean`; this file rebuilds them with only
  `LPBackendPure` registered, so a successful compilation proves
  the pure backend handles each case without falling through to
  `SolveError.bridge`.

  Most cases exercise backend code paths (multi-row LPs, ranged
  hypotheses, infeasible Farkas, unbounded ray). A few (closed
  scalar short-circuits, locally `let`-bound scalar) live entirely
  in the tactic and are kept here so the parity sweep tracks
  upstream tactic coverage too.

  Two `SoplexTest/LP.lean` examples (`: False` and `(p : Prop) : p`
  from contradictory hypotheses) are intentionally omitted: the
  pinned `LPTactic` (`f6a72b7`) rejects them before backend
  dispatch with "lp: goal is not an atomic Rat comparison". When
  the pin moves, they should be added.

  This is the file that closes the tracking issue for
  `LPBackendSoplexFFI` ↔ `LPBackendPure` feature parity. If a new
  case lands in `SoplexTest/LP.lean`, it should also land here.
-/

import LPBackendPure
import LPTactic

namespace LPBackendPureTest.LPParity

/-! ## Two-row optimal certificates. -/

example (a b : Rat) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a - b ≤ 1) : 3 * a ≤ 6 := by lp
example (a b : Rat) (_h₁ : 2 * a + b ≤ 2) (_h₂ : a - b ≤ 1) : 3 * a ≤ 3 := by lp
example (a b : Rat) (_h₁ : 2 * a + b ≤ 4) (_h₂ : a - b ≤ 1) : 3 * a ≤ 5 := by lp
example (a b : Rat) (_h₁ : 2 * a + b ≤ 1) (_h₂ : a - b ≤ 1) : 3 * a ≤ 2 := by lp
example (a b : Rat) (_h₁ : 2 * a + b ≤ 3) (_h₂ : a - b ≤ 1) : 3 * a ≤ 4 := by lp
example (a b : Rat) (_h₁ : 2 * a + b ≤ 10) (_h₂ : a - b ≤ 1) : 3 * a ≤ 11 := by lp
example (a b : Rat) (_h₁ : 5 ≥ 2 * a + b) (_h₂ : 1 ≥ a - b) : 6 ≥ 3 * a := by lp

example (n : Nat) (x : Rat) (_hn : 0 ≤ n) (_h : x ≤ 0) : x ≤ 0 := by lp

/-! ## Closed scalar short-circuits (no LP solve). -/

example : (1 : Rat) ≤ 2 := by lp
example : (-3 : Rat) ≤ -3 := by lp
example : (1 : Rat) < 2 := by lp

/-! ## Strict goals from non-strict hypotheses. -/

example (x : Rat) (_h : x ≤ 0) : x < 1 := by lp

/-! ## Half/integer coefficients and one-row simplifications. -/

example (x y : Rat) (_h : (1 / 2 : Rat) * x + y ≤ 1) : x + 2 * y ≤ 2 := by lp
example (x : Rat) (_h : (3 : Rat) * x ≤ 6) : x ≤ 2 := by lp

/-! ## Conjunction in a single hypothesis. -/

example (a : Rat) (_h : a ≤ 0 ∧ 0 ≤ a) : a = 0 := by lp

/-! ## Inconsistent hypotheses (Farkas-dual path). -/

example (x : Rat) (_h₁ : x ≤ 0) (_h₂ : 1 ≤ x) : x = 5 := by lp

/-! ## Unbounded objective: the pure backend produces the same
    `base=[0], ray=[1]` certificate as the FFI backend. -/

/-- error: lp: objective is unbounded above; base=[0], ray=[1] -/
#guard_msgs in
example (x : Rat) : x ≤ 0 := by lp

/-! ## Locally `let`-bound scalar — handled by the tactic, not the
    backend, but worth keeping in the parity sweep. -/

example (x : Rat) (_h : x ≤ 1) : True := by
  let c : Rat := 3
  have : c * x ≤ 3 := by lp
  trivial

/-! ## Multi-variable LPs. -/

example (x₁ x₂ x₃ x₄ : Rat)
    (_h1 : 0 ≤ x₁) (_h2 : 0 ≤ x₂) (_h3 : 0 ≤ x₃) (_h4 : 0 ≤ x₄)
    (_cal  : 3 * x₁ + x₂ + 4 * x₃ + 2 * x₄ ≥ 10)
    (_prot : x₁ + 2 * x₂ + 3 * x₄ ≥ 6)
    (_vit  : x₂ + 2 * x₃ + x₄ ≥ 4) :
    2 * x₁ + 3 * x₂ + x₃ + 4 * x₄ ≥ 5 := by lp

example (a₁ a₂ a₃ b₁ b₂ b₃ : Rat)
    (_n1 : 0 ≤ a₁) (_n2 : 0 ≤ a₂) (_n3 : 0 ≤ a₃)
    (_n4 : 0 ≤ b₁) (_n5 : 0 ≤ b₂) (_n6 : 0 ≤ b₃)
    (_s1 : a₁ + a₂ + a₃ ≤ 10)
    (_s2 : b₁ + b₂ + b₃ ≤ 15)
    (_d1 : a₁ + b₁ ≥ 8) (_d2 : a₂ + b₂ ≥ 9) (_d3 : a₃ + b₃ ≥ 8) :
    2 * a₁ + 3 * a₂ + 4 * a₃ + 5 * b₁ + b₂ + 3 * b₃ ≥ 30 := by lp

example (x y z : Rat)
    (_nx : 0 ≤ x) (_ny : 0 ≤ y) (_nz : 0 ≤ z)
    (_h1 : (1/3 : Rat) * x + (1/5 : Rat) * y + (1/7 : Rat) * z ≤ 1)
    (_h2 : (2/3 : Rat) * x - (1/5 : Rat) * y + (3/7 : Rat) * z ≤ 2)
    (_h3 : -(1/3 : Rat) * x + (4/5 : Rat) * y - (1/7 : Rat) * z ≤ 1) :
    (1/2 : Rat) * x + y + z ≥ 0 := by lp

example (x y _z u v w p q r : Rat)
    (_key₁ : 2 * x + y ≤ 4) (_key₂ : x - y ≤ 1)
    (_n1 : 0 ≤ u) (_n2 : 0 ≤ v) (_n3 : 0 ≤ w)
    (_n4 : 0 ≤ p) (_n5 : 0 ≤ q) (_n6 : 0 ≤ r)
    (_b1 : u ≤ 10) (_b2 : v ≤ 10) (_b3 : w ≤ 10)
    (_b4 : p ≤ 10) (_b5 : q ≤ 10) (_b6 : r ≤ 10)
    (_c1 : u + v + w ≤ 25) (_c2 : p + q + r ≤ 25)
    (_c3 : u + p ≤ 15) (_c4 : v + q ≤ 15) (_c5 : w + r ≤ 15) :
    3 * x ≤ 7 := by lp

end LPBackendPureTest.LPParity
