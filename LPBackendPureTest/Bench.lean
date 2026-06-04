/-
  Throwaway perf benchmark for the pure-Lean simplex.

  Builds dense `n × n` LPs with random `aᵢⱼ ∈ {1/2, 2/3, 3/5, 1, 3/2}`,
  random `cⱼ`, all `xⱼ ≥ 0`, half the rows sign-flipped (negative rhs,
  exercising the phase 1 startup). Times `Simplex.solve` at a few sizes.

  Run via `lake exe simplex-bench`.
-/

import LPBackendPure

namespace LPBackendPureTest.Bench

open LP

/-- Tiny deterministic LCG so we don't pull in a randomness dep. -/
private structure Rng where
  state : UInt64
  deriving Inhabited

private def Rng.next (r : Rng) : Rng × UInt64 :=
  let s := r.state * 6364136223846793005 + 1442695040888963407
  ({ state := s }, s)

private def Rng.nat (r : Rng) (bound : Nat) : Rng × Nat :=
  let (r', u) := r.next
  (r', u.toNat % bound)

private def coeffPool : Array Rat := #[1/2, 2/3, 3/5, 1, 3/2]

/-- Build a dense `n × n` LP. Half the rows are flipped to negative
    rhs, which forces the phase 1 startup path. -/
private def mkProblem (n : Nat) : Problem n n := Id.run do
  let mut rng : Rng := { state := UInt64.ofNat (n * 2654435761) }
  let mut a : Array (Fin n × Fin n × Rat) := Array.mkEmpty (n * n)
  let mut rowSum : Array Rat := Array.replicate n 0
  for i in [:n] do
    for j in [:n] do
      let (r', k) := rng.nat coeffPool.size
      rng := r'
      let v := coeffPool[k]!
      if hi : i < n then
        if hj : j < n then
          a := a.push (⟨i, hi⟩, ⟨j, hj⟩, v)
      rowSum := rowSum.set! i (rowSum[i]! + v)
  let mut c : Array Rat := Array.mkEmpty n
  for _ in [:n] do
    let (r', k) := rng.nat coeffPool.size
    rng := r'
    c := c.push (-coeffPool[k]!)
  let cVec : Vector Rat n := Vector.ofFn (fun j => c[j.val]!)
  -- Row `i` rhs: even rows are upper bounds at `rowSum + 1`; odd rows
  -- are lower bounds at `rowSum / 2`. After preprocessing the odd rows
  -- become `(-a) · x ≤ -rowSum/2`, which is the negative-rhs path that
  -- triggers phase 1.
  let rb : Vector (Option Rat × Option Rat) n := Vector.ofFn fun i =>
    let base := rowSum[i.val]!
    if i.val % 2 = 0 then (none, some (base + 1))
    else (some (base / 2), none)
  let cb : Vector (Option Rat × Option Rat) n :=
    Vector.replicate n (some 0, none)
  pure { c := cVec, objOffset := 0, a := a,
         rowBounds := rb, colBounds := cb }

private def timeMs (act : IO α) : IO (α × Nat) := do
  let t0 ← IO.monoMsNow
  let r ← act
  let t1 ← IO.monoMsNow
  pure (r, t1 - t0)

private partial def loop (p : Problem n n) (reps : Nat) (acc : String) :
    IO String :=
  match reps with
  | 0 => pure acc
  | k + 1 =>
    match Backend.Pure.Simplex.solve {} p with
    | .ok sol => loop p k s!"{repr sol.status}, obj = {sol.objective}"
    | .error _ => loop p k "error"

private def runOne (n : Nat) (reps : Nat := 1) : IO Unit := do
  let p := mkProblem n
  let (acc, ms) ← timeMs (loop p reps "")
  IO.println s!"n = {n} (×{reps}): {ms} ms  [{acc}]"
  (← IO.getStdout).flush

def runAll : IO Unit := do
  -- Reps chosen so each row of output is ≈ 0.5–5s on the baseline.
  runOne 8  100
  runOne 16 20
  runOne 24 5
  runOne 32 2
  runOne 48 1
  runOne 64 1

end LPBackendPureTest.Bench

def main : IO Unit := LPBackendPureTest.Bench.runAll
