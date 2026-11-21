import BridgingExamples.ProbSmoke.Spec
import BridgingExamples.ProbSmoke.Crypto
import Common.Correspondence
import Common.Metadata

/-! Randomness as entropy in the generator state. -/

namespace prob_smoke.Entropy.Bridge

open Aeneas Aeneas.Std BridgingExamples

/-- Let:
* `rngCore` be an implementation of the generator trait `rand_core.RngCore`, with state type `R`;
* `statesRng` be a family of distributions on `R`: `statesRng n` is the distribution of the
  generator state when `n` bytes can still be drawn.

Assumption: for all `n` and every buffer of length `k`, `fill_bytes` from a state drawn from
`statesRng (n + k)` has the distribution of `Crypto.fill_bytes` from `n + k`, with the returned
number `n` replaced by a state drawn from `statesRng n`. So a state drawn from `statesRng n` has at
least `n` bytes of entropy. -/
@[assumption_for rand_core.RngCore.fill_bytes]
def fill_bytes_assumption {R : Type} (rngCore : rand_core.RngCore R)
    (statesRng : ℕ → ProbComp R) : Prop :=
  ∀ (n : ℕ) (buffer : Slice U8),
    (do
      let stateRng ← statesRng (n + buffer.length)
      pure (rngCore.fill_bytes stateRng buffer))
    =ᵈ
    (do
      let (m, filled) ← Crypto.fill_bytes (n + buffer.length) buffer
      let stateRng ← statesRng m
      pure (Result.ok (stateRng, filled)))

/-- Let:
* `rngCore` be an implementation of the generator trait `rand_core.RngCore`, with state type `R`;
* `statesRng` be a family of distributions on `R`: `statesRng n` is the distribution of the
  generator state when `n` bytes can still be drawn.

Bridge: for all `n` and every buffer of length `k`, `prob_smoke.fill_random` from a state drawn
from `statesRng (n + k)` has the distribution of `Crypto.fill_random` from `n + k`, with the
returned number `n` replaced by a state drawn from `statesRng n`. -/
theorem fill_random_bridge {R : Type} (rngCore : rand_core.RngCore R)
    (statesRng : ℕ → ProbComp R) (h : fill_bytes_assumption rngCore statesRng)
    (buffer : Slice U8) (n : ℕ) :
    (do
      let stateRng ← statesRng (n + buffer.length)
      pure (prob_smoke.fill_random rngCore stateRng buffer))
    =ᵈ
    (do
      let (m, filled) ← Crypto.fill_random (n + buffer.length) buffer
      let stateRng ← statesRng m
      pure (Result.ok (stateRng, filled))) := by
  simp only [Spec.fill_random_spec, Crypto.fill_random]
  exact h n buffer

end prob_smoke.Entropy.Bridge
