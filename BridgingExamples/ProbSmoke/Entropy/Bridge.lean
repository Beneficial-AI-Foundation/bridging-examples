import BridgingExamples.ProbSmoke.Spec
import BridgingExamples.ProbSmoke.Entropy.Crypto
import Common.Correspondence
import Common.Metadata

/-! Randomness as entropy in the generator state. -/

namespace prob_smoke.Entropy.Bridge

open Aeneas Aeneas.Std BridgingExamples

/-- Let:
* `rngCore` be an implementation of the generator trait `rand_core.RngCore`, with state type `R`;
* `statesRng` be a family of distributions on `R`: `statesRng n` is the distribution of the
  generator state when `n` bytes can still be drawn.

Bridge assumption: for all `n` and every buffer of length `k`, from a state drawn from
`statesRng (n + k)`, `rngCore.fill_bytes`
* fills the buffer with uniform bytes, as `Crypto.fill_bytes` does;
* returns a state drawn from `statesRng n`, independent of those bytes.

So a state drawn from `statesRng n` has at least `n` bytes of entropy. -/
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

Bridge theorem: for all `n` and every buffer of length `k`, from a state drawn from
`statesRng (n + k)`, `prob_smoke.fill_random`
* fills the buffer with uniform bytes, as `Crypto.fill_random` does;
* returns a state drawn from `statesRng n`, independent of those bytes. -/
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
