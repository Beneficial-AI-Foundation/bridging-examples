import BridgingExamples.ProbSmoke.Spec
import BridgingExamples.ProbSmoke.Crypto
import Common.Correspondence
import Common.Metadata

/-! Randomness as entropy in the generator state. -/

namespace prob_smoke.Entropy.Bridge

open Aeneas Aeneas.Std BridgingExamples

/-- Let:
* `rngCore` be an implementation of the generator trait `rand_core.RngCore`, with state type `R`;
* `states` be a family of distributions on `R`: `states n` is the distribution of the generator
  state for the Crypto state `n`.

Assumption: for all `n` and every buffer of length `k`, `fill_bytes` from a state drawn from
`states (n + k)` has the distribution of `Crypto.fill_bytes` from `n + k`, with its Crypto state
`n` replaced by a state drawn from `states n`. So a state drawn from `states n` has at least `n`
bytes of entropy. -/
@[assumption_for rand_core.RngCore.fill_bytes]
def fill_bytes_assumption {R : Type} (rngCore : rand_core.RngCore R)
    (states : ℕ → ProbComp R) : Prop :=
  ∀ (n : ℕ) (buffer : Slice U8),
    (do
      let state ← states (n + buffer.length)
      pure (rngCore.fill_bytes state buffer))
    =ᵈ
    (do
      let (m, filled) ← Crypto.fill_bytes (n + buffer.length) buffer
      let state ← states m
      pure (Result.ok (state, filled)))

/-- Let:
* `rngCore` be an implementation of the generator trait `rand_core.RngCore`, with state type `R`;
* `states` be a family of distributions on `R`: `states n` is the distribution of the generator
  state for the Crypto state `n`.

Assumption: `fill_bytes_assumption rngCore states`.

Bridge: for all `n` and every buffer of length `k`, `prob_smoke.fill_random` from a state drawn
from `states (n + k)` has the distribution of `Crypto.fill_random` from `n + k`, with its Crypto
state `n` replaced by a state drawn from `states n`. -/
theorem fill_random_bridge {R : Type} (rngCore : rand_core.RngCore R) (states : ℕ → ProbComp R)
    (h : fill_bytes_assumption rngCore states) (buffer : Slice U8) (n : ℕ) :
    (do
      let state ← states (n + buffer.length)
      pure (prob_smoke.fill_random rngCore state buffer))
    =ᵈ
    (do
      let (m, filled) ← Crypto.fill_random (n + buffer.length) buffer
      let state ← states m
      pure (Result.ok (state, filled))) := by
  simp only [Spec.fill_random_spec, Crypto.fill_random]
  exact h n buffer

end prob_smoke.Entropy.Bridge
