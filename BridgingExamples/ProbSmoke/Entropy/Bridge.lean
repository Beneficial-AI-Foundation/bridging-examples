import BridgingExamples.ProbSmoke.Spec
import BridgingExamples.ProbSmoke.Crypto
import Common.Correspondence

/-! Randomness as entropy in the generator state. -/

namespace prob_smoke.Entropy.Bridge

open Aeneas Aeneas.Std BridgingExamples

/-- Let:
* `inst` be an implementation of the generator trait `rand_core.RngCore`, with state type `R`;
* `states` be a family of distributions on `R`, indexed by a natural number `n`.

Assumption: for all `n` and every buffer of length `k`, starting from a state drawn from
`states (n + k)`, `fill_bytes` fills the buffer with `k` uniform bytes and leaves a state drawn
from `states n`. So a state drawn from `states n` has at least `n` bytes of entropy. -/
def rand_core.RngCore.fill_bytes_assumption {R : Type} (inst : rand_core.RngCore R)
    (states : ℕ → ProbComp R) : Prop :=
  ∀ (n : ℕ) (buffer : Slice U8),
    (do let state ← states (n + buffer.length)
        pure (inst.fill_bytes state buffer)) =ᵈ
    (do let bytes ← Crypto.rand_core.RngCore.fill_bytes buffer.length
        let state ← states n
        pure (Result.ok (state, sliceOfVector buffer bytes)))

/-- Let:
* `inst` be an implementation of the generator trait `rand_core.RngCore`, with state type `R`;
* `states` be a family of distributions on `R`, indexed by a natural number `n`.

Assumption: `rand_core.RngCore.fill_bytes_assumption inst states`.

Bridge: for all `n` and every buffer of length `k`, starting from a state drawn from
`states (n + k)`, `fill_random` fills the buffer with the bytes of `Crypto.fill_random k` and
leaves a state drawn from `states n`. -/
theorem fill_random_bridge {R : Type} (inst : rand_core.RngCore R) (states : ℕ → ProbComp R)
    (h : rand_core.RngCore.fill_bytes_assumption inst states) (buffer : Slice U8) (n : ℕ) :
    (do let state ← states (n + buffer.length)
        pure (fill_random inst state buffer)) =ᵈ
    (do let bytes ← Crypto.fill_random buffer.length
        let state ← states n
        pure (Result.ok (state, sliceOfVector buffer bytes))) := by
  simp only [Spec.fill_random_spec, Crypto.fill_random]
  exact h n buffer

end prob_smoke.Entropy.Bridge
