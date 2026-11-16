import BridgingExamples.ProbSmoke.Spec
import BridgingExamples.ProbSmoke.Crypto
import Common.Correspondence
import Common.Oracle.Entropy

/-! Bridge for `fill_random`, with the generator state as a source of entropy -/

namespace prob_smoke.Entropy.Bridge

open Aeneas Aeneas.Std BridgingExamples

/-- Let:
* `inst` be an implementation of the generator trait `rand_core.RngCore`, with state type `R`;
* `states` be a family of distributions on `R`, indexed by a natural number `n`.

Assumption: for all `n` and every buffer of length `k`, starting from a state drawn from
`states (n + k)`, `fill_bytes` fills the buffer with `k` uniform bytes and, independently, leaves
a state drawn from `states n`. This is `EntropyRng inst.fill_bytes states`
(`fill_bytes_assumption_iff_entropyRng`). -/
def rand_core.RngCore.fill_bytes_assumption {R : Type} (inst : rand_core.RngCore R)
    (states : ℕ → ProbComp R) : Prop :=
  ∀ (n : ℕ) (buffer : Slice U8),
    (do let state ← states (n + buffer.length)
        pure (inst.fill_bytes state buffer)) =ᵈ
    (do let bytes ← Crypto.rand_core.RngCore.fill_bytes buffer.length
        let state ← states n
        pure (Result.ok (state, sliceOfVector buffer bytes)))

/-- `fill_bytes_assumption inst states` holds if and only if `EntropyRng inst.fill_bytes states`. -/
theorem fill_bytes_assumption_iff_entropyRng {R : Type} (inst : rand_core.RngCore R)
    (states : ℕ → ProbComp R) :
    rand_core.RngCore.fill_bytes_assumption inst states ↔
      BridgingExamples.Oracle.EntropyRng inst.fill_bytes states :=
  Iff.rfl

/-- Let:
* `inst` be an implementation of the generator trait `rand_core.RngCore`, with state type `R`;
* `states` be a family of distributions on `R`, indexed by a natural number `n`.

Assumption: `rand_core.RngCore.fill_bytes_assumption inst states`.

Bridge: for all `n` and every buffer of length `k`, starting from a state drawn from
`states (n + k)`, `fill_random` fills the buffer with the bytes of `Crypto.fill_random k` and,
independently, leaves a state drawn from `states n`. -/
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
