import BridgingExamples.ByteMask.Entropy.Spec
import BridgingExamples.ByteMask.Entropy.Crypto
import Common.Correspondence

/-! Randomness as entropy in the generator state. -/

namespace byte_mask.Entropy.Bridge

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

Bridge: for all `n`, starting from a state drawn from `states (n + 1)`, `mask` returns what
`Crypto.mask` returns and leaves a state drawn from `states n`. -/
theorem mask_bridge {R : Type} (inst : rand_core.RngCore R) (states : ℕ → ProbComp R)
    (h : rand_core.RngCore.fill_bytes_assumption inst states) (value : U8) (n : ℕ) :
    (do let state ← states (n + 1)
        pure (mask inst state value)) =ᵈ
    (do let masked ← Crypto.mask value
        let state ← states n
        pure (Result.ok (masked, state))) := by
  simp only [Spec.mask_spec, Crypto.mask]
  set zero := Array.repeat 1#usize 0#u8 with hzero
  have hlen : zero.to_slice.length = 1 := by rw [Array.length_to_slice]; rfl
  have hbudget : n + 1 = n + zero.to_slice.length := by rw [hlen]
  rw [hbudget]
  refine (bind_call (h n zero.to_slice) _).trans ?_
  simp only [sliceOfVector, Crypto.rand_core.RngCore.fill_bytes, bind_assoc, pure_bind, bind_tc_ok]
  refine uniformVector_bind_congr hlen _ _ (fun bytes => ?_)
  obtain ⟨list, hlist⟩ := bytes
  obtain ⟨byte, rfl⟩ := List.length_eq_one_iff.mp (hlist.trans hlen)
  simp [List.Vector.head]

/-- `unmask` returns what `Crypto.unmask` returns. -/
theorem unmask_bridge (pad masked : U8) :
    (pure (unmask pad masked) : ProbComp _) =ᵈ
    (do let value ← Crypto.unmask pad masked
        pure (Result.ok value)) :=
  bridge_of_spec (Spec.unmask_spec pad masked)

end byte_mask.Entropy.Bridge
