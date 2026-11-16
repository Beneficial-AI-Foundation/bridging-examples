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

Assumptions: `Spec.rand_core.RngCore.fill_bytes_assumption inst` and
`rand_core.RngCore.fill_bytes_assumption inst states`.

Bridge: for all `n`, starting from a state drawn from `states (n + 1)`, `mask` returns what
`Crypto.mask` returns and leaves a state drawn from `states n`. -/
theorem mask_bridge {R : Type} (inst : rand_core.RngCore R) (states : ℕ → ProbComp R)
    (hspec : Spec.rand_core.RngCore.fill_bytes_assumption inst)
    (h : rand_core.RngCore.fill_bytes_assumption inst states) (value : U8) (n : ℕ) :
    (do let state ← states (n + 1)
        pure (mask inst state value)) =ᵈ
    (do let masked ← Crypto.mask value
        let state ← states n
        pure (Result.ok (masked, state))) := by
  -- The one-byte buffer that `mask` passes to `fill_bytes`.
  set buffer := (Array.repeat 1#usize 0#u8).to_slice with hbuffer
  have hlen : buffer.length = 1 := by rw [hbuffer, Array.length_to_slice]; rfl
  -- By the contract and `mask_spec`, `mask` is a function of the result of its `fill_bytes` call.
  have hmask : ∀ state, mask inst state value =
      inst.fill_bytes state buffer >>= fun filled =>
        Result.ok ((filled.2.val[0]!, value ^^^ filled.2.val[0]!), filled.1) := by
    intro state
    obtain ⟨state', filled, hfill, hlength⟩ := hspec state buffer
    obtain ⟨pad, hpad⟩ := List.length_eq_one_iff.mp (hlength.trans hlen)
    rw [Spec.mask_spec inst state state' value pad filled hfill hpad, hfill]
    simp [hpad]
  simp only [hmask, Crypto.mask]
  rw [show n + 1 = n + buffer.length by rw [hlen]]
  refine (bind_call (h n buffer) _).trans ?_
  simp only [sliceOfVector, Crypto.rand_core.RngCore.fill_bytes, bind_assoc, pure_bind, bind_tc_ok]
  refine uniformVector_bind_congr hlen _ _ (fun bytes => ?_)
  obtain ⟨list, hlist⟩ := bytes
  obtain ⟨byte, rfl⟩ := List.length_eq_one_iff.mp (hlist.trans hlen)
  simp [List.Vector.get]

/-- `unmask` returns what `Crypto.unmask` returns. -/
theorem unmask_bridge (pad masked : U8) :
    (pure (unmask pad masked) : ProbComp _) =ᵈ
    (do let value ← Crypto.unmask pad masked
        pure (Result.ok value)) :=
  bridge_of_spec (Spec.unmask_spec pad masked)

end byte_mask.Entropy.Bridge
