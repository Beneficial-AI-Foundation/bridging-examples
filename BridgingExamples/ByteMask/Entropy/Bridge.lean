import BridgingExamples.ByteMask.Entropy.Spec
import BridgingExamples.ByteMask.Entropy.Crypto
import Common.Correspondence
import Common.Metadata

/-! Randomness as entropy in the generator state. -/

namespace byte_mask.Entropy.Bridge

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

Bridge theorem: under the Spec assumption `Spec.fill_bytes_assumption rngCore` and the bridge
assumption `fill_bytes_assumption rngCore statesRng`, for all `n`, from a state drawn from
`statesRng (n + 1)`, `byte_mask.mask`
* returns a uniform pad and the value masked with it, as `Crypto.mask` does;
* returns a state drawn from `statesRng n`, independent of the pad. -/
theorem mask_bridge {R : Type} (rngCore : rand_core.RngCore R) (statesRng : ℕ → ProbComp R)
    (hspec : Spec.fill_bytes_assumption rngCore) (h : fill_bytes_assumption rngCore statesRng)
    (value : U8) (n : ℕ) :
    (do
      let stateRng ← statesRng (n + 1)
      pure (byte_mask.mask rngCore stateRng value))
    =ᵈ
    (do
      let (masked, m) ← Crypto.mask (n + 1) value
      let stateRng ← statesRng m
      pure (Result.ok (masked, stateRng))) := by
  -- The one-byte buffer that `byte_mask.mask` and `Crypto.mask` pass to `fill_bytes`.
  set buffer := (Array.repeat 1#usize 0#u8).to_slice with hbuffer
  have hlen : buffer.length = 1 := by rw [hbuffer, Array.length_to_slice]; rfl
  -- By the contract and `Spec.mask_spec`, `byte_mask.mask` is a function of the result of its
  -- `fill_bytes` call.
  have hmask : ∀ stateRng, byte_mask.mask rngCore stateRng value =
      rngCore.fill_bytes stateRng buffer >>= fun filled =>
        Result.ok ((filled.2.val[0]!, value ^^^ filled.2.val[0]!), filled.1) := by
    intro stateRng
    obtain ⟨stateRng', filled, hfill, hlength⟩ := hspec stateRng buffer
    obtain ⟨pad, hpad⟩ := List.length_eq_one_iff.mp (hlength.trans hlen)
    rw [Spec.mask_spec rngCore stateRng stateRng' value pad filled hfill hpad, hfill]
    simp [hpad]
  simp only [hmask, Crypto.mask, ← hbuffer]
  rw [show n + 1 = n + buffer.length by rw [hlen]]
  refine (bind_call (h n buffer) _).trans ?_
  simp only [Crypto.fill_bytes, bind_assoc, pure_bind, bind_tc_ok, Slice.getElem!_Nat_eq,
    EvalDistEq.refl]

/-- `byte_mask.unmask` returns what `Crypto.unmask` returns. -/
theorem unmask_bridge (pad masked : U8) :
    (pure (byte_mask.unmask pad masked) : ProbComp _)
    =ᵈ
    (do
      let value ← Crypto.unmask pad masked
      pure (Result.ok value)) :=
  bridge_of_spec (Spec.unmask_spec pad masked)

end byte_mask.Entropy.Bridge
