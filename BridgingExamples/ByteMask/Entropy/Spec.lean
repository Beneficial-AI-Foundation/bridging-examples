import BridgingExamples.ByteMask.Aeneas
import Common.Metadata
import Common.Result

namespace byte_mask.Entropy.Spec

open Aeneas Aeneas.Std BridgingExamples

/-- Let `rngCore` be an implementation of the generator trait `rand_core.RngCore`, with state type
`R`.

Assumption: for every state and every buffer, `fill_bytes` succeeds and returns a buffer of the
same length. -/
@[assumption_for rand_core.RngCore.fill_bytes]
def fill_bytes_assumption {R : Type} (rngCore : rand_core.RngCore R) : Prop :=
  ∀ (state : R) (buffer : Slice U8), ∃ (state' : R) (filled : Slice U8),
    rngCore.fill_bytes state buffer = Result.ok (state', filled) ∧ filled.length = buffer.length

/-- Let `buffer` be the one-byte buffer `[0u8; 1]`. If `fill_bytes` fills `buffer` with the byte
`pad` and leaves the state `state'`, then `mask` returns `(pad, value ^^^ pad)` and `state'`. -/
theorem mask_spec {R : Type} (rngCore : rand_core.RngCore R) (state state' : R) (value pad : U8)
    (filled : Slice U8) :
    let buffer := (Array.repeat 1#usize 0#u8).to_slice
    rngCore.fill_bytes state buffer = Result.ok (state', filled) → filled.val = [pad] →
      mask rngCore state value = Result.ok ((pad, value ^^^ pad), state') := by
  intro buffer hfill hpad
  simp only [buffer] at hfill
  simp only [mask, lift, Array.to_slice_mut, Aeneas.Std.bind_ok, uncurry_eq, hfill]
  simp [Array.from_slice, Array.index_usize, hpad]

/-- `unmask` returns `masked ^^^ pad`. -/
@[step]
theorem unmask_spec (pad masked : U8) :
    unmask pad masked ⦃ value => value = masked ^^^ pad ⦄ := by
  simp [unmask]

end byte_mask.Entropy.Spec
