import BridgingExamples.ByteMask.Aeneas
import Common.Result
import Common.Metadata

namespace byte_mask.Spec

open Aeneas Aeneas.Std BridgingExamples

/-- The one-byte buffer that `mask` passes to `fill_bytes`. -/
def padBuf : Slice U8 := (Array.repeat 1#usize 0#u8).to_slice

theorem padBuf_length : padBuf.length = 1 := by
  simp only [padBuf, Slice.length, Array.val_to_slice, Aeneas.Std.Array.length_eq]; rfl

/-- If `fill_bytes` fills `padBuf` with the one byte `x` and returns the state `rng1`, then
`mask` returns the pad `x`, the masked byte `v ^^^ x` and the state `rng1`. -/
@[spec_for mask]
theorem mask_spec {R : Type} (inst : rand_core.RngCore R) (rng rng1 : R) (v x : U8)
    (b : Slice U8) (hfill : inst.fill_bytes rng padBuf = Result.ok (rng1, b))
    (hb : b.val = [x]) :
    mask inst rng v = Result.ok ((x, v ^^^ x), rng1) := by
  simp only [padBuf] at hfill
  simp only [mask, lift, Array.to_slice_mut, Aeneas.Std.bind_ok, uncurry_eq, hfill]
  simp [Array.from_slice, Array.index_usize, hb]

/-- `unmask pad masked` returns `masked ^^^ pad`. -/
@[step]
theorem unmask_spec (pad masked : U8) : unmask pad masked ⦃ r => r = masked ^^^ pad ⦄ := by
  simp [unmask]

/-- Unmasking with the pad gives back the value. -/
@[spec_for unmask]
theorem unmask_mask (pad v : U8) : unmask pad (v ^^^ pad) = Result.ok v := by
  simp only [unmask]
  congr 1
  apply UScalar.eq_of_val_eq
  simp

end byte_mask.Spec
