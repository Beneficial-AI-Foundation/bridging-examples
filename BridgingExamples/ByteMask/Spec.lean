import BridgingExamples.ByteMask.Aeneas
import Common.Result
import Common.Metadata
import Common.Oracle.Rng

namespace byte_mask.Spec

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle

/-- The one-byte buffer that `mask` passes to `fill_bytes`. -/
def padBuf : Slice U8 := (Array.repeat 1#usize 0#u8).to_slice

theorem padBuf_length : padBuf.length = 1 := by
  simp only [padBuf, Slice.length, Array.val_to_slice, Aeneas.Std.Array.length_eq]; rfl

/-- The stateless generator whose `fill_bytes` returns `b`. Its other methods fail, and `mask`
does not call them. -/
def constRng (b : Slice U8) : rand_core.RngCore Unit where
  next_u32 _ := Result.fail .panic
  next_u64 _ := Result.fail .panic
  fill_bytes := constFill b

/-- `maskRest v b`: the extracted `mask` on `v`, with `b` as the answer of `fill_bytes`. -/
def maskRest (v : U8) (b : Slice U8) : Result (U8 × U8) := do
  let (p, _) ← mask (constRng b) () v
  Result.ok p

/-- For every generator `inst` and state `rng`, `mask inst rng v` calls
`inst.fill_bytes rng padBuf`, then runs `maskRest` on the answer, failures included. -/
theorem mask_eq {R : Type} (inst : rand_core.RngCore R) (rng : R) (v : U8) :
    mask inst rng v = Aeneas.Std.bind (inst.fill_bytes rng padBuf) fun q =>
      Aeneas.Std.bind (maskRest v q.2) fun p => Result.ok (p, q.1) := by
  simp only [maskRest, mask, constRng, constFill, lift, Array.to_slice_mut, padBuf,
    Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok, uncurry_eq]

/-- If `b` is the one byte `x`, then `maskRest v b` returns the pad `x` and `v ^^^ x`. -/
theorem maskRest_of_val (v x : U8) (b : Slice U8) (hb : b.val = [x]) :
    maskRest v b = Result.ok (x, v ^^^ x) := by
  simp only [maskRest, mask, constRng, constFill, lift, Array.to_slice_mut,
    Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok, uncurry_eq]
  simp [Array.from_slice, Array.index_usize, hb]

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
