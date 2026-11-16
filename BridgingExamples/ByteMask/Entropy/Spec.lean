import BridgingExamples.ByteMask.Aeneas
import Common.Result

namespace byte_mask.Entropy.Spec

open Aeneas Aeneas.Std BridgingExamples

/-- `mask` makes one `fill_bytes` call on the one-byte array `pad`, initially zero. It returns
`byte`, the byte written into `pad`, together with `value ^^^ byte`, and the state left by the
call. -/
theorem mask_spec {R : Type} (inst : rand_core.RngCore R) (state : R) (value : U8) :
    mask inst state value =
      (do let pad := Array.repeat 1#usize 0#u8
          let (state, filled) ← inst.fill_bytes state pad.to_slice
          let byte := (pad.from_slice filled)[0]!
          Result.ok ((byte, value ^^^ byte), state)) := by
  unfold mask
  simp only [lift, Array.to_slice_mut, bind_ok, uncurry_eq]
  congr 1
  funext filled
  obtain ⟨state, filled⟩ := filled
  have hbound : (0#usize).val < (Array.from_slice (Array.repeat 1#usize 0#u8) filled).length := by
    simp
  obtain ⟨byte, hbyte, hvalue⟩ := returns (Array.index_usize_spec _ 0#usize hbound)
  simp [hbyte, hvalue]

/-- `unmask` returns `masked ^^^ pad`. -/
@[step]
theorem unmask_spec (pad masked : U8) :
    unmask pad masked ⦃ value => value = masked ^^^ pad ⦄ := by
  simp [unmask]

end byte_mask.Entropy.Spec
