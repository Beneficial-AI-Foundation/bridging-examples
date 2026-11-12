import BridgingExamples.ByteMask.Aeneas
import Common.Result

namespace byte_mask.Spec

open Aeneas Aeneas.Std BridgingExamples

/-- `unmask pad masked` returns `masked ^^^ pad`. -/
@[step]
theorem unmask_spec (pad masked : U8) : unmask pad masked ⦃ r => r = masked ^^^ pad ⦄ := by
  simp [unmask]

/-- Unmasking with the pad gives back the value. -/
theorem unmask_mask (pad v : U8) : unmask pad (v ^^^ pad) = Result.ok v := by
  simp only [unmask]
  congr 1
  apply UScalar.eq_of_val_eq
  simp

end byte_mask.Spec
