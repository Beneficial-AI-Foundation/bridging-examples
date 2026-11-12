import BridgingExamples.Smoke.Aeneas

namespace smoke.Spec

open Aeneas Aeneas.Std

@[step]
theorem identity_byte_spec (x : U8) : identity_byte x ⦃ y => y = x ⦄ := by
  simp [identity_byte]

end smoke.Spec
