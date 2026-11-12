import BridgingExamples.Smoke.Aeneas

namespace smoke.Distributional.Spec

open Aeneas Aeneas.Std

@[step]
theorem identity_byte_spec (x : U8) : identity_byte x ⦃ y => y = x ⦄ := by
  simp [identity_byte]

end smoke.Distributional.Spec
