import BridgingExamples.Smoke.Direct.Spec
import BridgingExamples.Smoke.Direct.Crypto
import Common.Byte

/-! Equality with a model on Fin 256, from an equational specification. -/

namespace smoke.Direct.Bridge

open Aeneas.Std BridgingExamples

theorem identity_byte_bridge (x : U8) :
    (pure (identity_byte x) : ProbComp (Result U8)) =
    (fun y => Result.ok (modelToByte y)) <$> Crypto.identity_byte (byteToModel x) := by
  simp [Spec.identity_byte_spec, Crypto.identity_byte]

end smoke.Direct.Bridge
