import BridgingExamples.Smoke.Spec
import BridgingExamples.Smoke.Crypto
import Common.Correspondence

namespace smoke.Bridge

open Aeneas.Std BridgingExamples

theorem identity_byte_bridge (x : U8) :
    (pure (identity_byte x) : ProbComp _) =ᵈ
    (do let y ← Crypto.identity_byte x
        pure (Result.ok y)) :=
  bridge_of_spec (Spec.identity_byte_spec x)

end smoke.Bridge
