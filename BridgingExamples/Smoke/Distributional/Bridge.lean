import BridgingExamples.Smoke.Distributional.Spec
import BridgingExamples.Smoke.Distributional.Crypto
import Common.Correspondence

/-! Equality in distribution with a model on U8, from a postcondition specification. -/

namespace smoke.Distributional.Bridge

open Aeneas.Std BridgingExamples

theorem identity_byte_bridge (x : U8) :
    (pure (identity_byte x) : ProbComp _) =ᵈ
    (do let y ← Crypto.identity_byte x
        pure (Result.ok y)) :=
  bridge_of_spec (Spec.identity_byte_spec x)

end smoke.Distributional.Bridge
