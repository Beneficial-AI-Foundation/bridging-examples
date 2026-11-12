import BridgingExamples.Smoke.Aeneas

namespace smoke.Direct.Spec

open Aeneas.Std

theorem identity_byte_spec (x : U8) : identity_byte x = .ok x := rfl

end smoke.Direct.Spec
