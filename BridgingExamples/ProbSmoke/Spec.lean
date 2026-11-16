import BridgingExamples.ProbSmoke.Aeneas
import Common.Result

namespace prob_smoke.Spec

open Aeneas Aeneas.Std BridgingExamples

/-- `fill_random` makes one `fill_bytes` call and returns its result. -/
theorem fill_random_spec {R : Type} (rngCore : rand_core.RngCore R) (state : R)
    (buffer : Slice U8) :
    fill_random rngCore state buffer = rngCore.fill_bytes state buffer := rfl

end prob_smoke.Spec
