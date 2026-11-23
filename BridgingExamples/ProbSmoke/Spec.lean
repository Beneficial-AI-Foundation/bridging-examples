import BridgingExamples.ProbSmoke.Aeneas
import Common.Result

namespace prob_smoke.Spec

open Aeneas Aeneas.Std BridgingExamples

/-- `fill_random` makes one `fill_bytes` call and returns its result. -/
theorem fill_random_spec {R : Type} (rngCore : rand_core.RngCore R) (stateRng : R)
    (buffer : Slice U8) :
    fill_random rngCore stateRng buffer = rngCore.fill_bytes stateRng buffer := rfl

end prob_smoke.Spec
