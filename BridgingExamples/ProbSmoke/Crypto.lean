import BridgingExamples.ProbSmoke.Aeneas
import Common.Byte
import Common.Metadata

namespace prob_smoke.Crypto

open Aeneas.Std BridgingExamples

/-- `buffer` filled with uniform bytes. -/
@[crypto_for rand_core.RngCore.fill_bytes]
def fill_bytes (buffer : Slice U8) : ProbComp (Slice U8) :=
  uniformBytes buffer

/-- `buffer` filled with `fill_bytes`. -/
def fill_random (buffer : Slice U8) : ProbComp (Slice U8) :=
  fill_bytes buffer

end prob_smoke.Crypto
