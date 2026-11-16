import BridgingExamples.ProbSmoke.Aeneas
import Common.Byte
import Common.Metadata

namespace prob_smoke.Crypto

open Aeneas.Std

/-- `length` uniform bytes. -/
@[crypto_for rand_core.RngCore.fill_bytes]
def fill_bytes (length : ℕ) : ProbComp (List.Vector U8 length) :=
  uniformSample (List.Vector U8 length)

/-- `length` bytes drawn with `fill_bytes`. -/
def fill_random (length : ℕ) : ProbComp (List.Vector U8 length) :=
  fill_bytes length

end prob_smoke.Crypto
