import BridgingExamples.ProbSmoke.Aeneas
import Common.Byte

namespace prob_smoke.Effect.Crypto

open Aeneas.Std

/-- `length` uniform bytes. -/
def rand_core.RngCore.fill_bytes (length : ℕ) : ProbComp (List.Vector U8 length) :=
  uniformSample (List.Vector U8 length)

/-- `length` bytes drawn with `fill_bytes`. -/
def fill_random (length : ℕ) : ProbComp (List.Vector U8 length) :=
  rand_core.RngCore.fill_bytes length

end prob_smoke.Effect.Crypto
