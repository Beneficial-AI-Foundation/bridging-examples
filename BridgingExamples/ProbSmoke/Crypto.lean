import BridgingExamples.ProbSmoke.Aeneas
import Common.Byte
import Common.Metadata

namespace prob_smoke.Crypto

open Aeneas.Std BridgingExamples

/-- `buffer` filled with uniform bytes, with `n` bytes left before and `n - buffer.length` after. -/
@[crypto_for rand_core.RngCore.fill_bytes]
def fill_bytes (n : ℕ) (buffer : Slice U8) : ProbComp (ℕ × Slice U8) := do
  let filled ← uniformBytes buffer
  pure (n - buffer.length, filled)

/-- `buffer` filled with `fill_bytes`, with `n` bytes left before. -/
def fill_random (n : ℕ) (buffer : Slice U8) : ProbComp (ℕ × Slice U8) :=
  fill_bytes n buffer

end prob_smoke.Crypto
