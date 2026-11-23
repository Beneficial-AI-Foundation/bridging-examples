import BridgingExamples.ProbSmoke.Aeneas
import Common.Byte
import Common.Metadata

namespace prob_smoke.Entropy.Crypto

open Aeneas.Std BridgingExamples

/-- Ideal model of `fill_bytes`: when `n` bytes can still be drawn, it fills `buffer` with
uniform bytes and returns the new number `n - buffer.length`. -/
@[crypto_for rand_core.RngCore.fill_bytes]
def fill_bytes (n : ℕ) (buffer : Slice U8) : ProbComp (ℕ × Slice U8) := do
  let bytes ← $ᵗ (List.Vector U8 buffer.length)
  pure (n - buffer.length, Slice.from bytes.val (vector_length_le buffer bytes))

/-- Ideal model of `fill_random`: one call of `fill_bytes`. -/
def fill_random (n : ℕ) (buffer : Slice U8) : ProbComp (ℕ × Slice U8) :=
  fill_bytes n buffer

end prob_smoke.Entropy.Crypto
