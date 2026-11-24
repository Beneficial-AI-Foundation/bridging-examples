import BridgingExamples.ByteMask.Aeneas
import Common.Byte
import Common.Metadata

namespace byte_mask.Entropy.Crypto

open Aeneas.Std BridgingExamples

/-- Ideal model of `fill_bytes`: when `n` bytes can still be drawn, it fills `buffer` with
uniform bytes and returns the new number `n - buffer.length`. -/
@[crypto_for rand_core.RngCore.fill_bytes]
def fill_bytes (n : ℕ) (buffer : Slice U8) : ProbComp (ℕ × Slice U8) := do
  let bytes ← $ᵗ (List.Vector U8 buffer.length)
  pure (n - buffer.length, sliceOfVector buffer bytes)

/-- Ideal model of `mask`: when `n` bytes can still be drawn, it fills the one-byte buffer
`[0u8; 1]` with `fill_bytes` and returns the pad, `value ^^^ pad` and the number of bytes that
can still be drawn after that. -/
def mask (n : ℕ) (value : U8) : ProbComp ((U8 × U8) × ℕ) := do
  let (m, filled) ← fill_bytes n (Array.repeat 1#usize 0#u8).to_slice
  let pad := filled[0]!
  pure ((pad, value ^^^ pad), m)

/-- Ideal model of `unmask`: returns `masked ^^^ pad`. -/
def unmask (pad masked : U8) : ProbComp U8 := pure (masked ^^^ pad)

end byte_mask.Entropy.Crypto
