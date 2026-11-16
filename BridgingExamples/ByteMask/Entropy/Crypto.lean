import BridgingExamples.ByteMask.Aeneas
import Common.Byte

namespace byte_mask.Entropy.Crypto

open Aeneas.Std

/-- `length` uniform bytes. -/
def rand_core.RngCore.fill_bytes (length : ℕ) : ProbComp (List.Vector U8 length) :=
  uniformSample (List.Vector U8 length)

/-- Masking algorithm: draws a one-byte pad and returns it together with `value ^^^ pad`. -/
def mask (value : U8) : ProbComp (U8 × U8) := do
  let bytes ← rand_core.RngCore.fill_bytes 1
  let pad := bytes.get 0
  pure (pad, value ^^^ pad)

/-- Unmasking algorithm: returns `masked ^^^ pad`. -/
def unmask (pad masked : U8) : ProbComp U8 := pure (masked ^^^ pad)

end byte_mask.Entropy.Crypto
