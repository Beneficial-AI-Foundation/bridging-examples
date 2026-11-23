import BridgingExamples.ByteMask.Aeneas
import Common.Byte
import VCVio.OracleComp.ProbComp.Basic

namespace byte_mask.Crypto

open Aeneas.Std

/-- `length` uniform bytes. This is the Crypto counterpart of the generator method `fill_bytes`.
The bridges assume that the extracted `fill_bytes` gives bytes with this distribution. -/
def rand_core.RngCore.fill_bytes (length : ℕ) : ProbComp (List.Vector U8 length) :=
  $ᵗ (List.Vector U8 length)

/-- Mask `v` with a pad. The pad is one byte filled with `fill_bytes`, as in the Rust `mask`.
Return the pad and the masked byte. -/
def mask (v : U8) : ProbComp (U8 × U8) := do
  let bytes ← rand_core.RngCore.fill_bytes 1
  pure (bytes.head, v ^^^ bytes.head)

/-- Remove the pad from a masked byte. -/
def unmask (pad masked : U8) : ProbComp U8 := pure (masked ^^^ pad)

end byte_mask.Crypto
