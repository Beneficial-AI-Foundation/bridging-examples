import BridgingExamples.ByteMask.Aeneas
import Common.Byte
import VCVio.OracleComp.ProbComp.Basic

namespace byte_mask.Crypto

open Aeneas.Std

/-- Mask `v` with a uniform pad. Return the pad and the masked byte. -/
def mask (v : U8) : ProbComp (U8 × U8) := do
  let pad ← $ᵗ U8
  pure (pad, v ^^^ pad)

/-- Remove the pad from a masked byte. -/
def unmask (pad masked : U8) : ProbComp U8 := pure (masked ^^^ pad)

end byte_mask.Crypto
