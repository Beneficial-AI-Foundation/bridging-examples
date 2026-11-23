import BridgingExamples.ByteMask.Pad
import Common.Oracle.Rng

/-!
# `mask` as an oracle program

The lemmas behind `mask_bridge` in `Bridge.lean`. `maskProg` is the extracted `mask` with its call
to `fill_bytes` replaced by an oracle query. A generator or the Crypto `fill_bytes` can then answer
the query.
-/

namespace byte_mask.Oracle.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle byte_mask.Spec byte_mask.Pad
  OracleSpec OracleComp

/-- `mask` as an oracle program: one query for `padBuf`, then `maskRest` on the answer. -/
def maskProg (v : U8) : OracleComp FillSpec (Result (U8 × U8)) := do
  let b ← (liftM (FillSpec.query padBuf) : OracleComp FillSpec _)
  return maskRest v b

/-- For every generator `inst` and state `rng`, `mask inst rng v` is `maskProg v` run with
`inst.fill_bytes` from `rng`, final state and failures included. -/
theorem mask_eq_prog {R : Type} (inst : rand_core.RngCore R) (rng : R) (v : U8) :
    mask inst rng v = runProg inst.fill_bytes (maskProg v) rng := by
  rw [maskProg, runProg_query, mask_eq]

/-- `maskProg v` asks for at most one byte. -/
theorem maskProg_byteBound (v : U8) : ByteBound (maskProg v) 1 := by
  simp [ByteBound, maskProg, padBuf_length]

/-- Run with `unifImpl`, `maskProg v` has the distribution of `Result.ok <$> Crypto.mask v`. -/
theorem maskProg_bridge (v : U8) :
    simulateQ unifImpl (maskProg v) =ᵈ
    (do let y ← Crypto.mask v
        pure (Result.ok y)) := by
  have e : simulateQ unifImpl (maskProg v) =
      (do let w ← $ᵗ (List.Vector U8 padBuf.length)
          pure (maskRest v (sliceOfVector padBuf w))) := by
    simp [maskProg, unifImpl]
    rfl
  rw [e]
  exact maskRest_fill_bytes v pure

end byte_mask.Oracle.Bridge
