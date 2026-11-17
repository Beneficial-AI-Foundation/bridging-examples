import BridgingExamples.ByteMask.Spec
import BridgingExamples.ByteMask.Crypto
import Common.Correspondence
import Common.Effect.Random
import Common.Metadata

/-!
# Bridge for `mask`, with the generator as the `random` effect

This bridge needs `aeneas.patch`: an Aeneas `Result` can then sample with `Result.random`. The
extracted `mask` does not change. The bridge has two steps.

1. `mask_eq`: if `inst.fill_bytes` samples with `Result.random` (`RandomFill`), then `mask` is
   equal to `toResult` of the oracle program `maskModel`.
2. `maskModel_bridge`: `maskModel`, run with uniform bytes (`uniformImpl`), has the distribution
   of `Crypto.mask`.

`RandomFill` is the only Lean assumption on the generator. Compare with the Oracle bridge:

- Its equality `mask_eq_prog` holds for every generator, with no assumption, final state
  included. The equality here needs `RandomFill`.
- Its assumption is on the distribution of a sampled state, with a byte budget. Here there is no
  sampled state, no byte budget and no generator built from the answer of a query (`constRng`),
  because the bytes come from the effect.
- Its `mask_bridge` states the distribution of the extracted code. Here only the model has a
  distribution (see `Common/Effect/Random.lean`).
-/

namespace byte_mask.Effect.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Effect byte_mask.Spec OracleSpec
  OracleComp

/-- `mask` as an oracle program: ask for one byte, the pad, and return the pad and the masked
byte. -/
def maskModel (v : U8) : OracleComp RandSpec (U8 × U8) := do
  let b ← randomBytes 1
  let pad := (vectorOfBytes b).head
  pure (pad, v ^^^ pad)

/-- The assumption on `fill_bytes`: it samples with `Result.random` and keeps the state. -/
def rand_core.RngCore.fill_bytes_assumption {R : Type} (inst : rand_core.RngCore R) : Prop :=
  RandomFill inst.fill_bytes

/-- If `inst.fill_bytes` samples with `Result.random`, then `mask inst rng v` is `maskModel v`,
read as an Aeneas result, with the state `rng` unchanged. -/
@[bridge_for mask]
theorem mask_eq {R : Type} (inst : rand_core.RngCore R)
    (h : rand_core.RngCore.fill_bytes_assumption inst) (rng : R) (v : U8) :
    mask inst rng v = toResult ((·, rng) <$> maskModel v) := by
  simp only [mask, lift, Array.to_slice_mut, Aeneas.Std.bind_ok, uncurry_eq]
  rw [RandomFill.fill_eq h rng (Array.repeat 1#usize 0#u8).to_slice 1 padBuf_length]
  simp only [maskModel, toResult_map, toResult_bind, toResult_randomBytes, toResult_pure,
    Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok]
  congr 1
  funext b
  obtain ⟨⟨l⟩, hl⟩ := b
  match l, hl with
  | [x], _ => simp [Array.from_slice, Array.index_usize, vectorOfBytes, List.Vector.head]

/-- Run with `uniformImpl`, `maskModel v` has the distribution of `Crypto.mask v`. -/
@[bridge_for mask]
theorem maskModel_bridge (v : U8) :
    simulateQ uniformImpl (maskModel v) =ᵈ Crypto.mask v := by
  have e : simulateQ uniformImpl (maskModel v) =
      (do let w ← $ᵗ (List.Vector U8 1)
          pure (w.head, v ^^^ w.head)) := by
    simp [maskModel, randomBytes, uniformImpl]
    rfl
  rw [e]
  have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective head_bijective).map
    (fun x => (x, v ^^^ x))
  simpa [Crypto.mask, map_eq_bind_pure_comp] using h

/-- `unmask pad masked` has the distribution of `Result.ok <$> Crypto.unmask pad masked`. -/
theorem unmask_bridge (pad masked : U8) :
    (pure (unmask pad masked) : ProbComp _) =ᵈ
    (do let r ← Crypto.unmask pad masked
        pure (Result.ok r)) :=
  bridge_of_spec (Spec.unmask_spec pad masked) (by simp [unmask])

end byte_mask.Effect.Bridge
