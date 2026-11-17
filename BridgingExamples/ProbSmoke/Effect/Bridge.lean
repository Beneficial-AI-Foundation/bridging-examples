import BridgingExamples.ProbSmoke.Spec
import BridgingExamples.ProbSmoke.Crypto
import Common.Effect.Random
import Common.Metadata

/-!
# Bridge for `fill_random`, with the generator as the `random` effect

This bridge needs `aeneas.patch`: an Aeneas `Result` can then sample with `Result.random`. The
extracted `fill_random` does not change. The bridge has two steps.

1. `fill_random_eq`: if `inst.fill_bytes` samples with `Result.random` (`RandomFill`), then
   `fill_random` is equal to `toResult` of the oracle program `fillModel`.
2. `fillModel_bridge`: `fillModel`, run with uniform bytes (`uniformImpl`), has the distribution
   of `Crypto.fill_random`.

`RandomFill` is the only Lean assumption on the generator. Compare with the Oracle bridge:

- Its equality `fill_random_eq_prog` holds for every generator, with no assumption, final state
  included. The equality here needs `RandomFill`.
- Its assumption is on the distribution of a sampled state, with a byte budget. Here there is no
  sampled state and no byte budget, because the bytes come from the effect.
- Its `fill_random_bridge` states the distribution of the extracted code. Here only the model has
  a distribution (see `Common/Effect/Random.lean`).
-/

namespace prob_smoke.Effect.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Effect OracleSpec OracleComp

/-- `fill_random` as an oracle program: ask for as many bytes as the buffer has, and return them
in the buffer. -/
def fillModel (buffer : Slice U8) : OracleComp RandSpec (Slice U8) :=
  sliceOfBytes buffer <$> randomBytes buffer.length

/-- The assumption on `fill_bytes`: it samples with `Result.random` and keeps the state. -/
def rand_core.RngCore.fill_bytes_assumption {R : Type} (inst : rand_core.RngCore R) : Prop :=
  RandomFill inst.fill_bytes

/-- If `inst.fill_bytes` samples with `Result.random`, then `fill_random inst rng buffer` is
`fillModel buffer`, read as an Aeneas result, with the state `rng` unchanged. -/
@[bridge_for fill_random]
theorem fill_random_eq {R : Type} (inst : rand_core.RngCore R)
    (h : rand_core.RngCore.fill_bytes_assumption inst) (rng : R) (buffer : Slice U8) :
    fill_random inst rng buffer = toResult ((rng, ·) <$> fillModel buffer) := by
  rw [Spec.fill_random_spec, h, fillModel]
  simp

/-- Run with `uniformImpl`, `fillModel buffer` has the distribution of `Crypto.fill_random k`,
where `k` is the buffer length. -/
@[bridge_for fill_random]
theorem fillModel_bridge (buffer : Slice U8) :
    simulateQ uniformImpl (fillModel buffer) =ᵈ
    (do let bytes ← Crypto.fill_random buffer.length
        pure (sliceOfVector buffer bytes)) := by
  simp [fillModel, randomBytes, uniformImpl, Crypto.fill_random,
    Crypto.rand_core.RngCore.fill_bytes]
  rfl

end prob_smoke.Effect.Bridge
