import BridgingExamples.ByteMask.Oracle.Program
import Common.Correspondence
import Common.Metadata
import Common.Oracle.Tape

/-!
# Bridge for `mask`, with the generator as an oracle

The generator method `fill_bytes` is the one random atom. `fill_bytes_assumption` relates the
extracted `fill_bytes` to `Crypto.rand_core.RngCore.fill_bytes`, and `mask_bridge` relates the
extracted `mask` to `Crypto.mask` under this assumption. `unmask_bridge` relates the deterministic
`unmask` to `Crypto.unmask`.

The lemmas behind `mask_bridge` are in `Program.lean`.
-/

namespace byte_mask.Oracle.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle OracleSpec OracleComp

/-- The Crypto `fill_bytes` as the answer to a query of `fill_bytes`: the query `s` gets
`Crypto.rand_core.RngCore.fill_bytes s.length`, with fresh randomness for each query. -/
def cryptoFill : QueryImpl FillSpec ProbComp := fun s => do
  let bytes ← Crypto.rand_core.RngCore.fill_bytes s.length
  pure (sliceOfVector s bytes)

/-- The assumption on `fill_bytes`: from a state sampled by `seed`, the extracted `fill_bytes`
answers every oracle program `p` that asks for at most `n` bytes as the Crypto `fill_bytes` does,
in distribution. This is `IdealRng inst.fill_bytes seed n` (`fill_bytes_assumption_iff`), and
`IdealRng` states its limits. A generator whose `fill_bytes` is `tapeFill` satisfies it with the
seed `tapeSeed n` (`idealRng_tape`). -/
def rand_core.RngCore.fill_bytes_assumption {R : Type} (inst : rand_core.RngCore R)
    (seed : ProbComp R) (n : ℕ) : Prop :=
  ∀ {α : Type} (p : OracleComp FillSpec (Result α)), ByteBound p n →
    (do let rng ← seed
        pure (Prod.fst <$> runProg inst.fill_bytes p rng)) =ᵈ
    simulateQ cryptoFill p

/-- `fill_bytes_assumption` is `IdealRng` unfolded. -/
theorem rand_core.RngCore.fill_bytes_assumption_iff {R : Type} (inst : rand_core.RngCore R)
    (seed : ProbComp R) (n : ℕ) :
    rand_core.RngCore.fill_bytes_assumption inst seed n ↔ IdealRng inst.fill_bytes seed n :=
  Iff.rfl

/-- If `fill_bytes_assumption inst seed 1`, then `mask inst rng v`, with `rng` sampled by `seed`
and the final state dropped, has the distribution of `Result.ok <$> Crypto.mask v`. The theorem
covers one call of `mask`. -/
theorem mask_bridge {R : Type} (inst : rand_core.RngCore R) (seed : ProbComp R)
    (h : rand_core.RngCore.fill_bytes_assumption inst seed 1) (v : U8) :
    (do let rng ← seed
        pure (Prod.fst <$> mask inst rng v)) =ᵈ
    (do let y ← Crypto.mask v
        pure (Result.ok y)) := by
  simp only [mask_eq_prog]
  exact (h (maskProg v) (maskProg_byteBound v)).trans (maskProg_bridge v)

/-- `unmask pad masked` has the distribution of `Result.ok <$> Crypto.unmask pad masked`. -/
theorem unmask_bridge (pad masked : U8) :
    (pure (unmask pad masked) : ProbComp _) =ᵈ
    (do let r ← Crypto.unmask pad masked
        pure (Result.ok r)) :=
  bridge_of_spec (Spec.unmask_spec pad masked)

end byte_mask.Oracle.Bridge
