import BridgingExamples.ProbSmoke.Oracle.Program
import Common.Oracle.Tape

/-!
# Bridge for `fill_random`, with the generator as an oracle

The generator method `fill_bytes` is the one random atom. `fill_bytes_assumption` relates the
extracted `fill_bytes` to `Crypto.rand_core.RngCore.fill_bytes`, and `fill_random_bridge` relates
the extracted `fill_random` to `Crypto.fill_random` under this assumption.

The lemmas behind `fill_random_bridge` are in `Program.lean`.
-/

namespace prob_smoke.Oracle.Bridge

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

/-- If `fill_bytes_assumption inst seed k`, where `k` is the buffer length, then
`fill_random inst rng buffer`, with `rng` sampled by `seed` and the final state dropped, fills the
buffer with the bytes of `Crypto.fill_random k`. The theorem covers one call of `fill_random`. -/
theorem fill_random_bridge {R : Type} (inst : rand_core.RngCore R) (seed : ProbComp R)
    (buffer : Slice U8)
    (h : rand_core.RngCore.fill_bytes_assumption inst seed buffer.length) :
    (do let rng ← seed
        pure (Prod.snd <$> fill_random inst rng buffer)) =ᵈ
    (do let bytes ← Crypto.fill_random buffer.length
        pure (Result.ok (sliceOfVector buffer bytes))) := by
  have e : ∀ rng, Prod.snd <$> fill_random inst rng buffer =
      Prod.fst <$> runProg inst.fill_bytes (fillProg buffer) rng := by
    intro rng
    rw [fill_random_eq_prog, Functor.map_map]
    rfl
  simp only [e]
  exact (h (fillProg buffer) (fillProg_byteBound buffer)).trans (fillProg_bridge buffer)

end prob_smoke.Oracle.Bridge
