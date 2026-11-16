import BridgingExamples.ProbSmoke.Spec
import BridgingExamples.ProbSmoke.Crypto
import Common.Metadata
import Common.Oracle.Rng

/-!
# Bridge for `fill_random`, with the generator as an oracle

Aeneas extracts `fill_random` as a deterministic function of a generator `inst : RngCore R` and a
state `rng : R`. The bridge to `Crypto.fill_random` has three steps.

1. `fill_random_eq_prog`: `fill_random` is the oracle program `fillProg`, run with
   `inst.fill_bytes`. This holds for every generator, with the final state and failures.
2. `fillProg_bridge`: `fillProg`, run with uniform bytes (`unifImpl`), has the distribution of
   `Crypto.fill_random`.
3. `fill_random_bridge`: under `fill_bytes_assumption`, the extracted `fill_random`, run from a
   sampled state with the final state dropped, returns `Result.ok` of a slice with the bytes of
   `Crypto.fill_random`. So the call also never fails.

`fill_bytes_assumption` is the only Lean assumption on the generator. Two assumptions stay outside
Lean. First, Aeneas extracts `fill_random` faithfully. Second, the real generator is `fill_bytes`
run from a state with the distribution `seed`, and this state is independent of the buffer. The
oracle definitions are in `Common/Oracle/Rng.lean`.
-/

namespace prob_smoke.Oracle.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle OracleSpec OracleComp

/-! ## `fill_random` as an oracle program -/

/-- `fill_random` as an oracle program: one query for `buffer`, then return the answer. -/
def fillProg (buffer : Slice U8) : OracleComp FillSpec (Result (Slice U8)) := do
  let b ← (liftM (FillSpec.query buffer) : OracleComp FillSpec _)
  return Result.ok b

/-- For every generator `inst` and state `rng`, `fill_random inst rng buffer` is `fillProg buffer`
run with `inst.fill_bytes` from `rng`, final state and failures included. `fill_random` returns the
state first and `runProg` returns it last, so the pair is swapped. -/
@[bridge_for fill_random]
theorem fill_random_eq_prog {R : Type} (inst : rand_core.RngCore R) (rng : R)
    (buffer : Slice U8) :
    fill_random inst rng buffer = Prod.swap <$> runProg inst.fill_bytes (fillProg buffer) rng := by
  rw [fillProg, runProg_query, Spec.fill_random_spec]
  simp only [Aeneas.Std.bind_ok]
  show _ = Prod.swap <$> (inst.fill_bytes rng buffer >>= fun p => pure (p.2, p.1))
  simp

/-- `fillProg buffer` asks for at most `buffer.length` bytes. -/
theorem fillProg_byteBound (buffer : Slice U8) : ByteBound (fillProg buffer) buffer.length := by
  simp [ByteBound, fillProg]

/-- Run with `unifImpl`, `fillProg buffer` has the distribution of `Crypto.fill_random k`, where
`k` is the buffer length. -/
@[bridge_for fill_random]
theorem fillProg_bridge (buffer : Slice U8) :
    simulateQ unifImpl (fillProg buffer) =ᵈ
    (do let bytes ← Crypto.fill_random buffer.length
        pure (Result.ok (sliceOfVector buffer bytes))) := by
  simp [fillProg, unifImpl, Crypto.fill_random, Crypto.rand_core.RngCore.fill_bytes]
  rfl

/-- The assumption on `fill_bytes`: from a state sampled by `seed`, it answers every oracle program
with `ByteBound p n` as `unifImpl` does, in distribution. This is `IdealRng inst.fill_bytes seed n`
unfolded (`fill_bytes_assumption_iff`). A generator whose `fill_bytes` is `tapeFill` satisfies it
with the seed `tapeSeed n` (`idealRng_tape`). If the state of a generator comes only from a seed
of fewer than `n` bytes, then the generator does not satisfy it. `IdealRng` argues this limit,
without a Lean proof, and states the others.

`fill_random_bridge` uses the assumption for one program with one query. The assumption covers
every program within the budget, as in the ByteMask bridge, so that one assumption also serves
programs with several calls. This excludes generators that answer each single query with uniform
bytes but correlate the answers of different queries. -/
def rand_core.RngCore.fill_bytes_assumption {R : Type} (inst : rand_core.RngCore R)
    (seed : ProbComp R) (n : ℕ) : Prop :=
  ∀ {α : Type} (p : OracleComp FillSpec (Result α)), ByteBound p n →
    (do let rng ← seed
        pure (Prod.fst <$> runProg inst.fill_bytes p rng)) =ᵈ
    simulateQ unifImpl p

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
