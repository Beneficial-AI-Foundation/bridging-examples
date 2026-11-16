import BridgingExamples.ProbSmoke.Spec
import BridgingExamples.ProbSmoke.Crypto
import Common.Oracle.Rng

/-!
# `fill_random` as an oracle program

The lemmas behind `fill_random_bridge` in `Bridge.lean`. `fillProg` is the extracted `fill_random`
with its call to `fill_bytes` replaced by an oracle query. A generator or the Crypto `fill_bytes`
can then answer the query.
-/

namespace prob_smoke.Oracle.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle OracleSpec OracleComp

/-- `fill_random` as an oracle program: one query for `buffer`, then return the answer. -/
def fillProg (buffer : Slice U8) : OracleComp FillSpec (Result (Slice U8)) := do
  let b ← (liftM (FillSpec.query buffer) : OracleComp FillSpec _)
  return Result.ok b

/-- For every generator `inst` and state `rng`, `fill_random inst rng buffer` is `fillProg buffer`
run with `inst.fill_bytes` from `rng`, final state and failures included. `fill_random` returns the
state first and `runProg` returns it last, so the pair is swapped. -/
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
theorem fillProg_bridge (buffer : Slice U8) :
    simulateQ unifImpl (fillProg buffer) =ᵈ
    (do let bytes ← Crypto.fill_random buffer.length
        pure (Result.ok (sliceOfVector buffer bytes))) := by
  simp [fillProg, unifImpl, Crypto.fill_random, Crypto.rand_core.RngCore.fill_bytes]
  rfl

end prob_smoke.Oracle.Bridge
