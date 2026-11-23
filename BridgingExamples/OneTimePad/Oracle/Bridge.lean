import BridgingExamples.OneTimePad.Oracle.Program
import Common.Correspondence
import Common.Metadata
import Common.Oracle.Tape

/-!
# Bridge for the one-time pad, with the generator as an oracle

The generator method `fill_bytes` is the one random atom. `fill_bytes_assumption` relates the
extracted `fill_bytes` to `Crypto.rand_core.RngCore.fill_bytes`, and `keygen_bridge` relates the
extracted `keygen` to `Crypto.otp.keygen` under this assumption. `encrypt_bridge` and
`decrypt_bridge` relate the deterministic `encrypt` and `decrypt` to `Crypto.otp`.

The lemmas behind `keygen_bridge` are in `Program.lean`.
-/

namespace one_time_pad.Oracle.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle one_time_pad.Oracle.Crypto
  OracleSpec OracleComp

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

/-- If `fill_bytes_assumption inst.RngCoreInst seed 16`, then `keygen inst rng`, with `rng`
sampled by `seed` and the final state dropped, has the distribution of
`Result.ok <$> Crypto.otp.keygen`. The theorem covers one call of `keygen`. -/
theorem keygen_bridge {R : Type} (inst : rand_core.CryptoRng R) (seed : ProbComp R)
    (h : rand_core.RngCore.fill_bytes_assumption inst.RngCoreInst seed 16) :
    (do let rng ← seed
        pure (Prod.fst <$> keygen inst rng)) =ᵈ
    (do let k ← otp.keygen
        pure (Result.ok k)) := by
  simp only [keygen_eq_prog]
  exact (h keygenProg keygenProg_byteBound).trans keygenProg_bridge

/-- `encrypt key message` has the distribution of
`Result.ok <$> Crypto.otp.encrypt key message`. -/
theorem encrypt_bridge (key message : Block) :
    (pure (encrypt key message) : ProbComp _) =ᵈ
    (do let c ← otp.encrypt key message
        pure (Result.ok c)) :=
  bridge_of_spec (Spec.encrypt_spec key message)

/-- The value of a successful result, and `none` for a failure or divergence. -/
def toOption {α : Type} (r : Result α) : Option α :=
  match r.match with
  | .ok a => some a
  | _ => none

/-- `toOption (decrypt key c)` is `Crypto.otp.decrypt key c`. -/
theorem decrypt_bridge (key c : Block) :
    (pure (toOption (decrypt key c)) : ProbComp _) = otp.decrypt key c := by
  simp [otp, decrypt, Spec.encrypt_eq, xorBlock_eq_xor, toOption]

end one_time_pad.Oracle.Bridge
