import BridgingExamples.OneTimePad.Oracle.Spec
import BridgingExamples.OneTimePad.Oracle.Crypto
import Common.Correspondence
import Common.Metadata
import Common.Oracle.Tape

/-!
# Bridge for the one-time pad, with the generator as an oracle

Aeneas extracts `keygen` as a deterministic function of a generator `inst : CryptoRng R` and a
state `rng : R`. The bridge to `Crypto.otp.keygen` has three steps.

1. `keygen_eq_prog`: `keygen` is the oracle program `keygenProg`, run with the `fill_bytes` of
   `inst`. This holds for every generator, with the final state and failures.
2. `keygenProg_bridge`: `keygenProg`, run with uniform bytes (`unifImpl`), has the distribution of
   `Crypto.otp.keygen`.
3. `keygen_bridge`: under `fill_bytes_assumption`, the extracted `keygen`, run from a sampled
   state, has the distribution of `Crypto.otp.keygen`.

`encrypt_bridge` and `decrypt_bridge` relate the deterministic `encrypt` and `decrypt` to
`Crypto.otp`. `fill_bytes_assumption` is the only Lean assumption on the generator. Two
assumptions stay outside Lean. First, Aeneas extracts `keygen`, `encrypt` and `decrypt`
faithfully. Second, the real generator is `fill_bytes` run from a state with the distribution
`seed`. The oracle definitions are in `Common/Oracle/Rng.lean`. This file proves no security
property.
-/

namespace one_time_pad.Oracle.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle one_time_pad.Oracle.Crypto
  OracleSpec OracleComp

/-! ## `keygen` as an oracle program -/

/-- The 16-byte buffer that `keygen` passes to `fill_bytes`. -/
def keyBuf : Slice U8 := (Array.repeat 16#usize 0#u8).to_slice

theorem keyBuf_length : keyBuf.length = 16 := by
  simp only [keyBuf, Slice.length, Array.val_to_slice, Aeneas.Std.Array.length_eq]; rfl

/-- The stateless generator whose `fill_bytes` returns `b`. Its other methods fail, and `keygen`
does not call them. -/
def constRng (b : Slice U8) : rand_core.CryptoRng Unit where
  RngCoreInst := {
    next_u32 := fun _ => Result.fail .panic
    next_u64 := fun _ => Result.fail .panic
    fill_bytes := constFill b }

/-- `keygenRest b`: the extracted `keygen`, with `b` as the answer of `fill_bytes`. -/
def keygenRest (b : Slice U8) : Result Block := do
  let (k, _) ← keygen (constRng b) ()
  Result.ok k

/-- `keygen` as an oracle program: one query for `keyBuf`, then `keygenRest` on the answer. -/
def keygenProg : OracleComp FillSpec (Result Block) := do
  let b ← (liftM (FillSpec.query keyBuf) : OracleComp FillSpec _)
  return keygenRest b

/-- For every generator `inst` and state `rng`, `keygen inst rng` is `keygenProg` run with
`inst.RngCoreInst.fill_bytes` from `rng`, final state and failures included. -/
@[bridge_for keygen]
theorem keygen_eq_prog {R : Type} (inst : rand_core.CryptoRng R) (rng : R) :
    keygen inst rng = runProg inst.RngCoreInst.fill_bytes keygenProg rng := by
  rw [keygenProg, runProg_query]
  simp only [keygenRest, keygen, constRng, constFill, lift, Array.to_slice_mut, keyBuf,
    Aeneas.Std.bind_ok, uncurry_eq]

/-- `keygenProg` asks for at most 16 bytes. -/
theorem keygenProg_byteBound : ByteBound keygenProg 16 := by
  simp [ByteBound, keygenProg, keyBuf_length]

/-- If `b` has 16 bytes, then `keygenRest b` returns them as the key. -/
theorem keygenRest_of_length (b : Slice U8) (hb : b.val.length = 16) :
    keygenRest b = Result.ok (Array.from b.val (by simpa using hb)) := by
  simp only [keygenRest, keygen, constRng, constFill, lift, Array.to_slice_mut,
    Aeneas.Std.bind_ok, uncurry_eq]
  simp [Array.from_slice, hb]

/-- Run with `unifImpl`, `keygenProg` has the distribution of `Result.ok <$> Crypto.otp.keygen`. -/
@[bridge_for keygen]
theorem keygenProg_bridge :
    simulateQ unifImpl keygenProg =ᵈ
    (do let k ← otp.keygen
        pure (Result.ok k)) := by
  have e : simulateQ unifImpl keygenProg =
      (do let w ← $ᵗ (List.Vector U8 keyBuf.length)
          pure (keygenRest (sliceOfVector keyBuf w))) := by
    simp [keygenProg, unifImpl]
    rfl
  rw [e]
  refine (uniformVector_bind_congr keyBuf_length _
    (fun w : List.Vector U8 16 =>
      pure (Result.ok ((arrayEquiv (n := 16#usize)).symm w))) ?_).trans ?_
  · intro w
    congr 1
    rw [keygenRest_of_length _ (by rw [sliceOfVector_val, w.property, keyBuf_length])]
    congr 1
    rw [Array.eq_iff, Array.from_val, sliceOfVector_val]
    exact (Array.from_val w.val (by rw [w.property, keyBuf_length]; rfl)).symm
  · have hs : (otp.keygen : ProbComp Block) =
        (arrayEquiv (n := 16#usize)).symm <$> ($ᵗ (List.Vector U8 16)) := rfl
    rw [hs, map_eq_bind_pure_comp, bind_assoc]
    simp only [pure_bind, Function.comp_def]
    exact EvalDistEq.rfl

/-- The assumption on `fill_bytes`: from a state sampled by `seed`, it answers every oracle program
with `ByteBound p n` as `unifImpl` does, in distribution. This is `IdealRng inst.fill_bytes seed n`
unfolded. `IdealRng` states its limits. A generator whose `fill_bytes` is `tapeFill` satisfies it
with the seed `tapeSeed n` (`idealRng_tape`). -/
def rand_core.RngCore.fill_bytes_assumption {R : Type} (inst : rand_core.RngCore R)
    (seed : ProbComp R) (n : ℕ) : Prop :=
  ∀ {α : Type} (p : OracleComp FillSpec (Result α)), ByteBound p n →
    (do let rng ← seed
        pure (Prod.fst <$> runProg inst.fill_bytes p rng)) =ᵈ
    simulateQ unifImpl p

/-- `fill_bytes_assumption` is `IdealRng` for the method `fill_bytes`. -/
theorem fill_bytes_assumption_iff {R : Type} (inst : rand_core.RngCore R) (seed : ProbComp R)
    (n : ℕ) :
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

/-! ## `encrypt` and `decrypt` -/

theorem xorBlock_eq_xor (a b : Block) : Spec.xorBlock a b = xor a b := rfl

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
