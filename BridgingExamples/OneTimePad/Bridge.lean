import BridgingExamples.OneTimePad.Spec
import BridgingExamples.OneTimePad.Crypto
import BridgingExamples.ByteMask.Bridge

/-!
# Bridge for the one-time pad, and perfect secrecy of the extracted code

1. `keygen_eq_prog`: for every generator, the extracted `keygen` is the oracle program
   `keygenProg`, answered by the generator's `fill_bytes`. The program asks for the 16-byte
   buffer `keyBuf`, then replays the extracted `keygen` on the answer. No assumption.
2. `keygenProg_bridge`: answered by uniform bytes (`unifImpl`), `keygenProg` returns a uniform
   key, the key of `Crypto.otp`. No generator appears in this theorem.
3. `keygen_bridge`: under `keygen_assumption`, which is `IdealRng` with a budget of 16 bytes, the extracted `keygen`, run from
   a state sampled by `seed`, returns a uniform key.
4. `rustOtp inst seed` is the `SymmEncAlg` whose algorithms run the extracted `keygen`,
   `encrypt` and `decrypt`. `rustOtp_perfectSecrecy` proves that it is perfectly secret under
   `keygen_assumption`, from `otp_perfectSecrecy`.

The oracle of `fill_bytes` (`FillSpec`, `runProg`, `unifImpl`, `IdealRng`, ...) is defined in
`ByteMask/Bridge.lean`.
-/

namespace one_time_pad.Bridge

open Aeneas Aeneas.Std BridgingExamples byte_mask.Bridge one_time_pad.Crypto OracleSpec
  OracleComp

/-! ## `keygen` as an oracle program -/

/-- The 16-byte buffer that `keygen` passes to `fill_bytes`. -/
def keyBuf : Slice U8 := (Array.repeat 16#usize 0#u8).to_slice

theorem keyBuf_length : keyBuf.length = 16 := by
  simp only [keyBuf, Slice.length, Array.val_to_slice, Aeneas.Std.Array.length_eq]; rfl

/-- The generator whose `fill_bytes` returns `b`. `keygen` does not call `next_u32` or
`next_u64`, so they fail. -/
def constRng (b : Slice U8) : rand_core.CryptoRng Unit where
  RngCoreInst := {
    next_u32 := fun _ => Result.fail .panic
    next_u64 := fun _ => Result.fail .panic
    fill_bytes := constFill b }

/-- `keygenRest b` replays the extracted `keygen` with the generator `constRng b`, and drops its
state. It is the extracted `keygen` run on the answer `b`. -/
def keygenRest (b : Slice U8) : Result Block := do
  let (k, _) ← keygen (constRng b) ()
  Result.ok k

/-- `keygen` as an oracle program: one query for `keyBuf`, then `keygenRest` on the answer. -/
def keygenProg : OracleComp FillSpec (Result Block) := do
  let b ← (liftM (FillSpec.query keyBuf) : OracleComp FillSpec _)
  return keygenRest b

/-- For every generator `inst` and state `rng`, `keygen inst rng` is `keygenProg` run with
`inst.RngCoreInst.fill_bytes` from `rng`. The equality is on the full `Result`, with the final
state. -/
@[bridge_for keygen]
theorem keygen_eq_prog {R : Type} (inst : rand_core.CryptoRng R) (rng : R) :
    keygen inst rng = runProg inst.RngCoreInst.fill_bytes keygenProg rng := by
  rw [keygenProg, runProg_query]
  simp only [keygenRest, keygen, constRng, constFill, lift, Array.to_slice_mut, keyBuf,
    Aeneas.Std.bind_ok, uncurry_eq]

/-- `keygenProg` asks for 16 bytes. -/
theorem keygenProg_byteBound : ByteBound keygenProg 16 := by
  simp [ByteBound, keygenProg, keyBuf_length]

/-- If the answer has 16 bytes, then `keygenRest` returns them as the key. -/
theorem keygenRest_of_length (b : Slice U8) (hb : b.val.length = 16) :
    keygenRest b = Result.ok (Array.from b.val (by simpa using hb)) := by
  simp only [keygenRest, keygen, constRng, constFill, lift, Array.to_slice_mut,
    Aeneas.Std.bind_ok, uncurry_eq]
  simp [Array.from_slice, hb]

/-- Answered by `unifImpl`, `keygenProg` samples a uniform buffer of the length of `keyBuf`
and runs `keygenRest` on it. -/
theorem simulateQ_keygenProg :
    simulateQ unifImpl keygenProg =
      (do let w ← $ᵗ (List.Vector U8 keyBuf.length)
          pure (keygenRest (sliceOfVector keyBuf w))) := by
  simp [keygenProg, unifImpl]
  rfl

/-- Answered by `unifImpl`, `keygenProg` returns a uniform key: it has the distribution of
`Result.ok <$> otp.keygen`. -/
@[bridge_for keygen]
theorem keygenProg_bridge :
    simulateQ unifImpl keygenProg =ᵈ
    (do let k ← otp.keygen
        pure (Result.ok k)) := by
  rw [simulateQ_keygenProg]
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

/-- The assumption on the generator: `IdealRng` for its `fill_bytes`, from a state sampled by
`seed`, with a budget of 16 bytes, the length of one key. See `IdealRng` in
`ByteMask/Bridge.lean`: it is an exact equality, so it is an idealization of a real generator. -/
def keygen_assumption {R : Type} (inst : rand_core.CryptoRng R) (seed : ProbComp R) : Prop :=
  IdealRng inst.RngCoreInst.fill_bytes seed 16

/-- Under `keygen_assumption inst seed`, the extracted `keygen`, run from a state sampled by
`seed`, returns a uniform key. The final generator state is dropped. -/
theorem keygen_bridge {R : Type} (inst : rand_core.CryptoRng R) (seed : ProbComp R)
    (h : keygen_assumption inst seed) :
    (do let rng ← seed
        pure (Prod.fst <$> keygen inst rng)) =ᵈ
    (do let k ← otp.keygen
        pure (Result.ok k)) := by
  simp only [keygen_eq_prog]
  exact (h keygenProg keygenProg_byteBound).trans keygenProg_bridge

/-! ## `encrypt` and `decrypt` -/

theorem xorBlock_eq_xor (a b : Block) : Spec.xorBlock a b = xor a b := by
  rw [Array.eq_iff, Spec.xorBlock_val, xor_val]

/-- `encrypt` is deterministic: it has the distribution of `otp.encrypt key message`. -/
theorem encrypt_bridge (key message : Block) :
    (pure (encrypt key message) : ProbComp _) =ᵈ
    (do let c ← otp.encrypt key message
        pure (Result.ok c)) := by
  simp [otp, Spec.encrypt_eq, xorBlock_eq_xor]

/-- The value of a successful result, and `none` for a failure or divergence. -/
def toOption {α : Type} (r : Result α) : Option α :=
  match r.match with
  | .ok a => some a
  | _ => none

@[simp] theorem toOption_ok {α : Type} (a : α) : toOption (Result.ok a) = some a := by
  simp [toOption]

/-- `decrypt` is deterministic, and returns what `otp.decrypt key c` returns. -/
theorem decrypt_bridge (key c : Block) :
    (pure (toOption (decrypt key c)) : ProbComp _) = otp.decrypt key c := by
  simp [otp, decrypt, Spec.encrypt_eq, xorBlock_eq_xor]

/-! ## The extracted one-time pad as a `SymmEncAlg` -/

/-- The one-time pad whose algorithms are the extracted code. `keygen` runs the extracted
`keygen` from a state sampled by `seed`, and drops the final state. A key or ciphertext is a
`Result`, so a failure of the extracted code is a value. `encrypt` and `decrypt` run the
extracted functions on a successful key, and pass a failure on. `decrypt` returns `none` on a
failure. -/
def rustOtp {R : Type} (inst : rand_core.CryptoRng R) (seed : ProbComp R) :
    SymmEncAlg ProbComp Block (Result Block) (Result Block) where
  keygen := do
    let rng ← seed
    pure (Prod.fst <$> one_time_pad.keygen inst rng)
  encrypt k m := pure (k >>= fun k => one_time_pad.encrypt k m)
  decrypt k c := pure (toOption (k >>= fun k => c >>= fun c => one_time_pad.decrypt k c))

/-- Under `keygen_assumption`, the ciphertext of `message` under `rustOtp` has the distribution of
`Result.ok` applied to the ciphertext under `otp`. -/
theorem rustOtp_cipher {R : Type} (inst : rand_core.CryptoRng R) (seed : ProbComp R)
    (h : keygen_assumption inst seed) (message : Block) :
    (rustOtp inst seed).perfectSecrecyCipherGivenMsgExperiment message =ᵈ
    Result.ok <$> otp.perfectSecrecyCipherGivenMsgExperiment message := by
  have hk := bind_call (keygen_bridge inst seed h) (fun k => one_time_pad.encrypt k message)
  simp only [SymmEncAlg.perfectSecrecyCipherGivenMsgExperiment, rustOtp, bind_assoc, pure_bind]
  refine hk.trans ?_
  simp [otp, Spec.encrypt_eq, xorBlock_eq_xor, map_eq_bind_pure_comp]

/-- Under `keygen_assumption inst seed`, every message gives the same
ciphertext distribution under `rustOtp inst seed`. -/
theorem rustOtp_ciphertextRowsEqual {R : Type} (inst : rand_core.CryptoRng R)
    (seed : ProbComp R) (h : keygen_assumption inst seed) :
    (rustOtp inst seed).ciphertextRowsEqualAt := fun m₀ m₁ =>
  (rustOtp_cipher inst seed h m₀).trans
    (((otp_ciphertextRowsEqual m₀ m₁).map Result.ok).trans (rustOtp_cipher inst seed h m₁).symm)

/-- Under `keygen_assumption inst seed`, the one-time pad of the extracted code
is perfectly secret: for every message distribution, the message and the ciphertext are
independent.

The perfect-secrecy experiment runs `keygen` once, so the budget of 16 bytes covers it. The
theorem is only as strong as `keygen_assumption`, which is an idealization of a real generator. -/
@[bridge_for keygen encrypt decrypt]
theorem rustOtp_perfectSecrecy {R : Type} (inst : rand_core.CryptoRng R) (seed : ProbComp R)
    (h : keygen_assumption inst seed) :
    (rustOtp inst seed).perfectSecrecyAt :=
  SymmEncAlg.perfectSecrecyAt_of_ciphertextRowsEqualAt _
    (rustOtp_ciphertextRowsEqual inst seed h)

end one_time_pad.Bridge
