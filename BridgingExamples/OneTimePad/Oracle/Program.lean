import BridgingExamples.OneTimePad.Oracle.Spec
import BridgingExamples.OneTimePad.Oracle.Crypto
import Common.Correspondence
import Common.Oracle.Rng

/-!
# `keygen` as an oracle program

The lemmas behind `keygen_bridge` in `Bridge.lean`. `keygenProg` is the extracted `keygen` with
its call to `fill_bytes` replaced by an oracle query. A generator or the Crypto `fill_bytes` can
then answer the query.
-/

namespace one_time_pad.Oracle.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle one_time_pad.Oracle.Crypto
  OracleSpec OracleComp

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
    fill_bytes := fun _ _ => Result.ok ((), b) }

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
theorem keygen_eq_prog {R : Type} (inst : rand_core.CryptoRng R) (rng : R) :
    keygen inst rng = runProg inst.RngCoreInst.fill_bytes keygenProg rng := by
  rw [keygenProg, runProg_query]
  simp only [keygenRest, keygen, constRng, lift, Array.to_slice_mut, keyBuf,
    Aeneas.Std.bind_ok, uncurry_eq]

/-- `keygenProg` asks for at most 16 bytes. -/
theorem keygenProg_byteBound : ByteBound keygenProg 16 := by
  simp [ByteBound, keygenProg, keyBuf_length]

/-- If `b` has 16 bytes, then `keygenRest b` returns them as the key. -/
theorem keygenRest_of_length (b : Slice U8) (hb : b.val.length = 16) :
    keygenRest b = Result.ok (Array.from b.val (by simpa using hb)) := by
  simp only [keygenRest, keygen, constRng, lift, Array.to_slice_mut,
    Aeneas.Std.bind_ok, uncurry_eq]
  simp [Array.from_slice, hb]

/-- Run with `unifImpl`, `keygenProg` has the distribution of `Result.ok <$> Crypto.otp.keygen`. -/
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
        (arrayEquiv (n := 16#usize)).symm <$> ($ᵗ (List.Vector U8 16)) := by
      rw [map_eq_bind_pure_comp]; rfl
    rw [hs, map_eq_bind_pure_comp, bind_assoc]
    simp only [pure_bind, Function.comp_def]
    exact EvalDistEq.rfl

theorem xorBlock_eq_xor (a b : Block) : Spec.xorBlock a b = xor a b := rfl

end one_time_pad.Oracle.Bridge
