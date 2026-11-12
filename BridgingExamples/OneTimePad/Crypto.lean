import BridgingExamples.OneTimePad.Aeneas
import Common.Byte
import Common.Metadata
import VCVio.CryptoFoundations.SymmEncAlg

/-!
# The one-time pad in VCVio

`otp` is the one-time pad on 16-byte blocks, as a VCVio `SymmEncAlg`: a uniform key, and
encryption and decryption by byte-wise XOR with the key. `otp_perfectSecrecy` proves that it is
perfectly secret, from VCVio's Shannon theorem.
-/

namespace one_time_pad.Crypto

open Aeneas.Std BridgingExamples

/-- A 16-byte block, the Rust type `[u8; 16]`. -/
abbrev Block : Type := Array U8 16#usize

/-- The byte-wise XOR of two blocks. -/
def xor (a b : Block) : Block :=
  Array.from (List.zipWith (· ^^^ ·) a.val b.val) (by simp)

theorem xor_val (a b : Block) : (xor a b).val = List.zipWith (· ^^^ ·) a.val b.val :=
  Array.from_val _ _

/-- XOR with a fixed block is a bijection. -/
theorem xor_left_bijective (msg : Block) : Function.Bijective (fun key => xor key msg) := by
  refine Function.Involutive.bijective fun key => ?_
  rw [Array.eq_iff, xor_val, xor_val]
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_zipWith]
  apply UScalar.eq_of_val_eq
  simp [UScalar.val_xor]

/-- The one-time pad on 16-byte blocks: a uniform key, and XOR with the key. -/
@[crypto_for keygen encrypt decrypt]
def otp : SymmEncAlg ProbComp Block Block Block where
  keygen := $ᵗ Block
  encrypt k m := pure (xor k m)
  decrypt k c := pure (some (xor k c))

/-- Every message gives the same ciphertext distribution. -/
theorem otp_ciphertextRowsEqual : otp.ciphertextRowsEqualAt := by
  let : MeasurableSpace Block := ⊤
  exact SymmEncAlg.ciphertextRowsEqualAt_of_uniformKey_of_bijective otp xor
    SampleableType.evalDist_uniformSample (fun _ _ => evalDist_pure _) xor_left_bijective

/-- The one-time pad is perfectly secret: for every message distribution, the message and the
ciphertext are independent. -/
theorem otp_perfectSecrecy : otp.perfectSecrecyAt :=
  SymmEncAlg.perfectSecrecyAt_of_ciphertextRowsEqualAt otp otp_ciphertextRowsEqual

end one_time_pad.Crypto
