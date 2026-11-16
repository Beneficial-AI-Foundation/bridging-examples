import BridgingExamples.OneTimePad.Aeneas
import Common.Byte
import Common.Metadata
import VCVio.CryptoFoundations.SymmEncAlg

namespace one_time_pad.Oracle.Crypto

open Aeneas.Std BridgingExamples

/-- A 16-byte block, the Rust type `[u8; 16]`. -/
abbrev Block : Type := Array U8 16#usize

/-- The byte-wise XOR of two blocks. -/
def xor (a b : Block) : Block :=
  Array.from (List.zipWith (· ^^^ ·) a.val b.val) (by simp)

/-- The one-time pad on 16-byte blocks: a uniform key, and XOR with the key. A key must encrypt
only one message: two ciphertexts under one key reveal the XOR of the two messages. It gives no
integrity: a change to a bit of the ciphertext changes the same bit of the decrypted message. -/
@[crypto_for keygen encrypt decrypt]
def otp : SymmEncAlg ProbComp Block Block Block where
  keygen := $ᵗ Block
  encrypt k m := pure (xor k m)
  decrypt k c := pure (some (xor k c))

end one_time_pad.Oracle.Crypto
