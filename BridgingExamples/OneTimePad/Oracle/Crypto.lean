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

/-- `length` uniform bytes. This is the Crypto counterpart of the generator method `fill_bytes`.
The bridge assumes that the extracted `fill_bytes` gives bytes with this distribution. -/
def rand_core.RngCore.fill_bytes (length : ℕ) : ProbComp (List.Vector U8 length) :=
  $ᵗ (List.Vector U8 length)

/-- The one-time pad on 16-byte blocks. `keygen` fills a 16-byte key with `fill_bytes`, as the Rust
`keygen` does, and `encrypt` and `decrypt` XOR with the key. A key must encrypt only one message:
two ciphertexts under one key reveal the XOR of the two messages. It gives no integrity: a change
to a bit of the ciphertext changes the same bit of the decrypted message. -/
@[crypto_for keygen encrypt decrypt]
def otp : SymmEncAlg ProbComp Block Block Block where
  keygen := do
    let bytes ← rand_core.RngCore.fill_bytes 16
    pure ((arrayEquiv (n := 16#usize)).symm bytes)
  encrypt k m := pure (xor k m)
  decrypt k c := pure (some (xor k c))

end one_time_pad.Oracle.Crypto
