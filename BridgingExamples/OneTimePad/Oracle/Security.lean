import BridgingExamples.OneTimePad.Oracle.Bridge

/-!
# Perfect secrecy of the one-time pad

`otp_perfectSecrecy` proves that `Crypto.otp` is perfectly secret, from VCVio's Shannon theorem.
`rustOtp inst seed` is the `SymmEncAlg` whose algorithms run the extracted `keygen`, `encrypt`
and `decrypt`. Under `fill_bytes_assumption` with a budget of 16 bytes:

* `rustOtp_cipher`: for every message, the extracted code never fails, and its ciphertext has
  the same distribution as the ciphertext under `Crypto.otp`.
* `rustOtp_perfectSecrecy`: `rustOtp` is perfectly secret, from `rustOtp_cipher` and
  `otp_ciphertextRowsEqual`.
* `rustOtp_complete`: decryption returns the message with probability 1.

The experiment of `perfectSecrecyAt` samples a message, then a generator state independent of the
message. It runs `keygen` once and `encrypt` once, and observes the message and the ciphertext. It
drops the final generator state and does not call `decrypt`. So the theorems say nothing about:

* two encryptions under one key, which reveal the XOR of the two messages for every generator;
* an observer of the final generator state, which can hold a copy of the key;
* a generator state that depends on the message.

Outside Lean, the theorems rely on two assumptions: Aeneas extracts the Rust functions faithfully,
and the real generator is `fill_bytes` run from a state with the distribution `seed`. The second
one is not proved for any real generator. An operating system generator reads an external entropy
source, so its state type and `seed` must model that source.
-/

namespace one_time_pad.Oracle.Security

open Aeneas.Std BridgingExamples one_time_pad.Oracle.Crypto one_time_pad.Oracle.Bridge

/-- `Crypto.otp.keygen` samples a uniform key. -/
theorem otp_keygen_eq : (otp.keygen : ProbComp Block) = $ᵗ Block := by
  show _ = (arrayEquiv (n := 16#usize)).symm <$> ($ᵗ (List.Vector U8 16))
  rw [map_eq_bind_pure_comp]
  rfl

/-- For all messages `m₀` and `m₁`, `otp.encrypt k m₀` and `otp.encrypt k m₁` with
`k ← otp.keygen` have the same distribution. This is VCVio's `ciphertextRowsEqualAt`. -/
theorem otp_ciphertextRowsEqual : otp.ciphertextRowsEqualAt := by
  let : MeasurableSpace Block := ⊤
  have hxor (msg : Block) : Function.Bijective (fun key => xor key msg) := by
    refine Function.Involutive.bijective fun key => ?_
    rw [Array.eq_iff]
    simp only [Crypto.xor, Array.from_val]
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp only [List.getElem_zipWith]
    apply UScalar.eq_of_val_eq
    simp [UScalar.val_xor]
  exact SymmEncAlg.ciphertextRowsEqualAt_of_uniformKey_of_bijective otp xor
    (by rw [otp_keygen_eq]; exact SampleableType.evalDist_uniformSample)
    (fun _ _ => evalDist_pure _) hxor

/-- `Crypto.otp` is perfectly secret: for every message sampler whose distribution has total
mass 1, the message and the ciphertext are independent. -/
theorem otp_perfectSecrecy : otp.perfectSecrecyAt :=
  SymmEncAlg.perfectSecrecyAt_of_ciphertextRowsEqualAt otp otp_ciphertextRowsEqual

/-- The one-time pad whose algorithms are the extracted code. A key or ciphertext is a `Result`
(the Aeneas type of a run that can fail), so a failure of the extracted code is a value.

* `keygen`: `rng ← seed`, then `(k, _) := keygen inst rng`. The final generator state is dropped.
* `encrypt rk m`: `k ← rk`, then `encrypt k m`. A failed key gives the same failure.
* `decrypt rk rc`: `k ← rk`, `c ← rc`, then `decrypt k c`. A failure gives `none`. -/
def rustOtp {R : Type} (inst : rand_core.CryptoRng R) (seed : ProbComp R) :
    SymmEncAlg ProbComp Block (Result Block) (Result Block) where
  keygen := do
    let rng ← seed
    pure (Prod.fst <$> one_time_pad.keygen inst rng)
  encrypt rk m := pure do
    let k ← rk
    one_time_pad.encrypt k m
  decrypt rk rc := pure <| toOption do
    let k ← rk
    let c ← rc
    one_time_pad.decrypt k c

/-- If `fill_bytes_assumption inst.RngCoreInst seed 16`, then for every `message`, the extracted
code never fails, and its ciphertext has the same distribution as `c ← otp.encrypt k message`
with `k ← otp.keygen`. -/
theorem rustOtp_cipher {R : Type} (inst : rand_core.CryptoRng R) (seed : ProbComp R)
    (h : rand_core.RngCore.fill_bytes_assumption inst.RngCoreInst seed 16) (message : Block) :
    (do let k ← (rustOtp inst seed).keygen
        (rustOtp inst seed).encrypt k message) =ᵈ
    Result.ok <$> (do let k ← otp.keygen
                      otp.encrypt k message) := by
  have hk := bind_call (keygen_bridge inst seed h) (fun k => one_time_pad.encrypt k message)
  simp only [rustOtp, bind_assoc, pure_bind]
  refine hk.trans ?_
  simp [otp, Spec.encrypt_eq, xorBlock_eq_xor, map_eq_bind_pure_comp]

/-- If `fill_bytes_assumption inst.RngCoreInst seed 16`, then `rustOtp inst seed` is perfectly
secret: for every message sampler whose distribution has total mass 1, the message and the
ciphertext are independent. The experiment calls `keygen` once, so the budget of 16 bytes covers
it. The module docstring lists what the experiment does not cover. -/
theorem rustOtp_perfectSecrecy {R : Type} (inst : rand_core.CryptoRng R) (seed : ProbComp R)
    (h : rand_core.RngCore.fill_bytes_assumption inst.RngCoreInst seed 16) :
    (rustOtp inst seed).perfectSecrecyAt :=
  SymmEncAlg.perfectSecrecyAt_of_ciphertextRowsEqualAt _ fun m₀ m₁ =>
    (rustOtp_cipher inst seed h m₀).trans
      (((otp_ciphertextRowsEqual m₀ m₁).map Result.ok).trans (rustOtp_cipher inst seed h m₁).symm)

/-- If `fill_bytes_assumption inst.RngCoreInst seed 16`, then `rustOtp inst seed` is complete:
for every message, `keygen`, `encrypt` and `decrypt` return the message with probability 1. -/
theorem rustOtp_complete {R : Type} (inst : rand_core.CryptoRng R) (seed : ProbComp R)
    (h : rand_core.RngCore.fill_bytes_assumption inst.RngCoreInst seed 16) :
    (rustOtp inst seed).Complete := by
  intro message
  let g : Result Block → Option Block := fun r =>
    toOption (r >>= fun k => (r >>= fun k => one_time_pad.encrypt k message) >>= fun c =>
      one_time_pad.decrypt k c)
  have hk := (keygen_bridge inst seed h).map g
  have e : (rustOtp inst seed).completenessExperiment message =
      g <$> (do let rng ← seed; pure (Prod.fst <$> one_time_pad.keygen inst rng)) := by
    simp [SymmEncAlg.completenessExperiment, rustOtp, g, map_eq_bind_pure_comp]
    simp only [Function.comp_def, Aeneas.Std.bind_tc_eq, Aeneas.Std.bind_assoc,
      Aeneas.Std.pure_bind, Aeneas.Std.pure_tc_eq]
  have hg : ∀ k, g (Result.ok k) = some message := fun k => by
    simp [g, Spec.encrypt_eq, Spec.decrypt_encrypt, toOption]
  have hc : (g <$> do let k ← otp.keygen; pure (Result.ok k)) =
      (fun _ => some message) <$> otp.keygen := by
    simp [map_eq_bind_pure_comp, hg]
  let : MeasurableSpace Block := ⊤
  rw [e, hk.evalDist_eq, hc, evalDist_map_const, otp_keygen_eq]
  simp

end one_time_pad.Oracle.Security
