import Generated.Commitment.Funs
import BridgingExamples.LazyOracle.Bridge
import Examples.CommitmentScheme.Common

/-!
This bridge preserves the hash callback's complete success, failure, and divergence result.
The roundtrip theorem specializes to a fixed successful hash and retains the exact RNG state on a
successful draw. `Result.fail` and `Result.div` carry no returned RNG state, so no recovery of
intermediate mutations is claimed. The callback contract is not derived from Rust's `&self`, and
the bridge states no probability or security theorem.
-/

namespace bridge_commitment.Bridge

open bridge_lazy_oracle.Bridge (byteToModel)

def openingToModel (opening : bridge_commitment.Opening) :
    Fin 256 × Fin 256 :=
  (byteToModel opening.message, byteToModel opening.salt)

def HashModels {H : Type}
    (hashInst : bridge_commitment.ByteHash H)
    (hash : H)
    (oracle :
      QueryImpl (CMOracle (Fin 256) (Fin 256) (Fin 256))
        Aeneas.Std.Result) : Prop :=
  ∀ message salt : Aeneas.Std.U8,
    byteToModel <$> hashInst.hash hash message salt =
      oracle (byteToModel message, byteToModel salt)

def commitModel {R : Type}
    (draw : R → Aeneas.Std.Result (Fin 256 × R))
    (oracle :
      QueryImpl (CMOracle (Fin 256) (Fin 256) (Fin 256))
        Aeneas.Std.Result)
    (message : Fin 256)
    (rng : R) :
    Aeneas.Std.Result ((Fin 256 × (Fin 256 × Fin 256)) × R) := do
  let (salt, rng') ← draw rng
  let commitment ← _root_.simulateQ oracle (CMCommit message salt)
  Aeneas.Std.Result.ok ((commitment, (message, salt)), rng')

theorem commit_refines {H R : Type}
    (hashInst : bridge_commitment.ByteHash H)
    (rngInst : bridge_commitment.ByteRng R)
    (hash : H)
    (oracle :
      QueryImpl (CMOracle (Fin 256) (Fin 256) (Fin 256))
        Aeneas.Std.Result)
    (hHash : HashModels hashInst hash oracle)
    (rng : R)
    (message : Aeneas.Std.U8) :
    Prod.map (Prod.map byteToModel openingToModel) id <$>
        bridge_commitment.commit hashInst rngInst hash rng message =
      commitModel
        (fun state => Prod.map byteToModel id <$> rngInst.next_u8 state)
        oracle (byteToModel message) rng := by
  unfold HashModels at hHash
  cases hdraw : rngInst.next_u8 rng with
  | fail error =>
      simp [bridge_commitment.commit, commitModel, hdraw]; rfl
  | div =>
      simp [bridge_commitment.commit, commitModel, hdraw]; rfl
  | ok draw =>
      rcases draw with ⟨salt, rng'⟩
      have hHash' := hHash message salt
      cases hResult : hashInst.hash hash message salt with
      | fail error =>
          simp [bridge_commitment.commit, commitModel, hdraw, hResult, CMCommit, ← hHash']; rfl
      | div =>
          simp [bridge_commitment.commit, commitModel, hdraw, hResult, CMCommit, ← hHash']; rfl
      | ok commitment =>
          simp [bridge_commitment.commit, commitModel, hdraw, hResult, CMCommit, ← hHash']; rfl

theorem verify_refines {H : Type}
    (hashInst : bridge_commitment.ByteHash H)
    (hash : H)
    (oracle :
      QueryImpl (CMOracle (Fin 256) (Fin 256) (Fin 256))
        Aeneas.Std.Result)
    (hHash : HashModels hashInst hash oracle)
    (commitment : Aeneas.Std.U8)
    (opening : bridge_commitment.Opening) :
    bridge_commitment.verify hashInst hash commitment opening =
      _root_.simulateQ oracle
        (CMCheck (byteToModel commitment)
          (openingToModel opening).1
          (openingToModel opening).2) := by
  unfold HashModels at hHash
  have hHash' := hHash opening.message opening.salt
  cases hResult : hashInst.hash hash opening.message opening.salt with
  | fail error =>
      simp [bridge_commitment.verify, openingToModel, CMCheck, hResult, ← hHash']
      rfl
  | div =>
      simp [bridge_commitment.verify, openingToModel, CMCheck, hResult, ← hHash']
      rfl
  | ok digest =>
      simp [bridge_commitment.verify, openingToModel, CMCheck, hResult, ← hHash']
      change
        Aeneas.Std.Result.ok (decide (commitment = digest)) =
          Aeneas.Std.Result.ok (byteToModel commitment == byteToModel digest)
      by_cases hEq : commitment = digest
      · subst digest
        simp
      · have hModelNe : byteToModel commitment ≠ byteToModel digest :=
          fun hModelEq => hEq
            (bridge_lazy_oracle.Bridge.byteToModel_bijective.1 hModelEq)
        simp [hEq, hModelNe]

theorem commit_verify_refines {H R : Type}
    (hashInst : bridge_commitment.ByteHash H)
    (rngInst : bridge_commitment.ByteRng R)
    (hash : H)
    (h : Fin 256 × Fin 256 → Fin 256)
    (hHash :
      HashModels hashInst hash
        (fun query => Aeneas.Std.Result.ok (h query)))
    (rng : R)
    (message : Aeneas.Std.U8) :
    (do
      let ((commitment, opening), rng') ←
        bridge_commitment.commit hashInst rngInst hash rng message
      let accepted ←
        bridge_commitment.verify hashInst hash commitment opening
      Aeneas.Std.Result.ok (accepted, rng')) =
      (fun draw => (true, draw.2)) <$> rngInst.next_u8 rng := by
  unfold HashModels at hHash
  cases hdraw : rngInst.next_u8 rng with
  | fail error =>
      simp [bridge_commitment.commit, hdraw]; rfl
  | div =>
      simp [bridge_commitment.commit, hdraw]; rfl
  | ok draw =>
      rcases draw with ⟨salt, rng'⟩
      have hHash' := hHash message salt
      cases hResult : hashInst.hash hash message salt with
      | fail error =>
          rw [hResult] at hHash'
          change
            Aeneas.Std.Result.fail error =
              Aeneas.Std.Result.ok (h (byteToModel message, byteToModel salt)) at hHash'
          cases hHash'
      | div =>
          rw [hResult] at hHash'
          change
            Aeneas.Std.Result.div =
              Aeneas.Std.Result.ok (h (byteToModel message, byteToModel salt)) at hHash'
          cases hHash'
      | ok commitment =>
          simp [bridge_commitment.commit, bridge_commitment.verify, hdraw, hResult]; rfl

end bridge_commitment.Bridge
