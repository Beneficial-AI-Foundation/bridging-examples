import Common.Oracle.Rng

/-!
# A tape generator

The state of `tapeFill` is a tape of bytes. A query reads the next bytes of the tape. A uniform
tape satisfies `EntropyRng` (`entropyRng_tape` in `Common/Oracle/Entropy.lean`) and `IdealRng`
(`idealRng_tape` in `Common/Oracle/EntropyIdealRng.lean`).
-/

namespace BridgingExamples.Oracle

open Aeneas Aeneas.Std OracleSpec OracleComp

/-- The first `s.length` bytes of `tape`, as a slice. -/
def tapePrefix (s : Slice U8) (tape : List U8) : Slice U8 :=
  Slice.from (tape.take s.length) (le_trans (List.length_take_le _ _) s.property)

/-- The generator whose state is the unread tape. It answers the query `s` with the first
`s.length` bytes of the tape and keeps the rest. It fails if the tape is too short. -/
def tapeFill : Fill (List U8) := fun tape s =>
  if s.length ≤ tape.length then Result.ok (tape.drop s.length, tapePrefix s tape)
  else Result.fail .panic

/-- A uniform tape of `n` bytes. -/
def tapeSeed (n : ℕ) : ProbComp (List U8) := (fun v => v.val) <$> ($ᵗ (List.Vector U8 n))

/-- A uniform vector of length `n` is a uniform prefix of length `m ≤ n` followed by an
independent uniform suffix of length `n - m`. -/
theorem uniformVector_split {γ : Type} :
    ∀ (m n : ℕ), m ≤ n → ∀ g : List U8 → ProbComp γ,
      (do let v ← $ᵗ (List.Vector U8 n); g v.val) =ᵈ
      (do let a ← $ᵗ (List.Vector U8 m)
          let b ← $ᵗ (List.Vector U8 (n - m))
          g (a.val ++ b.val)) := by
  intro m
  induction m with
  | zero =>
    intro n _ g
    have : (fun a : List.Vector U8 0 => (do
        let b ← $ᵗ (List.Vector U8 (n - 0)); g (a.val ++ b.val))) =
        fun _ => (do let v ← $ᵗ (List.Vector U8 n); g v.val) := by
      funext a
      rw [List.Vector.eq_nil a]
      rfl
    rw [this]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | succ m ih =>
    intro n hn g
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_add_right]
    refine ((SampleableType.evalDistEq_uniformSample_vector_succ n).bind_left _).trans ?_
    refine EvalDistEq.trans ?_
      ((SampleableType.evalDistEq_uniformSample_vector_succ m).bind_left _).symm
    simp only [bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun x => ?_
    exact ih n (by omega) (fun l => g (x :: l))

end BridgingExamples.Oracle
