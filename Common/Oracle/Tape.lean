import Common.Oracle.Rng

/-!
# A generator that satisfies `IdealRng`

The state of `tapeFill` is a tape of bytes. A query reads the next bytes of the tape. A uniform
tape of `n` bytes satisfies `IdealRng` with the budget `n` (`idealRng_tape`).
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

/-- If the tape has at least `s.length` bytes, then `tapeFill` answers the query `s` with the
prefix of the tape, and the program continues on the rest of the tape. -/
theorem run_tapeFill_query_bind {β : Type} (s : Slice U8) (k : Slice U8 → OracleComp FillSpec β)
    (tape : List U8) (h : s.length ≤ tape.length) :
    (simulateQ (fillImpl tapeFill) ((liftM (FillSpec.query s) : OracleComp FillSpec _) >>= k)).run
        tape =
      (simulateQ (fillImpl tapeFill) (k (tapePrefix s tape))).run (tape.drop s.length) := by
  have hq : (fillImpl tapeFill s).run tape =
      Result.ok (tapePrefix s tape, tape.drop s.length) := by
    simp only [fillImpl, tapeFill, StateT.run, h, ↓reduceIte]
    exact Aeneas.Std.bind_ok _ _
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hq]
  exact Aeneas.Std.bind_ok _ _

/-- If `ByteBound p n`, then `p` run with `tapeFill` on a uniform tape of `n` bytes, with the final
tape dropped, has the distribution of `Result.ok <$> simulateQ unifImpl p`. In particular, the run
never fails. -/
theorem tape_sim {β : Type} (p : OracleComp FillSpec β) :
    ∀ n, ByteBound p n →
      (do let v ← $ᵗ (List.Vector U8 n)
          pure (Prod.fst <$> (simulateQ (fillImpl tapeFill) p).run v.val)) =ᵈ
      (Result.ok <$> simulateQ unifImpl p) := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    intro n _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact OracleComp.EvalDistEq.bind_const _ _
  | query_bind s k ih =>
    intro n hb
    rw [ByteBound, isQueryBound_query_bind_iff] at hb
    obtain ⟨hs, hk⟩ := hb
    have e : ∀ v : List.Vector U8 n,
        Prod.fst <$> (simulateQ (fillImpl tapeFill)
            ((liftM (FillSpec.query s) : OracleComp FillSpec _) >>= k)).run v.val =
          Prod.fst <$> (simulateQ (fillImpl tapeFill) (k (tapePrefix s v.val))).run
            (v.val.drop s.length) := fun v =>
      congrArg _ (run_tapeFill_query_bind s k v.val (by rw [v.property]; exact hs))
    simp only [e]
    refine (uniformVector_split s.length n hs (fun l => pure (Prod.fst <$>
      (simulateQ (fillImpl tapeFill) (k (tapePrefix s l))).run (l.drop s.length)))).trans ?_
    have e2 : ∀ (a : List.Vector U8 s.length) (b : List U8),
        tapePrefix s (a.val ++ b) = sliceOfVector s a ∧ (a.val ++ b).drop s.length = b := by
      intro a b
      refine ⟨(Slice.eq_iff _ _).mpr ?_, List.drop_left' a.property⟩
      rw [tapePrefix, Slice.from_val, sliceOfVector_val]
      exact List.take_left' a.property
    simp only [e2, simulateQ_bind, simulateQ_spec_query, unifImpl, bind_assoc, pure_bind,
      map_bind]
    exact EvalDistEq.bind_right _ fun a => ih _ _ (hk _)

/-- A uniform tape of `n` bytes satisfies `IdealRng` with the budget `n`. -/
theorem idealRng_tape (n : ℕ) : IdealRng tapeFill (tapeSeed n) n := by
  intro α p hp
  have e : ∀ t, Prod.fst <$> runProg tapeFill p t =
      (Prod.fst <$> (simulateQ (fillImpl tapeFill) p).run t) >>= id := by
    intro t
    have hok : ∀ {γ : Type} (x : γ), Result.ok x = pure x := fun _ => rfl
    have hbind : ∀ {γ δ : Type} (x : Result γ) (f : γ → Result δ),
        Aeneas.Std.bind x f = x >>= f := fun _ _ => rfl
    simp only [runProg, hok, hbind, map_bind, bind_map_left, map_pure, bind_pure, uncurry,
      id]
  have h := (tape_sim p n hp).map (fun r => r >>= id)
  simp only [tapeSeed, e, bind_map_left]
  simpa [map_bind] using h

end BridgingExamples.Oracle
