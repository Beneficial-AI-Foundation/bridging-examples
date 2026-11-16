import Common.Oracle.Entropy

/-!
# `EntropyRng` and `IdealRng`

`EntropyRng fill states` implies `IdealRng fill (states n) n` for every `n`
(`idealRng_of_entropyRng`). So a uniform tape satisfies `IdealRng` (`idealRng_tape`). The converse
is false: `logFill` satisfies `IdealRng` and fails `EntropyRng` for every family
(`idealRng_logFill`, `not_entropyRng_logFill`). So `IdealRng` is the weaker assumption.
-/

namespace BridgingExamples.Oracle

open Aeneas Aeneas.Std OracleSpec OracleComp

/-! ## `EntropyRng` implies `IdealRng` -/

/-- If `EntropyRng fill states` and `ByteBound p n`, then `p` run with `fill` from a state in
`states n`, with the final state dropped, has the distribution of
`Result.ok <$> simulateQ unifImpl p`. -/
theorem entropyRng_sim {R β : Type} (fill : Fill R) (states : ℕ → ProbComp R)
    (h : EntropyRng fill states) (p : OracleComp FillSpec β) :
    ∀ n, ByteBound p n →
      (do let rng ← states n
          pure (Prod.fst <$> (simulateQ (fillImpl fill) p).run rng)) =ᵈ
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
    obtain ⟨m, rfl⟩ : ∃ m, n = m + s.length := ⟨n - s.length, by omega⟩
    have hk' : ∀ x, ByteBound (k x) m := fun x => by
      have := hk x
      rwa [Nat.add_sub_cancel] at this
    -- The run, as a function of the answer of `fill` to the first query.
    let G : Result (R × Slice U8) → Result β := fun r =>
      Prod.fst <$> Aeneas.Std.bind r (fun q => (simulateQ (fillImpl fill) (k q.2)).run q.1)
    have e : ∀ rng, Prod.fst <$> (simulateQ (fillImpl fill)
        ((liftM (FillSpec.query s) : OracleComp FillSpec _) >>= k)).run rng =
          G (fill rng s) := by
      intro rng
      simp only [G, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      show Prod.fst <$> Aeneas.Std.bind (Aeneas.Std.bind (fill rng s)
          fun q => Result.ok (q.2, q.1)) _ = _
      simp only [Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok]
    simp only [e]
    have step := (h m s).bind_left (fun r => (pure (G r) : ProbComp _))
    simp only [bind_assoc, pure_bind] at step
    refine step.trans ?_
    simp only [G, Aeneas.Std.bind_ok, simulateQ_bind, simulateQ_spec_query, unifImpl,
      bind_assoc, pure_bind, map_bind]
    exact EvalDistEq.bind_right _ fun a => ih _ _ (hk' _)

/-- `EntropyRng fill states` implies `IdealRng fill (states n) n` for every `n`. -/
theorem idealRng_of_entropyRng {R : Type} (fill : Fill R) (states : ℕ → ProbComp R)
    (h : EntropyRng fill states) (n : ℕ) : IdealRng fill (states n) n := by
  intro α p hp
  have h' := (entropyRng_sim fill states h p n hp).map (fun r => r >>= id)
  simp only [fst_runProg]
  simpa [map_bind] using h'

/-- A uniform tape of `n` bytes satisfies `IdealRng` with the budget `n`. -/
theorem idealRng_tape (n : ℕ) : IdealRng tapeFill (tapeSeed n) n :=
  idealRng_of_entropyRng tapeFill tapeSeed entropyRng_tape n

/-! ## `IdealRng` does not imply `EntropyRng` -/

/-- The tape generator with a log. Its state is a tape and a log. It answers like `tapeFill` on
the tape and appends each answer to the log. -/
def logFill : Fill (List U8 × List U8) := fun rng s =>
  if s.length ≤ rng.1.length then
    Result.ok ((rng.1.drop s.length, rng.2 ++ (tapePrefix s rng.1).val), tapePrefix s rng.1)
  else Result.fail .panic

/-- A uniform tape of `n` bytes and an empty log. -/
def logSeed (n : ℕ) : ProbComp (List U8 × List U8) := (fun tape => (tape, [])) <$> tapeSeed n

/-- Without the final state, a run with `logFill` is a run with `tapeFill` on the tape. -/
theorem fst_run_logFill {β : Type} (p : OracleComp FillSpec β) :
    ∀ (tape log : List U8),
      Prod.fst <$> (simulateQ (fillImpl logFill) p).run (tape, log) =
        Prod.fst <$> (simulateQ (fillImpl tapeFill) p).run tape := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    intro tape log
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind s k ih =>
    intro tape log
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases hs : s.length ≤ tape.length
    · have hl : (fillImpl logFill s).run (tape, log) =
          Result.ok (tapePrefix s tape, (tape.drop s.length, log ++ (tapePrefix s tape).val)) := by
        simp only [fillImpl, logFill, StateT.run, hs, ↓reduceIte]
        exact Aeneas.Std.bind_ok _ _
      have ht : (fillImpl tapeFill s).run tape =
          Result.ok (tapePrefix s tape, tape.drop s.length) := by
        simp only [fillImpl, tapeFill, StateT.run, hs, ↓reduceIte]
        exact Aeneas.Std.bind_ok _ _
      rw [hl, ht]
      simpa using ih (tapePrefix s tape) (tape.drop s.length) (log ++ (tapePrefix s tape).val)
    · simp [fillImpl, logFill, tapeFill, StateT.run, hs, map_eq_bind_pure_comp]

/-- `logFill` satisfies `IdealRng` from a uniform tape of `n` bytes, like `tapeFill`. -/
theorem idealRng_logFill (n : ℕ) : IdealRng logFill (logSeed n) n := by
  intro α p hp
  have e : ∀ tape, Prod.fst <$> runProg logFill p (tape, []) =
      Prod.fst <$> runProg tapeFill p tape := fun tape => by
    rw [fst_runProg, fst_runProg, fst_run_logFill]
  simp only [logSeed, bind_map_left, e]
  exact idealRng_tape n p hp

/-- A buffer of one byte. -/
def oneByte : Slice U8 := (Array.repeat 1#usize 0#u8).to_slice

theorem oneByte_length : oneByte.length = 1 := by
  simp only [oneByte, Slice.length, Array.val_to_slice, Aeneas.Std.Array.length_eq]; rfl

/-- `logFill` satisfies `EntropyRng` for no family: after a call for one byte, the last entry of
the log is the returned byte, but `EntropyRng` makes the returned byte independent of the
state. -/
theorem not_entropyRng_logFill (states : ℕ → ProbComp (List U8 × List U8)) :
    ¬ EntropyRng logFill states := by
  intro h
  have hsupp := support_eq_of_evalDistEq (h 0 oneByte)
  obtain ⟨rng, hrng⟩ := support_nonempty (states 0)
  -- A byte that is not the last entry of the log of `rng`.
  obtain ⟨x, hx⟩ : ∃ x : U8, rng.2.getLast? ≠ some x := by
    by_cases h0 : rng.2.getLast? = some 0#u8
    · exact ⟨1#u8, by rw [h0]; decide⟩
    · exact ⟨0#u8, h0⟩
  let bytes : List.Vector U8 oneByte.length := ⟨[x], by rw [oneByte_length]; rfl⟩
  have hmem : Result.ok (rng, sliceOfVector oneByte bytes) ∈
      support (do let bytes ← $ᵗ (List.Vector U8 oneByte.length)
                  let rng ← states 0
                  pure (Result.ok (rng, sliceOfVector oneByte bytes)) : ProbComp _) := by
    simp only [mem_support_bind_iff, mem_support_pure_iff]
    exact ⟨bytes, mem_support_uniformSample _, rng, hrng, rfl⟩
  rw [← hsupp] at hmem
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hmem
  obtain ⟨rng0, -, hfill⟩ := hmem
  simp only [logFill] at hfill
  split_ifs at hfill with hs
  · simp only [Result.ok.injEq, Prod.mk.injEq] at hfill
    obtain ⟨hrng0, hb⟩ := hfill
    apply hx
    rw [hrng0, ← hb, sliceOfVector_val]
    simp [bytes]
  · exact ok_not_fail hfill

/-- `IdealRng` does not imply `EntropyRng`: `logFill` satisfies `IdealRng` for every budget and
`EntropyRng` for no family. -/
theorem idealRng_not_entropyRng :
    (∀ n, IdealRng logFill (logSeed n) n) ∧ ∀ states, ¬ EntropyRng logFill states :=
  ⟨idealRng_logFill, not_entropyRng_logFill⟩

end BridgingExamples.Oracle
