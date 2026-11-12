import BridgingExamples.ByteMask.Spec
import BridgingExamples.ByteMask.Crypto
import Common.Correspondence
import Common.Metadata
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Bridge for `mask`, with the generator as an oracle

Aeneas extracts `mask` as a deterministic function of a generator `inst : RngCore R` and a
generator value `rng : R`. The bridge to `Crypto.mask` has three steps.

1. `mask_eq_prog`: for every generator, `mask` is the oracle program `maskProg`, answered by the
   generator's `fill_bytes`. The program asks for the one-byte buffer `padBuf`, then runs
   `maskRest` on the answer. `maskRest v b` replays the extracted `mask` with the generator that
   returns `b`. The theorem has no assumption on the generator, and keeps the final generator
   state and failures.
2. `maskProg_bridge`: answered by uniform bytes (`unifImpl`), `maskProg` has the distribution of
   `Crypto.mask`. No generator appears in this theorem.
3. `mask_bridge`: if the generator, from a sampled state, answers oracle programs like `unifImpl`
   (the assumption `IdealRng`), then the extracted `mask` has the distribution of `Crypto.mask`.

`IdealRng` is the only assumption on the generator. It is an exact equality, so it is an
idealization of a real generator. See its docstring. A uniform tape satisfies it
(`idealRng_tape`), so `mask_bridge` is not vacuous.

The oracle of `fill_bytes` (`FillSpec`, `fillImpl`, `runProg`, `unifImpl`, `constFill`) is
defined here, because the bridge theorems state their results with it. Each extraction emits its
own `RngCore` structure, so these definitions take only the method `fill_bytes`, as a `Fill R`.
-/

namespace byte_mask.Bridge

open Aeneas Aeneas.Std BridgingExamples byte_mask.Spec OracleSpec OracleComp

/-! ## The generator as an oracle -/

/-- The oracle of `fill_bytes`. A query is a buffer, and its answer is the filled buffer. -/
abbrev FillSpec : OracleSpec (Slice U8) := Slice U8 →ₒ Slice U8

/-- The `fill_bytes` method of a generator of type `R`, as Aeneas extracts it. -/
abbrev Fill (R : Type) : Type := R → Slice U8 → Result (R × Slice U8)

/-- `fillImpl fill` answers the query `s` in the state `rng` with `fill rng s`. -/
def fillImpl {R : Type} (fill : Fill R) : QueryImpl FillSpec (StateT R Result) :=
  fun s rng => do
    let (rng1, s1) ← fill rng s
    Result.ok (s1, rng1)

/-- `runProg fill p rng` runs the oracle program `p` with the generator `fill`, from the state
`rng`. It returns the result of `p` and the final state. A failure of `fill` or of `p` is a
failure of `runProg`. -/
def runProg {R α : Type} (fill : Fill R) (p : OracleComp FillSpec (Result α)) (rng : R) :
    Result (α × R) := do
  let (r, rng1) ← (simulateQ (fillImpl fill) p).run rng
  let a ← r
  Result.ok (a, rng1)

/-- `runProg` on one query `b` followed by `f`: call `fill rng b`, then run `f` on the answer. -/
theorem runProg_query {R α : Type} (fill : Fill R) (b : Slice U8) (f : Slice U8 → Result α)
    (rng : R) :
    runProg fill (do
        let x ← (liftM (FillSpec.query b) : OracleComp FillSpec _)
        return f x) rng =
      Aeneas.Std.bind (fill rng b) fun p =>
        Aeneas.Std.bind (f p.2) fun a => Result.ok (a, p.1) := by
  simp only [runProg, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  show Aeneas.Std.bind (Aeneas.Std.bind (Aeneas.Std.bind (fill rng b)
      fun p => Result.ok (p.2, p.1)) fun q => Result.ok (f q.1, q.2))
      (fun q => Aeneas.Std.bind q.1 fun a => Result.ok (a, q.2)) = _
  simp only [Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok]

/-- The slice of a byte vector of length `s.length`. -/
def sliceOfVector (s : Slice U8) (v : List.Vector U8 s.length) : Slice U8 :=
  Slice.from v.val (by rw [v.property]; exact s.property)

theorem sliceOfVector_val (s : Slice U8) (v : List.Vector U8 s.length) :
    (sliceOfVector s v).val = v.val := Slice.from_val _ _

/-- `unifImpl` answers the query `s` with uniform bytes of length `s.length`, independent of all
earlier answers. -/
def unifImpl : QueryImpl FillSpec ProbComp := fun s => do
  let v ← $ᵗ (List.Vector U8 s.length)
  pure (sliceOfVector s v)

/-- The generator that answers every call with `b` and has no state. -/
def constFill (b : Slice U8) : Fill Unit := fun _ _ => Result.ok ((), b)

/-! ## The assumption on the generator -/

/-- `ByteBound p n`: on every path, the queries of `p` ask for at most `n` bytes in total. The
query `s` asks for `s.length` bytes. -/
def ByteBound {α : Type} (p : OracleComp FillSpec α) (n : ℕ) : Prop :=
  p.IsQueryBound n (fun s b => s.length ≤ b) (fun s b => b - s.length)

/-- `IdealRng fill seed n`: for every oracle program `p` with `ByteBound p n`, these two
computations have the same distribution:

* sample a state `rng` from `seed`, run `p` with `fill` from `rng`, and drop the final state;
* run `p` with `unifImpl`.

The state is sampled once and threaded through all the queries of `p`. So the assumption is
about the joint distribution of all the answers to `p`, not about each call alone. The final state
is dropped only at the end of `p`. A failure of `fill` is an observable result.

This is an exact equality, so it is an idealization. If `n ≥ 1` and `seed` has fewer than
`256 ^ n` values in its support, then no `fill` satisfies it: the program that asks for `n` bytes
and returns them has fewer than `256 ^ n` results. A cryptographic generator can at best satisfy
an approximate form, with an error bound, for a bounded class of programs. That form is not
stated here.

The assumption gives `p` no access to the generator state, so it does not model an adversary that
reads, sets or copies that state.

A uniform tape of `n` bytes satisfies it with the budget `n` (`idealRng_tape`), so it is not
vacuous. -/
@[assumption_for mask]
def IdealRng {R : Type} (fill : Fill R) (seed : ProbComp R) (n : ℕ) : Prop :=
  ∀ {α : Type} (p : OracleComp FillSpec (Result α)), ByteBound p n →
    (do let rng ← seed
        pure (Prod.fst <$> runProg fill p rng)) =ᵈ
    simulateQ unifImpl p

/-! ## A generator that satisfies the assumption -/

/-- The slice of the first `s.length` bytes of the tape `tape`. -/
def tapePrefix (s : Slice U8) (tape : List U8) : Slice U8 :=
  Slice.from (tape.take s.length) (le_trans (List.length_take_le _ _) s.property)

/-- The generator whose state is the unread tape. It answers the query `s` with the first
`s.length` bytes of the tape, and keeps the rest. It fails if the tape is too short. -/
def tapeFill : Fill (List U8) := fun tape s =>
  if s.length ≤ tape.length then Result.ok (tape.drop s.length, tapePrefix s tape)
  else Result.fail .panic

/-- A uniform tape of `n` bytes. -/
def tapeSeed (n : ℕ) : ProbComp (List U8) := (fun v => v.val) <$> ($ᵗ (List.Vector U8 n))

/-- A uniform vector of length `n` is a uniform prefix of length `m` followed by an independent
uniform suffix of length `n - m`. -/
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
prefix of the tape, and the program goes on with the rest of the tape. -/
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

/-- For every oracle program `p` with `ByteBound p n`, running `p` with `tapeFill` on a uniform
tape of `n` bytes and dropping the final tape has the distribution of `p` run with `unifImpl`.
The tape is never too short, so the run is a success. -/
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

/-- The uniform tape of `n` bytes satisfies `IdealRng` with the budget `n`. -/
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

/-! ## `mask` as an oracle program -/

/-- The generator whose `fill_bytes` returns `b`. `mask` does not call `next_u32` or `next_u64`,
so they fail. -/
def constRng (b : Slice U8) : rand_core.RngCore Unit where
  next_u32 _ := Result.fail .panic
  next_u64 _ := Result.fail .panic
  fill_bytes := constFill b

/-- `maskRest v b` replays the extracted `mask` on `v` with the generator `constRng b`, and drops
its state. It is the extracted `mask` run on the answer `b`. -/
def maskRest (v : U8) (b : Slice U8) : Result (U8 × U8) := do
  let (p, _) ← mask (constRng b) () v
  Result.ok p

/-- `mask` as an oracle program: one query for `padBuf`, then `maskRest` on the answer. -/
def maskProg (v : U8) : OracleComp FillSpec (Result (U8 × U8)) := do
  let b ← (liftM (FillSpec.query padBuf) : OracleComp FillSpec _)
  return maskRest v b

/-- For every generator `inst` and state `rng`, `mask inst rng v` is `maskProg v` run with
`inst.fill_bytes` from `rng`. The equality is on the full `Result`, with the final state. -/
@[bridge_for mask]
theorem mask_eq_prog {R : Type} (inst : rand_core.RngCore R) (rng : R) (v : U8) :
    mask inst rng v = runProg inst.fill_bytes (maskProg v) rng := by
  rw [maskProg, runProg_query]
  simp only [maskRest, mask, constRng, constFill, lift, Array.to_slice_mut, padBuf,
    Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok, uncurry_eq]

/-- `maskProg v` asks for at most one byte. -/
theorem maskProg_byteBound (v : U8) : ByteBound (maskProg v) 1 := by
  simp [ByteBound, maskProg, padBuf_length]

/-- If the answer is the one byte `x`, then `maskRest` returns the pad `x` and `v ^^^ x`. -/
theorem maskRest_of_val (v x : U8) (b : Slice U8) (hb : b.val = [x]) :
    maskRest v b = Result.ok (x, v ^^^ x) := by
  simp only [maskRest, mask, constRng, constFill, lift, Array.to_slice_mut,
    Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok, uncurry_eq]
  simp [Array.from_slice, Array.index_usize, hb]

/-- The first element is a bijection from byte vectors of length 1 to bytes. -/
theorem head_bijective : Function.Bijective (List.Vector.head : List.Vector U8 1 → U8) := by
  refine ⟨fun a b h => ?_, fun x => ⟨x ::ᵥ List.Vector.nil, by simp⟩⟩
  rw [← List.Vector.cons_head_tail a, ← List.Vector.cons_head_tail b, h,
    List.Vector.eq_nil a.tail, List.Vector.eq_nil b.tail]

/-- Answered by `unifImpl`, `maskProg v` samples a uniform buffer of the length of `padBuf`
and runs `maskRest` on it. -/
theorem simulateQ_maskProg (v : U8) :
    simulateQ unifImpl (maskProg v) =
      (do let w ← $ᵗ (List.Vector U8 padBuf.length)
          pure (maskRest v (sliceOfVector padBuf w))) := by
  simp [maskProg, unifImpl]
  rfl

/-- Answered by `unifImpl`, `maskProg v` has the distribution of `Result.ok <$> Crypto.mask v`.
No generator appears in this theorem. -/
@[bridge_for mask]
theorem maskProg_bridge (v : U8) :
    simulateQ unifImpl (maskProg v) =ᵈ
    (do let y ← Crypto.mask v
        pure (Result.ok y)) := by
  rw [simulateQ_maskProg]
  refine (uniformVector_bind_congr padBuf_length _
    (fun w : List.Vector U8 1 => pure (Result.ok (w.head, v ^^^ w.head))) ?_).trans ?_
  · intro w
    congr 1
    apply maskRest_of_val
    rw [sliceOfVector_val]
    obtain ⟨l, hl⟩ := w
    rw [padBuf_length] at hl
    match l, hl with
    | [x], _ => rfl
  · have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective head_bijective).map
      (fun x => Result.ok (x, v ^^^ x))
    simpa [Crypto.mask, map_eq_bind_pure_comp] using h

/-- The extracted `mask`, replayed with `constRng` on a uniform one-byte buffer, has the
distribution of `Result.ok <$> Crypto.mask v`. The state of `constRng` is the unit value, and
`maskRest` drops it. -/
@[bridge_for mask]
theorem mask_uniform (v : U8) :
    (do let w ← $ᵗ (List.Vector U8 padBuf.length)
        pure (maskRest v (sliceOfVector padBuf w))) =ᵈ
    (do let y ← Crypto.mask v
        pure (Result.ok y)) :=
  simulateQ_maskProg v ▸ maskProg_bridge v

/-- Under the assumption `IdealRng inst.fill_bytes seed 1`, the extracted `mask`, run from a state
sampled by `seed`, has the distribution of `Result.ok <$> Crypto.mask v`. The final generator
state is dropped.

The theorem is about one call of `mask`. It says nothing about several calls on one generator
state: that needs `IdealRng` with a larger budget and a program for all the calls. The theorem is
only as strong as `IdealRng`, which is an idealization of a real generator. -/
theorem mask_bridge {R : Type} (inst : rand_core.RngCore R) (seed : ProbComp R)
    (h : IdealRng inst.fill_bytes seed 1) (v : U8) :
    (do let rng ← seed
        pure (Prod.fst <$> mask inst rng v)) =ᵈ
    (do let y ← Crypto.mask v
        pure (Result.ok y)) := by
  simp only [mask_eq_prog]
  exact (h (maskProg v) (maskProg_byteBound v)).trans (maskProg_bridge v)

/-- `unmask` is deterministic: it has the distribution of `Crypto.unmask pad masked`. -/
theorem unmask_bridge (pad masked : U8) :
    (pure (unmask pad masked) : ProbComp _) =ᵈ
    (do let r ← Crypto.unmask pad masked
        pure (Result.ok r)) :=
  bridge_of_spec (Spec.unmask_spec pad masked)

end byte_mask.Bridge
