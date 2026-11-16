import Common.Byte
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.EvalDist.EvalDistEq
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The generator as an oracle

A generator method `fill_bytes`, as Aeneas extracts it, answers the queries of an oracle program.
Each extraction emits its own `RngCore` structure, so these definitions take only the method, as a
`Fill R`.
-/

namespace BridgingExamples.Oracle

open Aeneas Aeneas.Std OracleSpec OracleComp

/-- The oracle of `fill_bytes`. A query is a buffer, and its answer is the filled buffer. The
type does not relate the lengths of a query and its answer. In Rust, `fill_bytes` writes into its
argument, so the length cannot change, but the Aeneas model returns a new slice. -/
abbrev FillSpec : OracleSpec (Slice U8) := Slice U8 →ₒ Slice U8

/-- The method `fill_bytes` of a generator with state type `R`. -/
abbrev Fill (R : Type) : Type := R → Slice U8 → Result (R × Slice U8)

/-- `fillImpl fill` answers the query `s` in the state `rng` with `fill rng s`. -/
def fillImpl {R : Type} (fill : Fill R) : QueryImpl FillSpec (StateT R Result) :=
  fun s rng => do
    let (rng1, s1) ← fill rng s
    Result.ok (s1, rng1)

/-- `runProg fill p rng` runs `p` with `fill` from the state `rng`, and returns the result of `p`
and the final state. It fails or diverges at the first failure or divergence of `fill` or of
`p`. -/
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

/-- Dropping the final state of `runProg fill p rng` is dropping the final state of the simulation
of `p` and flattening the nested `Result`. -/
theorem fst_runProg {R α : Type} (fill : Fill R) (p : OracleComp FillSpec (Result α)) (rng : R) :
    Prod.fst <$> runProg fill p rng =
      (Prod.fst <$> (simulateQ (fillImpl fill) p).run rng) >>= id := by
  have hok : ∀ {γ : Type} (x : γ), Result.ok x = pure x := fun _ => rfl
  have hbind : ∀ {γ δ : Type} (x : Result γ) (f : γ → Result δ),
      Aeneas.Std.bind x f = x >>= f := fun _ _ => rfl
  simp only [runProg, hok, hbind, map_bind, bind_map_left, map_pure, bind_pure, uncurry, id]

/-- `unifImpl` answers the query `s` with a uniform byte vector of length `s.length`, sampled with
fresh randomness for each query. The answer does not depend on the content of `s`. -/
def unifImpl : QueryImpl FillSpec ProbComp := fun s => do
  let v ← $ᵗ (List.Vector U8 s.length)
  pure (sliceOfVector s v)

/-- The stateless generator that answers every query with `b`. -/
def constFill (b : Slice U8) : Fill Unit := fun _ _ => Result.ok ((), b)

/-- `ByteBound p n`: on every path, the queries of `p` ask for at most `n` bytes in total. The
query `s` asks for `s.length` bytes. -/
def ByteBound {α : Type} (p : OracleComp FillSpec α) (n : ℕ) : Prop :=
  p.IsQueryBound n (fun s b => s.length ≤ b) (fun s b => b - s.length)

/-- `IdealRng fill seed n`: for every oracle program `p` with `ByteBound p n`, these two
computations have the same distribution:

* sample a state `rng` from `seed`, run `p` with `fill` from `rng`, and drop the final state;
* run `p` with `unifImpl`.

`p` picks each query from the earlier answers, and one state is threaded through all the
queries, so the condition is on the joint distribution of the answers. `unifImpl` never fails, so
`fill` must fail with probability zero on queries within the budget. The condition says nothing
about the other methods of the generator.

The equality is exact, so the condition idealizes a real generator. If the support of `seed` has
fewer than `256 ^ n` states, then no `fill` satisfies the condition. This is not proved in Lean.
The witness is the program that asks for `n` bytes and returns them. If `n > Usize.max`, it asks
for one byte at a time. It has `256 ^ n` results under `unifImpl`, and at most one result for each
state of `seed`. So a generator that expands a seed of `k` bytes satisfies the condition for no
budget above `k`. The usual cryptographic guarantee, a small advantage against computationally
bounded distinguishers, is not stated here.

`p` has no access to the state, and the final state is dropped. So the condition does not model
an adversary that reads, sets or copies the state, and a `fill` can satisfy the condition while it
keeps a copy of every byte it returns.

A uniform tape of `n` bytes satisfies the condition (`idealRng_tape` in
`Common/Oracle/EntropyIdealRng.lean`).
-/
def IdealRng {R : Type} (fill : Fill R) (seed : ProbComp R) (n : ℕ) : Prop :=
  ∀ {α : Type} (p : OracleComp FillSpec (Result α)), ByteBound p n →
    (do let rng ← seed
        pure (Prod.fst <$> runProg fill p rng)) =ᵈ
    simulateQ unifImpl p

end BridgingExamples.Oracle
