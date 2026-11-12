import Common.Result
import Common.Byte
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The generator as an oracle

Aeneas extracts a function that is generic in its generator `R : RngCore` as a deterministic
function of a generator value. This file gives the oracle form of the bridge to probabilities.

* `FillSpec` is the oracle of `fill_bytes`: a query is a buffer, the answer is the filled buffer.
* `fillImpl fill` answers each query with the `fill_bytes` of a generator, so `runProg fill p`
  runs an oracle program `p` with that generator. An example proves, by unfolding, that its
  extracted function is `runProg fill p` for every generator.
* `unifImpl` answers each query with fresh uniform bytes of the length of the buffer.
* `constFill b` is the generator that answers every call with `b`. It runs the extracted code on
  a given answer, so the deterministic part of a program is the extracted code itself.

Each extraction emits its own `RngCore` structure, so this file takes only the method
`fill_bytes`, as a function `Fill R`.
-/

namespace BridgingExamples.RngOracle

open Aeneas.Std OracleSpec OracleComp

/-- The oracle of `fill_bytes`. A query is a buffer, and its answer is the filled buffer. -/
abbrev FillSpec : OracleSpec (Slice U8) := Slice U8 →ₒ Slice U8

/-- The `fill_bytes` method of a generator of type `R`, as Aeneas extracts it. -/
abbrev Fill (R : Type) : Type := R → Slice U8 → Result (R × Slice U8)

/-- `fillImpl fill` answers the query `s` in the state `rng` with `fill rng s`. -/
def fillImpl {R : Type} (fill : Fill R) : QueryImpl FillSpec (StateT R Result) :=
  fun s rng => do
    let (rng1, s1) ← fill rng s
    Result.ok (s1, rng1)

/-- `runProg fill p rng` runs the oracle program `p` with the generator `fill`, from `rng`. -/
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

/-- `unifImpl` answers the query `s` with uniform bytes of length `s.length`. -/
def unifImpl : QueryImpl FillSpec ProbComp := fun s => do
  let v ← $ᵗ (List.Vector U8 s.length)
  pure (sliceOfVector s v)

/-- The generator that answers every call with `b`. -/
def constFill (b : Slice U8) : Fill Unit := fun _ _ => Result.ok ((), b)

end BridgingExamples.RngOracle
