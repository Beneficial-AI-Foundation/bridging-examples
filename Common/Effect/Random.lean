import Common.Byte
import Common.Oracle.Rng
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# The generator as the `random` effect of `Result`

With `aeneas.patch`, an Aeneas `Result` can sample: `Result.random n` asks for `n` random bytes.
The extracted code does not change, but a generator whose `fill_bytes` samples with
`Result.random` is now a legal argument of the extracted functions.

A model is an oracle program `OracleComp RandSpec α`, with one kind of query, "give me `n` random
bytes". `toResult` reads such a program as a `Result`, with one `random n` node for each query.
A bridge then has two parts:

1. under `RandomFill inst.fill_bytes`, the extracted function is *equal* to `toResult` of the
   model;
2. the model, run with uniform bytes (`uniformImpl`), has the distribution of the Crypto
   definition.

`toResult` and `RandSpec` come from https://github.com/Beneficial-AI-Foundation/toy-bridge.
-/

namespace BridgingExamples.Effect

open Aeneas Aeneas.Std OracleSpec OracleComp BridgingExamples.Oracle

/-- `n` bytes, as `Result.random n` returns them. -/
abbrev Bytes (n : ℕ) := Vector (BitVec 8) n

/-- The oracle of random bytes: the query `n` asks for `n` random bytes. -/
@[reducible] def RandSpec : OracleSpec ℕ := fun n => Bytes n

/-- Ask for `n` random bytes. -/
def randomBytes (n : ℕ) : OracleComp RandSpec (Bytes n) :=
  liftM (OracleSpec.query (spec := RandSpec) n)

/-- The bytes of `Result.random` as a byte vector of the Crypto definitions. -/
def vectorOfBytes {n : ℕ} (b : Bytes n) : List.Vector U8 n :=
  ⟨b.toList.map (⟨·⟩), by simp⟩

/-- The inverse of `vectorOfBytes`. -/
def bytesOfVector {n : ℕ} (v : List.Vector U8 n) : Bytes n :=
  ⟨(v.val.map (·.bv)).toArray, by simp⟩

@[simp] theorem vectorOfBytes_bytesOfVector {n : ℕ} (v : List.Vector U8 n) :
    vectorOfBytes (bytesOfVector v) = v := by
  apply Subtype.ext
  simp [vectorOfBytes, bytesOfVector, Function.comp_def]

/-- `uniformImpl` answers the query `n` with `n` uniform bytes. -/
def uniformImpl : QueryImpl RandSpec ProbComp := fun n => do
  let v ← $ᵗ (List.Vector U8 n)
  pure (bytesOfVector v)

/-! ## Reified programs as Aeneas results -/

variable {α β : Type}

/-- Read an oracle program as an Aeneas result: `pure a` becomes `ok a` and a query `n` becomes a
`random n` node. The result never fails and never diverges.

VCVio embeds `OracleComp` into PolyFun's interaction trees (`OracleComp.toITree`), not into
Aeneas's `ITree`, so the embedding is redone here. -/
def toResult (oa : OracleComp RandSpec α) : Result α :=
  oa.recOn (motive := fun _ => Result α) Result.ok
    (fun n _k ih => Result.vis (.random n) ih)

@[simp] theorem toResult_pure (a : α) : toResult (pure a : OracleComp RandSpec α) = Result.ok a :=
  rfl

theorem toResult_queryBind (n : ℕ) (k : Bytes n → OracleComp RandSpec α) :
    toResult (OracleComp.queryBind (spec := RandSpec) n k) =
      Result.vis (.random n) fun bytes => toResult (k bytes) := rfl

@[simp] theorem toResult_randomBytes (n : ℕ) : toResult (randomBytes n) = Result.random n := rfl

@[simp] theorem toResult_bind (oa : OracleComp RandSpec α) (f : α → OracleComp RandSpec β) :
    toResult (oa >>= f) = Aeneas.Std.bind (toResult oa) fun a => toResult (f a) := by
  induction oa with
  | pure a => simp
  | queryBind n k ih =>
    change toResult (OracleComp.queryBind (spec := RandSpec) n fun u => k u >>= f) =
      Aeneas.Std.bind (toResult (OracleComp.queryBind (spec := RandSpec) n k)) _
    rw [toResult_queryBind, toResult_queryBind, Aeneas.Std.bind_vis]
    congr 1
    funext bytes
    exact ih bytes

@[simp] theorem toResult_map (f : α → β) (oa : OracleComp RandSpec α) :
    toResult (f <$> oa) = Aeneas.Std.bind (toResult oa) fun a => Result.ok (f a) := by
  rw [map_eq_bind_pure_comp, toResult_bind]
  rfl

/-! ## The assumption on `fill_bytes` -/

/-- The slice of the bytes `b`. Its length is that of the slice `buffer`. -/
def sliceOfBytes (buffer : Slice U8) (b : Bytes buffer.length) : Slice U8 :=
  sliceOfVector buffer (vectorOfBytes b)

@[simp] theorem sliceOfBytes_bytesOfVector (buffer : Slice U8)
    (v : List.Vector U8 buffer.length) :
    sliceOfBytes buffer (bytesOfVector v) = sliceOfVector buffer v := by
  simp [sliceOfBytes]

/-- `RandomFill fill`: on a buffer of `k` bytes, `fill` samples `k` bytes with `Result.random`,
returns them in the buffer, and leaves the state unchanged. It never fails.

This is toy-bridge's `OsRngDoesNotFail`, stated for the generic `fill_bytes`, because the Rust
code of the examples does not call `OsRng`. The state does not change, so the generator holds no
entropy: each call samples fresh bytes. A generator that computes its bytes from its state, such
as a seeded PRG, does not satisfy it. -/
def RandomFill {R : Type} (fill : Fill R) : Prop :=
  ∀ (rng : R) (buffer : Slice U8),
    fill rng buffer = Aeneas.Std.bind (Result.random buffer.length) fun b =>
      Result.ok (rng, sliceOfBytes buffer b)

/-- `RandomFill` for a buffer whose length is known as an equation `buffer.length = n`, such as
the slice of a fixed-size array. -/
theorem RandomFill.fill_eq {R : Type} {fill : Fill R} (h : RandomFill fill) (rng : R)
    (buffer : Slice U8) (n : ℕ) (hn : buffer.length = n) :
    fill rng buffer = Aeneas.Std.bind (Result.random n) fun b =>
      Result.ok (rng, Slice.from (vectorOfBytes b).val
        (by rw [(vectorOfBytes b).property, ← hn]; exact buffer.property)) := by
  subst hn
  exact h rng buffer

end BridgingExamples.Effect
