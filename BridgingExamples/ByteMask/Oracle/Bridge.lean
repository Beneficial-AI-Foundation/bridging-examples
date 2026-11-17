import BridgingExamples.ByteMask.Spec
import BridgingExamples.ByteMask.Crypto
import Common.Correspondence
import Common.Metadata
import Common.Oracle.Tape

/-!
# Bridge for `mask`, with the generator as an oracle

Aeneas extracts `mask` as a deterministic function of a generator `inst : RngCore R` and a state
`rng : R`. The bridge to `Crypto.mask` has three steps.

1. `mask_eq_prog`: `mask` is the oracle program `maskProg`, run with `inst.fill_bytes`. This holds
   for every generator, with the final state and failures.
2. `maskProg_bridge`: `maskProg`, run with uniform bytes (`unifImpl`), has the distribution of
   `Result.ok <$> Crypto.mask v`.
3. `mask_bridge`: under `fill_bytes_assumption`, the extracted `mask`, run from a sampled state,
   has the distribution of `Result.ok <$> Crypto.mask v`.

`fill_bytes_assumption` is the only Lean assumption on the generator. Two assumptions stay outside
Lean. First, Aeneas extracts `mask` faithfully. Second, the real generator is `fill_bytes` run
from a state with the distribution `seed`, and this state is independent of the input `v`. The
oracle definitions are in `Common/Oracle/Rng.lean`.
-/

namespace byte_mask.Oracle.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle byte_mask.Spec OracleSpec
  OracleComp

/-! ## `mask` as an oracle program -/

/-- The stateless generator whose `fill_bytes` returns `b`. Its other methods fail, and `mask`
does not call them. -/
def constRng (b : Slice U8) : rand_core.RngCore Unit where
  next_u32 _ := Result.fail .panic
  next_u64 _ := Result.fail .panic
  fill_bytes := constFill b

/-- `maskRest v b`: the extracted `mask` on `v`, with `b` as the answer of `fill_bytes`. -/
def maskRest (v : U8) (b : Slice U8) : Result (U8 × U8) := do
  let (p, _) ← mask (constRng b) () v
  Result.ok p

/-- `mask` as an oracle program: one query for `padBuf`, then `maskRest` on the answer. -/
def maskProg (v : U8) : OracleComp FillSpec (Result (U8 × U8)) := do
  let b ← (liftM (FillSpec.query padBuf) : OracleComp FillSpec _)
  return maskRest v b

/-- For every generator `inst` and state `rng`, `mask inst rng v` is `maskProg v` run with
`inst.fill_bytes` from `rng`, final state and failures included. -/
@[bridge_for mask]
theorem mask_eq_prog {R : Type} (inst : rand_core.RngCore R) (rng : R) (v : U8) :
    mask inst rng v = runProg inst.fill_bytes (maskProg v) rng := by
  rw [maskProg, runProg_query]
  simp only [maskRest, mask, constRng, constFill, lift, Array.to_slice_mut, padBuf,
    Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok, uncurry_eq]

/-- `maskProg v` asks for at most one byte. -/
theorem maskProg_byteBound (v : U8) : ByteBound (maskProg v) 1 := by
  simp [ByteBound, maskProg, padBuf_length]

/-- If `b` is the one byte `x`, then `maskRest v b` returns the pad `x` and `v ^^^ x`. -/
theorem maskRest_of_val (v x : U8) (b : Slice U8) (hb : b.val = [x]) :
    maskRest v b = Result.ok (x, v ^^^ x) := by
  simp only [maskRest, mask, constRng, constFill, lift, Array.to_slice_mut,
    Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok, uncurry_eq]
  simp [Array.from_slice, Array.index_usize, hb]

/-- Run with `unifImpl`, `maskProg v` has the distribution of `Result.ok <$> Crypto.mask v`. -/
@[bridge_for mask]
theorem maskProg_bridge (v : U8) :
    simulateQ unifImpl (maskProg v) =ᵈ
    (do let y ← Crypto.mask v
        pure (Result.ok y)) := by
  have e : simulateQ unifImpl (maskProg v) =
      (do let w ← $ᵗ (List.Vector U8 padBuf.length)
          pure (maskRest v (sliceOfVector padBuf w))) := by
    simp [maskProg, unifImpl]
    rfl
  rw [e]
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

/-- The assumption on `fill_bytes`: from a state sampled by `seed`, it answers every oracle program
with `ByteBound p n` as `unifImpl` does, in distribution. This is `IdealRng inst.fill_bytes seed n`
unfolded. `IdealRng` states its limits. A generator whose `fill_bytes` is `tapeFill` satisfies it
with the seed `tapeSeed n` (`idealRng_tape`). -/
def rand_core.RngCore.fill_bytes_assumption {R : Type} (inst : rand_core.RngCore R)
    (seed : ProbComp R) (n : ℕ) : Prop :=
  ∀ {α : Type} (p : OracleComp FillSpec (Result α)), ByteBound p n →
    (do let rng ← seed
        pure (Prod.fst <$> runProg inst.fill_bytes p rng)) =ᵈ
    simulateQ unifImpl p

/-- If `fill_bytes_assumption inst seed 1`, then `mask inst rng v`, with `rng` sampled by `seed`
and the final state dropped, has the distribution of `Result.ok <$> Crypto.mask v`. The theorem
covers one call of `mask`. -/
theorem mask_bridge {R : Type} (inst : rand_core.RngCore R) (seed : ProbComp R)
    (h : rand_core.RngCore.fill_bytes_assumption inst seed 1) (v : U8) :
    (do let rng ← seed
        pure (Prod.fst <$> mask inst rng v)) =ᵈ
    (do let y ← Crypto.mask v
        pure (Result.ok y)) := by
  simp only [mask_eq_prog]
  exact (h (maskProg v) (maskProg_byteBound v)).trans (maskProg_bridge v)

/-- `unmask pad masked` has the distribution of `Result.ok <$> Crypto.unmask pad masked`. -/
theorem unmask_bridge (pad masked : U8) :
    (pure (unmask pad masked) : ProbComp _) =ᵈ
    (do let r ← Crypto.unmask pad masked
        pure (Result.ok r)) :=
  bridge_of_spec (Spec.unmask_spec pad masked) (by simp [unmask])

end byte_mask.Oracle.Bridge
