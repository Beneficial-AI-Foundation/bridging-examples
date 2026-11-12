import BridgingExamples.ByteMask.Spec
import BridgingExamples.ByteMask.Crypto
import Common.RngOracle
import Common.Correspondence

/-!
# Bridge for `mask`, with the generator as an oracle

Aeneas extracts `mask` as a deterministic function of a generator `inst : RngCore R` and a
generator value `rng : R`. The bridge to `Crypto.mask` has two steps.

1. `mask_eq_prog`: for every generator, `mask` is the oracle program `maskProg`, answered by the
   generator's `fill_bytes`. The program asks for the one-byte buffer `padBuf`, then runs
   `maskRest` on the answer. `maskRest v b` is the extracted `mask`, run with the generator that
   returns `b`. The theorem has no assumption on the generator.
2. `mask_bridge`: answered by uniform bytes (`unifImpl`), `maskProg` has the distribution of
   `Crypto.mask`. By `simulateQ_maskProg`, that program samples a uniform buffer and runs the
   extracted `mask` on it (`mask_uniform`).

So the deterministic part of both sides is the extracted code. Only the answer to the oracle
changes. That the real generator answers like `unifImpl` is trusted, and is not a Lean statement.
-/

namespace byte_mask.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.RngOracle OracleSpec OracleComp

/-- The generator whose `fill_bytes` returns `b`. `mask` does not call `next_u32` or `next_u64`,
so they fail. -/
def constRng (b : Slice U8) : rand_core.RngCore Unit where
  next_u32 _ := Result.fail .panic
  next_u64 _ := Result.fail .panic
  fill_bytes := constFill b

/-- The one-byte buffer that `mask` passes to `fill_bytes`. -/
def padBuf : Slice U8 := (Array.repeat 1#usize 0#u8).to_slice

theorem padBuf_length : padBuf.length = 1 := by
  simp only [padBuf, Slice.length, Array.val_to_slice, Aeneas.Std.Array.length_eq]; rfl

/-- `mask` after its draw: the extracted `mask`, run with the generator that returns `b`. -/
def maskRest (v : U8) (b : Slice U8) : Result (U8 × U8) := do
  let (p, _) ← mask (constRng b) () v
  Result.ok p

/-- `mask` as an oracle program: one query for `padBuf`, then `maskRest` on the answer. -/
def maskProg (v : U8) : OracleComp FillSpec (Result (U8 × U8)) := do
  let b ← (liftM (FillSpec.query padBuf) : OracleComp FillSpec _)
  return maskRest v b

/-- For every generator, `mask` is `maskProg` answered by the generator's `fill_bytes`. -/
theorem mask_eq_prog {R : Type} (inst : rand_core.RngCore R) (rng : R) (v : U8) :
    mask inst rng v = runProg inst.fill_bytes (maskProg v) rng := by
  rw [maskProg, runProg_query]
  simp only [maskRest, mask, constRng, constFill, lift, Array.to_slice_mut, padBuf,
    Aeneas.Std.bind_assoc, Aeneas.Std.bind_ok, uncurry_eq]

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

/-- Answered by uniform bytes, `maskProg v` samples a uniform buffer of the length of `padBuf`
and runs `maskRest` on it. -/
theorem simulateQ_maskProg (v : U8) :
    simulateQ unifImpl (maskProg v) =
      (do let w ← $ᵗ (List.Vector U8 padBuf.length)
          pure (maskRest v (sliceOfVector padBuf w))) := by
  simp [maskProg, unifImpl]
  rfl

/-- Answered by uniform bytes, `maskProg v` has the distribution of `Crypto.mask v`. -/
theorem mask_bridge (v : U8) :
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

/-- The extracted `mask`, run with a generator that returns a uniform one-byte buffer, has the
distribution of `Crypto.mask v`. -/
theorem mask_uniform (v : U8) :
    (do let w ← $ᵗ (List.Vector U8 padBuf.length)
        pure (maskRest v (sliceOfVector padBuf w))) =ᵈ
    (do let y ← Crypto.mask v
        pure (Result.ok y)) :=
  simulateQ_maskProg v ▸ mask_bridge v

end byte_mask.Bridge
