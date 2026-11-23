import BridgingExamples.ByteMask.Spec
import BridgingExamples.ByteMask.Crypto
import Common.Correspondence

/-!
# The pad as the answer of `fill_bytes`

The lemma behind both bridges for `mask`: when the Crypto `fill_bytes` fills `padBuf`, the rest of
the extracted `mask` returns `Crypto.mask v`.
-/

namespace byte_mask.Pad

open Aeneas Aeneas.Std BridgingExamples byte_mask.Spec

/-- If `bytes` is drawn with the Crypto `fill_bytes` for `padBuf`, then `maskRest v` on `bytes`,
followed by any `k`, has the distribution of `Crypto.mask v` followed by `k`. -/
theorem maskRest_fill_bytes {γ : Type} (v : U8) (k : Result (U8 × U8) → ProbComp γ) :
    (do let bytes ← Crypto.rand_core.RngCore.fill_bytes padBuf.length
        k (maskRest v (sliceOfVector padBuf bytes))) =ᵈ
    (do let y ← Crypto.mask v
        k (Result.ok y)) := by
  refine (uniformVector_bind_congr padBuf_length _
    (fun w : List.Vector U8 1 => k (Result.ok (w.head, v ^^^ w.head))) ?_).trans ?_
  · intro w
    obtain ⟨l, hl⟩ := w
    have hl1 := hl
    rw [padBuf_length] at hl1
    match l, hl1 with
    | [x], _ =>
      rw [maskRest_of_val v x _ (sliceOfVector_val _ _)]
      rfl
  · simp only [Crypto.mask, Crypto.rand_core.RngCore.fill_bytes, bind_assoc, pure_bind]
    exact EvalDistEq.rfl

end byte_mask.Pad
