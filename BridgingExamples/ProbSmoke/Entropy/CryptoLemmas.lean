import BridgingExamples.ProbSmoke.Entropy.Crypto

namespace prob_smoke.Entropy.Crypto

open Aeneas.Std BridgingExamples
open scoped ENNReal

/-- `fill_bytes n buffer` fills `buffer` uniformly: it returns each slice of length
`buffer.length` with probability `(256 ^ buffer.length)⁻¹`, and never a slice of another
length. -/
theorem prEvent_fill_bytes (n : ℕ) (buffer s : Slice U8) :
    Pr{let (_, filled) ← fill_bytes n buffer}[filled = s] =
      if s.length = buffer.length then (256 ^ buffer.length : ℝ≥0∞)⁻¹ else 0 := by
  have hmap : fill_bytes n buffer =
      (fun bytes => (n - buffer.length, Slice.from bytes.val (vector_length_le buffer bytes))) <$>
        ($ᵗ (List.Vector U8 buffer.length)) := by
    simp [fill_bytes, map_eq_bind_pure_comp]
  rw [hmap, prEvent_map]
  show Pr{let bytes ← $ᵗ (List.Vector U8 buffer.length)}[
    Slice.from bytes.val (vector_length_le buffer bytes) = s] = _
  split_ifs with h
  · calc
      _ = Pr{let bytes ← $ᵗ (List.Vector U8 buffer.length)}[bytes = ⟨s.val, h⟩] :=
          prEvent_congr _ _ _ fun bytes => by
            constructor
            · rintro rfl; exact Subtype.ext (Slice.from_val _ _).symm
            · rintro rfl; exact Slice.val_from s _
      _ = (Nat.card (List.Vector U8 buffer.length) : ℝ≥0∞)⁻¹ :=
          SampleableType.prEvent_uniformSample_eq_singleton_natCard _
      _ = (256 ^ buffer.length : ℝ≥0∞)⁻¹ := by
          rw [Nat.card_congr vectorEquiv, Nat.card_fun, Nat.card_congr byteEquiv]
          simp
  · apply prEvent_eq_zero_of_forall_not
    intro bytes hb
    apply h
    rw [← hb]
    simp [Slice.length, bytes.property]

end prob_smoke.Entropy.Crypto
