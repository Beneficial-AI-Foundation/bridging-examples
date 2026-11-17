import Aeneas
import Mathlib.Data.Fin.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

namespace BridgingExamples

open Aeneas.Std
open scoped ENNReal

/-- The value of a byte in `0..255`. -/
def byteToModel (value : U8) : Fin 256 := value.bv.toFin

/-- The byte with the given value. -/
def modelToByte (value : Fin 256) : U8 := ⟨BitVec.ofFin value⟩

@[simp] theorem byteToModel_modelToByte (value : Fin 256) :
    byteToModel (modelToByte value) = value := by
  change (BitVec.ofFin (w := 8) value).toFin = value
  simp

@[simp] theorem modelToByte_byteToModel (value : U8) :
    modelToByte (byteToModel value) = value := by
  cases value; rfl

theorem byteToModel_bijective : Function.Bijective byteToModel :=
  ⟨fun _ _ h => by simpa using congrArg modelToByte h, fun y => ⟨modelToByte y, by simp⟩⟩

def byteEquiv : U8 ≃ Fin 256 where
  toFun := byteToModel
  invFun := modelToByte
  left_inv := modelToByte_byteToModel
  right_inv := byteToModel_modelToByte

instance sampleableByte : SampleableType U8 := SampleableType.ofEquiv byteEquiv.symm

def vectorEquiv {n : ℕ} : List.Vector U8 n ≃ (Fin n → U8) := Equiv.vectorEquivFin U8 n

instance sampleableVector {n : ℕ} : SampleableType (List.Vector U8 n) :=
  SampleableType.ofEquiv vectorEquiv.symm

def arrayEquiv {n : Usize} : Array U8 n ≃ List.Vector U8 n.val where
  toFun := fun bytes => ⟨bytes.val, by simp⟩
  invFun := fun bytes => Array.from bytes.val (by simp)
  left_inv := by intro bytes; exact Array.val_from bytes _
  right_inv := by intro bytes; apply Subtype.ext; simp

instance sampleableArray {n : Usize} : SampleableType (Array U8 n) :=
  SampleableType.ofEquiv arrayEquiv.symm

/-- The slice of the byte vector `bytes`. Its length is that of the slice `buffer`, so it is
within the bound on slice lengths. -/
def sliceOfVector (buffer : Slice U8) (bytes : List.Vector U8 buffer.length) : Slice U8 :=
  Slice.from bytes.val (by rw [bytes.property]; exact buffer.property)

@[simp] theorem sliceOfVector_val (buffer : Slice U8) (bytes : List.Vector U8 buffer.length) :
    (sliceOfVector buffer bytes).val = bytes.val := Slice.from_val _ _

/-- A vector of `buffer.length` bytes has length at most `Usize.max`, the bound on slice lengths. -/
theorem vector_length_le (buffer : Slice U8) (bytes : List.Vector U8 buffer.length) :
    bytes.val.length ≤ Usize.max := by
  rw [bytes.property]; exact buffer.property

/-- A slice of `buffer.length` uniform bytes. -/
def uniformBytes (buffer : Slice U8) : ProbComp (Slice U8) := do
  let bytes ← $ᵗ (List.Vector U8 buffer.length)
  pure (Slice.from bytes.val (vector_length_le buffer bytes))

/-- `uniformBytes buffer` is uniform on the slices of length `buffer.length`: it returns each of
them with probability `(256 ^ buffer.length)⁻¹`, and never a slice of another length. -/
theorem prEvent_uniformBytes (buffer s : Slice U8) :
    Pr{let filled ← uniformBytes buffer}[filled = s] =
      if s.length = buffer.length then (256 ^ buffer.length : ℝ≥0∞)⁻¹ else 0 := by
  have hmap : uniformBytes buffer =
      (fun bytes => Slice.from bytes.val (vector_length_le buffer bytes)) <$>
        ($ᵗ (List.Vector U8 buffer.length)) := by
    simp [uniformBytes, map_eq_bind_pure_comp]
  rw [hmap, prEvent_map]
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

@[simp] theorem uniformSample_byte :
    uniformSample U8 = modelToByte <$> uniformSample (Fin 256) := rfl

end BridgingExamples
