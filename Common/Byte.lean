import Aeneas
import Mathlib.Data.Fin.Basic
import VCVio.OracleComp.Constructions.SampleableType.Measure

namespace BridgingExamples

open Aeneas.Std

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

@[simp] theorem uniformSample_byte :
    uniformSample U8 = modelToByte <$> uniformSample (Fin 256) := rfl

end BridgingExamples
