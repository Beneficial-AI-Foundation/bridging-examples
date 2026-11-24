import BridgingExamples.OneTimePad.Aeneas
import Common.Result
import Common.Metadata

namespace one_time_pad.Oracle.Spec

open Aeneas Aeneas.Std BridgingExamples

/-- The byte-wise XOR of two blocks. -/
def xorBlock (a b : Array U8 16#usize) : Array U8 16#usize :=
  Array.from (List.zipWith (· ^^^ ·) a.val b.val) (by simp)

theorem xorBlock_val (a b : Array U8 16#usize) :
    (xorBlock a b).val = List.zipWith (· ^^^ ·) a.val b.val := by
  simp only [xorBlock, Array.from_val]

theorem xorBlock_getElem! (a b : Array U8 16#usize) (j : Nat) (hj : j < 16) :
    (xorBlock a b).val[j]! = a.val[j]! ^^^ b.val[j]! := by
  have ha : a.val.length = 16 := by simp
  have hb : b.val.length = 16 := by simp
  simp only [xorBlock_val]
  rw [getElem!_pos _ j (by simp; omega), getElem!_pos _ j (by omega),
    getElem!_pos _ j (by omega), List.getElem_zipWith]

theorem eq_of_getElem! (a b : Array U8 16#usize)
    (h : ∀ j < 16, a.val[j]! = b.val[j]!) : a = b := by
  have ha : a.val.length = 16 := by simp
  have hb : b.val.length = 16 := by simp
  apply Std.Array.ext
  apply List.ext_getElem (by omega)
  intro j hja hjb
  have := h j (by simp at hja; omega)
  rwa [getElem!_pos _ j hja, getElem!_pos _ j hjb] at this

/-- The invariant of `encrypt_loop`: `i ≤ 16` and the first `i` entries of `c` are the XORs of
`key` and `message`. -/
def encryptInv (key message : Array U8 16#usize) (p : Array U8 16#usize × Usize) : Prop :=
  p.2.val ≤ 16 ∧ ∀ j < p.2.val, p.1.val[j]! = key.val[j]! ^^^ message.val[j]!

/-- One step of `encrypt_loop` keeps `encryptInv` and decreases `16 - i`, or returns
`xorBlock key message`. -/
theorem encrypt_loop_body_spec (key message c' : Array U8 16#usize) (i' : Usize)
    (hp : encryptInv key message (c', i')) :
    encrypt_loop.body key message c' i' ⦃ r =>
      match r with
      | .done y => y = xorBlock key message
      | .cont p' => encryptInv key message p' ∧ 16 - p'.2.val < 16 - i'.val ⦄ := by
  obtain ⟨hi', hc'⟩ := hp
  · simp only [encryptInv]
    simp only [encrypt_loop.body]
    split
    · step*
      simp only at hi' hc'
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj
      subst a_post
      rw [Array.set_val_eq]
      have hk : key.val.length = 16 := by simp
      have hm : message.val.length = 16 := by simp
      have hc : c'.val.length = 16 := by simp
      rw [getElem!_pos _ j (by simp; scalar_tac)]
      rcases Nat.lt_or_ge j i'.val with h | h
      · rw [List.getElem_set_ne (by omega), ← getElem!_pos]
        exact hc' j h
      · have hj' : j = i'.val := by scalar_tac
        subst hj'
        rw [List.getElem_set_self, getElem!_pos _ _ (by scalar_tac),
          getElem!_pos _ _ (by scalar_tac)]
        apply UScalar.eq_of_val_eq
        simp [i3_post, i1_post, i2_post]
    · simp only at hi' hc'
      simp only [WP.spec_ok]
      apply eq_of_getElem!
      intro j hj
      rw [xorBlock_getElem! _ _ _ hj]
      exact hc' j (by scalar_tac)

/-- One step of `encrypt_loop` does not start by sampling. -/
theorem encrypt_loop_body_noSample (key message c : Array U8 16#usize) (i : Usize) :
    NoSample (encrypt_loop.body key message c i) := by
  unfold encrypt_loop.body
  split
  · simp only [HAdd.hAdd, Add.add, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      Array.index_usize, Array.update, lift]
    repeat' split
    all_goals simp
  · simp

/-- If `i ≤ 16` and the first `i` entries of `c` are the XORs of `key` and `message`, then
`encrypt_loop key message c i` returns `xorBlock key message`. -/
theorem encrypt_loop_spec (key message c : Array U8 16#usize) (i : Usize)
    (hi : i.val ≤ 16)
    (hc : ∀ j < i.val, c.val[j]! = key.val[j]! ^^^ message.val[j]!) :
    encrypt_loop key message c i ⦃ r => r = xorBlock key message ⦄ := by
  unfold encrypt_loop
  apply loop.spec_decr_nat (fun p => 16 - p.2.val) (encryptInv key message)
  · rintro ⟨c', i'⟩ hp
    exact WP.spec_mono (encrypt_loop_body_spec key message c' i' hp) fun r h => by cases r <;> exact h
  · exact ⟨hi, hc⟩

/-- `encrypt key message` returns `xorBlock key message`. -/
@[step]
theorem encrypt_spec (key message : Array U8 16#usize) :
    encrypt key message ⦃ c => c = xorBlock key message ⦄ := by
  unfold encrypt
  exact encrypt_loop_spec key message _ 0#usize (by simp) (by simp)

theorem encrypt_eq (key message : Array U8 16#usize) :
    encrypt key message = Result.ok (xorBlock key message) := by
  unfold encrypt encrypt_loop
  have h := loop_returns (fun p : Array U8 16#usize × Usize => 16 - p.2.val)
    (encryptInv key message) (· = xorBlock key message)
    (fun (ciphertext1, i1) => encrypt_loop.body key message ciphertext1 i1)
    (Array.repeat 16#usize 0#u8, 0#usize)
    (by
      rintro ⟨c', i'⟩ hp
      exact WP.spec_mono (encrypt_loop_body_spec key message c' i' hp) fun r h => by
        cases r <;> exact h)
    (by rintro ⟨c', i'⟩ _; exact encrypt_loop_body_noSample key message c' i')
    ⟨by simp, by simp⟩
  obtain ⟨c, hc, rfl⟩ := h
  exact hc

/-- `decrypt key c` returns `xorBlock key c`. -/
@[step]
theorem decrypt_spec (key c : Array U8 16#usize) : decrypt key c ⦃ m => m = xorBlock key c ⦄ := by
  unfold decrypt
  exact encrypt_spec key c

/-- `decrypt key` returns `message` on `xorBlock key message`. -/
theorem decrypt_encrypt (key message : Array U8 16#usize) :
    decrypt key (xorBlock key message) = Result.ok message := by
  rw [decrypt, encrypt_eq]
  congr 1
  apply eq_of_getElem!
  intro j hj
  rw [xorBlock_getElem! _ _ _ hj, xorBlock_getElem! _ _ _ hj]
  apply UScalar.eq_of_val_eq
  simp

/-- `encrypt key message` succeeds, and `decrypt key` returns `message` on its result. -/
@[spec_for decrypt encrypt]
theorem encrypt_decrypt (key message : Array U8 16#usize) :
    (do let c ← encrypt key message; decrypt key c) = Result.ok message := by
  rw [encrypt_eq, Aeneas.Std.bind_ok, decrypt_encrypt]

end one_time_pad.Oracle.Spec
