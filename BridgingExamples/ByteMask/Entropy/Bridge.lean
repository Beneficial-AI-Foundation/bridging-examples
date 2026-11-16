import BridgingExamples.ByteMask.Spec
import BridgingExamples.ByteMask.Crypto
import Common.Correspondence
import Common.Metadata
import Common.Oracle.EntropyIdealRng

/-!
# Bridge for `mask`, with the generator state as a source of entropy

Aeneas extracts `mask` as a deterministic function of a generator `inst : RngCore R` and a state
`rng : R`. `mask_bridge`: under `fill_bytes_assumption`, with `rng` sampled from
`states (n + 1)`, `mask inst rng v` has the distribution of `Result.ok (y, rng')`, where
`y ← Crypto.mask v` and `rng' ← states n` are independent.

Unlike the oracle bridge, the theorem describes the final state, so the next call on the same
generator can start from it (`mask_twice_bridge`). `fill_bytes_assumption` implies the assumption
of the oracle bridge (`idealRng_of_entropyRng` in `Common/Oracle/EntropyIdealRng.lean`), and the
converse is false.
Two assumptions stay outside Lean. First, Aeneas extracts `mask` faithfully. Second, the real
generator is `fill_bytes` run from a state with the distribution `states (n + 1)`, and this state
is independent of the input `v`.
-/

namespace byte_mask.Entropy.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle byte_mask.Spec

/-- The assumption on `fill_bytes`: from a state sampled from `states (n + k)`, a call for `k`
bytes returns `k` uniform bytes and, independently, a state sampled from `states n`. This is
`EntropyRng inst.fill_bytes states` unfolded (`fill_bytes_assumption_iff_entropyRng`).
`EntropyRng` states its limits. A generator whose `fill_bytes` is `tapeFill` satisfies it with the
family `tapeSeed` (`entropyRng_tape`). -/
def rand_core.RngCore.fill_bytes_assumption {R : Type} (inst : rand_core.RngCore R)
    (states : ℕ → ProbComp R) : Prop :=
  ∀ (n : ℕ) (s : Slice U8),
    (do let rng ← states (n + s.length)
        pure (inst.fill_bytes rng s)) =ᵈ
    (do let bytes ← $ᵗ (List.Vector U8 s.length)
        let rng ← states n
        pure (Result.ok (rng, sliceOfVector s bytes)))

/-- `fill_bytes_assumption inst states` holds if and only if `EntropyRng inst.fill_bytes states`. -/
theorem fill_bytes_assumption_iff_entropyRng {R : Type} (inst : rand_core.RngCore R)
    (states : ℕ → ProbComp R) :
    rand_core.RngCore.fill_bytes_assumption inst states ↔ EntropyRng inst.fill_bytes states :=
  Iff.rfl

/-- `fill_bytes_assumption inst states` implies the assumption of the oracle bridge,
`IdealRng inst.fill_bytes (states n) n`, for every `n`. The converse is false
(`idealRng_not_entropyRng`). -/
theorem fill_bytes_assumption_idealRng {R : Type} (inst : rand_core.RngCore R)
    (states : ℕ → ProbComp R) (h : rand_core.RngCore.fill_bytes_assumption inst states) (n : ℕ) :
    IdealRng inst.fill_bytes (states n) n :=
  idealRng_of_entropyRng inst.fill_bytes states
    ((fill_bytes_assumption_iff_entropyRng inst states).mp h) n

/-- If `fill_bytes_assumption inst states`, then, with `rng` sampled from `states (n + 1)`,
`mask inst rng v` has the distribution of `Result.ok (y, rng')`, where `y ← Crypto.mask v` and
`rng' ← states n` are independent. -/
theorem mask_bridge {R : Type} (inst : rand_core.RngCore R) (states : ℕ → ProbComp R)
    (h : rand_core.RngCore.fill_bytes_assumption inst states) (n : ℕ) (v : U8) :
    (do let rng ← states (n + 1)
        pure (mask inst rng v)) =ᵈ
    (do let y ← Crypto.mask v
        let rng ← states n
        pure (Result.ok (y, rng))) := by
  let F : Result (R × Slice U8) → Result ((U8 × U8) × R) := fun r =>
    Aeneas.Std.bind r fun q => Aeneas.Std.bind (maskRest v q.2) fun p => Result.ok (p, q.1)
  have hn : n + 1 = n + padBuf.length := by rw [padBuf_length]
  simp only [hn, mask_eq]
  have step := (h n padBuf).bind_left (fun r => (pure (F r) : ProbComp _))
  simp only [bind_assoc, pure_bind] at step
  refine step.trans ?_
  -- The one byte of `bytes` is the pad.
  refine (uniformVector_bind_congr padBuf_length _
    (fun w : List.Vector U8 1 => do
      let rng ← states n
      pure (Result.ok ((w.head, v ^^^ w.head), rng))) ?_).trans ?_
  · intro w
    obtain ⟨l, hl⟩ := w
    have hl1 := hl
    rw [padBuf_length] at hl1
    match l, hl1 with
    | [x], _ =>
      have e := maskRest_of_val v x (sliceOfVector padBuf ⟨[x], hl⟩) (sliceOfVector_val _ _)
      simp [F, e]
      rfl
  · have hb := (SampleableType.map_uniformSample_evalDistEq_of_bijective head_bijective).bind_left
      (fun x => do
        let rng ← states n
        pure (Result.ok ((x, v ^^^ x), rng)))
    simpa [Crypto.mask, map_eq_bind_pure_comp] using hb

/-- Two calls of `mask` on one generator: the second call starts from the state that the first
returns, and its input `v' y` can depend on the output `y` of the first. If
`fill_bytes_assumption inst states`, then, with `rng` sampled from `states (n + 1 + 1)`, the two
calls have the distribution of `y ← Crypto.mask v`, `y' ← Crypto.mask (v' y)` and, independently,
a state sampled from `states n`. -/
@[bridge_for mask]
theorem mask_twice_bridge {R : Type} (inst : rand_core.RngCore R) (states : ℕ → ProbComp R)
    (h : rand_core.RngCore.fill_bytes_assumption inst states) (n : ℕ) (v : U8)
    (v' : U8 × U8 → U8) :
    (do let rng ← states (n + 1 + 1)
        pure (Aeneas.Std.bind (mask inst rng v) fun q =>
          Aeneas.Std.bind (mask inst q.2 (v' q.1)) fun r => Result.ok ((q.1, r.1), r.2))) =ᵈ
    (do let y ← Crypto.mask v
        let y' ← Crypto.mask (v' y)
        let rng ← states n
        pure (Result.ok ((y, y'), rng))) :=
  entropy_bind states 1 1 (fun rng => mask inst rng v) (Crypto.mask v)
    (fun m => mask_bridge inst states h m v) (fun y rng => mask inst rng (v' y))
    (fun y => Crypto.mask (v' y)) (fun y m => mask_bridge inst states h m (v' y)) n

/-- `unmask pad masked` has the distribution of `Result.ok <$> Crypto.unmask pad masked`. -/
theorem unmask_bridge (pad masked : U8) :
    (pure (unmask pad masked) : ProbComp _) =ᵈ
    (do let r ← Crypto.unmask pad masked
        pure (Result.ok r)) :=
  bridge_of_spec (Spec.unmask_spec pad masked)

end byte_mask.Entropy.Bridge
