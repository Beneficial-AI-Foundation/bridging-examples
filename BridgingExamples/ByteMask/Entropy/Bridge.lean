import BridgingExamples.ByteMask.Pad
import Common.Correspondence
import Common.Metadata
import Common.Oracle.Entropy

/-!
# Bridge for `mask`, with the generator state as a source of entropy

The generator method `fill_bytes` is the one random atom. `fill_bytes_assumption` relates the
extracted `fill_bytes` to `Crypto.rand_core.RngCore.fill_bytes`, and `mask_bridge` relates the
extracted `mask` to `Crypto.mask` under this assumption. Both describe the final generator state,
so the next call on the same generator can start from it (`mask_twice_bridge`). `unmask_bridge`
relates the deterministic `unmask` to `Crypto.unmask`.

`fill_bytes_assumption` implies the assumption of the oracle bridge (`idealRng_of_entropyRng`),
and the converse is false (`idealRng_not_entropyRng`).
-/

namespace byte_mask.Entropy.Bridge

open Aeneas Aeneas.Std BridgingExamples BridgingExamples.Oracle byte_mask.Spec byte_mask.Pad

/-- The assumption on `fill_bytes`: from a state sampled from `states (n + k)`, the extracted
`fill_bytes` fills a buffer of length `k` with the bytes of the Crypto `fill_bytes` and,
independently, returns a state sampled from `states n`. This is `EntropyRng inst.fill_bytes states`
(`fill_bytes_assumption_iff_entropyRng`), and `EntropyRng` states its limits. A generator whose
`fill_bytes` is `tapeFill` satisfies it with the family `tapeSeed` (`entropyRng_tape`). -/
def rand_core.RngCore.fill_bytes_assumption {R : Type} (inst : rand_core.RngCore R)
    (states : ℕ → ProbComp R) : Prop :=
  ∀ (n : ℕ) (s : Slice U8),
    (do let rng ← states (n + s.length)
        pure (inst.fill_bytes rng s)) =ᵈ
    (do let bytes ← Crypto.rand_core.RngCore.fill_bytes s.length
        let rng ← states n
        pure (Result.ok (rng, sliceOfVector s bytes)))

/-- `fill_bytes_assumption` is `EntropyRng` unfolded. -/
theorem fill_bytes_assumption_iff_entropyRng {R : Type} (inst : rand_core.RngCore R)
    (states : ℕ → ProbComp R) :
    rand_core.RngCore.fill_bytes_assumption inst states ↔ EntropyRng inst.fill_bytes states :=
  Iff.rfl

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
  have hn : n + 1 = n + padBuf.length := by rw [padBuf_length]
  simp only [hn, mask_eq]
  have step := (h n padBuf).bind_left (fun r => (pure (Aeneas.Std.bind r fun q =>
    Aeneas.Std.bind (maskRest v q.2) fun p => Result.ok (p, q.1)) : ProbComp _))
  simp only [bind_assoc, pure_bind, Aeneas.Std.bind_ok] at step
  refine step.trans ((maskRest_fill_bytes v fun r => do
    let rng ← states n
    pure (Aeneas.Std.bind r fun p => Result.ok (p, rng))).trans ?_)
  simp only [Aeneas.Std.bind_ok]
  exact EvalDistEq.rfl

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
