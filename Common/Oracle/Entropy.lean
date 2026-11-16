import Common.Oracle.Tape

/-!
# The generator state as a source of entropy

`EntropyRng fill states` relates `fill` to a family `states` of distributions on generator
states, indexed by a byte budget. From `states (n + k)`, a call for `k` bytes returns `k` uniform
bytes and, independently, a state sampled from `states n`.
-/

namespace BridgingExamples.Oracle

open Aeneas Aeneas.Std OracleComp

/-- `EntropyRng fill states`: for all `n` and every buffer `s` of length `k`, these two
computations have the same distribution:

* sample a state from `states (n + k)` and call `fill` on `s`;
* sample `k` uniform bytes and, independently, a state from `states n`.

Unlike `IdealRng`, the condition describes the final state: its distribution is again in the
family, and it is independent of the returned bytes. So the next call can start from it, and
bridges for successive calls compose (`entropy_bind`).

The independence holds for each call, with a fixed `n` and buffer. After a run that picks its
next buffer from earlier answers, the final state can depend on those answers, for example
through the number of bytes that the run used.

The equality is exact, so the condition idealizes a real generator. From `states n`, `n` calls
for one byte each return `n` uniform bytes, also if `n > Usize.max`. Each state determines these
bytes, so the support of `states n` has at least `256 ^ n` states, and the state type of `fill`
is infinite. This is not proved in Lean.

`EntropyRng` implies `IdealRng`, and the converse is false (`Common/Oracle/EntropyIdealRng.lean`).
A uniform tape satisfies the condition (`entropyRng_tape`). -/
def EntropyRng {R : Type} (fill : Fill R) (states : ℕ → ProbComp R) : Prop :=
  ∀ (n : ℕ) (s : Slice U8),
    (do let rng ← states (n + s.length)
        pure (fill rng s)) =ᵈ
    (do let bytes ← $ᵗ (List.Vector U8 s.length)
        let rng ← states n
        pure (Result.ok (rng, sliceOfVector s bytes)))

/-- A uniform tape satisfies `EntropyRng`: the tapes of `n` bytes form the family. -/
theorem entropyRng_tape : EntropyRng tapeFill tapeSeed := by
  intro n s
  have hs := uniformVector_split s.length (n + s.length) (by omega)
    (fun l => (pure (tapeFill l s) : ProbComp _))
  simp only [tapeSeed, bind_map_left]
  refine hs.trans ?_
  have e : ∀ (a : List.Vector U8 s.length) (b : List U8),
      tapeFill (a.val ++ b) s = Result.ok (b, sliceOfVector s a) := by
    intro a b
    have hlen : s.length ≤ (a.val ++ b).length := by simp [a.property]
    simp only [tapeFill, hlen, ↓reduceIte, List.drop_left' a.property]
    congr 2
    refine (Slice.eq_iff _ _).mpr ?_
    rw [tapePrefix, Slice.from_val, sliceOfVector_val]
    exact List.take_left' a.property
  simp only [e]
  rw [Nat.add_sub_cancel]

/-- Bridges in the form of `EntropyRng` compose. Assume that `f`, run from a state sampled from
`states (m + a)`, has the distribution of `x ← X` and, independently, a state from `states m`, and
that `g x`, run from `states (m + b)`, has the distribution of `y ← Y x` and, independently, a
state from `states m`. Then `f` followed by `g` on the state that `f` returns, run from
`states (n + b + a)`, has the distribution of `x ← X`, `y ← Y x` and, independently, a state from
`states n`. -/
theorem entropy_bind {R α β : Type} (states : ℕ → ProbComp R) (a b : ℕ)
    (f : R → Result (α × R)) (X : ProbComp α)
    (hf : ∀ m, (do let rng ← states (m + a)
                   pure (f rng)) =ᵈ
               (do let x ← X
                   let rng ← states m
                   pure (Result.ok (x, rng))))
    (g : α → R → Result (β × R)) (Y : α → ProbComp β)
    (hg : ∀ x m, (do let rng ← states (m + b)
                     pure (g x rng)) =ᵈ
                 (do let y ← Y x
                     let rng ← states m
                     pure (Result.ok (y, rng))))
    (n : ℕ) :
    (do let rng ← states (n + b + a)
        pure (Aeneas.Std.bind (f rng) fun q =>
          Aeneas.Std.bind (g q.1 q.2) fun r => Result.ok ((q.1, r.1), r.2))) =ᵈ
    (do let x ← X
        let y ← Y x
        let rng ← states n
        pure (Result.ok ((x, y), rng))) := by
  have step := (hf (n + b)).bind_left (fun r => (pure (Aeneas.Std.bind r fun q =>
    Aeneas.Std.bind (g q.1 q.2) fun r => Result.ok ((q.1, r.1), r.2)) : ProbComp _))
  simp only [bind_assoc, pure_bind, Aeneas.Std.bind_ok] at step
  refine step.trans (EvalDistEq.bind_right _ fun x => ?_)
  have step2 := (hg x n).bind_left (fun r => (pure (Aeneas.Std.bind r fun r =>
    Result.ok ((x, r.1), r.2)) : ProbComp _))
  simp only [bind_assoc, pure_bind, Aeneas.Std.bind_ok] at step2
  exact step2

end BridgingExamples.Oracle
