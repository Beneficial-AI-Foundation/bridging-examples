# Oracle and Effect bridges for random number generators

This note compares two ways to bridge extracted Rust code that calls a random number generator
(RNG) to its Crypto definition. Both are in PR #19 for ProbSmoke and ByteMask. A Codex review
of the comparison corrected an earlier version.

## Setting

The Rust code is generic over `R: rand::RngCore`. Aeneas extracts the trait as a dictionary
`inst : rand_core.RngCore R`, with `fill_bytes : R → Slice U8 → Result (R × Slice U8)`. An
extracted function `f inst rng x` takes the dictionary, a generator state `rng`, and the inputs.
`F x : ProbComp _` is its Crypto definition.

Upstream Aeneas `Result` has three outcomes: success, failure, and divergence. So every
dictionary is deterministic. `aeneas.patch`, from
[toy-bridge](https://github.com/Beneficial-AI-Foundation/toy-bridge), adds a fourth node,
`Result.random n`, that asks for `n` random bytes.

## The two approaches

The Oracle approach uses an oracle program `P x : OracleComp FillSpec _`. A query is a buffer, and
its answer is the filled buffer. The files are `Common/Oracle/Rng.lean`, `Common/Oracle/Tape.lean`
and `<Example>/Oracle/Bridge.lean`.

```
(O1)  ∀ inst rng x,  f inst rng x = runProg inst.fill_bytes (P x) rng
(O2)  simulateQ unifImpl (P x)  =ᵈ  Result.ok <$> F x
(O3)  IdealRng inst.fill_bytes seed n →
        (do let rng ← seed; pure (Prod.fst <$> f inst rng x))  =ᵈ  Result.ok <$> F x
```

The Effect approach uses an oracle program `M x : OracleComp RandSpec _`. The query `n` asks for
`n` random bytes. `toResult` reads such a program as a `Result`, with one `random n` node for each
query. The files are `aeneas.patch`, `Common/Effect/Random.lean` and `<Example>/Effect/Bridge.lean`.

```
(E1)  RandomFill inst.fill_bytes →  ∀ rng x,  f inst rng x = toResult ((·, rng) <$> M x)
(E2)  simulateQ uniformImpl (M x)  =ᵈ  F x
(E3)  not proved:  ∀ g,  wpe⟦toResult m⟧ g  =  wp (simulateQ uniformImpl m) (fun a => g (ok a))
```

In E2, `F x` is up to the output conversion of each example. In ProbSmoke, for example, the model
returns `sliceOfVector buffer bytes` for the bytes of `Crypto.fill_random`. In E3, `wpe` is a
weakest pre-expectation of `Result`: `wpe⟦x⟧ g` is the expected value of `g` on the outcome of `x`,
with uniform bytes at each `random` node. The repository does not define it. The section "Weakest
pre-expectation" describes it. `wp` is the quantitative weakest precondition of VCVio
(`VCVio/ProgramLogic/Unary/HoareTriple.lean`), with values in `ℝ≥0∞`.

The assumptions put the randomness in different places. `IdealRng fill seed n` is a statement
about distributions. The bytes come from an initial state that `seed` samples. The statement
holds for every oracle program that asks for at most `n` bytes in total. `RandomFill fill` is an
equation for every state: `fill rng buffer` asks for `buffer.length` bytes with `Result.random`,
returns them in the buffer, and returns `rng` unchanged.

## Advantages and disadvantages

The Oracle approach has these advantages:

1. O1 holds for every generator, with no assumption: deterministic, stateful, failing, or
   sampling. It keeps failures and the final state.
2. O3 states the distribution of the extracted code itself, in VCVio.
3. A concrete model satisfies `IdealRng`: a uniform tape of `n` bytes (`idealRng_tape`). So the
   assumption is consistent.
4. `IdealRng` covers the joint distribution of several adaptive queries within the budget.

The Oracle approach has these disadvantages:

1. `IdealRng` is an exact equality. A generator whose state comes from a seed of `k` bytes does
   not satisfy it for `n > k`. So it is not a contract for a real pseudorandom generator (PRG).
2. O3 drops the final state and covers one call. Several calls need one budget for all of them.
3. Each example needs more definitions: `runProg`, `ByteBound`, and a generator built from the
   answer of a query (`constRng`).

The Effect approach has these advantages:

1. `RandomFill` is one equation for each call, with no seed distribution and no budget.
2. The proofs of E1 are mostly `simp`. `toResult_bind` makes sequential calls compose.
3. It fits an opaque external source such as `OsRng`. Jasmin has the same pattern: a `rand`
   instruction makes an `Rnd` event in an interaction tree.

The Effect approach has these disadvantages:

1. E1 is conditional. No deterministic `fill_bytes` satisfies `RandomFill` on an inhabited state
   type. So no extracted Rust implementation, PRG, or stateful wrapper satisfies it. A Lean
   definition that samples with `Result.random` satisfies it by `rfl`.
2. Without E3, no theorem gives a distribution of the extracted code. Aeneas gives
   `Result.random` no probabilities. Only `uniformImpl` on the model side reads it as uniform.
3. The trusted translation is larger: the patched Aeneas and its models of `OsRng`, `TryRngCore`
   and `UnwrapErr`. The patch is not upstream. Its `OsRng` mappings are not tested in this
   repository, because extraction still uses the release binaries. The demonic `spec` and the
   `mvcgen` behavior below are definitions, not trusted assumptions. But they choose a meaning for
   `random` that a reader has to know.

Neither approach is a contract for a seeded PRG such as ChaCha in `StdRng`. That needs a
computational assumption with an advantage term. Neither approach models an adversary that reads,
copies, or resets the generator state.

## Combination

O1 holds for every dictionary, so it also holds for a dictionary that satisfies `RandomFill`. This
lemma connects the two approaches. It is not proved yet.

```
(C)  RandomFill fill →
       runProg fill p rng =
         Aeneas.Std.bind (toResult (τ p)) fun r => Aeneas.Std.bind r fun a => Result.ok (a, rng)
     where  τ : OracleComp FillSpec β → OracleComp RandSpec β
            τ := simulateQ (fun s => sliceOfBytes s <$> randomBytes s.length)
```

`τ` replaces each query "fill the buffer `s`" with "give `s.length` random bytes, put into `s`".
With C, E1 follows from O1 in each example. Then an example needs only O1 and O2, and the Effect
reading is a corollary in `Common`.

This gives a division of work:

1. You prove generic code once with O1, with no assumption on the generator.
2. You choose the assumption where the generator is fixed. For an external source such as
   `OsRng`, `RandomFill` and E3 give a distribution. For a seeded PRG, `IdealRng` or a
   computational assumption applies.

E3 then remains the only missing step for an end-to-end Effect bridge. C and O1 give E1, and E2
is proved. To state the distribution of the extracted code under `RandomFill`, E3 or another
semantics of `random` with the same role is necessary.

## Weakest pre-expectation

A weakest pre-expectation maps a function `g` from outcomes to `ENNReal` to the expected value of
`g` after a run of `x`. For `x : Result α` and `g : Result α → ENNReal`, these equations describe
it:

```
wpe⟦ok a⟧ g              = g (ok a)
wpe⟦fail e⟧ g            = g (fail e)
wpe⟦div⟧ g               = 0
wpe⟦vis (random n) k⟧ g  = (1 / 256^n) · Σ_b wpe⟦k b⟧ g
```

`Result` is coinductive, so the equations are not a recursive definition. `wpe` is the least
fixpoint of the operator that the equations describe, on the complete lattice of functions
`Result α → (Result α → ENNReal) → ENNReal`. The terminal cases do not depend on the argument, and
a finite sum multiplied by `(256^n)⁻¹` is monotone. So the operator is monotone, and the
Knaster-Tarski theorem gives the fixpoint and the four equations. `DWP` in
`Aeneas/Data/Coinductive/ITreeWP/DWP.lean` uses the same construction with `Prop`.

With the least fixpoint, an infinite execution contributes 0: its probability mass is not in the
distribution of terminal outcomes. This is not a claim that the probability of nontermination is
0. A program that samples forever has `wpe⟦x⟧ (fun _ => 1) = 0`, and it never terminates.

The failure equation chooses how failure counts. With `g (fail e)`, failure is an outcome. With 0
in its place, failure is absent, as in a sub-probability distribution. E3 cannot fix this choice,
because `toResult m` never fails. The examples need failure as an outcome, because Crypto
definitions return `Result.ok`.

`wpe` is defined on every `Result`. So E3 needs no interpreter on the image of `toResult`, and no
proof that `toResult` is injective. Each `toResult m` is a finite tree, because `RandSpec` has
finite answer types. So E3 follows by induction on `m`. The query case uses the `random` equation,
the bind law of VCVio's `wp`, and the fact that `uniformImpl n` gives each byte vector the
probability `(256^n)⁻¹`. The last fact needs a short proof, because `uniformImpl` samples
`List.Vector U8 n` and converts it with `bytesOfVector`.

With E1 and E2, E3 gives an end-to-end theorem under `RandomFill`. It keeps the state and the
output conversion of each example. For ByteMask:

```
wpe⟦mask inst rng v⟧ g  =  wp (Crypto.mask v) (fun y => g (ok (y, rng)))
```

For ProbSmoke:

```
wpe⟦fill_random inst rng buffer⟧ g  =
  wp (Crypto.fill_random buffer.length) (fun bytes => g (ok (rng, sliceOfVector buffer bytes)))
```

These are statements about the distribution of the extracted code, as O3 is for the Oracle
approach. `wpe` also gives probabilities that `Prop` does not, for example the probability of
failure.

E3 does not prove any part of the assumption that the real OS generator is uniform. It proves that
two readings of `random` agree: the `wpe` reading of the extracted tree, and the `uniformImpl`
reading of the model. The assumption on the real generator stays as it is.

`wpe` has these limits:

1. `mvcgen` produces `Prop` goals, so `wpe` needs its own rules. For the examples, the unfolding
   equations and `simp` are enough.
2. E3 does not need a bind rule. For extracted code in general, the rule for
   `x : Result α`, `h : α → Result β` and `g : Result β → ENNReal` is
   `wpe⟦x >>= h⟧ g = wpe⟦x⟧ g'`, where `g' (ok a) = wpe⟦h a⟧ g`, `g' (fail e) = g (fail e)`
   at type `Result β`, and `g' div = 0`. Its proof needs fixpoint approximation. The operator is
   continuous, because finite sums and multiplication by a constant preserve increasing suprema in
   `ENNReal`. So this is a proof to write, not an extra assumption. An outcome type such as
   `Except Error α` makes the interface cleaner than functions on `Result α`.
3. `wpe` describes one program. A security proof compares programs, with direct arguments on
   distributions or with a relational logic.
## The `mvcgen` behavior of the patch

The patch extends `spec` and `dspec` correctly. If a postcondition holds for all bytes, then a
computation that samples satisfies it. But the predicate transformer of `mvcgen` only looks at the
head of a computation. For a computation that starts with `Result.random`, the patch sets it to
`True` (the `.random _ => ⌜True⌝` case of `Result.instWP` in `WP.lean`). So a `mvcgen` triple
about such a computation holds for every postcondition. For example, this triple is provable by
`simp [Triple, x, Result.random, WP.wp, PredTrans.apply, bind_vis]`, although `x` always panics:

```lean
def x : Result Unit := do let _ ← Result.random 1; Result.fail .panic

example : ⦃⌜True⌝⦄ x ⦃⇓ _ => ⌜False⌝⦄
```

Without the `Result.random` step, the same proof ends with the goal `False`.

The patch documents this choice. It keeps `spec_to_mvcgen` free of side conditions, and
`Result.of_wp` has a precondition that prevents a wrong conclusion about results. So the logic is
consistent, but such a triple gives no information about the code after the first sample. A
triple can still give information about the code before the first sample. Use `step`, not
`mvcgen`, on code that samples.

These are four design choices for the `wp` of a `random` head. The list is not complete:

1. `⌜True⌝`, the choice of the patch. A triple about code that starts with `random` holds for
   every postcondition.
2. The dummy exception, which the patch comment mentions. A triple with a satisfiable
   precondition and a postcondition for success only is false. A triple that allows the dummy
   exception can hold. This is safe, but it gives no information either.
3. The demonic reading: the postcondition holds for all bytes. This agrees with `spec`
   (`spec_random`) and with `step`. It expresses functional properties, such as "`mask` returns
   `(pad, v ^^^ pad)`". On infinite trees, the choice between total and partial correctness
   (least or greatest fixpoint) is separate.
4. The probabilistic reading, `wpe` above. It expresses distributions, such as "the pad is
   uniform". It has values in `ENNReal`, so it does not fit the `Prop`-valued `Std.Do` of
   `mvcgen`. VCVio has a quantitative `Std.WP` for `OracleComp`.

Option 3 is the meaningful choice for `mvcgen`, and option 4 is the meaningful choice for
distributions. Option 3 needs the continuation `k b`. A `wp` that only looks at the head cannot
give it. These two programs have the same head:

```lean
def good : Result Unit := do let _ ← Result.random 1; Result.ok ()
def bad  : Result Unit := do let _ ← Result.random 1; Result.fail .panic
```

A demonic total-correctness `wp` separates them, because `spec good` holds for `True` and
`spec bad` does not. A head-only `wp` gives them the same value. The bind law also forces the
continuation: `wp (Result.random n >>= k) Q = wp (Result.random n) (fun b => wp (k b) Q)`. The
current head-only `wp` with `⌜True⌝` satisfies the bind law. The problem is meaning, not
lawfulness.

A specification `⦃⌜∀ b, P b⌝⦄ Result.random n ⦃⇓ b => ⌜P b⌝⦄` does not help. Under the current
`wp`, it is already provable, because the `wp` of `Result.random n` is `True`.

The route to option 3 is to define the `wp` of `mvcgen` from the demonic `DWP` of the patch. This
is not tried yet. It has these proof obligations:

1. A policy for failure and divergence. `spec` rejects both. The current `Std.Do` instance passes
   them to the exception postconditions. The new `wp` must choose one of the two.
2. The bind law, as an equality of predicate transformers. `DWP.bind` only gives an implication.
3. Conjunctivity, which `Std.Do.PredTrans` requires.

## Next steps

To prove C, start from branch `probsmoke-bytemask-effect-bridge`:

1. If `aeneas/` is missing, run `bash scripts/aeneas.sh`. Then run `lake build`.
2. State `τ` and C in `Common/Effect/Random.lean`. Prove C by induction on `p`
   (`OracleComp` has the eliminators `pure` and `queryBind`). Use `runProg`, `fillImpl` and
   `runProg_query` from `Common/Oracle/Rng.lean`, and `RandomFill.fill_eq`.
3. Derive `mask_eq` from `byte_mask.Oracle.Bridge.mask_eq_prog` and C, and `fill_random_eq` from
   `prob_smoke.Oracle.Bridge.fill_random_eq_prog` and C. Keep the current statements.
4. Run `bash scripts/check.sh`.

Do not run `lake` inside `git rebase --exec`. If you must check intermediate commits, check them
out one at a time.

For E3:

1. Define `wpe` on `Result` as a least fixpoint, in `Common/Effect/`, with failure as an outcome.
2. Prove the four unfolding equations.
3. Prove that `uniformImpl n` gives each byte vector the probability `(256^n)⁻¹`.
4. Prove E3 by induction on the oracle program `m`, with VCVio's quantitative `wp` on the right.
5. State the end-to-end theorems for `mask` and `fill_random` under `RandomFill`, with the state
   and the output conversion of each example, from E1, E2 and E3.
