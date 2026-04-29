# Cycle 024 — strategy

## Primary target: `lem:322A` — "Methods of order 4" auxiliary linear-algebra lemma (§322)

Statement (`extraction/formalization_data/entities/lem_322A.json`,
verbatim):

> If `P` and `Q` are each `3 × 3` matrices such that their product
> has the form
>
>     PQ = ⎡ r₁₁  r₁₂  0 ⎤
>          ⎢ r₂₁  r₂₂  0 ⎥
>          ⎣  0    0   0 ⎦
>
> where `det [r₁₁ r₁₂ ; r₂₁ r₂₂] ≠ 0`, then either the last row of `P`
> is zero or the last column of `Q` is zero.

Butcher's proof (verbatim from the entity JSON):

> Because `PQ` is singular, either `P` is singular or `Q` is
> singular. In the first case, let `u ≠ 0` be such that `uᵀP = 0`,
> and therefore `uᵀPQ = 0`; in the second case, let `v ≠ 0` be such
> that `Qv = 0`, and therefore `PQv = 0`. Because of the form of
> `PQ`, this implies that the first two components of `u` (or,
> respectively, the first two components of `v`) are zero.

### Why this target

* **Zero dependencies** — `dependencies: []` and
  `transitive_dependencies: []` in the entity JSON. Pure linear
  algebra over `ℝ`. No rooted trees, no `RKTableau`, no Mathlib
  ODE machinery. Anything blocking the §380 or §31x clusters
  (`thm:314A`, `thm:306A`, `reducedMethod` construction, partition
  algebra) is irrelevant here.
* **Concretely achievable in one cycle.** The proof is one
  rank/null-vector argument plus a 2-line case analysis on the
  zero-row index.
* **Mathlib has everything.** `Matrix.det`, `Matrix.det_mul`,
  `Matrix.isUnit_iff_isUnit_det`, `Matrix.det_fin_three`,
  `Matrix.transpose`, and `Matrix.ext` cover the entire argument.
* **Opens a new chapter file** (`OpenMath/Chapter3/Section322.lean`),
  consistent with the §343 / §380 / §312 / §301 / §310 sectional
  layout.
* **Avoids cherry-picking.** This is genuinely the next
  zero-dependency entity in plan.md's Chapter 3 list. The cycle 023
  worker's three suggestions (`thm:381G` scoping, `def:370A`
  transpose-resolution, `thm:302C` combinatorics) are each either
  multi-cycle infrastructure work or blocked on labelling
  infrastructure that we have not yet built.

## Worker action plan (sorry-first, then close)

### Step 1 — read the entity record

```
Read extraction/formalization_data/entities/lem_322A.json
```

Confirm the textbook statement and proof match your understanding
before writing Lean.

### Step 2 — create `OpenMath/Chapter3/Section322.lean`

Add the import to `OpenMath/Chapter3.lean` and skeleton the file:

```lean
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation

/-!
# Butcher §322 — Methods of order 4 (Lemma 322A)

This file formalises Lemma 322A …
-/

namespace OpenMath.Chapter3.Section322

open Matrix

theorem order_four_block_zero_decomposition
    (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (h_block : ∀ i, (P * Q) i 2 = 0 ∧ (P * Q) 2 i = 0)
    (h_det :
        (P * Q) 0 0 * (P * Q) 1 1 - (P * Q) 0 1 * (P * Q) 1 0 ≠ 0) :
    (∀ j, P 2 j = 0) ∨ (∀ i, Q i 2 = 0) := by
  sorry

end OpenMath.Chapter3.Section322
```

The two hypotheses `h_block` and `h_det` together encode "PQ has the
block form `⎡R 0; 0 0⎦` with `R` non-singular". Verify in Lean that
this matches the textbook display literally.

Run `lake env lean OpenMath/Chapter3/Section322.lean` to confirm the
sorry-skeleton compiles.

### Step 3 — close the sorry by hand

The textbook proof is short enough that direct manual proof should
work without Aristotle. Outline:

1. Show `det (P * Q) = 0`. Either expand the 3×3 determinant via
   `Matrix.det_fin_three` and read off zeros, or use the third row
   being zero plus `Matrix.det_eq_zero_of_row_eq_zero`. Do **not**
   use `Matrix.det_succ_row_zero` (cofactor expansion); the direct
   `det_fin_three` plus zero-substitution is cleaner.
2. Conclude `det P * det Q = 0` via `Matrix.det_mul`.
3. Case split: `det P = 0 ∨ det Q = 0`.
4. In the first case, obtain `u : Fin 3 → ℝ` with `u ≠ 0` and
   `u ᵥ* P = 0`. The right Mathlib name is most likely
   `Matrix.exists_vecMul_eq_zero_of_det_eq_zero` or
   `Matrix.left_mul_inj_iff_isUnit_det` complemented by negation. If
   neither lands directly, search:
   ```
   lean_local_search "vecMul_eq_zero"
   lean_loogle "Matrix.det _ = 0 → ?"
   ```
   The classical statement is "a non-invertible matrix has a non-zero
   left null vector".
5. From `u ᵥ* P = 0`, deduce `u ᵥ* (P * Q) = 0`. Then by `h_block`
   and the form of PQ, `u ᵥ* PQ = (u 0 * (P*Q) 0 0 + u 1 * (P*Q) 1 0,
   u 0 * (P*Q) 0 1 + u 1 * (P*Q) 1 1, 0)`. Setting this to zero
   yields a 2×2 system in `(u 0, u 1)` with non-singular coefficient
   matrix (by `h_det`), so `u 0 = u 1 = 0`. Combined with
   `u ≠ 0` we get `u 2 ≠ 0`.
6. Then `(u ᵥ* P) j = 0` for all `j`, i.e.
   `u 0 * P 0 j + u 1 * P 1 j + u 2 * P 2 j = 0`. With `u 0 = u 1 = 0`
   and `u 2 ≠ 0`, this gives `P 2 j = 0` for all `j`. ∎ (left disjunct).
7. The `det Q = 0` case is symmetric: `Q.mulVec v = 0` for some
   non-zero `v`, then `Q i 2` for all `i` (right disjunct).

If a sub-step (especially step 4 — the lemma-name lookup) takes more
than one `lean_multi_attempt` round, decompose it into a named
`have` with a local `sorry` and proceed. Submit that named sub-lemma
to Aristotle in step 4 below.

### Step 4 — Aristotle batch (only if step 3 stalls)

If step 3 hits more than one lemma-name dead end, batch-submit the
following named sub-lemmas to Aristotle:

1. **`exists_left_null_of_det_eq_zero`**: For `M : Matrix (Fin 3)
   (Fin 3) ℝ` with `M.det = 0`, there exists `u : Fin 3 → ℝ` with
   `u ≠ 0` and `u ᵥ* M = 0`.
2. **`exists_right_null_of_det_eq_zero`**: symmetric, with
   `M.mulVec v = 0`.
3. **`block_2x2_nonsing_kills_first_two`**: Given the `h_block` and
   `h_det` hypotheses, plus `u ᵥ* (P*Q) = 0`, conclude
   `u 0 = 0 ∧ u 1 = 0`.

These are three small lemmas. Submit, sleep 30 minutes (use the
`mcp__aristotle__submit_*` tools), then incorporate. Do **not**
poll repeatedly.

### Step 5 — concrete witness check

This is a lemma not a definition, so the "concrete instance"
requirement of CLAUDE.md does not literally apply. But add one
`example` near the bottom of the file demonstrating the lemma is
non-vacuous: pick `P = identity matrix with last row zeroed` and
`Q = identity` (or some explicit pair with `PQ = ⎡R 0; 0 0⎦`,
`det R ≠ 0`). Verify the conclusion holds for this example. This
catches definition-smuggling errors (e.g. accidentally requiring
`PQ` to be the zero matrix).

### Step 6 — pre-commit faithfulness check

Run the CLAUDE.md checklist:

* **For new `theorem order_four_block_zero_decomposition`**:
  * Quote the textbook statement (above) in the docstring.
  * Confirm Lean's hypothesis encoding `h_block` ∧ `h_det` literally
    captures "PQ = ⎡R 0; 0 0⎦ with `det R ≠ 0`".
  * Tautology check: conclusion is a disjunction; not a hypothesis.
  * Identity check: proof is non-trivial (multi-step rank argument).
  * Hypothesis-strength check: the textbook does not state the
    matrices are over `ℝ`; it works over any field. Worth noting in
    the docstring that we specialise to `ℝ` because Butcher's
    Runge–Kutta context is over `ℝ`. **Do NOT** generalise to a
    field parameter — keep the proof over `ℝ` for this cycle to
    avoid scope creep.

### Step 7 — bookkeeping

* Update `extraction/formalization_data/lean_status.json`: flip
  `lem:322A` from `unformalized` to `formalized`, set
  `lean_file: "OpenMath/Chapter3/Section322.lean"`,
  `lean_symbol: "OpenMath.Chapter3.Section322.order_four_block_zero_decomposition"`.
  (Use the exact symbol you committed.)
* Bump `plan.md`: flip `[ ] lem:322A` → `[x] lem:322A`, bump the
  progress counter `24 / 175` → `25 / 175`.
* Append `OpenMath/Chapter3/Section322` to `OpenMath/Chapter3.lean`'s
  import list so the chapter aggregator picks it up.

### Step 8 — write `task_results/cycle_024.md`

Use the CLAUDE.md template. Include:
* Full faithfulness write-up for the new theorem.
* Any Mathlib-name discoveries from step 3.4 (the null-vector
  lemma) — these are reusable for future linear-algebra theorems.
* Suggested next approach for cycle 025.

### Step 9 — commit

* `lake env lean OpenMath/Chapter3/Section322.lean` — must pass.
* `lake build` — must pass (full chapter).
* `rg '\bsorry\b' OpenMath/` — must be empty.
* `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/` —
  must be empty.
* `#print axioms` on the new theorem — must show only
  `propext, Classical.choice, Quot.sound`.

Commit message: `Formalize lem:322A 3x3 block-product lemma for order-4 RK methods`.

## Fallback if blocked

If step 3 hits a wall that is NOT lemma-name lookup — e.g. a Mathlib
gap in `Matrix` rank/null-vector API for `Fin 3` — switch to:

**Backup target: scoping `thm:381G` partition-algebra infrastructure.**

This is the cycle-023 worker's #1 suggestion. The work product is
**not** a closed proof — it is a structured `OpenMath/Chapter3/Section381G_Scope.lean`
file that declares the partition-algebra infrastructure with explicit
`sorry` decompositions, plus a corresponding
`.prover-state/issues/thm_381G_scope.md` describing exactly what
needs to come next. The intermediate sorries are EXPLICITLY allowed
this cycle (they are mid-restructuring, per CLAUDE.md). The worker
should:

1. Scaffold the proof: state `irreducible_implies_phi_distinguishability`
   with the partition `P` defined as
   `i ~ j ⟺ ∀ t, internalWeight M i t = internalWeight M j t`.
2. State (with sorry) the four key sub-lemmas:
   - `algebra_closed_under_A`: the subalgebra generated by Φ-vectors
     is closed under matrix-A multiplication.
   - `characteristic_function_in_subalgebra`: the characteristic
     function of each partition block is in the subalgebra.
   - `algebra_eq_full`: the subalgebra equals the full
     P-block-constant algebra.
   - `partition_irreducibility_contradiction`: A · char_J having
     block-constant components contradicts irreducibility.
3. Each sorry must have a ≥ 5-line block comment explaining (a) what
   it asserts, (b) why it suffices, (c) what infrastructure is
   needed (e.g. "needs Mathlib `Algebra.Subalgebra` over `Fin s →
   ℝ` with component-wise mul"). This is real, productive work for
   future cycles.
4. Skip the second half of `thm:381G` (the Y-stage clause). Note
   in the file docstring that the second half depends on
   `thm:314A` which is unformalized.

The fallback's commit message: `Scope thm:381G partition-algebra
infrastructure with explicit sorry decomposition`.

## Things NOT to try this cycle

The following approaches have failed or are blocked; do **not**
spend cycle time on them:

* **Do NOT pick `lem:310B`.** It depends on `thm:306A` (Taylor's
  theorem), unformalized. The proof literally says "Use Theorem
  306A".
* **Do NOT pick `def:381F`.** Blocked on the deferred `reducedMethod`
  construction (see `.prover-state/issues/reduced_method_deferred.md`).
  Settle Q1 + Q2 of that issue first.
* **Do NOT pick `thm:317A`.** Depends on `thm:314A` and `lem:310B`,
  both unformalized.
* **Do NOT pick `thm:381G` for full formalization.** Multi-cycle
  effort. Scoping is the fallback above; full formalization waits
  for §314.
* **Do NOT pick `thm:302A` / `thm:302B` / `thm:302C`.** They require
  building substantial labelling-count infrastructure (`α(t)`,
  `β(t)`, automorphism orbits) that we have not yet built. Multi-
  cycle. Plus Section301 already has the `symmetry_group_equivalence`
  faithfulness gap; adding `α/β` would compound it.
* **Do NOT pick `def:370A`.** The textbook formula
  `M = diag(b)A + Aᵀdiag(b) - bbᵀ` (or its variant) has a
  transpose-ambiguity unresolved between Butcher and Hairer–Wanner;
  scope this with the consultant subagent first, in a future cycle,
  before formalising.
* **Do NOT pick `thm:343B`.** Depends on §321 simplifying-assumption
  framework `B(η), C(η), D(η), E(η,ζ)` which is not yet started.
* **Do NOT modify `scripts/autonomous_loop.py`.** Per CLAUDE.md and
  cycle-014/015 consultant notes; scanner / prompt-builder bugs
  belong in the existing
  `.prover-state/issues/tautology_scanner_false_positives.md` file,
  not in worker edits to the loop.
* **Do NOT generalise `lem:322A` to a parametric field.** The
  textbook works over `ℝ`; over-generalising adds typeclass
  bookkeeping and risks blocking the proof. Stay over `ℝ`.
* **Do NOT raise `maxHeartbeats` above 200000.** The proof should
  not need it; if it does, decompose.
* **Do NOT introduce `axiom` or `constant`.**
* **Do NOT poll Aristotle repeatedly.** If you submit any sub-lemma
  in step 4, submit, sleep 30 min, check once, and incorporate or
  prove manually. No per-minute polling.

## Aristotle quota note

Aristotle was not used in cycles 020–023 (worker judged the proofs
short enough to do by hand). The free-compute quota is therefore
healthy. If cycle 024's step 3 stalls on the null-vector lemma name
lookup, this is a good cycle to use Aristotle on the three named
sub-lemmas in step 4 — they are exactly the kind of "find the right
Mathlib lemma name" tasks Aristotle excels at.

## Open issues — status as of cycle 024

* `consultant_advice_cycle_009.md` — meta diagnosis; informational.
* `consultant_advice_cycle_014.md` — scanner false-positive
  diagnosis; informational. Workaround applied (cycle 015).
* `consultant_advice_cycle_015.md` — phantom-stuck diagnosis;
  informational.
* `jordan_canonical_form_missing.md` — §142 deferred; not blocking
  Chapter 3.
* `picard_lindelof_bound_strengthening.md` — §319 deferred; not
  blocking lem:322A.
* `reduced_method_deferred.md` — blocks `def:381F` and onward in
  §380; not blocking lem:322A.
* `symmetry_group_equivalence.md` — §300 σ-faithfulness deferred;
  not blocking lem:322A (no rooted trees here).
* `tautology_scanner_false_positives.md` — loop-maintainer issue;
  worker should not touch.

None of these block the primary target. The fallback (scoping
`thm:381G`) interacts with `reduced_method_deferred.md` only
indirectly (both are §380 work) and would reasonably reference it
in the new scope file.

## Success criteria

Cycle 024 succeeds if EITHER:

* **Primary path:** `lem:322A` is fully formalised in
  `OpenMath/Chapter3/Section322.lean`, zero sorries, axiom check
  clean, `lake build` passes, `lean_status.json` and `plan.md`
  updated, `task_results/cycle_024.md` written, committed, pushed.
  Progress: 24/175 → 25/175.
* **Fallback path:** A scoping file
  `OpenMath/Chapter3/Section381G_Scope.lean` plus
  `.prover-state/issues/thm_381G_scope.md` are committed with
  explicit sorry-decomposition for the four sub-lemmas listed in
  the fallback section. Progress counter unchanged but a clear
  multi-cycle plan is laid down.

A cycle that produces neither is unacceptable per CLAUDE.md.
