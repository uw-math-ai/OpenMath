# Consultant advice — cycle 009

Author: consultant subagent.
Date: 2026-04-28.
Phase at time of writing (per `heartbeat.json`): cycle 9, `consultant`.
Branch tip: `3b1c87f Formalize thm:111A superposition principle for linear ODE systems`.

This advice covers (A) the meta-issue raised in the prompt
("commits not reaching repo for 4 cycles"), and (B) two of the three
real outstanding items: `thm:112B` (the immediate next target), the
`picard_lindelof_bound_strengthening` issue, and the
`jordan_canonical_form_missing` issue.

---

## A. Meta: "commits not reaching the repo" is a stale verdict

**Diagnosis: false alarm.** The prompt's framing ("fourth consecutive
cycle of empty diff") is contradicted by the actual git state:

```
$ git log --oneline -3
3b1c87f Formalize thm:111A superposition principle for linear ODE systems
1c3d12e Formalize thm:110C Picard-Lindelöf existence and uniqueness via Mathlib
e3c8474 Fix strategy_deviation regex to match nested OpenMath/ paths
```

* Cycle 008's commit (`1c3d12e`, thm:110C) IS on the branch tip and on
  `origin/Main/Experiments`. Cycle 008's `task_results/cycle_008.md`
  describes work that matches the diff at `1c3d12e` exactly.
* Cycle 009's commit (`3b1c87f`, thm:111A) IS likewise present, with a
  `cycle_009.md` task-result file that matches the diff (4 files,
  +276 / -3, includes new `OpenMath/Chapter1/Section111.lean`).
* The cycle-009 strategy file (`.prover-state/strategy.md`) explicitly
  flags the cycle-008 "empty diff" verdict as a false alarm:
  > `thm:110C` IS committed (commit `1c3d12e`, on disk in
  > `OpenMath/Chapter1/Section110.lean`). The cycle-8 "empty diff"
  > verdict was a false alarm — the work landed.

**What likely happened.** The supervisor's diff-stat heuristic
(presumably `git diff` between two stale refs, or a `git diff` that
ran before `git push`) reported empty even though the commit was
created. `.prover-state/attempts.md` carried that verdict forward
verbatim into cycle 009's prompt context, where it has now resurfaced
as the stated blocker.

**Recommendation.** Before any further worker iteration, the loop
machinery should run the following verification (and cache its output
into `attempts.md`) instead of relying on the inherited verdict:

```bash
# Was a commit produced this cycle?
git log -1 --format='%H %s'
# Did it actually push?
git fetch origin
git log -1 origin/Main/Experiments --format='%H %s'
# Are they the same?  Compare HEAD with origin tip.
git rev-parse HEAD
git rev-parse origin/Main/Experiments
# Non-empty diff vs previous commit?
git diff --stat HEAD~1 HEAD
```

If `HEAD == origin/Main/Experiments` AND `git diff HEAD~1 HEAD` is
non-empty, the cycle landed; otherwise diagnose specifically. Three
likely failure modes (none of which are present in cycles 005–009):

1. Worker writes files outside the repo working tree (e.g. into
   `.prover-state/aristotle_results/<id>/extracted/...` rather than
   `OpenMath/Chapter1/...`) and never `git mv`s them in. Diagnose by
   `find . -name 'Section*.lean' -newer .git/HEAD`.
2. Worker stages but does not commit (`git status` shows staged
   green). Diagnose by `git diff --cached --stat`.
3. Worker commits but does not push. Diagnose by comparing local and
   remote SHAs as above.

**Action item for the loop maintainers (NOT the worker):** the
"empty-diff" check in `attempts.md` appears to be a copy-paste from a
template, not a real measurement. Audit
`scripts/launch_loop.sh` and the supervisor's status reporter to make
sure the diff check is computed *after* the worker's `git commit /
git push` block exits, against the commit just produced (not against
the stale ref the loop started with). The cycle-005 task result
(`cycle_005.md`) already shipped real changes (`Section142.lean`),
visible at commit `d4bb6a5`, so the "cycles 5–8 empty diff" claim is
demonstrably false at least 4× over.

The worker should NOT spend any more cycle time chasing this; it is a
phantom problem.

---

## B. `thm:112B` — One-sided-Lipschitz solution-difference bound (next cycle)

This is the natural next target per `cycle_009.md`'s "Suggested next
approach" section. `def:112A` (`OneSidedLipschitzInSecond`) is already
formalised at `OpenMath/Chapter1/Section112.lean`.

### Mathematical argument that should work

Butcher's textbook proof transcribed:

1. Fix `y, z : ℝ → E` solving `y' = f(x, y(x))`, `z' = f(x, z(x))` on
   `[x₀, b]`, where `E` is a real inner product space. Let
   `u(x) := y(x) - z(x)`.
2. `u' = f(x, y) - f(x, z)`. By the inner-product chain rule for
   `‖u‖²`:
   `(d/dx) ‖u(x)‖² = 2 ⟨u'(x), u(x)⟩
       = 2 ⟨f(x, y(x)) - f(x, z(x)), y(x) - z(x)⟩
       ≤ 2 ℓ ‖u(x)‖²`
   where the last inequality is `def:112A`.
3. Apply (the scalar version of) Grönwall to the scalar function
   `g(x) := ‖u(x)‖²`. The hypothesis becomes
   `g'(x) ≤ 2ℓ * g(x) + 0`, so `g(x) ≤ g(x₀) * exp(2ℓ(x - x₀))`.
4. Take square roots:
   `‖u(x)‖ ≤ ‖u(x₀)‖ * exp(ℓ(x - x₀))`.

### Relevant Mathlib lemmas (verified to exist in pinned Mathlib)

All lemmas below are in `Mathlib.Analysis.ODE.Gronwall` (already
imported by `Section110.lean`) or `Mathlib.Analysis.InnerProductSpace.*`.

**Grönwall.** The textbook proof above wants the *scalar* Grönwall
inequality applied to `g(x) := ‖u(x)‖²`. Use:

* `le_gronwallBound_of_liminf_deriv_right_le`
  (`Mathlib/Analysis/ODE/Gronwall.lean:111`):
  for `f : ℝ → ℝ` continuous on `[a, b]` with right-liminf-slope
  `≤ K * f x + ε`, conclude `f x ≤ gronwallBound δ K ε (x - a)`. With
  `δ := ‖u(x₀)‖²`, `K := 2ℓ`, `ε := 0`, this matches.
* If `u` is differentiable on the whole open interval (true under
  Butcher's setup since `y, z` are exact solutions), the right-liminf
  hypothesis can be supplied by `HasDerivAt → liminf_right_slope_le`,
  via the Mathlib helper used inside
  `norm_le_gronwallBound_of_norm_deriv_right_le`.

**Inner-product / norm-square derivative.** Need
`(d/dx) ‖u(x)‖² = 2 ⟨u'(x), u(x)⟩`. Useful Mathlib facts:

* `@inner_self_eq_norm_sq_to_K` /
  `real_inner_self_eq_norm_mul_norm` /
  `real_inner_self_eq_norm_sq` (`Mathlib/Analysis/InnerProductSpace/Basic.lean`):
  `⟨u, u⟩ = ‖u‖²` over `ℝ`.
* `HasDerivAt.inner` (loogle: `HasDerivAt _ _ _ → HasDerivAt _ _ _ → HasDerivAt (⟪·, ·⟫) ...`):
  the inner-product chain rule. Apply to
  `f := u`, `g := u`, output `⟨u', u⟩ + ⟨u, u'⟩ = 2 ⟨u', u⟩`.
* In Mathlib, `‖·‖²` for a real inner-product space typically goes
  through `norm_sq` or `‖x‖^2`. Either spelling works; reduce to
  `⟨x, x⟩` via `real_inner_self_eq_norm_sq`.

**Scalar-Grönwall consequence: closed-form bound.** After applying
`le_gronwallBound_of_liminf_deriv_right_le` with `ε = 0`, the bound
becomes `gronwallBound δ K 0 (x - a) = δ * exp(K * (x - a))`. Mathlib
exposes this rewrite as `gronwallBound_ε0`. So you immediately get
`‖u(x)‖² ≤ ‖u(x₀)‖² * exp(2ℓ(x - x₀))`.

**Final square-root step.** From
`g(x) ≤ g(x₀) * exp(2ℓ(x - x₀))`:

* `Real.sqrt_le_sqrt` (monotonicity).
* `Real.sqrt_mul` and `Real.sqrt_exp` (or `Real.exp_half`-style:
  `sqrt (exp t) = exp (t/2)`, see `Real.sqrt_exp` in
  `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`-adjacent files;
  `loogle` for `Real.sqrt (Real.exp _)`).
* `Real.sqrt_sq` to remove `‖·‖²`.
* The exponent halves: `2ℓ(x - x₀) / 2 = ℓ(x - x₀)`.

### Recommended Lean signature

Match Butcher's setup tightly. Keep `s : Set ℝ` polymorphism (parallels
`def:110A` / `def:112A`); the textbook instance is `s = Icc x₀ b`.

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus  -- for HasDerivAt.inner
import Mathlib.Analysis.ODE.Gronwall
import OpenMath.Chapter1.Section112  -- def:112A is here

namespace OpenMath.Chapter1.Section112

open Real Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Butcher §112 Theorem 112B — one-sided Lipschitz solution-difference
bound. -/
theorem one_sided_lipschitz_solution_diff_bound
    {x₀ b : ℝ} (hx : x₀ ≤ b)
    {ℓ : ℝ}
    {f : ℝ → E → E}
    (hf : OneSidedLipschitzInSecond (Icc x₀ b) ℓ f)
    {y z : ℝ → E}
    (hy_cont : ContinuousOn y (Icc x₀ b))
    (hy : ∀ x ∈ Ico x₀ b, HasDerivWithinAt y (f x (y x)) (Ici x) x)
    (hz_cont : ContinuousOn z (Icc x₀ b))
    (hz : ∀ x ∈ Ico x₀ b, HasDerivWithinAt z (f x (z x)) (Ici x) x) :
    ∀ x ∈ Icc x₀ b,
        ‖y x - z x‖ ≤ Real.exp (ℓ * (x - x₀)) * ‖y x₀ - z x₀‖ := by
  sorry
```

Two things to note about this signature:

* `HasDerivWithinAt … (Ici x) x` matches `Section110.lean`'s convention
  exactly (and matches Mathlib's `ODE_solution_unique_of_mem_Icc_right`).
  The chain rule for inner products via `HasDerivWithinAt` is
  `HasDerivWithinAt.inner`. If that lemma has a slightly different name
  in the current Mathlib (loogle:
  `HasDerivWithinAt _ _ _ _ → HasDerivWithinAt _ _ _ _ →
   HasDerivWithinAt (⟪·, ·⟫) _ _ _`), use that.
* No `‖f‖`-bound strengthening is needed — this is a *uniqueness-style*
  statement, not an existence statement, so `picard_lindelof_bound_
  strengthening.md` does NOT inherit. Confirm by checking the
  hypothesis list against `entities/thm_112B.json` — Butcher requires
  only `f` one-sided Lipschitz and `y, z` solutions.

### Concrete Lean tactic plan

Inside the proof, the cleanest decomposition is:

1. **Reduce to scalar Grönwall on `g := ‖y - z‖²`.** Define
   `g : ℝ → ℝ := fun x => ‖y x - z x‖^2`. By
   `real_inner_self_eq_norm_sq`, `g x = ⟪y x - z x, y x - z x⟫`.

2. **Differentiability of `g`.** From `hy x` and `hz x`, get
   `(y - z)`'s right derivative `f x (y x) - f x (z x)`. Then
   `HasDerivWithinAt.inner` (apply twice with the same derivative
   pair) gives:
   ```
   HasDerivWithinAt g
     (⟪f x (y x) - f x (z x), y x - z x⟫
      + ⟪y x - z x, f x (y x) - f x (z x)⟫) (Ici x) x
   ```
   The two summands are equal (real inner product is symmetric); use
   `real_inner_comm` to combine into `2 * ⟪f x (y x) - f x (z x), y x - z x⟫`.

3. **Apply the one-sided Lipschitz hypothesis.** From `hf`:
   `⟪f x (y x) - f x (z x), y x - z x⟫ ≤ ℓ * ‖y x - z x‖² = ℓ * g x`.
   Multiply by 2: `g'(x) ≤ 2ℓ * g(x)`.

4. **Apply `le_gronwallBound_of_liminf_deriv_right_le`** with
   `δ := g x₀`, `K := 2ℓ`, `ε := 0`. The right-liminf hypothesis is
   discharged by `HasDerivWithinAt.liminf_right_slope_le` (look up the
   exact name; it's the helper used inside
   `norm_le_gronwallBound_of_norm_deriv_right_le`).

5. **Simplify the bound.** `gronwallBound_ε0` gives
   `gronwallBound (g x₀) (2ℓ) 0 (x - x₀) = g x₀ * exp(2ℓ(x - x₀))`.

6. **Square root.** `Real.sqrt_le_sqrt` plus `Real.sqrt_sq` (need
   `0 ≤ ‖_‖`) plus `Real.sqrt_mul` (need `0 ≤ g x₀`) plus
   `Real.sqrt_exp` (or `Real.exp_half`: `√(exp t) = exp (t/2)`).
   The exponent halves to `ℓ(x - x₀)`.

### `lean_multi_attempt` snippets to try at step 2 (chain rule)

If the obvious shape fails, try these in `lean_multi_attempt`:

```text
exact (hyz.inner hyz)
exact HasDerivWithinAt.inner hyz hyz
exact HasDerivWithinAt.inner ℝ hyz hyz
have := (hyz.inner hyz : HasDerivWithinAt _ _ _ _); convert this using 2; ring
```

(where `hyz := (hy x ‹_›).sub (hz x ‹_›)`).

### Aristotle batch suggestion

If steps 1–3 close by hand but step 4 (the Grönwall plumbing) and step
6 (square root) don't, batch-submit those two sub-goals to Aristotle.
The Grönwall sub-goal in particular is exactly the kind of lemma-name
substitution Aristotle excels at. **Do not** submit step 2 (chain
rule) to Aristotle until you have *tried* `lean_multi_attempt` on the
four snippets above — chain rule shapes are sensitive to which
`HasDerivAt` variant is at play and Aristotle often picks the wrong
one.

### Faithfulness flags for cycle 010's pre-commit check

* The textbook proof says `‖y(x) - z(x)‖ ≤ exp(ℓ(x - x₀)) · ‖y(x₀) -
  z(x₀)‖`. The Lean statement above orders the factors differently
  (`exp · norm` vs `norm · exp`); both are equal, but pick one and be
  consistent with downstream consumers.
* The textbook says "`f` satisfies a one-sided Lipschitz condition
  with constant `l`" without specifying a domain. Our `def:112A`
  parameterises by `s : Set ℝ`. Pick `s = Icc x₀ b`, matching the
  derivative interval.
* Butcher's preamble requires `R^N` to be an *inner product space*
  (he writes `⟨·, ·⟩`). The `[NormedAddCommGroup E] [InnerProductSpace
  ℝ E]` typeclass pair captures this exactly. **Do not** weaken to
  `NormedSpace ℝ E` — the proof uses inner product.

---

## C. `picard_lindelof_bound_strengthening` — concrete plan

This issue is correctly diagnosed in
`.prover-state/issues/picard_lindelof_bound_strengthening.md`. Two
points to tighten:

1. **Re-confirm Mathlib state.** Verify there is still no
   `IsPicardLindelof.of_global_lipschitz` wrapper:

   ```bash
   grep -rn 'globalLipschitz\|of_global_lipschitz\|IsPicardLindelof.of'\
     .lake/packages/mathlib/Mathlib/Analysis/ODE/
   ```

   In pinned Mathlib v4.28.0, this returns nothing. (Verified at
   consultancy time — only `IsPicardLindelof` itself and
   `exists_eq_forall_mem_Icc_hasDerivWithinAt₀` exist.)

2. **Concatenation strategy is the right move, but only when
   blocking downstream work.** The issue file already enumerates
   three options (concatenation in OpenMath, upstream PR, accept
   strengthening). The right call depends on whether `thm:112B`,
   `lem:319A`, or any §3 entity strictly *requires* existence on the
   full `[a, b]` rather than under the `M·(b-a) ≤ a_rad` regime.

   * `thm:112B` only references "two solutions exist"; the existence
     is a *hypothesis*, not a conclusion. So `thm:112B` does NOT
     inherit the strengthening. (This contradicts the issue file's
     "Affected downstream theorems" list — `thm:112B` is wrongly
     flagged. Update the issue.)
   * `lem:319A` (Chapter 3) is a different story; do not resolve
     until §3 is in scope.

3. **If/when you build concatenation,** the cleanest path is:

   * Define `IsPicardLindelofGlobal` (or extend `IsPicardLindelof`) as:
     "global Lipschitz on `[a, b] × E` and continuous in `t`".
   * Prove `exists_eq_forall_mem_Icc_hasDerivWithinAt₀_of_global` by
     induction on a finite cover `[a = a₀, a₁, ..., a_n = b]` chosen
     so that on each `[aᵢ, aᵢ₊₁]` we have `L·(aᵢ₊₁ - aᵢ) < 1` (so the
     bound `M(R) = M₀ + LR` solves to a finite ball).
   * Glue the local solutions via `HasDerivWithinAt`'s
     `union`-friendly behaviour: if `y` has a right-derivative on
     `[aᵢ, aᵢ₊₁)` and `y` has a left-derivative agreeing on the
     overlap, splice. Mathlib's `HasDerivWithinAt.union` (loogle for
     it) is the canonical splicer.
   * Use Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le`) for
     the a-priori bound `‖y(t)‖ ≤ ‖y₀‖ exp(L(t - a)) +
     M₀(exp(L(t-a)) - 1)/L`, which is what justifies the radius at
     each step.

4. **Estimated cost.** 2–3 cycles of focused infrastructure work.
   This is a real Mathlib gap; the wrapper would be PR-worthy
   upstream.

### Recommendation for cycle 010 disposition of this issue

Update the issue file:

* Remove `thm:112B` from the "Affected downstream theorems" list (it
  is a uniqueness/Grönwall theorem, not an existence statement).
* Mark §1 work as **not blocked** by this gap (only `lem:319A` and
  beyond are).
* Keep the issue open as a §3 prerequisite.

Defer the concatenation infrastructure until Chapter 3 enters the
plan. For cycles 010–012 (presumably `thm:112B`, then onward in §1),
this issue is non-blocking.

---

## D. `jordan_canonical_form_missing` — partial update

The issue file is **out of date**. Cycle 005 wrote it before cycle's
deliverable matured. Three corrections:

1. **The recommended option (c) is DONE.** The (ii) ⇒ (i) Gelfand
   route shipped at commit `0bd4a00` and is now packaged in
   `Section142.lean` as
   `OpenMath.Chapter1.Section142.minpoly_roots_lt_one_imp_convergent`
   and `convergent_iff_minpoly_roots_lt_one`. The two-way Iff
   `(i) ↔ (ii)` is now in the codebase.

2. **Remaining gaps for the full TFAE.** What is *still* blocked is
   *only* the reaching of (iii) and (iv), i.e. anything that requires
   recovering an explicit similarity transform. Specifically:

   * `(i) ⇒ (iv)` and `(ii) ⇒ (iv)` (need rescaled Schur or Jordan).
   * Any mention of (iii) at all.

3. **Schur is the right next move (option (b) of the issue), if and
   when §142 becomes blocking for downstream work.** As of cycle 009,
   §142 is not blocking anything in the current plan — `thm:142C`,
   `thm:142E`, `thm:142F` are unformalized but not on the immediate
   path to §11x or §12x.

### Schur sketch for a future cycle (if needed)

If/when Schur is needed, the constructive proof in Mathlib would go:

* Inductive scheme. For an `n × n` complex matrix `A`:
  - `n = 0`: trivial (empty matrix).
  - `n + 1`: pick a complex eigenvalue `λ` and unit eigenvector `v`
    via `Complex.isAlgClosed` + `Module.End.exists_hasEigenvalue` for
    finite-dimensional spaces over an algebraically closed field.
    Extend `{v}` to an orthonormal basis via
    `Mathlib.LinearAlgebra.OrthonormalBasis`'s
    `OrthonormalBasis.extend` (verify name with `lean_local_search`).
    In this basis, `A` has the block form
    `[ λ * ; 0 A' ]` where `A' : Matrix (Fin n) (Fin n) ℂ`. Apply IH
    to `A'`.
* Output: a unitary `U` and an upper-triangular `T` with
  `U⁻¹ * A * U = T` and the spectrum of `A` on the diagonal of `T`.
* Cost: 1 cycle for the basis+block-form mechanics, 1 cycle for the
  unitarity, 1 cycle for the spectrum-on-diagonal corollary.

### Bonus: rescaled Schur for `(iii) ⇒ (iv)`

Once Schur is in hand, the (iii) ⇒ (iv) step is a *diagonal* rescaling:
if `T` is upper triangular with diagonal in the open unit disc, pick
`D = diag(1, ε, ε², ..., εⁿ⁻¹)` for small `ε > 0`; then
`D⁻¹ T D` has the same diagonal but off-diagonal entries scaled by
`ε^{-(i-j)}` with `i < j`, which can be made arbitrarily small.
Combined with the diagonal bound, this gives `‖D⁻¹ T D‖_∞ < 1`.
This is a single-cycle infrastructure addition once Schur exists.

---

## E. Strategic recommendation

### Cycle 010 (next cycle): pick `thm:112B`.

Highest expected value:

* §B above gives a complete plan with verified Mathlib lemmas. Risk
  is low.
* No infrastructure gaps. The proof is genuinely 4–6 lemma-citation
  steps plus boilerplate.
* Aristotle is well-suited for steps 4 (Grönwall plumbing) and 6
  (square-root simplification) if hand-proof stalls.

### Cycle 011–012: extend the §11–§12 cluster.

Probable targets (verify against current `plan.md`):

* §11x: `thm:111B` if Butcher has one (check
  `extraction/formalization_data/entities/`).
* §12x: §122 / §123 are about Hamiltonians (`thm:123A`, `thm:123B`
  already done). Look at `thm:140A` (linear systems with constant
  coefficients), `thm:141A` (matrix exponential).

`thm:141A` (matrix exponential) is the natural §14 entry point and
unblocks much of §14. Mathlib has `NormedSpace.exp` /
`Matrix.exp` infrastructure (`Mathlib/Analysis/NormedSpace/MatrixExponential.lean`).

### Cycle 013+: revisit `picard_lindelof_bound_strengthening` only when §3 work begins.

### The Jordan/Schur path is on the back-burner until §142 is back on the critical path.

---

## F. Quick-reference table — Mathlib lemmas cited above

| Goal | Lemma | File |
|---|---|---|
| Scalar Grönwall (closed-form bound) | `le_gronwallBound_of_liminf_deriv_right_le` | `Mathlib/Analysis/ODE/Gronwall.lean` |
| Vector Grönwall (norm bound) | `norm_le_gronwallBound_of_norm_deriv_right_le` | same |
| Two-sided Lipschitz solution-difference bound | `dist_le_of_trajectories_ODE_of_mem` | same |
| Picard local existence | `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` | `Mathlib/Analysis/ODE/PicardLindelof.lean` |
| Inner product self = norm² (over ℝ) | `real_inner_self_eq_norm_sq` (or `_eq_norm_mul_norm`) | `Mathlib/Analysis/InnerProductSpace/Basic.lean` |
| Inner-product chain rule (HasDerivAt / HasDerivWithinAt) | `HasDerivAt.inner`, `HasDerivWithinAt.inner` | `Mathlib/Analysis/InnerProductSpace/Calculus.lean` |
| `√(exp t) = exp (t/2)` | `Real.sqrt_exp` (verify name with loogle) | `Mathlib/Analysis/SpecialFunctions/...` |
| `√(a²) = |a|` and `0 ≤ ‖_‖` | `Real.sqrt_sq_eq_abs`, `norm_nonneg` | std |
| Splicing `HasDerivWithinAt` across subintervals (for §C) | `HasDerivWithinAt.union` | `Mathlib/Analysis/Calculus/Deriv/Basic.lean` |

Names are best-effort accurate as of `Mathlib v4.28.0`. The worker
should verify each name with `lean_local_search` (or `lean_loogle` on
the type pattern) before relying on it.

---

## G. What NOT to do this cycle

* Do NOT re-do `thm:110C` or `thm:111A`. Both are committed and
  marked `formalized` in `lean_status.json`. The cycle-008 "empty
  diff" verdict was wrong.
* Do NOT raise `maxHeartbeats`. CLAUDE.md is explicit; decompose
  instead.
* Do NOT introduce `axiom` or `constant` for any of the gaps above.
  If the (iii) ⇒ (iv) Schur step is ever needed and Mathlib still
  lacks Schur, write a Schur lemma (option B-3 above), not an axiom.
* Do NOT spend cycle time chasing the phantom "commits not reaching
  repo" failure mode. It is a stale verdict in `attempts.md`. Verify
  with `git log -1 origin/Main/Experiments` and move on.
* Do NOT replace `def:112A`'s `OneSidedLipschitzInSecond` with a
  Mathlib equivalent — Mathlib does not have a one-sided Lipschitz
  predicate (verified by `lean_local_search "OneSided"`), so the
  current definition is correct and stable.
