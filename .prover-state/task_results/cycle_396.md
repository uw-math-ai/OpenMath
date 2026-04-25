# Cycle 396 Results

## Worked on
Polynomial-form packaging of `LMM.truncationOp` in
`OpenMath/MultistepMethods.lean`. All three planner targets closed:

- `LMM.truncationOp_finset_sum` (helper: linearity over a `Finset.sum`)
- `LMM.truncationOp_polyCombination_zero` (Target 1)
- `LMM.truncationOp_polyCombination_eq_zero_of_HasOrder` (Target 2)
- `LMM.truncationOp_polyDegSucc_eq_leading_of_HasOrder` (Target 3)

`plan.md` §1.2 truncation-operator bullet updated with a polynomial-form
sub-bullet tagged cycle 396.

## Approach
Followed the cycle-396 strategy. First added a small helper
`truncationOp_finset_sum` for finset-sum linearity (cleaner than
inducting via `truncationOp_add` directly), then derived the three
polynomial identities by direct rewriting:

- Target 1: applied the helper to `f k t = a k * t^k` and
  `f' k t = a k * ((k:ℝ) * t^(k-1))`, used `truncationOp_smul` to
  factor `a k` out of each term, then `truncationOp_monomial_zero`
  on each monomial. The derivative-side rewrite
  `a k * (k:ℝ) * t^(k-1) = a k * ((k:ℝ) * t^(k-1))` is required so
  `truncationOp_smul` matches; handled with a single `funext`/`ring`
  congruence step.
- Target 2: rewrite via Target 1, then each
  `m.orderCondVal (k : ℕ)` vanishes by `hord.conditions_hold` since
  `(k : ℕ) ≤ p` for `k : Fin (p + 1)`.
- Target 3: rewrite via Target 1 with `N = p + 1`, split the resulting
  sum at the top index using `Fin.sum_univ_castSucc`, the lower terms
  vanish by `hord.conditions_hold`, the top term unfolds via
  `errorConstant` and closes with `field_simp; ring`.

Used the required sorry-first workflow: wrote scaffolds, verified the
file compiled, then closed the `sorry`s in place.

## Result
SUCCESS. All three targets and the helper compile. Verified with:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH \
  lake env lean OpenMath/MultistepMethods.lean
```

Exits 0; output contains only pre-existing linter warnings elsewhere
in the file. No new `sorry`s, no `maxHeartbeats` increase.

## Dead ends
- First attempt at the finset-sum helper used a long sequence of
  `Finset.sum_comm` / `Finset.mul_sum` rewrites with explicit forward
  `Finset.mul_sum`. The simp normal form (after
  `simp only [truncationOp, Finset.mul_sum]`) had already pulled
  `h *` and `m.β j *` inside both nested sums, so a forward
  `Finset.mul_sum` on `h * ∑ ...` could no longer fire. Replaced with a
  single `Finset.sum_comm` (via `show ... from Finset.sum_comm`) on the
  β-side double sum, after which `← Finset.sum_sub_distrib` closed the
  goal directly — the trailing `Finset.sum_congr`/`ring` chain was
  unnecessary.

## Discovery
- The polynomial-form packaging only needs **finset-sum linearity** of
  `truncationOp`, not full induction over `N`. A single
  `truncationOp_finset_sum` helper subsumes the induction the planner
  suggested, and Targets 1–3 then reduce to simp+`ring` closures.
- The derivative-side rewrite shape
  `a k * (k:ℝ) * t^(k-1) = a k * ((k:ℝ) * t^(k-1))` is a pure
  associativity congruence (`Finset.sum_congr rfl + ring`); no
  parenthesization gymnastics needed beyond a single `funext`.
- After `simp only [truncationOp, Finset.mul_sum]`, both sides
  normalize to nested sums with `h *` and the structural coefficients
  fully distributed. Plan helper-lemma rewrites around that normal
  form, not around the surface syntax of the statement.

## Aristotle activity
No Aristotle batch was submitted this cycle. The three target proofs
closed immediately on first attempt after the finset-sum helper was
in place, and the helper itself was a one-screen calculation. There
was no isolated algebraic sub-goal that warranted a job, and the
strategy explicitly allowed proceeding manually if jobs were not
needed. (The strategy's optional Job 4/5 scratch helpers were
absorbed by the single `truncationOp_finset_sum` lemma.)

## Suggested next approach
Most natural follow-on (per planner): translation-invariance of
`truncationOp` in `t`, i.e. show that the value at general `t` agrees
with the `t = 0` value when the test pair is shifted, so the §1.2
polynomial formulas extend off the origin. The bigger separate cycle
remains the Taylor-with-remainder truncation-error formulation, which
the planner explicitly flagged as not for this cycle.
