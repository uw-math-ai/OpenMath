# Cycle 394 Results

## Worked on
Local truncation operator infrastructure for linear multistep methods
(Iserles §1.2 / eqn (2.6)). Added definition `LMM.truncationOp`, the
monomial identity that links it to `LMM.orderCondVal`, linearity
lemmas, and the two `HasOrder` corollaries (vanishing on order-`p`
monomials and leading coefficient at `t^(p+1)`).

All new declarations live at the bottom of
`OpenMath/MultistepMethods.lean` in a fresh `namespace LMM` block.

## Approach
Followed the cycle-394 strategy verbatim.

1. **Aristotle triage.** The only completed Aristotle bundle on hand
   (`07cc9e40-3e90-457f-b20f-878a0645369a`,
   `MultistepMethods.lean`, 2538 lines, `COMPLETE_WITH_ERRORS`) is a
   stub of an old slice of the live module: missing every BDF method
   (bdf2–bdf7), every Adams 3+ method, `LMM.errorConstant` and all
   error-constant theorems, the BDF7 zero-instability material, and
   the cycle-393 sign lemmas; it also re-imports `Mathlib` instead of
   `OpenMath.Basic` and rebuilds toy copies of helpers. Rejected
   wholesale per the strategy. Did **not** submit a new Aristotle
   batch this cycle (per strategy: scaffolding + mechanical sum/`ring`
   manipulation, the wrong surface for Aristotle).

2. **Sorry-first scaffold.** Wrote all six declarations
   (`truncationOp` def, `_add`, `_smul`, `_monomial_zero`,
   `_monomial_eq_zero_of_HasOrder`,
   `_monomial_leading_of_HasOrder`) with `sorry` and verified the
   file compiles.

3. **Closing order** (one pass per item):
   - `truncationOp_add`: `unfold truncationOp; simp only [mul_add,
     Finset.sum_add_distrib]; ring`.
   - `truncationOp_smul`: per-term `ring` lemmas to push `c` inside,
     then `simp only […, ← Finset.mul_sum]; ring`.
   - `truncationOp_monomial_zero`: case split on `q`. The `q = 0`
     case closes with `simp`. For `q = q' + 1`, expanded `(j*h)^k`
     via `mul_pow` and `pow_succ`, distributed both `Finset.mul_sum`
     occurrences over the RHS subtraction, used
     `← Finset.sum_sub_distrib` twice to merge into a single sum, and
     finished with `push_cast; ring`.
   - `truncationOp_monomial_eq_zero_of_HasOrder`: rewrite by
     `truncationOp_monomial_zero`, apply `hord.conditions_hold q hq`,
     then `mul_zero`.
   - `truncationOp_monomial_leading_of_HasOrder`: instantiate the
     monomial identity at `q = p + 1` (Nat subtraction `(p+1)-1 = p`
     handled by `simpa` to rewrite the derivative), unfold
     `errorConstant`, clear `(p+1).factorial` with `field_simp`. The
     `HasOrder` hypothesis is mathematically not needed here (the
     identity is universal), so it is recorded as `_hord` to keep
     the strategy-prescribed signature without triggering an unused-
     variable warning.

## Result
SUCCESS. `OpenMath/MultistepMethods.lean` compiles with `exit 0` and
no new warnings (only the pre-existing `simp`/unused-variable
warnings further up the file). All four target theorems plus the
two helper linearity lemmas are sorry-free. `plan.md` Chapter 1
§1.2 updated with one new bullet under "Error constants".

## Dead ends
- First attempt at `truncationOp_smul` used `Finset.mul_sum` plus a
  `congr 1; … ; ring` shape; this cluttered the proof. Replaced with
  a per-term `ring`-rewrite plus
  `simp only [hα, hβ, ← Finset.mul_sum]; ring` for a cleaner two-line
  body.
- First attempt at `truncationOp_monomial_zero` only invoked
  `Finset.mul_sum` three times; the second `← Finset.sum_sub_distrib`
  failed because the RHS still had `… - h^q' * h * ∑ … β j` (the
  inner `∑` had not been pulled in). Adding the fourth
  `Finset.mul_sum` made both subtractions sit at the sum level and
  let `← Finset.sum_sub_distrib` apply twice.
- Initial close of `truncationOp_monomial_leading_of_HasOrder` ended
  with `field_simp; ring`; `field_simp` closed the goal directly so
  the trailing `ring` produced "no goals to be solved" and was
  removed.

## Discovery
- `pow_succ h q' : h^(q'+1) = h^q' * h` combined with `simp only
  […, pow_succ]` is enough to let `ring` close monomial identities
  whose `h`-exponent is `q' + 1`; no manual `h * h^q' = h^(q'+1)`
  rewrite is needed once both sides are reduced to that form.
- The monomial identity `truncationOp_monomial_zero` works without
  any smoothness predicate because we pass the derivative
  `(q : ℝ) * t^(q-1)` in explicitly. Saves us from importing
  `HasDerivAt` / `Differentiable` infrastructure for this cycle.
- `(p+1).factorial > 0` (`Nat.factorial_pos`) gives the nonzero cast
  needed by `field_simp` directly, no positivity tactic required.

## Suggested next approach
The natural follow-up theorems live just on top of this cycle's
scaffolding:

1. **Smooth Taylor upgrade.** Connect `truncationOp` for a smooth
   `y : ℝ → ℝ` (with derivative supplied via `deriv` /
   `HasDerivAt`) to the local truncation error
   `C_{p+1} h^{p+1} y^{(p+1)}(t) + O(h^{p+2})` via Taylor's theorem
   with remainder. This requires Taylor expansion infrastructure
   (`Mathlib`'s `taylorWithinEval` /
   `Polynomial.iteratedDeriv` etc.) and would be the right cycle for
   one focused Aristotle batch on the residual `O(h^{p+2})` bound.
2. **Order ↔ truncation operator on monomials.** Prove the converse
   direction: if `m.truncationOp h (t ↦ t^q) (t ↦ q · t^(q-1)) 0 = 0`
   for all `q ≤ p` and is nonzero at `q = p+1`, then `m.HasOrder p`.
   This is essentially the order-conditions characterization in
   monomial form and is a direct consequence of
   `truncationOp_monomial_zero`.
3. **Convergence: Lax-style equivalence.** The local truncation
   operator is the right primitive to feed into convergence proofs
   for general LMMs — the Adams convergence path used in
   `DahlquistEquivalence.lean` could potentially be re-derived
   uniformly via `truncationOp` plus zero-stability. This is a
   bigger refactor and is not the next cycle's target.

The most concrete next step is (1) — picking a single LMM (e.g.
forward Euler) and proving the truncation-error bound for `C^2`
solutions, working inside `OpenMath/MultistepMethods.lean` or a new
`OpenMath/TruncationError.lean` module.

## Aristotle activity
- Verified bundle `07cc9e40-3e90-457f-b20f-878a0645369a` is a stub
  by spot-checking that `bdf2`, `LMM.errorConstant`, and the AB3+
  methods are missing from
  `.prover-state/aristotle_results/07cc9e40-3e90-457f-b20f-878a0645369a/MultistepMethods.lean`.
  Rejected; nothing transplanted.
- No new Aristotle batch submitted this cycle (per strategy).
