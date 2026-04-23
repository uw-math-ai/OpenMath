# Issue: `stabilityMatrix_quadForm_eq_neg_integral` now splits cleanly, but the top branch still has two local seams

## Blocker
After the cycle-368 split, the frontier theorem is reduced to the intended local tasks, but two seams remain:

1. `algStabMatrix_poly_bilinear_zero` still needs a clean finite-sum reindexing proof.
2. `stabilityMatrix_quadForm_eq_neg_integral_of_eq` now needs an explicit `s = 1` branch, because the naive degree-drop remainder lemma is false there.

## Context
- Live file: `OpenMath/CollocationAlgStability.lean`
- The file now contains:
  - a split main theorem
  - a proved low-degree branch
  - a proved corrected helper

```lean
private lemma sub_leading_term_natDegree_lt
    (hs : 1 < s) (q : ℝ[X]) (hqtop : q.natDegree = s - 1) :
    let r := q - Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1)
    r.natDegree < s - 1
```

- Remaining top-degree residual:

```lean
private lemma algStabMatrix_top_monomial_eq_neg_integral
```

## What was tried
- Added the planner-mandated sorry-first scaffold:
  - `algStabMatrix_poly_bilinear_zero`
  - `algStabMatrix_top_monomial_eq_neg_integral`
  - `stabilityMatrix_quadForm_eq_neg_integral_of_eq`
- Attempted to transplant the Aristotle proof from `dad34573...` for the bilinear helper.
  - The core idea is right: expand both polynomials into monomials and reduce to `algStabMatrix_monomial_bilinear_zero`.
  - The direct transplant became brittle due to four-way `Finset` reindexing and coefficient factoring.
- Proved instead the smaller corrected helper `sub_leading_term_natDegree_lt` with `1 < s`.
- Confirmed from Aristotle run `b851527f...` that the old `0 < s` statement is genuinely false at `s = 1`.

## Possible solutions
- For `algStabMatrix_poly_bilinear_zero`:
  - expand only one polynomial first,
  - factor one coefficient out at a time,
  - avoid a single giant `sum_bij` over four indices,
  - keep the summation range at `natDegree + 1` so the bound `m + n + 2 ≤ 2 * s - 1` comes directly from support indices plus `hpr`.
- For the top branch:
  - split on `1 < s` versus `s = 1`,
  - in the `1 < s` case use `sub_leading_term_natDegree_lt`,
  - in the `s = 1` case identify `q` as a constant polynomial and reduce directly to the pure top-monomial defect lemma.
- For the top-monomial defect:
  - set `p := nodePoly t * Polynomial.X ^ (s - 1)`,
  - write `p = Polynomial.X ^ (2 * s - 1) + lower`,
  - show `lower.natDegree < 2 * s - 1`,
  - use `quadEvalPoly_nodePoly_mul_eq_zero` on `p` and exactness on `lower`.
