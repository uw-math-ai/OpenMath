# Issue: Legendre polynomial bridge for Gaussian quadrature exactness

## Blocker
The remaining hard branch of `ButcherTableau.gaussLegendre_B_double` needs an inline polynomial representation and orthogonality statement for `shiftedLegendreP s`. The current file defines `shiftedLegendreP` recursively as a function `ℝ → ℝ`, while the clean reusable facts in Mathlib live on `Polynomial.shiftedLegendre`.

## Context
Current reduced goal shape inside `OpenMath/Legendre.lean`:

```lean
theorem gaussLegendre_B_double (t : ButcherTableau s)
    (hGL : t.HasGaussLegendreNodes)
    (hB : t.SatisfiesB s) :
    t.SatisfiesB (2 * s) := by
  unfold SatisfiesB at hB ⊢
  intro k hk1 hk2
  by_cases hks : k ≤ s
  · exact hB k hk1 hks
  · have hsk : s < k := by omega
    have hs_pos : 0 < s := by omega
    obtain ⟨j, hjlt, hk_eq⟩ : ∃ j, j < s ∧ k = s + (j + 1) := by
      refine ⟨k - s - 1, by omega, by omega⟩
    rw [hk_eq]
    sorry
```

Local Mathlib source inspection found:
- `Polynomial.shiftedLegendre`
- `Polynomial.coeff_shiftedLegendre`
- `Polynomial.degree_shiftedLegendre`
- `Polynomial.natDegree_shiftedLegendre`
- `Polynomial.shiftedLegendre_eval_symm`
- `Polynomial.factorial_mul_shiftedLegendre_eq`

## What was tried
- Looked for a ready-made orthogonality theorem or recurrence theorem for `Polynomial.shiftedLegendre`; nothing immediate turned up from local grep.
- Considered re-deriving coefficients directly from the recursive `shiftedLegendreP`, but that duplicates machinery now present in Mathlib.
- Submitted Aristotle jobs specifically targeting both `gaussLegendre_B_double` and the bridge from `shiftedLegendreP` to `Polynomial.shiftedLegendre`.
- Checked the two extracted Aristotle bundles from `d206f904-7ca0-487b-a04d-810746020839` and `de165c89-6ceb-4a51-a674-ee4da6c4264b`.
  The first left the main theorem open; the second solved a different theorem with a stronger custom definition of `HasGaussLegendreNodes`, so it was not directly incorporable.
- Found a more concrete orthogonality route: for fixed `j < s`,
  `choose (s + l) s / (l + j + 1)` is `1 / s!` times the degree-`s-1` polynomial
  `∏_{m ∈ {1, ..., s}, m ≠ j + 1} (l + m)`.
  This suggests proving
  `∑_{l=0}^s (-1)^l * choose s l * choose (s + l) s / (l + j + 1) = 0`
  via `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` instead of integrals.

## Possible solutions
- Prove:
  `∀ n x, shiftedLegendreP n x =
    Polynomial.eval x (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n))`
  and then obtain coefficients from `Polynomial.eval_eq_sum_range'`.
- If a recurrence theorem for `Polynomial.shiftedLegendre` exists elsewhere in Mathlib, use it to make the bridge proof a short induction.
- If not, derive the bridge from the explicit coefficient formula
  `Polynomial.coeff_shiftedLegendre`
  plus a closed-form proof that the recursive `shiftedLegendreP` satisfies the same coefficient expansion.
- Alternatively, avoid measure theory entirely and prove the coefficient orthogonality identity first using forward differences of the degree-`s-1` polynomial
  `Q_j(X) = ∏_{m ∈ range s, m ≠ j} (X + (m + 1))`.
  If that closes, the remaining work in `gaussLegendre_B_double` is the bridge from `hGL` to the defect-subtraction sum.
