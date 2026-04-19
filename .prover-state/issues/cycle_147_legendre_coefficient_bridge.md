# Issue: Coefficient bridge for `shiftedLegendreP`

## Blocker
`ButcherTableau.gaussLegendre_B_double` is not blocked on the algebraic defect-subtraction step anymore. It is blocked on one missing bridge:

1. turn the recursive function `shiftedLegendreP s` into an explicit degree-`s` polynomial expansion, or
2. prove an equivalent bridge to Mathlib's `Polynomial.shiftedLegendre`.

Without that bridge, the current hypothesis
`hGL : ∀ i : Fin s, shiftedLegendreP s (t.c i) = 0`
cannot be converted into the coefficient-level root identity needed by the harvested `B_extension_step` argument.

## Context
Current reduced goal shape in `OpenMath/Legendre.lean`:

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

Useful harvested fact from Aristotle project `de165c89-6ceb-4a51-a674-ee4da6c4264b`:
- the strong-induction / defect-subtraction proof of the high-degree branch is workable,
- but it expects hypotheses of the form
  `∃ a, a s ≠ 0 ∧ roots(a) at nodes ∧ orthogonality(a)`.

Useful Mathlib facts already confirmed:
- `Polynomial.shiftedLegendre`
- `Polynomial.coeff_shiftedLegendre`
- `Polynomial.natDegree_shiftedLegendre`
- `Polynomial.factorial_mul_shiftedLegendre_eq`
- `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`
- `fwdDiff_iter_eq_sum_shift`

## What was tried
- Harvested completed Aristotle bundles from:
  - `d206f904-7ca0-487b-a04d-810746020839`
  - `de165c89-6ceb-4a51-a674-ee4da6c4264b`
- Checked whether the harvested proof could be dropped in directly. It could not, because it strengthened `HasGaussLegendreNodes`.
- Re-searched Mathlib for a ready-made orthogonality theorem or a recurrence theorem for `Polynomial.shiftedLegendre`; none was found.
- Refined the orthogonality subgoal to a forward-difference identity:
  `∑_{l=0}^s (-1)^l * choose s l * choose (s + l) s / (l + j + 1) = 0`
  for `j < s`.

## Possible solutions
- Prove the explicit coefficient expansion directly by induction on the recursive definition:
  ```lean
  ∀ n x,
    shiftedLegendreP n x =
      ∑ l in Finset.range (n + 1),
        (((-1 : ℝ) ^ l) * (Nat.choose n l) * (((n + l).choose n : ℕ) : ℝ)) * x ^ l
  ```
- Or prove the cleaner bridge:
  ```lean
  ∀ n x,
    shiftedLegendreP n x =
      Polynomial.eval x (Polynomial.map (Int.castRingHom ℝ) (Polynomial.shiftedLegendre n))
  ```
- After that bridge:
  - use `Polynomial.coeff_shiftedLegendre` for the coefficients,
  - prove orthogonality by forward differences,
  - reuse the harvested algebraic `B_extension_step` proof to finish `gaussLegendre_B_double`.
