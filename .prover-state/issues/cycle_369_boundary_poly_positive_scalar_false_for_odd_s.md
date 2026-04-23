# Issue: `orthogonal_degree_eq_boundaryPoly` requires `0 < a`, but the live boundary polynomial has alternating leading sign

## Blocker
The current statement

```lean
∃ θ a : ℝ, 0 < a ∧ φ = Polynomial.C a * algStabilityBoundaryPoly s θ
```

is false for odd `s` under the live sign convention

```lean
algStabilityBoundaryPoly s θ =
  shiftedLegendrePoly s - Polynomial.C θ * shiftedLegendrePoly (s - 1)
```

because the degree-`s` term comes entirely from `shiftedLegendrePoly s`, and its leading coefficient
has sign `(-1)^s`.

## Context
- Live file: `OpenMath/CollocationAlgStability.lean`
- Current target theorem:

```lean
lemma orthogonal_degree_eq_boundaryPoly
    (hs : 0 < s) {φ : ℝ[X]}
    (hdeg : φ.natDegree = s) (hlc : 0 < φ.leadingCoeff)
    (horth : ∀ q : ℝ[X], q.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, (φ * q).eval x = 0) :
    ∃ θ a : ℝ, 0 < a ∧ φ = Polynomial.C a * algStabilityBoundaryPoly s θ := by
  sorry
```

- Mathlib source for shifted Legendre coefficients:
  `Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean`

```lean
theorem coeff_shiftedLegendre (n k : ℕ) :
    (shiftedLegendre n).coeff k =
      (-1) ^ k * n.choose k * (n + k).choose n
```

Taking `k = n`, the leading coefficient of `shiftedLegendrePoly n` is
`(-1)^n * Nat.choose (2 * n) n`, after casting to `ℝ`.

Since `shiftedLegendrePoly (s - 1)` has degree `s - 1`, it does not affect the leading term of
`algStabilityBoundaryPoly s θ`. Therefore:

```text
leadingCoeff (algStabilityBoundaryPoly s θ)
  = (-1)^s * Nat.choose (2 * s) s
```

so the leading sign alternates with the parity of `s`.

## What was tried
- Closed the three upstream frontier lemmas:
  - `algStabMatrix_poly_bilinear_zero`
  - `algStabMatrix_top_monomial_eq_neg_integral`
  - `stabilityMatrix_quadForm_eq_neg_integral_of_eq`
- Then performed the planner-required sanity check before attempting
  `orthogonal_degree_eq_boundaryPoly`.
- Cross-checked the planner warning from Aristotle bundle `b3b1362b...` against Mathlib’s
  coefficient formula for `shiftedLegendre`.

## Possible solutions
- Minimal statement repair:

```lean
∃ θ a : ℝ, a ≠ 0 ∧ φ = Polynomial.C a * algStabilityBoundaryPoly s θ
```

This matches the actual parity-dependent leading sign and is enough for the root-extraction step in
`thm_358A_only_if`.

- If later steps still want a positive scalar, normalize after the fact by absorbing a sign change
  into a parity-aware boundary-polynomial identity, rather than requiring positivity in the
  existential statement itself.

## Concrete counterexample
- Take `s = 1`, `φ = Polynomial.X`.
- Then `hdeg` and `hlc` hold, and the orthogonality premise is vacuous because `q.natDegree < 0`
  has no instances.
- But `algStabilityBoundaryPoly 1 θ` has degree-1 coefficient `-2`, so
  `Polynomial.C a * algStabilityBoundaryPoly 1 θ` has degree-1 coefficient `-2a`.
- Matching `φ = X` forces `a = -1 / 2`, contradicting `0 < a`.
