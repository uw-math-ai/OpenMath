import Mathlib

/-! Cycle 080 — Aristotle target 3/4 (RHS expansion).

Symmetric to `convProduct_assoc_lhs_eq`. Unfold the inner convolution
`(βγ) R = Σ_{Q ≤ R} β(R - Q) · γ(Q)`, then distribute by `α(S - R)`.

After this lemma lands, `convProduct α (convProduct β γ) S` expands to
a single double-bind sum, ready for the swap-of-summation step.
-/

variable {α : Type*} [DecidableEq α]

abbrev Forest : Type := Multiset α

/-- The convolution product (Butcher equation 383a). -/
noncomputable def convProduct (μ ν : Forest (α := α) → ℝ) (S : Forest (α := α)) : ℝ :=
  (S.powerset.map (fun R : Multiset α => μ (S - R) * ν R)).sum

theorem convProduct_assoc_rhs_eq (a b c : Forest (α := α) → ℝ) (S : Forest (α := α)) :
    convProduct a (convProduct b c) S
      = ((S.powerset).bind
          (fun R => R.powerset.map
            (fun Q => a (S - R) * b (R - Q) * c Q))).sum := by
  sorry
