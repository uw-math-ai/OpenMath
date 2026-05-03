import Mathlib

/-! Cycle 080 — Aristotle target 2/4 (LHS expansion).

Unfold the outer convolution and distribute the inner sum through
multiplication by `γ Q`. The `convProduct` is defined as
`Σ_{R ≤ S} α(S - R) · β(R)` over `S.powerset`.

After this lemma lands, `convProduct (convProduct α β) γ S` expands to
a single double-bind sum, ready for the swap-of-summation step.
-/

variable {α : Type*} [DecidableEq α]

abbrev Forest : Type := Multiset α

/-- The convolution product (Butcher equation 383a). -/
noncomputable def convProduct (μ ν : Forest (α := α) → ℝ) (S : Forest (α := α)) : ℝ :=
  (S.powerset.map (fun R : Multiset α => μ (S - R) * ν R)).sum

theorem convProduct_assoc_lhs_eq (a b c : Forest (α := α) → ℝ) (S : Forest (α := α)) :
    convProduct (convProduct a b) c S
      = ((S.powerset).bind
          (fun Q => (S - Q).powerset.map
            (fun T => a (S - Q - T) * b T * c Q))).sum := by
  sorry
