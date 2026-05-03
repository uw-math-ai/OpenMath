import Mathlib

/-! Cycle 080 — Aristotle target 4/4 (the main associativity).

Self-contained statement of `(αβ)γ = α(βγ)` with the LHS/RHS expansions
and the bijection lemma included as **hypotheses** (so Aristotle does
not need to re-derive them). Aristotle's job: combine the pieces.

The bijection lemma `double_powerset_swap` is provided as an axiom
parameter; the LHS/RHS expansions likewise. Aristotle should produce
a tactic chain that uses these to close the goal:

  funext S
  rw [convProduct_assoc_lhs_eq, convProduct_assoc_rhs_eq]
  -- LHS double sum:  Σ_{Q ≤ S} Σ_{T ≤ S-Q}  α (S - Q - T) * β T      * γ Q
  -- RHS double sum:  Σ_{R ≤ S} Σ_{Q ≤ R}    α (S - R)     * β (R - Q) * γ Q
  -- Apply bijection with f := fun Q T => α (S - Q - T) * β T * γ Q
  -- After swap, each term has α (S - Q - (R - Q)); use that
  -- `S - Q - (R - Q) = S - R` for `Q ≤ R ≤ S`.

Key facts: under `Q ≤ R`, `Q + (R - Q) = R`
(`Multiset.add_tsub_cancel_of_le` or `Multiset.sub_add_cancel`),
so `S - Q - (R - Q) = S - (Q + (R - Q)) = S - R` by
`Multiset.sub_add_eq_sub_sub` (`s - (t + u) = s - t - u`).
-/

variable {α : Type*} [DecidableEq α]

abbrev Forest : Type := Multiset α

/-- The convolution product (Butcher equation 383a). -/
noncomputable def convProduct (μ ν : Forest (α := α) → ℝ) (S : Forest (α := α)) : ℝ :=
  (S.powerset.map (fun R : Multiset α => μ (S - R) * ν R)).sum

/-- LHS expansion lemma — provided as hypothesis. -/
axiom convProduct_assoc_lhs_eq_ax
    (a b c : Forest (α := α) → ℝ) (S : Forest (α := α)) :
    convProduct (convProduct a b) c S
      = ((S.powerset).bind
          (fun Q => (S - Q).powerset.map
            (fun T => a (S - Q - T) * b T * c Q))).sum

/-- RHS expansion lemma — provided as hypothesis. -/
axiom convProduct_assoc_rhs_eq_ax
    (a b c : Forest (α := α) → ℝ) (S : Forest (α := α)) :
    convProduct a (convProduct b c) S
      = ((S.powerset).bind
          (fun R => R.powerset.map
            (fun Q => a (S - R) * b (R - Q) * c Q))).sum

/-- Key combinatorial bijection — provided as hypothesis. -/
axiom double_powerset_swap_ax
    (S : Multiset α)
    (f : Multiset α → Multiset α → ℝ) :
    ((S.powerset).bind
        (fun Q => (S - Q).powerset.map (fun T => f Q T))).sum
      = ((S.powerset).bind
          (fun R => R.powerset.map (fun Q => f Q (R - Q)))).sum

/-- Convolution product associativity (Butcher §383 Lemma 383B). -/
theorem convProduct_assoc (a b c : Forest (α := α) → ℝ) :
    convProduct (convProduct a b) c = convProduct a (convProduct b c) := by
  sorry
