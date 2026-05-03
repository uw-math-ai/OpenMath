# §521 — what's left after H.3 + I.3 endpoints (cycle 732 sketch)

After cycle 732, we have at full generality (non-BDF):

- **H.3** `D_mul_toGLM_charpoly_eval_one_eq_stabilityPolyPoly`
  `D · charpoly.eval 1 = (stabilityPolyPoly z).eval 1`.
- **I.3** `D_mul_toGLM_charpoly_eval_zero_eq_zero`
  `D · charpoly.eval 0 = 0`.

These are the two endpoint identities of the §521 A-stability bridge.
Neither is sufficient on its own — A-stability requires the
characteristic-polynomial identity at **every** ξ on the unit circle,
not just ξ ∈ {0, 1}.

## The next concrete seam

Two candidate routes to extend H.3 / I.3 to all unit-ξ:

### Route A — generic-ξ closed form for `D · charpoly.eval ξ`

Mirror H/I ladders for arbitrary `ξ : ℂ`. The H.1 last-column adjugate
lemma already gives `(X^k).eval ξ = ξ^k` in the surviving j-branch, so
`rowFAlphaResidual_eval_closed_form` would expose

  `(rowFAlphaResidual m l).eval ξ
    = -((m.β (Fin.castSucc l) : ℝ) : ℂ)
        * ∑ k, ((m.α (Fin.castSucc k) : ℝ) : ℂ) * ξ ^ (k : ℕ)`.

Substituting into the analogue of G.1 at general ξ then mirrors H.3's
cancellation with the position-graded α-sum, replacing
`∑α(castSucc l)` by `∑ α(castSucc k) · ξ^k`. The output should match
`(stabilityPolyPoly z).eval ξ`. This is the most direct path; the
algebra is the H.3 cancellation parametrised by `ξ`.

### Route B — global polynomial factorisation

State `(toGLM.stabilityMatrix z).charpoly = X^? * (m.stabilityPolyPoly z)`
(or close to it) as a polynomial identity, then evaluate. This route
is cleaner conceptually but requires a divisor lemma in
`Polynomial ℂ`. The BDF-restricted version
`D_mul_toGLM_charpoly_eval_zero_collapsed_of_bdf` does this implicitly;
the general version would need the I.2 closed form lifted from `eval`
to `Polynomial`.

Route A is the lower-friction continuation since the H/I ladders are
already in place. Route B is the cleaner architectural ending and
should be the **end state**, but Route A is the better incremental
seam for cycle 733.

## Bind for the planner

The next strategy should target the H.1-style adjugate lemma
**at general ξ** (`(adj k j).eval ξ = ξ^k` when `j = ⟨s-1, _⟩`,
0 otherwise on that column), then build the corresponding
`rowFAlphaResidual_eval_closed_form` for arbitrary ξ.
