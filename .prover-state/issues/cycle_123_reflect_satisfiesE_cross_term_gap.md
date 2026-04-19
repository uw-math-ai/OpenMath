# Issue: reflect_satisfiesE cross-term combinatorial gap

## Blocker
The final project-wide sorry in `OpenMath/ReflectedMethods.lean` is reduced to the local lemma
`h_A_term` inside `ButcherTableau.reflect_satisfiesE`, but that subgoal still requires a nontrivial
double alternating-binomial identity.

## Context
Current in-repo decomposition:

```lean
have h_A_term :
    ∑ i : Fin s, ∑ j : Fin s,
        t.b i * (1 - t.c i) ^ (k - 1) * t.A i j * (1 - t.c j) ^ (l - 1) =
      1 / ((k : ℝ) * (l : ℝ)) - 1 / ((l : ℝ) * ((k + l : ℕ) : ℝ)) := by
  sorry
```

The surrounding theorem already proves:
- reflected `B` as `hB_refl`
- binomial expansions for both reflected powers
- the algebraic split into the `b_j` product term and the `A_{ij}` cross term
- the `b_j` product term as `1 / (k l)`

So the only missing content is the reflected `A_{ij}` cross term.

## What was tried
- Checked old Aristotle results first; reflected `B/C/D` were already incorporated.
- Waited for and extracted Aristotle project `9cc99ed3-e6ac-4582-8edb-fe07c5a30a01`.
- That completed Aristotle proof succeeded only in a standalone scratch project over `ℚ`, not directly in the repo's `ℝ` file.
- Submitted five new focused Aristotle jobs after decomposing the in-repo theorem.
- Searched mathlib for existing reciprocal alternating-binomial identities; nothing obvious matched the remaining sum.

## Possible solutions
- Port the Aristotle scratch helper lemmas to `ℝ`:
  `gen_alt_binom_sum`
  `partial_alt_binom_sum`
- Use them to prove the double-sum identity obtained after expanding both `(1 - c)` powers and applying `hE`.
- If those lemmas are awkward over `ℝ`, prove them first over `ℚ` and cast to `ℝ`.
