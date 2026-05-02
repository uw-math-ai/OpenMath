# Cycle 648 Results

## Worked on

§521 polynomial-valued LMM stability polynomial in
`OpenMath/LMMAsGLM.lean`. Strategy's four deliverables:

1. `LMM.stabilityPolyPoly`
2. `LMM.stabilityPolyPoly_eval`
3. `LMM.stabilityPolyPoly_natDegree_le`
4. `LMM.toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf`

## Approach

All four landed manually in a single edit of `OpenMath/LMMAsGLM.lean`,
inserted immediately after cycle 647's
`toGLM_stabilityMatrixPY_charpoly_of_bdf` (line 1454). No Aristotle
submission was needed — the polynomial manipulation is straightforward
once the right `Polynomial` API is in hand.

Mathlib API used (verified by file-level grep against
`.lake/packages/mathlib`):
- `Polynomial.eval_finset_sum` — split eval over a sum.
- `Polynomial.eval_mul`, `Polynomial.eval_C`, `Polynomial.eval_pow`,
  `Polynomial.eval_X` — eval a `C r * X^k` term.
- `Polynomial.natDegree_sum_le` — bound `natDegree` of a sum by the max
  of the per-term `natDegree`s.
- `Polynomial.natDegree_C_mul_X_pow_le` — `natDegree (C r * X^k) ≤ k`.
- `Polynomial.smul_eq_C_mul` — `(c : ℂ) • p = Polynomial.C c * p`.
- `Polynomial.C_mul`, `Polynomial.C_neg` — homomorphism properties of
  `Polynomial.C`.
- `Finset.sum_sub_distrib`, `Finset.sum_neg_distrib`, `Finset.mul_sum`,
  `Finset.smul_sum` — standard finite-sum manipulations.
- `Fin.sum_univ_castSucc` — split a `Fin (s+1)` sum into the
  `castSucc` part plus the `last s` term.
- `Fin.val_castSucc`, `Fin.val_last` — cast lemmas needed because
  `Polynomial.X ^ ((Fin.castSucc l : Fin (s+1)) : ℕ)` and
  `Polynomial.X ^ (l : ℕ)` were not reducing without an explicit
  `simp only`.

## Result

SUCCESS, sorry-free. Final theorem statements:

```lean
noncomputable def stabilityPolyPoly (m : LMM s) (z : ℂ) : Polynomial ℂ :=
  ∑ j : Fin (s + 1),
    Polynomial.C (((m.α j : ℝ) : ℂ) - z * ((m.β j : ℝ) : ℂ)) *
      Polynomial.X ^ (j : ℕ)

theorem stabilityPolyPoly_eval (m : LMM s) (ξ z : ℂ) :
    (m.stabilityPolyPoly z).eval ξ = m.stabilityPoly ξ z

theorem stabilityPolyPoly_natDegree_le (m : LMM s) (z : ℂ) :
    (m.stabilityPolyPoly z).natDegree ≤ s

theorem toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) •
        (toGLM_stabilityMatrixPY m z).charpoly =
      m.stabilityPolyPoly z
```

`lake env lean OpenMath/LMMAsGLM.lean` exits 0 with no warnings.
`Grep` finds no `sorry` or `admit` in the file. File is now 2736
lines (was 2648), still well below the 3000 hard cap and only
slightly above the 2700 soft split threshold.

## Dead ends

The first attempt at the BDF bridge used a `simp_rw` over a per-`Fin s`
term-equality lemma and failed — the `Polynomial.X ^ (l : ℕ)` shape in
the lemma did not unify with the `Polynomial.X ^ ((Fin.castSucc l) : ℕ)`
shape produced by `Fin.sum_univ_castSucc`. Fix: insert
`simp only [Fin.val_castSucc, Fin.val_last]` *after*
`Fin.sum_univ_castSucc` to normalise the `Fin → ℕ` coercion before
applying the rewrite, then convert the term-equality lemma into a
single `Finset.sum_congr` rewrite.

The first attempt at the `c * (-α / c) = -α` cast inside `Polynomial.C`
failed with `field_simp` alone — `field_simp` left the
`((-x : ℝ) : ℂ) = -((x : ℝ) : ℂ)` cast unsolved. Fix: append
`push_cast; ring` after `field_simp`.

`Finset.sum_neg_distrib` direction note: the lemma is stated as
`∑ -f = -∑ f`, so the *forward* rewrite turns `∑ -f` into `-∑ f`.

## Discovery

The cleanest packaging of `c • charpoly = stabilityPolyPoly z` is
*both* sides expressed as
`C c * X^s + ∑ l : Fin s, C(α(castSucc l)) * X^l`. The BDF hypothesis
collapses two identifications simultaneously:
- `m.β (Fin.castSucc l) = 0` for every `l : Fin s` (kills the `z β`
  term in the lower coefficients);
- `m.α (Fin.last s) = 1` (the LMM `normalized` invariant — *not* part
  of the BDF predicate, but available unconditionally on `LMM s`),
  which makes the leading coefficient on the RHS exactly
  `1 - z β_last = c`.

So the `α(last s) = 1` normalisation that the strategy mentioned as a
possible *additional* hypothesis is automatic.

## Aristotle status

No submission this cycle. The strategy's "Aristotle policy" note said
to submit at most one scaffold and prefer deliverable 4, but the
manual proof closed in a single edit so a submission was not needed.
Recent cycles have reported HTTP 429 immediately on every submission.

## Suggested next approach

The four theorems landed are exactly the prerequisites named by the
plan's backlog item #7 for the eventual `LMM.toGLM_isAStable_iff`
headline. Two natural next steps:

1. **BDF root-condition bridge.** The pieces are now in place to prove
   that, under the BDF hypothesis,
   `m.toGLM.IsAStable ↔ ∀ z, z.re ≤ 0 → ∀ ξ, m.stabilityPoly ξ z = 0 →
   ‖ξ‖ ≤ 1` (i.e. the LMM A-stability condition implies and is implied
   by the GLM one). The bridge:
   - Cycle 647's `toGLM_stabilityMatrixPY_charpoly_of_bdf` plus
     this cycle's `toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf`
     identifies the roots of the GLM PY-block charpoly with the roots
     of `stabilityPolyPoly`.
   - This cycle's `stabilityPolyPoly_eval` identifies the roots of
     `stabilityPolyPoly` with the roots of `stabilityPoly`.
   - The block-triangular GLM stability decomposition (cycle 641
     `fromBlocks`) reduces the full GLM charpoly to the PY-block
     charpoly times an explicit factor with no spurious roots in the
     closed disk.
   The first deliverable for the next cycle should be the BDF
   instance: a clean
   `theorem LMM.toGLM_isAStable_of_bdf_aStable` that takes the
   classical LMM `IsAStable` (defined via `stabilityPoly`) plus the
   BDF hypothesis and produces the GLM `IsAStable`.

2. **General (non-BDF) rank-one-update determinant bridge.** The
   active blocker noted in
   `.prover-state/issues/lmm_toGLM_general_charpoly_rank_one.md` is
   the non-BDF case where the off-diagonal blocks of the cycle 641
   `fromBlocks` decomposition are non-zero. Independent of the BDF
   path, this would give the general bridge.

Path (1) is strictly easier and would close out the BDF specialisation
of the §521 A-stability bridge.
