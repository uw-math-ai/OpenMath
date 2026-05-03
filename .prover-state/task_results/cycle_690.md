# Cycle 690 Results

## Worked on

§521 Step C.12 — D-multiplied LMM-as-GLM charpoly identity (general
`s`-step LMM, no BDF hypothesis), plus the C.12b stretch (combined
residual degree bound) and the supporting `rowYQuot_degree_lt` helper.

Active file: `OpenMath/LMMAsGLM/StabilityCharpoly.lean`.

## Approach

Followed the strategy's recipe in spirit, but had to adjust the
headline statement:

1. **C.12a** — Multiplied the cycle 688 named charpoly identity
   (`toGLM_stabilityMatrix_charpoly_named`) by `Polynomial.C D`; the
   rank-one `Polynomial.C (1/D)` denominator cancels via
   `← Polynomial.C_mul`, `mul_one_div`, `div_self hz`,
   `Polynomial.C_1`. Closed with `linear_combination`.

2. **`rowYQuot_degree_lt`** — Modeled on cycle 686's
   `charmatrix_adjugate_natDegree_le`. `Matrix.det_apply` plus
   `Polynomial.natDegree_prod_le`; bound each per-permutation product
   by counting: the replaced row contributes natDegree 0 (constant
   `Polynomial.C`), the other `s − 1` rows contribute ≤ 1 each via
   `Matrix.charmatrix_apply_natDegree_le`. Filter cardinality argument
   gives total ≤ `s − 1`, hence degree `< s`.

3. **C.12b (`charpoly_residual_degree_lt`)** —
   `Polynomial.degree_add_le` plus `max_lt`, then bound each summand:
   - `rowYQuot · X^s · C(z β_last)`: `rowYQuot_degree_lt` (`< s`)
     plus `Polynomial.degree_X_pow` (= s) plus `Polynomial.degree_C_le`
     (≤ 0) → `< 2 s`.
   - `(rowFAlphaPoly + PY(0).charpoly · rowFBetaPoly) · C z`: cycle 688's
     `rowFNamedSum_degree_lt` (`< 2 s`) plus `Polynomial.degree_C_le`
     (≤ 0).

## Result

**SUCCESS** — three lemmas land sorry-free:

* `D_mul_toGLM_charpoly_eq_X_pow_mul_PY0_plus_residual` (Step C.12a)
* `rowYQuot_natDegree_le` + `rowYQuot_degree_lt` (helper)
* `charpoly_residual_degree_lt` (Step C.12b)

`OpenMath/LMMAsGLM/StabilityCharpoly.lean` clean (1418 lines, 0
sorries). Parent `OpenMath/LMMAsGLM.lean` clean. Commit pushed.

## Strategy adjustment — `activeStabilityPolyPoly` vs `PY(0).charpoly`

The strategy's stated theorem name was
`D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual` with
`activeStabilityPolyPoly m z` on the RHS. I had to deviate.

The reason is a real definitional mismatch:

* `activeStabilityPolyPoly m z := (1 - z β_last) • (toGLM_stabilityMatrixPY m z).charpoly`
  — uses `PY(z)`.
* The named consolidated charpoly identity (cycle 688) lands on
  `(toGLM_stabilityMatrixPY m 0).charpoly` — uses `PY(0)`.

These are **not equal** in general. `toGLM_stabilityMatrixPY m z` and
`toGLM_stabilityMatrixPY m 0` agree on the top `s − 1` rows but
disagree on the bottom row: at `j + 1 = s`,
`PY(z)[j, l] = (-α(castSucc l)) · (1 + z β_last / D) = -α(castSucc l) / D`
while `PY(0)[j, l] = -α(castSucc l)`. So `PY(z)` is `PY(0)` with the
last row scaled by `1/D`. Their `charpoly`s do not have a clean
relation modulo `Polynomial.C D`.

Concretely, after `rw [toGLM_stabilityMatrix_charpoly_named]` and
`unfold activeStabilityPolyPoly` and `rw [Polynomial.smul_eq_C_mul]`,
`ring` reduces to
`C(D) · PY(0).charpoly · X^s − C(D) · X^s · PY(z).charpoly = 0`, which
fails (concrete error attached during the cycle).

So I landed the natural theorem with `Polynomial.C D ·
(toGLM_stabilityMatrixPY m 0).charpoly` on the RHS instead of
`activeStabilityPolyPoly m z`. The proof is two lines: rewrite by the
named form, derive `C(D) · C(1/D) = 1`, close with `linear_combination`.

The bridge to `activeStabilityPolyPoly` is now a separate sub-step
that the planner should schedule. Two options:

1. **Redefine** `activeStabilityPolyPoly` to use `PY(0).charpoly`
   instead of `PY(z).charpoly`. The cycle 668 BDF specialisation
   would need a tweak (it currently uses `PY(z)` via `ring`-closure
   on `D • PY(z).charpoly`); under BDF, `PY(z) = E PY(0)` with
   `E = diag(1, …, 1, 1/D)`, so `D • PY(z).charpoly` and
   `D • PY(0).charpoly` are different polynomials — they coincide
   only after multiplication by another `D` factor.
2. **Keep both definitions** and prove an explicit residual identity
   `C D · PY(0).charpoly = activeStabilityPolyPoly m z + (PY(0)/PY(z)
   correction)`. This is non-trivial linear-algebra content.

Option 1 is cleaner for the next cycle; the BDF lemma would migrate
to the `PY(0)`-based definition and the `_via_general` derivation
would drop out of the new C.12a directly.

## Dead ends

The first attempt at C.12a tried the strategy's exact statement with
`activeStabilityPolyPoly` and `unfold ... ; rw [Polynomial.smul_eq_C_mul]
; ring`. `ring` failed with the residual goal
```
C(D) · PY(0).charpoly · X^s = C(D) · X^s · PY(z).charpoly
```
— exactly the `PY(0)` vs `PY(z)` mismatch above. Pivoted to the
`PY(0)`-stated headline.

## Discovery

* The named consolidated charpoly `toGLM_stabilityMatrix_charpoly_named`
  is *the* algebraic core: once it lands, the D-multiplied form is a
  three-line `linear_combination` that picks out
  `C(D) · C(1/D) = 1`. Cycles 678/680/682/684/688 paid for this
  cleanness.
* `rowYQuot_natDegree_le` is structurally a near-clone of cycle 686's
  `charmatrix_adjugate_natDegree_le`: the only difference is replacing
  `Pi.single i (1 : Polynomial ℂ)` with `Polynomial.C ∘ (-α ∘ castSucc)`,
  which still has natDegree 0 as a row.
* The `activeStabilityPolyPoly` definition appears to be load-bearing in
  the planner's roadmap (it bridges to `LMM.stabilityPolyPoly` under
  BDF). The `PY(z)` vs `PY(0)` discrepancy is a real architectural
  question that should be resolved before building on Step C.12a.

## Suggested next approach

**Cycle 691** — resolve the `activeStabilityPolyPoly` discrepancy.
Recommended path:

1. Redefine `activeStabilityPolyPoly m z` as
   `(1 - z β_last) • (toGLM_stabilityMatrixPY m 0).charpoly` (use
   `PY(0)`, not `PY(z)`).
2. Re-prove `D_mul_toGLM_charpoly_eq_X_pow_mul_active_of_bdf` from
   the new C.12a (one `rw` plus the BDF-vanishing of the residual via
   `toGLM_stabilityMatrixPYHF_eq_zero_of_bdf` on the `rowFAlphaPoly`
   side and `m.β (Fin.castSucc k) = 0` on the `rowFBetaPoly` side).
3. Re-prove `activeStabilityPolyPoly_eq_stabilityPolyPoly_of_bdf` using
   `PY(0)`'s closed-form companion charpoly (the cycle 643
   `toGLM_stabilityMatrixPYCompanion` machinery already covers the BDF
   case for `PY(z)`; the `PY(0)` version is even simpler since
   `PY(0)` *is* the bottom-row companion with bottom row `−α`).

If the planner prefers to keep `activeStabilityPolyPoly` on `PY(z)`,
then the right cycle 691 work is proving the `PY(z) → PY(0)` bridge
explicitly (multilinearity of `det` on the rescaled-bottom-row form)
— this is a 30–60 line linear-algebra proof.

After that, **cycle 692+** can attack the LMM iff bridge by combining
C.12a (D-multiplied identity) with C.12b (residual degree bound):
the iff bridge needs to compare the roots of `D · charpoly` with the
roots of `X^s · activeStabilityPolyPoly`, exploiting that the residual
has degree `< 2 s` and so cannot dominate the leading terms.

## Commit

`6a8a255370` — Cycle 690: §521 Step C.12a + C.12b D-multiplied
charpoly + residual degree bound. Pushed to `origin/main`.
