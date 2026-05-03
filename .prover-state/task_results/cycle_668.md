# Cycle 668 Results

## Worked on

§521 Sub-step S1 — first concrete pieces of the
`D · charpoly = X^s · activeStabilityPolyPoly` headline:

1. New definition `LMM.activeStabilityPolyPoly`.
2. BDF sanity lemma identifying it with the classical scalar
   `LMM.stabilityPolyPoly`.
3. BDF specialisation of the S1 headline
   (`D_mul_toGLM_charpoly_eq_X_pow_mul_active_of_bdf`),
   verifying the target shape `D · charpoly = X^s · activeStabilityPolyPoly`
   in the BDF case where the rank-one contraction collapses cleanly.

All three landed sorry-free in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`. The file is now 481 lines
and `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` is green.

## Approach

1. Added at the end of `StabilityCharpoly.lean`, before `end LMM`:

   ```lean
   noncomputable def activeStabilityPolyPoly (m : LMM s) (z : ℂ) : Polynomial ℂ :=
     (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) •
       (toGLM_stabilityMatrixPY m z).charpoly
   ```

   exactly as the strategy spec'd it.

2. The BDF sanity lemma `activeStabilityPolyPoly_eq_stabilityPolyPoly_of_bdf`
   is a one-liner: by `unfold activeStabilityPolyPoly`, the goal is
   identical to the existing
   `toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf`
   (line 1633 of `OpenMath/LMMAsGLM.lean`). Discharged by `exact`.

3. The BDF version of the headline:

   ```lean
   theorem D_mul_toGLM_charpoly_eq_X_pow_mul_active_of_bdf
       (m : LMM s) (z : ℂ)
       (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
       Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
           (m.toGLM.stabilityMatrix z).charpoly =
         (Polynomial.X : Polynomial ℂ) ^ s * activeStabilityPolyPoly m z
   ```

   Proof recipe:
   - `rw [toGLM_stabilityMatrix_charpoly_of_bdf m z hbdf]` to rewrite
     `charpoly = PY.charpoly · X^s`.
   - `unfold activeStabilityPolyPoly` to expose `D • PY.charpoly`.
   - `rw [Polynomial.smul_eq_C_mul]` to convert `•` to `C ·`.
   - `ring` to commute the factors.

## Result

SUCCESS — three sorry-free lemmas land. `lake env lean
OpenMath/LMMAsGLM/StabilityCharpoly.lean` is clean.

The §521 iff bridge `LMM.toGLM_isAStable_iff` is now structurally
unblocked in the BDF case (where it was already provable via
`toGLM_isAStable_iff_of_bdf`); the new BDF-specialisation of the S1
headline restates that result in the active-stability-polynomial form
the iff bridge wants.

## Dead ends

- The non-BDF generalisation of S1 was not attempted: under the BDF
  hypothesis `toGLM_stabilityMatrix_charpoly_of_bdf` already gives
  `charpoly = PY.charpoly · X^s` directly (because the off-diagonal
  block `PYHF` vanishes), but in the non-BDF case the rank-one
  contraction in `toGLM_stabilityMatrix_charpoly_explicit` introduces
  extra terms that need a real `Polynomial.X^s`-divisibility argument.
  This is the next sub-step (see "Suggested next approach" below).
- The strategy mentioned that under BDF "RowY = 0, RowF = 0 — all
  already landed". A grep for those names returned no matches; those
  collapse lemmas appear not to be landed yet. They are not strictly
  needed for the BDF version of the headline because
  `toGLM_stabilityMatrix_charpoly_of_bdf` short-circuits the rank-one
  contraction path entirely.

## Discovery

- The BDF version of the S1 headline drops out in four lines because
  cycle 643 already proved `charpoly = PY.charpoly · X^s` under BDF
  via the block-triangular factorisation. The new active-stability
  packaging is just `D • PY.charpoly`, so the headline is
  `(C D) · PY.charpoly · X^s = X^s · (D • PY.charpoly)`, which is
  `Polynomial.smul_eq_C_mul + ring`.
- The general-`z` claim `D · charpoly = X^s · activeStabilityPolyPoly`
  is not obviously the right RHS shape for the non-BDF case. The
  contraction term in `toGLM_stabilityMatrix_charpoly_explicit` adds
  `RowY · C(z·β_last) + RowF · C z` (after multiplying through by
  `C D`), and `RowY = updatedDet · PHF.charpoly` has a `PHF.charpoly`
  factor — but `PHF.charpoly` itself is **not** divisible by `X^s` in
  the non-BDF case (only its leading term is `X^s`; the lower-degree
  terms `C(z·β_l/D) · X^l` survive). So the X^s factor in the general
  RHS, if it exists, must come from a more subtle cancellation between
  the `RowF` top-half (the rank-one updated PY-block adjugate path)
  and the `PHF.charpoly` correction terms. A small concrete check at
  s=1 (trapezoidal rule) confirms the divisibility holds there: the
  trapezoidal-toGLM stability matrix has `charpoly = X · (X − C ·)`
  by an existing landed lemma, so X¹ divides charpoly. So the
  conjecture is plausibly true in general, but the proof is not the
  one-line argument the BDF case admits.

## Suggested next approach

For the non-BDF S1 step, the cleanest decomposition is probably:

1. Prove a private lemma collapsing the `RowY · C(z·β_last)` term:

   ```
   RowY · C(z·β_last) = updatedDet · PHF.charpoly · C(z·β_last)
   ```

   (immediate from `toGLM_stabilityCharpolyRowY_eq_explicit`).

2. Prove a private divisibility lemma for the `RowF` top-half that
   exhibits the `Polynomial.X^k` factors carried by
   `PHF.charmatrix.adjugate`'s last row. This is the algebraic crux —
   the strategy's "trace this carefully" hint. Mathlib's
   `Matrix.adjugate_apply` plus an explicit row-by-row computation on
   the bottom-row companion shape may suffice; concretely the entry
   `PHF.charmatrix.adjugate ⟨s-1, _⟩ k` should equal `Polynomial.X^k`
   times a polynomial in the lower-order coefficients.

3. Combine to express `D · charpoly` as `X^s · (active charpoly +
   correction)`, then identify the correction with the natural
   non-BDF generalisation of `activeStabilityPolyPoly`.

Alternatively (recommended fallback): pivot to S2 (split
`OpenMath/LMMAsGLM.lean`, currently 3062 lines, into umbrella +
`Stability.lean` + `AStabilityTransports.lean`). The split is
mechanical, lands a real cleanup, and removes the file-size pressure
that's been outstanding for several cycles.
