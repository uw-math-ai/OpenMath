# Cycle 670 Results

## Worked on
§521 Step C.5 — non-BDF entry on the path to
`D_mul_toGLM_charpoly_eq_X_pow_mul_active`. Two named theorems landed
in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`:

- `toGLM_stabilityMatrixPHF_zero_charpoly` (headline)
- `toGLM_V_active_charpoly_eq_X_pow_s_mul_PY` (stretch)

## Approach
Followed the planner's recipe verbatim. For the headline:

```lean
theorem toGLM_stabilityMatrixPHF_zero_charpoly (m : LMM s) :
    (toGLM_stabilityMatrixPHF m 0).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s := by
  rw [toGLM_stabilityMatrixPHF_charpoly m 0]
  simp
```

A single `simp` after the explicit form rewrite is enough — every
summand has the leading `z = 0` factor in `Polynomial.C (0 * … * …)`,
so `simp` collapses the sum to `0` and reduces `X^s - 0` to `X^s`.
The "fallback" `Finset.sum_eq_zero` ladder and the explicit
`hzero` hypothesis were not needed.

For the stretch:

```lean
theorem toGLM_V_active_charpoly_eq_X_pow_s_mul_PY (m : LMM s) :
    m.toGLM.Vℂ.charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s *
        (toGLM_stabilityMatrixPY m 0).charpoly := by
  rw [toGLM_V_active_charpoly, toGLM_stabilityMatrixPHF_zero_charpoly]
  ring
```

Three lines, exactly as the planner predicted.

## Result
SUCCESS — both lemmas compile sorry-free under
`lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean`. No
`maxHeartbeats` bumps, no helper detours, no Aristotle submissions.

## Dead ends
None. The 4-line recipe worked on the first attempt; the planner
correctly anticipated that `simp` would handle the `Polynomial.C 0`
collapse without manual `Finset.sum_eq_zero` handling.

## Discovery
- `simp` handles `Polynomial.C (0 * ... * ...) * X^l = 0` without any
  hand-rolled hypotheses or `zero_mul` simp set extension. The
  `Polynomial.X ^ s - 0 = X ^ s` cleanup lands in the same call.
- The non-BDF PHF block charpoly **at `z = 0`** is structurally
  identical to the BDF version of the same charpoly, even though the
  BDF version uses an upper-triangularity argument and the general
  version uses the companion-matrix `_eq_companion` rewrite. Two
  different proof paths, same value at `z = 0`.

## Suggested next approach
The full non-BDF
`D_mul_toGLM_charpoly_eq_X_pow_mul_active` is now blocked on
extracting the `X^s` factor from the rank-one correction term in
`toGLM_stabilityMatrix_charpoly_explicit`:

```
- C(1/D) * ( RowY * C(z β_last) + RowF * C(z) )
```

Both `RowY := toGLM_stabilityCharpolyRowY` and
`RowF := toGLM_stabilityCharpolyRowF` are dot products of the form
`vecMul (C ∘ rankOneRow) (PY(0).charmatrix.adjugate)` mapped against a
single column projection. The remaining arithmetic seam is:

1. Show that for the past-`y` adjugate-row entry
   `toGLM_stabilityCharpolyRowY` (a polynomial in `X`) the **product**
   `RowY · C(z · β_last)` is divisible by `X^s` *as a multiple of the
   PHF block*. Concretely: when paired with the rank-one column whose
   only non-zero entry is at the past-`y`-last index, the resulting
   contribution is a `RowY` value (one polynomial) times the resolvent
   prefactor.
2. Same for `RowF · C(z)` against the past-`h*f`-last column.

The natural formal step is **not** an `X^k`-divisibility lemma on
`RowY` / `RowF` alone, but rather a *rebracketing* of
`toGLM_stabilityMatrix_charpoly_explicit` whose right-hand side
already exposes `X^s` as a factor. Concretely, define

```
activeRankOneCorrection (m z : ℂ) : Polynomial ℂ :=
  Polynomial.C (1/D) *
    (toGLM_stabilityCharpolyRowY m * Polynomial.C (z β_last) +
     toGLM_stabilityCharpolyRowF m * Polynomial.C z)
```

and prove

```
activeRankOneCorrection m z = Polynomial.X ^ s * <something>
```

where `<something>` is a polynomial built from the *active* entries of
`toGLM_stabilityMatrixPY`. This decomposition mirrors the BDF case
where `(toGLM_stabilityMatrixPHF m 0).charpoly` itself was the `X^s`
factor.

A cycle 671 first deliverable could be:

- **Lemma**: `toGLM_stabilityCharpolyRowY` and
  `toGLM_stabilityCharpolyRowF` are themselves multiples of
  `(toGLM_stabilityMatrixPHF m 0).charpoly = X^s`. The reason is that
  the adjugate row from which they descend is computed against
  `(PY(0).charmatrix.adjugate)`, but the *embedding* into the
  full-block matrix carries the past-`h*f` block as a factor
  through the rank-one tensor structure (Step C.2 derivation,
  pre-projection).

That sub-step requires examining
`toGLM_stabilityMatrix_charpoly_rankOne_contraction_explicit` (the
"row block · -PYHF · column block" assembly): the bottom-row companion
adjugate is `(PHF(0).charmatrix).adjugate`, whose determinant identity
gives `C(charpoly) = adjugate * charmatrix`. The explicit `X^s` factor
falls out of the `(PHF(0).charmatrix).adjugate.det = X^(s-1) · …`
identity for companion matrices.

Recommendation: have the cycle 671 planner schedule **one** of:

(a) the rebracketed `activeRankOneCorrection` definition + the
    factorisation lemma above, in a *new sub-module*
    `OpenMath/LMMAsGLM/RankOneCorrection.lean`, since
    `LMMAsGLM/StabilityCharpoly.lean` is already at 503 lines with
    cycle 670's additions and the rank-one correction work will add
    significant infrastructure; **or**

(b) a more incremental first step: prove only the BDF→general bridge
    `toGLM_stabilityCharpolyRowF m * Polynomial.C z` vanishes
    *under BDF*, via the existing `_of_bdf` PHF nilpotency lemma,
    as a sanity check that the rebracketing works in the easy case.

Either path keeps the work in the sub-module and avoids growing
`OpenMath/LMMAsGLM.lean` past 3062 lines.
