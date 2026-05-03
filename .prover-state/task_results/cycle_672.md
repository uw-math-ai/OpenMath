# Cycle 672 Results

## Worked on

§521 Step C.5 BDF-branch headline. All four deliverables from the
strategy landed in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`:

1. `toGLM_stabilityCharpolyRowY_eq_X_pow_s_mul` — RowY as
   `updatedDet · X^s`, immediate two-`rw` from cycle 670 lemmas.
2. `rowYQuot` definition + `rowYQuot_mul_X_pow_eq_RowY` factorisation
   theorem.
3. `toGLM_stabilityCharpolyRowF_of_bdf` — RowF vanishes under BDF.
4. `toGLM_stabilityMatrix_charpoly_explicit_of_bdf` — clean BDF-branch
   `X^s · (PY.charpoly - resolvent · rowYQuot · zβ)` factorisation.

## Approach

* **Deliverable 1**: Two-line proof. `rw
  [toGLM_stabilityCharpolyRowY_eq_explicit m hs,
  toGLM_stabilityMatrixPHF_zero_charpoly]`. No `ring` needed.
* **Deliverable 2**: Followed the strategy template verbatim. The
  `s = 0` branch is dispatched by `dif_neg`.
* **Deliverable 3**: Both summands of
  `toGLM_stabilityCharpolyRowF_eq_explicit` collapse:
  - α-summand: `(toGLM_stabilityMatrixPYHF m 0).map C = 0` follows from
    the existing `toGLM_stabilityMatrixPYHF_eq_zero_of_bdf` (no PYHF
    helper needed in this file). Then
    `Matrix.mul_zero / Matrix.zero_mul / Matrix.vecMul_zero` collapse
    everything. Closed with a single `rfl` to align the
    `(0 : Fin s → Polynomial ℂ)` shape with the goal's pointwise zero.
  - β-summand: `funext` reduces the row to pointwise
    `Polynomial.C (m.β (Fin.castSucc k))`, which is zero under BDF.
    Then `Matrix.zero_vecMul` closes.
* **Deliverable 4**: Followed the strategy recipe exactly:
  `toGLM_stabilityMatrix_charpoly_explicit` → rewrite
  `(PHF m 0).charpoly` to `X^s` via
  `toGLM_stabilityMatrixPHF_zero_charpoly` → flip
  `rowYQuot_mul_X_pow_eq_RowY` to turn RowY into `rowYQuot · X^s` →
  apply `toGLM_stabilityCharpolyRowF_of_bdf` to zero out RowF → `ring`.
  No `show`/`rfl` bridge needed — the substitution targets matched
  cleanly.

## Result

SUCCESS — all four deliverables compiled, committed, and pushed in
four separate commits. File grew 498 → 609 lines (still well under
the 6000 hard cap).

## Dead ends

None this cycle. The strategy recipe was tight enough that each
deliverable closed on the first or second iteration.

## Discovery

* The `toGLM_stabilityMatrixPYHF_eq_zero_of_bdf` lemma (cycle 645) was
  exactly the right shape for the RowF-α summand collapse — no new
  helper needed.
* `Matrix.zero_vecMul` and `Matrix.vecMul_zero` plus a final `rfl`
  cleanly close pointwise-zero to function-extensional-zero gaps.
* The substitution path from the headline explicit form to the BDF
  factored form is a pure four-`rw` + `ring` proof — no `show` bridges.

## Suggested next approach

The next planning cycle should target the **general** (non-BDF) X^s
extraction from `toGLM_stabilityMatrix_charpoly_explicit`. The
remaining piece is the general factorisation of `RowF` as
`(something) · X^s` — i.e. the analogue of `rowYQuot_mul_X_pow_eq_RowY`
for the `toGLM_stabilityCharpolyRowF` side. This requires tracing the
companion-matrix adjugate `(PHF(0).charmatrix).adjugate` explicitly
(via `Matrix.adjugate_apply`) to expose the bottom-row `X^k`
divisibility, as the strategy file already noted.

Concrete sub-step: define a `rowFQuot` polynomial mirroring `rowYQuot`,
and prove `rowFQuot m * X^s = toGLM_stabilityCharpolyRowF m`. Once
that lands, the general `toGLM_stabilityMatrix_charpoly_explicit_of_X_pow`
factorisation follows by the same recipe as Deliverable 4 of this cycle,
just without the BDF zeroing.

A second, lower-priority follow-up: state the eventual §521 iff bridge
between the active stability polynomial and the `X^s`-quotient form,
once both Y- and F-quotients are exposed.
