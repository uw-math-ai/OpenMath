# Cycle 143 Results

## Worked on

**Priority 1 (PRIMARY) — completed.** r = 2 substantive L-stability
witness for `def:520F`, strengthening cycle 142's r = 1 case
`backwardEulerGLM_isLStable`. Added to
`OpenMath/Chapter5/Section520.lean`:

* `padded2DBackwardEulerGLM` — `(s, r) = (1, 2)` GLM. Padding pattern
  copied verbatim from cycle 133's `padded2DEulerGLM`; only the inner
  r = 1 block content differs (`A = U = B = V = !![1]` vs cycle
  133's `A = !![0]`).
* `padded2DBackwardEulerGLM_stabilityMatrix : z ≠ 1 → M(z) =
  !![1/(1-z), 0; 0, 0]` (closed form).
* `padded_2x2_eq_diagonal` (private) — `!![a, 0; 0, 0] = diagonal
  ![a, 0]`.
* `norm_padded_2x2_le` (private) — `‖!![a, 0; 0, 0]‖ ≤ ‖a‖` under
  `linftyOpNorm`.
* `padded2DBackwardEulerGLM_isAStable` — A-stability witness.
* `padded2DBackwardEulerGLM_isLStable` — L-stability witness.

All axiom-clean.

## Approach

Followed the planner strategy verbatim. The key simplification vs.
the strategy outline was avoiding an explicit closed form for the
matrix powers `M(z)^k`:

* **Step 0 (read precedents)**: located cycle 133's
  `padded2DEulerGLM` at `Section520.lean:1132` and copied the
  padding scheme. Only the r = 1 inner block changed (cycle
  142's backward-Euler `A = !![1]` instead of cycle 131's
  forward-Euler `A = !![0]`).
* **Step 1 (definition)**: `def padded2DBackwardEulerGLM :
  GeneralLinearMethod 1 2 where A := !![1]; U := !![1, 0];
  B := !![1; 0]; V := !![1, 0; 0, 0]`.
* **Step 2 (closed-form M(z))**: same template as cycle 142's
  `backwardEulerGLM_stabilityMatrix`: `Matrix.inv_subsingleton` on
  the 1 × 1 inner `(I − z·A) = !![1 − z]`, then `fin_cases i;
  fin_cases j` over the 2 × 2 entries; `field_simp` + `ring` closes
  the lone non-trivial `(0, 0)` case via `1 + z·(1−z)⁻¹ = (1−z)⁻¹`.
* **Step 3 (matrix-norm bound, NEW relative to strategy)**:
  instead of computing `M(z)^k` explicitly, used submultiplicativity
  `‖M^k‖ ≤ ‖M‖^k` (`norm_pow_le`, valid in any `NormOneClass`
  `SeminormedRing`). This dispenses with the explicit power induction
  the strategy suggested. Bound `‖M(z)‖`: rewrote `!![a, 0; 0, 0] =
  Matrix.diagonal ![a, 0]`, then `Matrix.linfty_opNorm_diagonal :
  ‖diagonal v‖ = ‖v‖`, then `pi_norm_le_iff_of_nonempty` to bound
  `‖![a, 0]‖ ≤ ‖a‖` componentwise. Combined: `‖M(z)‖ ≤ ‖1/(1−z)‖
  ≤ 1` on the closed left half-plane (cycle 142's
  `padeZeroOne_norm_le_one_of_re_nonpos`). Witness `C := 1` for
  `IsAStable`.
* **Step 4 (spectral-radius limit, also simplified)**: avoided the
  strategy's `spectralRadius_diag_2_with_zero` helper. Instead, used
  Mathlib's `spectrum.spectralRadius_le_nnnorm : ρ(M) ≤ ‖M‖₊`
  (valid in any `NormOneClass` Banach algebra), then transferred
  the upper bound `‖M(z)‖₊ ≤ ‖1/(1−z)‖₊` to `ENNReal` via
  `ENNReal.coe_le_coe`. Cycle 142's
  `norm_one_div_sub_tendsto_zero_cocompact` gives the cocompact
  limit on the upper bound; `ENNReal.tendsto_nhds_zero` does the
  squeeze.

## Result

**SUCCESS** — Cycle 143 closes Priority 1 axiom-clean.

* `lake env lean OpenMath/Chapter5/Section520.lean` clean.
* `lake build OpenMath.Chapter5.Section520` clean (50s, full
  Chapter 5 builds).
* `lean_verify padded2DBackwardEulerGLM_stabilityMatrix`:
  `[propext, Classical.choice, Quot.sound]` ✓
* `lean_verify padded2DBackwardEulerGLM_isAStable`:
  `[propext, Classical.choice, Quot.sound]` ✓
* `lean_verify padded2DBackwardEulerGLM_isLStable`:
  `[propext, Classical.choice, Quot.sound]` ✓
* No new `sorry` introduced.

## Faithfulness check

`padded2DBackwardEulerGLM` and the three new theorems are *named
instances* of `def:520F`'s non-vacuity, not new mathematical
concepts (matches the cycle 133/134 precedent):

* `padded2DBackwardEulerGLM : GeneralLinearMethod 1 2` —
  block-padded variant of `backwardEulerGLM`. Not a textbook
  concept; padding pattern identical to cycle 133's
  `padded2DEulerGLM` per planner instruction.
* `padded2DBackwardEulerGLM_stabilityMatrix` — closed-form
  computation, not a textbook claim.
* `padded2DBackwardEulerGLM_isAStable` — instance of
  `def:520E IsAStable`. The textbook predicate is unchanged;
  this just provides a new r = 2 witness.
* `padded2DBackwardEulerGLM_isLStable` — instance of
  `def:520F IsLStable`. Same situation: predicate unchanged,
  new substantive r = 2 witness.

No new `def`/`structure` of a named mathematical concept was
introduced this cycle, so the entity-JSON lookup is not required.
The hypothesis `z ≠ 1` on the closed-form theorem is mathematically
necessary (matches cycle 142's r = 1 stability matrix). No extra
hypotheses smuggled in.

Tautology / identity checks (per CLAUDE.md):
* No theorem conclusion appears verbatim as a hypothesis.
* No proof is a single `exact h` re-export — each does genuine
  matrix algebra / norm bounds.
* No structure `Prop` field is silently a derived consequence —
  no new structures or classes added.

## Dead ends

* **Tried `Matrix.norm_diagonal` first.** This is the *elementwise*
  norm in Mathlib; under our `Matrix.Norms.Operator` scope the
  correct lemma is `Matrix.linfty_opNorm_diagonal`. The error
  message was clear (`Did not find an occurrence of the pattern
  ‖diagonal ?v‖ in the target`). Fixed by switching name.
* **Tried `field_simp` alone for the closed-form (0, 0) entry.**
  Left a `1 - z + z = 1` residue. Added `ring` after `field_simp`;
  closed.
* **Tried `Fin.sup_univ_two`.** Doesn't exist in this Mathlib
  version. Switched to `pi_norm_le_iff_of_nonempty` for an
  inequality (which is all the downstream proofs need; equality
  was overkill). This also let me drop the `Fin.sup` machinery
  entirely.

## Discovery

* **Submultiplicative `norm_pow_le` + `linfty_opNorm_diagonal` is a
  cleaner template for "padded GLM A-stability" than explicit
  matrix-power induction.** The strategy outlined an explicit
  `(!![a, 0; 0, 0])^k = !![a^k, 0; 0, 0]` lemma (with `cases k`
  and `Matrix.mul_fin_two`), but `norm_pow_le` lifts the scalar
  norm bound directly to powers. This avoids ~20 LOC of fin-case
  pow induction and reduces the matrix-norm work to a single
  diagonal-norm + Pi-norm chain. **Future r = 2 witnesses with
  rank-1 padding should reuse this template.**
* **`spectrum.spectralRadius_le_nnnorm` + cycle 142's cocompact
  bridge is also a cleaner L-stability template than computing
  spectrum directly.** The strategy outlined a
  `spectralRadius_diag_2_with_zero : ρ(!![a, 0; 0, 0]) = ‖a‖₊`
  helper. Not needed: `spectralRadius ≤ ‖·‖₊` is a one-liner
  invocation of Mathlib, and an inequality is enough for the
  cocompact-zero limit (squeeze with the upper bound that goes
  to zero). Saves another ~30 LOC.
* **Matrix `Norms.Operator` scope conventions matter for naming.**
  Three families of norms coexist in `Mathlib.Analysis.Matrix.Normed`
  (elementwise, linftyOp, Frobenius) and use distinct lemma names
  (`norm_diagonal` vs. `linfty_opNorm_diagonal` vs.
  `frobenius_norm_diagonal`). Always check the active scope at the
  open-scoped declaration (`open scoped Matrix.Norms.Operator`
  in our case, line 66).
* **`pi_norm_le_iff_of_nonempty` is the bound-direction sibling of
  `Pi.norm_def`.** Easier than computing the sup explicitly when
  you only need an inequality.

## Suggested next approach for cycle 144

The next-cycle strategy file should consider one of:

1. **Backup A from cycle 143's strategy: `thm:550A` n = 3 stepping
   stone.** Cycles 138 (n = 1), 140 (n = 2) are closed; n = 3 via
   `Matrix.det_fin_three` and the leading-coefficient pattern
   `-(α_i · β_{n-i})` would give a third data point ahead of the
   eventual general-n proof. ~80 LOC, axiom-clean target.
2. **Backup B: r = 3 heterogeneous-stages witness for `def:530A`.**
   Cycle 141 added `mixedStartingMethod` (r = 2). An r = 3 variant
   with stages `(1, 1, 2)` or `(1, 2, 1)` would further strengthen
   non-vacuity. ~100 LOC.
3. **Negative L-stable r = 2 witness for `def:520F`.** Cycle 137
   added negative r = 1 `implicitMidpointGLM_not_isLStable`; an
   r = 2 negative would mirror this cycle's positive r = 2
   strengthening on the other side of the four-corner matrix.
   Likely uses cycle 135's `implicitMidpointGLM` padded analogously.
   ~120 LOC.

Do **not** attempt `thm:550A` general-n (cycle 141's Aristotle
job was cancelled at 6%; manual cofactor expansion is multi-cycle
work). Do **not** open `def:530B` / `def:530C` / `def:442A` per
cycle 142/143 strategy guidance — multi-cycle infrastructure.
