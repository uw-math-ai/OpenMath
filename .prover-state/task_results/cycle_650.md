# Cycle 650 Results

## Worked on
§521 — extending the BDF GLM A-stability transport from a one-way
implication (cycle 649's `LMM.toGLM_isAStable_of_bdf`) to a full
biconditional, then exploiting it as planned: a new negative result for
BDF3 and concrete-method refactors that drop the file size by ~100 lines.

## Approach

### 1. `LMM.toGLM_isAStable_iff_of_bdf` (`OpenMath/LMMAsGLM.lean`, just
after `toGLM_isAStable_of_bdf`)

Forward direction is just `toGLM_isAStable_of_bdf`. Reverse direction
splits on `s = 0`:

* `s = 0` branch is **vacuous in the live `LMM.IsAStable` definition**.
  Concretely, for `s = 0`,
  `m.stabilityPoly ξ z = m.rhoC ξ - z * m.sigmaC ξ
                       = (m.α 0 : ℂ) - z * (m.β 0 : ℂ)
                       = 1 - z * (m.β 0 : ℂ)`
  (using `m.normalized : m.α (Fin.last 0) = 1`). The hypothesis
  `hξ : m.stabilityPoly ξ z = 0` plus `hβ_last z hz_re` give a direct
  contradiction; the `‖ξ‖ ≤ 1` goal never has to be discharged on its
  merits. So the trivial-witness path predicted in the strategy works:
  produce the contradiction and `exact absurd hξ`-style finish.
* `s ≠ 0` branch instantiates `[NeZero s]`, applies
  `toGLM_stabilityMatrix_eigenvalue_iff_of_bdf` (cycle 649) in the `←`
  direction with `Or.inr hξ`, and feeds the resulting charpoly root to
  `hG z hz_re ξ`.

### 2. `bdf3_toGLM_not_isAStable`

Closed via the iff bridge plus the existing `bdf3_not_aStable` (BDF3
fails the Dahlquist second barrier; `OpenMath/BDF.lean:199`). Discharging
the side hypotheses:

* `hbdf` for `bdf3` collapses to `fin_cases l <;> simp [bdf3, Fin.last]
  at hl ⊢` — the three early-`l` cases hit `bdf3.β 0 = 0` etc., and the
  last case is `Fin.last 3 ≠ Fin.last 3`, which `simp` closes from `hl`.
  No `decide` needed (and `decide` would not have worked here anyway —
  `bdf3.β` is `noncomputable`).
* `hβ_last` for `bdf3`: `bdf3.β (Fin.last 3) = 6/11`. Substitute and
  take real parts: `Re(1 - z * (6/11)) = 1 - z.re * (6/11) ≥ 1 > 0` on
  the closed left half-plane. `simp [Complex.sub_re, Complex.mul_re]`
  then `linarith` closes it.

This is the **first negative GLM A-stability result in the codebase**.

### 3. Refactors (~150 → ~20 lines apiece)

* `backwardEuler_toGLM_isAStable`: replaced the explicit
  `2 × 2` charpoly + eigenvalue-norm proof (~55 lines) with the iff
  bridge applied to `backwardEuler_aStable`. `β_last = 1`, denominator
  `1 - z`, same `Re ≥ 1 > 0` argument.
* `bdf2_toGLM_isAStable`: replaced the explicit `4 × 4`
  `Matrix.fromBlocks` det expansion (~120 lines including the
  `det_fromBlocks_zero₁₂` plumbing) with the iff bridge applied to
  `bdf2_aStable`. `β_last = 2/3`, denominator `1 - z * (2/3)`, again
  `Re ≥ 1 > 0`.

`trapezoidalRule_toGLM_isAStable` left untouched per the strategy
(trapezoidal `β = ![1/2, 1/2]` violates the BDF predicate).

## Result
SUCCESS — file compiles (`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH
lake env lean OpenMath/LMMAsGLM.lean`) with no errors and no warnings.
Full `lake build` is clean (only pre-existing simp-arg warnings in
`OpenMath/ButcherGroup/Section386Aug/DepthThree.lean` remain). No
`sorry`/`admit` in `OpenMath/LMMAsGLM.lean`.

## Final line count
`wc -l OpenMath/LMMAsGLM.lean` → **2700** (down from 2801; net −101
lines despite **adding** the bridge + the BDF3 negative result).

## Dead ends
* First draft of the `s = 0` branch tried `linear_combination -hξ`
  after a `simp` chain that also unfolded `Fin.sum_univ_one`. The simp
  reduced the stability-polynomial equation directly to the denominator
  shape `1 - z * (m.β 0 : ℂ) = 0`, leaving `linear_combination -hξ`
  facing a wrong factor-of-2 RHS (`2 - z * ↑(m.β 0) * 2 = 0`). Switching
  to a plain `exact this` — and dropping the redundant `Fin.sum_univ_one`
  the linter flagged — closed it cleanly.
* `simp [Complex.sub_re, Complex.mul_re]` was *unused* in the
  `backwardEuler` `hβ_last` branch (β_last = 1 → `z * 1 = z`, no `mul_re`
  needed). The bdf2 and bdf3 branches do need `Complex.mul_re` because
  `β_last` is a non-trivial fraction.

## Discovery
* `m.IsAStable` for `s = 0` is **genuinely vacuous** under the BDF
  denominator hypothesis: the stability polynomial collapses to
  `1 - z · β_last`, and `hβ_last` rules out exactly that vanishing on
  `z.re ≤ 0`. So the reverse-direction `s = 0` branch needs no extra
  argument beyond the contradiction; the trivial-witness path predicted
  in the strategy works.
* The iff bridge collapses *both* `backwardEuler_toGLM_isAStable` and
  `bdf2_toGLM_isAStable` to the same ~10-line shape (discharge `hbdf`
  by `fin_cases + simp`, discharge `hβ_last` by a real-part argument,
  apply the bridge `.mpr` to the existing scalar A-stability proof).
  Future BDF*-as-GLM A-stability transports should follow the same
  recipe verbatim.

## Suggested next approach

Backlog item §521 #7 (BDF case of the LMM-as-GLM A-stability bridge)
is essentially closed. The open follow-on is the **non-BDF** iff:
generalising `toGLM_stabilityMatrix_eigenvalue_iff_of_bdf` to allow
`m.β` non-zero in the past-step block. That requires a determinant
identity for companion-shift + rank-one updates that Mathlib does not
provide; tracked in
`.prover-state/issues/lmm_toGLM_general_charpoly_rank_one.md`.

Concrete cycle-651 candidates:

1. Open work on the general (non-BDF) charpoly bridge: try the
   matrix-determinant lemma path (`Matrix.det_one_add_mul_comm` or
   `Matrix.det_one_add_smul_outer_mul`) on the explicit rank-one
   update from cycle 641's
   `toGLM_stabilityMatrix_eq_V_active_plus_rank_one`. The point would
   be to reduce the past-`β` charpoly to a closed form over the
   companion-shifted base. If the rank-one path is too brittle, fall
   back to the existing `Matrix.fromBlocks` Schur-complement seam.
2. A parallel low-hanging fruit: BDF4/5/6 negative GLM A-stability
   results. `bdf4_not_aStable` is already in `OpenMath/BDF.lean:225`, so
   `bdf4_toGLM_not_isAStable` is a 10-line copy of the BDF3 proof above
   (with `(8/25)` for `β_last` instead of `(6/11)`). BDF5/6 would need
   prior `bdf5_not_aStable` / `bdf6_not_aStable` — cycle 650 confirms
   the iff bridge makes those one-shot once the LMM-side proof exists,
   so the bottleneck is the classical (non-GLM) A-stability proofs.

Either direction is a proper next deliverable; the planner can pick
whichever fits the current §38/§503/§521 emphasis.
