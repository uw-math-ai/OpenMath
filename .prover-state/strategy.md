# Cycle 135 strategy — substantive A-stability witness

## TL;DR

Strengthen `def:520E` (A-stability) non-vacuity by proving
`implicitMidpointGLM.IsAStable`. Mirrors the cycle 133/134 pattern of
replacing trivial witnesses (currently `trivialZeroGLM_isAStable` with
`M(z) = 0` for all `z`) with a substantive textbook example
(`implicitMidpointGLM`, the canonical Padé(1,1) A-stable method).

This is a 1-cycle deliverable. No Aristotle batch necessary on the
critical path; the proof is ~80–120 LOC of explicit complex arithmetic.
File issues if a sub-lemma proves harder than expected.

## Why this target

* **No Aristotle results pending; no sorries in the codebase.** Cycle 134
  closed cleanly. Per CLAUDE.md, a cycle with zero changes is unacceptable;
  the next move must be a substantive forward step.
* **Clean target.** `implicitMidpointGLM` is already defined
  (`OpenMath/Chapter5/Section510.lean:218`, `A = !![1/2]`, `U = B = V =
  !![1]`) and already has `IsPreconsistent`, `IsStable`, `IsConsistent`,
  `IsGSymplectic` non-vacuity witnesses (cycle 129). Adding the A-stability
  witness is the natural next strengthening.
* **Why not cycle 134's other suggestions:**
  - `thm:551B` (Single Non-Zero Eigenvalue Stability) — BLOCKED on
    `thm:550A`/`thm:550B` (doubly companion matrices), which depend on
    `cor:550C` and an unbuilt §550 infrastructure stack. Multi-cycle.
  - `def:381F` (P-equivalent) — BLOCKED on the deferred reduced-method
    construction (see `.prover-state/issues/reduced_method_deferred.md`).
  - `lem:351A` (Criteria for A-stability) — would need a freshly defined
    RK stability function `R(z) = 1 + zb^T(I-zA)^{-1}1` for `RKTableau`,
    which doesn't exist yet. 2-cycle effort minimum.
  - Negative witness `¬ explicitEulerGLM.IsAStable` — viable as a fallback
    (see Backup plan below) but the positive-witness pattern is what
    cycles 133/134 established and the supervisor scored +2 on; stick
    with it.
* **Stability function is the famous Padé(1,1):** `R(z) = (1+z/2)/(1-z/2)`.
  `|R(z)| ≤ 1 ↔ Re(z) ≤ 0` is the textbook Möbius-transform calculation.

## Primary plan

Add to `OpenMath/Chapter5/Section520.lean`, in the section between
`trivialZeroGLM_isLStable` (line ~323) and the §521A `HasStabilityOrder`
docstring (line ~325). Place all new theorems together so the
implicit-midpoint A-stability cluster is contiguous.

### Step 1 — closed-form stability matrix on the closed left half-plane

```lean
/-- Closed-form stability matrix of `implicitMidpointGLM` on the closed
left half-plane: `M(z) = !![(1 + z/2) / (1 - z/2)]`. The hypothesis
`hz : z.re ≤ 0` ensures `1 - z/2 ≠ 0` (its real part is `≥ 1`), so the
1×1 matrix `(I - z·A)` is invertible and the resolvent is the scalar
inverse `1/(1 - z/2)`. -/
theorem implicitMidpointGLM_stabilityMatrix
    (z : ℂ) (hz : z.re ≤ 0) :
    implicitMidpointGLM.stabilityMatrix z
      = !![(1 + z / 2) / (1 - z / 2)] := by
  sorry
```

Proof shape: imitate `explicitEulerGLM_stabilityMatrix`
(`Section520.lean:124-136`) and `padded2DEulerGLM_stabilityMatrix`
(line ~668, cycle 134). Key differences from explicit Euler:

1. `(1 - z • complexify M.A) = !![1 - z/2]` (NOT `!![1]`), so we cannot
   `rw [inv_one]` — instead invert via `Matrix.inv_def` /
   `Matrix.inv_fin_one` for 1×1 non-singular matrices.
2. Need `1 - z/2 ≠ 0` to invert. Derive it from `hz`:
   `(1 - z/2).re = 1 - z.re/2 ≥ 1` (since `z.re ≤ 0`), so `≥ 1 > 0`,
   hence `(1 - z/2) ≠ 0` via `Complex.ne_zero_of_re_pos` or `ne_of_apply_ne re`.

If `Matrix.inv_fin_one` doesn't exist by that name, use
`Matrix.det_fin_one`-based hand expansion or `Matrix.nonsing_inv_apply`.
Verify with `lean_local_search "Matrix.inv_fin_one"` first.

### Step 2 — Padé(1,1) magnitude bound

```lean
/-- For complex `z` in the closed left half-plane, the Padé(1,1)
magnitude is bounded by 1: `|(1+z/2)/(1-z/2)| ≤ 1` whenever
`Re(z) ≤ 0`. -/
theorem padeOneOne_norm_le_one_of_re_nonpos
    {z : ℂ} (hz : z.re ≤ 0) :
    ‖(1 + z / 2) / (1 - z / 2)‖ ≤ 1 := by
  sorry
```

Proof shape: convert to `normSq`, expand, simplify.

```
‖(1+z/2)/(1-z/2)‖ ≤ 1
  ↔ ‖1+z/2‖² ≤ ‖1-z/2‖²    (since 1-z/2 ≠ 0)
  ↔ Complex.normSq (1+z/2) ≤ Complex.normSq (1-z/2)
```

Then `Complex.normSq` expansion:
```
normSq (1+z/2) = (1 + z.re/2)² + (z.im/2)²
normSq (1-z/2) = (1 - z.re/2)² + (z.im/2)²
diff = (1+z.re/2)² - (1-z.re/2)² = 2 · z.re ≤ 0  (by hz)
```

Use `Complex.normSq_div`, `Complex.normSq_add`, `Complex.normSq_sub`, or
manually via `Complex.sq_abs` / `Complex.normSq_eq_abs`. Likely easiest:
`Complex.norm_div`, then `div_le_one_iff_le` with `‖1-z/2‖ > 0`,
square both sides via `Real.sqrt`, finish with `Complex.normSq_apply`
(or `Complex.normSq` definition) + `nlinarith` / `linarith` /
hand-expansion.

### Step 3 — main A-stability theorem

```lean
/-- **Substantive non-vacuity witness for `IsAStable`** —
`implicitMidpointGLM` is A-stable. This complements the trivial
`trivialZeroGLM_isAStable` (cycle 088, with `M(z) = 0` everywhere): the
implicit midpoint method is a *substantive* A-stable method whose
stability function `R(z) = (1+z/2)/(1-z/2)` is the canonical Padé(1,1)
approximant of `exp(z)`. Power-boundedness of the 1×1 stability matrix
follows from the magnitude bound `|R(z)| ≤ 1` on the closed left
half-plane. -/
theorem implicitMidpointGLM_isAStable :
    implicitMidpointGLM.IsAStable := by
  intro z hz
  -- z ∈ stabilityRegion: ∃ C, PowerBounded C (M(z))
  refine ⟨1, ?_⟩
  intro k
  rw [implicitMidpointGLM_stabilityMatrix z hz]
  -- Goal: ‖!![(1+z/2)/(1-z/2)] ^ k‖ ≤ 1
  sorry
```

Inner sorry plan: `!![a]^k = !![a^k]` (use induction on `k` with
`Matrix.pow_succ` + `mul_apply` simp on 1×1, OR hunt for an existing
`Matrix.pow_fin_one` / `Matrix.fin_one_pow`-flavored lemma; otherwise
write a private helper). Then
`‖!![a^k]‖ ≤ ‖a^k‖ = ‖a‖^k ≤ 1^k = 1` via `‖a‖ ≤ 1` from Step 2.

The matrix-norm-of-1×1 → scalar bridge in the `linftyOpNorm` scope:
search `Matrix.linfty_opNorm` first — for `r = 1`, the L∞-operator
norm is just the row sum which for a 1×1 matrix collapses to
`|a 0 0|`. Likely lemma: `Matrix.linfty_opNorm_fin_one` or
hand-proof via `Matrix.linfty_opNorm_def` + `Finset.sup_singleton`.

If the matrix-norm bridge proves fiddly, alternative tactic: expand
`!![a]^k = !![a^k]` explicitly via a helper (≤ 10 LOC), then bound
`‖!![a^k]‖` directly entry-wise. The cycle 134
`padded2DEulerGLM_stabilityMatrix` proof and the cycle 088
`trivialZeroGLM_isAStable` proof both manipulate 1×1 norms — read those
as templates.

## Backup plan — if Step 1 or Step 2 stalls past 90 minutes of effort

**Backup A (recommended fallback):** Pivot to the negative witness
`¬ explicitEulerGLM.IsAStable`. This is shorter (no inverse-of-non-trivial
matrix; explicit Euler has `R(z) = 1 + z`):

1. Show `(-3 : ℂ).re ≤ 0` (trivial) but `(-3 : ℂ) ∉ explicitEulerGLM.stabilityRegion`.
2. From `explicitEulerGLM_stabilityMatrix (-3) = !![1 + (-3)] = !![-2]`,
   show `‖!![-2]^k‖ = 2^k` via induction.
3. Use `tendsto_pow_atTop_atTop_of_one_lt` (with `1 < |-2|`) to derive
   `Tendsto (fun k => ‖M(-3)^k‖) atTop atTop`; then any constant `C`
   bound is contradicted at sufficiently large `k`.

If pivoting, document the pivot in `.prover-state/task_results/cycle_135.md`
under "Dead ends" with the specific blocker that triggered it.

**Backup B (only if both stall):** File an issue
`.prover-state/issues/oneByOne_matrix_pow_norm.md` documenting the
1×1-matrix-power-norm gap discovered, then commit Steps 1+2 (sorry-free
closed-form lemmas) without Step 3. This still satisfies the cycle bar
("decompose a sorry or write an issue") but loses the witness deliverable.

## What NOT to try

* **Do not** raise `maxHeartbeats` if Step 3 is slow — decompose the
  matrix-pow-norm reasoning into a private 1×1 helper.
* **Do not** introduce `axiom`/`constant` for the matrix-power-norm
  bridge. If the lemma `‖!![a]^k‖ = ‖a‖^k` (or `‖!![a^k]‖ = ‖a‖^k`)
  isn't in Mathlib, write it by hand as a private helper in the same
  file (≤ 15 LOC by induction).
* **Do not** attempt `thm:551B`, `def:381F`, or `lem:351A` — all are
  blocked per the "Why this target" section above.
* **Do not** generalize to "any A-stable Padé approximant" or build a
  generic `padeOneOne` infrastructure. Keep the proof concrete to the
  implicit midpoint witness.
* **Do not** poll Aristotle — there are no pending submissions, and
  this cycle's analytical content (complex magnitude calculation +
  matrix-pow-norm) is faster to prove manually than batch-submit.
* **Do not** modify `def:520E.IsAStable`'s definition or the
  `stabilityRegion`/`PowerBounded` infrastructure. The witness must
  satisfy the existing predicate as-is.

## Hygiene

* **Build verification:** `lake env lean OpenMath/Chapter5/Section520.lean`
  to verify the file compiles. Then `lake build OpenMath.Chapter5.Section520`
  before `#print axioms` (per CLAUDE.md note: `lake env lean` alone does
  NOT update the .olean cache, leading to stale-cache `sorryAx` false
  positives).
* **Axiom check:** `#print axioms
  OpenMath.Chapter5.Section510.implicitMidpointGLM_isAStable` should
  return `[propext, Classical.choice, Quot.sound]` (or just
  `[propext, Quot.sound, Classical.choice]` — order varies).
* **Faithfulness check:** `def:520E` is a *definition*, not a theorem;
  the new witness theorem `implicitMidpointGLM_isAStable` is a
  theorem about a previously-defined object. The pre-commit checklist
  applies:
  - Tautology: conclusion is `IsAStable`, not a hypothesis.
  - Identity check: proof is non-trivial — uses Padé magnitude bound.
  - Hypothesis strength: zero hypotheses on the new theorem.
* **Tautology scanner:** if the proof needs `have h_<name>` /
  `exact h_<name>` patterns, use the no-underscore convention
  (`hname` / `exact hname`) per the standing
  `tautology_scanner_false_positives.md` workaround.
* **lean_status.json:** the `def:520E` row should already exist
  (cycle 088 marked it formalized); update its `notes` to reference
  the new substantive witness, and bump cycle reference to 135. Plan.md
  row for `def:520E` should be updated to reflect the substantive
  (not just trivial) witness.

## Deliverable bar

Minimum: Steps 1 and 2 closed (sorry-free), with Step 3 as a sorry'd
scaffold + an issue file documenting the matrix-pow-norm gap.

Target: All three steps closed (sorry-free), axiom-clean, with
`implicitMidpointGLM_isAStable` axiom-clean.

Stretch: Also derive `implicitMidpointGLM.HasStabilityOrder p` for
some `p ≥ 2` (the Padé(1,1) is order 2 — but this is bonus, NOT in
scope this cycle).

## Cycle 134 cleanup

Cycle 134 task results suggested `padded2DEulerGLM_stabilityMatrix`
and `padded2DEulerGLM_stabilityFunction` as natural building blocks.
Those are already landed (cycles 130, 133, 134) and visible at
`Section520.lean:668-680` (approximately). They are NOT consumed by
this cycle's plan (different witness, different stability function),
but they confirm the recipe pattern (`Matrix.det_fin_two` /
`Matrix.det_fin_one` + `simp [Matrix.smul_apply]; ring`) that the
implicit-midpoint closed-form proof should mirror.

No housekeeping pending from cycle 134.
