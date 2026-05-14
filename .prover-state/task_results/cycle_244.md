# Cycle 244 Results

## Worked on

`lem:319A` (Butcher §319 "Global truncation error (RK)"), Phase 1 — the two
intermediate inequalities of the textbook proof:

1. **D1** `RKTableau.stage_diff_recurrence` — stage-difference recurrence:
   `‖Yᵢ - Zᵢ‖ ≤ ‖y₀ - z₀‖ + h L ∑ⱼ |aᵢⱼ| ‖Yⱼ - Zⱼ‖`.
2. **D2** `RKTableau.output_diff_recurrence` — output-difference recurrence:
   `‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖ + h L ∑ᵢ |bᵢ| ‖Yᵢ - Zᵢ‖`.
3. **D3** `RKTableau.lem_319A_recurrences` — bundled existential wrapper against
   `IsRKOneStep` witnesses.
4. **D4** Non-vacuity witness on `paddedEuler` with `f := id`
   (Lipschitz with constant 1).

New file: `OpenMath/Chapter3/Section319.lean` (~270 LOC), aggregator update in
`OpenMath/Chapter3.lean`.

## Approach

Sorry-first structure was unnecessary; the planner's six-step recipe (subtract
stage equations → triangle inequality on the resulting norm → scalar-pull via
`norm_smul`+`abs_of_nonneg` → sum-triangle inequality `norm_sum_le` → pointwise
Lipschitz bound via the private helper `lipschitz_norm_bound_aux` (bridging
`hf_lip.dist_le_mul` through `dist_eq_norm` and `Real.coe_toNNReal`) →
factor `L` out of the bound sum via `Finset.mul_sum` + `Finset.sum_congr`)
threaded cleanly into a single direct proof per deliverable. Final assembly
via `calc` plus `linarith` for the constant-shift inequality at the last step.

The Lipschitz-norm helper was extracted as a private file-level lemma so D1
and D2 share it — Section404 has the analogous bridge inlined and consumed by
~6 sites, but we only have two consumers in Phase 1 so the inline trade-off
was negligible.

Faithfulness check ran cleanly: D1/D2 mirror the textbook's "we deduce that"
inequality and "substituting into" inequality verbatim; D3 packages the two
inputs the textbook proof would feed into the M-matrix inversion that
produces the `L^†` constant (Phase 2 work).

## Result

**SUCCESS** — file compiles, all three named theorems axiom-clean
(`[propext, Classical.choice, Quot.sound]`); D4 example also clean (it
specialises through D3).

Build time: ~3 seconds. No GPFS pathology.

Two errors caught on the first compile and fixed in a single revision:

1. **`add_le_add_left` direction**. `add_le_add_left h c` produced
   `a + c ≤ b + c` (not the `c + a ≤ c + b` form I needed). This matches
   the memory note `feedback_add_le_add_left_dispatch.md`. Replaced with
   `linarith` for both D1 and D2's final step. *(Memory was helpful here:
   I knew from the saved note to skip the dispatch puzzle and go straight
   to `linarith`.)*

2. **Namespace mismatch**. I initially put the theorems under
   `namespace OpenMath.Chapter3.Section319 ... theorem RKTableau.stage_diff_recurrence`,
   which declared `OpenMath.Chapter3.Section319.RKTableau.stage_diff_recurrence`
   — but `M.stage_diff_recurrence` (dot notation) resolves through the
   `RKTableau` type's actual namespace, which is `OpenMath.Chapter3.Section312`.
   Restructured to use a nested `namespace OpenMath.Chapter3.Section312.RKTableau`
   block for the three deliverables, with the file-local Section319 namespace
   re-entered only for the private helper and the D4 example. This matches the
   pattern in Section381 (lines 188-995, 997-1566 etc).

## Faithfulness check

### `RKTableau.stage_diff_recurrence` (D1)
- Entity ID: `lem:319A`, structural sub-claim (line 2 of `proof_text`):
  > `‖Yᵢ - Zᵢ‖ ≤ ‖y₀ - z₀‖ + h₀ L ∑ⱼ |aᵢⱼ| ‖Yⱼ - Zⱼ‖`.
- Lean statement captures: **same content** (uses `h` directly rather than
  the upper bound `h₀ ≥ h`; equivalent under `0 ≤ h ≤ h₀` since the bound
  is monotone in `h`. The textbook writes `h₀` because Phase 2 needs
  uniformity over `h ≤ h₀` for the M-matrix inversion; in Phase 1 the
  recurrence holds at the specific step size `h` and is what Phase 2 will
  bound uniformly).
- Tautology check: conclusion is an inequality involving the *output*
  `‖Yᵢ - Zᵢ‖`, not present in the hypotheses. ✓
- Identity check: proof is a 6-step calc chain (triangle inequality →
  scalar pull → sum triangle → pointwise Lipschitz → factor L → `linarith`),
  not `exact h`. ✓
- Hypothesis strength: `0 ≤ h`, `0 ≤ L`, `LipschitzWith L.toNNReal f`,
  and stage-equation hypotheses `hY_stage` / `hZ_stage`. All present in
  the textbook statement. ✓

### `RKTableau.output_diff_recurrence` (D2)
- Entity ID: `lem:319A`, structural sub-claim (line 3 of `proof_text`):
  > `‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖ + h L ∑ⱼ |bⱼ| ‖Yⱼ - Zⱼ‖`.
- Lean statement captures: **same content**.
- Tautology check: conclusion is `‖y₁ - z₁‖ ≤ ...`, not present in
  hypotheses. ✓
- Identity check: same 6-step calc chain as D1. ✓
- Hypothesis strength: same minimal set; `hY_out` / `hZ_out` are the
  textbook's output formulae for `y₁` and `z₁`. ✓

### `RKTableau.lem_319A_recurrences` (D3)
- Entity ID: `lem:319A`, packaging step of the proof.
- Lean statement captures: **weaker** than the headline textbook claim
  `‖y₁ - z₁‖ ≤ (1 + h L^†) ‖y₀ - z₀‖`. Ships the two intermediate
  inequalities (existential over the stage tuples extracted from
  `IsRKOneStep` witnesses); the headline closed-form is deferred to
  Phase 2.
- **Documented divergence**: the `L^† = L |b|^T (I - h₀ L |A|)^{-1} 𝟙`
  closed form requires inverting `(I - h₀ L |A|)` via M-matrix /
  Neumann-series machinery currently in `OpenMath/Chapter5/MMatrix.lean`
  (cycle 106's `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one`).
  Chapter 3 cannot import Chapter 5 without a circular dependency, so
  Phase 2 will either relocate `MMatrix.lean` to a chapter-neutral
  utility module or re-derive the needed Neumann inversion inline in
  Section319.
- Tautology check: conclusion is an existential over stage tuples, not
  in hypotheses. ✓
- Identity check: proof destructures `IsRKOneStep` witnesses and applies
  D1/D2 — real work, not re-export. ✓
- Hypothesis strength: same as D1/D2. ✓

### Helper `lipschitz_norm_bound_aux` (private)
- Bridges `LipschitzWith L.toNNReal f` to `‖f a - f b‖ ≤ L * ‖a - b‖`
  in a normed real-vector space. Pattern matches Section404 lines
  1216-1221 verbatim (modulo `Real.dist_eq` → `dist_eq_norm` for the
  generalisation to normed spaces). Not a new mathematical concept.

## Dead ends

- First attempt at the final `calc` step used `add_le_add_left h_h_inner _`.
  This is the `c + a ≤ c + b` form via the *Mathlib name* but the actual
  signature produces `a + c ≤ b + c` (per memory
  `feedback_add_le_add_left_dispatch.md`). Replaced with `linarith` —
  the bound is a single nonneg-preserved arithmetic shift and `linarith`
  closes it in one tactic.

- First file structure had the theorems under
  `namespace OpenMath.Chapter3.Section319` with names like
  `RKTableau.stage_diff_recurrence`. This declared
  `OpenMath.Chapter3.Section319.RKTableau.stage_diff_recurrence`, not
  `OpenMath.Chapter3.Section312.RKTableau.stage_diff_recurrence`. Dot
  notation `M.stage_diff_recurrence` (where `M : RKTableau s`) only
  resolves through the type's *defining* namespace, which is
  `OpenMath.Chapter3.Section312`. Fixed by wrapping the three theorems
  in a nested `namespace OpenMath.Chapter3.Section312.RKTableau` block
  matching the pattern Section381 uses for `IsRKOneStep`, `Equivalent`,
  etc.

## Discovery

- For a normed-space proof where `dist a b = ‖a - b‖`, the Lipschitz bridge
  is one rewrite shorter than the `Real.dist_eq` version Section404 uses:
  `rw [dist_eq_norm, dist_eq_norm]` works directly (no `abs` ↔ `norm`
  juggling needed because the codomain is `N` not `ℝ`).
- `add_le_add_left` keeps surprising me; saving the memory after cycle 064
  paid off here (avoided ~10 minutes of dispatch debugging on this cycle's
  final step).
- The `paddedEuler` non-vacuity carrier works cleanly with `f := id` —
  `LipschitzWith.id` plus the rewriting `(1 : ℝ).toNNReal = 1` via
  `Real.toNNReal_one` is the canonical bridge for the constant-1 Lipschitz
  case. Pattern worth keeping in mind for future Phase 1 ships that need
  a non-vacuity witness on an `LipschitzWith` hypothesis.

## Suggested next approach

**Cycle 245**: Phase 2 of `lem:319A` — derive the headline
`‖y₁ - z₁‖ ≤ (1 + h L^†) ‖y₀ - z₀‖` bound. Two options:

- **Option α (recommended)**: relocate `OpenMath/Chapter5/MMatrix.lean`
  to a chapter-neutral location (e.g. `OpenMath/Matrix/MMatrix.lean`).
  The file is a leaf utility (only depends on standard Mathlib `Matrix`
  + `Order` modules); cycle 106 is the only place that produces M-matrix
  inverses, and the only consumer right now is Chapter 5's stability
  analysis. Moving it removes the Chapter-3-imports-Chapter-5 obstruction
  for Section319 without re-deriving any maths.
- **Option β**: re-derive the needed
  `(I - h₀ L |A|)⁻¹` inversion inline in `Section319.lean` using the same
  `hasSum_geom_series_inverse` Neumann-series argument as cycle 106. About
  80 LOC, more code but isolates the inversion to where it's used.

Phase 2 then consumes D3 by:
1. Setting `M := h₀ L |A|` (entrywise-nonneg matrix with `‖M‖ < 1`
   guaranteed by `h₀ L ρ(|A|) < 1`).
2. Inverting `I - M` and reading off `L^† := L |b|^T (I - M)⁻¹ 𝟙`.
3. Substituting the stage-difference recurrence into itself via
   Picard-iteration / Neumann-series unrolling to bound
   `‖Yᵢ - Zᵢ‖ ≤ ((I - M)⁻¹ 𝟙)ᵢ ‖y₀ - z₀‖`.
4. Feeding into D2 to get the headline bound.

Estimated effort: 1 cycle if Option α is taken (the maths is already
present; only refactoring); 2 cycles if Option β is taken.

After `lem:319A` Phase 2 lands, `thm:319B` (Global truncation error
theorem) becomes the natural next target — it consumes `lem:319A` plus
the local error machinery from §301-§318, and is the headline §319
theorem the textbook proves via this lemma.
