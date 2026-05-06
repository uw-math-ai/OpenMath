# Cycle 146 Strategy — Strengthen `def:520E` / `def:520F` non-vacuity with r=2 negative witnesses (`padded2DEulerGLM_not_isAStable`, `padded2DEulerGLM_not_isLStable`)

## Context

Cycle 145 added `doublyCompanionMatrix_det_factorization_n_four`
(axiom-clean), bringing `thm:550A` concrete-`n` coverage to four data
points (n = 1, 2, 3, 4). The cycle 145 worker explicitly flagged n = 5
as **risky** (~250 LOC, possibly `maxHeartbeats`-blocking) with
*diminishing returns* in the absence of a closure-infrastructure plan
for general `n`. Their explicit suggestion was to **pivot** to a
smaller, surer non-vacuity strengthening.

The cleanest small win is to extend the r = 2 negative coverage of
`def:520E` (A-stability) and `def:520F` (L-stability) by lifting
cycle 137's r = 1 negative `explicitEulerGLM_not_isAStable` /
`explicitEulerGLM_not_isLStable` to the existing 2-D padded form
`padded2DEulerGLM` (already defined in `Section520.lean:1286`,
already used as the substantive r = 2 witness for `IsRKStable`,
`IsIRKStable`, and the closed-form `padded2DEulerGLM_stabilityMatrix`
at line 1322).

This mirrors the matrix:

| width  | A-stable +ve  | A-stable −ve  | L-stable +ve         | L-stable −ve         |
|--------|---------------|---------------|----------------------|----------------------|
| r = 1  | ✓ (cyc 088/135/142) | ✓ (cyc 136)   | ✓ (cyc 088/142)      | ✓ (cyc 137)          |
| r = 2  | ✓ (cyc 143)   | **CYCLE 146** | ✓ (cyc 143)          | **CYCLE 146**        |

Cycle 146 fills the two empty cells, giving symmetric four-corner
coverage at both r = 1 and r = 2.

## Priority 1 — Add `padded2DEulerGLM_not_isAStable` and `padded2DEulerGLM_not_isLStable` (axiom-clean, ~80 LOC)

**Target file**: `OpenMath/Chapter5/Section520.lean`.

**Insertion point**: insert immediately after
`padded2DEulerGLM_isRKStable` (around line 1369) and before the
"Theorem 520D" section header (around line 1371). Keep the two new
theorems together as a paired ✓/✗ pair.

### Step 1 — Closed-form `M(-3)` for `padded2DEulerGLM`

`padded2DEulerGLM_stabilityMatrix` (line 1322) gives
`M(z) = !![1 + z, 0; 0, 0]` for any `z`. Specialize at `z = -3`:
`M(-3) = !![-2, 0; 0, 0]`. Note this is a **2×2** matrix (not 1×1
collapsed), so the proof has to genuinely handle a 2×2 norm and a
2×2 power, not the 1×1 collapse used in cycle 136's
`explicitEulerGLM_not_isAStable`.

### Step 2 — Bound `‖M(-3)^k‖` from below

Two viable routes — **prefer Route A** (simpler):

**Route A: spectral radius lower bound.**
The matrix `M(-3) = !![-2, 0; 0, 0]` is diagonal (all off-diagonal
entries are zero). The spectrum of a diagonal matrix is the set of
its diagonal entries: `spectrum ℂ M(-3) = {-2, 0}`. So
`spectralRadius ℂ M(-3) = ‖-2‖₊ = 2`. By
`spectrum.pow_mem_pow`, `(-2)^k ∈ spectrum ℂ (M(-3)^k)`, so
`‖(-2)^k‖ ≤ ‖M(-3)^k‖` (use `Matrix.spectralRadius_le_nnnorm` or
`spectrum_norm_le` for a fixed eigenvalue → matrix norm bound).
Thus `2^k ≤ ‖M(-3)^k‖`, contradicting `‖M(-3)^k‖ ≤ C` for k large
via `pow_unbounded_of_one_lt`.

The relevant Mathlib bridge for Route A is in cycle 126's `Section520.lean`
(see `instabilityRegion_supseteq_outside_disc` proof, around the
`spectrum.pow_mem_pow` invocation). Re-use that pattern:
```
have h_eig : (-2 : ℂ) ∈ spectrum ℂ (padded2DEulerGLM.stabilityMatrix (-3)) := by
  rw [padded2DEulerGLM_stabilityMatrix]
  -- Use Matrix.spectrum_diagonal or a direct construction via mem_spectrum_iff_isRoot_charpoly
  ...
have h_eig_pow : ((-2 : ℂ))^k ∈ spectrum ℂ (padded2DEulerGLM.stabilityMatrix (-3))^k :=
  spectrum.pow_mem_pow _ h_eig _
have h_norm_lb : ‖((-2 : ℂ))^k‖ ≤ ‖(padded2DEulerGLM.stabilityMatrix (-3))^k‖ := by
  -- bridge: every spectrum element has norm ≤ matrix norm
  ...
```

**Route B (fallback if Route A's `spectrum_diagonal` bridge bogs down):
direct entry-wise computation.**
Compute `M(-3)^k` directly. Since `M(-3)` is diagonal,
`M(-3)^k = !![(-2)^k, 0; 0, 0]`. The matrix norm (under
`Section520.lean`'s default scope, which is L∞-operator norm — verify by
checking `Section510.lean`'s scope import) of `!![a, 0; 0, 0]` is `‖a‖`.
So `‖M(-3)^k‖ = 2^k`, and `pow_unbounded_of_one_lt 2 (by norm_num)`
gives the contradiction directly. This mirrors cycle 136's r=1
template more closely.

For Route B, use `Matrix.linfty_opNorm_diagonal` (search for it
under `Matrix.Norms.Operator` scope — see cycle 143's
`padded_2x2_eq_diagonal` + `Matrix.linfty_opNorm_diagonal` pattern at
`Section520.lean` near line 920).

### Step 3 — Pick `k` and conclude

Following cycle 136 (Section520.lean:482-486):
```
obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
have hCk := hC k
-- bridge to ‖M(-3)^k‖
linarith
```

### Step 4 — `padded2DEulerGLM_not_isLStable` is one-liner

```lean
theorem padded2DEulerGLM_not_isLStable :
    ¬ padded2DEulerGLM.IsLStable :=
  fun h => padded2DEulerGLM_not_isAStable h.1
```

This mirrors cycle 137's `explicitEulerGLM_not_isLStable` exactly.

### Faithfulness

* New theorems are *negative non-vacuity witnesses* for `def:520E`
  (A-stability) and `def:520F` (L-stability). They confirm both
  predicates remain meaningfully refutable at r = 2 (not just r = 1).
* No new definitions, no new structure fields. No risk of
  faithfulness divergence — the predicates are unchanged.
* Mathematical content: explicit Euler's stability region is the
  closed unit disc centred at -1, and `z = -3` lies outside it. The
  r = 2 padding does NOT change this boundary because the stability
  matrix is `!![1+z, 0; 0, 0]` with the (0, 0) entry carrying the
  full content. This is the textbook fact that "passively-decoupled
  zero channels do not improve A-stability".

## Priority 2 (BACKUP — only if Priority 1 closes in <30 min) — Submit Aristotle batch for `thm:550A` general-`n`

Cycle 141 cancelled the prior general-`n` Aristotle job at 6% after 24 h
as intractable. **Do NOT re-submit the same general-`n` formulation.**

Instead, batch-submit ~3 narrower Aristotle jobs targeting:

* `doublyCompanionMatrix_det_factorization_n_five` — concrete `n = 5`,
  same template as cycle 145 (`Matrix.det_succ_row_zero` + `det_fin_three`).
  This is the n=5 stepping stone the worker flagged as risky for direct
  manual attempt; Aristotle may handle it where direct attempt is
  marginal.
* A focused `Matrix.det_succ_row_zero`-induction sub-lemma: "if
  `det(I − zX_n) = α(z)·β(z) + O(z^{n+1})`, then
  `det(I − zX_{n+1}) = α(z)·β(z) + O(z^{n+2})`" — the inductive
  step. May be tractable as a focused proof if the cofactor
  expansion of an `(n+1)×(n+1)` doubly companion matrix can be
  matched against the `n×n` block.
* (Optional) A `polynomial-coefficient-density` formulation: prove the
  identity for symbolic `α, β : Fin n → ℂ[z]` then specialise — may
  exploit `Polynomial`'s definitional equality more aggressively
  than the `IsBigO` approach.

Submit at the start of cycle 146 if Priority 1 closes early. Sleep
30 min. Skip processing this cycle if Priority 1 takes the full cycle;
process results in cycle 147+. **Per CLAUDE.md, do NOT re-poll within
the cycle.**

## Priority 3 (HOUSEKEEPING) — Re-fold cycle 145 issue/plan updates

Cycle 145 closed without further updates to issue files; verify
`.prover-state/issues/thm_550A_general_n.md` already records the
n = 4 closure (cycle 144 update was the last entry). If the n = 4
closure is missing, append a "Status update (cycle 145)" section
mirroring the cycle 140 / 144 entries.

## What NOT to try this cycle

* **Do NOT attempt the n = 5 stepping stone for `thm:550A` directly.**
  The cycle 145 worker explicitly flagged ~250 LOC and possible
  `maxHeartbeats` blowup; cycle 146 should pivot to the negative-
  witness strengthening above. n = 5 may return as Priority 2 via
  Aristotle batch only.
* **Do NOT attempt the general-`n` proof of `thm:550A` directly.**
  Cycle 141 cancelled a 24h Aristotle attempt at 6%; cycle 142 did
  not retry; manual cofactor-expansion induction has not been
  scaffolded. Stay deferred per
  `.prover-state/issues/thm_550A_general_n.md`.
* **Do NOT open `def:530B` (Order relative to starting method) this
  cycle.** Encoding requires Taylor-expansion infrastructure to
  define the SM-vs-ES residual that does not yet exist in our
  codebase; a single-cycle attempt risks producing a vacuous or
  smuggled definition. Defer until a planned multi-cycle §530B/C
  cycle that includes the necessary Taylor framework.
* **Do NOT modify `IsAStable` or `IsLStable` predicate definitions.**
  The cycle 88/135/137/142 multi-witness coverage already saturates
  the four corners at r = 1; cycle 143 + cycle 146 saturate r = 2.
  Predicate stability is critical for the existing axiom-clean
  witness chain.
* **Do NOT change `padded2DEulerGLM`'s definition** (line 1286). It
  is consumed by `padded2DEulerGLM_isRKStable` (cycle 134) and
  `padded2DEulerGLM_isIRKStable` (cycle 133). Any change cascades.
* **Do NOT raise `maxHeartbeats`** above 200000. The new proofs are
  small (~80 LOC); maxHeartbeats should not even be a concern.
* **Do NOT inline-rewrite `padded2DEulerGLM_stabilityMatrix`** —
  reference the existing closed-form theorem at line 1322 via `rw`.
* **Do NOT introduce `axiom`/`constant`** declarations.
* **Do NOT modify `scripts/autonomous_loop.py`** (per CLAUDE.md +
  prior cycles). The tautology scanner false-positive issue
  (`tautology_scanner_false_positives.md`) remains the loop
  maintainer's responsibility, not the worker's. If a regex hit
  appears, apply the standard cosmetic rename (`h_<name>` → `h<name>`).

## Verification checklist (run before commit)

1. `lake env lean OpenMath/Chapter5/Section520.lean` — must compile
   clean, no errors, no warnings beyond the existing Mathlib lints.
2. `#print axioms OpenMath.Chapter5.Section520.padded2DEulerGLM_not_isAStable`
   should return `[propext, Classical.choice, Quot.sound]`.
3. `#print axioms OpenMath.Chapter5.Section520.padded2DEulerGLM_not_isLStable`
   should return the same set.
4. Sorry count remains at 0 across the entire `OpenMath/` tree:
   the `Grep` pattern `\bsorry\b|sorryAx` must return only docstring
   mentions.
5. `lake build OpenMath.Chapter5.Section520` must finish under 5 min
   on first run (cache may already cover dependencies).

## Plan-level updates after success

* `plan.md` Chapter 5 row for `def:520E`: append cycle-146 reference
  noting the r=2 negative witness `padded2DEulerGLM_not_isAStable`
  closes the four-corner coverage at r = 2.
* `plan.md` Chapter 5 row for `def:520F`: append cycle-146 reference
  noting `padded2DEulerGLM_not_isLStable` closes the four-corner
  coverage at r = 2.
* `lean_status.json` rows for `def:520E` and `def:520F`: bump
  `last_updated_cycle` to 146; status remains `formalized` (already
  was — these are non-vacuity strengthenings, not new entities).
* No new entries in `.prover-state/issues/` are expected.

## Estimated cycle effort

* Priority 1: ~60–90 min (paper algebra is trivial; Lean encoding
  ~80 LOC closely mirrors cycle 136 + cycle 143 patterns).
* Priority 2 (Aristotle batch): ~15 min to compose + submit, plus
  the unattended 30-min sleep window. Skip if Priority 1 dominates.
* Priority 3 (housekeeping): ~10 min if needed.

Total: well under one cycle's budget, with high confidence of axiom-
clean closure.
