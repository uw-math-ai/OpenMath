# Cycle 136 — Strategy

## Snapshot

- Branch tip: `8562b96 Cycle 135 — strengthen def:520E A-stability via substantive Padé(1,1) witness implicitMidpointGLM_isAStable (axiom-clean)`.
- Progress: 69 / 175.
- No sorries anywhere in `OpenMath/`.
- No pending Aristotle jobs.
- Cycle 135 just landed `implicitMidpointGLM_isAStable` (substantive Padé(1,1) witness), the closed-form `implicitMidpointGLM_stabilityMatrix`, the `padeOneOne_norm_le_one_of_re_nonpos` Möbius-transform bound, and three private `Fin 1` matrix-norm helpers. Axiom-clean.

## Aristotle results to incorporate

None. Skip the Aristotle-first step; proceed directly to manual proof.

## Target

**Add the *negative* A-stability witness `¬ explicitEulerGLM.IsAStable`** to
`OpenMath/Chapter5/Section520.lean`, alongside the existing positive
witnesses (`trivialZeroGLM_isAStable`, `implicitMidpointGLM_isAStable`).

Why this entity, this cycle:

- Cycle 135's task results explicitly list it as the cleanest follow-up
  ("Negative A-stability witness — Backup-A direction"), and the cycle
  135 strategy described it as out-of-scope for that cycle but ready
  to land next.
- After cycle 135, `def:520E`'s non-vacuity story has a *trivial*
  positive witness and a *substantive* positive witness. A negative
  witness is the missing leg: it proves `IsAStable` is non-vacuous in
  both directions — a real predicate, not satisfied by every GLM.
- The proof reuses cycle 088's `explicitEulerGLM_stabilityMatrix`
  (`M(z) = !![1+z]`, file line 123) verbatim. No new infrastructure
  needed.
- Single-cycle scope. Estimated ~80 LOC including the inevitable
  norm/`Fin 1`-power bookkeeping.
- Matches the cycles 133/134/135 cadence of one focused
  predicate-non-vacuity addition per cycle.

The new public theorem to land:

```lean
theorem explicitEulerGLM_not_isAStable :
    ¬ explicitEulerGLM.IsAStable
```

## Approach (specific)

Pick the witness `z := (-3 : ℂ)`. Then:

- `z.re = -3 ≤ 0`, so `IsAStable` would force `z ∈ stabilityRegion`,
  i.e. `∃ C, PowerBounded C (M(z))`.
- `M(z) = explicitEulerGLM.stabilityMatrix (-3) = !![1 + (-3)] = !![-2]`
  via the existing `explicitEulerGLM_stabilityMatrix` lemma.
- `M(z)^k = !![(-2)^k]` (matrix-power lifts to scalar via the
  cycle-135 private helper `fin_one_pow`).
- `‖M(z)^k‖ = ‖(-2 : ℂ)^k‖ = 2^k` via the cycle-135 helper
  `norm_pow_fin_one` plus `Complex.norm_neg` / `Complex.norm_ofNat`.
- For any candidate `C`, eventually `2^k > C` (Archimedean +
  `pow_unbounded_of_one_lt`), contradicting `‖M(z)^k‖ ≤ C ∀ k`.

### Step-by-step proof skeleton

```lean
theorem explicitEulerGLM_not_isAStable :
    ¬ explicitEulerGLM.IsAStable := by
  intro hStab
  -- Specialise A-stability at z = -3.
  have hz_re : ((-3 : ℂ)).re ≤ 0 := by
    rw [show ((-3 : ℂ)).re = -3 from by simp]; norm_num
  obtain ⟨C, hC⟩ := hStab (-3 : ℂ) hz_re
  -- Reduce ‖M(-3)^k‖ to 2^k.
  have hM : explicitEulerGLM.stabilityMatrix (-3 : ℂ) = !![(-2 : ℂ)] := by
    rw [explicitEulerGLM_stabilityMatrix]
    -- !![1 + (-3)] = !![-2]
    ext i j; fin_cases i; fin_cases j; simp; ring
  -- Simplify each iterate's norm to (2 : ℝ)^k.
  have hnorm : ∀ k, ‖(explicitEulerGLM.stabilityMatrix (-3 : ℂ))^k‖
                       = (2 : ℝ)^k := by
    intro k
    rw [hM, norm_pow_fin_one]
    rw [show ‖(-2 : ℂ)‖ = 2 from by
          rw [show (-2 : ℂ) = -(2 : ℂ) from by ring,
              norm_neg, Complex.norm_ofNat]]
  -- Pick k with 2^k > C.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, C < (2 : ℝ)^k := by
    -- Archimedean / `pow_unbounded_of_one_lt`
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, hk⟩
  -- Contradict the bound.
  have hCk := hC k
  rw [hnorm] at hCk
  linarith
```

The only fiddly bit is the `hM` step (`!![1 + (-3)] = !![-2]` as a
`Matrix (Fin 1) (Fin 1) ℂ`). If `ext i j; fin_cases i; fin_cases j;
simp; ring` does not close it, fall back to `Matrix.cons_val_zero` /
`Matrix.cons_val_fin_one` rewrites — see the `fin_cases` recipe in
`norm_fin_one` (line 423) for the exact incantation.

If `pow_unbounded_of_one_lt` has a different name in pinned Mathlib,
`lean_local_search "pow_unbounded"` and `lean_loogle "_ < _ ^ _"` are
both fast.

## Faithfulness check (run before commit)

- The theorem conclusion `¬ explicitEulerGLM.IsAStable` is a *negation*
  of a definition (no textbook entity `id`); no JSON statement to
  cross-check. The mathematical content matches the textbook fact
  that explicit Euler's stability region is the closed unit disc
  centred at `-1`, and `-3` lies *outside* that disc.
- Tautology check: conclusion is a negation of `IsAStable`; not a
  hypothesis.
- Identity check: proof does real work (norm calculation +
  Archimedean argument).
- Hypothesis-strength check: theorem takes no hypotheses.
- Absent-theorem check: no helper sorries.
- Update `lean_status.json` row for `def:520E` cycle reference to 136
  if you choose to track non-vacuity-strength alongside the existing
  `formalized` status. Otherwise no JSON change.
- Update `plan.md` Chapter 5 section to note the negative witness in
  the `def:520E` row.

## What NOT to try

- **Do NOT** attempt to use `Matrix.norm_le_iff` or
  `Matrix.linfty_opNorm_def` directly on `!![(-2)^k]`. The cycle-135
  helpers (`fin_one_pow`, `norm_fin_one`, `norm_pow_fin_one`) already
  encapsulate the bridge `‖!![a]^k‖ = ‖a‖^k`; reuse them instead of
  re-deriving.
- **Do NOT** unfold `IsAStable` past the first `intro hStab`. The
  predicate is `∀ z, z.re ≤ 0 → z ∈ M.stabilityRegion`, so applying
  `hStab (-3) hz_re` directly gives `∃ C, PowerBounded C ...`.
- **Do NOT** try to close `hM` (`!![1 + (-3)] = !![-2]`) with bare
  `decide` or `norm_num` — `ℂ` is not a decidable ring; need
  `ext + fin_cases + simp + ring` or equivalent.
- **Do NOT** weaken the witness from `z = -3` to `z = -2`. At `z = -2`,
  `M(z) = !![−1]`, with `‖M(z)^k‖ = 1` for all `k`, which IS
  power-bounded (with `C = 1`). The boundary `|1+z| = 1` corresponds
  exactly to the boundary of the stability region.
- **Do NOT** introduce `axiom`/`constant`. The proof is closed in
  Mathlib + cycle-135 helpers; no infrastructure gap.
- **Do NOT** raise `maxHeartbeats`. The proof is light.
- **Do NOT** spawn Aristotle for this — manual proof is faster than
  the 30-minute submit/sleep cycle for an ~80-LOC routine norm
  calculation.
- **Do NOT** edit `scripts/autonomous_loop.py`. (Standing rule.)

## Backup paths (if primary stalls within ~60 min)

### B1 — Padé(1,1) order-2 stability for implicit midpoint

Cycle 135's strategy noted this as a stretch goal. Show
`implicitMidpointGLM.HasStabilityOrder 2`. Requires computing
`Φ(exp z, z) = (1 - z/2) · (exp z - (1+z/2)/(1-z/2))` and showing it
is `O(z^3)` near `0`.

Mathlib hooks: `Complex.exp_sub_sum_range_isBigO_pow 3` or
equivalent Taylor-remainder lemmas; `Asymptotics.IsBigO`. The
`HasStabilityOrder` definition lives at
`OpenMath/Chapter5/Section520.lean:491`.

This is heavier (~150 LOC) and depends on holomorphic-function /
big-O machinery we have not used yet in §520. Prefer B2 below if
B1 looks stuck.

### B2 — Negative L-stability witness

Show `¬ explicitEulerGLM.IsLStable` (`def:520F`). This is *strictly
weaker* than the primary target's content: L-stability requires
A-stability, so a disproof of A-stability already gives the disproof
of L-stability as a one-liner (`fun h => explicitEulerGLM_not_isAStable h.1`).
Land this as a one-line corollary alongside the primary theorem if
time permits — it adds a second non-vacuity-strengthening data point
at near-zero cost.

### B3 — Pivot to a fresh entity

If both B1 and B2 prove unexpectedly difficult, pick one of these
Chapter 3 / Chapter 5 leaves (single-cycle scope each):

- `def:381F` *P-equivalent* (§380, Chapter 3): definition only;
  builds on `def:381E` (already partial). Cleanest entry point if
  bailing on §520.
- `def:530A` *non-degenerate* (§530, Chapter 5): definition only.
- `def:530B` / `def:530C` *Order relative to starting method*
  (§530, Chapter 5): definitions; would unblock §530-§534 work.

Don't pursue B3 unless primary AND B1/B2 both stall — stay focused
on the substantive single deliverable.

## Order of operations

1. (5 min) Read the cycle-135 helpers `fin_one_pow`, `norm_fin_one`,
   `norm_pow_fin_one` in `Section520.lean:411-440` to confirm signatures.
2. (10 min) Verify `explicitEulerGLM_stabilityMatrix` (line 123) and
   confirm `M(-3) = !![-2]` reduces cleanly with
   `ext + fin_cases + simp + ring`.
3. (15 min) Look up `pow_unbounded_of_one_lt` (or equivalent) via
   `lean_local_search`.
4. (40 min) Write the proof per the skeleton above. Sorry-first if
   any sub-step looks fiddly; verify with
   `lake env lean OpenMath/Chapter5/Section520.lean` after each
   reduction.
5. (5 min) Run `lake build OpenMath.Chapter5.Section520` then
   `#print axioms OpenMath.Chapter5.Section510.explicitEulerGLM_not_isAStable`
   to confirm `[propext, Classical.choice, Quot.sound]`.
6. (5 min) If B2 closes trivially, add `explicitEulerGLM_not_isLStable`
   as a one-liner.
7. (5 min) Update `plan.md` (§520 row note) and `lean_status.json`
   if appropriate.
8. (5 min) Write `cycle_136.md` task results, faithfulness section,
   commit + push.
9. **Do not poll Aristotle** — none submitted.
