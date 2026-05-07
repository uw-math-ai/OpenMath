# Cycle 180 Strategy

## Priority 0 (MANDATORY, FIRST ACTION) — Verify the supervisor's verdict against git state

**The supervisor has flagged cycles 176, 177, 178, AND 179 as "commit-not-reaching-repo" failures with score=−2. ALL FOUR VERDICTS ARE WRONG.** This is the same false-alarm pattern seen in cycles 8/14/15/35/73 (per `consultant_advice_cycle_009.md` §A and `consultant_advice_cycle_015.md` §B), but propagated through 4 consecutive cycles unfixed.

**Independent verification at the start of cycle 180** (run these commands and confirm the output):

```bash
git show --stat 0b171c9 -- OpenMath/Chapter4/Section441.lean   # cycle 176: +209 lines
git show --stat 1f0b21c -- OpenMath/Chapter4/Section441.lean   # cycle 177: +143 lines
git show --stat 80a5865 -- OpenMath/Chapter4/Section441.lean   # cycle 178: +62 lines
git show --stat 572f058 -- OpenMath/Chapter4/Section441.lean   # cycle 179: +32 lines
```

All four return non-empty diffstat — confirmed by the consultant in this strategy round. Cumulative: +446 lines to Section441.lean across cycles 176–179. Phase B of `lem:441A` IS COMPLETE. The file is at 932 LOC, sorry count 0, axiom-clean.

Confirm Phase B closure landmarks exist with:

```bash
grep -n "ρPoly_no_real_root_gt_one\|ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent\|ρPoly_pos_on_Ioi_one\|ρPoly_deriv_eval_one_pos_of_stable_preconsistent\|aPoly_coeff_one_pos_of_stable_preconsistent" OpenMath/Chapter4/Section441.lean
```

Expected: ≥ 5 hits (the five Phase B landmarks across cycles 175–179).

**Worker action items in priority order**:

1. Run the four `git show --stat` commands above and the `grep -n` command. Paste the (truncated) output into your task results under a header `## Phantom-verdict verification (cycle 180)`.
2. Append a "Cycle 180 confirmation" section to `.prover-state/attempts.md` recording the phantom pattern. Phrase it as: "Cycles 176–179 supervisor verdicts ('commit-not-reaching-repo') are false alarms. Verified by `git show --stat <sha>` on each cycle's commit; Section441.lean diffstat is non-empty in every case (+209/+143/+62/+32 lines respectively). Trust git state, not propagated `attempts.md` rows."
3. Create a fresh issue file at `.prover-state/issues/phantom_commit_verdict_pattern.md` summarising the cycle 176–179 pattern, cross-referencing the cycle-9 / cycle-14 / cycle-15 consultant advice files, and recommending that the loop-maintainer audit the supervisor's prompt-builder and diff-detection logic. This is loop-maintainer territory — do NOT attempt to fix it from the worker side. The issue file is the deliverable.
4. Do NOT modify `scripts/autonomous_loop.py` — that is loop-maintainer territory. The standing meta-issue `tautology_scanner_false_positives.md` already covers the supervisor-side prompt-builder bug; the new `phantom_commit_verdict_pattern.md` issue file is a separate but related diagnosis.

## Priority 1 — Phase C scoping issue file

Phase B (`a₁ > 0` half of `lem:441A`) is closed. Phase C (`aᵢ ≥ 0` for `i = 2, …, k`) is multi-cycle complex-root infrastructure work and CANNOT be attempted as a single-cycle deliverable. Before any Phase C proof attempt, write a comprehensive scoping issue file at `.prover-state/issues/lem_441A_phase_C_scoping.md`.

The file must contain:

### Section 1: Textbook argument (Butcher §441 p. 376)

Quote the relevant paragraph from `extraction/raw_text/ch04.txt` (locate via the `lem:441A` proof — the paragraph immediately following the `a₁ > 0` argument). Summarise:

- Möbius transformation `ψ(ζ) := (1 − ζ) / (1 + ζ)` is a bijection between the closed unit disk minus `{−1}` and the closed left half-plane.
- Algebraic identity: `aPoly(z)` and `α(ψ(z))` (or `ρ(ψ(z))`) are related by a `(1 + z)^k` scaling, so roots of `aPoly` correspond to roots of `α` (or `ρ`) under the Möbius bridge.
- Stability: roots of `α(z) = ∑ᵢ αᵢ z^i` lie in the closed unit disk (with simple roots on the boundary). Equivalently roots of `ρ` lie in the closed unit disk.
- Therefore: complex roots `ζ` of `aPoly` satisfy `Re(ζ) ≤ 0`.
- Real factorisation over `ℝ`: `aPoly` factors into a product of (a) real linear factors `z − ξ` with `ξ ≤ 0` (so `−ξ ≥ 0`) and (b) conjugate-pair quadratic factors `z² − 2(Re ζ)·z + |ζ|²` with non-negative coefficients (since `−2(Re ζ) ≥ 0` and `|ζ|² ≥ 0`).
- A polynomial that is a product of polynomials with non-negative coefficients itself has non-negative coefficients (induction on factor count, expanding the product).
- Combine: `aᵢ ≥ 0` for `i ≥ 2`.

### Section 2: Mathlib hooks needed

For each step, name the candidate Mathlib lemma. Verify availability with `lean_local_search` or `lean_loogle` BEFORE asserting it exists:

- `Polynomial.roots` over `ℂ` (multiset of roots with multiplicity).
- `Polynomial.aroots`, `Polynomial.IsRoot`, `Polynomial.eval₂` for the Möbius image.
- `Polynomial.Splits` over `ℂ` (algebraically closed).
- `Polynomial.prod_multiset_X_sub_C_dvd`, `Polynomial.prod_multiset_X_sub_C_of_splits` for the linear factorisation.
- For the real factorisation: `Polynomial.lifts`, `Polynomial.map_aeval_real_complex`, or building a quadratic factor manually from a conjugate pair.
- `Complex.conj`, `Complex.normSq`, `Complex.add_conj` (`z + conj z = 2 · z.re`).
- `Polynomial.coeff_mul`, `Polynomial.natDegree_mul` for the inductive coefficient-non-negativity argument.

If a hook is genuinely missing from Mathlib, document it as a sub-blocker (parallel to `rouche_theorem_missing.md`).

### Section 3: Phasing

Each phase should be 1–2 cycles with concrete deliverables:

- **Phase C.1** (1–2 cycles): Möbius algebraic bridge.
  - Define a Möbius polynomial transform (likely as `αPoly.eval₂ (Polynomial.C ∘ ?) ((1 - X) / (1 + X))` after clearing denominators by multiplying through by `(1 + X)^k`).
  - Prove the algebraic identity relating `aPoly` to `α` (or `ρ`) under the Möbius image.
  - Witness on explicit Euler and BDF2.

- **Phase C.2** (1 cycle): Stability ⇒ `aPoly` roots lie in closed left half-plane.
  - Compose Phase C.1 with `M.IsStable`'s implicit closed-unit-disk root location for `α` (or `ρ` — bridge already exists from cycle 174 `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`).
  - Output: `∀ ζ ∈ aPoly.aroots ℂ, ζ.re ≤ 0`.

- **Phase C.3** (1–2 cycles): Real factorisation + non-negative-coefficient closure.
  - Show `aPoly` (over `ℝ`) factors as a product of real linear factors `(X − ξ)` with `ξ ≤ 0` and conjugate-pair quadratic factors `(X² − 2·Re(ζ)·X + |ζ|²)` over `ℝ`.
  - Prove: each factor has non-negative coefficients (modulo the leading coefficient).
  - Prove: product of polynomials with non-negative `coeff i` for `i ≥ 1` (with non-negative constant terms allowed) has non-negative coefficients.
  - Compose to: `aᵢ ≥ 0` for `i ≥ 2`.

  (Note: `a₀ = 0` under preconsistency — already shipped as `aPoly_coeff_zero_of_preconsistent` in cycle 174; `a₁ > 0` per Phase B; Phase C only addresses `i ≥ 2`.)

- **Phase C.4** (1 cycle): Combine to close `lem:441A` fully and update `lean_status.json` from `partial` to `formalized`. Add BDF2 sanity witnesses for the `a₂ ≥ 0` clause.

### Section 4: Risk assessment

For each phase, estimate:

- LOC budget.
- Mathlib infrastructure risk (Phase C.3's "real factorisation of a complex-root polynomial via conjugate-pair quadratic factors" is the highest risk — verify Mathlib has the right tools).
- Aristotle suitability: Phase C.1 medium, Phase C.2 medium, Phase C.3 low (heavily structural).
- Alternative routes if a phase blocks (e.g., bypass via Schur/Jordan if we ever land that infrastructure for §142, or direct evaluation on small fixed `k` as a Phase C.bypass for BDF2 specifically).

### Section 5: Cross-references

Link to:
- `lem_441A_alpha_prime_negative.md` (the existing parent issue tracking the full `lem:441A` closure).
- `jordan_canonical_form_missing.md` (parallel infrastructure gap; not a blocker for Phase C but informative).
- `rouche_theorem_missing.md` (sibling `Polynomial`-over-`ℂ` infrastructure issue).
- The `αPoly` / `βPoly` definitions in `OpenMath/Chapter4/Section410.lean`.
- The Phase B chain ending at `aPoly_coeff_one_pos_of_stable_preconsistent` (cycle 179).

## Priority 2 (stretch — only if Priority 0 + 1 land cleanly with cycle budget remaining) — `bdf2LMM_aPoly_eq` closed form

Per cycle 174 consultant advice §B.3, the long-stalled BDF2 closed-form witness `bdf2LMM_aPoly_eq` can be closed via `Polynomial.funext` + `ring` (the "last-resort recipe" that was suggested but never tried — cycles 172/173 used `Polynomial.ext` + `ring` and stalled because `ring` cannot fold `Polynomial.C` arithmetic over the rationals).

Target:

```lean
theorem bdf2LMM_aPoly_eq :
    bdf2LMM.aPoly = Polynomial.C (4 / 3) * Polynomial.X
                    + Polynomial.C (8 / 3) * Polynomial.X ^ 2 := by
  apply Polynomial.funext
  intro x
  unfold LinearMultistepMethod.aPoly
  simp only [bdf2LMM, Fin.sum_univ_two,
             Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
             Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
             Polynomial.eval_one, Polynomial.eval_neg]
  ring
```

`Polynomial.funext` requires `Polynomial ℝ` over an infinite domain (which `ℝ` is), so the predicate should hold. Use `lean_local_search "Polynomial.funext"` to confirm the exact name and signature. If unavailable in current Mathlib, the cleanest alternative is `Polynomial.eq_of_eval_eq_of_natDegree_le`-style lemma (search for it). Do NOT fall back to manual `Polynomial.ext` + per-coefficient `simp + norm_num` skeleton (cycle 172/173 dead end pattern).

If `bdf2LMM_aPoly_eq` lands, add as one-line corollaries:

```lean
theorem bdf2LMM_aPoly_coeff_two_eq :
    bdf2LMM.aPoly.coeff 2 = 8 / 3 := by
  rw [bdf2LMM_aPoly_eq]
  simp

theorem bdf2LMM_aPoly_coeff_two_pos :
    0 < bdf2LMM.aPoly.coeff 2 := by
  rw [bdf2LMM_aPoly_coeff_two_eq]
  norm_num
```

These would numerically witness `aᵢ ≥ 0` for `i = 2` on BDF2, providing concrete evidence for Phase C without committing to its infrastructure.

**Time-box**: if `Polynomial.funext + ring` does not close within ≤ 30 minutes of attempt, abandon and ship Priority 0 + 1 only. Do NOT introduce `Polynomial.ext` skeletons (cycle 172/173 dead end). Do NOT raise `maxHeartbeats`.

## What NOT to do

- **DO NOT** treat the supervisor's "commit-not-reaching-repo" verdict as a real failure. It is the same `attempts.md`-propagated phantom diagnosed in cycles 8/14/15/35/73, now extended to cycles 176–179. The cycle 179 commit `572f058` IS valid; verify with `git show --stat 572f058 -- OpenMath/Chapter4/Section441.lean`.
- **DO NOT** revert any cycle 175–179 work. Phase B of `lem:441A` is correctly closed; the chain is mathematically sound (cycle 174 bridge `a₁ = 2·ρ'(1)` + cycle 178 `ρ'(1) > 0` + cycle 179 `linarith`).
- **DO NOT** attempt full Phase C closure in cycle 180. It is multi-cycle work per the cycle 179 task results' "Suggested next approach" section. Scoping the issue file IS the correct cycle 180 deliverable.
- **DO NOT** attempt any Phase C.1 / C.2 / C.3 proof body in this cycle. Save those for cycles 181+ with a dedicated strategy.
- **DO NOT** use `Polynomial.ext` + `ring` for `bdf2LMM_aPoly_eq` (cycle 172/173 stall pattern; `ring` cannot fold `Polynomial.C` arithmetic over the rationals).
- **DO NOT** raise `maxHeartbeats` above 200000.
- **DO NOT** introduce any `axiom` or `constant` declarations for Phase C blockers — Phase C's textbook argument is genuinely formalisable; the issue is just multi-cycle Mathlib plumbing.
- **DO NOT** modify `scripts/autonomous_loop.py` (loop-maintainer territory).
- **DO NOT** poll Aristotle (no jobs are pending per the prompt's "Completed Aristotle results: No pending Aristotle results" note).
- **DO NOT** spend cycle time on `picard_lindelof_bound_strengthening`, `jordan_canonical_form_missing`, or `rouche_theorem_missing` — all are non-blocking for cycle 180's targets.
- **DO NOT** attempt to ship any §441 entity besides `lem:441A`. `thm:441C`, `thm:443A`, `thm:443B` all depend on `lem:441A` Phase C closure or on `lem:441B` which is deferred per the misinterpretation issue file.
- **DO NOT** attempt to formalise `lem:441B` from scratch — the cycle 172 misinterpretation issue file (`lem_441B_misinterpretation.md`) outlines the correct approach (universal `c_{2i}` constants from a `PowerSeries ℝ` inversion), which is its own multi-cycle infrastructure project.
- **DO NOT** attempt Aristotle batch submissions in this cycle. Phase C.1's algebraic identity is a future-cycle target; Priority 2's `bdf2LMM_aPoly_eq` is a one-shot tactic recipe better suited to direct attempt than Aristotle.

## Pre-commit verification (MANDATORY)

Before committing, run AND verify each of these:

```bash
# 1. Sanity check: file builds and has no sorries.
lake env lean OpenMath/Chapter4/Section441.lean    # must exit 0
grep -c '\bsorry\b' OpenMath/Chapter4/Section441.lean    # must be 0
lake build OpenMath.Chapter4.Section441    # must succeed

# 2. Tautology-scanner regex hygiene.
grep -Pn ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter4/Section441.lean    # must be empty

# 3. Axiom check on any new Priority 2 theorem (skip if Priority 2 not attempted).
echo '#print axioms OpenMath.Chapter4.Section441.bdf2LMM_aPoly_eq' \
  | lake env lean --stdin OpenMath/Chapter4/Section441.lean
# Expected: [propext, Classical.choice, Quot.sound] only.

# 4. Stage and commit ONLY the expected files.
git status    # confirm only Section441.lean (if Priority 2 lands), the new issue files, and .prover-state changes

git add .prover-state/issues/lem_441A_phase_C_scoping.md \
        .prover-state/issues/phantom_commit_verdict_pattern.md \
        .prover-state/attempts.md \
        .prover-state/strategy.md \
        .prover-state/heartbeat.json \
        .prover-state/history.jsonl \
        .prover-state/task_results/cycle_180.md
# Add Section441.lean ONLY IF Priority 2 lands:
# git add OpenMath/Chapter4/Section441.lean

# 5. Commit with a clear cycle 180 message.
git commit -m "$(cat <<'EOF'
Cycle 180 — §441 lem:441A Phase C scoping + phantom-verdict documentation

Priority 0: independently verified that cycles 176–179 supervisor
verdicts ("commit-not-reaching-repo") are false alarms. Section441.lean
DOES contain non-empty diffs in all four cycles (+209/+143/+62/+32
lines respectively, +446 cumulative). Phase B of lem:441A is
correctly closed.

Priority 1: scoped Phase C ("aᵢ ≥ 0" for i ≥ 2) into a multi-cycle
issue file detailing the textbook Möbius / complex-root argument,
required Mathlib hooks, 4-phase implementation plan, and risk
assessment.

[Priority 2: bdf2LMM_aPoly_eq closed form via Polynomial.funext]
[(only if attempted and landed cleanly)]

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"

# 6. Verify the commit actually contains all expected files.
git log -1 --stat    # confirm the issue files AND (if Priority 2 landed) Section441.lean

# 7. Push.
git push
git rev-parse HEAD origin/Main/Experiments    # must be equal
```

If step 6 shows missing files, the commit failed — fix and retry. Do NOT push a partial commit.

## Cycle deliverable bar

**Minimum (score +1)**: Priority 0 phantom-verdict verification recorded in attempts.md AND task results AND the new issue file `phantom_commit_verdict_pattern.md`. Plus Priority 1 issue file `lem_441A_phase_C_scoping.md` with all 5 sections complete.

**Target (score +2)**: Above + Priority 2 `bdf2LMM_aPoly_eq`, `bdf2LMM_aPoly_coeff_two_eq`, and `bdf2LMM_aPoly_coeff_two_pos` axiom-clean.

**Floor (score 0)**: Just Priority 0 (the phantom-verdict cleanup). Even this is a real positive cycle — it unblocks future cycles from the propagated false verdict. CLAUDE.md's "minimum: decompose a sorry or write an issue" rule is satisfied by the two new issue files.

The cycle 180 worker should NOT attempt to ship Phase C proof body; that is a planning failure mode. Stick to the priorities above.

## Backup plan (if Priority 1 stalls on issue-file authoring)

If, while authoring the Phase C scoping issue file, you discover that:

- **Mathlib lacks a key hook** (e.g. no `Polynomial.aroots_complex_real_factorisation` analog): document the gap as a sub-issue (parallel to `rouche_theorem_missing.md`), recommend alternatives (manual factorisation via `Polynomial.lifts` + companion-matrix Schur, or a Phase C bypass via direct evaluation on small `k`), and ship the partial scoping. Do NOT attempt to fill the Mathlib gap in cycle 180.
- **The textbook argument has a typo or non-rigorous step** (cycle 174 had a Butcher typo): document independently-verified algebra, footnote the discrepancy, and ship the corrected scoping. Do NOT silently accept the textbook.

Either outcome still satisfies the +1 cycle deliverable bar. The goal is to leave Phase C in a state where cycle 181's planner has a complete blueprint to follow.

## Reference: cycle 175–179 deliverables for cross-checking

When auditing the file at the start of cycle 180, expect to see ALL of these landmark theorems (in this order, by file line):

1. `LinearMultistepMethod.aPoly_coeff_zero_of_preconsistent` (cycle 173)
2. `LinearMultistepMethod.aPoly_coeff_one_unconditional` (cycle 173)
3. `LinearMultistepMethod.aPoly_coeff_one_eq_neg_two_alpha_deriv_at_one_of_preconsistent` (cycle 173)
4. `LinearMultistepMethod.ρPoly` definition (cycle 174)
5. `LinearMultistepMethod.ρPoly_eval_one_eq_zero_of_preconsistent` (cycle 174)
6. `LinearMultistepMethod.ρPoly_deriv_eval_one_unconditional` (cycle 174)
7. `LinearMultistepMethod.ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent` (cycle 174)
8. `LinearMultistepMethod.aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent` (cycle 174)
9. Private aux `geomSeq_isHomogeneousSolution_of_ρPoly_isRoot` (cycle 175)
10. `LinearMultistepMethod.ρPoly_no_real_root_gt_one` (cycle 175)
11. Private aux `idSeq_isHomogeneousSolution_of_preconsistent_ρPoly_deriv_zero` (cycle 176)
12. `LinearMultistepMethod.ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent` (cycle 176)
13. Four private leading-coefficient helpers `ρPoly_coeff_top_eq_one`, `ρPoly_natDegree_eq_k`, `ρPoly_leadingCoeff_eq_one`, `ρPoly_tendsto_atTop` (cycle 177)
14. `LinearMultistepMethod.ρPoly_pos_on_Ioi_one` (cycle 177)
15. `LinearMultistepMethod.ρPoly_deriv_eval_one_pos_of_stable_preconsistent` (cycle 178)
16. `LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent` (cycle 179)
17. BDF2 sanity witnesses: `bdf2LMM_isPreconsistent`, `bdf2LMM_aPoly_coeff_zero_eq`, `bdf2LMM_aPoly_coeff_one_eq` (cycle 175); `bdf2LMM_ρPoly_deriv_eval_one_eq` (cycle 176); `bdf2LMM_ρPoly_pos_at_two` (cycle 177); `bdf2LMM_ρPoly_deriv_eval_one_pos` (cycle 178); `bdf2LMM_aPoly_coeff_one_pos` (cycle 179)

If any landmark is missing, the phantom-verdict diagnosis IS wrong (i.e. the prior cycle really did fail). Re-investigate before proceeding.

If all landmarks are present (which they are as of the consultant's verification), proceed with confidence: Phase B is closed, cycle 180's job is scoping + (optional) BDF2 closed-form polish, NOT re-deriving Phase B.
