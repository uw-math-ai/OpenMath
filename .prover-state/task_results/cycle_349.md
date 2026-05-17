# Cycle 349 Results

## Worked on

Phase D′.2.0 precursors for `def:422B` (the cycle 348 scoping doc
`.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md` §5).
Three small axiom-clean ships preparing the ground for Phase D′.2.1's
Route E refactor in cycle 350+.

* **Priority 1**: `Section451.bdf2LMM_isConsistent`
  (`OpenMath/Chapter4/Section451.lean:331`).
* **Priority 2**: `Section422.sum_β_pos_of_stable_consistent`
  (`OpenMath/Chapter4/Section422.lean:1024`).
* **Priority 3**: BDF2 numerical witness for Priority 2 — anonymous
  `example` immediately following (`Section422.lean:1045`).

## Approach

* **Priority 1 — placement deviation from strategy.** Strategy §
  Priority 1 asserted "Section451.lean already imports Section441
  (which provides `bdf2LMM_isPreconsistent`)". This is false:
  Section441 imports Section451 (cycle 346 dependency for
  `bdf2LMM_isStable`'s definition site), so the reverse would be
  circular. Placed `bdf2LMM_isConsistent` in Section451 (after
  `bdf2LMM_isStable`) and re-proved preconsistency inline — the
  proof is 4 lines and the duplication cost is minimal.
* **Priority 2** — verbatim from strategy: rewrote the goal via cycle
  345's `coef_α_eq_sum_β_of_isConsistent` (LHS = coef_α, RHS =
  sum_β, so `← rw` converts sum_β back to coef_α in the goal), then
  closed via cycle 344's `coef_α_pos_of_stable_preconsistent`. 2-line
  proof.
* **Priority 3** — preferred form (generic theorem applied to BDF2)
  shipped as a final-state anonymous `example`. Hypotheses:
  `0 < 2` discharged by `norm_num`; stability via cycle 346's
  `bdf2LMM_isStable`; consistency via Priority 1's
  `bdf2LMM_isConsistent`. End-to-end exercise of the generic theorem.

## Result

**SUCCESS** — all three deliverables compile axiom-clean.

* `Section451.lean` rebuilds in 308s (`lake build`).
* `Section422.lean` typechecks in ~5 min (`lake env lean`).
* Axiom check (verified via `#print axioms` appended temporarily then
  reverted):
  - `OpenMath.Chapter4.Section451.bdf2LMM_isConsistent` depends on
    `[propext, Classical.choice, Quot.sound]` ✓
  - `OpenMath.Chapter4.Section422.sum_β_pos_of_stable_consistent`
    depends on `[propext, Classical.choice, Quot.sound]` ✓
* Sorry count remains 0 in both files.

## Faithfulness check

### `Section451.bdf2LMM_isConsistent` (Priority 1)

* **Entity ID**: `def:404B` (the `IsConsistent` predicate Butcher
  defines on p. 339).
* **Textbook statement** (quoted from `entities/def_404B.json` via
  `Section404.LinearMultistepMethod.IsConsistent`'s docstring at
  `Section404.lean:128-137`):
  > "a linear multistep method satisfying (404a) and (404b) is said
  > to be 'consistent'"
* **Lean statement captures**: SAME — `bdf2LMM.IsConsistent`,
  where `IsConsistent` is defined as `IsPreconsistent ∧ SatisfiesEq404b`
  (Section404.lean:135-137).
* **Numerical content check**:
  - (404a) `α₁ + α₂ = 4/3 - 1/3 = 1` ✓
  - (404b) `1·(4/3) + 2·(-1/3) = 2/3 = 2/3 + 0 + 0` ✓
* **Tautology check**: conclusion is `bdf2LMM.IsConsistent`, no
  hypotheses — vacuously passes.
* **Identity check**: proof is a `refine`+`simp`+`norm_num` discharge,
  not `exact h`. Not vacuous.

### `Section422.sum_β_pos_of_stable_consistent` (Priority 2)

* **Entity ID**: not a Butcher-named lemma — Phase D′.2.0 helper
  precursor for `def:422B` (the cycle 348 scoping doc names this the
  "Route B precursor").
* **Textbook content captured**: a direct consequence of Butcher's
  (404a) + (404b) + the Dahlquist root condition (encoded as
  `IsStable`). The strict positivity is the β-side analog of the
  cycle 178 `ρPoly_deriv_eval_one_pos_of_stable_preconsistent` α-side
  positivity, but for the *unweighted* β-sum.
* **Hypothesis strength check**: hypotheses `hk : 0 < k`,
  `hStable : M.IsStable`, `hConsistent : M.IsConsistent`. The `0 < k`
  hypothesis is necessary (otherwise `coef_α` is the empty sum and
  positivity fails); textbook implicitly assumes `k ≥ 1` for an LMM
  to be a proper multistep method. `IsStable + IsConsistent` are
  the textbook hypotheses for the underlying-one-step-method
  existence statement in Butcher §422. No extra hypotheses.
* **Caveat documented in docstring**: this is the *unweighted*
  β-sum `Σᵢ βᵢ`, **NOT** the §422 weighted coefficient
  `coef_β = Σᵢ i · βᵢ`. The two differ; the lemma does NOT close
  Phase D′ Step 2 on its own (Phase D′.2.1 work).
* **Tautology check**: conclusion is `0 < Σ_{i:Fin (k+1)} M.β i`,
  not present in hypotheses. Passes.
* **Identity check**: proof is `rw + exact`, two lines of substantive
  composition. Not vacuous.

### Anonymous BDF2 witness (Priority 3)

* No new named symbol; non-vacuity check for Priority 2 on BDF2.
* Numerically: `2/3 + 0 + 0 = 2/3 > 0` ✓.

## Dead ends

1. **Placement error in strategy.** Strategy §Priority 1 specified
   Section451 as the location and claimed Section441 was imported.
   Checking `OpenMath/Chapter4/Section451.lean` imports revealed only
   `import Mathlib` and `import OpenMath.Chapter4.Section404` — no
   Section441. Confirmed via `grep ^import OpenMath/Chapter4/Section441.lean`
   that Section441 imports Section451 (for `bdf2LMM`), so the reverse
   import would create a cycle. **Resolution**: keep the Section451
   location but re-prove preconsistency inline (4 lines).

2. **`lake env lean` does not refresh oleans.** After editing
   Section451 and running `lake env lean OpenMath/Chapter4/Section451.lean`
   (EXIT=0), Section422 failed with `unknownIdentifier` on
   `Section451.bdf2LMM_isConsistent`. The stale `.olean` from before
   the edit was still present. **Resolution**: `lake build
   OpenMath.Chapter4.Section451` (308s) refreshed the olean; then
   `lake env lean OpenMath/Chapter4/Section422.lean` succeeded.

3. **LSP timeouts.** `mcp__lean-lsp__lean_diagnostic_messages` and
   `mcp__lean-lsp__lean_verify` both timed out / errored on the
   large Section441/Section422 files. **Resolution**: axiom check
   done via inline `#print axioms` appended to Section422.lean,
   then reverted.

4. **Axiom-check via separate file.** Created
   `.prover-state/axiom_check_349.lean` importing both files —
   timed out at 9 min on the dual-import. Reverted to inline
   `#print axioms`.

## Discovery

1. **`lake env lean` does NOT update build artifacts.** It runs the
   compiler against the cached oleans of dependencies. To make a
   downstream file see a new theorem in an upstream file, you must
   `lake build <upstream>` first. The cached-olean trap is easy to
   miss when the upstream typechecks cleanly. Saving this as a
   lesson for future cycles that touch multi-file edits.

2. **Strategy "imports already in place" claims need verification.**
   The cycle 348 scoping doc + the cycle 349 strategy both claimed
   Section451 imports Section441, contradicting the actual file
   header. Verifying imports via `grep ^import` is cheap; doing it
   first would have saved one round-trip of placement-then-revert.

3. **`Fin.sum_univ_two` + `Fin.sum_univ_three` is the canonical
   pair for BDF2 numerical proofs.** `α` has `Fin 3` indexing (size
   `k+1 = 3`), `α.succ` has `Fin 2` indexing (size `k = 2`),
   `β` has `Fin 3`. `simp [bdf2LMM, Fin.sum_univ_two, Fin.sum_univ_three]
   ; norm_num` discharges both (404a) and (404b) in one go.

## Suggested next approach

### For cycle 350 (Phase D′.2.1 — Route E execution per cycle 348 §7)

1. **First 30 min** — Re-read `extraction/raw_text/ch04.txt` §410,
   §432, §441 per cycle 348 §7 step 1 to refute/confirm Route A's
   βPoly leading-coefficient obstruction and to look for
   boundary-locus constraints on `σ'(1)`.

2. **Next 30 min** — Verify Mathlib hooks for Routes D and E via
   `lean_local_search` / `lean_loogle`.

3. **Rest of cycle** — Adopt Route E (corollary reformulation,
   ~100 LOC) as the Phase D′.2.1 deliverable. The cycle 349
   precursors (`sum_β_pos_of_stable_consistent`,
   `bdf2LMM_isConsistent`) feed into the non-vanishing argument
   `coef_α + coef_β ≠ 0`: combining `coef_α > 0` (cycle 344) with
   the `coef_β > -coef_α` style argument that Phase D′.2.1 needs to
   prove using the new precursors.

### Mathematical observation worth pursuing in cycle 350

The textbook (404b) equation gives `coef_α = sum_β` for any consistent
LMM, and `sum_β = β₀ + Σᵢ≥₁ βᵢ`. The §422 `coef_β = Σᵢ i·βᵢ = Σᵢ≥₁ i·βᵢ`
(since the `i=0` term vanishes). The gap `sum_β - coef_β = β₀ + Σᵢ≥₁
(1-i)·βᵢ` does **not** in general have a fixed sign — for BDF2 it's
`2/3 + 0 + (-1)·0 = 2/3 > 0`, but for explicit Euler
(`β₀ = 0, β₁ = 1`) it's `0 + 0 = 0`. So the **strict** non-vanishing
`coef_α + coef_β ≠ 0` route remains the cleanest path — Route E's
hypothesis-weakening reformulation rather than a direct `coef_β ≥ 0`
derivation.

### Pivot option per cycle 347

If `def:422B` has absorbed too many cycles (the streak is now 15
cycles since cycle 336), planner may pivot to:
* `def:451A` G-stability
* `thm:535A` GLM underlying one-step method
* `thm:541A` DIMSIM types

per the cycle 347 task results option C.
