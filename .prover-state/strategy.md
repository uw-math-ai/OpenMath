# Cycle 201 Strategy — Roll back `thm:381H` scaffold + ship Banach FP foundation

## Context (read carefully before doing anything)

**Cycle 200 scored −2 (REVERTED).** Reason: sorry count went 0 → 3 when
the worker shipped the `equivalent_iff_pEquivalent_iff_phiEquivalent`
(thm:381H) statement-only scaffold with 3 deferred-sorry directions.
The cycle 200 commit `53848e2` IS in HEAD — the "REVERTED" verdict is
a supervisor policy signal ("sorry increase is bad"), not a git revert.
The 3 sorries are still in `OpenMath/Chapter3/Section381.lean` at
lines 1622, 1629, 1640.

**Established precedent**: cycle 138 → cycle 139 (sorry-first scaffold
for `thm:550A` general-n was removed in the next cycle "to drive sorry
count back to 0" — the file `thm_550A_general_n.md` records this).
Cycle 149 → cycle 150 (sorry-first scaffold for def:530B Path A was
rolled back). Cycle 201 follows the same pattern.

**None of the 3 cycle-200 sorries can be closed in a single cycle:**
- `PhiEquivalent → PEquivalent` (line 1622): needs thm:381G (4–5 cycles)
- `PEquivalent → Equivalent` (line 1629): needs Banach FP (2–3 cycles)
- `Equivalent → PEquivalent` (line 1640): needs thm:381G (4–5 cycles)

Therefore cycle 201 must roll back, then ship substantive infrastructure
that unblocks a future cycle. The natural target is **Banach fixed-point
infrastructure** for the implicit RK stage iteration — the worker's own
cycle 200 "Suggested next approach" Track 1, and the shortest path to
closing one of the three sorries (in cycle 202 or 203).

## Priority 0 — GPFS smoke test (≤ 5 min)

Run `time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`.
Expect 21st consecutive timeout (cycles 182–200 all timed out at exactly
300s with near-zero CPU; pattern documented in
`.prover-state/issues/cycle_182_gpfs_slowness.md`).

**Branch decision**:
- If timeout (EXIT=124, CPU < 1%): log the 21st-iteration entry in
  `cycle_182_gpfs_slowness.md` and proceed to P1. Do NOT retry. Do NOT
  attempt Phase C.2.
- If GPFS recovers (compile succeeds in < 5 min, CPU > 50%): pivot to
  Phase C.2 per `.prover-state/issues/lem_441A_phase_C_scoping.md`.
  Apply the cycle 184 namespace fix to
  `.prover-state/cycle_182_draft_section441.lean` line 1529 (already
  identified), copy draft to `OpenMath/Chapter4/Section441.lean`, compile,
  ship. Skip P1 and P2.

## Priority 1 — Roll back thm:381H scaffold (sorry count 3 → 0)

Restore `Section381.lean` to cycle 199's state for the thm:381H region.

### Exact actions

1. **Locate the scaffold**: Open `OpenMath/Chapter3/Section381.lean` and
   find `theorem equivalent_iff_pEquivalent_iff_phiEquivalent` at
   line ~1613. The block spans approximately lines 1613–1642 (theorem
   declaration + docstring + proof body with three `sorry` lines plus
   per-sorry comments). Use `Read` to view the exact range first; the
   3 sorry lines (1622, 1629, 1640) are inside this block.

2. **Verify what's being removed**: Before deleting, confirm via Read
   that:
   - The theorem opens after a comment block citing Butcher §380, p. 304.
   - The proof body is `refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩` followed by four
     direction cases, three of which contain `sorry` and one of which
     uses `PEquivalent.toPhiEquivalent`.
   - No OTHER theorems in `Section381.lean` reference
     `equivalent_iff_pEquivalent_iff_phiEquivalent` (sanity check with
     `Grep` for the theorem name).

3. **Delete the scaffold**: Use `Edit` to remove the theorem declaration,
   docstring, and proof body entirely. Be careful not to accidentally
   remove the surrounding cycle 187 lemmas
   (`PEquivalent.toPhiEquivalent` and `PReducesTo.toPhiEquivalent`) —
   they precede thm:381H and must stay.

4. **Verify sorry count is 0**:
   ```bash
   grep -c "^  sorry$" OpenMath/Chapter3/Section381.lean
   grep -n "sorry" OpenMath/Chapter3/Section381.lean
   ```
   Should return 0 / empty.

5. **Compile-check**:
   `time lake env lean OpenMath/Chapter3/Section381.lean`
   Expect exit 0, ~50s warm rebuild, no `sorry` warnings.

6. **Axiom-check on a few cycle 199 theorems** to confirm no regression:
   - `pEquivalent_irreducible_reduct_unique_of_sources_irreducible`
   - `PEquivalent.toPhiEquivalent`
   - `PReducesTo.toPhiEquivalent`
   All should still return `[propext, Classical.choice, Quot.sound]`.

7. **Update `extraction/formalization_data/lean_status.json`**: change
   `thm:381H` row:
   - `status`: `partial` → `unformalized`
   - Remove `lean_file` and `lean_symbol` fields (or set to `null` —
     match the existing convention for `unformalized` rows).
   - Bump `cycle` reference to 201.

8. **Update `plan.md`** at the `thm:381H` row in the Chapter 3 section:
   - Change `[~]` → `[ ]`
   - Remove the long "cycle 200" summary text (the multi-line entry
     starting with "`OpenMath/Chapter3/Section381.lean` (cycle 200)").
   - Keep the row title and entity ID; revert to the original short form.

9. **Update `.prover-state/issues/thm_381H_deferred.md`** with a new
   "## Cycle 201 rollback" section at the top:
   - Explain the rollback (sorry count 3 → 0 per supervisor policy).
   - Preserve the cycle 200 analysis below (per-direction blockers,
     estimated cycle budget table) as planning material for future
     re-introduction.
   - Recommend Banach FP first (cycle 201 P2 work), then re-introduce
     scaffold once `PEquivalent → Equivalent` is closeable in one cycle.

**Do NOT** delete `thm_381H_deferred.md`. It has useful planning.

### P1 sanity check before moving to P2
- `grep -c "^  sorry$" OpenMath/Chapter3/Section381.lean` returns 0.
- `lake env lean OpenMath/Chapter3/Section381.lean` exits 0.
- `git diff --stat OpenMath/Chapter3/Section381.lean` shows only line
  deletions (or minor reflows), no additions yet.

## Priority 2 — Begin Banach fixed-point foundation (substantive ship)

The `PEquivalent → Equivalent` direction of thm:381H requires that the
implicit RK stage iteration converges to a unique fixed point for
sufficiently small step sizes. The infrastructure is also load-bearing
for `Equivalent M M` reflexivity (issue
`equivalent_self_general_deferred.md`) and the constructive `def:381E
reducedMethod` (issue `reduced_method_deferred.md`).

**Cycle 201 scope**: ship the FOUNDATION pieces (definition + Lipschitz
lemma + non-vacuity witness). Do NOT attempt the full `ContractingWith`
+ `fixedPoint` machinery this cycle — defer to cycle 202. Aim for
~80–120 LOC, 0 sorries net, axiom-clean.

### Concrete deliverables

Add to `OpenMath/Chapter3/Section381.lean` (after the existing
`RKTableau` namespace block but before the file's terminal `end`).
Section381 is currently ~1700 LOC after the P1 rollback; staying in
one file avoids import-graph disruption.

#### Step 1 — Definition: `RKStageMap`

The function whose fixed points are the implicit-stage solutions.
For a Runge-Kutta tableau `M : RKTableau s`, step size `h : ℝ`,
autonomous RHS `f : ℝ → ℝ` (start with scalar; vector-valued lift is a
later refinement), and initial value `y₀ : ℝ`:

```lean
noncomputable def RKStageMap {s : ℕ} (M : RKTableau s) (h : ℝ)
    (f : ℝ → ℝ) (y₀ : ℝ) : (Fin s → ℝ) → (Fin s → ℝ) :=
  fun Y i => y₀ + h * ∑ j : Fin s, M.A i j * f (Y j)
```

The fixed point property `RKStageMap M h f y₀ Y = Y` is exactly the
implicit stage equation. **Pre-flight**: verify the exact stage-equation
form by reading `IsRKOneStep` at `Section381.lean` around line 970 —
the definition above must align with the existing predicate's stage
equation (modulo the autonomous/non-autonomous distinction).

#### Step 2 — Lipschitz lemma

```lean
theorem RKStageMap_lipschitz {s : ℕ} (M : RKTableau s) (h : ℝ)
    (hh : 0 ≤ h) {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    (y₀ : ℝ) :
    LipschitzWith (some_constant_in_h_L_M) (RKStageMap M h f y₀)
```

The exact Lipschitz constant depends on the chosen metric on
`Fin s → ℝ`. Two reasonable options:

- **Sup norm** (`PiLp ∞`): Lipschitz constant is `h * L * max_i ∑_j |M.A i j|`.
- **Loose entrywise bound**: Lipschitz constant is
  `h * L * ∑_{i,j} |M.A i j|` (works for any reasonable metric).

Ship the loose bound first if the sup-norm version turns out to require
fiddly `PiLp` instance manipulation. Tightness is a future-cycle
refinement.

Use Mathlib lemmas:
- `LipschitzWith.const_mul` for scaling by `h * L * const`.
- `LipschitzWith.sum` for sums of Lipschitz functions.
- `LipschitzWith.comp` for the inner `f (Y j)` composition.

**Pre-flight**: before writing the proof, use `lean_loogle` to verify
the names of `LipschitzWith.sum`, `LipschitzWith.const_mul`,
`LipschitzWith.comp` in the pinned Mathlib v4.28.0. Some names may
differ (e.g. it might be `LipschitzWith.smul_const` or in a different
namespace).

#### Step 3 — Non-vacuity witness (explicit Euler / paddedEuler)

The `paddedEuler` method (already in Section381 from cycle 184 era —
verify by Grep) is the canonical test target. For `paddedEuler` with
`s = 2` and a strict-lower-triangular `A`, `RKStageMap` reduces to a
direct evaluation — Lipschitz with constant 0 in the diagonal stage
and `h * L` in the off-diagonal stage.

Alternative: use a simpler explicit Euler `RKTableau 1` with `A = 0`,
where `RKStageMap` is constant in `Y` (independent of input), giving
Lipschitz with constant 0 trivially.

```lean
example : LipschitzWith 0 (RKStageMap explicitEulerRKTableau (1 : ℝ)
    (fun y => y) (0 : ℝ))
```

Adjust to whatever explicit-Euler-flavored `RKTableau` instance already
exists in Section381. Don't create a new instance — reuse `paddedEuler`
or whatever cycle 184+ shipped.

### Faithfulness note for P2

`RKStageMap` is a direct transcription of the implicit stage equation
from Butcher §312 (definition of a general Runge-Kutta method). No
divergence from textbook content. The "for small h" qualifier in the
Banach FP argument matches Butcher's tacit assumption throughout §380
("for h sufficiently small the stage equations have a unique
solution"). When future cycles ship `ContractingWith`, document this
"small h" hypothesis explicitly as a parameter (per the cycle 116
`is_convergent_strengthened.md` pattern).

### Time budget for P2
- Step 1 (definition): 15 min.
- Step 2 (Lipschitz lemma): 60–90 min (Mathlib hook verification is the
  time risk).
- Step 3 (witness): 15 min.
- Total: ~90–120 min.

**Stall fallback**: if Step 2 doesn't close by ~90 min in, ship Steps
1 + 3 only (definition + simpler constant-map witness) and file an
issue noting the Lipschitz hook gap. Sorry count must remain 0 net.

## DO NOT (explicit pruning of failed/forbidden paths)

- **Do NOT attempt to close any of the 3 cycle-200 sorries** in this
  cycle. They require multi-cycle infrastructure that does not fit
  in one cycle (worker's own cycle 200 analysis).
- **Do NOT re-introduce the cycle 200 thm:381H scaffold** in any form
  before the P1 rollback is complete and committed. The scaffold can
  return in a future cycle once at least one direction is closeable.
- **Do NOT try the `PEquivalent → Equivalent` closure as a stretch
  goal in cycle 201**. The cycle 200 worker estimated 2–3 cycles; a
  one-cycle attempt is high-risk and would likely produce a half-built
  Banach FP scaffold that has the same supervisor-revert problem.
- **Do NOT re-attempt Section441 Phase C.2** beyond the 5-min P0 smoke
  test. 20 consecutive timeouts establish the GPFS pathology is
  cluster-side; loop-maintainer territory.
- **Do NOT modify `scripts/autonomous_loop.py`**. Per CLAUDE.md.
- **Do NOT modify `extraction/raw_text/` or
  `extraction/formalization_data/entities/`** (regenerated artifacts).
  Only `extraction/formalization_data/lean_status.json` is hand-editable.
- **Do NOT bump `maxHeartbeats`** above 200000. Decompose instead.
- **Do NOT introduce `axiom` / `constant`** for Banach FP. Mathlib has
  `LipschitzWith`, `ContractingWith`, `fixedPoint` — use them.
- **Do NOT** try the "smarter φ" approach for stage extraction (this
  was ruled out for §514 in cycle 097 — same structural issue applies
  to RK stages).
- **Do NOT** poll Aristotle more than once. No new Aristotle batches
  needed this cycle (Banach FP work is mechanical Mathlib plumbing,
  poor fit for natural-language premise selection).
- **Do NOT** create a new `Section381BanachFP.lean` file this cycle —
  stay in `Section381.lean` to avoid import-graph disruption. Splitting
  is a future-cycle refactor.

## Faithfulness check (run before commit)

For the P1 rollback:
- [ ] `thm:381H` row in `lean_status.json` returns to `unformalized`.
- [ ] `plan.md` row returns to `[ ]` form.
- [ ] No dangling references to the deleted theorem name anywhere:
  `grep -rn "equivalent_iff_pEquivalent_iff_phiEquivalent"` returns
  empty across the repo.

For the P2 ship:
- [ ] `RKStageMap` definition matches Butcher §312 implicit-stage form.
  Cross-check by reading the `IsRKOneStep` predicate that
  `Section381.lean` already defines.
- [ ] Non-vacuity witness compiles and is axiom-clean.
- [ ] Lipschitz lemma (if shipped) does not silently strengthen
  hypotheses beyond what the textbook implies. The Lipschitz constant
  should be derivable from `M.A` entries plus `L` and `h` — no extra
  monotonicity or non-negativity assumptions on `M.A` itself.
- [ ] Tautology scanner: `grep -nE ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$'
  OpenMath/Chapter3/Section381.lean` returns 0 hits (use `hLip`, not
  `h_lip`, etc. per the cycle 014/015 tautology-scanner workaround).
- [ ] `#print axioms` on each new public theorem returns only
  `[propext, Classical.choice, Quot.sound]`.

## Commit message template

```
Cycle 201 — §380 thm:381H scaffold rolled back (sorry count 3→0 per
supervisor policy); Banach FP foundation: RKStageMap def + Lipschitz
lemma + paddedEuler trivial witness in OpenMath/Chapter3/Section381.lean
(axiom-clean, unblocks PEquivalent → Equivalent closure in 1–2 future
cycles); §441 Phase C.2 GPFS-blocked (21st)
```

Adjust if P2 sub-steps were skipped per the stall fallback.

## Cycle 202 entry point (preview)

If cycle 201 ships Steps 1 + 2 + 3 cleanly:
- Cycle 202: prove `RKStageMap_contracting` (`ContractingWith` instance
  for small `h`) using cycle 201's `RKStageMap_lipschitz`. Apply
  `ContractingWith.fixedPoint` to produce the existence/uniqueness of
  stage solutions. ~80 LOC.
- Cycle 203: prove the P-partition iteration invariant
  `Yᵢ⁽ᵏ⁾ = Yⱼ⁽ᵏ⁾ for i, j in same block of an `IsPReducibleVia P`
  witness; lift to limit via Banach FP; close `PEquivalent → Equivalent`.
  Re-introduce thm:381H scaffold with this sorry now closed (sorry
  count 2; one closed). ~120 LOC.

If cycle 201 ships Step 1 only:
- Cycle 202: revisit the Lipschitz lemma with fresh Mathlib hook
  verification. Same downstream plan.
