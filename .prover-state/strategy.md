# Cycle 151 Strategy

## Status snapshot

- Sorry count: **0** (cycle 150 restored from cycle 149's regression).
- Cycle 150 score: **+2** (sorry restored to 0; n=7 stepping stone
  added axiom-clean).
- Last 5 cycles: 146 (r=2 negative witnesses +2) → 147 (n=5 +2) →
  148 (n=6 + Aristotle submission +2) → 149 (def:530B scaffold −2
  reverted) → 150 (rollback + n=7 +2).
- thm:515D capstone remains closed and axiom-clean since cycle 124.
- thm:550A: seven concrete-`n` axiom-clean stepping stones
  (n = 1..7); general-n deferred. Aristotle project
  `2c4630b2-2998-4d4a-af88-c2f83fbd9eda` (cycle 148) returned
  IN_PROGRESS at 18% on cycle 150's poll, ~48h after submission.

## Posture

We are not in recovery mode. The repo is on a clean tip with zero
sorries. Pivot to forward progress.

This cycle targets **def:530B Path A Step 1** — introduce the
`IsExplicit` predicate on `GeneralizedRungeKuttaMethod` together with
positive and negative witnesses. This is the recommended path forward
per the cycle-150 task results "Suggested next approach" and per
`.prover-state/issues/def_530B_scaffold_strategy.md`. It is a clean
single-cycle deliverable with bounded scope (~50-80 LOC), axiom-clean
expected, and lays the foundation for cycle 152's Step 2 (defining
the explicit-only operators `applyStartingThenStep_explicit` /
`applyExactThenStarting_explicit`, the load-bearing primitives for
def:530B itself).

## Priority 0 — Aristotle housekeeping (~5 min, MANDATORY first)

The cycle-148 Aristotle project `2c4630b2-2998-4d4a-af88-c2f83fbd9eda`
(general-`n` thm:550A) was at 18% after ~48h as of cycle 150. This
matches the cycle-141 pattern (analogous Job A cancelled at 6% after
24h) — clear evidence of intractability for the prover.

**Action**: cancel the project via `mcp__aristotle__cancel_project`
with id `2c4630b2-2998-4d4a-af88-c2f83fbd9eda`. Do NOT re-poll first
— CLAUDE.md "one check after 30 min is enough" already exhausted by
cycle 150's poll.

After cancelling, update `.prover-state/issues/thm_550A_general_n.md`:
add a paragraph noting cycle-151 cancellation alongside the existing
cycle-141 cancellation record. The general-`n` closure remains
deferred per the same multi-cycle infrastructure scope (cofactor
expansion induction or eigenvalue density).

Do NOT submit a fresh Aristotle job for the general-`n` proof this
cycle. Two failed long-running attempts (cycles 141 and 148) are
sufficient evidence; further submissions waste a job slot.

## Priority 1 — def:530B Path A Step 1: `IsExplicit` predicate + witnesses (substantive)

**Target file**: `OpenMath/Chapter5/Section530.lean`.

**What landed in cycle 139/141** (still in the file, do NOT touch):
- `GeneralizedRungeKuttaMethod` structure (with `s : ℕ`, `b₀ : ℂ`,
  `b : Fin s → ℂ`, `A : Matrix (Fin s) (Fin s) ℂ`).
- `StartingMethod` (the dependent-sequence wrapper).
- `IsDegenerate` / `IsNonDegenerate` predicates.
- Witnesses: `trivialGeneralizedRK`, `nontrivialTwoStageGRK`,
  `trivialStartingMethod`, `zeroStartingMethod`, `mixedStartingMethod`,
  `zero2StartingMethod`, plus their `_isNonDegenerate` /
  `_isDegenerate` companions.

**Pre-flight read**: open `OpenMath/Chapter5/Section530.lean` and
locate (a) the exact field names of `GeneralizedRungeKuttaMethod`
(b₀/b/A or different), (b) the concrete `A`-matrix definitions of
`trivialGeneralizedRK` and `nontrivialTwoStageGRK`, and (c) any
structure axioms (e.g. on `b`, `b₀`) that constrain valid
constructions. The strategy below assumes the cycle-139/141 record
is accurate; verify before encoding.

### 1.1 Add the predicate

Add the predicate after the cycle-139/141 infrastructure (locate the
right insertion point — likely just before the cycle 138-150
`doublyCompanionMatrix` section), in a new `section` or extension
of the existing namespace:

```lean
/-- A generalized Runge-Kutta method is *explicit* if its coefficient
matrix `A` is strictly lower triangular: `A i j = 0` whenever `i ≤ j`.
For an explicit method, the stage equations
`Y i = y₀ + h · Σⱼ A i j · f(Y j)` can be evaluated by direct
recursion on `i = 0, 1, …, s-1`, sidestepping the implicit
fixed-point machinery required for general (implicit) methods. -/
def GeneralizedRungeKuttaMethod.IsExplicit
    {s : ℕ} (M : GeneralizedRungeKuttaMethod s) : Prop :=
  ∀ i j : Fin s, i.val ≤ j.val → M.A i j = 0
```

Notes:
- Strict lower triangular means `A i j = 0` when `j ≥ i`. The
  spelling `i.val ≤ j.val` captures both `i = j` (diagonal) and
  `i < j` (above diagonal) — i.e. NOT below diagonal.
- Pick whichever spelling unifies with downstream Mathlib lemmas.
  Quick `lean_local_search "BlockTriangular"` and
  `lean_local_search "lowerTriangular"` BEFORE committing to the
  signature — if Mathlib has a clean predicate, prefer it for
  ergonomic reuse.

### 1.2 Add three witnesses (or two, see decision rule)

**Positive witness 1** — vacuous case at s = 1:
```lean
theorem trivialGeneralizedRK_isExplicit :
    trivialGeneralizedRK.IsExplicit := by
  intro i j _
  fin_cases i; fin_cases j
  -- exact closer depends on trivialGeneralizedRK.A definition;
  -- if A 0 0 = 0, `rfl` closes; else `simp [trivialGeneralizedRK]`
  rfl
```

If `trivialGeneralizedRK` has `A 0 0 = 0` (which the cycle-139 record
implies — it's the trivial 1-stage method with `b₀ = 1`), the witness
closes with `rfl` or a one-line `simp`. If `A 0 0 ≠ 0`, this witness
won't fly — fall back to a freshly-constructed `explicit1StageGRK`
trivially with `A := 0`.

**Positive witness 2** — non-trivial s = 2 case (DECISION REQUIRED):
Read `nontrivialTwoStageGRK`'s `A` definition first. If it is
strictly lower triangular (e.g. `A := !![0, 0; 1, 0]`), prove
`nontrivialTwoStageGRK_isExplicit` directly:
```lean
theorem nontrivialTwoStageGRK_isExplicit :
    nontrivialTwoStageGRK.IsExplicit := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | (exfalso; omega) | (simp [nontrivialTwoStageGRK]) | rfl
```
If it is NOT strictly lower triangular (e.g. `A 0 0 ≠ 0`, since
cycle 141 may have built it for the heterogeneous-stages design
rather than for explicit-method coverage):
- Construct a fresh `explicit2StageGRK : GeneralizedRungeKuttaMethod 2`
  with `A := !![0, 0; 1, 0]` (Heun-style stage matrix), and prove
  `explicit2StageGRK_isExplicit` for it.
- Optionally also prove `nontrivialTwoStageGRK_not_isExplicit` if
  it gives non-vacuity coverage in the negative direction without
  needing a fresh `implicit2StageGRK` (see Negative Witness below).

**Decision rule**: read `nontrivialTwoStageGRK`'s `A` definition
first. The CLAUDE.md non-vacuity rule requires at least ONE positive
witness AND at least ONE negative witness for `IsExplicit` to be
meaningful. Build the witness portfolio accordingly.

**Negative witness** — implicit method:
```lean
/-- A 2-stage implicit method (with `A 0 0 = 1/2`) that is *not*
explicit. Witnesses non-vacuity in the negative direction for
`IsExplicit`. -/
def implicit2StageGRK : GeneralizedRungeKuttaMethod 2 where
  b₀ := 1
  b := fun _ => (1 : ℂ) / 2
  A := !![1/2, 0; 0, 1/2]

theorem implicit2StageGRK_not_isExplicit :
    ¬ implicit2StageGRK.IsExplicit := by
  intro h
  have h00 := h ⟨0, by omega⟩ ⟨0, by omega⟩ (le_refl _)
  -- h00 : implicit2StageGRK.A ⟨0, _⟩ ⟨0, _⟩ = 0, i.e. (1 : ℂ) / 2 = 0
  simp [implicit2StageGRK] at h00
  -- norm_num at h00 if simp doesn't finish
```

If the `GeneralizedRungeKuttaMethod` structure has axioms on `b`,
`b₀` (e.g. `b₀ + Σ b = 1` consistency), pick `b`/`b₀` values
satisfying them. The negative witness only needs `A 0 0 ≠ 0`; the
remaining fields are bookkeeping.

### 1.3 Bookkeeping

- `extraction/formalization_data/lean_status.json`: no entity row
  changes (def:530B remains `unformalized`; `IsExplicit` is helper
  infrastructure, not a textbook entity).
- `plan.md`: no row changes for def:530B; if there's space, add a
  brief annotation under def:530B's `[ ]` row noting Path A Step 1
  is complete (cycle 151).
- `.prover-state/issues/def_530B_scaffold_strategy.md`: append a
  cycle-151 update noting that Path A Step 1 (the `IsExplicit`
  predicate + witnesses) is **complete**, and outline cycle 152's
  Step 2 target (defining `applyStartingThenStep_explicit` and
  `applyExactThenStarting_explicit` with `∀ i, IsExplicit (S.method i)`
  hypothesis; bodies via direct recursion on stage index using
  `Finset.sum` over already-computed earlier stages).
- `.prover-state/issues/thm_550A_general_n.md`: append a cycle-151
  paragraph recording the cancellation of project
  `2c4630b2-2998-4d4a-af88-c2f83fbd9eda` (companion to the cycle-141
  cancellation record). Note: the deferral remains in force; closure
  needs cofactor-expansion induction or eigenvalue-density
  infrastructure (multi-cycle).

## What NOT to try (explicit blacklist)

1. **Do NOT attempt the operator bodies** (`applyStartingThenStep`,
   `applyExactThenStarting`, the `HasOrderRelativeTo` predicate, or
   any non-vacuity witness for def:530B itself) this cycle. Cycle 149
   tried the sorry-first scaffold and was scored −2 because the
   operator bodies are indivisible multivariate fixed-point
   computations that cannot be decomposed into named sub-lemmas. Path
   A Step 2 (operator bodies) is cycle 152's target, AFTER `IsExplicit`
   lands in this cycle. Do NOT regress.

2. **Do NOT raise `maxHeartbeats`**. CLAUDE.md absolute rule. If any
   `IsExplicit` witness proof is slow (unlikely at s ≤ 2), decompose
   the matrix case-split, do not crank the heartbeat ceiling.

3. **Do NOT submit Aristotle for `IsExplicit` witnesses**. The
   witnesses are 2-line `fin_cases` + `rfl`/`norm_num` proofs.
   Aristotle adds latency without value at this scale.

4. **Do NOT re-poll Aristotle project
   `2c4630b2-2998-4d4a-af88-c2f83fbd9eda` before cancelling.** Cycle
   150's poll already exhausted the CLAUDE.md "one check" rule. Just
   cancel and move on.

5. **Do NOT submit a fresh Aristotle general-`n` thm:550A job.** Two
   failed long-running attempts (cycles 141 and 148) are sufficient
   evidence that the prover cannot close it without infrastructure
   work (cofactor-expansion induction or eigenvalue density). Save
   the job slot for genuinely tractable submissions.

6. **Do NOT extend the n-stepping-stone series for thm:550A to n=8**.
   Cycle 150 task results explicitly note "the seven-`n` data set is
   already strong evidence for the leading-coefficient pattern" and
   that marginal value is now low. Cycle 151's effort is better spent
   on def:530B Path A.

7. **Do NOT introduce `axiom` or `constant` declarations**. CLAUDE.md
   absolute rule. If `IsExplicit` runs into a Mathlib gap (unlikely —
   strict-lower-triangular is straightforward), file an issue rather
   than axiomatising.

8. **Do NOT modify `scripts/autonomous_loop.py`** or any loop
   infrastructure. The standing
   `tautology_scanner_false_positives.md` issue is loop-maintainer
   territory; workers do not patch it.

9. **Do NOT touch the cycle 139/141 infrastructure**
   (`GeneralizedRungeKuttaMethod`, `StartingMethod`, `IsDegenerate`,
   etc.) beyond reading. The `IsExplicit` predicate is purely
   additive — no existing definitions need changes. Touching them
   risks cascade regressions on the 8 axiom-clean witnesses already
   in §530.

10. **Do NOT use the cosmetic `h_<name>` workaround for the
    tautology scanner.** All new hypothesis names should use
    `h<name>` (no underscore) from the start to avoid scanner false
    positives — this is the standing convention from cycle 121
    (`tautology_scanner_false_positives.md`).

11. **Do NOT pivot to a different entity** (thm:541A, thm:535A,
    cor:550C, etc.) this cycle. def:530B is the highest-leverage
    target — it unblocks §530+ order theory. Cor:550C and thm:550B
    depend on the deferred general-`n` thm:550A. Other Chapter-5
    targets either depend on def:530B (e.g. def:530C) or are
    standalone but lower-impact. Stay on def:530B Path A.

## Minimum acceptable deliverable

If Priority 1's witness portfolio runs into snags (e.g.
`nontrivialTwoStageGRK`'s `A` turns out to be implicit, breaking
Witness 2, OR a structure axiom on `b` rules out the natural
`implicit2StageGRK` construction), the **minimum** acceptable
deliverable for a +2 score is:

* The `IsExplicit` predicate (axiom-clean).
* ONE positive witness (the trivial s=1 method, OR a freshly
  constructed `explicit1StageGRK` if `trivialGeneralizedRK.A 0 0 ≠ 0`).
* ONE negative witness (a freshly constructed `implicit2StageGRK` or
  similar — pick whatever satisfies the structure axioms).
* The Priority 0 Aristotle cancellation.
* The two issue-file updates (def:530B scaffold strategy + thm:550A
  general-n).

This satisfies the CLAUDE.md non-vacuity rule (at least one positive
and one negative witness, both axiom-clean), introduces no sorries,
and lays the foundation for cycle 152.

## Faithfulness check (mandatory pre-commit)

For each new `def`/`theorem` introduced this cycle:

* `IsExplicit`: not a textbook entity. Internal helper for def:530B
  Path A. Document in the docstring that this is a **strict
  refinement** of the textbook's `GeneralizedRungeKuttaMethod` —
  Butcher §530 does not single out the explicit case as a named
  predicate, but uses it implicitly when discussing methods like
  classical RK4. The docstring should make clear the strict
  lower-triangular requirement (`A i j = 0` when `i ≤ j`) is the
  Lean encoding of "no implicit stage equations".

* Each witness: tautology check (the conclusion is a `Prop` about a
  specific `M`'s `A`-entries — not a hypothesis re-export). Identity
  check (proofs are `fin_cases` + `rfl`/`norm_num`, not `exact h_*`).

* Spot-check via `lean_verify` (axiom check + source scan) on each
  named theorem before commit.

## Build verification

After Priority 1 lands, run:
```
lake env lean OpenMath/Chapter5/Section530.lean
```
Confirm clean compile (no errors, no sorry warnings).

For each new public `theorem`, refresh the cache with
```
lake build OpenMath.Chapter5.Section530
```
THEN run `#print axioms <fully-qualified-name>` (via `lean_verify`
or by reading the `.olean`). Expected:
`[propext, Classical.choice, Quot.sound]` only.

Per CLAUDE.md cycle-072 note: `lake env lean <file>` does NOT update
the `.olean` cache, so `#print axioms` against a stale cache can
report `sorryAx` false positives. ALWAYS `lake build` first.

## Suggested commit message

```
Cycle 151 — def:530B Path A Step 1: IsExplicit predicate + non-vacuity witnesses (axiom-clean)
```

(Or the minimum-deliverable variant if Witness 2 was skipped.)

## Cycle 152 preview (for context, do NOT pursue this cycle)

Path A Step 2: define `applyStartingThenStep_explicit` and
`applyExactThenStarting_explicit` taking the `IsExplicit` hypothesis,
with bodies via direct recursion on stage index — each stage `j`'s
`Y_j` is a `Finset.sum` over already-computed `Y_0, …, Y_{j-1}`.
The `IsExplicit` constraint guarantees `A i j = 0` for `j ≥ i`, so
the sum is well-defined without an implicit fixed-point. Estimated
~80-120 LOC.

Path A Step 3 (cycle 153): define `HasOrderRelativeTo_explicit` and
prove the trivial-IVP non-vacuity witness for explicit Euler ×
trivialStartingMethod with order `p = 0`. Estimated ~50-80 LOC.

Total Path A closure: cycles 151 + 152 + 153 = 3 cycles.
