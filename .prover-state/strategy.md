# Strategy — Cycle 158

## Headline

**Refactor cycles 154 + 157 i=0 closures into a shared parameterized
helper.** Extract a `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`
private lemma that captures the Taylor + Lipschitz machinery (currently
duplicated across two ~210-LOC and ~140-LOC proof bodies) and rewrite
both witnesses as one-line applications. Goal: reduce ~200 LOC of
duplication while preserving axiom-cleanliness, sorry count = 0, and
zero regressions on the §530 cycle 153/155/156 witnesses.

This is a *technical-debt reduction cycle* whose scope is narrow,
risk-bounded, and explicitly engineered to keep sorry count at 0. The
deliverable is one new helper + two refactored witnesses + updated
docstrings. **Do NOT** open new textbook entities this cycle.

## Why this target (and not the alternatives)

**Pivoting to `thm:532A`** (worker's Direction 1) is **rejected**: the
cycle 157 task results admit it "needs multi-cycle infrastructure
(rooted-tree elementary differentials from §31x or a polynomial
test-function reformulation)", and §31x is largely empty in our
codebase (`lem:310B`, `lem:311A`, `thm:311B`, `thm:311C`, `thm:311D`,
`lem:312B`, `lem:313A`, `thm:313B`, `thm:314A`, `thm:315A`, `thm:317A`
all unstarted). A single-cycle thm:532A attempt would either (a)
produce a sorry-first scaffold (blocked by the cycle 138/139 + 149/150
rollback precedents — the supervisor penalises sorry regressions
sharply) or (b) blow far past the cycle's compute budget on
infrastructure work alone. Wait for a multi-cycle plan that opens §31x
deliberately before tackling §532.

**Opening a new definition** (e.g. `def:422B`, `def:451A`, `def:442A`,
`def:381F`) is *also* rejected for cycle 158: each demands reading new
textbook context, settling new structural design decisions, and
proving non-vacuity — work that competes against the refactor for the
same compute window. Combining a new-entity deliverable with the
refactor risks producing two half-finished pieces (cf. cycle 119's
geometric-bound + Backup-B1 split, which delivered structural
narrowing but no closure). Stay focused on one clean substantive
deliverable.

**Continuing thm:550A stepping stones (n=8)** is rejected per the
cycle 150 verdict ("the seven-`n` data set is now strong enough that
further stepping stones provide marginal value; effort should
pivot") and the cycle 151 cancellation of the general-`n` Aristotle
job at 21% after 89h. Manual cofactor-expansion or eigenvalue-density
infrastructure is the only path forward — multi-cycle work, not
single-cycle.

The refactor advances *internal infrastructure* such that the next
cycle that does pivot to thm:532A (or to a Path A r=3 witness) gets a
one-line corollary instead of a 200-LOC port. It reduces the file's
current size (1600 LOC → ~1400 LOC), preserves all existing
axiom-clean theorems, and demonstrates that the Path A closure
pattern is genuinely portable. This is the lowest-risk, highest-
net-LOC-reduction cycle available right now.

## Priority 1 — Extract `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` helper

### Step 1.1 — Survey the duplication (5 min)

Open `OpenMath/Chapter5/Section530.lean` and locate the four cycle
153/154/156/157 witness theorems:

* `explicitEulerGLM_hasOrderZero_trivialStarting` (cycle 153, ~150 LOC)
* `explicitEulerGLM_hasOrderOne_trivialStarting` (cycle 154, ~210 LOC)
* `padded2DEulerGLM_hasOrderZero_padCompatStarting` (cycle 156)
* `padded2DEulerGLM_hasOrderOne_padCompatStarting` (cycle 157)

The cycle 154 and cycle 157-i=0 closures share the same machinery
(Taylor at degree 2 + Lipschitz on `f`). The cycle 153 and cycle
156-i=0 closures share a *different* (simpler) machinery (one-degree
`HasDerivAt` + Lipschitz). The cycle 156/157 closures additionally
pack a trivial i=1 channel (Diff = 0, closed via
`Asymptotics.isBigO_zero`).

The refactor target is the **cycle 154 + cycle 157-i=0 pair** (the
p=1 case). The p=0 cases (cycle 153 + cycle 156-i=0) have a
slightly different shape (T1 = o(h) instead of O(h²); single-
derivative Taylor instead of two-derivative); leave them alone this
cycle to keep scope bounded.

### Step 1.2 — Design the helper signature

The helper should abstract the closure of a **scalar SM−ES diff =
O(h²) under Lipschitz f + ContDiff ℝ 2 yex + full ODE**, given that
both `trivialStartingMethod` and `padCompatStartingMethod` (at index
0) reduce explicit-Euler-GLM × explicit-Euler-stage to the same
closed forms.

Place the helper *immediately before* the cycle 154 theorem
`explicitEulerGLM_hasOrderOne_trivialStarting` in a `private`-prefixed
section (no namespace change needed; it lives inside
`OpenMath.Chapter5.Section530`).

Proposed signature:

```lean
/-- (cycle 158) Extracted Taylor + Lipschitz closure for the explicit-
Euler-style scalar SM−ES diff at `p = 1`. Used by both
`explicitEulerGLM_hasOrderOne_trivialStarting` (cycle 154) and the
i=0 channel of `padded2DEulerGLM_hasOrderOne_padCompatStarting`
(cycle 157). -/
private theorem taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h : ℝ =>
        ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
          - (yex (x₀ + h) + h * f (yex (x₀ + h))))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
  sorry  -- proven in Step 1.3
```

The body will be the cycle 154 closure block extracted verbatim — **no
new mathematical content**. Just rename local hypothesis labels to be
self-contained (no references to outer-scope binders that don't appear
in the helper's signature).

### Step 1.3 — Prove the helper

Copy the cycle 154 T1 + T2 closure block verbatim into the helper's
body. Specifically, port the following sub-proofs from cycle 154's
`explicitEulerGLM_hasOrderOne_trivialStarting`:

* `htaylor := taylor_isLittleO …`
* `hT_eval` evaluating
  `taylorWithinEval yex 2 Set.univ x₀ (x₀+h)` via `taylor_within_apply`
  + the `simp_only` block
* `hderiv_x0 : iteratedDeriv 1 yex x₀ = f y₀` via `iteratedDeriv_one`
  + `(hyex_ode x₀).deriv` + `hyex_x₀`
* `htend := htaylor.comp_tendsto …` plus the `congr'` away the
  `((x₀+h) - x₀)^2 = h^2` conversion
* T1 decomposition into
  `taylor_remainder − (h²/2)·iteratedDeriv 2 yex x₀`
* T1 = O(h²) via `IsLittleO.isBigO` +
  `Asymptotics.isBigO_const_mul_self`
* T2 = O(h²) via `LipschitzWith.dist_le_mul` + `obtain ⟨C, hCpos, hC⟩
  := hT1.exists_pos` + `Asymptotics.isBigOWith_iff` + the eventual
  `|h| ≤ 1` argument (`Set.Ioo (-1) 1` open-set + calc chain)
* Combine via `hT1.add hT2`

Use `lake env lean OpenMath/Chapter5/Section530.lean` to verify after
each major sub-block. If the verbatim copy fails to typecheck after
the signature abstraction (e.g. due to outer-scope-binder leaks),
**don't fight it** — fall back to **Priority 1 backup** below.

### Step 1.4 — Refactor cycle 154's witness

Replace the cycle 154 theorem body with a one-line application of the
helper. Preserve the *exact* statement signature (don't change
hypothesis ordering, names, or the conclusion).

```lean
theorem explicitEulerGLM_hasOrderOne_trivialStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit explicitEulerGLM trivialStartingMethod
      (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
      explicitEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  intro i
  fin_cases i
  -- Closed-form rewrites for SM[0] and ES[0] (~30 LOC, verbatim from
  -- cycle 154's hSM + hES sub-blocks — these stay; only the T1+T2
  -- block becomes the helper invocation).
  ...
  have hcongr : (...) = (fun h => h ^ (1 + 1)) := by ring
  rw [show (fun h : ℝ => h ^ (1 + 1)) = (fun h => h ^ 2) from rfl]
  -- Apply helper:
  exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
          hf_lip hyex_x₀ hyex_C2 hyex_ode
```

Expected post-refactor LOC for this theorem: ~30–50 LOC (down from
~210 LOC). Net reduction: ~160 LOC.

### Step 1.5 — Refactor cycle 157's i=0 channel

Apply the same pattern to `padded2DEulerGLM_hasOrderOne_padCompatStarting`:

* The i=0 channel's T1+T2 block becomes the helper one-liner.
* The i=1 channel **stays as-is** (it's the cycle 156 zero-collapse
  pattern, ~30 LOC, already minimal — refactoring it is not worth
  the risk).
* The hSM/hES closed-form blocks stay verbatim (they're padCompat-
  specific and not in the helper).

Expected post-refactor LOC for this theorem: ~80 LOC (i=0 channel
~30 LOC + i=1 channel ~30 LOC + glue + fin_cases dispatch). Net
reduction from cycle 157 closure: ~140 LOC.

### Step 1.6 — Verify

Run, in order:

```bash
lake env lean OpenMath/Chapter5/Section530.lean
lake env lean OpenMath/Chapter5.lean
```

Both must exit 0 with no errors. Then `lean_verify` each of the
following four declarations to confirm
`[propext, Classical.choice, Quot.sound]` (axiom-clean):

* `OpenMath.Chapter5.Section530.taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`
* `OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderOne_trivialStarting`
* `OpenMath.Chapter5.Section530.padded2DEulerGLM_hasOrderOne_padCompatStarting`
* `OpenMath.Chapter5.Section530.padded2DEulerGLM_hasOrderOne` (the
  cycle 157 def:530C wrapper, which transitively cites the cycle 157
  witness)

Also re-verify these cycle 153/155/156 theorems remain axiom-clean
(no collateral damage):

* `explicitEulerGLM_hasOrderZero_trivialStarting`
* `padded2DEulerGLM_hasOrderZero_padCompatStarting`
* `explicitEulerGLM_hasOrderZero` (def:530C wrapper, cycle 155)
* `padded2DEulerGLM_hasOrderZero` (def:530C wrapper, cycle 156)
* `explicitEulerGLM_hasOrderOne` (def:530C wrapper, cycle 155)

Sorry count must remain at 0. Run:

```bash
grep -c sorry OpenMath/Chapter5/Section530.lean
```

Expected: `0`.

Run the project's tautology-scanner pattern to confirm no
`exact h_*` / `:= h_*` regressions were introduced:

```bash
grep -nE ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' \
  OpenMath/Chapter5/Section530.lean
```

Expected: zero hits.

### Step 1.7 — Update issue file

Edit `.prover-state/issues/def_530B_scaffold_strategy.md` and append a
"## Cycle 158 update — refactor of cycles 154+157 i=0 closures"
section noting:

* The new helper `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`.
* LOC reduction (~200 LOC).
* Both refactored witnesses remain axiom-clean.
* Path A status of def:530B/C remains `[~]` (Path B still deferred);
  `lean_status.json` does NOT change this cycle.

### Step 1.8 — Update `plan.md`

Append a brief note to the `def:530B` and `def:530C` rows in
`plan.md` indicating cycle 158 refactored the cycle 154/157 closures
into a shared helper; status remains `[~]`.

### Step 1.9 — Write `cycle_158.md`

Per CLAUDE.md, write `.prover-state/task_results/cycle_158.md`
documenting:

* What was refactored (helper extraction + two witness refactors).
* LOC delta (target: −200 LOC).
* Axiom-cleanliness preserved on all six relevant theorems.
* Sorry count: 0 → 0.
* No § 530 cycle 153/155/156 regressions.

## Priority 1 backup — Scope-down if helper signature stalls

If after **two compile attempts** the helper signature fails to
typecheck (e.g. because of dependent-type complications around
`HasOrderRelativeTo_explicit` unfolding, or because some implicit
arguments don't unify), fall back to the **partial refactor**:

1. Refactor *only* cycle 154's witness (don't touch cycle 157).
2. The helper becomes specific to `(M = explicitEulerGLM,
   S = trivialStartingMethod, p = 1)` — fully concrete signature
   instead of parameterized.
3. Net reduction: ~160 LOC (just from cycle 154).
4. File a brief follow-up note in
   `def_530B_scaffold_strategy.md` that cycle 159 should attempt the
   cycle 157 refactor with the lessons learned.

This still demonstrates the refactor approach and reduces real
duplication, even at half the planned scale.

## Priority 1 deeper backup — File issue + minimal hygiene

If even the partial refactor stalls (helper body fails to compile,
or the cycle 154 application call doesn't type-check), file an issue
at `.prover-state/issues/path_a_witness_refactor.md` documenting:

* The exact cycle 154/157 LOC pattern that was attempted.
* The compile-time obstacle (signature shape, unfolding behaviour,
  or hypothesis-pack mismatch).
* A concrete recommendation for cycle 159 (e.g. "extract the T1
  bound and T2 bound separately as two simpler helpers").

Then perform a **minimal hygiene cycle**: scan
`OpenMath/Chapter5/Section530.lean` for any `h_<name>` identifiers
that trip the tautology scanner (per
`tautology_scanner_false_positives.md`) and rename them to `hname`
form. Verify zero hits via the existing scanner pattern. This
guarantees a non-empty cycle deliverable even in the worst-case
scenario.

## What NOT to try

1. **Do NOT pivot to thm:532A.** It needs multi-cycle rooted-tree
   elementary-differential infrastructure (§31x is largely empty).
   See cycle 157 task results §"Suggested next approach" Direction
   1, which itself flagged the multi-cycle scope.

2. **Do NOT submit thm:550A general-`n` to Aristotle again.** Cycle
   141 cancelled at 6% after 24h; cycle 151 cancelled at 21% after
   89h. Two failed long-running attempts is sufficient evidence per
   `thm_550A_general_n.md`'s cycle 151 update.

3. **Do NOT add an n=8 stepping stone to thm:550A.** Cycle 150
   explicitly noted that "the seven-`n` data set is now strong
   enough that further stepping stones (n = 8) provide marginal
   value; effort should pivot."

4. **Do NOT attempt def:530B Path B (implicit branch).** Per
   `def_530B_scaffold_strategy.md`, Path B requires
   `ContractingWith` / `Function.IsFixedPt` infrastructure for
   stage-equation systems. Multi-cycle work; not yet on critical
   path.

5. **Do NOT use sorry-first scaffolds for the refactor.** The
   refactor is replacing axiom-clean code with axiom-clean code.
   Any sorry introduction is a regression, regardless of how it's
   framed (cf. cycle 138 → −2 score for a sorry-first thm:550A
   general-n; cycle 149 → −2 score for a sorry-first def:530B).
   If the helper body fails to close in one shot, scope down per
   Priority 1 backup; do NOT leave a `sorry`.

6. **Do NOT change the i=1 channel of cycle 156/157.** The
   zero-collapse pattern is already minimal (~30 LOC); refactoring
   it is not worth the risk. Keep it as-is.

7. **Do NOT extend the helper to cover cycles 153/156 (p=0
   cases).** The p=0 cases use a different smoothness assumption
   (`HasDerivAt` instead of `ContDiff ℝ 2`) and a different
   asymptotic conclusion (`o(h)` vs `O(h²)`). Parameterizing the
   helper over the Taylor degree is a separate refactor; defer to
   cycle 159+ if cycle 158 lands cleanly.

8. **Do NOT use `h_<name>` identifiers** in the new helper or the
   refactored witnesses. They trip the tautology scanner. Use
   `hname` (no underscore). See
   `tautology_scanner_false_positives.md` and the cycle 154 update
   that renamed `h_deriv → hderiv` for the same reason.

9. **Do NOT raise `maxHeartbeats` above 200000.** Cycle 150 hit a
   heartbeats wall on a 7×7 determinant simp and decomposed into
   `private lemma matrix7_oneMinusZSmul_det`. Same pattern applies
   here if the helper body times out: split into smaller private
   sub-lemmas (e.g. one for the T1 IsBigO, one for the T2 IsBigO).

10. **Do NOT open new textbook entities this cycle.** The refactor
    is the sole substantive deliverable. New-entity work + refactor
    in the same cycle risks delivering two half-finished pieces.

11. **Do NOT modify `scripts/autonomous_loop.py`.** The
    tautology-scanner false-positive bugs documented in
    `tautology_scanner_false_positives.md` remain loop-maintainer
    territory. Worker scope is the codebase under `OpenMath/`,
    `extraction/formalization_data/`, `plan.md`, and
    `.prover-state/issues/` + `.prover-state/task_results/`.

## Aristotle plan

**None this cycle.** The refactor is mechanical Lean carpentry, not
proof-search. Aristotle is poorly suited for it. With 0 sorries in
the codebase, there's nothing to submit on the closing front. Save
the Aristotle queue for cycle 159+ work that opens a new entity or
attacks a hard sorry.

## Pre-commit faithfulness checklist (apply before commit)

Per CLAUDE.md, run all of the following:

* For the new helper
  `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`:
  - **Tautology check**: ✓ — the conclusion is an asymptotic
    statement; no hypothesis is the conclusion.
  - **Identity check**: ✓ — the proof body is the cycle-154-
    extracted Taylor + Lipschitz machinery, not `exact h_*`.
  - **Hypothesis strength check**: hypotheses match cycle 154's
    exactly; do not add anything new.
  - **Absent theorem check**: no promised content elsewhere.
* For the refactored cycle 154 witness:
  - Statement signature unchanged from cycle 154 (only proof body
    differs; semantics identical).
  - Tautology / identity / strength / absent checks: same as above.
  - Faithfulness: predicate `HasOrderRelativeTo_explicit` and
    instantiation arguments unchanged.
* For the refactored cycle 157 witness (if landed):
  - Same checks as above.

Document the LOC delta and the helper extraction in
`task_results/cycle_158.md`.

## Expected scoring outcome

**Target: +2.** A clean refactor that:

* Reduces ~200 LOC of duplication from
  `OpenMath/Chapter5/Section530.lean`.
* Maintains sorry count at 0.
* Maintains axiom-cleanliness for all four affected theorems
  (cycles 154/155/156/157 + def:530C wrappers).
* Preserves cycle 153/156 theorems untouched.
* Adds one new private helper that future Path A r ≥ 3 / higher-p
  witnesses can apply as a one-liner.
* No textbook-pipeline regression.

If the partial-refactor backup (cycle 154 only) is needed, the
score expectation drops to **+1** (still a positive cycle but with
acknowledged scope reduction). If the deeper backup (file issue +
hygiene scan) is needed, the score expectation drops to **0** (no
forward progress, but a non-empty deliverable + an issue file).

## Cycle 158 LOC budget

* Target: file 1600 LOC → **~1400 LOC** (net **−200 LOC**, well
  below the +239 ceiling that has been the cycle 154/157 norm).
* Backup partial: file 1600 LOC → **~1450 LOC** (net **−150 LOC**).
* Worst-case hygiene-only: file 1600 LOC → 1600 LOC (no change to
  Section530.lean; only an issue file added at
  `.prover-state/issues/path_a_witness_refactor.md`).

## Quick-reference checklist for the worker

Before committing, confirm the following:

- [ ] `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
- [ ] `lake env lean OpenMath/Chapter5.lean` exits 0.
- [ ] `grep -c sorry OpenMath/Chapter5/Section530.lean` returns 0.
- [ ] Tautology-scanner regex returns zero hits.
- [ ] `lean_verify` returns axiom-clean for the new helper + the
      two refactored witnesses + the def:530C wrappers.
- [ ] `lean_verify` returns axiom-clean for the cycle 153/155/156
      theorems (no collateral damage).
- [ ] `def_530B_scaffold_strategy.md` updated with cycle 158 note.
- [ ] `plan.md` updated with cycle 158 note (status remains `[~]`).
- [ ] `task_results/cycle_158.md` documents the deliverable
      following the standard CLAUDE.md task-results template.
