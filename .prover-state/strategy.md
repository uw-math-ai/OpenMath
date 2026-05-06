# Cycle 162 Strategy

## Context

Cycle 161 saturated the `def:530B`/`def:530C` Path A non-vacuity grid
to `r ∈ {1, 2, 3, 4} × p ∈ {0, 1}`. **Six consecutive cycles**
(156–161) have now worked on the same pair of entities, alternating
between r-extensions (156, 157, 159, 161) and helper-extraction
refactors (158, 160). The cycle 161 worker explicitly flagged
**"diminishing returns on r = 5"** — each additional r-lift costs
≈300 LOC of duplication with no new mathematical content.

The cycle 161 task results recommended one of two paths for cycle
162:
1. r-parametric refactor (consolidate cycles 156/159/161's three
   padded GLM pairs into a single parametric family).
2. Pivot to a fresh entity from the cycle 160 candidate list.

This strategy commits to **option 1** (r-parametric refactor,
**Phase A** only). Reason: it is the highest-confidence single-cycle
deliverable, well-scoped (≈150–200 LOC), and sets up cycle 163 for a
clean parametric-witness consolidation in Phase B. After Phase B
lands, the planner pivots away from `def:530B/C` to a fresh entity —
state on these entities will then be a single parametric pair plus
inductive witnesses, instead of three hand-written pairs of
duplicated code.

## Priority 0 — pre-flight checks (5 min)

* Verify the cycle 161 commit is on the branch tip:
  ```
  git log -1 --format='%H %s'
  ```
  Expected: `8e56a89 Cycle 161 — def:530B/C Path A r = 4 × p ∈ {0, 1} witnesses (axiom-clean)`.
* Verify sorry count is 0:
  ```
  grep -c sorry OpenMath/Chapter5/Section{520,530}.lean
  ```
  Expected: `0` for both. **If non-zero**, abort the refactor and
  diagnose the regression instead.
* Spot-check that all eight cycle-161 declarations
  (`padded{2,3,4}DEulerGLM_hasOrder{Zero,One}` plus
  `padded{2,3,4}DEulerGLM_hasOrder{Zero,One}_pad{2,3,4}CompatStarting`)
  exist in `OpenMath/Chapter5/Section530.lean`.

## Priority 1 — r-parametric refactor Phase A (PRIMARY DELIVERABLE)

**Goal**: introduce a single parametric family that covers all
`r ≥ 1` and prove its basic structure lemmas axiom-clean.
**Out of scope this cycle**: parametric witnesses
(`HasOrderRelativeTo_explicit`) and reconciliation with existing
`r ∈ {1, 2, 3, 4}` instances. Both are **Phase B / cycle 163** work.

### Step 1.1 — design choice (fixed; do not deviate)

Use `r + 1` indexing rather than `r` with a hypothesis. This avoids
`NeZero` / `0 < r` pollution and makes the existing instances natural
specialisations conceptually:
- `paddedREulerGLM 0` ↔ `explicitEulerGLM` (r = 1 in old indexing)
- `paddedREulerGLM 1` ↔ `padded2DEulerGLM`
- `paddedREulerGLM 2` ↔ `padded3DEulerGLM`
- `paddedREulerGLM 3` ↔ `padded4DEulerGLM`

(Reconciliation lemmas for these correspondences are Phase B.3 work,
NOT cycle 162.)

### Step 1.2 — define the parametric GLM (Section520)

In `OpenMath/Chapter5/Section520.lean`, immediately after
`padded4DEulerGLM`, add:

```lean
/-- The `r + 1`-row padded explicit-Euler GLM (parametric family).
    Row 0 is the active explicit-Euler channel; rows 1, …, r are
    passively-decoupled zero channels. Conceptually specialises to
    `explicitEulerGLM` (at r = 0), `padded2DEulerGLM` (at r = 1),
    `padded3DEulerGLM` (at r = 2), `padded4DEulerGLM` (at r = 3).
    Reconciliation lemmas deferred to Phase B.3 (cycle 163). -/
noncomputable def paddedREulerGLM (r : ℕ) : GeneralLinearMethod 1 (r + 1) where
  A := !![0]
  U := Matrix.of fun (_ : Fin 1) (j : Fin (r + 1)) =>
         if j.val = 0 then (1 : ℝ) else 0
  B := Matrix.of fun (i : Fin (r + 1)) (_ : Fin 1) =>
         if i.val = 0 then (1 : ℝ) else 0
  V := Matrix.of fun (i j : Fin (r + 1)) =>
         if i.val = 0 ∧ j.val = 0 then (1 : ℝ) else 0
```

(Verify the field names `A`, `U`, `B`, `V` against the actual
`GeneralLinearMethod` structure in `Section510.lean` before writing —
the existing instances `padded{2,3,4}DEulerGLM` already use these
names, so this should match.)

### Step 1.3 — define the parametric starting method (Section530)

In `OpenMath/Chapter5/Section530.lean`, immediately after
`pad4CompatStartingMethod` (and its support theorems), add:

```lean
/-- The `r + 1`-method starting family compatible with
    `paddedREulerGLM r`. Index 0 is the active
    `trivialGeneralizedRK` channel; indices 1, …, r are
    passively-decoupled `zeroGeneralizedRK` channels. -/
noncomputable def padCompatMethodR (r : ℕ) :
    Fin (r + 1) → GeneralizedRungeKuttaMethod 1 :=
  fun i => if i.val = 0 then trivialGeneralizedRK else zeroGeneralizedRK

noncomputable def padCompatStartingMethodR (r : ℕ) : StartingMethod (r + 1) where
  stages := fun _ => 1
  method := padCompatMethodR r
```

(Again, verify the `StartingMethod` field names against
`Section530.lean`'s existing definition.)

### Step 1.4 — prove the four basic structure lemmas

In `OpenMath/Chapter5/Section530.lean`, after the definitions in
Step 1.3, add **exactly four** axiom-clean theorems matching the
shape of the existing `pad{2,3,4}` infrastructure:

1. **`paddedREulerGLM_isExplicit`** —
   ```lean
   theorem paddedREulerGLM_isExplicit (r : ℕ) :
       (paddedREulerGLM r).IsExplicit
   ```
   The `A`-block is `!![0]` (1×1), so the strict-lower-triangular
   condition is vacuous on `Fin 1`. Proof template:
   `intro i j _; fin_cases i; fin_cases j; rfl`. (Mirrors
   cycle 161's `padded4DEulerGLM_isExplicit` exactly — the `A`-block
   is identical across all r.)

2. **`padCompatStartingMethodR_isNonDegenerate`** —
   ```lean
   theorem padCompatStartingMethodR_isNonDegenerate (r : ℕ) :
       (padCompatStartingMethodR r).IsNonDegenerate
   ```
   Use the helper `StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero`
   (the bridge cycles 156/159/161 used). Witness at `i := ⟨0,
   Nat.succ_pos r⟩` with `b₀ = 1` from `trivialGeneralizedRK`.
   Proof sketch:
   ```lean
   refine StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero.mpr
     ⟨⟨0, Nat.succ_pos r⟩, ?_⟩
   simp [padCompatStartingMethodR, padCompatMethodR,
         trivialGeneralizedRK]
   ```

3. **`padCompatStartingMethodR_constituents_isExplicit`** —
   ```lean
   theorem padCompatStartingMethodR_constituents_isExplicit (r : ℕ) :
       ∀ i, ((padCompatStartingMethodR r).method i).IsExplicit
   ```
   Case-split on `i.val = 0`:
   ```lean
   intro i
   by_cases hi : i.val = 0
   · simp [padCompatStartingMethodR, padCompatMethodR, hi]
     exact trivialGeneralizedRK_isExplicit
   · simp [padCompatStartingMethodR, padCompatMethodR, hi]
     intro a b _
     fin_cases a; fin_cases b; rfl
   ```
   (The 1×1 strict-lower-triangular case for `zeroGeneralizedRK`
   closes vacuously; cycles 156/159/161 used the same shape.)

4. **`padCompatStartingMethodR_applyExplicit`** —
   ```lean
   theorem padCompatStartingMethodR_applyExplicit (r : ℕ)
       (f : ℝ → ℝ) (h y₀ : ℝ) :
       (padCompatStartingMethodR r).applyExplicit
         (padCompatStartingMethodR_constituents_isExplicit r)
         f h y₀
       = fun i => if i.val = 0 then y₀ + h * f y₀ else 0
   ```
   `ext i; by_cases hi : i.val = 0`. At `i.val = 0`, cite
   `trivialGeneralizedRK_explicitApply` (cycle 152). At `i.val ≠ 0`,
   cite the cycle 156 private helper `zeroGeneralizedRK_explicitApply`.
   The exact `simp` set should mirror what cycles 156/159/161 used
   for `pad{2,3,4}CompatStartingMethod_applyExplicit`. Verify the
   helper name `zeroGeneralizedRK_explicitApply` is reachable (it is
   private to Section530 per the cycle 156 update).

### Step 1.5 — verification (per declaration)

After each declaration, immediately:
1. `lake env lean OpenMath/Chapter5/Section530.lean` — exit 0.
2. `lean_verify` (MCP) on the just-added declaration — confirm
   `[propext, Classical.choice, Quot.sound]` ONLY.
3. **If `sorryAx` appears** (or any non-standard axiom), STOP and
   diagnose. Do NOT commit with sorries (cycle 138/149 rollback
   precedent).

After all four are clean:
```
lake env lean OpenMath/Chapter5/Section520.lean
lake env lean OpenMath/Chapter5/Section530.lean
lake env lean OpenMath/Chapter5.lean
grep -c sorry OpenMath/Chapter5/Section{520,530}.lean   # both → 0
```

### Step 1.6 — commit and update state files

* Update `extraction/formalization_data/lean_status.json` rows for
  `def:530B` and `def:530C`: bump `cycle` to 162. **Status remains
  `partial`** (Path B implicit branch still deferred; Phase A is
  parametric infrastructure, not full closure).
* Update `plan.md` rows for `def:530B` and `def:530C` to reflect
  the cycle 162 parametric infrastructure landing (one bullet each
  at the end of the existing summary).
* Update `.prover-state/issues/def_530B_scaffold_strategy.md` with
  a new "Cycle 162 update" section noting the parametric refactor
  Phase A landing and the deferred Phase B (parametric witness
  consolidation + reconciliation lemmas — see Priority 2 below).
* Commit message:
  `Cycle 162 — def:530B/C Path A r-parametric infrastructure (Phase A, axiom-clean)`.

## Priority 2 — Phase B planning notes (DO NOT IMPLEMENT THIS CYCLE)

Document for cycle 163 in the issue file update of Step 1.6:

* **Phase B.1**: parametric witnesses
  `paddedREulerGLM_hasOrderZero_padCompatStartingR (r : ℕ)` and
  `_hasOrderOne_padCompatStartingR (r : ℕ)`. Closure via case-split
  on `i.val = 0`: at `i.val = 0`, one-line invocation of cycle
  158/160's Taylor + Lipschitz helpers; at `i.val ≠ 0`,
  zero-collapse via `Asymptotics.isBigO_zero`. Estimated ~150–250
  LOC.
* **Phase B.2**: parametric `def:530C` wrappers
  `paddedREulerGLM_hasOrderZero (r : ℕ)` and `_hasOrderOne (r : ℕ)`,
  trivial corollaries citing Phase B.1.
* **Phase B.3** (optional / stretch): reconciliation lemmas
  `paddedREulerGLM_zero_eq_explicitEulerGLM`,
  `paddedREulerGLM_one_eq_padded2DEulerGLM`, etc. Likely close by
  `rfl`/`ext + simp` since the matrix bodies match definitionally
  modulo `Fin (r+1)` ↔ `Fin {1,2,3,4}` indexing. Ship only if they
  close cleanly; do not block on them.

After Phase B lands cleanly, the planner pivots to a fresh entity
(see backup pivot candidate list at the bottom of this file).

## What NOT to do this cycle

1. **Do NOT attempt r = 5 lift.** The cycle 161 worker confirmed
   diminishing returns; further hand-written `padded5DEulerGLM`
   instances add zero mathematical content and contradict this
   strategy's commitment to consolidation.

2. **Do NOT introduce sorries.** The cycle 138 (`thm:550A` general-n
   sorry-first scaffold) and cycle 149 (`def:530B` operator-body
   sorry-first scaffold) rollback precedent is in force. The four
   lemmas in Priority 1 Step 1.4 are mechanical structural facts
   that can and must be closed axiom-clean within the cycle.

3. **Do NOT attempt the parametric witnesses
   (`HasOrderRelativeTo_explicit`) this cycle.** That is Phase B.1.
   The cycle-153/154 closure work shows the witnesses themselves
   take 200+ LOC each. Combined with Phase A's 150–200 LOC,
   attempting both in one cycle exceeds a comfortable single-cycle
   budget and risks a stalled commit.

4. **Do NOT attempt to replace existing `r ∈ {1, 2, 3, 4}`
   instances** with corollaries of the parametric family this cycle.
   Reconciliation is Phase B.3. Let the parametric family **coexist**
   with the existing instances.

5. **Do NOT pivot to a fresh entity (e.g. `def:451A`, `def:422B`)
   yet.** This strategy commits to the refactor. The pivot is queued
   for cycle 164+ (after Phase B closes). See the backup candidate
   list at the end of this file.

6. **Do NOT modify any of cycles 138–161's existing helpers or
   theorems.** The parametric family is purely additive
   infrastructure; touching the existing axiom-clean witnesses
   risks regressions.

7. **Do NOT modify `scripts/autonomous_loop.py`** (worker rule). If
   the tautology-scanner regex flags any of the four new lemmas,
   apply the standard cosmetic rename `h_<name>` → `h<name>` per
   `.prover-state/issues/tautology_scanner_false_positives.md`.

8. **Do NOT raise `maxHeartbeats` above 200000.** If a `simp; ring`
   times out on `padCompatStartingMethodR_applyExplicit` (the most
   `simp`-heavy of the four), decompose by adding a private helper
   that handles the `i.val = 0` case separately, like cycles
   156/159/161 did.

## Failed approaches to avoid (from `attempts` history)

* **Sorry-first scaffold for new definitions** — cycles 138 (thm:550A
  general-n) and 149 (def:530B operator bodies) both regressed
  because a sorry was added without a clear single-cycle closure
  path. Phase A's four lemmas are all closable in this cycle by
  direct construction; do NOT scaffold any of them with sorry.
* **Aristotle for parametric structural lemmas** — historical
  Aristotle performance on parametric `Fin`-indexed sums and
  decidable-equality case splits has been weak (cycle 141 cancelled
  at 6%, cycle 148 still IN_PROGRESS at 18% as of cycle 150 poll —
  see `thm_550A_general_n.md`). Do NOT submit Phase A lemmas to
  Aristotle; close them manually.
* **`Fin.sum_univ_<n>` for parametric `r`** — these fire only at
  concrete `n`. For parametric `r + 1`, use
  `Finset.sum_eq_single 0 ... ...` or `Fin.sum_univ_succ` /
  `Finset.sum_ite_eq` family instead.
* **`fin_cases i` for parametric `Fin (r + 1)`** — same issue.
  Use `by_cases h : i.val = 0` (with `omega` discharge of side
  obligations) or `Fin.cases` / `Fin.induction` for case splits.
* **Definitional equality reliance for reconciliation** —
  `paddedREulerGLM 1 = padded2DEulerGLM` is NOT `rfl` in general
  (the `Matrix.of`-based body vs `!![..]` body unfold differently).
  Don't rely on it; the reconciliation is Phase B.3.

## Backup plan (only if Phase A's design hits a structural blocker)

If, while implementing Step 1.4, a structural blocker appears that
is genuinely irresolvable in this cycle (NOT just slow Lean
elaboration — that's what `decide` / `simp` / `omega` tuning is for):

* **Backup A1**: scope down to **Steps 1.2 + 1.3 only** (definitions
  without structure lemmas). Land the parametric family as a
  sorry-free definition; defer all four lemmas to cycle 163.
  Phase B then becomes Phase B.0 (the four lemmas) + Phase B.1/2/3
  as originally planned. Cycle score likely +1 (clean partial);
  cycle 163 picks up smoothly.

* **Backup A2** (only if A1 also fails — unlikely): pivot
  immediately to **`def:451A` G-stable** (Chapter 4 §451). First
  step: read `extraction/formalization_data/entities/def_451A.json`
  to determine textbook content. If the definition involves a
  positive-definite matrix `G` and a one-leg method, the LMM
  infrastructure in `OpenMath/Chapter4/Section404.lean` should
  suffice for a single-cycle definition + non-vacuity witness.
  This is genuinely a cycle 164+ task per Priority 2's "pivot to a
  fresh entity" plan; doing it under Backup A2 is suboptimal but
  acceptable.

* **Backup A3** (last resort): document the structural blocker as a
  new issue file `.prover-state/issues/r_parametric_<descriptor>.md`,
  revert any partial Phase A code so the file builds clean, and
  submit a cycle that LANDS THE ISSUE FILE (zero new sorries; no
  Lean-content advance, but documents the dead end for cycle 163).

## Mathlib hooks (Phase A only)

| Goal | Lemma |
|---|---|
| Specialise `Matrix.of` to entries | `Matrix.of_apply` |
| Sum with one non-zero entry | `Finset.sum_eq_single` |
| Indicator-style `if`-sums | `Finset.sum_ite_eq` / `Finset.sum_ite_eq'` |
| Case-split on `Fin (r+1)` | `Fin.cases`, or `by_cases h : i.val = 0` |
| `0 < r + 1` | `Nat.succ_pos r` |
| Non-degeneracy bridge | `StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero` (existing helper, used by cycles 156/159/161) |
| `b₀ ≠ 0` for `trivialGeneralizedRK` | unfolds to `(1 : ℝ) ≠ 0` |
| Index-0 closed-form | `trivialGeneralizedRK_explicitApply` (cycle 152) |
| Index-`> 0` closed-form | `zeroGeneralizedRK_explicitApply` (private helper, cycle 156) |

## Expected cycle 162 deliverable shape

* **Files modified**:
  - `OpenMath/Chapter5/Section520.lean` (one new `def`).
  - `OpenMath/Chapter5/Section530.lean` (two new `def`s + four new
    `theorem`s).
  - `extraction/formalization_data/lean_status.json` (cycle bumps
    on `def:530B`, `def:530C`).
  - `plan.md` (one bullet each on the `def:530B` and `def:530C`
    rows).
  - `.prover-state/issues/def_530B_scaffold_strategy.md` (cycle 162
    update + Phase B planning notes).
* **LOC delta**: +150 to +200 LOC, concentrated in
  `Section530.lean`.
* **Sorry count**: 0 → 0 (unchanged).
* **Axiom check**: all four new theorems report
  `[propext, Classical.choice, Quot.sound]` only.
* **Tautology scanner**: clean.
* **Path A status of `def:530B/C`**: still `[~]` (parametric
  infrastructure landed; parametric witnesses deferred to cycle
  163; Path B implicit branch still deferred).

## Plan progress impact and post-Phase-B pivot queue

This cycle does NOT advance `plan.md`'s 69/175 entity count (no new
`[x]` entities). Cycle 162's contribution is **structural
consolidation**, valued at the same level as the cycle 158/160
helper-extraction refactors (likely supervisor score +1).

The pivot to a fresh entity comes after cycle 163's Phase B closes.
**Candidate list for cycle 164+** (in approximate order of estimated
tractability — NOT to be acted on this cycle):

1. **`def:451A` G-stable** (§451, Chapter 4 LMM). Definition +
   non-vacuity witness. Estimated 1 cycle.
2. **`def:422B` underlying one-step method** (§422, Chapter 4 LMM).
   Definition + companion theorem (`thm:422A`). Estimated 1–2
   cycles.
3. **`def:442A` principal sheet** (§441, Chapter 4 LMM).
   Definition. Estimated 1 cycle.
4. **`thm:535A` underlying one-step method (GLM)** (§535,
   Chapter 5). Theorem; analog of `thm:422A` but at the GLM level.
   Estimated 2 cycles.
5. **`thm:541A` types of DIMSIM methods** (§541, Chapter 5).
   Classification theorem. Estimated 2–3 cycles.

Cycle 163's planner should pick the top tractable candidate after
Phase B lands. Worker should **not** scout these candidates this
cycle.
