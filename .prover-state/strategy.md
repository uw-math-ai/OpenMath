# Cycle 109 Strategy — Course-correct cycle 108: drop sorry count from 3 back to ≤ 2

## Context recap (course correction after cycle 108 -2 score)

Cycle 108 opened the §515 capstone `thm:515D` with a sorry-first
scaffold. The strategy budget allowed at most **2 named sub-lemma
sorries + an inline `u ≠ 0` proof for `s = 0`**. The cycle landed:

* `aux_515D_output_tendsto` — sorry at `Section515.lean:1504` ✓
* `aux_515D_stage_tendsto` — sorry at `Section515.lean:1544` ✓
* Inline `s = 0` branch — **3rd sorry at `Section515.lean:1594`** ✗

The third sorry was over-budget. The cycle was scored **-2 (REVERTED)**
because sorry count went 0 → 3.

Root cause (per `task_results/cycle_108.md` "Discovery"): the
strategy's recommended one-liner
`(M.U *ᵥ u : Fin s → ℝ) = 0 ⇒ contradiction` does **not** go through
when `s = 0`, because `(fun _ : Fin 0 => 1)` and `(0 : Fin 0 → ℝ)` are
both the empty function and extensionally equal. So `IsConsistent` does
not constrain `u ≠ 0` when `s = 0`, and the IsConvergent statement is
genuinely degenerate (in fact False for `(s, r) = (0, 0)`). See
`.prover-state/issues/thm_515D_s_zero_degenerate.md` for the full
analysis with Options A–D.

**Cycle 109's job**: bring sorry count back DOWN. The minimum
acceptable deliverable is **3 → 2 sorries**, with a stretch goal of
**3 → 1**. Priority 1 alone clears the floor.

The commit `6c7b6a3` IS on the branch — this is *not* a
commit-not-reaching-repo failure. The "Sorry locations" list in the
prompt is the literal post-cycle-108 file state. Do not chase phantom
push failures (per `consultant_advice_cycle_009.md` §A and
`consultant_advice_cycle_015.md` §B).

---

## Priority 1 (REQUIRED) — Add `(hs : 0 < s)` precondition to eliminate the inline `s = 0` sorry

**Goal**: Apply Option D of `thm_515D_s_zero_degenerate.md` —
strengthen the theorem signature with an `s ≥ 1` hypothesis. This is
the smallest, least-invasive fix and brings sorry count from 3 → 2.

**Justification**: Butcher §515 implicitly assumes the GLM has at
least one internal stage. The abscissae `c = A·𝟙 + U·v` analyzed in
lem:515A are vacuous (empty function) when `s = 0`, and the entire
§515 narrative concerns RK-style methods with at least one stage.
Adding `0 < s` is the smallest faithfulness divergence and the
cleanest fix. (For `(s, r) = (0, 0)` the IsConvergent statement is
literally False because `Fin 0 → ℝ` has only the zero inhabitant, so
`u ≠ 0` is impossible — the textbook's flat statement is therefore
also incorrect at that corner case, and our divergence is just
making this explicit.)

### Concrete edits

1. **`OpenMath/Chapter5/Section515.lean:1566–1594`** — replace
   `stable_consistent_isConvergent` with:

   ```lean
   theorem GeneralLinearMethod.stable_consistent_isConvergent
       {s r : ℕ} (hs : 0 < s) (M : GeneralLinearMethod s r)
       (hStab : M.IsStable) (hCons : M.IsConsistent) :
       M.IsConvergent := by
     intro f L hf_lip x₀ y₀ yex hyex_x₀ hyex_ode
     obtain ⟨u, v, ⟨hVu, hUu⟩, hCons_eq⟩ := hCons
     refine ⟨u, ?_, ?_⟩
     · -- u ≠ 0: evaluate `U·u = 𝟙` at index `⟨0, hs⟩`.
       intro hu0
       have h1 : (M.U *ᵥ u) ⟨0, hs⟩ = (fun _ : Fin s => (1 : ℝ)) ⟨0, hs⟩ :=
         congrFun hUu ⟨0, hs⟩
       rw [hu0] at h1
       simp [Matrix.mulVec, dotProduct] at h1
     · intro φ hφ x hxx Y Y_int hY_props
       refine ⟨?_, ?_⟩
       · exact aux_515D_output_tendsto M hStab hf_lip hyex_x₀ hyex_ode
                 hVu hUu hCons_eq hφ hxx Y Y_int hY_props
       · exact aux_515D_stage_tendsto M hStab hf_lip hyex_x₀ hyex_ode
                 hVu hUu hCons_eq hφ hxx Y Y_int hY_props
                 -- + h_output if Priority 2 lands; see Step 2a.
   ```

   Drop the `by_cases hs` and the `s = 0` branch entirely (the
   inline sorry at line 1594 disappears).

2. **Update the docstring** at lines 1546–1565 to add a divergence
   note:

   > **Faithfulness divergence**: the hypothesis `hs : 0 < s` is a
   > strengthening of Butcher's flat statement. The textbook
   > implicitly assumes the GLM has at least one internal stage —
   > the `s = 0` case is genuinely degenerate (for `(s, r) = (0, 0)`
   > the IsConvergent statement is vacuously False since `Fin 0 → ℝ`
   > has only the zero inhabitant). See
   > `.prover-state/issues/thm_515D_s_zero_degenerate.md` for the
   > full analysis.

3. **`extraction/formalization_data/lean_status.json`** — update
   `thm:515D` notes:

   * Replace any cycle-108 "scaffold + 3 sorries" wording with
     "scaffold + 2 sorries (cycle 109; `0 < s` precondition added)".
   * Status remains `partial` (not `formalized`) until both
     sub-lemmas close.

4. **`.prover-state/issues/thm_515D_s_zero_degenerate.md`** — prepend
   a `## Resolution (cycle 109) — RESOLVED via Option D` section
   citing the precondition addition. Move past Status and What was
   tried sections accordingly. Do **not** delete the issue file —
   keep as a record of the divergence.

### Verification

* `lake env lean OpenMath/Chapter5/Section515.lean` — clean compile,
  warnings only for the two remaining `sorry`s at lines 1504 and
  1544.
* `lake build OpenMath.Chapter5.Section515` — refresh `.olean`.
* `#print axioms
  OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`
  — should still show `[propext, sorryAx, Classical.choice, Quot.sound]`
  (sorryAx persists until both sub-lemmas close).
* `grep -rn "stable_consistent_isConvergent" OpenMath/` — confirm
  no callers outside the file itself need updating.

**Floor deliverable**: this priority alone takes the cycle from
3 → 2 sorries. **Do not skip Priority 1 even if Priority 2 stalls.**

---

## Priority 2 (TARGET) — Close `aux_515D_stage_tendsto` after refactoring its signature

**Goal**: Refactor the stage sub-lemma to take output convergence as
an explicit hypothesis, then close its proof. Net sorry change:
2 → 1 if it lands cleanly.

**Why this works now**: `aux_515D_stage_tendsto`'s proof needs the
output convergence `Y n n → fun i => u i * yex x` (per
`task_results/cycle_108.md` "Suggested next approach" §2). Currently
the lemma is parameterized on the same hypotheses as
`aux_515D_output_tendsto` and would have to *re-derive* output
convergence internally — duplicating the hardest part of cycle 110+'s
work. Cleaner split: pass output convergence as a hypothesis. Then
the stage proof reduces to the linear-algebra limit:
(a) bound `Y_int` from the stage equation via Lipschitz of `f`,
(b) show `h_n · f(Y_int n j) → 0`,
(c) take limits using `Matrix.mulVec` continuity + `U·u = 𝟙`.

### Step 2a — Refactor the signature

**`OpenMath/Chapter5/Section515.lean:1522–1544`** — modify
`aux_515D_stage_tendsto` to take `h_output` as a final parameter:

```lean
private theorem aux_515D_stage_tendsto {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (_hStab : M.IsStable)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (_hyex_x₀ : yex x₀ = y₀)
    (_hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x)
    {u v : Fin r → ℝ}
    (_hVu : M.V *ᵥ u = u) (hUu : M.U *ᵥ u = (fun _ => 1))
    (_hCons_eq : M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v)
    {φ : ℝ → Fin r → ℝ}
    (_hφ : ∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                          (nhds 0) (nhds (u i * y₀)))
    {x : ℝ} (hxx : x₀ < x)
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (hY_props : ∀ n : ℕ, 0 < n →
      Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
      M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n) ∧
      (∀ i, Y_int n i =
              (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
              + (∑ j, M.U i j * Y n n j)))
    (h_output : Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
                  (nhds (fun i => u i * yex x))) :
    Filter.Tendsto Y_int Filter.atTop (nhds (fun _ => yex x)) := by
  ...
```

Update the call site in `stable_consistent_isConvergent` (Priority 1
edit): bind a `let h_output := aux_515D_output_tendsto …`, then pass
to `aux_515D_stage_tendsto`. (See call-site comment in Step 1.)

### Step 2b — Close the proof

The proof reduces, entrywise, to: `Y_int n i = T1(n,i) + T2(n,i)`
where T1 → 0 and T2 → yex x. Lift to function-valued convergence
via `tendsto_pi_nhds.mpr`.

**(i) Eventual stage boundedness — `aux_515D_stage_eventually_bounded`**

**Decision: defer this as a `sorry`'d helper for cycle 110.**

Why: bounding `|Y_int n i|` from the implicit stage equation
requires inverting `(I − h_n L · |A|)`, the same M-matrix flavour
that cycle 105–107 built for `aux_515B_eta_contraction`. The
infrastructure exists (`Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`
in `OpenMath/Chapter5/MMatrix.lean`) but adapting it to a *limit*
statement (`∃ N K, ∀ n ≥ N, ∀ i, |Y_int n i| ≤ K`) is non-trivial:
need to choose `N` so that `h_n · L · ‖|A|‖` is small enough for the
Neumann series, then bound the RHS uniformly.

**Concrete deferral**: add a private sorry'd helper

```lean
private theorem aux_515D_stage_eventually_bounded {s r : ℕ}
    (M : GeneralLinearMethod s r)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {x₀ x : ℝ} (hxx : x₀ < x)
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (hY_props : ∀ n : ℕ, 0 < n →
      ∀ i, Y_int n i =
              (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
              + (∑ j, M.U i j * Y n n j))
    (h_output : Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
                  (nhds (fun i => sorry)))  -- u·yex x; pass this through
    : ∃ K : ℝ, ∀ᶠ n in Filter.atTop, ∀ i, |Y_int n i| ≤ K := by
  sorry
```

(Tighten the signature to accept `(fun i => u i * yex x)` directly
as the convergence target, taking `u : Fin r → ℝ` as a free
variable — keeps the helper reusable.)

This is **+1 sorry**, balanced by Priority 2 closing the
`aux_515D_stage_tendsto` sorry, **net 2 → 2**. Even at net-2 the
cycle is a positive course-correction (3 → 2).

### Stretch refinement (only if budget remains after Steps 2a-2b)

Try a *direct* boundedness argument that avoids the M-matrix
infrastructure: take `n` large enough that `h_n · L · ‖A‖_∞ ≤ 1/2`
(simple choice from `tendsto_one_div_atTop_nhds_zero` applied to
`h_n = (x - x₀)/n`), then derive the bound via a max-rearrangement
on `Fin s`:

```
max_i |Y_int n i| ≤ h_n L ‖A‖_∞ · max_i |Y_int n i|
                  + h_n |f(0)| ‖A‖_∞ + ‖U·Y n n‖_∞
                  ≤ ½ max_i |Y_int n i| + (bounded RHS)
```
giving `max_i |Y_int n i| ≤ 2 · (h_n |f(0)| ‖A‖_∞ + ‖U·Y n n‖_∞)`,
which is bounded by hypothesis. ~50–80 LOC. **Try this first; if it
balloons past 80 LOC, defer to the sorry'd helper above.**

**(ii) First summand vanishes**

Given the bound `|Y_int n i| ≤ K` eventually, Lipschitz of `f`
gives `|f(Y_int n j)| ≤ |f 0| + L · K`. Then

```
|h_n · ∑_j M.A i j * f(Y_int n j)| ≤ h_n · ∑_j |M.A i j| · (|f 0| + L K)
                                    ≤ h_n · (|f 0| + L K) · ∑_j |M.A i j|
                                    → 0
```

since `h_n = (x - x₀) / n → 0`. Mathlib lemmas:
* `tendsto_one_div_atTop_nhds_zero` (or
  `Filter.Tendsto.const_mul` + `tendsto_natCast_atTop_atTop` chain)
  for `h_n → 0`.
* `Filter.Tendsto.const_mul` to multiply by the bound constant.
* `Filter.Tendsto.eventually_le` / `Filter.Eventually.mono` to
  combine with the boundedness lemma.

**(iii) Second summand limit**

By `h_output` and continuity of `Matrix.mulVec`:

```
M.U *ᵥ Y n n → M.U *ᵥ (fun i => u i * yex x).
```

Then by linearity of `mulVec`:

```
M.U *ᵥ (fun i => u i * yex x)
  = (fun i => yex x * (M.U *ᵥ u) i)        -- linearity
  = (fun i => yex x * 1)                     -- by hUu
  = (fun _ => yex x).
```

**Mathlib lemmas to cite**:
* `Continuous.tendsto` for `Matrix.mulVec` continuity. Verify the
  exact name with `lean_local_search` first; candidates:
  - `Matrix.mulVec_continuous` (if it exists in
    `Mathlib.LinearAlgebra.Matrix.ToLin` or
    `Mathlib.Topology.Algebra.Module.Basic`).
  - Fallback: prove `Continuous (M.U *ᵥ ·)` inline as a finite sum
    of continuous coordinate maps:
    `(M.U *ᵥ y) i = ∑ j, M.U i j * y j` is continuous in `y`
    because each `y ↦ y j` is continuous (`continuous_apply j`)
    and finite sums/products of continuous maps are continuous.
  - Verify: `lean_local_search "Matrix.*mulVec.*[Cc]ontinuous"`,
    `lean_loogle "Continuous (Matrix.mulVec _)"`.
* For the linearity rewrite: `funext i; simp [Matrix.mulVec,
  dotProduct, Finset.mul_sum]; ring` should close it after pulling
  `yex x` out of the dot product.

**(iv) Combine**

```lean
rw [tendsto_pi_nhds]
intro i
have hT1 : Filter.Tendsto (fun n => h_n n · ∑ j, …) atTop (nhds 0) := …  -- step (ii)
have hT2 : Filter.Tendsto (fun n => (M.U *ᵥ Y n n) i) atTop (nhds (yex x)) := …  -- step (iii)
have hSum := hT1.add hT2
-- Rewrite Y_int n i = T1 + T2 via hY_props.
convert hSum using 1
· ring  -- 0 + yex x = yex x
· funext n  -- pointwise sum
  rcases Nat.lt_or_ge 0 n with h | h
  · exact (hY_props n h).2.2 i
  · sorry  -- handle the n = 0 edge case via Filter.Tendsto.congr' eventually
```

For the `n = 0` edge case, use `Filter.Tendsto.congr'` with the
eventual filter `{n | 0 < n}` (which is in `atTop`). This avoids
needing `hY_props` at `n = 0` (where it's not provided).

**Estimated effort**: ~150–200 LOC if direct boundedness lands,
~120–150 LOC if boundedness is deferred to a sorry'd helper.

### Net cycle outcome scenarios

| Scenario | Sorries delta |
|---|---|
| Priority 1 only | 3 → 2 |
| Priority 1 + Priority 2 with deferred boundedness helper | 3 → 2 (refactored) |
| Priority 1 + Priority 2 with inline boundedness | 3 → 1 |

All three scenarios are positive course-corrections from the -2
cycle 108 score. Aim for the third; settle for either of the
first two.

---

## Priority 3 (DEFERRED — do NOT attempt this cycle)

Decomposing `aux_515D_output_tendsto` into smaller named helpers
would mirror the LMM cycle 064–068 chain at
`OpenMath/Chapter4/Section404.lean:1300+` (`globalError_recurrence_bound`,
`globalError_recurrence_bound_textbook`, `globalError_per_step_sum_form`,
`globalError_recurrence_form_explicit`, plus `discrete_gronwall_exp_bound`).
But each helper is a sorry-first scaffold, and net opening 4 new
sorries in a course-correction cycle is unacceptable.

**Default**: skip Priority 3 entirely. Save it for cycle 110+.
The trajectory below sketches when to take this on.

---

## What NOT to do this cycle

* **DO NOT** reattempt the cycle-108 inline `s = 0` proof. It is
  genuinely impossible without strengthening the signature; see
  cycle-108 task results §"Dead ends".
* **DO NOT** modify `aux_515D_output_tendsto`'s signature or proof
  this cycle (other than the call-site update for Priority 2 to
  capture its result for `h_output`). Decomposition is cycle 110+
  work.
* **DO NOT** introduce Aristotle batches for `aux_515D_output_tendsto`
  this cycle. Aristotle has historically struggled with discrete
  Grönwall + squeeze arguments (cycle 094/096 evidence in
  `consultant_advice_cycle_040.md` §C). Hold for cycle 110+ when
  the helper decomposition lands.
* **DO NOT** add new top-level `def` or `structure`. Only signatures
  and proofs of existing lemmas change, plus possibly one new
  private helper (`aux_515D_stage_eventually_bounded`).
* **DO NOT** raise `maxHeartbeats` above 200000.
* **DO NOT** introduce `axiom` / `constant` declarations.
* **DO NOT** poll Aristotle more than once (per CLAUDE.md). The
  cycle-108 batch (`40554853-18b3-424c-81e4-2a2fae9e57c4`) is the
  only outstanding submission.
* **DO NOT** delete the issue file
  `.prover-state/issues/thm_515D_s_zero_degenerate.md`. Mark it
  RESOLVED by adding a "## Resolution (cycle 109)" section; keep
  the analysis as a record.
* **DO NOT** treat the prompt's "REVERTED" verdict as evidence of
  a commit-not-reaching-repo failure. Cycle 108's commit `6c7b6a3`
  IS on the branch (the "Sorry locations" list in the prompt is
  the literal post-cycle-108 file state). The -2 score reflects
  sorry-count regression, not a missing commit. If in doubt,
  verify with `git rev-parse HEAD` vs
  `git rev-parse origin/Main/Experiments`. This is the standing
  "phantom commit-failure" pattern from
  `consultant_advice_cycle_009.md` §A.

---

## Aristotle plan

**Step 1 — Status check on cycle-108 batch** (one poll only):

```
mcp__aristotle__get_status project_id="40554853-18b3-424c-81e4-2a2fae9e57c4"
```

**Branching**:

* **Completed with proofs returned**:
  * For `aux_515D_stage_tendsto`: incorporate iff the proof
    matches the **refactored** signature (Priority 2 Step 2a). If
    Aristotle's proof predates the refactor, discard — the original
    signature is being retired.
  * For `aux_515D_output_tendsto`: keep the sorry; that lemma is
    cycle 110+ work.
* **Still `IN_PROGRESS` at < 30%**: ignore. Do not block. Do not
  submit a new batch this cycle.
* **Completed with no useful proofs**: cancel the project to free
  the queue (`mcp__aristotle__cancel_project`). Then proceed
  manually with Priority 2.

**Step 2 — Do NOT submit a fresh batch this cycle.** Priority 2's
proof shape (Lipschitz boundedness + matrix continuity + sum-of-
limits) is too specific for Aristotle to handle cleanly. Manual
work has higher hit rate.

---

## Pre-commit faithfulness checklist

Before committing, run the CLAUDE.md checklist on every changed
declaration:

### `stable_consistent_isConvergent` (modified)

1. **Quote textbook statement** from `entities/thm_515D.json`:
   "A stable and consistent general linear method is convergent."
2. **Lean signature**: `M.IsStable` + `M.IsConsistent` in,
   `M.IsConvergent` out, plus `(hs : 0 < s)`.
3. **Faithfulness divergence**: Document `(hs : 0 < s)` in the
   docstring with rationale + link to issue. Captured: same content
   as textbook, with a clarifying domain restriction.
4. **Tautology check**: hypotheses ≠ conclusion. ✓
5. **Identity check**: proof uses `obtain` / `refine` / dispatch.
   Not a single `exact`. ✓
6. **Hypothesis strength**: `0 < s` is a strengthening; documented.
   Stab + Cons unchanged.
7. **Absent theorem check**: docstring promises `aux_515D_output_tendsto`
   and `aux_515D_stage_tendsto`; both still exist (with sorry's
   for the former, closed proof for the latter if Priority 2 lands).

### `aux_515D_stage_tendsto` (modified, if Priority 2 closes)

1. Internal helper — no Butcher entity to compare against. State
   this in the docstring.
2. **Signature change**: added `h_output` as final parameter. The
   parameter encodes *output convergence*, which the proof relies
   on; not a strengthening of the textbook (which conflates output
   and stage convergence) but a faithfulness-preserving refactor of
   the proof structure.
3. **Identity check**: proof uses real machinery (matrix-mulVec
   continuity, Lipschitz, sum-of-limits), not `exact`.

### `aux_515D_stage_eventually_bounded` (NEW, if added)

1. Internal helper — no entity. Document in docstring.
2. **Hypotheses**: minimal subset of stage-equation prerequisites
   plus output convergence. No `IsStable`/`IsConsistent` — purely
   linear-algebra boundedness.
3. **Sorry'd this cycle**: document in the docstring that the proof
   is deferred to cycle 110 with a pointer to the M-matrix
   infrastructure in `OpenMath/Chapter5/MMatrix.lean`.

---

## Commit message template

If Priority 1 + Priority 2 (full close) land:

```
Cycle 109 — close thm:515D s=0 inline sorry + close aux_515D_stage_tendsto

* Add (hs : 0 < s) precondition to stable_consistent_isConvergent.
  Eliminates the s=0 degenerate case (vacuously False for (0,0) GLMs).
  Faithfulness divergence documented; see thm_515D_s_zero_degenerate.md
  Resolution.
* Refactor aux_515D_stage_tendsto signature to take h_output as
  explicit hypothesis, then close its proof via stage-equation
  + Matrix.mulVec continuity + h_n → 0 squeeze.

Sorry count: 3 → 1 (out of 1 in OpenMath/).
```

If Priority 1 only:

```
Cycle 109 — close thm:515D s=0 inline sorry via 0 < s precondition

Add (hs : 0 < s) precondition to stable_consistent_isConvergent.
Eliminates the s=0 degenerate case (vacuously False for (0,0) GLMs).
Faithfulness divergence documented; see thm_515D_s_zero_degenerate.md
Resolution.

Sorry count: 3 → 2 (out of 2 in OpenMath/).
```

If Priority 1 + refactored stage with deferred boundedness helper:

```
Cycle 109 — course-correct thm:515D: drop s=0 sorry, refactor stage sub-lemma

* Add (hs : 0 < s) precondition to stable_consistent_isConvergent;
  eliminates the s=0 degenerate inline sorry. Faithfulness divergence
  documented.
* Refactor aux_515D_stage_tendsto to take h_output as explicit
  hypothesis. Close all but the eventual-stage-boundedness piece.
* Open aux_515D_stage_eventually_bounded as a sorry'd helper for
  cycle 110 (M-matrix infrastructure).

Sorry count: 3 → 2 (out of 2 in OpenMath/, refactored).
```

---

## Pre-commit verification

```
git rev-parse HEAD                          # capture pre-push HEAD
git push origin Main/Experiments
# After push:
test "$(git rev-parse HEAD)" = "$(git rev-parse origin/Main/Experiments)"
```

If the two HEADs differ, do **NOT** trust the cycle as committed.
Re-push and re-verify before finalizing
`task_results/cycle_109.md`. (Cycles 008/035/071 had real
commit-not-reaching-repo failures; do not assume.)

---

## Suggested cycle 110+ trajectory (informational)

* **Cycle 110**: close `aux_515D_stage_eventually_bounded` (if
  cycle 109 deferred it as sorry) using the M-matrix
  infrastructure from cycles 105–107
  (`Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg` in
  `OpenMath/Chapter5/MMatrix.lean`). Sorry count → 1.
* **Cycle 111**: open `aux_515D_output_tendsto` decomposition into
  helpers (per Priority 3 sketch above). This is sorry-first and
  raises the count temporarily, but positions cycles 112–114 to
  close the chain.
* **Cycles 112–114**: close the per-step recurrence,
  Grönwall-textbook form, and h → 0 squeeze, one per cycle. Final
  closure brings §515 sorry count to 0 and `thm:515D` to fully
  formalized.

This trajectory matches the cycle 064–068 LMM analog (4 cycles for
the analogous decomposition + closure chain).

---

## Quick-reference Mathlib lemmas for Priority 2

| Goal | Candidate lemma | Verify with |
|---|---|---|
| `1 / n → 0` as `n → ∞` | `tendsto_one_div_atTop_nhds_zero` | local_search |
| `(x - x₀) / n → 0` | `Tendsto.const_mul` after rewriting `(x-x₀)/n = (x-x₀) · (1/n)` | local_search |
| `Continuous (M.U *ᵥ ·)` | `Matrix.mulVec_continuous` (verify) or inline via `continuous_apply` + `continuous_finset_sum` | local_search "Matrix.*mulVec.*[Cc]ontinuous" |
| `tendsto_pi_nhds` | `tendsto_pi_nhds : Tendsto F atTop (nhds f) ↔ ∀ i, Tendsto (F · i) atTop (nhds (f i))` | local_search |
| `Tendsto.add` | std | std |
| `Tendsto.const_mul` | std | std |
| `Tendsto.congr'` (eventually) | std (in `Filter`) | local_search |
| Lipschitz |·| bound | `LipschitzWith.dist_le_mul` then `Real.dist_eq` | std |
| `Finset.abs_sum_le_sum_abs` | std | std |

Names are best-effort accurate as of pinned Mathlib v4.28.0; verify
each with `lean_local_search` or `lean_loogle` before relying on
it. The cycle 094/096/099 history shows Mathlib tendsto-API names
sometimes shift (`Filter.Tendsto.const_mul` vs `Tendsto.const_mul`
namespace in particular — both work depending on `open Filter`
state).
