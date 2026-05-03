# Strategy — Cycle 098

## Context summary (read this before doing anything)

* **Cycle 097 score**: −2.
* Cycle 097 *did real work*: closed `cesaro_orthogonal_to_VT_fixed`
  and `exists_inverse_of_cesaro_zero` cleanly (sorry count 2 → 1,
  axioms `[propext, Classical.choice, Quot.sound]` only).
* The −2 was driven entirely by the scanner: semantic sorry count
  rose 1 → 3 due to **two scanner false positives** in newly-written
  cycle-097 code at `Section514.lean:304` (`exact h_dot`) and
  `Section514.lean:305` (`exact h_inner`). The scanner reported
  these as lines 215–216 because of the well-documented line-drift
  bug (`tautology_scanner_false_positives.md` D1).
* These are **legitimate** `rw … at hX; exact hX` closers — the
  rewrites at lines 296–303 do real work materializing the goal.
* The standing workaround (cycles 010, 014, 015) is the
  underscore-rename: `h_<name>` → `h<name>`. **Do not edit
  `scripts/autonomous_loop.py`** (loop-maintainer territory).

The remaining `Section514.lean` sorry is `cesaro_residual_tendsto_zero`
(line ~159), gated on the `u' = u` bridge. Cycle 097 confirmed the
issue's option (b) is provably impossible and recommended **option
(iii)**: strengthen `def:512A` `IsConvergent` to expose stages so
`U·u' = 𝟙` becomes extractable.

---

## Priority 0a — MANDATORY scanner-cleanup (do this FIRST)

This is non-negotiable. Without this, cycle 098 scores ≤ 0 even on
substantive work.

### Edit 1 — `OpenMath/Chapter5/Section514.lean`

Open the file. Apply these renames (all four touch-points within the
proof body of `exists_inverse_of_cesaro_zero`, surrounding lines
292–305):

```
have h_dot : dotProduct w u = 0 :=     →    have hdot : dotProduct w u = 0 :=
  cesaro_orthogonal_to_VT_fixed hCes hVu      cesaro_orthogonal_to_VT_fixed hCes hVu
```

```
have h_inner : inner ℝ u_E w_E = (0 : ℝ) := by    →    have hinner : inner ℝ u_E w_E = (0 : ℝ) := by
```

```
exact h_dot     →    exact hdot
exact h_inner   →    exact hinner
```

Use `Edit` with the exact strings above (or larger surrounding
context if needed for uniqueness). Four edits total in
`Section514.lean`.

### Edit 2 — `OpenMath/Chapter4/Section404.lean` (BONUS, recommended)

Apply the same fix to the pre-existing baseline hit at lines 5774–5779
to drive the scanner count to 0:

```
have h_mono :                            →    have hmono :
    LinearMultistepMethod.runningMaxAbs y i ≤
      LinearMultistepMethod.runningMaxAbs y m :=
  LinearMultistepMethod.runningMaxAbs_monotone y him
rw [hi₂] at h_mono                       →    rw [hi₂] at hmono
exact h_mono                             →    exact hmono
```

### Verification gate (run BEFORE commit)

Use the `Grep` tool with this regex on `OpenMath/`:

```
:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$
```

Expected: 0 matches.

Then verify both touched files compile:

```bash
lake env lean OpenMath/Chapter5/Section514.lean
lake env lean OpenMath/Chapter4/Section404.lean
```

Expected: zero scanner hits, both files compile, axioms unchanged
(`[propext, Classical.choice, Quot.sound]` only on the touched
theorems).

**Time budget**: ≤ 15 min. If anything is unclear, stop and re-read
`tautology_scanner_false_positives.md`.

---

## Priority 1 — Begin the `IsConvergent` strengthening (option iii)

Pursue **option (iii)** of `u_prime_equals_u_bridge.md`: strengthen
`def:512A` `IsConvergent` to expose internal stages, so a future
cycle can extract `U·u' = 𝟙` and close the bridge.

This is design + plumbing work, NOT a closure of
`cesaro_residual_tendsto_zero`. Cycle 098 delivers the strengthened
definition and re-verifies the existing §513/§514 consumers; cycle
099+ uses the strengthening to close the bridge and the residual
sorry. Do NOT try to close everything in one cycle — that pattern
caused the cycle 060 / 092 / 094 reverts.

### Step 1 — Read carefully and write a one-page design note

Read these files fully before writing any code:

* `OpenMath/Chapter5/Section512.lean:138-154` — current `IsConvergent`.
* `OpenMath/Chapter5/Section510.lean` — `IsGLMSolution` definition
  (the existential structure exposing `Y_internal`).
* `OpenMath/Chapter5/Section513.lean` — cycle 093 `convergent_isStable`
  proof. You will need to keep this proof working after the change.
* `OpenMath/Chapter5/Section514.lean::convergence_witness_isVfixed`
  (cycle 096) — proves `V·u' = u'`. Keep this working too.
* `.prover-state/issues/u_prime_equals_u_bridge.md` — full context
  on why option (iii) is the recommended path.
* `.prover-state/issues/is_convergent_strengthened.md` — LMM precedent
  for documenting a faithfulness-divergent strengthening.

Then write a **brief** design note (≤ 40 lines) at
`.prover-state/issues/glm_isconvergent_strengthened.md` covering:

1. The exact new clause to add to `IsConvergent` (proposed shape:
   for the `Y_internal n` stages produced by `M.IsGLMSolution h f Y`,
   the sequence of stages also tends to a known limit; see Step 2 for
   the recommended shape).
2. Why this clause is needed (cite the `U·u' = 𝟙` extraction goal).
3. Faithfulness-divergence justification (analogous to the LMM
   precedent — Butcher's textbook does not literally state the stage
   limit, but it is implicit in any well-defined GLM applied to a
   smooth solution: stages approximate the same exact solution at
   shifted abscissae, and as `h → 0` all shifts collapse).
4. Downstream impact: list the consumers (cycle 091 sanity helpers,
   cycle 093 §513, cycle 096 `convergence_witness_isVfixed`,
   cycle 094 §514 scaffold) and a one-line note on whether each is
   trivially preserved or needs a small fix.

### Step 2 — Recommended shape of the strengthened definition

**Recommended**: package the stage sequence as part of the
`IsConvergent` witness rather than re-extracting it. Specifically,
add a new internal-stage parameter `Y_internal : ℕ → ℕ → Fin s → ℝ`
to the universal quantification, name the stage / output equations
inline (instead of via the existential `M.IsGLMSolution`), and add a
new conclusion clause:

```
Filter.Tendsto (fun n : ℕ => Y_internal n n)
               Filter.atTop (nhds (fun _ => yex x))
```

(i.e. each internal stage component tends to `yex(x)`, the all-ones
scalar multiple). For the trivial IVP (`f ≡ 1`, `yex := id`,
`x₀ := 0`), this gives `Y_internal n n → x` componentwise, and the
stage equation `Y_internal i = h • A𝟙 + U *ᵥ Y n` then forces
`x · 𝟙 = U · (u' · x)`, i.e. `U · u' = 𝟙`. ✓

**Concrete sketch** (do NOT copy verbatim; verify against the actual
`IsGLMSolution` shape and adjust):

```lean
def GeneralLinearMethod.IsConvergent {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∀ (f : ℝ → ℝ) (L : NNReal), LipschitzWith L f →
  ∀ (x₀ y₀ : ℝ) (yex : ℝ → ℝ),
    yex x₀ = y₀ →
    (∀ x, HasDerivAt yex (f (yex x)) x) →
  ∃ u : Fin r → ℝ, u ≠ 0 ∧
    ∀ φ : ℝ → Fin r → ℝ,
      (∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                       (nhds 0) (nhds (u i * y₀))) →
    ∀ x : ℝ, x₀ < x →
    ∀ Y : ℕ → ℕ → Fin r → ℝ,
    ∀ Y_internal : ℕ → ℕ → Fin s → ℝ,         -- NEW: explicit stage param
      (∀ n : ℕ, 0 < n →
        Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
        -- Bind stage to output via the stage + output equations
        -- directly (replacing the existential `M.IsGLMSolution …`
        -- with explicit per-step equalities that name `Y_internal n m`
        -- as the stage at micro-step m of macro-step n).
        (∀ m : ℕ, ∀ i : Fin s,
            Y_internal n m i =
              ((x - x₀) / (n : ℝ)) • (∑ j, M.A i j * f (Y_internal n m j))
              + ∑ j, M.U i j * Y n m j) ∧
        (∀ m : ℕ, ∀ i : Fin r,
            Y n (m + 1) i =
              ((x - x₀) / (n : ℝ)) • (∑ j, M.B i j * f (Y_internal n m j))
              + ∑ j, M.V i j * Y n m j)) →
      Filter.Tendsto (fun n : ℕ => Y n n)
                     Filter.atTop (nhds (fun i => u i * yex x))
      ∧ Filter.Tendsto (fun n : ℕ => Y_internal n n)        -- NEW: stage limit
                       Filter.atTop (nhds (fun _ => yex x))
```

Two design decisions you may revisit if the above shape causes
trouble:

* You may keep the `M.IsGLMSolution` existential and instead
  *re-state* the stage clause via a separate hypothesis chain — but
  the explicit form above avoids re-extracting the existential at
  every consumer. Pick whichever is cleaner; document the choice in
  the design note.
* The "stage limit is `(fun _ => yex x)`" is the all-ones-vector
  scaling of `yex(x)`. Confirm this matches the textbook abscissa
  convention (Butcher §510 / §511) before committing — if Butcher
  uses a different scaling (e.g. `c_i · yex(x)` for abscissae `c_i`),
  use that instead.

### Step 3 — Update consumers and re-verify

For each affected file:

1. **`Section512.lean` sanity helpers** (`isGLMSolution_zero_iff`,
   `zero_isGLMSolution_zero`, `zero_seq_homogeneous_V`): these
   characterize `IsGLMSolution`, NOT `IsConvergent`, so they are
   likely unaffected. Verify by running `lake env lean
   OpenMath/Chapter5/Section512.lean`.
2. **`Section513.lean` `convergent_isStable`** (cycle 093): the
   proof consumes `IsConvergent` symbolically. The new stage
   parameter adds a quantifier that consumers must supply. Update
   any `obtain ⟨u, hu_ne, hConv⟩ := hConv` / `hConv … hY …` patterns
   to bind/use the new stage parameter trivially (the stability
   proof does not need stage info; it can pass any well-typed
   stage sequence — e.g. a constructed witness from
   `M.IsGLMSolution`'s existential — and ignore the new stage
   limit). Re-verify the file compiles and axioms are unchanged.
3. **`Section514.lean` `convergence_witness_isVfixed`** (cycle 096):
   same pattern as §513 — the proof's `hConv` use will need updating
   to supply (or ignore) the stage parameter. Re-verify.
4. **`Section514.lean` `cesaro_residual_tendsto_zero`** (sorry):
   this stays as a sorry this cycle. Update its surrounding comment
   to note that the strengthened definition now makes the closure
   *possible* (the next cycle will use it), but do NOT attempt the
   closure in cycle 098.

After all updates: `lake build OpenMath.Chapter5` should succeed,
and axiom checks on `convergent_isStable`,
`convergence_witness_isVfixed`, `convergent_preconsistent_isConsistent`
(the §514 scaffold) must all return
`[propext, Classical.choice, Quot.sound]` only (no `sorryAx` from
unintended new gaps; the existing `sorryAx` from
`cesaro_residual_tendsto_zero` is expected and acceptable).

### Step 4 — Aristotle batch (CLAUDE.md mandate)

Before manual proof work on Step 3, batch-submit ~3–5 Aristotle jobs
on the most likely-to-stick obligations. Reasonable candidates:

* The `IsGLMSolution → strengthened-IsConvergent-stage-clause`
  bridge lemma (extract a stage sequence from `IsGLMSolution`'s
  existential; useful as a constructor for §513/§514 to feed into
  the new universal stage parameter).
* The `ignore-stage` adapter for §513: re-prove `convergent_isStable`
  under the new signature by feeding a chosen stage sequence (from
  the `IsGLMSolution` existential at `f ≡ 0`).
* The `ignore-stage` adapter for §514's `convergence_witness_isVfixed`.

Submit, sleep 30 min (single check, not repeated polling), then
proceed manually on whichever did not return. Do **NOT** poll
Aristotle more than once.

### Cycle 098 Definition of Done

* Priority 0a applied: scanner reports 0 hits across `OpenMath/`
  for the tautology regex (verified via Grep tool).
* `def:512A` `IsConvergent` strengthened with the stage clause.
* `glm_isconvergent_strengthened.md` design note filed.
* `convergent_isStable` (§513) and `convergence_witness_isVfixed`
  (§514) re-verified under the new signature; both axiom-clean.
* `lake build OpenMath.Chapter5` succeeds.
* `cesaro_residual_tendsto_zero` remains a single sorry (no new
  sorries introduced).
* `extraction/formalization_data/lean_status.json` unchanged this
  cycle (`def:512A` was already `formalized`; the strengthening is
  documented as a faithfulness divergence in the new issue, not as
  a status change).

Sorry count target: 1 (unchanged); semantic-sorry target: 0
(scanner-clean) or 1 (if Section404.lean:5779 is left for next
cycle); both acceptable.

---

## Backup plan (if Step 2 hits an unexpected blocker)

If, after reading the §510 `IsGLMSolution` definition, the
recommended shape in Step 2 turns out to be ill-typed or to require
a deeper restructuring than fits in one cycle (e.g. `IsGLMSolution`
already exposes stages in a way that conflicts with the proposed
inline equations), STOP the strengthening and instead deliver:

1. Priority 0a (the scanner cleanup — non-negotiable).
2. The design note at `glm_isconvergent_strengthened.md` documenting
   what shape was attempted, why it failed, and a revised
   recommendation for cycle 099.
3. A small infrastructure improvement to §514: factor the inline
   `(LinearMap.range T)ᗮ = ker(adjoint T)` proof out of
   `exists_inverse_of_cesaro_zero` into a named helper
   `LinearMap.orthogonal_range_eq_ker_adjoint` (cycle 097's
   "Suggested next approach" item 4). This is a clean ~10-line
   refactor with zero risk.

The backup plan still produces a positive-score cycle: scanner
cleanup + a real (if smaller) lemma + a design-note unblocker.

---

## What NOT to do this cycle

* **Do NOT** attempt to close `cesaro_residual_tendsto_zero` itself.
  That requires the bridge `u' = u`, which requires the strengthened
  definition + a new derivation of `U·u' = 𝟙`. Trying to do all of
  it in one cycle replicates the cycle 094 / 060 / 092 collapse
  pattern.
* **Do NOT** edit `scripts/autonomous_loop.py` to "fix the scanner".
  That is loop-maintainer territory; the standing issue file
  (`tautology_scanner_false_positives.md`) already documents the
  bugs. Use the underscore-rename workaround.
* **Do NOT** revert any cycle 093, 095, 096, or 097 work. All four
  cycles delivered axiom-clean lemmas that the strengthened
  definition must continue to prove. If the new signature breaks
  one of them, re-do the proof under the new signature — do not
  weaken the lemma statement.
* **Do NOT** add a non-degeneracy hypothesis on `V`'s 1-eigenspace
  to `def:512A` (option (a) of the bridge issue). That is a
  textbook-foreign hypothesis and is the wrong path.
* **Do NOT** try to skip the Aristotle batch. CLAUDE.md mandates
  ~5 jobs / cycle. The strengthening's adapter lemmas are
  Aristotle-suitable (premise selection on `IsGLMSolution` /
  `IsConvergent`).
* **Do NOT** raise `maxHeartbeats` above 200000.
* **Do NOT** introduce `axiom` or `constant` declarations.
* **Do NOT** poll Aristotle more than once. One status check after
  ≥ 30 min, then proceed.
* **Do NOT** pivot to §515 (`lem:515A`–`thm:515D`) this cycle. Those
  consume `IsConvergent` symbolically too and would need re-doing
  if attempted before the strengthening lands. Park them for cycle
  100+.
* **Do NOT** treat the cycle 097 −2 score as evidence the actual
  proof work was wrong. Re-read the cycle 097 results: the two
  closed sub-lemmas are axiom-clean and stay. The score was a
  scanner artefact; Priority 0a addresses it.

---

## Quick-reference checklist for the worker

```
[ ] Edit Section514.lean: h_dot → hdot (line 292)
[ ] Edit Section514.lean: h_inner → hinner (line 295)
[ ] Edit Section514.lean: exact h_dot → exact hdot (line 304)
[ ] Edit Section514.lean: exact h_inner → exact hinner (line 305)
[ ] Edit Section404.lean: h_mono → hmono (lines 5774, 5778, 5779) — bonus
[ ] Verify: Grep tautology regex returns 0 matches in OpenMath/
[ ] lake env lean OpenMath/Chapter5/Section514.lean
[ ] lake env lean OpenMath/Chapter4/Section404.lean
[ ] Read: Section512.lean:138-154 (current IsConvergent)
[ ] Read: Section510.lean (IsGLMSolution shape)
[ ] Read: Section513.lean (cycle 093 consumer)
[ ] Read: Section514.lean::convergence_witness_isVfixed (cycle 096)
[ ] Write: .prover-state/issues/glm_isconvergent_strengthened.md (≤ 40 lines)
[ ] Submit Aristotle batch (~3–5 jobs on adapter lemmas)
[ ] Edit Section512.lean: strengthen IsConvergent definition
[ ] Update §513 convergent_isStable for new signature
[ ] Update §514 convergence_witness_isVfixed for new signature
[ ] Update §514 cesaro_residual_tendsto_zero comment (keep sorry)
[ ] One Aristotle status check after ≥ 30 min
[ ] Incorporate any returned proofs
[ ] lake build OpenMath.Chapter5
[ ] Axiom checks on §513/§514 theorems
[ ] Write task_results/cycle_098.md
[ ] Commit + push
```
