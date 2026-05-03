# Cycle 084 Strategy — Formalize `def:510C` (stable GLM)

## Aristotle results

**None pending.** Skip the incorporation step.

## Priority 0 — Housekeeping

**No housekeeping required.** Cycle 083 already brought `plan.md` and
`lean_status.json` into agreement (54 / 175 entities, all `[x]` rows
matching `formalized` status, file pointers up to date). Do not waste
cycle budget hunting for stale rows; verify with one `Grep` for `[x]`
in `plan.md` if you want a sanity check, then move on.

## Priority 1 — Substantive target: `def:510C` (stable GLM)

### Why this entity

* Next entity in the §510 cluster after cycle 083's `def:510A`.
* Topologically unblocked: only depends on `def:142A` (power-boundedness,
  formalized in cycle 005 as
  `OpenMath.Chapter1.Section142.PowerBounded`).
* Unblocks `def:510B`, `def:512A`, `def:520A`, and 7 more downstream
  entities — a high-leverage definition.
* The prior worker's "Suggested next approach" explicitly named this
  as cycle 084's target.

### Textbook statement (verbatim from `entities/def_510C.json`)

> A general linear method `(A, U, B, V)` is `stable' if there exists
> a constant `C` such that, for all `n = 1, 2, ...`, `‖V^n‖ ≤ C`.

Faithful Lean encoding:

```lean
∃ C : ℝ, ∀ n : ℕ, ‖M.V ^ n‖ ≤ C
```

We quantify over **all** `n : ℕ` (including `n = 0`), not `n ≥ 1`.
This is equivalent to the textbook's `n = 1, 2, ...` quantification
because `‖V^0‖ = ‖1‖ = 1` is a fixed constant, and any bound `C` for
`n ≥ 1` extends to `max(C, 1)` for all `n`. The full-`ℕ`
quantification matches our existing `def:142A`
(`PowerBounded`) signature exactly, allowing direct reuse.

### Required infrastructure

`def:510C` is the textbook GLM instance of `def:142A`. **REUSE**
`OpenMath.Chapter1.Section142.PowerBounded` rather than re-deriving:

```lean
def GeneralLinearMethod.IsStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∃ C : ℝ, OpenMath.Chapter1.Section142.PowerBounded C M.V
```

`PowerBounded` is defined over an arbitrary `[SeminormedRing A]`, and
`Matrix (Fin r) (Fin r) ℝ` gets that instance from
`Matrix.linftyOpNormedRing` (in `Mathlib.Analysis.Matrix.Normed`).
The textbook is silent on which matrix norm is used; Butcher's
`def:142A` already documents this norm-equivalence reasoning, so
the choice is faithful.

### Concrete file plan — `OpenMath/Chapter5/Section510.lean`

1. **Add imports** at top of file:
   ```lean
   import Mathlib.Analysis.Matrix.Normed
   import OpenMath.Chapter1.Section142
   ```
   (`Mathlib.Analysis.Matrix.Normed` is the same import that
   `Section142.lean` uses to get the `SeminormedRing` instance for
   matrices; `OpenMath.Chapter1.Section142` brings in `PowerBounded`.)

2. **Insert below the `IsPreconsistent` definition** (around line 76):

   ```lean
   /-- **Definition 510C** — A GLM is *stable* if there exists a
   constant `C` such that `‖M.V ^ n‖ ≤ C` for every `n : ℕ`.

   This is the GLM instance of Butcher's general matrix-stability
   notion (`def:142A`, `OpenMath.Chapter1.Section142.PowerBounded`),
   applied to the input/output propagation matrix `V`. -/
   def GeneralLinearMethod.IsStable {s r : ℕ}
       (M : GeneralLinearMethod s r) : Prop :=
     ∃ C : ℝ, OpenMath.Chapter1.Section142.PowerBounded C M.V
   ```

3. **Witness for non-vacuity** (CLAUDE.md mandatory rule for new
   definitions). `explicitEulerGLM` already lives in this file with
   `V = !![1]`, so `V^n = !![1]` for all `n` and `‖V^n‖ = 1`. The
   bound `C = 1` works:

   ```lean
   /-- The non-vacuity witness: `explicitEulerGLM` is stable with
   `C = 1`. Its `V` block is the `(1 × 1)` identity, so every power
   has linfty operator norm `1`. -/
   theorem explicitEulerGLM_isStable : explicitEulerGLM.IsStable := by
     refine ⟨1, ?_⟩
     intro n
     -- Goal: ‖explicitEulerGLM.V ^ n‖ ≤ 1
     have hV : explicitEulerGLM.V = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
       ext i j; fin_cases i; fin_cases j
       simp [explicitEulerGLM, Matrix.one_apply]
     rw [hV, one_pow]
     -- Goal: ‖(1 : Matrix (Fin 1) (Fin 1) ℝ)‖ ≤ 1
     exact le_of_eq norm_one
   ```

   If `norm_one` does not close the final step (depends on whether
   the matrix `NormedRing` instance also provides `NormOneClass`),
   try in order:
   * `simp [Matrix.linftyOpNorm_one]` (if the lemma name exists).
   * `rw [show (1 : Matrix (Fin 1) (Fin 1) ℝ) =
       Matrix.diagonal (fun _ => 1) from rfl]` then unfold the linfty
     op norm via `Matrix.linftyOpNorm_def` and bound the singleton sum.
   * `lean_multi_attempt` with
     `["exact le_of_eq norm_one", "simp", "decide", "norm_num"]`.

   Verify the lemma name with `lean_local_search "linftyOpNorm_one"`
   or `lean_loogle "‖(1 : Matrix _ _ _)‖"` before committing.

4. **Update `lean_status.json`** for `def:510C`:
   ```json
   {
     "lean_file": "OpenMath/Chapter5/Section510.lean",
     "lean_symbol": "OpenMath.Chapter5.Section510.GeneralLinearMethod.IsStable",
     "formalization_status": "formalized"
   }
   ```

5. **Update `plan.md`**: mark the `def:510C` row `[x]` and append
   `— OpenMath/Chapter5/Section510.lean`. Bump the global progress
   counter `54 / 175 → 55 / 175`.

### Verification checklist (run before commit)

* `lake env lean OpenMath/Chapter5/Section510.lean` — clean.
* `lake build OpenMath.Chapter5.Section510` — clean, .olean cache
  refreshed (per cycle 072's discovery: `lake env lean` alone does
  NOT update the .olean cache, so `lake build` is required for the
  axiom check below to be accurate).
* `#print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.IsStable`
  — expect `[propext, Classical.choice, Quot.sound]`.
* `#print axioms OpenMath.Chapter5.Section510.explicitEulerGLM_isStable`
  — expect the same baseline set.

### Faithfulness check (required by CLAUDE.md pre-commit checklist)

For `def:510C` (`GeneralLinearMethod.IsStable`):
* Quote the textbook statement (above) in the cycle results.
* Confirm Lean type matches: `∃ C, PowerBounded C M.V` ↔ Butcher's
  `∃ C, ∀ n = 1, 2, ..., ‖V^n‖ ≤ C` (equivalent up to the harmless
  `n = 0` extension; documented in the docstring).
* No definition smuggling: we do **NOT** define stability via
  spectral radius `< 1`, eigenvalue conditions, or any other
  characterization theorem. The definition is the literal
  power-boundedness statement.

For `explicitEulerGLM_isStable`:
* Tautology check: conclusion `IsStable` is not a hypothesis (the
  theorem is hypothesis-free).
* Identity check: proof constructs witness `C = 1` and discharges
  a real norm bound — not `exact h`.

## What NOT to try

* **Do NOT define `IsStable` via spectral radius, eigenvalues, or
  the minimal polynomial having roots in the closed unit disc.**
  Each of those is a *characterization theorem*, not the definition.
  Butcher's `def:510C` is a literal power-boundedness condition;
  encoding any characterization as the definition would make those
  future theorems tautologies.
* **Do NOT re-derive `PowerBounded`.** It already exists at
  `OpenMath.Chapter1.Section142.PowerBounded` as a fully general
  `[SeminormedRing A]`-polymorphic predicate. Reuse it directly to
  preserve cross-chapter consistency and to keep the GLM definition
  trivially the textbook instance of the matrix definition.
* **Do NOT introduce a new norm instance for matrices.** Mathlib's
  `Matrix.linftyOpNormedRing` (in `Mathlib.Analysis.Matrix.Normed`)
  already gives `Matrix (Fin r) (Fin r) ℝ` a `SeminormedRing` /
  `NormedRing` structure that `PowerBounded` accepts.
* **Do NOT widen the witness from `explicitEulerGLM` to a more
  exotic GLM in this cycle.** The 1×1 identity-`V` case is the
  cheapest non-vacuity witness and is sufficient. Save more
  interesting witnesses (DIMSIMs, IRK methods) for the §54x and
  §55x cycles where they have direct theorem-level use.
* **Do NOT pursue `def:510B` (consistent GLM) in this cycle.**
  `def:510B` depends on `def:510A` and `def:510C` simultaneously,
  so landing `def:510C` first cleanly unblocks `def:510B` for
  cycle 085. Mixing them would produce a single bloated diff.
* **Do NOT submit to Aristotle for this cycle.** This is a single
  definition + a 6-line witness proof. Aristotle's overhead
  (30-min sleep) is not justified for a sub-cycle of work. If the
  `norm_one` close stalls, escalate via `lean_multi_attempt` and
  `lean_local_search` — they are immediate.
* **Do NOT raise `maxHeartbeats`.** The witness proof is trivial;
  if it stalls, the issue is a missing lemma name, not compute.
* **Do NOT trust the prompt's "stuck" / "commits not reaching
  repo" framing if it appears in the next cycle's prompt-builder
  output.** The pattern is the well-documented stale `attempts.md`
  carry-over diagnosed in cycles 008, 014, 015, 040 (see
  `consultant_advice_cycle_*.md`). If you see such a verdict, run
  `git log -1 --format='%H %s'` and `git rev-parse origin/Main/Experiments`
  to verify the cycle 084 commit landed, then proceed.

## After cycle 084 — roadmap (FYI, do not implement this cycle)

* **Cycle 085**: `def:510B` (consistent GLM) — adds the equation
  `B 𝟙 + V v = u + v`. Definition + witness on `explicitEulerGLM`.
* **Cycle 086**: `def:512A` (convergent GLM) — analogous to cycle
  068's LMM `IsConvergent`; predicate-only, no witness theorem
  required (will be a definition + non-vacuity sanity helper).
* **Cycle 087+**: `def:520A` (introduction) and §520 cluster.

The §51x cluster should clear in 3–4 cycles total at this pace,
giving Chapter 5 momentum before tackling the heavier §52x / §54x
infrastructure.
