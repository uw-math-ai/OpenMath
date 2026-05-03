# Cycle 091 Strategy — formalize `def:512A` (convergent GLM)

## Target

`def:512A` — **convergent (general linear method)**, Butcher §512, p. 409.

This is the GLM analogue of `def:402A` (convergent LMM), formalized in
cycle 038 as
`OpenMath.Chapter4.Section404.LinearMultistepMethod.IsConvergent`.

**Why this entity now.** Cycle 090's worker recommended the §514/§515
convergence thread (necessity of stability/consistency, sufficiency).
Inspecting the topo order in `plan.md` and
`extraction/formalization_data/entities/def_512A.json` confirms that
**`def:512A` is the immediate prerequisite** of every entity in that
thread:

```
dependents of def:512A:
  thm:513A   — necessity of stability
  thm:514A   — necessity of consistency
  lem:515B   — stability+consistency ⇒ convergence helper
  thm:515D   — stability+consistency ⇒ convergence
  def:542A
```

Without `def:512A` formalized, none of these can be stated. So
cycle 091's job is to land the definition + a `IsGLMSolution`
recurrence predicate + sanity helpers, mirroring the cycle 038 LMM
deliverable.

## Aristotle preflight

**No pending Aristotle results** as of the start of this cycle. Before
manual proof, batch-submit the helper lemmas listed in §"Aristotle
batch" below. Then proceed to manual proof while waiting (per
CLAUDE.md: one 30-min sleep, then check once).

## File placement

Create a new file `OpenMath/Chapter5/Section512.lean`. Do **not** add
to `Section510.lean` (which holds §510A/B/C only) or to
`Section520.lean` (which holds the stability theory of §52x).

This mirrors the chapter's textbook structure (§512 is a distinct
subsection — "Definition of convergence"), and parallels the way
Chapter 4 separated §402 / §404 / §405 / §406 / §410 into one file
per subsection. We choose the cleaner per-subsection split here
because §512 has a substantial recurrence predicate (`IsGLMSolution`)
that does not belong in §510.

## Imports (in this order)

```lean
import Mathlib.Topology.Algebra.Order.Filter
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Lipschitz
import OpenMath.Chapter5.Section510
```

`Section510` brings the `GeneralLinearMethod` structure and the four
existing predicates (`IsPreconsistent`, `IsStable`, `IsConsistent`).
The other imports cover `Filter.Tendsto`, `LipschitzWith`, and
`HasDerivAt`. Verify with `lean_build` after the file lands; do not
trial-and-error the import list.

## Encoding plan

### Step 1 — `IsGLMSolution` (the GLM iteration recurrence)

The textbook defines (Butcher §511) the GLM step as: given input
vector `y^{[n-1]} ∈ ℝ^r`, the internal stages `Y_i^{[n]}` and outputs
`y_i^{[n]}` satisfy

```
Y_i^{[n]} = Σ_j a_{ij} · h · f(Y_j^{[n]}) + Σ_j u_{ij} · y_j^{[n-1]}
y_i^{[n]} = Σ_j b_{ij} · h · f(Y_j^{[n]}) + Σ_j v_{ij} · y_j^{[n-1]}
```

For autonomous `f : ℝ → ℝ` (matching `def:512A`'s autonomous IVP
`y'(x) = f(y(x))`), encode this as a **per-step existential** over
the stage tuple `Y : Fin s → ℝ`:

```lean
/-- The sequence `y_seq : ℕ → Fin r → ℝ` is a GLM iteration of `M`
with stepsize `h` and autonomous RHS `f`, starting from `y_seq 0`,
if at every step `n` there exist internal stages `Y : Fin s → ℝ`
satisfying the implicit stage equations and producing
`y_seq (n+1)` via the output equations. -/
def GeneralLinearMethod.IsGLMSolution {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (f : ℝ → ℝ)
    (y_seq : ℕ → Fin r → ℝ) : Prop :=
  ∀ n : ℕ, ∃ Y : Fin s → ℝ,
    (∀ i, Y i = (∑ j, M.A i j * (h * f (Y j)))
                + (∑ j, M.U i j * y_seq n j))
    ∧ (∀ i, y_seq (n + 1) i = (∑ j, M.B i j * (h * f (Y j)))
                              + (∑ j, M.V i j * y_seq n j))
```

Existential per step (not a single existential over the whole stage
history) is the right encoding because the stage tuple `Y` at step
`n+1` depends only on `y_seq n`, not on the prior stages. This is the
parallel encoding to `LinearMultistepMethod.IsLMMSolution` at
`OpenMath/Chapter4/Section404.lean:275`.

**Faithfulness flag.** Butcher's `f` is generally vector-valued
(`f : ℝ^N → ℝ^N`) but the textbook §512 writes the IVP as the scalar
`y'(x) = f(y(x))`. We use scalar `f : ℝ → ℝ` to match the textbook
literally; this is also what `def:402A` did in `Section404.lean`.
Vectorization is a future generalization, not a faithfulness issue.

### Step 2 — `IsConvergent` (the textbook predicate)

```lean
/-- **Definition 512A** — A general linear method `(A, U, B, V)` is
*convergent* if for any IVP `y'(x) = f(y(x))`, `y(x₀) = y₀` with `f`
Lipschitz, there exists a non-zero vector `u ∈ ℝ^r` and a starting
procedure `φ : ℝ → Fin r → ℝ` with `φ_i(h) → u_i · y(x₀)` as `h → 0`,
such that for any `x > x₀`, the GLM iterations `y^{[n]}` (computed
with stepsize `h_n = (x - x₀)/n` and starting value `y^{[0]} = φ(h_n)`)
satisfy `y^{[n]} → u · y(x)` as `n → ∞`. -/
def GeneralLinearMethod.IsConvergent {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∀ (f : ℝ → ℝ) (L : ℝ≥0) (_ : LipschitzWith L f)
    (x₀ y₀ : ℝ) (yex : ℝ → ℝ)
    (_ : yex x₀ = y₀)
    (_ : ∀ x, HasDerivAt yex (f (yex x)) x),
  ∃ u : Fin r → ℝ, u ≠ 0 ∧
    ∃ φ : ℝ → Fin r → ℝ,
    (∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                     (nhds 0) (nhds (u i * y₀))) ∧
    ∀ x : ℝ, x₀ < x →
    ∀ Y : ℕ → ℕ → Fin r → ℝ,
      (∀ n : ℕ, 0 < n →
        Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
        M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n)) →
      Filter.Tendsto (fun n : ℕ => Y n n)
                     Filter.atTop (nhds (fun i => u i * yex x))
```

Note the **double-indexed `Y : ℕ → ℕ → Fin r → ℝ`**: outer index is
the discretization parameter `n` (number of steps; defines `h_n`),
inner index is the iteration step `0..n`. This matches the LMM
template's `Y : ℕ → ℕ → ℝ` shape from `Section404.lean:350`.

**Critical structural choices** (do not deviate without escalation):

1. **Autonomous `f : ℝ → ℝ`** (textbook is explicit: `y'(x) = f(y(x))`).
   Do NOT introduce a time argument; that would diverge from the
   textbook.
2. **Existential `u`, `φ` outside the `∀ Y`**, with `u ≠ 0` —
   matches "there exist a non-zero vector u and a starting procedure
   φ" in the textbook.
3. **Pointwise `Y n n → (fun i => u i * yex x)`** — pi-type pointwise
   convergence is the right Mathlib idiom; matches
   `Filter.tendsto_pi_nhds`.
4. **Do NOT add the cycle 068 strengthening** (joint Lipschitz, global
   C¹, M_bound) yet. The downstream §513/§514/§515 helpers may need
   strengthening eventually — when they do, file an issue parallel to
   `is_convergent_strengthened.md`. For def-only cycle 091, stay close
   to the textbook.

### Step 3 — Non-vacuity sanity helpers

CLAUDE.md requires a witness or an issue for every new structure with
`Prop` fields. `IsGLMSolution` and `IsConvergent` are predicates (not
structures), but the same spirit applies — provide enough evidence
that the predicate is non-vacuously inhabitable.

**Helper 1 (sanity, must close cleanly):**
```lean
/-- For autonomous RHS `f ≡ 0`, the GLM iteration recurrence reduces
to the homogeneous V-recurrence `y_seq (n+1) i = (B·U·y_seq n) i +
(V·y_seq n) i` (i.e., the stage `h·f(Y_j)` term vanishes; the
remaining stage equation `Y_i = Σ_j U_{ij} y_seq n j` makes
`B·h·f(Y) = 0` and the output reduces to `B·0 + V·y_seq n = V·y_seq n`,
plus a `B·U·y_seq n`-shaped contribution from the explicit-stage
b-row terms when `B` actually picks up the stage values via U).

NOTE: After unfolding `f ≡ 0`, the b-row's `B_{ij} · h · f(Y_j)` term
is zero — so the `B·U` contribution above vanishes too, and the
recurrence collapses fully to `y_seq (n+1) = V · y_seq n`. -/
theorem isGLMSolution_zero_iff {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (y_seq : ℕ → Fin r → ℝ) :
    M.IsGLMSolution h (fun _ => 0) y_seq ↔
    ∀ n : ℕ, ∀ i : Fin r,
      y_seq (n + 1) i = ∑ j : Fin r, M.V i j * y_seq n j
```

Proof shape: forward direction extracts `Y` from the existential and
substitutes `f = 0` into the stage equation to get
`Y i = Σ_j U_{ij} y_seq n j`, then notes the output equation's
`B·h·f(Y) = 0` term vanishes, leaving `Σ_j V_{ij} y_seq n j`.
Reverse direction constructs `Y i := Σ_j U_{ij} y_seq n j` and verifies
both equations under `f = 0`. The arithmetic is `simp [mul_zero]`-style;
should be ~30 lines after both directions.

**Helper 2 (sanity, must close cleanly):**
```lean
/-- The constantly-zero `y_seq` is a valid GLM iteration of any GLM at
any stepsize for the trivial autonomous RHS `f ≡ 0`. -/
theorem zero_isGLMSolution_zero {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) :
    M.IsGLMSolution h (fun _ => 0) (fun _ _ => 0) := by
  intro n
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro i; simp
  · intro i; simp
```

(`simp` closes both goals because every term is `* 0` or sum-of-zeros.)

These two helpers establish that `IsGLMSolution` is well-defined and
inhabitable. They will be reused by §513/§514/§515 work.

### Step 4 — Issue file for the deferred concrete `IsConvergent` witness

Following the cycle 038 LMM template, **do not** attempt to produce a
concrete `M.IsConvergent` witness for any specific GLM in this cycle.
The argument requires `thm:515D` ("stability + consistency ⇒
convergence"), which is itself one of the cycle 091 dependents (i.e.,
needs `def:512A` to even be stated).

Instead, write an issue file at
`.prover-state/issues/glm_convergence_witness_deferred.md` modeled on
`.prover-state/issues/lmm_convergence_witness_deferred.md`. Cover:

* Why no concrete witness in this cycle (any non-trivial proof needs
  `thm:515D`, which is downstream).
* Trivial-IVP path: `f ≡ 0`, `y₀ = 0`, `yex ≡ 0`, `u = (1, …, 1)`,
  `φ ≡ 0`. **Caveat**: this is *not* a witness for `M.IsConvergent`
  for any `M` (the predicate quantifies over *all* IVPs, not just the
  trivial one), but it is a reasonable target for a "trivial-IVP
  slice" lemma in a future cycle.
* Recommendation: the canonical witness producer is `thm:515D`. After
  it lands, `explicitEulerGLM.IsConvergent` and any preconsistent +
  stable + consistent GLM follow as corollaries.

This is the documented escape hatch of CLAUDE.md ("write an issue
explaining why this is currently impossible").

## What NOT to try

* **Do NOT pursue `thm:521B`** (Maximum stability order for given
  steps). The cycle 090 worker correctly flagged this as a multi-cycle
  polynomial-encoding tax — it requires re-encoding `stabilityFunction`
  as `Polynomial (Polynomial ℂ)` and proving the new representation
  agrees with the existing function form. Out of scope for cycle 091.
* **Do NOT add the cycle 068 `is_convergent_strengthened` clauses**
  (joint Lipschitz, ContDiff ℝ 1, M_bound) to `IsConvergent` yet.
  These are downstream-driven strengthenings that should appear only
  when a §513/§514/§515 proof actually fails without them. Faithfulness
  takes priority for the definition-cycle.
* **Do NOT attempt a concrete `M.IsConvergent` witness** for any GLM.
  See the issue file plan in Step 4 above.
* **Do NOT generalize to vector-valued `f : ℝ^N → ℝ^N`**. Textbook
  §512 writes scalar `y'(x) = f(y(x))` and this matches the `def:402A`
  encoding. Future-cycle generalization is acceptable; cycle 091 stays
  scalar.
* **Do NOT use `def:512A` to introduce a `class` or `structure`.**
  It is a `Prop` predicate on a value of type
  `Section510.GeneralLinearMethod s r`; the existing
  `GeneralLinearMethod` structure is the only structure that should
  appear in the cycle's diff.
* **Do NOT modify `Section510.lean`** beyond cosmetic comment fixes.
  The new content goes in `Section512.lean`.
* **Do NOT raise `maxHeartbeats`**. If `simp` is slow on Step 3
  helpers, decompose into named arithmetic lemmas. Per CLAUDE.md.
* **Do NOT introduce `axiom`** for the deferred concrete witness
  (write an issue, don't axiomatize).
* **Do NOT trust the prompt's "stuck on" text without verification.**
  The cycle-090 history shows zero stuck items — `git log -1 --oneline`
  is `1bd6ba0 Cycle 090 — formalize def:521A`, on
  `origin/Main/Experiments`, no sorry's reported. Treat any "commits
  not reaching repo" framing as the standing phantom from
  `consultant_advice_cycle_009.md` §A.
* **Do NOT poll Aristotle more than once.** Per CLAUDE.md: submit at
  the start, sleep 30 min, check once, then proceed. Do not block on
  Aristotle for the manually-tractable Step 3 helpers.

## Aristotle batch (submit at cycle start)

Submit the following ~3 helper lemmas / sub-goals to Aristotle in a
single `decomposition_attempt.lean`-style file. Use the existing
`.prover-state/aristotle_submissions/cycle_091/` directory pattern.

1. **`isGLMSolution_zero_iff`** (Helper 1 from Step 3). Likely
   tractable — the algebra is `mul_zero` + sum-distributivity.
2. **`zero_isGLMSolution_zero`** (Helper 2 from Step 3). Trivial; will
   probably close in seconds.
3. **A bonus statement**: prove that the all-zeros `y_seq` solves the
   homogeneous V-recurrence (RHS of `isGLMSolution_zero_iff`) for any
   `M`. Useful for future §513/§514/§515 work; ~5 lines.

Submit, sleep 30 min, then proceed to Steps 1/2 manually while
waiting. After the sleep, check once and incorporate any landed
proofs (or keep the manual proofs if they finished first).

## Faithfulness checklist (run BEFORE committing)

For `def:512A` / `IsConvergent`:

- [ ] Quote the textbook statement from `entities/def_512A.json` in
      the docstring. Match line-for-line where possible.
- [ ] **Tautology check** — `IsConvergent` is not a re-export. The
      conclusion `Tendsto (Y n n) atTop (nhds (u • yex x))` is
      genuinely derived from the iteration; no hypothesis says this
      directly.
- [ ] **Hypothesis-strength check** — current encoding has only
      `LipschitzWith L f`, `yex x₀ = y₀`, `HasDerivAt yex (f (yex x)) x`.
      No extra strengthening. ✓
- [ ] **Definition-smuggling check** — `IsConvergent` does NOT embed
      the conclusion of `thm:515D` (stable+consistent ⇒ convergent).
      It is the convergence predicate alone.
- [ ] **Identity check** on Helper 1 — the proof is not `exact h`. It
      is forward/reverse implication of an unfolding.
- [ ] Confirm `M.IsConvergent` does not contain
      `M.IsStable` or `M.IsConsistent` as sub-clauses (those are
      separate `Section510` predicates; only the *converse* direction
      is `thm:515D`).

For `IsGLMSolution`:

- [ ] Confirm the recurrence matches Butcher's general scheme (Butcher
      §511 equations or §501 introduction) for the autonomous case.
      Documented in `entities/def_512A.json`'s `preamble` field.
- [ ] Existential `Y` per step is the right encoding; bullet why
      (analogous to `IsLMMSolution`).

## Build verification

After landing the file:

```bash
lake env lean OpenMath/Chapter5/Section512.lean    # standalone check
lake build OpenMath.Chapter5.Section512            # cache update
echo '#print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.IsConvergent' \
  | lake env lean --stdin OpenMath/Chapter5/Section512.lean
echo '#print axioms OpenMath.Chapter5.Section512.zero_isGLMSolution_zero' \
  | lake env lean --stdin OpenMath/Chapter5/Section512.lean
```

(Note: `IsConvergent` and `IsGLMSolution` live in the
`Section510.GeneralLinearMethod` namespace via dot-notation declarations
in `Section512.lean`, mirroring the `Section520` pattern of declaring
`stabilityMatrix` in `OpenMath.Chapter5.Section510` namespace from
inside `Section520.lean`. The `#print axioms` prints under whichever
namespace was opened.)

Expected axiom output: `[propext, Classical.choice, Quot.sound]`.

If `#print axioms` returns `sorryAx`, run `lake build` first to
refresh the .olean cache (cycle 089 staleness pattern). Re-run.

## Bookkeeping

After the build is clean:

1. **`extraction/formalization_data/lean_status.json`** — mark
   `def:512A` row with status `formalized`,
   `lean_file = OpenMath/Chapter5/Section512.lean`,
   `lean_symbol = OpenMath.Chapter5.Section510.GeneralLinearMethod.IsConvergent`
   (or whichever namespace the dot-notation `def` lands in — verify
   after compile).
2. **`plan.md`** — update the `[ ] def:512A convergent (GLM)` row to
   `[x]`, bump progress counter `61 → 62 / 175`.
3. **`.prover-state/issues/glm_convergence_witness_deferred.md`** —
   write per Step 4 plan above.
4. **`.prover-state/task_results/cycle_091.md`** — write per CLAUDE.md
   format. Include all faithfulness-check answers in the
   "Faithfulness check" section.

## Commit

```
git add OpenMath/Chapter5/Section512.lean \
        extraction/formalization_data/lean_status.json \
        plan.md \
        .prover-state/issues/glm_convergence_witness_deferred.md \
        .prover-state/task_results/cycle_091.md \
        .prover-state/aristotle_submissions/cycle_091/

git commit -m "Cycle 091 — formalize def:512A (convergent GLM) + IsGLMSolution recurrence"

git push origin Main/Experiments
```

Verify HEAD == origin/Main/Experiments after push (cycle 008/035/071
phantom guard).

## Estimated effort

* New file `Section512.lean`: ~140 lines.
  * Imports + namespace boilerplate: ~10 lines.
  * `IsGLMSolution` def + docstring: ~30 lines.
  * `IsConvergent` def + docstring: ~50 lines.
  * `isGLMSolution_zero_iff`: ~30 lines (Helper 1).
  * `zero_isGLMSolution_zero`: ~5 lines (Helper 2).
  * Optional bonus helper: ~10 lines.
* Issue file: ~50 lines.
* Bookkeeping: ~10 lines (json, plan, task results).

Total cycle target: **~200 lines + bookkeeping**, in line with the
cycle 086–090 cadence (~150–250 lines per cycle for a definition +
witness deliverable).

## Cross-references

* `OpenMath/Chapter4/Section404.lean:242–354` — the LMM template for
  `IsLMMSolution` and `IsConvergent`.
* `OpenMath/Chapter5/Section510.lean` — the `GeneralLinearMethod`
  structure and `IsPreconsistent`/`IsStable`/`IsConsistent`.
* `extraction/formalization_data/entities/def_512A.json` — textbook
  statement.
* `extraction/formalization_data/entities/def_402A.json` — LMM
  parallel.
* `.prover-state/issues/lmm_convergence_witness_deferred.md` — the
  template for the new `glm_convergence_witness_deferred.md` issue.
* `.prover-state/issues/is_convergent_strengthened.md` — record of
  the LMM strengthening; do **not** preemptively apply to GLM (Step 2
  policy).
