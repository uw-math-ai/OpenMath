# Cycle 100 Strategy — open §515 (sufficiency direction)

## Status entering cycle 100

* Cycle 099 closed `thm:514A` (necessity of consistency) and produced
  `convergent_isPreconsistent` as a bonus — `OpenMath/Chapter5/Section514.lean`
  is now sorry-free.
* §513 (necessity of stability) closed cycle 093.
* The `IsConvergent` strengthening with stage-limit (cycle 098) was
  *consumed* successfully in cycle 099 via `convergence_witness_satisfies_U`.
* Plan: 63 / 175 entities done. Next §515 cluster:
  `lem:515A → lem:515B → lem:515C → thm:515D`. **`thm:515D` is the
  converse of cycles 093+099** — it produces the convergence witness
  from stability + consistency.
* No pending Aristotle results. Cycle 099 jobs A/B/C are presumed
  expired or moot (manual proofs landed first).

## Target this cycle: open §515 with `lem:515A` sorry-first scaffold

Following CLAUDE.md ("Sorry-first ABSOLUTE RULE") and the precedent
of cycles 040 (lem:406B) and 094 (thm:514A), cycle 100 will:

1. **Create `OpenMath/Chapter5/Section515.lean`** with imports
   `OpenMath.Chapter5.Section512`, `Mathlib.Analysis.MeanInequalities`,
   `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`,
   `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`
   (FTC pulled in so the cycle 040–style residual-integral plan can
   be reused).
2. **Define the auxiliary objects** lem:515A needs:
   * The abscissae vector `c : Fin s → ℝ` defined as `c = A·𝟙 + U·v`
     (Butcher §515, just before lem:515A; `v` is the consistency
     vector from `IsConsistent`).
   * The `ℓ : Fin s → ℝ` vector solving `(I − h₀L|A|) ℓ = ½ c² + |A| |c|`
     entrywise (Butcher §515 ℓ-system; `|A|` is the entrywise-absolute-
     value matrix). Encode as the textbook *defining linear equation*
     wrapped in a `noncomputable def` via `Matrix.cramer` or
     `Matrix.mulVec_injective_of_invertible` rather than carrying the
     existence proof inline; the well-definedness witness needs
     `h₀ L ‖A‖_∞ < 1` (Banach contraction) and is itself a sub-lemma.
3. **State lem:515A** as `localStageError_bound_a` and
   `localStageError_bound_b` (the two inequalities 515a, 515b). Leave
   the bodies as `sorry`. The textbook's third inequality (515c) is a
   trivial corollary; defer to the same cycle if scope allows,
   otherwise to cycle 101.
4. **Submit Aristotle batch (~5 jobs)** on the sub-bounds *before*
   manual work; sleep 30 min per CLAUDE.md.
5. **Close at minimum one** of the FTC-style sub-lemmas manually
   while Aristotle runs.

A cycle that delivers (1)+(2)+(3)+Aristotle submission is **on
target**; closing one sub-lemma is bonus. The bar is identical to
cycles 040 (lem:406B opened) and 094 (thm:514A scaffolded).

## Concrete sub-lemma decomposition for lem:515A (515a inequality)

Following Butcher §515's proof (p. 412–413), the bound

```
‖Ŷ_i − h Σ a_{ij} f(Ŷ_j) − Σ U_{ij} ŷ_j^{[n-1]}‖
   ≤ h² L² M (½ c_i² + Σ |a_{ij} c_j|)
```

decomposes as `T1 + T2 + T3 + T4` where (textbook quote):

* `T1 = Ŷ_i − y(x_{n-1}) − h ∫₀^{c_i} f(y(x_{n-1} + hξ)) dξ`
* `T2 = y(x_{n-1}) + c_i h y'(x_{n-1}) − Σ U_{ij} ŷ_j^{[n-1]} − Σ a_{ij} h y'(x_{n-1})`
* `T3` — analogous "remaining FTC residual" term (proof_text truncated
  in the entity JSON; extract from `extraction/raw_text/ch05.txt` if
  needed).
* `T4` — the integrated Lipschitz-difference term.

For cycle 100 the worker should:

1. **State (with `sorry`)** five sub-lemmas:
   * `aux_y_diff_norm_bound`: `‖y(x + hξ) − y(x)‖ ≤ |ξ| h L M`
     (Butcher §515 first preliminary; literally `exact_solution_norm_bound_nonauto`
     reused from `Section404.lean:5398`-area helpers if the type
     signature lines up — *check this first; reuse aggressively*).
   * `aux_T1_bound`: bounds `T1 = Ŷ_i − y(x_{n-1}) − h ∫₀^{c_i} f(y(...))`
     via FTC + `intervalIntegral.norm_integral_le_of_norm_le_const`.
   * `aux_T2_bound`: bounds `T2 = y(x_{n-1}) + c_i h y'(x_{n-1}) − Σ U_{ij} ŷ_j^{[n-1]} − Σ a_{ij} h y'(x_{n-1})`
     via the consistency identity `c = A·𝟙 + U·v` and the textbook's
     `ŷ^{[n-1]} = u·y(x_{n-1}) + v·h·y'(x_{n-1})` substitution
     (the lemma's own setup hypothesis).
   * `aux_T3_bound` and `aux_T4_bound`: integrate the FTC remainders
     and apply Lipschitz on `f`.
2. **State lem:515A's two main inequalities** as
   `localStageError_bound_a` and `localStageError_bound_b`, with
   `sorry` bodies and a textbook-comment block citing
   `entities/lem_515A.json`.
3. **Submit Aristotle batch** on `aux_y_diff_norm_bound`,
   `aux_T1_bound`, `aux_T2_bound`, `aux_T3_bound`, `aux_T4_bound`
   — these are exactly the FTC + Lipschitz + norm-bound shapes
   Aristotle handles well (see cycle 040's success on
   `exact_solution_norm_bound`, `residual_integral_form` for
   lem:406B).

## Aristotle batch instructions (Priority 0)

At the **start** of the cycle, before any manual proof work:

```python
mcp__aristotle__submit_directory(
    directory=".prover-state/aristotle_submissions/cycle_100/",
    title="Cycle 100 — §515 lem:515A FTC sub-bounds",
)
```

Submission directory should contain a single Lean file
`sub_lemmas.lean` with the five sorry-first stubs above. Each stub
must be self-contained (importing only `Mathlib.MeasureTheory.Integral.IntervalIntegral.*`,
`Mathlib.Topology.MetricSpace.Lipschitz`) so Aristotle can compile
without the full §510–§514 dependency chain.

After submission: **sleep 30 minutes** (CLAUDE.md mandates this; do
NOT poll repeatedly), then check status **once** and incorporate any
returned proofs.

## Setup details (auxiliary definitions)

### `c = A·𝟙 + U·v`

The vector `c` is parameter-dependent — it lives "under" the
`IsConsistent` hypothesis (which provides `v`). Two encoding choices:

* **(preferred)** Take `c` as a *parameter* of `lem:515A`'s
  hypothesis bundle, with a side condition `c = A·𝟙 + U·v`. This
  matches the textbook structure literally and avoids carrying
  `IsConsistent` derivations through every helper.
* **(rejected)** Define `c M v` as a noncomputable function. This
  works but couples the helpers to the consistency vector `v`,
  which makes `aux_T1_bound` etc. harder to reuse.

### `ℓ : Fin s → ℝ`

Defined implicitly by `(I − h₀L|A|) ℓ = ½ c² + |A| |c|`. For
`h₀ L ‖A‖_∞ < 1` the matrix `(I − h₀L|A|)` is invertible by Neumann
series. The textbook treats `ℓ` as a *given* (it is the unique
solution); Lean will need either:

* `noncomputable def ell M h₀ L c := (I − h₀L|A|)⁻¹ *ᵥ (½ c² + |A|·|c|)`
  with a separate `ell_satisfies` lemma, OR
* `∃ ℓ` introduced as a local `obtain` inside the lem:515A proof.

Pick option 1 (explicit `def`) so `ell` can be reused by `lem:515B`'s
`α = L max |ℓ|` definition next cycle. Well-definedness sublemma
`ell_well_defined` (proves invertibility from `h₀ L ‖A‖_∞ < 1`) gets
its own scaffold; this is **cycle 100 in-scope** and Aristotle can
likely close it via `Matrix.det_ne_zero_of_norm_lt_one` or a
diagonal-dominance argument.

## What NOT to try this cycle

* **Do NOT attempt to close lem:515A in one cycle.** The textbook
  proof is multiple paragraphs; cycles 040–050 took 4 cycles to close
  the analogous lem:406B. Cycle 100 = scaffold + 1–2 sub-lemmas only.
* **Do NOT skip lem:515A and jump to thm:515D.** thm:515D's proof
  cites lem:515A → lem:515B → lem:515C in a tight chain. Skipping
  produces a meaningless top-level shell.
* **Do NOT introduce `axiom` or `constant`** for the `ℓ`-system
  invertibility, the FTC, or the Lipschitz application. CLAUDE.md
  is absolute on this. If the Neumann-series invertibility proof is
  long, file an issue and use Aristotle.
* **Do NOT preemptively re-strengthen `IsConvergent`** with
  additional clauses beyond cycle 098's stage-limit strengthening.
  The strengthening landed; if the §515 proof reveals another gap,
  *file an issue first*, then update the predicate in a focused
  cycle. Do not silently widen.
* **Do NOT increase `maxHeartbeats`** above 200000. Decompose the
  helper into smaller goals.
* **Do NOT use `lake build` to verify** — use
  `lake env lean OpenMath/Chapter5/Section515.lean` for fast feedback.
  Only run `lake build OpenMath.Chapter5.Section515` before
  `#print axioms` to refresh the `.olean` cache (see cycle 072
  discovery: `lake env lean` does NOT refresh the cache, leading to
  stale `sorryAx` false positives).
* **Do NOT chase phantom "stuck" verdicts** if attempts.md
  re-surfaces stale rows. Per cycles 008/014/015/040/068 consultant
  notes, those are loop-maintainer prompt-builder bugs, not real
  blockers. Verify against `HEAD`, then proceed.
* **Do NOT** use unicode `𝟙` as an *identifier suffix* (cycle 099
  discovery: `B𝟙` breaks the parser). Use ASCII (`B1`, `Aone`, etc.)
  for identifiers; reserve `𝟙` for operators and standalone notation.
* **Do NOT** rewrite the cycle 099 closure in §514. It is final and
  axiom-clean.

## Reuse opportunities (check first, do not duplicate)

Before scaffolding new helpers, grep the existing codebase:

* **`exact_solution_norm_bound_nonauto`** (Section404.lean) — check
  if it generalises to `f : ℝ → ℝ` autonomous. If yes, reuse
  verbatim for `aux_y_diff_norm_bound`.
* **`residual_integral_form_nonauto`** (Section404.lean) — same.
* **`Continuous.matrix_mulVec`** — used in cycle 099 §514;
  reusable for stage-equation continuity arguments.
* **`Matrix.norm_mulVec_le`** — for `‖A·v‖ ≤ ‖A‖ ‖v‖` bounds.
* **`tendsto_one_div_atTop_nhds_zero_nat`** — used in cycle 099
  Step 8; reusable for `(1/n) → 0` patterns.

Do `Grep` for the names first; only write a fresh helper if no
reusable form exists.

## Pre-commit faithfulness checklist

Before committing, for each new `def`/`theorem`/`lemma`:

1. **Definitions (`c`, `ell`, etc.)**: open `entities/lem_515A.json`,
   quote the textbook setup, confirm the Lean type matches. The `ell`
   definition is a *consequence* of textbook prose, not a textbook
   `def` per se — document this in the docstring (it is a
   computational helper, not a faithfulness divergence).
2. **`localStageError_bound_a/b`**: the conclusions must exactly
   match the textbook inequalities (515a) and (515b) with all
   absolute values, sums, and coefficients in place. Tautology
   check: do not state `‖x‖ ≤ ‖x‖`.
3. **Hypothesis strength check**: do NOT silently bundle extra
   hypotheses (e.g. `ContDiff ℝ 1 yex` like the LMM strengthening)
   without filing a parallel
   `glm_lem_515A_strengthened.md` issue documenting why.
4. **Absent theorem check**: every `sorry` body must correspond to
   a real proof obligation; no comments promising "to be proved
   below" without an actual scaffold.

## Faithfulness flags to watch

* Butcher's preamble for §515 is autonomous-scalar ODE
  (`y'(x) = f(y(x))`) like §512. Stay autonomous-scalar; do not
  vectorize.
* The lemma quotes `‖y(x)‖ ≤ M`, `‖y'(x)‖ ≤ LM`. These are global
  trajectory bounds — make them explicit hypotheses. Document in
  the docstring as faithful (textbook makes them explicit).
* The lemma takes `h ≤ h₀` with `h₀ L ‖A‖_∞ < 1`. Encode as a side
  condition on the lemma; do NOT bundle inside the GLM structure.

## Issue housekeeping

If lem:515A's proof reveals an unanticipated gap (e.g. Mathlib
missing a Neumann-series invertibility wrapper for `(I − M)` with
`‖M‖ < 1`), file the issue file in `.prover-state/issues/` per
CLAUDE.md format and continue with sorry-first scaffolding.

If Aristotle returns proofs for any of the five sub-bounds,
incorporate verbatim, run `#print axioms` to verify clean, then
delete the corresponding sorry. Manual fallback only if Aristotle
fails.

## Suggested cycle-100 deliverable

* `OpenMath/Chapter5/Section515.lean` exists with scaffold.
* `c` and `ell` definitions in place (with non-vacuity witnesses
  derivable from `explicitEulerGLM` — `c = (1)`, `ell = (1)` after
  the trivial 1×1 system).
* `localStageError_bound_a` and `localStageError_bound_b` stated
  with `sorry` bodies.
* 5 Aristotle jobs submitted in
  `.prover-state/aristotle_submissions/cycle_100/`.
* At least 1 of the 5 sub-bounds closed manually (preferentially
  `aux_y_diff_norm_bound`, since it parallels the cycle 040
  `exact_solution_norm_bound` proof).
* `lake build OpenMath.Chapter5.Section515` clean (with `sorry`s
  acknowledged via `sorryAx`).
* `lean_status.json` row for `lem:515A` set to `partial` with
  pointer to the new file (do NOT mark `formalized` — there are
  sorries).
* Task results document at `.prover-state/task_results/cycle_100.md`.

## Backup plan

If the auxiliary `ell` infrastructure proves harder than expected
(Neumann-series invertibility especially), drop scope to:

* Just create `Section515.lean` with imports and namespace.
* State lem:515A with `c` and `ell` as **parameters** (not defined
  in this cycle). Sorry-first scaffold of the two main inequalities.
* Aristotle batch on the FTC sub-bounds only.
* Save the `c`/`ell` definitions for cycle 101.

This still constitutes meaningful cycle progress (CLAUDE.md
"minimum: decompose a sorry or write an issue" satisfied).
