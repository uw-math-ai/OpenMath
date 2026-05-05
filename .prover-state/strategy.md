# Cycle 137 Strategy

## Context

Cycle 136 closed `explicitEulerGLM_not_isAStable` (negative A-stability
witness for `def:520E`), completing the non-vacuity triangle for that
predicate (trivial-positive, substantive-positive, negative). The
cycle 136 task results recommended `¬ explicitEulerGLM.IsLStable`
as the natural single-cycle follow-up.

We will follow that recommendation **and** add a second L-stability
result that genuinely strengthens the non-vacuity story for `def:520F`:
a proof that `implicitMidpointGLM` — the cycle 135 *positive*
A-stability witness — is **not** L-stable. This pair reproduces the
textbook contrast (Padé(1,1) is A-stable but not L-stable, see
Butcher §520, p. 419) and broadens `IsLStable`'s non-vacuity into
the same triangle shape `def:520E` now has.

There are no Aristotle results to incorporate this cycle.

## Tasks (in order)

### Task 1 — `explicitEulerGLM_not_isLStable` (one-line follow-up)

**Target file**: `OpenMath/Chapter5/Section520.lean`, immediately
after the cycle 136 theorem `explicitEulerGLM_not_isAStable`.

**Definition shape** (verified — `Section520.lean:298–304`):

```lean
def GeneralLinearMethod.IsLStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  M.IsAStable ∧
  Filter.Tendsto
    (fun z : ℂ => spectralRadius ℂ (M.stabilityMatrix z))
    (Filter.cocompact ℂ)
    (nhds 0)
```

**Proof**: since `IsLStable` is `IsAStable ∧ ...`, the negation
follows from cycle 136's `explicitEulerGLM_not_isAStable` by
projecting the conjunction:

```lean
/-- Negative non-vacuity witness for `def:520F`: `explicitEulerGLM`
is not L-stable, since L-stability requires A-stability and cycle 136
showed `explicitEulerGLM` is not A-stable. -/
theorem explicitEulerGLM_not_isLStable :
    ¬ explicitEulerGLM.IsLStable :=
  fun h => explicitEulerGLM_not_isAStable h.1
```

That's it. Verify with `lake env lean OpenMath/Chapter5/Section520.lean`
and `#print axioms` (expect `[propext, Classical.choice, Quot.sound]`).

### Task 2 — `implicitMidpointGLM_not_isLStable` (substantive negative witness)

**Target file**: same — append after Task 1.

**Mathematical content**: `implicitMidpointGLM` has stability function
`R(z) = (1 + z/2)/(1 − z/2)` (cycle 135). As `|z| → ∞`, `|R(z)| → 1`,
so `spectralRadius (M(z)) → 1`, not `0`. Hence `IsLStable`'s
`Tendsto … cocompact … (nhds 0)` clause fails.

**Proof recipe** (planner sketch — verify each lemma name with
`lean_local_search` / `lean_loogle` before committing):

1. Specialize the negation by destructuring the conjunction; we
   attack the second conjunct
   `Tendsto (fun z => spectralRadius (M(z))) cocompact (𝓝 0)`.

2. Pick a divergent witness sequence in the **closed left half-plane**
   so cycle 135's `implicitMidpointGLM_stabilityMatrix` (which
   carries the `z.re ≤ 0` hypothesis) fires directly. Recommended:
   `n : ℕ ↦ (-(n + 2 : ℝ) : ℂ)`. Then `(-(n+2)).re = -(n+2) ≤ 0`,
   and `|R(-(n+2))| = |(1 - (n+2)/2) / (1 + (n+2)/2)|
                    = |(-n/2)/((n+4)/2)| = n/(n+4) → 1` as `n → ∞`.

3. Compute `spectralRadius` of `!![a]` for `a : ℂ`. The 1×1
   matrix's spectrum is `{a}`, so `spectralRadius ℂ !![a] = ‖a‖₊`.
   Useful tools to search for first:
   - `lean_local_search "spectralRadius"` — look for an
     existing 1×1 lemma.
   - If absent, prove a tiny private helper
     `spectralRadius_of_fin_one : spectralRadius ℂ !![a] = ‖a‖₊`
     reusing the cycle-135 `fin_one_pow` / `norm_fin_one` style.

4. Show `‖R(-(n+2))‖ = n/(n+4)`. Use the cycle-135 private
   `norm_fin_one` to extract the scalar norm; then
   `Complex.norm_div`, `Complex.norm_real`, and `abs_of_nonneg`
   to reduce to `n/(n+4)`.

5. Show `(n : ℝ) → ∞` ⇒ `n/(n+4) → 1`. Mathlib lemma:
   `Filter.Tendsto.div` or via
   `(n+4)/(n+4) - 4/(n+4) = n/(n+4)` and `4/(n+4) → 0`. Search
   `lean_loogle "Tendsto _ _ atTop _ (nhds 1)"` for a direct hit.

6. Bridge subsequence-divergence to `cocompact`-divergence: the
   embedding `(fun n : ℕ => -(n+2 : ℂ))` tends to `cocompact ℂ`
   along `Filter.atTop`. Find via
   `lean_loogle "Tendsto _ Filter.atTop (Filter.cocompact ℂ)"`.
   The standard pattern is `Filter.tendsto_norm_atTop` plus the
   cocompact-iff-norm-tends-to-infinity characterisation
   (`Complex.tendsto_norm_atTop_iff_cocompact` or similar — verify
   name).

7. Conclude `¬ IsLStable` via `Filter.Tendsto.unique` (the parent
   net would force the sub-net to converge to `0`; we have the
   sub-net converging to `1`; `0 ≠ 1`).

**Estimated LOC**: 40–60 lines, depending on how much of the
spectralRadius-of-1×1 plumbing already exists.

**Mathlib search to do FIRST** (do not skip — this is where the
estimate could blow up):

- `lean_local_search "spectralRadius"` plus `"fin"` for the 1×1
  spectralRadius lemma.
- `lean_loogle "Tendsto _ Filter.atTop (Filter.cocompact ℂ)"` for the
  `(n : ℂ)` → cocompact bridge.
- `lean_local_search "spectrum_one_eq_singleton"` (verify name).
- `lean_local_search "tendsto_norm_atTop_iff_cocompact"` for the
  cocompact characterisation.

If the spectralRadius-of-1×1 plumbing or the cocompact bridge turns
out to require nontrivial new infrastructure (>30 LOC by itself),
fall back per Backup B1 below.

## What NOT to try

- **Do NOT redo cycle 136 work.** `explicitEulerGLM_not_isAStable`
  is already in `Section520.lean` (axiom-clean). Task 1 invokes it
  directly via `h.1` — do not re-derive the matrix-norm bound.

- **Do NOT use cycle 135's `implicitMidpointGLM_stabilityMatrix`
  closed form on a positive-real `z`.** That lemma carries the
  hypothesis `z.re ≤ 0`; calling it with `z = (n : ℂ)` for `n ≥ 1`
  fails the hypothesis. Use the negative-real witness sequence
  `n ↦ -(n+2 : ℂ)` (or equivalent left-half-plane divergent
  sequence) instead.

- **Do NOT raise `maxHeartbeats`.** If Task 2 stalls on a single
  goal, decompose into private helpers (`spectralRadius_at_neg_n`,
  `padeOneOne_norm_neg_n_eq`, etc.).

- **Do NOT introduce `axiom` or `constant`** for any
  spectralRadius / Filter / cocompact lemma. If Mathlib lacks
  exactly the bridge you want, prove it as a private helper in the
  same file (the cycle 135 pattern: small private bridges
  `fin_one_pow`, `norm_fin_one`, `norm_pow_fin_one` for analogous
  matrix-norm reductions).

- **Do NOT expand scope to other `def:520F` witnesses or pivot to
  Padé order analysis (`HasStabilityOrder 2`).** Cycle 136 task
  results listed those as backup paths; they are >150 LOC and
  belong in their own cycle.

- **Do NOT touch Chapter 3 / 4 entries this cycle.** Tempting
  options like `def:381F` (P-equivalent — blocked on `def:381E`'s
  deferred `reducedMethod` per
  `.prover-state/issues/reduced_method_deferred.md`), `def:530A`
  (needs StartingMethod structure), `thm:431A` (needs Rouché's
  theorem), `def:451A` (needs one-leg method + matrix M from
  (451e)), and `thm:343B` (needs `B(η)/C(η)/D(η)/E(η,ζ)` simplifying
  assumptions) are all multi-cycle infrastructure investments and
  are out of scope for cycle 137.

- **Do NOT submit Aristotle for Task 1 or Task 2.** Both are short
  and tightly coupled to private helpers we control. The 30-min
  round-trip cost dominates the per-task work; manual is faster
  (matching cycle 134/135/136's pattern).

## Backup plans

### B1 — if Task 2's spectralRadius / cocompact plumbing requires >40 LOC by itself

Defer Task 2's *rigorous* implementation. In its place, file an
issue
`.prover-state/issues/lstable_negative_implicit_midpoint_deferred.md`
documenting the mathematical fact and the Mathlib gap (e.g.
"missing `spectralRadius` of 1×1 matrix lemma; specific name to
build is `Matrix.spectralRadius_fin_one_eq_nnnorm`"). Land Task 1
alone; the cycle still produces a non-zero net change (Task 1 +
issue file). This satisfies CLAUDE.md's "minimum: decompose a sorry
or write an issue" rule.

### B2 — if Task 2 is *easy* (<30 LOC) with existing plumbing

Bonus: also add a vacuous L-stability witness for `padded2DEulerGLM`
(cycle 133/134's r=2 padded explicit Euler GLM). Read
`Section520.lean` to confirm its stability matrix shape; if it has
the explicit-Euler block structure that fails A-stability at
`z = -3`, mirror Task 1's pattern with `padded2DEulerGLM_not_isAStable`
followed by `padded2DEulerGLM_not_isLStable`. This is one-liner
mirroring of Task 1 once the negative A-stability witness lands.

### B3 — if BOTH tasks close cleanly with time to spare

Read `extraction/formalization_data/entities/def_530A.json` (already
inspected: requires building a `StartingMethod` structure with
generalized Runge–Kutta methods and `b_0^{(i)}` coefficients —
**NOT a single-cycle deliverable**). Do NOT start the implementation;
instead, file an infrastructure issue
`.prover-state/issues/starting_method_structure_needed.md`
documenting the prerequisites for §530.

## Pre-commit faithfulness checklist (per CLAUDE.md)

For each new theorem this cycle:

- [ ] Tautology check: conclusion is `¬ IsLStable …` — not
  syntactically equal to any hypothesis.
- [ ] Identity check: Task 1 is `fun h => ... h.1` (∧-projection,
  not the identity function — the projection itself does
  meaningful work selecting the A-stable conjunct). Task 2 does
  real norm/spectral computation. Neither is `exact h`/`id` over
  the goal.
- [ ] Hypothesis-strength check: theorems take no hypotheses.
- [ ] Definition smuggling check: `IsLStable` was defined faithfully
  in cycle 088 (`IsAStable ∧ spectralRadius → 0`); we are
  *negating* it for specific GLMs, not redefining.
- [ ] Absent-theorem check: no `sorry` or "to be proved later"
  comments anywhere in the new theorems' bodies.
- [ ] No new structures introduced; no need to provide instances.

## Updates to make alongside the proofs

- `extraction/formalization_data/lean_status.json`: `def:520F` row —
  bump `cycle` field to 137 and refresh notes to mention both
  the trivial positive (cycle 088) and the new negative witness(es).
  Keep `status: formalized` (no change).
- `plan.md`: §520 row for `def:520F` — append cycle-137 note about
  negative witness completing the non-vacuity story.
- `.prover-state/task_results/cycle_137.md`: standard format per
  CLAUDE.md (Worked on / Approach / Result / Faithfulness check /
  Dead ends / Discovery / Suggested next approach).

## Suggested cycle 138 direction (for the next planner)

After cycle 137 lands, the non-vacuity story for `def:520E`,
`def:520F`, `def:525A`, `def:542A`, `def:551A` will all have at
least one substantive witness, and `def:520E` and `def:520F` will
have negative witnesses. The natural next step is to **shift away
from non-vacuity strengthening** and attack a real theorem:

- `thm:551B` Single Non Zero Eigenvalue Stability — small statement,
  builds on cycle 131/133's `def:551A`.
- `thm:521B` Maximum stability order for given steps — small
  statement, builds on `def:521A`.
- `thm:550A` Doubly companion matrices — pure linear algebra,
  potentially Mathlib-light.

Cycle 138 planner should pick one and commit; the
non-vacuity-strengthening cadence (cycles 128–137) has consumed
~10 cycles and should yield to substantive theorem work.
