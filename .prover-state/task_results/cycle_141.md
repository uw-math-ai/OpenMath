# Cycle 141 Results

## Worked on

- Priority 0: poll Aristotle Job A (project `7062c2a2-4a8b-4fae-b694-9355e06427a9`,
  general-`n` `thm:550A`).
- Priority 1: strengthen `def:530A` non-vacuity in
  `OpenMath/Chapter5/Section530.lean` with a **heterogeneous-stages**
  2-method starting-method witness, exercising the dependent-function
  design `stages : Fin r → ℕ` × `method : (i : Fin r) → GeneralizedRungeKuttaMethod (stages i)`.
- Priority 2 (stretch): refutability witness at `r = 2`
  (`zero2StartingMethod_isDegenerate`).

## Approach

### Priority 0
Polled Aristotle Job A once (`mcp__aristotle__get_status`). Reported
6 % at `2026-05-05T20:06`, ~24 h after first submission and ~56 min
after the post-cycle-140 resubmission. Per Priority-0 decision tree
(< 10 %): canceled via `mcp__aristotle__cancel_project`. Did not
re-poll, did not re-submit.

### Priority 1 (heterogeneous-stages witness, ~50 LOC)
Added to `OpenMath/Chapter5/Section530.lean` (between
`zeroStartingMethod_isDegenerate` and `end namespace`):

1. `nontrivialTwoStageGRK : GeneralizedRungeKuttaMethod 2`
   — 2-stage tableau with `c = ![0,0]`, `A = !![0,0; 0,0]`, `b₀ = 2`,
   `b = ![0,0]`. Distinguished from `zeroGeneralizedRK` and any
   `r = 1` tableau by both stage count and `b₀`.

2. `mixedStages : Fin 2 → ℕ` defined by
   ```lean
   | 0 => 1
   | 1 => 2
   ```
   Verified via `lean_multi_attempt` that `mixedStages 0 = 1` and
   `mixedStages 1 = 2` hold by `rfl` (the `Fin` literal pattern-match
   reduces definitionally).

3. `mixedMethod : (i : Fin 2) → GeneralizedRungeKuttaMethod (mixedStages i)`
   defined dependently:
   ```lean
   | 0 => trivialGeneralizedRK     -- type GeneralizedRungeKuttaMethod 1
   | 1 => nontrivialTwoStageGRK    -- type GeneralizedRungeKuttaMethod 2
   ```
   Type-checked because `mixedStages 0 ↝ 1` and `mixedStages 1 ↝ 2`
   reduce on the right branches.

4. `mixedStartingMethod : StartingMethod 2 :=
   { stages := mixedStages, method := mixedMethod }`.

5. `mixedStartingMethod_isNonDegenerate` — proof template identical
   to `trivialStartingMethod_isNonDegenerate`: rewrite via
   `isNonDegenerate_iff_exists_b₀_ne_zero`, exhibit `i = 0`, reduce
   to `(1 : ℝ) ≠ 0`, close with `one_ne_zero`.

6. `mixedStartingMethod_stages_neq :
   mixedStartingMethod.stages 0 ≠ mixedStartingMethod.stages 1` —
   closed with `decide`. **Load-bearing**: confirms the dependent
   `stages : Fin r → ℕ` field captures information the existing
   constant-stages witnesses leave open.

### Priority 2 (stretch, ~10 LOC)
Added `zero2StartingMethod : StartingMethod 2`
(constant `stages = 1`, both methods `zeroGeneralizedRK`) and
`zero2StartingMethod_isDegenerate` closed by `intro i; fin_cases i <;> rfl`.

### Verification gates
- `lean_diagnostic_messages OpenMath/Chapter5/Section530.lean` → empty.
- `lean_verify` on each new theorem (`mixedStartingMethod_isNonDegenerate`,
  `mixedStartingMethod_stages_neq`, `zero2StartingMethod_isDegenerate`)
  → axioms `[propext, Classical.choice, Quot.sound]` only. **No `sorryAx`.**
- `lake build OpenMath.Chapter5` → `2787/2787` green.
- Sorry count across `OpenMath/` (re-checked via comment-stripped grep):
  **0**.

## Result

SUCCESS — all definition-of-done items met (Priority 0 + Priority 1 +
stretch Priority 2). Three new axiom-clean theorems and four new
defs added to `Section530.lean`; sorry count remains 0; full Chapter 5
build green.

## Faithfulness check

This cycle introduces **no new mathematical claims**: it adds witnesses
exercising existing definitions, in the cycle 134/135/137/140 +2
non-vacuity-strengthening pattern.

For each new `def`/`theorem`:

- `nontrivialTwoStageGRK : GeneralizedRungeKuttaMethod 2`
  - Entity: helper witness, not a textbook entity.
  - Faithfulness: a valid inhabitant of the §530 tableau type
    `(c, A, b₀, b)`. No textbook claim.

- `mixedStages : Fin 2 → ℕ`, `mixedMethod : ...`,
  `mixedStartingMethod : StartingMethod 2`
  - Entity: helper witnesses for `def:530A`'s `StartingMethod`
    structure.
  - Faithfulness: §530 (Butcher p. 410) admits *heterogeneous*
    `s_i` per `i = 1, …, r`. The witness exhibits the simplest
    non-trivial case (r = 2, s_1 = 1, s_2 = 2). No textbook divergence.

- `mixedStartingMethod_isNonDegenerate` (axiom-clean):
  - Faithfulness: derives the textbook `def:530A` non-degeneracy
    condition (∃ i, b₀^{(i)} ≠ 0) on the new witness. Captures
    same content as `trivialStartingMethod_isNonDegenerate` at
    `r = 2`.

- `mixedStartingMethod_stages_neq` (axiom-clean):
  - Entity: load-bearing structural-design verification.
  - Faithfulness: states `stages 0 ≠ stages 1` for the new witness.
    No textbook claim — it confirms our **encoding** matches the
    textbook's heterogeneous-stages design (Butcher p. 410: "each
    Sᵢ may have its own stage count s_i").

- `zero2StartingMethod_isDegenerate` (axiom-clean):
  - Faithfulness: same content as `zeroStartingMethod_isDegenerate`
    at `r = 2`. Refutes the dichotomy degenerate-vs-non-degenerate
    being trivial across `r`.

**Tautology check**: none of the new theorems' conclusions appear as
hypotheses (no hypotheses).

**Identity check**: no `exact h`-style proofs. Each proof exhibits
genuine work (witness-index selection, `decide` over a non-trivial
`Fin`-indexed inequality, or `fin_cases`-driven exhaustion).

**Definition smuggling check**: no new `Prop`-valued structures or
classes. The new defs only inhabit existing structures.

**Hypothesis strength check**: theorems take no hypotheses. N/A.

**No new sorry, no new axiom, no maxHeartbeats change.**

## Dead ends

None within Priority 1's deliverables. Pattern-matching `mixedStages`
and `mixedMethod` worked on first attempt — the planner's worry that
`![1, 2]`-style `Fin → ℕ` matchers might not reduce definitionally
was sidestepped by using equation-style pattern definitions
(`| 0 => ... | 1 => ...`), confirmed by `lean_multi_attempt` to give
both `mixedStages 0 = 1` and `mixedStages 1 = 2` by `rfl`.

The Aristotle Job A flatlining at 6 % is itself a dead end — see
`thm_550A_general_n.md` and the discussion below.

## Discovery

1. **Equation-style pattern matching on `Fin n` reduces by `rfl`.**
   `def f : Fin 2 → ℕ | 0 => 1 | 1 => 2` gives both `f 0 = 1` and
   `f 1 = 2` definitionally (verified via `lean_multi_attempt`).
   This is the cleanest way to define heterogeneous dependent
   structures over `Fin` indices — preferred over `Fin.cases`
   (which needs explicit `motive`) and `if-then-else` (which may
   not reduce on `Decidable` instances). Applies to any future
   §530B/C work that needs heterogeneous starting-method witnesses.

2. **Aristotle's `thm:550A` general-`n` job is genuinely intractable
   for the prover.** 24 h, 6 % progress, flat-line. The eigenvalue-
   density / cofactor-induction argument requires too much
   context-specific Mathlib machinery for the prover to assemble
   automatically. Future cycles attacking general-`n` should not
   re-submit — they should plan a manual cofactor-expansion
   induction (see `.prover-state/issues/thm_550A_general_n.md`) or
   absorb the cost of hand-formalising the eigenvalue-density
   argument over a multi-cycle horizon.

3. **The `(i : Fin r) → GeneralizedRungeKuttaMethod (stages i)`
   dependent-function design is now exercised on a non-trivial shape**,
   removing a latent risk that the design might admit no
   heterogeneous inhabitants in practice. This is a structural-
   integrity gain comparable to cycle 134's Padé / matrix-stability
   witness: it converts an *uncoverred* design assumption into a
   *covered* one.

## Suggested next approach

Top-of-queue candidates for cycle 142:

1. **Open `Section520.lean` `def:520F` `IsExplicitGLM` non-vacuity**
   was already strengthened in cycle 137. Skip.

2. **Strengthen `def:520E` non-vacuity** with a *positive* witness
   (a non-zero stable explicit method) — currently only refutability
   is witnessed (cycle 136 negative witness). Estimated 30–50 LOC.
   Risk: requires a concrete stable explicit-Euler-style GLM with
   `IsAStable` proved positively, which may need eigenvalue-spectrum
   bounds. Defer to a focused cycle.

3. **Extend `mixedStartingMethod` to `r = 3` with `stages = ![1, 2, 3]`** —
   cheap +1 LOC strengthening, but Priority 0's blacklist explicitly
   forbids `r > 2` for `mixedStartingMethod` to avoid matcher-complexity
   creep. Skip.

4. **Open `def:540A` (Butcher §540) skeleton** — risk-free section
   opening if the textbook statement is short. Worth a Planner audit
   of §540's first definition.

5. **Pivot to Chapter 4 §442 (principal sheet)** as a fresh section
   opening — cycle 141's Priority 3 backup. Adds breadth across
   chapters and is currently the cheapest open Chapter-4 entry per
   `plan.md`. Recommended primary candidate.

6. **Continue ignoring `thm:550A` general-`n`.** Three cycle attempts
   (138 partial, 140 n=2 stepping stone, 141 cancellation) confirm
   this is multi-cycle infrastructure work, not single-cycle.

**Recommendation for the Planner**: pick one of (4) / (5) for
cycle 142 — ideally (5) §442 to spread chapter coverage. If (5) is
chosen, the Priority-3 sketch in cycle 141's strategy already lays out
the principal-sheet predicate and explicit-Euler witness.
