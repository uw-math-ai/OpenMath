# Cycle 155 Results

## Worked on

Priority 1 from the planner — opened `def:530C` as an axiom-clean
Path A predicate plus two non-vacuity witnesses in
`OpenMath/Chapter5/Section530.lean`.

* `HasOrder_explicit` — existential closure of cycle 153's
  `HasOrderRelativeTo_explicit` over the choice of starting method.
* `explicitEulerGLM_hasOrderZero` — `p=0` non-vacuity witness via
  `trivialStartingMethod` and the cycle-153
  `explicitEulerGLM_hasOrderZero_trivialStarting`.
* `explicitEulerGLM_hasOrderOne` — `p=1` non-vacuity witness via
  `trivialStartingMethod` and the cycle-154
  `explicitEulerGLM_hasOrderOne_trivialStarting`.

Priority 2 (`r = 2` coverage witness) was not attempted — Priority 1
landed cleanly but is the cycle's primary deliverable; the planner
explicitly marked Priority 2 as stretch.

## Approach

Implemented the planner's literal sketch verbatim (Section530.lean
lines ~987–1052, just below `explicitEulerGLM_hasOrderOne_trivialStarting`):

* `HasOrder_explicit` is a closed-form `∃ S, ∃ hS, S.IsNonDegenerate ∧
  HasOrderRelativeTo_explicit M S hS hM p f yex x₀ y₀` — no operator
  bodies to defer, so no sorry-first scaffold.
* Both witnesses follow the same `refine ⟨trivialStartingMethod,
  (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit),
  trivialStartingMethod_isNonDegenerate, ?_⟩` skeleton, then `exact`
  the corresponding cycle 153/154 theorem.

`lake env lean OpenMath/Chapter5/Section530.lean` compiles with no
warnings or errors. Each new declaration verifies axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## Result

SUCCESS. Sorry count remains **0**. Three new axiom-clean
declarations:

* `OpenMath.Chapter5.Section530.HasOrder_explicit` (def)
* `OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderZero`
  (theorem)
* `OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderOne`
  (theorem)

File grew 989 → 1054 LOC (+65 LOC, within the planner's ~50–80 LOC
budget). `def:530C` status `[ ] → [~]` in `plan.md`;
`lean_status.json` updated with `lean_file`, `lean_symbol`, `status:
partial`, `cycle: 155`, plus a notes paragraph mirroring def:530B's
status.

## Faithfulness check

### `def HasOrder_explicit` (entity `def:530C`)

* Textbook statement (quoted from
  `extraction/formalization_data/entities/def_530C.json`):

  > A general linear method `M` has order `p` if there exists a
  > non-degenerate starting method `S` such that `M` has order `p`
  > relative to `S`.

  (Butcher §530, p. 432, def:530C; full LaTeX:
  `\\begin{definition} A general linear method $\\mathbf{M}$ has order
  $p$ if there exists a non-degenerate starting method $\\mathbf{S}$
  such that $\\mathbf{M}$ has order $p$ relative to $\\mathbf{S}$.
  \\end{definition}`)

* Lean statement:

  ```lean
  def HasOrder_explicit
      {s r : ℕ}
      (M : OpenMath.Chapter5.Section510.GeneralLinearMethod s r)
      (hM : M.IsExplicit)
      (p : ℕ)
      (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
    ∃ (S : StartingMethod r) (hS : ∀ i, (S.method i).IsExplicit),
      S.IsNonDegenerate ∧
      HasOrderRelativeTo_explicit M S hS hM p f yex x₀ y₀
  ```

* **Lean statement captures: weaker** — restricted to the explicit
  branch (Path A). The existential `∃ S, S.IsNonDegenerate ∧ …` and
  the relative-order predicate are verbatim from the textbook; the
  divergence is the additional `∀ i, (S.method i).IsExplicit`
  hypothesis on `S` and the `M.IsExplicit` hypothesis.

* **Justification for divergence**: same as def:530B's Path A
  (cycles 151–154). Path B (implicit via fixed-point machinery) is
  multi-cycle infrastructure not justified by current downstream
  demand and is documented as deferred in
  `.prover-state/issues/def_530B_scaffold_strategy.md`. The
  `S.IsNonDegenerate` clause is preserved verbatim from the textbook
  ("there exists a non-degenerate starting method `S`"), and the
  embedded `HasOrderRelativeTo_explicit` is the genuine
  `IsBigO`-based asymptotic from cycle 153 — no definition smuggling
  via algebraic conditions.

* **Definition-smuggling check**: passed. `HasOrder_explicit` does
  NOT redefine "order" via the algebraic conditions characterizing
  it (e.g. order conditions on Butcher tableau coefficients);
  instead it inherits the genuine asymptotic from `HasOrderRelativeTo_explicit`
  and existentially closes over `S`. A future "order conditions"
  characterization theorem (the textbook's Theorem 532A and friends)
  will be a genuine *theorem*, not a definitional rewrite.

### `theorem explicitEulerGLM_hasOrderZero` (non-vacuity witness, no entity)

* Textbook claim being witnessed: explicit Euler is a method (in the
  textbook sense, paired with *some* non-degenerate starting method).
  The `p=0` claim is a non-vacuity stepping stone — Butcher §531
  classifies explicit Euler as order 1, but the `p=0` witness
  guarantees the predicate `HasOrder_explicit` is satisfiable from
  hypotheses present in cycle 153.

* Lean statement:

  ```lean
  theorem explicitEulerGLM_hasOrderZero
      {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
      {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
      (hyex_x₀ : yex x₀ = y₀)
      (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
      HasOrder_explicit explicitEulerGLM explicitEulerGLM_isExplicit
        0 f yex x₀ y₀
  ```

* **Lean statement captures**: same content as cycle-153
  `explicitEulerGLM_hasOrderZero_trivialStarting`, just lifted under
  the existential closure. Hypothesis strength matches cycle 153
  exactly.

* **Tautology check**: passed — the conclusion
  `HasOrder_explicit explicitEulerGLM …` does not appear verbatim in
  the hypotheses.

* **Identity check**: passed — the proof is `refine ⟨…⟩; exact
  <cycle-153 theorem>`, i.e. an existential introduction that does
  real mathematical work (it constructs an explicit witness `S =
  trivialStartingMethod` and proves it satisfies the three
  conjuncts).

### `theorem explicitEulerGLM_hasOrderOne` (non-vacuity witness, no entity)

* Lean statement:

  ```lean
  theorem explicitEulerGLM_hasOrderOne
      {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
      {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
      (hyex_x₀ : yex x₀ = y₀)
      (hyex_C2 : ContDiff ℝ 2 yex)
      (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
      HasOrder_explicit explicitEulerGLM explicitEulerGLM_isExplicit
        1 f yex x₀ y₀
  ```

* **Lean statement captures**: same content as cycle-154
  `explicitEulerGLM_hasOrderOne_trivialStarting` lifted under the
  existential closure. Hypothesis strength matches cycle 154 exactly
  (`ContDiff ℝ 2 yex` + genuine ODE relation
  `∀ x, HasDerivAt yex (f (yex x)) x` + `yex x₀ = y₀` +
  `LipschitzWith L f`).

* **Tautology check**: passed.

* **Identity check**: passed — same existential-introduction shape
  as the `p=0` witness.

### Hypothesis strength check (cross-cutting)

The two witness theorems carry exactly the hypotheses of cycle 153
and cycle 154 respectively, no more no less. The textbook does not
state these specific quantitative hypotheses for explicit Euler at
order 0/1 (it uses the implicit "exact solution sufficiently
regular" assumption); the explicit `LipschitzWith L f`, `ContDiff
ℝ 2 yex`, and `HasDerivAt yex (f (yex x)) x` hypotheses are the
minimal Mathlib-friendly formalization of that implicit regularity,
already documented in cycles 153/154.

## Dead ends

None. The planner's sketch matched the actual Lean shape exactly;
no algebraic surprises, no rewrites needed. The
`(fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)`
incantation matched cycle 153's verbatim.

## Discovery

* **Existential-closure definitions are cheap when the inner
  predicate is already proved at concrete witnesses.** The whole
  Priority 1 deliverable was ~65 LOC because `HasOrderRelativeTo_explicit`
  (cycle 153) plus the cycle 153/154 witnesses did all the
  mathematical work; def:530C just bundles them into the textbook's
  outer existential.

* **`refine ⟨a, b, c, ?_⟩; exact d` is a clean shape for
  axiom-cleanness verification** — no `obtain`, no `cases`, no
  rewrites that could introduce stray axioms beyond
  `[propext, Classical.choice, Quot.sound]`.

## Suggested next approach

For cycle 156 the natural follow-up is one of:

1. **Priority 2 of cycle 155** — the deferred `r = 2` coverage
   witness `padded2DEulerGLM_hasOrderZero_mixedStarting`. Concretely:
   - Add `padded2DEulerGLM_isExplicit` (a one-line `fin_cases`
     proof; the `A` block is the zero matrix).
   - Add `mixedStartingMethod_isExplicit` (one-line `fin_cases`
     over `Fin 2`).
   - Apply `HasOrderRelativeTo_explicit` at `r = 2`. Row 1 is the
     zero channel of `padded2DEulerGLM`, so SM[1] = ES[1] = 0 and
     the diff is identically zero — immediate `IsBigO` via
     `Asymptotics.isBigO_zero`. Row 0 reduces to a closed form
     close to cycle 153's. Estimated ~80 LOC if the algebra at
     i=0 mirrors cycle 153 closely.

2. **Open `def:525A`** — uses `def:530C`. With def:530C's predicate
   now landed, downstream consumers can be unblocked.

3. **Open `thm:532A`** — the textbook's first theorem about
   `HasOrder` (Butcher §532), which gives the order conditions
   characterization. This is probably the canonical next step,
   since it's where the genuine mathematical content of "having
   order p" is unpacked into computable conditions on the GLM
   tableau coefficients.

I lean toward (1) for cycle 156 — it's the natural completion of
cycle 155's coverage story, the planner has already sketched it,
and it doesn't open new infrastructure. Then (3) for cycle 157.
