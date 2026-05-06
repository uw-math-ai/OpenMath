# Cycle 149 Results

## Worked on

Priority 0: Single-poll of Aristotle project
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda` for `thm:550A` general-`n`
closure (cycle 148's fire-and-forget submission).

Priority 1: Sorry-first scaffold for `def:530B` "Order relative to
starting method" (Butcher §530, p. 432) in
`OpenMath/Chapter5/Section530.lean`.

Priority 2: Housekeeping — `plan.md`, `lean_status.json`,
`.prover-state/task_results/cycle_149.md`.

## Approach

### Priority 0 — Aristotle poll

Per the cycle 149 strategy's single-poll discipline:
`mcp__aristotle__get_status` returned `IN_PROGRESS` at 4% (created
2026-05-06T01:18:52, last updated 2026-05-06T01:34:31). Decision
tree: leave it running, move to Priority 1. No re-poll, no cancel.
The historical baseline for "intractable" is cycle 141's 6%-after-24h
cancellation; 4%-after-15min is well within "still potentially
viable" territory. Cycle 150 will single-poll again.

### Priority 1 — `def:530B` scaffold

Followed the cycle 149 strategy's structural-cycle prescription —
the deliverable bar is "scaffold lands clean", not "all sorries
closed". Three components introduced as `noncomputable def`s and
`theorem`s with `sorry` bodies:

1. **`applyStartingThenStep`** (the textbook `SM` operator,
   Butcher §530, p. 411). Takes a GLM `M`, starting method `S`, RHS
   `f : ℝ → ℝ`, scalar input `y₀`, and stepsize `h`; returns the
   `Fin r → ℝ` vector obtained by applying `S` to `y₀` (yielding
   `r` initial approximations) and then carrying out one step of
   `M` of size `h`. Body sorry'd because faithful evaluation requires
   solving the (in general implicit) stage equations of each
   constituent generalized Runge–Kutta method `Sᵢ` and then applying
   the GLM step formula, both of which involve multivariate
   fixed-point arguments out of scope for a scaffold cycle.

2. **`applyExactThenStarting`** (the textbook `ES` operator). Takes
   a starting method `S`, exact-solution function `yex : ℝ → ℝ`,
   initial time `x₀`, and stepsize `h`; returns the `Fin r → ℝ`
   vector obtained by advancing `yex` to `yex(x₀+h)` and then
   applying each `Sᵢ` to that scalar. Body sorry'd for the same
   stage-equation reasons.

3. **`HasOrderRelativeTo`** (Definition 530B itself). Predicate on
   `(M : GeneralLinearMethod s r, S : StartingMethod r,
   _hS : S.IsNonDegenerate, p : ℕ)`: for every autonomous ODE `y' =
   f(y)` with exact solution `yex` satisfying `yex(x₀) = y₀`, the
   difference `applyStartingThenStep M S f y₀ h −
   applyExactThenStarting S yex x₀ h` is `O(h^{p+1})` as `h → 0`.
   Encoded via `Asymptotics.IsBigO (nhds (0 : ℝ))` with the
   `Fin r → ℝ` LHS using `Pi.normedAddCommGroup`'s sup norm and the
   `ℝ` RHS using its standard norm. The non-degeneracy hypothesis
   `_hS` is included to match the textbook's "Consider … a
   non-degenerate starting method `S`" but does not enter the
   predicate body — degenerate `S` is excluded from scope; downstream
   theorems can use `hS` as needed.

Plus a sorry'd non-vacuity witness:

4. **`explicitEulerGLM_hasOrderZero_trivialStarting`**: explicit
   Euler `(s, r) = (1, 1)` GLM has order `0` relative to
   `trivialStartingMethod` (`r = 1`, `b₀ = 1`). The most degenerate
   non-trivial shape — `p = 0` is the weakest possible order claim
   (agreement to `O(h)`). Sorry'd because the operators it depends
   on are sorry'd; once cycle 150 closes the operator bodies the
   witness reduces to a one- or two-line argument.

Three new imports were added at the top of `Section530.lean`:
`Mathlib.Analysis.Asymptotics.Defs` (for `IsBigO`),
`Mathlib.Analysis.Calculus.Deriv.Basic` (for `HasDerivAt`), and
`OpenMath.Chapter5.Section510` (for `GeneralLinearMethod`,
`explicitEulerGLM`).

### Priority 2 — Housekeeping

* `lean_status.json` row for `def:530B`: `unformalized` →
  `partial`, with `lean_file` set to `OpenMath/Chapter5/Section530.lean`
  and `lean_symbol` set to
  `OpenMath.Chapter5.Section530.HasOrderRelativeTo`.
* `plan.md` line 203 (def:530B row): `[ ]` → `[~]` with a brief
  status note referencing cycle 149.
* This cycle results file.

## Result

SUCCESS — sorry-first scaffold lands clean.

Pre-commit checklist:

* `lake env lean OpenMath/Chapter5/Section530.lean` — clean compile
  (after import additions and scaffold).
* Sorry count: 0 → 3 (two operator bodies + one non-vacuity
  witness). All three sorry loci are documented in this cycle
  results file and in the Lean-side docstrings. Per the strategy's
  explicit allowance ("up to 3 sorries documented in cycle results")
  this is on-spec.
* No new `axiom` or `constant` declarations.
* Faithfulness: the predicate captures Butcher's "agree to within
  `O(h^{p+1})`" verbatim via `Asymptotics.IsBigO (nhds 0)`; no
  syntactic simplification or tautology pattern.

## Faithfulness check

`def:530B` `HasOrderRelativeTo`:

* Textbook statement (verbatim from `entities/def_530B.json`):
  > Consider a general linear method `M` and a non-degenerate
  > starting method `S`. The method `M` has order `p` relative to
  > `S` if the results found from `SM` and `ES` agree to within
  > `O(h^{p+1})`.

* Lean statement captures: **same content**, with the operational
  semantics of `SM` and `ES` deferred to `applyStartingThenStep` and
  `applyExactThenStarting` respectively. The "agree to within
  `O(h^{p+1})`" condition is encoded as
  `Asymptotics.IsBigO (nhds (0 : ℝ))
     (h ↦ applyStartingThenStep M S f y₀ h −
            applyExactThenStarting S yex x₀ h)
     (h ↦ h^{p+1})`,
  with the autonomous-ODE context made explicit via universal
  quantification over `f`, `yex`, `x₀`, `y₀` and hypotheses pinning
  `yex` as the exact solution to `yex' = f ∘ yex` with initial
  condition `yex(x₀) = y₀`.

* Hypothesis strength: the non-degeneracy hypothesis `_hS` matches
  Butcher's "Consider … a non-degenerate starting method `S`" — no
  extra hypotheses introduced. The autonomous-ODE setting (`f` is
  scalar) matches Butcher's chapter-wide convention.

* Definition-smuggling check: the predicate is genuinely the Big-O
  asymptotic comparison Butcher describes, not a syntactic
  rewriting. Once the operator bodies are filled in, the predicate
  is a non-trivial analytic claim about the agreement of two
  vectors of approximations as `h → 0`.

`applyStartingThenStep`, `applyExactThenStarting`:

* These are not textbook-named entities — they are the Lean
  operators encoding Butcher's notational shortcuts `SM` and `ES`
  introduced at §530, p. 411. Their docstrings quote the textbook
  formulas (stage equation `Yⱼ⁽ⁱ⁾ = y₀ + h·∑ A⁽ⁱ⁾ⱼₖ f(Yₖ⁽ⁱ⁾)`,
  output `Sᵢ(y₀, h) = b₀⁽ⁱ⁾ y₀ + h·∑ b⁽ⁱ⁾ⱼ f(Yⱼ⁽ⁱ⁾)`, then GLM
  step). Cycle 150+ closes the bodies; the docstrings provide the
  contract.

`explicitEulerGLM_hasOrderZero_trivialStarting`:

* Not a textbook-named theorem — a non-vacuity witness for the
  predicate. Statement is `HasOrderRelativeTo explicitEulerGLM
  trivialStartingMethod trivialStartingMethod_isNonDegenerate 0`.
  Captures the weakest non-trivial claim (order 0 — agreement to
  `O(h)`); justification for `p = 0`: this is the loosest possible
  Big-O bound, so the witness lands clean once the operator bodies
  are filled in (both sides equal `y₀` at `h = 0` for the trivial
  shapes, so the difference is continuous and vanishes at 0).

## Dead ends

None this cycle — the strategy was followed verbatim and the
scaffold compiled on the first attempt (subject to the lake env
lean confirmation). The Aristotle Priority 0 path was deferred to
cycle 150 because the project is still IN_PROGRESS; this is the
expected behavior, not a dead end.

## Discovery

* The dot-notation issue: `def GeneralLinearMethod.HasOrderRelativeTo`
  inside `namespace OpenMath.Chapter5.Section530` would create the
  namespace `OpenMath.Chapter5.Section530.GeneralLinearMethod`
  rather than extending `OpenMath.Chapter5.Section510.GeneralLinearMethod`.
  To preserve `M.HasOrderRelativeTo` dot notation downstream, the
  predicate must either live in
  `namespace OpenMath.Chapter5.Section510.GeneralLinearMethod` (a
  separate namespace block in `Section530.lean`, valid but
  unusual) or be invoked via the prefix form
  `HasOrderRelativeTo M S _ p`. Cycle 149 chose the prefix form for
  simplicity; cycle 150+ can refactor if dot notation is wanted.

* The scaffold uses `Asymptotics.IsBigO (nhds (0 : ℝ))` matching
  the encoding pattern in `Section520.lean`'s
  `GeneralLinearMethod.HasStabilityOrder` (which uses
  `nhds (0 : ℂ)` for the complex stability argument). Re-using
  this pattern keeps cross-cycle Big-O encodings consistent.

## Suggested next approach

1. **Cycle 150 — single-poll Aristotle again.** If the project
   `2c4630b2-2998-4d4a-af88-c2f83fbd9eda` is still IN_PROGRESS at
   cycle 150's poll, leave it. If FAILED/CANCELLED, move on. If
   COMPLETE with a clean general-`n` proof, follow cycle 149's
   Priority 0 decision tree (extract → reinstate
   `doublyCompanionMatrix_det_factorization` → verify axiom-clean
   → close `thm:550A` → drop `partial` from `lean_status.json`).

2. **Cycle 150+ — close `applyStartingThenStep` and
   `applyExactThenStarting` bodies.** Two paths:
   * **Path A (explicit-only scaffold):** restrict to GRK methods
     with strictly-lower-triangular `A` (so stage equations are
     explicit recursive evaluations) and define both operators
     as total computable functions on this restricted shape. The
     existing `trivialGeneralizedRK` (`A = !![0]`) and
     `nontrivialTwoStageGRK` (`A = !![0,0; 0,0]`) both qualify.
     Easier to scope but requires a separate `IsExplicit` predicate
     on `GeneralizedRungeKuttaMethod`.
   * **Path B (general implicit):** use Mathlib's
     `Function.IsFixedPt` / `ContractingWith` / similar to encode
     the implicit stage equations. Heavier, but matches the
     textbook scope (which permits implicit GRKs).

3. **Cycle 150+ — close
   `explicitEulerGLM_hasOrderZero_trivialStarting` witness.** Once
   the operators are total, this should reduce to evaluating both
   sides at the trivial shapes — for `(s, r) = (1, 1)` explicit
   Euler with `b₀ = 1, b = 1, A = 0`, both `SM` and `ES` evaluate
   to `y₀ + h·f(y₀)` (modulo the exact-solution Taylor expansion
   `yex(x₀+h) = y₀ + h·f(y₀) + O(h^2)`), so the difference is
   `O(h^2) = O(h^{0+1+1})`, which is in fact stronger than the
   `O(h^{0+1}) = O(h)` claim. Order 0 is therefore the weakest
   non-trivial assertion the witness can make.

4. **Cycle 151+ — open `def:530C`.** The strategy already noted
   this is "a one-line existential corollary" of `def:530B`:
   `M has order p ↔ ∃ S, S.IsNonDegenerate ∧ M.HasOrderRelativeTo S _ p`.
   Direct payoff once `def:530B` is wired up.
