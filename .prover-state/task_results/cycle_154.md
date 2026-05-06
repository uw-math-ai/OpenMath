# Cycle 154 Results

## Worked on

* **Priority 0** (cosmetic, ~5 min): cycle-153 tautology-scanner
  false-positive rename inside
  `OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderZero_trivialStarting`
  (`h_deriv → hderiv`), per the standard workaround in
  `.prover-state/issues/tautology_scanner_false_positives.md`.
* **Priority 1** (substantive): def:530B Path A Step 4 — added
  `OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderOne_trivialStarting`,
  the `p = 1` axiom-clean non-vacuity witness for explicit Euler GLM
  × `trivialStartingMethod`. Continues the def:530B Path A chain
  toward Butcher §531's classification of explicit Euler as order 1
  relative to the canonical starting method.

## Approach

### Priority 0
Two-touch-point `Edit` in `OpenMath/Chapter5/Section530.lean` lines
711 and 717 (the `have h_deriv : ... := ...` introduction and the
`have := h_deriv` reuse). Verified `lake env lean ...` exits 0 and
`lean_verify ...explicitEulerGLM_hasOrderZero_trivialStarting`
remains `[propext, Classical.choice, Quot.sound]` (rename is
α-equivalent). Post-rename scanner regex
`grep -n ':=\s*h_\w*\s*$\|exact\s\+h_\w\+\s*$\|:=\s*id\s*$' OpenMath/Chapter5/Section530.lean`
returns no hits.

### Priority 1
Sorry-first scaffold of the new theorem; copied the cycle-153
boilerplate verbatim for `intro i; fin_cases i; change …; hSM; hES;
hcongr; rw [hcongr]` and adjusted only the `h^(0+1) → h` collapse to
`h^(1+1) → h^2`. Two sorry's at the T1/T2 split. Then closed both
manually (no Aristotle, per strategy "Things to NOT try" item 1):

* **T1 = O(h²)** (Taylor route):
  1. `htaylor` from `taylor_isLittleO (n := 2) (s := Set.univ)`
     applied with `convex_univ`, `Set.mem_univ _`,
     `hyex_C2.contDiffOn`; `simpa [nhdsWithin_univ]` to convert
     `nhdsWithin x₀ Set.univ` → `nhds x₀`.
  2. `hT_eval` evaluates
     `taylorWithinEval yex 2 Set.univ x₀ (x₀ + h)
        = yex x₀ + h · iteratedDeriv 1 yex x₀
            + h²/2 · iteratedDeriv 2 yex x₀`
     via `rw [taylor_within_apply]` + `simp_only [Finset.sum_range_succ,
     Finset.sum_range_zero, zero_add, iteratedDerivWithin_univ,
     iteratedDeriv_zero, Nat.factorial, Nat.cast_one, Nat.cast_mul,
     smul_eq_mul, pow_zero, pow_one, mul_one, one_mul, inv_one]`
     followed by `ring`.
  3. `hderiv_x0 : iteratedDeriv 1 yex x₀ = f y₀` via `iteratedDeriv_one`
     + `(hyex_ode x₀).deriv` + `rw [hyex_x₀]`.
  4. Compose `htaylor` with `h ↦ x₀ + h` via
     `Asymptotics.IsLittleO.comp_tendsto`, then `congr'` away
     `((x₀+h) - x₀)^2 = h^2`.
  5. Algebraic rewrite of T1 to
     `T1(h) = -(yex(x₀+h) - taylor₂(x₀+h)) - (h²/2) · iteratedDeriv 2 yex x₀`
     via `funext + rw [hT_eval, hderiv_x0, hyex_x₀]; ring`.
  6. Constant-times-h² is O(h²) via
     `Asymptotics.isBigO_const_mul_self (iteratedDeriv 2 yex x₀ / 2) ...`
     after `congr'` to align the multiplication shape.
  7. Sum (`hres.isBigO.add hconst`) then `.neg_left` and `congr'`
     to land the final form.

* **T2 = O(h²)** (Lipschitz + T1 bound):
  1. `obtain ⟨C, hCpos, hC⟩ := hT1.exists_pos`, then
     `Asymptotics.isBigOWith_iff` to extract
     `‖T1(h)‖ ≤ C · ‖h²‖` eventually with `C > 0`.
  2. Eventual `|h| ≤ 1` near 0 via
     `Filter.eventually_iff_exists_mem` + `Set.Ioo (-1) 1 ∈ nhds 0`.
  3. `Asymptotics.IsBigO.of_bound (↑L * C)` with calc chain:
     `‖h · (f a − f b)‖ = |h| · |f a − f b|
        ≤ |h| · L · |a − b|` (Lipschitz via `hf_lip.dist_le_mul`)
        `= L · (|h| · |a − b|)
        ≤ L · (|h| · (C · |h²|))` (from `hT1bound`)
        `= L · C · (|h| · h²)
        ≤ L · C · (1 · h²)` (from `hh1bound`)
        `= L · C · ‖h²‖`.

* **Combine**: `hT1.add hT2` closes the goal.

## Result

**SUCCESS.**

* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0
  (no warnings, no errors).
* `grep -c sorry OpenMath/Chapter5/Section530.lean` → 0.
* `lean_verify
  OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderOne_trivialStarting`
  → `[propext, Classical.choice, Quot.sound]` (axiom-clean).
* `lean_verify
  OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderZero_trivialStarting`
  → `[propext, Classical.choice, Quot.sound]` (axiom-clean preserved
  through the rename).
* Tautology scanner regex returns no hits.
* File: 779 → 989 LOC (+210 LOC, including the new theorem
  + docstring + 2 new imports).
* Imports added: `Mathlib.Analysis.Calculus.Taylor`,
  `Mathlib.Analysis.Calculus.IteratedDeriv.Defs`.

## Faithfulness check

For `explicitEulerGLM_hasOrderOne_trivialStarting`:

* **Entity ID + textbook statement**: this is a Lean-internal
  non-vacuity witness for `HasOrderRelativeTo_explicit`, NOT a
  textbook-numbered entity. Butcher §531 (immediately after def:530B)
  classifies explicit Euler as order 1 in the GLM framework
  (consistent with the conclusion `p = 1`).
* **Lean statement captures**: same content as Butcher's
  classification, with documented hypothesis upgrades from cycle 153:
  * `HasDerivAt yex (f y₀) x₀` → `∀ x, HasDerivAt yex (f (yex x)) x`
    (genuine ODE relation; needed because the Taylor expansion uses
    `deriv yex` at `x₀` which must equal `f(yex x₀) = f y₀`).
  * `ContDiff ℝ 2 yex` newly added (needed for the second-order
    Taylor remainder bound).
  Both upgrades are well within Butcher's implicit "exact solution
  sufficiently regular" assumption.
* **Tautology check**: conclusion
  `HasOrderRelativeTo_explicit … 1 …` does not appear verbatim in
  any hypothesis. The hypotheses provide regularity + ODE structure;
  the conclusion is a quantitative asymptotic claim about the SM−ES
  difference. Genuine theorem.
* **Hypothesis strength check**: `ContDiff ℝ 2` is the minimal
  regularity for second-order Taylor — `ContDiff ℝ 1` only yields
  `O(h)` (the cycle-153 statement). The full ODE relation is the
  cleanest hypothesis that gives `deriv yex x₀ = f y₀`; cycle 153's
  `HasDerivAt yex (f y₀) x₀` is a strictly weaker special case but
  insufficient for the Taylor argument's higher-order chain rule
  step (which needs `yex'` defined nearby, not just at `x₀`).
* **Identity check**: proof is multi-step (Taylor remainder + closed-
  form expansion + composition + Lipschitz + IsBigO arithmetic),
  not a single `exact h_*`. Not vacuous.
* **Absent theorem check**: post-build `lean_verify` confirms the
  theorem exists and is axiom-clean.

## Dead ends

None this cycle. The strategy's "search-first protocol" identified
`taylor_isLittleO_univ` immediately via leansearch, but that name
turned out to be in a newer Mathlib than this project pins;
substituted with `taylor_isLittleO` + `Set.univ` arguments + `simpa
[nhdsWithin_univ]`. One-line adjustment.

A brief intermediate dead end: `simp only` on `taylor_within_apply`
output left an `iteratedDeriv 0 yex x₀` factor uncollapsed, so
`ring` couldn't close. Adding `iteratedDeriv_zero` to the simp set
resolved it. Net cost: ~5 min of iteration with `lean_diagnostic_messages`.

## Discovery

* `taylor_isLittleO` + `Set.univ` is a clean, search-friendly path
  to "C^n function = nth-order Taylor + o((·-x₀)^n)" for any `n`.
  Compose with translation `h ↦ x₀ + h` via `IsLittleO.comp_tendsto`
  to land in `nhds 0` form.
* `Asymptotics.IsBigO.exists_pos` + `Asymptotics.isBigOWith_iff` is
  the right pattern for extracting a positive absolute-bound
  constant from an `=O[l] g` claim — cleaner than `IsBigO.bound`
  which yields a possibly-negative constant.
* `Asymptotics.isBigO_const_mul_self c f l : (fun x => c * f x) =O[l] f`
  is the canonical "constant times g is O(g)" lemma; combine with
  `congr'` to massage the multiplication order if needed.

## Suggested next approach

For cycle 155, the planner has two productive directions:

1. **Broaden the (M × S, p) coverage matrix**: a `padded2DEulerGLM ×
   mixedStartingMethod` non-vacuity witness (cycles 133/141 ground-
   work) at `p = 0` would establish that
   `HasOrderRelativeTo_explicit` is satisfiable on non-trivial
   `r = 2` indexing, complementing the cycle-153/154 `r = 1`
   witnesses. Estimated 60–100 LOC; mostly mechanical given existing
   2D matrix arithmetic helpers.

2. **Open def:530C** (variants of order). Per planner cycle-154
   strategy, `def:530C` may be a tractable Path-A variant
   (e.g. starting-method-independence or component-wise vs global
   order) rather than full Path-B implicit machinery. Worth reading
   `extraction/formalization_data/entities/def_530C.json` first to
   confirm.

Path B (implicit branch) of def:530B remains deferred — pull-in
cost (`ContractingWith` / fixed-point infrastructure for stage
equations) is multi-cycle and not yet justified by downstream
demand.

Stretch: A `padded2DEulerGLM × mixedStartingMethod` `p = 1` witness
would parallel cycle 154's `p = 1` upgrade for the trivial pair,
but the closed-form algebra at `r = 2` with non-trivial off-diagonal
coupling is significantly larger; defer until the `p = 0`
counterpart is in place.
