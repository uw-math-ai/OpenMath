# Cycle 170 Results

## Worked on

`thm:431A` (Stability regions / Schur criterion, Butcher §431,
p. 366) — partial formalisation.

New file `OpenMath/Chapter4/Section431.lean` shipping:

* `IsStronglyStable` predicate (open unit disc characterisation).
* Three non-vacuity witnesses:
  - `isStronglyStable_witness_n2` — `(X - 1/2)(X + 1/3)`.
  - `isStronglyStable_witness_n3` — `(X - 1/2)(X - 1/4)(X + 1/3)`.
  - `not_isStronglyStable_xsq_sub_one` — refutability witness for
    `X² - 1` (root at `w = 1`).
* `schurReduce` definition (the §431 Butcher Schur reduction `Pₙ₋₁`,
  in ascending coefficient form).
* `schur_identity_coeff` — the coefficient form of Butcher's
  load-bearing identity `wPₙ₋₁(w) = a₀Pₙ(w) - aₙwⁿPₙ(w⁻¹)`.
* `strongly_stable_imp_lead_gt_const` — the **necessity direction**
  of (431e), `‖a₀‖² < ‖aₙ‖²` for any strongly stable polynomial of
  positive degree, via Vieta on the multiset of complex roots.

Plus two private helpers:
* `multiset_prod_nonneg_of_nonneg`
* `multiset_prod_lt_one_of_lt_one`

## Approach

Followed cycle 170 strategy verbatim. Key choices:

1. **Predicate before structure**: defined `IsStronglyStable` as a
   plain `∀-IsRoot-implies-norm<1` predicate (definition of "strong
   stability" from Butcher §431). Resisted the temptation to encode
   the Schur conditions *as* the definition — those become a real
   theorem (the IFF), not a definitional rewrite.

2. **Coefficient-by-coefficient algebraic identity**: defined
   `schurReduce P` as a `Finset.sum` of `Polynomial.C ... * X^k`,
   then proved the algebraic identity (Butcher's
   `wPₙ₋₁ = a₀Pₙ - aₙwⁿPₙ(w⁻¹)`) directly in coefficient form via
   `Polynomial.coeff_X_mul` + `Finset.sum_eq_single`. This sidesteps
   the awkward `P.comp (1/X)` representation entirely.

3. **Necessity via Vieta**: used Mathlib's
   `Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots` (over ℂ via
   `IsAlgClosed.splits`) to land
   `coeff 0 = (-1)^n · lead · ∏ roots` with one rewrite, then
   chained norm-of-product = product-of-norms (`hProdNorm` inline
   induction) and the `multiset_prod_lt_one_of_lt_one` helper to
   close the strict inequality.

4. **Squaring step**: `sq_lt_sq'` with the correct sign hypothesis
   (`-‖lead‖ < ‖coeff 0‖` is automatic from norm-nonneg).

## Result

**SUCCESS** — all five mandatory deliverables landed axiom-clean.
`OpenMath/Chapter4/Section431.lean` compiles cleanly (`lake env lean`
exit 0, zero warnings, zero errors). Sorry count remains 0 across
the project. Tautology scanner clean (no `:= h_…` / `exact h_…` /
`:= id` patterns).

Aristotle was not used this cycle: the manual proofs went through
on the first elaboration after the API-name fixes (`Splits` no
longer takes a ringHom; `Complex.norm_one` → `norm_one`;
`P.Splits (RingHom.id ℂ)` → `P.Splits`). Strategy permitted
skipping Aristotle when manual proofs land cleanly.

The **sufficiency direction** of Butcher 431A (the Rouché step)
was not attempted; see
`.prover-state/issues/rouche_theorem_missing.md`.

## Faithfulness check

### `def: IsStronglyStable`

* Entity ID: `thm:431A` (the predicate is what the textbook
  *uses* — `extraction/formalization_data/entities/thm_431A.json`
  context: "type `(n, 0, 0)`, meaning all zeros are in the open
  unit disc").

  > "A polynomial is strongly stable if it has type `(n, 0, 0)`,
  >  meaning all zeros are in the open unit disc."

* Lean statement captures: **same content** —
  `∀ w : ℂ, P.IsRoot w → ‖w‖ < 1` is exactly "all roots lie in
  the open unit disc".

* Definition smuggling check: PASS. The Schur conditions
  (`|a₀|² > |aₙ|²` ∧ recursive) become a *theorem* (the IFF),
  not the definition.

### `theorem: schur_identity_coeff`

* Textbook source: Butcher §431 proof, equation
  `wPₙ₋₁(w) = a₀Pₙ(w) - aₙwⁿPₙ(w⁻¹)`.

  > "It is easy to verify that
  >   wPn−1(w) = a0 Pn(w) − an wn Pn(w−1)."

* Lean statement captures: **same content** in coefficient form.
  Extracting the coefficient of `w^{k+1}` from both sides:
  - LHS coefficient of `w^{k+1}` in `w·Pₙ₋₁(w)` = `Pₙ₋₁.coeff k`.
  - RHS coefficient of `w^{k+1}` in `a₀Pₙ - aₙwⁿPₙ(w⁻¹)` =
    `a₀ · Pₙ.coeff(k+1) - aₙ · Pₙ.coeff(n - k - 1)` (with the
    conjugation pattern from `Pₙ(w⁻¹)`'s reflection structure;
    here `star = conj` since we are over ℂ).
  - Note: Butcher's formula uses `aᵢ := P.coeff (n - i)` (descending
    indices), so our `(k+1)` corresponds to Butcher's
    `n - (k+1)`-th coefficient when read in his ascending-power
    convention. The translation is recorded in the docstring
    convention paragraph.

* Tautology check: PASS. Conclusion is a non-trivial polynomial
  identity, not equal to any hypothesis.

### `theorem: strongly_stable_imp_lead_gt_const`

* Textbook source: Butcher §431, proof of 431A, first paragraph.

  > "First note that (431e) is necessary for strong stability
  >  because if it were not true, the product of the zeros could
  >  not have a magnitude less than 1."

* Lean statement captures: **same content** —
  `IsStronglyStable P ⇒ ‖coeff 0‖² < ‖lead‖²`.

* Hypothesis strength check: weaker than Butcher's `n ≥ 2` — we
  use `1 ≤ P.natDegree` because the necessity *direction* goes
  through for any `n ≥ 1` (product of `n ≥ 1` factors each strictly
  less than 1 is strictly less than 1). The textbook's `n ≥ 2`
  is for the IFF (the recursive Schur-reduction step needs `n ≥ 2`,
  but that step is not in the necessity direction). The weakening
  is documented in the docstring.

* Definition smuggling check: PASS. The conclusion
  `‖a₀‖² < ‖aₙ‖²` is **derived** via Vieta + product bound — it
  is not part of `IsStronglyStable`.

### Pre-commit checklist (CLAUDE.md)

* [✓] Tautology check: no theorem conclusion appears verbatim as
  a hypothesis.
* [✓] Identity check: no proof is just `exact h` re-export.
* [✓] Definition smuggling check: `IsStronglyStable` is the
  textbook open-unit-disc definition, not the Schur conditions.
* [✓] Hypothesis strength check: necessity uses `n ≥ 1` (weaker
  than textbook's `n ≥ 2`); justified above.
* [✓] Absent theorem check: every theorem promised in the
  docstring exists in the file.

## Dead ends

1. **Initial Splits API mistakes**: tried `P.Splits (RingHom.id ℂ)`
   — `Splits` is single-argument in current Mathlib. Fixed by
   reading `Mathlib/Algebra/Polynomial/Splits.lean` line 36 directly.

2. **`Complex.norm_one` does not exist**: tried
   `rw [Complex.norm_one]` in witness proofs — `Complex.norm_one`
   is not a Mathlib name. The general `norm_one` (from
   `NormedAddGroup`) handles ℂ via instance resolution.

3. **Inline rewriting of `Multiset.map id`**: my first attempt
   used `Multiset.prod_map` (non-existent) and `Multiset.map id`
   rewrites that didn't fire because the multiset was already in
   `(fun r => r)` form, not `id`. Replaced by direct
   `Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots` (which lands
   the desired form in one step).

4. **Inner induction inside the necessity proof** for product
   non-negativity tripped over a hypothesis-shadowing issue when
   I did the induction inline. Extracted to a top-level private
   helper `multiset_prod_nonneg_of_nonneg`; the helper has clean
   variables and the main proof becomes a single application.

## Discovery

1. **`Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots` is the
   right Mathlib hammer for Vieta-style necessity arguments.** It
   lands `coeff 0 = (-1)^n · lead · ∏ roots` directly without
   re-deriving the splitting decomposition.

2. **Mathlib's `Splits` over an algebraically-closed field is
   single-argument** (just `f.Splits`); the `(map f)` form is for
   when one targets a different field. `IsAlgClosed.splits_codomain`
   is deprecated in favor of `IsAlgClosed.splits`.

3. **`norm_one`, `norm_neg`, `Complex.norm_div`, `Complex.norm_ofNat`
   suffice for explicit witness norm computations**; no need for
   `Complex.abs_*` or coercion lemmas.

4. **Coefficient-by-coefficient algebraic identities are far easier
   than full polynomial identities.** Working in
   `(P · Q).coeff k = ...` + `coeff_X_mul` + `Finset.sum_eq_single`
   completely sidesteps `Polynomial.comp` issues and `1/X` handling
   that the §451 proof (cycle 167-168) had to deal with for the
   §451e quadratic form identity.

## Suggested next approach

For the planner of cycle 171:

1. **Stretch on `thm:431A`**: consider building Rouché's theorem
   in `OpenMath/` as a multi-cycle infrastructure. Mathlib has
   the argument principle pieces. Closing 431A's sufficiency
   direction would make the full IFF available and unblock
   downstream §441 stability theorems (`thm:441C`, `lem:441A`,
   `lem:441B`) at higher fidelity.

2. **Or move on**: pick the next Ch.4 leaf entity per
   `extraction/formalization_data/topo_order.json`. Leading
   candidates (after filtering out the 442A/422B blockers
   identified in cycle 170 strategy):
   - `thm:441C` (Maximum order bound for stable LMMs, §441) —
     uses Schur criterion at a black-box level.
   - `lem:441A` (Maximum order for a convergent k-step method,
     §441) — depends on `thm:441C` and Dahlquist barrier.
   - `lem:441B` (Maximum order coefficients negativity, §441) —
     leaf-ish.
   The §441 cluster is the natural neighbour to start once the
   §431 partial is in.

3. **Tautology-scanner false positives** (recorded in
   `.prover-state/issues/tautology_scanner_false_positives.md`)
   were not triggered this cycle because we used hypothesis names
   without leading underscores (`hLt`, `hk`, `hSS`, etc.) per
   strategy guidance.
