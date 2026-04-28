# Cycle 003 Results

## Worked on
- `def:142B` *convergent (matrix)* in `OpenMath/Chapter1/Section142.lean`
- `lem:110B` *Banach contraction-mapping fixed-point theorem* in
  `OpenMath/Chapter1/Section110.lean`
- `thm:101A` *the Kepler problem* (Hamiltonian + angular momentum
  conservation) in **new** file `OpenMath/Chapter1/Section101.lean`

## Approach
1. **`def:142B`**. Read entity JSON; verbatim transcription of
   `lim_{n→∞} A^n = 0` as `Tendsto (fun n => a ^ n) atTop (𝓝 0)` over a
   `SeminormedRing` carrier (matching `def:142A`). No spectral-radius /
   Jordan / similarity smuggling. Added `Mathlib.Topology.Order` import.
2. **`lem:110B`**. Wrapped Mathlib's
   `ContractingWith.fixedPoint` + `fixedPoint_isFixedPt` +
   `fixedPoint_unique'` in Butcher's `∃!` form. Verified the API
   surface via `lean_loogle` first; all three Mathlib names exist in
   our pin (`Mathlib.Topology.MetricSpace.Contracting`).
3. **`thm:101A`**. Sorry-first scaffolding with a `KeplerSystem`
   structure bundling the four scalar ODEs (101a–101d) plus a
   `nonzero` field excluding the origin. Defined `kepler_H` and
   `kepler_A` term-for-term with the textbook (Hamiltonian uses
   `Real.rpow` and is `noncomputable`). Submitted to Aristotle as a
   single batch job. After the 30-minute single-shot wait, Aristotle
   returned compiling proofs for **both** theorems using
   `HasDerivAt.{add,sub,mul,const_mul,pow,rpow_const}` plus
   `Real.rpow_neg` and `ring` / `norm_num`. Required adding
   `import Mathlib.Analysis.SpecialFunctions.Pow.Deriv`.

## Result
**SUCCESS.** All three priorities landed:
- `def:142B` formalised as `Convergent`. No `sorry`.
- `lem:110B` formalised as `contraction_fixedPoint`. No `sorry`.
- `thm:101A` formalised as `kepler_H_const` + `kepler_A_const`. No
  `sorry`. Aristotle solved both proofs.

`lake build OpenMath` returns "Build completed successfully (2223 jobs)"
with zero errors and zero warnings.

## Faithfulness check

### `def Convergent` (`def:142B`)
- Textbook statement (`def_142B.json` `statement_latex`):
  > A square matrix `A` is `convergent' if `\lim_{n \to \infty} A^n = 0`.
- Lean statement captures: **same content**.
  `Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0)` is the canonical Mathlib
  spelling of "the sequence `n → a^n` has limit 0".
- Smuggling check: NOT defined via spectral radius, minimal-polynomial
  root location, Jordan canonical form, or `∃ S, ‖S⁻¹AS‖_∞ < 1`. Each
  of those is one of the four equivalent characterisations in `thm:142D`.
- Carrier generalised from `Matrix n n ℝ` to `[SeminormedRing A]` for
  parity with `def:142A`'s carrier; documented in the doc-comment.

### `lemma contraction_fixedPoint` (`lem:110B`)
- Textbook statement (`lem_110B.json` `statement_latex`):
  > Let `M` denote a complete metric space with metric `\rho` and let
  > `\varphi : M \to M` denote a mapping which is a contraction, in the
  > sense that there exists a number `k`, satisfying `0 \leq k < 1`,
  > such that, for any `\eta, \zeta \in M`,
  > `\rho(\varphi(\eta), \varphi(\zeta)) \leq k \rho(\eta, \zeta)`. Then
  > there exists a unique `\xi \in M` such that `\varphi(\xi) = \xi`.
- Lean statement captures: **same content** modulo one explicit hypothesis.
  - `LipschitzWith k φ` with `k : ℝ≥0` and `(hk : k < 1)` is exactly
    Butcher's "contraction with constant `0 ≤ k < 1`" (the lower bound
    `0 ≤ k` is built into `ℝ≥0`).
  - `∃! ξ, φ ξ = ξ` packages existence and uniqueness in one quantifier.
- Hypothesis-strength check: `[Nonempty M]` is added beyond the
  textbook. This is required by Mathlib's `ContractingWith.fixedPoint`
  (the fixed point is a literal element of `M`) and is implicit in the
  textbook (on an empty `M` the existential conclusion is vacuously
  false). Documented in the doc-comment.
- Tautology check: conclusion `∃! ξ, φ ξ = ξ` is not among the
  hypotheses. ✓
- Identity check: proof is `refine` + three Mathlib-API appeals; not a
  one-liner re-export. ✓

### `structure KeplerSystem` (`thm:101A` infrastructure)
- All five fields are *hypotheses* (the four ODE derivatives 101a–101d
  plus `nonzero : ∀ x, y₁² + y₂² ≠ 0`). No conclusion fields. ✓
- Definition-smuggling check: this is not a definition of a named
  mathematical concept; it is a hypothesis bundle for the Kepler ODE.
  No smuggling possible.
- The `nonzero` field is an extra hypothesis beyond the bare ODE
  system, required because the potential `(y₁²+y₂²)^(-1/2)` is
  undefined at the origin. Butcher implicitly assumes this; we make
  it explicit. Documented in the structure's doc-comment.

### `def kepler_H` and `def kepler_A`
- Textbook (`thm_101A.json` `statement_latex`):
  > `H = \frac{1}{2}(y_3^2 + y_4^2) - (y_1^2 + y_2^2)^{-1/2}`,
  > `A = y_1 y_4 - y_2 y_3`.
- Lean statements capture: **same content** term-for-term.
  - `kepler_H = (1/2) * (y₃² + y₄²) - (y₁² + y₂²) ^ (-(1:ℝ)/2)`. The
    minus sign on the potential is written verbatim; the `^ (-1/2)` is
    `Real.rpow`, which makes `kepler_H` `noncomputable`.
  - `kepler_A = y₁ * y₄ - y₂ * y₃`.
- Smuggling check: not defined via abstract symplectic-flow machinery
  or any vector-form reformulation; matches Butcher's scalar formulas.

### `theorem kepler_H_const` and `theorem kepler_A_const`
- Textbook: "The quantities H and A are constant."
- Lean statement captures: **same content** modulo the standard
  reformulation "constant on ℝ ⇔ derivative vanishes everywhere on ℝ".
  Both theorems prove `∀ x, HasDerivAt (… y₁ y₂ y₃ y₄) 0 x`. The
  follow-up "value equals the value at any fixed point" is a one-line
  corollary of `is_const_of_deriv_eq_zero` if a downstream user wants it.
- Tautology check: conclusion `HasDerivAt … 0 x` is not a hypothesis. ✓
- Identity check: proofs are multi-line chain-rule expansions
  (`HasDerivAt.{add,sub,mul,const_mul,pow,rpow_const}` + `ring` /
  `norm_num` / `Real.rpow_neg` + the `nonzero` field for positivity of
  `y₁²+y₂²`); they are not one-liner re-exports. ✓
- Hypothesis-strength check: `KeplerSystem y₁ y₂ y₃ y₄`, which carries
  the four ODEs and the `nonzero` field. The `nonzero` field is the
  only added hypothesis beyond Butcher's bare statement; documented above.

## Dead ends
None this cycle. Every step matched the planner's prediction:

- `Mathlib.Topology.MetricSpace.Contracting` is importable and the
  three names (`ContractingWith.fixedPoint`,
  `ContractingWith.fixedPoint_isFixedPt`,
  `ContractingWith.fixedPoint_unique'`) exist in our pin under exactly
  those names.
- The Kepler sorry-first file typechecked on the first try with the
  exact import set the planner predicted (`Calculus.Deriv.Basic` +
  `SpecialFunctions.Pow.Real`); Aristotle added one further import
  (`SpecialFunctions.Pow.Deriv`) for the rpow-derivative chain rule.

## Discovery
- **Aristotle handles `Real.rpow` chain-rule expansions cleanly** when
  given a positivity sidegoal-source. Aristotle's proof of
  `kepler_H_const` chains `HasDerivAt.const_mul`, `HasDerivAt.add`,
  `HasDerivAt.pow`, `HasDerivAt.rpow_const`, and discharges the
  remaining algebra with `convert ... using 1; norm_num; rw
  [Real.rpow_neg (by positivity)]; ring`. Worth banking as a recipe for
  future ODE-conservation theorems (e.g. `thm:123B`).
- **Project status `COMPLETE_WITH_ERRORS`** does NOT mean the result is
  unusable — Aristotle returned compiling proofs that built cleanly in
  our project. The "errors" tag may reflect intermediate failed
  attempts in the search; the final extracted file is what matters.
- **`obtain ⟨h1, h2, h3, h4⟩ := h` against a 5-field structure
  compiles** in Lean 4 — Lean right-associates the trailing pattern,
  effectively destructuring the last two fields together. (Aristotle
  used this idiom successfully for `kepler_A_const`.)

## Suggested next approach
1. **`thm:123B`** (Hamiltonian area invariance) is the natural §12x
   target now that `thm:101A` is in. The proof pattern is the same as
   `kepler_H_const`: a small Hamiltonian-system structure + a
   chain-rule conservation theorem. Aristotle should handle it given
   the cycle-003 recipe.
2. **`thm:110C`** (Picard existence/uniqueness) is now unblocked: it
   needs `def:110A` (✓), `lem:110B` (✓), plus a Banach-space-valued
   integral and the Picard iteration map. Budget multiple cycles —
   the metric-space-of-continuous-functions construction with the
   exponentially-weighted sup norm is non-trivial.
3. **§142 theorem chain.** With `def:142A` and `def:142B` both in,
   `thm:142C/D/E/F` (the Jordan / minimal-polynomial / spectral-radius
   characterisations) become reachable. `thm:142D` is the heaviest;
   `thm:142F` (a corollary chain) is likely the easiest entry point.
4. **`thm:112B`** (one-sided Lipschitz ⇒ exponential-growth bound) is
   another stand-alone §11x target that needs only `def:112A` (✓) plus
   Grönwall's inequality from Mathlib.

If Aristotle quota allows, cycle 004 should batch-submit a §12x
Hamiltonian-conservation theorem alongside one §142 characterisation
to keep the auto-prover busy while the planner-side definition work
proceeds.
