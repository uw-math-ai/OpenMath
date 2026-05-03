# Cycle 100 Results

## Worked on

`lem:515A` (Butcher Lemma 515A — local truncation error bounds for a
GLM applied to a Lipschitz autonomous-scalar IVP). Cycle 100 opened
§515 with a sorry-first scaffold per the planner: created
`OpenMath/Chapter5/Section515.lean`, defined `glmAbscissae` (the
abscissae vector `c = A·𝟙 + U·v`), stated the two main inequalities
`localStageError_bound_a` (515a) and `localStageError_bound_b`
(515b) as `sorry`, and closed the FTC-based preliminary
`aux_y_diff_norm_bound` (the textbook's `‖y(x + hξ) − y(x)‖ ≤ |ξ|·h·L·M`)
manually.

## Approach

Followed the cycle-100 planner verbatim, including the backup
plan's scope reduction (state lem:515A with `c` as parameter, defer
the `ϕ` (= `ell`) infrastructure to cycle 101). Concretely:

1. **Imports + namespace**: pulled `Mathlib.Analysis.MeanInequalities`,
   `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`,
   `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`,
   `Mathlib.Analysis.Calculus.Deriv.Basic`,
   `Mathlib.Topology.MetricSpace.Lipschitz`,
   `OpenMath.Chapter5.Section512`. Re-opened
   `namespace OpenMath.Chapter5.Section510` for symbol continuity
   with §510/§512/§513/§514.

2. **`glmAbscissae` def**: `M.A *ᵥ (fun _ => 1) + M.U *ᵥ v`. Marked
   as a computational helper (textbook §515 sets it up just before
   lem:515A; not a numbered textbook def). Non-vacuity witness
   `explicitEulerGLM_glmAbscissae_eq_zero` (with `v = 0`,
   `c = (fun _ => 0)`).

3. **`aux_y_diff_norm_bound`**: closed manually. Adapted from the
   Section404.lean cycle-040 helper `exact_solution_norm_bound`,
   generalised to allow ξ of either sign (using `|ξ|` and
   `|h·ξ| = h · |ξ|` for `h ≥ 0`) and using `L · M_bound` directly
   as the integrand bound (matching textbook `‖y'(x)‖ ≤ L M`).
   30-line proof: continuity of `f∘y = deriv y`,
   `HasDerivAt y (f (y t)) t`, integrability,
   `intervalIntegral.integral_eq_sub_of_hasDerivAt`,
   `intervalIntegral.norm_integral_le_of_norm_le_const`, then the
   ξ-sign-symmetric absolute-value bookkeeping.

4. **`localStageError_bound_a` and `localStageError_bound_b`**:
   stated with full hypothesis bundle (Lipschitz `f`, `C¹` exact
   solution `yex`, `‖yex‖ ≤ M`, `‖yex'‖ ≤ L M`, consistency vectors
   `u, v` with `V·u = u`, `U·u = 𝟙`, `B·𝟙 + V·v = u + v`, abscissae
   `c = M.glmAbscissae v`). Conclusion verbatim from
   `entities/lem_515A.json` for both (515a) and (515b). Bodies
   `sorry` per the planner's scope.

5. **Aristotle batch**: submitted
   `.prover-state/aristotle_submissions/cycle_100/sub_lemmas.lean`
   with five sorry-first stubs:
   `aux_y_diff_norm_bound` (already manually closed; included for
   the batch as a free job), `aux_T1_bound` (FTC ⇒ T1 = 0),
   `aux_T2_bound` (algebraic ⇒ T2 = 0), `aux_T3_bound` (Lipschitz
   integral bound), `aux_T4_bound` (Lipschitz at discrete
   abscissae). Project ID
   `18cdd9f8-0168-4a49-9721-f214918a7afe`. Submitted at 14:09 UTC;
   slept 30 min; status check at 14:39 UTC: `IN_PROGRESS, 1%`.
   Per CLAUDE.md ("one check after 30 min is enough"), no further
   polling — cycle 101 will pick up the results.

## Result

**SUCCESS** (cycle target met) — scaffold delivered, one sub-bound
closed manually, Aristotle batch submitted.

* `OpenMath/Chapter5/Section515.lean` exists, `lake build
  OpenMath.Chapter5.Section515` succeeds (2773 jobs).
* Two `sorry` warnings (one each for `localStageError_bound_a` and
  `localStageError_bound_b`); these are the only sorries in the
  file (matches the planner's scope).
* `aux_y_diff_norm_bound` closed; non-vacuity
  `explicitEulerGLM_glmAbscissae_eq_zero` closed.
* `lean_status.json` row for `lem:515A` set to `partial` with
  pointer to `Section515.lean`.
* `plan.md` row updated to `[~]` with cycle-100 closure note.
* Aristotle batch in flight (will be revisited cycle 101).

## Faithfulness check

### `def GeneralLinearMethod.glmAbscissae`

Entity ID: not a numbered textbook entity (computational helper).
Textbook setup (`entities/lem_515A.json`):

> "where `c = A𝟙 + U v`."

Lean definition: `M.A *ᵥ (fun _ => 1) + M.U *ᵥ v`. Captures: **same
content** (entrywise: `c_i = Σ_j A_{ij} · 1 + Σ_j U_{ij} · v_j`,
which is exactly Butcher's `c = A·𝟙 + U·v`). No divergence.

### `theorem explicitEulerGLM_glmAbscissae_eq_zero`

Non-vacuity witness (not a textbook entity). Trivially derivable:
`A = !![0]`, `U = !![1]`, `v = (fun _ => 0)` ⇒ `c = 0 + 0 = 0`.

### `lemma aux_y_diff_norm_bound`

Helper lemma (not a textbook-numbered entity, but corresponds to
Butcher's first preliminary at the start of the §515 proof:

> "y(x_{n−1} + h c_i) − y(x_{n−1}) ≤ h ∫_0^{c_i} |y'(x_{n−1} + hξ)| dξ ≤ |c_i| h L M"

Lean statement: `|y(x + h·ξ) − y(x)| ≤ h · |ξ| · (L · M_bound)`,
generalised over arbitrary `ξ ∈ ℝ`. Captures: **same content**
(textbook ξ-range `[0, c_i]` is absorbed into the absolute value).

### `theorem GeneralLinearMethod.localStageError_bound_a`

Entity ID: `lem:515A`, inequality (515a). Textbook statement
(`entities/lem_515A.json`):

> `‖Ŷ_i − h Σ_j a_{ij} f(Ŷ_j) − Σ_j U_{ij} y_j^{[n−1]}‖`
> `≤ h² L² M (½ c_i² + Σ_j |a_{ij} c_j|)`

with `Ŷ_i = y(x_{n−1} + h c_i)` and
`y_j^{[n−1]} = u_j y(x_{n−1}) + v_j h y'(x_{n−1})`.

Lean statement captures: **same content**. The conclusion
`|yex (xn1 + h * c i) − h * (Σ_j A_{ij} f (yex (xn1 + h c_j)))
− (Σ_j U_{ij} (u_j yex xn1 + v_j h deriv yex xn1))|
≤ h² L² M (½ c_i² + Σ_j |A_{ij} c_j|)` is term-by-term identical to
(515a) after substitution of `Ŷ_j = yex (xn1 + h c_j)` and
`y_j^{[n−1]} = u_j yex xn1 + v_j h deriv yex xn1`.

Hypothesis-strength check: bundle includes `_hCons` (consistency
510c equation `B·𝟙 + V·v = u + v`) which is **strictly stronger**
than the textbook prerequisite for *just* the (515a) stage bound
(only `c = A·𝟙 + U·v` and the input identities matter for this
inequality). The 510c clause is included so the same hypothesis
bundle drives both `localStageError_bound_a` and
`localStageError_bound_b` and downstream `lem:515B` consumption.
Documented in the docstring; can be weakened in a future cleanup
cycle if no consumer needs it for (515a) specifically.

Other hypotheses (`hh`, `hL`, `hM`, `hf_lip`, `hy_C1`, `hy_ode`,
`hy_M`, `hy'_LM`, `hVu`, `hUu`, `hc_def`) all match the textbook
setup verbatim. The C¹ smoothness `hy_C1` is implicit in the
textbook's appeal to FTC (same convention as the cycle-040
`exact_solution_norm_bound` faithfulness note).

### `theorem GeneralLinearMethod.localStageError_bound_b`

Entity ID: `lem:515A`, inequality (515b). Textbook statement:

> `‖y_i^{[n]} − h Σ_j b_{ij} f(Ŷ_j) − Σ_j V_{ij} y_j^{[n−1]}‖`
> `≤ h² L² M (½ |u_i| + |v_i| + Σ_j |b_{ij} c_j|)`

with `y_i^{[n]} = u_i y(x_n) + v_i h y'(x_n)` and `x_n = x_{n−1} + h`.

Lean statement captures: **same content** (substitution
`y_i^{[n]} = u_i yex (xn1 + h) + v_i h deriv yex (xn1 + h)`). No
divergence.

## Dead ends

* **First compilation pass** had unused-variable warnings for `hL`,
  `hM` in `aux_y_diff_norm_bound` (the FTC + integral bound proof
  doesn't need positivity of `L * M_bound` since the absolute-value
  conclusion is automatically nonneg) and matching warnings in
  `localStageError_bound_a/b`. Resolved by underscore-prefixing
  the unused parameters in the signatures.
* **`Matrix.mulVec` in `simp` argument** for
  `explicitEulerGLM_glmAbscissae_eq_zero` was flagged as unused by
  the linter (the simp set already unfolds it via the standard
  `simp` lemmas for 1×1 matrices). Removed.

## Discovery

* **Cycle-040 helper structure ports cleanly to a sign-agnostic form.**
  The §404 `exact_solution_norm_bound` was written for `ξ ≤ 0`; the
  symmetric `|ξ|` form (needed for §515 since `c_i ≥ 0`) needs
  exactly the same proof body — only `abs_of_nonpos` ↦ no-op (we
  use `|·|` from the start) and one ξ-sign tweak in the final calc.
  Total ~30 lines, no Mathlib gaps. Future ξ-sign-agnostic versions
  of `residual_integral_form`, `residual_bound`, etc. are expected
  to lift just as cleanly.
* **`glmAbscissae` non-vacuity for explicit Euler is `c = 0`,
  not `c = 1`.** The cycle-100 planner suggested `c = (1)` for
  `explicitEulerGLM`, but the actual computation gives
  `c = A·𝟙 + U·v = !![0]·𝟙 + !![1]·0 = 0`. This matches the
  forward-Euler abscissa convention (the stage is evaluated at the
  *start* of the step, `c_1 = 0`). Updated witness lemma name to
  reflect this: `explicitEulerGLM_glmAbscissae_eq_zero`.
* **Hypothesis bundle width.** lem:515A's full hypothesis bundle is
  ~13 parameters (counting `s`, `r`, `M`, `h`, `L`, `M_bound`, `f`,
  `yex`, `xn1`, `u`, `v`, `c`, plus 8 hypotheses). Wide signatures
  like this are unavoidable for textbook-faithful local truncation
  bounds; the alternative (bundling into a structure) would couple
  to `IsConsistent`'s existential and break helper reusability per
  the planner's encoding choice.

## Suggested next approach

* **Cycle 101**: incorporate Aristotle results from cycle 100. If
  Aristotle returns proofs for the four `Tk` sub-bounds, assemble
  `localStageError_bound_a` directly. Manual fallback for
  whichever sub-bound Aristotle missed; the §404 cycle-040–050
  precedent shows these are tractable but each takes ~50–100 lines
  of FTC + Lipschitz bookkeeping.
* **Cycle 102** (if 101 closes lem:515A): scaffold lem:515B
  (the `ϕ` contraction argument). The planner's deferred `ell`
  infrastructure (Neumann series for `(I − h₀ L |A|)`-invertibility)
  becomes load-bearing here.
* **Hypothesis weakening**: `localStageError_bound_a` currently
  carries the full `_hCons` (510c) hypothesis even though it isn't
  used. Once cycle 101 closes the proof, audit which hypotheses
  are actually consumed and propose a sharper signature.
* **`exact_solution_norm_bound_symmetric`**: consider extracting
  the sign-agnostic form to a shared helper (perhaps in a new
  `OpenMath/Common/IVPHelpers.lean`) so cycle 101's `aux_T3_bound`
  / `aux_T4_bound` proofs and any future §515 follow-ons can reuse
  it without re-proving from FTC. Low priority — only matters if
  the helper appears 3+ times in the codebase.
