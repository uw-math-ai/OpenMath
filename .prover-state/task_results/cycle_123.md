# Cycle 123 Results

## Worked on

Closed the body of `aux_515D_per_step_K_bound` (cycle 122 narrower
helper, `OpenMath/Chapter5/Section515.lean:1953`), reducing the §515D
sorry count from 2 to 1. Threaded a new hypothesis `_hc_le_one : ∀ i,
M.glmAbscissae v i ≤ 1` through the §515D internal chain
(`aux_515D_per_step_K_bound`, `aux_515D_max_deviation_geometric_bound`,
`aux_515D_max_deviation_bound_tendsto_zero`,
`aux_515D_componentwise_deviation_tendsto_zero`,
`aux_515D_output_tendsto`) and extended `stable_consistent_isConvergent`'s
`hc_nn_witness` conclusion to also produce `c_j ≤ 1`.

## Approach

Followed Priority 1 from the cycle 123 strategy verbatim:

1. **Hypothesis propagation**: added `(_hc_le_one : ∀ i,
   M.glmAbscissae v i ≤ 1)` to `aux_515D_per_step_K_bound`'s
   signature, then forwarded it through the four upstream helpers and
   into the capstone via the conjunctive
   `(∀ i, 0 ≤ M.glmAbscissae v i) ∧ (∀ i, M.glmAbscissae v i ≤ 1)`.
   §513/§514 are unaffected — they consume `IsConvergent` directly.

2. **Manual proof of per_step_K_bound** (skipped Aristotle backup):
   * Constructed `ell_U`, `phi_A` via `aux_515D_construct_ell_U_phi_A`
     (cycle 114 helper) with `h₀ := x − x₀`, `L := (L : ℝ)`.
   * Defined α, β as `Finset.sup'` over per-`i` constants matching
     `localStepError_bound`'s `_hα_def`, `_hβ_def` shapes.
   * Per-(n, m) setup: `h_n := (x − x₀)/n`, `xn1 := x₀ + m·h_n`,
     `δm` and `δ_max` matching `localStepError_bound`'s `δ`/`δ_max`.
   * Extracted the internal stage `Y_stage` from `IsGLMSolution` at
     step `m`, then converted both stage and next-step equations
     from the inner `h * f(Y)` form to the outer `h * (∑ A · f(Y))` form.
   * Discharged the *localised* M_bound hypotheses
     (`hyex_M_local`, `hyex'_LM_local`) using `_hc_nn` and
     `_hc_le_one` to bound `h_n · c_j ∈ [0, h_n]`, then the
     interval `[xn1, xn1 + h_n·c_j] ⊆ [x₀, x]`.
   * Discharged the endpoint M_bound hypotheses by the same
     interval-inclusion argument (without `c_j`).
   * Applied `localStepError_bound` to obtain `K`, then matched the
     algebraic identity
     `Y(m+1) − target(m+1) − (V·δ(m)) = K` and the bound
     `|K i| ≤ α·h·δ_max + β·h²` to the conclusion.

The Lipschitz-coercion bridge `LipschitzWith L f` (NNReal `L`) →
`LipschitzWith ((L : ℝ).toNNReal) f` (Real `L` for the bound's
expected form) was handled with `Real.toNNReal_coe ▸ _hf_lip`.

3. **Faithfulness documentation**: appended a "Cycle 123 update"
   section to `.prover-state/issues/stable_consistent_isConvergent_hc_nn.md`
   explaining why `_hc_le_one` is required (the per-stage path
   `[xn1, xn1 + h_n·c_j]` must stay inside `[x₀, x]` to apply the
   global `_hyex_M`), citing the standard RK convention `c ∈ [0,1]`
   for textbook GLMs.

Aristotle backup was skipped — the manual proof was tractable
within the cycle and Aristotle requires substantial axiom-shimming
infrastructure (the helper signatures depend on `GeneralLinearMethod`,
`IsGLMSolution`, `aux_515D_construct_ell_U_phi_A`, and
`localStepError_bound`, none of which Aristotle would have without
custom axiomatic stubs). Per the strategy's slot-management
guidance, "if Aristotle stalls (< 30 % at check), proceed with the
manual proof from Step 2" — that path was viable and chosen.

## Result

SUCCESS.

* `aux_515D_per_step_K_bound` body closed (~155 LOC after blanks
  stripped).
* §515D sorry count: 2 → 1 (cycle 122 penalty recovered).
* Build verification:
  * `lake env lean OpenMath/Chapter5/Section515.lean` exits 0
    (warnings only — `hβ_nn` unused linter on the cycle 113 lemma,
    pre-existing simp warning, `ring`-tries at the cycle 109/118
    locations — all pre-existing).
  * `lake env lean OpenMath/Chapter5/Section513.lean` exits 0.
  * `lake env lean OpenMath/Chapter5/Section514.lean` exits 0
    (deprecation warnings only).
* Axiom check:
  `#print axioms GeneralLinearMethod.stable_consistent_isConvergent`
  returns `[propext, sorryAx, Classical.choice, Quot.sound]`. The
  `sorryAx` traces solely to the remaining
  `aux_515D_max_deviation_geometric_bound` body sorry.
* Tautology scanner: 0 hits
  (`grep -nE ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'
  OpenMath/Chapter5/Section515.lean`).

Stretch (Priority 2: closing `aux_515D_max_deviation_geometric_bound`)
was not attempted — Priority 1 took the full cycle budget (the
Lipschitz coercion, the `Finset.le_sup'` parameter-name mismatch,
and the `δm`/`xn1` definitional-unfolding details all required
iteration). The cycle nets +1 (sorry count 2 → 1), which fully
recovers the cycle 122 −2 supervisor penalty in conjunction with
cycle 122's structural progress.

## Faithfulness check

Cycle 123 introduced one signature-level divergence (no new
textbook entities):

* **`_hc_le_one` propagation** — see
  `.prover-state/issues/stable_consistent_isConvergent_hc_nn.md`
  "Cycle 123 update" section. Butcher's §515 does not require GLM
  abscissae bounded above by 1; the standard RK / GLM convention
  takes `c ∈ [0, 1]` and all worked examples in Butcher Ch. 2/3/5
  satisfy this. The hypothesis is required because
  `localStepError_bound`'s localised `_hy_M_local`/`_hy'_LM_local`
  hypotheses are stated on the per-stage interval
  `[xn1, xn1 + h·c_j]`, and discharging them from the global
  `_hyex_M : ∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound` requires
  `c_j ≤ 1`. This divergence is contained inside the §515D internal
  chain plus the capstone witness; §513/§514 / `IsConvergent`
  (def:512A) are unaffected.

* **`aux_515D_per_step_K_bound`** (cycle 122 narrower, body closed
  this cycle) — internal infrastructure, not a Butcher entity. No
  textbook divergence.

* `lean_status.json` `thm:515D` — remains `partial` (one sorry
  remains in `aux_515D_max_deviation_geometric_bound`). Will flip
  to `formalized` only when Priority 2 closes.

## Dead ends

None. The strategy's recipe was directly applicable.

Minor iteration loops:

1. Initial `Finset.le_sup' (a := i₀) ...` calls failed — Mathlib's
   `Finset.le_sup'` uses positional or `b`-named binding, not `a`.
   Switched to positional invocation.
2. The `hδm_eq` proof had an over-engineered `congr 2 <;> ring`
   step; after `rw [hδm_def]` Lean's def-unfolding closes the goal
   reflexively, so `intro k; rfl` suffices.

## Discovery

* `localStepError_bound` accepts the `xn1 + h_n · c_j` interval
  parameterisation directly — all the `c_j ∈ [0, 1]` interval
  arithmetic can be discharged with two `linarith` invocations
  (one for the lower bound `0 ≤ h_n · c_j`, one for the upper
  bound `h_n · c_j ≤ h_n`) plus the global endpoint-inclusion
  `xn1 + h_n ≤ x`. No specialised interval-stretching lemma is
  needed.
* `Real.toNNReal_coe` (Mathlib) is the Lipschitz NNReal/Real
  bridge for round-tripping; this is a small but recurring
  pattern when calling `localStep*` lemmas with our `L : NNReal`
  context.
* `Finset.le_sup'`'s parameter naming convention is `b` (not `a`)
  in current Mathlib; codebase calls using positional notation
  (e.g. `Finset.le_sup' f hmem` or `Finset.le_sup' (s := …) f hmem`)
  are robust against this.

## Suggested next approach

**Cycle 124 should target Priority 2:** closing
`aux_515D_max_deviation_geometric_bound` body
(`OpenMath/Chapter5/Section515.lean:2034`, sorry near 2271).

Recipe (per cycle 123 strategy Priority 2 + cycle 121 correction
issue):

1. Apply `aux_515D_per_step_K_bound` (now closed) to extract
   constants `α, β ≥ 0` with `|R(m) i| ≤ α·h_n·δ_max(m) + β·h_n²`.
2. Apply `aux_515D_iterated_V_bound` (cycle 120 helper at line
   1835) to `M.V` and `_hStab`'s power-bounded witness, obtaining
   `C₀ ≥ 0` with `sup'_i |((V^k) *ᵥ x) i| ≤ C₀ · sup'_j |x j|`.
   Bridge `M.IsStable`'s `∃ C, ‖V^k‖ ≤ C` to the helper's expected
   `∃ C, 0 ≤ C ∧ …` shape via `max C 0`.
3. Closed-form expansion: induction on `m` proves
   `δ(m) = V^m · δ(0) + Σ_{k<m} V^(m−1−k) · K(k)`. If the
   induction is heartbeat-heavy, factor as a separate
   `aux_515D_delta_closed_form` helper (be wary of net-decrease
   constraint — only factor if induction directly fails).
4. Sum-form bound: combine (2) + (3) + per_step_K_bound's K-bound:
   ```
   u(m) ≤ a + α'·h_n·Σ_{k∈Ico 1 m} u(k) + β'·h_n²·m
   ```
   where `u(m) := sup'_i |δ(m) i|`, `α' := C₀·α`, `β' := C₀·β`.
5. Apply `aux_515D_gronwall_bound` (cycle 117 helper at line 1742);
   split `α = 0` vs `α > 0` via `by_cases on (α : ℝ) = 0`.
6. Set `C_init := C₀ · (1 + α·(x − x₀)) · exp(C₀·α·(x − x₀))` and
   `C_lin := (exp(C₀·α·(x − x₀)) − 1) · (β/α)` (or
   `C₀·β·(x − x₀)` for `α = 0` branch).

Estimated cycle-124 size: 120–180 LOC.

If cycle 124 closes Priority 2, the §515D sorry count drops to 0,
fully closing `thm:515D`'s narrowing chain. The capstone
`stable_consistent_isConvergent` would then have axioms
`[propext, Classical.choice, Quot.sound]` only (no `sorryAx`),
and `lean_status.json` `thm:515D` flips to `formalized`.

Do **not** attempt to refactor `_hc_le_one` away in cycle 124 —
treat it as a stable signature commitment, parallel to `_hc_nn`.
The textbook-faithful unconditional cleanup is a separate
multi-cycle effort and is documented in the issue file's "Future
remediation" section.
