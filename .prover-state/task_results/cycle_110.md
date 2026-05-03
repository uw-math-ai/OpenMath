# Cycle 110 Results

## Worked on

* `aux_515D_stage_tendsto` (the *easier* of the two §515D sub-lemmas) —
  refactored signature to take an explicit output-convergence
  hypothesis, and **closed the body** modulo a single named helper
  sorry.
* `aux_515D_stage_eventually_bounded` (NEW private helper) — opened
  with sorry, scoped to the M-matrix-based eventual boundedness step
  identified in the cycle 109 task results' "Suggested next approach".
* `GeneralLinearMethod.stable_consistent_isConvergent` — call site
  updated to thread the output-convergence witness from
  `aux_515D_output_tendsto` into the new `aux_515D_stage_tendsto`
  signature.
* Issue file `aux_515D_stage_eventually_bounded_deferred.md` — written
  per the cycle 110 plan.

## Approach

### Aristotle (Priority 0)

Polled batch `40554853-18b3-424c-81e4-2a2fae9e57c4` once: status
`IN_PROGRESS` at 6%. Per cycle 110 strategy ("the shape of the cycle
110 work below diverges from the cycle 108 submission signature, so
leftover work won't fit the new signature anyway"), canceled the
project to free the queue. Did not poll a second time (CLAUDE.md
rule).

### Refactor + helper (Priority 1, Steps 1a/1b)

* Added `(h_output : Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
  (nhds (fun i => u i * yex x)))` as a new explicit hypothesis on
  `aux_515D_stage_tendsto`. Renamed previously unused `_hStab`,
  `_hf_lip`, `_hyex_x₀`, `hUu`, `hxx`, `hY_props` (dropped the
  underscore prefix where the new body uses them).
* Inserted `aux_515D_stage_eventually_bounded` immediately *before*
  `aux_515D_stage_tendsto` (so it is in scope), with a `sorry` body
  and a docstring referencing the new issue file. Statement: there
  exists `Bf ≥ 0` and an `∀ᶠ n in atTop, ∀ j, |f (Y_int n j)| ≤ Bf`.
  Hypotheses minimal — only what the closure proof in cycle 111 will
  actually need (M-matrix invariant, Lipschitz `f`, stage equation,
  output limit).

### Body proof of `aux_515D_stage_tendsto` (Step 2)

Followed the strategy's recipe verbatim:

1. `obtain ⟨Bf, _, hBf_ev⟩ := aux_515D_stage_eventually_bounded …`.
2. `rw [tendsto_pi_nhds]; intro i` — reduce to component-wise.
3. Lift `h_output` through `Continuous.matrix_mulVec` to get
   `M.U *ᵥ Y n n → M.U *ᵥ (fun i => u i * yex x)`, then evaluate at
   index `i` via `tendsto_pi_nhds.mp`.
4. Simplify the limit point using `M.U *ᵥ u = 𝟙`:
   `(M.U *ᵥ (fun i => u i * yex x)) i = yex x · 1 = yex x`.
5. `(x - x₀) / n → 0` via `tendsto_one_div_atTop_nhds_zero_nat`
   followed by `.const_mul (x - x₀)` and `simpa [mul_div_assoc']`.
6. Per-summand `(x - x₀)/n * f(Y_int n j) → 0` via
   `NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded` (with
   `(𝕜 := ℝ) (E := ℝ)` and `simpa [Pi.smul_apply', smul_eq_mul]` to
   convert pointwise `•` to `*`).
7. Multiply by `M.A i j` via `.const_mul`; sum via
   `tendsto_finset_sum`.
8. Combine sum + matrix-mulVec limits via `.add`; rewrite `0 + yex x
   = yex x`.
9. `Filter.Tendsto.congr'` over the cofinite tail `n ≥ 1`: on that
   tail the stage equation `hY_props.2.2` rewrites the combined
   expression to `Y_int n i`.

### Call site (Step 1a continued)

In `stable_consistent_isConvergent`, replaced

```
refine ⟨?_, ?_⟩
· exact aux_515D_output_tendsto …
· exact aux_515D_stage_tendsto …
```

with

```
have h_output := aux_515D_output_tendsto …
refine ⟨h_output, ?_⟩
exact aux_515D_stage_tendsto … h_output
```

— a zero-cost change. The refine clauses still produce the same
witnesses; only the binding order differs.

## Result

**SUCCESS.** Build via `lake env lean OpenMath/Chapter5/Section515.lean`
clean — exactly 2 sorry warnings:

```
OpenMath/Chapter5/Section515.lean:1481:16: warning: declaration uses `sorry`
OpenMath/Chapter5/Section515.lean:1522:16: warning: declaration uses `sorry`
```

matching the cycle 110 expected sorry distribution
(`aux_515D_output_tendsto` at 1481, `aux_515D_stage_eventually_bounded`
at 1522). Sorry count net 2 → 2 (closed `aux_515D_stage_tendsto`,
opened `aux_515D_stage_eventually_bounded`), with the residual
*shape* improved from a vague "stage limit" to a clean *eventual
boundedness* claim.

`mcp__lean-lsp__lean_verify aux_515D_stage_tendsto` reports axioms
`{propext, sorryAx, Classical.choice, Quot.sound}` — `sorryAx` is
inherited from the helper, as expected.

## Faithfulness check

### `aux_515D_stage_eventually_bounded` (new private helper)

* Not a Butcher entity — internal helper for the §515D capstone.
* Lean statement is a non-trivial *existence* of a uniform eventual
  bound `Bf`. Hypotheses minimal: stability (M-matrix invariant),
  Lipschitz `f`, stage equation, output convergence. No unused
  hypotheses promoted to internal lemmas.
* No tautology: conclusion is an `∃ ∀ᶠ` statement; not equal to any
  hypothesis.
* No identity: body is `sorry`, *guarded* by an issue file with a
  concrete M-matrix path.
* Definition smuggling: N/A (no new definition introduced).

### `aux_515D_stage_tendsto` (refactored)

* Not a Butcher entity — internal helper.
* Compared to cycle 108/109 signature, the only change is the *added*
  parameter
  `h_output : Tendsto (fun n => Y n n) atTop (nhds (fun i => u i * yex x))`.
  No hypothesis weakened, no hypothesis strengthened beyond the
  textbook-tacit output convergence (which the cycle 109 plan
  identified as zero-cost since the call site supplies it from
  `aux_515D_output_tendsto`).
* Tautology check: conclusion `Tendsto Y_int atTop (nhds (fun _ => yex
  x))` is not equal to any hypothesis. (`h_output` is about `Y n n`,
  not `Y_int`.)
* Identity check: body is *not* `exact h_output` — it computes
  componentwise via the stage equation, matrix-mulVec continuity,
  and the M-matrix-based boundedness helper.
* Definition smuggling: N/A.

### `thm:515D` (capstone, statement unchanged)

* Entity: `thm:515D` (Butcher 2008 p. 417): "A stable and consistent
  general linear method is convergent." Quoted from
  `entities/thm_515D.json` `statement_text`:
  > A stable and consistent general linear method is convergent.
* Lean statement captures: same content, modulo the cycle 109
  `(hs : 0 < s)` precondition (already documented as a faithfulness
  divergence in cycle 109; no change this cycle).
* Cycle 110 only modified the call site's *binding* of the two
  sub-lemma witnesses; the surrounding theorem statement is
  byte-identical to cycle 109.

## Dead ends

None this cycle. The strategy was followed verbatim:

* Aristotle poll → cancel (per the strategy guidance about the
  refactor invalidating the submission signature).
* Refactor + helper-sorry-first → closure of stage_tendsto body.

The main type-checker hiccup was the named-argument `(𝔸 := ℝ)` for
`NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded` — the
correct parameter name is `E`, not `𝔸` (Mathlib renamed since some
older usage). One-line fix.

## Discovery

* `NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded` for
  `(𝕜 := ℝ) (E := ℝ)` produces a `Tendsto (ε • f)` whose pointwise
  smul is *not* automatically definitionally equal to multiplication
  in syntactic form — `simpa [Pi.smul_apply', smul_eq_mul]` is the
  bridge. Worth filing in the cycle 111 worker's quick-reference.
* The cycle 109 plan's "zero-cost signature change" prediction was
  exactly right: adding `h_output` cost 3 lines at the call site
  (one `have`, one `refine`, one `exact … h_output`) and unlocked
  a 30-line clean stage proof.
* The decomposition pattern from `Section514.lean:622-670`
  (`convergence_witness_satisfies_U`'s U-side) translates directly:
  same `Continuous.matrix_mulVec` + `tendsto_pi_nhds` + per-summand
  bounded-times-tendsto-zero recipe.

## Suggested next approach

### Cycle 111 — Close `aux_515D_stage_eventually_bounded` (Net 2 → 1)

Per the issue file `aux_515D_stage_eventually_bounded_deferred.md`
and the cycle 110 plan's "After cycle 110: forward-looking
trajectory":

1. **Surface the M-matrix Frobenius hypothesis.** Either
   * add `(h_norm : ‖((x - x₀) * (L : ℝ)) • M.A.map (|·|)‖ < 1)`
     directly to `aux_515D_stage_eventually_bounded`, OR
   * thread it from a strengthened `IsConvergent` (heavier; cycle 098
     already strengthened the field; touching it again is a
     compatibility burden).
   Recommend the helper-local approach (clean, additive, mirrors
   cycle 107's `lem:515B` plumbing).

2. **Choose `N : ℕ`** such that for `n ≥ N`, `‖h_n L |A|‖ < 1`.
   Combine `tendsto_one_div_atTop_nhds_zero_nat` with
   `Filter.Eventually.mono` and the M-matrix Frobenius hypothesis at
   `h₀ = (x - x₀)/N`.

3. **Rearrange the stage equation.** Pass `|·|` through, use
   Lipschitz `|f y| ≤ L · |y - 0| + |f 0|`, get
   `(I - h_n L |A|) · |Y_int n| ≤ rhs` where rhs involves
   `h_n · |A| · 𝟙 · |f 0|` and `|M.U *ᵥ Y n n|`.

4. **Apply `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`**
   (cycle 106) entrywise to invert the comparison.

5. **Bound the RHS uniformly** using output convergence: `|M.U *ᵥ Y n
   n|` converges (continuous image of convergent sequence), so it's
   eventually bounded. `h_n → 0` makes the other term eventually
   bounded.

6. **Lift to `f` via Lipschitz**: `|f (Y_int n j)| ≤ L · |Y_int n j -
   0| + |f 0| ≤ L · Bd + |f 0|`, where `Bd` is the bound on `|Y_int
   n|` from step 5.

Estimated 60–90 min. Will likely require 1–2 helper lemmas pulled
from `OpenMath/Chapter5/MMatrix.lean` plus a `Matrix.linfty_opNorm`
manipulation. No new Mathlib infrastructure should be needed.

### Cycle 112+ — Open `aux_515D_output_tendsto`

The discrete-Grönwall + squeeze sub-lemma. Cycle 110 deliberately
did not touch this; per the strategy and cycle 109 task results,
this is comfortably 2–3 cycles of focused work mirroring the LMM
chain at `Section404.lean:1300+`.
