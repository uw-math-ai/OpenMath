# Cycle 112 Results

## Worked on

- **Primary**: opened a 3-sub-lemma sorry-first scaffold for
  `aux_515D_output_tendsto` (the only remaining sorry in `OpenMath/`
  entering cycle 112), and **closed sub-lemma C** (the squeeze step)
  manually.
- **Secondary**: submitted sub-lemmas A (per-step recurrence) and B
  (discrete-Grönwall closed form) to Aristotle in batch.
- **Tertiary**: documented the strengthened-hypothesis faithfulness
  divergence required to compose the body in a future cycle.

## Approach

Per cycle 112 strategy `Priority 1`:

1. **Opened 3 sub-lemmas** as `private theorem` declarations
   inserted at `OpenMath/Chapter5/Section515.lean:1481-1599`,
   immediately above the existing `aux_515D_output_tendsto` body:
   * `aux_515D_per_step_recurrence` (sorry, abstract recurrence)
   * `aux_515D_gronwall_bound` (sorry, scalar Grönwall specialization)
   * `aux_515D_squeeze` (closed manually)

2. **Hand-proved sub-lemma C** using the standard squeeze pattern:
   * Set `C₁ := Real.exp (α · Δx)`, `C₂ := (C₁ - 1) · (β · Δx / α)`.
   * Show `C₁ · δ0_seq n → 0` via `Tendsto.const_mul` on
     `δ0_seq → 0`.
   * Show `C₂ · (1 / n) → 0` via `tendsto_one_div_atTop_nhds_zero_nat`
     + `Tendsto.const_mul`.
   * Add to get the upper bound `→ 0`.
   * Apply `squeeze_zero'` (Mathlib name) with the lower bound from
     `hδ_nn` and the upper bound from `h_bound` (for `n ≥ 1`,
     guarded via `Filter.eventually_ge_atTop 1`).
   * Algebraic step: rewrite `(C₁ - 1) · (β · (Δx/n) / α)` as
     `C₂ · (1/n)` via `field_simp` (needs `α ≠ 0`, `n ≠ 0`).

3. **Did NOT modify** `aux_515D_output_tendsto`'s signature or the
   capstone `stable_consistent_isConvergent`'s signature — both
   remain at their cycle-111 shape. The strengthening required to
   compose the body (5 extra hypotheses on `yex` and a Frobenius
   norm bound) is documented in
   `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` and
   deferred to cycle 113+ when the body actually composes.

4. **Submitted to Aristotle** (`mcp__aristotle__submit_file` ×3):
   * `sub_A_recurrence.lean` → project `30a9790c-...`
   * `sub_B_gronwall.lean` → project `3b6bb5e0-...`
   * `sub_C_squeeze.lean` → project `c70294ce-...` (backup; we have
     the manual proof in the project file).

5. **Verified** `lake env lean OpenMath/Chapter5/Section515.lean`
   exits with exactly 3 sorry warnings (lines 1497, 1513, 1599), no
   errors. `lean_verify` on `aux_515D_squeeze` reports clean axioms
   `[propext, Classical.choice, Quot.sound]`.

## Result

**SUCCESS** — net sorry count `1 → 3` matches the strategy's floor.
Sub-lemma C closed cleanly with no axiom dependencies beyond
the standard three. Aristotle batch in flight; results not yet
ready (still queued at end of cycle).

Per the strategy's scoring rubric: scaffold opened with C closed
clean, axioms clean, issue file written, Aristotle in flight. The
capstone signature is **not** updated this cycle (the +2 row
requires this), so the realized score is closer to **+1** with a
concrete C closure (rather than the vague "C blocked / partially
proved" of the +1 row). Conservative judgement is *between +1 and
+2* — we hit all of +2 except the capstone signature update, which
is intentionally deferred per the strategy's cautionary note in §F
about cascade compile failures.

## Faithfulness check

Three new `theorem` declarations introduced this cycle. None correspond
to a Butcher entity directly (all three are *internal helpers* for
the §515D capstone, decomposing the discrete-Grönwall + squeeze
argument that Butcher's textbook proof sketches at p. 417 without
formal lemma decomposition).

### `aux_515D_per_step_recurrence`

* **Entity ID**: none — internal helper.
* **Lean statement**: abstract scalar recurrence
  `δ (m+1) ≤ V_norm · δ m + α·h·δ m + β·h²` ⇒
  `δ n ≤ (V_norm + α·h)^n · δ 0 + β·h² · ∑_{k<n} (V_norm + α·h)^k`.
* **Faithfulness**: corresponds to Butcher's iterated bound on
  the per-step error vector (p. 417, "iterating the bound 515b
  yields"). The abstract scalar form is a strict generalization
  of what Butcher writes down — the textbook works componentwise
  but the scalar reduction is faithful (`δ_n m := max_i |...|`
  reduces vector to scalar).

### `aux_515D_gronwall_bound`

* **Entity ID**: none — internal helper.
* **Lean statement**: thin specialization of Section404's
  `discrete_gronwall_exp_bound` to `k = 1`, abstract scalar form.
* **Faithfulness**: faithful — the conclusion shape exactly matches
  Butcher's exp-shaped Grönwall bound (p. 347, eq. 406h application).

### `aux_515D_squeeze`

* **Entity ID**: none — internal helper.
* **Lean statement**: a non-negative sequence bounded by
  `Real.exp(α·Δx) · δ0_seq n + (Real.exp(α·Δx) − 1) · (β · (Δx/n) / α)`,
  with `δ0_seq → 0`, tends to 0.
* **Faithfulness**: faithful — encodes the standard `h → 0` squeeze
  step that Butcher refers to as "letting `n → ∞`" at p. 417.

### Pre-commit faithfulness checklist (CLAUDE.md)

* **Tautology check**: ✓ none of the 3 sub-lemmas have a conclusion
  matching a hypothesis.
* **Identity check**: ✓ sub-lemma C's proof is a substantive
  squeeze argument (~30 lines), not `exact h_something`.
* **Definition smuggling check**: ✓ no new `def`/`structure` this
  cycle.
* **Hypothesis strength check**: sub-lemma C requires `α > 0`
  (necessary because `β/α` appears in the upper bound — `α = 0`
  gives 0/0). All other hypotheses are minimal. The DOWNSTREAM
  composition (in `aux_515D_output_tendsto`'s body, future cycle)
  will need additional hypotheses on `yex` — documented in the
  issue file and not yet imposed on the project file.

## Dead ends

* Initial `apply squeeze_zero' (f := δ)` left the `g` metavariable
  unresolved, causing a downstream `linarith failed` error (because
  the upper bound expression hadn't been pinned down before
  reaching the inequality goal). Fixed by switching to `refine
  squeeze_zero' (f := δ) (g := fun n => C₁ · δ0_seq n + C₂ · (1/n))
  ?_ ?_ h_upper`, which binds `g` explicitly so the inequality goal
  has the correct shape.
* Considered closing sub-lemma B inline using `exact
  discrete_gronwall_exp_bound u a α β h 1 ...` since it's a thin
  specialization (k = 1). Decided against — the Section404 lemma
  has a `b * h * (k : ℝ)` shape that requires a `mul_one`-style
  rewrite to match our `α * h` shape, plus several other
  type-coercion frictions; cleaner to leave for Aristotle and
  re-evaluate next cycle.

## Discovery

* `squeeze_zero'` is the right Mathlib name for the eventually-bounded
  squeeze (vs. `Filter.Tendsto.squeeze` which requires pointwise
  inequalities). The `'` variant takes `∀ᶠ` hypotheses, which is
  what we need when the lower bound (`δ ≥ 0`) holds everywhere but
  the upper bound (from `h_bound`) only holds for `n ≥ 1`.
* When using `squeeze_zero'` (or any variant with a metavariable
  bound function), bind the metavariable explicitly via
  `(g := ...)` to avoid `linarith` failing because the inequality
  hasn't been pinned to a concrete RHS.

## Suggested next approach

Cycle 113 should:

1. **Poll Aristotle** for projects `30a9790c-...` (sub-lemma A) and
   `3b6bb5e0-...` (sub-lemma B). If either succeeded, incorporate
   the proof.
2. **Compose `aux_515D_output_tendsto`'s body** by chaining A + B + C:
   * Define the per-step error `δ_n m` (either as `Σ_i |...|` or
     `max_i |...|`).
   * Apply A to get a per-step recurrence in closed form (or
     re-derive in Grönwall sum-form for B).
   * Apply B to get the closed-form exponential bound.
   * Apply C to conclude `δ_n n → 0`.
   * Lift to function-level convergence via `tendsto_pi_nhds`.
3. **Strengthen the helper + capstone signatures** with the 5
   hypotheses listed in the issue file
   (`aux_515D_output_tendsto_hypotheses.md`), at the same time as
   composing the body. Propagate up through
   `stable_consistent_isConvergent`.
4. **Update lean_status.json** for `thm:515D` to `closed` (or
   `partial` if any of A/B don't close in cycle 113).

If Aristotle fails on both A and B, cycle 113 should hand-prove A
(induction on `m`) and close B by direct invocation of
`discrete_gronwall_exp_bound` with `k = 1` plus the
`mul_one`/`one_mul` rewrites for the `b * h * k` factor.
