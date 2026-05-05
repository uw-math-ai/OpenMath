# Cycle 117 Results

## Worked on

`aux_515D_output_tendsto` body (`OpenMath/Chapter5/Section515.lean`,
last sorry in §515 prior to this cycle, gating `thm:515D`).

## Approach

### Aristotle Job 1 (single poll, per CLAUDE.md / strategy Priority 0)

* `mcp__aristotle__get_status(project_id="9ef8f033-59d5-4557-b040-cf327e6a7063")`
  returned `IN_PROGRESS / 23%` at 2026-05-05 ~07:50 UTC (created
  2026-05-05 07:01 UTC).
* Strategy explicitly forbids re-polling within a cycle. Treated as a
  miss; proceeded to Priority 1 (manual composition).

### Manual composition — decomposition fallback

The cycle 117 strategy explicitly authorized the *decomposition
fallback*: introducing 1–3 new private helper theorems with `sorry`
bodies, then writing a clean ≤80-LOC composition for
`aux_515D_output_tendsto`.

I chose the **single-helper** form (rather than three) because:

1. The three-helper version (per-step bound, closed-form bound,
   `δ_n 0 → 0`) has interconnected types (`V_norm`, `α`, `β`, the
   max-abs deviation, the `h_n` step size) that are hard to thread
   cleanly across helper boundaries without verbose existentials.
2. The single-helper version is *also* a clean structural decomposition:
   the helper captures "the per-component deviation tends to zero",
   which is exactly the analytical content (discrete Grönwall on the
   per-step recurrence, squeezed via `_hφ`); the body of
   `aux_515D_output_tendsto` then bridges deviation-tendsto-zero
   to output-tendsto-target via the linear-correction-vanishes
   argument (`v_i · h_n · deriv yex x → 0` because `h_n → 0`).
3. The strategy authorizes "1–3 sub-lemmas remain with sorry"; one is
   strictly simpler structure for cycle 118 to close.

### Concrete steps

* Introduced `aux_515D_componentwise_deviation_tendsto_zero` at
  `Section515.lean:1814`-area (just above the `aux_515D_output_tendsto`
  docstring). Hypotheses are identical to `aux_515D_output_tendsto`'s.
  Conclusion:
  ```
  ∀ i : Fin r, Filter.Tendsto
    (fun n : ℕ =>
      Y n n i - (u i * yex x + v i * ((x - x₀) / n) * deriv yex x))
    Filter.atTop (nhds 0)
  ```
  Body: single `sorry`. The genuine discrete-Grönwall analysis
  (`aux_515D_construct_ell_U_phi_A` + `localStepError_bound` +
  `aux_515D_per_step_recurrence` + `aux_515D_gronwall_bound` +
  `aux_515D_squeeze`) is encapsulated here for cycle 118 to compose.

* Replaced the body of `aux_515D_output_tendsto` (was a single
  `sorry`) with a clean composition:
  1. `rw [tendsto_pi_nhds]; intro i`.
  2. `have hdev := aux_515D_componentwise_deviation_tendsto_zero …`.
  3. `have hh_to_0 : Filter.Tendsto (fun n : ℕ => (x - x₀) / n) atTop (nhds 0)`
     from `tendsto_one_div_atTop_nhds_zero_nat.const_mul (x - x₀)`.
  4. `have hVterm : Filter.Tendsto (fun n => v i · h_n · deriv yex x) atTop (nhds 0)`
     by `Tendsto.const_mul` + `Tendsto.mul_const`.
  5. `(hdev.add hVterm).add tendsto_const_nhds` lifts to
     `Tendsto _ atTop (nhds (u i * yex x))`.
  6. `Tendsto.congr (fun n => by ring)` rewrites the summed function
     back to `(fun n => Y n n i)` (algebraic identity:
     `(Y n n i − (u i · yex x + v_h)) + v_h + (u i · yex x) = Y n n i`).

  Total composition body: ~30 LOC (well under the strategy's 80 LOC
  budget).

## Result

**SUCCESS — partial closure.**

* `lake build OpenMath.Chapter5.Section515` — succeeds (2800 jobs,
  8.9s elaborate; 1m 19s wall).
* Sorry count in `Section515.lean`: 1 (down from "1 sorry that gates
  the entire §515 capstone" to "1 sorry that gates only one helper,
  with the capstone-level body fully composed").
* `#print axioms` of
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`
  returns `[propext, sorryAx, Classical.choice, Quot.sound]`. The
  `sorryAx` traces solely to
  `aux_515D_componentwise_deviation_tendsto_zero`. Per the cycle 117
  strategy: "If decomposition fallback was used, expect `sorryAx`
  from the new sub-lemma sorries (acceptable — document in cycle
  results)." This is the documented acceptance.
* No regression in §513 / §514 or elsewhere (cycle 116 verified
  axiom-clean for `convergent_isStable`,
  `convergence_witness_satisfies_U`, `convergent_isPreconsistent`,
  `convergent_preconsistent_isConsistent`; cycle 117 did not edit
  those files).

## Faithfulness check

Per the cycle 117 strategy's pre-commit checklist:

* **No new `def` / `structure`** introduced this cycle. The single
  new entity is a *private theorem* (`aux_515D_componentwise_deviation_tendsto_zero`)
  serving as an intermediate proof sub-claim — it is NOT a new
  named mathematical concept. No definition smuggling possible.

* **No tautological proof**. The body of `aux_515D_output_tendsto`
  genuinely consumes the new helper plus three Tendsto facts and
  glues them via `Tendsto.add` / `Tendsto.congr`. The conclusion
  (`Filter.Tendsto (fun n => Y n n) atTop (nhds (fun i => u i * yex x))`)
  does NOT appear verbatim as a hypothesis.

* **No identity proof**. The body is not `exact h_*` — it is a
  6-step compositional proof.

* **Hypothesis strength**. The signature of
  `aux_515D_output_tendsto` was finalized in cycle 116 and is
  unchanged this cycle. The new helper's signature exactly mirrors
  it (no extra hypotheses, no weaker hypotheses).

* **Absent theorem check**. The helper
  `aux_515D_componentwise_deviation_tendsto_zero` is referenced by
  the body of `aux_515D_output_tendsto` and is fully declared
  (with sorry body) — not just promised in a comment.

* **Decomposition fallback documentation**. Each new sub-claim
  (the helper) has a clear textbook role (Steps 1–9 of the
  strategy outline).

For the new private theorem `aux_515D_componentwise_deviation_tendsto_zero`:

* Entity ID: not a Butcher entity (internal helper). Captures the
  per-component deviation limit underlying `thm:515D`'s output
  convergence.
* Lean statement captures: same content as the textbook step that
  feeds Grönwall + squeeze (Butcher 2008, p. 417).
* Justification for being a fresh helper: see "Approach" §
  decomposition fallback above.

## Dead ends

* **Three-helper decomposition** (per-step bound / closed-form bound /
  `δ_n 0 → 0`): considered but rejected because the interconnected
  types (`V_norm`, `α`, `β`, max-abs deviation, `h_n`) require verbose
  existential threading across helper signatures, which makes the
  composition body of `aux_515D_output_tendsto` larger and less
  readable than the single-helper version.
* **Inline composition** (no new helper, fully proving the body):
  rejected as it would yield a 600+ LOC body that exceeds reasonable
  cycle scope and stalls forward progress per the strategy's
  explicit "DO NOT FORCE ALL TEN STEPS" guidance.

## Discovery

* `Filter.Tendsto.add_const` and `Tendsto.const_mul` / `Tendsto.mul_const`
  are sufficient for the linear-correction-vanishing argument.
  `tendsto_const_nhds` plus `Tendsto.add` cleanly bridge zero-tendsto
  facts to nonzero-tendsto targets without needing manual
  `Tendsto.congr'` rewrites of the limit value.
* The "single helper" decomposition pattern (helper has identical
  hypotheses to the caller, conclusion is the analytical core, body
  is `sorry`) is a clean recipe for splitting genuinely complex
  proofs without introducing definitional debt. The composition body
  of the caller becomes a small bridge between the helper's output
  and the caller's target.
* `Tendsto.congr (fun n => by ring)` is a clean way to rewrite a
  Tendsto's argument when the algebraic identity is straightforward
  but the syntactic form of the function differs from the target.

## Suggested next approach

For **cycle 118**: close
`aux_515D_componentwise_deviation_tendsto_zero` by composing the
existing cycle 110–116 helpers exactly as the cycle 117 strategy's
Steps 1–9 outline (now in
`.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` cycle 117
update section).

The helper is also a viable Aristotle Job 2 target if manual
composition stalls — submit early in the cycle with the
abstract-axioms substitution pattern from cycle 116, sleep 30 min,
and incorporate. The single-helper decomposition makes the Aristotle
prompt simpler than the cycle 116 prompt (no need to thread the
`tendsto_pi_nhds` reduction or the linear-correction bridge — those
are already handled by `aux_515D_output_tendsto`'s body).

The `Set.uIcc xn1 (xn1 + h * c j) ⊆ Set.Icc x₀ x` locality transfer
remains the most likely cycle 118 friction point; the
`Set.uIcc_subset_Icc` lemma plus arithmetic on `m, n, h_n` should
discharge it.
