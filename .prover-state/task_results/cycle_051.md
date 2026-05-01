# Cycle 051 Results

## Worked on

Single new private helper lemma `globalError_per_step_sum_form` in
`OpenMath/Chapter4/Section404.lean`, inserted between
`recentSum_swap_bound` (cycle 050) and the
`stable_consistent_isConvergent` scaffold (cycle 047, line-1947 sorry
preserved).

This bridges:
- cycle 045's `globalError_recurrence_bound_textbook` (per-step bound
  parameterised over a single `Mmax` upper-bounding `|ε(n-(j+1))|`),
- cycle 048's `sum_theta_psi_contraction` (consumes a per-`i` `Sε(i)`
  value, not a max).

Specialisation: `Mmax := ∑_{j : Fin k} |ε(n-(j+1))|`.

## Approach

Followed the planner's four-step recipe verbatim:

1. `set Mmax : ℝ := ∑ j : Fin k, |…(j.val + 1)…| with hMmax_def` to
   introduce the sum-form upper bound.
2. `hMmax_nn : 0 ≤ Mmax` via
   `Finset.sum_nonneg (fun _ _ => abs_nonneg _)`.
3. `hMmax_bound : ∀ i, |…(i.val + 1)…| ≤ Mmax` via the standard
   Mathlib lemma `Finset.single_le_sum` (verified via `lean_loogle`
   before use; signature
   `(hf : ∀ i ∈ s, 0 ≤ f i) (h : a ∈ s) : f a ≤ ∑ x ∈ s, f x` is
   exactly the planner's expected form).
4. `exact M.globalError_recurrence_bound_textbook … Mmax hMmax_nn
    hMmax_bound`.

The `set` tactic ensured the goal's RHS contained the identifier
`Mmax`, so `exact` succeeded without `convert` or fallback rewrites.

## Result

**SUCCESS** — single-cycle target landed exactly as planned.

- `lake env lean OpenMath/Chapter4/Section404.lean` exits cleanly
  (exit 0).
- Diagnostics: only the four pre-existing warnings
  (unused-variable at lines 568, 627, 1204; sorry at line 2010 =
  `stable_consistent_isConvergent`, formerly line 1947 before the
  new lemma was inserted). No new warnings.
- Sorry count: **1** (unchanged — only the documented cycle-047
  scaffold target remains, awaiting the cycle 052+ outer assembly).
- Axioms: `[propext, Classical.choice, Quot.sound]` only,
  confirmed via temporary in-file `#print axioms` (then removed).
  No new axioms.

Aristotle was NOT invoked: the manual proof is ~22 lines of pure
forward instantiation, and the cycle 045 lemma's calling convention
was well documented in cycle 045's task results, so the planner's
"manual proof should land first" prediction held.

## Faithfulness check

For `globalError_per_step_sum_form` (the only new declaration this
cycle):

- **Entity ID**: N/A — internal helper, not a Butcher entity. Same
  category as `recentSum_swap_bound` (cycle 050),
  `sum_theta_psi_contraction` (cycle 048), and
  `starting_error_sum_tendsto_zero` (cycle 049). The docstring
  documents the bridging role explicitly, citing cycle 045 as the
  source and cycles 048 / 052+ as consumers.
- **Lean statement captures**: same content as cycle 045's
  `globalError_recurrence_bound_textbook` with the `Mmax`/`hMmax0`/
  `hMmax` triple specialised to the concrete sum
  `∑ j : Fin k, |yex (x₀ + ((n - (j.val+1) : ℕ) : ℝ) * h)
                   - Y (n - (j.val+1))|`.
- **Tautology check**: PASS — the conclusion (a polynomial-in-`h`
  sum-form upper bound on the per-step residual) does not appear
  verbatim in any hypothesis. Hypotheses are: Lipschitz bound on
  `f`, ODE smoothness/derivative-equation/uniform-bound on `yex`,
  consistency, smallness `h L |β_0| < 1`, LMM-solution
  hypothesis. None mention the goal's sum form.
- **Identity check**: PASS — proof body is
  `set Mmax := …; have hMmax_nn := …; have hMmax_bound := …; exact
   M.globalError_recurrence_bound_textbook …`.
  This is forward instantiation, but it does real work: it
  specialises the abstract `Mmax` slot to a concrete value
  (a sum) AND discharges the per-element upper-bound hypothesis
  via `Finset.single_le_sum`. The output is genuinely a different
  shape than the input (sum-form vs max-form), so this is not a
  vacuous re-export.
- **Hypothesis strength check**: PASS — every hypothesis flows
  through to cycle 045's lemma; none can be weakened without
  weakening the parent. The cycle 045 lemma's hypothesis set was
  itself faithfulness-checked at the time of its introduction.
- **Class/structure check**: N/A — no new class or structure.
- **Definition smuggling check**: N/A — no new definition.
- **Absent theorem check**: N/A — no comment promises content not
  present in the file.

## Dead ends

None. The four-step planner recipe worked first try. The only minor
hiccup was that `lean_local_search` is unavailable (no `rg` on
PATH), so `Finset.single_le_sum`'s signature was confirmed via
`lean_loogle` instead — the type signature returned matched the
planner's expectation exactly.

## Discovery

- `Finset.single_le_sum`'s argument convention in current Mathlib
  is `(hf : ∀ i ∈ s, 0 ≤ f i) {a : ι} (h : a ∈ s)`. No name drift,
  no argument-order surprises. Future cycles needing
  "single ≤ sum of non-negatives" can use this lemma directly.

- The `set X := … with hX_def` pattern combined with `exact`
  (no `convert`) is sufficient when the parent lemma's RHS is
  parameterised over `X` and the goal already mentions the
  spelled-out form. Lean's elaborator handles the unfold-on-demand
  cleanly. No need for `simp only [← hX_def]` workarounds.

- The cycle 045 lemma's hypothesis order
  `(hcons hL hM hf_lip hyex_C1 hyex_ode hf_yex_bound hh hsmall hY n
    hn Mmax hMmax0 hMmax)` is stable and applied cleanly without
  `apply` / `refine` plumbing — pure `exact` worked.

## Suggested next approach

Cycle 052 should begin the outer assembly of
`stable_consistent_isConvergent` (line 2014). The planner's preview
in cycle 051's strategy lists nine sub-steps; the natural starting
point is **step 1**: unfold `IsConvergent` to expose the
`Tendsto … atTop (𝓝 0)` conclusion and the per-`Fin k`
starting-method hypotheses. This is a definitional unfolding step
and should be tractable in a single sub-cycle.

The full outer assembly is large; the planner correctly scoped it
across cycles 052–053. Suggested cycle 052 deliverable: a
sorry-first version of `stable_consistent_isConvergent` that
introduces the `f`, `L`, `M_bound`, `x₀`, `y₀`, `h`, `start`
universals (per `IsConvergent`'s definition) and replaces the
top-level `sorry` with a structured proof scaffold whose internal
sorries are individually identified and labelled with which
helper lemma will close them (cycle 045 → 048 → 050 → 046 → 049).

Stretch consideration for cycle 052: if step 1 (unfolding) lands
quickly, attempt step 2 (apply `Section141.linRec_closed_form` to
get the `θ`-decomposition `ε_n = Σ θ_{n-i} ζ_i + Σ θ_{n-i} ψ_i`).
That requires reading `Section141.lean` for the closed-form
signature, which may take some exploration time.

The stretch goal proposed in cycle 051's strategy (preparing a
sorry-first scaffold for the outer assembly's first internal step)
was **not attempted this cycle** — the main lemma landed quickly,
but introducing the outer-assembly scaffold as a separate
preparatory commit risks confusing the cycle 052 worker about the
relationship between cycle 051's deliverable and cycle 052's
target. Better to let cycle 052's planner own the outer-assembly
scaffolding decisions explicitly.
