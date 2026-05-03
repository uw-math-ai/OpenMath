import Mathlib

/-! Cycle 112 — Aristotle batch for `aux_515D_output_tendsto` (Butcher §515D).

Self-contained file with sub-lemma A: the **per-step recurrence**
arising from applying `localStepError_bound` (Butcher §515 lem:515B)
to each iteration step of a GLM.

Statement (informal): for a stable GLM `M`, Lipschitz `f`, exact ODE
solution `yex`, and computed iteration `Y n m`, the step-wise error
  δ n m := max_i |Y n m i − (u_i · yex(x_{n,m}) + v_i · h_n · y'(x_{n,m}))|
satisfies a recurrence
  δ n (m+1) ≤ ‖V‖_∞ · δ n m + α · h_n · δ n m + β · h_n²
for explicit constants `α, β` depending on `M, L, M_bound`.

This file uses *abstract* parameters (no GLM-specific encoding) so
that Aristotle can reason about the recurrence shape independently
of the §515 encoding. The Aristotle prompt instructs the prover to
return a proof in the abstract form; the project file then wires
it into the GLM-specific call site.
-/

open scoped BigOperators

namespace AristotleBatch112

/-- **Sub-lemma A (abstract form)** — given a per-step bound of the
shape derived from `localStepError_bound` plus stability bookkeeping,
write the recurrence for `δ_n m+1` in terms of `δ_n m`. This is the
*abstract* statement; the project file specializes the constants. -/
theorem aux_515D_per_step_recurrence_abstract
    (δ : ℕ → ℝ) (V_norm α β h : ℝ)
    (hV_nn : 0 ≤ V_norm) (hα_nn : 0 ≤ α) (hβ_nn : 0 ≤ β) (hh : 0 ≤ h)
    (hδ_nn : ∀ m, 0 ≤ δ m)
    (hrec : ∀ m, δ (m + 1) ≤ V_norm * δ m + α * h * δ m + β * h^2) :
    -- Reshape into the form consumed by `discrete_gronwall_exp_bound`:
    -- δ n ≤ δ 0 + (V_norm + α · h) · h · k · (∑ i ∈ Ico 1 n, δ i) + β · h² · n.
    -- We just need: δ n ≤ δ 0 · (V_norm + α · h)^n + β · h² · ((V_norm + α · h)^n - 1) / (V_norm + α · h - 1).
    -- For the intended Aristotle target, we settle for the iterated form:
    ∀ n, δ n ≤ (V_norm + α * h)^n * δ 0
              + β * h^2 * (∑ k ∈ Finset.range n, (V_norm + α * h)^k) := by
  sorry

end AristotleBatch112
