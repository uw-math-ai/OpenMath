import Mathlib

/-! Cycle 112 — Aristotle batch for `aux_515D_output_tendsto` (Butcher §515D).

Self-contained file with sub-lemma B: a thin **specialization** of
`discrete_gronwall_exp_bound` to the §515 setting. The Section404
helper takes a recurrence
  u n ≤ a + b·h·k·(∑_{i ∈ Ico 1 n} u i) + c·h²·n
and concludes
  u n ≤ exp(b·k·n·h)·a + (exp(b·k·n·h) − 1)·(c·h / (b·k)).

The §515 use case wires:
* `b ↔ α` (linear-in-error coefficient),
* `c ↔ β` (quadratic-in-h residual coefficient),
* `h ↔ h_n = (x − x₀) / n` (per-step size),
* `k ↔ n` (number of steps so far).

Then `b·k·n·h = α · n · n · h_n = α · n · (x − x₀)`. Hmm — too large.
The correct binding here is `k ↔ ⌈Δx / h_n⌉` (number of steps to
reach `x`); since we only care about `n` steps with `n · h_n = Δx`,
we instantiate `k = n` and the product `b·k·n·h = α · n · n · h_n =
α · n · Δx`, also too large.

The intended specialization in `aux_515D_output_tendsto` uses
`k ↔ 1` (so `b·k·n·h = b·n·h = α · n · h_n = α · Δx` is bounded
uniformly in n) and a recurrence shape
  u (m+1) ≤ a + b·h·(∑_{i ∈ Ico 1 (m+1)} u i) + c·h²·(m+1)
which the Aristotle agent should verify is consistent with sub-lemma A's output.

Note: the existing Section404 helper has the constant-step
formulation (uniform `h`). For the variable-step §515 application,
we fix `n` (so `h_n` is constant within the recurrence) and run the
recurrence over `m = 0, …, n`.
-/

open scoped BigOperators

namespace AristotleBatch112

/-- **Sub-lemma B** — specialization of `discrete_gronwall_exp_bound`
to the §515 shape, with `k = 1` and constants `α, β > 0`. The conclusion
is bounded uniformly in `n` provided `α · Δx` is bounded.

This is the abstract scalar Grönwall bound; the §515 application
(in `aux_515D_output_tendsto`) instantiates `δ` with the per-step
diagonal error `δ_n m`, `a` with `δ_n 0`, and reads off the bound
at `m = n` (i.e. evaluates `δ` at the diagonal).

Hypotheses match `OpenMath.Chapter4.Section404.discrete_gronwall_exp_bound`. -/
theorem aux_515D_gronwall_bound
    (u : ℕ → ℝ) (a α β h : ℝ)
    (ha : 0 ≤ a) (hα_pos : 0 < α) (hβ_nn : 0 ≤ β) (hh : 0 ≤ h)
    (hu0 : u 0 ≤ a)
    (hu_rec : ∀ m, 1 ≤ m →
      u m ≤ a + α * h * (∑ i ∈ Finset.Ico 1 m, u i)
              + β * h^2 * (m : ℝ))
    (n : ℕ) :
    u n ≤ Real.exp (α * (n : ℝ) * h) * a
            + (Real.exp (α * (n : ℝ) * h) - 1) * (β * h / α) := by
  sorry

end AristotleBatch112
