import Mathlib

/-! # Generic Adams–Bashforth convergence scaffolding

Definitions of the generic (s-step) Adams–Bashforth iteration, its effective
Lipschitz constant, and the local truncation residual.
-/

namespace LMM

open Finset BigOperators

/-- Effective Lipschitz constant for an s-step AB method with coefficient
    vector `c` when the right-hand side is `L`-Lipschitz. -/
noncomputable def abLip (s : ℕ) (c : Fin s → ℝ) (L : ℝ) : ℝ :=
  (∑ i : Fin s, |c i|) * L

/-- Generic s-step explicit Adams–Bashforth iteration.

`abIter s c h f t₀ init n` returns the `n`-th iterate, where

* `s` – number of steps (= number of starting values),
* `c` – coefficient vector (oldest-to-newest),
* `h` – step size,
* `f` – the ODE right-hand side `f(t, y)`,
* `t₀` – initial time,
* `init` – the `s` starting values `y₀, …, y_{s-1}`,
* `n` – iterate index.

For `n < s` it returns `init n`; for `n ≥ s` it performs the AB update
using the previous `s` function evaluations. -/
noncomputable def abIter (s : ℕ) (c : Fin s → ℝ) (h : ℝ) (f : ℝ → ℝ → ℝ)
    (t₀ : ℝ) (init : Fin s → ℝ) : ℕ → ℝ :=
  fun n => Nat.strongRecOn (motive := fun _ => ℝ) n fun n ih =>
    if hn : n < s then init ⟨n, hn⟩
    else if hs : s = 0 then 0
    else
      ih (n - 1) (by omega) +
        h * ∑ i : Fin s, c i *
          f (t₀ + (↑(n - s) + ↑(i : ℕ)) * h)
            (ih (n - s + ↑i) (by omega))

/-- Local truncation residual of the generic s-step AB method applied to a
    smooth solution `y`. -/
noncomputable def abResidual (s : ℕ) (c : Fin s → ℝ) (h : ℝ) (y : ℝ → ℝ)
    (t₀ : ℝ) (n : ℕ) : ℝ :=
  y (t₀ + (↑n + ↑s) * h) - y (t₀ + (↑n + (↑s - 1)) * h)
    - h * ∑ i : Fin s, c i * deriv y (t₀ + (↑n + ↑(i : ℕ)) * h)

end LMM
