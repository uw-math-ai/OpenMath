import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.ODE.Gronwall

/-!
# Butcher §112 — Stiff differential equations

This file collects the entities of subsection 112 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

Contents:

* `def:112A` — `OneSidedLipschitzInSecond` (one-sided Lipschitz predicate).
* `thm:112B` — `one_sided_lipschitz_solution_diff_bound` (Grönwall-style
  contraction estimate for solutions of `y' = f(x, y)` whose RHS is
  one-sided Lipschitz).
-/

namespace OpenMath.Chapter1.Section112

open Real Set

/-- Butcher §112, Definition 112A — *one-sided Lipschitz condition*.

The textbook statement (Butcher 2008, p. 47):

> The function `f` satisfies a *one-sided Lipschitz condition*, with
> *one-sided Lipschitz constant* `ℓ` if for all `x ∈ [a, b]` and all
> `u, v ∈ ℝ^N`, `⟨f(x, u) - f(x, v), u - v⟩ ≤ ℓ ‖u - v‖²`.

We follow the same generalization pattern as `def:110A`:
* the closed interval `[a, b]` is replaced by an arbitrary `s : Set ℝ`;
* the concrete `ℝ^N` is replaced by an arbitrary real inner-product space `E`
  (the Butcher instance is recovered by `E = EuclideanSpace ℝ (Fin N)`,
  `s = Set.Icc a b`).

The constant `ℓ : ℝ` (not `ℝ≥0`) is intentional: one-sided Lipschitz
constants can be **negative**, and that is exactly when the condition is
strictly stronger than the two-sided Lipschitz condition (it gives
contractivity rather than mere boundedness of growth). This is a genuine
difference from `def:110A`, where `L : ℝ≥0` matched Mathlib's `LipschitzWith`
convention.

The constant `ℓ` is exposed as a parameter (matching the textbook's "with
one-sided Lipschitz constant `ℓ`"), not baked into an existential. The
existential variant `∃ ℓ, OneSidedLipschitzInSecond s ℓ f` is recoverable
downstream when needed. -/
def OneSidedLipschitzInSecond {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Set ℝ) (ℓ : ℝ) (f : ℝ → E → E) : Prop :=
  ∀ x ∈ s, ∀ Y Z : E, inner ℝ (f x Y - f x Z) (Y - Z) ≤ ℓ * ‖Y - Z‖ ^ 2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Butcher §112, Theorem 112B — *one-sided Lipschitz solution-difference bound*.

Verbatim textbook statement (Butcher 2008, p. 47):

> If `f` satisfies a one-sided Lipschitz condition with constant `ℓ`, and
> `y` and `z` are each solutions of `y'(x) = f(x, y(x))`, then for all
> `x ≥ x₀`, `‖y(x) - z(x)‖ ≤ exp(ℓ(x - x₀)) ‖y(x₀) - z(x₀)‖`.

We work on `[x₀, b]` (the textbook's `x ≥ x₀`, restricted to a closed
interval to match Mathlib's right-derivative convention). The
right-derivative shape `HasDerivWithinAt _ _ (Ici x) x` matches
`Section110.lean` and Mathlib's Grönwall API.

**Faithfulness flag.** The proof factor order is `exp(...) * ‖y x₀ - z x₀‖`
rather than the textbook's `‖y x₀ - z x₀‖ * exp(...)`. Mathematically
identical (real multiplication is commutative); the chosen order matches
Mathlib's `gronwallBound_ε0` output. -/
theorem one_sided_lipschitz_solution_diff_bound
    {x₀ b : ℝ}
    {ℓ : ℝ}
    {f : ℝ → E → E}
    (hf : OneSidedLipschitzInSecond (Icc x₀ b) ℓ f)
    {y z : ℝ → E}
    (hy_cont : ContinuousOn y (Icc x₀ b))
    (hy : ∀ x ∈ Ico x₀ b, HasDerivWithinAt y (f x (y x)) (Ici x) x)
    (hz_cont : ContinuousOn z (Icc x₀ b))
    (hz : ∀ x ∈ Ico x₀ b, HasDerivWithinAt z (f x (z x)) (Ici x) x) :
    ∀ x ∈ Icc x₀ b,
      ‖y x - z x‖ ≤ Real.exp (ℓ * (x - x₀)) * ‖y x₀ - z x₀‖ := by
  -- Define `g(x) := ‖y x - z x‖²`. The proof has six steps:
  --   1. Rewrite `g` to inner-product form.
  --   2. Compute the right derivative of `g`.
  --   3. Bound it via the one-sided Lipschitz hypothesis.
  --   4. Apply scalar Grönwall.
  --   5. Simplify `gronwallBound · · 0 ·`.
  --   6. Take the square root.
  set g : ℝ → ℝ := fun x => ‖y x - z x‖ ^ 2 with hg_def
  -- Step 1 — `g x = ⟪y x - z x, y x - z x⟫`.
  have hg_inner : ∀ x, g x = inner ℝ (y x - z x) (y x - z x) := fun x =>
    (real_inner_self_eq_norm_sq (y x - z x)).symm
  -- `g` is non-negative.
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
  -- Continuity of `g` on `[x₀, b]`.
  have hg_cont : ContinuousOn g (Icc x₀ b) := by
    have h_sub : ContinuousOn (fun x => y x - z x) (Icc x₀ b) := hy_cont.sub hz_cont
    exact (h_sub.norm).pow 2
  -- Step 2 — Right derivative of `g` on `[x₀, b)`.
  have hg_deriv : ∀ x ∈ Ico x₀ b,
      HasDerivWithinAt g (2 * inner ℝ (f x (y x) - f x (z x)) (y x - z x))
        (Ici x) x := by
    intro x hx_mem
    -- y - z has derivative f x (y x) - f x (z x).
    have hyz : HasDerivWithinAt (fun t => y t - z t)
        (f x (y x) - f x (z x)) (Ici x) x := (hy x hx_mem).sub (hz x hx_mem)
    -- Apply HasDerivWithinAt.inner ℝ to get the derivative of ⟪u t, u t⟫.
    have hinner :=
      (HasDerivWithinAt.inner (𝕜 := ℝ) hyz hyz :
        HasDerivWithinAt (fun t => inner ℝ (y t - z t) (y t - z t))
          (inner ℝ (y x - z x) (f x (y x) - f x (z x))
            + inner ℝ (f x (y x) - f x (z x)) (y x - z x)) (Ici x) x)
    -- Convert to g via congruence.
    have h_eq : (fun t => inner ℝ (y t - z t) (y t - z t)) = g := by
      funext t; exact (hg_inner t).symm
    rw [h_eq] at hinner
    -- Combine the two summands using real_inner_comm.
    have h_combine : inner ℝ (y x - z x) (f x (y x) - f x (z x))
        + inner ℝ (f x (y x) - f x (z x)) (y x - z x)
        = 2 * inner ℝ (f x (y x) - f x (z x)) (y x - z x) := by
      rw [real_inner_comm (y x - z x) (f x (y x) - f x (z x))]
      ring
    rw [h_combine] at hinner
    exact hinner
  -- Step 3 — Bound the derivative by `2ℓ * g x` using `def:112A`.
  have hg_bound : ∀ x ∈ Ico x₀ b,
      2 * inner ℝ (f x (y x) - f x (z x)) (y x - z x) ≤ 2 * ℓ * g x := by
    intro x hx_mem
    have hx_Icc : x ∈ Icc x₀ b := Ico_subset_Icc_self hx_mem
    have h_lip := hf x hx_Icc (y x) (z x)
    -- inner ℝ (f x (y x) - f x (z x)) (y x - z x) ≤ ℓ * ‖y x - z x‖^2
    have hg_eq : g x = ‖y x - z x‖ ^ 2 := rfl
    linarith
  -- Step 4 — Apply scalar Grönwall to obtain
  --   `g x ≤ g x₀ * exp(2ℓ (x - x₀))`.
  have hG : ∀ x ∈ Icc x₀ b,
      g x ≤ g x₀ * Real.exp (2 * ℓ * (x - x₀)) := by
    have h_main := le_gronwallBound_of_liminf_deriv_right_le
      (f := g)
      (f' := fun x => 2 * inner ℝ (f x (y x) - f x (z x)) (y x - z x))
      (δ := g x₀) (K := 2 * ℓ) (ε := 0) (a := x₀) (b := b)
      hg_cont
      (fun x hx_mem r hr =>
        (hg_deriv x hx_mem).liminf_right_slope_le hr)
      le_rfl
      (fun x hx_mem => by
        have := hg_bound x hx_mem
        linarith)
    intro x hx_mem
    have := h_main x hx_mem
    rwa [gronwallBound_ε0] at this
  -- Step 6 — Take the square root.
  intro x hx_mem
  have hgx := hG x hx_mem
  -- `g x = ‖y x - z x‖^2`, so `‖y x - z x‖ = √(g x)`.
  have h_sqrt_g : ∀ t, Real.sqrt (g t) = ‖y t - z t‖ := fun t => by
    show Real.sqrt (‖y t - z t‖ ^ 2) = ‖y t - z t‖
    rw [sq, Real.sqrt_mul_self (norm_nonneg _)]
  -- Take sqrt of both sides; the RHS factors via `Real.sqrt_mul`.
  have h_sqrt := Real.sqrt_le_sqrt hgx
  rw [h_sqrt_g, Real.sqrt_mul (hg_nonneg x₀), h_sqrt_g] at h_sqrt
  -- Convert `√(exp(2ℓ(x-x₀)))` to `exp(ℓ(x-x₀))` via `Real.exp_half`.
  have h_half : Real.sqrt (Real.exp (2 * ℓ * (x - x₀))) = Real.exp (ℓ * (x - x₀)) := by
    rw [← Real.exp_half]; ring_nf
  rw [h_half] at h_sqrt
  -- h_sqrt : ‖y x - z x‖ ≤ ‖y x₀ - z x₀‖ * exp(ℓ(x-x₀));
  -- goal:    ‖y x - z x‖ ≤ exp(ℓ(x-x₀)) * ‖y x₀ - z x₀‖.
  linarith [h_sqrt]

end OpenMath.Chapter1.Section112
