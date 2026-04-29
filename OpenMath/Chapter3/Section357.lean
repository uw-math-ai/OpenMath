import OpenMath.Chapter3.Section370
import OpenMath.Chapter3.Section381
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Butcher §357 — Non-linear stability of Runge–Kutta methods

This file formalises Definitions 357A (BN-stability) and 357B (algebraic
stability) from Butcher's *Numerical Methods for Ordinary Differential
Equations* (3rd ed., page 271).

## Definition 357A textbook statement (quoted verbatim from
`extraction/raw_text/ch03.txt:6806-6813`)

> **Definition 357A.** A Runge–Kutta `(A, b, c)` is *'BN-stable'* if for
> any initial value problem
> `y'(x) = f(x, y(x)), y(x₀) = y₀`,
> satisfying the condition
> `⟨f(x, u), u⟩ ≤ 0`,
> the sequence of computed solutions satisfies
> `‖yₙ‖ ≤ ‖yₙ₋₁‖`.

This is the non-autonomous, single-solution simplification of
B-stability (Butcher §357 explicitly notes at lines 6790–6797 that the
test condition `⟨f(x, u), u⟩ ≤ 0` (equation (357c)) replaces the
"formally more complicated" two-solution condition (357a)).

## Definition 357B textbook statement (quoted verbatim from
`def_357B.json`)

> A Runge–Kutta method `(A, b, c)` is 'algebraically stable' if
> `bᵢ > 0`, for `i = 1, 2, …, s`, and if the matrix `M`, given by
> `M = diag(b)A + A diag(b) − bbᵀ` (357d), is positive
> semi-definite.

## Faithfulness notes

* `IsBNStable M` is the predicate "for every real inner-product space
  `N`, every `f : ℝ → N → N` satisfying the dissipativity condition
  `∀ x u, ⟨f x u, u⟩ ≤ 0`, every step size `h > 0`, every starting time
  `x₀`, and every pair `(y₀, y₁)` related by one non-autonomous
  Runge–Kutta step of `M`, the norm does not grow: `‖y₁‖ ≤ ‖y₀‖`."
  This is the textbook definition verbatim — the *semantic*
  norm-non-increase under dissipative right-hand sides — not the matrix
  characterisation (357d), which is `IsAlgebraicallyStable` (def:357B).
  Defining BN-stability as the matrix condition would be definition
  smuggling: the matrix condition is *sufficient* for BN-stability
  (Burrage–Butcher, thm:357C), not the primary definition.
* `[InnerProductSpace ℝ N]` is required: Butcher's definition is
  inner-product-intrinsic ("for `‖·‖` the corresponding norm" of "a
  standard semi-inner product"). Weakening to `NormedSpace ℝ N` would
  change the meaning.
* The continuity-in-`x` regularity implicit in Butcher's "for any IVP"
  phrasing is **not** added as a hypothesis: our predicate concerns the
  algebraic relation between `(y₀, y₁)` via the stage equations, not
  IVP existence/uniqueness. Adding regularity would be a
  *strengthening*, not a faithfulness improvement.
* The matrix `M` of equation (357d) is **literally the same matrix** as
  Butcher's equation (370a) used to define symplecticity. We reuse
  `OpenMath.Chapter3.Section370.symplecticityMatrix` rather than
  introducing a parallel definition; symplecticity is the case `M = 0`,
  and algebraic stability is the case `M ⪰ 0` together with `b > 0`.
* `IsAlgebraicallyStable R` is the conjunction of two textbook clauses:
  componentwise positivity of `b` and `(symplecticityMatrix R).PosSemidef`.
  This matches the textbook definition verbatim with no reformulation.
* The LLM-extracted dependency graph lists `def:357B → def:357A`
  (B-stability), but Butcher's text presents algebraic stability as a
  *sufficient condition* for B/BN-stability (Burrage–Butcher), not the
  other way round. Algebraic stability is a self-contained matrix
  condition; the JSON edge is reversed and is **not** a real
  mathematical dependency for this definition.

## Concrete witnesses — the implicit midpoint method

The implicit midpoint method (cycle 027's `implicitMidpoint`,
`s = 1`, `A = [[1/2]]`, `b = [1]`, `c = [1/2]`) witnesses both
predicates:

* `implicitMidpoint_isAlgebraicallyStable`: its symplecticity matrix
  vanishes, so the zero matrix is positive semidefinite; its single
  weight is `1 > 0`.
* `implicitMidpoint_isBNStable`: a direct inner-product computation.
  Setting `K := f(x₀ + h/2, Y 0)`, the stage equation
  `Y 0 = y₀ + (h/2) • K` and update `y₁ = y₀ + h • K` give
  `‖y₁‖² = ‖y₀‖² + 2h ⟨K, Y 0⟩`, and dissipativity
  `⟨K, Y 0⟩ ≤ 0` together with `h > 0` yields `‖y₁‖² ≤ ‖y₀‖²`.
-/

namespace OpenMath.Chapter3.Section357

open OpenMath.Chapter3.Section312
open OpenMath.Chapter3.Section370
open OpenMath.Chapter3.Section381

/-! ## Definition 357A — BN-stability -/

/-- Butcher §357 Definition 357A — a Runge–Kutta method is *BN-stable*
iff for every real inner-product space `N`, every (non-autonomous) RHS
`f : ℝ → N → N` satisfying the dissipativity condition
`∀ x u, ⟨f x u, u⟩ ≤ 0` (Butcher's (357c)), every step size `h > 0`,
every starting time `x₀`, and every pair `(y₀, y₁)` related by one
non-autonomous step of `M` (`M.IsRKOneStepNonAut f x₀ y₀ h y₁`), the
norm does not grow: `‖y₁‖ ≤ ‖y₀‖`.

This is the *semantic* form of the textbook definition; the matrix
characterisation (357d) — `IsAlgebraicallyStable` — is `def:357B`,
which is *sufficient* but not the primary definition. -/
def IsBNStable {s : ℕ} (M : RKTableau s) : Prop :=
  ∀ {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (f : ℝ → N → N)
    (_hDiss : ∀ x u, inner ℝ (f x u) u ≤ 0)
    (x₀ : ℝ) (y₀ : N) (h : ℝ) (_hh : 0 < h) (y₁ : N),
    M.IsRKOneStepNonAut f x₀ y₀ h y₁ → ‖y₁‖ ≤ ‖y₀‖

/-! ## Definition 357B — Algebraically stable Runge–Kutta methods -/

/-- Butcher §357 Definition 357B — a Runge–Kutta method `(A, b, c)` is
*algebraically stable* iff every weight `bᵢ` is strictly positive and
the symplecticity matrix `M = diag(b) A + A diag(b) − b bᵀ` (equation
(357d), the same matrix as in (370a)) is positive semidefinite. -/
def IsAlgebraicallyStable {s : ℕ} (R : RKTableau s) : Prop :=
  (∀ i, 0 < R.b i) ∧ (symplecticityMatrix R).PosSemidef

/-! ## Concrete witnesses — implicit midpoint -/

/-- The implicit midpoint method is algebraically stable: its single
weight is `1 > 0`, and its symplecticity matrix vanishes (cycle 027's
`implicitMidpoint_isSymplectic`), so the zero matrix is trivially
positive semidefinite. -/
theorem implicitMidpoint_isAlgebraicallyStable :
    IsAlgebraicallyStable implicitMidpoint := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    norm_num [implicitMidpoint]
  · rw [show symplecticityMatrix implicitMidpoint = 0 from
        implicitMidpoint_isSymplectic]
    exact Matrix.PosSemidef.zero

/-! ### `implicitMidpoint_isBNStable` — non-vacuity witness for `def:357A`

The implicit midpoint method has `s = 1`, `A 0 0 = 1/2`, `b 0 = 1`,
`c 0 = 1/2`. Given dissipativity and `IsRKOneStepNonAut`, set
`K := f(x₀ + h/2, Y 0)`. The stage equation reads
`Y 0 = y₀ + (h/2) • K` and the update reads `y₁ = y₀ + h • K`.
Compute:

```
‖y₁‖² = ‖y₀ + h • K‖²                           (substitute)
      = ‖y₀‖² + 2 h ⟨K, y₀⟩ + h² ‖K‖²            (norm-add square)
      = ‖y₀‖² + 2 h ⟨K, Y 0 - (h/2) • K⟩ + h² ‖K‖²  (sub-stage equation)
      = ‖y₀‖² + 2 h ⟨K, Y 0⟩ - h² ‖K‖² + h² ‖K‖²
      = ‖y₀‖² + 2 h ⟨K, Y 0⟩
      ≤ ‖y₀‖²                                    (dissipativity at (x₀+h/2, Y 0))
```

Then `‖y₁‖ ≤ ‖y₀‖` by square-root monotonicity. -/

/-- Algebraic identity used in the implicit-midpoint BN-stability witness.

In a real inner-product space, if `Y0 = y₀ + (h/2) • K` and
`y₁ = y₀ + h • K`, then `‖y₁‖² = ‖y₀‖² + 2 h ⟨K, Y0⟩`.

The cross term arising from `y₀ = Y0 - (h/2) • K` precisely cancels
the `h² ‖K‖²` term from the norm-add expansion. -/
private lemma midpoint_norm_sq_identity {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (h : ℝ) (y₀ Y0 K y₁ : N)
    (hY0 : Y0 = y₀ + (h / 2) • K) (hy1 : y₁ = y₀ + h • K) :
    ‖y₁‖ ^ 2 = ‖y₀‖ ^ 2 + 2 * h * inner ℝ K Y0 := by
  have hy0 : y₀ = Y0 - (h / 2) • K := by
    rw [hY0]; abel
  -- Expand ‖y₁‖² via ⟨y₁, y₁⟩.
  have h_self : ‖y₁‖ ^ 2 = inner ℝ y₁ y₁ := (real_inner_self_eq_norm_sq y₁).symm
  rw [h_self, hy1]
  rw [inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_left, real_inner_smul_right]
  -- Now in fully real form: ⟨y₀,y₀⟩ + h ⟨y₀,K⟩ + (h ⟨K,y₀⟩ + h(h ⟨K,K⟩)).
  have h_swap : (inner ℝ K y₀ : ℝ) = inner ℝ y₀ K := real_inner_comm y₀ K
  have h_y0_K : (inner ℝ y₀ K : ℝ) = inner ℝ Y0 K - (h / 2) * inner ℝ K K := by
    rw [hy0, inner_sub_left, real_inner_smul_left]
  have h_K_Y0 : (inner ℝ Y0 K : ℝ) = inner ℝ K Y0 := real_inner_comm K Y0
  have h_y0_y0 : (inner ℝ y₀ y₀ : ℝ) = ‖y₀‖ ^ 2 := real_inner_self_eq_norm_sq y₀
  have h_K_K : (inner ℝ K K : ℝ) = ‖K‖ ^ 2 := real_inner_self_eq_norm_sq K
  rw [h_swap, h_y0_K, h_K_Y0, h_y0_y0, h_K_K]
  ring

/-- Square-root monotonicity packaged for the BN-stability conclusion:
`‖a‖² ≤ ‖b‖²` implies `‖a‖ ≤ ‖b‖`. -/
private lemma norm_le_of_norm_sq_le {N : Type*} [NormedAddCommGroup N]
    (a b : N) (h : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2) : ‖a‖ ≤ ‖b‖ :=
  le_of_sq_le_sq h (norm_nonneg _)

/-- Butcher §357 — the implicit midpoint method is BN-stable.

Witness for non-vacuity of `def:357A`: the implicit midpoint method
satisfies the BN-stability predicate. Combined with cycle 027's
`implicitMidpoint_isSymplectic` and cycle 028's
`implicitMidpoint_isAlgebraicallyStable`, this confirms that all three
non-linear-stability predicates are simultaneously satisfiable on a
concrete tableau. -/
theorem implicitMidpoint_isBNStable :
    IsBNStable implicitMidpoint := by
  intro N _ _ f hDiss x₀ y₀ h hh y₁ hStep
  obtain ⟨Y, hY_stage, hy₁⟩ := hStep
  -- Reduce the stage and update equations to canonical form.
  have hs := hY_stage 0
  simp [implicitMidpoint] at hs
  -- hs : Y 0 = y₀ + h • 2⁻¹ • f (x₀ + 2⁻¹ * h) (Y 0)
  simp [implicitMidpoint] at hy₁
  -- hy₁ : y₁ = y₀ + h • f (x₀ + 2⁻¹ * h) (Y 0)
  -- Define K = f(x₀ + h/2, Y 0).
  set K : N := f (x₀ + 2⁻¹ * h) (Y 0) with hK_def
  -- Stage equation in K-form: Y 0 = y₀ + (h/2) • K.
  have hY0 : Y 0 = y₀ + (h / 2) • K := by
    rw [hs, smul_smul]; ring_nf
  -- Update equation in K-form: y₁ = y₀ + h • K.
  have hy1 : y₁ = y₀ + h • K := hy₁
  -- Algebraic identity: ‖y₁‖² = ‖y₀‖² + 2 h ⟨K, Y 0⟩.
  have hSqEq := midpoint_norm_sq_identity (N := N) h y₀ (Y 0) K y₁ hY0 hy1
  -- Dissipativity at (x₀ + h/2, Y 0): ⟨K, Y 0⟩ ≤ 0.
  have hinner : inner ℝ K (Y 0) ≤ 0 := hDiss (x₀ + 2⁻¹ * h) (Y 0)
  have hbound : ‖y₁‖ ^ 2 ≤ ‖y₀‖ ^ 2 := by
    have h2h : 0 ≤ 2 * h := by linarith
    have hprod : 2 * h * inner ℝ K (Y 0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h2h hinner
    linarith [hSqEq]
  exact norm_le_of_norm_sq_le y₁ y₀ hbound

end OpenMath.Chapter3.Section357
