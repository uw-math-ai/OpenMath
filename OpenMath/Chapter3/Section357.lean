import OpenMath.Chapter3.Section370
import OpenMath.Chapter3.Section381
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

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

/-! ## Theorem 357C — algebraic stability implies BN-stability

The Burrage–Butcher theorem: an algebraically stable Runge–Kutta method is
BN-stable. The proof rests on the algebraic identity

\[
  \|y_1\|^2 - \|y_0\|^2 = 2h \sum_i b_i \langle F_i, Y_i\rangle
                      - h^2 \sum_{ij}(2 b_i a_{ij} - b_i b_j)\langle F_i, F_j\rangle,
\]

where `F i = f(x₀ + cᵢ h, Y i)`. Under algebraic stability:

* The first term is `≤ 0` because `b_i > 0`, `h > 0`, and dissipativity gives
  `⟨F_i, Y_i⟩ ≤ 0`.
* The second term's coefficient sum equals
  `∑ symplecticityMatrix M i j ⟨F_i, F_j⟩`, which is `≥ 0` because the
  symplecticity matrix is positive semidefinite.

`symplecticityMatrix M` is the textbook form
`m_{ij} = b_i a_{ij} + b_j a_{ji} − b_i b_j` (equation (357d) and
equivalently (370a)); the proof below uses this form directly via
the index-swap identity in Lemma 1, which holds for **all** `M`
without an `A` symmetric hypothesis.
-/

/-- Lemma 1 — entry-wise unfolding plus an index-swap identity:
the quadratic form built from the asymmetric coefficient
`(2 bᵢ aᵢⱼ − bᵢ bⱼ)` agrees with the quadratic form built from
`symplecticityMatrix M`. The equality holds for **every**
`RKTableau` — no `A` symmetric hypothesis is needed once
`symplecticityMatrix` is the textbook form
`m_{ij} = bᵢ aᵢⱼ + aⱼᵢ bⱼ − bᵢ bⱼ`. The argument is `Finset.sum_comm`
together with `⟨Fⱼ, Fᵢ⟩ = ⟨Fᵢ, Fⱼ⟩`. -/
private lemma symplecticityMatrix_quadratic_form_eq {s : ℕ}
    (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (F : Fin s → N) :
    ∑ i, ∑ j, (2 * M.b i * M.A i j - M.b i * M.b j) *
        inner ℝ (F i) (F j)
    = ∑ i, ∑ j, symplecticityMatrix M i j * inner ℝ (F i) (F j) := by
  -- Step 1: unfold symplecticityMatrix entry-wise to the textbook form.
  have hM : ∀ i j, symplecticityMatrix M i j =
      M.b i * M.A i j + M.A j i * M.b j - M.b i * M.b j := by
    intro i j
    simp [symplecticityMatrix, Matrix.mul_apply, Matrix.diagonal_apply,
          Matrix.vecMulVec, Matrix.transpose_apply, Matrix.sub_apply,
          Matrix.add_apply]
  -- Step 2: rewrite the RHS so both sides have the same shape with explicit
  -- coefficients depending on `M.b` and `M.A`.
  have rhs_rewrite :
      (∑ i, ∑ j, symplecticityMatrix M i j * inner ℝ (F i) (F j))
      = ∑ i, ∑ j, (M.b i * M.A i j + M.A j i * M.b j - M.b i * M.b j)
                  * inner ℝ (F i) (F j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM]
  rw [rhs_rewrite]
  -- Step 3: the key index-swap identity:
  --   ∑ᵢⱼ a_{ji} b_j ⟨F i, F j⟩ = ∑ᵢⱼ b_i a_{ij} ⟨F i, F j⟩
  -- via i ↔ j swap and ⟨F j, F i⟩ = ⟨F i, F j⟩.
  have hswap : ∑ i, ∑ j, M.A j i * M.b j * inner ℝ (F i) (F j)
             = ∑ i, ∑ j, M.b i * M.A i j * inner ℝ (F i) (F j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (F j) (F i)]
    ring
  -- Step 4: split both sides into the linear pieces and use hswap.
  have lhs_split :
      (∑ i, ∑ j, (2 * M.b i * M.A i j - M.b i * M.b j) * inner ℝ (F i) (F j))
      = (2 : ℝ) * (∑ i, ∑ j, M.b i * M.A i j * inner ℝ (F i) (F j))
        - (∑ i, ∑ j, M.b i * M.b j * inner ℝ (F i) (F j)) := by
    simp only [sub_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have rhs_split :
      (∑ i, ∑ j, (M.b i * M.A i j + M.A j i * M.b j - M.b i * M.b j)
                * inner ℝ (F i) (F j))
      = (∑ i, ∑ j, M.b i * M.A i j * inner ℝ (F i) (F j))
        + (∑ i, ∑ j, M.A j i * M.b j * inner ℝ (F i) (F j))
        - (∑ i, ∑ j, M.b i * M.b j * inner ℝ (F i) (F j)) := by
    simp only [add_mul, sub_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [lhs_split, rhs_split, hswap]
  ring

/-- Lemma 2 — the BN-stability algebraic identity (★).

In a real inner-product space, given the stage equations
`Y i = y₀ + h • ∑ⱼ aᵢⱼ • F j` and the update equation
`y₁ = y₀ + h • ∑ᵢ bᵢ • F i`,

\[
  \|y_1\|^2 - \|y_0\|^2 = 2h \sum_i b_i \langle F_i, Y_i\rangle
    - h^2 \sum_{ij} (2 b_i a_{ij} - b_i b_j) \langle F_i, F_j\rangle.
\]

The proof uses the polarisation `‖a‖² − ‖b‖² = ⟨a + b, a − b⟩` together
with the per-stage identity `y₁ + y₀ = 2 • Y i + h • ∑ⱼ (bⱼ − 2 aᵢⱼ) • F j`. -/
private lemma bn_stability_identity {s : ℕ}
    (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (h : ℝ) (y₀ y₁ : N) (Y : Fin s → N) (F : Fin s → N)
    (hY_stage : ∀ i, Y i = y₀ + h • ∑ j, M.A i j • F j)
    (hy_update : y₁ = y₀ + h • ∑ i, M.b i • F i) :
    ‖y₁‖^2 - ‖y₀‖^2
      = 2 * h * (∑ i, M.b i * inner ℝ (F i) (Y i))
      - h^2 * (∑ i, ∑ j, (2 * M.b i * M.A i j - M.b i * M.b j) *
                          inner ℝ (F i) (F j)) := by
  -- Set V = ∑ⱼ bⱼ • Fⱼ, the "update vector".
  set V : N := ∑ j, M.b j • F j with hV_def
  -- Step 1: ‖y₁‖² - ‖y₀‖² = 2 h ⟨y₀, V⟩ + h² ‖V‖² (since y₁ = y₀ + h • V).
  have hsq : ‖y₁‖^2 - ‖y₀‖^2 = 2 * h * inner ℝ y₀ V + h^2 * ‖V‖^2 := by
    rw [hy_update, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow]
    have hh : ‖h‖ ^ 2 = h ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    rw [hh]; ring
  rw [hsq]
  -- Step 2: ⟨y₀, V⟩ = ∑ⱼ bⱼ * ⟨y₀, Fⱼ⟩.
  have hy0V : inner ℝ y₀ V = ∑ j, M.b j * inner ℝ y₀ (F j) := by
    show inner ℝ y₀ (∑ j, M.b j • F j) = _
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
  -- Step 3: ‖V‖² = ∑ᵢⱼ bᵢ bⱼ ⟨Fᵢ, Fⱼ⟩.
  have hVsq : ‖V‖^2 = ∑ i, ∑ j, M.b i * M.b j * inner ℝ (F i) (F j) := by
    rw [← real_inner_self_eq_norm_sq]
    show inner ℝ (∑ j, M.b j • F j) (∑ j, M.b j • F j) = _
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]; ring
  rw [hy0V, hVsq]
  -- Step 4: ⟨Fᵢ, Yᵢ⟩ = ⟨Fᵢ, y₀⟩ + h ∑ⱼ aᵢⱼ ⟨Fᵢ, Fⱼ⟩, so
  --   ⟨y₀, Fᵢ⟩ = ⟨Fᵢ, y₀⟩ = ⟨Fᵢ, Yᵢ⟩ - h ∑ⱼ aᵢⱼ ⟨Fᵢ, Fⱼ⟩.
  have hy0Fi : ∀ i, inner ℝ y₀ (F i) =
      inner ℝ (F i) (Y i) - h * ∑ j, M.A i j * inner ℝ (F i) (F j) := by
    intro i
    rw [real_inner_comm, hY_stage i, inner_add_right, real_inner_smul_right, inner_sum]
    simp_rw [real_inner_smul_right]
    rw [Finset.mul_sum]; ring
  -- Step 5: substitute hy0Fi.
  have hsubst :
      ∑ j, M.b j * inner ℝ y₀ (F j)
      = ∑ j, M.b j * (inner ℝ (F j) (Y j)
        - h * ∑ k, M.A j k * inner ℝ (F j) (F k)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hy0Fi j]
  rw [hsubst]
  -- Step 6: distribute the multiplications and combine into the desired form.
  have hLHS :
      2 * h * ∑ j, M.b j * (inner ℝ (F j) (Y j)
        - h * ∑ k, M.A j k * inner ℝ (F j) (F k))
      + h^2 * ∑ i, ∑ j, M.b i * M.b j * inner ℝ (F i) (F j)
      = 2 * h * ∑ j, M.b j * inner ℝ (F j) (Y j)
        - 2 * h^2 * ∑ j, ∑ k, M.b j * M.A j k * inner ℝ (F j) (F k)
        + h^2 * ∑ i, ∑ j, M.b i * M.b j * inner ℝ (F i) (F j) := by
    have hsplit : ∀ j,
        M.b j * (inner ℝ (F j) (Y j)
          - h * ∑ k, M.A j k * inner ℝ (F j) (F k))
        = M.b j * inner ℝ (F j) (Y j)
          - h * ∑ k, M.b j * M.A j k * inner ℝ (F j) (F k) := by
      intro j
      have hmul : ∑ k, M.b j * M.A j k * inner ℝ (F j) (F k)
                 = M.b j * ∑ k, M.A j k * inner ℝ (F j) (F k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hmul]; ring
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hLHS]
  -- Combine: 2h² ∑ⱼ ∑ₖ bⱼ aⱼₖ ⟨Fⱼ, Fₖ⟩ - h² ∑ᵢ ∑ⱼ bᵢ bⱼ ⟨Fᵢ, Fⱼ⟩
  -- = h² ∑ᵢ ∑ⱼ (2 bᵢ aᵢⱼ - bᵢ bⱼ) ⟨Fᵢ, Fⱼ⟩.
  have hcombine :
      2 * h^2 * ∑ j, ∑ k, M.b j * M.A j k * inner ℝ (F j) (F k)
      - h^2 * ∑ i, ∑ j, M.b i * M.b j * inner ℝ (F i) (F j)
      = h^2 * ∑ i, ∑ j, (2 * M.b i * M.A i j - M.b i * M.b j) *
                         inner ℝ (F i) (F j) := by
    rw [show (∑ i, ∑ j, (2 * M.b i * M.A i j - M.b i * M.b j) *
                       inner ℝ (F i) (F j))
         = ∑ i, ∑ j, (2 * (M.b i * M.A i j * inner ℝ (F i) (F j))
                      - M.b i * M.b j * inner ℝ (F i) (F j))
        from by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring]
    simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  linarith [hcombine]

/-- Lemma 3 — a positive-semidefinite real matrix produces a non-negative
value when summed against the Gram matrix of any vectors `F i` in a real
inner-product space.

Proof outline: by `Matrix.posSemidef_iff_eq_conjTranspose_mul_self`,
`hPSD` provides `B` with `M = Bᵀ B` (over ℝ). Then
`∑ᵢⱼ M_{ij} ⟨Fᵢ, Fⱼ⟩ = ∑_k ‖∑ᵢ B_{ki} Fᵢ‖² ≥ 0`. -/
private lemma posSemidef_inner_form_nonneg {s : ℕ}
    {M : Matrix (Fin s) (Fin s) ℝ} (hM : M.PosSemidef)
    {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (F : Fin s → N) :
    0 ≤ ∑ i, ∑ j, M i j * inner ℝ (F i) (F j) := by
  -- Cholesky-like factorisation: ∃ B, M = Bᵀ B (conjTranspose = transpose over ℝ).
  obtain ⟨B, hB⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hM
  -- Set v k := ∑ i, B k i • F i; then ∑ M_{ij} ⟨F i, F j⟩ = ∑ k ‖v k‖² ≥ 0.
  set v : Fin s → N := fun k => ∑ i, B k i • F i with hv_def
  have hvk_sq : ∀ k, ‖v k‖^2 =
      ∑ i, ∑ j, B k i * B k j * inner ℝ (F i) (F j) := by
    intro k
    rw [← real_inner_self_eq_norm_sq]
    show inner ℝ (∑ i, B k i • F i) (∑ i, B k i • F i) = _
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
    ring
  -- Entry-wise factorisation: M i j = ∑ k, B k i * B k j.
  have hMij : ∀ i j, M i j = ∑ k, B k i * B k j := by
    intro i j
    rw [hB]
    simp [Matrix.mul_apply]
  -- Combine via sum_comm to express the goal as ∑ k ‖v k‖² ≥ 0.
  have hsum_eq :
      ∑ i, ∑ j, M i j * inner ℝ (F i) (F j) = ∑ k, ‖v k‖^2 := by
    have hgoal_expand :
        (∑ i, ∑ j, M i j * inner ℝ (F i) (F j))
        = ∑ i, ∑ j, (∑ k, B k i * B k j) * inner ℝ (F i) (F j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hMij]
    rw [hgoal_expand]
    -- Push ∑ k outermost via two sum_comm swaps.
    simp_rw [Finset.sum_mul]
    -- Goal: ∑ i, ∑ j, ∑ k, B k i * B k j * inner = ∑ k, ‖v k‖²
    rw [show (∑ i, ∑ j, ∑ k, B k i * B k j * inner ℝ (F i) (F j))
            = ∑ i, ∑ k, ∑ j, B k i * B k j * inner ℝ (F i) (F j) from by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hvk_sq k]
  rw [hsum_eq]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- Butcher §357 Theorem 357C — algebraic stability implies BN-stability
(Burrage–Butcher).

Given an algebraically stable Runge–Kutta method `M`, every dissipative
non-autonomous IVP and every step yields `‖y₁‖ ≤ ‖y₀‖`. -/
theorem algebraicallyStable_isBNStable
    {s : ℕ} (M : RKTableau s) (hAS : IsAlgebraicallyStable M) :
    IsBNStable M := by
  intro N _ _ f hDiss x₀ y₀ h hh y₁ hStep
  obtain ⟨Y, hY_stage, hy_update⟩ := hStep
  obtain ⟨hb_pos, hM_psd⟩ := hAS
  -- Define F i := f (x₀ + c i * h) (Y i).
  set F : Fin s → N := fun i => f (x₀ + M.c i * h) (Y i) with hF_def
  have hY_stage' : ∀ i, Y i = y₀ + h • ∑ j, M.A i j • F j := hY_stage
  have hy_update' : y₁ = y₀ + h • ∑ i, M.b i • F i := hy_update
  -- Apply Lemma 2 (algebraic identity).
  have hIdentity := bn_stability_identity M h y₀ y₁ Y F hY_stage' hy_update'
  -- First term ≤ 0 by dissipativity.
  have hFirst : 2 * h * (∑ i, M.b i * inner ℝ (F i) (Y i)) ≤ 0 := by
    have h2h : 0 ≤ 2 * h := by linarith
    apply mul_nonpos_of_nonneg_of_nonpos h2h
    apply Finset.sum_nonpos
    intro i _
    apply mul_nonpos_of_nonneg_of_nonpos (hb_pos i).le
    show inner ℝ (F i) (Y i) ≤ 0
    simpa [F, hF_def] using hDiss (x₀ + M.c i * h) (Y i)
  -- Second term: equals symplecticity-matrix quadratic form via Lemma 1,
  -- and is ≥ 0 via Lemma 3.
  have hForm := symplecticityMatrix_quadratic_form_eq M F
  have hSecond : 0 ≤ ∑ i, ∑ j, (2 * M.b i * M.A i j - M.b i * M.b j) *
                                 inner ℝ (F i) (F j) := by
    rw [hForm]
    exact posSemidef_inner_form_nonneg hM_psd F
  -- Combine.
  have hbound : ‖y₁‖^2 ≤ ‖y₀‖^2 := by
    have h2_nonneg : 0 ≤ h^2 := sq_nonneg h
    have h_h2_term : 0 ≤ h^2 * (∑ i, ∑ j,
        (2 * M.b i * M.A i j - M.b i * M.b j) * inner ℝ (F i) (F j)) :=
      mul_nonneg h2_nonneg hSecond
    linarith [hIdentity]
  exact norm_le_of_norm_sq_le y₁ y₀ hbound

end OpenMath.Chapter3.Section357
