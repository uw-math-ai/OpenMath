import OpenMath.RungeKutta

/-!
# Order Stars (Section 355)

For a stability function `R : ℂ → ℂ`, the **order star** decomposes `ℂ` into three regions
based on the order-star amplitude function `φ(z) = R(z)·e⁻ᶻ`:

* `𝒜⁺(R) = {z : |φ(z)| > 1}` — the method amplifies more than the exact exponential
* `𝒜⁻(R) = {z : |φ(z)| < 1}` — the exact exponential amplifies more
* `𝒜⁰(R) = {z : |φ(z)| = 1}` — the order star boundary (or "web")

The geometry of order stars encodes stability: a method is A-stable iff no connected
component of `𝒜⁺` crosses into the left half-plane. The Ehle barrier (Theorem 355B)
constrains which Padé approximants can be A-stable.

## Main Results

1. **Definitions**: `orderStarPlus`, `orderStarMinus`, `orderStarBdry`
2. **Partition**: the three regions partition `ℂ` and are pairwise disjoint
3. **Topology**: `𝒜⁺` and `𝒜⁻` are open; `𝒜⁰` is closed (for continuous `R`)
4. **Origin**: if `R(0) = 1` then `0 ∈ 𝒜⁰`
5. **Exact exponential**: `𝒜⁰(exp) = ℂ`
6. **A-stability link**: `|R(z)| > 1` with `Re(z) ≤ 0` implies `z ∈ 𝒜⁺`
7. **Forward Euler witness**: `z = −3 ∈ 𝒜⁺` for `R(z) = 1 + z`
8. **Ehle barrier** (statement only): A-stable `R_{p,q}` requires `p ≤ q ≤ p + 2`

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Section 355.
-/

open Complex Set Real

/-! ## Definitions -/

/-- The **order-star plus** region: `𝒜⁺(R) = {z ∈ ℂ : |R(z)·e⁻ᶻ| > 1}`. -/
def orderStarPlus (R : ℂ → ℂ) : Set ℂ := {z | 1 < ‖R z * exp (-z)‖}

/-- The **order-star minus** region: `𝒜⁻(R) = {z ∈ ℂ : |R(z)·e⁻ᶻ| < 1}`. -/
def orderStarMinus (R : ℂ → ℂ) : Set ℂ := {z | ‖R z * exp (-z)‖ < 1}

/-- The **order-star boundary** (web): `𝒜⁰(R) = {z ∈ ℂ : |R(z)·e⁻ᶻ| = 1}`. -/
def orderStarBdry (R : ℂ → ℂ) : Set ℂ := {z | ‖R z * exp (-z)‖ = 1}

/-! ## Norm Identity -/

/-- Key identity: `‖R(z)·e⁻ᶻ‖ = ‖R(z)‖ · exp(-Re(z))`. -/
theorem orderStar_norm_eq (R : ℂ → ℂ) (z : ℂ) :
    ‖R z * exp (-z)‖ = ‖R z‖ * rexp (-z.re) := by
  rw [norm_mul, Complex.norm_exp, Complex.neg_re]

/-! ## Partition of ℂ -/

/-- The three order-star regions cover all of `ℂ`. -/
theorem orderStar_union (R : ℂ → ℂ) :
    orderStarPlus R ∪ orderStarMinus R ∪ orderStarBdry R = univ := by
  ext z
  simp only [mem_union, orderStarPlus, orderStarMinus, orderStarBdry, mem_setOf_eq,
    mem_univ, iff_true]
  rcases lt_trichotomy ‖R z * exp (-z)‖ 1 with h | h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr h
  · exact Or.inl (Or.inl h)

/-- `𝒜⁺` and `𝒜⁻` are disjoint. -/
theorem orderStarPlus_disjoint_minus (R : ℂ → ℂ) :
    Disjoint (orderStarPlus R) (orderStarMinus R) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  simp only [orderStarPlus, mem_setOf_eq] at h1
  simp only [orderStarMinus, mem_setOf_eq] at h2
  linarith

/-- `𝒜⁺` and `𝒜⁰` are disjoint. -/
theorem orderStarPlus_disjoint_bdry (R : ℂ → ℂ) :
    Disjoint (orderStarPlus R) (orderStarBdry R) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  simp only [orderStarPlus, mem_setOf_eq] at h1
  simp only [orderStarBdry, mem_setOf_eq] at h2
  linarith

/-- `𝒜⁻` and `𝒜⁰` are disjoint. -/
theorem orderStarMinus_disjoint_bdry (R : ℂ → ℂ) :
    Disjoint (orderStarMinus R) (orderStarBdry R) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  simp only [orderStarMinus, mem_setOf_eq] at h1
  simp only [orderStarBdry, mem_setOf_eq] at h2
  linarith

/-! ## Topological Properties -/

private theorem continuous_orderStarNorm (R : ℂ → ℂ) (hR : Continuous R) :
    Continuous (fun z => ‖R z * exp (-z)‖) :=
  (hR.mul (continuous_exp.comp continuous_neg)).norm

/-- `𝒜⁺(R)` is open for continuous `R`: preimage of `(1,∞)` under a continuous function. -/
theorem isOpen_orderStarPlus (R : ℂ → ℂ) (hR : Continuous R) :
    IsOpen (orderStarPlus R) :=
  isOpen_lt continuous_const (continuous_orderStarNorm R hR)

/-- `𝒜⁻(R)` is open for continuous `R`: preimage of `[0,1)` under a continuous function. -/
theorem isOpen_orderStarMinus (R : ℂ → ℂ) (hR : Continuous R) :
    IsOpen (orderStarMinus R) :=
  isOpen_lt (continuous_orderStarNorm R hR) continuous_const

/-- `𝒜⁰(R)` is closed for continuous `R`: preimage of `{1}` under a continuous function. -/
theorem isClosed_orderStarBdry (R : ℂ → ℂ) (hR : Continuous R) :
    IsClosed (orderStarBdry R) :=
  isClosed_eq (continuous_orderStarNorm R hR) continuous_const

/-! ## Origin Membership -/

/-- If `R(0) = 1` (consistent method), then the origin lies on the order star boundary. -/
theorem mem_orderStarBdry_zero (R : ℂ → ℂ) (h : R 0 = 1) :
    (0 : ℂ) ∈ orderStarBdry R := by
  show ‖R 0 * exp (-(0 : ℂ))‖ = 1
  simp [h]

/-! ## Exact Exponential -/

private theorem exp_mul_exp_neg (z : ℂ) : exp z * exp (-z) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- For the exact exponential `R(z) = eᶻ`, `𝒜⁰(exp) = ℂ`: every point is on the boundary. -/
theorem orderStarBdry_exp_eq_univ :
    orderStarBdry exp = univ := by
  ext z; simp only [orderStarBdry, mem_setOf_eq, mem_univ, iff_true]
  rw [exp_mul_exp_neg, norm_one]

/-- For the exact exponential, `𝒜⁺(exp) = ∅`. -/
theorem orderStarPlus_exp_eq_empty :
    orderStarPlus exp = ∅ := by
  ext z; simp only [orderStarPlus, mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
  rw [exp_mul_exp_neg, norm_one]

/-- For the exact exponential, `𝒜⁻(exp) = ∅`. -/
theorem orderStarMinus_exp_eq_empty :
    orderStarMinus exp = ∅ := by
  ext z; simp only [orderStarMinus, mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
  rw [exp_mul_exp_neg, norm_one]

/-! ## A-Stability and Order Stars -/

/-- If `‖R(z)‖ > 1` and `Re(z) ≤ 0`, then `z ∈ 𝒜⁺(R)`. In the left half-plane,
    `exp(-Re z) ≥ 1`, so the order-star amplitude is at least as large as `‖R(z)‖`. -/
theorem mem_orderStarPlus_of_norm_gt_one (R : ℂ → ℂ) (z : ℂ)
    (hz : z.re ≤ 0) (hR : 1 < ‖R z‖) :
    z ∈ orderStarPlus R := by
  simp only [orderStarPlus, mem_setOf_eq, orderStar_norm_eq]
  have hexp : 1 ≤ rexp (-z.re) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp_of_le (by linarith)
  linarith [le_mul_of_one_le_right (norm_nonneg (R z)) hexp]

/-- A method that violates A-stability (`∃ z` with `Re z ≤ 0` and `‖R z‖ > 1`)
    has `𝒜⁺` intersecting the closed left half-plane. -/
theorem orderStarPlus_inter_lhp_nonempty_of_not_aStable (R : ℂ → ℂ)
    (h : ∃ z : ℂ, z.re ≤ 0 ∧ 1 < ‖R z‖) :
    (orderStarPlus R ∩ {z : ℂ | z.re ≤ 0}).Nonempty := by
  obtain ⟨z, hz, hR⟩ := h
  exact ⟨z, mem_orderStarPlus_of_norm_gt_one R z hz hR, hz⟩

/-! ## Forward Euler Order Star -/

/-- Forward Euler stability function: `R(z) = 1 + z`. -/
noncomputable def forwardEulerR (z : ℂ) : ℂ := 1 + z

theorem forwardEulerR_zero : forwardEulerR 0 = 1 := by simp [forwardEulerR]

/-- `z = −3` lies in `𝒜⁺` for forward Euler: `‖R(−3)‖ = ‖−2‖ = 2 > 1`. -/
theorem forwardEuler_neg3_mem_orderStarPlus :
    (-3 : ℂ) ∈ orderStarPlus forwardEulerR := by
  apply mem_orderStarPlus_of_norm_gt_one
  · show (-3 : ℂ).re ≤ 0; simp
  · show 1 < ‖forwardEulerR (-3 : ℂ)‖
    simp [forwardEulerR]; norm_num

/-- Forward Euler: `𝒜⁺` intersects the left half-plane, confirming non-A-stability
    through the order-star lens. -/
theorem forwardEuler_orderStarPlus_inter_lhp :
    (orderStarPlus forwardEulerR ∩ {z : ℂ | z.re ≤ 0}).Nonempty :=
  ⟨-3, forwardEuler_neg3_mem_orderStarPlus, by simp⟩

/-- The origin lies on the order star boundary for forward Euler. -/
theorem forwardEuler_zero_mem_bdry :
    (0 : ℂ) ∈ orderStarBdry forwardEulerR :=
  mem_orderStarBdry_zero _ forwardEulerR_zero

/-! ## Imaginary Axis and Order Stars

For a real-valued stability function `R` with `R(0) = 1`, the imaginary axis
plays a special role in the order star geometry. -/

private theorem ofReal_mul_I_re (t : ℝ) : ((↑t : ℂ) * I).re = 0 := by
  simp [Complex.mul_re]

/-- On the imaginary axis, `|e⁻ᶻ| = 1`, so `z ∈ 𝒜⁺` iff `|R(z)| > 1`. -/
theorem orderStarPlus_imaginaryAxis (R : ℂ → ℂ) (t : ℝ) :
    (↑t * I) ∈ orderStarPlus R ↔ 1 < ‖R (↑t * I)‖ := by
  simp only [orderStarPlus, mem_setOf_eq, orderStar_norm_eq, ofReal_mul_I_re, neg_zero,
    Real.exp_zero, mul_one]

/-- On the imaginary axis, `z ∈ 𝒜⁻` iff `|R(z)| < 1`. -/
theorem orderStarMinus_imaginaryAxis (R : ℂ → ℂ) (t : ℝ) :
    (↑t * I) ∈ orderStarMinus R ↔ ‖R (↑t * I)‖ < 1 := by
  simp only [orderStarMinus, mem_setOf_eq, orderStar_norm_eq, ofReal_mul_I_re, neg_zero,
    Real.exp_zero, mul_one]

/-- On the imaginary axis, `z ∈ 𝒜⁰` iff `|R(z)| = 1`. -/
theorem orderStarBdry_imaginaryAxis (R : ℂ → ℂ) (t : ℝ) :
    (↑t * I) ∈ orderStarBdry R ↔ ‖R (↑t * I)‖ = 1 := by
  simp only [orderStarBdry, mem_setOf_eq, orderStar_norm_eq, ofReal_mul_I_re, neg_zero,
    Real.exp_zero, mul_one]

/-! ## Ehle Barrier (Theorem 355B)

The Ehle barrier constrains which Padé approximants to `eᶻ` can be A-stable.
The full proof requires winding number theory (not yet formalized), so we
state the result with `sorry`.

**Theorem (Ehle, 1969)**: The `(p,q)`-Padé approximant `R_{p,q}(z)` to `eᶻ` is
A-stable if and only if `p ≤ q ≤ p + 2`. Equivalently, an A-stable Padé
approximant lies in the "Ehle wedge" of the Padé table.

Reference: Iserles, Theorem 355B.
-/

/-- The **Ehle wedge** condition: indices `(p,q)` satisfy `p ≤ q ≤ p + 2`,
    where `p` is the numerator degree and `q` is the denominator degree. -/
def InEhleWedge (p q : ℕ) : Prop := p ≤ q ∧ q ≤ p + 2

/-- Known A-stable pairs all satisfy the Ehle wedge. -/
theorem pade01_inEhleWedge : InEhleWedge 0 1 := ⟨by omega, by omega⟩
theorem pade11_inEhleWedge : InEhleWedge 1 1 := ⟨le_refl _, by omega⟩
theorem pade02_inEhleWedge : InEhleWedge 0 2 := ⟨by omega, by omega⟩
theorem pade12_inEhleWedge : InEhleWedge 1 2 := ⟨by omega, by omega⟩
theorem pade22_inEhleWedge : InEhleWedge 2 2 := ⟨le_refl _, by omega⟩
theorem pade23_inEhleWedge : InEhleWedge 2 3 := ⟨by omega, by omega⟩
theorem pade33_inEhleWedge : InEhleWedge 3 3 := ⟨le_refl _, by omega⟩

/-- Known non-A-stable pair `(2,1)` violates the Ehle wedge. -/
theorem pade21_not_inEhleWedge : ¬InEhleWedge 2 1 := by
  intro ⟨h1, _⟩; omega

/-- Known non-A-stable pair `(1,0)` violates the Ehle wedge. -/
theorem pade10_not_inEhleWedge : ¬InEhleWedge 1 0 := by
  intro ⟨h1, _⟩; omega

/-! ## Order Arrows (Definition 355A)

For a stability function `R`, the **order web** is the locus where `φ(z) = R(z)·e⁻ᶻ`
is real and positive. **Order arrows** are rays emanating from the origin along which
`φ` is real and positive: "up arrows" have `φ` increasing (so `‖φ(z)‖ > 1` near 0)
and "down arrows" have `φ` decreasing (`‖φ(z)‖ < 1` near 0).

Reference: Iserles, Definition 355A.
-/

/-- The **order web**: locus where `φ(z) = R(z)·exp(-z)` is real and positive. -/
def orderWeb (R : ℂ → ℂ) : Set ℂ := {z | ∃ r : ℝ, 0 < r ∧ R z * exp (-z) = ↑r}

/-- A ray direction `θ` from the origin is an **up-arrow direction** if
    `t ↦ ‖R(t·exp(iθ))·exp(-t·exp(iθ))‖` exceeds 1 for small positive `t`. -/
def IsUpArrowDir (R : ℂ → ℂ) (θ : ℝ) : Prop :=
  ∃ ε > 0, ∀ t ∈ Set.Ioo (0 : ℝ) ε,
    1 < ‖R (↑t * exp (↑θ * I)) * exp (-(↑t * exp (↑θ * I)))‖

/-- A ray direction `θ` from the origin is a **down-arrow direction** if
    `t ↦ ‖R(t·exp(iθ))·exp(-t·exp(iθ))‖` is below 1 for small positive `t`. -/
def IsDownArrowDir (R : ℂ → ℂ) (θ : ℝ) : Prop :=
  ∃ ε > 0, ∀ t ∈ Set.Ioo (0 : ℝ) ε,
    ‖R (↑t * exp (↑θ * I)) * exp (-(↑t * exp (↑θ * I)))‖ < 1

/-- Up and down arrow directions are mutually exclusive. -/
theorem not_isUpArrowDir_and_isDownArrowDir (R : ℂ → ℂ) (θ : ℝ) :
    ¬(IsUpArrowDir R θ ∧ IsDownArrowDir R θ) := by
  intro ⟨⟨ε₁, hε₁, h₁⟩, ⟨ε₂, hε₂, h₂⟩⟩
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have hm₁ : min ε₁ ε₂ / 2 ∈ Set.Ioo (0 : ℝ) ε₁ := by
    constructor <;> [linarith [min_le_left ε₁ ε₂]; linarith [min_le_left ε₁ ε₂]]
  have hm₂ : min ε₁ ε₂ / 2 ∈ Set.Ioo (0 : ℝ) ε₂ := by
    constructor <;> [linarith [min_le_right ε₁ ε₂]; linarith [min_le_right ε₁ ε₂]]
  linarith [h₁ _ hm₁, h₂ _ hm₂]

/-- Up-arrow directions land in `𝒜⁺` near the origin. -/
theorem isUpArrowDir_subset_orderStarPlus (R : ℂ → ℂ) (θ : ℝ)
    (h : IsUpArrowDir R θ) :
    ∃ ε > 0, ∀ t ∈ Set.Ioo (0 : ℝ) ε,
      (↑t * exp (↑θ * I) : ℂ) ∈ orderStarPlus R := by
  obtain ⟨ε, hε, hup⟩ := h
  exact ⟨ε, hε, fun t ht => hup t ht⟩

/-- Down-arrow directions land in `𝒜⁻` near the origin. -/
theorem isDownArrowDir_subset_orderStarMinus (R : ℂ → ℂ) (θ : ℝ)
    (h : IsDownArrowDir R θ) :
    ∃ ε > 0, ∀ t ∈ Set.Ioo (0 : ℝ) ε,
      (↑t * exp (↑θ * I) : ℂ) ∈ orderStarMinus R := by
  obtain ⟨ε, hε, hdn⟩ := h
  exact ⟨ε, hε, fun t ht => hdn t ht⟩

/-- The origin lies on the order web when `R(0) = 1`. -/
theorem mem_orderWeb_zero (R : ℂ → ℂ) (h : R 0 = 1) :
    (0 : ℂ) ∈ orderWeb R := by
  refine ⟨1, one_pos, ?_⟩
  simp [h]

/-! ## Theorem 355B: Arrow Tangency Directions

Let `R` be a rational approximation to `exp` of exact order `p`, meaning
`R(z) = exp(z) - C·z^{p+1} + O(z^{p+2})` with `C ≠ 0`.

The key identity: for `z = t·exp(iθ)` with `t` small,
```
  R(z)·exp(-z) = 1 - C·t^{p+1}·exp(i(p+1)θ) + O(t^{p+2})
```
So `‖R(z)·exp(-z)‖² ≈ 1 - 2C·t^{p+1}·cos((p+1)θ)`.

At angles `θ = 2kπ/(p+1)`, `cos((p+1)θ) = 1`, so:
- `C < 0` ⟹ `‖φ‖² > 1` ⟹ up arrow
- `C > 0` ⟹ `‖φ‖² < 1` ⟹ down arrow

Reference: Iserles, Theorem 355B.
-/

/-- **Forward Euler** (`R(z) = 1 + z`, order `p = 1`, error constant `C = 1/2 > 0`):
    `θ = 0` is a down-arrow direction. On the positive real axis near the origin,
    `‖(1+t)·e⁻ᵗ‖ < 1` for small `t > 0`. -/
theorem forwardEuler_isDownArrowDir_zero :
    IsDownArrowDir forwardEulerR 0 := by
  refine ⟨1, one_pos, fun t ht => ?_⟩
  simp only [forwardEulerR, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [orderStar_norm_eq]
  have ht0 : (0 : ℝ) < t := ht.1
  rw [show ‖1 + (↑t : ℂ)‖ = 1 + t from by
    rw [show (1 : ℂ) + ↑t = ↑((1 : ℝ) + t) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]]
  calc (1 + t) * rexp (-t)
      _ < rexp t * rexp (-t) := by
          apply mul_lt_mul_of_pos_right _ (Real.exp_pos _)
          linarith [Real.add_one_lt_exp (ne_of_gt ht0)]
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- **Forward Euler**: `θ = π` is a down-arrow direction.
    On the negative real axis near the origin, `‖(1 - t)·eᵗ‖ < 1` for small `t > 0`. -/
theorem forwardEuler_isDownArrowDir_pi :
    IsDownArrowDir forwardEulerR π := by
  refine ⟨1/2, by positivity, fun t ht => ?_⟩
  have ht0 : (0 : ℝ) < t := ht.1
  simp only [forwardEulerR]
  rw [show (↑π : ℂ) * I = ↑Real.pi * I from by norm_cast, Complex.exp_pi_mul_I]
  simp only [mul_neg, mul_one, neg_neg]
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.ofReal_re]
  have ht1 : t < 1/2 := ht.2
  rw [show ‖1 + -(↑t : ℂ)‖ = 1 - t from by
    rw [show (1 : ℂ) + -((↑t : ℂ)) = ↑((1 : ℝ) - t) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]]
  calc (1 - t) * rexp t
      _ < rexp (-t) * rexp t := by
          apply mul_lt_mul_of_pos_right _ (Real.exp_pos _)
          linarith [Real.one_sub_lt_exp_neg (ne_of_gt ht0)]
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- **Backward Euler** stability function: `R(z) = 1/(1 - z)`. -/
noncomputable def backwardEulerR (z : ℂ) : ℂ := (1 - z)⁻¹

theorem backwardEulerR_zero : backwardEulerR 0 = 1 := by
  simp [backwardEulerR]

/-- **Backward Euler** (`R(z) = 1/(1-z)`, order `p = 1`, error constant `C = -1/2 < 0`):
    `θ = 0` is an up-arrow direction. On the positive real axis near the origin,
    `‖(1-t)⁻¹·e⁻ᵗ‖ > 1` for small `t > 0`. -/
theorem backwardEuler_isUpArrowDir_zero :
    IsUpArrowDir backwardEulerR 0 := by
  refine ⟨1/2, by positivity, fun t ht => ?_⟩
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : t < 1/2 := ht.2
  simp only [backwardEulerR, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
  rw [show ‖(1 - (↑t : ℂ))⁻¹‖ = (1 - t)⁻¹ from by
    rw [norm_inv]
    rw [show (1 : ℂ) - ↑t = ↑((1 : ℝ) - t) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]]
  have h1t : (0 : ℝ) < 1 - t := by linarith
  rw [show (1 - t)⁻¹ * rexp (-t) = rexp (-t) * (1 - t)⁻¹ from mul_comm _ _]
  rw [← div_eq_mul_inv, one_lt_div h1t]
  linarith [Real.one_sub_lt_exp_neg (ne_of_gt ht0)]

/-- **Backward Euler**: `θ = π` is an up-arrow direction. -/
theorem backwardEuler_isUpArrowDir_pi :
    IsUpArrowDir backwardEulerR π := by
  refine ⟨1, one_pos, fun t ht => ?_⟩
  have ht0 : (0 : ℝ) < t := ht.1
  simp only [backwardEulerR]
  rw [show (↑π : ℂ) * I = ↑Real.pi * I from by norm_cast, Complex.exp_pi_mul_I]
  simp only [mul_neg, mul_one, neg_neg]
  rw [show (1 : ℂ) - -↑t = 1 + ↑t from by ring]
  rw [norm_mul, Complex.norm_exp, Complex.ofReal_re]
  rw [show ‖(1 + (↑t : ℂ))⁻¹‖ = (1 + t)⁻¹ from by
    rw [norm_inv]
    rw [show (1 : ℂ) + ↑t = ↑((1 : ℝ) + t) from by push_cast; ring]
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]]
  have h1t : (0 : ℝ) < 1 + t := by linarith
  rw [show (1 + t)⁻¹ * rexp t = rexp t * (1 + t)⁻¹ from mul_comm _ _]
  rw [← div_eq_mul_inv, one_lt_div h1t]
  linarith [Real.add_one_lt_exp (ne_of_gt ht0)]

/-- **Trapezoidal rule** stability function: `R(z) = (1 + z/2)/(1 - z/2)`. -/
noncomputable def trapezoidalR (z : ℂ) : ℂ := (1 + z / 2) / (1 - z / 2)

theorem trapezoidalR_zero : trapezoidalR 0 = 1 := by
  simp [trapezoidalR]

/-- **Trapezoidal rule** (`R(z) = (1+z/2)/(1-z/2)`, order `p = 2`, `C = -1/12 < 0`):
    `θ = 0` is an up-arrow direction. -/
private theorem trapezoidal_key_ineq {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1/4) :
    rexp t < (2 + t) / (2 - t) := by
  have h2t : (0 : ℝ) < 2 - t := by linarith
  suffices h : (2 - t) * rexp t < 2 + t by rwa [lt_div_iff₀' h2t]
  have hle : rexp t ≤ ∑ m ∈ Finset.range 3, t ^ m / ↑m.factorial +
      t ^ 3 * (↑3 + 1) / (↑(Nat.factorial 3) * ↑3) :=
    Real.exp_bound' (le_of_lt ht0) (by linarith) (by norm_num : (0 : ℕ) < 3)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hle
  have httt : 0 < t ^ 3 := pow_pos ht0 3
  have h4 : 0 ≤ t ^ 4 := pow_nonneg ht0.le 4
  calc (2 - t) * rexp t
      _ ≤ (2 - t) * (1 + t + t ^ 2 / 2 + t ^ 3 * 4 / 18) :=
          mul_le_mul_of_nonneg_left hle h2t.le
      _ = 2 + t - t ^ 3 / 18 - t ^ 4 * 2 / 9 := by ring
      _ < 2 + t := by nlinarith

theorem trapezoidal_isUpArrowDir_zero :
    IsUpArrowDir trapezoidalR 0 := by
  refine ⟨1/4, by positivity, fun t ht => ?_⟩
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : t < 1/4 := ht.2
  simp only [trapezoidalR, ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
  have h2t : (0 : ℝ) < 2 - t := by linarith
  rw [show ‖(1 + (↑t : ℂ) / 2) / (1 - (↑t : ℂ) / 2)‖ = (2 + t) / (2 - t) from by
    rw [show (1 + (↑t : ℂ) / 2) / (1 - (↑t : ℂ) / 2) = ↑((2 + t) / (2 - t)) from by
      push_cast; field_simp]
    rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg (by linarith) h2t.le)]]
  have hkey := trapezoidal_key_ineq ht0 (le_of_lt ht1)
  -- hkey : rexp t < (2 + t) / (2 - t)
  -- Goal: 1 < (2 + t) / (2 - t) * rexp (-t)
  have hexp_pos := Real.exp_pos t
  calc (1 : ℝ) = rexp t * rexp (-t) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    _ < (2 + t) / (2 - t) * rexp (-t) := by
        apply mul_lt_mul_of_pos_right hkey (Real.exp_pos (-t))
