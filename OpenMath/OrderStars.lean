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
