import OpenMath.RungeKutta

/-!
# Collocation Methods and Simplifying Assumptions

## Section 2.3 of Iserles: Collocation Methods

A collocation method with s distinct nodes c₁,...,cₛ ∈ [0,1] defines an s-stage
Runge–Kutta method with coefficients given by integrals of Lagrange basis polynomials:
  aᵢⱼ = ∫₀^{cᵢ} ℓⱼ(τ) dτ,  bⱼ = ∫₀¹ ℓⱼ(τ) dτ

The resulting RK methods are characterized by the **simplifying assumptions**:

- **B(p)**: ∑ bᵢ cᵢ^{k-1} = 1/k  for k = 1,...,p
  (the quadrature rule integrates polynomials of degree ≤ p-1 exactly)

- **C(q)**: ∑ⱼ aᵢⱼ cⱼ^{k-1} = cᵢ^k/k  for k = 1,...,q  and all i
  (a collocation method with s nodes satisfies C(s))

- **D(r)**: ∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = bⱼ(1 - cⱼ^k)/k  for k = 1,...,r  and all j

Key results:
- C(1) is exactly the row-sum condition
- B(1) is exactly the weight-sum condition (order 1)
- B(p) ∧ C(q) implies order conditions through specific orders

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Section 2.3 and Chapter 4.
-/

open Finset Real

namespace ButcherTableau

variable {s : ℕ}

/-! ## Simplifying Assumptions -/

/-- **Simplifying assumption B(p)**: the quadrature rule (b, c) integrates polynomials
of degree ≤ p-1 exactly. Equivalently, ∑ bᵢ cᵢ^{k-1} = 1/k for k = 1,...,p.
Reference: Iserles, Section 2.3 / Hairer–Nørsett–Wanner IV.5. -/
def SatisfiesB (t : ButcherTableau s) (p : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ p → ∑ i : Fin s, t.b i * t.c i ^ (k - 1) = 1 / (k : ℝ)

/-- **Simplifying assumption C(q)**: ∑ⱼ aᵢⱼ cⱼ^{k-1} = cᵢ^k/k for k = 1,...,q.
A collocation method with s distinct nodes satisfies C(s).
Reference: Iserles, Theorem 2.5. -/
def SatisfiesC (t : ButcherTableau s) (q : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ q →
    ∀ i : Fin s, ∑ j : Fin s, t.A i j * t.c j ^ (k - 1) = t.c i ^ k / (k : ℝ)

/-- **Simplifying assumption D(r)**: ∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = bⱼ(1 - cⱼ^k)/k
for k = 1,...,r and all j.
Reference: Hairer–Nørsett–Wanner, IV.5. -/
def SatisfiesD (t : ButcherTableau s) (r : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ r →
    ∀ j : Fin s, ∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j =
      t.b j / (k : ℝ) * (1 - t.c j ^ k)

/-! ## Monotonicity: B(p) implies B(p') for p' ≤ p, etc. -/

theorem SatisfiesB.mono {t : ButcherTableau s} {p p' : ℕ} (h : t.SatisfiesB p) (hp : p' ≤ p) :
    t.SatisfiesB p' :=
  fun k hk1 hk2 => h k hk1 (le_trans hk2 hp)

theorem SatisfiesC.mono {t : ButcherTableau s} {q q' : ℕ} (h : t.SatisfiesC q) (hq : q' ≤ q) :
    t.SatisfiesC q' :=
  fun k hk1 hk2 i => h k hk1 (le_trans hk2 hq) i

/-! ## Equivalences with Existing Definitions -/

/-- C(1) is equivalent to the row-sum condition: cᵢ = ∑ⱼ aᵢⱼ. -/
theorem satisfiesC_one_iff (t : ButcherTableau s) :
    t.SatisfiesC 1 ↔ t.IsRowSumConsistent := by
  constructor
  · intro hC i
    have h := hC 1 le_rfl le_rfl i
    simp at h
    linarith
  · intro hRS k hk1 hk2 i
    have hk : k = 1 := le_antisymm hk2 hk1
    subst hk; simp
    linarith [hRS i]

/-- B(1) is equivalent to the first-order condition: ∑ bᵢ = 1. -/
theorem satisfiesB_one_iff (t : ButcherTableau s) :
    t.SatisfiesB 1 ↔ t.order1 := by
  constructor
  · intro hB
    have h := hB 1 le_rfl le_rfl
    simp at h
    exact h
  · intro h1 k hk1 hk2
    have hk : k = 1 := le_antisymm hk2 hk1
    subst hk; simp
    exact h1

/-- B(1) ∧ C(1) is equivalent to consistency. -/
theorem satisfiesB1_C1_iff_consistent (t : ButcherTableau s) :
    t.SatisfiesB 1 ∧ t.SatisfiesC 1 ↔ t.IsConsistent := by
  rw [satisfiesB_one_iff, satisfiesC_one_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

/-! ## Order from Simplifying Assumptions

The simplifying assumptions B, C, D are powerful tools for verifying high-order
conditions without checking each tree individually.

Key implications:
- B(1) → order ≥ 1
- B(2) ∧ C(1) → order ≥ 2
- B(3) ∧ C(2) → order ≥ 3
- B(4) ∧ C(3) → order ≥ 4

Reference: Iserles, Theorem 2.6 / Hairer–Nørsett–Wanner, Theorem IV.5.1.
-/

/-- B(1) implies order at least 1. -/
theorem HasOrderGe1_of_B1 (t : ButcherTableau s) (hB : t.SatisfiesB 1) :
    t.HasOrderGe1 :=
  (satisfiesB_one_iff t).mp hB

/-- B(2) ∧ C(1) implies order at least 2.
The proof of order2 uses B(2) directly: ∑ bᵢ cᵢ = 1/2. -/
theorem HasOrderGe2_of_B2_C1 (t : ButcherTableau s) (hB : t.SatisfiesB 2)
    (_hC : t.SatisfiesC 1) : t.HasOrderGe2 := by
  constructor
  · -- order1 from B(1) ⊆ B(2)
    exact (satisfiesB_one_iff t).mp (hB.mono (by omega))
  · -- order2: ∑ bᵢ cᵢ = 1/2, directly from B(2) at k=2
    have h := hB 2 (by omega) le_rfl
    simp [order2] at h ⊢
    convert h using 1

/-- **B(3) ∧ C(2) → order ≥ 3.**

The third-order condition (b), ∑ᵢⱼ bᵢ aᵢⱼ cⱼ = 1/6, follows from:
- C(2): ∑ⱼ aᵢⱼ cⱼ = cᵢ²/2
- B(3): ∑ᵢ bᵢ cᵢ² = 1/3
- Combining: ∑ᵢ bᵢ · (cᵢ²/2) = (1/2) · (1/3) = 1/6.

Reference: Iserles, proof of Theorem 2.6. -/
theorem HasOrderGe3_of_B3_C2 (t : ButcherTableau s) (hB : t.SatisfiesB 3)
    (hC : t.SatisfiesC 2) : t.HasOrderGe3 := by
  have hOrd2 := HasOrderGe2_of_B2_C1 t (hB.mono (by omega)) (hC.mono (by omega))
  refine ⟨hOrd2.1, hOrd2.2, ?_, ?_⟩
  · -- order3a: ∑ bᵢ cᵢ² = 1/3, from B(3) at k=3
    have h := hB 3 (by omega) le_rfl
    simp [order3a] at h ⊢
    convert h using 1
  · -- order3b: ∑ᵢⱼ bᵢ aᵢⱼ cⱼ = 1/6
    -- Use C(2): ∑ⱼ aᵢⱼ cⱼ = cᵢ²/2
    have hC2 : ∀ i : Fin s, ∑ j, t.A i j * t.c j = t.c i ^ 2 / 2 := by
      intro i
      have h := hC 2 (by omega) le_rfl i
      simpa using h
    -- Use B(3): ∑ᵢ bᵢ cᵢ² = 1/3
    have hB3 : ∑ i : Fin s, t.b i * t.c i ^ 2 = 1 / 3 := by
      have h := hB 3 (by omega) le_rfl
      simpa using h
    simp only [order3b]
    -- Rewrite: ∑ i, ∑ j, bᵢ * aᵢⱼ * cⱼ = ∑ i, bᵢ * (∑ j, aᵢⱼ * cⱼ) = ∑ i, bᵢ * cᵢ²/2
    have step1 : ∀ i : Fin s,
        ∑ j, t.b i * t.A i j * t.c j = t.b i * (∑ j, t.A i j * t.c j) := by
      intro i
      rw [Finset.mul_sum]
      congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step1 i, hC2 i]
    -- Now have ∑ i, bᵢ * (cᵢ²/2) = (1/2) * ∑ bᵢ cᵢ² = 1/6
    have step2 : ∑ i : Fin s, t.b i * (t.c i ^ 2 / 2) =
        (1 / 2) * ∑ i : Fin s, t.b i * t.c i ^ 2 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [step2, hB3]; ring

/-- **B(4) ∧ C(3) → order ≥ 4.**

All four fourth-order conditions follow from B(4) and C(3):
- (4a) ∑ bᵢ cᵢ³ = 1/4 : direct from B(4)
- (4b) ∑ bᵢ cᵢ (∑ aᵢⱼ cⱼ) = 1/8 : C(2) gives inner sum = cᵢ²/2
- (4c) ∑ bᵢ (∑ aᵢⱼ cⱼ²) = 1/12 : C(3) gives inner sum = cᵢ³/3
- (4d) ∑ bᵢ (∑ aᵢⱼ (∑ aⱼₖ cₖ)) = 1/24 : C(2) twice + B(4)

Reference: Iserles, Theorem 2.6. -/
theorem HasOrderGe4_of_B4_C3 (t : ButcherTableau s) (hB : t.SatisfiesB 4)
    (hC : t.SatisfiesC 3) : t.HasOrderGe4 := by
  have hOrd3 := HasOrderGe3_of_B3_C2 t (hB.mono (by omega)) (hC.mono (by omega))
  refine ⟨hOrd3.1, hOrd3.2.1, hOrd3.2.2.1, hOrd3.2.2.2, ?_, ?_, ?_, ?_⟩
  · -- order4a: ∑ bᵢ cᵢ³ = 1/4, from B(4) at k=4
    have h := hB 4 (by omega) le_rfl
    simp [order4a] at h ⊢
    convert h using 1
  · -- order4b: ∑ bᵢ cᵢ (∑ aᵢⱼ cⱼ) = 1/8
    have hC2 : ∀ i : Fin s, ∑ j, t.A i j * t.c j = t.c i ^ 2 / 2 := by
      intro i; have h := hC 2 (by omega) (by omega) i; simpa using h
    have hB4 : ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4 := by
      have h := hB 4 (by omega) le_rfl; simpa using h
    simp only [order4b]
    have step : ∀ i : Fin s,
        t.b i * t.c i * ∑ j, t.A i j * t.c j = t.b i * t.c i * (t.c i ^ 2 / 2) := by
      intro i; rw [hC2 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * t.c i * (t.c i ^ 2 / 2) =
        (1 / 2) * ∑ i : Fin s, t.b i * t.c i ^ 3 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB4]; ring
  · -- order4c: ∑ bᵢ (∑ aᵢⱼ cⱼ²) = 1/12
    have hC3 : ∀ i : Fin s, ∑ j, t.A i j * t.c j ^ 2 = t.c i ^ 3 / 3 := by
      intro i; have h := hC 3 (by omega) le_rfl i; simpa using h
    have hB4 : ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4 := by
      have h := hB 4 (by omega) le_rfl; simpa using h
    simp only [order4c]
    have step : ∀ i : Fin s,
        ∑ j, t.b i * t.A i j * t.c j ^ 2 = t.b i * (∑ j, t.A i j * t.c j ^ 2) := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step i, hC3 i]
    have : ∑ i : Fin s, t.b i * (t.c i ^ 3 / 3) =
        (1 / 3) * ∑ i : Fin s, t.b i * t.c i ^ 3 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB4]; ring
  · -- order4d: ∑ᵢⱼₖ bᵢ aᵢⱼ aⱼₖ cₖ = 1/24
    -- C(2): ∑ₖ aⱼₖ cₖ = cⱼ²/2
    have hC2 : ∀ j : Fin s, ∑ k, t.A j k * t.c k = t.c j ^ 2 / 2 := by
      intro j; have h := hC 2 (by omega) (by omega) j; simpa using h
    -- C(3): ∑ⱼ aᵢⱼ cⱼ² = cᵢ³/3
    have hC3 : ∀ i : Fin s, ∑ j, t.A i j * t.c j ^ 2 = t.c i ^ 3 / 3 := by
      intro i; have h := hC 3 (by omega) le_rfl i; simpa using h
    have hB4 : ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4 := by
      have h := hB 4 (by omega) le_rfl; simpa using h
    simp only [order4d]
    -- Step 1: collapse innermost sum using C(2)
    have step1 : ∀ i j : Fin s,
        ∑ k, t.b i * t.A i j * t.A j k * t.c k =
        t.b i * t.A i j * (∑ k, t.A j k * t.c k) := by
      intro i j; rw [Finset.mul_sum]; congr 1; ext k; ring
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step1 i j, hC2 j]
    -- Step 2: now have ∑ᵢⱼ bᵢ aᵢⱼ (cⱼ²/2); factor and use C(3)
    have step2 : ∀ i : Fin s,
        ∑ j, t.b i * t.A i j * (t.c j ^ 2 / 2) =
        (1 / 2) * (t.b i * ∑ j, t.A i j * t.c j ^ 2) := by
      intro i
      rw [Finset.sum_congr rfl (fun j _ => show t.b i * t.A i j * (t.c j ^ 2 / 2) =
        (1 / 2 * t.b i) * (t.A i j * t.c j ^ 2) from by ring), ← Finset.mul_sum, mul_assoc]
    conv_lhs => arg 2; ext i; rw [step2 i, hC3 i]
    -- Step 3: ∑ᵢ (1/2) * bᵢ * cᵢ³/3 = (1/6) * ∑ bᵢ cᵢ³ = 1/24
    have : ∑ i : Fin s, 1 / 2 * (t.b i * (t.c i ^ 3 / 3)) =
        (1 / 6) * ∑ i : Fin s, t.b i * t.c i ^ 3 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB4]; ring

/-! ## Verification for Standard Methods -/

section BackwardEuler

/-- Backward Euler satisfies B(1): the 1-point quadrature at c=1 integrates constants. -/
theorem rkImplicitEuler_B1 : rkImplicitEuler.SatisfiesB 1 := by
  intro k hk1 hk2
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; simp [rkImplicitEuler]

/-- Backward Euler satisfies C(1): row-sum condition. -/
theorem rkImplicitEuler_C1 : rkImplicitEuler.SatisfiesC 1 := by
  rw [satisfiesC_one_iff]
  exact rkImplicitEuler_consistent.row_sum

end BackwardEuler

section ImplicitMidpoint

/-- Implicit midpoint satisfies B(2): the 1-point midpoint rule integrates linear functions. -/
theorem rkImplicitMidpoint_B2 : rkImplicitMidpoint.SatisfiesB 2 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkImplicitMidpoint]

/-- Implicit midpoint satisfies C(1). -/
theorem rkImplicitMidpoint_C1 : rkImplicitMidpoint.SatisfiesC 1 := by
  rw [satisfiesC_one_iff]
  exact rkImplicitMidpoint_consistent.row_sum

/-- Implicit midpoint has order ≥ 2, derived from B(2) ∧ C(1). -/
theorem rkImplicitMidpoint_order2' : rkImplicitMidpoint.HasOrderGe2 :=
  HasOrderGe2_of_B2_C1 _ rkImplicitMidpoint_B2 rkImplicitMidpoint_C1

end ImplicitMidpoint

section GaussLegendre2

private theorem sqrt3_sq' : Real.sqrt 3 ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)

/-- GL2 satisfies B(4): the 2-point Gauss–Legendre quadrature integrates polynomials
of degree ≤ 3 exactly (2s-1 = 3 for s=2). -/
theorem rkGaussLegendre2_B4 : rkGaussLegendre2.SatisfiesB 4 := by
  intro k hk1 hk2
  interval_cases k <;> simp [rkGaussLegendre2, Fin.sum_univ_two] <;> nlinarith [sqrt3_sq']

/-- GL2 satisfies C(2): ∑ⱼ aᵢⱼ = cᵢ and ∑ⱼ aᵢⱼ cⱼ = cᵢ²/2. -/
theorem rkGaussLegendre2_C2 : rkGaussLegendre2.SatisfiesC 2 := by
  intro k hk1 hk2 i
  interval_cases k <;> fin_cases i <;>
    simp [rkGaussLegendre2, Fin.sum_univ_two] <;> nlinarith [sqrt3_sq']

/-- GL2 has order ≥ 3, derived from B(3) ∧ C(2).
(GL2 actually has order 4, but B(4) ∧ C(3) would require C(3) which needs s ≥ 3.) -/
theorem rkGaussLegendre2_order3' : rkGaussLegendre2.HasOrderGe3 :=
  HasOrderGe3_of_B3_C2 _ (rkGaussLegendre2_B4.mono (by omega)) rkGaussLegendre2_C2

end GaussLegendre2

end ButcherTableau
