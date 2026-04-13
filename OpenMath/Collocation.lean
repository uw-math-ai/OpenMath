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

theorem SatisfiesD.mono {t : ButcherTableau s} {r r' : ℕ} (h : t.SatisfiesD r) (hr : r' ≤ r) :
    t.SatisfiesD r' :=
  fun k hk1 hk2 j => h k hk1 (le_trans hk2 hr) j

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

/-- **B(4) ∧ C(2) ∧ D(1) → order ≥ 4.**

This alternative to `HasOrderGe4_of_B4_C3` uses D(1) instead of C(3).
The key insights:
- order4c: swap sums, apply D(1) to get ∑ bⱼ cⱼ²(1-cⱼ) = 1/3 - 1/4 = 1/12
- order4d: use C(2) first, then reduce to order4c

This is needed for Lobatto IIIC methods which satisfy C(2) and D(1) but not C(3).
Reference: Hairer–Nørsett–Wanner, Theorem IV.5.1. -/
theorem HasOrderGe4_of_B4_C2_D1 (t : ButcherTableau s) (hB : t.SatisfiesB 4)
    (hC : t.SatisfiesC 2) (hD : t.SatisfiesD 1) : t.HasOrderGe4 := by
  have hOrd3 := HasOrderGe3_of_B3_C2 t (hB.mono (by omega)) hC
  refine ⟨hOrd3.1, hOrd3.2.1, hOrd3.2.2.1, hOrd3.2.2.2, ?_, ?_, ?_, ?_⟩
  · -- order4a: ∑ bᵢ cᵢ³ = 1/4, from B(4) at k=4
    have h := hB 4 (by omega) le_rfl
    simp [order4a] at h ⊢
    convert h using 1
  · -- order4b: ∑ bᵢ cᵢ (∑ aᵢⱼ cⱼ) = 1/8, using C(2)
    have hC2 : ∀ i : Fin s, ∑ j, t.A i j * t.c j = t.c i ^ 2 / 2 := by
      intro i; have h := hC 2 (by omega) le_rfl i; simpa using h
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
  · -- order4c: ∑ bᵢ aᵢⱼ cⱼ² = 1/12, using D(1)
    -- Swap sums: ∑ᵢⱼ bᵢ aᵢⱼ cⱼ² = ∑ⱼ cⱼ² (∑ᵢ bᵢ aᵢⱼ) = ∑ⱼ cⱼ² bⱼ(1-cⱼ)
    have hD1 : ∀ j : Fin s, ∑ i, t.b i * t.A i j = t.b j * (1 - t.c j) := by
      intro j
      have h := hD 1 (by omega) le_rfl j
      simpa using h
    have hB3 : ∑ i : Fin s, t.b i * t.c i ^ 2 = 1 / 3 := by
      have h := hB 3 (by omega) (by omega); simpa using h
    have hB4 : ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4 := by
      have h := hB 4 (by omega) le_rfl; simpa using h
    simp only [order4c]
    -- Swap sums: ∑ᵢ ∑ⱼ bᵢ aᵢⱼ cⱼ² = ∑ⱼ cⱼ² ∑ᵢ bᵢ aᵢⱼ
    rw [Finset.sum_comm]
    have step : ∀ j : Fin s,
        ∑ i, t.b i * t.A i j * t.c j ^ 2 = t.c j ^ 2 * ∑ i, t.b i * t.A i j := by
      intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
    conv_lhs => arg 2; ext j; rw [step j, hD1 j]
    -- Now ∑ⱼ cⱼ² · bⱼ(1-cⱼ) = ∑ bⱼ cⱼ² - ∑ bⱼ cⱼ³ = 1/3 - 1/4 = 1/12
    have : ∑ j : Fin s, t.c j ^ 2 * (t.b j * (1 - t.c j)) =
        ∑ j, t.b j * t.c j ^ 2 - ∑ j, t.b j * t.c j ^ 3 := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
    rw [this, hB3, hB4]; ring
  · -- order4d: ∑ᵢⱼₖ bᵢ aᵢⱼ aⱼₖ cₖ = 1/24, using C(2) then order4c
    -- Strategy: C(2) collapses the inner sum, then we get (1/2) · order4c = 1/24
    have hC2 : ∀ j : Fin s, ∑ k, t.A j k * t.c k = t.c j ^ 2 / 2 := by
      intro j; have h := hC 2 (by omega) le_rfl j; simpa using h
    -- First show order4c = 1/12 using D(1)
    have hD1' : ∀ j : Fin s, ∑ i, t.b i * t.A i j = t.b j * (1 - t.c j) := by
      intro j; have h := hD 1 (by omega) le_rfl j; simpa using h
    have hB3' : ∑ i : Fin s, t.b i * t.c i ^ 2 = 1 / 3 := by
      have h := hB 3 (by omega) (by omega); simpa using h
    have hB4' : ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4 := by
      have h := hB 4 (by omega) le_rfl; simpa using h
    have h4c : ∑ i : Fin s, ∑ j, t.b i * t.A i j * t.c j ^ 2 = 1 / 12 := by
      rw [Finset.sum_comm]
      have : ∀ j : Fin s,
          ∑ i, t.b i * t.A i j * t.c j ^ 2 = t.c j ^ 2 * ∑ i, t.b i * t.A i j := by
        intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
      simp_rw [this]
      conv_lhs => arg 2; ext j; rw [hD1' j]
      have : ∑ j : Fin s, t.c j ^ 2 * (t.b j * (1 - t.c j)) =
          ∑ j, t.b j * t.c j ^ 2 - ∑ j, t.b j * t.c j ^ 3 := by
        rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
      rw [this, hB3', hB4']; ring
    simp only [order4d]
    -- Step 1: collapse innermost sum using C(2)
    have step1 : ∀ i j : Fin s,
        ∑ k, t.b i * t.A i j * t.A j k * t.c k =
        t.b i * t.A i j * (∑ k, t.A j k * t.c k) := by
      intro i j; rw [Finset.mul_sum]; congr 1; ext k; ring
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step1 i j, hC2 j]
    -- Step 2: factor out 1/2
    have step2 : ∀ i : Fin s,
        ∑ j, t.b i * t.A i j * (t.c j ^ 2 / 2) =
        (1 / 2) * ∑ j, t.b i * t.A i j * t.c j ^ 2 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step2 i]
    rw [← Finset.mul_sum, h4c]; ring

theorem SatisfiesD.mono {t : ButcherTableau s} {r r' : ℕ} (h : t.SatisfiesD r) (hr : r' ≤ r) :
    t.SatisfiesD r' :=
  fun k hk1 hk2 j => h k hk1 (le_trans hk2 hr) j

/-- **B(4) ∧ C(1) ∧ D(2) → order ≥ 4.**

This alternative uses D(2) to compensate for only having C(1) (row-sum).
The key insights:
- order3b: swap sums, apply D(1) to get ∑ bⱼcⱼ(1-cⱼ) = 1/2 - 1/3 = 1/6
- order4b: swap sums, apply D(2) to get ∑ bⱼcⱼ(1-cⱼ²)/2 = (1/2-1/4)/2 = 1/8
- order4c: swap sums, apply D(1) to get ∑ bⱼcⱼ²(1-cⱼ) = 1/3 - 1/4 = 1/12
- order4d: apply D(1) then D(2) to reduce to B-sums

This is needed for Lobatto IIIB 3-stage which satisfies C(1) and D(2) but not C(2).
Reference: Hairer–Nørsett–Wanner, Theorem IV.5.1. -/
theorem HasOrderGe4_of_B4_C1_D2 (t : ButcherTableau s) (hB : t.SatisfiesB 4)
    (hC : t.SatisfiesC 1) (hD : t.SatisfiesD 2) : t.HasOrderGe4 := by
  -- Extract D(1) from D(2)
  have hD1 : ∀ j : Fin s, ∑ i, t.b i * t.A i j = t.b j * (1 - t.c j) := by
    intro j; have h := hD 1 (by omega) (by omega) j; simpa using h
  have hD2 : ∀ j : Fin s, ∑ i, t.b i * t.c i * t.A i j = t.b j / 2 * (1 - t.c j ^ 2) := by
    intro j; have h := hD 2 (by omega) le_rfl j; simpa using h
  -- Extract B-sums
  have hB2 : ∑ i : Fin s, t.b i * t.c i = 1 / 2 := by
    have h := hB 2 (by omega) (by omega); simpa using h
  have hB3 : ∑ i : Fin s, t.b i * t.c i ^ 2 = 1 / 3 := by
    have h := hB 3 (by omega) (by omega); simpa using h
  have hB4 : ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4 := by
    have h := hB 4 (by omega) le_rfl; simpa using h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- order1
    have h := hB 1 (by omega) (by omega); rw [order1]; simpa using h
  · -- order2
    simp only [order2]; linarith [hB2]
  · -- order3a: ∑ bᵢ cᵢ² = 1/3
    simp only [order3a]; linarith [hB3]
  · -- order3b: ∑ᵢⱼ bᵢ aᵢⱼ cⱼ = 1/6, using D(1)
    simp only [order3b]
    rw [Finset.sum_comm]
    have step : ∀ j : Fin s,
        ∑ i, t.b i * t.A i j * t.c j = t.c j * ∑ i, t.b i * t.A i j := by
      intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
    conv_lhs => arg 2; ext j; rw [step j, hD1 j]
    have pw : ∀ j : Fin s, t.c j * (t.b j * (1 - t.c j)) =
        t.b j * t.c j - t.b j * t.c j ^ 2 := by intro j; ring
    simp_rw [pw, Finset.sum_sub_distrib, hB2, hB3]; ring
  · -- order4a: ∑ bᵢ cᵢ³ = 1/4
    simp only [order4a]; linarith [hB4]
  · -- order4b: ∑ bᵢ cᵢ (∑ aᵢⱼ cⱼ) = 1/8, using D(2) (swap sums)
    simp only [order4b]
    -- Expand product into sum, swap, factor, apply D(2)
    have expand : ∀ i : Fin s, t.b i * t.c i * ∑ j, t.A i j * t.c j =
        ∑ j, t.b i * t.c i * t.A i j * t.c j := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [expand i]
    rw [Finset.sum_comm]
    have factor : ∀ j : Fin s, ∑ i, t.b i * t.c i * t.A i j * t.c j =
        t.c j * ∑ i, t.b i * t.c i * t.A i j := by
      intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
    conv_lhs => arg 2; ext j; rw [factor j, hD2 j]
    -- Close using pointwise ring + B-sums
    have pw : ∀ j : Fin s, t.c j * (t.b j / 2 * (1 - t.c j ^ 2)) =
        1 / 2 * (t.b j * t.c j) - 1 / 2 * (t.b j * t.c j ^ 3) := by intro j; ring
    simp_rw [pw, Finset.sum_sub_distrib, ← Finset.mul_sum, hB2, hB4]; ring
  · -- order4c: ∑ bᵢ aᵢⱼ cⱼ² = 1/12, using D(1)
    simp only [order4c]
    rw [Finset.sum_comm]
    have step : ∀ j : Fin s,
        ∑ i, t.b i * t.A i j * t.c j ^ 2 = t.c j ^ 2 * ∑ i, t.b i * t.A i j := by
      intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
    conv_lhs => arg 2; ext j; rw [step j, hD1 j]
    have pw : ∀ j : Fin s, t.c j ^ 2 * (t.b j * (1 - t.c j)) =
        t.b j * t.c j ^ 2 - t.b j * t.c j ^ 3 := by intro j; ring
    simp_rw [pw, Finset.sum_sub_distrib, hB3, hB4]; ring
  · -- order4d: ∑ᵢⱼₖ bᵢ aᵢⱼ aⱼₖ cₖ = 1/24, using D(1) + D(2)
    simp only [order4d]
    -- Step 1: collapse inner sum, swap, factor, apply D(1)
    have step1 : ∀ i j : Fin s,
        ∑ k, t.b i * t.A i j * t.A j k * t.c k =
        t.b i * t.A i j * ∑ k, t.A j k * t.c k := by
      intro i j; rw [Finset.mul_sum]; congr 1; ext k; ring
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step1 i j]
    rw [Finset.sum_comm]
    have step2 : ∀ j : Fin s, ∑ i, t.b i * t.A i j * ∑ k, t.A j k * t.c k =
        (∑ i, t.b i * t.A i j) * ∑ k, t.A j k * t.c k := by
      intro j; rw [← Finset.sum_mul]
    conv_lhs => arg 2; ext j; rw [step2 j, hD1 j]
    -- Step 2: expand product, swap, apply D(1) and D(2)
    have step3 : ∀ j : Fin s, t.b j * (1 - t.c j) * ∑ k, t.A j k * t.c k =
        ∑ k, (t.b j * t.A j k * t.c k - t.b j * t.c j * t.A j k * t.c k) := by
      intro j; rw [Finset.mul_sum]; congr 1; ext k; ring
    conv_lhs => arg 2; ext j; rw [step3 j]
    rw [Finset.sum_comm]
    have step4 : ∀ k : Fin s,
        ∑ j, (t.b j * t.A j k * t.c k - t.b j * t.c j * t.A j k * t.c k) =
        t.c k * (∑ j, t.b j * t.A j k - ∑ j, t.b j * t.c j * t.A j k) := by
      intro k; rw [← Finset.sum_sub_distrib, Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext k; rw [step4 k]
    have step5 : ∀ k : Fin s,
        t.c k * (∑ j, t.b j * t.A j k - ∑ j, t.b j * t.c j * t.A j k) =
        t.c k * (t.b k * (1 - t.c k) - t.b k / 2 * (1 - t.c k ^ 2)) := by
      intro k; congr 1; rw [hD1 k, hD2 k]
    conv_lhs => arg 2; ext k; rw [step5 k]
    -- Close using pointwise ring + B-sums
    have pw : ∀ k : Fin s,
        t.c k * (t.b k * (1 - t.c k) - t.b k / 2 * (1 - t.c k ^ 2)) =
        1 / 2 * (t.b k * t.c k) - t.b k * t.c k ^ 2 +
        1 / 2 * (t.b k * t.c k ^ 3) := by intro k; ring
    simp_rw [pw, Finset.sum_add_distrib, Finset.sum_sub_distrib,
             ← Finset.mul_sum, hB2, hB3, hB4]; ring

/-- **B(5) ∧ C(3) ∧ D(1) → order ≥ 5.**

The 9 fifth-order conditions all follow from B(5), C(3), and D(1):
- Conditions 1–4, 6: C(2) or C(3) collapses inner sums, reducing to B(5).
- Condition 5: D(1) swaps sums: ∑ bᵢ(∑ aᵢⱼcⱼ³) = ∑ bⱼcⱼ³(1−cⱼ) = B(4)−B(5).
- Conditions 7–9: C collapses inner sums, reducing to a constant times condition 5.

Reference: Hairer–Nørsett–Wanner, Theorem IV.5.1. -/
theorem HasOrderGe5_of_B5_C3_D1 (t : ButcherTableau s) (hB : t.SatisfiesB 5)
    (hC : t.SatisfiesC 3) (hD : t.SatisfiesD 1) : t.HasOrderGe5 := by
  have hOrd4 := HasOrderGe4_of_B4_C3 t (hB.mono (by omega)) hC
  -- Extract B-sums
  have hB4 : ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4 := by
    have h := hB 4 (by omega) (by omega); simpa using h
  have hB5 : ∑ i : Fin s, t.b i * t.c i ^ 4 = 1 / 5 := by
    have h := hB 5 (by omega) le_rfl; simpa using h
  -- Extract C-sums
  have hC2 : ∀ i : Fin s, ∑ j, t.A i j * t.c j = t.c i ^ 2 / 2 := by
    intro i; have h := hC 2 (by omega) (by omega) i; simpa using h
  have hC3 : ∀ i : Fin s, ∑ j, t.A i j * t.c j ^ 2 = t.c i ^ 3 / 3 := by
    intro i; have h := hC 3 (by omega) le_rfl i; simpa using h
  -- Extract D(1)
  have hD1 : ∀ j : Fin s, ∑ i, t.b i * t.A i j = t.b j * (1 - t.c j) := by
    intro j; have h := hD 1 (by omega) le_rfl j; simpa using h
  -- Prove condition 5 first (used by conditions 7–9)
  have h5e : ∑ i : Fin s, ∑ j, t.b i * t.A i j * t.c j ^ 3 = 1 / 20 := by
    rw [Finset.sum_comm]
    have step : ∀ j : Fin s,
        ∑ i, t.b i * t.A i j * t.c j ^ 3 = t.c j ^ 3 * ∑ i, t.b i * t.A i j := by
      intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
    conv_lhs => arg 2; ext j; rw [step j, hD1 j]
    have pw : ∀ j : Fin s, t.c j ^ 3 * (t.b j * (1 - t.c j)) =
        t.b j * t.c j ^ 3 - t.b j * t.c j ^ 4 := by intro j; ring
    simp_rw [pw, Finset.sum_sub_distrib, hB4, hB5]; ring
  refine ⟨hOrd4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- order5a: ∑ bᵢcᵢ⁴ = 1/5, from B(5)
    simp only [order5a]; linarith [hB5]
  · -- order5b: ∑ bᵢcᵢ²(∑ aᵢⱼcⱼ) = 1/10, using C(2)
    simp only [order5b]
    have step : ∀ i : Fin s,
        t.b i * t.c i ^ 2 * ∑ j, t.A i j * t.c j =
        t.b i * t.c i ^ 2 * (t.c i ^ 2 / 2) := by
      intro i; rw [hC2 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * t.c i ^ 2 * (t.c i ^ 2 / 2) =
        (1 / 2) * ∑ i : Fin s, t.b i * t.c i ^ 4 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB5]; ring
  · -- order5c: ∑ bᵢ(∑ aᵢⱼcⱼ)² = 1/20, using C(2)
    simp only [order5c]
    have step : ∀ i : Fin s,
        t.b i * (∑ j, t.A i j * t.c j) ^ 2 =
        t.b i * (t.c i ^ 2 / 2) ^ 2 := by
      intro i; rw [hC2 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * (t.c i ^ 2 / 2) ^ 2 =
        (1 / 4) * ∑ i : Fin s, t.b i * t.c i ^ 4 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB5]; ring
  · -- order5d: ∑ bᵢcᵢ(∑ aᵢⱼcⱼ²) = 1/15, using C(3)
    simp only [order5d]
    have step : ∀ i : Fin s,
        t.b i * t.c i * ∑ j, t.A i j * t.c j ^ 2 =
        t.b i * t.c i * (t.c i ^ 3 / 3) := by
      intro i; rw [hC3 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * t.c i * (t.c i ^ 3 / 3) =
        (1 / 3) * ∑ i : Fin s, t.b i * t.c i ^ 4 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB5]; ring
  · -- order5e: ∑∑ bᵢaᵢⱼcⱼ³ = 1/20, using D(1)
    exact h5e
  · -- order5f: ∑ bᵢcᵢ(∑ aᵢⱼ(∑ aⱼₖcₖ)) = 1/30, using C(2) then C(3) then B(5)
    simp only [order5f]
    -- Inner: ∑ₖ aⱼₖcₖ = cⱼ²/2, then ∑ⱼ aᵢⱼ(cⱼ²/2) = cᵢ³/6
    have inner : ∀ i : Fin s,
        ∑ j, t.A i j * (∑ k, t.A j k * t.c k) = t.c i ^ 3 / 6 := by
      intro i
      have h1 : ∀ j : Fin s, ∑ k, t.A j k * t.c k = t.c j ^ 2 / 2 := hC2
      conv_lhs => arg 2; ext j; rw [h1 j]
      have : ∑ j : Fin s, t.A i j * (t.c j ^ 2 / 2) =
          (1 / 2) * ∑ j, t.A i j * t.c j ^ 2 := by
        rw [Finset.mul_sum]; congr 1; ext j; ring
      rw [this, hC3 i]; ring
    have step2 : ∀ i : Fin s,
        t.b i * t.c i * (∑ j, t.A i j * (∑ k, t.A j k * t.c k)) =
        t.b i * t.c i * (t.c i ^ 3 / 6) := by
      intro i; rw [inner i]
    conv_lhs => arg 2; ext i; rw [step2 i]
    have : ∑ i : Fin s, t.b i * t.c i * (t.c i ^ 3 / 6) =
        (1 / 6) * ∑ i : Fin s, t.b i * t.c i ^ 4 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB5]; ring
  · -- order5g: ∑∑ bᵢaᵢⱼcⱼ(∑ aⱼₖcₖ) = 1/40, using C(2), reduces to (1/2)·condition 5
    simp only [order5g]
    -- C(2): ∑ₖ aⱼₖcₖ = cⱼ²/2
    have step : ∀ i j : Fin s,
        t.b i * t.A i j * t.c j * ∑ k, t.A j k * t.c k =
        t.b i * t.A i j * t.c j * (t.c j ^ 2 / 2) := by
      intro i j; rw [hC2 j]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step i j]
    -- Factor: bᵢaᵢⱼcⱼ·cⱼ²/2 = (1/2)·bᵢaᵢⱼcⱼ³
    have step2 : ∀ i : Fin s, ∑ j, t.b i * t.A i j * t.c j * (t.c j ^ 2 / 2) =
        (1 / 2) * ∑ j, t.b i * t.A i j * t.c j ^ 3 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step2 i]
    rw [← Finset.mul_sum, h5e]; ring
  · -- order5h: ∑∑ bᵢaᵢⱼ(∑ aⱼₖcₖ²) = 1/60, using C(3), reduces to (1/3)·condition 5
    simp only [order5h]
    -- C(3): ∑ₖ aⱼₖcₖ² = cⱼ³/3
    have step : ∀ i j : Fin s,
        t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 2 =
        t.b i * t.A i j * (t.c j ^ 3 / 3) := by
      intro i j; rw [hC3 j]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step i j]
    have step2 : ∀ i : Fin s, ∑ j, t.b i * t.A i j * (t.c j ^ 3 / 3) =
        (1 / 3) * ∑ j, t.b i * t.A i j * t.c j ^ 3 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step2 i]
    rw [← Finset.mul_sum, h5e]; ring
  · -- order5i: ∑∑∑ bᵢaᵢⱼaⱼₖ(∑ aₖₗcₗ) = 1/120
    -- C(2): ∑ₗ aₖₗcₗ = cₖ²/2, then C(3): ∑ₖ aⱼₖcₖ² → cⱼ³/3
    -- Net: reduces to (1/6)·condition 5
    simp only [order5i]
    -- Step 1: C(2) on innermost sum
    have step1 : ∀ i j k : Fin s,
        t.b i * t.A i j * t.A j k * ∑ l, t.A k l * t.c l =
        t.b i * t.A i j * t.A j k * (t.c k ^ 2 / 2) := by
      intro i j k; rw [hC2 k]
    conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; ext k; rw [step1 i j k]
    -- Step 2: factor out 1/2, collapse to ∑ aⱼₖcₖ²
    have step2 : ∀ i j : Fin s,
        ∑ k, t.b i * t.A i j * t.A j k * (t.c k ^ 2 / 2) =
        (1 / 2) * (t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 2) := by
      intro i j
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step2 i j]
    -- Step 3: C(3) on ∑ₖ aⱼₖcₖ²
    have step3 : ∀ i j : Fin s,
        (1 / 2) * (t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 2) =
        (1 / 2) * (t.b i * t.A i j * (t.c j ^ 3 / 3)) := by
      intro i j; rw [hC3 j]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step3 i j]
    -- Step 4: factor to (1/6)·∑∑ bᵢaᵢⱼcⱼ³
    have step4 : ∀ i : Fin s,
        ∑ j, 1 / 2 * (t.b i * t.A i j * (t.c j ^ 3 / 3)) =
        (1 / 6) * ∑ j, t.b i * t.A i j * t.c j ^ 3 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step4 i]
    rw [← Finset.mul_sum, h5e]; ring

/-- **B(5) ∧ C(2) ∧ D(2) → order ≥ 5.**

This alternative to `HasOrderGe5_of_B5_C3_D1` uses C(2) and D(2) instead of C(3) and D(1).
The key insights:
- Conditions 1–3: C(2) collapses inner sums, then B(5).
- Condition 4: swap sums, apply D(2): ∑ bⱼcⱼ²(1−cⱼ²)/2 = (B(3)−B(5))/2.
- Condition 5: swap sums, apply D(1): ∑ bⱼcⱼ³(1−cⱼ) = B(4)−B(5).
- Condition 6: C(2) on inner, then reduces to (1/2)·condition 4.
- Condition 7: C(2) on inner, then (1/2)·condition 5.
- Condition 8: D(1)+D(2) double application: ∑ bₖcₖ²(1−cₖ)²/2 = (B(3)−2B(4)+B(5))/2.
- Condition 9: C(2) on inner, then (1/2)·condition 8.

This is needed for Radau IA 3-stage which satisfies B(5), C(2), and D(3) ⊇ D(2).
Reference: Hairer–Nørsett–Wanner, Theorem IV.5.1. -/
theorem HasOrderGe5_of_B5_C2_D2 (t : ButcherTableau s) (hB : t.SatisfiesB 5)
    (hC : t.SatisfiesC 2) (hD : t.SatisfiesD 2) : t.HasOrderGe5 := by
  have hOrd4 := HasOrderGe4_of_B4_C2_D1 t (hB.mono (by omega)) hC (hD.mono (by omega))
  -- Extract B-sums
  have hB3 : ∑ i : Fin s, t.b i * t.c i ^ 2 = 1 / 3 := by
    have h := hB 3 (by omega) (by omega); simpa using h
  have hB4 : ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4 := by
    have h := hB 4 (by omega) (by omega); simpa using h
  have hB5 : ∑ i : Fin s, t.b i * t.c i ^ 4 = 1 / 5 := by
    have h := hB 5 (by omega) le_rfl; simpa using h
  -- Extract C/D conditions
  have hC2 : ∀ i : Fin s, ∑ j, t.A i j * t.c j = t.c i ^ 2 / 2 := by
    intro i; have h := hC 2 (by omega) le_rfl i; simpa using h
  have hD1 : ∀ j : Fin s, ∑ i, t.b i * t.A i j = t.b j * (1 - t.c j) := by
    intro j; have h := hD 1 (by omega) (by omega) j; simpa using h
  have hD2 : ∀ j : Fin s, ∑ i, t.b i * t.c i * t.A i j = t.b j / 2 * (1 - t.c j ^ 2) := by
    intro j; have h := hD 2 (by omega) le_rfl j; simpa using h
  -- Prove condition 5e first (used by conditions 7 and 9)
  have h5e : ∑ i : Fin s, ∑ j, t.b i * t.A i j * t.c j ^ 3 = 1 / 20 := by
    rw [Finset.sum_comm]
    have step : ∀ j : Fin s,
        ∑ i, t.b i * t.A i j * t.c j ^ 3 = t.c j ^ 3 * ∑ i, t.b i * t.A i j := by
      intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
    conv_lhs => arg 2; ext j; rw [step j, hD1 j]
    have pw : ∀ j : Fin s, t.c j ^ 3 * (t.b j * (1 - t.c j)) =
        t.b j * t.c j ^ 3 - t.b j * t.c j ^ 4 := by intro j; ring
    simp_rw [pw, Finset.sum_sub_distrib, hB4, hB5]; ring
  -- Prove condition 5h (used by condition 9)
  have h5h : ∑ i : Fin s, ∑ j, t.b i * t.A i j *
      (∑ k, t.A j k * t.c k ^ 2) = 1 / 60 := by
    -- Step 1: swap outer sum, apply D(1) to column j
    rw [Finset.sum_comm]
    have step1 : ∀ j : Fin s,
        ∑ i, t.b i * t.A i j * (∑ k, t.A j k * t.c k ^ 2) =
        (∑ i, t.b i * t.A i j) * (∑ k, t.A j k * t.c k ^ 2) := by
      intro j; rw [← Finset.sum_mul]
    conv_lhs => arg 2; ext j; rw [step1 j, hD1 j]
    -- Step 2: expand product, swap inner sum
    have step2 : ∀ j : Fin s,
        t.b j * (1 - t.c j) * ∑ k, t.A j k * t.c k ^ 2 =
        ∑ k, (t.b j * t.A j k * t.c k ^ 2 - t.b j * t.c j * t.A j k * t.c k ^ 2) := by
      intro j; rw [Finset.mul_sum]; congr 1; ext k; ring
    conv_lhs => arg 2; ext j; rw [step2 j]
    rw [Finset.sum_comm]
    have step3 : ∀ k : Fin s,
        ∑ j, (t.b j * t.A j k * t.c k ^ 2 - t.b j * t.c j * t.A j k * t.c k ^ 2) =
        t.c k ^ 2 * (∑ j, t.b j * t.A j k - ∑ j, t.b j * t.c j * t.A j k) := by
      intro k; rw [← Finset.sum_sub_distrib, Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext k; rw [step3 k]
    -- Step 3: apply D(1) and D(2) to inner sums
    have step4 : ∀ k : Fin s,
        t.c k ^ 2 * (∑ j, t.b j * t.A j k - ∑ j, t.b j * t.c j * t.A j k) =
        t.c k ^ 2 * (t.b k * (1 - t.c k) - t.b k / 2 * (1 - t.c k ^ 2)) := by
      intro k; congr 1; rw [hD1 k, hD2 k]
    conv_lhs => arg 2; ext k; rw [step4 k]
    -- Simplify: bₖ(1-cₖ) - bₖ(1-cₖ²)/2 = bₖ(1-cₖ)²/2
    have pw : ∀ k : Fin s,
        t.c k ^ 2 * (t.b k * (1 - t.c k) - t.b k / 2 * (1 - t.c k ^ 2)) =
        1 / 2 * (t.b k * t.c k ^ 2) - t.b k * t.c k ^ 3 +
        1 / 2 * (t.b k * t.c k ^ 4) := by intro k; ring
    simp_rw [pw, Finset.sum_add_distrib, Finset.sum_sub_distrib,
             ← Finset.mul_sum, hB3, hB4, hB5]; ring
  refine ⟨hOrd4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- order5a: ∑ bᵢcᵢ⁴ = 1/5, from B(5)
    simp only [order5a]; linarith [hB5]
  · -- order5b: ∑ bᵢcᵢ²(∑ aᵢⱼcⱼ) = 1/10, using C(2)
    simp only [order5b]
    have step : ∀ i : Fin s,
        t.b i * t.c i ^ 2 * ∑ j, t.A i j * t.c j =
        t.b i * t.c i ^ 2 * (t.c i ^ 2 / 2) := by
      intro i; rw [hC2 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * t.c i ^ 2 * (t.c i ^ 2 / 2) =
        (1 / 2) * ∑ i : Fin s, t.b i * t.c i ^ 4 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB5]; ring
  · -- order5c: ∑ bᵢ(∑ aᵢⱼcⱼ)² = 1/20, using C(2)
    simp only [order5c]
    have step : ∀ i : Fin s,
        t.b i * (∑ j, t.A i j * t.c j) ^ 2 =
        t.b i * (t.c i ^ 2 / 2) ^ 2 := by
      intro i; rw [hC2 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * (t.c i ^ 2 / 2) ^ 2 =
        (1 / 4) * ∑ i : Fin s, t.b i * t.c i ^ 4 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB5]; ring
  · -- order5d: ∑ bᵢcᵢ(∑ aᵢⱼcⱼ²) = 1/15, using D(2)
    -- Swap sums, apply D(2): ∑ⱼ cⱼ²(∑ᵢ bᵢcᵢaᵢⱼ) = ∑ⱼ cⱼ² bⱼ(1-cⱼ²)/2
    simp only [order5d]
    have expand : ∀ i : Fin s, t.b i * t.c i * ∑ j, t.A i j * t.c j ^ 2 =
        ∑ j, t.b i * t.c i * t.A i j * t.c j ^ 2 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [expand i]
    rw [Finset.sum_comm]
    have factor : ∀ j : Fin s, ∑ i, t.b i * t.c i * t.A i j * t.c j ^ 2 =
        t.c j ^ 2 * ∑ i, t.b i * t.c i * t.A i j := by
      intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
    conv_lhs => arg 2; ext j; rw [factor j, hD2 j]
    have pw : ∀ j : Fin s, t.c j ^ 2 * (t.b j / 2 * (1 - t.c j ^ 2)) =
        1 / 2 * (t.b j * t.c j ^ 2) - 1 / 2 * (t.b j * t.c j ^ 4) := by
      intro j; ring
    simp_rw [pw, Finset.sum_sub_distrib, ← Finset.mul_sum, hB3, hB5]; ring
  · -- order5e: ∑∑ bᵢaᵢⱼcⱼ³ = 1/20, using D(1)
    exact h5e
  · -- order5f: ∑ bᵢcᵢ(∑ⱼ aᵢⱼ(∑ₖ aⱼₖcₖ)) = 1/30
    -- C(2) on inner: ∑ₖ aⱼₖcₖ = cⱼ²/2, then reduces to (1/2)·order5d
    simp only [order5f]
    have inner : ∀ i : Fin s,
        ∑ j, t.A i j * (∑ k, t.A j k * t.c k) = ∑ j, t.A i j * (t.c j ^ 2 / 2) := by
      intro i; congr 1; ext j; rw [hC2 j]
    conv_lhs => arg 2; ext i; rw [show t.b i * t.c i *
        (∑ j, t.A i j * (∑ k, t.A j k * t.c k)) =
        t.b i * t.c i * (∑ j, t.A i j * (∑ k, t.A j k * t.c k)) from rfl, inner i]
    -- Factor out 1/2
    have factor : ∀ i : Fin s,
        t.b i * t.c i * ∑ j, t.A i j * (t.c j ^ 2 / 2) =
        (1 / 2) * (t.b i * t.c i * ∑ j, t.A i j * t.c j ^ 2) := by
      intro i; rw [Finset.mul_sum, Finset.mul_sum]; congr 1
      rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [factor i]
    -- Now (1/2) · ∑ bᵢcᵢ(∑ aᵢⱼcⱼ²) = (1/2) · 1/15 = 1/30
    -- Reprove order5d inline
    rw [← Finset.mul_sum]
    have expand : ∀ i : Fin s, t.b i * t.c i * ∑ j, t.A i j * t.c j ^ 2 =
        ∑ j, t.b i * t.c i * t.A i j * t.c j ^ 2 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; arg 2; ext i; rw [expand i]
    rw [Finset.sum_comm]
    have factor2 : ∀ j : Fin s, ∑ i, t.b i * t.c i * t.A i j * t.c j ^ 2 =
        t.c j ^ 2 * ∑ i, t.b i * t.c i * t.A i j := by
      intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
    conv_lhs => arg 2; arg 2; ext j; rw [factor2 j, hD2 j]
    have pw : ∀ j : Fin s, t.c j ^ 2 * (t.b j / 2 * (1 - t.c j ^ 2)) =
        1 / 2 * (t.b j * t.c j ^ 2) - 1 / 2 * (t.b j * t.c j ^ 4) := by
      intro j; ring
    simp_rw [pw, Finset.sum_sub_distrib, ← Finset.mul_sum, hB3, hB5]; ring
  · -- order5g: ∑∑ bᵢaᵢⱼcⱼ(∑ₖ aⱼₖcₖ) = 1/40
    -- C(2) on inner: ∑ₖ aⱼₖcₖ = cⱼ²/2, then (1/2)·condition 5e
    simp only [order5g]
    have step : ∀ i j : Fin s,
        t.b i * t.A i j * t.c j * ∑ k, t.A j k * t.c k =
        t.b i * t.A i j * t.c j * (t.c j ^ 2 / 2) := by
      intro i j; rw [hC2 j]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step i j]
    have step2 : ∀ i : Fin s, ∑ j, t.b i * t.A i j * t.c j * (t.c j ^ 2 / 2) =
        (1 / 2) * ∑ j, t.b i * t.A i j * t.c j ^ 3 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step2 i]
    rw [← Finset.mul_sum, h5e]; ring
  · -- order5h: ∑∑ bᵢaᵢⱼ(∑ₖ aⱼₖcₖ²) = 1/60
    exact h5h
  · -- order5i: ∑∑∑ bᵢaᵢⱼaⱼₖ(∑ₗ aₖₗcₗ) = 1/120
    -- C(2) on innermost: ∑ₗ aₖₗcₗ = cₖ²/2, then (1/2)·condition 8
    simp only [order5i]
    have step1 : ∀ i j k : Fin s,
        t.b i * t.A i j * t.A j k * ∑ l, t.A k l * t.c l =
        t.b i * t.A i j * t.A j k * (t.c k ^ 2 / 2) := by
      intro i j k; rw [hC2 k]
    conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; ext k; rw [step1 i j k]
    -- Factor out 1/2, collapse to ∑ aⱼₖcₖ²
    have step2 : ∀ i j : Fin s,
        ∑ k, t.b i * t.A i j * t.A j k * (t.c k ^ 2 / 2) =
        (1 / 2) * (t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 2) := by
      intro i j
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step2 i j]
    -- Factor out 1/2 from double sum
    have step3 : ∀ i : Fin s,
        ∑ j, 1 / 2 * (t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 2) =
        (1 / 2) * ∑ j, t.b i * t.A i j * (∑ k, t.A j k * t.c k ^ 2) := by
      intro i; rw [Finset.mul_sum]
    conv_lhs => arg 2; ext i; rw [step3 i]
    rw [← Finset.mul_sum, h5h]; ring

/-- **B(6) ∧ C(3) ∧ D(2) → order ≥ 6.**

All 20 sixth-order conditions follow from B(6), C(3), and D(2).
The proof strategy:
- Conditions 6a–6g: C(2)/C(3) collapse inner sums, reducing to B(6).
- Condition 6h: D(2) swaps sums, reducing to B(4)−B(6).
- Conditions 6i–6k: C collapses to a constant times 6h.
- Condition 6l: D(1) swaps sums: B(5)−B(6).
- Conditions 6m–6o, 6q: C collapses to constants times 6l.
- Condition 6p: D(1)+D(2): (B(4)−B(5))−(B(4)−B(6))/2.
- Conditions 6r–6t: C collapses to constants times 6p.

Reference: Hairer–Nørsett–Wanner, Theorem IV.7.4 (p ≤ η+ζ+1, p ≤ 2η+2). -/
theorem HasOrderGe6_of_B6_C3_D2 (t : ButcherTableau s) (hB : t.SatisfiesB 6)
    (hC : t.SatisfiesC 3) (hD : t.SatisfiesD 2) : t.HasOrderGe6 := by
  have hOrd5 := HasOrderGe5_of_B5_C3_D1 t (hB.mono (by omega)) hC (hD.mono (by omega))
  -- Extract B-sums
  have hB4 : ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4 := by
    have h := hB 4 (by omega) (by omega); simpa using h
  have hB5 : ∑ i : Fin s, t.b i * t.c i ^ 4 = 1 / 5 := by
    have h := hB 5 (by omega) (by omega); simpa using h
  have hB6 : ∑ i : Fin s, t.b i * t.c i ^ 5 = 1 / 6 := by
    have h := hB 6 (by omega) le_rfl; simpa using h
  -- Extract C conditions
  have hC2 : ∀ i : Fin s, ∑ j, t.A i j * t.c j = t.c i ^ 2 / 2 := by
    intro i; have h := hC 2 (by omega) (by omega) i; simpa using h
  have hC3 : ∀ i : Fin s, ∑ j, t.A i j * t.c j ^ 2 = t.c i ^ 3 / 3 := by
    intro i; have h := hC 3 (by omega) le_rfl i; simpa using h
  -- Extract D conditions
  have hD1 : ∀ j : Fin s, ∑ i, t.b i * t.A i j = t.b j * (1 - t.c j) := by
    intro j; have h := hD 1 (by omega) (by omega) j; simpa using h
  have hD2 : ∀ j : Fin s, ∑ i, t.b i * t.c i * t.A i j = t.b j / 2 * (1 - t.c j ^ 2) := by
    intro j; have h := hD 2 (by omega) le_rfl j; simpa using h
  -- Derived: ∑ⱼ aᵢⱼ(∑ₖ aⱼₖcₖ) = cᵢ³/6 (C(2) then C(3))
  have h_inner2 : ∀ i : Fin s,
      ∑ j, t.A i j * (∑ k, t.A j k * t.c k) = t.c i ^ 3 / 6 := by
    intro i
    conv_lhs => arg 2; ext j; rw [hC2 j]
    have : ∑ j : Fin s, t.A i j * (t.c j ^ 2 / 2) =
        (1 / 2) * ∑ j, t.A i j * t.c j ^ 2 := by
      rw [Finset.mul_sum]; congr 1; ext j; ring
    rw [this, hC3 i]; ring
  -- Key intermediate: h6h_val — ∑ bᵢcᵢ(∑ aᵢⱼcⱼ³) = 1/24
  -- Strategy: swap sums, apply D(2)
  have h6h_val : ∑ i : Fin s, t.b i * t.c i *
      (∑ j, t.A i j * t.c j ^ 3) = 1 / 24 := by
    have expand : ∀ i : Fin s, t.b i * t.c i * ∑ j, t.A i j * t.c j ^ 3 =
        ∑ j, t.b i * t.c i * t.A i j * t.c j ^ 3 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [expand i]
    rw [Finset.sum_comm]
    have factor : ∀ j : Fin s, ∑ i, t.b i * t.c i * t.A i j * t.c j ^ 3 =
        t.c j ^ 3 * ∑ i, t.b i * t.c i * t.A i j := by
      intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
    conv_lhs => arg 2; ext j; rw [factor j, hD2 j]
    have pw : ∀ j : Fin s, t.c j ^ 3 * (t.b j / 2 * (1 - t.c j ^ 2)) =
        1 / 2 * (t.b j * t.c j ^ 3) - 1 / 2 * (t.b j * t.c j ^ 5) := by intro j; ring
    simp_rw [pw, Finset.sum_sub_distrib, ← Finset.mul_sum, hB4, hB6]; ring
  -- Key intermediate: h6l_val — ∑∑ bᵢaᵢⱼcⱼ⁴ = 1/30
  -- Strategy: swap sums, apply D(1)
  have h6l_val : ∑ i : Fin s, ∑ j, t.b i * t.A i j * t.c j ^ 4 = 1 / 30 := by
    rw [Finset.sum_comm]
    have step : ∀ j : Fin s,
        ∑ i, t.b i * t.A i j * t.c j ^ 4 = t.c j ^ 4 * ∑ i, t.b i * t.A i j := by
      intro j; rw [Finset.mul_sum]; congr 1; ext i; ring
    conv_lhs => arg 2; ext j; rw [step j, hD1 j]
    have pw : ∀ j : Fin s, t.c j ^ 4 * (t.b j * (1 - t.c j)) =
        t.b j * t.c j ^ 4 - t.b j * t.c j ^ 5 := by intro j; ring
    simp_rw [pw, Finset.sum_sub_distrib, hB5, hB6]; ring
  -- Key intermediate: h6p_val — ∑∑ bᵢaᵢⱼ(∑ aⱼₖcₖ³) = 1/120
  -- Strategy: D(1) on outer, then D(1)+D(2) on inner
  have h6p_val : ∑ i : Fin s, ∑ j,
      t.b i * t.A i j * (∑ k, t.A j k * t.c k ^ 3) = 1 / 120 := by
    rw [Finset.sum_comm]
    have step1 : ∀ j : Fin s,
        ∑ i, t.b i * t.A i j * (∑ k, t.A j k * t.c k ^ 3) =
        (∑ i, t.b i * t.A i j) * (∑ k, t.A j k * t.c k ^ 3) := by
      intro j; rw [← Finset.sum_mul]
    conv_lhs => arg 2; ext j; rw [step1 j, hD1 j]
    -- Expand bⱼ(1-cⱼ) · (∑ₖ aⱼₖcₖ³)
    have step2 : ∀ j : Fin s, t.b j * (1 - t.c j) * ∑ k, t.A j k * t.c k ^ 3 =
        ∑ k, (t.b j * t.A j k * t.c k ^ 3 - t.b j * t.c j * t.A j k * t.c k ^ 3) := by
      intro j; rw [Finset.mul_sum]; congr 1; ext k; ring
    conv_lhs => arg 2; ext j; rw [step2 j]
    rw [Finset.sum_comm]
    have step3 : ∀ k : Fin s,
        ∑ j, (t.b j * t.A j k * t.c k ^ 3 - t.b j * t.c j * t.A j k * t.c k ^ 3) =
        t.c k ^ 3 * (∑ j, t.b j * t.A j k - ∑ j, t.b j * t.c j * t.A j k) := by
      intro k; rw [← Finset.sum_sub_distrib, Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext k; rw [step3 k]
    have step4 : ∀ k : Fin s,
        t.c k ^ 3 * (∑ j, t.b j * t.A j k - ∑ j, t.b j * t.c j * t.A j k) =
        t.c k ^ 3 * (t.b k * (1 - t.c k) - t.b k / 2 * (1 - t.c k ^ 2)) := by
      intro k; congr 1; rw [hD1 k, hD2 k]
    conv_lhs => arg 2; ext k; rw [step4 k]
    have pw : ∀ k : Fin s,
        t.c k ^ 3 * (t.b k * (1 - t.c k) - t.b k / 2 * (1 - t.c k ^ 2)) =
        1 / 2 * (t.b k * t.c k ^ 3) - t.b k * t.c k ^ 4 +
        1 / 2 * (t.b k * t.c k ^ 5) := by intro k; ring
    simp_rw [pw, Finset.sum_add_distrib, Finset.sum_sub_distrib,
             ← Finset.mul_sum, hB4, hB5, hB6]; ring
  refine ⟨hOrd5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- order6a: ∑ bᵢcᵢ⁵ = 1/6, from B(6)
    simp only [order6a]; linarith [hB6]
  · -- order6b: ∑ bᵢcᵢ³(∑ aᵢⱼcⱼ) = 1/12, C(2): inner = cᵢ²/2
    simp only [order6b]
    have step : ∀ i : Fin s,
        t.b i * t.c i ^ 3 * ∑ j, t.A i j * t.c j =
        t.b i * t.c i ^ 3 * (t.c i ^ 2 / 2) := by
      intro i; rw [hC2 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * t.c i ^ 3 * (t.c i ^ 2 / 2) =
        (1 / 2) * ∑ i : Fin s, t.b i * t.c i ^ 5 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB6]; ring
  · -- order6c: ∑ bᵢcᵢ(∑ aᵢⱼcⱼ)² = 1/24, C(2): inner = cᵢ²/2
    simp only [order6c]
    have step : ∀ i : Fin s,
        t.b i * t.c i * (∑ j, t.A i j * t.c j) ^ 2 =
        t.b i * t.c i * (t.c i ^ 2 / 2) ^ 2 := by
      intro i; rw [hC2 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * t.c i * (t.c i ^ 2 / 2) ^ 2 =
        (1 / 4) * ∑ i : Fin s, t.b i * t.c i ^ 5 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB6]; ring
  · -- order6d: ∑ bᵢcᵢ²(∑ aᵢⱼcⱼ²) = 1/18, C(3): inner = cᵢ³/3
    simp only [order6d]
    have step : ∀ i : Fin s,
        t.b i * t.c i ^ 2 * ∑ j, t.A i j * t.c j ^ 2 =
        t.b i * t.c i ^ 2 * (t.c i ^ 3 / 3) := by
      intro i; rw [hC3 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * t.c i ^ 2 * (t.c i ^ 3 / 3) =
        (1 / 3) * ∑ i : Fin s, t.b i * t.c i ^ 5 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB6]; ring
  · -- order6e: ∑ bᵢcᵢ²(∑ aᵢⱼ(∑ aⱼₖcₖ)) = 1/36, using h_inner2 = cᵢ³/6
    simp only [order6e]
    have step : ∀ i : Fin s,
        t.b i * t.c i ^ 2 * (∑ j, t.A i j * (∑ k, t.A j k * t.c k)) =
        t.b i * t.c i ^ 2 * (t.c i ^ 3 / 6) := by
      intro i; rw [h_inner2 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * t.c i ^ 2 * (t.c i ^ 3 / 6) =
        (1 / 6) * ∑ i : Fin s, t.b i * t.c i ^ 5 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB6]; ring
  · -- order6f: ∑ bᵢ(∑ aᵢⱼcⱼ)(∑ aᵢⱼcⱼ²) = 1/36, C(2)·C(3)
    simp only [order6f]
    have step : ∀ i : Fin s,
        t.b i * (∑ j, t.A i j * t.c j) * (∑ j, t.A i j * t.c j ^ 2) =
        t.b i * (t.c i ^ 2 / 2) * (t.c i ^ 3 / 3) := by
      intro i; rw [hC2 i, hC3 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * (t.c i ^ 2 / 2) * (t.c i ^ 3 / 3) =
        (1 / 6) * ∑ i : Fin s, t.b i * t.c i ^ 5 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB6]; ring
  · -- order6g: ∑ bᵢ(∑ aᵢⱼcⱼ)(∑ aᵢⱼ(∑ aⱼₖcₖ)) = 1/72, C(2)·h_inner2
    simp only [order6g]
    have step : ∀ i : Fin s,
        t.b i * (∑ j, t.A i j * t.c j) *
        (∑ j, t.A i j * (∑ k, t.A j k * t.c k)) =
        t.b i * (t.c i ^ 2 / 2) * (t.c i ^ 3 / 6) := by
      intro i; rw [hC2 i, h_inner2 i]
    conv_lhs => arg 2; ext i; rw [step i]
    have : ∑ i : Fin s, t.b i * (t.c i ^ 2 / 2) * (t.c i ^ 3 / 6) =
        (1 / 12) * ∑ i : Fin s, t.b i * t.c i ^ 5 := by
      rw [Finset.mul_sum]; congr 1; ext i; ring
    rw [this, hB6]; ring
  · -- order6h: ∑ bᵢcᵢ(∑ aᵢⱼcⱼ³) = 1/24
    exact h6h_val
  · -- order6i: ∑ bᵢcᵢ(∑ aᵢⱼcⱼ(∑ aⱼₖcₖ)) = 1/48
    -- C(2) on inner: ∑ₖ aⱼₖcₖ = cⱼ²/2, then = (1/2)·h6h
    simp only [order6i]
    have step : ∀ i : Fin s,
        t.b i * t.c i * (∑ j, t.A i j * t.c j * (∑ k, t.A j k * t.c k)) =
        t.b i * t.c i * (∑ j, t.A i j * t.c j * (t.c j ^ 2 / 2)) := by
      intro i; congr 1; congr 1; ext j; rw [hC2 j]
    conv_lhs => arg 2; ext i; rw [step i]
    have step2 : ∀ i : Fin s,
        t.b i * t.c i * ∑ j, t.A i j * t.c j * (t.c j ^ 2 / 2) =
        (1 / 2) * (t.b i * t.c i * ∑ j, t.A i j * t.c j ^ 3) := by
      intro i; rw [Finset.mul_sum, Finset.mul_sum]; congr 1
      rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step2 i]
    rw [← Finset.mul_sum, h6h_val]; ring
  · -- order6j: ∑ bᵢcᵢ(∑ aᵢⱼ(∑ aⱼₖcₖ²)) = 1/72
    -- C(3): inner = cⱼ³/3, then = (1/3)·h6h
    simp only [order6j]
    have step : ∀ i : Fin s,
        t.b i * t.c i * (∑ j, t.A i j * (∑ k, t.A j k * t.c k ^ 2)) =
        t.b i * t.c i * (∑ j, t.A i j * (t.c j ^ 3 / 3)) := by
      intro i; congr 1; congr 1; ext j; rw [hC3 j]
    conv_lhs => arg 2; ext i; rw [step i]
    have step2 : ∀ i : Fin s,
        t.b i * t.c i * ∑ j, t.A i j * (t.c j ^ 3 / 3) =
        (1 / 3) * (t.b i * t.c i * ∑ j, t.A i j * t.c j ^ 3) := by
      intro i; rw [Finset.mul_sum, Finset.mul_sum]; congr 1
      rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step2 i]
    rw [← Finset.mul_sum, h6h_val]; ring
  · -- order6k: ∑ bᵢcᵢ(∑ aᵢⱼ(∑ aⱼₖ(∑ aₖₗcₗ))) = 1/144
    -- C(2) on innermost, then C(3), then = (1/6)·h6h
    simp only [order6k]
    -- Step 1: C(2) on innermost: ∑ₗ aₖₗcₗ = cₖ²/2
    have step1 : ∀ i : Fin s,
        t.b i * t.c i * (∑ j, t.A i j * (∑ k, t.A j k * (∑ l, t.A k l * t.c l))) =
        t.b i * t.c i * (∑ j, t.A i j * (∑ k, t.A j k * (t.c k ^ 2 / 2))) := by
      intro i; congr 1; congr 1; ext j; congr 1; congr 1; ext k; congr 1; rw [hC2 k]
    conv_lhs => arg 2; ext i; rw [step1 i]
    -- Step 2: ∑ₖ aⱼₖ(cₖ²/2) = (1/2)·∑ₖ aⱼₖcₖ² = (1/2)·cⱼ³/3 = cⱼ³/6
    have step2 : ∀ j : Fin s,
        ∑ k, t.A j k * (t.c k ^ 2 / 2) = t.c j ^ 3 / 6 := by
      intro j
      have : ∑ k : Fin s, t.A j k * (t.c k ^ 2 / 2) =
          (1 / 2) * ∑ k, t.A j k * t.c k ^ 2 := by
        rw [Finset.mul_sum]; congr 1; ext k; ring
      rw [this, hC3 j]; ring
    have step3 : ∀ i : Fin s,
        t.b i * t.c i * (∑ j, t.A i j * (∑ k, t.A j k * (t.c k ^ 2 / 2))) =
        t.b i * t.c i * (∑ j, t.A i j * (t.c j ^ 3 / 6)) := by
      intro i; congr 1; congr 1; ext j; rw [step2 j]
    conv_lhs => arg 2; ext i; rw [step3 i]
    -- Step 3: factor to (1/6)·h6h
    have step4 : ∀ i : Fin s,
        t.b i * t.c i * ∑ j, t.A i j * (t.c j ^ 3 / 6) =
        (1 / 6) * (t.b i * t.c i * ∑ j, t.A i j * t.c j ^ 3) := by
      intro i; rw [Finset.mul_sum, Finset.mul_sum]; congr 1
      rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step4 i]
    rw [← Finset.mul_sum, h6h_val]; ring
  · -- order6l: ∑∑ bᵢaᵢⱼcⱼ⁴ = 1/30
    exact h6l_val
  · -- order6m: ∑∑ bᵢaᵢⱼcⱼ²(∑ aⱼₖcₖ) = 1/60
    -- C(2): inner = cⱼ²/2, so cⱼ²·(cⱼ²/2) = cⱼ⁴/2, then (1/2)·h6l
    simp only [order6m]
    have step : ∀ i j : Fin s,
        t.b i * t.A i j * t.c j ^ 2 * (∑ k, t.A j k * t.c k) =
        t.b i * t.A i j * t.c j ^ 2 * (t.c j ^ 2 / 2) := by
      intro i j; rw [hC2 j]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step i j]
    have step2 : ∀ i : Fin s,
        ∑ j, t.b i * t.A i j * t.c j ^ 2 * (t.c j ^ 2 / 2) =
        (1 / 2) * ∑ j, t.b i * t.A i j * t.c j ^ 4 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step2 i]
    rw [← Finset.mul_sum, h6l_val]; ring
  · -- order6n: ∑∑ bᵢaᵢⱼ(∑ aⱼₖcₖ)² = 1/120
    -- C(2): (∑ aⱼₖcₖ)² = (cⱼ²/2)² = cⱼ⁴/4, then (1/4)·h6l
    simp only [order6n]
    have step : ∀ i j : Fin s,
        t.b i * t.A i j * (∑ k, t.A j k * t.c k) ^ 2 =
        t.b i * t.A i j * (t.c j ^ 2 / 2) ^ 2 := by
      intro i j; rw [hC2 j]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step i j]
    have step2 : ∀ i : Fin s,
        ∑ j, t.b i * t.A i j * (t.c j ^ 2 / 2) ^ 2 =
        (1 / 4) * ∑ j, t.b i * t.A i j * t.c j ^ 4 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step2 i]
    rw [← Finset.mul_sum, h6l_val]; ring
  · -- order6o: ∑∑ bᵢaᵢⱼcⱼ(∑ aⱼₖcₖ²) = 1/90
    -- C(3): inner = cⱼ³/3, then cⱼ·(cⱼ³/3) = cⱼ⁴/3, then (1/3)·h6l
    simp only [order6o]
    have step : ∀ i j : Fin s,
        t.b i * t.A i j * t.c j * (∑ k, t.A j k * t.c k ^ 2) =
        t.b i * t.A i j * t.c j * (t.c j ^ 3 / 3) := by
      intro i j; rw [hC3 j]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step i j]
    have step2 : ∀ i : Fin s,
        ∑ j, t.b i * t.A i j * t.c j * (t.c j ^ 3 / 3) =
        (1 / 3) * ∑ j, t.b i * t.A i j * t.c j ^ 4 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step2 i]
    rw [← Finset.mul_sum, h6l_val]; ring
  · -- order6p: ∑∑ bᵢaᵢⱼ(∑ aⱼₖcₖ³) = 1/120
    exact h6p_val
  · -- order6q: ∑∑ bᵢaᵢⱼcⱼ(∑ aⱼₖ(∑ aₖₗcₗ)) = 1/180
    -- C(2) on innermost, then C(3), net: cⱼ·(cⱼ³/6) = cⱼ⁴/6, then (1/6)·h6l
    simp only [order6q]
    -- Step 1: C(2) on innermost
    have step1 : ∀ i j : Fin s,
        t.b i * t.A i j * t.c j * (∑ k, t.A j k * (∑ l, t.A k l * t.c l)) =
        t.b i * t.A i j * t.c j * (∑ k, t.A j k * (t.c k ^ 2 / 2)) := by
      intro i j; congr 1; congr 1; ext k; rw [hC2 k]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step1 i j]
    -- Step 2: ∑ₖ aⱼₖ(cₖ²/2) = cⱼ³/6
    have step2 : ∀ j : Fin s,
        ∑ k, t.A j k * (t.c k ^ 2 / 2) = t.c j ^ 3 / 6 := by
      intro j
      have : ∑ k : Fin s, t.A j k * (t.c k ^ 2 / 2) =
          (1 / 2) * ∑ k, t.A j k * t.c k ^ 2 := by
        rw [Finset.mul_sum]; congr 1; ext k; ring
      rw [this, hC3 j]; ring
    have step3 : ∀ i j : Fin s,
        t.b i * t.A i j * t.c j * (∑ k, t.A j k * (t.c k ^ 2 / 2)) =
        t.b i * t.A i j * t.c j * (t.c j ^ 3 / 6) := by
      intro i j; rw [step2 j]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step3 i j]
    -- Step 3: factor to (1/6)·h6l
    have step4 : ∀ i : Fin s,
        ∑ j, t.b i * t.A i j * t.c j * (t.c j ^ 3 / 6) =
        (1 / 6) * ∑ j, t.b i * t.A i j * t.c j ^ 4 := by
      intro i; rw [Finset.mul_sum]; congr 1; ext j; ring
    conv_lhs => arg 2; ext i; rw [step4 i]
    rw [← Finset.mul_sum, h6l_val]; ring
  · -- order6r: ∑∑ bᵢaᵢⱼ(∑ aⱼₖcₖ(∑ aₖₗcₗ)) = 1/240
    -- C(2): inner = cₖ²/2, so cₖ·(cₖ²/2) = cₖ³/2, then (1/2)·h6p
    simp only [order6r]
    have step : ∀ i j : Fin s,
        t.b i * t.A i j * (∑ k, t.A j k * t.c k * (∑ l, t.A k l * t.c l)) =
        t.b i * t.A i j * (∑ k, t.A j k * t.c k * (t.c k ^ 2 / 2)) := by
      intro i j; congr 1; congr 1; ext k; rw [hC2 k]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step i j]
    have step2 : ∀ i j : Fin s,
        t.b i * t.A i j * ∑ k, t.A j k * t.c k * (t.c k ^ 2 / 2) =
        (1 / 2) * (t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 3) := by
      intro i j; rw [Finset.mul_sum, Finset.mul_sum]; congr 1
      rw [Finset.mul_sum]; congr 1; ext k; ring
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step2 i j]
    have step3 : ∀ i : Fin s,
        ∑ j, 1 / 2 * (t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 3) =
        (1 / 2) * ∑ j, t.b i * t.A i j * (∑ k, t.A j k * t.c k ^ 3) := by
      intro i; rw [Finset.mul_sum]
    conv_lhs => arg 2; ext i; rw [step3 i]
    rw [← Finset.mul_sum, h6p_val]; ring
  · -- order6s: ∑∑ bᵢaᵢⱼ(∑ aⱼₖ(∑ aₖₗcₗ²)) = 1/360
    -- C(3): inner = cₖ³/3, then (1/3)·h6p
    simp only [order6s]
    have step : ∀ i j : Fin s,
        t.b i * t.A i j * (∑ k, t.A j k * (∑ l, t.A k l * t.c l ^ 2)) =
        t.b i * t.A i j * (∑ k, t.A j k * (t.c k ^ 3 / 3)) := by
      intro i j; congr 1; congr 1; ext k; rw [hC3 k]
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step i j]
    have step2 : ∀ i j : Fin s,
        t.b i * t.A i j * ∑ k, t.A j k * (t.c k ^ 3 / 3) =
        (1 / 3) * (t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 3) := by
      intro i j; rw [Finset.mul_sum, Finset.mul_sum]; congr 1
      rw [Finset.mul_sum]; congr 1; ext k; ring
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step2 i j]
    have step3 : ∀ i : Fin s,
        ∑ j, 1 / 3 * (t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 3) =
        (1 / 3) * ∑ j, t.b i * t.A i j * (∑ k, t.A j k * t.c k ^ 3) := by
      intro i; rw [Finset.mul_sum]
    conv_lhs => arg 2; ext i; rw [step3 i]
    rw [← Finset.mul_sum, h6p_val]; ring
  · -- order6t: ∑∑∑ bᵢaᵢⱼaⱼₖ(∑ₗ aₖₗ(∑ₘ aₗₘcₘ)) = 1/720
    -- C(2) on innermost, then C(3), net: (1/6)·h6p
    simp only [order6t]
    -- Step 1: C(2) on innermost sum
    have step1 : ∀ i j k : Fin s,
        t.b i * t.A i j * t.A j k * (∑ l, t.A k l * (∑ m, t.A l m * t.c m)) =
        t.b i * t.A i j * t.A j k * (∑ l, t.A k l * (t.c l ^ 2 / 2)) := by
      intro i j k; congr 1; congr 1; ext l; rw [hC2 l]
    conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; ext k; rw [step1 i j k]
    -- Step 2: ∑ₗ aₖₗ(cₗ²/2) = cₖ³/6
    have inner6 : ∀ k : Fin s,
        ∑ l, t.A k l * (t.c l ^ 2 / 2) = t.c k ^ 3 / 6 := by
      intro k
      have : ∑ l : Fin s, t.A k l * (t.c l ^ 2 / 2) =
          (1 / 2) * ∑ l, t.A k l * t.c l ^ 2 := by
        rw [Finset.mul_sum]; congr 1; ext l; ring
      rw [this, hC3 k]; ring
    have step2 : ∀ i j k : Fin s,
        t.b i * t.A i j * t.A j k * (∑ l, t.A k l * (t.c l ^ 2 / 2)) =
        t.b i * t.A i j * t.A j k * (t.c k ^ 3 / 6) := by
      intro i j k; rw [inner6 k]
    conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; ext k; rw [step2 i j k]
    -- Step 3: factor (1/6) out, collapse ∑ₖ aⱼₖ(cₖ³/6) = (1/6)·∑ₖ aⱼₖcₖ³
    have step3 : ∀ i j : Fin s,
        ∑ k, t.b i * t.A i j * t.A j k * (t.c k ^ 3 / 6) =
        (1 / 6) * (t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 3) := by
      intro i j
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [step3 i j]
    -- Step 4: factor out 1/6 from double sum
    have step4 : ∀ i : Fin s,
        ∑ j, 1 / 6 * (t.b i * t.A i j * ∑ k, t.A j k * t.c k ^ 3) =
        (1 / 6) * ∑ j, t.b i * t.A i j * (∑ k, t.A j k * t.c k ^ 3) := by
      intro i; rw [Finset.mul_sum]
    conv_lhs => arg 2; ext i; rw [step4 i]
    rw [← Finset.mul_sum, h6p_val]; ring

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

/-- GL2 satisfies D(1): ∑ᵢ bᵢ aᵢⱼ = bⱼ(1 − cⱼ). -/
theorem rkGaussLegendre2_D1 : rkGaussLegendre2.SatisfiesD 1 := by
  intro k hk1 hk2 j
  have hk : k = 1 := le_antisymm hk2 hk1
  subst hk; fin_cases j <;> simp [rkGaussLegendre2, Fin.sum_univ_two] <;> nlinarith [sqrt3_sq']

/-- GL2 satisfies D(2): the maximal D condition for 2 stages.
  ∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = bⱼ(1 − cⱼ^k)/k for k = 1, 2 and all j.
  This is the maximal D condition: Gauss methods with s stages satisfy D(s). -/
theorem rkGaussLegendre2_D2 : rkGaussLegendre2.SatisfiesD 2 := by
  intro k hk1 hk2 j
  interval_cases k <;> fin_cases j <;>
    simp [rkGaussLegendre2, Fin.sum_univ_two] <;> nlinarith [sqrt3_sq']

/-- **GL2 has order ≥ 4 via simplifying assumptions B(4) ∧ C(2) ∧ D(1).**
  This avoids needing C(3) (which requires s ≥ 3) by using D(1) instead.
  Reference: Hairer–Nørsett–Wanner, Theorem IV.5.1. -/
theorem rkGaussLegendre2_order4' : rkGaussLegendre2.HasOrderGe4 :=
  HasOrderGe4_of_B4_C2_D1 _ rkGaussLegendre2_B4 rkGaussLegendre2_C2 rkGaussLegendre2_D1

/-- GL2 does NOT satisfy B(5): ∑ bᵢ cᵢ⁴ = 7/120 ≠ 1/5.
  The 2-point Gauss quadrature is exact only up to degree 2s−1 = 3. -/
theorem rkGaussLegendre2_not_B5 : ¬rkGaussLegendre2.SatisfiesB 5 := by
  intro hB
  have h := hB 5 (by omega) le_rfl
  simp [rkGaussLegendre2, Fin.sum_univ_two] at h
  nlinarith [sqrt3_sq']

/-- GL2 does NOT satisfy C(3): for a 2-stage method, C(q) with q ≥ 3 is impossible
  (the system is overdetermined). In particular, ∑ⱼ a₁ⱼ cⱼ² ≠ c₁³/3.
  This shows the stage order of GL2 is exactly 2. -/
theorem rkGaussLegendre2_not_C3 : ¬rkGaussLegendre2.SatisfiesC 3 := by
  intro hC
  have h := hC 3 (by omega) le_rfl 0
  simp [rkGaussLegendre2, Fin.sum_univ_two] at h
  nlinarith [sqrt3_sq']

end GaussLegendre2

end ButcherTableau
