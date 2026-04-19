import OpenMath.RungeKutta
import OpenMath.OrderConditions
import Mathlib.LinearAlgebra.Vandermonde

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

/-- **Simplifying assumption E(η,ζ)**: for k = 1,...,η and l = 1,...,ζ,
∑ᵢⱼ bᵢ cᵢ^{k-1} aᵢⱼ cⱼ^{l-1} = 1 / (l (k + l)).
This is equation (321c) in Iserles, and equivalently the monomial form of
Theorem 343B, equation (343k). -/
def SatisfiesE (t : ButcherTableau s) (η ζ : ℕ) : Prop :=
  ∀ k l : ℕ, 1 ≤ k → k ≤ η → 1 ≤ l → l ≤ ζ →
    ∑ i : Fin s, ∑ j : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j * t.c j ^ (l - 1) =
      1 / ((l : ℝ) * ((k + l : ℕ) : ℝ))

/-- **B(2s) ∧ C(s) ⇒ E(s,s)**, the implication (342m) from Theorem 342C. -/
theorem SatisfiesE_of_B_C (t : ButcherTableau s) (hB : t.SatisfiesB (2 * s))
    (hC : t.SatisfiesC s) : t.SatisfiesE s s := by
  intro k l hk1 hk2 hl1 hl2
  have hC_l : ∀ i : Fin s, ∑ j : Fin s, t.A i j * t.c j ^ (l - 1) = t.c i ^ l / (l : ℝ) := by
    intro i
    exact hC l hl1 hl2 i
  have hB_kl : ∑ i : Fin s, t.b i * t.c i ^ (k + l - 1) = 1 / ((k + l : ℕ) : ℝ) := by
    exact hB (k + l) (by omega) (by omega)
  have hfactor : ∀ i : Fin s,
      ∑ j : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j * t.c j ^ (l - 1) =
        t.b i * t.c i ^ (k - 1) * (∑ j : Fin s, t.A i j * t.c j ^ (l - 1)) := by
    intro i
    calc
      ∑ j : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j * t.c j ^ (l - 1)
          = ∑ j : Fin s, (t.b i * t.c i ^ (k - 1)) * (t.A i j * t.c j ^ (l - 1)) := by
              refine sum_congr rfl ?_
              intro j hj
              ring
      _ = t.b i * t.c i ^ (k - 1) * (∑ j : Fin s, t.A i j * t.c j ^ (l - 1)) := by
            rw [mul_sum]
  calc
    ∑ i : Fin s, ∑ j : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j * t.c j ^ (l - 1)
        = ∑ i : Fin s, t.b i * t.c i ^ (k - 1) * (∑ j : Fin s, t.A i j * t.c j ^ (l - 1)) := by
            simp [hfactor]
    _ = ∑ i : Fin s, t.b i * t.c i ^ (k - 1) * (t.c i ^ l / (l : ℝ)) := by
          simp [hC_l]
    _ = (1 / (l : ℝ)) * ∑ i : Fin s, t.b i * t.c i ^ (k + l - 1) := by
          rw [mul_sum]
          refine sum_congr rfl ?_
          intro i hi
          have hkll : k - 1 + l = k + l - 1 := by omega
          calc
            t.b i * t.c i ^ (k - 1) * (t.c i ^ l / (l : ℝ))
                = (1 / (l : ℝ)) * (t.b i * (t.c i ^ (k - 1) * t.c i ^ l)) := by ring
            _ = (1 / (l : ℝ)) * (t.b i * t.c i ^ (k + l - 1)) := by
                  rw [← pow_add, hkll]
    _ = (1 / (l : ℝ)) * (1 / ((k + l : ℕ) : ℝ)) := by rw [hB_kl]
    _ = 1 / ((l : ℝ) * ((k + l : ℕ) : ℝ)) := by
          ring_nf

/-- **B(2s) ∧ D(s) ⇒ E(s,s)**, the implication (342o) from Theorem 342C. -/
theorem SatisfiesE_of_B_D (t : ButcherTableau s) (hB : t.SatisfiesB (2 * s))
    (hD : t.SatisfiesD s) : t.SatisfiesE s s := by
  intro k l hk1 hk2 hl1 hl2
  have hD_k : ∀ j : Fin s, ∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j =
      t.b j / (k : ℝ) * (1 - t.c j ^ k) := by
    intro j
    exact hD k hk1 hk2 j
  have hB_l : ∑ j : Fin s, t.b j * t.c j ^ (l - 1) = 1 / (l : ℝ) := by
    exact hB l hl1 (by omega)
  have hB_kl : ∑ j : Fin s, t.b j * t.c j ^ (k + l - 1) = 1 / ((k + l : ℕ) : ℝ) := by
    exact hB (k + l) (by omega) (by omega)
  have hfactor : ∀ j : Fin s,
      ∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j * t.c j ^ (l - 1) =
        (∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j) * t.c j ^ (l - 1) := by
    intro j
    calc
      ∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j * t.c j ^ (l - 1)
          = ∑ i : Fin s, (t.b i * t.c i ^ (k - 1) * t.A i j) * t.c j ^ (l - 1) := by
              refine sum_congr rfl ?_
              intro i hi
              ring
      _ = (∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j) * t.c j ^ (l - 1) := by
            rw [sum_mul]
  have hsplit : ∀ j : Fin s,
      (t.b j / (k : ℝ) * (1 - t.c j ^ k)) * t.c j ^ (l - 1) =
        (1 / (k : ℝ)) * (t.b j * t.c j ^ (l - 1)) -
          (1 / (k : ℝ)) * (t.b j * t.c j ^ (k + l - 1)) := by
    intro j
    have hkll : k + (l - 1) = k + l - 1 := by omega
    calc
      (t.b j / (k : ℝ) * (1 - t.c j ^ k)) * t.c j ^ (l - 1)
          = (t.b j / (k : ℝ)) * t.c j ^ (l - 1) -
              (t.b j / (k : ℝ)) * (t.c j ^ k * t.c j ^ (l - 1)) := by
                ring
      _ = (1 / (k : ℝ)) * (t.b j * t.c j ^ (l - 1)) -
            (1 / (k : ℝ)) * (t.b j * t.c j ^ (k + l - 1)) := by
              rw [← pow_add, hkll]
              ring
  calc
    ∑ i : Fin s, ∑ j : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j * t.c j ^ (l - 1)
        = ∑ j : Fin s, (∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j) * t.c j ^ (l - 1) := by
            rw [sum_comm]
            simp [hfactor]
    _ = ∑ j : Fin s, (t.b j / (k : ℝ) * (1 - t.c j ^ k)) * t.c j ^ (l - 1) := by
          simp [hD_k]
    _ = (1 / (k : ℝ)) *
          (∑ j : Fin s, t.b j * t.c j ^ (l - 1) - ∑ j : Fin s, t.b j * t.c j ^ (k + l - 1)) := by
            calc
              ∑ j : Fin s, (t.b j / (k : ℝ) * (1 - t.c j ^ k)) * t.c j ^ (l - 1)
                  = ∑ j : Fin s,
                      ((1 / (k : ℝ)) * (t.b j * t.c j ^ (l - 1)) -
                        (1 / (k : ℝ)) * (t.b j * t.c j ^ (k + l - 1))) := by
                          simp [hsplit]
              _ = (∑ j : Fin s, (1 / (k : ℝ)) * (t.b j * t.c j ^ (l - 1))) -
                    ∑ j : Fin s, (1 / (k : ℝ)) * (t.b j * t.c j ^ (k + l - 1)) := by
                      rw [sum_sub_distrib]
              _ = (1 / (k : ℝ)) *
                    (∑ j : Fin s, t.b j * t.c j ^ (l - 1) - ∑ j : Fin s, t.b j * t.c j ^ (k + l - 1)) := by
                      rw [mul_sub, mul_sum, mul_sum]
    _ = (1 / (k : ℝ)) * (1 / (l : ℝ) - 1 / ((k + l : ℕ) : ℝ)) := by
          rw [hB_l, hB_kl]
    _ = 1 / ((l : ℝ) * ((k + l : ℕ) : ℝ)) := by
          have hk0 : (k : ℝ) ≠ 0 := by positivity
          have hl0 : (l : ℝ) ≠ 0 := by positivity
          field_simp [hk0, hl0]
          norm_num [Nat.cast_add]

/-- **B(2s) ∧ E(s,s) ⇒ C(s)**, the implication (342n) from Theorem 342C.
    Requires distinct nodes (injective c) and nonzero weights. -/
theorem SatisfiesC_of_B_E (t : ButcherTableau s) (hB : t.SatisfiesB (2 * s))
    (hE : t.SatisfiesE s s) (hc_inj : Function.Injective t.c)
    (hb_ne : ∀ i : Fin s, t.b i ≠ 0) : t.SatisfiesC s := by
  intro l hl1 hl2 i
  -- Define v_i = b_i * (∑_j A_{ij} c_j^{l-1} - c_i^l / l)  (C-defect weighted by b_i)
  -- Show v = 0 via Vandermonde, then divide by b_i ≠ 0.
  suffices hzero : ∀ i' : Fin s,
      t.b i' * ((∑ j : Fin s, t.A i' j * t.c j ^ (l - 1)) - t.c i' ^ l / (l : ℝ)) = 0 by
    have := hzero i
    have hbi : t.b i ≠ 0 := hb_ne i
    have := mul_eq_zero.mp this
    cases this with
    | inl h => exact absurd h hbi
    | inr h => linarith
  -- Apply Vandermonde: show the weighted defect vector is zero
  have hvan := @Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ℝ _ s _
    t.c (fun i' => t.b i' * ((∑ j : Fin s, t.A i' j * t.c j ^ (l - 1)) -
      t.c i' ^ l / (l : ℝ))) hc_inj
  suffices hsum : ∀ m : Fin s,
      ∑ i' : Fin s, (t.b i' * ((∑ j : Fin s, t.A i' j * t.c j ^ (l - 1)) -
        t.c i' ^ l / (l : ℝ))) * t.c i' ^ (m : ℕ) = 0 by
    intro i'
    have := hvan hsum
    exact congr_fun this i'
  intro m
  -- Distribute: b * (X - Y) * c^m = b * c^m * X - b * c^m * Y
  have hdist : ∀ i' : Fin s,
      (t.b i' * ((∑ j : Fin s, t.A i' j * t.c j ^ (l - 1)) -
        t.c i' ^ l / (l : ℝ))) * t.c i' ^ (m : ℕ) =
      t.b i' * t.c i' ^ (m : ℕ) * (∑ j : Fin s, t.A i' j * t.c j ^ (l - 1)) -
        t.b i' * t.c i' ^ (m : ℕ) * (t.c i' ^ l / (l : ℝ)) := by
    intro i'; ring
  simp_rw [hdist]
  rw [Finset.sum_sub_distrib]
  -- First sum = E(m+1, l) = 1/(l(m+1+l))
  -- Second sum = (1/l) * B(m+1+l) = (1/l) * 1/(m+1+l) = 1/(l(m+1+l))
  set m' := (m : ℕ) + 1 with hm'_def
  have hm'1 : 1 ≤ m' := by omega
  have hm'2 : m' ≤ s := by omega
  have hm'exp : m' - 1 = (m : ℕ) := by omega
  -- First sum: ∑_i b_i c_i^m * (∑_j A_{ij} c_j^{l-1})
  -- = ∑_i ∑_j b_i c_i^{m'-1} A_{ij} c_j^{l-1} = E(m', l)
  have hE_val : ∑ i' : Fin s, ∑ j : Fin s,
      t.b i' * t.c i' ^ (m : ℕ) * t.A i' j * t.c j ^ (l - 1) =
        1 / ((l : ℝ) * ((m' + l : ℕ) : ℝ)) := by
    have := hE m' l hm'1 hm'2 hl1 hl2
    rw [hm'exp] at this
    exact this
  have hsum1 : ∑ i' : Fin s, t.b i' * t.c i' ^ (m : ℕ) *
      (∑ j : Fin s, t.A i' j * t.c j ^ (l - 1)) =
        1 / ((l : ℝ) * ((m' + l : ℕ) : ℝ)) := by
    rw [← hE_val]
    refine Finset.sum_congr rfl ?_
    intro i' _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  -- Second sum: ∑_i b_i c_i^m * c_i^l / l = (1/l) * ∑_i b_i c_i^{m+l}
  -- = (1/l) * B(m+l+1) = (1/l) * 1/(m+l+1) = 1/(l(m+l+1))
  -- Note: m + l = m' - 1 + l = m' + l - 1
  have hB_ml : ∑ i' : Fin s, t.b i' * t.c i' ^ ((m : ℕ) + l) =
      1 / ((m' + l : ℕ) : ℝ) := by
    have := hB (m' + l) (by omega) (by omega)
    have hexp : m' + l - 1 = (m : ℕ) + l := by omega
    rw [hexp] at this
    exact this
  have hsum2 : ∑ i' : Fin s, t.b i' * t.c i' ^ (m : ℕ) *
      (t.c i' ^ l / (l : ℝ)) =
        1 / ((l : ℝ) * ((m' + l : ℕ) : ℝ)) := by
    have hl0 : (l : ℝ) ≠ 0 := by positivity
    calc ∑ i' : Fin s, t.b i' * t.c i' ^ (m : ℕ) * (t.c i' ^ l / (l : ℝ))
        = (1 / (l : ℝ)) * ∑ i' : Fin s, t.b i' * t.c i' ^ ((m : ℕ) + l) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i' _
          have : t.c i' ^ (m : ℕ) * t.c i' ^ l = t.c i' ^ ((m : ℕ) + l) := by
            rw [pow_add]
          rw [← this]; ring
      _ = (1 / (l : ℝ)) * (1 / ((m' + l : ℕ) : ℝ)) := by
          rw [hB_ml]
      _ = 1 / ((l : ℝ) * ((m' + l : ℕ) : ℝ)) := by ring
  linarith [hsum1, hsum2]

/-- **B(2s) ∧ E(s,s) ⇒ D(s)**, the implication (342p) from Theorem 342C.
    Requires distinct nodes (injective c). -/
theorem SatisfiesD_of_B_E (t : ButcherTableau s) (hB : t.SatisfiesB (2 * s))
    (hE : t.SatisfiesE s s) (hc_inj : Function.Injective t.c) : t.SatisfiesD s := by
  intro k hk1 hk2 j
  -- Define the defect vector: u_j = (∑_i b_i c_i^{k-1} A_{ij}) - b_j/k * (1 - c_j^k)
  -- We show u = 0 via Vandermonde uniqueness.
  -- Step 1: Show ∀ l : Fin s, ∑ j, u_j * c_j^l = 0
  -- where u_j := (∑ i, b i * c i ^ (k-1) * A i j) - b j / k * (1 - c j ^ k)
  suffices h : ∀ j : Fin s,
      (∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j) -
        t.b j / (k : ℝ) * (1 - t.c j ^ k) = 0 by
    linarith [h j]
  -- Apply Vandermonde: show defect vector is zero
  have hvan := @Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ℝ _ s _
    t.c (fun j => (∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j) -
      t.b j / (k : ℝ) * (1 - t.c j ^ k)) hc_inj
  -- Need: ∀ l : Fin s, ∑ j, u_j * c_j ^ ↑l = 0
  suffices hsum : ∀ l : Fin s,
      ∑ j : Fin s, ((∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j) -
        t.b j / (k : ℝ) * (1 - t.c j ^ k)) * t.c j ^ (l : ℕ) = 0 by
    intro j'
    have := hvan hsum
    exact congr_fun this j'
  intro l
  -- Distribute: (a - b) * c = a*c - b*c, then split sum
  have hsplit : ∀ j : Fin s,
      ((∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j) -
        t.b j / (k : ℝ) * (1 - t.c j ^ k)) * t.c j ^ (l : ℕ) =
      (∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j) * t.c j ^ (l : ℕ) -
        (t.b j / (k : ℝ) * (1 - t.c j ^ k)) * t.c j ^ (l : ℕ) := by
    intro j; ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib]
  -- Both parts equal 1/((l+1)(k+l+1)), so they cancel.
  have hl1 : 1 ≤ (l : ℕ) + 1 := by omega
  have hl2 : (l : ℕ) + 1 ≤ s := by omega
  -- First sum: ∑_j (∑_i b_i c_i^{k-1} A_{ij}) * c_j^l
  -- = ∑_i ∑_j b_i c_i^{k-1} A_{ij} c_j^l = E(k, l+1)
  -- The l-th Vandermonde equation: exponent is ↑l = 0,...,s-1, corresponding to B/E index l+1
  set l' := (l : ℕ) + 1 with hl'_def
  have hl'1 : 1 ≤ l' := by omega
  have hl'2 : l' ≤ s := by omega
  have hl'exp : l' - 1 = (l : ℕ) := by omega
  have hE_val : ∑ i : Fin s, ∑ j : Fin s,
      t.b i * t.c i ^ (k - 1) * t.A i j * t.c j ^ (l : ℕ) =
        1 / ((l' : ℝ) * ((k + l' : ℕ) : ℝ)) := by
    have := hE k l' hk1 hk2 hl'1 hl'2
    rw [hl'exp] at this
    exact this
  have hsum1 : ∑ j : Fin s, (∑ i : Fin s, t.b i * t.c i ^ (k - 1) * t.A i j) *
      t.c j ^ (l : ℕ) =
        1 / ((l' : ℝ) * ((k + l' : ℕ) : ℝ)) := by
    rw [← hE_val]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_mul]
  -- Second sum: ∑_j (b_j / k * (1 - c_j^k)) * c_j^l
  -- = (1/k) * (∑_j b_j c_j^l - ∑_j b_j c_j^{k+l})
  -- = (1/k) * (B(l+1) - B(k+l+1))
  -- = (1/k) * (1/(l+1) - 1/(k+l+1))
  -- = 1/((l+1)(k+l+1))
  have hB_l' : ∑ j : Fin s, t.b j * t.c j ^ (l : ℕ) = 1 / (l' : ℝ) := by
    have := hB l' hl'1 (by omega)
    rw [hl'exp] at this
    exact this
  have hB_kl' : ∑ j : Fin s, t.b j * t.c j ^ (k + (l : ℕ)) =
      1 / ((k + l' : ℕ) : ℝ) := by
    have := hB (k + l') (by omega) (by omega)
    have hexp : k + l' - 1 = k + (l : ℕ) := by omega
    rw [hexp] at this
    exact this
  have hsum2 : ∑ j : Fin s, (t.b j / (k : ℝ) * (1 - t.c j ^ k)) * t.c j ^ (l : ℕ) =
      1 / ((l' : ℝ) * ((k + l' : ℕ) : ℝ)) := by
    have hk0 : (k : ℝ) ≠ 0 := by positivity
    have hl0 : (l' : ℝ) ≠ 0 := by positivity
    calc ∑ j : Fin s, (t.b j / (k : ℝ) * (1 - t.c j ^ k)) * t.c j ^ (l : ℕ)
        = ∑ j : Fin s, (1 / (k : ℝ)) * (t.b j * t.c j ^ (l : ℕ) -
            t.b j * t.c j ^ (k + (l : ℕ))) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          have : t.c j ^ k * t.c j ^ (l : ℕ) = t.c j ^ (k + (l : ℕ)) := by
            rw [pow_add]
          rw [← this]; ring
      _ = (1 / (k : ℝ)) * (∑ j : Fin s, t.b j * t.c j ^ (l : ℕ) -
            ∑ j : Fin s, t.b j * t.c j ^ (k + (l : ℕ))) := by
          rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (1 / (k : ℝ)) * (1 / (l' : ℝ) - 1 / ((k + l' : ℕ) : ℝ)) := by
          rw [hB_l', hB_kl']
      _ = 1 / ((l' : ℝ) * ((k + l' : ℕ) : ℝ)) := by
          field_simp [hk0, hl0]
          norm_num [Nat.cast_add]
  linarith [hsum1, hsum2]

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

/-! ## Tree-Based Order ↔ Simplifying Assumptions (Theorem 342C, equations j/k/l)

The connection between tree-based order G(p) and the simplifying assumptions B, C, D, E.
- 342j: G(p) ⇒ B(p) — tree-based order implies B
- 342k: G(2n) ⇒ E(n,n) — tree-based order implies E
- 342l: B(2n) ∧ C(n) ∧ D(n) ⇒ G(2n) — simplifying assumptions imply tree-based order

Reference: Iserles, Theorem 342C. -/

/-- The bushy tree of order `k`: a root with `k-1` leaf children.
For k ≤ 1, returns `.leaf` (order 1). For k ≥ 2, returns
`.node (List.replicate (k-1) .leaf)` which has order k.

This is the tree whose tree condition corresponds to B(k). -/
private def bushyTree : ℕ → BTree
  | 0 => .leaf
  | 1 => .leaf
  | (n + 2) => .node (List.replicate (n + 1) .leaf)

private theorem foldr_order_replicate_leaf (n : ℕ) :
    List.foldr (fun (t : BTree) (acc : ℕ) => t.order + acc) 0 (List.replicate n .leaf) = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, BTree.order_leaf, ih]; omega

private theorem bushyTree_order (k : ℕ) (hk : 1 ≤ k) :
    (bushyTree k).order = k := by
  match k, hk with
  | 1, _ => simp [bushyTree, BTree.order_leaf]
  | k + 2, _ => simp [bushyTree, BTree.order_node, foldr_order_replicate_leaf]; omega

private theorem foldr_density_replicate_leaf (n : ℕ) :
    List.foldr (fun (t : BTree) (acc : ℕ) => t.density * acc) 1 (List.replicate n .leaf) = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, BTree.density_leaf, ih]

private theorem bushyTree_density (k : ℕ) (hk : 1 ≤ k) :
    (bushyTree k).density = k := by
  match k, hk with
  | 1, _ => simp [bushyTree, BTree.density_leaf]
  | k + 2, _ =>
    simp [bushyTree, BTree.density_node, BTree.order_node,
          foldr_order_replicate_leaf, foldr_density_replicate_leaf]; omega

private theorem foldr_ew_replicate_leaf (tab : ButcherTableau s) (n : ℕ) (i : Fin s) :
    List.foldr (fun (t : BTree) (acc : ℝ) =>
      acc * (∑ k : Fin s, tab.A i k * tab.elementaryWeight t k)) 1
      (List.replicate n .leaf) = (∑ k : Fin s, tab.A i k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.replicate, elementaryWeight_leaf, ih]
    ring

private theorem bushyTree_ew (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent)
    (k : ℕ) (hk : 2 ≤ k) (i : Fin s) :
    tab.elementaryWeight (bushyTree k) i = tab.c i ^ (k - 1) := by
  match k, hk with
  | k + 2, _ =>
    simp only [bushyTree, elementaryWeight]
    rw [foldr_ew_replicate_leaf]
    have : ∑ j : Fin s, tab.A i j = tab.c i := (hrc i).symm
    rw [this, show k + 2 - 1 = k + 1 from by omega]

private theorem satisfiesTreeCondition_bushyTree (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (k : ℕ) (hk : 1 ≤ k) :
    tab.satisfiesTreeCondition (bushyTree k) ↔
    ∑ i : Fin s, tab.b i * tab.c i ^ (k - 1) = 1 / (k : ℝ) := by
  simp only [satisfiesTreeCondition, bushyTree_density k hk]
  have hew : ∀ i : Fin s, tab.elementaryWeight (bushyTree k) i = tab.c i ^ (k - 1) := by
    intro i
    match k, hk with
    | 1, _ => simp [bushyTree, elementaryWeight_leaf]
    | k + 2, _ => exact bushyTree_ew tab hrc _ (by omega) i
  simp_rw [hew]

/-- **(342j)** `G(p) ⇒ B(p)`: tree-based order p implies B(p).
Reference: Iserles, Theorem 342C, equation (342j). -/
theorem SatisfiesB_of_hasTreeOrder (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (p : ℕ)
    (hG : tab.hasTreeOrder p) : tab.SatisfiesB p := by
  intro k hk1 hkp
  have hord : (bushyTree k).order = k := bushyTree_order k hk1
  have hle : (bushyTree k).order ≤ p := by omega
  exact (satisfiesTreeCondition_bushyTree tab hrc k hk1).mp (hG (bushyTree k) hle)

/-! ### 342k: G(2n) ⇒ E(n,n) -/

/-- The branched tree for the E(k,l) condition: a root with k-1 leaf
children and one bushy child of order l. Has order k+l. -/
private def branchedTree (k l : ℕ) : BTree :=
  .node (List.replicate (k - 1) .leaf ++ [bushyTree l])

private theorem foldr_order_replicate_leaf_init (n init : ℕ) :
    List.foldr (fun (t : BTree) (acc : ℕ) => t.order + acc) init
      (List.replicate n .leaf) = n + init := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, BTree.order_leaf, ih]; omega

private theorem branchedTree_order (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (branchedTree k l).order = k + l := by
  simp only [branchedTree, BTree.order_node, List.foldr_append, List.foldr_cons, List.foldr_nil,
             bushyTree_order l hl, foldr_order_replicate_leaf_init]
  omega

private theorem foldr_density_replicate_leaf_init (n init : ℕ) :
    List.foldr (fun (t : BTree) (acc : ℕ) => t.density * acc) init
      (List.replicate n .leaf) = init := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate, BTree.density_leaf, ih]

private theorem branchedTree_density (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    (branchedTree k l).density = l * (k + l) := by
  simp only [branchedTree, BTree.density_node, BTree.order_node,
             List.foldr_append, List.foldr_cons, List.foldr_nil,
             bushyTree_density l hl, bushyTree_order l hl,
             foldr_order_replicate_leaf_init, foldr_density_replicate_leaf_init,
             Nat.add_zero, Nat.mul_one]
  have : 1 + (k - 1 + l) = k + l := by omega
  rw [this]; ring

private theorem foldr_ew_replicate_leaf_init (tab : ButcherTableau s)
    (n : ℕ) (i : Fin s) (init : ℝ) :
    List.foldr (fun (t : BTree) (acc : ℝ) =>
      acc * (∑ k : Fin s, tab.A i k * tab.elementaryWeight t k)) init
      (List.replicate n .leaf) = init * (∑ k : Fin s, tab.A i k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [List.replicate, elementaryWeight_leaf, ih]
    ring

private theorem branchedTree_ew (tab : ButcherTableau s) (hrc : tab.IsRowSumConsistent)
    (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (i : Fin s) :
    tab.elementaryWeight (branchedTree k l) i =
    tab.c i ^ (k - 1) * (∑ j : Fin s, tab.A i j * tab.c j ^ (l - 1)) := by
  have hew : ∀ j : Fin s,
      tab.elementaryWeight (bushyTree l) j = tab.c j ^ (l - 1) := by
    intro j
    match l, hl with
    | 1, _ => simp [bushyTree, elementaryWeight_leaf]
    | l + 2, _ => exact bushyTree_ew tab hrc _ (by omega) j
  simp only [branchedTree, elementaryWeight]
  rw [List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil]
  rw [foldr_ew_replicate_leaf_init]
  simp only [(hrc i).symm]
  simp_rw [hew]
  ring

private theorem satisfiesTreeCondition_branchedTree (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    tab.satisfiesTreeCondition (branchedTree k l) ↔
    ∑ i : Fin s, ∑ j : Fin s,
      tab.b i * tab.c i ^ (k - 1) * tab.A i j * tab.c j ^ (l - 1) =
      1 / ((l : ℝ) * ((k + l : ℕ) : ℝ)) := by
  simp only [satisfiesTreeCondition, branchedTree_density k l hk hl,
             branchedTree_ew tab hrc k l hk hl]
  have hsum : ∀ i : Fin s,
      tab.b i * (tab.c i ^ (k - 1) * ∑ j, tab.A i j * tab.c j ^ (l - 1)) =
      ∑ j, tab.b i * tab.c i ^ (k - 1) * tab.A i j * tab.c j ^ (l - 1) := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hsum]
  push_cast [Nat.cast_mul]
  exact Iff.rfl

/-- **(342k)** `G(2n) ⇒ E(n,n)`: tree-based order 2n implies E(n,n).
Reference: Iserles, Theorem 342C, equation (342k). -/
theorem SatisfiesE_of_hasTreeOrder (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (n : ℕ)
    (hG : tab.hasTreeOrder (2 * n)) : tab.SatisfiesE n n := by
  intro k l hk1 hk2 hl1 hl2
  have hord : (branchedTree k l).order = k + l := branchedTree_order k l hk1 hl1
  have hle : (branchedTree k l).order ≤ 2 * n := by omega
  exact (satisfiesTreeCondition_branchedTree tab hrc k l hk1 hl1).mp (hG (branchedTree k l) hle)

/-! ### 342l: B(2n) ∧ C(n) ∧ D(n) ⇒ G(2n) -/

private def childrenOf : BTree → List BTree
  | .leaf => []
  | .node children => children

/-- Product of the child densities appearing in `density_node`. -/
private def childDensityProd : BTree → ℕ
  | .leaf => 1
  | .node children => children.foldr (fun t acc => t.density * acc) 1

/-- For any tree, `density = order * childDensityProd`. -/
private theorem density_eq_order_mul_childDensityProd (t : BTree) :
    t.density = t.order * childDensityProd t := by
  cases t with
  | leaf => simp [childDensityProd]
  | node children => simp [BTree.density_node, childDensityProd]

/-- A child of a node has order strictly less than the node's order. -/
private theorem child_order_lt_of_mem {children : List BTree} {ch : BTree}
    (hmem : ch ∈ children) :
    ch.order < (BTree.node children).order := by
  simp only [BTree.order_node]
  have : ch.order ≤ children.foldr (fun t n => t.order + n) 0 := by
    induction children with
    | nil => simp at hmem
    | cons hd tl ih =>
      simp only [List.foldr]
      cases hmem with
      | head => omega
      | tail _ htl => have := ih htl; omega
  omega

/-- A member's order is at most the foldr order sum. -/
private theorem single_mem_order_le_foldr {children : List BTree} {ch : BTree}
    (hmem : ch ∈ children) :
    ch.order ≤ children.foldr (fun t n => t.order + n) 0 := by
  induction children with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.foldr]
    cases hmem with
    | head => omega
    | tail _ htl => have := ih htl; omega

/-- If two distinct elements are in a list, their orders sum to at most the foldr order sum. -/
private theorem two_distinct_order_le_foldr {children : List BTree} {ch tb : BTree}
    (hch : ch ∈ children) (htb : tb ∈ children) (hne : ch ≠ tb) :
    ch.order + tb.order ≤ children.foldr (fun t n => t.order + n) 0 := by
  induction children with
  | nil => simp at hch
  | cons hd tl ih =>
    simp only [List.foldr]
    simp only [List.mem_cons] at hch htb
    rcases hch with rfl | hch_tl
    · rcases htb with rfl | htb_tl
      · exact absurd rfl hne
      · have := single_mem_order_le_foldr htb_tl; omega
    · rcases htb with rfl | htb_tl
      · have := single_mem_order_le_foldr hch_tl; omega
      · have := ih hch_tl htb_tl; omega

/-- The childDensityProd is positive. -/
private theorem childDensityProd_pos (t : BTree) : 0 < childDensityProd t := by
  cases t with
  | leaf => simp [childDensityProd]
  | node children =>
    simp only [childDensityProd]
    induction children with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.foldr]
      exact Nat.mul_pos (BTree.density_pos hd) ih

/-- For each child, the IH-simplified A-weighted sum equals `cᵢ^(order) / density`. -/
private theorem ew_factor_simplified (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (n : ℕ) (hC : tab.SatisfiesC n)
    (ch : BTree) (hord : ch.order ≤ n) (hord_pos : 1 ≤ ch.order) (i : Fin s)
    (hew : ∀ j : Fin s,
      tab.elementaryWeight ch j = tab.c j ^ (ch.order - 1) / (childDensityProd ch : ℝ)) :
    ∑ k : Fin s, tab.A i k * tab.elementaryWeight ch k =
    tab.c i ^ ch.order / ch.density := by
  simp_rw [hew, mul_div_assoc']
  rw [← Finset.sum_div]
  have hC_app := hC ch.order hord_pos hord i
  rw [hC_app, density_eq_order_mul_childDensityProd ch, Nat.cast_mul, div_div]

/-- Product of densities in a children list is positive. -/
private theorem foldr_density_prod_pos (children : List BTree) :
    0 < children.foldr (fun t n => t.density * n) 1 := by
  induction children with
  | nil => simp
  | cons hd tl ih => simp only [List.foldr]; exact Nat.mul_pos (BTree.density_pos hd) ih

/-- Product of ew-factors over a children list simplifies to a power / product of densities.
    Each child's A-weighted ew sum is `cᵢ^(child.order) / child.density`. -/
private theorem foldr_ew_simplified (tab : ButcherTableau s) (i : Fin s) (c_i : ℝ)
    (children : List BTree)
    (hfact : ∀ ch ∈ children,
      ∑ k : Fin s, tab.A i k * tab.elementaryWeight ch k =
      c_i ^ ch.order / (ch.density : ℝ)) :
    children.foldr (fun t acc =>
      acc * (∑ k : Fin s, tab.A i k * tab.elementaryWeight t k)) 1 =
    c_i ^ (children.foldr (fun t n => t.order + n) 0) /
    (↑(children.foldr (fun (t : BTree) (n : ℕ) => t.density * n) 1) : ℝ) := by
  induction children with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldr]
    have ih' := ih (fun ch hmem => hfact ch (List.mem_cons_of_mem hd hmem))
    rw [ih']
    have hhd := hfact hd (by simp)
    rw [hhd]
    rw [div_mul_div_comm, ← pow_add]
    congr 1
    · ring
    · push_cast; ring

/-- Elementary weights simplify to powers of `cᵢ` divided by the product of child
densities under the `C(n)` simplifying assumption. -/
private theorem elementaryWeight_simplified_of_C (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (n : ℕ) (hC : tab.SatisfiesC n)
    (t : BTree) (ht : t.order ≤ n + 1) (i : Fin s) :
    tab.elementaryWeight t i = tab.c i ^ (t.order - 1) / (childDensityProd t : ℝ) := by
  refine Nat.strongRecOn (n := t.order)
    (motive := fun m => ∀ u : BTree, u.order = m → u.order ≤ n + 1 → ∀ j : Fin s,
      tab.elementaryWeight u j = tab.c j ^ (u.order - 1) / (childDensityProd u : ℝ))
    ?_ t rfl ht i
  intro m ih_ord u hu_eq hu_le j
  cases u with
  | leaf => simp [childDensityProd]
  | node children =>
    simp only [elementaryWeight, childDensityProd, BTree.order_node]
    -- Simplify the exponent: 1 + ∑ orders - 1 = ∑ orders
    have hexp : 1 + children.foldr (fun t n => t.order + n) 0 - 1 =
        children.foldr (fun t n => t.order + n) 0 := by omega
    rw [hexp]
    -- Use foldr_ew_simplified
    apply foldr_ew_simplified tab j (tab.c j) children
    intro ch hmem
    -- Need: ∑ k, A j k * ew ch k = c j ^ ch.order / ch.density
    have hch_lt : ch.order < m := by
      have := child_order_lt_of_mem hmem; omega
    have hch_le_n : ch.order ≤ n := by omega
    have hch_le_n1 : ch.order ≤ n + 1 := by omega
    have hch_pos : 1 ≤ ch.order := BTree.order_pos ch
    -- Apply IH to get elementaryWeight_simplified for the child
    have hew_ch : ∀ k : Fin s,
        tab.elementaryWeight ch k = tab.c k ^ (ch.order - 1) / (childDensityProd ch : ℝ) :=
      fun k => ih_ord ch.order hch_lt ch rfl hch_le_n1 k
    exact ew_factor_simplified tab hrc n hC ch hch_le_n hch_pos j hew_ch

/-- Under `C(n)`, the tree kernel simplifies to `cᵢ^|t| / γ(t)` for all trees of
order at most `n`. -/
private theorem ew_simplified_of_C (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (n : ℕ) (hC : tab.SatisfiesC n)
    (t : BTree) (ht : t.order ≤ n) (i : Fin s) :
    ∑ k : Fin s, tab.A i k * tab.elementaryWeight t k =
    tab.c i ^ t.order / t.density := by
  have hle : t.order ≤ n + 1 := by omega
  simp_rw [elementaryWeight_simplified_of_C tab hrc n hC t hle, mul_div_assoc']
  rw [← Finset.sum_div]
  have hord_pos : 1 ≤ t.order := BTree.order_pos t
  have hC_app := hC t.order hord_pos ht i
  rw [hC_app, density_eq_order_mul_childDensityProd t, Nat.cast_mul, div_div]

/-- If every child of `t` has order at most `n`, then `B(2n)` and `C(n)` imply the
tree order condition for `t`. -/
private theorem tree_cond_all_small (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (n : ℕ)
    (hB : tab.SatisfiesB (2 * n)) (hC : tab.SatisfiesC n)
    (t : BTree) (ht : t.order ≤ 2 * n)
    (hsmall : ∀ u ∈ childrenOf t, u.order ≤ n) :
    tab.satisfiesTreeCondition t := by
  cases t with
  | leaf =>
    simp only [satisfiesTreeCondition, elementaryWeight_leaf, BTree.density_leaf, Nat.cast_one]
    simp only [BTree.order_leaf] at ht
    simpa using hB 1 le_rfl ht
  | node children =>
    -- hsmall now gives: ∀ u ∈ children, u.order ≤ n
    simp only [childrenOf] at hsmall
    -- Each child's ew simplifies under C(n)
    have hew_i : ∀ i : Fin s,
        tab.elementaryWeight (.node children) i =
        tab.c i ^ ((BTree.node children).order - 1) /
        (childDensityProd (.node children) : ℝ) := by
      intro i
      simp only [elementaryWeight, childDensityProd, BTree.order_node]
      have hexp : 1 + children.foldr (fun t n => t.order + n) 0 - 1 =
          children.foldr (fun t n => t.order + n) 0 := by omega
      rw [hexp]
      apply foldr_ew_simplified tab i (tab.c i) children
      intro ch hmem
      have hch_le := hsmall ch hmem
      exact ew_factor_simplified tab hrc n hC ch hch_le (BTree.order_pos ch) i
        (fun k => elementaryWeight_simplified_of_C tab hrc n hC ch (by omega) k)
    -- Now: ∑ b_i * ew(t, i) = (1/childDensityProd) * ∑ b_i * c_i^(t.order-1)
    simp only [satisfiesTreeCondition]
    simp_rw [hew_i, mul_div_assoc']
    rw [← Finset.sum_div]
    -- Apply B(t.order)
    have hB_app := hB (BTree.node children).order (BTree.order_pos _) ht
    rw [hB_app, density_eq_order_mul_childDensityProd, Nat.cast_mul, div_div]

/-- Generalized tree condition: under B(2n), C(n), D(n), for any tree t and
exponent q with q + t.order ≤ 2n, the q-weighted tree sum evaluates to
  r(t) / ((q + r(t)) · γ(t))
where r(t) = t.order and γ(t) = t.density.
When q = 0 this reduces to the standard tree condition 1/γ(t). -/
private theorem gen_tree_cond (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (n : ℕ)
    (hB : tab.SatisfiesB (2 * n)) (hC : tab.SatisfiesC n) (hD : tab.SatisfiesD n)
    (q : ℕ) (t : BTree) (hqt : q + t.order ≤ 2 * n) :
    ∑ i : Fin s, tab.b i * tab.c i ^ q * tab.elementaryWeight t i =
    (t.order : ℝ) / ((q + t.order) * (t.density : ℝ)) := by
  refine Nat.strongRecOn (n := t.order)
    (motive := fun m => ∀ (q' : ℕ) (u : BTree), u.order = m → q' + u.order ≤ 2 * n →
      ∑ i : Fin s, tab.b i * tab.c i ^ q' * tab.elementaryWeight u i =
      (u.order : ℝ) / ((q' + u.order) * (u.density : ℝ)))
    ?_ q t rfl hqt
  intro m ih_gen q' u hu_eq hq'u
  cases u with
  | leaf =>
    -- ∑ bᵢ cᵢ^q' · 1 = 1 / ((q'+1) · 1) = 1/(q'+1)
    simp only [elementaryWeight_leaf, mul_one, BTree.order_leaf, BTree.density_leaf,
               Nat.cast_one, mul_one]
    simp only [BTree.order_leaf] at hu_eq hq'u
    have hq'_bound : q' + 1 ≤ 2 * n := by omega
    have hB_app := hB (q' + 1) (by omega) hq'_bound
    simp only [show q' + 1 - 1 = q' from by omega] at hB_app
    convert hB_app using 1
    simp [Nat.cast_add, Nat.cast_one]
  | node children =>
    simp only at *
    -- Case split: all children small vs one big child
    by_cases hall_small : ∀ ch ∈ children, ch.order ≤ n
    · -- All children have order ≤ n: use ew simplification + B
      have hew_i : ∀ j : Fin s,
          tab.elementaryWeight (.node children) j =
          tab.c j ^ ((BTree.node children).order - 1) /
          (childDensityProd (.node children) : ℝ) := by
        intro j
        simp only [elementaryWeight, childDensityProd, BTree.order_node]
        have hexp : 1 + children.foldr (fun t n => t.order + n) 0 - 1 =
            children.foldr (fun t n => t.order + n) 0 := by omega
        rw [hexp]
        apply foldr_ew_simplified tab j (tab.c j) children
        intro ch hmem
        have hch_le := hall_small ch hmem
        exact ew_factor_simplified tab hrc n hC ch hch_le (BTree.order_pos ch) j
          (fun k => elementaryWeight_simplified_of_C tab hrc n hC ch (by omega) k)
      simp_rw [hew_i, mul_div_assoc']
      have hpow : ∀ j : Fin s, tab.b j * tab.c j ^ q' *
          tab.c j ^ ((BTree.node children).order - 1) =
          tab.b j * tab.c j ^ (q' + ((BTree.node children).order - 1)) := by
        intro j; rw [mul_assoc, ← pow_add]
      simp_rw [hpow]
      rw [← Finset.sum_div]
      have hord := BTree.order_pos (BTree.node children)
      have hq'r_bound : q' + (BTree.node children).order ≤ 2 * n := by omega
      have hkval : q' + ((BTree.node children).order - 1) =
          q' + (BTree.node children).order - 1 := by omega
      have hB_app := hB (q' + (BTree.node children).order) (by omega) hq'r_bound
      rw [show q' + (BTree.node children).order - 1 = q' + ((BTree.node children).order - 1)
        from by omega] at hB_app
      rw [hB_app, density_eq_order_mul_childDensityProd, Nat.cast_mul]
      have hord_ne : ((BTree.node children).order : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hcdp_ne : (childDensityProd (.node children) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (childDensityProd_pos _))
      field_simp
      push_cast
      ring
    · -- One big child case: use D(n) and recursive gen_tree_cond
      push_neg at hall_small
      obtain ⟨tb, htb_mem, htb_big⟩ := hall_small
      -- Separate children into smalls and the big child tb
      -- tb.order > n, all others have order ≤ n (since at most one child can have order > n)
      have htb_unique : ∀ ch ∈ children, n < ch.order → ch = tb := by
        intro ch hch hch_big
        by_contra hne
        have h_combined := two_distinct_order_le_foldr hch htb_mem hne
        have hord_eq := BTree.order_node children
        -- node.order = 1 + foldr ≥ 1 + ch.order + tb.order ≥ 1 + 2(n+1) = 2n+3 > 2n
        omega
      sorry  -- Main algebraic proof using D(n) and ih_gen

/-- The remaining case of Theorem 342l: exactly one child of `t` can have order
strictly larger than `n`, and this is where the `D(n)` simplification is used. -/
private theorem tree_cond_one_big (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (n : ℕ)
    (hB : tab.SatisfiesB (2 * n)) (hC : tab.SatisfiesC n)
    (hD : tab.SatisfiesD n)
    (t : BTree)
    (_ih : ∀ u : BTree, u.order < t.order → u.order ≤ 2 * n →
      tab.satisfiesTreeCondition u)
    (ht : t.order ≤ 2 * n)
    (hbig : ∃ u ∈ childrenOf t, n < u.order) :
    tab.satisfiesTreeCondition t := by
  -- Use the generalized tree condition with q = 0
  have hgen := gen_tree_cond tab hrc n hB hC hD 0 t (by omega)
  simp only [pow_zero, mul_one] at hgen
  simp only [satisfiesTreeCondition]
  rw [hgen]
  -- goal: ↑t.order / ((↑0 + ↑t.order) * ↑t.density) = 1 / ↑t.density
  have hord_ne : (t.order : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (BTree.order_pos t))
  have hdens_ne : (t.density : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (BTree.density_pos t))
  simp only [Nat.cast_zero, zero_add]
  field_simp

/-- **(342l)** `B(2n) ∧ C(n) ∧ D(n) ⇒ G(2n)`: the simplifying assumptions
together imply all tree-based order conditions up to order 2n.
Reference: Iserles, Theorem 342C, equation (342l). -/
theorem hasTreeOrder_of_B_C_D (tab : ButcherTableau s)
    (hrc : tab.IsRowSumConsistent) (n : ℕ)
    (hB : tab.SatisfiesB (2 * n)) (hC : tab.SatisfiesC n) (hD : tab.SatisfiesD n) :
    tab.hasTreeOrder (2 * n) := by
  intro t ht
  classical
  refine Nat.strongRecOn (n := t.order)
    (motive := fun m => ∀ u : BTree, u.order = m → u.order ≤ 2 * n →
      tab.satisfiesTreeCondition u) ?_ t rfl ht
  intro m ih u hu_eq hu_le
  by_cases hbig : ∃ v ∈ childrenOf u, n < v.order
  · exact tree_cond_one_big tab hrc n hB hC hD u
      (fun v hvlt hvle => ih v.order (by simpa [hu_eq] using hvlt) v rfl hvle)
      hu_le hbig
  · refine tree_cond_all_small tab hrc n hB hC u hu_le ?_
    intro v hv
    by_contra hvgt
    exact hbig ⟨v, hv, lt_of_not_ge hvgt⟩

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
