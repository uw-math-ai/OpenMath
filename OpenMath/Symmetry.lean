import OpenMath.GaussLegendre3
import OpenMath.LobattoIIIA3
import OpenMath.LobattoIIIB
import OpenMath.LobattoIIIB3
import OpenMath.LobattoIIIC3
import OpenMath.RadauIA2
import OpenMath.RadauIA3
import OpenMath.SDIRK3

/-!
# RK Method Symmetry (Section 2.5)

## Definition

A Runge–Kutta method with Butcher tableau (A, b, c) is **symmetric** (or **self-adjoint**)
if applying it with step size h followed by step size −h returns to the starting point.

The algebraic characterization is (0-based indexing with `Fin.rev`):
  A[i][j] + A[rev(i)][rev(j)] = b[j]   for all i, j
  b[i] = b[rev(i)]                       for all i
  c[i] + c[rev(i)] = 1                   for all i

## Key Results

- **Gauss–Legendre methods** are symmetric (implicit midpoint, GL2, GL3)
- **Lobatto IIIA/IIIB** are symmetric; Lobatto IIIC is NOT
- **Radau methods** are NOT symmetric (asymmetric weights)
- **SDIRK methods** are NOT symmetric
- Symmetric methods have even order (Theorem 2.8, Iserles)
- Symmetric methods are never L-stable

## The Adjoint Method

The **adjoint** of (A, b, c) is (A*, b*, c*) with:
  a*[i][j] = b[j] − a[rev(i)][rev(j)],   b*[i] = b[rev(i)],   c*[i] = 1 − c[rev(i)]

A method is symmetric iff it equals its own adjoint.

Reference: Iserles, *A First Course in the Numerical Analysis of Differential Equations*,
Section 2.5; Hairer–Nørsett–Wanner, *Solving ODEs I*, Section II.8.
-/

open Finset Real Filter

namespace ButcherTableau

variable {s : ℕ}

/-! ## Symmetry Definition -/

/-- An RK method is **symmetric** (self-adjoint) if:
  1. b[i] = b[rev(i)] (symmetric weights)
  2. c[i] + c[rev(i)] = 1 (symmetric nodes about 1/2)
  3. A[i][j] + A[rev(i)][rev(j)] = b[j] (the defining symmetry condition)

  A symmetric method applied with step h then step −h recovers the initial value.
  Reference: Iserles, Definition 2.5 / Hairer–Nørsett–Wanner, Definition II.8.2. -/
structure IsSymmetric (t : ButcherTableau s) : Prop where
  symm_weights : ∀ i : Fin s, t.b i = t.b i.rev
  symm_nodes : ∀ i : Fin s, t.c i + t.c i.rev = 1
  symm_tableau : ∀ i j : Fin s, t.A i j + t.A i.rev j.rev = t.b j

/-! ## The Adjoint Method -/

/-- The **adjoint** (or **dual**) of a Butcher tableau.
  Given (A, b, c), the adjoint has:
    A*[i][j] = b[j] − A[rev(i)][rev(j)]
    b*[i] = b[rev(i)]
    c*[i] = 1 − c[rev(i)]
  Reference: Hairer–Nørsett–Wanner, Definition II.8.1. -/
noncomputable def adjoint (t : ButcherTableau s) : ButcherTableau s where
  A := fun i j => t.b j - t.A i.rev j.rev
  b := fun i => t.b i.rev
  c := fun i => 1 - t.c i.rev

/-- A method is symmetric iff A = A* (it equals its adjoint). -/
theorem isSymmetric_iff_eq_adjoint (t : ButcherTableau s) :
    t.IsSymmetric ↔
    (∀ i j : Fin s, t.A i j = (t.adjoint).A i j) ∧
    (∀ i : Fin s, t.b i = (t.adjoint).b i) ∧
    (∀ i : Fin s, t.c i = (t.adjoint).c i) := by
  constructor
  · intro ⟨hw, hn, ht⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i j; simp only [adjoint]; linarith [ht i j]
    · exact hw
    · intro i; simp only [adjoint]; linarith [hn i]
  · intro ⟨hA, hb, hc⟩
    refine ⟨hb, ?_, ?_⟩
    · intro i; simp only [adjoint] at hc; linarith [hc i]
    · intro i j; simp only [adjoint] at hA; linarith [hA i j]

/-- The adjoint of the adjoint recovers the original tableau entries. -/
theorem adjoint_adjoint (t : ButcherTableau s) :
    ∀ i j : Fin s, (t.adjoint.adjoint).A i j = t.A i j := by
  intro i j; simp only [adjoint, Fin.rev_rev]; ring

/-! ## Symmetry Implies Even Order

Symmetric methods satisfy the remarkable property that their order is always even.
The key insight: if a method is symmetric and consistent, then ∑ bᵢcᵢ = 1/2
follows automatically from node and weight symmetry.

Reference: Iserles, Theorem 2.8; Hairer–Nørsett–Wanner, Theorem II.8.4. -/

/-- **Symmetric consistent methods have order ≥ 2.**
  From the node symmetry cᵢ + c_{rev(i)} = 1 and weight symmetry bᵢ = b_{rev(i)},
  the second-order condition ∑ bᵢcᵢ = 1/2 follows.
  Reference: Iserles, Theorem 2.8. -/
theorem IsSymmetric.order2_of_consistent {t : ButcherTableau s}
    (hs : t.IsSymmetric) (hc : t.order1) : t.HasOrderGe2 := by
  refine ⟨hc, ?_⟩
  simp only [order2]
  -- Key: 2·∑ bᵢcᵢ = ∑ bᵢcᵢ + ∑ b_{rev(i)}c_{rev(i)}
  --               = ∑ bᵢcᵢ + ∑ bᵢc_{rev(i)}    (weight symmetry)
  --               = ∑ bᵢ(cᵢ + c_{rev(i)})
  --               = ∑ bᵢ · 1 = 1
  have step1 : ∑ i : Fin s, t.b i * t.c i =
      ∑ i : Fin s, t.b i.rev * t.c i.rev :=
    (Equiv.sum_comp Fin.revPerm (fun i => t.b i * t.c i)).symm
  have step2 : ∑ i : Fin s, t.b i.rev * t.c i.rev =
      ∑ i : Fin s, t.b i * t.c i.rev := by
    congr 1; ext i; rw [← hs.symm_weights i]
  have step3 : 2 * ∑ i : Fin s, t.b i * t.c i = 1 := by
    have : ∑ i : Fin s, t.b i * t.c i + ∑ i : Fin s, t.b i * t.c i.rev = 1 := by
      rw [← Finset.sum_add_distrib]
      conv_rhs => rw [← hc]
      congr 1; ext i; rw [← mul_add, hs.symm_nodes i, mul_one]
    linarith [step1, step2]
  linarith

/-! ## Symmetric + Order 3 implies Order 4 (Nørsett's Even-Order Theorem)

The key identity: for a symmetric, row-sum consistent method,
  f(i) := ∑ⱼ aᵢⱼcⱼ satisfies f(rev(i)) = f(i) − cᵢ + 1/2.
This follows from the tableau symmetry A[i][j] + A[rev(i)][rev(j)] = b[j]
combined with the node symmetry c[rev(i)] = 1 − c[i].

Using this identity and the pairing trick i ↔ rev(i), all four fourth-order
conditions can be derived from the third-order conditions.

Reference: Iserles, Theorem 2.8; Hairer–Nørsett–Wanner, Theorem II.8.4. -/

/-- Helper: for a symmetric method, c[rev(i)] = 1 − c[i]. -/
theorem IsSymmetric.c_rev {t : ButcherTableau s} (hs : t.IsSymmetric) (i : Fin s) :
    t.c i.rev = 1 - t.c i := by
  linarith [hs.symm_nodes i]

/-- Helper: for a symmetric, row-sum consistent method with order ≥ 2,
  the "Ac sum" satisfies the antisymmetry relation
  ∑ⱼ A[rev(i)][j]·cⱼ = (∑ⱼ A[i][j]·cⱼ) − cᵢ + 1/2.
  This is the crucial identity for deriving fourth-order conditions. -/
private lemma symm_Ac_rev {t : ButcherTableau s} (hs : t.IsSymmetric)
    (hrc : t.IsRowSumConsistent) (h2 : t.order2) (i : Fin s) :
    ∑ j : Fin s, t.A i.rev j * t.c j =
    (∑ j : Fin s, t.A i j * t.c j) - t.c i + 1 / 2 := by
  have hsymm : ∀ j : Fin s, t.A i j = t.b j - t.A i.rev j.rev := by
    intro j; linarith [hs.symm_tableau i j]
  have hfi : ∑ j, t.A i j * t.c j = ∑ j, (t.b j * t.c j - t.A i.rev j.rev * t.c j) := by
    congr 1; ext j; rw [hsymm]; ring
  have hfi' : ∑ j, t.A i j * t.c j = ∑ j, t.b j * t.c j - ∑ j, t.A i.rev j.rev * t.c j := by
    rw [hfi, Finset.sum_sub_distrib]
  have hreindex : ∑ j, t.A i.rev j.rev * t.c j = ∑ k, t.A i.rev k * t.c k.rev := by
    rw [← Equiv.sum_comp Fin.revPerm (fun k => t.A i.rev k * t.c k.rev)]
    congr 1; ext k; simp [Fin.revPerm]
  have hcrev_expand : ∑ k, t.A i.rev k * t.c k.rev =
      ∑ k, (t.A i.rev k - t.A i.rev k * t.c k) := by
    congr 1; ext k; rw [hs.c_rev]; ring
  have hcrev_split : ∑ k, (t.A i.rev k - t.A i.rev k * t.c k) =
      ∑ k, t.A i.rev k - ∑ k, t.A i.rev k * t.c k := Finset.sum_sub_distrib ..
  have hrs : ∑ k, t.A i.rev k = 1 - t.c i := by rw [← hrc i.rev, hs.c_rev]
  simp only [order2] at h2
  linarith [hfi', hreindex, hcrev_expand, hcrev_split, hrs, h2]

/-- Helper: the "Ac²" sums satisfy g(i) + g(rev(i)) = 1/3 − cᵢ + 2f(i). -/
private lemma symm_Ac2_sum {t : ButcherTableau s} (hs : t.IsSymmetric)
    (hrc : t.IsRowSumConsistent) (h2 : t.order2) (h3a : t.order3a) (i : Fin s) :
    (∑ j, t.A i j * t.c j ^ 2) + (∑ j, t.A i.rev j * t.c j ^ 2) =
    1 / 3 - t.c i + 2 * ∑ j, t.A i j * t.c j := by
  have hsymm : ∀ j : Fin s, t.A i j = t.b j - t.A i.rev j.rev := by
    intro j; linarith [hs.symm_tableau i j]
  have hgi : ∑ j, t.A i j * t.c j ^ 2 =
      ∑ j, t.b j * t.c j ^ 2 - ∑ j, t.A i.rev j.rev * t.c j ^ 2 := by
    rw [← Finset.sum_sub_distrib]; congr 1; ext j; rw [hsymm]; ring
  have hreindex : ∑ j, t.A i.rev j.rev * t.c j ^ 2 =
      ∑ k, t.A i.rev k * t.c k.rev ^ 2 := by
    rw [← Equiv.sum_comp Fin.revPerm (fun k => t.A i.rev k * t.c k.rev ^ 2)]
    congr 1; ext k; simp [Fin.revPerm]
  have hcrev2 : ∑ k, t.A i.rev k * t.c k.rev ^ 2 =
      ∑ k, t.A i.rev k * (1 - 2 * t.c k + t.c k ^ 2) := by
    congr 1; ext k; rw [hs.c_rev]; ring
  have hexpand_sub : ∑ k, t.A i.rev k * (1 - 2 * t.c k + t.c k ^ 2) =
      ∑ k, (t.A i.rev k - t.A i.rev k * (2 * t.c k) + t.A i.rev k * t.c k ^ 2) := by
    congr 1; ext k; ring
  have hsplit_a : ∑ k, (t.A i.rev k - t.A i.rev k * (2 * t.c k) + t.A i.rev k * t.c k ^ 2) =
      ∑ k, (t.A i.rev k - t.A i.rev k * (2 * t.c k)) + ∑ k, t.A i.rev k * t.c k ^ 2 := by
    rw [← Finset.sum_add_distrib]
  have hsplit_b : ∑ k, (t.A i.rev k - t.A i.rev k * (2 * t.c k)) =
      ∑ k, t.A i.rev k - ∑ k, t.A i.rev k * (2 * t.c k) :=
    Finset.sum_sub_distrib ..
  have h2factor : ∑ k, t.A i.rev k * (2 * t.c k) = 2 * ∑ k, t.A i.rev k * t.c k := by
    have : ∑ k, t.A i.rev k * (2 * t.c k) = ∑ k, 2 * (t.A i.rev k * t.c k) := by
      congr 1; ext k; ring
    rw [this, ← Finset.mul_sum]
  have hrs : ∑ k, t.A i.rev k = 1 - t.c i := by rw [← hrc i.rev, hs.c_rev]
  have hAc_rev := symm_Ac_rev hs hrc h2 i
  simp only [order3a] at h3a
  linarith [hgi, hreindex, hcrev2, hexpand_sub, hsplit_a, hsplit_b, h2factor, hrs, h3a, hAc_rev]

/-- Helper: D(j) + D(rev(j)) = b[j] where D(j) = ∑ᵢ bᵢaᵢⱼ. -/
private lemma symm_D_pair {t : ButcherTableau s} (hs : t.IsSymmetric)
    (h1 : t.order1) (j : Fin s) :
    (∑ i, t.b i * t.A i j) + (∑ i, t.b i * t.A i j.rev) = t.b j := by
  have h_symm_sum : ∑ i, t.b i * t.A i j + ∑ i, t.b i * t.A i.rev j.rev = t.b j := by
    rw [← Finset.sum_add_distrib]
    have : ∀ i, t.b i * t.A i j + t.b i * t.A i.rev j.rev = t.b i * t.b j := by
      intro i; rw [← mul_add]; congr 1; exact hs.symm_tableau i j
    simp_rw [this, ← Finset.sum_mul]
    simp only [order1] at h1; rw [h1, one_mul]
  have h_reindex : ∑ i, t.b i * t.A i.rev j.rev =
      ∑ i, t.b i * t.A i j.rev := by
    have hstep : ∀ i : Fin s, t.b i * t.A i.rev j.rev =
        (fun k => t.b k * t.A k j.rev) (Fin.revPerm i) := by
      intro i; simp [Fin.revPerm, hs.symm_weights i]
    simp_rw [hstep]
    exact Equiv.sum_comp Fin.revPerm (fun k => t.b k * t.A k j.rev)
  linarith

/-- **Symmetric methods of order 3 have order ≥ 4.**
  If a symmetric, row-sum consistent RK method satisfies all order conditions
  through order 3, then it also satisfies all fourth-order conditions.
  This is the key step in Nørsett's theorem that symmetric methods have even order.
  Reference: Iserles, Theorem 2.8; Hairer–Nørsett–Wanner, Theorem II.8.4. -/
theorem IsSymmetric.order4_of_order3 {t : ButcherTableau s}
    (hs : t.IsSymmetric) (hrc : t.IsRowSumConsistent) (h3 : t.HasOrderGe3) :
    t.HasOrderGe4 := by
  obtain ⟨h1, h2, h3a, h3b⟩ := h3
  refine ⟨h1, h2, h3a, h3b, ?_, ?_, ?_, ?_⟩
  -- order4a: ∑ bᵢcᵢ³ = 1/4
  -- Proof: 2·∑ bᵢcᵢ³ = ∑ bᵢ[cᵢ³ + (1−cᵢ)³] = ∑ bᵢ(1 − 3cᵢ + 3cᵢ²) = 1/2
  · show ∑ i : Fin s, t.b i * t.c i ^ 3 = 1 / 4
    have hpair : ∑ i : Fin s, t.b i * t.c i ^ 3 =
        ∑ i : Fin s, t.b i * (1 - t.c i) ^ 3 := by
      conv_lhs => rw [(Equiv.sum_comp Fin.revPerm (fun i => t.b i * t.c i ^ 3)).symm]
      congr 1; ext i; simp only [Fin.revPerm_apply]
      rw [← hs.symm_weights i]; congr 1; rw [hs.c_rev]
    have h2sum : 2 * ∑ i : Fin s, t.b i * t.c i ^ 3 =
        ∑ i : Fin s, t.b i * (1 - 3 * t.c i + 3 * t.c i ^ 2) := by
      have hcomb : ∑ i : Fin s, t.b i * t.c i ^ 3 +
          ∑ i : Fin s, t.b i * (1 - t.c i) ^ 3 =
          ∑ i : Fin s, t.b i * (1 - 3 * t.c i + 3 * t.c i ^ 2) := by
        rw [← Finset.sum_add_distrib]; congr 1; ext i; ring
      linarith [hpair]
    have hstep : ∑ i : Fin s, t.b i * (1 - 3 * t.c i + 3 * t.c i ^ 2) =
        ∑ i, (t.b i - 3 * (t.b i * t.c i) + 3 * (t.b i * t.c i ^ 2)) := by
      congr 1; ext i; ring
    have hfact1 : ∑ i, (3 * (t.b i * t.c i)) = 3 * ∑ i, t.b i * t.c i := by
      rw [← Finset.mul_sum]
    have hfact2 : ∑ i, (3 * (t.b i * t.c i ^ 2)) = 3 * ∑ i, t.b i * t.c i ^ 2 := by
      rw [← Finset.mul_sum]
    simp only [order1] at h1; simp only [order2] at h2; simp only [order3a] at h3a
    linarith [h2sum, hstep,
      Finset.sum_sub_distrib (f := fun i => t.b i) (g := fun i => 3 * (t.b i * t.c i))
        (s := Finset.univ),
      Finset.sum_add_distrib (f := fun i => t.b i - 3 * (t.b i * t.c i))
        (g := fun i => 3 * (t.b i * t.c i ^ 2)) (s := Finset.univ),
      hfact1, hfact2]
  -- order4b: ∑ bᵢcᵢ(∑ⱼ aᵢⱼcⱼ) = 1/8
  -- Proof: pair i ↔ rev(i) using f(rev(i)) = f(i) − cᵢ + 1/2
  · show ∑ i : Fin s, t.b i * t.c i * (∑ j : Fin s, t.A i j * t.c j) = 1 / 8
    set f := fun i : Fin s => ∑ j : Fin s, t.A i j * t.c j with hf_def
    have hpair : ∑ i, t.b i * t.c i * f i =
        ∑ i, t.b i * (1 - t.c i) * (f i - t.c i + 1 / 2) := by
      conv_lhs => rw [(Equiv.sum_comp Fin.revPerm (fun i => t.b i * t.c i * f i)).symm]
      congr 1; ext i; simp only [Fin.revPerm_apply]
      rw [← hs.symm_weights i, hs.c_rev]
      simp only [hf_def]
      rw [symm_Ac_rev hs hrc h2]
    have h2sum : 2 * ∑ i, t.b i * t.c i * f i =
        ∑ i, t.b i * (f i + t.c i ^ 2 - 3 / 2 * t.c i + 1 / 2) := by
      have hcomb : ∑ i, t.b i * t.c i * f i +
          ∑ i, t.b i * (1 - t.c i) * (f i - t.c i + 1 / 2) =
          ∑ i, t.b i * (f i + t.c i ^ 2 - 3 / 2 * t.c i + 1 / 2) := by
        rw [← Finset.sum_add_distrib]; congr 1; ext i; ring
      linarith [hpair]
    have hstep4b : ∑ i, t.b i * (f i + t.c i ^ 2 - 3 / 2 * t.c i + 1 / 2) =
        ∑ i, (t.b i * f i + t.b i * t.c i ^ 2 - 3 / 2 * (t.b i * t.c i) +
              1 / 2 * t.b i) := by
      congr 1; ext i; ring
    have hfact3 : ∑ i, (3 / 2 * (t.b i * t.c i)) = 3 / 2 * ∑ i, t.b i * t.c i := by
      rw [← Finset.mul_sum]
    have hfact4 : ∑ i, (1 / 2 * t.b i) = 1 / 2 * ∑ i, t.b i := by
      rw [← Finset.mul_sum]
    have hbf : ∑ i, t.b i * f i = 1 / 6 := by
      simp only [order3b, hf_def] at h3b ⊢; convert h3b using 1
      congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
    simp only [order1] at h1; simp only [order2] at h2; simp only [order3a] at h3a
    linarith [h2sum, hstep4b, hbf, hfact3, hfact4,
      Finset.sum_add_distrib
        (f := fun i => t.b i * f i + t.b i * t.c i ^ 2 - 3 / 2 * (t.b i * t.c i))
        (g := fun i => 1 / 2 * t.b i) (s := Finset.univ),
      Finset.sum_sub_distrib
        (f := fun i => t.b i * f i + t.b i * t.c i ^ 2)
        (g := fun i => 3 / 2 * (t.b i * t.c i)) (s := Finset.univ),
      Finset.sum_add_distrib
        (f := fun i => t.b i * f i)
        (g := fun i => t.b i * t.c i ^ 2) (s := Finset.univ)]
  -- order4c: ∑ bᵢ(∑ⱼ aᵢⱼcⱼ²) = 1/12
  -- Proof: 2·∑ bᵢg(i) = ∑ bᵢ(1/3 − cᵢ + 2f(i)) = 1/6
  · show ∑ i : Fin s, ∑ j : Fin s, t.b i * t.A i j * t.c j ^ 2 = 1 / 12
    set g := fun i : Fin s => ∑ j : Fin s, t.A i j * t.c j ^ 2 with hg_def
    set f := fun i : Fin s => ∑ j : Fin s, t.A i j * t.c j with hf_def
    have hconv : ∀ i, ∑ j, t.b i * t.A i j * t.c j ^ 2 = t.b i * g i := by
      intro i; simp only [hg_def]
      have : ∀ j, t.b i * t.A i j * t.c j ^ 2 = t.b i * (t.A i j * t.c j ^ 2) := by
        intro j; ring
      simp_rw [this]; rw [← Finset.mul_sum]
    simp_rw [hconv]
    have hpair : ∑ i, t.b i * g i = ∑ i, t.b i * g i.rev := by
      conv_lhs => rw [(Equiv.sum_comp Fin.revPerm (fun i => t.b i * g i)).symm]
      congr 1; ext i; simp only [Fin.revPerm_apply]; rw [← hs.symm_weights i]
    have h2sum : 2 * ∑ i, t.b i * g i =
        ∑ i, t.b i * (1 / 3 - t.c i + 2 * f i) := by
      have hcomb : ∑ i, t.b i * g i + ∑ i, t.b i * g i.rev =
          ∑ i, t.b i * (1 / 3 - t.c i + 2 * f i) := by
        rw [← Finset.sum_add_distrib]
        congr 1; ext i
        rw [← mul_add]; congr 1
        simp only [hg_def, hf_def]
        exact symm_Ac2_sum hs hrc h2 h3a i
      linarith [hpair]
    have hstep4c : ∑ i, t.b i * (1 / 3 - t.c i + 2 * f i) =
        ∑ i, (1 / 3 * t.b i - t.b i * t.c i + 2 * (t.b i * f i)) := by
      congr 1; ext i; ring
    have hfact5 : ∑ i, (1 / 3 * t.b i) = 1 / 3 * ∑ i, t.b i := by
      rw [← Finset.mul_sum]
    have hfact6 : ∑ i, (2 * (t.b i * f i)) = 2 * ∑ i, t.b i * f i := by
      rw [← Finset.mul_sum]
    have hbf : ∑ i, t.b i * f i = 1 / 6 := by
      simp only [order3b, hf_def] at h3b ⊢; convert h3b using 1
      congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
    simp only [order1] at h1; simp only [order2] at h2
    linarith [h2sum, hstep4c, hbf, hfact5, hfact6,
      Finset.sum_sub_distrib
        (f := fun i => 1 / 3 * t.b i)
        (g := fun i => t.b i * t.c i) (s := Finset.univ),
      Finset.sum_add_distrib
        (f := fun i => 1 / 3 * t.b i - t.b i * t.c i)
        (g := fun i => 2 * (t.b i * f i)) (s := Finset.univ)]
  -- order4d: ∑∑∑ bᵢaᵢⱼaⱼₖcₖ = 1/24
  -- Proof: rewrite as ∑ⱼ D(j)f(j), pair j ↔ rev(j)
  · show ∑ i : Fin s, ∑ j : Fin s, ∑ k : Fin s,
        t.b i * t.A i j * t.A j k * t.c k = 1 / 24
    set f := fun j : Fin s => ∑ k : Fin s, t.A j k * t.c k with hf_def
    set D := fun j : Fin s => ∑ i : Fin s, t.b i * t.A i j with hD_def
    have hrewrite : ∑ i, ∑ j, ∑ k, t.b i * t.A i j * t.A j k * t.c k =
        ∑ j, D j * f j := by
      simp only [hD_def, hf_def]; simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]; congr 1; ext j; rw [Finset.sum_comm]
      congr 1; ext i; congr 1; ext k; ring
    rw [hrewrite]
    have hpair : ∑ j : Fin s, D j * f j = ∑ j : Fin s, D j.rev * f j.rev := by
      have := (Equiv.sum_comp Fin.revPerm (fun j => D j * f j)).symm
      simp only [Fin.revPerm_apply] at this; exact this
    have hpair2 : ∑ j : Fin s, D j.rev * f j.rev =
        ∑ j, (t.b j - D j) * (f j - t.c j + 1 / 2) := by
      congr 1; ext j; congr 1
      · simp only [hD_def]; linarith [symm_D_pair hs h1 j]
      · simp only [hf_def]; exact symm_Ac_rev hs hrc h2 j
    have h2Q : 2 * ∑ j, D j * f j =
        ∑ j, (t.b j * f j - t.b j * t.c j + t.b j / 2 +
               D j * t.c j - D j / 2) := by
      have hcomb : ∑ j, D j * f j +
          ∑ j, (t.b j - D j) * (f j - t.c j + 1 / 2) =
          ∑ j, (t.b j * f j - t.b j * t.c j + t.b j / 2 +
               D j * t.c j - D j / 2) := by
        rw [← Finset.sum_add_distrib]; congr 1; ext j; ring
      linarith [hpair, hpair2]
    have hstep4d : ∑ j, (t.b j * f j - t.b j * t.c j + t.b j / 2 +
               D j * t.c j - D j / 2) =
        ∑ j, (t.b j * f j - t.b j * t.c j + 1 / 2 * t.b j +
               D j * t.c j - 1 / 2 * D j) := by
      congr 1; ext j; ring
    have hfact_b : ∑ j, (1 / 2 * t.b j) = 1 / 2 * ∑ j, t.b j := by
      rw [← Finset.mul_sum]
    have hfact_D : ∑ j, (1 / 2 * D j) = 1 / 2 * ∑ j, D j := by
      rw [← Finset.mul_sum]
    have hbf : ∑ j, t.b j * f j = 1 / 6 := by
      simp only [order3b, hf_def] at h3b ⊢; convert h3b using 1
      congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
    have hDc : ∑ j, D j * t.c j = 1 / 6 := by
      simp only [hD_def, Finset.sum_mul]; rw [Finset.sum_comm]
      simp only [order3b] at h3b; exact h3b
    have hDsum : ∑ j, D j = 1 / 2 := by
      simp only [hD_def]; rw [Finset.sum_comm]
      have : ∑ i, ∑ j, t.b i * t.A i j = ∑ i, t.b i * ∑ j, t.A i j := by
        congr 1; ext i; rw [Finset.mul_sum]
      rw [this]; simp_rw [fun i => (hrc i).symm]
      simp only [order2] at h2; exact h2
    simp only [order1] at h1; simp only [order2] at h2
    -- The goal is ∑ D*f = 1/24. We have 2*∑D*f = ∑(bf - bc + b/2 + Dc - D/2)
    -- = ∑bf - ∑bc + (1/2)∑b + ∑Dc - (1/2)∑D = 1/6 - 1/2 + 1/2 + 1/6 - 1/4 = 1/12
    -- Need: ∑(bf - bc + b/2 + Dc - D/2) = ∑bf - ∑bc + (1/2)∑b + ∑Dc - (1/2)∑D
    -- = 1/6 - 1/2 + 1/2 + 1/6 - 1/4 = 1/12, so ∑Df = 1/24
    have hsub_bc : ∑ j, (t.b j * f j - t.b j * t.c j) =
        ∑ j, t.b j * f j - ∑ j, t.b j * t.c j := Finset.sum_sub_distrib ..
    have hadd_b : ∑ j, (t.b j * f j - t.b j * t.c j + 1 / 2 * t.b j) =
        ∑ j, (t.b j * f j - t.b j * t.c j) + ∑ j, (1 / 2 * t.b j) := by
      rw [← Finset.sum_add_distrib]
    have hadd_Dc : ∑ j, (t.b j * f j - t.b j * t.c j + 1 / 2 * t.b j + D j * t.c j) =
        ∑ j, (t.b j * f j - t.b j * t.c j + 1 / 2 * t.b j) + ∑ j, D j * t.c j := by
      rw [← Finset.sum_add_distrib]
    have hsub_D : ∑ j, (t.b j * f j - t.b j * t.c j + 1 / 2 * t.b j + D j * t.c j - 1 / 2 * D j) =
        ∑ j, (t.b j * f j - t.b j * t.c j + 1 / 2 * t.b j + D j * t.c j) -
        ∑ j, (1 / 2 * D j) := by
      rw [← Finset.sum_sub_distrib]
    have hfact_b' : ∑ j, (1 / 2 * t.b j) = 1 / 2 * ∑ j, t.b j := by
      rw [← Finset.mul_sum]
    have hfact_D' : ∑ j, (1 / 2 * D j) = 1 / 2 * ∑ j, D j := by
      rw [← Finset.mul_sum]
    linarith [h2Q, hstep4d, hbf, hDc, hDsum,
      hsub_bc, hadd_b, hadd_Dc, hsub_D, hfact_b', hfact_D']

end ButcherTableau

/-! ## Implicit Midpoint is Symmetric -/

/-- **Implicit midpoint is symmetric.**
  For s = 1: rev(0) = 0, so the conditions reduce to b₀ = b₀, 2c₀ = 1, and 2a₀₀ = b₀.
  All hold with b₀ = 1, c₀ = 1/2, a₀₀ = 1/2.
  Reference: Iserles, Section 2.5. -/
theorem rkImplicitMidpoint_symmetric : rkImplicitMidpoint.IsSymmetric where
  symm_weights := by intro i; fin_cases i; simp [rkImplicitMidpoint]
  symm_nodes := by intro i; fin_cases i; simp [rkImplicitMidpoint]; norm_num
  symm_tableau := by
    intro i j; fin_cases i; fin_cases j; simp [rkImplicitMidpoint]; norm_num

/-! ## Backward Euler is NOT Symmetric -/

/-- **Backward Euler is NOT symmetric**: c₀ = 1, so c₀ + c₀ = 2 ≠ 1. -/
theorem rkImplicitEuler_not_symmetric : ¬rkImplicitEuler.IsSymmetric := by
  intro ⟨_, hn, _⟩
  have h := hn 0
  simp [rkImplicitEuler, Fin.rev] at h

/-! ## Forward Euler is NOT Symmetric -/

/-- **Forward Euler is NOT symmetric**: c₀ = 0, so c₀ + c₀ = 0 ≠ 1. -/
theorem rkEuler_not_symmetric : ¬rkEuler.IsSymmetric := by
  intro ⟨_, hn, _⟩
  have h := hn 0
  simp [rkEuler, Fin.rev] at h

/-! ## Gauss–Legendre 2-Stage is Symmetric -/

/-- **GL2 is symmetric.**
  The nodes c₀ + c₁ = 1, weights b₀ = b₁ = 1/2, and A[i][j] + A[1−i][1−j] = 1/2 = b[j].
  Reference: Iserles, Section 2.5; Hairer–Nørsett–Wanner, Theorem IV.5.2. -/
theorem rkGaussLegendre2_symmetric : rkGaussLegendre2.IsSymmetric where
  symm_weights := by intro i; fin_cases i <;> simp [rkGaussLegendre2]
  symm_nodes := by intro i; fin_cases i <;> simp [rkGaussLegendre2] <;> ring
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkGaussLegendre2] <;> ring

/-! ## Gauss–Legendre 3-Stage is Symmetric -/

/-- **GL3 is symmetric.**
  The nodes satisfy c₀ + c₂ = 1, c₁ = 1/2. The weights satisfy b₀ = b₂, b₁ = 4/9.
  The tableau satisfies A[i][j] + A[2−i][2−j] = b[j].
  Reference: Iserles, Section 2.5; Hairer–Nørsett–Wanner, Theorem IV.5.2. -/
theorem rkGaussLegendre3_symmetric : rkGaussLegendre3.IsSymmetric where
  symm_weights := by
    intro i; fin_cases i <;> simp [rkGaussLegendre3]
  symm_nodes := by
    intro i; fin_cases i <;> simp [rkGaussLegendre3] <;> ring
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkGaussLegendre3] <;> ring

/-! ## Lobatto IIIA 2-Stage (Trapezoidal Rule) is Symmetric -/

/-- **Lobatto IIIA 2-stage (trapezoidal rule) is symmetric.**
  Nodes c = (0, 1), weights b = (1/2, 1/2), both symmetric.
  A = [[0,0],[1/2,1/2]] satisfies A[i][j] + A[1−i][1−j] = 1/2. -/
theorem rkLobattoIIIA2_symmetric : rkLobattoIIIA2.IsSymmetric where
  symm_weights := by intro i; fin_cases i <;> simp [rkLobattoIIIA2]
  symm_nodes := by intro i; fin_cases i <;> simp [rkLobattoIIIA2]
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkLobattoIIIA2]

/-! ## Lobatto IIIA 3-Stage is Symmetric -/

/-- **Lobatto IIIA 3-stage is symmetric.**
  Nodes c = (0, 1/2, 1) and Simpson weights b = (1/6, 2/3, 1/6) are both symmetric.
  The tableau satisfies A[i][j] + A[2−i][2−j] = b[j]. -/
theorem rkLobattoIIIA3_symmetric : rkLobattoIIIA3.IsSymmetric where
  symm_weights := by intro i; fin_cases i <;> simp [rkLobattoIIIA3]
  symm_nodes := by intro i; fin_cases i <;> simp [rkLobattoIIIA3]; norm_num
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkLobattoIIIA3] <;> norm_num

/-! ## Lobatto IIIB 2-Stage is Symmetric -/

/-- **Lobatto IIIB 2-stage is symmetric.**
  Same nodes and weights as IIIA 2-stage. A = [[1/2,0],[1/2,0]] satisfies
  A[i][j] + A[1−i][1−j] = 1/2. -/
theorem rkLobattoIIIB2_symmetric : rkLobattoIIIB2.IsSymmetric where
  symm_weights := by intro i; fin_cases i <;> simp [rkLobattoIIIB2]
  symm_nodes := by intro i; fin_cases i <;> simp [rkLobattoIIIB2]
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkLobattoIIIB2]

/-! ## Lobatto IIIB 3-Stage is Symmetric -/

/-- **Lobatto IIIB 3-stage is symmetric.**
  Same nodes and weights as IIIA 3-stage. The tableau A has zero last column and
  satisfies A[i][j] + A[2−i][2−j] = b[j]. -/
theorem rkLobattoIIIB3_symmetric : rkLobattoIIIB3.IsSymmetric where
  symm_weights := by intro i; fin_cases i <;> simp [rkLobattoIIIB3]
  symm_nodes := by intro i; fin_cases i <;> simp [rkLobattoIIIB3]; norm_num
  symm_tableau := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [rkLobattoIIIB3] <;> norm_num

/-! ## Lobatto IIIC 2-Stage is NOT Symmetric -/

/-- **Lobatto IIIC 2-stage is NOT symmetric.**
  A[0][0] + A[1][1] = 1/2 + 1/2 = 1 ≠ 1/2 = b[0]. -/
theorem rkLobattoIIIC2_not_symmetric : ¬rkLobattoIIIC2.IsSymmetric := by
  intro ⟨_, _, ht⟩
  have h := ht 0 0
  simp [rkLobattoIIIC2, Fin.rev] at h

/-! ## Lobatto IIIC 3-Stage is NOT Symmetric -/

/-- **Lobatto IIIC 3-stage is NOT symmetric.**
  A[0][0] + A[2][2] = 1/6 + 1/6 = 1/3 ≠ 1/6 = b[0]. -/
theorem rkLobattoIIIC3_not_symmetric : ¬rkLobattoIIIC3.IsSymmetric := by
  intro ⟨_, _, ht⟩
  have h := ht 0 0
  simp [rkLobattoIIIC3, Fin.rev] at h

/-! ## Radau Methods are NOT Symmetric -/

/-- **Radau IIA 2-stage is NOT symmetric**: b₀ = 3/4 ≠ 1/4 = b₁. -/
theorem rkRadauIIA2_not_symmetric : ¬rkRadauIIA2.IsSymmetric := by
  intro ⟨hw, _, _⟩
  have h := hw 0
  simp [rkRadauIIA2, Fin.rev] at h
  norm_num at h

/-- **Radau IA 2-stage is NOT symmetric**: b₀ = 1/4 ≠ 3/4 = b₁. -/
theorem rkRadauIA2_not_symmetric : ¬rkRadauIA2.IsSymmetric := by
  intro ⟨hw, _, _⟩
  have h := hw 0
  simp [rkRadauIA2, Fin.rev] at h
  norm_num at h

private theorem sqrt6_sq' : Real.sqrt 6 ^ 2 = 6 :=
  Real.sq_sqrt (by norm_num : (6 : ℝ) ≥ 0)

/-- **Radau IIA 3-stage is NOT symmetric**: b₀ = (16−√6)/36 ≠ 1/9 = b₂. -/
theorem rkRadauIIA3_not_symmetric : ¬rkRadauIIA3.IsSymmetric := by
  intro ⟨hw, _, _⟩
  have h := hw 0
  simp [rkRadauIIA3, Fin.rev] at h
  nlinarith [sqrt6_sq']

/-- **Radau IA 3-stage is NOT symmetric**: b₀ = 1/9 ≠ (16−√6)/36 = b₂. -/
theorem rkRadauIA3_not_symmetric : ¬rkRadauIA3.IsSymmetric := by
  intro ⟨hw, _, _⟩
  have h := hw 0
  simp [rkRadauIA3, Fin.rev] at h
  nlinarith [sqrt6_sq']

/-! ## SDIRK3 is NOT Symmetric -/

/-- **SDIRK3 is NOT symmetric**: c₀ + c₂ = λ + 1 ≠ 1 (since λ > 0). -/
theorem rkSDIRK3_not_symmetric : ¬rkSDIRK3.IsSymmetric := by
  intro ⟨_, hn, _⟩
  have h := hn 0
  simp [rkSDIRK3, Fin.rev] at h
  linarith [sdirk3Lambda_pos]

/-! ## Lobatto IIIA and IIIB are Adjoint to Each Other

The Lobatto IIIA and IIIB families are **adjoint** to each other:
  b_i · A^{IIIA}_{ij} + b_j · A^{IIIB}_{ji} = b_i · b_j

This means their algebraic stability matrices sum to zero.

Reference: Hairer–Wanner, Section IV.2. -/

/-- **Lobatto IIIA 2-stage and IIIB 2-stage are adjoint.** -/
theorem lobattoIIIA2_IIIB2_adjoint :
    ∀ i j : Fin 2, rkLobattoIIIA2.b i * rkLobattoIIIA2.A i j +
      rkLobattoIIIA2.b j * rkLobattoIIIB2.A j i =
      rkLobattoIIIA2.b i * rkLobattoIIIA2.b j := by
  intro i j; fin_cases i <;> fin_cases j <;>
    simp [rkLobattoIIIA2, rkLobattoIIIB2]

/-- **Lobatto IIIA 3-stage and IIIB 3-stage are adjoint.** -/
theorem lobattoIIIA3_IIIB3_adjoint :
    ∀ i j : Fin 3, rkLobattoIIIA3.b i * rkLobattoIIIA3.A i j +
      rkLobattoIIIA3.b j * rkLobattoIIIB3.A j i =
      rkLobattoIIIA3.b i * rkLobattoIIIA3.b j := by
  intro i j; fin_cases i <;> fin_cases j <;>
    simp [rkLobattoIIIA3, rkLobattoIIIB3] <;> norm_num

/-! ## Summary Table

| Method              | Symmetric | Order | L-stable | Alg. stable |
|---------------------|-----------|-------|----------|-------------|
| Backward Euler      | ✗         | 1     | ✓        | ✓           |
| Forward Euler       | ✗         | 1     | ✗        | ✗           |
| Implicit midpoint   | ✓         | 2     | ✗        | ✓           |
| GL2                 | ✓         | 4     | ✗        | ✓           |
| GL3                 | ✓         | 6     | ✗        | ✓           |
| Radau IIA 2-stage   | ✗         | 3     | ✓        | ✓           |
| Radau IIA 3-stage   | ✗         | 5     | ✓        | ✓           |
| Radau IA 2-stage    | ✗         | 3     | ✓        | ✓           |
| Radau IA 3-stage    | ✗         | 5     | ✓        | ✓           |
| Lobatto IIIA 2-stg  | ✓         | 2     | ✗        | ✗           |
| Lobatto IIIA 3-stg  | ✓         | 4     | ✗        | ✗           |
| Lobatto IIIB 2-stg  | ✓         | 2     | ✗        | ✗           |
| Lobatto IIIB 3-stg  | ✓         | 4     | ✗        | ✗           |
| Lobatto IIIC 2-stg  | ✗         | 2     | ✓        | ✓           |
| Lobatto IIIC 3-stg  | ✗         | 4     | ✓        | ✓           |
| SDIRK3              | ✗         | 3     | ✓        | ✗           |

Key observations:
- **Symmetric ↔ Not L-stable**: symmetry implies R(z)·R(−z) = 1, forcing
  |R(−∞)| = 1/|R(+∞)| = 1 ≠ 0, so stiff decay is impossible.
- **Symmetric ↔ Even order**: consistent with Iserles Theorem 2.8.
- **Lobatto IIIA and IIIB are adjoint pairs**; each is individually symmetric.
  Lobatto IIIC is NOT symmetric (but has the best stability properties).
-/
