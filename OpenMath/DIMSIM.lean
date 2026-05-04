import OpenMath.RKAsGLM
import OpenMath.SDIRK

/-!
# Butcher §54 — DIMSIM type 1/2/3/4 classification

Butcher §541 classifies "Diagonally Implicit Multistage Integration
Methods" (DIMSIMs) by which of `A` and `V` are restricted:

* **Type 1** — `A` strictly lower triangular (the GLM is explicit) with
  `V` unrestricted.
* **Type 2** — `A` lower triangular with constant diagonal (singly
  diagonally implicit) with `V` unrestricted.
* **Type 3** — type 1 specialised to `V` of rank one (an explicit method
  with a single output history quantity, useful for parallel
  implementation).
* **Type 4** — type 2 specialised to `V` of rank one.

Reference: J. C. Butcher, *Numerical Methods for Ordinary Differential
Equations*, 2nd ed., §54.
-/

namespace GeneralLinearMethod

variable {s r : ℕ}

/-! ## §541 — Shape predicates on the `A` and `V` blocks -/

/-- `A` is lower triangular: every strictly above-diagonal entry vanishes.
Diagonal entries are unrestricted. -/
def IsLowerTriangular (m : GeneralLinearMethod s r) : Prop :=
  ∀ i j : Fin s, i < j → m.A i j = 0

/-- `A` is strictly lower triangular: every on-or-above-diagonal entry
vanishes. This matches `m.IsExplicit`. -/
def IsStrictLowerTriangular (m : GeneralLinearMethod s r) : Prop :=
  ∀ i j : Fin s, i ≤ j → m.A i j = 0

/-- `A` has a constant diagonal: there is a single scalar `λ` with
`A i i = λ` for every stage `i`. This is the "singly diagonally implicit"
constant of the §541 type-2 / type-4 classification. -/
def HasConstantDiagonal (m : GeneralLinearMethod s r) : Prop :=
  ∃ lam : ℝ, ∀ i : Fin s, m.A i i = lam

/-- The output-propagation block `V` has rank one: it factors as
`V k l = u k * v l` for some vectors `u, v : Fin r → ℝ`. -/
def IsRankOneV (m : GeneralLinearMethod s r) : Prop :=
  ∃ u v : Fin r → ℝ, ∀ k l : Fin r, m.V k l = u k * v l

/-! ## §541 — DIMSIM type 1/2/3/4 predicates -/

/-- **Type 1 DIMSIM**: explicit (`A` strictly lower triangular), `V`
unrestricted. -/
def IsDIMSIMType1 (m : GeneralLinearMethod s r) : Prop :=
  m.IsStrictLowerTriangular

/-- **Type 2 DIMSIM**: diagonally implicit (`A` lower triangular with a
constant diagonal), `V` unrestricted. -/
def IsDIMSIMType2 (m : GeneralLinearMethod s r) : Prop :=
  m.IsLowerTriangular ∧ m.HasConstantDiagonal

/-- **Type 3 DIMSIM**: type 1 with a rank-one `V`. -/
def IsDIMSIMType3 (m : GeneralLinearMethod s r) : Prop :=
  m.IsDIMSIMType1 ∧ m.IsRankOneV

/-- **Type 4 DIMSIM**: type 2 with a rank-one `V`. -/
def IsDIMSIMType4 (m : GeneralLinearMethod s r) : Prop :=
  m.IsDIMSIMType2 ∧ m.IsRankOneV

/-! ## Compatibility with the existing `IsExplicit` predicate -/

/-- An explicit GLM is strictly lower triangular. The two predicates
agree definitionally up to the `Fin`-order convention. -/
theorem IsExplicit.isStrictLowerTriangular {m : GeneralLinearMethod s r}
    (hm : m.IsExplicit) : m.IsStrictLowerTriangular := by
  intro i j hij
  exact hm i j (Fin.le_iff_val_le_val.mp hij)

/-- An explicit GLM is a type-1 DIMSIM. -/
theorem IsExplicit.isDIMSIMType1 {m : GeneralLinearMethod s r}
    (hm : m.IsExplicit) : m.IsDIMSIMType1 :=
  hm.isStrictLowerTriangular

/-- A type-2 DIMSIM whose constant diagonal is zero is a type-1 DIMSIM. -/
theorem IsDIMSIMType2.isDIMSIMType1_of_zero_diag
    {m : GeneralLinearMethod s r} (h : m.IsDIMSIMType2)
    (h0 : ∀ i : Fin s, m.A i i = 0) : m.IsDIMSIMType1 := by
  intro i j hij
  rcases lt_or_eq_of_le hij with h1 | h1
  · exact h.1 i j h1
  · subst h1; exact h0 i

end GeneralLinearMethod

/-! ## §502 sanity bridge — RK-as-GLM embedding -/

namespace ButcherTableau

variable {s : ℕ}

/-- The RK-as-GLM embedding of an explicit RK method is a type-1
DIMSIM. -/
theorem toGLM_isDIMSIMType1_of_isExplicit {t : ButcherTableau s}
    (h : t.IsExplicit) : (t.toGLM).IsDIMSIMType1 :=
  (t.toGLM_isExplicit h).isDIMSIMType1

end ButcherTableau

/-- Forward Euler embeds as a type-1 DIMSIM. -/
theorem rkEuler_toGLM_isDIMSIMType1 :
    (rkEuler.toGLM).IsDIMSIMType1 :=
  rkEuler.toGLM_isDIMSIMType1_of_isExplicit rkEuler_explicit

/-! ## §54 — RK-side rank-one `V` and type-2/3/4 bridges -/

namespace ButcherTableau

variable {s : ℕ}

/-- The output-propagation block of any RK-as-GLM is rank one because
`r = 1` collapses `V` to the constant `1`. -/
theorem toGLM_isRankOneV (t : ButcherTableau s) :
    (t.toGLM).IsRankOneV :=
  ⟨fun _ => 1, fun _ => 1, by intro k l; simp⟩

/-- Every explicit RK embeds as a type-3 DIMSIM. -/
theorem toGLM_isDIMSIMType3_of_isExplicit {t : ButcherTableau s}
    (h : t.IsExplicit) : (t.toGLM).IsDIMSIMType3 :=
  ⟨t.toGLM_isDIMSIMType1_of_isExplicit h, t.toGLM_isRankOneV⟩

/-- An SDIRK tableau embeds with a lower-triangular `A` block. -/
theorem toGLM_isLowerTriangular_of_isSDIRK {t : ButcherTableau s}
    (h : t.IsSDIRK) : (t.toGLM).IsLowerTriangular := by
  intro i j hij
  exact h.lower_tri i j hij

/-- An SDIRK tableau embeds with a constant-diagonal `A` block. -/
theorem toGLM_hasConstantDiagonal_of_isSDIRK {t : ButcherTableau s}
    (h : t.IsSDIRK) : (t.toGLM).HasConstantDiagonal := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · refine ⟨0, ?_⟩
    intro i
    exact (Fin.elim0 (hs ▸ i))
  · refine ⟨t.A ⟨0, hs⟩ ⟨0, hs⟩, fun i => ?_⟩
    exact h.const_diag i ⟨0, hs⟩

/-- Every SDIRK embeds as a type-2 DIMSIM. -/
theorem toGLM_isDIMSIMType2_of_isSDIRK {t : ButcherTableau s}
    (h : t.IsSDIRK) : (t.toGLM).IsDIMSIMType2 :=
  ⟨t.toGLM_isLowerTriangular_of_isSDIRK h,
   t.toGLM_hasConstantDiagonal_of_isSDIRK h⟩

/-- Every SDIRK embeds as a type-4 DIMSIM (type-2 plus rank-one `V`). -/
theorem toGLM_isDIMSIMType4_of_isSDIRK {t : ButcherTableau s}
    (h : t.IsSDIRK) : (t.toGLM).IsDIMSIMType4 :=
  ⟨t.toGLM_isDIMSIMType2_of_isSDIRK h, t.toGLM_isRankOneV⟩

end ButcherTableau

/-- Forward Euler embeds as a type-3 DIMSIM. -/
theorem rkEuler_toGLM_isDIMSIMType3 :
    (rkEuler.toGLM).IsDIMSIMType3 :=
  rkEuler.toGLM_isDIMSIMType3_of_isExplicit rkEuler_explicit

/-- 2-stage SDIRK embeds as a type-2 DIMSIM. -/
theorem rkSDIRK2_toGLM_isDIMSIMType2 :
    (rkSDIRK2.toGLM).IsDIMSIMType2 :=
  rkSDIRK2.toGLM_isDIMSIMType2_of_isSDIRK rkSDIRK2_isSDIRK

/-- 2-stage SDIRK embeds as a type-4 DIMSIM. -/
theorem rkSDIRK2_toGLM_isDIMSIMType4 :
    (rkSDIRK2.toGLM).IsDIMSIMType4 :=
  rkSDIRK2.toGLM_isDIMSIMType4_of_isSDIRK rkSDIRK2_isSDIRK

/-! ## §542 — Runge–Kutta stability of general linear methods

Butcher §542 isolates the design criterion that the stability matrix
`M(z)` has at most one non-zero eigenvalue, so that the spurious
eigenvalues introduced by the multivalue input vector are forced to
zero and only a single RK-flavoured eigenvalue survives. We encode
"at most one non-zero eigenvalue" as "any two non-zero roots of the
characteristic polynomial are equal", which sidesteps multiplicity
bookkeeping. -/

namespace GeneralLinearMethod

variable {s r : ℕ}

/-- Butcher §542 — **Runge–Kutta stability**. A GLM has Runge–Kutta
stability if for every complex `z`, the stability matrix `M(z)` has at
most one non-zero eigenvalue, encoded as "any two non-zero roots of
the characteristic polynomial are equal". -/
def IsRungeKuttaStable (m : GeneralLinearMethod s r) : Prop :=
  ∀ z : ℂ, ∀ μ₁ μ₂ : ℂ,
    (m.stabilityMatrix z).charpoly.IsRoot μ₁ → μ₁ ≠ 0 →
    (m.stabilityMatrix z).charpoly.IsRoot μ₂ → μ₂ ≠ 0 →
    μ₁ = μ₂

end GeneralLinearMethod

namespace ButcherTableau

variable {s : ℕ}

/-- Every RK-as-GLM is Runge–Kutta stable in the §542 sense, because
the embedding has `r = 1` and the `1×1` stability matrix has a single
characteristic root, hence at most one non-zero eigenvalue. -/
theorem toGLM_isRungeKuttaStable (t : ButcherTableau s) :
    (t.toGLM).IsRungeKuttaStable := by
  intro z μ₁ μ₂ h₁ _ h₂ _
  rw [toGLM_stabilityMatrix] at h₁ h₂
  exact ((charpoly_fin_one_const_isRoot_iff _ _).mp h₁).trans
    ((charpoly_fin_one_const_isRoot_iff _ _).mp h₂).symm

end ButcherTableau

/-- Forward Euler embeds with §542 Runge–Kutta stability. -/
theorem rkEuler_toGLM_isRungeKuttaStable :
    (rkEuler.toGLM).IsRungeKuttaStable :=
  rkEuler.toGLM_isRungeKuttaStable

/-- Implicit Euler embeds with §542 Runge–Kutta stability. -/
theorem rkImplicitEuler_toGLM_isRungeKuttaStable :
    (rkImplicitEuler.toGLM).IsRungeKuttaStable :=
  rkImplicitEuler.toGLM_isRungeKuttaStable

/-- 2-stage SDIRK embeds with §542 Runge–Kutta stability. -/
theorem rkSDIRK2_toGLM_isRungeKuttaStable :
    (rkSDIRK2.toGLM).IsRungeKuttaStable :=
  rkSDIRK2.toGLM_isRungeKuttaStable

/-- Forward Euler embeds as a type-3 DIMSIM that is also §542
Runge–Kutta stable. -/
theorem rkEuler_toGLM_type3_isRungeKuttaStable :
    (rkEuler.toGLM).IsDIMSIMType3 ∧ (rkEuler.toGLM).IsRungeKuttaStable :=
  ⟨rkEuler_toGLM_isDIMSIMType3, rkEuler_toGLM_isRungeKuttaStable⟩
