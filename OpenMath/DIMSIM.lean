import OpenMath.RKAsGLM

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
