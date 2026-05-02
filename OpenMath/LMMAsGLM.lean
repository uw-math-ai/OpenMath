import OpenMath.MultistepMethods
import OpenMath.GeneralLinearMethod
import OpenMath.DahlquistEquivalence

/-!
# Butcher §503 — Linear multistep methods as general linear methods

Embed an `s`-step linear multistep method as a one-stage general linear
method carrying the past `s` solution values and past `s` scaled vector-field
values.

Reference: J. C. Butcher, *Numerical Methods for Ordinary Differential
Equations*, 2nd ed., §503.
-/

open Finset Real

namespace LMM

variable {s : ℕ}

local instance finAddToTwoMulCoe {s : ℕ} : Coe (Fin (s + s)) (Fin (2 * s)) where
  coe := Fin.cast (Nat.two_mul s).symm

/-- §503 — Embed an `s`-step LMM as a 1-stage general linear method
with `r = 2 * s` Nordsieck-style input quantities. The first `s`
input slots carry past `y`-values `(y_n, y_{n+1}, …, y_{n+s-1})` and
the last `s` carry scaled past `h · f`-values
`(h · f_n, h · f_{n+1}, …, h · f_{n+s-1})`.

Block layout (one stage `Y = y_{n+s}`):

* `A[0,0] = m.β (Fin.last s)` — coefficient on `h · f(Y)` in the
  stage equation.
* `U[0, k] = -m.α (Fin.castSucc k)` for `k : Fin s` (past `y` slots).
* `U[0, s + k] = m.β (Fin.castSucc k)` for `k : Fin s` (past `f` slots).

Output blocks (shift register, dimension `2 * s`):

* For `k : Fin s` representing the new `y`-output index `k`:
  - if `k.val < s - 1`: copy `y^{[n-1]}_{k+1}` (shift), so
    `V[k, k+1] = 1` and `B[k, 0] = 0`.
  - if `k.val = s - 1` (output `y_{n+s} = Y`): take
    `V[s-1, l] = -m.α (Fin.castSucc l)` for `l < s`,
    `V[s-1, s + l] = m.β (Fin.castSucc l)` for `l < s`,
    `B[s-1, 0] = m.β (Fin.last s)`.
* For `k : Fin s` representing the new `h · f`-output index
  `s + k.val`:
  - if `k.val < s - 1`: copy `y^{[n-1]}_{s + k + 1}` (shift), so
    `V[s + k, s + k + 1] = 1` and `B[s + k, 0] = 0`.
  - if `k.val = s - 1` (output `h · f(Y)`):
    `B[2 * s - 1, 0] = 1`, `V[2 * s - 1, _] = 0`.

This matches the standard Butcher §503 / §504 Nordsieck-style
embedding restricted to the past-state representation (no derivative
truncation). -/
noncomputable def toGLM (m : LMM s) : GeneralLinearMethod 1 (2 * s) where
  A := fun _ _ => m.β (Fin.last s)
  U := fun _ k =>
    Fin.addCases
      (fun j : Fin s => -m.α (Fin.castSucc j))
      (fun j : Fin s => m.β (Fin.castSucc j))
      (Fin.cast (Nat.two_mul s) k)
  B := fun k _ =>
    Fin.addCases
      (fun j : Fin s => if (j : ℕ) + 1 = s then m.β (Fin.last s) else 0)
      (fun j : Fin s => if (j : ℕ) + 1 = s then 1 else 0)
      (Fin.cast (Nat.two_mul s) k)
  V := fun k l =>
    Fin.addCases
      (fun j : Fin s =>
        if (j : ℕ) + 1 = s then
          Fin.addCases
            (fun q : Fin s => -m.α (Fin.castSucc q))
            (fun q : Fin s => m.β (Fin.castSucc q))
            (Fin.cast (Nat.two_mul s) l)
        else if (l : ℕ) = (j : ℕ) + 1 then 1 else 0)
      (fun j : Fin s =>
        if (j : ℕ) + 1 = s then 0
        else if (l : ℕ) = s + (j : ℕ) + 1 then 1 else 0)
      (Fin.cast (Nat.two_mul s) k)

/-- Shape projection lemma for the (sole) `A` entry. -/
@[simp] theorem toGLM_A_apply (m : LMM s) :
    m.toGLM.A 0 0 = m.β (Fin.last s) := rfl

/-- Shape projection lemma for the past-`y` half of the `U` block. -/
@[simp] theorem toGLM_U_castAdd (m : LMM s) (k : Fin s) :
    m.toGLM.U 0 (Fin.castAdd s k) = -m.α (Fin.castSucc k) := by
  simp [toGLM]

/-- Shape projection lemma for the past-`f` half of the `U` block. -/
@[simp] theorem toGLM_U_natAdd (m : LMM s) (k : Fin s) :
    m.toGLM.U 0 (Fin.natAdd s k) = m.β (Fin.castSucc k) := by
  simp only [toGLM]
  change
    Fin.addCases (fun j : Fin s => -m.α (Fin.castSucc j))
        (fun j : Fin s => m.β (Fin.castSucc j)) (Fin.natAdd s k) =
      m.β (Fin.castSucc k)
  exact Fin.addCases_right k

/-- Shape projection lemma for non-last past-`y` shift rows of the `V` block. -/
@[simp] theorem toGLM_V_castAdd_shift_apply (m : LMM s) (j : Fin s)
    (hj : (j : ℕ) + 1 ≠ s) (l : Fin (2 * s)) :
    m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) l =
      if (l : ℕ) = (j : ℕ) + 1 then (1 : ℝ) else 0 := by
  simp only [toGLM]
  have hrow :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) =
        Fin.castAdd s j := by
    ext
    simp
  rw [hrow, Fin.addCases_left, if_neg hj]

/-- Shape projection lemma for the last past-`y` row against past-`y` entries. -/
@[simp] theorem toGLM_V_castAdd_last_castAdd_apply (m : LMM s) (j : Fin s)
    (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
              (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
      -m.α (Fin.castSucc l) := by
  simp only [toGLM]
  have hrow :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) =
        Fin.castAdd s j := by
    ext
    simp
  rw [hrow, Fin.addCases_left, if_pos hj]
  have hcol :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
        Fin.castAdd s l := by
    ext
    simp
  rw [hcol, Fin.addCases_left]

/-- Shape projection lemma for the last past-`y` row against past-`h*f` entries. -/
@[simp] theorem toGLM_V_castAdd_last_natAdd_apply (m : LMM s) (j : Fin s)
    (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
              (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
      m.β (Fin.castSucc l) := by
  simp only [toGLM]
  have hrow :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) =
        Fin.castAdd s j := by
    ext
    simp
  rw [hrow, Fin.addCases_left, if_pos hj]
  have hcol :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
        Fin.natAdd s l := by
    ext
    simp
  rw [hcol, Fin.addCases_right]

/-- Shape projection lemma for non-last past-`h*f` shift rows of the `V` block. -/
@[simp] theorem toGLM_V_natAdd_shift_apply (m : LMM s) (j : Fin s)
    (hj : (j : ℕ) + 1 ≠ s) (l : Fin (2 * s)) :
    m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l =
      if (l : ℕ) = s + (j : ℕ) + 1 then (1 : ℝ) else 0 := by
  simp only [toGLM]
  have hrow :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) =
        Fin.natAdd s j := by
    ext
    simp
  rw [hrow, Fin.addCases_right, if_neg hj]

/-- Shape projection lemma for the zero last past-`h*f` row of the `V` block. -/
@[simp] theorem toGLM_V_natAdd_last_apply (m : LMM s) (j : Fin s)
    (hj : (j : ℕ) + 1 = s) (l : Fin (2 * s)) :
    m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l = 0 := by
  simp only [toGLM]
  have hrow :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) =
        Fin.natAdd s j := by
    ext
    simp
  rw [hrow, Fin.addCases_right, if_pos hj]

/-- §510 / §512 stability prep — Phase B. Iterating the LMM-as-GLM
`V`-block always zeros the past-`h*f` half of the input within `s`
steps. Specifically, the `h*f`-slot at position `s + k` of the
`n`-fold `V`-iterate is zero whenever `n + k ≥ s`. The proof is purely
structural (no zero-stability or companion-matrix input). -/
theorem toGLM_V_iter_natAdd_eq_zero
    (m : LMM s) (q : Fin (2 * s) → ℝ) :
    ∀ (n : ℕ) (k : Fin s), s ≤ n + (k : ℕ) →
      ((fun v : Fin (2 * s) → ℝ =>
          fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q)
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    exact absurd hk (by have := k.isLt; omega)
  | succ n ih =>
    intro k hk
    rw [Function.iterate_succ_apply']
    -- Beta-reduce the outer lambda application.
    show (∑ l, m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) l *
        ((fun v : Fin (2 * s) → ℝ =>
            fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q) l) = 0
    by_cases hk1 : (k : ℕ) + 1 = s
    · -- Last past-h*f row: every V entry is 0 (cycle 619 simp lemma).
      simp_rw [toGLM_V_natAdd_last_apply m k hk1, zero_mul, Finset.sum_const_zero]
    · -- Shift past-h*f row: V row picks out a single column at s + (k:ℕ) + 1.
      simp_rw [toGLM_V_natAdd_shift_apply m k hk1]
      have hkSucc : (k : ℕ) + 1 < s := by
        have := k.isLt; omega
      set l₀ : Fin (2 * s) :=
        Fin.cast (Nat.two_mul s).symm (Fin.natAdd s ⟨(k : ℕ) + 1, hkSucc⟩)
        with hl₀_def
      have hl₀_val : (l₀ : ℕ) = s + (k : ℕ) + 1 := by
        rw [hl₀_def]; simp [Fin.natAdd]; omega
      rw [Finset.sum_eq_single l₀]
      · rw [if_pos hl₀_val, one_mul, hl₀_def]
        exact ih ⟨(k : ℕ) + 1, hkSucc⟩ (by show s ≤ n + ((k : ℕ) + 1); omega)
      · intro b _ hb
        rw [if_neg, zero_mul]
        intro hbeq
        apply hb
        apply Fin.ext
        rw [hbeq, hl₀_val]
      · intro h; exact absurd (Finset.mem_univ _) h

/-- Phase B corollary specialised to `n ≥ s`. After at least `s`
iterations the entire past-`h*f` half of the `V`-iterate is identically
zero. -/
theorem toGLM_V_iter_natAdd_eq_zero_of_le
    (m : LMM s) (q : Fin (2 * s) → ℝ) (n : ℕ) (hn : s ≤ n) (k : Fin s) :
    ((fun v : Fin (2 * s) → ℝ =>
        fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q)
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) = 0 := by
  exact toGLM_V_iter_natAdd_eq_zero m q n k (by have := k.isLt; omega)

/-- Local row-sum bound for the LMM-as-GLM `V` block. This is deliberately
private: it is only a coarse proof artefact for the §512 stability lift. -/
private noncomputable def M_max (m : LMM s) : ℝ :=
  1 + ∑ k : Fin s, (|m.α (Fin.castSucc k)| + |m.β (Fin.castSucc k)|)

private theorem M_max_nonneg (m : LMM s) : 0 ≤ M_max m := by
  unfold M_max
  have hsum : 0 ≤ ∑ k : Fin s, (|m.α (Fin.castSucc k)| + |m.β (Fin.castSucc k)|) := by
    exact Finset.sum_nonneg (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  linarith

private theorem one_le_M_max (m : LMM s) : 1 ≤ M_max m := by
  unfold M_max
  have hsum : 0 ≤ ∑ k : Fin s, (|m.α (Fin.castSucc k)| + |m.β (Fin.castSucc k)|) := by
    exact Finset.sum_nonneg (fun k _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  linarith

private theorem toGLM_V_row_l1_split (m : LMM s) (k : Fin (2 * s)) :
    (∑ l : Fin (2 * s), |m.toGLM.V k l|)
      =
    (∑ l : Fin s, |m.toGLM.V k
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l))|)
      + (∑ l : Fin s, |m.toGLM.V k
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l))|) := by
  have hstep :
      (∑ l : Fin (2 * s), |m.toGLM.V k l|)
        =
      ∑ l : Fin (2 * s),
        |m.toGLM.V k (Fin.cast (Nat.two_mul s).symm
          (Fin.cast (Nat.two_mul s) l))| := rfl
  rw [hstep]
  rw [Fin.sum_congr' (M := ℝ)
    (fun l : Fin (s + s) =>
      |m.toGLM.V k (Fin.cast (Nat.two_mul s).symm l)|)
    (Nat.two_mul s)]
  rw [Fin.sum_univ_add]

/-- Phase C row bound: each row of the structural `V` block has ℓ¹ norm
bounded by the local coarse constant `M_max`. -/
theorem toGLM_V_row_l1_le (m : LMM s) (k : Fin (2 * s)) :
    (∑ l, |m.toGLM.V k l|) ≤ M_max m := by
  set kc : Fin (s + s) := Fin.cast (Nat.two_mul s) k with hkc_def
  have hk : k = Fin.cast (Nat.two_mul s).symm kc := by
    rw [hkc_def]
    ext
    simp
  rw [hk]
  refine kc.addCases (motive := fun kc' =>
      (∑ l : Fin (2 * s),
        |m.toGLM.V (Fin.cast (Nat.two_mul s).symm kc') l|) ≤ M_max m)
    ?_ ?_
  · intro j
    by_cases hj : (j : ℕ) + 1 = s
    · rw [toGLM_V_row_l1_split]
      simp_rw [toGLM_V_castAdd_last_castAdd_apply m j hj,
        toGLM_V_castAdd_last_natAdd_apply m j hj]
      unfold M_max
      simp_rw [abs_neg]
      rw [Finset.sum_add_distrib]
      linarith
    · simp_rw [toGLM_V_castAdd_shift_apply m j hj]
      have hc : (j : ℕ) + 1 < 2 * s := by
        have := j.isLt
        omega
      rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hc⟩ : Fin (2 * s))]
      · simp [one_le_M_max m]
      · intro b _ hb
        have hbne : (b : ℕ) ≠ (j : ℕ) + 1 := by
          intro h
          apply hb
          ext
          exact h
        rw [if_neg hbne, abs_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
  · intro j
    by_cases hj : (j : ℕ) + 1 = s
    · simp_rw [toGLM_V_natAdd_last_apply m j hj, abs_zero]
      simp [M_max_nonneg m]
    · simp_rw [toGLM_V_natAdd_shift_apply m j hj]
      have hc : s + (j : ℕ) + 1 < 2 * s := by
        have := j.isLt
        omega
      rw [Finset.sum_eq_single (⟨s + (j : ℕ) + 1, hc⟩ : Fin (2 * s))]
      · simp [one_le_M_max m]
      · intro b _ hb
        have hbne : (b : ℕ) ≠ s + (j : ℕ) + 1 := by
          intro h
          apply hb
          ext
          exact h
        rw [if_neg hbne, abs_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h

/-- Phase C one-step pointwise bound for the structural `V` block. -/
theorem toGLM_V_step_le
    (m : LMM s) (q : Fin (2 * s) → ℝ) (M : ℝ)
    (hq : ∀ l, |q l| ≤ M) (k : Fin (2 * s)) :
    |∑ l, m.toGLM.V k l * q l| ≤ (M_max m) * M := by
  have hM : 0 ≤ M := by
    have hqk := hq k
    have hnonneg : 0 ≤ |q k| := abs_nonneg _
    linarith
  calc
    |∑ l, m.toGLM.V k l * q l|
        ≤ ∑ l, |m.toGLM.V k l * q l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |m.toGLM.V k l| * M := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hq l) (abs_nonneg _)
    _ = (∑ l, |m.toGLM.V k l|) * M := by
      rw [← Finset.sum_mul]
    _ ≤ (M_max m) * M :=
      mul_le_mul_of_nonneg_right (toGLM_V_row_l1_le m k) hM

/-- Phase C. Bound on the `V`-iterate for any number of iterations in terms
of the input ℓ∞-norm. Used later with the y-side spectral bound. -/
theorem toGLM_V_iter_le
    (m : LMM s) (q : Fin (2 * s) → ℝ) (M : ℝ)
    (hq : ∀ l, |q l| ≤ M) (n : ℕ) (k : Fin (2 * s)) :
    |((fun v : Fin (2 * s) → ℝ =>
        fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q) k|
      ≤ (M_max m) ^ n * M := by
  let Vop : (Fin (2 * s) → ℝ) → Fin (2 * s) → ℝ :=
    fun v k' => ∑ l, m.toGLM.V k' l * v l
  change |(Vop^[n] q) k| ≤ (M_max m) ^ n * M
  induction n generalizing k with
  | zero =>
    simpa using hq k
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change |∑ l, m.toGLM.V k l * (Vop^[n] q) l| ≤ (M_max m) ^ (n + 1) * M
    have hiter : ∀ l : Fin (2 * s), |(Vop^[n] q) l| ≤ (M_max m) ^ n * M := by
      intro l
      exact ih l
    calc
      |∑ l, m.toGLM.V k l * (Vop^[n] q) l|
          ≤ (M_max m) * ((M_max m) ^ n * M) :=
            toGLM_V_step_le m (Vop^[n] q) ((M_max m) ^ n * M) hiter k
      _ = (M_max m) ^ (n + 1) * M := by
        rw [pow_succ']
        ring

/-- §512 Phase D prep: extract the past-`y` half of a `Fin (2*s)`-indexed
input vector. -/
def toGLM_y_half (q : Fin (2 * s) → ℝ) (k : Fin s) : ℝ :=
  q (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k))

/-- §512 Phase D prep: extract the past-`h·f` half of a `Fin (2*s)`-indexed
input vector. -/
def toGLM_hf_half (q : Fin (2 * s) → ℝ) (k : Fin s) : ℝ :=
  q (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k))

/-- §512 Phase D bridge (step 1, shift case). When the past-`h·f` half of
the input vector is zero (unused here, kept for symmetry with the last-row
sibling), one application of the LMM-as-GLM `V`-block on a non-last
past-`y` row simply shifts the `y` slot. -/
theorem toGLM_V_step_y_of_hf_zero_shift
    (m : LMM s) (q : Fin (2 * s) → ℝ)
    (k : Fin s) (hk1 : (k : ℕ) + 1 ≠ s) :
    (∑ l, m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) l * q l)
      = toGLM_y_half q ⟨(k : ℕ) + 1, by have := k.isLt; omega⟩ := by
  simp_rw [toGLM_V_castAdd_shift_apply m k hk1]
  have hkSucc : (k : ℕ) + 1 < s := by have := k.isLt; omega
  set l₀ : Fin (2 * s) :=
    Fin.cast (Nat.two_mul s).symm (Fin.castAdd s ⟨(k : ℕ) + 1, hkSucc⟩)
    with hl₀_def
  have hl₀_val : (l₀ : ℕ) = (k : ℕ) + 1 := by
    rw [hl₀_def]; simp [Fin.castAdd]
  rw [Finset.sum_eq_single l₀]
  · rw [if_pos hl₀_val, one_mul, hl₀_def]
    rfl
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro hbeq
    apply hb
    apply Fin.ext
    rw [hbeq, hl₀_val]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- §512 Phase D bridge (step 1, last-row case). When the past-`h·f` half
of the input vector is zero, one application of the LMM-as-GLM `V`-block
on the last past-`y` row produces the LMM update's `−ρ`-side coefficient
sum against the past-`y` half. -/
theorem toGLM_V_step_y_of_hf_zero_last
    (m : LMM s) (q : Fin (2 * s) → ℝ)
    (hhf : ∀ k : Fin s, toGLM_hf_half q k = 0)
    (k : Fin s) (hk1 : (k : ℕ) + 1 = s) :
    (∑ l, m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) l * q l)
      = ∑ l, (-m.α (Fin.castSucc l)) * toGLM_y_half q l := by
  -- Reindex `Fin (2*s)` to `Fin (s+s)` and split into past-y / past-h·f halves.
  have hstep :
      (∑ l : Fin (2 * s),
          m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) l *
            q l)
        =
      ∑ l : Fin (2 * s),
          m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k))
              (Fin.cast (Nat.two_mul s).symm
                (Fin.cast (Nat.two_mul s) l)) *
            q (Fin.cast (Nat.two_mul s).symm
              (Fin.cast (Nat.two_mul s) l)) := rfl
  rw [hstep]
  rw [Fin.sum_congr' (M := ℝ)
    (fun l : Fin (s + s) =>
      m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k))
          (Fin.cast (Nat.two_mul s).symm l) *
        q (Fin.cast (Nat.two_mul s).symm l))
    (Nat.two_mul s)]
  rw [Fin.sum_univ_add]
  simp_rw [toGLM_V_castAdd_last_castAdd_apply m k hk1,
    toGLM_V_castAdd_last_natAdd_apply m k hk1]
  -- Past-`h·f` half is zero termwise by `hhf`.
  have hhfsum :
      (∑ l : Fin s, m.β (Fin.castSucc l) *
          q (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l))) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hl : q (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
        toGLM_hf_half q l := rfl
    rw [hl, hhf l, mul_zero]
  rw [hhfsum, add_zero]
  -- Past-`y` half is exactly `∑ l, -α(castSucc l) * toGLM_y_half q l`.
  rfl

/-- §512 Phase D step 2 (shift case). Once `n ≥ s` so that the past-`h·f`
half of `V^n q` has vanished (Phase B), one further application of `V`
on a non-last past-`y` row of `V^n q` is the y-half shift. -/
theorem toGLM_V_iter_step_y_shift
    (m : LMM s) (q : Fin (2 * s) → ℝ) (n : ℕ) (_hn : s ≤ n)
    (k : Fin s) (hk1 : (k : ℕ) + 1 ≠ s) :
    (∑ l, m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) l *
        ((fun v : Fin (2 * s) → ℝ =>
            fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q) l)
      =
    toGLM_y_half
      ((fun v : Fin (2 * s) → ℝ =>
          fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q)
      ⟨(k : ℕ) + 1, by have := k.isLt; omega⟩ := by
  exact toGLM_V_step_y_of_hf_zero_shift m _ k hk1

/-- §512 Phase D step 2 (last-row case). Once `n ≥ s`, applying `V` to
the last past-`y` row of `V^n q` gives the LMM companion update on the
y-half. -/
theorem toGLM_V_iter_step_y_last
    (m : LMM s) (q : Fin (2 * s) → ℝ) (n : ℕ) (hn : s ≤ n)
    (k : Fin s) (hk1 : (k : ℕ) + 1 = s) :
    (∑ l, m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) l *
        ((fun v : Fin (2 * s) → ℝ =>
            fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q) l)
      =
    ∑ l, (-m.α (Fin.castSucc l)) *
      toGLM_y_half
        ((fun v : Fin (2 * s) → ℝ =>
            fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q)
        l := by
  have hhf : ∀ k : Fin s,
      toGLM_hf_half
        ((fun v : Fin (2 * s) → ℝ =>
            fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q) k = 0 := by
    intro k
    exact toGLM_V_iter_natAdd_eq_zero_of_le m q n hn k
  exact toGLM_V_step_y_of_hf_zero_last m _ hhf k hk1

/-- §512 Phase D step 3 — companion-step operator on the y-half. Given a
real-valued y-state `v : Fin s → ℝ`, produce the next y-state by shifting
forward, except on the last row where we apply the LMM `−ρ`-coefficient
combination. This is the real-valued companion-step extracted from the
cycle 622/623 one-step / iterate bridges. -/
noncomputable def toGLM_y_step (m : LMM s) (v : Fin s → ℝ) : Fin s → ℝ :=
  fun k =>
    if h : (k : ℕ) + 1 = s then
      ∑ l, (-m.α (Fin.castSucc l)) * v l
    else
      v ⟨(k : ℕ) + 1, by have := k.isLt; omega⟩

/-- §512 Phase D step 3 — one-step matching theorem. For `n ≥ s`, the
y-half of `V^{n+1} q` equals the companion-step operator applied to the
y-half of `V^n q`. -/
theorem toGLM_y_half_step_eq (m : LMM s) (q : Fin (2 * s) → ℝ)
    (n : ℕ) (hn : s ≤ n) :
    toGLM_y_half ((fun v : Fin (2 * s) → ℝ =>
        fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n + 1] q)
      = toGLM_y_step m
          (toGLM_y_half ((fun v : Fin (2 * s) → ℝ =>
              fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q)) := by
  funext k
  by_cases hk1 : (k : ℕ) + 1 = s
  · -- last-row case
    rw [Function.iterate_succ_apply']
    show (∑ l, m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) l *
        ((fun v : Fin (2 * s) → ℝ =>
            fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q) l)
        = toGLM_y_step m
            (toGLM_y_half
              ((fun v : Fin (2 * s) → ℝ =>
                  fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q)) k
    unfold toGLM_y_step
    rw [dif_pos hk1]
    exact toGLM_V_iter_step_y_last m q n hn k hk1
  · -- shift case
    rw [Function.iterate_succ_apply']
    show (∑ l, m.toGLM.V (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) l *
        ((fun v : Fin (2 * s) → ℝ =>
            fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q) l)
        = toGLM_y_step m
            (toGLM_y_half
              ((fun v : Fin (2 * s) → ℝ =>
                  fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q)) k
    unfold toGLM_y_step
    rw [dif_neg hk1]
    exact toGLM_V_iter_step_y_shift m q n hn k hk1

/-- §512 Phase D step 3 — multi-step matching theorem. For `n ≥ s` and
`j : ℕ`, the y-half of `V^{n+j} q` equals the `j`-th iterate of the
companion-step operator applied to the y-half of `V^n q`. -/
theorem toGLM_y_half_iter_eq (m : LMM s) (q : Fin (2 * s) → ℝ)
    (n : ℕ) (hn : s ≤ n) (j : ℕ) :
    toGLM_y_half ((fun v : Fin (2 * s) → ℝ =>
        fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n + j] q)
      = (toGLM_y_step m)^[j]
          (toGLM_y_half ((fun v : Fin (2 * s) → ℝ =>
              fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, Function.iterate_succ_apply' (toGLM_y_step m)]
    rw [← ih]
    exact toGLM_y_half_step_eq m q (n + j) (by omega)

/-- §512 Phase D step 4 — the real y-half companion step is the
`Complex.ofReal` lift of Mathlib's `LinearRecurrence.tupleSucc` companion
for the LMM characteristic recurrence. -/
theorem toGLM_y_step_complex_eq (m : LMM s) (v : Fin s → ℝ) :
    (fun k : Fin s => ((toGLM_y_step m v k : ℝ) : ℂ))
      = m.toLinearRecurrence.tupleSucc (fun k : Fin s => ((v k : ℝ) : ℂ)) := by
  funext k
  unfold toGLM_y_step
  simp only [toLinearRecurrence, LinearRecurrence.tupleSucc, LinearMap.coe_mk,
    AddHom.coe_mk]
  by_cases hlt : (k : ℕ) + 1 < s
  · have hne : ¬ (k : ℕ) + 1 = s := by omega
    rw [dif_neg hne, dif_pos hlt]
  · have heq : (k : ℕ) + 1 = s := by
      have := k.isLt
      omega
    rw [dif_pos heq, dif_neg hlt]
    simp [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_neg]

/-- §512 Phase D step 4 — iterate the real/complex companion-step bridge. -/
theorem toGLM_y_step_iter_complex_eq (m : LMM s)
    (v : Fin s → ℝ) (j : ℕ) :
    (fun k : Fin s => (((toGLM_y_step m)^[j] v) k : ℂ))
      = (m.toLinearRecurrence.tupleSucc^[j])
          (fun k : Fin s => ((v k : ℝ) : ℂ)) := by
  induction j with
  | zero =>
    simp
  | succ j ih =>
    calc
      (fun k : Fin s => (((toGLM_y_step m)^[j + 1] v) k : ℂ))
          = (fun k : Fin s =>
              (toGLM_y_step m ((toGLM_y_step m)^[j] v) k : ℂ)) := by
            rw [Function.iterate_succ_apply']
      _ = m.toLinearRecurrence.tupleSucc
            (fun k : Fin s => (((toGLM_y_step m)^[j] v) k : ℂ)) :=
          toGLM_y_step_complex_eq m ((toGLM_y_step m)^[j] v)
      _ = m.toLinearRecurrence.tupleSucc
            ((m.toLinearRecurrence.tupleSucc^[j])
              (fun k : Fin s => ((v k : ℝ) : ℂ))) := by
          rw [ih]
      _ = (m.toLinearRecurrence.tupleSucc^[j + 1])
            (fun k : Fin s => ((v k : ℝ) : ℂ)) := by
          rw [Function.iterate_succ_apply']

/-- §512 Phase D step 4 — zero-stability gives a uniform complex norm bound
on the y-half of all post-`s` GLM iterates. -/
theorem toGLM_y_half_iter_complex_norm_bound
    (m : LMM s) (hzs : m.IsZeroStable) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (q : Fin (2 * s) → ℝ) (n : ℕ) (_hn : s ≤ n) (j : ℕ),
        ‖fun k : Fin s =>
            ((toGLM_y_half ((fun v : Fin (2 * s) → ℝ =>
                fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n + j] q) k
              : ℝ) : ℂ)‖
          ≤ M * ‖fun k : Fin s =>
              ((toGLM_y_half ((fun v : Fin (2 * s) → ℝ =>
                  fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q) k
                : ℝ) : ℂ)‖ := by
  obtain ⟨M, hM_nonneg, hM⟩ := uniformly_bounded_tupleSucc_iterates m hzs
  refine ⟨M, hM_nonneg, ?_⟩
  intro q n hn j
  let Vop : (Fin (2 * s) → ℝ) → Fin (2 * s) → ℝ :=
    fun v k' => ∑ l, m.toGLM.V k' l * v l
  let initR : Fin s → ℝ := toGLM_y_half ((Vop^[n]) q)
  let initC : Fin s → ℂ := fun k => ((initR k : ℝ) : ℂ)
  have hreal :
      toGLM_y_half ((Vop^[n + j]) q) = (toGLM_y_step m)^[j] initR := by
    exact toGLM_y_half_iter_eq m q n hn j
  have hcomplex :
      (fun k : Fin s => ((toGLM_y_half ((Vop^[n + j]) q) k : ℝ) : ℂ))
        = (m.toLinearRecurrence.tupleSucc^[j]) initC := by
    calc
      (fun k : Fin s => ((toGLM_y_half ((Vop^[n + j]) q) k : ℝ) : ℂ))
          = (fun k : Fin s => (((toGLM_y_step m)^[j] initR) k : ℂ)) := by
            rw [hreal]
      _ = (m.toLinearRecurrence.tupleSucc^[j]) initC := by
          exact toGLM_y_step_iter_complex_eq m initR j
  rw [hcomplex]
  exact hM j initC

/-- §503 sanity check for §520: because an LMM embeds as a one-stage GLM,
the stability-matrix entry collapses to the single stage resolvent factor.
The surrounding `toGLM` blocks retain the literal §503 row/column shape. -/
theorem toGLM_stabilityMatrix_apply (m : LMM s) (z : ℂ) (k l : Fin (2 * s)) :
    m.toGLM.stabilityMatrix z k l =
      m.toGLM.Vℂ k l +
        z *
          (m.toGLM.Bℂ k 0 *
            (((1 : Matrix (Fin 1) (Fin 1) ℂ) - z • m.toGLM.Aℂ)⁻¹ 0 0) *
            m.toGLM.Uℂ 0 l) := by
  rw [GeneralLinearMethod.stabilityMatrix_apply]
  simp

/-- Stage map specialisation: the GLM stage equation reduces to the
expected linear combination of past values plus the implicit `f(Y)`
term. State this in scalar form, taking `yIn : Fin (2 * s) → ℝ` as the
encoded past state and `Y : Fin 1 → ℝ` (so `Y 0 = y_{n+s}`). -/
theorem toGLM_stageMap_eq (m : LMM s) (f : ℝ → ℝ) (h : ℝ)
    (yIn : Fin (2 * s) → ℝ) (Y : Fin 1 → ℝ) :
    m.toGLM.stageMap f h yIn Y 0 =
      h * m.β (Fin.last s) * f (Y 0)
      + (∑ k : Fin s, -m.α (Fin.castSucc k) * yIn (Fin.castAdd s k))
      + (∑ k : Fin s,  m.β (Fin.castSucc k) * yIn (Fin.natAdd s k)) := by
  simp [GeneralLinearMethod.stageMap_apply, toGLM]
  rw [show
      (∑ x : Fin (2 * s),
          Fin.addCases (fun j : Fin s => -m.α (Fin.castSucc j))
              (fun j : Fin s => m.β (Fin.castSucc j))
              (Fin.cast (Nat.two_mul s) x) *
            yIn x)
        =
      (∑ x : Fin (s + s),
          Fin.addCases (fun j : Fin s => -m.α (Fin.castSucc j))
              (fun j : Fin s => m.β (Fin.castSucc j)) x *
            yIn (Fin.cast (Nat.two_mul s).symm x)) by
    rw [← Fin.sum_congr'
      (fun x : Fin (s + s) =>
        Fin.addCases (fun j : Fin s => -m.α (Fin.castSucc j))
            (fun j : Fin s => m.β (Fin.castSucc j)) x *
          yIn (Fin.cast (Nat.two_mul s).symm x))
      (Nat.two_mul s)]
    simp]
  rw [Fin.sum_univ_add]
  simp [Fin.addCases, Fin.natAdd]
  simp [Fin.addNat, Nat.add_comm]
  ring

/-- Explicitness: an LMM is explicit (`m.β (Fin.last s) = 0`) iff its
GLM image is explicit. The GLM stage matrix is `1×1`, so explicitness
reduces to `A 0 0 = 0`. -/
theorem toGLM_isExplicit_iff (m : LMM s) :
    m.toGLM.IsExplicit ↔ m.IsExplicit := by
  unfold GeneralLinearMethod.IsExplicit LMM.IsExplicit
  simp [toGLM]

/-- §503 sanity check — every consistent LMM embeds as a §510-consistent
GLM. The witnesses encode the Nordsieck "y / h·y'" content of each
input slot:

* `q` carries the `y_n` content: the past-`y` slots all hold `1`, the
  past-`h·f` slots all hold `0`.
* `q'` carries the `h · y'_n` content: the `j`-th past-`y` slot
  (`j : Fin s`) holds `(j : ℝ)`, every past-`h·f` slot holds `1`. -/
theorem toGLM_isConsistent (m : LMM s) (hm : m.IsConsistent) :
    m.toGLM.IsConsistent := by
  refine
    ⟨fun k =>
        Fin.addCases (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ))
          (Fin.cast (Nat.two_mul s) k),
     fun k =>
        Fin.addCases (fun j : Fin s => (j : ℝ)) (fun _ : Fin s => (1 : ℝ))
          (Fin.cast (Nat.two_mul s) k),
     ?_, ?_, ?_⟩
  · -- V q = q (q is the past-y indicator: 1 on past-y slots, 0 on past-f slots)
    intro k
    -- Reindex the sum Fin (2*s) → Fin (s+s) so q's addCases collapses cleanly,
    -- and split into past-y / past-f halves.
    have hreindex :
        (∑ l : Fin (2 * s), m.toGLM.V k l *
            Fin.addCases (motive := fun _ => ℝ)
                (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ))
                (Fin.cast (Nat.two_mul s) l))
          = (∑ l : Fin s, m.toGLM.V k (Fin.cast (Nat.two_mul s).symm
                  (Fin.castAdd s l))) := by
      -- Step A: V k l = V k (Fin.cast _.symm (Fin.cast _ l)) (cast cancels).
      have stepA : (∑ l : Fin (2 * s), m.toGLM.V k l *
              Fin.addCases (motive := fun _ => ℝ)
                  (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ))
                  (Fin.cast (Nat.two_mul s) l))
            = ∑ l : Fin (2 * s),
                m.toGLM.V k (Fin.cast (Nat.two_mul s).symm
                  (Fin.cast (Nat.two_mul s) l)) *
                  Fin.addCases (motive := fun _ => ℝ)
                    (fun _ : Fin s => (1 : ℝ))
                    (fun _ : Fin s => (0 : ℝ))
                    (Fin.cast (Nat.two_mul s) l) := rfl
      rw [stepA]
      -- Step B: reindex via Fin.sum_congr'.
      rw [Fin.sum_congr' (M := ℝ)
        (fun l : Fin (s + s) =>
          m.toGLM.V k (Fin.cast (Nat.two_mul s).symm l) *
            Fin.addCases (motive := fun _ => ℝ)
              (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ)) l)
        (Nat.two_mul s)]
      -- Step C: split via Fin.sum_univ_add.
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, mul_one, mul_zero,
        Finset.sum_const_zero, add_zero]
    rw [hreindex]
    -- Now case-split on Fin.cast _ k via addCases.
    -- We do this by generalizing.
    have hqk :
        Fin.addCases (motive := fun _ => ℝ)
            (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ))
            (Fin.cast (Nat.two_mul s) k) =
          Fin.addCases (motive := fun _ => ℝ)
            (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ))
            (Fin.cast (Nat.two_mul s) k) := rfl
    -- Case-split on (Fin.cast _ k) via addCases
    set kc : Fin (s + s) := Fin.cast (Nat.two_mul s) k with hkc_def
    have hk_recover : k = Fin.cast (Nat.two_mul s).symm kc := by
      rw [hkc_def]; ext; simp
    refine kc.addCases (motive := fun kc' =>
        Fin.cast (Nat.two_mul s) k = kc' →
        (∑ l : Fin s, m.toGLM.V k
              (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l))) =
          Fin.addCases (motive := fun _ => ℝ)
            (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ)) kc')
      ?_ ?_ rfl
    · -- past-y row: kc = Fin.castAdd s ⟨j, _⟩
      intro j hkc_eq
      simp only [Fin.addCases_left]
      -- Goal: ∑ l, V k (cast.symm (castAdd s l)) = 1
      -- V k (cast.symm (castAdd s l)) when k_cast = castAdd s j:
      -- = V at past-y row j, looking up past-y slot l.
      by_cases hj : (j : ℕ) + 1 = s
      · -- last-y row: V[k, l] = -m.α (Fin.castSucc l)
        have hVrow : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
              -m.α (Fin.castSucc l) := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then
                Fin.addCases (motive := fun _ => ℝ)
                    (fun q : Fin s => -m.α (Fin.castSucc q))
                    (fun q : Fin s => m.β (Fin.castSucc q))
                    (Fin.cast (Nat.two_mul s)
                      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)))
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = -m.α (Fin.castSucc l)
          rw [hkc_eq]
          rw [Fin.addCases_left]
          rw [if_pos hj]
          have hcast :
              Fin.cast (Nat.two_mul s)
                  (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
                Fin.castAdd s l := by ext; simp
          rw [hcast, Fin.addCases_left]
        simp_rw [hVrow]
        rw [Finset.sum_neg_distrib]
        have h1 := hm.sum_α_eq_zero
        rw [m.rho_one, Fin.sum_univ_castSucc, m.normalized] at h1
        linarith
      · -- shift-y row: V[k, l] = if l.val = j+1 then 1 else 0
        have hVrow : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
              if (l : ℕ) = (j : ℕ) + 1 then (1 : ℝ) else 0 := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then _
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = _
          rw [hkc_eq]
          rw [Fin.addCases_left]
          rw [if_neg hj]
          have hval : (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
              = (l : ℕ) := by simp [Fin.castAdd]
          rw [hval]
        simp_rw [hVrow]
        -- Now sum: ∑ l : Fin s, (if l.val = j+1 then 1 else 0) = 1 since j+1 < s.
        have hjlt : (j : ℕ) + 1 < s := by
          rcases lt_or_eq_of_le (Nat.succ_le_of_lt j.isLt) with h | h
          · exact h
          · exact absurd h hj
        have hexists : (⟨(j : ℕ) + 1, hjlt⟩ : Fin s) ∈ (Finset.univ : Finset (Fin s)) :=
          Finset.mem_univ _
        rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hjlt⟩ : Fin s)]
        · simp
        · intro b _ hb
          have : (b : ℕ) ≠ (j : ℕ) + 1 := by
            intro heq
            apply hb
            ext; exact heq
          rw [if_neg this]
        · intro h; exact absurd hexists h
    · -- past-f row: kc = Fin.natAdd s ⟨j, _⟩
      intro j hkc_eq
      simp only [Fin.addCases_right]
      -- Goal: ∑ l, V k (cast.symm (castAdd s l)) = 0
      by_cases hj : (j : ℕ) + 1 = s
      · -- last-f row: V[k, _] = 0
        have hVrow : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
              (0 : ℝ) := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then _
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = _
          rw [hkc_eq]
          rw [Fin.addCases_right]
          rw [if_pos hj]
        simp_rw [hVrow]
        simp
      · -- shift-f row: V[k, l] = if l.val = s + j + 1 then 1 else 0
        --   But we sum only over past-y l (l : Fin s, so l.val < s ≤ s + j + 1 always).
        have hVrow : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
              (0 : ℝ) := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then _
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = _
          rw [hkc_eq]
          rw [Fin.addCases_right]
          rw [if_neg hj]
          have hval : (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
              = (l : ℕ) := by simp [Fin.castAdd]
          rw [hval, if_neg]
          omega
        simp_rw [hVrow]
        simp
  · -- U q = 𝟙 (one-stage GLM, single equation)
    intro i
    -- Unfold toGLM and reindex Fin (2*s) → Fin (s+s).
    show (∑ x : Fin (2 * s),
            Fin.addCases (motive := fun _ => ℝ)
                (fun j : Fin s => (-m.α (Fin.castSucc j) : ℝ))
                (fun j : Fin s => (m.β (Fin.castSucc j) : ℝ))
                (Fin.cast (Nat.two_mul s) x) *
              Fin.addCases (motive := fun _ => ℝ)
                (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ))
                (Fin.cast (Nat.two_mul s) x)) = 1
    rw [show (∑ x : Fin (2 * s),
            Fin.addCases (motive := fun _ => ℝ)
                (fun j : Fin s => (-m.α (Fin.castSucc j) : ℝ))
                (fun j : Fin s => (m.β (Fin.castSucc j) : ℝ))
                (Fin.cast (Nat.two_mul s) x) *
              Fin.addCases (motive := fun _ => ℝ)
                (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ))
                (Fin.cast (Nat.two_mul s) x))
          = ∑ x : Fin (s + s),
              Fin.addCases (motive := fun _ => ℝ)
                  (fun j : Fin s => (-m.α (Fin.castSucc j) : ℝ))
                  (fun j : Fin s => (m.β (Fin.castSucc j) : ℝ)) x *
                Fin.addCases (motive := fun _ => ℝ)
                  (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ)) x from
      Fin.sum_congr' (M := ℝ)
        (fun y : Fin (s + s) =>
          Fin.addCases (motive := fun _ => ℝ)
              (fun j : Fin s => (-m.α (Fin.castSucc j) : ℝ))
              (fun j : Fin s => (m.β (Fin.castSucc j) : ℝ)) y *
            Fin.addCases (motive := fun _ => ℝ)
              (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ)) y)
        (Nat.two_mul s)]
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, mul_one, mul_zero,
      Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib]
    have h1 := hm.sum_α_eq_zero
    rw [m.rho_one, Fin.sum_univ_castSucc, m.normalized] at h1
    linarith
  · -- (B 𝟙_s) + V q' = q + q'
    -- q k = AddCases (1) (0) (Fin.cast _ k); q' k = AddCases (j) (1) (Fin.cast _ k).
    intro k
    -- ∑ j : Fin 1, B k j = B k 0.
    rw [Fin.sum_univ_one]
    -- Reindex Fin (2*s) → Fin (s+s) for the V·q' sum (mirrors subgoal 1).
    have hreindex :
        (∑ l : Fin (2 * s), m.toGLM.V k l *
            Fin.addCases (motive := fun _ => ℝ)
                (fun j : Fin s => ((j : ℕ) : ℝ)) (fun _ : Fin s => (1 : ℝ))
                (Fin.cast (Nat.two_mul s) l))
          = (∑ l : Fin s,
                m.toGLM.V k (Fin.cast (Nat.two_mul s).symm
                  (Fin.castAdd s l)) * ((l : ℕ) : ℝ))
            + (∑ l : Fin s,
                m.toGLM.V k (Fin.cast (Nat.two_mul s).symm
                  (Fin.natAdd s l))) := by
      have stepA : (∑ l : Fin (2 * s), m.toGLM.V k l *
              Fin.addCases (motive := fun _ => ℝ)
                  (fun j : Fin s => ((j : ℕ) : ℝ))
                  (fun _ : Fin s => (1 : ℝ))
                  (Fin.cast (Nat.two_mul s) l))
            = ∑ l : Fin (2 * s),
                m.toGLM.V k (Fin.cast (Nat.two_mul s).symm
                  (Fin.cast (Nat.two_mul s) l)) *
                  Fin.addCases (motive := fun _ => ℝ)
                    (fun j : Fin s => ((j : ℕ) : ℝ))
                    (fun _ : Fin s => (1 : ℝ))
                    (Fin.cast (Nat.two_mul s) l) := rfl
      rw [stepA, Fin.sum_congr' (M := ℝ)
        (fun l : Fin (s + s) =>
          m.toGLM.V k (Fin.cast (Nat.two_mul s).symm l) *
            Fin.addCases (motive := fun _ => ℝ)
              (fun j : Fin s => ((j : ℕ) : ℝ))
              (fun _ : Fin s => (1 : ℝ)) l)
        (Nat.two_mul s)]
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right, mul_one]
    rw [hreindex]
    -- Case-split on Fin.cast _ k via addCases.
    set kc : Fin (s + s) := Fin.cast (Nat.two_mul s) k with hkc_def
    refine kc.addCases (motive := fun kc' =>
        Fin.cast (Nat.two_mul s) k = kc' →
        m.toGLM.B k 0
            + ((∑ l : Fin s,
                m.toGLM.V k (Fin.cast (Nat.two_mul s).symm
                  (Fin.castAdd s l)) * ((l : ℕ) : ℝ))
              + ∑ l : Fin s,
                m.toGLM.V k (Fin.cast (Nat.two_mul s).symm
                  (Fin.natAdd s l))) =
          Fin.addCases (motive := fun _ => ℝ)
              (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ)) kc'
            + Fin.addCases (motive := fun _ => ℝ)
              (fun j : Fin s => ((j : ℕ) : ℝ)) (fun _ : Fin s => (1 : ℝ)) kc')
      ?_ ?_ rfl
    · -- past-y row: kc = Fin.castAdd s ⟨j, _⟩
      intro j hkc_eq
      simp only [Fin.addCases_left]
      -- Compute B k 0.
      have hBk : m.toGLM.B k 0 =
          if (j : ℕ) + 1 = s then m.β (Fin.last s) else (0 : ℝ) := by
        show Fin.addCases (motive := fun _ => ℝ)
            (fun j' : Fin s =>
              if (j' : ℕ) + 1 = s then m.β (Fin.last s) else 0)
            (fun j' : Fin s => if (j' : ℕ) + 1 = s then 1 else 0)
            (Fin.cast (Nat.two_mul s) k) = _
        rw [hkc_eq, Fin.addCases_left]
      by_cases hj : (j : ℕ) + 1 = s
      · -- last-y row
        rw [hBk, if_pos hj]
        have hVy : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
              -m.α (Fin.castSucc l) := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then
                Fin.addCases (motive := fun _ => ℝ)
                    (fun q : Fin s => -m.α (Fin.castSucc q))
                    (fun q : Fin s => m.β (Fin.castSucc q))
                    (Fin.cast (Nat.two_mul s)
                      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)))
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = -m.α (Fin.castSucc l)
          rw [hkc_eq, Fin.addCases_left, if_pos hj]
          have hcast :
              Fin.cast (Nat.two_mul s)
                  (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
                Fin.castAdd s l := by ext; simp
          rw [hcast, Fin.addCases_left]
        have hVf : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
              m.β (Fin.castSucc l) := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then
                Fin.addCases (motive := fun _ => ℝ)
                    (fun q : Fin s => -m.α (Fin.castSucc q))
                    (fun q : Fin s => m.β (Fin.castSucc q))
                    (Fin.cast (Nat.two_mul s)
                      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)))
                else if (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = m.β (Fin.castSucc l)
          rw [hkc_eq, Fin.addCases_left, if_pos hj]
          have hcast :
              Fin.cast (Nat.two_mul s)
                  (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
                Fin.natAdd s l := by ext; simp
          rw [hcast, Fin.addCases_right]
        simp_rw [hVy, hVf]
        rw [show (∑ l : Fin s, -m.α (Fin.castSucc l) * ((l : ℕ) : ℝ)) =
              -∑ l : Fin s, ((l : ℕ) : ℝ) * m.α (Fin.castSucc l) by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun l _ => by ring)]
        -- Now: m.β (last s) + (-∑ l, l · α (castSucc l) + ∑ l, β (castSucc l)) = 1 + j
        -- Use deriv_match: ∑ j : Fin (s+1), (j : ℝ) · α j = m.sigma 1 = ∑ j : Fin (s+1), β j.
        have hderiv := hm.deriv_match
        rw [m.sigma_one,
            Fin.sum_univ_castSucc (f := fun j : Fin (s+1) => ((j : ℕ) : ℝ) * m.α j),
            Fin.sum_univ_castSucc (f := fun j : Fin (s+1) => m.β j)] at hderiv
        simp only [Fin.val_castSucc, Fin.val_last, m.normalized, mul_one] at hderiv
        -- hderiv: (∑ l, (l : ℝ) · α (castSucc l)) + s = (∑ l, β (castSucc l)) + β (last s)
        have hjval : ((j : ℕ) : ℝ) = (s : ℝ) - 1 := by
          have : ((j : ℕ) : ℝ) + 1 = (s : ℝ) := by
            exact_mod_cast hj
          linarith
        rw [hjval]
        linarith
      · -- shift-y row: B k 0 = 0, only V·q' contribution from past-y at l = j+1.
        rw [hBk, if_neg hj]
        have hVy : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
              if (l : ℕ) = (j : ℕ) + 1 then (1 : ℝ) else 0 := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then _
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = _
          rw [hkc_eq, Fin.addCases_left, if_neg hj]
          have hval : (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
              = (l : ℕ) := by simp [Fin.castAdd]
          rw [hval]
        have hVf : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
              (0 : ℝ) := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then _
                else if (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = _
          rw [hkc_eq, Fin.addCases_left, if_neg hj]
          have hval : (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l) : Fin (2*s)).val
              = s + (l : ℕ) := by simp [Fin.natAdd]
          rw [hval, if_neg]
          omega
        simp_rw [hVy, hVf]
        have hjlt : (j : ℕ) + 1 < s := by
          rcases lt_or_eq_of_le (Nat.succ_le_of_lt j.isLt) with h | h
          · exact h
          · exact absurd h hj
        rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hjlt⟩ : Fin s)]
        · push_cast
          simp
          ring
        · intro b _ hb
          have : (b : ℕ) ≠ (j : ℕ) + 1 := by
            intro heq; apply hb; ext; exact heq
          rw [if_neg this, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
    · -- past-f row: kc = Fin.natAdd s ⟨j, _⟩
      intro j hkc_eq
      simp only [Fin.addCases_right]
      -- Compute B k 0.
      have hBk : m.toGLM.B k 0 =
          if (j : ℕ) + 1 = s then (1 : ℝ) else (0 : ℝ) := by
        show Fin.addCases (motive := fun _ => ℝ)
            (fun j' : Fin s =>
              if (j' : ℕ) + 1 = s then m.β (Fin.last s) else 0)
            (fun j' : Fin s => if (j' : ℕ) + 1 = s then 1 else 0)
            (Fin.cast (Nat.two_mul s) k) = _
        rw [hkc_eq, Fin.addCases_right]
      by_cases hj : (j : ℕ) + 1 = s
      · -- last-f row: V[k, _] = 0 everywhere; B k 0 = 1.
        rw [hBk, if_pos hj]
        have hVy : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
              (0 : ℝ) := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then _
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = _
          rw [hkc_eq, Fin.addCases_right, if_pos hj]
        have hVf : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
              (0 : ℝ) := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then _
                else if (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = _
          rw [hkc_eq, Fin.addCases_right, if_pos hj]
        simp_rw [hVy, hVf]
        simp
      · -- shift-f row: B k 0 = 0, V·q' nonzero only at l_f = j+1.
        rw [hBk, if_neg hj]
        have hVy : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
              (0 : ℝ) := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then _
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = _
          rw [hkc_eq, Fin.addCases_right, if_neg hj]
          have hval : (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l) : Fin (2*s)).val
              = (l : ℕ) := by simp [Fin.castAdd]
          rw [hval, if_neg]
          omega
        have hVf : ∀ l : Fin s,
            m.toGLM.V k (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
              if (l : ℕ) = (j : ℕ) + 1 then (1 : ℝ) else 0 := by
          intro l
          show Fin.addCases (motive := fun _ => ℝ)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then _
                else if (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l) : Fin (2*s)).val
                    = (j' : ℕ) + 1 then 1 else 0)
              (fun j' : Fin s => if (j' : ℕ) + 1 = s then 0
                else if (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l) : Fin (2*s)).val
                    = s + (j' : ℕ) + 1 then 1 else 0)
              (Fin.cast (Nat.two_mul s) k) = _
          rw [hkc_eq, Fin.addCases_right, if_neg hj]
          have hval : (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l) : Fin (2*s)).val
              = s + (l : ℕ) := by simp [Fin.natAdd]
          rw [hval]
          by_cases hlj : (l : ℕ) = (j : ℕ) + 1
          · rw [if_pos (by omega), if_pos hlj]
          · rw [if_neg (by omega), if_neg hlj]
        simp_rw [hVy, hVf]
        have hjlt : (j : ℕ) + 1 < s := by
          rcases lt_or_eq_of_le (Nat.succ_le_of_lt j.isLt) with h | h
          · exact h
          · exact absurd h hj
        -- The past-y sum is identically zero; clear it.
        rw [show (∑ l : Fin s, (0 : ℝ) * ((l : ℕ) : ℝ)) = 0 by simp,
            zero_add, zero_add]
        rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hjlt⟩ : Fin s)]
        · rw [if_pos rfl]; norm_num
        · intro b _ hb
          have : (b : ℕ) ≠ (j : ℕ) + 1 := by
            intro heq; apply hb; ext; exact heq
          rw [if_neg this]
        · intro h; exact absurd (Finset.mem_univ _) h

end LMM
