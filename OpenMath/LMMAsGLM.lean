import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.GeneralLinearMethod
import OpenMath.DahlquistEquivalence
import OpenMath.BDF

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

/-- Shape projection lemma for non-last past-`y` shift rows of the `B` block:
the `B` row vanishes because the `B`-block input is unused on shift rows. -/
@[simp] theorem toGLM_B_castAdd_shift_apply (m : LMM s) (j : Fin s)
    (hj : (j : ℕ) + 1 ≠ s) :
    m.toGLM.B (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) 0 = 0 := by
  simp only [toGLM]
  have hrow :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) =
        Fin.castAdd s j := by
    ext
    simp
  rw [hrow, Fin.addCases_left, if_neg hj]

/-- Shape projection lemma for the last past-`y` row of the `B` block:
carries the implicit-stage coefficient `m.β (Fin.last s)` from `f(Y)`. -/
@[simp] theorem toGLM_B_castAdd_last_apply (m : LMM s) (j : Fin s)
    (hj : (j : ℕ) + 1 = s) :
    m.toGLM.B (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) 0 =
      m.β (Fin.last s) := by
  simp only [toGLM]
  have hrow :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) =
        Fin.castAdd s j := by
    ext
    simp
  rw [hrow, Fin.addCases_left, if_pos hj]

/-- Shape projection lemma for non-last past-`h*f` shift rows of the `B` block:
the `B` row vanishes because shift rows do not consume `f(Y)`. -/
@[simp] theorem toGLM_B_natAdd_shift_apply (m : LMM s) (j : Fin s)
    (hj : (j : ℕ) + 1 ≠ s) :
    m.toGLM.B (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) 0 = 0 := by
  simp only [toGLM]
  have hrow :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) =
        Fin.natAdd s j := by
    ext
    simp
  rw [hrow, Fin.addCases_right, if_neg hj]

/-- Shape projection lemma for the last past-`h*f` row of the `B` block:
emits the canonical `1` carrying `f(Y)` to the new `h · f` slot. -/
@[simp] theorem toGLM_B_natAdd_last_apply (m : LMM s) (j : Fin s)
    (hj : (j : ℕ) + 1 = s) :
    m.toGLM.B (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) 0 = 1 := by
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

/-- §512 Phase E helper. Monotonicity of `(M_max m) ^ n` in `n`. -/
private theorem M_max_pow_le_M_max_pow_of_le
    (m : LMM s) {a b : ℕ} (h : a ≤ b) :
    (M_max m) ^ a ≤ (M_max m) ^ b :=
  pow_le_pow_right₀ (one_le_M_max m) h

/-- §512 Phase E. Every zero-stable LMM embeds as a §510-stable GLM.
This combines Phase B (`toGLM_V_iter_natAdd_eq_zero_of_le`), Phase C
(`toGLM_V_iter_le`) and Phase D step 4
(`toGLM_y_half_iter_complex_norm_bound`). -/
theorem toGLM_isStable (m : LMM s) (hzs : m.IsZeroStable) :
    m.toGLM.IsStable := by
  obtain ⟨My, hMy_nonneg, hMy⟩ := toGLM_y_half_iter_complex_norm_bound m hzs
  set Mbase : ℝ := (M_max m) ^ s with hMbase_def
  have hMbase_nonneg : 0 ≤ Mbase := by
    rw [hMbase_def]; exact pow_nonneg (M_max_nonneg m) s
  set M' : ℝ := My * Mbase + Mbase with hM'_def
  have hMyMb_nonneg : 0 ≤ My * Mbase := mul_nonneg hMy_nonneg hMbase_nonneg
  have hM'_nonneg : 0 ≤ M' := by rw [hM'_def]; linarith
  have hMyMb_le_M' : My * Mbase ≤ M' := by rw [hM'_def]; linarith
  have hMbase_le_M' : Mbase ≤ M' := by rw [hM'_def]; linarith
  refine ⟨M', hM'_nonneg, ?_⟩
  intro n q hq k
  -- Reindex k via Fin.cast (Nat.two_mul s) into Fin (s + s).
  set kc : Fin (s + s) := Fin.cast (Nat.two_mul s) k with hkc_def
  have hk : k = Fin.cast (Nat.two_mul s).symm kc := by
    rw [hkc_def]; ext; simp
  rw [hk]
  refine kc.addCases (motive := fun kc' =>
      |((fun v : Fin (2 * s) → ℝ =>
            fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[n] q)
        (Fin.cast (Nat.two_mul s).symm kc')| ≤ M') ?_ ?_
  · -- y-half slot.
    intro k'
    rcases Nat.lt_or_ge n s with hns | hns
    · -- n < s: Phase C bound.
      have hbound := toGLM_V_iter_le m q 1 hq n
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k'))
      rw [mul_one] at hbound
      have hpow : (M_max m) ^ n ≤ Mbase :=
        M_max_pow_le_M_max_pow_of_le m (le_of_lt hns)
      linarith
    · -- s ≤ n: companion-step bound.
      set j : ℕ := n - s with hj_def
      have hns_eq : s + j = n := by rw [hj_def]; omega
      -- Inner-norm bound: complex y-half of V^[s] q has Pi-norm ≤ Mbase.
      have hVs_yhalf_norm :
          ‖fun k0 : Fin s =>
            ((toGLM_y_half ((fun v : Fin (2 * s) → ℝ =>
                fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[s] q) k0
              : ℝ) : ℂ)‖
          ≤ Mbase := by
        rw [pi_norm_le_iff_of_nonneg hMbase_nonneg]
        intro i
        rw [Complex.norm_real, Real.norm_eq_abs]
        unfold toGLM_y_half
        have := toGLM_V_iter_le m q 1 hq s
          (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s i))
        rw [mul_one] at this
        rw [hMbase_def]
        exact this
      -- Apply Phase D step 4 with n := s, j := j.
      have hMy_app := hMy q s (le_refl s) j
      have hMy_total :
          ‖fun k0 : Fin s =>
            ((toGLM_y_half ((fun v : Fin (2 * s) → ℝ =>
                fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[s + j] q)
              k0 : ℝ) : ℂ)‖
          ≤ My * Mbase :=
        hMy_app.trans (mul_le_mul_of_nonneg_left hVs_yhalf_norm hMy_nonneg)
      -- Single-coordinate extraction via norm_le_pi_norm.
      have hsingle :
          ‖((toGLM_y_half ((fun v : Fin (2 * s) → ℝ =>
              fun k' : Fin (2 * s) => ∑ l, m.toGLM.V k' l * v l)^[s + j] q) k'
            : ℝ) : ℂ)‖
          ≤ My * Mbase :=
        (norm_le_pi_norm _ k').trans hMy_total
      rw [Complex.norm_real, Real.norm_eq_abs] at hsingle
      -- Identify: toGLM_y_half (V^[s+j] q) k' = (V^[n] q) (cast.symm (castAdd s k')).
      unfold toGLM_y_half at hsingle
      rw [hns_eq] at hsingle
      exact hsingle.trans hMyMb_le_M'
  · -- h·f-half slot.
    intro k'
    rcases Nat.lt_or_ge n s with hns | hns
    · -- n < s: Phase C bound.
      have hbound := toGLM_V_iter_le m q 1 hq n
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k'))
      rw [mul_one] at hbound
      have hpow : (M_max m) ^ n ≤ Mbase :=
        M_max_pow_le_M_max_pow_of_le m (le_of_lt hns)
      linarith
    · -- s ≤ n: Phase B says the slot is zero.
      have hzero := toGLM_V_iter_natAdd_eq_zero_of_le m q n hns k'
      rw [hzero, abs_zero]
      exact hM'_nonneg

/-- §512 Phase E. Every consistent and zero-stable LMM embeds as a §512
convergent GLM. -/
theorem toGLM_isConvergent (m : LMM s)
    (hcon : m.IsConsistent) (hzs : m.IsZeroStable) :
    m.toGLM.IsConvergent :=
  ⟨m.toGLM_isConsistent hcon, m.toGLM_isStable hzs⟩

/-! ## §521 — Stability defect for LMM as GLM -/

/-- §510/§521 Nordsieck preconsistency vector for an LMM-as-GLM:
`1` on past-`y` slots, `0` on past-`h·f` slots. Identical to the
witness used in `toGLM_isConsistent`. -/
noncomputable def nordsieckQ (s : ℕ) : Fin (2 * s) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ))
    (Fin.cast (Nat.two_mul s) k)

@[simp] theorem nordsieckQ_castAdd (k : Fin s) :
    nordsieckQ s (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) = 1 := by
  unfold nordsieckQ
  have hcast :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) =
        Fin.castAdd s k := by
    ext; simp
  rw [hcast, Fin.addCases_left]

@[simp] theorem nordsieckQ_natAdd (k : Fin s) :
    nordsieckQ s (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) = 0 := by
  unfold nordsieckQ
  have hcast :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) =
        Fin.natAdd s k := by
    ext; simp
  rw [hcast, Fin.addCases_right]

@[simp] theorem toGLM_qℂ_nordsieckQ_castAdd (k : Fin s) :
    GeneralLinearMethod.qℂ (nordsieckQ s)
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) = (1 : ℂ) := by
  unfold GeneralLinearMethod.qℂ
  rw [nordsieckQ_castAdd]
  norm_num

@[simp] theorem toGLM_qℂ_nordsieckQ_natAdd (k : Fin s) :
    GeneralLinearMethod.qℂ (nordsieckQ s)
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) = (0 : ℂ) := by
  unfold GeneralLinearMethod.qℂ
  rw [nordsieckQ_natAdd]
  norm_num

/-- §521 — `V · q = q` for the Nordsieck preconsistency vector.
Extracted from cycle 614's `toGLM_isConsistent` first subgoal. -/
theorem toGLM_V_nordsieckQ_eq (m : LMM s) (hm : m.IsConsistent)
    (k : Fin (2 * s)) :
    ∑ l, m.toGLM.V k l * nordsieckQ s l = nordsieckQ s k := by
  -- Reindex Fin (2*s) → Fin (s+s) and split into past-y / past-f halves.
  have hreindex :
      (∑ l : Fin (2 * s), m.toGLM.V k l * nordsieckQ s l)
        = (∑ l : Fin s, m.toGLM.V k (Fin.cast (Nat.two_mul s).symm
              (Fin.castAdd s l))) := by
    have stepA : (∑ l : Fin (2 * s), m.toGLM.V k l * nordsieckQ s l)
          = ∑ l : Fin (2 * s),
              m.toGLM.V k (Fin.cast (Nat.two_mul s).symm
                (Fin.cast (Nat.two_mul s) l)) *
                Fin.addCases (motive := fun _ => ℝ)
                  (fun _ : Fin s => (1 : ℝ))
                  (fun _ : Fin s => (0 : ℝ))
                  (Fin.cast (Nat.two_mul s) l) := by
      apply Finset.sum_congr rfl
      intro l _
      have hcast : Fin.cast (Nat.two_mul s).symm
              (Fin.cast (Nat.two_mul s) l) = l := by ext; simp
      rw [hcast]
      rfl
    rw [stepA]
    rw [Fin.sum_congr' (M := ℝ)
      (fun l : Fin (s + s) =>
        m.toGLM.V k (Fin.cast (Nat.two_mul s).symm l) *
          Fin.addCases (motive := fun _ => ℝ)
            (fun _ : Fin s => (1 : ℝ)) (fun _ : Fin s => (0 : ℝ)) l)
      (Nat.two_mul s)]
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right, mul_one, mul_zero,
      Finset.sum_const_zero, add_zero]
  rw [hreindex]
  -- Case-split on (Fin.cast _ k) via addCases.
  set kc : Fin (s + s) := Fin.cast (Nat.two_mul s) k with hkc_def
  refine kc.addCases (motive := fun kc' =>
      Fin.cast (Nat.two_mul s) k = kc' →
      (∑ l : Fin s, m.toGLM.V k
            (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l))) =
        nordsieckQ s k)
    ?_ ?_ rfl
  · -- past-y row
    intro j hkc_eq
    have hqk : nordsieckQ s k = 1 := by
      unfold nordsieckQ
      rw [hkc_eq, Fin.addCases_left]
    rw [hqk]
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
    · -- shift-y row
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
  · -- past-f row
    intro j hkc_eq
    have hqk : nordsieckQ s k = 0 := by
      unfold nordsieckQ
      rw [hkc_eq, Fin.addCases_right]
    rw [hqk]
    by_cases hj : (j : ℕ) + 1 = s
    · -- last-f row
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
    · -- shift-f row
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

/-- §521 — Row formula for the LMM-as-GLM stability defect on the
Nordsieck preconsistency vector. Tautological unfolding mirroring
`ButcherTableau.toGLM_stabilityDefect_apply` on the RK side; supplies
a `simp`-shaped restatement so downstream `HasStabilityOrder`-style
work does not have to re-unfold `stabilityDefect` and `mulVec`. -/
theorem toGLM_stabilityDefect_apply (m : LMM s) (hm : m.IsConsistent)
    (z : ℂ) (k : Fin (2 * s)) :
    m.toGLM.stabilityDefect (nordsieckQ s) z k =
      (∑ l, m.toGLM.stabilityMatrix z k l *
              GeneralLinearMethod.qℂ (nordsieckQ s) l)
        - Complex.exp z * GeneralLinearMethod.qℂ (nordsieckQ s) k := by
  have _ : m.IsConsistent := hm
  simp [GeneralLinearMethod.stabilityDefect, Matrix.mulVec,
    dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- §521 — At a past-`h·f` slot the defect drops the `exp z` term
because `qℂ_natAdd = 0`. -/
theorem toGLM_stabilityDefect_natAdd (m : LMM s)
    (hm : m.IsConsistent) (z : ℂ) (k : Fin s) :
    m.toGLM.stabilityDefect (nordsieckQ s) z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) =
      ∑ l, m.toGLM.stabilityMatrix z
              (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) l *
        GeneralLinearMethod.qℂ (nordsieckQ s) l := by
  rw [toGLM_stabilityDefect_apply m hm, toGLM_qℂ_nordsieckQ_natAdd]
  ring

/-- §521 — Headline mirror of `ButcherTableau.toGLM_stabilityDefect_zero`:
the stability defect at `z = 0` vanishes on the Nordsieck preconsistency
vector. -/
theorem toGLM_stabilityDefect_zero (m : LMM s) (hm : m.IsConsistent) :
    m.toGLM.stabilityDefect (nordsieckQ s) 0 = 0 := by
  apply GeneralLinearMethod.stabilityDefect_zero
  intro k
  exact m.toGLM_V_nordsieckQ_eq hm k

/-- **§530 / §503 bridge** — Every consistent LMM embeds as a
GLM of order ≥ 1. This is the LMM-side mirror of
`ButcherTableau.toGLM_hasOrderGe1` and is a one-line wrapper around
`toGLM_isConsistent`. -/
theorem toGLM_hasOrderGe1 (m : LMM s) (hm : m.IsConsistent) :
    m.toGLM.HasOrderGe1 :=
  m.toGLM_isConsistent hm

end LMM

/-! ### §530 LMM-as-GLM order-≥ 1 witnesses

Concrete consistent LMMs of step `s = 1` (forward Euler, backward Euler,
trapezoidal rule) and `s = 2` (BDF2) exhibit `HasOrderGe1` for their
GLM embeddings. Each witness is a one-line application of
`LMM.toGLM_hasOrderGe1` to the corresponding `_consistent` lemma in
`OpenMath/MultistepMethods.lean`. -/

theorem forwardEuler_toGLM_hasOrderGe1 :
    forwardEuler.toGLM.HasOrderGe1 :=
  forwardEuler.toGLM_hasOrderGe1 forwardEuler_consistent

theorem backwardEuler_toGLM_hasOrderGe1 :
    backwardEuler.toGLM.HasOrderGe1 :=
  backwardEuler.toGLM_hasOrderGe1 backwardEuler_consistent

theorem trapezoidalRule_toGLM_hasOrderGe1 :
    trapezoidalRule.toGLM.HasOrderGe1 :=
  trapezoidalRule.toGLM_hasOrderGe1 trapezoidalRule_consistent

theorem bdf2_toGLM_hasOrderGe1 :
    bdf2.toGLM.HasOrderGe1 :=
  bdf2.toGLM_hasOrderGe1 bdf2_consistent

theorem adamsBashforth2_toGLM_hasOrderGe1 :
    adamsBashforth2.toGLM.HasOrderGe1 :=
  adamsBashforth2.toGLM_hasOrderGe1 adamsBashforth2_consistent

theorem adamsBashforth3_toGLM_hasOrderGe1 :
    adamsBashforth3.toGLM.HasOrderGe1 :=
  adamsBashforth3.toGLM_hasOrderGe1 adamsBashforth3_consistent

theorem adamsBashforth4_toGLM_hasOrderGe1 :
    adamsBashforth4.toGLM.HasOrderGe1 :=
  adamsBashforth4.toGLM_hasOrderGe1 adamsBashforth4_consistent

theorem adamsBashforth5_toGLM_hasOrderGe1 :
    adamsBashforth5.toGLM.HasOrderGe1 :=
  adamsBashforth5.toGLM_hasOrderGe1 adamsBashforth5_consistent

/-! ### §530 LMM-as-GLM order-≥ 2 witness — trapezoidal rule

The trapezoidal rule (`s = 1`, two GLM input slots `Fin 2`) embeds as a
GLM of order ≥ 2. The witness uses `(q, q', q'')` with
`q = (1, 0)` (past-`y` indicator), `q' = (0, 1)` (Nordsieck `h·y'_n`
content), and `q'' = 0` — the second-derivative identity collapses to
`2 (B c) = q + 2 q'` because the trapezoid `B`-block already carries the
order-2 Taylor content directly (`B[0,0] = 1/2`, `B[1,0] = 1`,
`c_0 = 1`). -/
theorem trapezoidalRule_toGLM_hasOrderGe2 :
    trapezoidalRule.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 1) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 1) k),
    fun k : Fin (2 * 1) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 1 => ((j : ℕ) : ℝ)) (fun _ : Fin 1 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 1) k),
    fun _ : Fin (2 * 1) => (0 : ℝ),
    ?_, ?_, ?_, ?_⟩
  · -- V q = q. The witness is `LMM.nordsieckQ 1` definitionally; reuse the
    -- exposed cycle 614 lemma.
    exact trapezoidalRule.toGLM_V_nordsieckQ_eq trapezoidalRule_consistent
  · -- U q = 𝟙. Single stage; one obligation indexed by `i : Fin 1`.
    intro i; fin_cases i
    simp [LMM.toGLM, trapezoidalRule, Fin.addCases]
  · -- (B 𝟙) + V q' = q + q'. The trapezoid coefficients close both `Fin 2`
    -- cases by direct expansion.
    intro k; fin_cases k
    all_goals simp [LMM.toGLM, trapezoidalRule, Fin.addCases, Fin.sum_univ_two]
    all_goals norm_num
  · -- 2 (B c) + V q'' = q + 2 q' + q''. With `q'' ≡ 0` this collapses to
    -- `2 (B c) = q + 2 q'`; `c_0 = 1` for trapezoid and both rows verify.
    intro k; fin_cases k
    all_goals simp [LMM.toGLM, trapezoidalRule, Fin.addCases, Fin.sum_univ_two]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — BDF2

BDF2 (`s = 2`, four GLM input slots `Fin 4`) embeds as a GLM of order ≥ 2.
The witness uses the Nordsieck Taylor-moment table:
`q' j = (j : ℝ)` on past-`y` and `1` on past-`h·f`,
`q'' j = (j : ℝ)²` on past-`y` and `2 (j : ℝ)` on past-`h·f`. For
BDF2 (s = 2) this gives `q'' = (0, 1, 0, 2)`, which matches the
constraint solution of the second-derivative compatibility identity. -/
theorem bdf2_toGLM_hasOrderGe2 :
    bdf2.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 2 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    ?_, ?_, ?_, ?_⟩
  · exact bdf2.toGLM_V_nordsieckQ_eq bdf2_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf2, Fin.addCases, Fin.sum_univ_succ]; norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 2-step

`adamsBashforth2` (`s = 2`, four GLM input slots `Fin 4`, explicit with
`β_s = 0`) embeds as a GLM of order ≥ 2. The witness uses the natural
Nordsieck Taylor template (no shift): `q' j = j` on past-`y` and `1`
on past-`h·f`, `q'' j = j²` on past-`y` and `2 j` on past-`h·f`.
Because AB2 is explicit, the implicit-row contribution (β_s · …)
vanishes, making this a strictly easier case than BDF2. -/
theorem adamsBashforth2_toGLM_hasOrderGe2 :
    adamsBashforth2.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 2 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    ?_, ?_, ?_, ?_⟩
  · exact adamsBashforth2.toGLM_V_nordsieckQ_eq adamsBashforth2_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth2, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 3-step

`adamsBashforth3` (`s = 3`, six GLM input slots `Fin 6`, explicit with
`β_s = 0`, order 3) embeds as a GLM of order ≥ 2. The witness reuses the
cycle-782 AB2 natural Nordsieck Taylor template (no shift):
`q' j = j` on past-`y` and `1` on past-`h·f`, `q'' j = j²` on past-`y`
and `2 j` on past-`h·f`. Because AB3 is explicit (`β_s = 0`), the
implicit-row contributions vanish in every obligation. -/
theorem adamsBashforth3_toGLM_hasOrderGe2 :
    adamsBashforth3.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    ?_, ?_, ?_, ?_⟩
  · exact adamsBashforth3.toGLM_V_nordsieckQ_eq adamsBashforth3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Moulton 3-step

`adamsMoulton3` (`s = 3`, six GLM input slots `Fin 6`, implicit, order 4)
embeds as a GLM of order ≥ 2. Same natural Nordsieck Taylor template as
BDF2 (`q'' j = j²` on past-`y`, `2 j` on past-`h·f`); the
`(Uq'')_0`-shift used at HasOrderGe3 for AM2 is not needed at level 2. -/
theorem adamsMoulton3_toGLM_hasOrderGe2 :
    adamsMoulton3.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    ?_, ?_, ?_, ?_⟩
  · exact adamsMoulton3.toGLM_V_nordsieckQ_eq adamsMoulton3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

theorem adamsMoulton3_toGLM_hasOrderGe1 :
    adamsMoulton3.toGLM.HasOrderGe1 :=
  adamsMoulton3_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 2 witness — BDF3

`bdf3` (`s = 3`, six GLM input slots `Fin 6`, implicit, order 3) embeds
as a GLM of order ≥ 2. Same natural Nordsieck Taylor template as BDF2.
HasOrderGe3 hits the heartbeat cap on the q''' obligation (cycle 780),
but HasOrderGe2 — only q'/q'' on `Fin 6` — closes within budget. -/
theorem bdf3_toGLM_hasOrderGe2 :
    bdf3.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    fun k : Fin (2 * 3) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 3) k),
    ?_, ?_, ?_, ?_⟩
  · exact bdf3.toGLM_V_nordsieckQ_eq bdf3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ]; norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

theorem bdf3_toGLM_hasOrderGe1 :
    bdf3.toGLM.HasOrderGe1 :=
  bdf3_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Bashforth 4-step

`adamsBashforth4` (`s = 4`, eight GLM input slots `Fin 8`, explicit with
`β_s = 0`, order 4) embeds as a GLM of order ≥ 2. Same natural Nordsieck
Taylor template as AB2/AB3 (no shift). -/
theorem adamsBashforth4_toGLM_hasOrderGe2 :
    adamsBashforth4.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    ?_, ?_, ?_, ?_⟩
  · exact adamsBashforth4.toGLM_V_nordsieckQ_eq adamsBashforth4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 2 witness — Adams–Moulton 4-step

`adamsMoulton4` (`s = 4`, eight GLM input slots `Fin 8`, implicit, order 5)
embeds as a GLM of order ≥ 2. Same natural Nordsieck Taylor template as
AM3/BDF3. -/
theorem adamsMoulton4_toGLM_hasOrderGe2 :
    adamsMoulton4.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    ?_, ?_, ?_, ?_⟩
  · exact adamsMoulton4.toGLM_V_nordsieckQ_eq adamsMoulton4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

theorem adamsMoulton4_toGLM_hasOrderGe1 :
    adamsMoulton4.toGLM.HasOrderGe1 :=
  adamsMoulton4_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 2 witness — BDF4

`bdf4` (`s = 4`, eight GLM input slots `Fin 8`, implicit, order 4) embeds
as a GLM of order ≥ 2. Same natural Nordsieck Taylor template as BDF3. -/
theorem bdf4_toGLM_hasOrderGe2 :
    bdf4.toGLM.HasOrderGe2 := by
  refine ⟨
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    fun k : Fin (2 * 4) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2)
      (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 4) k),
    ?_, ?_, ?_, ?_⟩
  · exact bdf4.toGLM_V_nordsieckQ_eq bdf4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ]; norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

theorem bdf4_toGLM_hasOrderGe1 :
    bdf4.toGLM.HasOrderGe1 :=
  bdf4_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Moulton 2-step

`adamsMoulton2` (`s = 2`, four GLM input slots `Fin 4`, order 3) embeds
as a GLM of order ≥ 3. The naive Nordsieck Taylor template
`q'' = j², 2j` and `q''' = j³, 3j²` does **not** satisfy
`HasOrderGe3` for any LMM with non-zero `(U q'')_0` because the
predicate's `m₂_j := (Ac)_j + (Uq'')_j` term hides an extra
`3 · (B (Uq''))_k` mismatch from the natural Taylor identity. The fix
is to shift `q''_{past-y}` by `-C` where
`C := s² - 2 · β_s · s = (Uq'')_0_natural`, which forces
`(Uq'')_0 = 0` and restores `m₂_0 = (Ac)_0 = β_s · c_0`. The
corresponding `q'''` shift is `q'''_{past-y j} := j³ - 3·C·j` and
`q'''_{past-f j} := 3·(j² - C)`. For AM2 (`s = 2, β_s = 5/12`) this
gives `C = 7/3`. -/
theorem adamsMoulton2_toGLM_hasOrderGe3 :
    adamsMoulton2.toGLM.HasOrderGe3 := by
  refine ⟨
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (0 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ)) (fun _ : Fin 2 => (1 : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ) ^ 2 - 7/3)
      (fun j : Fin 2 => 2 * ((j : ℕ) : ℝ))
      (Fin.cast (Nat.two_mul 2) k),
    fun k : Fin (2 * 2) => Fin.addCases (motive := fun _ => ℝ)
      (fun j : Fin 2 => ((j : ℕ) : ℝ) ^ 3 - 7 * ((j : ℕ) : ℝ))
      (fun j : Fin 2 => 3 * (((j : ℕ) : ℝ) ^ 2 - 7/3))
      (Fin.cast (Nat.two_mul 2) k),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact adamsMoulton2.toGLM_V_nordsieckQ_eq adamsMoulton2_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsMoulton2, Fin.addCases, Fin.sum_univ_succ]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton2, Fin.addCases, Fin.sum_univ_succ]
    all_goals norm_num

/-- §530 projection — `adamsMoulton2.toGLM` has order ≥ 2 by dropping
the third-derivative obligation from `adamsMoulton2_toGLM_hasOrderGe3`. -/
theorem adamsMoulton2_toGLM_hasOrderGe2 :
    adamsMoulton2.toGLM.HasOrderGe2 :=
  adamsMoulton2_toGLM_hasOrderGe3.toHasOrderGe2

/-- §530 projection — `adamsMoulton2.toGLM` has order ≥ 1 by dropping
the second-derivative obligation. -/
theorem adamsMoulton2_toGLM_hasOrderGe1 :
    adamsMoulton2.toGLM.HasOrderGe1 :=
  adamsMoulton2_toGLM_hasOrderGe2.toHasOrderGe1

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Bashforth 3-step

`adamsBashforth3` (`s = 3`, six GLM input slots `Fin 6`, explicit with
`β_s = 0`, order 3) embeds as a GLM of order ≥ 3. The naive Nordsieck
template `q'' = j², 2j` and `q''' = j³, 3j²` does **not** satisfy
`HasOrderGe3` for AB3: the third-derivative obligation at the
last past-`f` row `k = 5` reduces to `54 = 27`, off by `(U q'')_0 = 9`.

For AB3, `(U q'')_{0, natural}` evaluates to
`-α₂ · 2² + β₀ · 0 + β₁ · 2 + β₂ · 4 = 4 + 5 = 9` (matching the cycle
780 formula `s² − 2 β_s s = 9` with `β_s = 0`). The shift `C₂ = 9`
sets `q''_{past-y j} := j² − 9` and forces `(U q'')_0 = 0`, which
restores the q''' identity. Because `β_s = 0`, the q'' obligation has
no shift constraint at the closure row (the `β_s · c_0` term vanishes),
so any `C₂` is admissible at level 2; the constraint `C₂ = 9` comes
from the level-3 obligation at the past-`f` last row. The corresponding
`q'''` shift is `q'''_{past-y j} := j³ − 27 j` and
`q'''_{past-f j} := 3 (j² − 9)`.

Tactic structure: the q''' obligation lives on `Fin 6` and exhausts the
default `maxHeartbeats 200000` budget when discharged with a single
`all_goals simp [...]; all_goals norm_num` block (cycle 800 confirmed
the timeout at case `k = 3` even when split per `·` block in the parent
theorem). The fix is to factor the q''' obligation into its own private
helper theorem (`q'''_obligation`) so each `fin_cases k` branch gets a
fresh heartbeat budget. The four Nordsieck vectors are extracted as
`private noncomputable def`s in `namespace AB3GE3` for the same reason
— inlined `fun k => Fin.addCases ...` triggers extra elaboration work
inside the parent theorem. -/
namespace AB3GE3

private noncomputable def qN : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q'N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q''N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2 - 9)
    (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q'''N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 3 - 27 * ((j : ℕ) : ℝ))
    (fun j : Fin 3 => 3 * (((j : ℕ) : ℝ) ^ 2 - 9))
    (Fin.cast (Nat.two_mul 3) k)

private theorem q'''_obligation (k : Fin 6) :
    6 * (∑ j, adamsBashforth3.toGLM.B k j *
            ((∑ i, adamsBashforth3.toGLM.A j i *
                ((∑ i', adamsBashforth3.toGLM.A i i') +
                  ∑ l, adamsBashforth3.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth3.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth3.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num

end AB3GE3

theorem adamsBashforth3_toGLM_hasOrderGe3 :
    adamsBashforth3.toGLM.HasOrderGe3 := by
  refine ⟨AB3GE3.qN, AB3GE3.q'N, AB3GE3.q''N, AB3GE3.q'''N,
    ?_, ?_, ?_, ?_, AB3GE3.q'''_obligation⟩
  · exact adamsBashforth3.toGLM_V_nordsieckQ_eq adamsBashforth3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ, AB3GE3.qN]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      AB3GE3.qN, AB3GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth3, Fin.addCases, Fin.sum_univ_succ,
      AB3GE3.qN, AB3GE3.q'N, AB3GE3.q''N]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 3 witness — BDF3

`bdf3` (`s = 3`, six GLM input slots `Fin 6`, implicit, order 3) embeds
as a GLM of order ≥ 3. The shift constant is
`C := s² − 2 β_s s = 9 − 36/11 = 63/11` for `β_s = 6/11`. Same
helper-extraction recipe as AB3GE3: the q''' obligation lives on `Fin 6`
and exhausts the heartbeat budget when discharged inline, so the four
Nordsieck vectors and the q''' obligation are factored as `private`
declarations inside `namespace BDF3GE3`. -/
namespace BDF3GE3

private noncomputable def qN : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q'N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q''N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2 - 63/11)
    (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q'''N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 3 - 3 * (63/11) * ((j : ℕ) : ℝ))
    (fun j : Fin 3 => 3 * (((j : ℕ) : ℝ) ^ 2 - 63/11))
    (Fin.cast (Nat.two_mul 3) k)

private theorem q'''_obligation (k : Fin 6) :
    6 * (∑ j, bdf3.toGLM.B k j *
            ((∑ i, bdf3.toGLM.A j i *
                ((∑ i', bdf3.toGLM.A i i') +
                  ∑ l, bdf3.toGLM.U i l * q'N l)) +
              ∑ l, bdf3.toGLM.U j l * q''N l)) +
        ∑ l, bdf3.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num

end BDF3GE3

theorem bdf3_toGLM_hasOrderGe3 :
    bdf3.toGLM.HasOrderGe3 := by
  refine ⟨BDF3GE3.qN, BDF3GE3.q'N, BDF3GE3.q''N, BDF3GE3.q'''N,
    ?_, ?_, ?_, ?_, BDF3GE3.q'''_obligation⟩
  · exact bdf3.toGLM_V_nordsieckQ_eq bdf3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ, BDF3GE3.qN]; norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      BDF3GE3.qN, BDF3GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ,
      BDF3GE3.qN, BDF3GE3.q'N, BDF3GE3.q''N]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 3 witness — adamsMoulton3

`adamsMoulton3` (`s = 3`, six GLM input slots `Fin 6`, implicit, order 4)
embeds as a GLM of order ≥ 3. The shift constant is
`C := s² − 2 β_s s = 9 − 2·(3/8)·3 = 27/4` for `β_s = 9/24 = 3/8`.
Same helper-extraction recipe as AB3GE3 / BDF3GE3: the q''' obligation
lives on `Fin 6` and exhausts the heartbeat budget when discharged
inline, so the four Nordsieck vectors and the q''' obligation are
factored as `private` declarations inside `namespace AM3GE3`. -/
namespace AM3GE3

private noncomputable def qN : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 3 => (1 : ℝ)) (fun _ : Fin 3 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q'N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q''N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 2 - 27/4)
    (fun j : Fin 3 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 3) k)

private noncomputable def q'''N : Fin (2 * 3) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 3 => ((j : ℕ) : ℝ) ^ 3 - 3 * (27/4) * ((j : ℕ) : ℝ))
    (fun j : Fin 3 => 3 * (((j : ℕ) : ℝ) ^ 2 - 27/4))
    (Fin.cast (Nat.two_mul 3) k)

private theorem q'''_obligation (k : Fin 6) :
    6 * (∑ j, adamsMoulton3.toGLM.B k j *
            ((∑ i, adamsMoulton3.toGLM.A j i *
                ((∑ i', adamsMoulton3.toGLM.A i i') +
                  ∑ l, adamsMoulton3.toGLM.U i l * q'N l)) +
              ∑ l, adamsMoulton3.toGLM.U j l * q''N l)) +
        ∑ l, adamsMoulton3.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num

end AM3GE3

theorem adamsMoulton3_toGLM_hasOrderGe3 :
    adamsMoulton3.toGLM.HasOrderGe3 := by
  refine ⟨AM3GE3.qN, AM3GE3.q'N, AM3GE3.q''N, AM3GE3.q'''N,
    ?_, ?_, ?_, ?_, AM3GE3.q'''_obligation⟩
  · exact adamsMoulton3.toGLM_V_nordsieckQ_eq adamsMoulton3_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ, AM3GE3.qN]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      AM3GE3.qN, AM3GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
      AM3GE3.qN, AM3GE3.q'N, AM3GE3.q''N]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 3 witness — Adams–Bashforth 4-step

`adamsBashforth4` (`s = 4`, eight GLM input slots `Fin 8`, explicit with
`β_s = 0`, order 4) embeds as a GLM of order ≥ 3. The shift constant is
`C := s² − 2 β_s s = 16 − 0 = 16`. Same helper-extraction recipe as
AB3GE3 / BDF3GE3 / AM3GE3: the q''' obligation lives on `Fin 8` and
exhausts the heartbeat budget when discharged inline, so the four
Nordsieck vectors and the q''' obligation are factored as `private`
declarations inside `namespace AB4GE3`. -/
namespace AB4GE3

private noncomputable def qN : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q'N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q''N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2 - 16)
    (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q'''N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 3 - 3 * 16 * ((j : ℕ) : ℝ))
    (fun j : Fin 4 => 3 * (((j : ℕ) : ℝ) ^ 2 - 16))
    (Fin.cast (Nat.two_mul 4) k)

/-- Helper for the last `Fin 8` case (`k = 7`) of `q'''_obligation`. Factored
into its own private theorem so it gets a fresh heartbeat budget; the
inline `simp; norm_num` block consistently exhausts the 200000 limit at
this case. -/
private theorem q'''_obligation_seven :
    6 * (∑ j, adamsBashforth4.toGLM.B (⟨7, by decide⟩ : Fin 8) j *
            ((∑ i, adamsBashforth4.toGLM.A j i *
                ((∑ i', adamsBashforth4.toGLM.A i i') +
                  ∑ l, adamsBashforth4.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth4.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth4.toGLM.V (⟨7, by decide⟩ : Fin 8) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 8) :
    6 * (∑ j, adamsBashforth4.toGLM.B k j *
            ((∑ i, adamsBashforth4.toGLM.A j i *
                ((∑ i', adamsBashforth4.toGLM.A i i') +
                  ∑ l, adamsBashforth4.toGLM.U i l * q'N l)) +
              ∑ l, adamsBashforth4.toGLM.U j l * q''N l)) +
        ∑ l, adamsBashforth4.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_seven

end AB4GE3

theorem adamsBashforth4_toGLM_hasOrderGe3 :
    adamsBashforth4.toGLM.HasOrderGe3 := by
  refine ⟨AB4GE3.qN, AB4GE3.q'N, AB4GE3.q''N, AB4GE3.q'''N,
    ?_, ?_, ?_, ?_, AB4GE3.q'''_obligation⟩
  · exact adamsBashforth4.toGLM_V_nordsieckQ_eq adamsBashforth4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ, AB4GE3.qN]
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      AB4GE3.qN, AB4GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, adamsBashforth4, Fin.addCases, Fin.sum_univ_succ,
      AB4GE3.qN, AB4GE3.q'N, AB4GE3.q''N]
    all_goals norm_num

/-! ### §530 LMM-as-GLM order-≥ 3 witness — BDF 4-step

`bdf4` (`s = 4`, eight GLM input slots `Fin 8`, implicit, order 4)
embeds as a GLM of order ≥ 3. The shift constant is
`C := s² − 2 β_s s = 16 − 2·(12/25)·4 = 304/25` for `β_s = 12/25`.
Same helper-extraction recipe as AB4GE3: each `Fin 8` case in the
q''' obligation gets its own block, and any cases that exceed the
heartbeat budget are factored into separate private theorems. -/
namespace BDF4GE3

private noncomputable def qN : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun _ : Fin 4 => (1 : ℝ)) (fun _ : Fin 4 => (0 : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q'N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ)) (fun _ : Fin 4 => (1 : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q''N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 2 - 304/25)
    (fun j : Fin 4 => 2 * ((j : ℕ) : ℝ))
    (Fin.cast (Nat.two_mul 4) k)

private noncomputable def q'''N : Fin (2 * 4) → ℝ := fun k =>
  Fin.addCases (motive := fun _ => ℝ)
    (fun j : Fin 4 => ((j : ℕ) : ℝ) ^ 3 - 3 * (304/25) * ((j : ℕ) : ℝ))
    (fun j : Fin 4 => 3 * (((j : ℕ) : ℝ) ^ 2 - 304/25))
    (Fin.cast (Nat.two_mul 4) k)

/-- Helper for the last `Fin 8` case (`k = 7`) of `q'''_obligation`.
Factored into a private theorem so it gets a fresh heartbeat budget. -/
private theorem q'''_obligation_seven :
    6 * (∑ j, bdf4.toGLM.B (⟨7, by decide⟩ : Fin 8) j *
            ((∑ i, bdf4.toGLM.A j i *
                ((∑ i', bdf4.toGLM.A i i') +
                  ∑ l, bdf4.toGLM.U i l * q'N l)) +
              ∑ l, bdf4.toGLM.U j l * q''N l)) +
        ∑ l, bdf4.toGLM.V (⟨7, by decide⟩ : Fin 8) l * q'''N l =
      qN ⟨7, by decide⟩ + 3 * q'N ⟨7, by decide⟩ +
        3 * q''N ⟨7, by decide⟩ + q'''N ⟨7, by decide⟩ := by
  simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N]; norm_num

private theorem q'''_obligation (k : Fin 8) :
    6 * (∑ j, bdf4.toGLM.B k j *
            ((∑ i, bdf4.toGLM.A j i *
                ((∑ i', bdf4.toGLM.A i i') +
                  ∑ l, bdf4.toGLM.U i l * q'N l)) +
              ∑ l, bdf4.toGLM.U j l * q''N l)) +
        ∑ l, bdf4.toGLM.V k l * q'''N l =
      qN k + 3 * q'N k + 3 * q''N k + q'''N k := by
  fin_cases k
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      qN, q'N, q''N, q'''N]; norm_num
  · exact q'''_obligation_seven

end BDF4GE3

theorem bdf4_toGLM_hasOrderGe3 :
    bdf4.toGLM.HasOrderGe3 := by
  refine ⟨BDF4GE3.qN, BDF4GE3.q'N, BDF4GE3.q''N, BDF4GE3.q'''N,
    ?_, ?_, ?_, ?_, BDF4GE3.q'''_obligation⟩
  · exact bdf4.toGLM_V_nordsieckQ_eq bdf4_consistent
  · intro i; fin_cases i
    simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ, BDF4GE3.qN]
    norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      BDF4GE3.qN, BDF4GE3.q'N]
    all_goals norm_num
  · intro k; fin_cases k
    all_goals simp [LMM.toGLM, bdf4, Fin.addCases, Fin.sum_univ_succ,
      BDF4GE3.qN, BDF4GE3.q'N, BDF4GE3.q''N]
    all_goals norm_num

namespace Matrix

/-- §521 helper — auxiliary cardinality split for `Finset n`-indexed sums:
when a function `F` vanishes on subsets of size `≥ 2`, the total sum
collapses to the empty-set term plus the sum of singleton terms. Used to
isolate the rank-one contribution in `det_add_vecMulVec`. -/
private lemma sum_finset_le_one_eq
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [AddCommMonoid R]
    {F : Finset n → R} (hF : ∀ S, 2 ≤ S.card → F S = 0) :
    ∑ S : Finset n, F S = F ∅ + ∑ k, F {k} := by
  classical
  rw [show ∑ S : Finset n, F S =
        ∑ S ∈ (Finset.univ : Finset (Finset n)).filter (·.card ≤ 1), F S from ?_]
  · rw [show (Finset.univ : Finset (Finset n)).filter (·.card ≤ 1) =
          insert ∅ (Finset.univ.image (fun k : n => ({k} : Finset n))) from ?_]
    · rw [Finset.sum_insert ?_, Finset.sum_image ?_]
      · intros a _ b _ hab
        exact (Finset.singleton_inj.mp hab : a = b)
      · intro hh
        rcases Finset.mem_image.mp hh with ⟨k, _, hk⟩
        exact (Finset.singleton_ne_empty k) hk
    · ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_image]
      constructor
      · intro hS
        rcases Nat.lt_or_ge S.card 1 with h | h
        · left
          exact Finset.card_eq_zero.mp (Nat.lt_one_iff.mp h)
        · right
          have hcard : S.card = 1 := le_antisymm hS h
          obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
          exact ⟨k, hk.symm⟩
      · rintro (rfl | ⟨k, rfl⟩) <;> simp
  · apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro S _ hS
    have h2 : 2 ≤ S.card := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hS
      exact hS
    exact hF S h2

/-- §521 — Matrix determinant lemma in `vecMulVec` form, valid for any
commutative ring. No invertibility hypothesis on `M.det` is required.

This is the rank-one update form of the matrix determinant lemma:
`det(M + u vᵀ) = det M + vᵀ · adj(M) · u`. Lifting to the polynomial
ring `R[X]` produces the rank-one charpoly update; that step is left for
a downstream cycle.

Reference: Butcher §521 / classical matrix determinant lemma; the
Mathlib lemma `Matrix.det_add_replicateCol_mul_replicateRow` covers the
`IsUnit M.det` special case, and the file-level TODO there records the
general version proved here. -/
theorem det_add_vecMulVec
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : Matrix n n R) (u v : n → R) :
    (M + Matrix.vecMulVec u v).det
      = M.det + dotProduct v (M.adjugate.mulVec u) := by
  classical
  -- Step 1: rewrite `(M + vecMulVec u v).det` as a sum-over-subsets via
  -- multilinearity of `detRowAlternating` along the rows.
  rw [show (M + Matrix.vecMulVec u v).det
        = ∑ S : Finset n,
            (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
              (S.piecewise (fun i => u i • v) (fun i => M i)) from ?_]
  swap
  · rw [show (M + Matrix.vecMulVec u v).det
          = (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
              (fun i => u i • v + M i) from ?_]
    · exact (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).toMultilinearMap.map_add_univ
        (fun i => u i • v) (fun i => M i)
    · congr 1
      funext i
      ext j
      simp [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
        Pi.add_apply, smul_eq_mul, add_comm]
  -- Step 2: factor `∏ i ∈ S, u i` out of each term using `map_piecewise_smul`.
  have hpiece : ∀ S : Finset n,
      (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
          (S.piecewise (fun i => u i • v) (fun i => M i))
        = (∏ i ∈ S, u i) • (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
            (S.piecewise (fun _ => v) (fun i => M i)) := by
    intro S
    let m' : n → (n → R) := S.piecewise (fun _ => v) (fun i => M i)
    have heq : S.piecewise (fun i => u i • v) (fun i => M i)
        = S.piecewise (fun i => u i • m' i) m' := by
      funext i
      by_cases hi : i ∈ S
      · simp [Finset.piecewise_eq_of_mem _ _ _ hi, m']
      · simp [Finset.piecewise_eq_of_notMem _ _ _ hi, m']
    rw [heq]
    exact (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).toMultilinearMap.map_piecewise_smul
      u m' S
  rw [Finset.sum_congr rfl (fun S _ => hpiece S)]
  -- Step 3: terms with `|S| ≥ 2` vanish (two rows equal `v`).
  have hzero : ∀ S : Finset n, 2 ≤ S.card →
      (∏ i ∈ S, u i) • (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
        (S.piecewise (fun _ => v) (fun i => M i)) = 0 := by
    intro S hS
    obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ S, ∃ j ∈ S, i ≠ j := by
      rcases Finset.one_lt_card_iff.mp hS with ⟨i, j, hi, hj, hij⟩
      exact ⟨i, hi, j, hj, hij⟩
    have hd0 : (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
        (S.piecewise (fun _ => v) (fun i => M i)) = 0 := by
      refine (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_eq_zero_of_eq _ ?_ hij
      simp [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ hj]
    rw [hd0, smul_zero]
  -- Step 4: collapse the sum to the `|S| ≤ 1` terms.
  rw [sum_finset_le_one_eq hzero]
  -- Step 5: the `S = ∅` term is `M.det`; each `S = {k}` term is
  -- `u k * (M.updateRow k v).det`.
  have hempty : (∏ i ∈ (∅ : Finset n), u i) •
      (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
        ((∅ : Finset n).piecewise (fun _ => v) (fun i => M i)) = M.det := by
    simp
    rfl
  rw [hempty]
  have hsingleton : ∀ k : n,
      (∏ i ∈ ({k} : Finset n), u i) •
        (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
          (({k} : Finset n).piecewise (fun _ => v) (fun i => M i))
        = u k * (M.updateRow k v).det := by
    intro k
    rw [Finset.prod_singleton]
    have hpw : ({k} : Finset n).piecewise (fun _ : n => v) (fun i => M i)
        = fun i => (M.updateRow k v) i := by
      funext i
      by_cases hik : i = k
      · subst hik
        simp [Matrix.updateRow_self]
      · rw [Matrix.updateRow_ne hik]
        have : i ∉ ({k} : Finset n) := by simpa using fun h => hik h
        rw [Finset.piecewise_eq_of_notMem _ _ _ this]
    rw [hpw]
    show u k • (M.updateRow k v).det = u k * (M.updateRow k v).det
    rw [smul_eq_mul]
  rw [Finset.sum_congr rfl (fun k _ => hsingleton k)]
  -- Step 6: replace `(M.updateRow k v).det` by the cofactor expansion
  -- `∑ j, v j * adj(M) j k`, using Cramer's rule.
  have hupdate : ∀ k : n, (M.updateRow k v).det = ∑ j, v j * M.adjugate j k := by
    intro k
    rw [← Matrix.cramer_transpose_apply M v k, Matrix.cramer_eq_adjugate_mulVec,
        ← Matrix.adjugate_transpose]
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hupdate])]
  -- Step 7: reorganise the double sum as `dotProduct v (adjugate M *ᵥ u)`.
  congr 1
  rw [dotProduct]
  conv_rhs =>
    enter [2, i]
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intros k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros j _
  ring

/-- §521 — Characteristic polynomial form of the unrestricted rank-one
determinant lemma. No invertibility hypothesis on `M.det` is required. -/
theorem charpoly_add_vecMulVec
    {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]
    (M : Matrix n n R) (u v : n → R) :
    (M + Matrix.vecMulVec u v).charpoly
      = M.charpoly
        - dotProduct (fun j => Polynomial.C (v j))
            ((M.charmatrix).adjugate.mulVec
               (fun i => Polynomial.C (u i))) := by
  classical
  have hcharmatrix :
      (M + Matrix.vecMulVec u v).charmatrix =
        M.charmatrix + Matrix.vecMulVec (fun i => -Polynomial.C (u i))
          (fun j => Polynomial.C (v j)) := by
    ext i j
    simp [Matrix.charmatrix, Matrix.vecMulVec_apply]
    ring
  rw [Matrix.charpoly, hcharmatrix]
  have h := Matrix.det_add_vecMulVec (M.charmatrix)
    (fun i => -Polynomial.C (u i)) (fun j => Polynomial.C (v j))
  simpa [Matrix.charpoly, dotProduct, Matrix.mulVec, sub_eq_add_neg] using h

end Matrix

