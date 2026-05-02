import OpenMath.MultistepMethods
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

/-- §521 prep — on a non-last past-`y` shift row, the stability matrix
agrees with `m.toGLM.Vℂ` because the `B`-block contribution vanishes. -/
theorem toGLM_stabilityMatrix_castAdd_shift_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 ≠ s) (l : Fin (2 * s)) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) l =
      m.toGLM.Vℂ (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) l := by
  rw [toGLM_stabilityMatrix_apply]
  have hB : m.toGLM.Bℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) 0 = 0 := by
    show ((m.toGLM.B
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) 0 : ℝ) : ℂ) = 0
    rw [toGLM_B_castAdd_shift_apply m j hj]
    simp
  rw [hB]
  ring

/-- §521 prep — on a non-last past-`h*f` shift row, the stability matrix
agrees with `m.toGLM.Vℂ` because the `B`-block contribution vanishes. -/
theorem toGLM_stabilityMatrix_natAdd_shift_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 ≠ s) (l : Fin (2 * s)) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l =
      m.toGLM.Vℂ (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l := by
  rw [toGLM_stabilityMatrix_apply]
  have hB : m.toGLM.Bℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) 0 = 0 := by
    show ((m.toGLM.B
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) 0 : ℝ) : ℂ) = 0
    rw [toGLM_B_natAdd_shift_apply m j hj]
    simp
  rw [hB]
  ring

/-- §521 prep — on the last past-`y` row (the `y_{n+s}` output row),
the stability matrix sums the `Vℂ` part (the `α` / `β` LMM coefficients
on past-`y` and past-`h*f` slots) with the implicit-stage resolvent
contribution `z * β(last) * resolvent * Uℂ 0 l`. -/
theorem toGLM_stabilityMatrix_castAdd_last_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin (2 * s)) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) l =
      m.toGLM.Vℂ (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) l +
        z * ((m.β (Fin.last s) : ℝ) : ℂ) *
          (((1 : Matrix (Fin 1) (Fin 1) ℂ) - z • m.toGLM.Aℂ)⁻¹ 0 0) *
          m.toGLM.Uℂ 0 l := by
  rw [toGLM_stabilityMatrix_apply]
  have hB : m.toGLM.Bℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) 0 =
        ((m.β (Fin.last s) : ℝ) : ℂ) := by
    show ((m.toGLM.B
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) 0 : ℝ) : ℂ) = _
    rw [toGLM_B_castAdd_last_apply m j hj]
  rw [hB]
  ring

/-- §521 prep — on the last past-`h*f` row (the `h·f_{n+s}` output row),
the stability matrix has *no* `Vℂ` contribution (cycle 620 lemma) and
reduces to a pure resolvent-times-`Uℂ` term. -/
theorem toGLM_stabilityMatrix_natAdd_last_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin (2 * s)) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l =
      z *
          (((1 : Matrix (Fin 1) (Fin 1) ℂ) - z • m.toGLM.Aℂ)⁻¹ 0 0) *
          m.toGLM.Uℂ 0 l := by
  rw [toGLM_stabilityMatrix_apply]
  have hV : m.toGLM.Vℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l = 0 := by
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l : ℝ) : ℂ) = 0
    rw [toGLM_V_natAdd_last_apply m j hj]
    simp
  have hB : m.toGLM.Bℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) 0 = 1 := by
    show ((m.toGLM.B
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) 0 : ℝ) : ℂ) = 1
    rw [toGLM_B_natAdd_last_apply m j hj]
    simp
  rw [hV, hB]
  ring

/-- §521 prep — the `1×1` `A`-block of the LMM-as-GLM embedding is
the implicit-stage coefficient `m.β (Fin.last s)`, lifted to ℂ. -/
@[simp] theorem toGLM_Aℂ_apply (m : LMM s) :
    m.toGLM.Aℂ 0 0 = ((m.β (Fin.last s) : ℝ) : ℂ) := by
  show ((m.toGLM.A 0 0 : ℝ) : ℂ) = _
  rw [toGLM_A_apply]

/-- §521 prep — the `1×1` GLM resolvent collapses to a scalar
inverse in `z` and `m.β (Fin.last s)`. -/
theorem toGLM_resolvent_apply (m : LMM s) (z : ℂ) :
    (((1 : Matrix (Fin 1) (Fin 1) ℂ) - z • m.toGLM.Aℂ)⁻¹ 0 0)
      = 1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) := by
  have hsub : (1 : Matrix (Fin 1) (Fin 1) ℂ) - z • m.toGLM.Aℂ =
      !![1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)] := by
    ext i j
    fin_cases i; fin_cases j
    show (1 : ℂ) - z * m.toGLM.Aℂ 0 0 = _
    rw [toGLM_Aℂ_apply]
    simp
  rw [hsub, Matrix.inv_def]
  simp [Matrix.adjugate_fin_one]

/-- §521 prep — past-`y` half of the `Uℂ` block: the complex-lifted
LMM-as-GLM `U` row reads off `-m.α (Fin.castSucc k)` on past-`y` slots. -/
@[simp] theorem toGLM_Uℂ_castAdd (m : LMM s) (k : Fin s) :
    m.toGLM.Uℂ 0 (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k))
      = ((-m.α (Fin.castSucc k) : ℝ) : ℂ) := by
  show ((m.toGLM.U 0
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) : ℝ) : ℂ) = _
  simp only [toGLM]
  have hcol :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) =
        Fin.castAdd s k := by
    ext; simp
  rw [hcol, Fin.addCases_left]

/-- §521 prep — past-`h*f` half of the `Uℂ` block: the complex-lifted
LMM-as-GLM `U` row reads off `m.β (Fin.castSucc k)` on past-`h*f` slots. -/
@[simp] theorem toGLM_Uℂ_natAdd (m : LMM s) (k : Fin s) :
    m.toGLM.Uℂ 0 (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k))
      = ((m.β (Fin.castSucc k) : ℝ) : ℂ) := by
  show ((m.toGLM.U 0
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) : ℝ) : ℂ) = _
  simp only [toGLM]
  have hcol :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) =
        Fin.natAdd s k := by
    ext; simp
  rw [hcol, Fin.addCases_right]

/-- §521 — closed scalar entry on (last past-`y` row, past-`y` column). -/
theorem toGLM_stabilityMatrix_castAdd_last_castAdd_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
      ((-m.α (Fin.castSucc l) : ℝ) : ℂ) +
        z * ((m.β (Fin.last s) : ℝ) : ℂ) *
          (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
          ((-m.α (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrix_castAdd_last_apply m z j hj]
  rw [toGLM_resolvent_apply, toGLM_Uℂ_castAdd]
  have hV : m.toGLM.Vℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
        ((-m.α (Fin.castSucc l) : ℝ) : ℂ) := by
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) : ℝ) : ℂ) = _
    rw [toGLM_V_castAdd_last_castAdd_apply m j hj]
  rw [hV]

/-- §521 — closed scalar entry on (last past-`y` row, past-`h*f` column). -/
theorem toGLM_stabilityMatrix_castAdd_last_natAdd_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
      ((m.β (Fin.castSucc l) : ℝ) : ℂ) +
        z * ((m.β (Fin.last s) : ℝ) : ℂ) *
          (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
          ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrix_castAdd_last_apply m z j hj]
  rw [toGLM_resolvent_apply, toGLM_Uℂ_natAdd]
  have hV : m.toGLM.Vℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
        ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) : ℝ) : ℂ) = _
    rw [toGLM_V_castAdd_last_natAdd_apply m j hj]
  rw [hV]

/-- §521 — closed scalar entry on (last past-`h*f` row, past-`y` column). -/
theorem toGLM_stabilityMatrix_natAdd_last_castAdd_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
      z * (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
        ((-m.α (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrix_natAdd_last_apply m z j hj]
  rw [toGLM_resolvent_apply, toGLM_Uℂ_castAdd]

/-- §521 — closed scalar entry on (last past-`h*f` row, past-`h*f` column). -/
theorem toGLM_stabilityMatrix_natAdd_last_natAdd_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
      z * (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
        ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrix_natAdd_last_apply m z j hj]
  rw [toGLM_resolvent_apply, toGLM_Uℂ_natAdd]

/-- §521 block reindexing: split the `2*s` GLM state into past-`y`
and past-`h*f` halves. -/
noncomputable def toGLM_stabilityBlockEquiv (s : ℕ) :
    Fin s ⊕ Fin s ≃ Fin (2 * s) :=
  finSumFinEquiv.trans (finCongr (Nat.two_mul s).symm)

@[simp] theorem toGLM_stabilityBlockEquiv_symm_castAdd (j : Fin s) :
    (toGLM_stabilityBlockEquiv s).symm
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) =
      Sum.inl j := by
  simp [toGLM_stabilityBlockEquiv]

@[simp] theorem toGLM_stabilityBlockEquiv_symm_natAdd (j : Fin s) :
    (toGLM_stabilityBlockEquiv s).symm
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) =
      Sum.inr j := by
  simp [toGLM_stabilityBlockEquiv]
  apply finSumFinEquiv.injective
  ext
  simp [Fin.addNat, Fin.natAdd, Nat.add_comm]

@[simp] theorem toGLM_stabilityBlockEquiv_symm_addNat (j : Fin s) :
    (toGLM_stabilityBlockEquiv s).symm
        (Fin.cast (Nat.two_mul s).symm (j.addNat s)) =
      Sum.inr j := by
  simp [toGLM_stabilityBlockEquiv]
  apply finSumFinEquiv.injective
  ext
  simp [Fin.addNat, Fin.natAdd, Nat.add_comm]

/-- §521 block form: past-`y` rows against past-`y` columns. -/
noncomputable def toGLM_stabilityMatrixPY (m : LMM s) (z : ℂ) :
    Matrix (Fin s) (Fin s) ℂ := fun j l =>
  if (j : ℕ) + 1 = s then
    ((-m.α (Fin.castSucc l) : ℝ) : ℂ) +
      z * ((m.β (Fin.last s) : ℝ) : ℂ) *
        (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
        ((-m.α (Fin.castSucc l) : ℝ) : ℂ)
  else if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0

/-- §521 block form: past-`y` rows against past-`h*f` columns. -/
noncomputable def toGLM_stabilityMatrixPYHF (m : LMM s) (z : ℂ) :
    Matrix (Fin s) (Fin s) ℂ := fun j l =>
  if (j : ℕ) + 1 = s then
    ((m.β (Fin.castSucc l) : ℝ) : ℂ) +
      z * ((m.β (Fin.last s) : ℝ) : ℂ) *
        (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
        ((m.β (Fin.castSucc l) : ℝ) : ℂ)
  else 0

/-- §521 block form: past-`h*f` rows against past-`y` columns. -/
noncomputable def toGLM_stabilityMatrixPHFY (m : LMM s) (z : ℂ) :
    Matrix (Fin s) (Fin s) ℂ := fun j l =>
  if (j : ℕ) + 1 = s then
    z * (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
      ((-m.α (Fin.castSucc l) : ℝ) : ℂ)
  else 0

/-- §521 block form: past-`h*f` rows against past-`h*f` columns. -/
noncomputable def toGLM_stabilityMatrixPHF (m : LMM s) (z : ℂ) :
    Matrix (Fin s) (Fin s) ℂ := fun j l =>
  if (j : ℕ) + 1 = s then
    z * (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
      ((m.β (Fin.castSucc l) : ℝ) : ℂ)
  else if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0

theorem toGLM_stabilityMatrix_castAdd_castAdd_apply (m : LMM s) (z : ℂ)
    (j l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
      toGLM_stabilityMatrixPY m z j l := by
  unfold toGLM_stabilityMatrixPY
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    exact toGLM_stabilityMatrix_castAdd_last_castAdd_apply m z j hj l
  · rw [if_neg hj]
    rw [toGLM_stabilityMatrix_castAdd_shift_apply m z j hj]
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) : ℝ) : ℂ) =
      if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0
    rw [toGLM_V_castAdd_shift_apply m j hj]
    by_cases hlj : (l : ℕ) = (j : ℕ) + 1 <;> simp [Fin.castAdd, hlj]

theorem toGLM_stabilityMatrix_castAdd_natAdd_apply (m : LMM s) (z : ℂ)
    (j l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
      toGLM_stabilityMatrixPYHF m z j l := by
  unfold toGLM_stabilityMatrixPYHF
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    exact toGLM_stabilityMatrix_castAdd_last_natAdd_apply m z j hj l
  · rw [if_neg hj]
    rw [toGLM_stabilityMatrix_castAdd_shift_apply m z j hj]
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) : ℝ) : ℂ) = 0
    rw [toGLM_V_castAdd_shift_apply m j hj]
    rw [if_neg]
    · norm_num
    · simp [Fin.natAdd]
      omega

theorem toGLM_stabilityMatrix_natAdd_castAdd_apply (m : LMM s) (z : ℂ)
    (j l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
      toGLM_stabilityMatrixPHFY m z j l := by
  unfold toGLM_stabilityMatrixPHFY
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    exact toGLM_stabilityMatrix_natAdd_last_castAdd_apply m z j hj l
  · rw [if_neg hj]
    rw [toGLM_stabilityMatrix_natAdd_shift_apply m z j hj]
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) : ℝ) : ℂ) = 0
    rw [toGLM_V_natAdd_shift_apply m j hj]
    rw [if_neg]
    · norm_num
    · simp [Fin.castAdd]
      omega

theorem toGLM_stabilityMatrix_natAdd_natAdd_apply (m : LMM s) (z : ℂ)
    (j l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
      toGLM_stabilityMatrixPHF m z j l := by
  unfold toGLM_stabilityMatrixPHF
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    exact toGLM_stabilityMatrix_natAdd_last_natAdd_apply m z j hj l
  · rw [if_neg hj]
    rw [toGLM_stabilityMatrix_natAdd_shift_apply m z j hj]
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) : ℝ) : ℂ) =
      if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0
    rw [toGLM_V_natAdd_shift_apply m j hj]
    by_cases hlj : (l : ℕ) = (j : ℕ) + 1
    · rw [if_pos (by simp [Fin.natAdd]; omega), if_pos hlj]
      norm_num
    · rw [if_neg (by simp [Fin.natAdd]; omega), if_neg hlj]
      norm_num

/-- §521 — Reindexing the LMM-as-GLM stability matrix by the past-`y` /
past-`h*f` split exposes the four closed-form `s × s` blocks. -/
theorem toGLM_stabilityMatrix_eq_fromBlocks (m : LMM s) (z : ℂ) :
    m.toGLM.stabilityMatrix z =
      Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
        (Matrix.fromBlocks
          (toGLM_stabilityMatrixPY m z) (toGLM_stabilityMatrixPYHF m z)
          (toGLM_stabilityMatrixPHFY m z) (toGLM_stabilityMatrixPHF m z)) := by
  let blocks : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ :=
    Matrix.fromBlocks
      (toGLM_stabilityMatrixPY m z) (toGLM_stabilityMatrixPYHF m z)
      (toGLM_stabilityMatrixPHFY m z) (toGLM_stabilityMatrixPHF m z)
  suffices h :
      ∀ kc lc : Fin (s + s),
        m.toGLM.stabilityMatrix z
            (Fin.cast (Nat.two_mul s).symm kc)
            (Fin.cast (Nat.two_mul s).symm lc) =
          (Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
            blocks)
            (Fin.cast (Nat.two_mul s).symm kc)
            (Fin.cast (Nat.two_mul s).symm lc) by
    ext k l
    simpa [blocks] using h (Fin.cast (Nat.two_mul s) k) (Fin.cast (Nat.two_mul s) l)
  intro kc lc
  refine kc.addCases (motive := fun kc' =>
      m.toGLM.stabilityMatrix z
          (Fin.cast (Nat.two_mul s).symm kc')
          (Fin.cast (Nat.two_mul s).symm lc) =
        (Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
          blocks)
          (Fin.cast (Nat.two_mul s).symm kc')
          (Fin.cast (Nat.two_mul s).symm lc)) ?_ ?_
  · intro j
    refine lc.addCases (motive := fun lc' =>
        m.toGLM.stabilityMatrix z
            (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
            (Fin.cast (Nat.two_mul s).symm lc') =
          (Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
            blocks)
            (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
            (Fin.cast (Nat.two_mul s).symm lc')) ?_ ?_
    · intro l
      simpa [blocks, Matrix.reindex, Matrix.fromBlocks]
        using toGLM_stabilityMatrix_castAdd_castAdd_apply m z j l
    · intro l
      simpa [blocks, Matrix.reindex, Matrix.fromBlocks]
        using toGLM_stabilityMatrix_castAdd_natAdd_apply m z j l
  · intro j
    refine lc.addCases (motive := fun lc' =>
        m.toGLM.stabilityMatrix z
            (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
            (Fin.cast (Nat.two_mul s).symm lc') =
          (Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
            blocks)
            (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
            (Fin.cast (Nat.two_mul s).symm lc')) ?_ ?_
    · intro l
      simpa [blocks, Matrix.reindex, Matrix.fromBlocks]
        using toGLM_stabilityMatrix_natAdd_castAdd_apply m z j l
    · intro l
      simpa [blocks, Matrix.reindex, Matrix.fromBlocks]
        using toGLM_stabilityMatrix_natAdd_natAdd_apply m z j l

/-- §521 — In a non-final past-`y` row of the PY block, the entry is the
pure shift indicator: `1` at the next column, `0` otherwise. -/
theorem toGLM_stabilityMatrixPY_apply_shift
    (m : LMM s) (z : ℂ) (j : Fin s) (hj : (j : ℕ) + 1 ≠ s) (l : Fin s) :
    toGLM_stabilityMatrixPY m z j l =
      (if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0) := by
  unfold toGLM_stabilityMatrixPY
  rw [if_neg hj]

/-- §521 — In the final past-`y` row of the PY block, the entry simplifies to
`-α l / (1 - z · β_s)` once the resolvent denominator is non-zero. -/
theorem toGLM_stabilityMatrixPY_apply_last_of_bdf
    (m : LMM s) (z : ℂ)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    toGLM_stabilityMatrixPY m z j l =
      ((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
        (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) := by
  unfold toGLM_stabilityMatrixPY
  rw [if_pos hj]
  field_simp
  ring

/-- §521 rank-one base matrix: the complex lift of the underlying `V` shift
block. -/
private noncomputable def toGLM_V_active_lift (m : LMM s) :
    Matrix (Fin (2 * s)) (Fin (2 * s)) ℂ :=
  m.toGLM.Vℂ

/-- §521 rank-one correction column: only the implicit output rows can
consume the one-stage resolvent. -/
private noncomputable def toGLM_rankOneColumn (m : LMM s) (z : ℂ) :
    Fin (2 * s) → ℂ := fun k => z * m.toGLM.Bℂ k 0

/-- §521 rank-one correction row: the one-stage `U` row over past data. -/
private noncomputable def toGLM_rankOneRow (m : LMM s) :
    Fin (2 * s) → ℂ := fun l => m.toGLM.Uℂ 0 l

/-- §521 rank-one correction for the one-stage LMM-as-GLM stability matrix. -/
private noncomputable def toGLM_rankOneCorrection (m : LMM s) (z : ℂ) :
    Matrix (Fin (2 * s)) (Fin (2 * s)) ℂ :=
  Matrix.vecMulVec (toGLM_rankOneColumn m z) (toGLM_rankOneRow m)

/-- §521 — The one-stage resolvent contribution to the LMM-as-GLM stability
matrix is a rank-one update of the complex `V` block. -/
theorem toGLM_stabilityMatrix_eq_V_active_plus_rank_one
    (m : LMM s) (z : ℂ) (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    m.toGLM.stabilityMatrix z =
      toGLM_V_active_lift m +
        (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) •
          toGLM_rankOneCorrection m z := by
  have _ := hz
  ext k l
  rw [toGLM_stabilityMatrix_apply, toGLM_resolvent_apply]
  simp [toGLM_V_active_lift, toGLM_rankOneCorrection, toGLM_rankOneColumn,
    toGLM_rankOneRow, Matrix.vecMulVec_apply]
  ring

/-- §521 — Under the BDF hypothesis, the past-`y` rows have no dependence on
past `h*f` columns. -/
theorem toGLM_stabilityMatrixPYHF_eq_zero_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    toGLM_stabilityMatrixPYHF m z = 0 := by
  ext j l
  change toGLM_stabilityMatrixPYHF m z j l = (0 : ℂ)
  unfold toGLM_stabilityMatrixPYHF
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    have hlne : (Fin.castSucc l) ≠ Fin.last s := by
      intro hl
      have : (l : ℕ) = s := by
        have := congrArg (Fin.val) hl
        simpa [Fin.castSucc, Fin.last] using this
      exact absurd this (by have := l.isLt; omega)
    have hβ : m.β (Fin.castSucc l) = 0 := hbdf (Fin.castSucc l) hlne
    rw [hβ]
    push_cast
    ring_nf
  · rw [if_neg hj]

/-- §521 — Under the BDF hypothesis (only the last `β` coefficient is
non-zero), the past-`h*f` block of the LMM-as-GLM stability matrix
collapses to the pure shift companion: no `z`-dependence, no resolvent
prefactor. -/
theorem toGLM_stabilityMatrixPHF_apply_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (j l : Fin s) :
    toGLM_stabilityMatrixPHF m z j l =
      (if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0) := by
  unfold toGLM_stabilityMatrixPHF
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    have hlne : (Fin.castSucc l) ≠ Fin.last s := by
      intro hl
      have : (l : ℕ) = s := by
        have := congrArg (Fin.val) hl
        simpa [Fin.castSucc, Fin.last] using this
      exact absurd this (by have := l.isLt; omega)
    have hβ : m.β (Fin.castSucc l) = 0 := hbdf (Fin.castSucc l) hlne
    rw [hβ]
    push_cast
    rw [if_neg]
    · ring
    · intro hlj
      have hl_lt : (l : ℕ) < s := l.isLt
      omega
  · rw [if_neg hj]

/-- §521 — Under the BDF hypothesis, the past-`h*f` block is upper
triangular in the `Fin s` order. Off-diagonal nonzero entries live
strictly above the diagonal at `(l : ℕ) = (j : ℕ) + 1`. -/
theorem toGLM_stabilityMatrixPHF_blockTriangular_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    (toGLM_stabilityMatrixPHF m z).BlockTriangular id := by
  intro j l hlt
  rw [toGLM_stabilityMatrixPHF_apply_of_bdf m z hbdf j l]
  rw [if_neg]
  intro h
  -- `hlt : id l < id j`, i.e. `(l : ℕ) < (j : ℕ)`; `h : (l : ℕ) = (j : ℕ) + 1`
  simp [id] at hlt
  omega

/-- §521 — Under the BDF hypothesis, the past-`h*f` block has
characteristic polynomial `X^s`. The diagonal of the upper-triangular
matrix is identically zero (since `(j : ℕ) ≠ (j : ℕ) + 1`), so each
linear factor in the diagonal product collapses to `X`. -/
theorem toGLM_stabilityMatrixPHF_charpoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    (toGLM_stabilityMatrixPHF m z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s := by
  rw [Matrix.charpoly_of_upperTriangular _
        (toGLM_stabilityMatrixPHF_blockTriangular_of_bdf m z hbdf)]
  have hdiag : ∀ j : Fin s,
      (Polynomial.X - Polynomial.C (toGLM_stabilityMatrixPHF m z j j)) =
      (Polynomial.X : Polynomial ℂ) := by
    intro j
    rw [toGLM_stabilityMatrixPHF_apply_of_bdf m z hbdf j j]
    rw [if_neg (by omega)]
    simp
  simp [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- §521 — For BDF-type LMMs, the full LMM-as-GLM stability matrix has the
same characteristic polynomial as the active past-`y` block, multiplied by
the nilpotent past-`h*f` shift factor. -/
theorem toGLM_stabilityMatrix_charpoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    (m.toGLM.stabilityMatrix z).charpoly =
      (toGLM_stabilityMatrixPY m z).charpoly *
        (Polynomial.X : Polynomial ℂ) ^ s := by
  rw [toGLM_stabilityMatrix_eq_fromBlocks m z]
  rw [Matrix.charpoly_reindex]
  rw [toGLM_stabilityMatrixPYHF_eq_zero_of_bdf m z hbdf]
  rw [Matrix.charpoly_fromBlocks_zero₁₂]
  rw [toGLM_stabilityMatrixPHF_charpoly_of_bdf m z hbdf]

/-- §521 helper: the bottom-row companion matrix with shift rows above it. -/
private noncomputable def toGLM_stabilityMatrixPYCompanion (a : Fin s → ℂ) :
    Matrix (Fin s) (Fin s) ℂ := fun j l =>
  if (j : ℕ) + 1 = s then a l
  else if (l : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- §521 helper: characteristic polynomial of the bottom-row companion shape
used by the BDF past-`y` block. -/
private theorem toGLM_stabilityMatrixPYCompanion_charpoly (a : Fin s → ℂ) :
    (toGLM_stabilityMatrixPYCompanion a).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s -
        ∑ l : Fin s, Polynomial.C (a l) * Polynomial.X ^ (l : ℕ) := by
  induction s with
  | zero =>
      simp [Matrix.charpoly]
  | succ n ih =>
      cases n with
      | zero =>
          simp [Matrix.charpoly, toGLM_stabilityMatrixPYCompanion]
      | succ n =>
          rw [Matrix.charpoly, Matrix.det_succ_column_zero]
          have htail :
              (toGLM_stabilityMatrixPYCompanion a).charmatrix.submatrix Fin.succ Fin.succ =
                (toGLM_stabilityMatrixPYCompanion
                  (fun i : Fin (n + 1) => a i.succ)).charmatrix := by
            ext i j k
            by_cases hij : i = j
            · subst j
              simp [Matrix.charmatrix, toGLM_stabilityMatrixPYCompanion]
            · have hsij : i.succ ≠ j.succ := by
                intro h
                exact hij (Fin.succ_injective _ h)
              simp [Matrix.charmatrix, toGLM_stabilityMatrixPYCompanion, hij, hsij]
          have htail_det :
              ((toGLM_stabilityMatrixPYCompanion a).charmatrix.submatrix
                  Fin.succ Fin.succ).det =
                (toGLM_stabilityMatrixPYCompanion
                  (fun i : Fin (n + 1) => a i.succ)).charpoly := by
            rw [htail, Matrix.charpoly]
          have hlast :
              ((toGLM_stabilityMatrixPYCompanion a).charmatrix.submatrix
                  Fin.castSucc Fin.succ).det =
                (-1 : Polynomial ℂ) ^ (n + 1) := by
            let B :=
              (toGLM_stabilityMatrixPYCompanion a).charmatrix.submatrix
                Fin.castSucc Fin.succ
            have htri : B.BlockTriangular OrderDual.toDual := by
              intro i j hij
              have hij' : (i : ℕ) < (j : ℕ) := by simpa using hij
              have hi_not : (i : ℕ) ≠ n + 1 := by omega
              have hji_ne : (j : ℕ) ≠ (i : ℕ) := by omega
              have hdiagOff :
                  (Fin.castSucc i : Fin (n + 1 + 1)) ≠
                    (Fin.succ j : Fin (n + 1 + 1)) := by
                intro h
                have hv := congrArg Fin.val h
                simp at hv
                omega
              simp [B, Matrix.charmatrix, toGLM_stabilityMatrixPYCompanion,
                hi_not, hji_ne, hdiagOff]
            rw [Matrix.det_of_lowerTriangular B htri]
            have hdiag : ∀ i : Fin (n + 1), B i i = (-1 : Polynomial ℂ) := by
              intro i
              have hne :
                  (Fin.castSucc i : Fin (n + 1 + 1)) ≠
                    (Fin.succ i : Fin (n + 1 + 1)) := by
                intro h
                have hv := congrArg Fin.val h
                simp at hv
              have hi_not : (i : ℕ) ≠ n + 1 := by omega
              simp [B, Matrix.charmatrix, toGLM_stabilityMatrixPYCompanion,
                hne, hi_not]
            simp [hdiag, Finset.prod_const, Fintype.card_fin]
          have hnotLast : ∀ x : Fin n, (x : ℕ) ≠ n := by
            intro x
            omega
          rw [Fin.sum_univ_succ]
          rw [Fin.sum_univ_castSucc]
          simp [toGLM_stabilityMatrixPYCompanion, htail_det, hlast, hnotLast]
          rw [ih (fun i : Fin (n + 1) => a i.succ)]
          conv_lhs =>
            rw [Fin.sum_univ_succ]
          conv_rhs =>
            rw [Fin.sum_univ_succ]
            rw [Fin.sum_univ_succ]
          simp
          have hsign :
              (-1 : Polynomial ℂ) ^ (n + 1) * Polynomial.C (a 0) *
                  (-1) ^ (n + 1) =
                Polynomial.C (a 0) := by
            calc
              (-1 : Polynomial ℂ) ^ (n + 1) * Polynomial.C (a 0) *
                    (-1) ^ (n + 1)
                  = Polynomial.C (a 0) *
                      (((-1 : Polynomial ℂ) ^ (n + 1)) *
                        ((-1) ^ (n + 1))) := by
                    ring
              _ = Polynomial.C (a 0) * ((-1 : Polynomial ℂ) ^ (2 * (n + 1))) := by
                    rw [← pow_add]
                    have hpow : (n + 1) + (n + 1) = 2 * (n + 1) := by omega
                    rw [hpow]
              _ = Polynomial.C (a 0) := by
                    rw [pow_mul]
                    simp
          rw [hsign]
          simp_rw [mul_sub, mul_add, Finset.mul_sum]
          have hpow_main :
              Polynomial.X * Polynomial.X ^ (n + 1) =
                (Polynomial.X : Polynomial ℂ) ^ (n + 1 + 1) := by
            rw [← pow_succ']
          have hsum_pow :
              (∑ i : Fin n,
                  Polynomial.X *
                    (Polynomial.C (a i.succ.succ) *
                      Polynomial.X ^ ((i : ℕ) + 1))) =
                ∑ i : Fin n,
                  Polynomial.C (a i.succ.succ) *
                    Polynomial.X ^ ((i : ℕ) + 1 + 1) := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              Polynomial.X *
                    (Polynomial.C (a i.succ.succ) *
                      Polynomial.X ^ ((i : ℕ) + 1))
                  = Polynomial.C (a i.succ.succ) *
                      (Polynomial.X * Polynomial.X ^ ((i : ℕ) + 1)) := by
                    ring
              _ = Polynomial.C (a i.succ.succ) *
                    Polynomial.X ^ ((i : ℕ) + 1 + 1) := by
                    rw [← pow_succ']
          rw [hpow_main, hsum_pow]
          ring_nf

/-- §521 — Under the BDF denominator hypothesis, the active past-`y` block is
the bottom-row companion matrix with coefficients `-α_l / (1 - z β_s)`. -/
private theorem toGLM_stabilityMatrixPY_eq_companion_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    toGLM_stabilityMatrixPY m z =
      toGLM_stabilityMatrixPYCompanion
        (fun l : Fin s =>
          (((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
            (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)))) := by
  have _ := hbdf
  ext j l
  by_cases hj : (j : ℕ) + 1 = s
  · rw [toGLM_stabilityMatrixPY_apply_last_of_bdf m z hz j hj l]
    simp [toGLM_stabilityMatrixPYCompanion, hj]
  · rw [toGLM_stabilityMatrixPY_apply_shift m z j hj l]
    simp [toGLM_stabilityMatrixPYCompanion, hj]

/-- §521 — For BDF-type LMMs, the active past-`y` block has the expected
monic companion characteristic polynomial. -/
theorem toGLM_stabilityMatrixPY_charpoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    (toGLM_stabilityMatrixPY m z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s -
        ∑ l : Fin s,
          Polynomial.C
            (((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
              (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
            Polynomial.X ^ (l : ℕ) := by
  rw [toGLM_stabilityMatrixPY_eq_companion_of_bdf m z hbdf hz]
  exact toGLM_stabilityMatrixPYCompanion_charpoly
    (fun l : Fin s =>
      (((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
        (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))))

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

end LMM

/-- §521 — Backward Euler is A-stable in the GLM sense after the §503
embedding. Direct concrete check at `s = 1`: the `2 × 2` stability
matrix is `!![1/(1-z), 0; z/(1-z), 0]`, whose characteristic polynomial
factors as `X * (X - 1/(1-z))`. The two eigenvalues are `0` and
`1/(1-z)`, both of norm at most `1` for `z.re ≤ 0`. The LMM-side
analogue of cycle 627's `rkImplicitEuler_toGLM_isAStable`. -/
theorem backwardEuler_toGLM_isAStable :
    backwardEuler.toGLM.IsAStable := by
  intro z hz μ hμ
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re] at hre
    linarith
  have hM : backwardEuler.toGLM.stabilityMatrix z =
      !![1 / (1 - z), 0; z / (1 - z), 0] := by
    ext k l
    rw [LMM.toGLM_stabilityMatrix_apply]
    have hAℂ : backwardEuler.toGLM.Aℂ = !![1] := by
      ext i j
      fin_cases i; fin_cases j
      show (backwardEuler.β (Fin.last 1) : ℂ) = (!![(1 : ℂ)]) 0 0
      simp [backwardEuler]
    rw [hAℂ]
    have hsub : (1 : Matrix (Fin 1) (Fin 1) ℂ) - z • !![(1 : ℂ)] = !![1 - z] := by
      ext i j
      fin_cases i; fin_cases j; simp
    rw [hsub]
    have hinv : (!![1 - z] : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ 0 0 = 1 / (1 - z) := by
      rw [Matrix.inv_def]
      simp [Matrix.adjugate_fin_one]
    rw [hinv]
    fin_cases k <;> fin_cases l <;>
      simp [LMM.toGLM, backwardEuler, Fin.addCases, Fin.cast,
        GeneralLinearMethod.Vℂ, GeneralLinearMethod.Bℂ, GeneralLinearMethod.Uℂ,
        Fin.last]
    all_goals first | rfl | (field_simp; ring)
  rw [hM] at hμ
  have hchar :
      (!![(1 : ℂ) / (1 - z), 0; z / (1 - z), 0]).charpoly =
        Polynomial.X * (Polynomial.X - Polynomial.C (1 / (1 - z))) := by
    rw [Matrix.charpoly]
    rw [Matrix.charmatrix]
    rw [Matrix.det_fin_two]
    simp
    ring
  rw [hchar] at hμ
  rw [Polynomial.IsRoot] at hμ
  simp at hμ
  rcases hμ with hμ0 | hμ1
  · rw [hμ0]; simp
  · have hμeq : μ = (1 - z)⁻¹ := sub_eq_zero.mp hμ1
    rw [hμeq]
    rw [norm_inv]
    have h1z_ge : 1 ≤ ‖(1 : ℂ) - z‖ := by
      have h1 := Complex.abs_re_le_norm ((1 : ℂ) - z)
      simp [Complex.sub_re] at h1
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - z.re)] at h1
      linarith
    rw [inv_le_one_iff₀]
    right
    exact h1z_ge

/-- §521 — The trapezoidal rule is A-stable in the GLM sense after the
§503 embedding. At `s = 1`, the `2 × 2` stability matrix is rank one with
trace `(2 + z)/(2 - z)`, so its characteristic polynomial factors as
`X * (X - C ((2 + z)/(2 - z)))`. -/
theorem trapezoidalRule_toGLM_isAStable :
    trapezoidalRule.toGLM.IsAStable := by
  intro z hz μ hμ
  have hne : (2 : ℂ) - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re] at hre
    linarith
  have hM : trapezoidalRule.toGLM.stabilityMatrix z =
      !![2 / (2 - z), 1 / (2 - z);
        2 * z / (2 - z), z / (2 - z)] := by
    ext k l
    rw [LMM.toGLM_stabilityMatrix_apply]
    have hAℂ : trapezoidalRule.toGLM.Aℂ = !![(1 / 2 : ℂ)] := by
      ext i j
      fin_cases i; fin_cases j
      show (trapezoidalRule.β (Fin.last 1) : ℂ) = (!![(1 / 2 : ℂ)]) 0 0
      simp [trapezoidalRule]
    rw [hAℂ]
    have hsub : (1 : Matrix (Fin 1) (Fin 1) ℂ) - z • !![(1 / 2 : ℂ)] =
        !![1 - z / 2] := by
      ext i j
      fin_cases i; fin_cases j
      simp
      ring
    rw [hsub]
    have hinv : (!![1 - z / 2] : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ 0 0 =
        1 / (1 - z / 2) := by
      rw [Matrix.inv_def]
      simp [Matrix.adjugate_fin_one]
    rw [hinv]
    fin_cases k <;> fin_cases l <;>
      simp [LMM.toGLM, trapezoidalRule, Fin.addCases, Fin.cast,
        GeneralLinearMethod.Vℂ, GeneralLinearMethod.Bℂ, GeneralLinearMethod.Uℂ,
        Fin.last]
    all_goals
      field_simp [hne]
      try ring
  rw [hM] at hμ
  have hchar :
      (!![2 / (2 - z), 1 / (2 - z);
        2 * z / (2 - z), z / (2 - z)] : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
        Polynomial.X * (Polynomial.X - Polynomial.C ((2 + z) / (2 - z))) := by
    have htrace :
        (!![2 / (2 - z), 1 / (2 - z);
          2 * z / (2 - z), z / (2 - z)] : Matrix (Fin 2) (Fin 2) ℂ).trace =
          (2 + z) / (2 - z) := by
      simp [Matrix.trace]
      field_simp [hne]
    have hdet :
        (!![2 / (2 - z), 1 / (2 - z);
          2 * z / (2 - z), z / (2 - z)] : Matrix (Fin 2) (Fin 2) ℂ).det = 0 := by
      rw [Matrix.det_fin_two]
      simp
      field_simp [hne]
      ring
    rw [Matrix.charpoly_fin_two, htrace, hdet]
    simp
    rw [mul_sub]
    rw [mul_comm Polynomial.X (Polynomial.C ((2 + z) / (2 - z)))]
    ring
  rw [hchar] at hμ
  rw [Polynomial.IsRoot] at hμ
  simp at hμ
  rcases hμ with hμ0 | hμ1
  · rw [hμ0]; simp
  · have hμeq : μ = (2 + z) / (2 - z) := sub_eq_zero.mp hμ1
    rw [hμeq]
    have h_denom_pos : (0 : ℝ) < ‖(2 : ℂ) - z‖ := norm_pos_iff.mpr hne
    have h_nsq_le : ‖(2 : ℂ) + z‖ ^ 2 ≤ ‖(2 : ℂ) - z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
        Complex.add_im, Complex.sub_im]
      norm_num
      nlinarith
    have h_num_le : ‖(2 : ℂ) + z‖ ≤ ‖(2 : ℂ) - z‖ := by
      nlinarith [norm_nonneg ((2 : ℂ) + z), norm_nonneg ((2 : ℂ) - z),
        sq_nonneg (‖(2 : ℂ) - z‖ - ‖(2 : ℂ) + z‖)]
    rw [norm_div]
    exact (div_le_one h_denom_pos).mpr h_num_le

/-- §521 — BDF2 is A-stable in the GLM sense after the §503 embedding.
At `s = 2`, the GLM stability matrix is `4 × 4` and block lower-triangular:
the rows / columns indexed by the `h·f` slot give two zero eigenvalues,
and the remaining `2 × 2` active block has charpoly
`X² − (4 / (3 − 2z)) X + 1 / (3 − 2z)`, whose roots are precisely the
roots of `bdf2.stabilityPoly · z` rescaled by `1/(3 − 2z)`. -/
theorem bdf2_toGLM_isAStable :
    bdf2.toGLM.IsAStable := by
  intro z hz μ hμ
  have hne : (3 : ℂ) - 2 * z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at hre
    linarith
  have hne' : (3 : ℂ) - z * 2 ≠ 0 := by
    rwa [show (3 : ℂ) - z * 2 = 3 - 2 * z from by ring]
  have hAℂ : bdf2.toGLM.Aℂ = !![(2 / 3 : ℂ)] := by
    ext i j; fin_cases i; fin_cases j
    show (bdf2.β (Fin.last 2) : ℂ) = (!![(2 / 3 : ℂ)]) 0 0
    simp [bdf2]
  have hsub : (1 : Matrix (Fin 1) (Fin 1) ℂ) - z • !![(2 / 3 : ℂ)] =
      !![1 - z * (2 / 3)] := by
    ext i j; fin_cases i; fin_cases j; simp
  have hinv : (!![1 - z * (2 / 3)] : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ 0 0 =
      1 / (1 - z * (2 / 3)) := by
    rw [Matrix.inv_def]
    simp [Matrix.adjugate_fin_one]
  have hM : bdf2.toGLM.stabilityMatrix z =
      !![0, 1, 0, 0;
         -(1 / (3 - 2 * z)), 4 / (3 - 2 * z), 0, 0;
         0, 0, 0, 1;
         -(z / (3 - 2 * z)), 4 * z / (3 - 2 * z), 0, 0] := by
    ext k l
    rw [LMM.toGLM_stabilityMatrix_apply]
    rw [hAℂ, hsub, hinv]
    fin_cases k <;> fin_cases l <;>
      simp [LMM.toGLM, bdf2, Fin.addCases, Fin.cast,
        GeneralLinearMethod.Vℂ, GeneralLinearMethod.Bℂ, GeneralLinearMethod.Uℂ,
        Fin.last]
    all_goals first | rfl | (field_simp [hne, hne']; try ring)
  -- Convert IsRoot to determinant condition via eval_charpoly.
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, hM] at hμ
  -- Compute the determinant by expanding twice along sparse columns.
  -- The matrix `(scalar μ - M)` is block lower-triangular with zero
  -- top-right `2 × 2` block; the bottom-right block is upper-triangular
  -- with diagonal `(μ, μ)`, contributing `μ²`. The top-left active block
  -- is `!![μ, -1; 1/(3-2z), μ-4/(3-2z)]`, with det `μ² - 4μ/(3-2z) + 1/(3-2z)`.
  have hdet :
      (Matrix.scalar (Fin 4) μ -
        !![(0 : ℂ), 1, 0, 0;
           -(1 / (3 - 2 * z)), 4 / (3 - 2 * z), 0, 0;
           0, 0, 0, 1;
           -(z / (3 - 2 * z)), 4 * z / (3 - 2 * z), 0, 0]).det =
        μ ^ 2 * (μ ^ 2 - (4 / (3 - 2 * z)) * μ + 1 / (3 - 2 * z)) := by
    -- Rewrite scalar μ as the explicit diagonal 4×4 matrix and form the
    -- explicit difference matrix.
    have hscalar : Matrix.scalar (Fin 4) μ =
        !![μ, 0, 0, 0; 0, μ, 0, 0; 0, 0, μ, 0; 0, 0, 0, μ] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, Matrix.diagonal]
    rw [hscalar]
    have hdiff :
        (!![(μ : ℂ), 0, 0, 0; 0, μ, 0, 0; 0, 0, μ, 0; 0, 0, 0, μ] -
          !![(0 : ℂ), 1, 0, 0;
             -(1 / (3 - 2 * z)), 4 / (3 - 2 * z), 0, 0;
             0, 0, 0, 1;
             -(z / (3 - 2 * z)), 4 * z / (3 - 2 * z), 0, 0]) =
        !![(μ : ℂ), -1, 0, 0;
           1 / (3 - 2 * z), μ - 4 / (3 - 2 * z), 0, 0;
           0, 0, μ, -1;
           z / (3 - 2 * z), -(4 * z / (3 - 2 * z)), 0, μ] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hdiff]
    -- The 4×4 matrix is block lower-triangular: rows {0,1} cols {2,3} block is
    -- zero. Express it as a `Matrix.fromBlocks` permuted via `finSumFinEquiv`,
    -- then use `det_fromBlocks_zero₁₂`.
    set Ablk : Matrix (Fin 2) (Fin 2) ℂ :=
      !![μ, -1; 1 / (3 - 2 * z), μ - 4 / (3 - 2 * z)] with hAblk
    set Cblk : Matrix (Fin 2) (Fin 2) ℂ :=
      !![0, 0; z / (3 - 2 * z), -(4 * z / (3 - 2 * z))] with hCblk
    set Dblk : Matrix (Fin 2) (Fin 2) ℂ := !![μ, -1; 0, μ] with hDblk
    have hblock :
        !![(μ : ℂ), -1, 0, 0;
           1 / (3 - 2 * z), μ - 4 / (3 - 2 * z), 0, 0;
           0, 0, μ, -1;
           z / (3 - 2 * z), -(4 * z / (3 - 2 * z)), 0, μ] =
        (Matrix.fromBlocks Ablk 0 Cblk Dblk).submatrix
            finSumFinEquiv.symm finSumFinEquiv.symm := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.submatrix_apply, Matrix.fromBlocks,
          finSumFinEquiv, Fin.addCases, Ablk, Cblk, Dblk]
    rw [hblock, Matrix.det_submatrix_equiv_self,
        Matrix.det_fromBlocks_zero₁₂]
    simp [Ablk, Dblk, Matrix.det_fin_two]
    ring
  rw [hdet] at hμ
  -- μ = 0 or quadratic factor vanishes.
  have hquad_or_zero : μ = 0 ∨
      μ ^ 2 - (4 / (3 - 2 * z)) * μ + 1 / (3 - 2 * z) = 0 := by
    rcases mul_eq_zero.mp hμ with h2 | h2
    · left
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    · right; exact h2
  rcases hquad_or_zero with hμ0 | hquad
  · rw [hμ0]; simp
  · -- The quadratic root condition becomes `bdf2.stabilityPoly μ z = 0`.
    have hpoly : bdf2.stabilityPoly μ z = 0 := by
      have h_zero : (3 - 2 * z) * μ ^ 2 - 4 * μ + 1 = 0 := by
        have h1 : (3 - 2 * z) * (μ ^ 2 - (4 / (3 - 2 * z)) * μ + 1 / (3 - 2 * z)) = 0 := by
          rw [hquad, mul_zero]
        have h_eq :
            (3 - 2 * z) * (μ ^ 2 - (4 / (3 - 2 * z)) * μ + 1 / (3 - 2 * z))
              = (3 - 2 * z) * μ ^ 2 - 4 * μ + 1 := by
          field_simp
        linear_combination h1 - h_eq
      -- bdf2.stabilityPoly μ z = (1 - 2z/3)μ² - (4/3)μ + 1/3 = (1/3)((3-2z)μ² - 4μ + 1)
      simp only [LMM.stabilityPoly, LMM.rhoC, LMM.sigmaC, bdf2]
      simp [Fin.sum_univ_three]
      linear_combination h_zero / 3
    -- Apply bdf2_aStable.
    exact bdf2_aStable z hz μ hpoly
