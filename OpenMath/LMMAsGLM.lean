import OpenMath.MultistepMethods
import OpenMath.GeneralLinearMethod

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
