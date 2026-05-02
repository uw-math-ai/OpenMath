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

end LMM
