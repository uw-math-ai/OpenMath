import Mathlib

/-! # Cycle 075 Aristotle batch — `C_one_eq_zero_iff_isConsistent_aux`

Self-contained submission for the §410↔§404 bridge lemma:
the first Taylor coefficient `C M 1` vanishes iff the LMM
satisfies the consistency equation (404b).

Mathematical content:
* `C M 1 = -Σᵢ M.α(i.succ) · (-(i+1))^1 / 1!  -  Σᵢ M.β i · (-i)^0 / 0!`
        = `Σᵢ (i+1) · M.α(i.succ)  -  Σᵢ M.β i`
* `(404b)`: `Σᵢ (i+1) · M.α(i.succ) = Σᵢ M.β i`
So `C M 1 = 0 ↔ (404b)`.

The algebra is one `simp` collapse of factorials/pow-zero/pow-one
plus a `linarith` on the resulting linear equation. The cast from
`((i : ℕ) + 1 : ℝ)` (cast then add) to `((i.val + 1 : ℕ) : ℝ)`
(add then cast) requires `push_cast`/`Finset.sum_congr`.
-/

namespace AristotleCycle075

structure LinearMultistepMethod (k : ℕ) where
  α : Fin (k + 1) → ℝ
  β : Fin (k + 1) → ℝ
  α_zero : α 0 = -1

noncomputable def C {k : ℕ} (M : LinearMultistepMethod k) : ℕ → ℝ
  | 0 => 1 - ∑ i : Fin k, M.α i.succ
  | j + 1 =>
      -∑ i : Fin k,
          M.α i.succ *
            (-((i.val + 1 : ℕ) : ℝ)) ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)
      - ∑ i : Fin (k + 1),
          M.β i * (-((i.val : ℕ) : ℝ)) ^ j / (Nat.factorial j : ℝ)

def LinearMultistepMethod.SatisfiesEq404b {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  (∑ i : Fin k, ((i : ℕ) + 1 : ℝ) * M.α i.succ) = ∑ i, M.β i

theorem C_one_eq_zero_iff_isConsistent_aux {k : ℕ}
    (M : LinearMultistepMethod k) :
    C M 1 = 0 ↔ M.SatisfiesEq404b := by
  sorry

/-- Auxiliary: explicit Euler's `C M 2 ≠ 0`. Encoded inline as
`α := if i = 0 then -1 else 1`, `β := if i = 0 then 0 else 1`,
which is a 1-step LMM. -/
def explicitEulerAux : LinearMultistepMethod 1 where
  α := fun i => if i = 0 then -1 else 1
  β := fun i => if i = 0 then 0 else 1
  α_zero := by simp

theorem explicitEulerAux_C_two_ne_zero :
    C explicitEulerAux 2 ≠ 0 := by
  sorry

end AristotleCycle075
