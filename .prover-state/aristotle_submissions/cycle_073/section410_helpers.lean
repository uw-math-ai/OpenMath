import Mathlib

/-! # Cycle 073 — §410 generating-function infrastructure helpers

Self-contained Aristotle submission for §410 sub-lemmas in support
of `thm:410A` (Butcher §410, p. 350).

The §410 generating polynomials and Taylor coefficient `C_j` of an
LMM are reproduced locally so this file is standalone (project
versions live in `OpenMath/Chapter4/Section410.lean`).

Sub-lemmas (each `sorry`):

1. `αPoly_natDegree_le`  : (αPoly M).natDegree ≤ k.
2. `βPoly_natDegree_le`  : (βPoly M).natDegree ≤ k.
3. `expNegPS_coeff`      : PowerSeries.coeff n expNegPS = (-1)^n / n!.
4. `coeff_aeval_C_X_pow` : closed form for the coefficient of
                            `aeval expNegPS (C c * X^m)` at degree j.
5. `thm_410A_zero`       : j=0 case of thm:410A (the constant
                            term identity reduces to `1 - Σ M.α i.succ`).
-/

open Polynomial

namespace AristotleCycle073

structure LinearMultistepMethod (k : ℕ) where
  α : Fin (k + 1) → ℝ
  β : Fin (k + 1) → ℝ
  α_zero : α 0 = -1

variable {k : ℕ}

/-- Butcher §410 α-polynomial (`α 0 = -1` LMM convention):
`α(z) = 1 - Σ_{i=1}^k M.α_i · z^i`. -/
noncomputable def αPoly (M : LinearMultistepMethod k) : Polynomial ℝ :=
  1 - ∑ i : Fin k, Polynomial.C (M.α i.succ) * Polynomial.X ^ (i.val + 1)

/-- Butcher §410 β-polynomial: `β(z) = Σ_{i=0}^k M.β_i · z^i`. -/
noncomputable def βPoly (M : LinearMultistepMethod k) : Polynomial ℝ :=
  ∑ i : Fin (k + 1), Polynomial.C (M.β i) * Polynomial.X ^ i.val

/-- Butcher (410b) Taylor coefficient C_j (closed form per the
proof of 410A). -/
noncomputable def C (M : LinearMultistepMethod k) : ℕ → ℝ
  | 0 => 1 - ∑ i : Fin k, M.α i.succ
  | j + 1 =>
      -∑ i : Fin k,
          M.α i.succ *
            (-((i.val + 1 : ℕ) : ℝ)) ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)
      - ∑ i : Fin (k + 1),
          M.β i * (-((i.val : ℕ) : ℝ)) ^ j / (Nat.factorial j : ℝ)

/-- Formal power series `exp(-z) = Σ_n (-1)^n z^n / n!`. -/
noncomputable def expNegPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => (-1 : ℝ) ^ n / (Nat.factorial n : ℝ)

/-! ## Sub-lemmas (Fill in each `sorry`) -/

/-- The §410 α-polynomial has degree at most `k`. -/
theorem αPoly_natDegree_le (M : LinearMultistepMethod k) :
    (αPoly M).natDegree ≤ k := by
  sorry

/-- The §410 β-polynomial has degree at most `k`. -/
theorem βPoly_natDegree_le (M : LinearMultistepMethod k) :
    (βPoly M).natDegree ≤ k := by
  sorry

/-- The j-th coefficient of `expNegPS` is `(-1)^j / j!`. -/
theorem expNegPS_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ℝ) n) expNegPS
      = (-1 : ℝ) ^ n / (Nat.factorial n : ℝ) := by
  sorry

/-- For a constant `c : ℝ` and exponent `m : ℕ`, the j-th coefficient
of `aeval expNegPS (Polynomial.C c * X^m)` is `c * (-m)^j / j!`. -/
theorem coeff_aeval_C_X_pow (c : ℝ) (m j : ℕ) :
    (PowerSeries.coeff (R := ℝ) j)
        ((Polynomial.aeval expNegPS) (Polynomial.C c * Polynomial.X ^ m))
      = c * (-(m : ℝ)) ^ j / (Nat.factorial j : ℝ) := by
  sorry

/-- **Theorem 410A at j=0** — the constant term of
`α(exp(-z)) - z β(exp(-z))` equals `1 - Σ_{i=1}^k M.α_i = C M 0`.

The `z β(exp(-z))` term contributes 0 at z⁰ (the leading `z`
factor kills it), so this reduces to `α(1) = 1 - Σ M.α i.succ`.
-/
theorem thm_410A_zero (M : LinearMultistepMethod k) :
    (PowerSeries.coeff (R := ℝ) 0)
        ((Polynomial.aeval expNegPS) (αPoly M)
          - PowerSeries.X * (Polynomial.aeval expNegPS) (βPoly M))
      = C M 0 := by
  sorry

end AristotleCycle073
