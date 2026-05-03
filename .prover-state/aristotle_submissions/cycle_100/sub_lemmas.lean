import Mathlib

/-! Cycle 100 — Aristotle batch for `lem:515A` (Butcher §515) sub-bounds.

Self-contained file with five sorry-first sub-lemmas decomposing the
local truncation error bound (515a) of Butcher's §515. The textbook
proof (p. 412–413) writes the residual as `T1 + T2 + T3 + T4`:

  T1 = Ŷ_i − y(x_{n-1}) − h ∫₀^{c_i} f(y(x_{n-1}+hξ)) dξ              [= 0 by FTC]
  T2 = y(x_{n-1}) + c_i h y'(x_{n-1})
       − Σ_j U_{ij} y_j^{[n-1]} − Σ_j a_{ij} h y'(x_{n-1})            [= 0 by setup]
  T3 = h ∫₀^{c_i} (f(y(x_{n-1}+hξ)) − y'(x_{n-1})) dξ                  [≤ ½ h² L² M c_i²]
  T4 = −h Σ_j a_{ij} (f(y(x_{n-1}+h c_j)) − y'(x_{n-1}))               [≤ h² L² M Σ|a_{ij} c_j|]

The first preliminary `‖y(x + hξ) − y(x)‖ ≤ |ξ| h L M`
(`aux_y_diff_norm_bound`) is also included.

Hypotheses across all five lemmas are kept identical and minimal:

* `f : ℝ → ℝ`, Lipschitz with constant `L ≥ 0`
* `y : ℝ → ℝ`, `C¹`, satisfying `y'(t) = f(y(t))`
* `|f(y(t))| ≤ L · M_bound`, i.e. `|y'(t)| ≤ L · M_bound`
* `0 ≤ h`, real `x` (= x_{n-1})
* `c : Fin s → ℝ` (the abscissae, treated as a parameter)
* `A : Matrix (Fin s) (Fin s) ℝ`, `U : Matrix (Fin s) (Fin r) ℝ`
* `u v : Fin r → ℝ` (consistency vectors), with `c = A·𝟙 + U·v`

The output bounds match the four `Tk` decomposition with `Tk` replaced
by its closed-form expression (since `Y_hat_i = y(x + h c_i)` in this
formulation, the `T1` and `T2` claims are equalities to zero, not
inequalities). -/

open Matrix
open scoped BigOperators

namespace AristotleBatch100

/-- **Sub-lemma 1** (preliminary): pointwise bound on `|y(x + hξ) − y x|`
for any sign of ξ.

Proof sketch: FTC + `intervalIntegral.norm_integral_le_of_norm_le_const`. -/
lemma aux_y_diff_norm_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (_hL : 0 ≤ L) (_hM : 0 ≤ M_bound)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)
    (x h : ℝ) (hh : 0 ≤ h) (ξ : ℝ) :
    |y (x + h * ξ) - y x| ≤ h * |ξ| * (L * M_bound) := by
  sorry

/-- **Sub-lemma 2 (T1 ≡ 0)**: by FTC,

  `y(x + h c_i) − y(x) − h ∫₀^{c_i} f(y(x + hξ)) dξ = 0`.

Proof sketch: the integrand `f(y(x + hξ))` equals `(d/dξ) y(x + hξ) / h`
(by chain rule). The integral telescopes to `(y(x + h c_i) − y(x)) / h`,
multiplied by `h` gives `y(x + h c_i) − y(x)`, which cancels the first
two terms. -/
lemma aux_T1_bound
    {f : ℝ → ℝ}
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (x h c_i : ℝ) :
    y (x + h * c_i) - y x
      - h * ∫ ξ in (0 : ℝ)..c_i, f (y (x + h * ξ)) = 0 := by
  sorry

/-- **Sub-lemma 3 (T2 ≡ 0)**: by `c = A·𝟙 + U·v` and the input
identities `y_j^{[n-1]} = u_j y(x) + v_j h y'(x)`,

  `y(x) + c_i h y'(x) − Σ_j U_{ij} (u_j y(x) + v_j h y'(x))
     − Σ_j A_{ij} h y'(x) = 0`.

Proof sketch: pure algebraic rearrangement using `c = A·𝟙 + U·v` and
the preconsistency identity `U·u = 𝟙`. -/
lemma aux_T2_bound {s r : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ) (U : Matrix (Fin s) (Fin r) ℝ)
    (u v : Fin r → ℝ)
    (hUu : U *ᵥ u = (fun _ => 1))
    (c : Fin s → ℝ)
    (hc : c = A *ᵥ (fun _ => 1) + U *ᵥ v)
    {y : ℝ → ℝ} (x h : ℝ) (i : Fin s) :
    y x + c i * h * deriv y x
      - (∑ j, U i j * (u j * y x + v j * h * deriv y x))
      - (∑ j, A i j * h * deriv y x) = 0 := by
  sorry

/-- **Sub-lemma 4 (T3 bound)**: by `aux_y_diff_norm_bound` applied
inside the integrand and Lipschitz of `f`,

  `|h ∫₀^{c_i} (f(y(x + hξ)) − f(y x)) dξ| ≤ ½ h² L² M c_i²`.

Proof sketch: bound `|f(y(x + hξ)) − f(y x)| ≤ L |y(x + hξ) − y x|
≤ L · h · |ξ| · (L M)` via Lipschitz then `aux_y_diff_norm_bound`,
then `∫₀^{c_i} h |ξ| dξ = h c_i² / 2` (for `c_i ≥ 0`). -/
lemma aux_T3_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)
    (x h : ℝ) (hh : 0 ≤ h) (c_i : ℝ) (hc_i : 0 ≤ c_i) :
    |h * ∫ ξ in (0 : ℝ)..c_i, (f (y (x + h * ξ)) - f (y x))|
      ≤ (1/2) * h^2 * L^2 * M_bound * c_i^2 := by
  sorry

/-- **Sub-lemma 5 (T4 bound)**: by Lipschitz of `f` and
`aux_y_diff_norm_bound` applied at ξ = c_j,

  `|h Σ_j A_{ij} (f(y(x + h c_j)) − f(y x))| ≤ h² L² M Σ_j |A_{ij} c_j|`.

Proof sketch: each summand is bounded by `|A_{ij}| · L · h · |c_j| · (L M)`. -/
lemma aux_T4_bound {s : ℕ}
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)
    (A : Matrix (Fin s) (Fin s) ℝ)
    (c : Fin s → ℝ)
    (x h : ℝ) (hh : 0 ≤ h) (i : Fin s) :
    |h * ∑ j, A i j * (f (y (x + h * c j)) - f (y x))|
      ≤ h^2 * L^2 * M_bound * ∑ j, |A i j * c j| := by
  sorry

end AristotleBatch100
