/-
Cycle 138 Aristotle Job A: close `doublyCompanionMatrix_det_factorization`
for general `n` (Butcher Theorem 550A, p. 457).

## Theorem statement

For the doubly companion matrix `X` (encoded by `doublyCompanionMatrix α β`)
built from coefficient vectors `α, β : Fin n → ℂ`, we have
  `det(I − z X) = α(z) · β(z) + O(z^{n+1})`
as `z → 0` in ℂ. Here `α(z) = 1 + Σᵢ α_i z^{i+1}` and similarly for β.

## Suggested proof outline (Butcher's approach, eigenvalue density)

1. WLOG the `β` coefficients are chosen so that X has distinct non-zero
   eigenvalues. The set of such `β` is dense in ℂⁿ, and the LHS and RHS
   are both continuous in α and β, so density extends the conclusion.

2. On that dense set, let λ be an eigenvalue of X. Define
   `v_k = λ^k + β₁ λ^{k-1} + … + βₖ` for k = 0..n. Then
   `V = (v_{n-1}, v_{n-2}, …, v_0)` is the corresponding eigenvector
   (verify by comparing components 2..n of Xv = λv).
3. The first-component equation `λ v_n + α₁ v_{n-1} + … + αₙ = 0`
   reduces, after substitution `λ = z⁻¹`, to:
       det(I - zX) = α(z)·β(z) + O(z^{n+1}).

## Alternative proof routes

- Direct cofactor expansion of det(I - zX) for general n — feasible but
  tedious (~150 LOC).
- Induction on n via row-reduction (the bottom-right (n-1)×(n-1) block
  of X is itself a doubly companion matrix shifted down).

The witness for n = 1 is closed in Section550.lean directly; this file
asks Aristotle to handle the general n.
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace OpenMath.Chapter5.Section550

open Asymptotics

def doublyCompanionMatrix {n : ℕ} (α β : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if h0 : i.val = 0 then
    if hj : j.val + 1 = n then
      -α ⟨n - 1, by omega⟩ - β ⟨n - 1, by omega⟩
    else
      -α j
  else if hj : j.val + 1 = n then
    -β ⟨n - i.val - 1, by omega⟩
  else if i.val = j.val + 1 then
    1
  else
    0

noncomputable def alphaPoly {n : ℕ} (α : Fin n → ℂ) (z : ℂ) : ℂ :=
  1 + ∑ i : Fin n, α i * z ^ (i.val + 1)

noncomputable def betaPoly {n : ℕ} (β : Fin n → ℂ) (z : ℂ) : ℂ :=
  1 + ∑ i : Fin n, β i * z ^ (i.val + 1)

theorem doublyCompanionMatrix_det_factorization
    {n : ℕ} (α β : Fin n → ℂ) :
    Asymptotics.IsBigO (nhds (0 : ℂ))
      (fun z : ℂ =>
        (1 - z • doublyCompanionMatrix α β).det
          - alphaPoly α z * betaPoly β z)
      (fun z : ℂ => z ^ (n + 1)) := by
  sorry

end OpenMath.Chapter5.Section550
