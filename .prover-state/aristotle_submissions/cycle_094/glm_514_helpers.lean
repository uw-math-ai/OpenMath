import Mathlib

/-! Cycle 094 — Aristotle batch for `thm:514A` infrastructure helpers.

Self-contained file with the GLM structure inlined and four
infrastructure helpers as `sorry`s. The fifth (sub-lemma D —
`exists_inverse_of_cesaro_zero`) is the textbook's
"Schur decomposition + invert (I − W)" step and is deliberately NOT
included here: it requires Mathlib infrastructure (mean ergodic
theorem in finite dim, or Schur decomposition over ℝ) that does not
exist in current Mathlib. See
`.prover-state/issues/cesaro_inverse_I_minus_V.md`.

The four helpers submitted:

1. `glmConstOneIterate_isGLMSolution` (sub-lemma A) — for `f ≡ 1`,
   the closed-form recurrence `y[n+1] = h·B·𝟙 + V·y[n]` is a GLM
   iteration of `M`.
2. `glmConstOneIterate_closed_form` (sub-lemma B) — induction on `n`
   shows `y[n] = h · Σ_{k=0}^{n-1} V^k · (B·𝟙)`.
3. `cesaro_residual_tendsto_zero` (sub-lemma C) — plumbing from
   `IsConvergent` (instantiated at `f ≡ 1`, `y(x) = x`) to the
   Cesàro statement `(1/n) Σ V^k · (B·𝟙 − u) → 0`.
4. `witness_v_of_cesaro_inverse` (sub-lemma E) — given a `v` with
   `(I − V)·v = B·𝟙 − u`, rearrange to `B·𝟙 + V·v = u + v`.
-/

open Matrix
open scoped BigOperators Topology Matrix.Norms.Operator

namespace AristotleBatch094

/-- A general linear method (Butcher §510) with `s` internal stages
and `r` input/output values. -/
structure GeneralLinearMethod (s r : ℕ) where
  A : Matrix (Fin s) (Fin s) ℝ
  U : Matrix (Fin s) (Fin r) ℝ
  B : Matrix (Fin r) (Fin s) ℝ
  V : Matrix (Fin r) (Fin r) ℝ

/-- GLM iteration recurrence (def:511, used by def:512A). -/
def GeneralLinearMethod.IsGLMSolution {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (f : ℝ → ℝ)
    (y_seq : ℕ → Fin r → ℝ) : Prop :=
  ∀ n : ℕ, ∃ Y : Fin s → ℝ,
    (∀ i, Y i = (∑ j, M.A i j * (h * f (Y j)))
                + (∑ j, M.U i j * y_seq n j))
    ∧ (∀ i, y_seq (n + 1) i = (∑ j, M.B i j * (h * f (Y j)))
                              + (∑ j, M.V i j * y_seq n j))

/-- IsConvergent (def:512A): for any Lipschitz IVP there exists a
non-zero `u` such that any `n`-step iterate converges to `u·yex(x)`. -/
def GeneralLinearMethod.IsConvergent {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∀ (f : ℝ → ℝ) (L : NNReal), LipschitzWith L f →
  ∀ (x₀ y₀ : ℝ) (yex : ℝ → ℝ),
    yex x₀ = y₀ →
    (∀ x, HasDerivAt yex (f (yex x)) x) →
  ∃ u : Fin r → ℝ, u ≠ 0 ∧
    ∀ φ : ℝ → Fin r → ℝ,
      (∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                       (nhds 0) (nhds (u i * y₀))) →
    ∀ x : ℝ, x₀ < x →
    ∀ Y : ℕ → ℕ → Fin r → ℝ,
      (∀ n : ℕ, 0 < n →
        Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
        M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n)) →
      Filter.Tendsto (fun n : ℕ => Y n n)
                     Filter.atTop (nhds (fun i => u i * yex x))

/-! ## Sub-lemma A — closed-form iterate for `f ≡ 1` -/

/-- Closed-form GLM iteration for the autonomous RHS `f ≡ 1`,
starting from `y_seq 0 = 0`. -/
noncomputable def GeneralLinearMethod.glmConstOneIterate {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) : ℕ → Fin r → ℝ
  | 0       => fun _ => 0
  | n + 1   => fun i =>
      (∑ j, M.B i j * h) +
      (∑ j, M.V i j * GeneralLinearMethod.glmConstOneIterate M h n j)

/-- The constant-one iterate is a GLM iteration of `M` for `f ≡ 1`. -/
theorem GeneralLinearMethod.glmConstOneIterate_isGLMSolution {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) :
    M.IsGLMSolution h (fun _ => (1 : ℝ)) (M.glmConstOneIterate h) := by
  sorry

/-! ## Sub-lemma B — closed-form summation expression -/

/-- Closed-form summation: `y[n] = h · Σ_{k=0}^{n-1} V^k · (B·𝟙)`. -/
theorem GeneralLinearMethod.glmConstOneIterate_closed_form {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (n : ℕ) :
    M.glmConstOneIterate h n =
      h • (∑ k ∈ Finset.range n,
              (M.V ^ k) *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ)))) := by
  sorry

/-! ## Sub-lemma C — Cesàro residual tends to zero

Bridge from `IsConvergent` (instantiated at the trivial `f ≡ 1` IVP
`y'(x) = 1, y(0) = 0` with exact solution `yex(x) = x`) to the
Cesàro residual statement
`(1/n) Σ V^k · (B·𝟙 − u) → 0`.

Hint outline:

1. `f := fun _ => 1` is `LipschitzWith 0` (constant).
2. `yex := id`; `yex 0 = 0`; `HasDerivAt id 1 x` (from
   `hasDerivAt_id` and `id` rewrites — note `f (yex x) = 1`).
3. Apply `hConv f 0 hLip 0 0 yex rfl hOde` to extract some `u'` with
   `u' ≠ 0`.
4. Use the constant-zero starting procedure `φ ≡ 0`; verify
   `Tendsto (fun _ => 0) (nhds 0) (nhds (u' i * 0)) = nhds 0`.
5. Apply `hConv'` with `x = 1` to the family
   `Y n m := M.glmConstOneIterate (1/n) m`. Discharge the
   `IsGLMSolution` premise by sub-lemma A (specialised to `h = 1/n`)
   and the `Y n 0 = φ ((1-0)/n)` premise via the recurrence base case
   `M.glmConstOneIterate (1/n) 0 = 0`.
6. Conclude `Y n n → fun i => u' i * 1 = u'`.
7. Use sub-lemma B to rewrite `Y n n = (1/n) · Σ V^k · (B·𝟙)`.
8. The hypothesis here uses `u`, not `u'`. Possible reconciliation: if
   `u' = u` (textbook says they coincide for preconsistent methods),
   the Cesàro statement follows by subtracting `u` from both sides
   (using `V·u = u` ⇒ `V^k · u = u`, hence
   `Σ V^k · u = n·u`, hence `(1/n) Σ V^k · u = u`).

Aristotle: feel free to attempt with the simplification `u = u'` (i.e.
prove the Cesàro statement *for the convergence-witness `u'`*). If
the bridge `u' = u` is the issue, return a partial proof and we will
formalise the bridge separately. -/

/-- Cesàro mean of `V^k · (B·𝟙 − u)` tends to `0` under
convergence + preconsistency. -/
theorem GeneralLinearMethod.cesaro_residual_tendsto_zero {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (hConv : M.IsConvergent) {u : Fin r → ℝ}
    (hPre_u : M.V *ᵥ u = u ∧ M.U *ᵥ u = (fun _ => 1)) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n,
            (M.V ^ k) *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ)) - u)))
      Filter.atTop (nhds 0) := by
  sorry

/-! ## Sub-lemma E — assemble witness `v`

Algebraic rearrangement: `(I − V) · v = B·𝟙 − u` ⟺
`v − V v = B·𝟙 − u` ⟺ `B·𝟙 + V v = u + v`. -/

/-- Witness construction: given `v` with `(I − V) · v = B·𝟙 − u`,
exhibit `B·𝟙 + V·v = u + v`. -/
theorem GeneralLinearMethod.witness_v_of_cesaro_inverse {s r : ℕ}
    (M : GeneralLinearMethod s r) {u v : Fin r → ℝ}
    (hv : ((1 : Matrix (Fin r) (Fin r) ℝ) - M.V) *ᵥ v =
            M.B *ᵥ (fun _ => (1 : ℝ)) - u) :
    M.B *ᵥ (fun _ => (1 : ℝ)) + M.V *ᵥ v = u + v := by
  sorry

end AristotleBatch094
