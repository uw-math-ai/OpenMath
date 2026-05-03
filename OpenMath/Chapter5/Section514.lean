import Mathlib.Topology.Algebra.InfiniteSum.Basic
import OpenMath.Chapter5.Section512
import OpenMath.Chapter5.Section513

/-!
# Butcher §514 — The necessity of consistency (Theorem 514A)

This file scaffolds Butcher's Theorem 514A: a convergent general
linear method that is preconsistent (with preconsistency vector `u`)
is consistent — i.e. there exists a vector `v` such that
`B·𝟙 + V·v = u + v` (equation 510c).

## Cycle 094 deliverable (sorry-first scaffold)

* The main theorem `convergent_preconsistent_isConsistent` is stated
  with a `sorry` body and a textbook-faithful proof outline.
* Five sub-lemmas formalising Butcher's textbook proof are stated:
  `glmConstOneIterate` + `glmConstOneIterate_isGLMSolution` (sub-lemma
  A), `glmConstOneIterate_closed_form` (sub-lemma B),
  `cesaro_residual_tendsto_zero` (sub-lemma C),
  `exists_inverse_of_cesaro_zero` (sub-lemma D —
  **the infrastructure gap**, see `.prover-state/issues/cesaro_inverse_I_minus_V.md`),
  `witness_v_of_cesaro_inverse` (sub-lemma E).

## Textbook statement (quoted from `entities/thm_514A.json`)

> Let `(A, U, B, V)` denote a convergent method which is, moreover,
> covariant with preconsistency vector `u`. Then there exists a vector
> `v ∈ ℝ^r`, such that (510c) holds.

Equation (510c) is `B·𝟙 + V·v = u + v` (the second clause of
`def:510B`). We read "covariant with preconsistency vector `u`" as
`IsPreconsistent`.

## Proof strategy (Butcher §514)

> Consider the IVP `y'(x) = 1, y(0) = 0` with `φ(h) = 0` and `x = 1`.
> The sequence of approximations with `n` steps and `h = 1/n` is
> `y[i] = (1/n) B·𝟙 + V·y[i-1]`. The error after `n` steps is
> `y[n] - u = (1/n) (I + V + V² + ... + V^(n-1)) (B·𝟙 - u)`
> (using `V·u = u`). Because `V` has bounded powers, a Schur-like
> decomposition isolates the `1`-eigenspace, yielding the limit
> `S(B·𝟙 - u)` having only zeros in its first `r'` components, which
> rearranges to `B·𝟙 + V·v = u + v` with
> `v = S^{-1}(0; (I-W)^{-1} (S(B·𝟙 - u))_{2nd block})`.

In the Lean proof we replace the explicit Schur step with the
abstract mean-ergodic statement *if `(1/n) Σ V^k w → 0` and `V` is
power-bounded, then `w ∈ range (I - V)`* (sub-lemma D), then
algebraically rearrange to (510c).
-/

namespace OpenMath.Chapter5.Section510

open Matrix
open scoped BigOperators Topology Matrix.Norms.Operator

/-! ### Sub-lemma A — closed-form GLM iterate for `f ≡ 1`

For the autonomous RHS `f ≡ 1`, the GLM stage system collapses to
`f(Y j) = 1` for every `j`, so the recurrence reduces to
`y[n+1] = h · (B·𝟙) + V · y[n]`. Starting from `y[0] = 0`, this is a
GLM iteration of `M`. -/

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
  intro n
  refine ⟨fun i => (∑ j, M.A i j * h) +
                   (∑ j, M.U i j * M.glmConstOneIterate h n j), ?_, ?_⟩
  · intro i
    simp [mul_one]
  · intro i
    show M.glmConstOneIterate h (n + 1) i =
          (∑ j, M.B i j * (h * 1)) + (∑ j, M.V i j * M.glmConstOneIterate h n j)
    show (∑ j, M.B i j * h) + (∑ j, M.V i j * M.glmConstOneIterate h n j) =
          (∑ j, M.B i j * (h * 1)) + (∑ j, M.V i j * M.glmConstOneIterate h n j)
    simp [mul_one]

/-! ### Sub-lemma B — closed-form summation expression

The constant-one iterate at step `n` can be expressed as
`y[n] = h · Σ_{k=0}^{n-1} V^k · (B·𝟙)`. Proof by induction on `n`. -/

/-- Closed-form summation: `y[n] = h · Σ_{k=0}^{n-1} V^k · (B·𝟙)`. -/
theorem GeneralLinearMethod.glmConstOneIterate_closed_form {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (n : ℕ) :
    M.glmConstOneIterate h n =
      h • (∑ k ∈ Finset.range n,
              (M.V ^ k) *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ)))) := by
  sorry

/-! ### Sub-lemma C — Cesàro residual tends to zero

Plumbing from `IsConvergent` (instantiated at the trivial `f ≡ 1`
IVP `y(x) = x`) to the Cesàro statement
`(1/n) Σ V^k · (B·𝟙 - u) → 0`. The argument:

1. Apply `hConv` to `f ≡ 1`, `x₀ = 0`, `y₀ = 0`, `yex = id`,
   yielding a convergence-witness vector `u'` with `u' ≠ 0`.
2. Use `φ ≡ 0` (constant zero starting procedure); verify
   `Tendsto (fun h => 0) (nhds 0) (nhds (u' i * 0)) = nhds 0`.
3. Apply `hConv'` to the iterate `Y n m := M.glmConstOneIterate (1/n) m`.
4. Conclude `Y n n → fun i => u' i * yex 1 = u' i`.
5. Use `glmConstOneIterate_closed_form` to rewrite `Y n n`.
6. Subtract `u`-dependent term using `V·u = u` ⇒ `V^k · u = u`,
   factor, and conclude.

Note: `u'` from `IsConvergent` may differ from the `u` of
`IsPreconsistent`. For cycle 094 we accept this: the proof either
extracts `u` from `hPre` and shows the Cesàro statement directly, or
defers the bridging to a separate sub-lemma. -/

/-- Cesàro mean of `V^k · (B·𝟙 - u)` tends to `0` under
convergence + preconsistency. -/
theorem GeneralLinearMethod.cesaro_residual_tendsto_zero {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (_hConv : M.IsConvergent) {u : Fin r → ℝ}
    (_hPre_u : M.V *ᵥ u = u ∧ M.U *ᵥ u = (fun _ => 1)) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n,
            (M.V ^ k) *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ)) - u)))
      Filter.atTop (nhds 0) := by
  sorry

/-! ### Sub-lemma D — INFRASTRUCTURE GAP

The textbook step "Schur decomposition + invert `(I − W)` block"
is captured abstractly here as a finite-dimensional mean-ergodic
statement. **This is the gating infrastructure dependency for
`thm:514A`.** Multi-cycle work; see
`.prover-state/issues/cesaro_inverse_I_minus_V.md`. -/

/-- **INFRASTRUCTURE GAP** (cesaro_inverse_I_minus_V.md): if `V` is
power-bounded and the Cesàro mean of `V^k · w` tends to `0`, then
`w ∈ range (I − V)`. -/
theorem exists_inverse_of_cesaro_zero {r : ℕ}
    {V : Matrix (Fin r) (Fin r) ℝ}
    (_hPB : ∃ K : ℝ, ∀ n, ‖V ^ n‖ ≤ K)
    {w : Fin r → ℝ}
    (_hCes : Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ w))
      Filter.atTop (nhds 0)) :
    ∃ v : Fin r → ℝ,
      ((1 : Matrix (Fin r) (Fin r) ℝ) - V) *ᵥ v = w := by
  sorry

/-! ### Sub-lemma E — assemble the witness `v`

Given the Cesàro inverse `v` with `(I − V) v = B·𝟙 − u`, rearrange
to `B·𝟙 + V·v = u + v`. -/

/-- Witness construction: from the Cesàro inverse, build `v` such
that `B·𝟙 + V·v = u + v`. -/
private theorem GeneralLinearMethod.witness_v_of_cesaro_inverse {s r : ℕ}
    (M : GeneralLinearMethod s r) {u : Fin r → ℝ}
    (_hPre_u : M.V *ᵥ u = u ∧ M.U *ᵥ u = (fun _ => 1))
    (hCes : Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n,
            (M.V ^ k) *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ)) - u)))
      Filter.atTop (nhds 0))
    (hPB : ∃ K : ℝ, ∀ n, ‖M.V ^ n‖ ≤ K) :
    ∃ v : Fin r → ℝ,
      M.B *ᵥ (fun _ => (1 : ℝ)) + M.V *ᵥ v = u + v := by
  obtain ⟨v, hv⟩ := exists_inverse_of_cesaro_zero (V := M.V) hPB hCes
  refine ⟨v, ?_⟩
  -- hv : (1 - M.V) *ᵥ v = M.B *ᵥ 1 - u.
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hv
  -- hv : v - M.V *ᵥ v = M.B *ᵥ 1 - u.
  funext i
  have hi := congrFun hv i
  show (M.B *ᵥ (fun _ => (1 : ℝ))) i + (M.V *ᵥ v) i = u i + v i
  have hpi : (v - M.V *ᵥ v) i = v i - (M.V *ᵥ v) i := Pi.sub_apply v _ i
  have hpi' : (M.B *ᵥ (fun _ => (1 : ℝ)) - u) i =
              (M.B *ᵥ (fun _ => (1 : ℝ))) i - u i := Pi.sub_apply _ u i
  rw [hpi, hpi'] at hi
  linarith

/-! ### Stability ⇒ power-boundedness

Bridge from `M.IsStable` (existential of a `PowerBounded` constant) to
the explicit `‖V^n‖ ≤ K` form needed by sub-lemma D. -/

/-- The `V` block of a stable GLM is power-bounded with an explicit constant. -/
theorem GeneralLinearMethod.IsStable.powerBound {s r : ℕ}
    {M : GeneralLinearMethod s r} (hStable : M.IsStable) :
    ∃ K : ℝ, ∀ n, ‖M.V ^ n‖ ≤ K := by
  obtain ⟨K, hK⟩ := hStable
  exact ⟨K, hK⟩

/-! ### Main theorem: `thm:514A`

Butcher's textbook proof: under `IsConvergent` + `IsPreconsistent`
(witness `u`), instantiate the trivial IVP `y'(x) = 1, y(0) = 0`,
derive the Cesàro residual statement (sub-lemma C), invert
`(I − V)` via the mean-ergodic gap (sub-lemma D), and assemble the
witness `v` via sub-lemma E. -/

/-- **Butcher Theorem 514A** (p. 410) — A convergent preconsistent
GLM is consistent. -/
theorem GeneralLinearMethod.convergent_preconsistent_isConsistent
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (hConv : M.IsConvergent) (hPre : M.IsPreconsistent) :
    M.IsConsistent := by
  obtain ⟨u, hVu, hUu⟩ := hPre
  -- Get power-boundedness of V via the §513 stability theorem.
  have hStable := M.convergent_isStable hConv
  have hPB : ∃ K : ℝ, ∀ n, ‖M.V ^ n‖ ≤ K := hStable.powerBound
  -- Sub-lemma C: Cesàro residual tends to zero.
  have hCes := M.cesaro_residual_tendsto_zero hConv ⟨hVu, hUu⟩
  -- Sub-lemma E: assemble the witness v.
  obtain ⟨v, hv⟩ := M.witness_v_of_cesaro_inverse ⟨hVu, hUu⟩ hCes hPB
  -- Pack into IsConsistent.
  exact ⟨u, v, ⟨hVu, hUu⟩, hv⟩

end OpenMath.Chapter5.Section510
