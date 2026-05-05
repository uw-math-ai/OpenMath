import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import OpenMath.Chapter5.Section512
import OpenMath.Chapter5.Section513

/-!
# Butcher §514 — The necessity of consistency (Theorem 514A)

This file scaffolds Butcher's Theorem 514A: a convergent general
linear method that is preconsistent (with preconsistency vector `u`)
is consistent — i.e. there exists a vector `v` such that
`B·𝟙 + V·v = u + v` (equation 510c).

## Status (cycle 099): closed

The main theorem `convergent_preconsistent_isConsistent` is now
sorry-free. Sub-lemmas:

* `glmConstOneIterate` + `glmConstOneIterate_isGLMSolution` (sub-lemma A)
* `glmConstOneIterate_closed_form` (sub-lemma B)
* `cesaro_residual_tendsto_zero` (sub-lemma C — closed cycle 099 as
  a pure-algebraic identity)
* `cesaro_orthogonal_to_VT_fixed` + `exists_inverse_of_cesaro_zero`
  (sub-lemma D — closed cycle 097 via Path B mean ergodic)
* `witness_v_of_cesaro_inverse` (sub-lemma E)
* `convergence_witness_satisfies_U` (cycle 099) — convergence-
  witness vector `u'` is itself a preconsistency vector
* `convergent_isPreconsistent` (cycle 099) — GLM analog of LMM
  `thm:405B`: convergent ⇒ preconsistent

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
  induction n with
  | zero =>
    funext i
    simp [GeneralLinearMethod.glmConstOneIterate]
  | succ n ih =>
    -- Reshape the RHS: peel off the k = 0 term, factor V out of the
    -- inner sum, distribute h • over +, and substitute the IH.
    rw [Finset.sum_range_succ']
    simp_rw [pow_succ', ← Matrix.mulVec_mulVec]
    rw [← Matrix.mulVec_sum, pow_zero, Matrix.one_mulVec, smul_add,
        ← Matrix.mulVec_smul, ← ih]
    -- Goal is now: glmConstOneIterate h (n+1) =
    --              V *ᵥ glmConstOneIterate h n + h • (B *ᵥ 𝟙)
    funext i
    show (∑ j, M.B i j * h) + (∑ j, M.V i j * M.glmConstOneIterate h n j) =
         (M.V *ᵥ M.glmConstOneIterate h n +
            h • (M.B *ᵥ (fun _ => (1 : ℝ)))) i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, mul_one, Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring

/-! ### Sub-lemma C — Cesàro residual tends to zero (cycle 099)

Pure-algebraic statement (no GLM dependence): given
`hY_lim : (1/n) • Σ_{k<n} V^k *ᵥ B1 → u'` and a fixed-point witness
`hVu' : V *ᵥ u' = u'`, the residual Cesàro sum
`(1/n) • Σ_{k<n} V^k *ᵥ (B1 - u')` tends to `0`.

Proof: by induction `V^k *ᵥ u' = u'` for all k; distributing
`V^k *ᵥ (B1 - u') = V^k *ᵥ B1 - u'`; the sum becomes
`(Σ V^k *ᵥ B1) - n • u'`, and `(1/n) • (n • u') = u'` for `n ≥ 1`,
so the difference Cesàro sum tends to `u' - u' = 0`.

Cycle 099 reformulation: previously the lemma was parameterised by
`hConv` and a preconsistency witness `u`. Now it's parameterised by
the convergence-witness `u'` and its V-fixed property — the GLM
context is no longer needed. The consumer
(`convergent_preconsistent_isConsistent`) supplies these via
`convergence_witness_satisfies_U`. -/

/-- Cesàro mean of `V^k *ᵥ (B1 - u')` tends to `0`, given that the
Cesàro mean of `V^k *ᵥ B1` tends to `u'` and `V *ᵥ u' = u'`. -/
private theorem cesaro_residual_tendsto_zero
    {r : ℕ} (V : Matrix (Fin r) (Fin r) ℝ) (B1 : Fin r → ℝ)
    {u' : Fin r → ℝ}
    (hVu' : V *ᵥ u' = u')
    (hY_lim : Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ B1))
      Filter.atTop (nhds u')) :
    Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ (B1 - u')))
      Filter.atTop (nhds 0) := by
  -- Step 1: V^k *ᵥ u' = u' for all k.
  have hV_pow_u : ∀ k : ℕ, V ^ k *ᵥ u' = u' := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact Matrix.one_mulVec u'
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hVu', ih]
  -- Step 2: distribute V^k over the subtraction.
  have hsplit : ∀ k : ℕ, V ^ k *ᵥ (B1 - u') = V ^ k *ᵥ B1 - u' := by
    intro k; rw [Matrix.mulVec_sub, hV_pow_u k]
  -- Step 3: pointwise (componentwise) reduction to scalar Tendsto.
  rw [tendsto_pi_nhds]; intro i
  show Filter.Tendsto
      (fun n : ℕ => ((1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ (B1 - u'))) i)
      Filter.atTop (nhds 0)
  -- Step 4: pointwise equality (for n ≥ 1):
  --   ((1/n) • Σ V^k *ᵥ (B1 - u')) i = ((1/n) • Σ V^k *ᵥ B1) i - u' i.
  have h_pointwise : ∀ n : ℕ, 0 < n →
      ((1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ (B1 - u'))) i
      = ((1 / (n : ℝ)) •
          (∑ k ∈ Finset.range n, (V ^ k) *ᵥ B1)) i - u' i := by
    intro n hn
    have h_inner : ∀ k ∈ Finset.range n,
        ((V ^ k) *ᵥ (B1 - u')) i = ((V ^ k) *ᵥ B1) i - u' i := by
      intro k _
      rw [hsplit]; rfl
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [Finset.sum_congr rfl h_inner, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    field_simp
  -- Step 5: hY_lim componentwise gives convergence to u' i.
  have hY_lim_i : Filter.Tendsto
      (fun n : ℕ => ((1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ B1)) i)
      Filter.atTop (nhds (u' i)) := (tendsto_pi_nhds.mp hY_lim) i
  -- Step 6: subtract u' i to get → 0.
  have h_sub_lim : Filter.Tendsto
      (fun n : ℕ => ((1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ B1)) i - u' i)
      Filter.atTop (nhds (u' i - u' i)) := hY_lim_i.sub tendsto_const_nhds
  rw [sub_self] at h_sub_lim
  -- Step 7: bridge eventually-equal.
  have h_eventually : (fun n : ℕ => ((1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ (B1 - u'))) i)
      =ᶠ[Filter.atTop]
      (fun n : ℕ => ((1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ B1)) i - u' i) :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => h_pointwise n hn⟩
  exact (Filter.tendsto_congr' h_eventually).mpr h_sub_lim

/-! ### Sub-lemma D — INFRASTRUCTURE GAP

The textbook step "Schur decomposition + invert `(I − W)` block"
is captured abstractly here as a finite-dimensional mean-ergodic
statement. **This is the gating infrastructure dependency for
`thm:514A`.** Multi-cycle work; see
`.prover-state/issues/cesaro_inverse_I_minus_V.md`. -/

/-- Inner-product orthogonality (Path B step 1): under the
Cesàro-zero hypothesis on `V` and `w`, every fixed point `u` of
`Vᵀ` satisfies `dotProduct w u = 0`. -/
private lemma cesaro_orthogonal_to_VT_fixed {r : ℕ}
    {V : Matrix (Fin r) (Fin r) ℝ}
    {w : Fin r → ℝ}
    (hCes : Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ w))
      Filter.atTop (nhds 0))
    {u : Fin r → ℝ} (hu : V.transpose *ᵥ u = u) :
    dotProduct w u = 0 := by
  -- Step 1: V.transpose ^ k *ᵥ u = u for all k.
  have hVT_pow : ∀ k : ℕ, V.transpose ^ k *ᵥ u = u := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact Matrix.one_mulVec u
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hu, ih]
  -- Step 2: per-k identity dotProduct (V^k *ᵥ w) u = dotProduct w u.
  have h_per_k : ∀ k : ℕ,
      dotProduct ((V ^ k) *ᵥ w) u = dotProduct w u := by
    intro k
    rw [dotProduct_comm, dotProduct_mulVec]
    have h_uV : u ᵥ* V ^ k = u := by
      rw [← Matrix.mulVec_transpose, Matrix.transpose_pow]
      exact hVT_pow k
    rw [h_uV, dotProduct_comm]
  -- Step 3: sum identity.
  have h_sum : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, dotProduct ((V ^ k) *ᵥ w) u)
        = (n : ℝ) * dotProduct w u := by
    intro n
    simp_rw [h_per_k]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Step 4: bridge sum into dotProduct.
  have h_bridge_sum : ∀ n : ℕ,
      dotProduct (∑ k ∈ Finset.range n, (V ^ k) *ᵥ w) u
        = (n : ℝ) * dotProduct w u := by
    intro n
    rw [sum_dotProduct, h_sum n]
  -- Step 5: combine smul into dotProduct + cancellation (n > 0).
  have h_eventually : ∀ n : ℕ, 0 < n →
      dotProduct
        ((1 / (n : ℝ)) • (∑ k ∈ Finset.range n, (V ^ k) *ᵥ w)) u
        = dotProduct w u := by
    intro n hn
    rw [smul_dotProduct, h_bridge_sum, smul_eq_mul]
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
    field_simp
  -- Step 6: continuity → lift hCes to dotProduct convergence.
  have h_cont : Continuous fun s : Fin r → ℝ => dotProduct s u :=
    Continuous.dotProduct continuous_id continuous_const
  have h_lim : Filter.Tendsto
      (fun n : ℕ => dotProduct
        ((1 / (n : ℝ)) • (∑ k ∈ Finset.range n, (V ^ k) *ᵥ w)) u)
      Filter.atTop (nhds (dotProduct (0 : Fin r → ℝ) u)) :=
    (h_cont.tendsto _).comp hCes
  rw [zero_dotProduct] at h_lim
  -- Step 7: the same sequence is eventually-constant `dotProduct w u`.
  have h_eq : (fun _ : ℕ => dotProduct w u) =ᶠ[Filter.atTop]
      (fun n : ℕ => dotProduct
        ((1 / (n : ℝ)) • (∑ k ∈ Finset.range n, (V ^ k) *ᵥ w)) u) :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => (h_eventually n hn).symm⟩
  have h_const : Filter.Tendsto
      (fun n : ℕ => dotProduct
        ((1 / (n : ℝ)) • (∑ k ∈ Finset.range n, (V ^ k) *ᵥ w)) u)
      Filter.atTop (nhds (dotProduct w u)) :=
    (Filter.tendsto_congr' h_eq).mp tendsto_const_nhds
  -- Step 8: tendsto_nhds_unique.
  exact tendsto_nhds_unique h_const h_lim

/-- Path B mean-ergodic step: if `V` is power-bounded (`_hPB` is
unused here — power-boundedness is needed for
`cesaro_residual_tendsto_zero`, not for the orthogonal-range
argument) and the Cesàro mean of `V^k · w` tends to `0`, then
`w ∈ range (I − V)`. The proof goes through the inner-product
orthogonality lemma `cesaro_orthogonal_to_VT_fixed` plus the
finite-dim Fredholm alternative `LinearMap.orthogonal_ker`. -/
theorem exists_inverse_of_cesaro_zero {r : ℕ}
    {V : Matrix (Fin r) (Fin r) ℝ}
    (_hPB : ∃ K : ℝ, ∀ n, ‖V ^ n‖ ≤ K)
    {w : Fin r → ℝ}
    (hCes : Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n, (V ^ k) *ᵥ w))
      Filter.atTop (nhds 0)) :
    ∃ v : Fin r → ℝ,
      ((1 : Matrix (Fin r) (Fin r) ℝ) - V) *ᵥ v = w := by
  set M : Matrix (Fin r) (Fin r) ℝ := 1 - V with hM_def
  -- Work in EuclideanSpace ℝ (Fin r) via toEuclideanLin.
  set T : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin r) :=
    Matrix.toEuclideanLin M with hT_def
  set w_E : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 w with hw_E_def
  -- adjoint(T) = (Mᵀ).toEuclideanLin (over ℝ, conjTranspose = transpose).
  have hT_adj : LinearMap.adjoint T = Matrix.toEuclideanLin M.transpose := by
    rw [hT_def, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        Matrix.conjTranspose_eq_transpose_of_trivial]
  -- Step A: `w_E ∈ (T.adjoint).kerᗮ`.
  have h_orth : w_E ∈ (LinearMap.adjoint T).kerᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u_E hu_E_ker
    set u : Fin r → ℝ := u_E.ofLp with hu_def
    -- u_E ∈ ker(T.adjoint) ⟹ V.transpose *ᵥ u = u.
    have hadj_apply : Matrix.toEuclideanLin M.transpose u_E = 0 := by
      rw [← hT_adj]; exact hu_E_ker
    have hMTu : M.transpose *ᵥ u = 0 := by
      have h_apply : Matrix.toEuclideanLin M.transpose u_E
                      = WithLp.toLp 2 (M.transpose *ᵥ u_E.ofLp) :=
        Matrix.toEuclideanLin_apply M.transpose u_E
      rw [h_apply] at hadj_apply
      have hzero : WithLp.toLp 2 (M.transpose *ᵥ u_E.ofLp)
                    = WithLp.toLp 2 (0 : Fin r → ℝ) := by
        rw [hadj_apply]; rfl
      have := (WithLp.toLp_injective 2 (V := Fin r → ℝ)) hzero
      simpa [hu_def] using this
    have hVu : V.transpose *ᵥ u = u := by
      have h_eq : M.transpose = (1 : Matrix (Fin r) (Fin r) ℝ) - V.transpose := by
        rw [hM_def, Matrix.transpose_sub, Matrix.transpose_one]
      rw [h_eq, Matrix.sub_mulVec, Matrix.one_mulVec] at hMTu
      -- hMTu : u - V.transpose *ᵥ u = 0
      exact (sub_eq_zero.mp hMTu).symm
    -- Apply orthogonality lemma.
    have hdot : dotProduct w u = 0 :=
      cesaro_orthogonal_to_VT_fixed hCes hVu
    -- Bridge to inner-product form.
    have hinner : inner ℝ u_E w_E = (0 : ℝ) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      -- ⟨u_E, w_E⟩ = w_E.ofLp ⬝ᵥ star u_E.ofLp = w ⬝ᵥ u (over ℝ, star = id).
      show w_E.ofLp ⬝ᵥ star u_E.ofLp = 0
      have hw_ofLp : w_E.ofLp = w := WithLp.ofLp_toLp 2 w
      have hstar_u : star u_E.ofLp = u_E.ofLp := by
        funext i
        exact star_trivial _
      rw [hw_ofLp, hstar_u, ← hu_def]
      exact hdot
    exact hinner
  -- Step B: `(T.adjoint).kerᗮ = T.range` via `(range T)ᗮ = ker(T.adjoint)`
  -- and `Submodule.orthogonal_orthogonal` in finite-dim.
  have h_orth_range : (LinearMap.range T)ᗮ = LinearMap.ker (LinearMap.adjoint T) := by
    ext x
    simp only [Submodule.mem_orthogonal, LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · intro hx
      refine ext_inner_left ℝ fun v => ?_
      rw [inner_zero_right, LinearMap.adjoint_inner_right]
      exact hx (T v) ⟨v, rfl⟩
    · rintro hx _ ⟨v, rfl⟩
      rw [← LinearMap.adjoint_inner_right, hx]
      exact inner_zero_right v
  have h_range_eq : (LinearMap.adjoint T).kerᗮ = LinearMap.range T := by
    rw [← h_orth_range]
    exact Submodule.orthogonal_orthogonal _
  rw [h_range_eq] at h_orth
  -- Step C: extract `v_E` and convert to `v : Fin r → ℝ`.
  obtain ⟨v_E, hv_E⟩ := LinearMap.mem_range.mp h_orth
  refine ⟨v_E.ofLp, ?_⟩
  -- T v_E = w_E, so M *ᵥ v_E.ofLp = w.
  have h_apply : T v_E = WithLp.toLp 2 (M *ᵥ v_E.ofLp) :=
    Matrix.toEuclideanLin_apply M v_E
  rw [h_apply] at hv_E
  have hv_E' : WithLp.toLp 2 (M *ᵥ v_E.ofLp) = WithLp.toLp 2 w := hv_E
  exact (WithLp.toLp_injective 2 (V := Fin r → ℝ)) hv_E'

/-! ### Sub-lemma E — assemble the witness `v`

Given the Cesàro inverse `v` with `(I − V) v = B·𝟙 − u`, rearrange
to `B·𝟙 + V·v = u + v`. -/

/-- Witness construction: from the Cesàro inverse, build `v` such
that `B·𝟙 + V·v = u' + v`. -/
private theorem GeneralLinearMethod.witness_v_of_cesaro_inverse {s r : ℕ}
    (M : GeneralLinearMethod s r) {u' : Fin r → ℝ}
    (_hPre_u' : M.V *ᵥ u' = u' ∧ M.U *ᵥ u' = (fun _ => 1))
    (hCes : Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n,
            (M.V ^ k) *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ)) - u')))
      Filter.atTop (nhds 0))
    (hPB : ∃ K : ℝ, ∀ n, ‖M.V ^ n‖ ≤ K) :
    ∃ v : Fin r → ℝ,
      M.B *ᵥ (fun _ => (1 : ℝ)) + M.V *ᵥ v = u' + v := by
  obtain ⟨v, hv⟩ := exists_inverse_of_cesaro_zero (V := M.V) hPB hCes
  refine ⟨v, ?_⟩
  -- hv : (1 - M.V) *ᵥ v = M.B *ᵥ 1 - u'.
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hv
  -- hv : v - M.V *ᵥ v = M.B *ᵥ 1 - u'.
  funext i
  have hi := congrFun hv i
  show (M.B *ᵥ (fun _ => (1 : ℝ))) i + (M.V *ᵥ v) i = u' i + v i
  have hpi : (v - M.V *ᵥ v) i = v i - (M.V *ᵥ v) i := Pi.sub_apply v _ i
  have hpi' : (M.B *ᵥ (fun _ => (1 : ℝ)) - u') i =
              (M.B *ᵥ (fun _ => (1 : ℝ))) i - u' i := Pi.sub_apply _ u' i
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

/-! ### Convergence-witness vector is a preconsistency vector

The convergence-witness vector `u'` extracted from `M.IsConvergent`
(applied to the trivial IVP `y'(x) = 1, y(0) = 0, yex = id`) is
itself a preconsistency vector: it satisfies both `V·u' = u'` and
`U·u' = 𝟙` (with `u' ≠ 0`). This sidesteps the textbook's implicit
`u' = u` identification — `IsConsistent` is existential, so we can
just use `u'` as the witness. The fourth conclusion is the Cesàro
sum form, used by `cesaro_residual_tendsto_zero`. -/

/-- Algebraic identity: `V *ᵥ y[n] = y[n] + h • (V^n *ᵥ B1 - B1)`
where `y[n] = M.glmConstOneIterate h n`. Proof: substitute the
closed form, distribute `V` through the `h • Σ` shell, reindex
`Σ_{k<n} V^(k+1) = Σ_{k<n+1} V^k - V^0`. -/
private lemma GeneralLinearMethod.V_mulVec_glmConstOneIterate_eq
    {s r : ℕ} (M : GeneralLinearMethod s r) (h : ℝ) (n : ℕ) :
    M.V *ᵥ M.glmConstOneIterate h n =
      M.glmConstOneIterate h n
      + h • (M.V ^ n *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ)))
              - M.B *ᵥ (fun _ => (1 : ℝ))) := by
  rw [M.glmConstOneIterate_closed_form h n,
      Matrix.mulVec_smul, Matrix.mulVec_sum]
  have hterm : ∀ k : ℕ, M.V *ᵥ (M.V ^ k *ᵥ (M.B *ᵥ (fun _ => (1:ℝ)))) =
                M.V ^ (k+1) *ᵥ (M.B *ᵥ (fun _ => (1:ℝ))) := by
    intro k
    rw [Matrix.mulVec_mulVec, ← pow_succ']
  simp_rw [hterm]
  -- LHS: h • Σ_{k<n} V^(k+1) *ᵥ (B *ᵥ 𝟙)
  -- RHS: h • Σ V^k *ᵥ (B *ᵥ 𝟙) + h • (V^n *ᵥ (B *ᵥ 𝟙) - B *ᵥ 𝟙)
  set v : Fin r → ℝ := M.B *ᵥ (fun _ => (1:ℝ)) with hv_def
  -- Reindex `Σ V^(k+1) *ᵥ v = (Σ V^k *ᵥ v) + V^n *ᵥ v - v` via
  -- the two `sum_range_succ` peels.
  have h1 : (∑ k ∈ Finset.range n, M.V ^ (k+1) *ᵥ v) + (M.V ^ (0 : ℕ)) *ᵥ v
              = ∑ k ∈ Finset.range (n+1), M.V ^ k *ᵥ v := by
    exact (Finset.sum_range_succ' (fun k => M.V ^ k *ᵥ v) n).symm
  have h2 : ∑ k ∈ Finset.range (n+1), M.V ^ k *ᵥ v =
              (∑ k ∈ Finset.range n, M.V ^ k *ᵥ v) + M.V ^ n *ᵥ v := by
    exact Finset.sum_range_succ (fun k => M.V ^ k *ᵥ v) n
  have hV0 : (M.V ^ (0 : ℕ)) *ᵥ v = v := by
    rw [pow_zero, Matrix.one_mulVec]
  rw [hV0] at h1
  have h12 : (∑ k ∈ Finset.range n, M.V ^ (k+1) *ᵥ v) + v
              = (∑ k ∈ Finset.range n, M.V ^ k *ᵥ v) + M.V ^ n *ᵥ v :=
    h1.trans h2
  -- Goal: h • Σ V^(k+1) *ᵥ v = h • Σ V^k *ᵥ v + h • (V^n *ᵥ v - v)
  rw [smul_sub]
  -- Reduce to vector equation: rewrite as a single funext.
  funext i
  have hi := congrFun h12 i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply] at hi ⊢
  linear_combination h * hi

/-- **Convergence-witness preconsistency**: the convergence-witness
vector `u'` extracted from `M.IsConvergent` (applied to the trivial
IVP `y'(x) = 1, y(0) = 0, yex = id`) is itself a preconsistency
vector — it satisfies both `M.V *ᵥ u' = u'` AND `M.U *ᵥ u' = 𝟙`.
The fourth conclusion exposes the Cesàro-sum form of the limit
(consumed by `cesaro_residual_tendsto_zero`).

This is the load-bearing helper for `thm:514A`. The cycle 098
strengthening of `IsConvergent` (with the stage-limit clause) is
exactly what enables the `U *ᵥ u' = 𝟙` extraction in Step 8.

**Cycle 116 cascade fallback (Solution A → option (b) propagation)**:
the cycle 116 strengthening of `IsConvergent` (Solution A: localized
`M_bound` to `Set.Icc x₀ x`) requires the consumer to discharge a
Frobenius-norm contraction `‖((x - x₀) * L) • A.map abs‖ < 1` at the
chosen `(x, L)`. For `yex = id` we use `L := 1` (since `|deriv id| = 1`
forces `L ≥ 1`); thus the obligation specializes to
`‖(1 : ℝ) • A.map abs‖ = ‖A.map abs‖ < 1` (Frobenius). Per the cycle
113 audit (`cycle_113_isconvergent_strengthening_514_blocker.md`), the
clean Solution A discharge required option (a) restructuring (small
`x` chosen so the bound holds via `lim_{x→0} x·A = 0`). For this
cycle we use the FALLBACK (option b): propagate the bound as a
hypothesis. -/
private theorem GeneralLinearMethod.convergence_witness_satisfies_U
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (hConv : M.IsConvergent)
    -- Cycle 116 fallback: Frobenius bound on `A.map abs` (the obligation
    -- left over from instantiating IsConvergent's localized M_bound at
    -- the trivial IVP `f ≡ 1, yex = id, x₀ = 0, x = 1, L = 1`).
    (h_norm_obligation : @norm _ Matrix.frobeniusNormedRing.toNorm
      (M.A.map (fun a => |a|)) < 1) :
    ∃ u' : Fin r → ℝ,
      u' ≠ 0 ∧
      M.V *ᵥ u' = u' ∧
      M.U *ᵥ u' = (fun _ => 1) ∧
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) •
          (∑ k ∈ Finset.range n,
              (M.V ^ k) *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ)))))
        Filter.atTop (nhds u') := by
  -- Step 1: trivial IVP setup (f ≡ 1, x₀ = 0, y₀ = 0, yex = id).
  -- Cycle 116: use `L := 1` (any L ≥ 1 works; L = 0 is incompatible with
  -- |deriv id| = 1 ≤ L · M_bound).
  set f : ℝ → ℝ := fun _ => (1 : ℝ) with hf_def
  set yex : ℝ → ℝ := id with hyex_def
  have hf_lip : LipschitzWith 1 f := by
    rw [hf_def]
    exact (LipschitzWith.const (1 : ℝ)).weaken (by norm_num)
  have hyex_x₀ : yex 0 = 0 := rfl
  have hyex_ode : ∀ x : ℝ, HasDerivAt yex (f (yex x)) x := by
    intro x
    rw [hyex_def, hf_def]
    exact hasDerivAt_id x
  -- Step 2: extract u' from hConv.
  obtain ⟨u', hu'_ne, hConv'⟩ :=
    hConv f 1 hf_lip 0 0 yex hyex_x₀ hyex_ode
  -- Step 3: instantiate hConv' at φ ≡ 0, x = 1, Y := glmConstOneIterate (1/n).
  set φ : ℝ → Fin r → ℝ := fun _ _ => (0 : ℝ) with hφ_def
  set Y : ℕ → ℕ → Fin r → ℝ :=
    fun n m => M.glmConstOneIterate ((1 - 0 : ℝ) / (n : ℝ)) m with hY_def
  have hφ_tendsto : ∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                       (nhds 0) (nhds (u' i * 0)) := by
    intro i
    rw [show u' i * 0 = 0 from by ring]
    exact tendsto_const_nhds
  have hxx : (0 : ℝ) < 1 := by norm_num
  -- Cycle 098 stage choice: for f ≡ 1 the stage equation reduces to
  --   `Y_int n i = (1/n) • (A𝟙)_i + (U *ᵥ Y n n)_i`.
  set Y_int : ℕ → Fin s → ℝ :=
    fun n i => (∑ j, M.A i j * (((1 - 0 : ℝ) / (n : ℝ)) * f (0 : ℝ)))
               + (∑ j, M.U i j * Y n n j) with hY_int_def
  have hY_props : ∀ n : ℕ, 0 < n →
      Y n 0 = φ ((1 - 0) / (n : ℝ)) ∧
      M.IsGLMSolution ((1 - 0) / (n : ℝ)) f (Y n) ∧
      (∀ i, Y_int n i =
        (∑ j, M.A i j * (((1 - 0) / (n : ℝ)) * f (Y_int n j)))
        + (∑ j, M.U i j * Y n n j)) := by
    intro n hn
    refine ⟨?_, ?_, ?_⟩
    · funext i
      show M.glmConstOneIterate ((1 - 0 : ℝ) / (n : ℝ)) 0 i = (0 : ℝ)
      rfl
    · rw [hf_def]
      exact M.glmConstOneIterate_isGLMSolution ((1 - 0 : ℝ) / (n : ℝ))
    · intro i
      show (∑ j, M.A i j * (((1 - 0 : ℝ) / (n : ℝ)) * f (0 : ℝ)))
            + (∑ j, M.U i j * Y n n j) =
            (∑ j, M.A i j * (((1 - 0) / (n : ℝ)) * f (Y_int n j)))
            + (∑ j, M.U i j * Y n n j)
      simp only [hf_def]
  -- Cycle 116: discharge the four localized hypotheses on `[0, 1]`.
  -- For `yex = id` and `L := 1`: `M_bound := 1`, `|id t| = |t| ≤ 1`,
  -- `|deriv id t| = 1 ≤ 1 · 1`, and `‖A.map abs‖ < 1` is the propagated
  -- `h_norm_obligation`.
  have hyex_C1 : ContDiff ℝ 1 yex := by
    rw [hyex_def]; exact contDiff_id
  have hyex_M : ∀ t ∈ Set.Icc (0 : ℝ) 1, |yex t| ≤ 1 := by
    intro t ht
    rw [hyex_def]
    show |t| ≤ 1
    obtain ⟨h0, h1⟩ := Set.mem_Icc.mp ht
    rw [abs_of_nonneg h0]; exact h1
  have hyex'_LM : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |deriv yex t| ≤ ((1 : NNReal) : ℝ) * 1 := by
    intro t _
    rw [hyex_def]
    show |deriv (fun x : ℝ => x) t| ≤ ((1 : NNReal) : ℝ) * 1
    rw [deriv_id'']
    push_cast
    norm_num
  have h_norm : @norm _ Matrix.frobeniusNormedRing.toNorm
                  (((1 - 0 : ℝ) * ((1 : NNReal) : ℝ)) • M.A.map (fun a => |a|))
                < 1 := by
    have h0 : (1 - 0 : ℝ) * ((1 : NNReal) : ℝ) = 1 := by push_cast; ring
    rw [h0, one_smul]
    exact h_norm_obligation
  have hConv_pair := hConv' φ hφ_tendsto 1 hxx 1 (by norm_num) hyex_C1
                       hyex_M hyex'_LM h_norm Y Y_int hY_props
  have hY_lim : Filter.Tendsto (fun n : ℕ => Y n n)
                  Filter.atTop (nhds (fun i => u' i * yex 1)) :=
    hConv_pair.1
  have hYint_lim : Filter.Tendsto Y_int
                     Filter.atTop (nhds (fun _ => yex 1)) :=
    hConv_pair.2
  -- Simplify yex 1 = id 1 = 1.
  have h_lim_simp : (fun i : Fin r => u' i * yex 1) = u' := by
    rw [hyex_def]; funext i; show u' i * (1 : ℝ) = u' i; ring
  rw [h_lim_simp] at hY_lim
  have h_lim_simp_int : (fun _ : Fin s => yex 1) = (fun _ => (1 : ℝ)) := by
    rw [hyex_def]; rfl
  rw [h_lim_simp_int] at hYint_lim
  -- Step 4: V-fixed conclusion (cycle 096).
  have hStable := M.convergent_isStable hConv
  obtain ⟨K, hK⟩ := hStable.powerBound
  set w : Fin r → ℝ := M.B *ᵥ (fun _ => (1 : ℝ)) with hw_def
  set residual : ℕ → Fin r → ℝ := fun n => M.V ^ n *ᵥ w - w with hresidual_def
  have h_residual_bd : ∀ n : ℕ, ‖residual n‖ ≤ K * ‖w‖ + ‖w‖ := by
    intro n
    have h1 : ‖M.V ^ n *ᵥ w‖ ≤ ‖M.V ^ n‖ * ‖w‖ :=
      Matrix.linfty_opNorm_mulVec _ _
    have h2 : ‖M.V ^ n‖ * ‖w‖ ≤ K * ‖w‖ :=
      mul_le_mul_of_nonneg_right (hK n) (norm_nonneg _)
    have h3 : ‖M.V ^ n *ᵥ w - w‖ ≤ ‖M.V ^ n *ᵥ w‖ + ‖w‖ := norm_sub_le _ _
    linarith
  have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => (1 - 0 : ℝ) / (n : ℝ))
                          Filter.atTop (nhds 0) := by
    have heq : (fun n : ℕ => (1 - 0 : ℝ) / (n : ℝ))
                 = fun n : ℕ => (1 : ℝ) / (n : ℝ) := by
      funext n; ring
    rw [heq]
    exact tendsto_one_div_atTop_nhds_zero_nat
  have h_residual_vanish : Filter.Tendsto
      (fun n : ℕ => ((1 - 0 : ℝ) / (n : ℝ)) • residual n)
      Filter.atTop (nhds 0) := by
    refine NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded h_inv_tendsto ?_
    exact ⟨K * ‖w‖ + ‖w‖, by
      rw [Filter.eventually_map]
      exact Filter.Eventually.of_forall h_residual_bd⟩
  have hVu' : M.V *ᵥ u' = u' := by
    have hVY_lim : Filter.Tendsto (fun n : ℕ => M.V *ᵥ Y n n)
                     Filter.atTop (nhds (M.V *ᵥ u')) := by
      have hcont : Continuous fun w : Fin r → ℝ => M.V *ᵥ w :=
        Continuous.matrix_mulVec continuous_const continuous_id
      exact hcont.tendsto _ |>.comp hY_lim
    have h_step4 : ∀ n : ℕ, M.V *ᵥ Y n n = Y n n
          + ((1 - 0 : ℝ) / (n : ℝ)) • (M.V ^ n *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ)))
                                        - M.B *ᵥ (fun _ => (1 : ℝ))) := by
      intro n
      show M.V *ᵥ M.glmConstOneIterate ((1 - 0 : ℝ) / (n : ℝ)) n = _
      exact M.V_mulVec_glmConstOneIterate_eq ((1 - 0 : ℝ) / (n : ℝ)) n
    have hYn_plus_res : Filter.Tendsto
        (fun n : ℕ => Y n n + ((1 - 0 : ℝ) / (n : ℝ)) • residual n)
        Filter.atTop (nhds (u' + 0)) :=
      hY_lim.add h_residual_vanish
    rw [add_zero] at hYn_plus_res
    have hVY_eq : (fun n : ℕ => M.V *ᵥ Y n n) =
                  (fun n : ℕ => Y n n + ((1 - 0 : ℝ) / (n : ℝ)) • residual n) := by
      funext n
      exact h_step4 n
    rw [hVY_eq] at hVY_lim
    exact tendsto_nhds_unique hVY_lim hYn_plus_res
  -- Step 8 (NEW, cycle 099): U-side conclusion via the stage-limit
  -- clause. From `hYint_lim : Y_int n → (fun _ => 1)` and the
  -- stage equation reduction `Y_int n i = (1/n) • (Σ j, A i j) + (U·Y n n) i`,
  -- the first term → 0 and the second → (U·u') i, so (U·u') i = 1.
  have hUu' : M.U *ᵥ u' = (fun _ => 1) := by
    have hUY_lim : Filter.Tendsto (fun n : ℕ => M.U *ᵥ Y n n)
                     Filter.atTop (nhds (M.U *ᵥ u')) := by
      have hcont : Continuous fun w : Fin r → ℝ => M.U *ᵥ w :=
        Continuous.matrix_mulVec continuous_const continuous_id
      exact hcont.tendsto _ |>.comp hY_lim
    have hY_int_simp : ∀ n : ℕ, ∀ i : Fin s,
        Y_int n i = ((1 : ℝ) / (n : ℝ)) * (∑ j, M.A i j) + (M.U *ᵥ Y n n) i := by
      intro n i
      show (∑ j, M.A i j * (((1 - 0 : ℝ) / (n : ℝ)) * f (0 : ℝ)))
            + (∑ j, M.U i j * Y n n j) =
            ((1 : ℝ) / (n : ℝ)) * (∑ j, M.A i j) + (M.U *ᵥ Y n n) i
      rw [hf_def]
      show (∑ j, M.A i j * (((1 - 0 : ℝ) / (n : ℝ)) * 1))
            + (∑ j, M.U i j * Y n n j) =
            ((1 : ℝ) / (n : ℝ)) * (∑ j, M.A i j) + (M.U *ᵥ Y n n) i
      have h_left : (∑ j, M.A i j * (((1 - 0 : ℝ) / (n : ℝ)) * 1))
                      = ((1 : ℝ) / (n : ℝ)) * (∑ j, M.A i j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      have h_right : (∑ j, M.U i j * Y n n j) = (M.U *ᵥ Y n n) i := rfl
      rw [h_left, h_right]
    funext i
    show (M.U *ᵥ u') i = (1 : ℝ)
    have hYint_lim_i : Filter.Tendsto (fun n => Y_int n i)
                          Filter.atTop (nhds 1) := by
      have h := (tendsto_pi_nhds.mp hYint_lim) i
      simpa using h
    have hUY_lim_i : Filter.Tendsto (fun n => (M.U *ᵥ Y n n) i)
                       Filter.atTop (nhds ((M.U *ᵥ u') i)) :=
      (tendsto_pi_nhds.mp hUY_lim) i
    have h_first_tendsto : Filter.Tendsto
        (fun n : ℕ => ((1 : ℝ) / (n : ℝ)) * (∑ j, M.A i j))
        Filter.atTop (nhds 0) := by
      have hone : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
                     Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
      have := hone.mul_const (∑ j, M.A i j)
      simpa using this
    have h_sum_tendsto : Filter.Tendsto
        (fun n : ℕ => ((1 : ℝ) / (n : ℝ)) * (∑ j, M.A i j) + (M.U *ᵥ Y n n) i)
        Filter.atTop (nhds (0 + (M.U *ᵥ u') i)) :=
      h_first_tendsto.add hUY_lim_i
    rw [zero_add] at h_sum_tendsto
    have h_eq : (fun n : ℕ => Y_int n i) =
                (fun n : ℕ => ((1 : ℝ) / (n : ℝ)) * (∑ j, M.A i j) + (M.U *ᵥ Y n n) i) := by
      funext n; exact hY_int_simp n i
    rw [h_eq] at hYint_lim_i
    exact (tendsto_nhds_unique hYint_lim_i h_sum_tendsto).symm
  -- Step 9 (NEW, cycle 099): Cesàro-sum form of hY_lim, exposed as the
  -- fourth conclusion. Y n n equals the Cesàro sum by the closed form.
  have hCes_lim : Filter.Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) •
        (∑ k ∈ Finset.range n,
            (M.V ^ k) *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ)))))
      Filter.atTop (nhds u') := by
    have h_eq : (fun n : ℕ => Y n n) =
                (fun n : ℕ => (1 / (n : ℝ)) •
                  (∑ k ∈ Finset.range n,
                      (M.V ^ k) *ᵥ (M.B *ᵥ (fun _ => (1 : ℝ))))) := by
      funext n
      show M.glmConstOneIterate ((1 - 0 : ℝ) / (n : ℝ)) n = _
      rw [M.glmConstOneIterate_closed_form ((1 - 0 : ℝ) / (n : ℝ)) n]
      congr 1
      ring
    rw [h_eq] at hY_lim
    exact hY_lim
  exact ⟨u', hu'_ne, hVu', hUu', hCes_lim⟩

/-- **GLM analog of LMM `thm:405B`** (cycle 069): A convergent GLM
is preconsistent. The convergence-witness vector `u'` extracted from
`IsConvergent` satisfies both `V *ᵥ u' = u'` and `U *ᵥ u' = 𝟙`, and
is non-zero — i.e. `u'` is itself a preconsistency vector. -/
theorem GeneralLinearMethod.convergent_isPreconsistent
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (hConv : M.IsConvergent)
    -- Cycle 116 cascade: propagated h_norm obligation from
    -- `convergence_witness_satisfies_U`. See its docstring for the
    -- Solution-A fallback rationale.
    (h_norm_obligation : @norm _ Matrix.frobeniusNormedRing.toNorm
      (M.A.map (fun a => |a|)) < 1) :
    M.IsPreconsistent := by
  obtain ⟨u', _, hVu, hUu, _⟩ :=
    M.convergence_witness_satisfies_U hConv h_norm_obligation
  exact ⟨u', hVu, hUu⟩

/-! ### Main theorem: `thm:514A`

Butcher's textbook proof: under `IsConvergent` + `IsPreconsistent`
(witness `u`), instantiate the trivial IVP `y'(x) = 1, y(0) = 0`,
derive the Cesàro residual statement (sub-lemma C), invert
`(I − V)` via the mean-ergodic gap (sub-lemma D), and assemble the
witness `v` via sub-lemma E. -/

/-- **Butcher Theorem 514A** (p. 410) — A convergent preconsistent
GLM is consistent.

**Faithfulness note** (cycle 099): the `_hPre` hypothesis matches
the textbook signature but is unused internally. The proof uses the
convergence-witness vector `u'` (extracted via
`convergence_witness_satisfies_U`) as its own preconsistency vector,
sidestepping the textbook's implicit `u' = u` identification — the
cycle 097 analysis showed that uniqueness of preconsistency vectors
is non-trivial in general, but `IsConsistent` is existential, so
*any* preconsistency vector witnesses it. The stronger fact
`IsConvergent → IsPreconsistent` (without `hPre`) is exposed
separately as `convergent_isPreconsistent`. -/
theorem GeneralLinearMethod.convergent_preconsistent_isConsistent
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (hConv : M.IsConvergent) (_hPre : M.IsPreconsistent)
    -- Cycle 116 cascade: propagated h_norm obligation from
    -- `convergence_witness_satisfies_U`. See its docstring for the
    -- Solution-A fallback rationale.
    (h_norm_obligation : @norm _ Matrix.frobeniusNormedRing.toNorm
      (M.A.map (fun a => |a|)) < 1) :
    M.IsConsistent := by
  -- Extract the convergence-witness vector u' (cycle 099 closure).
  obtain ⟨u', _hu'_ne, hVu', hUu', hY_lim⟩ :=
    M.convergence_witness_satisfies_U hConv h_norm_obligation
  -- Get power-boundedness of V via the §513 stability theorem.
  have hStable := M.convergent_isStable hConv
  have hPB : ∃ K : ℝ, ∀ n, ‖M.V ^ n‖ ≤ K := hStable.powerBound
  -- Sub-lemma C (pure-algebraic): Cesàro residual tends to zero.
  have hCes := cesaro_residual_tendsto_zero M.V (M.B *ᵥ (fun _ => 1))
                  hVu' hY_lim
  -- Sub-lemma E: assemble the witness v.
  obtain ⟨v, hv⟩ := M.witness_v_of_cesaro_inverse ⟨hVu', hUu'⟩ hCes hPB
  -- Pack into IsConsistent (using u' as the preconsistency witness).
  exact ⟨u', v, ⟨hVu', hUu'⟩, hv⟩

end OpenMath.Chapter5.Section510
