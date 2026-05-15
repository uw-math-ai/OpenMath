import OpenMath.Chapter3.Section381
import OpenMath.Matrix.MMatrix
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Butcher §319 — Global truncation error (RK), Phase 1

This file ships the two **intermediate inequalities** that underlie
Butcher's `lem:319A` (p. 188, *Numerical Methods for Ordinary
Differential Equations*, 3rd ed.):

> Let `f : ℝ^m → ℝ^m` satisfy a Lipschitz condition with constant
> `L`. Let `y₀, z₀ ∈ ℝ^m` be two input values to a step with the
> RK method `(A, b, c)`, using stepsize `h ≤ h₀` where
> `h₀ L ρ(|A|) < 1`, and let `y₁, z₁` be the corresponding output
> values. Then
>   `‖y₁ − z₁‖ ≤ (1 + h L^†) ‖y₀ − z₀‖`,
> where `L^† = L |b|^T (I − h₀ L |A|)^{−1} 𝟙`.

The textbook proof has two structural steps plus a M-matrix inversion
that produces the constant `L^†`:

1. (D1) **Stage-difference recurrence**:
   `‖Yᵢ − Zᵢ‖ ≤ ‖y₀ − z₀‖ + h L ∑ⱼ |aᵢⱼ| ‖Yⱼ − Zⱼ‖`.
2. (D2) **Output-difference recurrence**:
   `‖y₁ − z₁‖ ≤ ‖y₀ − z₀‖ + h L ∑ᵢ |bᵢ| ‖Yᵢ − Zᵢ‖`.
3. (Phase 2, deferred) Substitute D1 into D2 and invert the
   M-matrix `(I − h L |A|)` (Neumann series, requires
   `Matrix.EntrywiseNonneg` infrastructure currently in
   `OpenMath/Chapter5/MMatrix.lean`).

Cycle 244 ships D1 + D2 + a bundled wrapper against `IsRKOneStep`
witnesses. Phase 2 (the closed-form `L^†` derivation) is deferred to
a future cycle which will either relocate `MMatrix.lean` to a
chapter-neutral module or re-derive the small piece needed inline.

**Faithfulness divergence**: D1/D2 are the *primary structural
content* of Butcher's proof; the headline `(1 + h L^†)` form is
purely arithmetic packaging of D1+D2 once the M-matrix inversion is
available. The `lean_status.json` row therefore moves from
`unformalized` → `partial` (not `formalized`) and the
section-specific divergence note is recorded both in the entity row
and in `plan.md`.
-/

namespace OpenMath.Chapter3.Section319

open OpenMath.Chapter3.Section312 OpenMath.Chapter3.Section381

open scoped NNReal

/-- Helper: bridge `LipschitzWith L.toNNReal f` to the norm-form
inequality `‖f a - f b‖ ≤ L * ‖a - b‖` over a normed real-vector
space. -/
private lemma lipschitz_norm_bound_aux
    {N : Type*} [NormedAddCommGroup N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f) (a b : N) :
    ‖f a - f b‖ ≤ L * ‖a - b‖ := by
  have hd := hf_lip.dist_le_mul a b
  rw [dist_eq_norm, dist_eq_norm] at hd
  have hco : ((Real.toNNReal L : ℝ≥0) : ℝ) = L := Real.coe_toNNReal L hL
  rw [hco] at hd
  exact hd

end OpenMath.Chapter3.Section319

namespace OpenMath.Chapter3.Section312.RKTableau

open OpenMath.Chapter3.Section319
open scoped NNReal

/-- **Deliverable D1** — Stage-difference recurrence for Runge–Kutta.

If `Y, Z : Fin s → N` are the stage tuples of two RK steps with the
same method `M` and stepsize `h`, started from inputs `y₀, z₀ : N`
on a Lipschitz right-hand side `f : N → N`, then each stage
difference is bounded by the input difference plus the row-weighted
sum of stage differences:

  `‖Yᵢ − Zᵢ‖ ≤ ‖y₀ − z₀‖ + h L ∑ⱼ |aᵢⱼ| ‖Yⱼ − Zⱼ‖`.

This is Butcher's intermediate inequality (line 2 of the `lem:319A`
proof).
-/
theorem stage_diff_recurrence {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y₀ z₀ : N} {h : ℝ} (hh : 0 ≤ h)
    {Y Z : Fin s → N}
    (hY_stage : ∀ i, Y i = y₀ + h • ∑ j, M.A i j • f (Y j))
    (hZ_stage : ∀ i, Z i = z₀ + h • ∑ j, M.A i j • f (Z j))
    (i : Fin s) :
    ‖Y i - Z i‖ ≤ ‖y₀ - z₀‖ + h * L * ∑ j, |M.A i j| * ‖Y j - Z j‖ := by
  -- Step 1: subtract stage equations.
  have hdiff : Y i - Z i
      = (y₀ - z₀) + h • ∑ j, M.A i j • (f (Y j) - f (Z j)) := by
    rw [hY_stage i, hZ_stage i]
    simp only [add_sub_add_comm, ← smul_sub, ← Finset.sum_sub_distrib,
               ← smul_sub]
  -- Step 2: triangle inequality on the norm of the sum.
  have htri : ‖Y i - Z i‖
      ≤ ‖y₀ - z₀‖ + ‖h • ∑ j, M.A i j • (f (Y j) - f (Z j))‖ := by
    rw [hdiff]; exact norm_add_le _ _
  -- Step 3: pull `h` (scalar) out via `norm_smul` + `abs_of_nonneg`.
  have hpull : ‖h • ∑ j, M.A i j • (f (Y j) - f (Z j))‖
      = h * ‖∑ j, M.A i j • (f (Y j) - f (Z j))‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  -- Step 4: triangle inequality on the inner sum.
  have hsum_le : ‖∑ j, M.A i j • (f (Y j) - f (Z j))‖
      ≤ ∑ j, ‖M.A i j • (f (Y j) - f (Z j))‖ := norm_sum_le _ _
  -- Step 5: each summand is bounded by `|aᵢⱼ| * (L * ‖Yⱼ - Zⱼ‖)`.
  have hpw : ∀ j ∈ (Finset.univ : Finset (Fin s)),
      ‖M.A i j • (f (Y j) - f (Z j))‖
        ≤ |M.A i j| * (L * ‖Y j - Z j‖) := by
    intro j _
    rw [norm_smul, Real.norm_eq_abs]
    have hLip : ‖f (Y j) - f (Z j)‖ ≤ L * ‖Y j - Z j‖ :=
      lipschitz_norm_bound_aux hL hf_lip (Y j) (Z j)
    exact mul_le_mul_of_nonneg_left hLip (abs_nonneg _)
  have hsum_pw : (∑ j, ‖M.A i j • (f (Y j) - f (Z j))‖)
      ≤ ∑ j, |M.A i j| * (L * ‖Y j - Z j‖) :=
    Finset.sum_le_sum hpw
  -- Step 6: factor `L` out of the bound sum.
  have hfactor : (∑ j, |M.A i j| * (L * ‖Y j - Z j‖))
      = L * ∑ j, |M.A i j| * ‖Y j - Z j‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- Combine.
  have h_inner : ‖∑ j, M.A i j • (f (Y j) - f (Z j))‖
      ≤ L * ∑ j, |M.A i j| * ‖Y j - Z j‖ := by
    calc ‖∑ j, M.A i j • (f (Y j) - f (Z j))‖
        ≤ ∑ j, ‖M.A i j • (f (Y j) - f (Z j))‖ := hsum_le
      _ ≤ ∑ j, |M.A i j| * (L * ‖Y j - Z j‖) := hsum_pw
      _ = L * ∑ j, |M.A i j| * ‖Y j - Z j‖ := hfactor
  have h_h_inner : h * ‖∑ j, M.A i j • (f (Y j) - f (Z j))‖
      ≤ h * (L * ∑ j, |M.A i j| * ‖Y j - Z j‖) :=
    mul_le_mul_of_nonneg_left h_inner hh
  calc ‖Y i - Z i‖
      ≤ ‖y₀ - z₀‖ + ‖h • ∑ j, M.A i j • (f (Y j) - f (Z j))‖ := htri
    _ = ‖y₀ - z₀‖ + h * ‖∑ j, M.A i j • (f (Y j) - f (Z j))‖ := by rw [hpull]
    _ ≤ ‖y₀ - z₀‖ + h * (L * ∑ j, |M.A i j| * ‖Y j - Z j‖) := by linarith
    _ = ‖y₀ - z₀‖ + h * L * ∑ j, |M.A i j| * ‖Y j - Z j‖ := by ring

/-- **Deliverable D2** — Output-difference recurrence for Runge–Kutta.

Given stage tuples `Y, Z` for two RK steps with the same method `M`
and stepsize `h` on a Lipschitz right-hand side, and the
corresponding outputs `y₁, z₁`, the output difference is bounded by:

  `‖y₁ − z₁‖ ≤ ‖y₀ − z₀‖ + h L ∑ᵢ |bᵢ| ‖Yᵢ − Zᵢ‖`.

This is Butcher's intermediate inequality (line 3 of the `lem:319A`
proof). The proof is structurally identical to `stage_diff_recurrence`
with `(M.b i, y₁, z₁)` substituted for `(M.A i j, Y i, Z i)`; the
output formula is *not* implicit, so the proof is genuinely shorter
than D1's.
-/
theorem output_diff_recurrence {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y₀ z₀ y₁ z₁ : N} {h : ℝ} (hh : 0 ≤ h)
    {Y Z : Fin s → N}
    (hY_out : y₁ = y₀ + h • ∑ i, M.b i • f (Y i))
    (hZ_out : z₁ = z₀ + h • ∑ i, M.b i • f (Z i)) :
    ‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * ‖Y i - Z i‖ := by
  -- Step 1: subtract output equations.
  have hdiff : y₁ - z₁
      = (y₀ - z₀) + h • ∑ i, M.b i • (f (Y i) - f (Z i)) := by
    rw [hY_out, hZ_out]
    simp only [add_sub_add_comm, ← smul_sub, ← Finset.sum_sub_distrib,
               ← smul_sub]
  -- Step 2: triangle inequality.
  have htri : ‖y₁ - z₁‖
      ≤ ‖y₀ - z₀‖ + ‖h • ∑ i, M.b i • (f (Y i) - f (Z i))‖ := by
    rw [hdiff]; exact norm_add_le _ _
  -- Step 3: pull `h` out.
  have hpull : ‖h • ∑ i, M.b i • (f (Y i) - f (Z i))‖
      = h * ‖∑ i, M.b i • (f (Y i) - f (Z i))‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  -- Step 4: triangle inequality on inner sum.
  have hsum_le : ‖∑ i, M.b i • (f (Y i) - f (Z i))‖
      ≤ ∑ i, ‖M.b i • (f (Y i) - f (Z i))‖ := norm_sum_le _ _
  -- Step 5: per-summand Lipschitz bound.
  have hpw : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      ‖M.b i • (f (Y i) - f (Z i))‖
        ≤ |M.b i| * (L * ‖Y i - Z i‖) := by
    intro i _
    rw [norm_smul, Real.norm_eq_abs]
    have hLip : ‖f (Y i) - f (Z i)‖ ≤ L * ‖Y i - Z i‖ :=
      lipschitz_norm_bound_aux hL hf_lip (Y i) (Z i)
    exact mul_le_mul_of_nonneg_left hLip (abs_nonneg _)
  have hsum_pw : (∑ i, ‖M.b i • (f (Y i) - f (Z i))‖)
      ≤ ∑ i, |M.b i| * (L * ‖Y i - Z i‖) :=
    Finset.sum_le_sum hpw
  -- Step 6: factor `L` out.
  have hfactor : (∑ i, |M.b i| * (L * ‖Y i - Z i‖))
      = L * ∑ i, |M.b i| * ‖Y i - Z i‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h_inner : ‖∑ i, M.b i • (f (Y i) - f (Z i))‖
      ≤ L * ∑ i, |M.b i| * ‖Y i - Z i‖ := by
    calc ‖∑ i, M.b i • (f (Y i) - f (Z i))‖
        ≤ ∑ i, ‖M.b i • (f (Y i) - f (Z i))‖ := hsum_le
      _ ≤ ∑ i, |M.b i| * (L * ‖Y i - Z i‖) := hsum_pw
      _ = L * ∑ i, |M.b i| * ‖Y i - Z i‖ := hfactor
  have h_h_inner : h * ‖∑ i, M.b i • (f (Y i) - f (Z i))‖
      ≤ h * (L * ∑ i, |M.b i| * ‖Y i - Z i‖) :=
    mul_le_mul_of_nonneg_left h_inner hh
  calc ‖y₁ - z₁‖
      ≤ ‖y₀ - z₀‖ + ‖h • ∑ i, M.b i • (f (Y i) - f (Z i))‖ := htri
    _ = ‖y₀ - z₀‖ + h * ‖∑ i, M.b i • (f (Y i) - f (Z i))‖ := by rw [hpull]
    _ ≤ ‖y₀ - z₀‖ + h * (L * ∑ i, |M.b i| * ‖Y i - Z i‖) := by linarith
    _ = ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * ‖Y i - Z i‖ := by ring

/-- **Deliverable D3** — Bundled `lem:319A` Phase 1 packaging.

Given `IsRKOneStep` witnesses for two RK runs of the same method `M`
on the same Lipschitz right-hand side `f`, the two stage tuples
extracted from the witnesses satisfy the stage-difference recurrence
(D1) universally and the output-difference recurrence (D2). The
packaging is existential so that the stage tuples (which are part of
the `IsRKOneStep` data) are exposed for downstream consumers to
iterate or specialise.

**Phase 2 (deferred)**: combining D1+D2 with the M-matrix inversion
`(I − h L |A|)⁻¹` yields the headline
`‖y₁ − z₁‖ ≤ (1 + h L^†) ‖y₀ − z₀‖` bound. The inversion machinery
currently lives in `OpenMath/Chapter5/MMatrix.lean` (Chapter 3
cannot import Chapter 5), so the closed-form derivation is split off.
-/
theorem lem_319A_recurrences {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y₀ z₀ y₁ z₁ : N} {h : ℝ} (hh : 0 ≤ h)
    (h_y : M.IsRKOneStep f y₀ h y₁) (h_z : M.IsRKOneStep f z₀ h z₁) :
    ∃ Y Z : Fin s → N,
      (∀ i, ‖Y i - Z i‖
        ≤ ‖y₀ - z₀‖ + h * L * ∑ j, |M.A i j| * ‖Y j - Z j‖)
      ∧ ‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * ‖Y i - Z i‖ := by
  obtain ⟨Y, hY_stage, hY_out⟩ := h_y
  obtain ⟨Z, hZ_stage, hZ_out⟩ := h_z
  refine ⟨Y, Z, ?_, ?_⟩
  · intro i
    exact M.stage_diff_recurrence hL hf_lip hh hY_stage hZ_stage i
  · exact M.output_diff_recurrence hL hf_lip hh hY_out hZ_out

section Phase2

open scoped Matrix Matrix.Norms.Frobenius

/-- **Butcher §319 `lem:319A`** — global one-step truncation contraction.

For a Lipschitz right-hand side `f` with constant `L ≥ 0` and stepsize
`h ≤ h₀` satisfying the M-matrix smallness condition
`‖(h₀ * L) • |A|‖_F < 1`, the difference of two one-step Runge–Kutta
outputs starting from different inputs contracts as
`‖y₁ − z₁‖ ≤ (1 + h L^†) ‖y₀ − z₀‖`, where the textbook constant
`L^† = L |b|^T (I − h₀ L |A|)^{−1} 𝟙` is exposed existentially as
`L_dag` (the closed form is the witness built in the proof).

Composes cycle 244's stage/output recurrences (D1, D2) with cycle
106's M-matrix inverse-positivity (`Matrix.EntrywiseNonneg`).

**Faithfulness divergence**: the textbook smallness condition is
`h₀ L ρ(|A|) < 1` (spectral-radius form). The Lean hypothesis uses the
Frobenius operator norm of `(h₀ * L) • |A|` instead, which dominates
the spectral radius, so the Lean hypothesis is **strictly stronger**
than the textbook's. This matches the cycle 106/107 M-matrix
machinery's built-in hypothesis shape. -/
theorem lem_319A {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y₀ z₀ : N} {h h₀ : ℝ} (hh : 0 < h) (hh_le : h ≤ h₀) (hh₀ : 0 ≤ h₀)
    (h_norm : ‖((h₀ * L) • M.A.map (fun a => |a|))‖ < 1) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ∀ y₁ z₁,
        M.IsRKOneStep f y₀ h y₁ → M.IsRKOneStep f z₀ h z₁ →
        ‖y₁ - z₁‖ ≤ (1 + h * L_dag) * ‖y₀ - z₀‖ := by
  -- Step A: K = (h₀ * L) • |A|, entrywise non-negative with ‖K‖ < 1.
  set K : Matrix (Fin s) (Fin s) ℝ :=
    (h₀ * L) • M.A.map (fun a => |a|) with hK_def
  have hK_nn : K.EntrywiseNonneg := by
    have habs_nn : (M.A.map (fun a => |a|)).EntrywiseNonneg := by
      intro i j
      simp only [Matrix.map_apply]
      exact abs_nonneg _
    exact habs_nn.smul (mul_nonneg hh₀ hL)
  -- Step B: extract w := (I − K)⁻¹ 𝟙 and prove componentwise non-negativity.
  set w : Fin s → ℝ :=
    (Ring.inverse ((1 : Matrix (Fin s) (Fin s) ℝ) - K)) *ᵥ (fun _ => 1)
    with hw_def
  have h_inv_nn :
      (Ring.inverse ((1 : Matrix (Fin s) (Fin s) ℝ) - K)).EntrywiseNonneg :=
    hK_nn.inv_one_sub_of_norm_lt_one h_norm
  have hw_nn : ∀ i, 0 ≤ w i := by
    intro i
    exact h_inv_nn.mulVec_nonneg (fun _ => zero_le_one) i
  -- Step C: L^† = L * ∑ᵢ |bᵢ| * wᵢ, nonneg.
  set L_dag : ℝ := L * ∑ i, |M.b i| * w i with hL_dag_def
  have hL_dag_nn : 0 ≤ L_dag := by
    refine mul_nonneg hL ?_
    refine Finset.sum_nonneg (fun i _ => ?_)
    exact mul_nonneg (abs_nonneg _) (hw_nn i)
  -- Step D: (I − K) *ᵥ w = 𝟙.
  have h_unit : IsUnit ((1 : Matrix (Fin s) (Fin s) ℝ) - K) :=
    isUnit_one_sub_of_norm_lt_one h_norm
  have h_mul_inv :
      ((1 : Matrix (Fin s) (Fin s) ℝ) - K)
        * Ring.inverse (1 - K) = 1 :=
    Ring.mul_inverse_cancel _ h_unit
  have h_oneMK_mulVec_w :
      ((1 : Matrix (Fin s) (Fin s) ℝ) - K) *ᵥ w
        = (fun _ : Fin s => (1 : ℝ)) := by
    rw [hw_def, Matrix.mulVec_mulVec, h_mul_inv, Matrix.one_mulVec]
  -- Step E: open the universal.
  refine ⟨L_dag, hL_dag_nn, ?_⟩
  intro y₁ z₁ hY hZ
  obtain ⟨Y, hY_stage, hY_out⟩ := hY
  obtain ⟨Z, hZ_stage, hZ_out⟩ := hZ
  set vM : Fin s → ℝ := fun i => ‖Y i - Z i‖ with hvM_def
  have hvM_nn : ∀ i, 0 ≤ vM i := fun i => norm_nonneg _
  -- Step F: stage recurrence (cycle 244 D1).
  have h_stage_bound : ∀ i,
      vM i ≤ ‖y₀ - z₀‖ + h * L * ∑ j, |M.A i j| * vM j := by
    intro i
    exact M.stage_diff_recurrence hL hf_lip hh.le hY_stage hZ_stage i
  -- Step G: output recurrence (cycle 244 D2).
  have h_out_bound :
      ‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * vM i :=
    M.output_diff_recurrence hL hf_lip hh.le hY_out hZ_out
  -- Step H: (K *ᵥ vM) i = (h₀ * L) * ∑ⱼ |Aᵢⱼ| * vM j.
  have h_K_mulVec : ∀ i,
      (K *ᵥ vM) i = (h₀ * L) * ∑ j, |M.A i j| * vM j := by
    intro i
    rw [hK_def, Matrix.smul_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
  -- Step I: ((I − K) *ᵥ vM) i ≤ ‖y₀ − z₀‖.
  have h_oneMK_mulVec_vM : ∀ i,
      (((1 : Matrix (Fin s) (Fin s) ℝ) - K) *ᵥ vM) i
        = vM i - (K *ᵥ vM) i := by
    intro i
    rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec]
  have h_inner_sum_nn : ∀ i, 0 ≤ ∑ j, |M.A i j| * vM j := by
    intro i
    refine Finset.sum_nonneg (fun j _ => ?_)
    exact mul_nonneg (abs_nonneg _) (hvM_nn j)
  have h_hL_le : h * L ≤ h₀ * L :=
    mul_le_mul_of_nonneg_right hh_le hL
  have h_vM_oneMK_bound : ∀ i,
      (((1 : Matrix (Fin s) (Fin s) ℝ) - K) *ᵥ vM) i ≤ ‖y₀ - z₀‖ := by
    intro i
    rw [h_oneMK_mulVec_vM i, h_K_mulVec i]
    have h_step : h * L * ∑ j, |M.A i j| * vM j
        ≤ (h₀ * L) * ∑ j, |M.A i j| * vM j :=
      mul_le_mul_of_nonneg_right h_hL_le (h_inner_sum_nn i)
    have h_recur := h_stage_bound i
    linarith
  -- Step J: comparison principle ⇒ vM i ≤ ‖y₀ − z₀‖ * w i.
  have h_vM_le : ∀ i, vM i ≤ ‖y₀ - z₀‖ * w i := by
    set v' : Fin s → ℝ := fun i => ‖y₀ - z₀‖ * w i - vM i with hv'_def
    have h_v'_lin : v' = ‖y₀ - z₀‖ • w - vM := by
      funext j
      simp [hv'_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have h_v'_nn : ∀ i, 0 ≤ v' i := by
      apply hK_nn.nonneg_of_one_sub_mulVec_nonneg h_norm
      intro i
      rw [h_v'_lin, Matrix.mulVec_sub, Matrix.mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [h_oneMK_mulVec_w]
      have h_norm_nn : 0 ≤ ‖y₀ - z₀‖ := norm_nonneg _
      have hbound := h_vM_oneMK_bound i
      linarith
    intro i
    have := h_v'_nn i
    simp only [hv'_def] at this
    linarith
  -- Step K: substitute into the output recurrence.
  have h_out_sub : ∑ i, |M.b i| * vM i
      ≤ ∑ i, |M.b i| * (‖y₀ - z₀‖ * w i) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact mul_le_mul_of_nonneg_left (h_vM_le i) (abs_nonneg _)
  have h_hL_nn : 0 ≤ h * L := mul_nonneg hh.le hL
  have h_sum_eq : ∑ i, |M.b i| * (‖y₀ - z₀‖ * w i)
      = ‖y₀ - z₀‖ * ∑ i, |M.b i| * w i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  calc ‖y₁ - z₁‖
      ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * vM i := h_out_bound
    _ ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * (‖y₀ - z₀‖ * w i) := by
        have := mul_le_mul_of_nonneg_left h_out_sub h_hL_nn
        linarith
    _ = ‖y₀ - z₀‖ + h * L * (‖y₀ - z₀‖ * ∑ i, |M.b i| * w i) := by
        rw [h_sum_eq]
    _ = ‖y₀ - z₀‖ + h * L_dag * ‖y₀ - z₀‖ := by rw [hL_dag_def]; ring
    _ = (1 + h * L_dag) * ‖y₀ - z₀‖ := by ring

end Phase2

section Phase3

open scoped Matrix Matrix.Norms.Frobenius

/-- **Iterated trajectory predicate** — `M.IsRKTrajectory f h traj` says
that `traj : Fin (n + 1) → N` is a sequence of `n + 1` nodes such that
between consecutive nodes the method `M` performs a single RK step of
size `h` on the autonomous ODE `y' = f(y)`.

This is an encoding of Butcher's `(y_k)_{k = 0}^{n}` numerical-trajectory
sequence; the concept is not itself a named textbook definition. -/
def IsRKTrajectory {s : ℕ} (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (h : ℝ) {n : ℕ} (traj : Fin (n + 1) → N) : Prop :=
  ∀ k : Fin n,
    M.IsRKOneStep f (traj k.castSucc) h (traj k.succ)

/-- **Local truncation error bound predicate** — Butcher's Figure
319(ii) framework. `M.HasLocalTruncationErrorBound f h yex δ` says that
for each step `k`, there exists an intermediate value `y_step` produced
by running `M` on the exact solution sample `yex k.castSucc`, and the
deviation `‖yex k.succ − y_step‖` is bounded by `δ k`.

**Faithfulness divergence**: the textbook defines `δ_k` as an
*equality* `δ_k = ‖y(x_k) − ŷ_k‖`. We use an *inequality* `‖…‖ ≤ δ k`
because what propagates through the accumulation recurrence is the
bound on `δ_k`, not its exact value. -/
def HasLocalTruncationErrorBound {s : ℕ} (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (h : ℝ) {n : ℕ} (yex : Fin (n + 1) → N)
    (δ : Fin n → ℝ) : Prop :=
  ∀ k : Fin n, ∃ y_step : N,
    M.IsRKOneStep f (yex k.castSucc) h y_step ∧
    ‖yex k.succ - y_step‖ ≤ δ k

/-- **Helper** — universal `(y₀, z₀)` version of `lem_319A`. The
extraction of `L_dag` from the M-matrix machinery depends only on
`(M, L, h, h₀)`; the actual contraction conclusion is universal in
`(y₀, z₀, y₁, z₁)`. This re-statement is essential for accumulation
arguments where `(y₀, z₀)` varies step by step.

Body is structurally identical to `lem_319A` (cycle 245). The only
difference is the position of the `(y₀, z₀)` quantifier (here inside
the existential's conclusion; in `lem_319A` it is in the outer signature
as implicit binders). -/
private theorem lem_319A_extract {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {h h₀ : ℝ} (hh : 0 < h) (hh_le : h ≤ h₀) (hh₀ : 0 ≤ h₀)
    (h_norm : ‖((h₀ * L) • M.A.map (fun a => |a|))‖ < 1) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ∀ y₀ z₀ y₁ z₁,
        M.IsRKOneStep f y₀ h y₁ → M.IsRKOneStep f z₀ h z₁ →
        ‖y₁ - z₁‖ ≤ (1 + h * L_dag) * ‖y₀ - z₀‖ := by
  set K : Matrix (Fin s) (Fin s) ℝ :=
    (h₀ * L) • M.A.map (fun a => |a|) with hK_def
  have hK_nn : K.EntrywiseNonneg := by
    have habs_nn : (M.A.map (fun a => |a|)).EntrywiseNonneg := by
      intro i j
      simp only [Matrix.map_apply]
      exact abs_nonneg _
    exact habs_nn.smul (mul_nonneg hh₀ hL)
  set w : Fin s → ℝ :=
    (Ring.inverse ((1 : Matrix (Fin s) (Fin s) ℝ) - K)) *ᵥ (fun _ => 1)
    with hw_def
  have h_inv_nn :
      (Ring.inverse ((1 : Matrix (Fin s) (Fin s) ℝ) - K)).EntrywiseNonneg :=
    hK_nn.inv_one_sub_of_norm_lt_one h_norm
  have hw_nn : ∀ i, 0 ≤ w i := by
    intro i
    exact h_inv_nn.mulVec_nonneg (fun _ => zero_le_one) i
  set L_dag : ℝ := L * ∑ i, |M.b i| * w i with hL_dag_def
  have hL_dag_nn : 0 ≤ L_dag := by
    refine mul_nonneg hL ?_
    refine Finset.sum_nonneg (fun i _ => ?_)
    exact mul_nonneg (abs_nonneg _) (hw_nn i)
  have h_unit : IsUnit ((1 : Matrix (Fin s) (Fin s) ℝ) - K) :=
    isUnit_one_sub_of_norm_lt_one h_norm
  have h_mul_inv :
      ((1 : Matrix (Fin s) (Fin s) ℝ) - K)
        * Ring.inverse (1 - K) = 1 :=
    Ring.mul_inverse_cancel _ h_unit
  have h_oneMK_mulVec_w :
      ((1 : Matrix (Fin s) (Fin s) ℝ) - K) *ᵥ w
        = (fun _ : Fin s => (1 : ℝ)) := by
    rw [hw_def, Matrix.mulVec_mulVec, h_mul_inv, Matrix.one_mulVec]
  refine ⟨L_dag, hL_dag_nn, ?_⟩
  intro y₀ z₀ y₁ z₁ hY hZ
  obtain ⟨Y, hY_stage, hY_out⟩ := hY
  obtain ⟨Z, hZ_stage, hZ_out⟩ := hZ
  set vM : Fin s → ℝ := fun i => ‖Y i - Z i‖ with hvM_def
  have hvM_nn : ∀ i, 0 ≤ vM i := fun i => norm_nonneg _
  have h_stage_bound : ∀ i,
      vM i ≤ ‖y₀ - z₀‖ + h * L * ∑ j, |M.A i j| * vM j := by
    intro i
    exact M.stage_diff_recurrence hL hf_lip hh.le hY_stage hZ_stage i
  have h_out_bound :
      ‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * vM i :=
    M.output_diff_recurrence hL hf_lip hh.le hY_out hZ_out
  have h_K_mulVec : ∀ i,
      (K *ᵥ vM) i = (h₀ * L) * ∑ j, |M.A i j| * vM j := by
    intro i
    rw [hK_def, Matrix.smul_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
  have h_oneMK_mulVec_vM : ∀ i,
      (((1 : Matrix (Fin s) (Fin s) ℝ) - K) *ᵥ vM) i
        = vM i - (K *ᵥ vM) i := by
    intro i
    rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec]
  have h_inner_sum_nn : ∀ i, 0 ≤ ∑ j, |M.A i j| * vM j := by
    intro i
    refine Finset.sum_nonneg (fun j _ => ?_)
    exact mul_nonneg (abs_nonneg _) (hvM_nn j)
  have h_hL_le : h * L ≤ h₀ * L :=
    mul_le_mul_of_nonneg_right hh_le hL
  have h_vM_oneMK_bound : ∀ i,
      (((1 : Matrix (Fin s) (Fin s) ℝ) - K) *ᵥ vM) i ≤ ‖y₀ - z₀‖ := by
    intro i
    rw [h_oneMK_mulVec_vM i, h_K_mulVec i]
    have h_step : h * L * ∑ j, |M.A i j| * vM j
        ≤ (h₀ * L) * ∑ j, |M.A i j| * vM j :=
      mul_le_mul_of_nonneg_right h_hL_le (h_inner_sum_nn i)
    have h_recur := h_stage_bound i
    linarith
  have h_vM_le : ∀ i, vM i ≤ ‖y₀ - z₀‖ * w i := by
    set v' : Fin s → ℝ := fun i => ‖y₀ - z₀‖ * w i - vM i with hv'_def
    have h_v'_lin : v' = ‖y₀ - z₀‖ • w - vM := by
      funext j
      simp [hv'_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have h_v'_nn : ∀ i, 0 ≤ v' i := by
      apply hK_nn.nonneg_of_one_sub_mulVec_nonneg h_norm
      intro i
      rw [h_v'_lin, Matrix.mulVec_sub, Matrix.mulVec_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [h_oneMK_mulVec_w]
      have h_norm_nn : 0 ≤ ‖y₀ - z₀‖ := norm_nonneg _
      have hbound := h_vM_oneMK_bound i
      linarith
    intro i
    have := h_v'_nn i
    simp only [hv'_def] at this
    linarith
  have h_out_sub : ∑ i, |M.b i| * vM i
      ≤ ∑ i, |M.b i| * (‖y₀ - z₀‖ * w i) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact mul_le_mul_of_nonneg_left (h_vM_le i) (abs_nonneg _)
  have h_hL_nn : 0 ≤ h * L := mul_nonneg hh.le hL
  have h_sum_eq : ∑ i, |M.b i| * (‖y₀ - z₀‖ * w i)
      = ‖y₀ - z₀‖ * ∑ i, |M.b i| * w i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  calc ‖y₁ - z₁‖
      ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * vM i := h_out_bound
    _ ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * (‖y₀ - z₀‖ * w i) := by
        have := mul_le_mul_of_nonneg_left h_out_sub h_hL_nn
        linarith
    _ = ‖y₀ - z₀‖ + h * L * (‖y₀ - z₀‖ * ∑ i, |M.b i| * w i) := by
        rw [h_sum_eq]
    _ = ‖y₀ - z₀‖ + h * L_dag * ‖y₀ - z₀‖ := by rw [hL_dag_def]; ring
    _ = (1 + h * L_dag) * ‖y₀ - z₀‖ := by ring

/-- **Deliverable D3 — `thm:319B` Phase 1: accumulation recurrence.**

For an iterated RK trajectory `traj` and a hypothetical exact-solution
sequence `yex` with per-step local truncation errors bounded by
`δ : Fin n → ℝ`, the global error at the final node is bounded by the
contraction-amplified initial error plus a weighted sum of local errors:

  `‖yex_n − traj_n‖ ≤ (1 + h L^†)^n · ‖yex_0 − traj_0‖`
    `+ ∑_{k=0}^{n-1} (1 + h L^†)^{n-1-k} · δ_k`.

This is Butcher's intermediate inequality
`y(xn) − yn ≤ C h^{p+1} ∑_{k=1}^{n} (1 + h L^†)^k` (§319 p. 190) in a
generalised form that does *not* pre-specialise `δ_k = C h^{p+1}`.
Phase 2 (cycle 247) will specialise and bound the geometric sum.

**Faithfulness divergence (smallness)**: inherited from cycle 245's
`lem_319A` — Frobenius operator norm `‖(h₀ L) • |A|‖_F < 1` instead of
spectral-radius `h₀ L ρ(|A|) < 1`. -/
theorem accumulation_recurrence {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {h h₀ : ℝ} (hh : 0 < h) (hh_le : h ≤ h₀) (hh₀ : 0 ≤ h₀)
    (h_norm : ‖((h₀ * L) • M.A.map (fun a => |a|))‖ < 1) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ∀ {n : ℕ} (traj yex : Fin (n + 1) → N),
        M.IsRKTrajectory f h traj →
        ∀ (δ : Fin n → ℝ),
          M.HasLocalTruncationErrorBound f h yex δ →
          ‖yex (Fin.last n) - traj (Fin.last n)‖
            ≤ (1 + h * L_dag) ^ n * ‖yex 0 - traj 0‖
              + ∑ k : Fin n, (1 + h * L_dag) ^ (n - 1 - k.val) * δ k := by
  obtain ⟨L_dag, hL_dag_nn, h_contract⟩ :=
    M.lem_319A_extract hL hf_lip hh hh_le hh₀ h_norm
  refine ⟨L_dag, hL_dag_nn, ?_⟩
  have hC_nn : 0 ≤ 1 + h * L_dag :=
    add_nonneg zero_le_one (mul_nonneg hh.le hL_dag_nn)
  intro n
  induction n with
  | zero =>
    intro traj yex _ δ _
    simp [Fin.last]
  | succ m ih =>
    intro traj yex h_traj δ h_lte
    -- Restrict the trajectory/yex/δ to the prefix Fin (m+1).
    set traj' : Fin (m + 1) → N := fun k => traj k.castSucc with htraj'_def
    set yex' : Fin (m + 1) → N := fun k => yex k.castSucc with hyex'_def
    set δ' : Fin m → ℝ := fun k => δ k.castSucc with hδ'_def
    have h_traj' : M.IsRKTrajectory f h traj' := by
      intro k
      have hk : M.IsRKOneStep f (traj k.castSucc.castSucc) h
                  (traj k.castSucc.succ) := h_traj k.castSucc
      have h_eq : k.castSucc.succ = k.succ.castSucc := Fin.succ_castSucc k
      rw [h_eq] at hk
      simpa [htraj'_def] using hk
    have h_lte' : M.HasLocalTruncationErrorBound f h yex' δ' := by
      intro k
      obtain ⟨y_step, hstep, hdiff⟩ := h_lte k.castSucc
      have h_eq : k.castSucc.succ = k.succ.castSucc := Fin.succ_castSucc k
      rw [h_eq] at hdiff
      refine ⟨y_step, ?_, ?_⟩
      · simpa [hyex'_def] using hstep
      · simpa [hyex'_def, hδ'_def] using hdiff
    have ih_app := ih traj' yex' h_traj' δ' h_lte'
    -- Apply ih: now we have a bound on ‖yex' (Fin.last m) - traj' (Fin.last m)‖.
    -- yex' (Fin.last m) = yex (Fin.last m).castSucc.
    -- yex' 0 = yex 0 (castSucc 0 = 0 in Fin (m+2)).
    -- The "last step" goes from index Fin.castSucc (Fin.last m) to
    -- Fin.last (m+1).
    -- Step S3: invoke contraction at the last step.
    obtain ⟨y_step, h_step, h_diff⟩ := h_lte (Fin.last m)
    have h_traj_last : M.IsRKOneStep f (traj (Fin.last m).castSucc) h
        (traj (Fin.last m).succ) := h_traj (Fin.last m)
    have h_traj_last' : M.IsRKOneStep f (traj (Fin.last m).castSucc) h
        (traj (Fin.last (m + 1))) := by
      have : (Fin.last m).succ = Fin.last (m + 1) := Fin.succ_last m
      rw [this] at h_traj_last
      exact h_traj_last
    -- Contraction step: ‖y_step − traj (Fin.last (m+1))‖
    --                  ≤ (1 + h L_dag) ‖yex (...) − traj (...)‖.
    have h_step_contract :
        ‖y_step - traj (Fin.last (m + 1))‖
          ≤ (1 + h * L_dag)
              * ‖yex (Fin.last m).castSucc - traj (Fin.last m).castSucc‖ :=
      h_contract _ _ _ _ h_step h_traj_last'
    -- Triangle inequality.
    have h_diff_last : ‖yex (Fin.last (m + 1)) - y_step‖ ≤ δ (Fin.last m) := by
      have : (Fin.last m).succ = Fin.last (m + 1) := Fin.succ_last m
      rw [this] at h_diff
      exact h_diff
    have h_tri :
        ‖yex (Fin.last (m + 1)) - traj (Fin.last (m + 1))‖
          ≤ ‖yex (Fin.last (m + 1)) - y_step‖
            + ‖y_step - traj (Fin.last (m + 1))‖ := by
      have hsub :
          yex (Fin.last (m + 1)) - traj (Fin.last (m + 1))
            = (yex (Fin.last (m + 1)) - y_step)
                + (y_step - traj (Fin.last (m + 1))) := by abel
      rw [hsub]
      exact norm_add_le _ _
    -- IH bound expression.
    -- yex' (Fin.last m) = yex (Fin.last m).castSucc by definition,
    -- and yex' 0 = yex 0.castSucc = yex 0 since (0 : Fin (m+1)).castSucc = (0 : Fin (m+2)).
    have h_yex'_last : yex' (Fin.last m) = yex (Fin.last m).castSucc := by
      simp [hyex'_def]
    have h_traj'_last : traj' (Fin.last m) = traj (Fin.last m).castSucc := by
      simp [htraj'_def]
    have h_yex'_zero : yex' 0 = yex 0 := by
      simp [hyex'_def]
    have h_traj'_zero : traj' 0 = traj 0 := by
      simp [htraj'_def]
    rw [h_yex'_last, h_traj'_last, h_yex'_zero, h_traj'_zero] at ih_app
    -- Multiply ih by (1 + h * L_dag) ≥ 0.
    have ih_amplified :
        (1 + h * L_dag)
          * ‖yex (Fin.last m).castSucc - traj (Fin.last m).castSucc‖
          ≤ (1 + h * L_dag)
              * ((1 + h * L_dag) ^ m * ‖yex 0 - traj 0‖
                  + ∑ k : Fin m, (1 + h * L_dag) ^ (m - 1 - k.val) * δ' k) :=
      mul_le_mul_of_nonneg_left ih_app hC_nn
    -- Combine.
    have h_combine :
        ‖yex (Fin.last (m + 1)) - traj (Fin.last (m + 1))‖
          ≤ δ (Fin.last m)
            + (1 + h * L_dag)
                * ((1 + h * L_dag) ^ m * ‖yex 0 - traj 0‖
                    + ∑ k : Fin m, (1 + h * L_dag) ^ (m - 1 - k.val) * δ' k) := by
      calc ‖yex (Fin.last (m + 1)) - traj (Fin.last (m + 1))‖
          ≤ ‖yex (Fin.last (m + 1)) - y_step‖
              + ‖y_step - traj (Fin.last (m + 1))‖ := h_tri
        _ ≤ δ (Fin.last m)
              + (1 + h * L_dag)
                  * ‖yex (Fin.last m).castSucc - traj (Fin.last m).castSucc‖ := by
            exact add_le_add h_diff_last h_step_contract
        _ ≤ δ (Fin.last m)
              + (1 + h * L_dag)
                  * ((1 + h * L_dag) ^ m * ‖yex 0 - traj 0‖
                      + ∑ k : Fin m, (1 + h * L_dag) ^ (m - 1 - k.val) * δ' k) := by
            linarith [ih_amplified]
    -- Now the RHS of the goal at n = m+1.
    -- Distribute the (1 + h * L_dag) factor.
    have h_dist :
        (1 + h * L_dag)
            * ((1 + h * L_dag) ^ m * ‖yex 0 - traj 0‖
                + ∑ k : Fin m, (1 + h * L_dag) ^ (m - 1 - k.val) * δ' k)
        = (1 + h * L_dag) ^ (m + 1) * ‖yex 0 - traj 0‖
          + ∑ k : Fin m, (1 + h * L_dag) ^ (m - k.val) * δ' k := by
      rw [mul_add, Finset.mul_sum]
      have h_pow : (1 + h * L_dag) * (1 + h * L_dag) ^ m
          = (1 + h * L_dag) ^ (m + 1) := (pow_succ' _ _).symm
      have h_sum :
          (∑ k : Fin m, (1 + h * L_dag)
              * ((1 + h * L_dag) ^ (m - 1 - k.val) * δ' k))
            = ∑ k : Fin m, (1 + h * L_dag) ^ (m - k.val) * δ' k := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have hk : k.val < m := k.isLt
        have h_exp : (1 + h * L_dag) * (1 + h * L_dag) ^ (m - 1 - k.val)
            = (1 + h * L_dag) ^ (m - k.val) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [← mul_assoc, h_exp]
      rw [← mul_assoc, h_pow, h_sum]
    -- Now the goal's RHS for n = m+1:
    -- (1 + h L_dag)^(m+1) * ‖yex 0 - traj 0‖
    --   + ∑ k : Fin (m+1), (1 + h L_dag)^(m+1 - 1 - k.val) * δ k
    -- = (1 + h L_dag)^(m+1) * ‖yex 0 - traj 0‖
    --   + ∑ k : Fin (m+1), (1 + h L_dag)^(m - k.val) * δ k
    -- Split by Fin.sum_univ_castSucc:
    --   ∑ k : Fin (m+1), (1 + h L_dag)^(m - k.val) * δ k
    --   = ∑ k : Fin m, (1 + h L_dag)^(m - k.castSucc.val) * δ k.castSucc
    --     + (1 + h L_dag)^(m - m) * δ (Fin.last m)
    -- The last term = 1 * δ (Fin.last m) = δ (Fin.last m).
    have h_sum_split :
        (∑ k : Fin (m + 1), (1 + h * L_dag) ^ (m + 1 - 1 - k.val) * δ k)
          = (∑ k : Fin m, (1 + h * L_dag) ^ (m - k.val) * δ' k)
              + δ (Fin.last m) := by
      have h_lhs :
          (∑ k : Fin (m + 1), (1 + h * L_dag) ^ (m + 1 - 1 - k.val) * δ k)
            = ∑ k : Fin (m + 1), (1 + h * L_dag) ^ (m - k.val) * δ k := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rfl
      rw [h_lhs, Fin.sum_univ_castSucc]
      have h_last :
          (1 + h * L_dag) ^ (m - (Fin.last m).val) * δ (Fin.last m)
            = δ (Fin.last m) := by
        simp [Fin.val_last]
      have h_sum_eq :
          (∑ k : Fin m,
            (1 + h * L_dag) ^ (m - k.castSucc.val) * δ k.castSucc)
            = ∑ k : Fin m, (1 + h * L_dag) ^ (m - k.val) * δ' k := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp [hδ'_def]
      rw [h_last, h_sum_eq]
    -- Final combine.
    rw [h_sum_split]
    linarith [h_combine, h_dist]

end Phase3

end OpenMath.Chapter3.Section312.RKTableau

namespace OpenMath.Chapter3.Section319

open OpenMath.Chapter3.Section312 OpenMath.Chapter3.Section381

open scoped NNReal

/-- **Deliverable D4** — Non-vacuity witness on `paddedEuler` with
`f := id` (Lipschitz with constant 1). Demonstrates that the
bundled D3 form is inhabited on a concrete tableau. -/
example : ∀ (y₀ z₀ y₁ z₁ : ℝ) (h : ℝ) (_hh : 0 ≤ h),
    paddedEuler.IsRKOneStep (fun y => y) y₀ h y₁ →
    paddedEuler.IsRKOneStep (fun y => y) z₀ h z₁ →
    ∃ Y Z : Fin 2 → ℝ,
      (∀ i, ‖Y i - Z i‖
        ≤ ‖y₀ - z₀‖ + h * 1 * ∑ j, |paddedEuler.A i j| * ‖Y j - Z j‖)
      ∧ ‖y₁ - z₁‖
        ≤ ‖y₀ - z₀‖ + h * 1 * ∑ i, |paddedEuler.b i| * ‖Y i - Z i‖ := by
  intro y₀ z₀ y₁ z₁ h hh hY hZ
  have hL : (0 : ℝ) ≤ 1 := by norm_num
  have hlip : LipschitzWith (1 : ℝ).toNNReal (fun y : ℝ => y) := by
    have hone : (1 : ℝ).toNNReal = 1 := Real.toNNReal_one
    rw [hone]
    exact LipschitzWith.id
  exact paddedEuler.lem_319A_recurrences hL hlip hh hY hZ

section Phase2

open scoped Matrix Matrix.Norms.Frobenius

/-- **Deliverable D5** — Non-vacuity witness for the Phase 2 headline
`lem_319A` on `paddedEuler` (where `A = 0`). With `f := id`
(Lipschitz with constant 1) and any positive `h ≤ h₀`, the M-matrix
smallness hypothesis is satisfied (`‖0‖ = 0 < 1`), so the existential
`L_dag` and the corresponding contraction bound exist. -/
example (h h₀ : ℝ) (hh : 0 < h) (hh_le : h ≤ h₀) (hh₀ : 0 ≤ h₀)
    (y₀ z₀ y₁ z₁ : ℝ)
    (hY : paddedEuler.IsRKOneStep (fun y => y) y₀ h y₁)
    (hZ : paddedEuler.IsRKOneStep (fun y => y) z₀ h z₁) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ‖y₁ - z₁‖ ≤ (1 + h * L_dag) * ‖y₀ - z₀‖ := by
  have hL : (0 : ℝ) ≤ 1 := by norm_num
  have hlip : LipschitzWith (1 : ℝ).toNNReal (fun y : ℝ => y) := by
    have hone : (1 : ℝ).toNNReal = 1 := Real.toNNReal_one
    rw [hone]
    exact LipschitzWith.id
  -- paddedEuler.A = 0 ⇒ paddedEuler.A.map abs = 0 ⇒ smul = 0 ⇒ ‖0‖ = 0 < 1.
  have hzero :
      (h₀ * (1 : ℝ)) • paddedEuler.A.map (fun a : ℝ => |a|)
        = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    simp [paddedEuler, Matrix.smul_apply]
  have hnorm :
      ‖((h₀ * (1 : ℝ)) • paddedEuler.A.map (fun a : ℝ => |a|))‖ < 1 := by
    rw [hzero, norm_zero]
    exact zero_lt_one
  obtain ⟨L_dag, hL_nn, hbound⟩ :=
    paddedEuler.lem_319A (L := 1) (h₀ := h₀) hL hlip hh hh_le hh₀ hnorm
  exact ⟨L_dag, hL_nn, hbound y₁ z₁ hY hZ⟩

/-- **Deliverable D6** — Non-vacuity witness for the Phase 1
`accumulation_recurrence` on `paddedEuler` with `f := id` (Lipschitz
with constant 1). The M-matrix smallness hypothesis is automatic
(`paddedEuler.A = 0` ⇒ `‖0‖ = 0 < 1`), so the existential `L_dag` and
the accumulation bound exist for any iterated trajectory. -/
example (h h₀ : ℝ) (hh : 0 < h) (hh_le : h ≤ h₀) (hh₀ : 0 ≤ h₀) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ∀ {n : ℕ} (traj yex : Fin (n + 1) → ℝ),
        paddedEuler.IsRKTrajectory (fun y => y) h traj →
        ∀ (δ : Fin n → ℝ),
          paddedEuler.HasLocalTruncationErrorBound
            (fun y => y) h yex δ →
          ‖yex (Fin.last n) - traj (Fin.last n)‖
            ≤ (1 + h * L_dag) ^ n * ‖yex 0 - traj 0‖
              + ∑ k : Fin n,
                  (1 + h * L_dag) ^ (n - 1 - k.val) * δ k := by
  have hL : (0 : ℝ) ≤ 1 := by norm_num
  have hlip : LipschitzWith (1 : ℝ).toNNReal (fun y : ℝ => y) := by
    have hone : (1 : ℝ).toNNReal = 1 := Real.toNNReal_one
    rw [hone]
    exact LipschitzWith.id
  have hzero :
      (h₀ * (1 : ℝ)) • paddedEuler.A.map (fun a : ℝ => |a|)
        = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    simp [paddedEuler, Matrix.smul_apply]
  have hnorm :
      ‖((h₀ * (1 : ℝ)) • paddedEuler.A.map (fun a : ℝ => |a|))‖ < 1 := by
    rw [hzero, norm_zero]
    exact zero_lt_one
  exact paddedEuler.accumulation_recurrence (L := 1) (h₀ := h₀)
    hL hlip hh hh_le hh₀ hnorm

end Phase2

end OpenMath.Chapter3.Section319
