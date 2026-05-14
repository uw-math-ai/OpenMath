import OpenMath.Chapter3.Section381
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

end OpenMath.Chapter3.Section319
