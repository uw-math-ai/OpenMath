import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import OpenMath.Chapter2.Section212

/-!
# Butcher §213 — Convergence of the Euler method

Theorem 213A states: given a sequence of Euler approximations whose
maximum step size `Hₙ` and initial error `Kₙ` both tend to zero, the
global error `Dₙ = ‖y(xN) - ŷₙ(xN)‖` tends to zero. The proof is a
direct consequence of `thm:212A` (the global truncation error bound).

`xN` denotes the right endpoint of the integration interval (Butcher's
`x̄`); we use the ASCII spelling `xN` to avoid combining-character
parser quirks.

## Faithfulness notes

Butcher's setup has a single fixed exact solution `y` and a sequence of
approximations `ŷₙ`. We package the per-`n` data as a sequence of
`EulerSetup`s, one per index. The shared exact solution is encoded
implicitly: each `(S n).y` is permitted to vary with `n`, but the
theorem's hypotheses pin down the shared endpoints and a uniform
bound on the local-truncation constant `mₙ`.

The local-truncation constant `mₙ := (S n).m` is allowed to vary with
`n` but is bounded uniformly by some `M`; this matches Butcher's
implicit assumption that `m` depends only on `y''` and `f`, not on the
discretization. The Lipschitz constant `L` is fixed across the sequence
(Butcher's "f satisfies a Lipschitz condition" is a single hypothesis).
-/

namespace OpenMath.Chapter2.Section213

open scoped NNReal Topology
open Filter
open OpenMath.Chapter2.Section212

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Butcher §213 Theorem 213A — the Euler method is convergent.

Given a sequence `S : ℕ → EulerSetup E` whose grids share the same
left endpoint `x₀` and right endpoint `xN`, whose Lipschitz constant
is the fixed `L`, whose maximum step sizes `(S n).H` tend to zero,
whose initial errors are bounded by `K n` with `K n → 0`, and whose
local-truncation constants `(S n).m` are uniformly bounded by `M`,
the global error at the right endpoint tends to zero. -/
theorem euler_convergence
    (S : ℕ → EulerSetup E)
    (x₀ xN : ℝ) (L : ℝ≥0)
    (h_x₀ : ∀ n, (S n).x ⟨0, by omega⟩ = x₀)
    (h_xN : ∀ n, (S n).x ⟨(S n).n, Nat.lt_succ_self _⟩ = xN)
    (h_L : ∀ n, (S n).L = L)
    (M : ℝ)
    (h_m_bound : ∀ n, (S n).m ≤ M)
    (h_M_nn : 0 ≤ M)
    (K : ℕ → ℝ)
    (h_K_bound : ∀ n, ‖(S n).y x₀ - (S n).ŷ x₀‖ ≤ K n)
    (hH : Tendsto (fun n => (S n).H) atTop (𝓝 0))
    (hK : Tendsto K atTop (𝓝 0)) :
    Tendsto (fun n => ‖(S n).y xN - (S n).ŷ xN‖) atTop (𝓝 0) := by
  -- The endpoints are ordered: `x₀ ≤ xN`, since the grid is monotone.
  have h_x_le : x₀ ≤ xN := by
    rw [← h_x₀ 0, ← h_xN 0]
    rcases Nat.eq_zero_or_pos (S 0).n with h0 | hpos
    · simp [h0]
    · exact (S 0).hx_mono.monotone
        (show (⟨0, by omega⟩ : Fin ((S 0).n + 1)) ≤ ⟨(S 0).n, _⟩ from
          Fin.mk_le_mk.mpr (Nat.zero_le _))
  have h_d_nn : 0 ≤ xN - x₀ := sub_nonneg.mpr h_x_le
  -- Split on `(L : ℝ) = 0` vs `> 0`.
  rcases eq_or_lt_of_le (NNReal.coe_nonneg L) with hL_eq | hL_pos
  · -- Case `L = 0`.
    have hL0 : (L : ℝ) = 0 := hL_eq.symm
    -- Upper bound `b n := K n + (xN - x₀) * M * (S n).H`.
    set b : ℕ → ℝ := fun n => K n + (xN - x₀) * M * (S n).H with hb_def
    have hbound : ∀ n, ‖(S n).y xN - (S n).ŷ xN‖ ≤ b n := by
      intro n
      have hS_L : (S n).L = 0 := by
        have h := h_L n
        rw [h]; ext; exact hL0
      have hgt :=
        global_truncation_error_L_zero (S n) hS_L
          ⟨(S n).n, Nat.lt_succ_self _⟩
      simp only at hgt
      rw [h_x₀ n, h_xN n] at hgt
      have h_init : ‖(S n).y x₀ - (S n).ŷ x₀‖ ≤ K n := h_K_bound n
      have hH_nn : 0 ≤ (S n).H := (S n).H_nonneg
      have hm_nn : 0 ≤ (S n).m := (S n).hm_nn
      have hmM : (S n).m ≤ M := h_m_bound n
      have h_HmM : (S n).H * (S n).m * (xN - x₀)
                    ≤ (xN - x₀) * M * (S n).H := by
        have h_HM : (S n).H * (S n).m ≤ (S n).H * M :=
          mul_le_mul_of_nonneg_left hmM hH_nn
        nlinarith [h_HM, hH_nn, hm_nn, h_d_nn, hmM, h_M_nn,
                   mul_nonneg hH_nn h_d_nn, mul_nonneg hH_nn hm_nn,
                   mul_nonneg h_d_nn h_M_nn]
      calc ‖(S n).y xN - (S n).ŷ xN‖
          ≤ ‖(S n).y x₀ - (S n).ŷ x₀‖ + (S n).H * (S n).m * (xN - x₀) := hgt
        _ ≤ K n + (xN - x₀) * M * (S n).H := by linarith
    have hb_tendsto : Tendsto b atTop (𝓝 0) := by
      have h₁ : Tendsto (fun n => (xN - x₀) * M * (S n).H) atTop (𝓝 0) := by
        have := hH.const_mul ((xN - x₀) * M)
        simpa using this
      have h₂ :
          Tendsto (fun n => K n + (xN - x₀) * M * (S n).H) atTop (𝓝 (0 + 0)) :=
        hK.add h₁
      simpa using h₂
    have h_nn : ∀ n, 0 ≤ ‖(S n).y xN - (S n).ŷ xN‖ := fun n => norm_nonneg _
    exact squeeze_zero h_nn hbound hb_tendsto
  · -- Case `L > 0`.
    set E0 : ℝ := Real.exp ((xN - x₀) * (L : ℝ)) with hE0_def
    set C : ℝ := (E0 - 1) / (L : ℝ) * M with hC_def
    set b : ℕ → ℝ := fun n => E0 * K n + C * (S n).H with hb_def
    have hE0_pos : 0 < E0 := Real.exp_pos _
    have hxL_nn : 0 ≤ (xN - x₀) * (L : ℝ) := mul_nonneg h_d_nn hL_pos.le
    have hE0_ge_1 : 1 ≤ E0 := by rw [hE0_def]; exact Real.one_le_exp hxL_nn
    have hE0_minus_1_nn : 0 ≤ E0 - 1 := by linarith
    have hC_nn : 0 ≤ C := by
      rw [hC_def]
      exact mul_nonneg (div_nonneg hE0_minus_1_nn hL_pos.le) h_M_nn
    have hbound : ∀ n, ‖(S n).y xN - (S n).ŷ xN‖ ≤ b n := by
      intro n
      have hS_L_coe : ((S n).L : ℝ) = (L : ℝ) := by
        have h := h_L n
        rw [h]
      have hSL_pos : 0 < ((S n).L : ℝ) := by rw [hS_L_coe]; exact hL_pos
      have hgt :=
        global_truncation_error_L_pos (S n) hSL_pos
          ⟨(S n).n, Nat.lt_succ_self _⟩
      simp only at hgt
      rw [h_x₀ n, h_xN n, hS_L_coe] at hgt
      have h_init : ‖(S n).y x₀ - (S n).ŷ x₀‖ ≤ K n := h_K_bound n
      have hE0_nn : 0 ≤ E0 := hE0_pos.le
      have hE0K : E0 * ‖(S n).y x₀ - (S n).ŷ x₀‖ ≤ E0 * K n :=
        mul_le_mul_of_nonneg_left h_init hE0_nn
      have hH_nn : 0 ≤ (S n).H := (S n).H_nonneg
      have hm_nn : 0 ≤ (S n).m := (S n).hm_nn
      have hmM : (S n).m ≤ M := h_m_bound n
      have h_resid :
          (E0 - 1) / (L : ℝ) * (S n).H * (S n).m ≤ C * (S n).H := by
        rw [hC_def]
        have hfac_nn : 0 ≤ (E0 - 1) / (L : ℝ) :=
          div_nonneg hE0_minus_1_nn hL_pos.le
        have h_facH_nn : 0 ≤ (E0 - 1) / (L : ℝ) * (S n).H :=
          mul_nonneg hfac_nn hH_nn
        have hkey : (E0 - 1) / (L : ℝ) * (S n).H * (S n).m
                      ≤ (E0 - 1) / (L : ℝ) * (S n).H * M :=
          mul_le_mul_of_nonneg_left hmM h_facH_nn
        nlinarith [hkey, hfac_nn, hH_nn, hm_nn, hmM, h_M_nn,
                   mul_nonneg hfac_nn h_M_nn]
      calc ‖(S n).y xN - (S n).ŷ xN‖
          ≤ E0 * ‖(S n).y x₀ - (S n).ŷ x₀‖
              + (E0 - 1) / (L : ℝ) * (S n).H * (S n).m := hgt
        _ ≤ E0 * K n + C * (S n).H := by linarith
    have hb_tendsto : Tendsto b atTop (𝓝 0) := by
      have h₁ : Tendsto (fun n => E0 * K n) atTop (𝓝 0) := by
        have := hK.const_mul E0
        simpa using this
      have h₂ : Tendsto (fun n => C * (S n).H) atTop (𝓝 0) := by
        have := hH.const_mul C
        simpa using this
      have h₃ :
          Tendsto (fun n => E0 * K n + C * (S n).H) atTop (𝓝 (0 + 0)) :=
        h₁.add h₂
      simpa using h₃
    have h_nn : ∀ n, 0 ≤ ‖(S n).y xN - (S n).ŷ xN‖ := fun n => norm_nonneg _
    exact squeeze_zero h_nn hbound hb_tendsto

/-- Butcher §213 Theorem 213B — uniform convergence of the Euler method.

Under the conditions of Theorem 213A, augmented with a uniform Lipschitz
bound on the exact solutions and a uniform bound on `‖f‖` at grid
values, the supremum of `‖y(x) - ŷₙ(x)‖` over `x ∈ [x₀, xN]` tends to
zero. We state this in the ε-N form

> `∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t ∈ [x₀, xN], ‖y t - ŷₙ t‖ < ε`

which is textbook-faithful (and avoids the measurability/boundedness
machinery a `⨆ t ∈ Icc x₀ xN, …` formulation would need).

## Faithfulness notes

Compared to `euler_convergence` (213A), three extra hypotheses appear:
* `Mf` and `h_Mf_nn` — a non-negative ceiling.
* `h_y_lip` — `Mf`-Lipschitz bound on the exact solution `(S n).y` over
  `[x₀, xN]`. Butcher's setup posits that `y` solves `y'(t) = f(t, y(t))`
  with `‖f‖ ≤ Mf` on the relevant domain; that yields this Lipschitz
  bound. We pass it as a hypothesis rather than re-deriving it.
* `h_f_grid_bound` — `‖f(xₖ, ŷₙ(xₖ))‖ ≤ Mf` at every grid value. Same
  source: Butcher's uniform `‖f‖ ≤ Mf` premise.

These two hypotheses are *consequences* of Butcher's setup, not
strengthenings of it. -/
theorem euler_convergence_uniform
    (S : ℕ → EulerSetup E)
    (x₀ xN : ℝ) (L : ℝ≥0)
    (h_x₀ : ∀ n, (S n).x ⟨0, by omega⟩ = x₀)
    (h_xN : ∀ n, (S n).x ⟨(S n).n, Nat.lt_succ_self _⟩ = xN)
    (h_L : ∀ n, (S n).L = L)
    (M : ℝ) (h_m_bound : ∀ n, (S n).m ≤ M) (h_M_nn : 0 ≤ M)
    (Mf : ℝ) (h_Mf_nn : 0 ≤ Mf)
    (h_y_lip : ∀ n s t, s ∈ Set.Icc x₀ xN → t ∈ Set.Icc x₀ xN →
        ‖(S n).y t - (S n).y s‖ ≤ Mf * |t - s|)
    (h_f_grid_bound : ∀ n, ∀ k : Fin ((S n).n + 1),
        ‖(S n).f ((S n).x k) ((S n).ŷ ((S n).x k))‖ ≤ Mf)
    (K : ℕ → ℝ) (h_K_bound : ∀ n, ‖(S n).y x₀ - (S n).ŷ x₀‖ ≤ K n)
    (hH : Tendsto (fun n => (S n).H) atTop (𝓝 0))
    (hK : Tendsto K atTop (𝓝 0)) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t ∈ Set.Icc x₀ xN,
        ‖(S n).y t - (S n).ŷ t‖ < ε := by
  -- Order of endpoints: x₀ ≤ xN.
  have h_x_le : x₀ ≤ xN := by
    rw [← h_x₀ 0, ← h_xN 0]
    rcases Nat.eq_zero_or_pos (S 0).n with h0 | hpos
    · simp [h0]
    · exact (S 0).hx_mono.monotone
        (show (⟨0, by omega⟩ : Fin ((S 0).n + 1)) ≤ ⟨(S 0).n, _⟩ from
          Fin.mk_le_mk.mpr (Nat.zero_le _))
  have h_d_nn : 0 ≤ xN - x₀ := sub_nonneg.mpr h_x_le
  -- Helper: package h_y_lip / set membership translated to the (S n).x form.
  have h_lip_translate : ∀ n,
      ∀ s t,
        s ∈ Set.Icc ((S n).x ⟨0, by omega⟩) ((S n).x ⟨(S n).n, Nat.lt_succ_self _⟩) →
        t ∈ Set.Icc ((S n).x ⟨0, by omega⟩) ((S n).x ⟨(S n).n, Nat.lt_succ_self _⟩) →
        ‖(S n).y t - (S n).y s‖ ≤ Mf * |t - s| := by
    intro n s t hs ht
    rw [h_x₀ n, h_xN n] at hs ht
    exact h_y_lip n s t hs ht
  have h_mem_translate : ∀ n, ∀ {t : ℝ}, t ∈ Set.Icc x₀ xN →
      t ∈ Set.Icc ((S n).x ⟨0, by omega⟩) ((S n).x ⟨(S n).n, Nat.lt_succ_self _⟩) := by
    intro n t ht
    rw [h_x₀ n, h_xN n]; exact ht
  -- Split on (L : ℝ) = 0 vs > 0.
  rcases eq_or_lt_of_le (NNReal.coe_nonneg L) with hL_eq | hL_pos
  · -- Case L = 0.
    have hL0 : (L : ℝ) = 0 := hL_eq.symm
    set b : ℕ → ℝ := fun n =>
      K n + (xN - x₀) * M * (S n).H + 2 * Mf * (S n).H with hb_def
    have hbound : ∀ n, ∀ t ∈ Set.Icc x₀ xN, ‖(S n).y t - (S n).ŷ t‖ ≤ b n := by
      intro n t ht
      have hS_L : (S n).L = 0 := by
        have h := h_L n; rw [h]; ext; exact hL0
      have hgt := global_truncation_error_L_zero_offstep
                    (S n) hS_L h_Mf_nn (h_lip_translate n) (h_f_grid_bound n)
                    (h_mem_translate n ht)
      rw [h_x₀ n, h_xN n] at hgt
      have h_init : ‖(S n).y x₀ - (S n).ŷ x₀‖ ≤ K n := h_K_bound n
      have hH_nn : 0 ≤ (S n).H := (S n).H_nonneg
      have hm_nn : 0 ≤ (S n).m := (S n).hm_nn
      have hmM : (S n).m ≤ M := h_m_bound n
      have h_HmM : (S n).H * (S n).m * (xN - x₀) ≤ (xN - x₀) * M * (S n).H := by
        nlinarith [hH_nn, hm_nn, hmM, h_M_nn, h_d_nn,
                   mul_nonneg hH_nn h_d_nn, mul_nonneg hH_nn hm_nn]
      linarith [hgt, h_init, h_HmM]
    have hb_tendsto : Tendsto b atTop (𝓝 0) := by
      have h₁ : Tendsto (fun n => (xN - x₀) * M * (S n).H) atTop (𝓝 0) := by
        have := hH.const_mul ((xN - x₀) * M); simpa using this
      have h₂ : Tendsto (fun n => 2 * Mf * (S n).H) atTop (𝓝 0) := by
        have := hH.const_mul (2 * Mf); simpa using this
      have h₃ :
          Tendsto (fun n => K n + (xN - x₀) * M * (S n).H + 2 * Mf * (S n).H)
                  atTop (𝓝 (0 + 0 + 0)) := (hK.add h₁).add h₂
      simpa using h₃
    intro ε hε
    have hev : ∀ᶠ n in atTop, b n < ε :=
      hb_tendsto (isOpen_Iio.mem_nhds hε)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn t ht => ?_⟩
    have hbn_lt := hN n hn
    have h_le := hbound n t ht
    linarith
  · -- Case L > 0.
    set E0 : ℝ := Real.exp ((xN - x₀) * (L : ℝ)) with hE0_def
    set C : ℝ := (E0 - 1) / (L : ℝ) * M with hC_def
    set b : ℕ → ℝ := fun n =>
      E0 * K n + C * (S n).H + 2 * Mf * (S n).H with hb_def
    have hE0_pos : 0 < E0 := Real.exp_pos _
    have hxL_nn : 0 ≤ (xN - x₀) * (L : ℝ) := mul_nonneg h_d_nn hL_pos.le
    have hE0_ge_1 : 1 ≤ E0 := by rw [hE0_def]; exact Real.one_le_exp hxL_nn
    have hE0_minus_1_nn : 0 ≤ E0 - 1 := by linarith
    have hC_nn : 0 ≤ C := by
      rw [hC_def]
      exact mul_nonneg (div_nonneg hE0_minus_1_nn hL_pos.le) h_M_nn
    have hbound : ∀ n, ∀ t ∈ Set.Icc x₀ xN, ‖(S n).y t - (S n).ŷ t‖ ≤ b n := by
      intro n t ht
      have hS_L_coe : ((S n).L : ℝ) = (L : ℝ) := by
        have h := h_L n; rw [h]
      have hSL_pos : 0 < ((S n).L : ℝ) := by rw [hS_L_coe]; exact hL_pos
      have hgt := global_truncation_error_L_pos_offstep
                    (S n) hSL_pos h_Mf_nn (h_lip_translate n) (h_f_grid_bound n)
                    (h_mem_translate n ht)
      rw [h_x₀ n, h_xN n, hS_L_coe] at hgt
      have h_init : ‖(S n).y x₀ - (S n).ŷ x₀‖ ≤ K n := h_K_bound n
      have hE0_nn : 0 ≤ E0 := hE0_pos.le
      have hE0K : E0 * ‖(S n).y x₀ - (S n).ŷ x₀‖ ≤ E0 * K n :=
        mul_le_mul_of_nonneg_left h_init hE0_nn
      have hH_nn : 0 ≤ (S n).H := (S n).H_nonneg
      have hm_nn : 0 ≤ (S n).m := (S n).hm_nn
      have hmM : (S n).m ≤ M := h_m_bound n
      have h_resid :
          (E0 - 1) / (L : ℝ) * (S n).H * (S n).m ≤ C * (S n).H := by
        rw [hC_def]
        have hfac_nn : 0 ≤ (E0 - 1) / (L : ℝ) :=
          div_nonneg hE0_minus_1_nn hL_pos.le
        have h_facH_nn : 0 ≤ (E0 - 1) / (L : ℝ) * (S n).H :=
          mul_nonneg hfac_nn hH_nn
        have hkey : (E0 - 1) / (L : ℝ) * (S n).H * (S n).m
                      ≤ (E0 - 1) / (L : ℝ) * (S n).H * M :=
          mul_le_mul_of_nonneg_left hmM h_facH_nn
        nlinarith [hkey, hfac_nn, hH_nn, hm_nn, hmM, h_M_nn,
                   mul_nonneg hfac_nn h_M_nn]
      linarith [hgt, hE0K, h_resid]
    have hb_tendsto : Tendsto b atTop (𝓝 0) := by
      have h₁ : Tendsto (fun n => E0 * K n) atTop (𝓝 0) := by
        have := hK.const_mul E0; simpa using this
      have h₂ : Tendsto (fun n => C * (S n).H) atTop (𝓝 0) := by
        have := hH.const_mul C; simpa using this
      have h₃ : Tendsto (fun n => 2 * Mf * (S n).H) atTop (𝓝 0) := by
        have := hH.const_mul (2 * Mf); simpa using this
      have h₄ :
          Tendsto (fun n => E0 * K n + C * (S n).H + 2 * Mf * (S n).H) atTop
                  (𝓝 (0 + 0 + 0)) := (h₁.add h₂).add h₃
      simpa using h₄
    intro ε hε
    have hev : ∀ᶠ n in atTop, b n < ε :=
      hb_tendsto (isOpen_Iio.mem_nhds hε)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn t ht => ?_⟩
    have hbn_lt := hN n hn
    have h_le := hbound n t ht
    linarith

end OpenMath.Chapter2.Section213
