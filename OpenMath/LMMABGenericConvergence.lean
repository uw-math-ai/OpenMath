import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp

/-! ## Generic Adams–Bashforth `s`-step convergence scaffold (Iserles §1.2)

This file factors the AB2–AB6 scalar convergence pattern (cycles 408, 412,
418, 422, 424) into a small reusable shape. It exposes:

* `LMM.abIter s α h f t₀ y₀` — the explicit AB recurrence
  `y_{n+s} = y_{n+s-1} + h · ∑ α_j · f(t₀ + (n+j) h, y_{n+j})`,
* `LMM.abIter_lipschitz_one_step` — the standard window-max
  `(1 + h · Λ)`-recurrence with `Λ = L · ∑ |α_j|`,
* `LMM.ab_global_error_bound_generic` — the headline, applying
  `lmm_error_bound_from_local_truncation` once a uniform `|τ_n| ≤ K · h^(p+1)`
  residual bound is supplied as a hypothesis.

This first iteration deliberately does NOT subsume the AB2–AB6 chains. The
chains close their own residual ladders manually; this scaffold only wraps
the `one-step ⇒ Grönwall ⇒ headline` plumbing. Refactoring AB2–AB6 to flow
through this abstraction is deferred to follow-up cycles.
-/

namespace LMM

/-- Generic Adams–Bashforth `s`-step iteration with `s` starting samples
`y₀ : Fin s → ℝ`:
`y_{n+s} = y_{n+s-1} + h · ∑_{j : Fin s} α_j · f(t₀ + (n+j) h, y_{n+j})`.
For `n < s` it returns the corresponding starting sample. For `s = 0` it
returns `0`. -/
noncomputable def abIter (s : ℕ) (α : Fin s → ℝ)
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ) (y₀ : Fin s → ℝ) : ℕ → ℝ
  | n =>
    if h_lt : n < s then y₀ ⟨n, h_lt⟩
    else if hs : 0 < s then
      let prev : Fin s → ℝ := fun j =>
        have hjs : (j : ℕ) < s := j.isLt
        have h_le : s ≤ n := Nat.not_lt.mp h_lt
        have hdec : n - s + (j : ℕ) < n := by omega
        abIter s α h f t₀ y₀ (n - s + (j : ℕ))
      prev ⟨s - 1, by omega⟩
        + h * ∑ j : Fin s,
            α j * f (t₀ + ((n - s + (j : ℕ) : ℕ) : ℝ) * h) (prev j)
    else 0
  termination_by n => n

/-- One-step unfolding of the generic AB iteration at index `n + s`,
exposing the explicit `s`-window recurrence in textbook form. -/
theorem abIter_step (s : ℕ) (hs : 0 < s) (α : Fin s → ℝ)
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ) (y₀ : Fin s → ℝ) (n : ℕ) :
    abIter s α h f t₀ y₀ (n + s)
      = abIter s α h f t₀ y₀ (n + s - 1)
        + h * ∑ j : Fin s,
            α j * f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
              (abIter s α h f t₀ y₀ (n + (j : ℕ))) := by
  have h_lt : ¬ n + s < s := by omega
  conv_lhs => rw [abIter]
  rw [dif_neg h_lt, dif_pos hs]
  have hidx : ∀ (j : ℕ), n + s - s + j = n + j := by intro j; omega
  have hsm1 : n + (s - 1) = n + s - 1 := by omega
  simp only [hidx, hsm1]

/-- The effective Lipschitz constant `Λ = L · ∑_{j} |α_j|` driving the
exponential Grönwall amplification of the AB `s`-step recurrence. -/
noncomputable def abLip (s : ℕ) (α : Fin s → ℝ) (L : ℝ) : ℝ :=
  L * ∑ j : Fin s, |α j|

@[simp] lemma abLip_def (s : ℕ) (α : Fin s → ℝ) (L : ℝ) :
    abLip s α L = L * ∑ j : Fin s, |α j| := rfl

lemma abLip_nonneg {s : ℕ} {α : Fin s → ℝ} {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ abLip s α L :=
  mul_nonneg hL (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

/-- Pointwise error of the generic AB iterate against the exact solution. -/
noncomputable def abErr (s : ℕ) (α : Fin s → ℝ) (h : ℝ) (f : ℝ → ℝ → ℝ)
    (t₀ : ℝ) (y₀ : Fin s → ℝ) (y : ℝ → ℝ) (k : ℕ) : ℝ :=
  |abIter s α h f t₀ y₀ k - y (t₀ + (k : ℝ) * h)|

lemma abErr_nonneg (s : ℕ) (α : Fin s → ℝ) (h : ℝ) (f : ℝ → ℝ → ℝ)
    (t₀ : ℝ) (y₀ : Fin s → ℝ) (y : ℝ → ℝ) (k : ℕ) :
    0 ≤ abErr s α h f t₀ y₀ y k := abs_nonneg _

/-- The local truncation residual at step `n` as it appears in the generic
window-max recurrence:
`τ_n = y(t₀ + (n+s) h) − y(t₀ + (n+s-1) h) − h · ∑ α_j · y'(t₀ + (n+j) h)`.

This is the same form the AB2–AB6 files end up bounding by `K · h^(p+1)`
through their per-`s` Taylor ladders. -/
noncomputable def abResidual (s : ℕ) (α : Fin s → ℝ) (h : ℝ) (y : ℝ → ℝ)
    (t₀ : ℝ) (n : ℕ) : ℝ :=
  y (t₀ + ((n + s : ℕ) : ℝ) * h) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)
    - h * ∑ j : Fin s, α j * deriv y (t₀ + ((n + j : ℕ) : ℝ) * h)

/-- Window-max error sequence: `EN k = max_{j : Fin s} |y_{k+j} − y(t₀+(k+j)h)|`.
Defined for `1 ≤ s` so the maximum is taken over a nonempty index set. -/
noncomputable def abErrWindow {s : ℕ} (hs : 1 ≤ s) (α : Fin s → ℝ) (h : ℝ)
    (f : ℝ → ℝ → ℝ) (t₀ : ℝ) (y₀ : Fin s → ℝ) (y : ℝ → ℝ) (k : ℕ) : ℝ :=
  haveI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin s => abErr s α h f t₀ y₀ y (k + (j : ℕ)))

lemma abErrWindow_nonneg {s : ℕ} (hs : 1 ≤ s) (α : Fin s → ℝ) (h : ℝ)
    (f : ℝ → ℝ → ℝ) (t₀ : ℝ) (y₀ : Fin s → ℝ) (y : ℝ → ℝ) (k : ℕ) :
    0 ≤ abErrWindow hs α h f t₀ y₀ y k := by
  haveI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  unfold abErrWindow
  exact (Finset.le_sup' (b := ⟨0, hs⟩)
        (f := fun j : Fin s => abErr s α h f t₀ y₀ y (k + (j : ℕ)))
        (Finset.mem_univ _)).trans' (abErr_nonneg _ _ _ _ _ _ _ _) |>.trans
      (le_refl _)

/-- Window-max one-step error recurrence for the generic AB iteration: with
window size `s` and effective Lipschitz constant `Λ = L · ∑ |α_j|`,
`EN (n + 1) ≤ (1 + h · Λ) · EN n + |τ_n|`. -/
theorem abIter_lipschitz_one_step
    {s : ℕ} (hs : 1 ≤ s) (α : Fin s → ℝ)
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) (y₀ : Fin s → ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindow hs α h f t₀ y₀ y (n + 1)
      ≤ (1 + h * abLip s α L) * abErrWindow hs α h f t₀ y₀ y n
        + |abResidual s α h y t₀ n| := by
  haveI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  set Λ : ℝ := abLip s α L with hΛ_def
  have hΛ_nn : 0 ≤ Λ := abLip_nonneg hL
  have hhΛ_nn : 0 ≤ h * Λ := mul_nonneg hh hΛ_nn
  set EN_n : ℝ := abErrWindow hs α h f t₀ y₀ y n with hEN_n_def
  have hEN_n_nn : 0 ≤ EN_n := abErrWindow_nonneg hs α h f t₀ y₀ y n
  set τ : ℝ := abResidual s α h y t₀ n with hτ_def
  set τabs : ℝ := |τ| with hτabs_def
  have hτabs_nn : 0 ≤ τabs := abs_nonneg _
  -- Each in-window sample bounded by EN_n.
  have h_eN_in_window : ∀ j : Fin s,
      abErr s α h f t₀ y₀ y (n + (j : ℕ)) ≤ EN_n := by
    intro j
    show abErr s α h f t₀ y₀ y (n + (j : ℕ)) ≤ abErrWindow hs α h f t₀ y₀ y n
    unfold abErrWindow
    exact Finset.le_sup' (b := j)
      (f := fun k : Fin s => abErr s α h f t₀ y₀ y (n + (k : ℕ)))
      (Finset.mem_univ _)
  -- One-step bound at the new point n + s.
  have h_eN_ns_bound :
      abErr s α h f t₀ y₀ y (n + s) ≤ (1 + h * Λ) * EN_n + τabs := by
    -- Notation.
    set yiter : ℕ → ℝ := abIter s α h f t₀ y₀
    set tval : ℕ → ℝ := fun k => t₀ + ((k : ℕ) : ℝ) * h
    -- AB step formula at index n + s.
    have hstep := abIter_step s hs α h f t₀ y₀ n
    -- τ in textbook form using `deriv y = f` along the trajectory.
    have hτ_alt : τ
        = y (t₀ + ((n + s : ℕ) : ℝ) * h)
            - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)
            - h * ∑ j : Fin s, α j
                * f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                    (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)) := by
      show abResidual s α h y t₀ n = _
      unfold abResidual
      have hcong :
          (fun j : Fin s => α j * deriv y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))
            = (fun j : Fin s => α j
                * f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                    (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))) := by
        funext j; rw [hyf]
      rw [hcong]
    -- Set sum abbreviations.
    set Sa : ℝ := ∑ j : Fin s, α j
        * f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
            (yiter (n + (j : ℕ))) with hSa_def
    set Sy : ℝ := ∑ j : Fin s, α j
        * f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
            (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)) with hSy_def
    -- Algebraic decomposition.
    have halg :
        yiter (n + s) - y (t₀ + ((n + s : ℕ) : ℝ) * h)
          = (yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h))
            + h * (Sa - Sy)
            - τ := by
      rw [hτ_alt]
      have : yiter (n + s) = yiter (n + s - 1) + h * Sa := hstep
      rw [this]
      ring
    -- Bound on h * (Sa - Sy) via Lipschitz.
    have hSa_sub_Sy :
        Sa - Sy = ∑ j : Fin s, α j
          * (f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
            - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))) := by
      rw [hSa_def, hSy_def, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intros j _; ring
    -- Per-summand Lipschitz bound (in absolute value).
    have h_diff_bound : ∀ j : Fin s,
        |α j * (f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
              - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                  (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)))|
          ≤ |α j| * L * EN_n := by
      intro j
      have hLip := hf (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                      (yiter (n + (j : ℕ)))
                      (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))
      have heN : abErr s α h f t₀ y₀ y (n + (j : ℕ)) ≤ EN_n := h_eN_in_window j
      have heN_eq : abErr s α h f t₀ y₀ y (n + (j : ℕ))
          = |yiter (n + (j : ℕ)) - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)| := by
        show |yiter (n + (j : ℕ)) - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)|
            = _; rfl
      have hLip_EN :
          |yiter (n + (j : ℕ)) - y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)|
            ≤ EN_n := by rw [← heN_eq]; exact heN
      rw [abs_mul]
      have hαj_nn : 0 ≤ |α j| := abs_nonneg _
      have h_inner : |f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
            - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))|
          ≤ L * EN_n := by
        refine hLip.trans ?_
        exact mul_le_mul_of_nonneg_left hLip_EN hL
      calc |α j| * |f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
              - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                  (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h))|
          ≤ |α j| * (L * EN_n) :=
            mul_le_mul_of_nonneg_left h_inner hαj_nn
        _ = |α j| * L * EN_n := by ring
    -- Sum bound.
    have hSd_abs : |Sa - Sy| ≤ Λ * EN_n := by
      rw [hSa_sub_Sy]
      calc |∑ j : Fin s, α j
              * (f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
                  - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                      (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)))|
            ≤ ∑ j : Fin s,
                |α j * (f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h) (yiter (n + (j : ℕ)))
                  - f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                      (y (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j : Fin s, |α j| * L * EN_n :=
              Finset.sum_le_sum (fun j _ => h_diff_bound j)
          _ = (∑ j : Fin s, |α j|) * L * EN_n := by
              rw [← Finset.sum_mul, ← Finset.sum_mul]
          _ = Λ * EN_n := by rw [hΛ_def, abLip]; ring
    -- Bound on |abIter (n+s-1) - y(tn+s-1)| ≤ EN_n via the (s-1)-th window slot.
    have h_eN_nsm1 :
        |yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)| ≤ EN_n := by
      have hs1 : (s - 1 : ℕ) < s := by omega
      have h_in := h_eN_in_window ⟨s - 1, hs1⟩
      have hidx : n + ((⟨s - 1, hs1⟩ : Fin s) : ℕ) = n + s - 1 := by
        show n + (s - 1) = n + s - 1; omega
      have hcoe : abErr s α h f t₀ y₀ y (n + ((⟨s - 1, hs1⟩ : Fin s) : ℕ))
          = |yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)| := by
        show |yiter (n + ((⟨s - 1, hs1⟩ : Fin s) : ℕ))
              - y (t₀ + ((n + ((⟨s - 1, hs1⟩ : Fin s) : ℕ) : ℕ) : ℝ) * h)|
              = _
        rw [hidx]
      linarith [hcoe.symm ▸ h_in]
    -- Triangle inequality: |a + b - τ| ≤ |a| + |b| + |τ|.
    have htri :
        |yiter (n + s) - y (t₀ + ((n + s : ℕ) : ℝ) * h)|
          ≤ |yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)|
            + |h * (Sa - Sy)| + τabs := by
      rw [halg]
      have h1 :
          |(yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h))
              + h * (Sa - Sy) - τ|
            ≤ |(yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h))
                + h * (Sa - Sy)| + |τ| := abs_sub _ _
      have h2 :
          |(yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h))
              + h * (Sa - Sy)|
            ≤ |yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)|
              + |h * (Sa - Sy)| := abs_add_le _ _
      linarith
    -- Bound h * (Sa - Sy) in absolute value.
    have h_h_Sd : |h * (Sa - Sy)| ≤ h * (Λ * EN_n) := by
      rw [abs_mul, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left hSd_abs hh
    -- Combine.
    have hfinal :
        |yiter (n + s) - y (t₀ + ((n + s : ℕ) : ℝ) * h)|
          ≤ EN_n + h * Λ * EN_n + τabs := by
      have := htri
      have h_alg : |yiter (n + s - 1) - y (t₀ + ((n + s - 1 : ℕ) : ℝ) * h)|
              + |h * (Sa - Sy)| + τabs
            ≤ EN_n + h * (Λ * EN_n) + τabs := by linarith
      have h_alg2 : EN_n + h * (Λ * EN_n) = EN_n + h * Λ * EN_n := by ring
      linarith
    -- Convert back to abErr.
    show |yiter (n + s) - y (t₀ + ((n + s : ℕ) : ℝ) * h)|
        ≤ (1 + h * Λ) * EN_n + τabs
    have h_one : (1 + h * Λ) * EN_n = EN_n + h * Λ * EN_n := by ring
    linarith
  -- Per-window bound on EN(n+1).
  have h_per : ∀ j : Fin s,
      abErr s α h f t₀ y₀ y (n + 1 + (j : ℕ))
        ≤ (1 + h * Λ) * EN_n + τabs := by
    intro j
    have hjs : (j : ℕ) < s := j.isLt
    by_cases hj : (j : ℕ) + 1 < s
    · -- j + 1 < s: lies in the prior window.
      have hwindow : abErr s α h f t₀ y₀ y (n + ((j : ℕ) + 1)) ≤ EN_n := by
        have h_in := h_eN_in_window ⟨(j : ℕ) + 1, hj⟩
        show abErr s α h f t₀ y₀ y (n + ((j : ℕ) + 1)) ≤ EN_n
        have hcoe :
            n + ((⟨(j : ℕ) + 1, hj⟩ : Fin s) : ℕ) = n + ((j : ℕ) + 1) := rfl
        rw [show (n + ((⟨(j : ℕ) + 1, hj⟩ : Fin s) : ℕ))
            = n + ((j : ℕ) + 1) from rfl] at h_in
        exact h_in
      have hidx : n + 1 + (j : ℕ) = n + ((j : ℕ) + 1) := by omega
      rw [hidx]
      have h1 : EN_n ≤ (1 + h * Λ) * EN_n := by
        have := mul_le_mul_of_nonneg_right
          (show (1 : ℝ) ≤ 1 + h * Λ by linarith) hEN_n_nn
        linarith
      linarith
    · -- (j : ℕ) + 1 ≥ s, so (j : ℕ) = s - 1.
      have hjeq : (j : ℕ) = s - 1 := by omega
      have hidx : n + 1 + (j : ℕ) = n + s := by omega
      rw [hidx]
      exact h_eN_ns_bound
  -- Conclude with Finset.sup'_le.
  unfold abErrWindow
  exact Finset.sup'_le _ _ (fun j _ => h_per j)

/-- Auxiliary finite-sum helper extracted for clean rewriting in the
window-max one-step bound: `h · L · ∑ |α_j| · m = h · Λ · m`. Stated
abstractly so per-`s` chains can reuse it without rederiving. -/
lemma abLip_window_bound {s : ℕ} (α : Fin s → ℝ) (h L m : ℝ) :
    h * (L * ∑ j : Fin s, |α j|) * m
      = h * abLip s α L * m := by
  simp [abLip]

/-- Monotonicity of the residual bound `K · h^(p+1)` in `h`: the bound is
nondecreasing in `h` on `[0, ∞)`. Used when chaining the per-step residual
bound through the Grönwall recurrence. -/
lemma abResidual_bound_mono {K : ℝ} {p : ℕ} (hK : 0 ≤ K)
    {h₁ h₂ : ℝ} (hh₁ : 0 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) :
    K * h₁ ^ (p + 1) ≤ K * h₂ ^ (p + 1) :=
  mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hh₁ hh₁₂ (p + 1)) hK

/-- Headline generic AB convergence bound. Given a uniform residual bound
`|τ_n| ≤ K · h^(p+1)` and the window-max one-step recurrence, the global
error obeys the textbook `O(ε₀ + h^p)` bound on a finite horizon. The
residual bound is taken as a hypothesis; deriving it from a `ContDiff`
exact solution is the AB-specific Taylor ladder, handled in the per-`s`
files (cycles 408, 412, 418, 422, 424).

The Grönwall plumbing is wrapped via
`lmm_error_bound_from_local_truncation`; this declaration packages it for
generic Adams–Bashforth use. -/
theorem ab_global_error_bound_generic
    {s : ℕ} (hs : 1 ≤ s) (α : Fin s → ℝ)
    {h L K T : ℝ} {p : ℕ}
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hK : 0 ≤ K)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) (y₀ : Fin s → ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    {ε₀ : ℝ} (_hε₀ : 0 ≤ ε₀)
    (hstart : abErrWindow hs α h f t₀ y₀ y 0 ≤ ε₀)
    (N : ℕ) (hNh : ((N : ℝ)) * h ≤ T)
    (hresidual : ∀ n : ℕ, n < N →
      |abResidual s α h y t₀ n| ≤ K * h ^ (p + 1)) :
    abErrWindow hs α h f t₀ y₀ y N
      ≤ Real.exp (abLip s α L * T) * ε₀
        + T * Real.exp (abLip s α L * T) * K * h ^ p := by
  set EN : ℕ → ℝ := abErrWindow hs α h f t₀ y₀ y with hEN_def
  have hΛ_nn : 0 ≤ abLip s α L := abLip_nonneg hL
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    abErrWindow_nonneg hs α h f t₀ y₀ y k
  -- Combine the window-max one-step bound with the residual bound.
  have hstep : ∀ n, n < N →
      EN (n + 1) ≤ (1 + h * abLip s α L) * EN n + K * h ^ (p + 1) := by
    intro n hn
    have honestep :=
      abIter_lipschitz_one_step hs α hh hL hf t₀ y₀ y hyf n
    have hres := hresidual n hn
    show abErrWindow hs α h f t₀ y₀ y (n + 1)
        ≤ (1 + h * abLip s α L) * abErrWindow hs α h f t₀ y₀ y n
          + K * h ^ (p + 1)
    linarith
  -- Apply the abstract Grönwall bridge from LMMTruncationOp.
  have hgronwall :=
    lmm_error_bound_from_local_truncation
      (h := h) (L := abLip s α L) (C := K) (T := T) (p := p) (e := EN)
      (N := N) hh hΛ_nn hK (hEN_nn 0) hstep N le_rfl hNh
  have hexp_nn : 0 ≤ Real.exp (abLip s α L * T) := Real.exp_nonneg _
  have h_chain :
      Real.exp (abLip s α L * T) * EN 0
        ≤ Real.exp (abLip s α L * T) * ε₀ :=
    mul_le_mul_of_nonneg_left hstart hexp_nn
  linarith

end LMM
