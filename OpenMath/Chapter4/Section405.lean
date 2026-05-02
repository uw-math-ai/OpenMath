import OpenMath.Chapter4.Section404

/-!
# Butcher §405 — Necessity of conditions for convergence

This file packages the converse of cycle 068's
`stable_consistent_isConvergent` (Butcher `thm:406D`) — the necessity
direction of the equivalence "convergent ⇔ stable ∧ consistent"
(Butcher `thm:243A`, originally cross-chapter deferred from §243).

## Textbook statements

> **Theorem 405A** (Butcher, p. 343).  A convergent linear multistep
> method is stable.

> **Theorem 405B** (Butcher, p. 343).  A convergent linear multistep
> method is preconsistent.

> **Theorem 405C** (Butcher, p. 344).  A convergent linear multistep
> method is consistent.

> **Theorem 243A** (Butcher, p. 130).  A linear multistep method is
> convergent if and only if it is stable and consistent.

The forward direction (`stable ∧ consistent ⇒ convergent`) is cycle
068's `LinearMultistepMethod.stable_consistent_isConvergent`. Cycle
069 lands the iff packager and closes `thm:405B`
(`convergent_isPreconsistent`) via the trivial-IVP argument with
the canonical homogeneous-from-ones sequence. `thm:405A` and
`thm:405C` remain as scaffold sorries for cycle 070+
(Butcher's argument for `thm:405A` uses an unbounded homogeneous
solution; `thm:405C` reuses the trivial-IVP argument with RHS
`f ≡ 1` and starting values `η_i / n`).
-/

namespace OpenMath.Chapter4.Section404

open scoped Topology

/-- **Helper for `thm:405B` (cycle 069).** The unique sequence with
`η i = 1` for `i < k` and satisfying the homogeneous recurrence

  `η (m + k) = Σ_{j : Fin k} M.α j.succ · η (m + k − (j.val + 1))`

for `m ≥ 0`. Defined by strong recursion on `ℕ`; the recursive call
at `n − (j.val + 1)` is well-founded because `n ≥ k > j.val` in the
recursion branch. -/
noncomputable def LinearMultistepMethod.homogeneousFromOnes
    {k : ℕ} (M : LinearMultistepMethod k) : ℕ → ℝ
  | n => if h : n < k then 1
         else
           ∑ j : Fin k,
             M.α j.succ *
               LinearMultistepMethod.homogeneousFromOnes M
                 (n - (j.val + 1))
  termination_by n => n
  decreasing_by
    simp_wf
    rename_i h
    have hm : k ≤ n := Nat.not_lt.mp h
    have hj : j.val < k := j.isLt
    omega

/-- For `i < k`, the homogeneous-from-ones sequence equals `1`. -/
theorem LinearMultistepMethod.homogeneousFromOnes_lt_k
    {k : ℕ} (M : LinearMultistepMethod k) (i : ℕ) (hi : i < k) :
    M.homogeneousFromOnes i = 1 := by
  rw [LinearMultistepMethod.homogeneousFromOnes, dif_pos hi]

/-- The recurrence at indices `n ≥ k`. -/
theorem LinearMultistepMethod.homogeneousFromOnes_recurrence
    {k : ℕ} (M : LinearMultistepMethod k) (n : ℕ) (hn : k ≤ n) :
    M.homogeneousFromOnes n =
      ∑ j : Fin k, M.α j.succ * M.homogeneousFromOnes (n - (j.val + 1)) := by
  rw [LinearMultistepMethod.homogeneousFromOnes, dif_neg (Nat.not_lt.mpr hn)]

/-- The homogeneous-from-ones sequence is a solution of the
homogeneous recurrence (Butcher (403a)). -/
theorem LinearMultistepMethod.homogeneousFromOnes_isHomogeneousSolution
    {k : ℕ} (M : LinearMultistepMethod k) :
    M.IsHomogeneousSolution M.homogeneousFromOnes := by
  intro m
  have hk : k ≤ m + k := Nat.le_add_left k m
  exact M.homogeneousFromOnes_recurrence (m + k) hk

/-- **Butcher Theorem 405A** (p. 343).  A convergent linear multistep
method is stable.

Textbook proof sketch: if the method were not stable, there would
exist an unbounded sequence `η` solving the homogeneous recurrence.
Setting `ζ_n = max_{i ≤ n} |η_i|` and applying convergence to the
trivial IVP `y' = 0, y(0) = 0` with starting values `η_i / ζ_n`
forces `|η_n / ζ_n| → 0`, contradicting `|η_n / ζ_n| = 1` for
infinitely many `n`.

Cycle 070+ followup. -/
theorem LinearMultistepMethod.convergent_isStable
    {k : ℕ} (M : LinearMultistepMethod k)
    (hConv : M.IsConvergent) : M.IsStable := by
  sorry

/-- **Butcher Theorem 405B** (p. 343).  A convergent linear multistep
method is preconsistent.

Textbook proof sketch: by `thm:405A` the method is stable.  Take
the homogeneous solution `η` with `η_0 = ⋯ = η_{k-1} = 1`.  Applying
convergence to the trivial IVP `y' = 0, y(0) = 1` at `x = 1` with
starting values `1` gives `η_n → 1`, and the recurrence at step `n`
forces `1 - α_1 - ⋯ - α_k = 0`, i.e. preconsistency.

Lean strategy: introduce the canonical homogeneous-from-ones
sequence `η = M.homogeneousFromOnes` (built by strong recursion in
this file); apply `hConv` to the trivial IVP with constant-1 starts
to obtain `Tendsto η atTop (𝓝 1)`; then take limits in the
recurrence `η (n + k) = ∑ M.α j.succ · η (n + k − (j+1))` to
extract `1 = ∑ M.α j.succ`, i.e. `M.IsPreconsistent`. The Lean
proof side-steps Butcher's appeal to `thm:405A` (used in the textbook
to bound `η`); convergence directly forces `η m → 1` without
needing stability. -/
theorem LinearMultistepMethod.convergent_isPreconsistent
    {k : ℕ} (M : LinearMultistepMethod k)
    (hConv : M.IsConvergent) : M.IsPreconsistent := by
  -- Trivial IVP setup: y' = 0, y(0) = 1, x = 1, with constant-1 starts.
  set f : ℝ → ℝ → ℝ := fun _ _ => 0 with hf_def
  set yex : ℝ → ℝ := fun _ => 1 with hyex_def
  set start : ℝ → Fin k → ℝ := fun _ _ => 1 with hstart_def
  set Y : ℕ → ℕ → ℝ := fun _ n => M.homogeneousFromOnes n with hY_def
  -- Hypotheses for hConv.
  have hf_uncurry_const : Function.uncurry f = fun _ => (0 : ℝ) := by
    funext p; rfl
  have hf_cont : Continuous (Function.uncurry f) := by
    rw [hf_uncurry_const]; exact continuous_const
  have hf_lip : LipschitzWith 0 (Function.uncurry f) := by
    rw [hf_uncurry_const]; exact LipschitzWith.const _
  have hyex_x₀ : yex 0 = 1 := rfl
  have hyex_C1 : ContDiff ℝ 1 yex := contDiff_const
  have hyex_ode : ∀ x, HasDerivAt yex (f x (yex x)) x := by
    intro x; exact hasDerivAt_const x 1
  have hM_bound_nn : (0 : ℝ) ≤ 0 := le_refl 0
  have hf_yex_bound : ∀ t, |f t (yex t)| ≤ 0 := by
    intro t; simp [f]
  have hstart_tendsto : ∀ i : Fin k,
      Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds 1) := by
    intro _; exact tendsto_const_nhds
  have hxx : (0 : ℝ) < 1 := by norm_num
  have hY_props : ∀ m : ℕ, 0 < m →
      (∀ i : Fin k, Y m i.val = start ((1 - 0) / (m : ℝ)) i) ∧
      M.IsLMMSolution ((1 - 0) / (m : ℝ)) 0 f (Y m) := by
    intro m _
    refine ⟨?_, ?_⟩
    · intro i
      simp [Y, start, M.homogeneousFromOnes_lt_k i.val i.isLt]
    · -- IsLMMSolution at f = 0 reduces to IsHomogeneousSolution.
      rw [show f = (fun _ _ : ℝ => 0) from rfl, isLMMSolution_zero_iff]
      exact M.homogeneousFromOnes_isHomogeneousSolution
  -- Apply hConv to extract η m → 1.
  have hconv_tendsto :
      Filter.Tendsto (fun m : ℕ => Y m m - yex 1) Filter.atTop (nhds 0) := by
    refine hConv f hf_cont 0 hf_lip 0 1 yex hyex_x₀ hyex_C1 hyex_ode
      0 hM_bound_nn hf_yex_bound start hstart_tendsto 1 hxx Y hY_props
  have hη_tendsto :
      Filter.Tendsto M.homogeneousFromOnes Filter.atTop (nhds 1) := by
    have hsub_tendsto :
        Filter.Tendsto (fun m : ℕ => M.homogeneousFromOnes m - 1)
          Filter.atTop (nhds 0) := by
      simpa [Y, yex] using hconv_tendsto
    have hconst :
        Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    have hadd := hsub_tendsto.add hconst
    simpa using hadd
  -- Tendsto on shifted indices: for each j : Fin k, η (n + k - (j.val + 1)) → 1.
  have hη_shift : ∀ j : Fin k,
      Filter.Tendsto
        (fun n : ℕ => M.homogeneousFromOnes (n + k - (j.val + 1)))
        Filter.atTop (nhds 1) := by
    intro j
    refine hη_tendsto.comp ?_
    -- The shift function `n ↦ n + k - (j.val + 1)` tends to atTop.
    refine Filter.tendsto_atTop_mono (f := fun n : ℕ => n) (g := _) ?_
      Filter.tendsto_id
    intro n
    have hjk : j.val < k := j.isLt
    show n ≤ n + k - (j.val + 1)
    omega
  -- Combine the recurrence with the limits to conclude.
  have hrec_lhs :
      Filter.Tendsto
        (fun n : ℕ => M.homogeneousFromOnes (n + k))
        Filter.atTop (nhds 1) := by
    refine hη_tendsto.comp ?_
    refine Filter.tendsto_atTop_mono (f := fun n : ℕ => n) (g := _) ?_
      Filter.tendsto_id
    intro n; show n ≤ n + k; omega
  have hrec_eq : ∀ n : ℕ,
      M.homogeneousFromOnes (n + k) =
        ∑ j : Fin k, M.α j.succ *
          M.homogeneousFromOnes (n + k - (j.val + 1)) := by
    intro n
    exact M.homogeneousFromOnes_recurrence (n + k) (Nat.le_add_left k n)
  -- The RHS sequence tends to (∑ j, M.α j.succ).
  have hrec_rhs :
      Filter.Tendsto
        (fun n : ℕ => ∑ j : Fin k, M.α j.succ *
                        M.homogeneousFromOnes (n + k - (j.val + 1)))
        Filter.atTop (nhds (∑ j : Fin k, M.α j.succ)) := by
    have htarget : (∑ j : Fin k, M.α j.succ) =
        ∑ j : Fin k, M.α j.succ * (1 : ℝ) := by
      simp
    rw [htarget]
    refine tendsto_finset_sum _ ?_
    intro j _
    have h := (hη_shift j).const_mul (M.α j.succ)
    simpa using h
  -- LHS = RHS pointwise, so their limits agree: 1 = Σ M.α j.succ.
  have hrec_lhs_via_rhs :
      Filter.Tendsto
        (fun n : ℕ => ∑ j : Fin k, M.α j.succ *
                        M.homogeneousFromOnes (n + k - (j.val + 1)))
        Filter.atTop (nhds 1) := by
    refine (Filter.tendsto_congr ?_).mp hrec_lhs
    intro n; exact hrec_eq n
  have hunique : (1 : ℝ) = ∑ j : Fin k, M.α j.succ :=
    tendsto_nhds_unique hrec_lhs_via_rhs hrec_rhs
  exact hunique

/-- **Butcher Theorem 405C** (p. 344).  A convergent linear multistep
method is consistent.

Textbook proof sketch: convergence + `thm:405A` (stability) imply
`α_1 + 2α_2 + ⋯ + k α_k ≠ 0`.  Setting `η_i = i · (Σβ) / (Σ i α_i)`
and applying convergence to the trivial IVP `y' = 1, y(0) = 0` at
`x = 1` with starting values `η_i / n` forces
`Σ β_i = Σ i α_i`, the consistency identity (404b).  Combined with
`thm:405B` (preconsistency), this gives consistency.

**Faithfulness deviation (cycle 070).** The Lean proof side-steps
Butcher's appeal to `thm:405A` (stability, used in the textbook to
bound `T := α_1 + 2α_2 + ⋯ + k α_k` away from `0`).  Instead we do
a case split on whether `T = 0`:

* If `T = 0`, apply `hConv` to the trivial IVP `y' = 0, y(0) = 0`
  with `Y m n := n / m` (a homogeneous solution iff `T = 0`) and
  starts `start h i := i · h`.  Then `Y m m = 1` for `m > 0`, but
  `hConv` forces `Y m m → yex(1) = 0`, contradiction.  Hence
  `T = 0` is vacuous.
* If `T ≠ 0`, set `A := S / T` (where `S := Σ M.β i`) and
  `Y m n := A · n / m`.  By preconsistency, `Y` is an LMM solution
  of `y' = 1, y(0) = 0` with starts `start h i := A · i · h`.
  Convergence forces `Y m m = A → yex(1) = 1`, hence `A = 1`,
  hence `S = A · T = T`.

The conclusion (`SatisfiesEq404b`) matches Butcher's exactly; the
divergence is only in the proof — we don't need stability. -/
theorem LinearMultistepMethod.convergent_isConsistent
    {k : ℕ} (M : LinearMultistepMethod k)
    (hConv : M.IsConvergent) : M.IsConsistent := by
  have hPre : M.IsPreconsistent := M.convergent_isPreconsistent hConv
  refine ⟨hPre, ?_⟩
  -- Goal: M.SatisfiesEq404b, i.e. T = S where
  --   T := Σ_{i:Fin k} ((i.val:ℝ) + 1) * M.α i.succ
  --   S := Σ_{i:Fin (k+1)} M.β i
  unfold LinearMultistepMethod.SatisfiesEq404b
  set S : ℝ := ∑ i : Fin (k + 1), M.β i with hS_def
  set T : ℝ := ∑ i : Fin k, ((i.val : ℝ) + 1) * M.α i.succ with hT_def
  show T = S
  -- Algebraic helpers (preconsistency-driven sum identities).
  have hsum_α : (∑ i : Fin (k + 1), M.α i) = 0 := by
    rw [Fin.sum_univ_succ, M.α_zero]
    have hP : (1 : ℝ) = ∑ i : Fin k, M.α i.succ := hPre
    linarith
  have hsum_iα : (∑ i : Fin (k + 1), (i.val : ℝ) * M.α i) = T := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_add, Fin.val_succ]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  -- Core "linear LMM equation collapses to A·T = -RHS_constant" computation.
  -- For Y m n := A · n / m, the LMM-recurrence LHS at index n is
  --   Σ_{i:Fin (k+1)} M.α i · A · ((n+k - i.val : ℕ):ℝ) / (m:ℝ)
  --   = (A/m) · Σ M.α i · ((n+k - i.val : ℕ):ℝ)
  --   = (A/m) · ((n+k) · 0 - T)         [preconsistency + hsum_iα]
  --   = -A·T/m.
  -- The cast helper `((n+k - i.val : ℕ):ℝ) = (n+k:ℝ) - (i.val:ℝ)` requires
  -- `i.val ≤ n+k`, which follows from `i.val < k+1 ≤ n+k+1`.
  have hLHS_collapse : ∀ (A : ℝ) (m n : ℕ), 0 < m →
      (∑ i : Fin (k + 1),
          M.α i * (A * ((n + k - i.val : ℕ) : ℝ) / (m : ℝ))) = -A * T / m := by
    intro A m n _hm
    have hcast : ∀ i : Fin (k + 1),
        ((n + k - i.val : ℕ) : ℝ) = (n + k : ℝ) - (i.val : ℝ) := by
      intro i
      have hile : i.val ≤ n + k := by
        have := i.isLt
        omega
      rw [Nat.cast_sub hile]
      push_cast
      ring
    have hrewrite : ∀ i : Fin (k + 1),
        M.α i * (A * ((n + k - i.val : ℕ) : ℝ) / (m : ℝ)) =
          (A / m) * ((n + k : ℝ) * M.α i - (i.val : ℝ) * M.α i) := by
      intro i; rw [hcast i]; ring
    rw [Finset.sum_congr rfl (fun i _ => hrewrite i)]
    rw [← Finset.mul_sum]
    have hexpand : (∑ i : Fin (k + 1), ((n + k : ℝ) * M.α i - (i.val : ℝ) * M.α i)) =
        (n + k : ℝ) * (∑ i : Fin (k + 1), M.α i) -
          (∑ i : Fin (k + 1), (i.val : ℝ) * M.α i) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hexpand, hsum_α, hsum_iα]
    ring
  -- Case split on whether T = 0.
  by_cases hT_zero : T = 0
  · -- Case T = 0: derive contradiction via Y m n := n/m and trivial IVP y' = 0.
    exfalso
    set f : ℝ → ℝ → ℝ := fun _ _ => 0 with hf_def
    set yex : ℝ → ℝ := fun _ => 0 with hyex_def
    set start : ℝ → Fin k → ℝ := fun h i => (i.val : ℝ) * h with hstart_def
    set Y : ℕ → ℕ → ℝ := fun m n => (n : ℝ) / (m : ℝ) with hY_def
    have hf_uncurry_const : Function.uncurry f = fun _ => (0 : ℝ) := by
      funext p; rfl
    have hf_cont : Continuous (Function.uncurry f) := by
      rw [hf_uncurry_const]; exact continuous_const
    have hf_lip : LipschitzWith 0 (Function.uncurry f) := by
      rw [hf_uncurry_const]; exact LipschitzWith.const _
    have hyex_x₀ : yex 0 = 0 := rfl
    have hyex_C1 : ContDiff ℝ 1 yex := contDiff_const
    have hyex_ode : ∀ x, HasDerivAt yex (f x (yex x)) x := by
      intro x; exact hasDerivAt_const x 0
    have hM_bound_nn : (0 : ℝ) ≤ 0 := le_refl 0
    have hf_yex_bound : ∀ t, |f t (yex t)| ≤ 0 := by
      intro t; simp [f]
    have hstart_tendsto : ∀ i : Fin k,
        Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds 0) := by
      intro i
      have h1 : Filter.Tendsto (fun h : ℝ => (i.val : ℝ) * h) (nhds 0)
          (nhds ((i.val : ℝ) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa [start] using h1
    have hxx : (0 : ℝ) < 1 := by norm_num
    have hY_props : ∀ m : ℕ, 0 < m →
        (∀ i : Fin k, Y m i.val = start ((1 - 0) / (m : ℝ)) i) ∧
        M.IsLMMSolution ((1 - 0) / (m : ℝ)) 0 f (Y m) := by
      intro m hm
      refine ⟨?_, ?_⟩
      · intro i
        simp [Y, start]
        ring
      · -- f ≡ 0 ⇒ IsLMMSolution = IsHomogeneousSolution; verify recurrence.
        intro n
        -- Goal: Σ M.α i · Y m (n+k-i.val) = -((1-0)/m) * Σ M.β i * 0 = 0
        have hLHS := hLHS_collapse 1 m n hm
        simp only [hT_zero, mul_zero, zero_div] at hLHS
        -- hLHS : Σ M.α i · (1 · ((n+k-i.val:ℕ):ℝ) / m) = 0
        -- Rewrite Y m (n+k-i.val) = ((n+k-i.val:ℕ):ℝ) / m = 1 · ... / m
        have hY_eq : ∀ i : Fin (k + 1),
            Y m (n + k - i.val) =
              1 * ((n + k - i.val : ℕ) : ℝ) / (m : ℝ) := by
          intro i; simp [Y]
        simp_rw [hY_eq]
        rw [hLHS]
        simp [f]
    have hconv : Filter.Tendsto (fun m : ℕ => Y m m - yex 1)
                   Filter.atTop (nhds 0) := by
      refine hConv f hf_cont 0 hf_lip 0 0 yex hyex_x₀ hyex_C1 hyex_ode
        0 hM_bound_nn hf_yex_bound start hstart_tendsto 1 hxx Y hY_props
    -- Y m m - yex 1 = m/m - 0 = 1 (eventually); but the limit is 0. Contradiction.
    have hY_diff_eventually_one :
        ∀ᶠ m : ℕ in Filter.atTop, Y m m - yex 1 = 1 := by
      filter_upwards [Filter.eventually_gt_atTop 0] with m hm
      simp [Y, yex, ne_of_gt hm]
    have hconst :
        Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    have hconv_one : Filter.Tendsto (fun m : ℕ => Y m m - yex 1)
        Filter.atTop (nhds 1) := by
      refine (Filter.tendsto_congr' ?_).mpr hconst
      filter_upwards [hY_diff_eventually_one] with m hm
      exact hm
    exact absurd (tendsto_nhds_unique hconv hconv_one) (by norm_num)
  · -- Case T ≠ 0: use Y m n := (S/T) · n / m with f ≡ 1; hConv ⇒ S/T = 1.
    set A : ℝ := S / T with hA_def
    have hA_T : A * T = S := by
      rw [hA_def]; field_simp
    set f : ℝ → ℝ → ℝ := fun _ _ => 1 with hf_def
    set yex : ℝ → ℝ := fun t => t with hyex_def
    set start : ℝ → Fin k → ℝ := fun h i => A * (i.val : ℝ) * h with hstart_def
    set Y : ℕ → ℕ → ℝ := fun m n => A * (n : ℝ) / (m : ℝ) with hY_def
    have hf_uncurry_const : Function.uncurry f = fun _ => (1 : ℝ) := by
      funext p; rfl
    have hf_cont : Continuous (Function.uncurry f) := by
      rw [hf_uncurry_const]; exact continuous_const
    have hf_lip : LipschitzWith 0 (Function.uncurry f) := by
      rw [hf_uncurry_const]; exact LipschitzWith.const _
    have hyex_x₀ : yex 0 = 0 := rfl
    have hyex_C1 : ContDiff ℝ 1 yex := contDiff_id
    have hyex_ode : ∀ x, HasDerivAt yex (f x (yex x)) x := by
      intro x; exact hasDerivAt_id x
    have hM_bound_nn : (0 : ℝ) ≤ 1 := by norm_num
    have hf_yex_bound : ∀ t, |f t (yex t)| ≤ 1 := by
      intro t; simp [f]
    have hstart_tendsto : ∀ i : Fin k,
        Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds 0) := by
      intro i
      have h1 : Filter.Tendsto (fun h : ℝ => A * (i.val : ℝ) * h) (nhds 0)
          (nhds (A * (i.val : ℝ) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa [start] using h1
    have hxx : (0 : ℝ) < 1 := by norm_num
    have hY_props : ∀ m : ℕ, 0 < m →
        (∀ i : Fin k, Y m i.val = start ((1 - 0) / (m : ℝ)) i) ∧
        M.IsLMMSolution ((1 - 0) / (m : ℝ)) 0 f (Y m) := by
      intro m hm
      refine ⟨?_, ?_⟩
      · intro i
        simp [Y, start]; ring
      · intro n
        -- Goal: Σ M.α i · Y m (n+k-i.val) = -((1-0)/m) * Σ M.β i * f(...)(Y(...))
        have hLHS := hLHS_collapse A m n hm
        -- hLHS : Σ M.α i · (A · ((n+k-i.val:ℕ):ℝ) / m) = -A·T/m
        have hY_eq : ∀ i : Fin (k + 1),
            Y m (n + k - i.val) =
              A * ((n + k - i.val : ℕ) : ℝ) / (m : ℝ) := by
          intro i; simp [Y]
        simp_rw [hY_eq]
        rw [hLHS]
        -- Goal: -A·T/m = -((1-0)/m) * Σ M.β i * f(...)(...) where f ≡ 1
        have hf_eval : ∀ (x y : ℝ), f x y = 1 := fun _ _ => rfl
        simp_rw [hf_eval, mul_one]
        -- Goal: -A·T/m = -((1-0)/m) * S
        rw [show (-A * T / (m:ℝ)) = -(A * T) / (m:ℝ) from by ring, hA_T]
        ring
    have hconv : Filter.Tendsto (fun m : ℕ => Y m m - yex 1)
                   Filter.atTop (nhds 0) := by
      refine hConv f hf_cont 0 hf_lip 0 0 yex hyex_x₀ hyex_C1 hyex_ode
        1 hM_bound_nn hf_yex_bound start hstart_tendsto 1 hxx Y hY_props
    -- Y m m = A · m / m = A (eventually). yex 1 = 1.
    have hY_diff_eventually : ∀ᶠ m : ℕ in Filter.atTop,
        Y m m - yex 1 = A - 1 := by
      filter_upwards [Filter.eventually_gt_atTop 0] with m hm
      simp [Y, yex]
      field_simp [ne_of_gt hm]
    have hconst : Filter.Tendsto (fun _ : ℕ => A - 1)
        Filter.atTop (nhds (A - 1)) := tendsto_const_nhds
    have hconv_const : Filter.Tendsto (fun m : ℕ => Y m m - yex 1)
        Filter.atTop (nhds (A - 1)) := by
      refine (Filter.tendsto_congr' ?_).mpr hconst
      filter_upwards [hY_diff_eventually] with m hm
      exact hm
    have hA_minus_one_zero : A - 1 = 0 :=
      tendsto_nhds_unique hconv_const hconv
    have hA_eq_one : A = 1 := by linarith
    -- S = A · T = 1 · T = T, so T = S.
    have : S = T := by rw [← hA_T, hA_eq_one, one_mul]
    linarith

/-- **Butcher Theorem 243A** (p. 130).  A linear multistep method is
convergent if and only if it is stable and consistent.

This is the cross-chapter deferred theorem from §243.  The forward
direction (`⇐`) is cycle 068's
`LinearMultistepMethod.stable_consistent_isConvergent`.  The reverse
direction (`⇒`) splits into `convergent_isStable` (`thm:405A`) and
`convergent_isConsistent` (`thm:405C`).  Cycle 069 lands the iff
packager; the three reverse-direction lemmas remain as scaffold
sorries to be closed in followups. -/
theorem LinearMultistepMethod.isConvergent_iff_isStable_and_isConsistent
    {k : ℕ} (M : LinearMultistepMethod k) :
    M.IsConvergent ↔ M.IsStable ∧ M.IsConsistent :=
  ⟨fun hConv => ⟨M.convergent_isStable hConv,
                  M.convergent_isConsistent hConv⟩,
   fun ⟨hStable, hCons⟩ =>
     M.stable_consistent_isConvergent hStable hCons⟩

end OpenMath.Chapter4.Section404
