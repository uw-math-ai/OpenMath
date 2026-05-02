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

Cycle 070+ followup. -/
theorem LinearMultistepMethod.convergent_isConsistent
    {k : ℕ} (M : LinearMultistepMethod k)
    (hConv : M.IsConvergent) : M.IsConsistent := by
  sorry

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
