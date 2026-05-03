import OpenMath.Chapter5.Section512

/-!
# Butcher §513 — The necessity of stability (Theorem 513A)

This file scaffolds Butcher's Theorem 513A: a convergent general
linear method is stable. The textbook proof (Butcher 2008, p. 409)
runs the trivial IVP `y' = 0, y(0) = 0` with a carefully chosen
starting procedure that exposes the unboundedness of `‖V^n‖`,
contradicting convergence.

## Cycle 092 deliverable

* The scaffold of `GeneralLinearMethod.convergent_isStable` with a
  single top-level `sorry` — cycle 093 closes this from here using
  the line-by-line LMM template at
  `OpenMath/Chapter4/Section405.lean:101–227`.
* Manual ports of `runningMaxNorm` (Helper 1, four lemmas),
  `glmZeroIterate` and `glmZeroIterate_isGLMSolution` (Helper 3),
  and `glmZeroIterate_const_smul` (Helper 4).
* Signatures (with `sorry` bodies) of the two genuinely-loaded
  helpers `unit_vector_witness_of_not_stable` (Helper 2) and
  `unbounded_zero_iterate_contra` (Helper 5). These are deferred
  to cycle 093 per the cycle-092 strategy.

## Textbook statement (quoted from `entities/thm_513A.json`)

> A general linear method `(A, U, B, V)` is convergent only if it
> is stable.

## Proof strategy (Butcher §513)

> Suppose, on the contrary, that `{V^n : n = 1, 2, …}` is unbounded.
> There exists a sequence of vectors `w_1, w_2, …` with `‖w_n‖ = 1`
> such that `{V^n w_n}` is unbounded. Run the trivial IVP
> `y' = 0, y(0) = 0` with `n` steps of stepsize `h = 1/n`,
> approximating at `x = 1`. Convergence forces the approximations
> to converge to `u·0 = 0`. Use the starting approximation
> `φ(1/n) = (1/max_{i ≤ n} ‖V^i w_i‖) w_n`. Then `‖φ(1/n)‖ → 0`
> (denominator → ∞), and the result after `n` steps is
> `V^n φ(1/n) = (1/max...) V^n w_n` with norm
> `‖V^n φ(1/n)‖ = ‖V^n w_n‖ / max_{i ≤ n} ‖V^i w_i‖`. Infinitely
> many `n` make this ratio = 1 (whenever
> `‖V^n w_n‖ = max_{i ≤ n} ‖V^i w_i‖`), contradicting convergence
> to 0.
-/

namespace OpenMath.Chapter5.Section510

open Matrix
open scoped BigOperators Topology

/-! ### Helper 1 — `runningMaxNorm` family

Real-valued running maximum, used to rescale the unbounded sequence
`fun n => ‖V^n *ᵥ w n‖` so that its image under the GLM iteration
becomes a starting procedure φ that converges to zero.

Direct port of `LinearMultistepMethod.runningMaxAbs` from
`OpenMath/Chapter4/Section404.lean:5651–5719`, with `|y i|` replaced
by `z i` (we will only feed in nonneg sequences). -/

/-- Running maximum of a real-valued sequence. -/
def runningMaxNorm (z : ℕ → ℝ) : ℕ → ℝ
  | 0     => z 0
  | n + 1 => max (runningMaxNorm z n) (z (n + 1))

/-- The running maximum is monotone in `n`. -/
theorem runningMaxNorm_monotone (z : ℕ → ℝ) :
    Monotone (runningMaxNorm z) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

/-- `z n` is bounded above by the running maximum at index `n`. -/
theorem runningMaxNorm_ge (z : ℕ → ℝ) (n : ℕ) :
    z n ≤ runningMaxNorm z n := by
  cases n with
  | zero => exact le_refl _
  | succ n => exact le_max_right _ _

/-- If `z n` is unbounded above, the running maximum tends to ∞. -/
theorem runningMaxNorm_atTop_of_unbounded
    {z : ℕ → ℝ} (hz : ∀ C : ℝ, ∃ n, C < z n) :
    Filter.Tendsto (runningMaxNorm z) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.mpr ?_
  intro C
  obtain ⟨n₀, hn₀⟩ := hz C
  refine ⟨n₀, fun n hn => ?_⟩
  have hC_le : C ≤ z n₀ := le_of_lt hn₀
  have h_ge_at_n₀ : z n₀ ≤ runningMaxNorm z n₀ := runningMaxNorm_ge z n₀
  have h_mono : runningMaxNorm z n₀ ≤ runningMaxNorm z n :=
    runningMaxNorm_monotone z hn
  linarith

/-- Existence of arbitrarily-large *record* indices for an unbounded
nonneg sequence: `n` is a record if `z n = runningMaxNorm z n`
(the new value sets a fresh maximum). Mirrors
`runningMaxAbs_record_above`; uses `hz_nn` instead of `abs_nonneg`. -/
theorem runningMaxNorm_record_above
    {z : ℕ → ℝ} (hz_nn : ∀ n, 0 ≤ z n) (hz : ∀ C : ℝ, ∃ n, C < z n)
    (N : ℕ) :
    ∃ n, N ≤ n ∧ z n = runningMaxNorm z n := by
  obtain ⟨m, hm⟩ := hz (Max.max (runningMaxNorm z N)
      (∑ i ∈ Finset.range (N + 1), z i))
  obtain ⟨i, hi₁, hi₂⟩ : ∃ i ∈ Finset.range (m + 1),
      runningMaxNorm z m = z i := by
    have h_max : ∀ n, ∃ i ∈ Finset.range (n + 1),
        runningMaxNorm z n = z i := by
      intro n
      induction n with
      | zero => exact ⟨0, by norm_num, rfl⟩
      | succ n ih =>
          obtain ⟨j, hj_mem, hj_eq⟩ := ih
          rcases le_or_gt (z (n + 1)) (runningMaxNorm z n) with hcase | hcase
          · refine ⟨j, ?_, ?_⟩
            · simp [Finset.mem_range] at hj_mem ⊢
              omega
            · show runningMaxNorm z (n + 1) = z j
              show max (runningMaxNorm z n) (z (n + 1)) = z j
              rw [max_eq_left hcase]
              exact hj_eq
          · refine ⟨n + 1, ?_, ?_⟩
            · simp [Finset.mem_range]
            · show runningMaxNorm z (n + 1) = z (n + 1)
              show max (runningMaxNorm z n) (z (n + 1)) = z (n + 1)
              exact max_eq_right (le_of_lt hcase)
    exact h_max m
  by_cases hi₃ : i ≤ N
  · exfalso
    have hsum : z i ≤ ∑ j ∈ Finset.range (N + 1), z j := by
      refine Finset.single_le_sum (f := fun j => z j)
        (fun j _ => hz_nn j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi₃))
    have h_le : runningMaxNorm z m ≤ ∑ j ∈ Finset.range (N + 1), z j := by
      rw [hi₂]; exact hsum
    have h_lt : runningMaxNorm z m < z m := by
      have := lt_of_le_of_lt h_le (lt_of_le_of_lt (le_max_right _ _) hm)
      exact this
    have hge : z m ≤ runningMaxNorm z m := runningMaxNorm_ge z m
    linarith
  · refine ⟨i, le_of_not_ge hi₃, ?_⟩
    refine le_antisymm (runningMaxNorm_ge z i) ?_
    have him : i ≤ m := by
      have := Finset.mem_range.mp hi₁
      omega
    have h_mono : runningMaxNorm z i ≤ runningMaxNorm z m :=
      runningMaxNorm_monotone z him
    rw [hi₂] at h_mono
    -- h_mono : runningMaxNorm z i ≤ z i
    exact h_mono

/-! ### Helper 3 — `glmZeroIterate`

For the trivial autonomous RHS `f ≡ 0`, the GLM iteration recurrence
collapses to the homogeneous V-recurrence (cf. `isGLMSolution_zero_iff`
in `Section512.lean`). The pure-`V` iterate `y_seq n := V^n *ᵥ y₀` is
therefore a GLM iteration of `M` for any starting vector `y₀`. -/

/-- The pure-`V` iterate from a starting vector `y₀`: the value at
step `n` is `V^n *ᵥ y₀`. -/
def GeneralLinearMethod.glmZeroIterate {s r : ℕ}
    (M : GeneralLinearMethod s r) (y₀ : Fin r → ℝ) (n : ℕ) :
    Fin r → ℝ :=
  (M.V ^ n) *ᵥ y₀

/-- The pure-`V` iterate is a GLM iteration of `M` at any stepsize for
the trivial autonomous RHS `f ≡ 0`. -/
theorem GeneralLinearMethod.glmZeroIterate_isGLMSolution {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (y₀ : Fin r → ℝ) :
    M.IsGLMSolution h (fun _ => 0) (M.glmZeroIterate y₀) := by
  rw [isGLMSolution_zero_iff]
  intro n i
  show ((M.V ^ (n + 1)) *ᵥ y₀) i = ∑ j, M.V i j * ((M.V ^ n) *ᵥ y₀) j
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  rfl

/-! ### Helper 4 — closure under scalar multiplication

The pure-`V` iterate is linear: scaling `y₀` by `c` scales the
iterate by `c`, and the result is still a GLM iteration. This is the
GLM analog of `IsHomogeneousSolution.const_smul` from Section404. -/

/-- Scalar multiples of the pure-`V` iterate are GLM iterations. -/
theorem GeneralLinearMethod.glmZeroIterate_const_smul {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (y₀ : Fin r → ℝ) (c : ℝ) :
    M.IsGLMSolution h (fun _ => 0)
      (fun n i => c * (M.glmZeroIterate y₀ n) i) := by
  rw [isGLMSolution_zero_iff]
  intro n i
  have hrec :=
    (isGLMSolution_zero_iff M h _).mp (M.glmZeroIterate_isGLMSolution h y₀) n i
  show c * (M.glmZeroIterate y₀ (n + 1)) i =
        ∑ j, M.V i j * (c * (M.glmZeroIterate y₀ n) j)
  rw [hrec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ### Helper 2 — unit-norm witness extractor (deferred to cycle 093)

From `¬ M.IsStable` (i.e. `∀ C, ∃ n, C < ‖V^n‖`), extract a sequence
`w : ℕ → Fin r → ℝ` with `‖w n‖ ≤ 1` and `‖V^n *ᵥ w n‖` unbounded.

**Construction (cycle 093):** for each `n`, the linfty operator norm
`‖V^n‖` equals `Finset.univ.sup' ⟨0, …⟩ (fun i => ∑ j, |((V^n) i j)|)`.
Pick the row `i_n : Fin r` realising the sup; set
`w n j := SignType.sign ((V^n) i_n j)` (cast as `±1`). Then
`((V^n) *ᵥ w n) i_n = ∑_j (V^n) i_n j · sign(...) = ∑_j |(V^n) i_n j| = ‖V^n‖`,
so `‖V^n *ᵥ w n‖ ≥ ‖V^n‖` is unbounded. The bound `‖w n‖ ≤ 1` follows
from each entry being in `{-1, 0, +1}`. -/

/-- Given `¬ M.IsStable`, produce a unit-bounded sequence `w` whose
images `(M.V^n) *ᵥ w n` are unbounded in norm. -/
theorem GeneralLinearMethod.unit_vector_witness_of_not_stable
    {s r : ℕ} {M : GeneralLinearMethod s r} (_h_ns : ¬ M.IsStable) :
    ∃ w : ℕ → Fin r → ℝ,
      (∀ n, ‖w n‖ ≤ 1) ∧
      (∀ C : ℝ, ∃ n, C < ‖(M.V ^ n) *ᵥ w n‖) := by
  -- TODO (cycle 093): construct via the row-realiser of `‖V^n‖`
  -- (linfty operator norm). See file docstring above.
  sorry

/-! ### Helper 5 — record-index contradiction (deferred to cycle 093)

If the rescaled sequence `‖V^n *ᵥ w n‖ / runningMaxNorm (...) n`
tends to zero, but `‖V^n *ᵥ w n‖` is unbounded, the record-index
argument provides infinitely many `n` at which the ratio equals `1`,
contradicting convergence to `0`. -/

/-- Vector-valued analog of
`LinearMultistepMethod.unbounded_homogeneous_contra`: from the
unbounded sequence `‖V^n *ᵥ w n‖` and the convergence of its
record-rescaled ratio to zero, derive `False`. -/
theorem GeneralLinearMethod.unbounded_zero_iterate_contra
    {s r : ℕ} {M : GeneralLinearMethod s r}
    {w : ℕ → Fin r → ℝ}
    (_hw_unit : ∀ n, ‖w n‖ ≤ 1)
    (_hw_unbd : ∀ C : ℝ, ∃ n, C < ‖(M.V ^ n) *ᵥ w n‖)
    (_hY : Filter.Tendsto
            (fun n : ℕ => ‖(M.V ^ n) *ᵥ w n‖ /
                            runningMaxNorm
                              (fun i => ‖(M.V ^ i) *ᵥ w i‖) n)
            Filter.atTop (nhds 0)) :
    False := by
  -- TODO (cycle 093): record-index argument analogous to
  -- `unbounded_homogeneous_contra` in Section404.lean.
  sorry

/-! ### Main theorem: `thm:513A` (scaffold)

The textbook proof requires the sub-helpers above. Cycle 092 lands
the scaffold (extracting `u`, the unit-vector witness, and the
trivial-IVP setup); cycle 093 will close the contradiction by
constructing the start procedure
`φ(1/n) := (1/runningMaxNorm ...) · w n` and applying
`unbounded_zero_iterate_contra`. -/

/-- **Butcher Theorem 513A** (p. 409) — A convergent general linear
method is stable. -/
theorem GeneralLinearMethod.convergent_isStable
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (hConv : M.IsConvergent) : M.IsStable := by
  by_contra h_ns
  -- Step 1: extract unit-vector witness sequence.
  obtain ⟨w, hw_unit, hw_unbd⟩ :=
    GeneralLinearMethod.unit_vector_witness_of_not_stable h_ns
  -- Step 2: trivial IVP setup (f ≡ 0, x₀ = 0, y₀ = 0, yex ≡ 0).
  set f : ℝ → ℝ := fun _ => 0 with hf_def
  set yex : ℝ → ℝ := fun _ => 0 with hyex_def
  have hf_lip : LipschitzWith 0 f := by
    rw [hf_def]; exact LipschitzWith.const _
  have hyex_x₀ : yex 0 = 0 := rfl
  have hyex_ode : ∀ x : ℝ, HasDerivAt yex (f (yex x)) x := by
    intro x
    rw [hyex_def, hf_def]
    exact hasDerivAt_const x 0
  -- Step 3: extract u from hConv (applied to trivial IVP).
  obtain ⟨u, hu_ne, hConv'⟩ :=
    hConv f 0 hf_lip 0 0 yex hyex_x₀ hyex_ode
  -- TODO (cycle 093): construct φ(1/n) := (1/runningMaxNorm) · w n,
  -- the rescaled iterate Y, apply hConv', and close via
  -- `unbounded_zero_iterate_contra`. See LMM template at
  -- `OpenMath/Chapter4/Section405.lean:101–227`.
  sorry

end OpenMath.Chapter5.Section510
