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
open scoped BigOperators Topology Matrix.Norms.Operator

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
images `(M.V^n) *ᵥ w n` are unbounded in norm.

**Construction (Aristotle, cycle 093):** the contrapositive form
"if no unit-norm w gives unbounded images then `‖V^n‖` is bounded"
is proved by applying the negated hypothesis to the family of standard
basis vectors `e_i = fun j => if j = i then 1 else 0` (each has Pi
linfty norm 1). The resulting per-`i` bounds `C_i` sum to a global
bound on `‖V^n‖` via the linfty operator norm row-sum inequality
`sup_b ∑_j ‖A b j‖₊ ≤ ∑_j sup_b ‖A b j‖₊`. -/
theorem GeneralLinearMethod.unit_vector_witness_of_not_stable
    {s r : ℕ} {M : GeneralLinearMethod s r} (h_ns : ¬ M.IsStable) :
    ∃ w : ℕ → Fin r → ℝ,
      (∀ n, ‖w n‖ ≤ 1) ∧
      (∀ C : ℝ, ∃ n, C < ‖(M.V ^ n) *ᵥ w n‖) := by
  -- Step 1: convert `¬ IsStable` to the unbounded-`‖V^n‖` form.
  have h_unbd : ∀ C : ℝ, ∃ n, C < ‖M.V ^ n‖ := by
    intro C
    by_contra h
    push_neg at h
    exact h_ns ⟨C, fun n => h n⟩
  -- Step 2: contrapositive — assume no unit-norm w gives unbounded
  -- images, derive a global bound on `‖V^n‖`, contradicting `h_unbd`.
  contrapose! h_unbd
  -- Now `h_unbd : ∀ w, (∀ n, ‖w n‖ ≤ 1) → ∃ C, ∀ n, ‖V^n *ᵥ w n‖ ≤ C`,
  -- and the goal is `∃ C, ∀ n, ‖V^n‖ ≤ C`.
  -- Apply h_unbd to the constant sequence `fun n => e_i` for each i.
  have h_basis : ∀ i : Fin r, ∃ C, ∀ n,
      ‖(M.V ^ n) *ᵥ (fun j : Fin r => if j = i then (1:ℝ) else 0)‖ ≤ C := by
    intro i
    refine h_unbd (fun _ : ℕ => fun j : Fin r => if j = i then (1:ℝ) else 0) ?_
    intro n
    rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro j
    show ‖(if j = i then (1:ℝ) else 0)‖ ≤ 1
    split_ifs <;> simp
  choose C hC using h_basis
  refine ⟨∑ i, C i, fun n => ?_⟩
  -- Goal: ‖V^n‖ ≤ ∑ i, C i.
  refine le_trans ?_ (Finset.sum_le_sum (fun i _ => hC i n))
  -- Goal: ‖V^n‖ ≤ ∑ i, ‖V^n *ᵥ e_i‖.
  -- Helper: (V^n *ᵥ e_i) b = V^n b i.
  have h_e_apply : ∀ i b : Fin r,
      (M.V ^ n *ᵥ (fun j : Fin r => if j = i then (1:ℝ) else 0)) b = (M.V ^ n) b i := by
    intro i b
    simp [Matrix.mulVec, dotProduct, Finset.sum_ite_eq']
  -- Bound: |V^n b i| ≤ ‖V^n *ᵥ e_i‖ via the Pi norm.
  have h_col_bound : ∀ i b : Fin r,
      ‖(M.V ^ n) b i‖₊ ≤ ‖(M.V ^ n) *ᵥ (fun j : Fin r => if j = i then (1:ℝ) else 0)‖₊ := by
    intro i b
    have h := nnnorm_le_pi_nnnorm (M.V ^ n *ᵥ (fun j : Fin r => if j = i then (1:ℝ) else 0)) b
    rwa [h_e_apply i b] at h
  -- Bound at the NNReal level: ‖V^n‖₊ ≤ ∑ i, ‖V^n *ᵥ e_i‖₊.
  have h_nnreal :
      ‖M.V ^ n‖₊ ≤
      ∑ i : Fin r, ‖(M.V ^ n) *ᵥ (fun j : Fin r => if j = i then (1:ℝ) else 0)‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le (fun b _ => ?_)
    refine Finset.sum_le_sum (fun j _ => ?_)
    exact h_col_bound j b
  -- Cast to ℝ.
  have := (NNReal.coe_le_coe.mpr h_nnreal)
  push_cast at this
  exact this

/-! ### Helper 5 — record-index contradiction (deferred to cycle 093)

If the rescaled sequence `‖V^n *ᵥ w n‖ / runningMaxNorm (...) n`
tends to zero, but `‖V^n *ᵥ w n‖` is unbounded, the record-index
argument provides infinitely many `n` at which the ratio equals `1`,
contradicting convergence to `0`. -/

/-- Vector-valued analog of
`LinearMultistepMethod.unbounded_homogeneous_contra`: from the
unbounded sequence `‖V^n *ᵥ w n‖` and the convergence of its
record-rescaled ratio to zero, derive `False`.

**Proof (Aristotle, cycle 093):** by `runningMaxNorm_record_above`,
record indices exist beyond any threshold; at a record `n`, the
ratio equals `1`, contradicting convergence to `0`. We pick `n`
beyond both the convergence threshold and a `runningMaxNorm > 0`
threshold, then derive `False` from `1 < 1/2`. -/
theorem GeneralLinearMethod.unbounded_zero_iterate_contra
    {s r : ℕ} {M : GeneralLinearMethod s r}
    {w : ℕ → Fin r → ℝ}
    (_hw_unit : ∀ n, ‖w n‖ ≤ 1)
    (hw_unbd : ∀ C : ℝ, ∃ n, C < ‖(M.V ^ n) *ᵥ w n‖)
    (hY : Filter.Tendsto
            (fun n : ℕ => ‖(M.V ^ n) *ᵥ w n‖ /
                            runningMaxNorm
                              (fun i => ‖(M.V ^ i) *ᵥ w i‖) n)
            Filter.atTop (nhds 0)) :
    False := by
  set z : ℕ → ℝ := fun n => ‖(M.V ^ n) *ᵥ w n‖ with hz_def
  have hz_nn : ∀ n, 0 ≤ z n := fun n => norm_nonneg _
  -- Record indices exist beyond any N.
  have h_record : ∀ N : ℕ, ∃ n, N ≤ n ∧ z n = runningMaxNorm z n :=
    fun N => runningMaxNorm_record_above hz_nn hw_unbd N
  -- For sufficiently large n, runningMaxNorm z n > 0.
  have h_pos : ∃ N₀ : ℕ, ∀ n ≥ N₀, 0 < runningMaxNorm z n := by
    obtain ⟨N₀, hN₀⟩ := hw_unbd 0
    refine ⟨N₀, fun n hn => ?_⟩
    have h₁ : z N₀ ≤ runningMaxNorm z N₀ := runningMaxNorm_ge z N₀
    have h₂ : runningMaxNorm z N₀ ≤ runningMaxNorm z n := runningMaxNorm_monotone z hn
    linarith
  obtain ⟨N₀, hN₀⟩ := h_pos
  -- Threshold beyond which the ratio is < 1/2.
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hY (1 / 2 : ℝ) (by norm_num)
  -- Find a record index ≥ max N₀ N₁.
  obtain ⟨n, hn_ge, hn_record⟩ := h_record (Max.max N₀ N₁)
  have hN₀_at : 0 < runningMaxNorm z n :=
    hN₀ n (le_trans (le_max_left _ _) hn_ge)
  have hN₁_at := hN₁ n (le_trans (le_max_right _ _) hn_ge)
  -- At a record index, z n / runningMaxNorm z n = 1, contradicting < 1/2.
  have hzn : z n = ‖M.V ^ n *ᵥ w n‖ := rfl
  rw [Real.dist_eq, sub_zero] at hN₁_at
  rw [← hzn, hn_record, div_self hN₀_at.ne'] at hN₁_at
  norm_num at hN₁_at

/-! ### Main theorem: `thm:513A`

Butcher's textbook proof: assuming `¬ IsStable`, extract via Helper 2 a
unit-bounded sequence `w n` whose images `‖V^n *ᵥ w n‖` are unbounded.
Run the trivial IVP `y' = 0, y(0) = 0` with starting procedure
`φ(h) = (1 / ζ ⌈1/h⌉₊) · w ⌈1/h⌉₊` (where `ζ` is the running maximum
of `‖V^n *ᵥ w n‖`) and rescaled iterates `Y m n = (1/ζ m) · (V^n *ᵥ w m)`.
Convergence forces `‖Y n n‖ = z n / ζ n → 0`, but Helper 5 (record-index
contradiction) shows `z n / ζ n = 1` for infinitely many `n` — `False`. -/

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
  obtain ⟨u, _hu_ne, hConv'⟩ :=
    hConv f 0 hf_lip 0 0 yex hyex_x₀ hyex_ode
  -- Step 4: define z, ζ, the start procedure, and the rescaled iterates.
  set z : ℕ → ℝ := fun n => ‖(M.V ^ n) *ᵥ w n‖ with hz_def
  set ζ : ℕ → ℝ := runningMaxNorm z with hζ_def
  have hz_nn : ∀ n, 0 ≤ z n := fun n => norm_nonneg _
  have hζ_nn : ∀ n, 0 ≤ ζ n := fun n => le_trans (hz_nn n) (runningMaxNorm_ge z n)
  have hζ_atTop : Filter.Tendsto ζ Filter.atTop Filter.atTop :=
    runningMaxNorm_atTop_of_unbounded hw_unbd
  set start : ℝ → Fin r → ℝ := fun h i =>
    if 0 < h then ((1:ℝ) / ζ ⌈(1:ℝ)/h⌉₊) * w ⌈(1:ℝ)/h⌉₊ i else 0 with hstart_def
  set Y : ℕ → ℕ → Fin r → ℝ := fun m n i =>
    ((1:ℝ) / ζ m) * ((M.V ^ n *ᵥ w m) i) with hY_def
  -- Step 5: `start h i → 0` as `h → 0`.
  have hstart_tendsto : ∀ i : Fin r,
      Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds (u i * yex 0)) := by
    intro i
    rw [show u i * yex 0 = 0 from by rw [hyex_def]; ring]
    -- Right tail: 0 < h.
    have h_inv : Filter.Tendsto (fun h : ℝ => (1 : ℝ) / h)
        (𝓝[>] (0 : ℝ)) Filter.atTop := by
      have h_eq : (fun h : ℝ => (1 : ℝ) / h) = fun h : ℝ => h⁻¹ := by
        funext h; rw [one_div]
      rw [h_eq]; exact tendsto_inv_nhdsGT_zero
    have h_ceil : Filter.Tendsto
        (fun h : ℝ => (⌈(1 : ℝ) / h⌉₊ : ℕ))
        (𝓝[>] (0 : ℝ)) Filter.atTop :=
      tendsto_nat_ceil_atTop.comp h_inv
    have h_zeta : Filter.Tendsto
        (fun h : ℝ => ζ (⌈(1 : ℝ) / h⌉₊))
        (𝓝[>] (0 : ℝ)) Filter.atTop :=
      hζ_atTop.comp h_ceil
    have h_inv_zeta : Filter.Tendsto
        (fun h : ℝ => (1 : ℝ) / ζ (⌈(1 : ℝ) / h⌉₊))
        (𝓝[>] (0 : ℝ)) (nhds 0) :=
      h_zeta.const_div_atTop _
    have h_right : Filter.Tendsto (fun h : ℝ => start h i)
        (𝓝[>] (0 : ℝ)) (nhds 0) := by
      refine squeeze_zero_norm' (a := fun h : ℝ => 1 / ζ ⌈(1:ℝ)/h⌉₊) ?_ h_inv_zeta
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh_pos : (0 : ℝ) < h := hh
      have hstart_eq : start h i = (1 / ζ ⌈(1:ℝ)/h⌉₊) * w ⌈(1:ℝ)/h⌉₊ i := by
        simp only [hstart_def, if_pos hh_pos]
      rw [hstart_eq, Real.norm_eq_abs, abs_mul]
      have hw_bd : |w ⌈(1:ℝ)/h⌉₊ i| ≤ 1 := by
        have h₁ : ‖w ⌈(1:ℝ)/h⌉₊ i‖ ≤ ‖w ⌈(1:ℝ)/h⌉₊‖ := norm_le_pi_norm _ i
        have h₂ : ‖w ⌈(1:ℝ)/h⌉₊‖ ≤ 1 := hw_unit _
        simpa [Real.norm_eq_abs] using le_trans h₁ h₂
      have hinv_nn : 0 ≤ 1 / ζ ⌈(1:ℝ)/h⌉₊ :=
        div_nonneg (by norm_num) (hζ_nn _)
      have habs : |(1 : ℝ) / ζ ⌈(1:ℝ)/h⌉₊| = 1 / ζ ⌈(1:ℝ)/h⌉₊ := abs_of_nonneg hinv_nn
      rw [habs]
      calc (1 / ζ ⌈(1:ℝ)/h⌉₊) * |w ⌈(1:ℝ)/h⌉₊ i|
          ≤ (1 / ζ ⌈(1:ℝ)/h⌉₊) * 1 :=
            mul_le_mul_of_nonneg_left hw_bd hinv_nn
        _ = 1 / ζ ⌈(1:ℝ)/h⌉₊ := by ring
    -- Left tail: h ≤ 0 ⇒ start h i = 0.
    have h_left : Filter.Tendsto (fun h : ℝ => start h i)
        (𝓝[≤] (0 : ℝ)) (nhds 0) := by
      refine (Filter.tendsto_congr' ?_).mpr tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh' : ¬ (0 : ℝ) < h := not_lt.mpr hh
      show start h i = 0
      simp only [hstart_def, if_neg hh']
    have h_combined : Filter.Tendsto (fun h : ℝ => start h i)
        (𝓝[≤] (0 : ℝ) ⊔ 𝓝[>] (0 : ℝ)) (nhds 0) :=
      h_left.sup h_right
    rwa [nhdsLE_sup_nhdsGT] at h_combined
  -- Step 6: Y m matches start (1/m) initially and is a GLM solution.
  have hxx : (0 : ℝ) < 1 := by norm_num
  have hY_props : ∀ m : ℕ, 0 < m →
      Y m 0 = start ((1 - 0) / (m : ℝ)) ∧
      M.IsGLMSolution ((1 - 0) / (m : ℝ)) f (Y m) := by
    intro m hm
    have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hm_real_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_real_pos
    refine ⟨?_, ?_⟩
    · funext i
      have hh_pos : (0 : ℝ) < 1 / (m : ℝ) := by positivity
      have hh_eq : (1 - 0 : ℝ) / m = 1 / m := by ring
      have h11 : (1 : ℝ) / (1 / m) = m := one_div_one_div _
      have hceil : ⌈((m : ℝ))⌉₊ = m := Nat.ceil_natCast m
      show Y m 0 i = start ((1 - 0) / (m : ℝ)) i
      have hY0 : Y m 0 i = (1 / ζ m) * w m i := by
        show (1 / ζ m) * ((M.V ^ 0 *ᵥ w m) i) = (1 / ζ m) * w m i
        rw [pow_zero, Matrix.one_mulVec]
      rw [hY0, hh_eq]
      show (1 / ζ m) * w m i =
            (if 0 < 1 / (m : ℝ) then
              (1 / ζ ⌈(1:ℝ)/(1/(m:ℝ))⌉₊) * w ⌈(1:ℝ)/(1/(m:ℝ))⌉₊ i else 0)
      rw [if_pos hh_pos, h11, hceil]
    · -- M.IsGLMSolution (1/m) f (Y m).
      have hh_eq : (1 - 0 : ℝ) / m = 1 / m := by ring
      rw [hh_eq, hf_def]
      -- Apply glmZeroIterate_const_smul.
      have hY_alt :
          (fun n i => (1 / ζ m) * (M.glmZeroIterate (w m) n) i) = Y m := by
        funext n i
        show (1 / ζ m) * ((M.V ^ n) *ᵥ w m) i =
              (1 / ζ m) * ((M.V ^ n) *ᵥ w m) i
        rfl
      rw [← hY_alt]
      exact M.glmZeroIterate_const_smul (1 / (m : ℝ)) (w m) (1 / ζ m)
  -- Step 7: apply hConv' to obtain `Y n n → fun i => u i * yex 1 = 0`.
  have hconv : Filter.Tendsto (fun n : ℕ => Y n n)
                 Filter.atTop (nhds (fun i => u i * yex 1)) :=
    hConv' start hstart_tendsto 1 hxx Y hY_props
  -- yex 1 = 0, so the limit is the zero vector.
  have h_zero_fn : (fun i : Fin r => u i * yex 1) = (fun _ : Fin r => (0 : ℝ)) := by
    funext i; rw [hyex_def]; ring
  rw [h_zero_fn] at hconv
  -- Step 8: take norms, both sides → 0.
  have hconv_norm : Filter.Tendsto (fun n : ℕ => ‖Y n n‖) Filter.atTop (nhds 0) := by
    have h := hconv.norm
    have hzero : ‖(fun _ : Fin r => (0:ℝ))‖ = 0 := by
      simp [Pi.norm_def]
    rw [hzero] at h
    exact h
  -- Step 9: ‖Y n n‖ = z n / ζ n via norm_smul.
  have h_norm_eq : ∀ n, ‖Y n n‖ = z n / ζ n := by
    intro n
    show ‖(fun i => (1 / ζ n) * (M.V ^ n *ᵥ w n) i)‖ = z n / ζ n
    have h_smul_eq : (fun i => (1 / ζ n) * (M.V ^ n *ᵥ w n) i) =
                     (1 / ζ n) • (M.V ^ n *ᵥ w n) := by
      funext i; show (1 / ζ n) * (M.V ^ n *ᵥ w n) i = (1 / ζ n) • (M.V ^ n *ᵥ w n) i
      rfl
    rw [h_smul_eq, norm_smul]
    show ‖(1 / ζ n)‖ * ‖M.V ^ n *ᵥ w n‖ = z n / ζ n
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by norm_num) (hζ_nn n))]
    show (1 / ζ n) * z n = z n / ζ n
    field_simp
  rw [Filter.tendsto_congr h_norm_eq] at hconv_norm
  -- Step 10: apply Helper 5.
  exact M.unbounded_zero_iterate_contra hw_unit hw_unbd hconv_norm

end OpenMath.Chapter5.Section510
