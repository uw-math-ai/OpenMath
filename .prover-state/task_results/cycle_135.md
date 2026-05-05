# Cycle 135 Results

## Worked on

Strengthened the `def:520E` (A-stability) non-vacuity story: added a
*substantive* A-stable witness `implicitMidpointGLM_isAStable` to
`OpenMath/Chapter5/Section520.lean`, complementing the cycle 088
trivial `trivialZeroGLM_isAStable` (`M(z) = 0`).

New declarations (all axiom-clean: `[propext, Classical.choice, Quot.sound]`):

* `implicitMidpointGLM_stabilityMatrix (z : ℂ) (hz : z.re ≤ 0) :
  M(z) = !![(1 + z/2) / (1 - z/2)]` — closed form on the closed left
  half-plane.
* `padeOneOne_norm_le_one_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) :
  ‖(1 + z/2)/(1 - z/2)‖ ≤ 1` — Padé(1,1) magnitude bound.
* `implicitMidpointGLM_isAStable : implicitMidpointGLM.IsAStable`
  — main A-stability witness.
* Three private 1×1 helpers: `fin_one_pow`, `norm_fin_one`,
  `norm_pow_fin_one` (bridge `‖!![a]^k‖ = ‖a‖^k`).

## Approach

Mirrored the cycles 133/134 substantive-witness pattern.

### Step 1 — closed-form stability matrix

`implicitMidpointGLM` has `A = !![1/2]`, `U = B = V = !![1]`, so

* `(1 - z·A) = !![1 - z/2]` (entrywise simp + `ring`).
* The matrix `(1 - z·A)` is non-singular for `Re(z) ≤ 0`: its single
  entry has real part `≥ 1`, hence is non-zero. A small auxiliary
  `(2 - z) ≠ 0` is needed for `field_simp` to clear all fractions.
* `Matrix.inv_subsingleton` (`Subsingleton (Fin 1)`) gives
  `(I - z·A)⁻¹ = diagonal (Ring.inverse ∘ A i i)`, so the `(0,0)` entry
  is `Ring.inverse (1 - z/2) = (1 - z/2)⁻¹` (`Ring.inverse_eq_inv`).
* Entrywise: `1 + z·(1 - z/2)⁻¹ = (1 + z/2)/(1 - z/2)` follows from
  `eq_div_iff hne` + `field_simp` + `ring`.

### Step 2 — Padé(1,1) magnitude bound

* Reduce `‖a/b‖ ≤ 1 ↔ ‖a‖ ≤ ‖b‖` via `norm_div` + `div_le_one`
  (using `‖1 - z/2‖ > 0`).
* Square both sides via `Complex.sq_norm`: it suffices to show
  `Complex.normSq (1 + z/2) ≤ Complex.normSq (1 - z/2)`.
* Compute real and imaginary parts of `1 ± z/2` directly via
  `Complex.add_re`, `Complex.sub_re`, `Complex.add_im`, `Complex.sub_im`
  (the simp normal form already inlines the `/2`).
* Expand `Complex.normSq_apply` to `re² + im²` and finish with
  `nlinarith` using `hz : z.re ≤ 0` plus standard `sq_nonneg` hints.
* Conclude `‖1+z/2‖ ≤ ‖1-z/2‖` via
  `(abs_le_of_sq_le_sq' h_sq_le (norm_nonneg _)).2`.

### Step 3 — main A-stability theorem

* The strategy's Backup-A "matrix-pow-norm bridge" was implementable as
  three short private helpers. `fin_one_pow` (5 LOC induction) shows
  `!![a]^k = !![a^k]`. `norm_fin_one` (2 LOC) shows
  `‖!![a]‖ = ‖a‖` via `Matrix.linfty_opNorm_def` + `simp`.
  `norm_pow_fin_one` then chains them: `‖!![a]^k‖ = ‖!![a^k]‖ =
  ‖a^k‖ = ‖a‖^k` (`norm_pow`).
* Main theorem then closes by `refine ⟨1, ?_⟩`, unfolding to
  `‖M(z)^k‖ ≤ 1`, applying the closed form, the norm bridge, and
  `pow_le_one₀` against the Padé bound.

## Result

SUCCESS — all three steps closed sorry-free. `lake build
OpenMath.Chapter5.Section520` succeeds; `#print axioms` on each new
public theorem returns the standard `[propext, Classical.choice,
Quot.sound]` triple.

## Faithfulness check

For each new theorem introduced this cycle:

* `implicitMidpointGLM_stabilityMatrix`
  - Entity ID: helper for `def:520A` (stabilityMatrix) applied to
    `implicitMidpointGLM`.
  - Lean statement: closed form `M(z) = !![(1+z/2)/(1-z/2)]` on the
    closed left half-plane `z.re ≤ 0`.
  - The `z.re ≤ 0` hypothesis is *not* in the textbook for the
    stability matrix's *definition* — it is needed only because our
    `Matrix.inv` returns junk-zero on singular matrices. Without the
    hypothesis the closed form would fail at `z = 2` (where
    `1 - z/2 = 0`). This matches the textbook's tacit "outside the
    spectrum of `A⁻¹`" caveat. Faithful.
* `padeOneOne_norm_le_one_of_re_nonpos`
  - Pure complex-arithmetic helper. Same content as the textbook's
    Möbius-transform calculation `|R(z)| ≤ 1 ↔ Re(z) ≤ 0` for the
    Padé(1,1) approximant.
  - Lean statement captures: same content (with closed left half-plane).
* `implicitMidpointGLM_isAStable`
  - Substantive non-vacuity witness for `def:520E`. The textbook
    explicitly highlights the implicit midpoint as the canonical
    A-stable single-stage method (cf. §351 / §520 discussion of
    Padé approximants).
  - Lean statement captures: same content.

For the private helpers (`fin_one_pow`, `norm_fin_one`,
`norm_pow_fin_one`): pure 1×1 matrix-norm bridges, no faithfulness
concern.

Tautology / identity / hypothesis-strength checks all pass:
* No theorem conclusion appears verbatim as a hypothesis.
* No proof is `exact h` style; each does real work
  (`stabilityMatrix` does matrix algebra, `padeOneOne_…` does complex
  arithmetic, `isAStable` chains them via the norm bridge).
* No hypothesis is stronger than required (`hz : z.re ≤ 0` is the
  literal A-stability domain).

## Dead ends

* First attempt at `implicitMidpointGLM_stabilityMatrix` used
  `Ring.inverse_eq_inv'` (the unapplied function form). The applied
  version `Ring.inverse_eq_inv` (no prime) is what's needed.
* First `field_simp` call after `eq_div_iff hne` partially cleared
  fractions but left `(2 - z)⁻¹` because field_simp didn't
  autodiscover `2 - z ≠ 0`. Adding an explicit `hne2 : (2 : ℂ) - z ≠ 0`
  via `(1 - z/2) = (2 - z)/2` rewriting let `field_simp` finish.
* Initial `norm_pow_fin_one` was an attempted single induction
  expanding `‖!![a]^(n+1)‖` directly. This conflated two things at
  once. Decomposing into `fin_one_pow` (matrix → scalar power),
  `norm_fin_one` (1×1 norm), and `norm_pow_fin_one` (chain) was 1/3
  the LOC and clearer.

## Discovery

* `Matrix.inv_subsingleton` is the right tool for inverting
  `Matrix (Fin 1) (Fin 1) α`: it exposes the diagonal-of-inverse
  form `A⁻¹ = diagonal (fun i => Ring.inverse (A i i))` on any
  `Subsingleton` index, removing the need to chase `Matrix.det_fin_one`
  / `Matrix.nonsing_inv_apply`.
* `Matrix.linfty_opNorm_def` simplifies trivially on `Fin 1` (the
  `Finset.univ.sup` over a singleton collapses, the inner sum has one
  term). Bare `simp` after `rw [Matrix.linfty_opNorm_def]` was enough
  for `‖!![a]‖ = ‖a‖`.
* `Complex.sub_re` / `Complex.add_re` / `Complex.sub_im` /
  `Complex.add_im` already simp-normalize `(1 ± z/2).re` and `.im`
  to `1 ± z.re/2` and `±z.im/2` respectively — no need to manually
  invoke `Complex.div_re` / `Complex.normSq_ofNat`.
* `(abs_le_of_sq_le_sq' h ha).2` is the cleanest way to lift
  `a^2 ≤ b^2` (with `0 ≤ b`) to `a ≤ b` on the real line.

## Suggested next approach

* Padé(1,1) order-2 stability: stretch goal from this cycle's strategy.
  Show `implicitMidpointGLM.HasStabilityOrder 2` by computing
  `Φ(exp z, z)` and applying `Complex.exp_sub_sum_range_isBigO_pow 3`.
  This is a natural follow-up that reuses the stability-matrix
  closed form.
* Negative A-stability witness: `¬ explicitEulerGLM.IsAStable` (the
  strategy's Backup-A direction). Picks a specific `z = -3` and uses
  `tendsto_pow_atTop_atTop_of_one_lt` to refute power-boundedness.
  Would round out the A-stability witness portfolio
  (positive trivial / positive substantive / negative).
* `lem:351A` (criteria for A-stability): would require defining the
  RK stability function `R(z) = 1 + z·b^T·(I - z·A)^{-1}·𝟙` for
  `RKTableau`, which doesn't yet exist. Would consume the new
  `Matrix.inv_subsingleton` recipe established here.
* The same recipe (closed-form stability matrix + norm bound + 1×1
  helpers) generalizes to any single-stage GLM. Could lift the helpers
  to a shared `Section520` infrastructure file if more witnesses are
  added.
