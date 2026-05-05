# Cycle 142 Results

## Worked on

Substantive **positive** L-stability witness for `def:520F`: backward
Euler GLM. Specifically:

* `backwardEulerGLM` definition added to `OpenMath/Chapter5/Section510.lean`
  (`(s, r) = (1, 1)`; `A = U = B = V = !![1]`).
* `backwardEulerGLM_stabilityMatrix` closed form `M(z) = !![1/(1-z)]`
  (hypothesis `z ≠ 1`).
* `padeZeroOne_norm_le_one_of_re_nonpos`: `‖1/(1-z)‖ ≤ 1` for
  `Re(z) ≤ 0`.
* `backwardEulerGLM_isAStable`: A-stability witness.
* `norm_one_div_sub_tendsto_zero_cocompact`: private helper, the
  cocompact-limit core.
* `backwardEulerGLM_isLStable`: full L-stability witness — *the
  canonical positive substantive witness* and final corner of the
  4-corner coverage matrix.

## Approach

Followed the planner strategy verbatim, mirroring the cycle 135
`implicitMidpointGLM_isAStable` template for steps 1–4:

* **Step 1 (def)**: Added next to `implicitMidpointGLM` in Section510.
* **Step 2 (closed-form M(z))**: Used `Matrix.inv_subsingleton` to
  invert the `1×1` matrix `!![1 - z]`, then `field_simp; ring` to
  reduce `1 + z(1-z)⁻¹ = (1-z)⁻¹`. Initial `eq_div_iff` plan didn't
  fire (post-`simp` goal had `(·)⁻¹`, not `_/_`); switched to
  `field_simp; ring` and it closed.
* **Step 3 (magnitude bound)**: Squared form via `Complex.normSq_apply`
  + `nlinarith` (using `(z.im)²` non-negativity). Identical structure
  to cycle-135's `padeOneOne_norm_le_one_of_re_nonpos`.
* **Step 4 (A-stability)**: Bridge `Re(z) ≤ 0 ⇒ z ≠ 1` (via `(1:ℂ).re = 1`),
  then standard `pow_le_one₀ (norm_nonneg _) (padeZeroOne_norm_…)`.
* **Step 5 (L-stability cocompact)**:
  - Found `tendsto_norm_cocompact_atTop` via `lean_loogle`
    (`SeminormedAddGroup E + ProperSpace E`).
  - Built private helper
    `norm_one_div_sub_tendsto_zero_cocompact` using
    `squeeze_zero'`: bound `‖1/(1-z)‖ ≤ 1/(‖z‖ - 1)` eventually on
    `‖z‖ > 1` via reverse triangle (`norm_sub_norm_le z 1` +
    `‖1‖ = 1`) and `Filter.Tendsto.inv_tendsto_atTop` to push
    `1/(r-1) → 0` as `r → ∞`.
  - For the spectral-radius bridge to scalar norm, used the
    cycle-137 private helper `spectralRadius_fin_one` (in scope) and
    converted the `ENNReal`-valued `Tendsto` to `ℝ` via
    `ENNReal.tendsto_coe` then `NNReal.tendsto_coe`.

No Aristotle submissions (per planner — too small a problem; manual
is faster). No `maxHeartbeats` change. No new axioms. No `sorry`.

## Result

**SUCCESS** — all 5 steps closed.

Verification gates (all green):

* `grep -rn '\bsorry\b' --include='*.lean' OpenMath/`: only doc-comment
  references; **no actual `sorry` introduced**.
* `lake env lean OpenMath/Chapter5/Section510.lean` and
  `lake env lean OpenMath/Chapter5/Section520.lean`: clean.
* `lake build OpenMath.Chapter5`: clean (`2787/2787` jobs).
* `mcp__lean-lsp__lean_verify` on
  `backwardEulerGLM_stabilityMatrix`,
  `backwardEulerGLM_isAStable`,
  `backwardEulerGLM_isLStable` — all return
  `axioms = [propext, Classical.choice, Quot.sound]`. **No
  `sorryAx`.**

## Faithfulness check

### `backwardEulerGLM` (new `def` in Section510)

* This is a *named instance* (a specific `(s,r)=(1,1)` GLM), not a new
  mathematical concept. No `entities/<id>.json` exists for it
  (it is a Lean-side witness, like `explicitEulerGLM`).
* Lean tableau `A = U = B = V = !![1]` is the textbook backward-Euler
  GLM tableau (cf. Butcher §351 BDF1; §520 backward-Euler discussion):
  the single stage equation `Y = y_n + h f(Y)` and output
  `y_{n+1} = y_n + h f(Y) = Y` collapse to `Y = (1) y_n + h (1) f(Y)`,
  i.e. `A = U = !![1]`, and `y_{n+1} = (1) Y_? + (1) y_n` … wait
  actually this is `B = U = V = !![1]` and stage `Y` with
  `A = !![1]` gives `Y = U y_n + h A f(Y) = y_n + h f(Y)`,
  and `y_{n+1} = V y_n + h B f(Y) = y_n + h f(Y) = Y`. Both forms
  agree. Faithful.

### `backwardEulerGLM_stabilityMatrix`

* Entity ID: `def:520A` (definitional consequence). Statement:
  `M(z) = V + zB(I − zA)⁻¹U`. Plug in `V = B = U = !![1]`,
  `A = !![1]` ⇒ `M(z) = 1 + z (1)(1−z)⁻¹(1) = 1 + z/(1−z) = 1/(1−z)`.
  Lean: `!![1 / (1 - z)]`. Same content. The hypothesis `z ≠ 1` is
  the *exact* condition for `(I − zA) = !![1−z]` to be invertible —
  no extra strength.

### `padeZeroOne_norm_le_one_of_re_nonpos`

* No textbook entity (helper lemma). Statement: `Re(z) ≤ 0 ⇒
  |1/(1-z)| ≤ 1`. Standard real-analysis fact about the Padé(0,1)
  approximant; mirrors cycle 135's analog for Padé(1,1). Same content.

### `backwardEulerGLM_isAStable`

* Entity ID: `def:520E` (witness for the predicate). The predicate
  asks `∀ z, Re z ≤ 0 → ∃ C, ∀ k, ‖M(z)^k‖ ≤ C`. Lean witness uses
  `C = 1` and `‖M(z)^k‖ = ‖1/(1-z)‖^k ≤ 1^k = 1`. Faithful, no
  extra hypothesis.

### `norm_one_div_sub_tendsto_zero_cocompact`

* Helper, no entity. Statement: `‖1/(1-z)‖ → 0` along
  `cocompact ℂ`. Pure complex-analysis fact. Same content.

### `backwardEulerGLM_isLStable`

* Entity ID: `def:520F`. Predicate is `IsAStable ∧ Tendsto (fun z =>
  ρ(M(z))) cocompact (𝓝 0)`. Lean witness combines
  `backwardEulerGLM_isAStable` with the cocompact-limit derived from
  `norm_one_div_sub_tendsto_zero_cocompact` via the `1×1` spectral
  radius collapse `ρ(!![a]) = ‖a‖₊` (cycle-137 helper
  `spectralRadius_fin_one`). Same content; no extra hypothesis.

### Smuggling check

* `IsLStable` predicate was already in place from cycle 137; no
  predicate redefinition. Witness only.
* No new `class`/`structure`. No new `axiom`. No `maxHeartbeats`
  change.
* No tautology / identity: every theorem does substantive work.
* Hypothesis strength: `z ≠ 1` for `backwardEulerGLM_stabilityMatrix`
  is necessary (the matrix is genuinely undefined at `z = 1`); no
  extraneous strengthening.

## Dead ends

* Initial `field_simp` plan in Step 2 used `rw [eq_div_iff hne]`
  before `field_simp`, but the post-`simp` goal had `(·)⁻¹` not `_/_`,
  so `eq_div_iff` failed to find a pattern. Switched to dropping
  `eq_div_iff`, just `field_simp; ring`.
* The `simp [...]` line at the end of `backwardEulerGLM_stabilityMatrix`
  initially closed too much, leaving only the residual algebraic
  goal `1 - z + z = 1`; `ring` closes it.
* Reverse-triangle `‖1 - z‖ ≥ ‖z‖ - 1` was tricky because Mathlib's
  `norm_sub_norm_le` produces `‖a‖ - ‖b‖ ≤ ‖a - b‖` and the order
  matters. Instead used both directions
  `norm_sub_norm_le z (1 : ℂ)` (gives `‖z‖ - 1 ≤ ‖z - 1‖`) plus
  `‖z - 1‖ = ‖1 - z‖` via `← norm_neg` + `ring_nf`, then `linarith`.

## Discovery

* `Matrix.inv_subsingleton` + `Ring.inverse_eq_inv` is the canonical
  way to invert `1×1` complex matrices in this file. Pattern is now
  used in 3 stability-matrix closed forms (`explicitEulerGLM`,
  `implicitMidpointGLM`, `backwardEulerGLM`).
* `Filter.Tendsto.inv_tendsto_atTop` is the right tool to send a
  positive `Tendsto _ _ atTop` sequence to `0`.
* For cocompact-norm-tendsto-atTop, **only** the named lemma
  `tendsto_norm_cocompact_atTop` (in `Mathlib.Analysis.Normed.Group.Bounded`)
  is needed — no `ProperSpace`/`Bornology.cobounded` plumbing
  required for `ℂ` since it instantiates `ProperSpace` automatically.
* The `ENNReal → NNReal → ℝ` Tendsto-lifting via `ENNReal.tendsto_coe`
  + `NNReal.tendsto_coe` works smoothly: requires only `push_cast`
  to handle the coercion under the function symbol.

## Suggested next approach

Per planner's "Suggested cycle-143 next target", the cheapest
+score path is now:

* **`padded2DBackwardEulerGLM` r=2 witness for `IsLStable`** —
  mirrors cycles 133/134's `padded2DEulerGLM` for IRK-stability,
  uses the cycle-142 `backwardEulerGLM_stabilityMatrix` machinery
  on the row-0 block.

Medium-risk alternatives:

* **Open `def:530B` order-relative-to-starting-method** — backward
  Euler is now available as a substantive concrete GLM to feed into
  the `M.HasOrderRelativeTo` predicate. The `applyStartingMethod` /
  `applyGLMStep` infrastructure remains the main cost (~250 LOC),
  so cycle 143 should pick this only if the planner is willing to
  spend a multi-cycle infra budget.

High-risk (defer):

* **`def:442A` principal sheet** — Riemann surface + local
  injectivity infrastructure. Multi-cycle. Not cheap.
* **`thm:550A` general-`n`** — confirmed intractable for Aristotle
  (cycle 141 cancelled at 6%); manual cofactor expansion remains
  the only path and is itself multi-cycle.
