# Cycle 245 Results

## Worked on
- **Phase 2 of `lem:319A`** — the headline contraction bound
  `‖y₁ − z₁‖ ≤ (1 + h L^†) ‖y₀ − z₀‖` (Butcher §319 p. 188).
- **Module relocation** `OpenMath/Chapter5/MMatrix.lean` →
  `OpenMath/Matrix/MMatrix.lean` (chapter-neutral helper module so
  Chapter 3 can consume the M-matrix machinery without inducing a
  circular dependency on Chapter 5).

## Approach
Followed planner's Option α (relocate the MMatrix module rather than
duplicate it inline). The relocation was a 3-step mechanical edit
(create `OpenMath/Matrix/`, `git mv` the file, update two consumer
imports `OpenMath/Chapter5.lean` and `OpenMath/Chapter5/Section515.lean`).
Section 515 is the load-bearing consumer (≈3000 LOC); it compiled
cleanly with only pre-existing warnings after the path change.

For Phase 2, composed cycle 244's stage/output recurrences
(`stage_diff_recurrence`, `output_diff_recurrence`) with cycle 106's
M-matrix inverse-positivity (`Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one`
and `nonneg_of_one_sub_mulVec_nonneg`) following the recipe in §D of
the strategy. The key intermediate step was establishing the stage-vector
comparison `vM i ≤ ‖y₀ − z₀‖ * w i` where `w := (I − K)⁻¹ 𝟙` and
`K := (h₀ L) • |A|`, via the M-matrix comparison principle applied to
`v' i := ‖y₀ − z₀‖ * w i − vM i` with `(1 − K) *ᵥ v' ≥ 0` componentwise.

`L^†` is exposed existentially with witness `L * ∑ᵢ |bᵢ| * wᵢ`
(closed-form formula matching the textbook
`L^† = L |b|^T (I − h₀ L |A|)^{−1} 𝟙`).

## Result
**SUCCESS** — both deliverables shipped axiom-clean.

- **Relocation**: `OpenMath/Matrix/MMatrix.lean` (171 LOC, contents
  byte-identical to cycle 105/106's original). Two consumer imports
  updated. Old file removed via `git rm`. Section515 and Chapter5
  aggregator both compile.
- **Phase 2 theorem**: `OpenMath.Chapter3.Section312.RKTableau.lem_319A`
  (~125 LOC body). Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
- **Non-vacuity (D5)**: Phase 2 example on `paddedEuler` with `f := id`
  (witness uses `paddedEuler.A = 0` ⇒ `K = 0` ⇒ `‖K‖ = 0 < 1`).

Section319.lean: 282 LOC → 466 LOC, 0 sorries.

## Faithfulness check

- **Entity ID**: `lem:319A`. Textbook statement (Butcher §319 p. 188,
  quoted from `extraction/formalization_data/entities/lem_319A.json`):
  > "Let `f : ℝ^m → ℝ^m` satisfy a Lipschitz condition with constant
  > `L`. Let `y_0, z_0 ∈ ℝ^m` be two input values to a step with the
  > Runge–Kutta method `(A, b, c)`, using stepsize `h ≤ h_0`, where
  > `h_0 L ρ(|A|) < 1`, and let `y_1` and `z_1` be the corresponding
  > output values. Then `‖y_1 − z_1‖ ≤ (1 + h L^†) ‖y_0 − z_0‖`, where
  > `L^† = L |b|^T (I − h_0 L |A|)^{−1} 𝟙`."

- **Lean statement captures**: **same content modulo packaging and
  smallness-form divergence**. The existential `∃ L_dag, 0 ≤ L_dag ∧ …`
  exposes `L^†` as a non-negative real; the closed form
  `L * ∑ᵢ |bᵢ| * ((I − h_0 L |A|)⁻¹ 𝟙)ᵢ` is the textbook formula
  expressed in Lean.

- **Divergence (smallness)**: textbook `h_0 L ρ(|A|) < 1` (spectral
  radius), Lean `‖(h_0 L) • |A|‖_F < 1` (Frobenius operator norm).
  Frobenius dominates spectral, so the Lean hypothesis is **strictly
  stronger** than the textbook's. Matches the cycle 106/107 M-matrix
  machinery's built-in hypothesis shape. Documented in the theorem's
  docstring.

- **Tautology check**: conclusion `‖y₁ − z₁‖ ≤ (1 + h * L_dag) * ‖y₀ − z₀‖`
  does not appear verbatim as any hypothesis. ✓

- **Identity check**: the proof is non-trivial (~125 LOC, composes
  three load-bearing prior lemmas + algebraic substitution). Not a
  re-export. ✓

- **Hypothesis strength**: `hL`, `hf_lip`, `hh`, `hh_le`, `hh₀` match
  the textbook hypotheses exactly. `h_norm` is the Frobenius form of
  the textbook smallness (see divergence note above). ✓

- **Definition smuggling check**: nothing was redefined; the theorem
  composes existing infrastructure. ✓

## Dead ends

* **Initial `*ᵥ` notation failure**: writing `*ᵥ` inside
  `namespace OpenMath.Chapter3.Section312.RKTableau` triggered
  "elaboration function for `Mathlib.Tactic.subscriptTerm` has not been
  implemented" — the matrix-vector mul infix `*ᵥ` is scoped to
  `Matrix` (`scoped infixr:73 " *ᵥ " => Matrix.mulVec` in
  `Mathlib.Data.Matrix.Mul`). Fixed by adding `open scoped Matrix`
  alongside `open scoped Matrix.Norms.Frobenius`.

* **`congr 1` aggression**: the entry-wise `(K *ᵥ vM) i = (h₀ L) ∑ⱼ …`
  proof had `congr 1` closing the goal entirely (because
  `M.A.map (fun a => |a|) i j` reduces definitionally to `|M.A i j|`),
  so the subsequent `rw [Matrix.mulVec, dotProduct]` triggered "no
  goals" error. Resolution: drop the post-`congr 1` tactics.

## Discovery

* **`*ᵥ` scope**: when working outside `namespace Matrix`, you must
  `open scoped Matrix` to use the infix. Section515 works without this
  only because it transitively activates the scope via its import
  chain. Chapter 3 files (Section319) do not get this transitivity
  and need the explicit `open scoped Matrix`. Recorded in
  `attempts.md` under cycle 245.

* **Cycle 244 supervisor verdict was a phantom**: the "2 suspected
  vacuous proofs" flag was the documented D2 over-firing pattern
  (scanner mis-identifying multi-line theorem-signature hypothesis
  bindings `(hY_out : ...) (hZ_out : ...)` as proof bodies). No
  remediation needed — the code is correct as-is. Recorded under
  cycle 245 in `attempts.md`.

* **Module relocation is mechanical when callers use top-level
  namespaces**: `MMatrix.lean` lives under `namespace Matrix`, so
  consumers cite `Matrix.EntrywiseNonneg.*` etc., not
  `OpenMath.Chapter5.MMatrix.*`. Moving the file changed only the
  `import` line in two files; no symbol references needed updating.

## Suggested next approach

**Cycle 246**: `thm:319B "Global truncation error bound via local
error accumulation"` — the §319 capstone. Composes `lem_319A`
(one-step contraction) iteratively over n steps. Needs a
local-truncation-error definition (likely matches Butcher's
Figure 319(ii) setup: comparing exact solution from `y(x_{k-1})` over
one step against numerical step from same input). Build a recursion
of the form
`‖e_n‖ ≤ (1 + h L^†)^n ‖e_0‖ + ∑_{k=1}^{n} (1 + h L^†)^{n−k} ‖δ_k‖`
and bound via geometric-sum manipulation (Gronwall-like).

Backup pivots if `thm:319B` proves harder than expected:
* `lem:310B` (Elementary Differential Weight Formula, §310) — pure
  tree combinatorics, builds on cycle 232+ elementaryWeight
  infrastructure.
* `lem:311A` (Taylor expansion of exact solution, §311) — fresh §311
  ground.
* `thm:443A` (Order arrows for LMM, §441) — §441 continuation after
  cycle 240's Section441B.
