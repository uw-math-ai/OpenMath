# Cycle 107 Results

## Worked on
Closed the last `sorry` in `OpenMath/`: `aux_515B_eta_contraction` in
`OpenMath/Chapter5/Section515.lean` (the η-contraction step of
Butcher's `lem:515B`). Net change: **−1 sorry** (1 → 0 in OpenMath/).

## Approach
Followed the cycle-107 strategy verbatim:

1. Added `import OpenMath.Chapter5.MMatrix` and
   `open scoped Matrix.Norms.Frobenius` at the top of Section515 so
   the M-matrix infrastructure landed in cycle 106 is in scope.

2. Added the explicit Frobenius-norm hypothesis
   `_h_norm : ‖((h₀ * L) • A.map (fun x => |x|))‖ < 1` to
   `aux_515B_eta_contraction` (faithfulness divergence: textbook says
   "h₀ small enough"; we surface the precise condition).

3. Propagated the new hypothesis up to the unique caller
   `GeneralLinearMethod.localStepError_bound` so the assumption lives
   at the lem:515B signature, where it belongs textbook-wise.

4. Wrote the proof in seven steps:
   * **Setup**: `M_pos := (h₀ * L) • |A|`, `target j := ell_U j * δ_max
     + h²L²M * phi_A j`, `absη j := |η j|`.
   * **Step 6 (`hMpos_nn`)**: `M_pos.EntrywiseNonneg` from
     `0 ≤ h₀ * L` and `abs_nonneg`.
   * **Mulvec computation**: `(M_pos *ᵥ v) i = h₀ * L * Σ |A i k| * v k`
     proved via the `rfl` equation
     `(M_pos *ᵥ v) i = ∑ k, M_pos i k * v k` plus `Finset.mul_sum` and
     the entrywise formula `M_pos i k = h₀ * L * |A i k|`.
   * **Step 1+δ-bound (`htriangle` + `hUδ_bound`)**: `|η j| ≤
     |η j − Σ U δ| + |Σ U δ| ≤ contraction-RHS + Σ |U_jk| * δ_max`.
   * **Step 2 (substitute side equations)**: rewrite using
     `_hellU_eq` (`Σ |U_jk| = ell_U j − h₀L Σ |A_jk| ell_U_k`) and
     `_hphiA_eq` analogously. Then expand `Σ |A_jk| * target_k`
     algebraically.
   * **Step 4 (`h ≤ h₀` upgrade)**: bound
     `h * L * Σ|A_jk||η_k| ≤ h₀ * L * Σ|A_jk||η_k|`.
   * **Step 5 (matrix form)**: combine to
     `0 ≤ ((1 - M_pos) *ᵥ (target - absη)) j` via
     `Matrix.sub_mulVec` + `Matrix.one_mulVec` + the explicit mulVec
     formula.
   * **Step 7 (apply comparison principle)**:
     `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg
       hMpos_nn _h_norm hkey_matrix` yields
     `0 ≤ (target - absη) j`, i.e. `|η j| ≤ target j`.

5. Updated `localStepError_bound`'s docstring to reflect closure.

6. Verified `lake build OpenMath.Chapter5.Section515` succeeds, then
   `#print axioms` for `localStepError_bound` confirmed clean axioms
   `[propext, Classical.choice, Quot.sound]`.

7. Updated `plan.md` (lem:515B `[~]` → `[x]`; progress 64 → 65),
   `extraction/formalization_data/lean_status.json` (lem:515B
   "partial" → "formalized"), and the deferred issue file with a
   RESOLVED header.

## Result
SUCCESS — `aux_515B_eta_contraction` closed cleanly in ~120 LOC,
within the strategy's hard ceiling. Sorry count in `OpenMath/` is now
0; lem:515B is fully formalized.

## Faithfulness check
For every new theorem / proof / signature change introduced this cycle:

- **Entity ID**: `lem:515B` (textbook Lemma 515B, p. 414).
  Textbook statement (quoted from `entities/lem_515B.json`):
  > Under the conditions of Lemma 515A, the exact solution and the
  > computed solution in a step are related by … with
  > `‖K^[n]‖ ≤ h α max|ỹ^[n−1] − y^[n−1]| + β h²` … and α, β given via
  > `ℓ` solving `Σ_j (δ_{ij} − h₀ L |a_{ij}|) ℓ_j = Σ_j |U_{ij}|`.

  The Lean theorem `localStepError_bound` captures **the same content
  with one explicit hypothesis added**: `‖(h₀ L) • |A|‖_F < 1`
  (Frobenius norm). The textbook proof tacitly relies on this
  condition (it's the M-matrix non-singularity assumption needed for
  the `(I − h₀ L |A|)^{−1}` step in Butcher's proof — see the
  paragraph just before display (515c)). Surfacing it as an explicit
  Lean hypothesis makes the latent assumption first-class and is
  documented in the docstring + the deferred-issue file.

- **`aux_515B_eta_contraction`**: an internal helper, not a textbook
  entity. Same `_h_norm` hypothesis added.

- **Hypothesis-strength check**: the proof uses `h ≤ h₀`, `0 ≤ h`,
  `0 ≤ L`, `0 ≤ M_bound`, `0 ≤ δ_max`, the `_hellU_eq` / `_hphiA_eq`
  side equations, `_hδ_max`, `_hcontraction`, plus `_h_norm`. All
  match the textbook except `_h_norm`, which is the single explicit
  faithfulness divergence.

- **Tautology / identity / definition-smuggling**: N/A — no `def`,
  `structure`, or new abstraction introduced. The proof is purely
  applicative: Mathlib's Neumann-series machinery + cycle-106 M-matrix
  lemmas + standard real-analysis tactics.

## Dead ends
None this cycle — the strategy was prescriptive and the planned proof
worked. Two minor compilation hiccups were fixed quickly:

* Initial `show ((h₀ * L) • A.map (fun x => |x|) *ᵥ v) i = ...`
  failed to definitionally unify with `(M_pos *ᵥ v) i = ...` because
  `set` keeps `M_pos` opaque. Fixed by `rw [hMpos_def]` first, but
  then `Matrix.mulVec_eq_sum` rewrote into a `MulOpposite`-flavored
  form. Final fix: use the `rfl` equation
  `(M_pos *ᵥ v) i = ∑ k, M_pos i k * v k` directly (works because
  `dotProduct` is left-multiplied for ℝ as a commutative semiring).
* `abs_add` is named `abs_add_le` in current Mathlib.

## Discovery
* `(M *ᵥ v) i = ∑ k, M i k * v k` holds by `rfl` over a commutative
  semiring (no need to invoke `Matrix.mulVec_eq_sum`, which targets
  the non-commutative case via `MulOpposite`). This is more reliable
  than chained `simp` calls when the matrix is a `set`-bound
  abbreviation.
* When `set X := …` is used and you need the unfolded form for `rfl`
  or `show`, it's easiest to pass the equation `hX_def` to a
  point-of-use `rw` rather than relying on definitional unfolding via
  `show`.
* Frobenius-scope opening in Section515 doesn't conflict with
  Section510's `open scoped Matrix.Norms.Operator` because the
  Section510 scope only affects content inside Section510.lean —
  scopes in `open scoped` are file-local once the namespace is left.

## Suggested next approach
* **Cycle 108 (Excellent path)**: open the sorry-first scaffold for
  `thm:515D` ("Stability and consistency imply convergence", §515)
  per cycle-107 strategy's preview. Per `entities/thm_515D.json`,
  expect 3–5 cycles total — the textbook proof composes
  `lem:515B` (now closed!) with a discrete-Grönwall global-error
  argument analogous to §406D for LMMs. First cycle should:
  - Read `entities/thm_515D.json` to nail the statement.
  - Scaffold the theorem with `sorry` + ≤2 sub-lemma sorries (matching
    cycle-103 ceiling).
  - Identify whether Mathlib already has a discrete-Grönwall lemma
    we can reuse (try `lean_local_search "Gronwall"` /
    `lean_leansearch "discrete Gronwall"`).
* **Optional housekeeping**: cancel Aristotle project `4688b630-…`
  (cycle-103 η-contraction batch, dead at >50h, 6%) to free a slot.
  Skipped this cycle since the strategy marked it optional.
* **Optional pre-work**: add a non-vacuity witness for the
  `_h_norm` hypothesis (e.g., for `explicitEulerGLM` with `h₀ * L`
  small, `‖(h₀ * L) • |A|‖_F = 0` since A is the zero matrix). Not
  load-bearing but improves faithfulness audit signal.
