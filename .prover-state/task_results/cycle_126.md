# Cycle 126 Results

## Worked on

`thm:520D` (Butcher Theorem 520D, p. 419) — *Instability Region
Boundary Characterization* — both directions, fully closed
axiom-clean. Decomposed into four private sub-lemmas (D1, D3, D4
plus contrapositive plumbing) and two public theorems (one per
inclusion).

Files changed:
- `OpenMath/Chapter5/Section520.lean` — added §520D scaffolding plus
  closed all six lemmas; added imports for
  `Mathlib.Analysis.Normed.Algebra.GelfandFormula` and
  `Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs`.
- `extraction/formalization_data/lean_status.json` — `thm:520D` →
  `formalized`.
- `plan.md` — `thm:520D` row marked done.
- `.prover-state/aristotle_submissions/cycle_126/` — D4 standalone
  submission file authored but **not** sent: closed manually instead.

## Approach

Followed the strategy's six-lemma scaffold:

1. **D1 `stabilityFunction_eq_zero_iff_mem_spectrum`** — bridge
   `Φ(w,z) = 0 ↔ w ∈ spectrum ℂ M(z)`. Closed via
   `Matrix.smul_one_eq_diagonal` + `Matrix.scalar_apply` to rewrite
   `w • 1 - M(z)` as `(scalar w) - M(z)`, then `Matrix.eval_charpoly`
   + `Matrix.mem_spectrum_iff_isRoot_charpoly`. `rfl` finishes after
   the rewrites since `Polynomial.IsRoot p w ≡ p.eval w = 0`.
2. **Direction (2) `instabilityRegion_supseteq_outside_disc`** —
   manually proved. Pipeline: hypothesis ⇒ D1 puts `w ∈ spectrum` ⇒
   `spectrum.pow_mem_pow` gives `w^n ∈ spectrum (M(z)^n)` ⇒
   `spectrum.norm_le_norm_mul_of_mem` gives
   `‖w‖^n ≤ ‖M(z)^n‖ · ‖1‖`. PowerBounded gives `‖M(z)^n‖ ≤ C`. With
   `‖w‖ > 1` and `tendsto_pow_atTop_atTop_of_one_lt`, pick `N` with
   `‖w‖^N > C·‖1‖ + 1`, contradiction via `linarith` after
   `mul_le_mul_of_nonneg_right`.
3. **D3 `stabilityRegion_imp_spectralRadius_le_one`** — symmetric to
   direction (2). `iSup₂_le` reduces `spectralRadius ≤ 1` to
   `∀ μ ∈ σ, (‖μ‖₊ : ENNReal) ≤ 1`. Same `pow_mem_pow` +
   `tendsto_pow_atTop_atTop_of_one_lt` argument.
4. **D4 `instabilityRegion_imp_spectralRadius_ge_one`** —
   contrapositive: `spectralRadius < 1 → power-bounded`. Routes
   through Section142:
   - Every minpoly root `μ` is a charpoly root
     (`Matrix.minpoly_dvd_charpoly` + `Polynomial.IsRoot.dvd`),
     hence `μ ∈ spectrum` (`Matrix.mem_spectrum_iff_isRoot_charpoly`).
   - `(‖μ‖₊ : ENNReal) ≤ spectralRadius < 1` via `le_iSup₂` with the
     `f := fun k _ => (‖k‖₊ : ENNReal)` annotation, then
     `ENNReal.coe_lt_one_iff` + `exact_mod_cast`.
   - Apply `Section142.minpoly_roots_lt_one_imp_convergent` to get
     `Tendsto (M(z)^n) atTop (𝓝 0)`.
   - `.norm` + `simpa` ⇒ `Tendsto (‖M(z)^n‖) atTop (𝓝 0)` ⇒
     `Filter.Tendsto.bddAbove_range` ⇒ uniform bound `C` ⇒
     PowerBounded.
5. **Direction (1) `instabilityRegion_subseteq_closed_disc_zeros`** —
   case-splits on `isEmpty_or_nonempty (Fin r)`:
   - `r = 0`: `Subsingleton.elim` reduces `M(z)^k` to `0`, so PB
     by `0`, contradicting `hz`.
   - `r ≥ 1`: D4 + `spectrum.exists_nnnorm_eq_spectralRadius` picks
     `w ∈ σ` realising the spectral radius; `‖w‖₊ ≥ 1` via
     `ENNReal.one_le_coe_iff` + `exact_mod_cast`; D1 ⇒ `Φ(w,z) = 0`.

## Result

**SUCCESS** — all six lemmas closed manually, no Aristotle round-trip
required this cycle. `lake env lean OpenMath/Chapter5/Section520.lean`
exits 0 with no warnings. Both public direction theorems axiom-clean
(verified via `#print axioms` returning
`[propext, Classical.choice, Quot.sound]`).

## Faithfulness check

For each new public `theorem` introduced this cycle:

### `instabilityRegion_subseteq_closed_disc_zeros` (direction (1))

- Entity ID and textbook statement (quoted from
  `entities/thm_520D.json`):
  > "The instability region for `(A, U, B, V)` is a subset of the set
  > of points `z`, such that `Φ(w, z) = 0`, where `|w| ≥ 1`."
- Lean signature:
  ```lean
  ∀ {z : ℂ}, z ∈ M.instabilityRegion →
      ∃ w : ℂ, 1 ≤ ‖w‖ ∧ M.stabilityFunction w z = 0
  ```
- Captures: **same content**. The set-theoretic inclusion
  `instabilityRegion ⊆ S` becomes the Lean form
  `z ∈ instabilityRegion → ∃ w …` with `S` unfolded.
- No extra hypotheses beyond what the textbook supplies (`z` lying
  in the instability region).

### `instabilityRegion_supseteq_outside_disc` (direction (2))

- Entity ID and textbook statement (quoted from
  `entities/thm_520D.json`):
  > "The instability region is a superset of the points defined by
  > `Φ(w, z) = 0`, where `|w| > 1`."
- Lean signature:
  ```lean
  ∀ {z : ℂ}, (∃ w : ℂ, 1 < ‖w‖ ∧ M.stabilityFunction w z = 0) →
      z ∈ M.instabilityRegion
  ```
- Captures: **same content**. The superset relation `S' ⊆
  instabilityRegion` is encoded as the implication.
- No extra hypotheses.

### Private sub-lemmas (D1, D3, D4)

These are auxiliary bridges, not Butcher-named entities. Their
content is documented in docstrings; D1 = spectrum ↔ Φ-zero, D3 =
PowerBounded ⇒ spectralRadius ≤ 1, D4 = ¬PowerBounded ⇒
spectralRadius ≥ 1. None of them carries hypotheses stronger than
the textbook implies.

## Dead ends

1. **`(1 : ℝ≥0)` notation parsing**. Initial `D3` and direction (1)
   proofs used `ℝ≥0` and `ℝ≥0∞` notations directly, but the
   elaborator gave `failed to synthesize instance of type class
   LE Type` errors with column hints in the middle of the multibyte
   notation glyphs. Replacing with the unicode-free `NNReal` /
   `ENNReal` names made everything compile. Not a Mathlib bug — a
   Lean parser misdiagnosis triggered when the multibyte glyph sits
   on an awkward position. **Lesson for future cycles:** when a
   `LE Type` / `OfNat Type 0` synth-failure points at a column
   inside `ℝ≥0` or `ℝ≥0∞`, swap the notation for the bare type name.
2. **`intro hMN` after `push_neg ⟨N, ?_⟩`**. After `push_neg`, the
   goal `∃ k, ¬ ‖M(z)^k‖ ≤ C` becomes `∃ k, C < ‖M(z)^k‖` (via
   `not_le`). The strict-form goal has no binder to `intro`; switch
   to `by_contra hMN; push_neg at hMN` to recover the proof-by-
   contradiction shape.
3. **Empty-`Fin r` degeneracy in direction (1)**. Mathlib's
   `spectrum.exists_nnnorm_eq_spectralRadius` requires
   `[Nontrivial A]`, which fails on `Matrix (Fin 0) (Fin 0) ℂ`.
   Sidestepped via `cases isEmpty_or_nonempty (Fin r)`:
   `Subsingleton.elim` collapses `M(z)^k = 0` in the empty case,
   contradicting `hz` directly.

## Discovery

1. **Spectrum-charpoly bridge is `rfl`-clean**. The chain
   `Φ(w, z) = (w • 1 - M(z)).det = ((scalar) w - M(z)).det =
   eval w M(z).charpoly = (IsRoot M(z).charpoly w → 0)` resolves
   without any heavy unification: `Matrix.smul_one_eq_diagonal` +
   `Matrix.scalar_apply` + `Matrix.eval_charpoly` +
   `mem_spectrum_iff_isRoot_charpoly` is enough.
2. **`spectrum.pow_mem_pow` is in
   `Mathlib.FieldTheory.IsAlgClosed.Spectrum`** (not
   `Algebra.Spectrum.Basic`). Imported transitively via
   `GelfandFormula`. Key tool for any "eigenvalue power = matrix
   power eigenvalue" argument.
3. **`Filter.Tendsto.bddAbove_range`** is the bridge from
   "convergent sequence" to "bounded sequence" — the cleanest path
   from `Section142.Convergent` to `PowerBounded` without re-
   inventing the eventually-bounded + finite-prefix argument.
4. **`le_iSup₂` annotation pattern**. To obtain
   `f i j ≤ ⨆ i ∈ s, f i j`, Lean needs the `f := fun k _ => …`
   annotation when the family has a propositional second argument
   (membership). Without it the type-class instance for
   `OrderBot ENNReal` was being mis-inferred.

## Suggested next approach

The closed §520D unblocks `def:520E` (A-stability) downstream
consumers (which already exist in the file). Triage between:

1. **`thm:550A` (Doubly companion matrices)** — a major §550
   companion-matrix datatype. Multi-cycle.
2. **`thm:521B` (Maximal stability order)** — needs `stabilityOrder`
   maximality predicate plus a polynomial re-encoding of
   `stabilityFunction`. Multi-cycle.
3. **`thm:431A` (Schur criterion)** — would close a §431 entry that
   depends on complex-analysis (Rouché). Mathlib provides Rouché
   (`Complex.OneDiffOn` etc.). One-cycle if the Schur statement
   is the standard one; multi-cycle otherwise.

I'd suggest **`thm:521B`** if the stability-order infrastructure is
the planner's focus this quarter (it consolidates §520 ↔ §521), or
**`thm:550B`** ("companion matrix similarity") since `thm:550A` is
listed as the precursor — checking whether `550B`'s textbook proof
goes through with a non-companion encoding would unblock both.

## Hygiene notes

Did **not** touch §C bonus (Section515 unused-simp warnings) — the
mandatory work consumed the cycle's budget, and the warnings are
non-blocking. Tracked for cycle 127 if planner wants the cleanup.
