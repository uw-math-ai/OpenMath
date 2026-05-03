# Cycle 105 Results

## Worked on

Helper infrastructure: created `OpenMath/Chapter5/MMatrix.lean` with the
`Matrix.EntrywiseNonneg` predicate and 6 closure/application lemmas.
This unblocks the deferred `aux_515B_eta_contraction` (Section515.lean
line 995, the only `sorry` in `OpenMath/`).

## Approach

1. **Aristotle Priority 0 poll.** Polled project
   `4688b630-d9c9-4f86-9572-7e4bd9a6b0b8` (cycle 103/104 batch for
   `aux_515B_eta_contraction` etc.). Status: `IN_PROGRESS` at 5 %
   (started 2026-05-03 17:52, last update 18:28). No usable result.
   Did not poll again per CLAUDE.md.
2. **Mathlib search.** Confirmed via grep over
   `.lake/packages/mathlib/` that no `EntrywiseNonneg` /
   `entrywise nonneg` predicate exists. `Matrix.PosSemidef` exists but
   captures the *spectral* (Loewner) notion, not componentwise — not
   suitable for the η-contraction proof.
3. **Created `MMatrix.lean`.** Definition + 6 fully-proved lemmas, no
   sorries:
   - `Matrix.EntrywiseNonneg M : Prop := ∀ i j, 0 ≤ M i j`
   - `entrywiseNonneg_zero` — zero matrix is nonneg.
   - `entrywiseNonneg_one` — identity matrix is nonneg
     (over any ordered semiring).
   - `EntrywiseNonneg.add` — sum of two nonneg matrices.
   - `EntrywiseNonneg.smul` — scalar mult by nonneg constant.
   - `EntrywiseNonneg.mul` — matrix product.
   - `EntrywiseNonneg.mulVec_nonneg` — sends nonneg vectors to
     nonneg vectors.
   - `EntrywiseNonneg.pow` — natural-number powers preserve nonneg.
   - `EntrywiseNonneg.mulVec_mono` — monotone on componentwise-ordered
     vectors (the **load-bearing** lemma for η-contraction).
   - `EntrywiseNonneg.sum` — finite sum of nonneg matrices.
   - Three concrete `example` witnesses: 2×2 zero, 2×2 identity, and
     a 2×2 stochastic-style matrix `!![1/2,1/2; 1/3,2/3]`.
4. **Wired into Chapter5.** Added `import OpenMath.Chapter5.MMatrix`
   at the top of `OpenMath/Chapter5.lean`, ran
   `lake build OpenMath.Chapter5.MMatrix` to populate `.olean` cache.
   `OpenMath.Chapter5.lean` and `OpenMath.Chapter5.Section515.lean`
   both still compile cleanly.
5. **Cycle 106 Aristotle batch.** Submitted a self-contained file
   `inv_one_sub.lean` (project
   `8e9eec37-2285-439b-b8b9-cd116e58534c`, QUEUED at 18:36 UTC)
   asking Aristotle to prove the inverse-positivity lemma
   `EntrywiseNonneg.inv_one_sub_of_norm_lt_one` (the deferred Neumann-
   series result) plus an aux `tsum_pow_of_norm_lt_one`. If
   Aristotle returns this, cycle 106 can directly close
   `aux_515B_eta_contraction`.

## Result

**SUCCESS** —

- 8 new lemmas + 1 definition added under `OpenMath/Chapter5/MMatrix.lean`,
  all fully proved (no sorries introduced).
- 3 concrete witnesses provided (CLAUDE.md non-vacuity rule satisfied).
- Sorry count in `OpenMath/` unchanged at exactly 1
  (`Section515.lean:995` `aux_515B_eta_contraction`, deferred per
  prior issue file).
- Inverse-positivity (the deferred Neumann lemma) is **documented as
  a docstring-only future target**, not stubbed with `sorry`, per the
  hard cycle 105 constraint.
- Aristotle batch submitted for cycle 106, no blocking on result.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

* **`def Matrix.EntrywiseNonneg`** — helper infrastructure, no textbook
  entity. Definition matches standard mathematical convention
  (componentwise non-negativity, distinct from `Matrix.PosSemidef`).
  The docstring explicitly disambiguates these two notions. Concrete
  witnesses provided (zero, identity, stochastic-style).
  *No definition smuggling*: this is a primitive predicate, not a
  characterization of a deeper concept.

* **`entrywiseNonneg_zero`** — trivial corollary; not vacuous, since
  it specializes the universal predicate to the zero matrix.
  Hypothesis `[Zero α] [Preorder α]` is minimal (zero needs Zero,
  `≤` needs Preorder).

* **`entrywiseNonneg_one`** — relies on `IsOrderedRing α` for
  `0 ≤ 1`. The two hypotheses (`Semiring`, `IsOrderedRing`) are both
  necessary: semiring for the matrix `1`, ordered for `0 ≤ 1`.

* **`EntrywiseNonneg.add` / `.smul` / `.mul` / `.mulVec_nonneg` /
  `.pow` / `.mulVec_mono` / `.sum`** — all closure lemmas, all proved
  by direct unfolding + `Finset.sum_nonneg` / induction. Tautology
  check passes (no conclusion equals a hypothesis verbatim). Identity
  check passes (no proof is `:= h_something`; all use real reasoning).
  Hypothesis-strength check: every nonneg hypothesis is consumed in
  the proof. All hypotheses are exactly the closure required by the
  conclusion — none are stronger than the textbook would require.

* **No theorems are tautological or vacuous.** The earlier draft had
  `entrywiseNonneg_iff` and `EntrywiseNonneg.apply` as `Iff.rfl` /
  function-application thin wrappers; these were **removed during the
  faithfulness pass** to avoid identity-check violations.

* **No new `class` or `structure`.** No new `Prop` fields to label.

* **Promised-but-absent check.** The docstring at the bottom of
  `MMatrix.lean` describes `EntrywiseNonneg.inv_one_sub_of_norm_lt_one`
  as a *future* (cycle 106) target, explicitly *not* stubbed. This is
  a forward-reference, not a promised lemma — the docstring states
  `**not** stubbed with sorry here`, so no invisible gap.

## Dead ends

* Initial proof of `entrywiseNonneg_one` used
  `by_cases h : i = j; · simp [h]; · simp [Matrix.one_apply, h]`,
  which failed because the `i = j` case left `0 ≤ 1 i j` unsimplified
  (Lean did not unfold the matrix `1` at that step). Switched to
  `rw [Matrix.one_apply]; split_ifs` which gives proper case-split.

* `fin_cases i <;> fin_cases j <;> norm_num` failed on the 2×2
  stochastic witness because `norm_num` alone could not see through
  the `!![...]` matrix-literal projections. Adding the
  `Matrix.cons_val_*` simp set as `norm_num` lemmas (`norm_num
  [Matrix.cons_val_fin_one, Matrix.cons_val_zero, ...]`) closed all 4
  cases cleanly.

* Forgot `Mathlib.Tactic.NormNum`/`Linarith`/`Positivity` imports
  initially — `norm_num` and `linarith` were unknown identifiers.
  `positivity` worked from `Mathlib.Algebra.Order.BigOperators...`
  transitively, which masked the missing imports until I needed
  more. Now imports are explicit.

## Discovery

* **`Matrix.PosSemidef` is the only nonneg-style matrix predicate in
  Mathlib.** No `Matrix.EntrywiseNonneg`, no `Matrix.NonnegMatrix`, no
  `Matrix.MMatrix`. Project must build this from scratch (now done).

* **`Matrix.mulVec_def` unfolds via `dotProduct`**, which is
  `Finset.sum (fun j => v j * w j)`. So `Finset.sum_nonneg` and
  `Finset.sum_le_sum` (with `mul_nonneg`/`mul_le_mul_of_nonneg_left`)
  are the workhorses for componentwise reasoning. No need for any
  bespoke matrix lemmas — direct finsum manipulation suffices.

* **Concrete witness via matrix literal `!![...]`** requires
  `Mathlib.LinearAlgebra.Matrix.Notation` (NOT `Mathlib.Data.Matrix.
  Notation`, which doesn't exist as an `.olean`). Save 30s of
  debugging next cycle.

* **The Aristotle batch from cycle 103 is still IN_PROGRESS at 5 %
  after >40 hours.** This is not a transient stall — it suggests the
  η-contraction problem is genuinely beyond Aristotle's reach without
  M-matrix infrastructure. The cycle 105 strategy's diagnosis was
  correct.

## Suggested next approach

For cycle 106, the planner should:

1. **Poll Aristotle on `8e9eec37-2285-439b-b8b9-cd116e58534c`**
   (the cycle 105 inverse-positivity submission) at the start of the
   cycle.

2. **If Aristotle returns inverse-positivity**, copy the proof into
   `OpenMath/Chapter5/MMatrix.lean` (replacing the "Deferred to cycle
   106" docstring with a real lemma), then close
   `aux_515B_eta_contraction` in `Section515.lean` using
   `EntrywiseNonneg.inv_one_sub_of_norm_lt_one` +
   `EntrywiseNonneg.mulVec_mono`.

3. **If Aristotle fails or stalls**, the cycle 106 worker should
   manually prove inverse-positivity. The proof outline:
   - Show `(1 - M)` is invertible via `IsUnit.sub_left` or similar
     given `‖M‖ < 1`.
   - Express `(1 - M)⁻¹` as `Ring.inverse (1 - M)`.
   - Use `tsum_geometric_of_norm_lt_one`-style lemma to identify
     `(1 - M)⁻¹ = ∑' k, M^k` entrywise.
   - Apply `EntrywiseNonneg.pow` and the fact that entrywise non-
     negativity is closed under entrywise convergence (which itself
     is a one-line lemma: tsum of nonneg = nonneg).

4. **Once `aux_515B_eta_contraction` closes**, sorry count in
   `OpenMath/` drops to 0. Then update
   `extraction/formalization_data/lean_status.json` for `lem:515B`
   and the `localStepError_bound` entity to mark them complete.

5. **Stretch: open `lem:515C` or `thm:515D`** with sorry-first
   scaffolds (now safe, since `lem:515B` is fully closed). Both
   lemmas appear in `entities/lem_515C.json` and
   `entities/thm_515D.json`.
