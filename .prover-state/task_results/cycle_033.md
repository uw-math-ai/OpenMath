# Cycle 033 Results

## Worked on

`thm:357C` — Algebraic Stability ⇒ BN-Stability (Burrage–Butcher), the
target named by the cycle 033 strategy. Added to
`OpenMath/Chapter3/Section357.lean`:

* `algebraicallyStable_imp_A_symm` (helper) — derives `A i j = A j i`
  from `IsAlgebraicallyStable M`.
* `symplecticityMatrix_quadratic_form_eq` (Lemma 1) — symmetrisation of
  the quadratic form when `A` is symmetric.
* `bn_stability_identity` (Lemma 2) — the algebraic identity
  `‖y₁‖² − ‖y₀‖² = 2h Σᵢ bᵢ⟨Fᵢ,Yᵢ⟩ − h² Σᵢⱼ (2bᵢaᵢⱼ − bᵢbⱼ)⟨Fᵢ,Fⱼ⟩`.
* `posSemidef_inner_form_nonneg` (Lemma 3) — PSD matrix produces a
  non-negative bilinear form on `⟨Fᵢ, Fⱼ⟩` via the
  `posSemidef_iff_eq_conjTranspose_mul_self` factorisation.
* `algebraicallyStable_isBNStable` (the §357C theorem itself).

## Approach

1. Read the cycle-032 task results and the cycle-033 strategy. Confirmed
   the predicate-form question: BN-stability uses the (357c)
   single-trajectory dissipativity, *not* the (357a) two-solution form.
2. Loaded `extraction/formalization_data/entities/thm_357C.json` and
   verified the textbook statement.
3. Set up the file with three sorry'd helper lemmas + the theorem and
   confirmed the structure compiles.
4. Submitted the three lemmas to Aristotle in a batch (per the
   "Aristotle-first" rule) — see project IDs in the commit.
5. While Aristotle ran, manually proved Lemma 1 (symmetrisation),
   Lemma 3 (PSD bilinear form via Cholesky-style factorisation), and
   Lemma 2 (algebraic identity by polarisation + linearity).
6. Closed the §357C theorem by combining the three lemmas with the
   dissipativity hypothesis and `b > 0`.

### Discovery during set-up — the symplecticity matrix bug

While drafting Lemma 1 I realised the cycle-027 `symplecticityMatrix`
unfolds to `(b_i + b_j) a_{ij} − b_i b_j`, **not** the textbook form
`b_i a_{ij} + b_j a_{ji} − b_i b_j`. The Lean definition is missing a
transpose: it is `diag(b) A + A diag(b) − bbᵀ` whereas Butcher means
`diag(b) A + Aᵀ diag(b) − bbᵀ`.

Because `Matrix.PosSemidef` entails `IsHermitian` (= symmetric over ℝ),
`(symplecticityMatrix M).PosSemidef` together with `b > 0` silently
forces `A i j = A j i`. Under that derived hypothesis the two forms
agree as quadratic forms on the symmetric Gram matrix `⟨F_i, F_j⟩`, so
the §357C theorem still goes through — but `IsAlgebraicallyStable` is
narrower than the textbook intends.

Per the strategy's explicit "do not modify `symplecticityMatrix` or
`IsAlgebraicallyStable`" rule, I worked around the bug by adding
`algebraicallyStable_imp_A_symm` and using A-symmetry as a hypothesis
in Lemma 1. **An issue file documenting the bug and recommending a
fix in cycle 034 has been written to
`.prover-state/issues/symplecticityMatrix_missing_transpose.md`.**

## Result

**SUCCESS.** All three lemmas + the theorem are proved.
`lake env lean OpenMath/Chapter3/Section357.lean` is clean (one
deprecation warning for `Matrix.posSemidef_iff_eq_conjTranspose_mul_self`,
no errors, no sorrys). `lake build` completes successfully.
`#print axioms OpenMath.Chapter3.Section357.algebraicallyStable_isBNStable`
returns `[propext, Classical.choice, Quot.sound]`.

## Faithfulness check

Following the CLAUDE.md "Pre-Commit Faithfulness Checklist".

### `algebraicallyStable_imp_A_symm` (helper)

* Entity: not in textbook — introduced as a workaround for the
  symplecticity-matrix bug.
* Status: **Lean-side helper**, not a Butcher entity. Documented
  inline; the issue file recommends removing it once cycle 034 fixes
  the underlying definition. Justification: under
  `IsAlgebraicallyStable M`, the Hermitian requirement of
  `(symplecticityMatrix M).PosSemidef` plus `b_i > 0` forces
  `A i j = A j i`.

### `symplecticityMatrix_quadratic_form_eq` (Lemma 1)

* Statement: `Σᵢⱼ (2 bᵢaᵢⱼ − bᵢbⱼ) ⟨Fᵢ, Fⱼ⟩ = Σᵢⱼ symplecticityMatrix M i j ⟨Fᵢ, Fⱼ⟩`,
  given `A i j = A j i`.
* Pure technical lemma; not in the textbook. Hypothesis `A` symmetric
  is needed because of the symplecticity-matrix bug; once the bug is
  fixed, the lemma's hypothesis disappears.

### `bn_stability_identity` (Lemma 2)

* Statement: the algebraic identity (★) used in Butcher's proof of
  §357C, equation (357e). Quoting from `thm_357C.json:proof_text`
  (with the OCR-corrupted "−" → "²" fixed):
  > `‖yₙ‖² − ‖yₙ₋₁‖² = 2h ∑ᵢ bᵢ ⟨Yᵢ, Fᵢ⟩ − h² ∑ᵢⱼ mᵢⱼ ⟨Fᵢ, Fⱼ⟩`
  Lean version uses the equivalent form
  `2h ∑ᵢ bᵢ ⟨Fᵢ, Yᵢ⟩ − h² ∑ᵢⱼ (2bᵢaᵢⱼ − bᵢbⱼ) ⟨Fᵢ, Fⱼ⟩`. The
  coefficient `(2bᵢaᵢⱼ − bᵢbⱼ)` is the natural form coming from
  polarisation + the per-stage decomposition, before symmetrisation
  to `mᵢⱼ`. Same content. ✓

### `posSemidef_inner_form_nonneg` (Lemma 3)

* Statement: a real PSD matrix gives a non-negative quadratic form on
  arbitrary inner products `⟨Fᵢ, Fⱼ⟩` of vectors in any real
  inner-product space.
* Pure linear-algebra lemma; corresponds to the textbook's "Furthermore,
  a quadratic form of inner products … cannot be negative" sentence in
  the §357C proof. Same content. ✓

### `algebraicallyStable_isBNStable` (the theorem)

* Entity: `thm:357C`. Quoting `thm_357C.json:statement_latex`:
  > "If a Runge–Kutta method is algebraically stable then it is BN-stable."
* Lean statement: `IsAlgebraicallyStable M → IsBNStable M`.
* **Tautology check**: hypothesis `IsAlgebraicallyStable M`, conclusion
  `IsBNStable M`. Neither verbatim repeats the other; they are distinct
  predicates. ✓
* **Identity check**: proof body is non-trivial — extracts `A`-symmetry,
  applies Lemma 2 (the algebraic identity), bounds the first sum by
  dissipativity + `b > 0` + `h > 0`, bounds the second sum by Lemma 1 +
  Lemma 3, then concludes via `norm_le_of_norm_sq_le`. Real
  mathematical work. ✓
* **Hypothesis-strength check**: hypotheses are exactly
  `IsAlgebraicallyStable M`. No extra smoothness, no extra positivity,
  no extra regularity. ✓ (Caveat: the **predicate**
  `IsAlgebraicallyStable` itself is silently stronger than the textbook
  due to the symplecticity-matrix bug. The theorem is faithful relative
  to the predicate; the predicate's faithfulness is the topic of the
  filed issue.)
* **Definition-smuggling check**: BN-stability is the semantic
  norm-non-increase predicate (`def:357A`); algebraic stability is the
  matrix condition (`def:357B`). The theorem proves the matrix
  condition is sufficient for the semantic condition — a real
  implication. ✓

## Dead ends

* The cycle-033 strategy's Lemma 1 was stated without an `A`-symmetric
  hypothesis, claiming the bare equation
  `Σᵢⱼ (2 bᵢaᵢⱼ − bᵢbⱼ) ⟨Fᵢ,Fⱼ⟩ = Σᵢⱼ symplecticityMatrix M i j ⟨Fᵢ,Fⱼ⟩`.
  That statement is **false** in general because of the bug above (a
  two-stage counterexample is in the issue file). The fix was to add
  the A-symmetric hypothesis derived from `IsAlgebraicallyStable M`.

* Initial Lemma-2 attempt expanded `‖y₁‖² − ‖y₀‖²` via polarisation and
  tried to substitute the per-stage form `y₁ + y₀ = 2 Yᵢ + h Σⱼ
  (bⱼ − 2 aᵢⱼ) Fⱼ` into the inner product. The algebra was correct but
  the Lean proof became unwieldy due to nested `smul`/`Finset.sum`
  rewrites. Switched to a cleaner approach using `norm_add_sq_real`
  directly on `y₁ = y₀ + h • V` (with `V = Σⱼ bⱼ • Fⱼ`), then expressed
  `⟨y₀, Fᵢ⟩` via the i-th stage equation. Closed in ~50 lines.

* Aristotle returned `COMPLETE_WITH_ERRORS` for Lemmas 1 and 2 and
  `COMPLETE` for Lemma 3, but I had already finished the manual proofs
  by then. The Aristotle attempts can be inspected for future cycles
  if the manual proofs need refactoring (Lemma 3 had a working
  Aristotle proof that I didn't end up needing).

## Discovery

* **Critical**: the cycle-027 `symplecticityMatrix` definition is
  missing a transpose (`A diag(b)` should be `Aᵀ diag(b)`). This means
  `IsAlgebraicallyStable` silently restricts to RK methods with
  symmetric `A`, excluding most explicit and many implicit RK methods.
  See `.prover-state/issues/symplecticityMatrix_missing_transpose.md`.

* `Matrix.posSemidef_iff_eq_conjTranspose_mul_self` is now deprecated
  in favour of `CStarAlgebra.nonneg_iff_eq_star_mul_self`. The
  deprecated lemma still works for matrices but the new lemma's type
  is in a generic C\* algebra, which would need extra plumbing to use
  on `Matrix _ _ ℝ`. Kept the deprecated form for now (one warning); a
  future cycle could refactor.

* `Matrix.PosSemidef` includes `IsHermitian` as part of its definition.
  This is what made the symplecticity-matrix bug detectable: PSD
  silently forces matrix symmetry.

* `Finset.sum_comm` only swaps the **outermost** two summations; for
  three nested sums one needs `rw [show … from by refine …; exact
  Finset.sum_comm]` or `conv_lhs => ext i; rw [Finset.sum_comm]` to
  target the inner two.

## Suggested next approach

1. **Cycle 034 should fix the `symplecticityMatrix` bug** (issue file
   has the recommended one-line change). After the fix:
   - `algebraicallyStable_imp_A_symm` and the `hSym` hypothesis on
     Lemma 1 become unnecessary; the theorem proof simplifies by
     ~5 lines.
   - `IsAlgebraicallyStable` covers the textbook's intended class of
     methods (no longer silently restricted to symmetric `A`).

2. After the §357C chain, the natural next §357 target is
   **`thm:357D` — BN-stability ⇒ AN-stability** (already named in the
   `thm_357C.json` proof_text continuation). This requires the
   non-autonomous → autonomous reduction Butcher describes (real/imag
   parts of the linear test problem). It is mostly a routine corollary
   but needs `def:356A` (AN-stability) which is already available
   (cycle 030).

3. Replace the deprecated
   `Matrix.posSemidef_iff_eq_conjTranspose_mul_self` with the
   `CStarAlgebra` form once Mathlib provides a clean specialisation
   for matrices.
