# Cycle 171 Results

## Worked on

* **Priority 0** — verified the cycle 170 phantom verdict.
* **Priority 1** — opened the §441 cluster: created
  `OpenMath/Chapter4/Section441.lean` with the `aPoly`
  polynomial-construction definition, an axiom-clean
  non-vacuity witness for explicit Euler, and the headline
  `aPoly_even_coeff_neg` (`lem:441B`) as a `sorry` for
  multi-cycle (Phase B/C) closure.

## Approach

### Priority 0 — phantom verdict resolution

Ran the strategy's verification checks. All passed:

* `git log -1` → `101ff07 Cycle 170 — thm:431A predicate ...`
* `ls -la OpenMath/Chapter4/Section431.lean` → 11856 bytes, present.
* `git show --stat 101ff07 -- OpenMath/Chapter4/Section431.lean`
  confirms the file is in the cycle-170 commit.
* `grep -c sorry OpenMath/Chapter4/Section431.lean` → `0`.
* `lake env lean OpenMath/Chapter4/Section431.lean` → exited 0.

The cycle 170 supervisor verdict ("score=0, no Lean source
changes") was a **false alarm** in the same shape as cycles
008/035/073. The cycle 170 work was committed correctly.

### Priority 1 — §441 Phase A

1. Read `extraction/formalization_data/entities/lem_441B.json`,
   `Section404.lean::LinearMultistepMethod`,
   `Section404.lean::explicitEulerLMM`, and
   `Section410.lean::αPoly` to fix the sign convention.
2. Created `OpenMath/Chapter4/Section441.lean` with three
   declarations:
   * `LinearMultistepMethod.aPoly` (in the
     `OpenMath.Chapter4.Section404.LinearMultistepMethod`
     namespace so dot-notation `M.aPoly` resolves).
   * `explicitEulerLMM_aPoly_eq` — non-vacuity witness
     (`explicitEulerLMM.aPoly = 2 * Polynomial.X`).
   * `LinearMultistepMethod.aPoly_even_coeff_neg` —
     headline `lem:441B`, `sorry`'d, multi-cycle plan
     documented in the docstring.
3. Added `import OpenMath.Chapter4.Section441` to
   `OpenMath/Chapter4.lean`.
4. Updated `extraction/formalization_data/lean_status.json`:
   `lem:441B` → `partial`, file
   `OpenMath/Chapter4/Section441.lean`, symbol
   `aPoly_even_coeff_neg`.
5. Updated `plan.md`: `lem:441B` `[ ]` → `[~]` with cycle 171
   note.

### Aristotle batch

Per the strategy's own caveat ("Do NOT batch-submit
`aPoly_even_coeff_neg` to Aristotle in cycle 171 — needs the
(441c) recurrence as input"), no Aristotle batch was submitted
this cycle. The optional Phase B (441c) recurrence batch is a
cycle 172 deliverable, not a cycle 171 one.

### Removed scope: degree lemma

Strategy step 4 listed an optional `aPoly_natDegree_le_k`
degree lemma. My first attempt used `Finset.fold_max_le` which
turned out not to exist as named (Mathlib uses
`Finset.sup_le` plus `Polynomial.natDegree_sum_le` returning a
`Finset.sup` bound). The strategy explicitly says "Skip if
Phase A's witness step takes more than 1 hour" so I dropped
the degree lemma to keep Phase A reliable. The Phase B plan
(in the file's docstring) explicitly takes responsibility for
this lemma in cycle 172+.

## Result

**SUCCESS.**

* `lake build OpenMath.Chapter4.Section441` exits 0
  (one expected `sorry` warning at line 128).
* `#print axioms OpenMath.Chapter4.Section441.explicitEulerLMM_aPoly_eq`
  → `[propext, Classical.choice, Quot.sound]` (axiom-clean).
* `#print axioms OpenMath.Chapter4.Section404.LinearMultistepMethod.aPoly`
  → `[propext, Classical.choice, Quot.sound]` (axiom-clean).
* Sorry count delta: 0 → 1 (the planned `aPoly_even_coeff_neg`
  headline).

## Faithfulness check

### `LinearMultistepMethod.aPoly` (definition)

* **Entity ID**: `lem:441B` context (preamble of the lemma's
  `entities/lem_441B.json`):
  > `a(z) = (1+z)^k − α₁(1+z)^{k−1}(1−z) − α₂(1+z)^{k−2}(1−z)² − ⋯ − αₖ(1−z)^k`
* **Lean statement captures**: same content. The Lean encoding
  uses `M.α i.succ` for `i : Fin k` to pick out Butcher's
  `αᵢ` (i.e. `α₁, …, αₖ`), with the `(1+X)`/`(1−X)` exponents
  matching textbook indices (k − (i+1) and i+1 respectively).
* **Sign convention**: matches Butcher one-to-one. The §404
  encoding stores `M.α 0 = -1` (the leading-coefficient
  normalisation) and `M.α (i+1) = αᵢ₊₁` (Butcher); since
  Butcher's `a(z)` only references `α₁, …, αₖ`, the
  `M.α 0 = -1` slot is irrelevant here, and the `M.α i.succ`
  selection is faithful.
* **Definition smuggling check**: `aPoly` is defined by
  Butcher's *primary* formula
  `(1+z)^k − Σ αᵢ (1+z)^{k−i} (1−z)^i`, NOT by its
  c-coefficient expansion `c₀ + c₁z + c₂z² + ⋯`. The
  c-coefficients are *outputs* (computed via
  `Polynomial.coeff`) of the polynomial. Defining the
  polynomial by its coefficients would be smuggling and is
  avoided here.

### `explicitEulerLMM_aPoly_eq` (witness)

* **Entity ID**: derived from `lem_441B.json`'s formula
  applied to `explicitEulerLMM` (k=1, α₁=1).
* **Lean statement captures**: same content. The closed form
  `2X` follows from `(1+z) − 1·(1+z)^0·(1−z)^1 = 2z`,
  matching the textbook formula evaluated at the explicit
  Euler coefficients.
* **Tautology check**: the conclusion `aPoly = 2X` is a
  derived equality, not a hypothesis (no hypotheses).
* **Identity check**: the proof body is
  `unfold; simp [explicitEulerLMM]; ring`, which is
  genuinely doing work — unfolding the polynomial, expanding
  the singleton sum over `Fin 1`, evaluating the if-then-else
  in `explicitEulerLMM.α`, and ring-normalising the
  polynomial expression. Not a vacuous re-export.

### `LinearMultistepMethod.aPoly_even_coeff_neg` (sorry'd)

* **Entity ID**: `lem:441B`. **Textbook statement**:
  > "The coefficients $c_2, c_4, \dots$ are all negative."
  (`lem_441B.json::statement_latex`)
* **Lean statement captures**: same content (with explicit
  index range `2 ≤ 2*n ≤ k` instead of leaving "..." informal).
  The hypothesis `M.IsStable` matches the `lem:441B`
  context (the lemma sits inside §441's
  "Maximum order for a convergent k-step method" subsection,
  which assumes stability via the convergent⇒stable
  direction; this is consistent with the dependents
  `thm:441C`/`lem:441A`).
* **Absent theorem check**: the docstring explicitly states
  the (441c) recurrence and base cases are NOT yet
  formalised — they are the cycle 172+ deliverable. No
  promise of unwritten content.
* **Hypothesis strength check**: the `M.IsStable` hypothesis
  is exactly what Butcher's surrounding §441 paragraph
  implicitly assumes (the proof of `lem:441B` uses the
  `a(z)`-non-negative-coefficient claim from the immediately
  preceding paragraph, which itself rests on stability via
  the stability⇒zeros-in-closed-disc characterisation
  matched to `thm:431A`/§431). The hypothesis is no
  stronger than the textbook requires.
* **Sorry status**: deliberate, planned, documented.

## Dead ends

1. **First file layout** — defined `aPoly` in the
   `Section441` namespace; the projection `M.aPoly`
   then failed because Lean's dot-notation looks up the
   function in the type's namespace
   (`Section404.LinearMultistepMethod`), not the file's
   active namespace. Fixed by moving `aPoly`'s `def` into
   `namespace OpenMath.Chapter4.Section404` (and keeping
   subsequent theorems in `Section441`).
2. **`Finset.fold_max_le`** — does not exist as named in
   our Mathlib snapshot. The path used by Section410
   (`Finset.sup_le` after `natDegree_sum_le`) is the
   correct shape. I dropped the optional degree lemma
   rather than fight this; the file's docstring assigns it
   to Phase B (cycle 172+).

## Discovery

* **Dot notation requires same-namespace `def`** —
  Lean 4's dot notation `M.aPoly` looks up the function in
  the *type*'s namespace, not the calling file's namespace.
  When defining a method on a type from another file,
  `def TypeNs.TypeName.method ... :=` must be inside
  `namespace TypeNs.TypeName` (or the inverted-period form).
  Strategy explicitly anticipates this; I confirmed it
  empirically.
* **`Finset.sup_le` is the right entry point for
  polynomial-sum degree bounds** —
  `Polynomial.natDegree_sum_le` returns a `Finset.sup`
  bound, then `Finset.sup_le` reduces to a per-summand
  bound. (See `Section410.lean::αPoly_natDegree_le` for
  the canonical recipe.) Save for cycle 172.

## Suggested next approach

For **cycle 172** (Phase B):

1. **Degree bound**: prove `M.aPoly.natDegree ≤ k` using
   `Section410.lean::αPoly_natDegree_le`'s recipe
   (`Finset.sup_le` after `Polynomial.natDegree_sum_le`,
   plus `Polynomial.natDegree_mul_le` and a
   `Polynomial.natDegree_pow_le_of_natDegree_le`-style
   bound for `(1±X)^m`).
2. **(441c) recurrence and base cases**: define the c-coefficient
   sequence as `c i := M.aPoly.coeff i` and state
   * `c 0 = 1/2 - (Σ M.α i.succ)/2`-ish (closed form via
     `eval 0` or `coeff 0` and the binomial expansion),
   * `c 2 = ...` (base case — Butcher's (441c) gives
     `c 2 = -1/6` for stable LMMs).
   These are essentially `Polynomial.coeff` extractions;
   should be Aristotle-friendly modulo the `(1±X)^m`
   coefficient expansions.
3. **Aristotle batch (start of cycle 172)**: submit
   * the (441c) recurrence statement,
   * the `c 0 = 1/2`, `c 2 = -1/6` base cases,
   * the degree bound,
   in a single batch and sleep 30 min.
4. **Phase C (cycle 173)**: induction on `n` per Butcher.
   The crux is the `2n+1 − (2n−1)z²` multiplication trick
   (441d). This will likely need Mathlib's
   `Polynomial.coeff_mul` plus careful index arithmetic.

For the **standing phantom-verdict pattern**: the strategy
explicitly says do not modify `scripts/autonomous_loop.py`;
that's loop-maintainer territory. The standing issue
`tautology_scanner_false_positives.md` already documents the
pattern. No new issue file needed this cycle.
