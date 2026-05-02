# Cycle 074 Results

## Worked on

* **Priority 0**: Closed `thm_410A` (Section410.lean:300) — the
  general-`j` case of Butcher's §410 generating-function identity
  `α(exp(-z)) - z β(exp(-z)) = C₀ + C₁ z + C₂ z² + ⋯`.
* **Priority 1**: Updated `Section410.lean` file docstring + theorem
  docstring to reflect that the cycle 073 sorry is now closed.
* **Priority 1**: Updated artefacts — `lean_status.json::thm:410A`
  flipped to `formalized` with full notes;
  `plan.md::thm:410A` switched from `[ ]` to `[x]`; progress counter
  `43 → 44 of 175`.

## Approach

The strategy outlined the structural reduction: case split on `j`,
discharge `j = 0` via `thm_410A_zero`, and for `j = j' + 1` push
`Polynomial.aeval expNegPS` and `PowerSeries.coeff (j'+1)` through
the `1 - Σ` (α) and `Σ` (β) sums via `map_sub`/`map_one`/`map_sum`,
then reduce each monomial via `coeff_aeval_C_X_pow` (Aristotle,
cycle 073).

### α-side

```lean
unfold αPoly
rw [map_sub, map_one, map_sub, map_sum, map_sum]
simp only [PowerSeries.coeff_one, Nat.succ_ne_zero, if_false]
rw [zero_sub]
congr 1
apply Finset.sum_congr rfl
intro i _
rw [coeff_aeval_C_X_pow (M.α i.succ) (i.val + 1) (j' + 1)]
```

The first `map_sub` is the algebra-hom property of
`Polynomial.aeval` over `1 - Σ`; the inner `map_sum` is the
algebra-hom property over the `Σᵢ C(M.α i.succ) * X^(i+1)` sum.
The outer `map_sub`/`map_sum` push `PowerSeries.coeff (j'+1)`
through the resulting `1 - Σ`. `PowerSeries.coeff_one` plus
`Nat.succ_ne_zero` zeros out the constant term, and
`coeff_aeval_C_X_pow` matches each summand to its closed form.

### β-side

```lean
rw [PowerSeries.coeff_succ_X_mul]
unfold βPoly
rw [map_sum, map_sum]
apply Finset.sum_congr rfl
intro i _
rw [coeff_aeval_C_X_pow (M.β i) i.val j']
```

`PowerSeries.coeff_succ_X_mul`:
`coeff (n+1) (X * φ) = coeff n φ` peels off the leading `X`, so
the β-side reduces to `coeff j' (aeval expNegPS βPoly)`. Push-through
on `βPoly = Σᵢ C(M.β i) * X^i` is just two `map_sum` calls (no
`1 -` to handle). Per-monomial reduction via `coeff_aeval_C_X_pow`
with `c = M.β i`, `m = i.val`.

### Combine

```lean
rw [hα, hβ]
rfl
```

After substituting `hα` and `hβ`, the LHS is exactly the `j' + 1`
branch of `C M`'s pattern match, so `rfl` closes the goal.

## Result

**SUCCESS.**

* `lake env lean OpenMath/Chapter4/Section410.lean` — clean (only a
  pre-existing informational `Try this: ring_nf` from
  `coeff_aeval_C_X_pow`'s Aristotle-supplied proof; not an error).
* `lake build OpenMath.Chapter4.Section410` — exit 0, .olean refreshed.
* `#print axioms OpenMath.Chapter4.Section410.thm_410A` →
  `[propext, Classical.choice, Quot.sound]` (the standard Lean
  classical axiom set, no `sorryAx`).
* `grep -nE "^[[:space:]]*sorry" OpenMath/Chapter4/Section410.lean`
  → 0 hits. The two remaining "sorry" matches in the file are
  inside docstrings (lines 68, 294 in the cycle-073 draft; the
  docstring at 68 has been rewritten in this cycle, line numbers
  shift).

Net sorry count from `HEAD` (`7c69187`) to this cycle's commit:
`0 → 0` (Section410.lean was untracked in `7c69187`; the cycle
074 commit lands a new file with zero sorries, the Aristotle
helpers, and `thm_410A` closed). Progress counter: `43 → 44 of 175`.

## Faithfulness check

### `theorem thm_410A` (no other new defs/theorems this cycle)

* Entity ID `thm:410A`, textbook statement
  (`extraction/formalization_data/entities/thm_410A.json::statement_latex`):
  > The constants C₀, C₁, C₂, … in (410b) are given by
  > α(exp(−z)) − zβ(exp(−z)) = C₀ + C₁ z + C₂ z² + ⋯.   (410c)

* Lean statement captures: **same content**. The Lean theorem
  asserts that for every `j : ℕ`, the j-th `PowerSeries.coeff`
  of `Polynomial.aeval expNegPS (αPoly M) - PowerSeries.X *
  Polynomial.aeval expNegPS (βPoly M)` equals `C M j`. This is
  exactly the formal-power-series content of (410c).

* **Tautology check**: ✓ — LHS is a generating-function coefficient
  (computed via `aeval` substitution of `expNegPS`), RHS is the
  closed-form `C M j` defined directly from `M.α`/`M.β` per
  Butcher's proof. They are independently defined; the theorem
  asserts a substantive identity between them.

* **Identity check**: ✓ — the proof is a 30-line tactic block
  combining `map_sub`/`map_one`/`map_sum` push-throughs, an
  Aristotle helper (`coeff_aeval_C_X_pow`), and definitional `rfl`
  matching. Real mathematical work.

* **Hypothesis strength check**: ✓ — Butcher takes only an LMM
  (no preconsistency / consistency hypothesis). Our Lean statement
  is parameterised only by `M : LinearMultistepMethod k`. Matches
  exactly.

* **Sign convention**: documented in the file header (cycle 073).
  The `αPoly = 1 - Σ` form was verified by hand against explicit
  Euler in cycle 073, and the cycle-074 closure provides the
  rigorous confirmation that this convention matches Butcher's
  closed-form `C_j` formula.

## Dead ends

* The strategy's pseudo-Lean draft used `unfold C` followed by
  `ring`. The match block in `C M (j' + 1)` reduces only via
  pattern-match recognition, not via `ring`. Replacing
  `unfold C; ring` with `rfl` (after the final `rw [hα, hβ]`)
  works because the sums on the LHS are syntactically the
  `j' + 1` branch of `C M`.

* The strategy's pseudo-Lean also had `push_cast; ring` after each
  `coeff_aeval_C_X_pow` rewrite. These are unnecessary —
  `coeff_aeval_C_X_pow (c) (m) (j)` rewrites the goal to exactly
  `c * (-(m : ℝ))^j / (Nat.factorial j : ℝ)`, which definitionally
  matches the Finset.sum_congr summand `M.α i.succ *
  (-((i.val + 1 : ℕ) : ℝ))^(j'+1) / (Nat.factorial (j'+1) : ℝ)`.
  Removing the `push_cast; ring` lines kept the proof at ~30 LOC.

* Did not need separate helper lemmas (`coeff_aeval_αPoly_succ` /
  `coeff_X_mul_aeval_βPoly_succ`). The proof inlined cleanly under
  ~80 LOC, well below the strategy's decomposition threshold.

## Discovery

* **`PowerSeries.coeff_succ_X_mul`** (Mathlib) is the canonical
  name for the `coeff (n+1) (X * φ) = coeff n φ` identity. Useful
  in any future §410B/C/D work where the `z β(exp(-z))` term
  appears.

* **`map_sub`/`map_one`/`map_sum` chain through `aeval` then
  `coeff`.** Both `Polynomial.aeval` (algebra hom) and
  `PowerSeries.coeff (R := ℝ) j` (linear map) admit `map_sub` /
  `map_sum` directly. Stacking them in a single `rw [...]` works
  if the order matches the structural surface (`map_sub` first,
  then `map_sum` if there's an inner sum). For our `1 - Σ` α-side,
  the order is `map_sub, map_one, map_sub, map_sum, map_sum`
  (outer `aeval` on `1 - Σ` → `aeval(1) - aeval(Σ)` → `1 -
  Σ aeval(...)` after `map_one`/`map_sum`; then outer `coeff` on
  `1 - Σ aeval(...)` → `coeff(1) - Σ coeff(aeval(...))`).

* **`PowerSeries.coeff_one (n : ℕ)`** returns
  `if n = 0 then 1 else 0`. Combined with `Nat.succ_ne_zero` and
  `if_false`, the constant term cleanly drops to 0 in the
  `j = j' + 1` case.

* **Definitional `rfl` matching against pattern-match
  definitions.** `C M (j' + 1)` does not auto-reduce under
  `unfold C` (the match expression `match j' + 1 with...` blocks
  reduction). However, after substituting the explicit closed-form
  expressions for `coeff (j'+1) (aeval expNegPS αPoly)` and
  `coeff (j'+1) (X * aeval expNegPS βPoly)`, the LHS is exactly
  the body of the `j + 1` arm of `C`, and `rfl` closes the goal.
  This is cheaper than trying to `ring` through factorials.

## Suggested next approach

The §410 cluster opener is now landed. Natural follow-ups:

1. **`thm:410B`** ("Order Condition for LMM 410B") — the order
   characterisation `α(exp(z)) + z β(exp(z)) = O(z^{p+1}) ↔
   method has order p`. Needs `α(exp(z))` (note `+z`, not `-z`).
   One approach: define `expPS : PowerSeries ℝ` analogously to
   `expNegPS` (just with `1` instead of `(-1)^n`), prove a
   `coeff_aeval_C_X_pow_pos` analogue (or derive from
   `coeff_aeval_C_X_pow` via a sign flip), and define `IsOrderP`
   as `∀ j ≤ p, C M j = 0`. Estimated cycle: ~1 cycle.

2. **`C_one_eq_zero_iff_isConsistent`** — small bridge lemma
   connecting §410 to def:404B `IsConsistent`. The `j = 1` case
   of `C M j = 0` should equal the §404 consistency condition
   (after sign reconciliation). ~1 hour of work; useful for
   §405/§406 cross-references.

3. **`thm:410C`** ("Order condition via generating functions") —
   reformulates 410B in a way that's friendlier to numerical
   verification. Likely depends on 410B + a small `O(z^{p+1})`
   tower lemma. Estimated cycle: ~1 cycle.

4. **`thm:410D`** ("Order Condition for LMM 410D") — order
   condition with the residual L. Depends on 410A + 410B.

If §410 stalls, pivot to **`thm:431A`** (Schur stability,
self-contained per Butcher) or **`thm:422A`** (LMM as one-step
method). Both have zero §410 dependencies.

Section410.lean is now ~340 LOC; if §410B/C/D triple it, consider
splitting into `Section410A.lean` (current contents) and
`Section410BCD.lean` (order conditions).
