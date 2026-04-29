# Cycle 029 Results

## Worked on

* `def:356B` — DJ-reducibility predicate (Butcher §356, p. 268).
* DJ-irreducibility component of `def:356A` (same page).
* New file `OpenMath/Chapter3/Section356.lean`.
* Imports plumbing in `OpenMath/Chapter3.lean`.
* Issue file `AN_stability_deferred.md` documenting the deferral of
  the AN-stability component of `def:356A`.

## Approach

Followed cycle 029 strategy verbatim:

1. **Predicates**. Wrote `IsDJReducibleVia` (the conjunctive zero
   conditions on a 2-block partition), `IsDJReducible` (with both
   `S` and `S₀` non-empty — the spirit-of-the-theorem strengthening
   of Butcher's "S₀ non-empty" — see file docstring for the vacuity
   argument that motivates this), and `IsDJIrreducible` (negation).
   Predicates are placed in the
   `OpenMath.Chapter3.Section312.RKTableau` namespace mirroring
   `Section381.lean`'s `IsZeroReducibleVia` / `IsZeroReducible` /
   `IsIrreducible` pattern, so users write `M.IsDJReducible`.
2. **Compile check**. `lake env lean OpenMath/Chapter3/Section356.lean`
   passed after fixing one identifier (`Bool.true_ne_false` is not in
   the current Mathlib snapshot — replaced with `simp_all` which
   discharges the `true = false` contradiction directly).
3. **`explicitEuler_isDJIrreducible`**. Used the `Fin 1` cardinality
   trick: any partition with both sides non-empty would force the
   unique stage `0` to satisfy `inS 0 = true ∧ inS 0 = false`, which
   `simp_all` discharges after `fin_cases` on both witnesses.
4. **`paddedEuler` reducibility witness**. Defined `paddedEuler` locally
   (duplicating `Section381.paddedEuler` to keep `Section356`
   independent of `Section381` per textbook order), and proved both
   `IsDJReducibleVia` (via `inS = ![true, false]`) and
   `IsDJReducible`. The `j = 0` case (`inS 0 = true`) is impossible
   because the hypothesis is `inS 0 = false`, so `simp at hj` closes
   it; the `j = 1` case discharges `b 1 = 0` via `rfl` and the
   inner-zero condition via `simp [paddedEuler]`.
5. **Issue file**. Wrote `AN_stability_deferred.md` cataloguing
   what AN-stability would require (complex matrix resolvent
   `(I − A Z)⁻¹`, left-half-plane condition, magnitude bound), the
   downstream consumers that depend on it (`thm:356C`, `cor:356D`,
   `thm:357C/D`), and the recommended resolution (a dedicated cycle).
6. **Status updates**. `lean_status.json`: `def:356B` → `formalized`,
   `def:356A` → `in_progress` with a `notes` pointer to the issue
   file. `plan.md`: `def:356B` → `[x]`, `def:356A` → `[~]`,
   progress counter 29 → 30.

## Result

**SUCCESS.**

* `lake env lean OpenMath/Chapter3/Section356.lean` — clean.
* `lake build` — clean (2844/2844 jobs).
* `#print axioms` for `IsDJReducible`, `IsDJIrreducible`, and
  `explicitEuler_isDJIrreducible` — only `[propext, Classical.choice,
  Quot.sound]`.
* `rg --pcre2 '(?<!--\s)sorry' OpenMath/` — zero hits.
* Tautology scanner — zero hits.

## Faithfulness check

### `def:356B` → `RKTableau.IsDJReducible` and `IsDJReducibleVia`

* Entity ID and textbook statement (quoted from `def_356B.json`):
  > A Runge–Kutta method is 'DJ-reducible' if there exists a
  > partition of the stages `{1, 2, …, s} = S ∪ S₀`, with `S₀`
  > non-empty, such that if `i ∈ S` and `j ∈ S₀`, `b_j = 0` and
  > `a_{ij} = 0`.

* Lean statement captures: **stronger** (deliberate, documented).

* Justification for divergence: Butcher requires only `S₀` non-empty.
  Reading literally, taking `S = ∅, S₀ = {1, …, s}` makes the
  `(i ∈ S ∧ j ∈ S₀) →` antecedent vacuously false for every method,
  so every tableau would be DJ-reducible and DJ-irreducibility would
  have no models. Butcher's later usage (e.g. `cor:356D` asserting
  `b_i > 0` *under* DJ-irreducibility, vacuous on the literal
  reading) requires the spirit-of-the-theorem reading where both
  sides are non-empty. We therefore add `(∃ i, inS i = true)` to
  `IsDJReducible`, mirroring the analogous `P₀ ≠ ∅` strengthening on
  `IsZeroReducible` in `Section381.lean`. Documented at the
  definition site and in the file docstring.

### `def:356A` (DJ-irreducibility component) → `RKTableau.IsDJIrreducible`

* Entity ID and textbook statement (quoted from `def_356A.json`):
  > we identify 'irreducibility in the sense of Dahlquist and
  > Jeltsch', or 'DJ-irreducibility', (Dahlquist and Jeltsch, 1979)
  > as the property that a tableau cannot be reduced in the sense
  > of Definition 356B.

* Lean statement captures: **same content** (negation of
  `IsDJReducible`, which is faithful to def:356B per above).

* Note: `def:356A` also introduces AN-stability (first sentence,
  `R(Z) = 1 + b'Z(I − AZ)⁻¹𝟏` boundedness condition). That
  component is **deferred** to a dedicated cycle and is documented
  in `.prover-state/issues/AN_stability_deferred.md`. The
  `lean_status.json` entry for `def:356A` is `in_progress` (not
  `formalized`), with the `notes` field pointing at the issue.

### `explicitEuler_isDJIrreducible` (helper theorem)

* Not a textbook entity; a non-vacuity witness for
  `IsDJIrreducible`. Does real work (constructs a contradiction
  from the partition data via `fin_cases` and `simp_all`); not
  vacuous.

### `paddedEuler` (helper definition) and DJ-reducibility examples

* Local copy of `Section381.paddedEuler`. The two examples
  (`paddedEuler.IsDJReducibleVia ![true, false]` and
  `paddedEuler.IsDJReducible`) are the non-vacuity witnesses for
  `IsDJReducible`. Both proofs do real work.

## Dead ends

* `Bool.true_ne_false` is not (or not yet) a constant in the current
  Mathlib snapshot. Switched to `simp_all`, which closes the
  resulting `true = false` contradiction directly. Took ~30 seconds
  to identify and fix.

## Discovery

* The `paddedEuler` tableau is now duplicated across `Section356.lean`
  and `Section381.lean`. A future refactor could share the witness via
  a dedicated helpers file (e.g. `OpenMath/Chapter3/Helpers/Paddings.lean`),
  but textbook ordering makes it cleaner to keep `Section356`
  independent of `Section381` for now. The duplication is one short
  `def` and is well-flagged with cross-reference comments.
* The `IsDJReducibleVia` / `IsDJReducible` split (zero conditions
  factored out, non-emptiness in the outer `∃`) matches the
  `Section381` `IsZeroReducibleVia` / `IsZeroReducible` pattern
  exactly. The two reducibility predicates are mathematically
  related — DJ-reducibility is essentially 0-reducibility with both
  sides of the partition non-empty — and a future
  `IsDJReducible_iff_IsZeroReducible_with_both_sides_nonempty`
  equivalence in `Section381.lean` would be a natural faithfulness
  bonus. Skipped this cycle to keep the deliverable focused.

## Suggested next approach

The cycle 029 strategy listed three natural follow-ups; ordered by
unblocking power:

1. **AN-stability machinery for `def:356A`** — the explicit deferral
   target. Builds the complex matrix resolvent infrastructure
   (`(I − A Z)⁻¹`, left-half-plane condition, `R(Z)` magnitude
   bound). Once landed, `def:356A` can be flipped from `in_progress`
   to `formalized`, and the §357 stability stack
   (`thm:357C/D`) gains its prerequisite. This is the **highest-value
   next step**.
2. **`def:381A` (`equivalent`)** — pure §381 leaf. `Section381`
   already has `PhiEquivalent` and the reducibility predicates;
   defining the broader "equivalent" notion (likely as
   "Φ-equivalent up to reducibility" or a coarser quotient) is the
   next §381 building block. Read `entities/def_381A.json` first to
   confirm the textbook formulation.
3. **`def:323A` (internal order `q`)** — pure scalar definition,
   no stability infrastructure needed. Quick win if AN-stability
   proves too heavy for the next cycle.

The strategy explicitly warns against `thm:356C` and `cor:356D`
without AN-stability, so those should remain blocked until item 1
lands.
