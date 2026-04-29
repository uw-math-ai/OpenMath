# Cycle 019 Results

## Worked on
`def:381B` — Φ-equivalence of Runge–Kutta methods (Butcher §380, p. 302),
plus the three reflexivity / symmetry / transitivity API lemmas
(`PhiEquivalent.refl/symm/trans`) and a non-reflexive sanity witness
(equality of elementary weights of `explicitEuler` and a 2-stage
`paddedEuler` on `RootedTree.vertex`).

## Approach
Followed the strategy verbatim:

1. State sanity (sorry = 0, tautology regex = 0, Section312 builds) — all clean.
2. Read `extraction/formalization_data/entities/def_381B.json` and
   confirmed the textbook statement (verbatim quote: "Two Runge–Kutta
   methods are 'Φ-equivalent' if, for any t ∈ T, the elementary weight
   Φ(t) corresponding to the first method is equal to Φ(t)
   corresponding to the second method").
3. Created `OpenMath/Chapter3/Section381.lean` with the recommended
   signature: `PhiEquivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s')`
   parametrised on independent stage counts to support reducibility.
4. API lemmas: `PhiEquivalent.refl = fun _ => rfl`,
   `PhiEquivalent.symm = fun t => (h t).symm`,
   `PhiEquivalent.trans = fun t => (h₁ t).trans (h₂ t)`. All
   one-liners; no Aristotle round-trip needed.
5. Sanity witness: defined `paddedEuler : RKTableau 2` (zero matrix
   `A`, weight vector `![1, 0]`, abscissae `0`) and checked the
   single-vertex elementary weights coincide with `explicitEuler`'s
   via `simp` on `derivativeWeight_vertex` and `Fin.sum_univ_two`.
6. Added `import OpenMath.Chapter3.Section381` to `OpenMath/Chapter3.lean`.
7. `lake env lean OpenMath/Chapter3/Section381.lean` — clean (one
   unused-simp-arg lint that I removed by dropping
   `Fin.sum_univ_one`).
8. `lake build` — full project clean.
9. `#print axioms` on all four declarations: each depends on
   `[propext, Classical.choice, Quot.sound]` only (the standard set).
10. Re-ran tautology and sorry scanners: 0 hits each.
11. Updated `lean_status.json` (`def:381B` row → formalized) and
    `plan.md` (counter 19 → 20, row marked `[x]`).

## Result
SUCCESS. `def:381B` is formalized with reflexivity, symmetry, and
transitivity lemmas plus a non-vacuous example witness. All build,
axiom, and scanner checks pass. Five downstream entities (`def:370A`,
`def:381A`, `def:381C`, `def:422B`, `thm:381G`) are now unblocked.

## Faithfulness check

### `PhiEquivalent` (def:381B)
- Entity ID and textbook statement (quoted from
  `extraction/formalization_data/entities/def_381B.json`):
  > Two Runge–Kutta methods are 'Φ-equivalent' if, for any `t ∈ T`,
  > the elementary weight `Φ(t)` corresponding to the first method
  > is equal to `Φ(t)` corresponding to the second method.
- Lean statement captures: **same content**.
  `∀ t : RootedTree, M.elementaryWeight t = M'.elementaryWeight t` is
  a verbatim translation. The two methods are parametrised by
  independent stage counts `s` and `s'`, matching the textbook's
  surrounding-context use (reducibility = replacing a method by one
  with fewer stages).
- Definition smuggling: no later theorem's conclusion is baked in.
  The condition "elementary weights agree on every tree" *is* the
  definition; downstream theorems like `thm:381G` (irreducible RK
  methods are Φ-equivalent iff their stage indices are pairwise
  distinguishable) must be proved, not assumed.

### `PhiEquivalent.refl` / `.symm` / `.trans`
- These are the reflexivity / symmetry / transitivity facts implicit
  in the textbook's "is equal to" framing; Butcher does not
  separately label them.
- Tautology check: none of the conclusions appear verbatim as
  hypotheses. Each is doing real (definitional) work
  (`refl` exhibits the proof `fun _ => rfl`; `symm` and `trans`
  invoke `Eq.symm` / `Eq.trans` pointwise).
- Identity check: `refl` is `fun _ => rfl` — the standard Lean idiom
  for reflexivity. Not a vacuous `exact h` re-export.

### `paddedEuler` (helper / sanity witness, no entity ID)
- Internal helper, not a textbook concept. Defined to demonstrate
  that two distinct tableaux of different stage counts can produce
  the same elementary weight on the single-vertex tree, witnessing
  non-vacuity of `PhiEquivalent`.
- The `example` uses a vertex-only check (per strategy guidance to
  avoid blocking on full structural induction over `RootedTree`); the
  witness IS a step short of a full `PhiEquivalent explicitEuler
  paddedEuler` proof, but is sufficient to demonstrate the relation
  is non-trivially inhabited.

## Dead ends
None. The strategy's recommended one-liner proofs went through on the
first attempt. The only build hiccup was an unused-simp-arg lint
warning on `Fin.sum_univ_one` (1-stage Euler sums collapse without
needing it), which I removed.

## Discovery
1. `simp` on the elementary-weight equality with
   `RKTableau.derivativeWeight_vertex` + `Fin.sum_univ_two` is
   sufficient to dispatch the vertex-only Φ-equivalence check between
   `explicitEuler` and `paddedEuler`. `Fin.sum_univ_one` is not needed
   because `simp` already handles 1-element `Fin.sum` reductions.
2. `RKTableau` does not have `funext`-style equality issues at the
   vertex level — both sides reduce cleanly because the tree
   `RootedTree.vertex = mk []` makes `derivativeWeightProd _ _ [] = 1`
   by `rfl`, and the remaining sum is just over the `b`-vector.
3. `paddedEuler` with `A := 0`, `c := 0`, `b := ![1, 0]` is a clean
   minimal example; using `Matrix.zero` (`A := 0`) avoids any
   `!!`-notation or per-entry specification.

## Suggested next approach
The next natural Chapter 3 target depends on Planner judgment, but
the unblocked downstream chain from `def:381B` plus the planner's
own stretch suggestion gives a clear menu:

- **`def:381D` "P-reducible"** (planner's stretch suggestion). Needs
  `Classical.choose` plumbing for block representatives; one cycle
  of work. Pairs naturally with `def:381A` and `def:381C` once those
  land.
- **`def:381A` "S-reducible"** is a closer twin of `def:381B` and
  often paired with it in Butcher; might be a smaller next step than
  `def:381D`.
- **`def:381C` "P-equivalent"** depends on `def:381B` directly and
  is the natural follow-up: P-equivalence is defined in terms of
  Φ-equivalence after P-reduction, so it can land once P-reduction
  itself is in place.

For Chapter 3 infrastructure work that would unblock larger swathes:
**`thm:306A`** (Taylor's theorem bridge to `iteratedFDeriv` /
`taylorWithinEval`) is a non-trivial cycle that would unblock
`lem:310B`, `thm:311B/C/D` (the elementary-differential analytic
expansion theorems). Worth Planner consideration when ready to
invest a full cycle on bridge-building.

I did **not** pursue the stretch target this cycle: the primary
target plus housekeeping is complete and tested. Splitting `def:381D`
into its own focused cycle keeps the supervisor's grading granularity
intact (one entity per commit), as the strategy explicitly suggested.
