# Cycle 382 Results

## Worked on

§422 Phase α'.3 Family B closed-form helper `inversePolyBroom` (per the
cycle 382 strategy):

* New `broomTree : ℕ → RT` definition.
* Three name-equality theorems `broomTree_one/two/three`.
* New `noncomputable def inversePolyBroom (k : ℕ) (f : RT → ℝ) : ℝ`
  (closed-form binomial sum).
* Four closed-form calibration theorems
  `inversePolyBroom_zero/one/two/three`.

Inserted as a new Phase α'.3 block in `OpenMath/Chapter4/Section422.lean`
immediately after cycle 380's `inversePolyChain_three` (around line 4762).

## Approach

Followed the strategy verbatim. Closed-form sum:
`Σⱼ∈range(k+1), (-1)^(k+1+j) · C(k,j) · (f vertex)^(k-j) · f (broomTree j)`.

Initial proof attempt used `simp [broomTree, broomTree_one, ..., Nat.choose]`
followed by `ring`. This **failed** for `inversePolyBroom_one/two/three`
because `simp [broomTree]` unfolded `broomTree j` all the way to
`mk [vertex, ...]` form before the name theorems could fold it back to
`cherry`/`broom₃`/`bushy`. The unused-simp-arg linter flagged
`broomTree_one`/`_two`/`_three` as unused — a signal that simp normalized
in the wrong direction. `ring` then couldn't reconcile
`f (mk [vertex])` vs `f cherry` (definitional equality not visible inside
applied `f`).

**Fix**: rewrite via the name theorems (and a `show broomTree 0 =
RootedTree.vertex from rfl` inline rewrite for the `j=0` summand) BEFORE
running `simp`. The name theorems fire as targeted rewrites without
recursive simp unfolding. Then `simp [Nat.choose]` evaluates the
choose-coefficients and the `(-1)^n` literals, and `ring` closes.

For `inversePolyBroom_zero`, the simpler form `simp [broomTree]` worked
because `broomTree 0 = RootedTree.vertex` is the leaf case (no `mk`
unfolding needed). Kept that proof as is.

## Result

**SUCCESS** — all four closed-form theorems plus the three name
theorems compiled axiom-clean:

```
'broomTree_one'  : no axioms
'broomTree_two'  : no axioms
'broomTree_three': no axioms
'inversePolyBroom_zero'  : [propext, Classical.choice, Quot.sound]
'inversePolyBroom_one'   : [propext, Classical.choice, Quot.sound]
'inversePolyBroom_two'   : [propext, Classical.choice, Quot.sound]
'inversePolyBroom_three' : [propext, Classical.choice, Quot.sound]
```

Verification checklist (per strategy §E):

* `lake env lean OpenMath/Chapter4/Section422.lean` → exit 0
  (only warning: the grandfathered cycle 365 sorry at line 2272).
* `lake build OpenMath.Chapter4.Section422` → exit 0, 170s cold.
* `lake build OpenMath.Chapter4` (aggregator) → exit 0, 152s.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` → **5**
  (unchanged: 4 docstring references + 1 grandfathered code sorry).
* Tautology scanner regex `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`
  over Section422.lean → 0 hits.

LOC added: ~110 lines (within strategy budget of 80-120).

## Faithfulness check

Entity ID `def:422B` (underlying one-step method) — the new helpers
are Phase α'.3 *infrastructure* for the future Family B bridge
migration, not new textbook entities. Per strategy §F.9,
`def:422B` stays `partial` in `lean_status.json`.

For each new declaration this cycle:

### `broomTree : ℕ → RT`

* Not a textbook concept — internal helper enumerating
  `mk [vertex, …, vertex]` trees as `broomTree k`.
* Justified by cycle 379 §4 Family B classification + cycle 380's
  `chainTree` precedent for Family A.
* Concrete instance: `broomTree 0 = vertex`, `broomTree 1 = cherry`,
  `broomTree 2 = broom₃`, `broomTree 3 = bushy` (verified `rfl`).

### `broomTree_one/two/three`

* Pure naming equalities — each `:= rfl`.
* Not tautologies: they bridge the generic recursive definition
  `broomTree (n+1) = mk (List.replicate (n+1) vertex)` to the
  named small-tree aliases that downstream proofs use.

### `inversePolyBroom : ℕ → (RT → ℝ) → ℝ`

* Not a textbook concept — closed-form binomial sum for the
  inverse polynomial values on broom-family trees.
* Derived from cycle 368 Discovery: expanding `(Aᵢ − v)^k` and
  summing against `M.b i` yields the binomial-style sum.
* Verified against all four small-`k` closed forms (cycles 341,
  367, 368, 370) in the planner's sign verification table — no
  divergence.

### `inversePolyBroom_zero/one/two/three`

* These are closed-form *theorems*, not definitions. Each
  computes `inversePolyBroom k f` for `k ∈ {0,1,2,3}` and shows
  the result equals the corresponding cycle-341/367/368/370
  closed form.
* Lean statements capture: **same content** as cycles
  341 (vertex), 367 (cherry), 368 (broom₃), 370 (bushy).
* Cycle 341 vertex closed form `-Φ_η(τ)` ↔ `inversePolyBroom_zero
  f = -f RootedTree.vertex` ✓
* Cycle 367 cherry closed form `(Φ_η τ)² − Φ_η[τ]` ↔
  `inversePolyBroom_one f = (f vertex)^2 - f cherry` ✓
* Cycle 368 broom₃ closed form `-(Φ_η τ)³ + 2·Φ_η τ·Φ_η[τ] −
  Φ_η[τ,τ]` ↔ `inversePolyBroom_two f = -(f vertex)^3 + 2 · f
  vertex · f cherry - f broom₃` ✓
* Cycle 370 bushy closed form `(Φ_η τ)⁴ − 3·(Φ_η τ)²·Φ_η[τ] +
  3·Φ_η τ·Φ_η[τ,τ] − Φ_η[τ,τ,τ]` ↔ `inversePolyBroom_three f =
  (f vertex)^4 - 3·(f vertex)^2·f cherry + 3·f vertex·f broom₃ -
  f bushy` ✓

Hypothesis strength: each theorem takes only `(f : RT → ℝ)` — no
extraneous hypotheses about M, b, A, η, etc. The closed forms are
purely algebraic identities about `f` evaluated on the broom-tree
ladder.

Tautology / identity check: each proof unfolds
`inversePolyBroom`, expands the sum, rewrites `broomTree j` via the
name theorems, and closes by `simp [Nat.choose]; ring`. No proof
is a single `exact h_*` or `:= id`.

Definition smuggling check: `inversePolyBroom` is a sum, not the
characterization of a named mathematical concept. There is no
hidden definition of "inverse polynomial" being smuggled — the
genuine textbook concept (§385 group inverse / §387 D-operator
inverse) lives elsewhere. The helper is named-as-Sum and the
calibration theorems do the real work of matching the cycle
341/367/368/370 closed forms.

## Dead ends

1. **`simp [broomTree, broomTree_one, ...]` over-unfolds.** The
   first-try proof tactic unfolded `broomTree` as a recursive `def`
   all the way to `mk [vertex, ...]` form before the name theorems
   could fire. The unused-simp-arg linter caught it. Fix: use
   targeted `rw [broomTree_one, broomTree_two, ...]` rewrites
   before `simp`. Worth remembering for cycle 383+ Family B/C
   migrations.

## Discovery

**Targeted `rw` of name-equality theorems beats `simp [recursive-def, name-thm-1, name-thm-2, …]`.**
When you have a recursive `def D : ℕ → α` plus name theorems
`D_k : D k = aliasₖ`, `simp [D, D_k]` will eagerly unfold the def
all the way to `mk [...]` form before normalizing back via the name
theorems. The name theorems then become "unused" and the goal is
stranded in raw-constructor form. The cleaner pattern is

```lean
rw [Finset.sum_range_succ, …, Finset.sum_range_zero, zero_add,
    show D 0 = base from rfl, D_one, D_two, …]
simp [Nat.choose]
ring
```

This is the inverse of the `simp` instinct: with simp, more rewrites
usually means more closure; with name-equalities backed by a
recursive `def`, MORE simp rewrites unfolds-the-wrong-direction.
Worth recording for cycle 383+ as a Family B/C migration pattern.

## Suggested next approach

Per cycle 382 strategy §K and the planner's outlook:

1. **Cycle 383 (recommended primary)**: Family B bridge migration —
   replace the explicit `if-then-else` polynomial bodies for
   `broom₃` and `bushy` in `inversePolynomial`'s branches with
   `inversePolyBroom 2 f` and `inversePolyBroom 3 f`. Add two
   bridge theorems `inversePolyBroom_{two,three}_eq_inversePolynomial`
   (parallel to cycle 381's chain-bridge theorems). Update the
   matching Phase β bridges from cycles 368/370 and the Phase γ
   subtree-agreement theorem.

2. **Cycle 384+**: Family C scoping. The two Family C trees
   `mk [broom₃]` and `mk [vertex, cherry]` have heterogeneous
   children; they likely need a per-tree closed form or a
   `inversePolyFamilyC` helper indexed by tree shape rather than
   integer parameter.

3. **Cycle 385+**: Phase α'.4 closure of the cycle 365 grandfathered
   sorry. Requires Families A + B + C closed forms unified into a
   fully recursive `inversePolynomial` (or `inversePolyTree`)
   covering arbitrary `t`, plus the global bridge
   `elementaryWeightQ_phi_inv_eq_inversePolynomial`.

The cycle 382 ship is the Family B counterpart of cycle 380's Family
A helper; cycle 383 will be the Family B counterpart of cycle 381's
Family A bridge. Two more cycles of Family B+C scoping/bridge work,
then the grandfathered sorry can be tackled in earnest.
