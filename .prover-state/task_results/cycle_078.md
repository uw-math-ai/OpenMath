# Cycle 078 Results

## Path taken
**Path B** (pivot to `lem:383A`). Aristotle was still in progress on the
cycle 077 §410D submission, so per the strategy's decision rule the
§410D rebuild was off-limits.

## Aristotle status report
Project `18504be5-2481-4d60-9d7b-12b8a5cd2b47` (cycle 077 submission of
the five §410D helper sub-lemmas) was still `IN_PROGRESS` at start of
cycle 078: 13% complete, ~2 hours elapsed since creation. No new
proofs available. Per CLAUDE.md "do not poll Aristotle more than once
per cycle" rule, no further status checks were performed this cycle.
Project will be re-checked in cycle 079.

## Worked on
* **`lem:383A`** (Butcher §383, page 287, "The Runge–Kutta group" —
  convolution of multiplicative forest mappings is multiplicative).
  Closed in `OpenMath/Chapter3/Section383.lean` as
  `OpenMath.Chapter3.Section383.multiplicative_conv`.
* Bookkeeping: marked `thm:406D` `[x]` in `plan.md` (it was already
  `formalized` in `lean_status.json` per cycle 068, but plan.md was
  stale); updated progress counter from 46/175 → 50/175 (47 + 1 newly
  closed lem:383A + 2 already-formalized def:381B/D + 1 stale
  thm:406D).

## Approach

### Faithfulness deviation from the planner's Path B sketch

The planner's Path B sketch defined `multiplicative_mul` as the
**pointwise** product `(αβ)(S) = α(S) · β(S)`. This is **not** what
Butcher's lemma 383A is about. Butcher's product, equation (383a)
quoted from the entity JSON:

> `(αβ)(S) = Σ_{R ⊑ S} α(S \ R) β(R)`

is the **convolution** product over sub-forests. The pointwise product
trivially preserves multiplicativity (one line, `simp`), but it is a
different algebraic object — the convolution defines the Runge–Kutta
group structure of §383 onwards (used in lem:383B associativity,
lem:383C inverses, and the connection to the elementary weights). I
could not in good faith ship the pointwise version under the name
`lem:383A`; the CLAUDE.md "definition smuggling" check explicitly
forbids this (the *characterization theorem* — that pointwise is
multiplicative — is trivial and a totally different statement than
what Butcher proves).

So I implemented the faithful convolution version.

### Implementation

Created `OpenMath/Chapter3/Section383.lean` with:

1. `noncomputable instance : DecidableEq RootedTree := Classical.decEq _`
   — needed because `Multiset.sub` requires `DecidableEq` on the carrier
   and the auto-`deriving` handler does not fire on the nested-inductive
   `RootedTree | mk : List RootedTree → RootedTree`. Per cycle strategy
   (do not modify Section310.lean), the instance is added in this file.

2. `abbrev Forest := Multiset RootedTree` — Butcher's forest as an
   unordered collection of trees with multiplicities.

3. `IsMultiplicative (α : Forest → ℝ) : Prop := α 0 = 1 ∧ ∀ s t, α(s+t) = α s * α t`
   — the predicate-style multiplicativity hypothesis.

4. `noncomputable def convProduct (α β : Forest → ℝ) (S : Multiset RootedTree) : ℝ`
   — the convolution product
   `(αβ)(S) = Σ_{R ∈ S.powerset} α(S - R) * β(R)`. Note `S.powerset`
   counts sub-multisets *with multiplicity* (e.g. `({a,a}).powerset`
   lists `{a}` twice), which is the right combinatorial interpretation:
   each "way of selecting a sub-forest" contributes once. Without this
   weighting, the lemma would be false in the duplicate-tree case.

5. `_PowersetAdd.powerset_add` (private helper) —
   `(s + t).powerset = (s.powerset ×ˢ t.powerset).map (· + ·)`. Proved
   by induction on `t` using `Multiset.powerset_cons` and
   `Multiset.product_add`. **This lemma is not in Mathlib at the time
   of writing** (May 2026); the inductive proof is ~10 lines.

6. `_PowersetAdd.sum_mul_sum_eq_sum_product` (private helper) —
   `(s.map f).sum * (t.map g).sum = ((s ×ˢ t).map (fun p => f p.1 * g p.2)).sum`.
   The additive analogue of `Multiset.prod_map_product_eq_prod_prod`.
   Proved by induction on `s` using `Multiset.sum_map_mul_left`.

7. `multiplicative_conv` — the lemma 383A statement. Three-step proof:
   (a) Apply `powerset_add` to express the sum on `(S+T).powerset` as
       a sum on `S.powerset ×ˢ T.powerset`.
   (b) Pointwise rewrite each summand via `Multiset.sum_map_congr`
       using multiplicativity of `α` and `β`, plus the identity
       `(S+T) - (R₁+R₂) = (S-R₁) + (T-R₂)` (true when `R₁ ≤ S, R₂ ≤ T`,
       proved by extensionality on `count`).
   (c) Apply `sum_mul_sum_eq_sum_product` to factor the resulting sum
       into `(αβ)(S) * (αβ)(T)`.

8. `isMultiplicative_const_one` — non-vacuity witness (the constant
   function `Forest → ℝ, _ ↦ 1` is multiplicative).

## Result

**SUCCESS.**

* `lake build OpenMath.Chapter3.Section383` — clean (3.0s incremental).
* `#print axioms OpenMath.Chapter3.Section383.multiplicative_conv` →
  `[propext, Classical.choice, Quot.sound]` (the latter is now
  load-bearing because of the `Classical.decEq` instance for
  `RootedTree`; Mathlib's `Multiset` proofs would already pull in
  `Quot.sound` regardless, so this is no expansion of the trusted
  base).
* `#print axioms OpenMath.Chapter3.Section383.isMultiplicative_const_one`
  → same clean axiom set.
* No new `sorry` introduced anywhere in the repo.

## Faithfulness check

### `Forest := Multiset RootedTree`

* Textbook (Butcher §383, page 287, raw_text/ch03.txt:8849-8854):
  > "By a 'forest', we mean a set of vertices V and a set of edges E
  > such that each edge is an ordered pair of members of V under the
  > restrictions that each vertex appears as the second member of at
  > most one edge."

  Butcher then partitions `(V, E)` into connected components, each a
  rooted tree.

* Lean: `abbrev Forest := Multiset RootedTree`, an unordered
  collection of rooted trees with multiplicities.

* Captures: **same content** modulo a deliberate identification — we
  identify forests up to graph isomorphism on each component and
  forget vertex labels (since the only operations Butcher performs on
  forests in §383 — multiset addition, sub-forest enumeration via
  powerset, and "induced sub-forest by vertex difference" — all
  factor through this identification).

  More precisely: Butcher's labeled forest `(V, E)` carries strictly
  more information (vertex names) than `Multiset RootedTree`, but the
  multiplicative mappings α : Forest → ℝ in §383 are by construction
  invariant under relabeling (since they are extended multiplicatively
  from a function on rooted-tree-isomorphism-classes). The
  multiplicity counting in `S.powerset` exactly recovers the count of
  vertex-labeled sub-forests up to relabeling.

### `IsMultiplicative`

* Textbook (page 287):
  > "A function α : T → R can be extended multiplicatively to a
  > function on the set of all forests by defining α(V, E) = ∏ᵢ α(Vᵢ, Eᵢ)."

  (where `(V, E) = ⋃ᵢ (Vᵢ, Eᵢ)` is the partition into trees.)

* Lean: `IsMultiplicative α := α 0 = 1 ∧ ∀ s t, α (s+t) = α s * α t`.

* Captures: **same content**. The empty-forest normalisation
  `α(0) = 1` is the empty product, implicit in Butcher's `∏ᵢ`
  notation. The binary additive law `α(s+t) = α(s)·α(t)` is the
  iterated form of the textbook multi-component product (proved by
  induction once we have the binary case).

### `convProduct` (equation 383a)

* Textbook (page 287, equation 383a):
  > `(αβ)(S) = Σ_{R ⊑ S} α(S \ R) β(R)`

* Lean:
  ```
  convProduct α β S = (S.powerset.map (fun R => α (S - R) * β R)).sum
  ```

* Captures: **same content**. The sub-forest relation `R ⊑ S` is
  multiset `R ≤ S`, and `S \ R` (induced sub-forest by vertex
  difference) is multiset subtraction `S - R`. The sum `Σ_{R ⊑ S}`
  uses `S.powerset` with each sub-multiset weighted by its
  combinatorial multiplicity — see the discussion in the file
  docstring.

### `multiplicative_conv` (Lemma 383A)

* Textbook statement (entity JSON, statement_text):
  > "Let α and β be multiplicative mappings from the forests to the
  > real numbers. Then αβ is multiplicative."

* Lean:
  ```
  theorem multiplicative_conv {α β : Forest → ℝ}
      (hα : IsMultiplicative α) (hβ : IsMultiplicative β) :
      IsMultiplicative (convProduct α β)
  ```

* Captures: **same content**. The Lean proof follows Butcher's
  textbook proof structure exactly: split `S = S₁ + S₂`, decompose
  each `R ⊑ S` as `R = R₁ + R₂`, use multiplicativity of α and β to
  factor, then apply `sum_mul_sum`-style identity. The `powerset_add`
  combinatorial bijection is the rigorous content of Butcher's
  informal "Each R ⊑ S can be written as R = R₁ ∪ R₂".

* No hypotheses are stronger than Butcher requires; the conclusion
  matches verbatim.

## Dead ends

### Auto-`deriving DecidableEq for RootedTree`

`deriving instance DecidableEq for RootedTree` failed: "None of the
deriving handlers for class DecidableEq applied". This is the standard
nested-inductive limitation — `RootedTree` contains `List RootedTree`
which would need its own derived `DecidableEq` referring back to
`RootedTree`. Workaround: `noncomputable instance : DecidableEq
RootedTree := Classical.decEq _`, which makes `convProduct`
`noncomputable` but is fine since we only use it for stating /
proving propositions in §383.

### `Multiset.mul_sum`

I initially used `Multiset.mul_sum` in the sum-product helper, but
that name does not exist; the right name is `Multiset.sum_map_mul_left`
(`sum (s.map fun i => a * f i) = a * sum (s.map f)`).

### `HSub Forest Forest Forest` synthesis

Even after annotating lambdas with `: Forest`, instance synthesis
failed for `S - R` until I switched the parameter type of `convProduct`
from `Forest` to `Multiset RootedTree`. Root cause was `DecidableEq`
missing on `RootedTree`, not the abbrev itself. (Once `DecidableEq`
was provided, both `Forest` and `Multiset RootedTree` worked
interchangeably.)

## Discovery

* **Mathlib gap**: `Multiset.powerset_add` is missing from Mathlib.
  Worth upstreaming: the proof is ~10 lines and follows the same
  pattern as existing `Multiset.product_add`. If we end up needing
  more sub-multiset combinatorics in §383B/C/D, this lemma will be
  hot.

* **Forest encoding choice**: `Multiset RootedTree` is the right
  encoding for §383 *as long as* multiplicative mappings are by
  construction invariant under relabeling (Butcher's setup). If
  later sections need vertex-labeled forests (e.g. for partitions
  in §383D's `α⁻¹(t) = Σ_P ∏ (-α(tᵢ))` formula, which sums over
  graph-theoretic partitions of the vertex set), we may need to
  switch to `Finset` over a labeled-tree structure. Re-evaluate
  when reaching lem:383D.

* **Strategy faithfulness**: the planner's Path B sketch contained a
  significant faithfulness flaw (pointwise vs convolution product).
  The faithfulness check caught it because the lemma's *proof* in
  Butcher uses sub-forest enumeration, which is meaningless for
  pointwise. Lesson: when a planner proposes a "trivial one-liner",
  spot-check by reading the textbook proof and asking "what work is
  the proof doing?" If the proof's combinatorial machinery doesn't
  apply to the proposed Lean statement, the statement is wrong.

## Suggested next approach

* **Cycle 079**: re-check Aristotle project `18504be5` first thing
  (it should have completed by then). If both reverse-direction
  §410D sub-lemmas came back, take the §410D rebuild path; if not,
  proceed to §383B (associativity of convolution product on
  forests). The §383B proof uses the same `powerset_add` machinery
  already built here, plus a more involved double-sum reordering
  (Butcher's proof rewrites `Σ_{Q ⊑ R ⊑ S}` as `Σ_{R ⊑ S, Q ⊑ R}`).

* **Cycle 080**: §383C (existence of left and right inverses in
  `G_1`). This requires restricting from forests to single-tree
  domain (`G_1 := T → ℝ` rather than `Forest → ℝ`) and an
  order-induction on rooted trees — moderate difficulty.

* **Mathlib upstream**: consider PR'ing `Multiset.powerset_add` and
  `Multiset.sum_mul_sum_eq_sum_product` to Mathlib (after polishing
  and consulting the maintainers). The proofs are short and
  general.
