# Cycle 016 Results

## Worked on

Priority 1 from `.prover-state/strategy.md`: formalize `def:310A` (Butcher
§310, the **elementary differential**). Created
`OpenMath/Chapter3/Section310.lean`, set up the new
`OpenMath/Chapter3.lean` aggregator, wired it into top-level
`OpenMath.lean`. No Aristotle batch — the work was definitional plumbing
for which Aristotle is poorly suited (per strategy guidance).

## Approach

1. **Loaded entity data.** Read
   `extraction/formalization_data/entities/def_310A.json` and
   `extraction/raw_text/ch03.txt §300, §310`. Quoted the textbook
   statement of Definition 310A (equations (310g)/(310h)) verbatim
   into the file docstring.

2. **Designed the rooted-tree type.** First attempt
   `inductive RootedTree | mk : Multiset RootedTree → RootedTree`
   was rejected by Lean's strict-positivity checker (verified
   experimentally — kernel error: "arg #1 of … contains a non valid
   occurrence of the datatypes being declared"). Fell back to the
   `List` representation per the strategy's documented escape hatch:
   `inductive RootedTree | mk : List RootedTree → RootedTree`. The
   spurious child order is harmless for `def:310A` because the
   `iteratedFDeriv` produces a symmetric multilinear map (Schwarz),
   so permuting children leaves `F(t)(y)` invariant whenever `f` is
   smooth enough. The file docstring documents this faithfulness
   argument explicitly.

3. **Defined `order`.** First attempt used direct nested recursion
   `def order : RootedTree → ℕ | mk children => 1 + (children.map order).sum`.
   This compiles but Lean lowers it to `WellFounded.fix`, so the
   small-example checks `vertex.order = 1`, `cherry.order = 2`,
   `broom₃.order = 3` failed under both `rfl` and `decide` ("did not
   reduce"). Refactored to mutual recursion with a helper `orderSum :
   List RootedTree → ℕ` so the recursion is now structural, and the
   examples close by `rfl`.

4. **Defined `elementaryDiff`.** Signature
   `elementaryDiff (f : E → E) (y : E) : RootedTree → E` over an
   abstract real normed space `E` (the strategy explicitly approves
   either `Fin N → ℝ` or abstract `E`; abstract is more
   Mathlib-idiomatic and avoids `{N : ℕ}` clutter). The recursive case
   `mk children` evaluates to
   `iteratedFDeriv ℝ children.length f y (fun i : Fin children.length =>
       elementaryDiff f y (children.get i))`, matching equation (310h)
   modulo the `List`/`Multiset` choice. Termination via
   `sizeOf`-based well-founded recursion: discharged
   `decreasing_by` with `Nat.lt_add_left 1 (List.sizeOf_get …)`.

5. **Wired imports.** Created `OpenMath/Chapter3.lean` (single import
   of `Section310`) and added `import OpenMath.Chapter3` to
   `OpenMath.lean`.

6. **Verified.** `lake build` passes with 2822 jobs and no errors.
   `#print axioms OpenMath.Chapter3.Section310.elementaryDiff` reports
   only `[propext, Classical.choice, Quot.sound]` — the standard
   Mathlib trio. `RootedTree.order`, `orderSum`, and `vertex` depend
   on no axioms at all. The tautology scanner returns zero hits
   across `OpenMath/`. No `sorry` introduced.

## Result

**SUCCESS** — Priority 1 fully delivered. `def:310A` is formalized as
`OpenMath.Chapter3.Section310.elementaryDiff`, with the
`RootedTree` inductive, `order` recursion, three small-tree witnesses
(`vertex`, `cherry`, `broom₃`) and reduction-test examples that close
by `rfl`.

Priority 2 (`thm:301A`) deferred to cycle 017 — the Priority 1 work
plus design exploration consumed the cycle as the strategy
predicted.

## Faithfulness check

### `def:310A` (the cycle's main deliverable)

- **Entity ID and textbook statement** (quoted from
  `formalization_data/entities/def_310A.json`):
  > Given a tree $t$ and a function $f : \mathbb{R}^N \to \mathbb{R}^N$,
  > analytic in a neighbourhood of $y$, the 'elementary differential'
  > $F(t)(y)$ is defined by
  >
  > $F(\tau)(y) = f(y),$
  > $F([t_1, t_2, \dots, t_m])(y) = f^{(m)}(y)\bigl(F(t_1)(y), F(t_2)(y),
  > \dots, F(t_m)(y)\bigr).$

- **Lean statement captures**: same content, with two documented
  generalisations:
  1. The codomain is an abstract real normed space `E` instead of
     `ℝ^N` — strictly more general; specialising `E := Fin N → ℝ`
     recovers the textbook signature exactly. The strategy explicitly
     approves either choice.
  2. The smoothness hypothesis on `f` is dropped from the *definition*
     because `iteratedFDeriv ℝ k f y` is defined for arbitrary `f`
     (returns the zero multilinear map at non-smooth points).
     Smoothness will appear as a hypothesis on theorems *about*
     `elementaryDiff`, not on the definition itself. This is standard
     Mathlib practice for derivative-based definitions and matches
     `iteratedFDeriv`'s own signature.

- **Definition-smuggling check**: `elementaryDiff` is a `def`
  returning a function, not a theorem. The recursive equation
  matches (310h) literally — no characterisation theorem is being
  smuggled in as a definition.

- **Class/structure check**: `def:310A` uses `inductive` (not
  `class`/`structure`), so the `Prop`-field rule does not apply.
  The "concrete witness" rule is satisfied informally by the three
  small-tree examples (`vertex`, `cherry`, `broom₃`) and their
  `rfl`-reducible `order` values, which confirm the inductive type
  and recursion are well-formed.

### `RootedTree` (file-local infrastructure, introduced this cycle)

- **Textbook source**: Butcher §300, "Rooted trees", and the second
  notation in §300 (page 138, "we consider a tree $t$ such that, when
  the root is removed, there remain a number of disconnected trees,
  say $t_1, t_2, \dots, t_m$").
- **Lean statement captures**: weaker than the textbook — the textbook
  uses *unordered* rooted trees (graph-isomorphism quotient), and our
  `inductive RootedTree | mk : List RootedTree → RootedTree`
  carries a spurious child order. Justification documented in the file
  docstring: (a) `Multiset RootedTree` is rejected by Lean's
  strict-positivity check, (b) `iteratedFDeriv` is symmetric, so the
  spurious order does not leak into observable behaviour of
  `elementaryDiff` for smooth `f`, (c) a true unordered-tree quotient
  can be built later if downstream proofs need it (e.g. for `α(t)`,
  `σ(t)`).

### `order`, `orderSum` (file-local infrastructure)

- **Textbook source**: Butcher's `r(t)` (Section 300, Table 300(I)).
- **Lean statement captures**: same content. `order (mk children) =
  1 + Σ order children`. `orderSum` is a list-recursion helper for
  mutual structural recursion — does not appear in Butcher and adds
  no mathematical content.

### `vertex`, `cherry`, `broom₃` (concrete witnesses)

- These are not Butcher entities — they are concrete witnesses
  introduced per the spirit of CLAUDE.md's "non-vacuity" rule, to
  confirm the inductive type and `order` recursion are well-formed.
  No faithfulness concern.

## Dead ends

1. **`Multiset RootedTree` for the inductive children**. Rejected by
   strict-positivity. Documented in the file docstring as the reason
   for the `List` fallback. Not a productive avenue without significant
   metaprogramming infrastructure (custom `Quot`-based encoding) that
   is way out of scope.

2. **Direct nested recursion for `order`** (single
   `def order | mk children => 1 + (children.map order).sum`). Compiles
   but is lowered to `WellFounded.fix`, so example checks like
   `vertex.order = 1` fail under `rfl` and `decide`. Replaced with
   mutual recursion `order` / `orderSum`, which is genuinely structural
   and reduces by `rfl`.

3. **`decreasing_by simp_wf; have h := List.sizeOf_get children i;
   omega`** — `omega` could not bridge `children[↑i]` (the form Lean
   normalises to) and `children.get i` (the form `List.sizeOf_get`
   returns). Resolved by an explicit `show sizeOf (children.get i) <
   1 + sizeOf children` step before `Nat.lt_add_left 1 (List.sizeOf_get
   children i)`.

## Discovery

1. **Mathlib already has a `RootedTree`** in
   `Mathlib.Order.SuccPred.Tree`, but it is an order-theoretic
   construction (a type with a `SemilatticeInf` structure), not a
   Butcher-style combinatorial tree. Since we never `import
   Mathlib.Order.SuccPred.Tree`, there is no name conflict, but
   downstream files should be aware that `OpenMath.Chapter3.Section310.
   RootedTree` is the Butcher object, not the Mathlib one. Documented
   implicitly by the fully-qualified namespace.

2. **Nested-inductive recursion through `List` does NOT auto-reduce
   under `rfl`/`decide` in Lean 4** unless written via mutual
   recursion (or an equivalent that the elaborator recognises as
   structural). This is worth remembering for the next §31x
   definitions: `def:312A` (derivative weights) will face the same
   issue and should be written mutually with a `derivativeWeightSum`
   list helper from the start.

3. **Lean's auto-generated `sizeOf` for nested-inductive
   `mk : List RootedTree → RootedTree`** uses `1 + sizeOf children`
   as the size of `mk children`. Combined with `List.sizeOf_get :
   sizeOf (l.get i) < sizeOf l`, well-founded recursion through
   children is straightforward via `Nat.lt_add_left`. No need for
   exotic measures.

4. **`decreasing_by` in Lean 4 normalises `l.get i` to `l[↑i]`**
   when constructing the goal, but `List.sizeOf_get` still returns
   the `l.get i` form. An explicit `show sizeOf (l.get i) < …`
   bridges the two (they are definitionally equal but `omega` and
   `exact` won't infer that automatically).

## Suggested next approach

For cycle 017, the natural next entity is **`thm:301A` (Functions on
trees)**, the Priority 2 deferred from this cycle. Read
`extraction/formalization_data/entities/thm_301A.json` and
`extraction/raw_text/ch03.txt §301` first — the strategy hint suggests
§301 may overlap with §310 (in which case keep both in
`Section310.lean`), or it may be a separate section worth its own
file. Verify before creating `Section301.lean`.

Alternative §31x leaves that are also unblocked by `def:310A`:

- **`lem:310B`** (elementary differential weight formula, listed as
  the next §310 entity in `lean_status.json`). Uses `elementaryDiff`
  directly — natural follow-on. May need `iteratedFDeriv` symmetry
  lemmas (`iteratedFDeriv_symm`) and `iteratedFDeriv_zero_apply` /
  `_succ_apply` from Mathlib.
- **`def:312A`** (derivative weights). Defines `α(t)` and would
  motivate adding the `Multiset`/`Sym` quotient on `RootedTree` if
  Butcher's `α(t)` requires unordered trees. Worth checking the
  textbook before committing.

Whichever is chosen, the pattern from this cycle is reusable:
  - Mutual recursion through `List RootedTree` for any new
    tree-recursive definition (§310 / §31x will need many).
  - File-level docstring quoting the textbook statement and
    documenting any faithfulness divergence.
  - Concrete small-tree witnesses (`vertex`, `cherry`, `broom₃`,
    plus a few of order 4) closed by `rfl` to guarantee the
    recursion reduces cleanly.

A second housekeeping note for the planner: if cycle 017 grows the
small-tree fixture set, consider extracting `vertex`, `cherry`,
`broom₃`, etc. into a shared helper namespace inside `Section310`
so later sections can `open` it for examples without redefining.
