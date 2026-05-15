# Cycle 255 Results

## Worked on
§310 B-series partial sum infrastructure (Phase A.1 + A.2 of `lem:310B`
roadmap, per cycle 255 strategy).

Shipped into `OpenMath/Chapter3/Section301.lean` (after cycle 254's
`bseriesTerm` non-vacuity examples, before `end RootedTree`), inside
the `OpenMath.Chapter3.Section310.RootedTree` namespace:

- **P1**: `TruncatedRootedTree N` subtype with `order` projection +
  `order_le` accessor.
- **P2**: `bseriesPartialSum f y₀ h S` over `Finset RootedTree`, with
  `bseriesPartialSum_empty` (`@[simp]`) and `bseriesPartialSum_insert`
  algebraic facts.
- **P3**: Two non-vacuity witnesses — singleton `{vertex}` and
  two-element `{vertex, cherry}` (using `DecidableEq RootedTree` from
  Section301 line 92 to discharge the membership-side condition via
  `simp`).
- **P4** (stretch): `exists_truncated_of_forall_order_le` —
  bounded-order lifting from `Finset RootedTree` to
  `TruncatedRootedTree N`.

## Approach
1. Read strategy.md + cycle_254.md to confirm placement (Section301.lean,
   inside the `RootedTree` namespace re-opened across the file).
2. Read Section301.lean lines 540–605 to confirm cycle 254's tail
   structure (`bseriesTerm`, `bseriesTerm_vertex`,
   `bseriesTerm_eq_theta_smul_bseriesTerm`, three non-vacuity examples,
   `end RootedTree` at line 603).
3. Inserted ~80 LOC of new content between line 601's last example and
   `end RootedTree`. One single `Edit` block — no sorry-first scaffold
   needed since every declaration is short and has natural inhabitants
   (per strategy §C forbidden #9).
4. Resolved one elaboration error (see "Dead ends").
5. Verified via `lake env lean OpenMath/Chapter3/Section301.lean`,
   regression-checked `lake env lean OpenMath/Chapter3.lean`,
   `grep -c sorry` = 0, tautology regex returns nothing, and
   `lake build OpenMath.Chapter3.Section301` to refresh olean cache.
6. Confirmed axiom-cleanliness via `#print axioms` on all 7 new
   public declarations (TruncatedRootedTree, .order, .order_le,
   bseriesPartialSum, _empty, _insert, exists_truncated_of_forall_order_le).
   All depend only on `propext`, `Classical.choice`, `Quot.sound` (or
   subsets thereof, including `TruncatedRootedTree` itself which
   "does not depend on any axioms"). No `sorryAx`.

## Result
SUCCESS — all of P1, P2, P3, P4 shipped axiom-clean and sorry-clean
in a single edit.

## Faithfulness check

### `def TruncatedRootedTree (N : ℕ) : Type`
- Entity ID: **none** — this is a Lean engineering scaffold, not a
  Butcher-named concept. Documented in the docstring: "Butcher does
  not name it." The subtype packages "rooted tree of order at most N"
  for stating B-series truncation results. No faithfulness obligation
  to a textbook statement (no `entities/*.json` exists for it).
- Lean statement captures: the natural mathematical type
  `{ t : RootedTree // order t ≤ N }`.

### `def TruncatedRootedTree.order` + `theorem TruncatedRootedTree.order_le`
- Engineering accessors for the subtype's projection and bound; no
  textbook obligation.

### `def bseriesPartialSum`
- Entity ID: derives from `lem:310B` (Butcher §310 (310i)).
  Quoted dependency:
  > "B-series of (310i): $y_1 = y_0 + \sum_t \frac{h^{r(t)}}{\sigma(t)}
  > \alpha(t) F(t)(y_0)$ (over all unlabeled rooted trees t)."
- Lean statement captures: weaker than the full (310i) (it does not
  sum α-weights — see issues below) but the natural **finite partial
  sum** of the `bseriesTerm`s. The α-weighted form is the cycle 256+
  target. Here we use Butcher's "scaffold" form with the elementary
  term `(h^r(t)/σ(t)) • F(t)(y₀)` exactly as cycle 254 shipped it.
- Justification for divergence: `lem:310B` is multi-cycle (requires
  `thm:306A`/Taylor and labelled-tree quotients). `bseriesPartialSum`
  is the immediate finite-Finset analog of (310i) — partial sums in
  the Lean sense are a finite `Finset.sum`, which is the standard
  Mathlib pattern. The "B-series partial sum" *name* is informal —
  Butcher reaches a similar concept implicitly via the `O(h^{N+1})`
  truncation form (§310 introduces order-N truncated B-series in
  Table 310(II) and the surrounding discussion). The Finset is supplied
  by the call site, which lets us state the partial sum without
  needing `Fintype (TruncatedRootedTree N)`.

### `theorem bseriesPartialSum_empty`, `theorem bseriesPartialSum_insert`
- Pure Finset.sum algebraic identities; no textbook obligation.

### `theorem exists_truncated_of_forall_order_le`
- Pure existence/lifting lemma between the subtype and Finsets; no
  textbook obligation. Closes via `⟨⟨t, hS t ht⟩, rfl⟩`.

### Tautology / identity / definition-smuggling checks
- No theorem conclusion equals one of its own hypotheses.
- No proof is a bare `exact h_X` re-export.
- `TruncatedRootedTree` is a subtype, not a structure with Prop fields,
  so the definition-smuggling pattern doesn't apply.
- `order_le` *is* `t.property` — but `t.property` is the unique
  Prop projection of the subtype, exactly what the lemma signature
  promises. This is the legitimate "subtype-accessor" pattern, not a
  vacuous tautology. The lemma re-exports `Subtype.property` under a
  meaningful name, which is the standard idiom in Mathlib (cf.
  `Subtype.coe_lt`, `Set.mem_def`, etc.).

## Dead ends

### `Coe (TruncatedRootedTree N) RootedTree` instance failed
The strategy's P1 included an `instance instCoe (N : ℕ) :
Coe (TruncatedRootedTree N) RootedTree := ⟨Subtype.val⟩`. Lean
rejected it with:
> "instance does not provide concrete values for (semi-)out-params
>   Coe (TruncatedRootedTree ?N) RootedTree"

Lean 4's current `Coe` typeclass has semi-out-params on both sides;
because `N` is a parameter (not derivable from the target type
`RootedTree`), instance synthesis can't fix `N` from a `Coe ?T
RootedTree` query.

**Mitigation (per strategy R2)**: dropped the `Coe` instance entirely.
Consumers use `Subtype.val` (or `t.val`) directly. No cycle-255
deliverable consumes the subtype, so no downstream impact. Future
cycles needing the coercion can add a `CoeHead`-style instance or a
typed projection.

This is the **only** elaboration failure in the cycle.

## Discovery

1. **`Coe` typeclass quirk**: Lean's `Coe α β` typeclass has both
   sides as semi-out-params in Lean 4. For a parameterized source type
   like `TruncatedRootedTree N`, the parameter `N` cannot be inferred
   from the target type alone, so the instance is rejected with the
   "concrete values for (semi-)out-params" error. The clean
   workaround is to either (a) use `Subtype.val` directly, or (b)
   declare a `CoeHead` (or `CoeTC`) instance — but the simpler "drop
   the coercion entirely" approach used here suffices for cycle 255's
   deliverables. Future cycles needing an automatic coercion should
   check the `Coe`/`CoeHead`/`CoeTC`/`CoeFun` decision matrix before
   writing the instance line.

2. **`DecidableEq RootedTree` is available**: Section301.lean line 92
   already provides this (hand-written mutual `decEqTree`/`decEqList`
   pattern). The two-element non-vacuity example
   (`{vertex, cherry}`) thus closes its `vertex ∉ {cherry}` side
   condition via `simp [Finset.mem_singleton, vertex, cherry]` —
   no explicit `cherry ≠ vertex` hypothesis required. (Strategy
   risk R1 anticipated this might be needed; it wasn't.)

3. **Olean cache staleness**: `lake env lean <file>` re-elaborates the
   file in-place but **does not** update the olean used by `import`-
   side resolution. After editing a file, you need `lake build
   OpenMath.<Path>` (or `lake build`) to refresh the cache before
   downstream `import OpenMath.<Path>; #print axioms ...` can resolve
   the new names. Useful protocol for future axiom-check steps in this
   workflow. (Recorded here, not yet in CLAUDE.md.)

4. **Strategy's P4 was easy**: The `exists_truncated_of_forall_order_le`
   lemma compiled first try with a two-line `intro t ht; exact ⟨⟨t, hS
   t ht⟩, rfl⟩`. No subtype-unification snags (per R2 risk register).
   This suggests the strategy's "60% cycle budget" gating was
   conservative — P4 could safely be elevated to P3-tier next time.

## Suggested next approach

The strategy §I cycle-256+ outlook stands unchanged:

1. **Cycle 256**: `lem_311A_order_two` — the order-2 Taylor expansion
   bridge for `lem:311A`. Requires the
   `iteratedFDeriv ℝ 1 ↔ fderiv` Mathlib bridge plus a small ODE-side
   helper. Aristotle-batch-friendly. ~150-250 LOC, possibly 2 cycles.

2. **Cycle 257**: small-r partial `lem:310B` — state `lem:310B`
   restricted to a hand-enumerated `Finset` on the RHS (now made
   possible by cycle 255's `bseriesPartialSum`), with the LHS as a
   partial Taylor expansion via cycle 256's order-2 result.

3. **`α`-weighted version of `bseriesPartialSum`**: a natural cycle
   256+ companion to cycle 255's scaffold-form partial sum would be
   `bseriesAlphaPartialSum f y₀ h S := ∑ t ∈ S, alphaWeight t • bseriesTerm
   f y₀ h t`, matching Butcher's (310i) up to the labelled-tree-orbit
   prefactor. This is one declaration (~5 LOC) plus singleton/insert
   companions; could be folded into cycle 256 with no extra
   infrastructure burden.

4. **Fintype `TruncatedRootedTree N`**: still deferred — depends on
   a decidable enumeration of rooted trees up to order `N` (mathematically
   Cayley's formula). Multi-cycle; no path in cycle 256.

5. **`Coe`-style instance for `TruncatedRootedTree N → RootedTree`**:
   if future cycles need an automatic coercion, the workaround is
   probably a `CoeHead` instance or a typed `val` projection at call
   sites. Defer until first consumer arises.
