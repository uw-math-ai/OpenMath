# Cycle 343 Results

## Worked on

§422 Phase D.2 well-founded recursion infrastructure on
`RootedTree.order`, per planner's primary target (P1 + P2). Closed
Phase D.2 of `def:422B`. No Phase D.3 / E / F work this cycle.

## Approach

Followed strategy §B verbatim. Two deliverables landed in
`OpenMath/Chapter3/Section301.lean` immediately after `order_pos`
(line 159), inside the existing `OpenMath.Chapter3.Section310.RootedTree`
namespace:

* **P1 — `RootedTree.order_lt_of_mem_children`** (~9 LOC body, ~12 LOC
  with docstring). Proof recipe followed strategy §B.2 verbatim:
  1. `rw [order_eq]` to unfold `(mk children).order = 1 + (children.map order).sum`.
  2. `List.mem_map_of_mem hc : c.order ∈ children.map order`.
  3. `List.le_sum_of_mem h₁ : c.order ≤ (children.map order).sum` (Mathlib's
     `Mathlib.Algebra.Order.BigOperators.Group.List` lemma for `CanonicallyOrderedAdd`
     monoids — `ℕ` qualifies).
  4. `omega` closes the resulting `c.order < 1 + sum` from the `≤` bound.

* **P2 — `instance : WellFoundedRelation RootedTree`** (1-line body).
  Used Lean's canonical `measure : (α → ℕ) → WellFoundedRelation α`
  combinator (verified via `lean_loogle WellFoundedRelation` —
  Init.WF.measure). Equivalent to the strategy's
  `InvImage.wf RootedTree.order Nat.lt_wfRel.wf` spelling but more
  idiomatic.

* Two `example` sanity checks (strategy §B.2): `vertex.order < cherry.order`
  and `cherry.order < broom₃.order`, both closed by `by decide` —
  confirms `RootedTree.order` reduces definitionally and the relation
  is concretely usable.

P3 (documentation-only Phase D.3 signature sketch in Section422.lean)
**skipped**. Rationale: P1+P2 landed quickly (~10 min editing + ~2
compile cycles), and the path tracker
`.prover-state/issues/def_422B_path.md` already carries the Phase D.3
entry-point sketch (Cycle 343 update §, lines 1080+ post-update);
adding a Lean-comment-only block was deemed redundant noise.

## Result

**SUCCESS.** Phase D.2 closed in single cycle, well under the 60–100
LOC budget estimate (actual: +17 LOC to Section301.lean).

* `lake env lean OpenMath/Chapter3/Section301.lean` → exit 0.
* `lake env lean OpenMath/Chapter3.lean` (aggregator) → exit 0.
* `grep -c sorry OpenMath/Chapter3/Section301.lean` → 0.
* Tautology scanner (`:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`)
  → 0 hits.

**Axiom audit (verified via temporary `#print axioms` directive,
then removed):**
* `OpenMath.Chapter3.Section310.RootedTree.order_lt_of_mem_children` →
  `[propext, Quot.sound]` only. (No `Classical.choice` — the proof
  uses only structural/decidable reasoning.)
* `OpenMath.Chapter3.Section310.RootedTree.instWellFoundedRelation` →
  **does not depend on any axioms.** Pure `measure` combinator
  application; reduces by `rfl`.

## Faithfulness check

For each new public symbol introduced this cycle:

* **`RootedTree.order_lt_of_mem_children`**
  - Entity ID and textbook statement: N/A — this is a pure
    `RootedTree`-API lemma about the `order` function defined in
    `Section310`. Not a textbook-named entity. The mathematical
    statement (every immediate subtree has strictly smaller order
    than its parent) is a direct combinatorial consequence of
    Butcher's order recursion `r(t) = 1 + Σᵢ mᵢ · r(tᵢ)` (Theorem
    301A equation (301a)). No divergence.
  - Lean statement captures: same content as the obvious
    mathematical statement.

* **`instance : WellFoundedRelation RootedTree`**
  - Entity ID and textbook statement: N/A — Lean-engineering
    scaffold, no textbook analogue. Butcher §422 implicitly uses
    induction on tree order throughout the (422a) inductive
    construction (p. 1163); this instance is the Lean machinery that
    will mediate that induction in Phase D.3's `noncomputable def`.
  - Lean statement captures: standard `measure`-derived
    well-founded relation; well-foundedness inherited from
    `Nat.lt_wfRel.wf` via `InvImage.wf` under the hood.

No textbook divergences introduced.

## Dead ends

None this cycle. Strategy §B's approach worked first try; no need to
pivot to §C (stability bridge) or §D (manual cherry case). The
`List.le_sum_of_mem` lemma — strategy §B.2 flagged this as the
"might not exist" worry — does exist in Mathlib at
`Mathlib.Algebra.Order.BigOperators.Group.List`. Confirmed via
`lean_loogle "_ ≤ List.sum _"`.

Minor friction: my first `#print axioms` attempt in `/tmp/check_axioms.lean`
failed with "Unknown constant" because the imported `Section301.olean`
was stale (cached from prior build, mtime 2026-05-15 vs source 2026-05-16).
Pivoted to inline `#print axioms` directives within Section301.lean
itself (run via `lake env lean OpenMath/Chapter3/Section301.lean`),
then removed the directives after capture. Standard workaround for
the GPFS-cache-staleness pattern.

## Discovery

* `List.le_sum_of_mem` requires `CanonicallyOrderedAdd M` — the
  exact Mathlib name as of Lean 4.28 / current Mathlib. Earlier
  versions used `OrderedCancelAddCommMonoid` or similar; the
  canonically-ordered constraint is the modern phrasing and `ℕ`
  satisfies it via the `Nat.instCanonicallyOrderedAdd` instance.
* `measure : (α → ℕ) → WellFoundedRelation α` is the idiomatic
  Lean-4 spelling for "well-founded relation derived from a
  natural-number-valued ranking function". The strategy's fallback
  `InvImage.wf` form would work but is unnecessary boilerplate.
* The `WellFoundedRelation` instance built via `measure` requires
  **zero axioms** to typecheck — verified via `#print axioms`. This
  is meaningfully stronger than the typical `[propext, Quot.sound]`
  baseline; future consumers of the instance (Phase D.3's `η`
  solver) can claim the same zero-axiom property for their
  termination metric independent of the body of the function.
* `lake env lean` on a single file produces no stdout/stderr on
  success (exit 0, zero output bytes). For sanity I now check exit
  code explicitly via `&& echo "exit: $?"` after every compile.

## Suggested next approach

**Cycle 344 entry: Phase D.3 inductive-step `η`-recursion solver.**
Per `def_422B_path.md` §5 row D.3 (100–200 LOC, 1–2 cycle estimate,
substantive risk).

Concrete steps:

1. **Scaffold `underlyingEta_aux` as a `noncomputable def`** on
   `RootedTree` with `termination_by t => t` consuming the new
   `WellFoundedRelation`, and `decreasing_by` invoking
   `order_lt_of_mem_children`. Start with `sorry` body for the
   recursive case.
2. **Base case at `t = mk [] = vertex`**: cycle 342's
   `Eq422a_at_vertex_eta_eq` gives the closed form. Just dispatch.
3. **Recursive case at `t = mk children` with `children ≠ []`**:
   expand `Eq422a M η_q` at this `t`, isolate `η(t)`'s linear
   coefficient, substitute `underlyingEta_aux M ... c` for each
   `c ∈ children`. This is the substantive `~100–200 LOC` step —
   requires unpacking `derivativeWeightWithSrc`'s recursion through
   `c ∈ children` (each child contributes via the (422a) sum
   structure).
4. **Stretch (cycle 345)**: package the result as a proof that the
   constructed `η` satisfies `Eq422a M η_q` — the Phase E lift /
   Phase F `thm:422A` step.

The non-vanishing hypothesis `coef_α + coef_β ≠ 0` that cycle 342's
`Eq422a_at_vertex_eta_eq` requires will need to be threaded through
the recursion. Strategy 343 §C documented the stability-bridge
backup path for converting `IsStable + IsPreconsistent` →
`coef_α + coef_β > 0`; that bridge is now a candidate first-task for
cycle 344 (could even be split off as a 30-LOC standalone ship
before scaffolding the full recursion).

Alternative if Phase D.3 stalls (cycle 344 may want to time-box):
back-fill the `coef_α + coef_β > 0` stability bridge from §C as a
quick win, keeping the §422 streak alive while the inductive-step
strategy crystallizes.
