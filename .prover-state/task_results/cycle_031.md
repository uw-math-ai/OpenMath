# Cycle 031 Results

## Worked on
`def:323A` — internal order `q` of a Runge–Kutta stage. New file
`OpenMath/Chapter3/Section323.lean` containing:

* `RootedTree.order_pos` — small helper: every rooted tree has positive order.
* `RKTableau.HasInternalOrder M i q` — the predicate.
* `RKTableau.hasInternalOrder_zero` — vacuous case at `q = 0`.
* `Section323.explicitEuler_hasInternalOrder_one` — non-vacuous witness.

## Approach
1. Read `extraction/formalization_data/entities/def_323A.json` for the
   verbatim textbook statement, including the `Φᵢ(t)` notation defined
   via the auxiliary tableau `[c A / eᵢ A]`.
2. Confirmed the §323 line at `extraction/raw_text/ch03.txt:2465`
   ("internal order 1 is equivalent to `cᵢ = Σⱼ aᵢⱼ`") forces the
   §323 `Φᵢ(t)` to be the §312 *internal weight*
   (`M.internalWeight t i`), since `cᵢ = M.internalWeight τ i`. The
   alternative (auxiliary-tableau `derivativeWeight`) would give
   `cᵢ = (Φᵢ D)(τ) = 1` instead, which is wrong. Documented this in
   the file docstring.
3. Verified `density` and `order` both return `ℕ` via
   `lean_hover_info` — used `(t.density : ℝ)` cast for the division
   in the equation.
4. Wrote the predicate, the `q = 0` lemma, and the `explicitEuler`
   witness. Witness proof: `internalWeight = 0` because `A = 0`;
   `(c 0)^t.order / γ(t) = 0` because `c 0 = 0` and `0^k = 0` for
   `k ≥ 1` (uses `order_pos`).
5. Verified single-file compile (`lake env lean`), full project build
   (`lake build`, 2845 jobs), and ran `#print axioms` on the witness
   to confirm clean axiom dependency.

## Result
**SUCCESS** — definition + 2 named theorems + 1 helper land in one
cycle. No `sorry`, no new axioms, no `maxHeartbeats` increase. Full
project builds cleanly.

Aristotle was not used this cycle — the witness proof closed cleanly
by hand in one short `simp` per side, well under the 10-minute
threshold the strategy gave for batching to Aristotle.

## Faithfulness check

### `RootedTree.order_pos`
- Helper lemma, not a Butcher entity. No `def_323A.json` cross-check
  needed. Statement: `∀ t : RootedTree, 0 < t.order`. Proof: case
  on `mk children`, then `omega` against the recursive
  `order = 1 + orderSum children`. Real arithmetic work, not vacuous.

### `RKTableau.HasInternalOrder` (`def:323A`)
- Entity ID: `def:323A`.
- Textbook statement (quoted from `def_323A.json`):
  > Stage `i` has 'internal order `q`', if for all trees such that
  > `r(t) ≤ q`, `Φᵢ(t) = cᵢ^{r(t)} / γ(t)`.
- Lean statement captures: **same content**.
  - `∀ t : RootedTree, t.order ≤ q → ...` matches "for all trees
    such that `r(t) ≤ q`".
  - `M.internalWeight t i = (M.c i) ^ t.order / (t.density : ℝ)`
    matches `Φᵢ(t) = cᵢ^{r(t)} / γ(t)` under the §312/§323
    `Φᵢ(t)` identification documented in the file docstring and
    justified by `extraction/raw_text/ch03.txt:2465`.
- Definition smuggling check: We are NOT defining "internal order" as
  some equivalent characterisation. The Lean predicate IS the
  textbook condition.

### `RKTableau.hasInternalOrder_zero`
- Auxiliary lemma, not a Butcher entity.
- Tautology check: conclusion `M.HasInternalOrder i 0` does not appear
  as a hypothesis (the only hypotheses are `M`, `i`).
- Identity check: proof unfolds the predicate, then closes by
  `omega` against `order_pos`. Real work.
- Hypothesis-strength check: no extra hypotheses.

### `Section323.explicitEuler_hasInternalOrder_one`
- Witness for non-vacuity of `def:323A`.
- Tautology check: conclusion is the equation
  `internalWeight = c^_/γ`, not a hypothesis.
- Identity check: proof actually computes both sides to `0`. Not a
  re-export.
- Hypothesis-strength check: no extra hypotheses (the universal
  quantification is part of the predicate definition).

## Dead ends
None this cycle. The witness proof closed on the first attempt. The
notational ambiguity around §312 vs §323 `Φᵢ(t)` was resolved by
re-reading the strategy's pointer to `extraction/raw_text/ch03.txt:2465`
before writing any Lean code, as the strategy instructed.

## Discovery
* **`order_pos` is genuinely missing from existing infrastructure.**
  A `RootedTree.order_pos` lemma is the kind of basic fact that any
  proof about elementary weights eventually needs (e.g. `0^t.order = 0`
  forms appear naturally when reasoning about explicit methods or
  vacuous orders). It now lives in
  `OpenMath/Chapter3/Section323.lean` in the
  `OpenMath.Chapter3.Section310.RootedTree` namespace; downstream
  consumers can `import OpenMath.Chapter3.Section323` (or be
  refactored to put `order_pos` in `Section310` directly if more
  files end up needing it). For now, putting it here keeps the
  infrastructure changes local and reversible.
* **The §312/§323 `Φᵢ(t)` ambiguity is real.** Future entities that
  reference Butcher's `Φᵢ(t)` symbol (e.g. `thm:323B`, the
  characterisation of internal order; `thm:324A`, related order
  conditions; `thm:343B`, downstream consumer) will need to either
  cite this file's notational decision or re-derive it from
  `ch03.txt:2465`. Worth flagging in the strategy for whoever
  picks up the §323 follow-on theorems.

## Suggested next approach

The natural follow-on targets, in roughly increasing order of effort:

1. **`thm:323B`** (page 203) — characterising condition for internal
   order. This is a real theorem, not just a definition, and is the
   first consumer of `HasInternalOrder`. The textbook claims
   "the `C(q)` condition is necessary and sufficient for every stage
   to have internal order `q`". Worth checking the entity JSON for
   what is actually labeled `323B` and what `C(q)` translates to.
2. **`def:357A`** (BN-stability) — the cycle 030 worker's "next
   alternative" suggestion. Requires non-autonomous one-step
   infrastructure parallel to `IsRKOneStep` and an inner-product
   witness (implicit midpoint via `‖y₁‖² - ‖y₀‖² = 2h ⟨f(m), m⟩`).
   Riskier than `def:323A` but feasible in one focused cycle if the
   non-autonomous predicate is kept minimal.
3. **`thm:324A`** — generalisation of order conditions, depends on
   `def:323A`. Probably needs `def:312A`'s recursion in concert with
   `HasInternalOrder` to characterise "every stage has internal
   order `q`" as the `C(q)` condition.
4. **`def:381F`** (P-equivalent) — still parked. The strategy was
   right to defer; the multi-cycle plan in
   `.prover-state/issues/reduced_method_deferred.md` is the proper
   path.

Of these, **`thm:323B` is the strongest fit for cycle 032**: it is
a direct downstream consumer of this cycle's work, the textbook
statement is short, and the proof is likely a straightforward
calculation reusing `internalWeight` and `derivativeWeight` from
§312. If the planner agrees, the cycle 032 strategy should walk
through `thm:323B`'s entity JSON and the textbook discussion of
`C(q)` (around `extraction/raw_text/ch03.txt:2400–2500`) to
confirm the statement and the C(q) ↔ internal-order claim before
committing the worker to it.
