# Issue: `convProduct` uses multiset sub-selection, not Butcher's vertex-subset partition

## Blocker (escalation, not a build blocker)

`OpenMath/Chapter3/Section383.lean` defines `convProduct` (the
"convolution product") using multiset sub-selection — i.e.
`(αβ)(S) = Σ_{R ≤ S} α(S - R) · β(R)` where `R ≤ S` is multiset
inclusion on `Multiset RootedTree`.

But Butcher §383 (page 287, just above equation 383a) defines
`R ⊑ S` as a **vertex subset of S**:

> If R ⊑ S then S \ R will denote the forest induced by the
> difference of the vertex sets of S and R, respectively.

Vertex subsets of a forest can split a connected tree into multiple
components by selecting only some of its vertices, producing a
*finer* family of "sub-forests" than multiset sub-selection.

## Consequence

Our `convProduct` is a **strictly weaker** convolution than
Butcher's. Concretely, on a single-tree forest `{t}` where `t` has
order `n > 1`:

* Butcher's convolution produces `α(t) + β(t) + φ(t, α, β)`, where
  the φ-term sums over non-trivial vertex subsets of `V(t)` that
  yield non-trivial sub-forests.
* Our `convProduct` produces only `α({t}) + β({t})` — the
  multiset powerset of `{t}` is just `{∅, {t}}`.

This is precisely the mismatch acknowledged (and effectively
exploited) in cycle 081's strategy:

> our convolution operates over forest sub-multisets, which for a
> singleton-tree forest are just ∅ and {t} itself.

## Affected entities

* `convProduct` (definition, `Section383.lean:155`).
* `multiplicative_conv` — Lemma 383A, claims convolution preserves
  multiplicativity. **True for both convolutions**, so the lemma is
  not vacuous; but it proves the statement for our convolution, not
  Butcher's.
* `convProduct_assoc` — Lemma 383B. Same situation.
* `exists_inverse_of_isMultiplicative` — Lemma 383C, **closed
  this cycle**. The inverse exists in both algebras; the closed
  form differs — Butcher's `α⁻¹` involves a sum over vertex-subset
  partitions (Lemma 383D), our `convInverse α` is just
  `(-1)^|F| · ∏ α({t})`.

## Why the prior planner accepted this

Looking at `Section383.lean` header notes (cycle 077–078):

> The textbook's sub-forest relation `R ⊑ S` reduces, in this
> encoding, to `R ≤ S` as multisets. The induced "set difference"
> `S \ R` becomes multiset subtraction `S - R`.

This claim is **incorrect** for forests containing trees of order
> 1 (i.e., trees with edges). It is correct only for forests of
isolated vertices (each tree has order 1).

Cycle 081's strategy openly acknowledges the discrepancy ("there is
no φ term at the forest level for single-tree forests — the
textbook's φ comes from tree-level partitions") and exploits it to
get a closed-form inverse instead of the textbook's recursive one.

## What was tried

* Verified by re-reading Butcher §383 (`extraction/raw_text/ch03.txt`):
  the textbook's R ⊑ S is genuinely vertex-subset, not
  tree-multiset.
* Verified the φ-term in 383C's textbook proof requires a richer
  convolution than ours.
* Did **not** refactor `convProduct` — it is committed in cycles
  077–080's work and refactoring would invalidate `lem:383A`,
  `lem:383B`, etc.

## Possible solutions

1. **Refactor `convProduct` to use a vertex-subset notion.** This
   requires:
   * Adding a vertex-set / edge-set datatype on `RootedTree` (or
     adopting one from Mathlib).
   * Defining "sub-forest by vertex subset" — every vertex subset
     of a forest yields a sub-forest with induced edges.
   * Re-proving 383A, 383B, 383C in this richer setting. The proof
     of 383A would still go through (now the partition over
     R = R₁ ⊔ R₂ uses vertex-disjoint decomposition, which is the
     standard tensor-product structure on the Butcher Hopf
     algebra).
   * Re-proving 383C with the textbook's induction-on-tree-order
     argument (the closed form no longer applies).

2. **Reframe the existing work as the "graded multiplicative
   algebra"**, distinct from Butcher's group. Document this
   prominently and update Lemma 383C's docstring to clarify which
   algebra it lives in. (We've done this partially in 081; expand.)

3. **Hybrid**: keep `convProduct` as-is for the multiset algebra,
   add a separate `butcherProduct` for the textbook convolution,
   and prove the inverse-existence theorem twice — once with our
   closed form, once with the textbook's recurrence.

## Recommended action for the planner

Option (2) for now (we've already chosen it implicitly through
081's cycle); option (1) eventually if downstream lemmas (383D,
386A — Runge–Kutta group) require Butcher's true convolution.

Specifically:

* Decide whether `lem:383D` (the partition-sum formula for `α⁻¹`)
  is feasible in our multiset algebra. If yes → continue with
  current encoding. If no → option (1) is needed before tackling
  383D.
* Strengthen the file-level docstring on `Section383.lean` to
  document the divergence at the top, not just buried in
  individual theorem comments.

## Status (cycle 082)

**Planner decision adopted: Option (b).** The refactor of
`convProduct` to use vertex-subset partition is deferred until
`lem:383D` or `thm:386A` becomes a blocker.

Rationale (per cycle 082 strategy):

* Option (a) would invalidate cycles 077–081's group-axiom chain
  (Lemma 383A multiplicativity, Lemma 383B associativity, Lemma
  383C inverse existence) and is a multi-cycle effort.
* The current convolution defines a valid graded-multiplicative
  algebra in which the cycle 077–081 lemmas are sound.
* `lem:383D` and `thm:386A` are explicitly *out of scope* for the
  next several cycles per this decision.

Cycle 082 actions taken in support of this decision:

1. File-level docstring on `OpenMath/Chapter3/Section383.lean`
   extended with a CAVEAT block documenting the multiset/vertex-
   subset divergence and pointing to this issue.
2. `lem:383D`, `thm:386A` to remain unscheduled until either (a)
   the refactor is undertaken or (b) downstream work strictly
   requires them.
