# Cycle 082 Results

## Worked on

- **Priority 0**: documented the multiset/vertex-subset convolution
  divergence at the file-level docstring of
  `OpenMath/Chapter3/Section383.lean`, and appended a "Status (cycle
  082)" subsection to
  `.prover-state/issues/convolution_vertex_vs_multiset.md` recording
  the planner decision (option (b) — defer the refactor).
- **Priority 1a**: closed `convProduct_one_right` and
  `convProduct_one_left` (right and left identity laws of `convOne`
  in the convolution algebra).
- **Priority 1b**: closed `inverse_unique` (uniqueness of two-sided
  convolution inverses).
- **Priority 1c**: closed `convInverse_convInverse` (involution of
  the closed-form inverse, stretch goal).
- Two new private helper lemmas, `sum_powerset_indicator_zero` and
  `sum_powerset_indicator_top`, supporting the identity laws.

## Approach

* Both identity laws were reduced to a generic indicator-sum
  identity over `Multiset.powerset`, which I proved by induction
  using `Multiset.powerset_cons` together with `Multiset.cons_ne_zero`
  (for the zero-indicator helper) and a cardinality argument plus
  `Multiset.cons_inj_right` (for the top-indicator helper).
* `inverse_unique` was a textbook five-step `calc` chain through the
  identity laws and `convProduct_assoc`.
* `convInverse_convInverse` fell out of `inverse_unique` once the
  implicit `α` was given explicitly via `(α := convInverse α)`.

## Result

SUCCESS.

* `lake env lean OpenMath/Chapter3/Section383.lean` — clean.
* `lake build OpenMath.Chapter3.Section383` — successful.
* `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`
  for all four new theorems.
* Zero `sorry`s in the file.

Lemma counts in `Section383.lean`: previously 53/175; this cycle's
additions are helper/private lemmas, not textbook entities, so
`lean_status.json` is unchanged (per Priority 2 expectation).

## Faithfulness check

For each new theorem (no textbook entity IDs — all four are
helper/structural lemmas in the convolution algebra):

- `convProduct_one_left`, `convProduct_one_right`: direct
  consequences of the `convOne` indicator definition; the proofs do
  genuine combinatorial work (powerset induction, summand
  rewriting) — not bare `exact h`. No hypothesis on `α` because the
  `convOne` indicator collapses the convolution sum without needing
  multiplicativity of `α` (matches the planner's hypothesis-strength
  note).

- `inverse_unique`: standard group-uniqueness `calc` chain. No
  multiplicativity hypothesis (the four cited lemmas
  `convProduct_one_left/right` and `convProduct_assoc` themselves
  drop multiplicativity).

- `convInverse_convInverse`: needs `IsMultiplicative α` because
  `convProduct_convInverse` requires it. Tautology check: the
  conclusion `convInverse (convInverse α) = α` does not appear
  verbatim as a hypothesis. Identity check: the proof invokes
  `inverse_unique` with two non-trivial witnesses
  (`convProduct_convInverse` applied to `convInverse_isMultiplicative
  α` and to `hα`); not a bare re-export.

Definition smuggling check: no new `def` or `structure` introduced
this cycle.

The two `private` helpers `sum_powerset_indicator_zero` and
`sum_powerset_indicator_top` are pure Multiset combinatorics, no
textbook content.

## Dead ends

* My first draft of `convInverse_convInverse` left the implicit
  `α` of `inverse_unique` ambiguous (compiler couldn't synthesize
  it from `?_`); fixed by passing `(α := convInverse α)`
  explicitly. Cost ~1 minute.

## Discovery

* `tsub_eq_zero_iff_le` works on `Multiset` directly (via the
  `OrderedSub` typeclass), no `Multiset`-specific lemma needed.
  Useful for the left-identity proof: `S - R = 0 ↔ S ≤ R`, combined
  with `R ≤ S`, gave `R = S` cleanly.
* The two indicator-sum helpers
  (`sum_powerset_indicator_zero`/`_top`) may be reusable in any
  future powerset-sum collapse arguments — they are stated for
  `Multiset RootedTree` but the proofs are generic and could be
  hoisted to `Multiset α` if a future use case demands it.

## Suggested next approach

Per Priority 4 (cycle 083 scoping): I read four candidate entity
files and rate them as follows.

* `lem:311A` (Taylor expansion of exact solution): **heavy**.
  Inductive proof requires elementary-differential formalization
  (`F(|t|)`), function trees, the chain rule applied to compositions,
  and `f^{(k)}` Fréchet derivatives. Transitive dependencies include
  `thm:301A`, `thm:306A`, `thm:311B`, `def:310A`, `lem:310B` — i.e.
  the whole §31 elementary-differential machinery is upstream.
  Skip for cycle 083.

* `lem:441A` (Max order for convergent k-step method): **moderate**.
  A polynomial-decomposition argument. Statement is concrete (real
  coefficients, conjugate-pair root analysis, sign deductions) but
  depends on `def:403A` (stability), `def:404B` (consistent LMM),
  `lem:441B` and `thm:441C` — the §404 LMM-consistency
  infrastructure must be in place first. Tractable but only if §404
  prereqs are landed; not a one-cycle target on its own.

* `def:422B` (underlying one-step method): **heavy and risky**.
  Defined in terms of an inductively-constructed mapping `η ∈ G₁`
  satisfying eqn (422a). G₁ here is precisely the convolution group
  whose multiset/vertex-subset divergence we just escalated;
  formalizing this definition before resolving the divergence
  bakes our weakened convolution into a downstream-visible
  definition. Strongly defer until the convolution decision is
  re-examined.

* `lem:322A` (Methods of order 4 — the 3×3 matrix lemma):
  **lightweight, standalone, dependency-free**. A pure linear
  algebra statement about a singular product of two 3×3 matrices
  ("either the last row of P is zero or the last column of Q is
  zero", given a 2×2 invertible block in the upper-left of `PQ`).
  Zero dependencies. Mathlib has all the linear algebra needed
  (left/right kernels, singularity, vector multiplication). Estimated
  one cycle. **Recommended target for cycle 083.**

If the planner accepts `lem:322A` for cycle 083, it would be a
clean Chapter-3 algebraic win that does not depend on either the
elementary-differential machinery or the §380 convolution group, and
would cleanly avoid the ongoing convolution-divergence concern.
