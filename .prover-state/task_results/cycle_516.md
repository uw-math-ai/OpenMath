# Cycle 516 Results

## Worked on
Butcher §38 group structure on `G1 p` in `OpenMath/ButcherGroup.lean`.

## Approach
The strategy directed three steps to land:
`IsG1Equiv.product_congr`, `G1.mul`, `G1.mul_mk` (with optional
`G1.bSeriesHomAt_mul`). Step 1 is the well-definedness witness for
`Quotient.lift₂`-based steps 2 and 3.

I prepared a sorry-first scaffold for `IsG1Equiv.product_congr` in
`.prover-state/aristotle_scaffolds/cycle_516/product_congr.lean`,
submitted it to Aristotle, and analysed manual closure paths in
parallel.

The strategy claimed the cross-stage congruence "is **not** the §384
honest convolution gap" because the b-series of a `ButcherProduct`
splits into a left-block and right-block contribution. This is partly
true: the left block reduces immediately to `t₁.bSeries τ` because
`ButcherProduct.A`'s upper-right block is zero. The **right block** is
where the strategy is overconfident. Tracing through

```
ψ(τ, i) := (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.natAdd s i)
```

gives the recursion

```
ψ(node children, i)
  = children.foldr
      (fun c acc => acc * (t₁.bSeries c + ∑ j, t₂.A i j * ψ(c, j))) 1
```

The closed-form decomposition

```
∑ i, t₂.b i * ψ(τ, i)
  = ∑ (trunk, cuts) of τ,
      (∏ cut, t₁.bSeries cut) * t₂.bSeries trunk
```

would let `IsG1Equiv.product_congr` follow as a one-line consequence
of the per-tree-fixed agreement hypotheses. The closed-form
decomposition **is** the §384 honest convolution recorded in
`.prover-state/issues/butcher_section384_convolution.md`. There is no
proof of `IsG1Equiv.product_congr` that bypasses formalising it,
because the right-block contribution genuinely involves `t₂.A`
internal to the recursion, not just `t₂.bSeries` values.

Given this, I pivoted to landing a substantive cycle-516 deliverable
that is unblocked by §384 and closes a real chunk of the §38 surface.

## Result
SUCCESS on the unblocked surface. Added to `OpenMath/ButcherGroup.lean`
inside the existing `G1` namespace:

- `G1.one : ℕ → G1 p` — the §387 identity element as the `G1`-class of
  `trivialTableau`.
- `G1.bSeriesHomAt_one` — `bSeriesHomAt p τ hτ (G1.one p) = 0`,
  by reduction through `G1.mk` and the cycle-503 `bSeriesHom_one`.
- `G1.ext` — extensionality: `g₁ = g₂` if their `bSeriesHomAt`
  agree on every tree of order ≤ `p`.
- `G1.eq_iff_forall_bSeriesHomAt` — iff form of the above.
- `G1.mk_eq_mk_iff_isG1Equiv` — class-equality bridge:
  `G1.mk q = G1.mk q' ↔ IsG1Equiv p q q'`.
- `G1.hasTreeOrder_iff_forall` — quotient-level characterization
  matching `IsRKEquivalentExt.hasTreeOrder_iff_forall`.

`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/ButcherGroup.lean` succeeds with no `sorry` reported in any
new declaration.

The §38 group multiplication is recorded as §384-blocked in a fresh
issue file `.prover-state/issues/butcher_g1_mul_section384_blocker.md`,
which lays out the `(trunk, cuts)` analysis above, lists what is and
is not unblocked, and recommends formalising the §384 convolution as
the resolution.

`plan.md` was updated in two places: the §383 status entry now lists
the cycle-516 declarations, and the Current Target body explicitly
flags the §38 multiplication as §384-blocked while the §387 identity,
the extensionality layer, and any `G1.npow`-style stage-count
arithmetic remain unblocked. The Current Target was not rotated — §38
is still in progress.

## Aristotle
Submitted the planned scaffold:

1. `IsG1Equiv.product_congr_target`, the cross-stage congruence stub.

The submission immediately returned HTTP 429
("You have too many requests in progress"). Per the strategy, no
retry. This matches the recent cycle-495/503/507/509/511/512/513/515
pattern.

## Dead ends
- Trying to side-step the §384 convolution by inducting on `τ` alone:
  the inductive hypothesis on subtrees does not chain into the
  right-block contribution because `ψ(c, j)` recurses on `t₂.A`
  internally rather than on `t₂.bSeries(c)` directly.
- Trying to reduce to `IsRKEquivalent` (same stage count) to reuse
  `ButcherProduct.equiv_congr`: `IsG1Equiv` is strictly weaker than
  `IsRKEquivalent` even at fixed stage count (`IsG1Equiv` only sees
  bSeries values, not the `A`/`b`/`c` permutation), so this does not
  cover the actual hypothesis.
- Considering whether `IsRKEquivalentExt.product_congr` (cross-stage
  relabel-equivalence) could substitute: it does not, because the
  `G1 p` quotient is over `IsG1Equiv` (strictly coarser), and the
  blocker is on the coarser side.

## Discovery
- `bSeriesHomAt` for `G1 p` is faithful at order ≤ `p`: equality of
  `G1 p` classes is exactly equality of all order-≤`p` Butcher-series
  coefficients. This is the cycle-516 `G1.ext` /
  `G1.eq_iff_forall_bSeriesHomAt` / `G1.mk_eq_mk_iff_isG1Equiv` layer
  and is the right characterization to lean on for any future
  multiplication / inverse / power equality after §384 lands.
- `G1.one` is a clean standalone definition that needs no congruence
  lemma. `G1.bSeriesHomAt_one = 0` is the §387 vanishing identity at
  the quotient level and lifts cleanly from cycle 503's
  `QuotEquiv.bSeriesHom_one`.
- The cycle-515 `bSeriesHomAt_mk` simp lemma drives the `G1.one`
  computation reduction by `unfold one` plus the `_mk` rewrite,
  exactly as it should for any future `G1.mul_mk`-style lemmas.
- The §387 group identity `G1.one_mul`, `G1.mul_one` will follow
  from `G1.ext` plus `G1.bSeriesHomAt_one` and (when available) the
  product-side computation lemma `G1.bSeriesHomAt_mul` once the
  `G1.mul` blocker is cleared.

## Suggested next approach
Two options for cycle 517:

1. **Tackle the §384 convolution head-on.** Define the recursive
   tree-coefficient convolution `BTree → (BTree → ℝ) → (BTree → ℝ) → ℝ`
   with the explicit `(trunk, cuts)` decomposition (or the equivalent
   children-foldr / subset expansion), prove
   `(q.product r).bSeriesHom τ = q.bSeriesHom τ + (rightBlock q.bSeriesHom r τ)`,
   and unblock everything downstream (`G1.mul`, `G1.npow`-power
   homomorphism, the §38 `Group (G1 p)` instance). This is the path
   recorded in `butcher_section384_convolution.md` and now
   `butcher_g1_mul_section384_blocker.md`. It is the highest-leverage
   step in §38.

2. **Stay on the unblocked §387 / `G1` characterization layer.** Add
   `G1.satisfiesTreeCondition_one` (vacuously false above order 1, so
   the right statement is `G1.hasTreeOrder_one_zero` for `p = 0`),
   `G1.bSeriesHomAt_mk` simp variants, and `G1`-side wrappers for the
   already-landed `QuotEquiv.npow_*` arithmetic that do not require
   `G1.mul`. These are smaller wins but keep cycle scope honest.

Cycle 517 should pick (1) if the planner believes the convolution is
ready to land; otherwise (2). Do not attempt `IsG1Equiv.product_congr`
again until (1) has produced the closed-form right-block decomposition.
