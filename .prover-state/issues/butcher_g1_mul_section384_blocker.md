# Issue: `G1.mul` requires the §384 tree-coefficient convolution

## Blocker

Cycle 516 attempted to land the §38 group multiplication on the `G1 p`
quotient. The strategy outlined three steps:

1. `IsG1Equiv.product_congr` — congruence of the cross-stage relation
   `IsG1Equiv p` under `QuotEquiv.product`.
2. `G1.mul := Quotient.lift₂ ... QuotEquiv.product ...` using the
   well-definedness witness from step 1.
3. `G1.mul_mk` — the computation lemma.

Steps 2 and 3 are routine `Quotient.lift₂` boilerplate **once step 1
exists**. Step 1 is the obstruction.

`IsG1Equiv p q q'` is defined as

```
∀ τ : BTree, τ.order ≤ p → q.bSeriesHom τ = q'.bSeriesHom τ
```

so `IsG1Equiv.product_congr` reduces (at a fixed tree `τ` with
`τ.order ≤ p`) to:

```
(q.product r).bSeriesHom τ = (q'.product r').bSeriesHom τ
```

given the per-tree-fixed agreement of `q, q'` and of `r, r'` on every
tree of order ≤ `p`.

## Why this is the §384 convolution gap

For representatives `t₁ : ButcherTableau s` and `t₂ : ButcherTableau t`,
the b-series coefficient of `ButcherProduct t₁ t₂` at a node tree
`node children` decomposes over the two stage blocks. The left block
(rows in `Fin (Fin.castAdd t '_)`) yields `t₁.bSeries τ` because the
upper-right block of `ButcherProduct.A` is zero, so the recursion stays
inside the first factor.

The right block (rows in `Fin (Fin.natAdd s '_)`) yields a contribution

```
∑ i : Fin t, t₂.b i · ψ(τ, i)
```

where the auxiliary `ψ : BTree → Fin t → ℝ` satisfies

```
ψ(leaf, i) = 1
ψ(node children, i) =
  children.foldr
    (fun c acc => acc * (t₁.bSeries c + ∑ j, t₂.A i j * ψ(c, j))) 1
```

Expanding the foldr's product across children as a sum over subsets `S`
of children — those in `S` "stay attached" to the second factor, those
not in `S` are "pinched off" via `t₁`'s bSeries — and recursing on the
attached side, one obtains a closed form

```
∑ i, t₂.b i · ψ(τ, i)
  = ∑ (trunk, cuts) of τ,
      (∏ cut, t₁.bSeries cut) · t₂.bSeries trunk
```

The right-hand side mentions `t₁` and `t₂` only through `bSeries`
values on subtrees of `τ`, which all have order ≤ `τ.order ≤ p`. Once
this closed form is in Lean, `IsG1Equiv.product_congr` is a one-line
consequence of the per-tree agreement hypotheses.

The closed form is the §384 honest convolution. Defining it is exactly
what
[`butcher_section384_convolution.md`](butcher_section384_convolution.md)
records as the open obstruction. Cycle 512 attempted a tautological
shortcut (`bSeriesConvolution q₁ q₂ τ := (q₁.product q₂).bSeries τ`),
which trivialises the headline statement without expressing Butcher's
homomorphism, raised the file's sorry count 0 → 2, and was reverted.

The strategy for cycle 516 claimed the per-block decomposition could be
done without the §384 convolution by inducting on `τ`. The induction
needs an inductive hypothesis stating exactly the closed form above —
because the right-block contribution `ψ` involves the full structure of
`t₂.A` on internal nodes, not just `t₂.bSeries` values. There is no
proof of `IsG1Equiv.product_congr` that bypasses formalising the
convolution.

## What was tried in cycle 516

- The sorry-first scaffold for `IsG1Equiv.product_congr` was prepared in
  `.prover-state/aristotle_scaffolds/cycle_516/product_congr.lean`.
- Aristotle was submitted once and returned HTTP 429 immediately; per
  the strategy, no retry was attempted.
- A direct manual proof was scoped: the per-tree-fixed reduction is
  fine, but the inductive step for `node children` requires the closed
  convolution decomposition. Without `(q.product r).bSeriesHom τ`
  expressed as a function of `q.bSeriesHom`, `r.bSeriesHom` values on
  subtrees, the per-tree hypotheses cannot be applied.

## Possible resolutions

1. Formalise the §384 convolution as a recursive `BTree`-indexed
   operation on coefficient functions, with explicit subset / forest
   pruning combinators, then prove

   ```
   (q.product r).bSeriesHom τ
     = q.bSeriesHom τ
       + (right-block convolution of q.bSeriesHom and r.bSeriesHom at τ)
   ```

   This is the path documented in
   `butcher_section384_convolution.md`. Once it lands,
   `IsG1Equiv.product_congr` is essentially a corollary.

2. Strengthen the relation underlying `G1 p`. Replacing `IsG1Equiv` by
   `IsRKEquivalentExt` would give a quotient on which `product_congr`
   is provable (relabel-equivalence is preserved by `ButcherProduct`
   via `ButcherProduct.equiv_congr` once both sides are padded to a
   common stage count). This produces a *different* quotient, *not*
   Butcher's `G₁(p)`, and is therefore not a substitute. It is a
   reasonable intermediate object to study while the §384 convolution
   is being built.

3. Stage the §38 group construction differently: define `G1.mul` only
   on a subquotient where representatives are already known to commute
   nicely with `ButcherProduct` (e.g., classes whose representatives
   admit a permutation matching `IsRKEquivalentExt`). This is brittle
   and not aligned with Butcher's textbook presentation.

The recommended resolution is (1).

## Downstream consequences

Until this blocker is cleared:

- `G1.mul`, `G1.mul_mk`, `G1.bSeriesHomAt_mul`, `G1.one_mul`,
  `G1.mul_one`, `G1.mul_assoc`, `G1.npow`, and `G1.inv` all wait.
- The §38 group structure (`Group (G1 p)` instance) cannot be
  assembled.
- The §387 powers `G1.npow` only need a working `G1.mul` to lift from
  `QuotEquiv.npow`, so they are also blocked.

## What is unblocked

- `G1` itself (the quotient carrier).
- `G1.mk`, `G1.bSeriesHomAt`, `G1.satisfiesTreeCondition`,
  `G1.hasTreeOrder` and the `_mk` computation lemmas (cycle 515).
- `G1.one` (the identity element as a class), `G1.bSeriesHomAt_one`
  (cycle 516).
- Extensionality / characterization lemmas: `G1.ext`,
  `G1.eq_iff_forall_bSeriesHomAt`, `G1.mk_eq_mk_iff_isG1Equiv`,
  `G1.hasTreeOrder_iff_forall` (cycle 516).
- Cross-stage equivalence at the `IsRKEquivalentExt` level still
  upgrades to `IsG1Equiv` for free via `IsRKEquivalentExt.toG1Equiv`.
