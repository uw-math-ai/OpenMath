# Disproven Identities — DO NOT RE-ATTEMPT

This file lists statements that the project has **proved false** at some
point. Re-attempting any of them is a guaranteed waste of cycles.

The autonomous loop injects this file's contents into both the planner and
worker prompts every cycle, so the rules below are visible to every engine.

## Format

For each disproven identity:
- The statement (or shape of it)
- The cycle that produced the counterexample
- The counterexample / why it fails
- What's actually true (and where the salvaged version lives)

---

## 1. `bSeriesConvAug` associativity for **non-unital** middle factor — FALSE

**Cycle**: 583

**Statement (false)**:
```
bSeriesConvAug α (bSeriesConvAug β γ) τ = bSeriesConvAug (bSeriesConvAug α β) γ τ
```
without any unitality hypothesis on `β.emptyVal` or `γ.emptyVal`.

**Counterexample**: small concrete trees with `β.emptyVal ≠ 1` produce
unequal sides. The counterexample evaluation lives in
`.prover-state/issues/bseries_conv_aug_assoc_nonunital_counterexample.md`.

**What is true**: associativity holds on the **unital subspace** —
i.e. when both `β` and `γ` satisfy `β.emptyVal = 1` and `γ.emptyVal = 1`.
This unital version is the active §386 work in
`OpenMath/ButcherGroup/Section386Aug.lean`.

**Do not** re-attempt the unrestricted version. **Do not** weaken the
hypothesis to "only `β` unital" or "only `γ` unital" — both must be unital.

---

## 2. §388 left-cancellation for `bSeriesConv` — FALSE

**Cycle**: 578

**Statement (false)**:
```
bSeriesConv α β = bSeriesConv α γ → β = γ
```
for arbitrary `α` (no invertibility hypothesis).

**Counterexample**: `α = 0` (the all-zero B-series) makes both sides equal
the zero series for any `β, γ`, breaking the implication trivially.
Even non-zero non-unital `α` admits counterexamples since `bSeriesConv`
on the non-unital algebra is not cancellative.

**What is true**: cancellation **does** hold on the augmented unital
group `G1 p` (where `α` is forced unital and hence has an inverse). That
is the cycle 572–574 monoid + inverse infrastructure already in
`OpenMath/ButcherGroup.lean`.

**Do not** re-attempt unrestricted left/right cancellation for
`bSeriesConv`. **Do not** add an `α ≠ 0` hypothesis as a fix — that is
not strong enough.

---

## 3. Naive symmetric `Finset (Fin n)` powerset closed form for
`bSeriesConvAug α β (node (replicate n (node [leaf])))` — FALSE

**Cycle**: 587 (reverted)

**Statement (false)**:
```
bSeriesConvAug α β (node (replicate n (node [leaf])))
  = ∑ S : Finset (Fin n), <symmetric closed form over |S|>
```
i.e. any closed form that depends only on `|S|` and not on the *positions*
in the trunk.

**Counterexample**: at `τ = node [leaf]`, `α(leaf) = 1`, the symmetric
form collapses asymmetric trunks like `[node [leaf], node []]` and
`[node [], node [leaf]]` (which `bSeriesConvAug` distinguishes via the
list position of children) into one term, off by a position-dependent
factor. The cycle 590 manual expansion shows position order is
load-bearing.

**What was tried and failed**: the **disjoint pair**
`(S₁, S₂) : Finset (Fin n) × Finset (Fin n)` parametrization plus a
positional `trunkChildren` combinator that walks `Fin n` in order. Cycle
592 attempted this shape and was reverted (sorry count went 0 → 1 with
no proof landing). Cycle 595 re-introduced the disjoint-pair combinator
(`threeChoice`) as scaffolding and was flagged off-strategy.

**What is actually the path forward**: the **cons-decomposition** for
`bSeriesConvAug` at a `c :: cs` node head — `bSeriesConvAug_node_cons`
(landed cycle 594, recovered as commit 4507aadbc1). Once the cons-split
is solid, the unital associativity headline drops out of one mutual
`BTree.rec`. See strategy.md "Why this seam" for the architecture.

**Do not**:
- Restate the parametric replicate-subtree closed form using a single
  `Finset (Fin n)` powerset (the original cycle 587 form).
- Re-introduce the disjoint-pair `Finset (Fin n) × Finset (Fin n)`
  parametrization or any supporting combinator (`threeChoice`,
  `trunkChildren`, etc.) for the `replicate n (node [leaf])` shape.
  Cycle 592 already failed at this and cycle 595 re-attempted the
  scaffolding off-strategy. The disjoint-pair path stays closed until
  the cons-decomposition gives a generic seam.

---

## How to add an entry

When a cycle proves an identity false, append a new section here with
the four fields above. Counterexample evaluations belong in
`.prover-state/issues/<topic>_counterexample.md`; this file is the
short-form index that gets shown to every prompt.

Do not delete entries — even old disproven identities may resurface as
plausible-looking proof targets.
