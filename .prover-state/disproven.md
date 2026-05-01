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

**What is true**: the correct closed form needs a **disjoint pair**
`(S₁, S₂) : Finset (Fin n) × Finset (Fin n)` parametrization plus a
positional `trunkChildren` combinator that walks `Fin n` in order. The
cycle 590 issue file
`.prover-state/issues/butcher_section386_aug_replicate_singleton_leaf.md`
describes the correct shape.

**Do not** restate the parametric replicate-subtree closed form using a
single `Finset (Fin n)` powerset.

---

## How to add an entry

When a cycle proves an identity false, append a new section here with
the four fields above. Counterexample evaluations belong in
`.prover-state/issues/<topic>_counterexample.md`; this file is the
short-form index that gets shown to every prompt.

Do not delete entries — even old disproven identities may resurface as
plausible-looking proof targets.
