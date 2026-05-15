# Issue: Cycle 250 strategy proposed wrong definition of α(t)

## Blocker

(Resolved in cycle 250 by pivoting to the correct definition. Filed for
the planner so the same error does not recur.)

The cycle 250 strategy (Section F, "Phase B") proposed:

```lean
noncomputable def alphaWeight (t : RootedTree) : ℝ :=
  1 / (density t : ℝ)
```

with the docstring

> The elementary weight `α(t) := 1 / γ(t)` of a rooted tree
> (Butcher §312, the γ-only form), where γ(t) is the density from
> cycle 017.

This is **definition smuggling** (the exact pattern flagged by memory
`feedback_planner_faithfulness_spotcheck.md` and forbidden by
`CLAUDE.md` "Pre-Commit Faithfulness Checklist > Definition smuggling
check").

## Context — what Butcher actually says

Butcher's α(t) is defined in §302 (page 142) as the number of distinct
labellings of `t` satisfying conditions (i)–(iii) (each vertex labelled
exactly once; equivalent labellings under symmetry counted once; labels
along every edge increasing root-to-leaf). Theorem 302A then gives the
**closed form**:

> ```
>           r(t)!
> α(t) = ─────────         (302a)
>         σ(t) γ(t)
> ```

— `extraction/raw_text/ch03.txt:207–223` and `:743–796` (Table 310(II)
shows α-values that match (302a) for all 19 trees up to order 5).

The expression `1/γ(t)` (or `Φ(t) = 1/γ(t)`) does appear in the textbook
— but it is the **order condition** `Φ(t) = 1/γ(t)` for a Runge–Kutta
method to match the exact-solution expansion (see ch03.txt:1827 and
1927), NOT the definition of α(t). Calling `1/γ(t)` "the elementary
weight α(t), γ-only form" conflates two different objects.

## Specific harms had this been shipped

1. **Faithfulness violation.** A future planner cycle would believe
   `RootedTree.alphaWeight` IS Butcher's α(t) and use it as such in
   downstream §312/§315 work (Φ-comparison theorems, order conditions),
   silently propagating the error.

2. **Hidden symmetry term.** Butcher's α(t) carries σ(t) in its
   denominator. Code that consumes a `1/γ(t)`-only "α" would silently
   compute the wrong values for trees with nontrivial symmetry
   (`broom₃` has σ=2, so the real α is 6/(2·3) = 1, NOT 1/3 as the
   strategy's definition would give).

3. **Order-condition confusion.** `Φ(t) = 1/γ(t)` (ch03.txt:1827) is
   the order condition, NOT α(t). Mixing them obscures the distinction
   that ch03.txt:1149 explicitly emphasises ("σ(t)γ(t) appears in the
   denominator of α(t), γ(t) alone in the order condition").

## Resolution applied in cycle 250

Pivoted to the correct (302a) definition in
`OpenMath/Chapter3/Section301.lean`:

```lean
noncomputable def alphaWeight (t : RootedTree) : ℝ :=
  (Nat.factorial (order t) : ℝ) / ((symmetry t : ℝ) * (density t : ℝ))
```

Placed in Section301 (not Section310 as the strategy suggested) because
α(t) depends on `density` and `symmetry`, both defined in Section301.
Section310 cannot import Section301 (would be a cycle), so the
strategy's Section310 placement was impossible regardless of the
definition error.

Faithfulness convention adopted is the same one already used for
`RootedTree.symmetry` (file docstring's "σ-faithfulness divergence"):
define via the closed form (302a) and treat the equivalence with the
combinatorial labelling count as an unformalised mathematical fact.
The same downstream consumers that are unblocked by the σ-divergence
are also unblocked by the α-divergence.

Non-vacuity witnesses match Butcher Table 310(II):
- `α(τ) = 1` (r=1 row).
- `α(cherry) = 1` (r=2 row).
- `α(broom₃) = 1` (r=3 row).
- `α(mk [vertex, cherry]) = 3` (r=4 row, second entry — `f'(f, f'f)`).

The last witness is critical: it exercises a tree where the strategy's
`1/γ` formula would give 1/8 instead of 3, providing a regression check.

## Possible solutions (for the planner)

1. **Read entity JSONs more carefully when scaffolding around named
   textbook concepts.** The α/Φ/θ symbols in Butcher §3 are subtly
   different. Strategy docstrings that say "(γ-only form)" or similar
   ad hoc qualifiers around a textbook-named symbol should trigger a
   self-check.

2. **Spot-check via Butcher tables.** Table 310(II) gives α-values for
   all 19 small trees. Any proposed Lean α(t) should reproduce these
   for the standard test trees. This is a 1-minute sanity check that
   would have caught the (302a) ≠ 1/γ(t) discrepancy.

3. **Cross-reference the dependents list.** `lem:310B` (which the
   strategy named as the target) does NOT depend on α(t) — it depends
   on θ(t) and σ(t). A 5-second `dependencies` scan in `lem_310B.json`
   would have shown that "α(t) is a scaffold for lem:310B" is
   incorrect.
