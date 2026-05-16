# Cycle 309 strategy

## Headline target

**Phase 2/3 of the §342 ↔ §321 Gauss–Legendre `RKTableau` lift**:
ship the general-`n` definition `butcherGaussLegendreRK (n : ℕ) :
RKTableau n` and the headline corollary
`butcherGaussLegendreRK_satisfiesB`, which lifts cycle 307's algebraic
B(2n) bridge onto a concrete `RKTableau`. Cycle 308 closed Phase 1 of
3 at `n = 1`; cycle 309 closes Phase 2 of 3 (general-`n` for B(2n)
only — the C(n)/D(n)/E(n,n) halves are Phase 3, multi-cycle and
deferred).

Per cycle 308 task results §"Suggested next approach", this is a
~10–20 LOC cycle. It is the obvious single-cycle clean ship.

## §A Deliverables

Append to `OpenMath/Chapter3/Section342.lean`, immediately after
cycle 308's `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage` and
its `example : butcherGaussLegendreRK_one.SatisfiesB 2`:

### A.1 — The general-`n` definition

```lean
noncomputable def butcherGaussLegendreRK (n : ℕ) :
    OpenMath.Chapter3.Section312.RKTableau n where
  A := butcherShiftedLegendre_collocationA n
  b := butcherShiftedLegendre_quadratureWeights n
  c := butcherShiftedLegendre_zeros n
```

Mirrors cycle 308's `butcherGaussLegendreRK_one` literal but with the
stage count abstracted to `n : ℕ`. All three fields are cycle
302/303/308 definitions; no new infrastructure.

### A.2 — Coincidence with `butcherGaussLegendreRK_one`

```lean
theorem butcherGaussLegendreRK_one_eq :
    butcherGaussLegendreRK 1 = butcherGaussLegendreRK_one := rfl
```

Should close by `rfl` (both reduce to the same `RKTableau.mk` literal
with identical field bodies). If `rfl` fails, fall back to
`RKTableau.mk.injEq.mpr ⟨rfl, rfl, rfl⟩` (the cycle 308 pattern for
per-field decomposition).

### A.3 — The headline B(2n) corollary

```lean
theorem butcherGaussLegendreRK_satisfiesB (n : ℕ) (hn : 0 < n) :
    (butcherGaussLegendreRK n).SatisfiesB (2 * n) := by
  intro k h1 hk
  show (∑ j : Fin n,
          butcherShiftedLegendre_quadratureWeights n j *
            butcherShiftedLegendre_zeros n j ^ (k - 1))
        = 1 / (k : ℝ)
  exact butcherShiftedLegendre_quadratureWeights_satisfiesB n hn k h1 hk
```

Direct port from the cycle 308 task results' quoted snippet. The
`show` step bridges `SatisfiesB`'s definitional unfolding to the
cycle 307 bridge's verbatim conclusion shape. The `intro k h1 hk`
matches `SatisfiesB`'s `∀ k : ℕ, 1 ≤ k → k ≤ K → ...` signature
(verify with `mcp__lean-lsp__lean_hover_info` on
`RKTableau.SatisfiesB` before writing if uncertain).

**Pre-flight check**: read `OpenMath/Chapter3/Section321.lean`
around the `SatisfiesB` def to confirm:

* whether `SatisfiesB` is `∀ k, 1 ≤ k → k ≤ K → ...` or `∀ k ∈ ..., ...`,
* whether the LHS is `∑ j, M.b j * M.c j ^ (k - 1)` or some other
  equivalent form (cycle 306 baseline).

If the LHS shape differs from the cycle 307 bridge's verbatim form
(`∑ j, _quadratureWeights n j * _zeros n j ^ (k - 1)`), the `show`
step may need adjustment. The cycle 307 bridge's `_satisfiesB` lemma
already has the exact `1 / (k : ℝ)` RHS; the only possible mismatch
is sum indexing or the `^ (k - 1)` placement, both of which a single
`simp only [butcherGaussLegendreRK]` should normalise away if `show`
doesn't.

### A.4 — Non-vacuity witness (`n = 2` instance)

```lean
example : (butcherGaussLegendreRK 2).SatisfiesB 4 :=
  butcherGaussLegendreRK_satisfiesB 2 (by norm_num)
```

Concrete witness at `n = 2` (so B(4)) exercises the general theorem
at a non-trivial stage count beyond cycle 308's `n = 1` anchor. If
Lean rejects the literal `4`, write `(butcherGaussLegendreRK 2).SatisfiesB (2 * 2)`
and discharge by `decide` or `norm_num`.

### A.5 — Optional stretch (only if A.1–A.4 close in ≤ 30 min)

Add a `gaussLegendre1Stage` round-trip witness:

```lean
example : (OpenMath.Chapter3.Section321.gaussLegendre1Stage).SatisfiesB 2 := by
  rw [← butcherGaussLegendreRK_one_eq_gaussLegendre1Stage,
      ← butcherGaussLegendreRK_one_eq]
  exact butcherGaussLegendreRK_satisfiesB 1 (by norm_num)
```

This proves §321's hand-defined `gaussLegendre1Stage` satisfies B(2)
via the cycle 309 general theorem rather than cycle 306's direct
`interval_cases k; simp` — a small but real validation that the
cycle 308/309 bridge is downstream-consumable.

## §B Workflow

1. **Pre-flight** (5 min): Use `mcp__lean-lsp__lean_hover_info` on
   `RKTableau.SatisfiesB` (find via Grep on
   `OpenMath/Chapter3/Section321.lean`) to confirm its precise
   signature shape. Confirm cycle 307's
   `butcherShiftedLegendre_quadratureWeights_satisfiesB` signature
   matches the `show` goal you'll write (Grep for the name in
   `OpenMath/Chapter3/Section342.lean`).
2. **Ship A.1** (`butcherGaussLegendreRK` def). Verify it compiles
   in isolation by adding it before A.2 and running
   `lake env lean OpenMath/Chapter3/Section342.lean`.
3. **Ship A.2** (`_one_eq` coincidence). Try `rfl` first; fall back
   to `RKTableau.mk.injEq.mpr ⟨rfl, rfl, rfl⟩` if needed.
4. **Ship A.3** (`_satisfiesB`). The `show` + `exact` shape above is
   verbatim correct per the cycle 307 bridge's existing signature.
   If `show` rejects the goal, switch to
   `simp only [butcherGaussLegendreRK,
   OpenMath.Chapter3.Section321.RKTableau.SatisfiesB]` (or whatever
   the unfolding lemma is — confirm via `lean_hover_info`) to expose
   the LHS, then `exact` the bridge.
5. **Ship A.4** (`n = 2` non-vacuity example).
6. **Compile-check** with `lake env lean OpenMath/Chapter3/Section342.lean`.
7. **Axiom-verify** all three new public symbols (A.1 def, A.2, A.3,
   plus A.5 if attempted) via `mcp__lean-lsp__lean_verify`. Expect
   `[propext, sorryAx, Classical.choice, Quot.sound]` — the
   pre-existing leak from cycle 301's `_rootsInIoo_card_ge`
   propagates here and is **not a regression** (cycle 308 has the
   same profile; see §D below).
8. **Update plan.md** to record the cycle 309 Phase 2/3 deliverable
   on the existing `lem:342B` line.
9. **Optional A.5** stretch only if steps 1–8 close in well under
   the cycle budget.

## §C What NOT to do

* **Do NOT attempt the C(n)/D(n)/E(n,n) order conditions.** Those
  require an upper-limit-parametrised version of cycle 304's
  `_quadrature_exact_lt_two_n` (integrating over `[0, cᵢ]` instead
  of `[0, 1]`), which is the cycle 310+ infrastructure step. Per
  cycle 308 §"Suggested next approach", that's Phase 3 of 3 and
  multi-cycle.
* **Do NOT attempt `cor:342D` (Gauss-Legendre order-2n RK condition).**
  It requires B(2n) ∧ C(s) ∧ D(s) → order 2n via the §314A
  elementary-weight argument. Three of those four pieces are
  multi-cycle work. Out of scope.
* **Do NOT attempt the upstream `sorryAx` cleanup on
  `_rootsInIoo_card_ge`** this cycle. It is a separate audit cycle.
  Mixing it with the Phase 2 lift risks blowing the LOC budget and
  the cycle's primary deliverable.
* **Do NOT define a new `SatisfiesB` predicate.** Reuse §321's
  exactly as cycle 307 / 308 did. Faithfulness check: the §321
  predicate is the textbook Butcher §321 B(η) condition.
* **Do NOT raise `maxHeartbeats`.** None of these proofs need it;
  the cycle 307 bridge is already proved and we are just lifting it
  onto a `RKTableau`.
* **Do NOT introduce new `sorry` or `axiom` declarations.** The
  sorry count must remain 0 on commit. (Cycle 308's task results
  confirm there is no `sorry` keyword in the file; the leak is
  purely upstream-propagated via `sorryAx` in the axiom check,
  which is a different concern.)
* **Do NOT pivot to a fresh entity (e.g. `cor:342D`, `thm:351B`,
  `lem:310B` Phase A.1) instead of this Phase 2 lift.** Cycle 308
  task results explicitly identified this Phase 2 deliverable as
  the obvious cycle 309 target (~10 LOC). Skipping it leaves the
  §342 ↔ §321 bridge partial at `n = 1` only, when general-`n` is
  one cycle away.
* **Do NOT use Aristotle.** There are no pending Aristotle results.
  The cycle 308 strategy did not submit any (manual closure was
  the recommended Branch B). This is a single-cycle deliverable
  that does not warrant Aristotle's 30-min minimum latency.

## §D Faithfulness check (mandatory pre-commit)

For each new `def`/`theorem`:

### `butcherGaussLegendreRK`

* Entity: no dedicated textbook entity; this is the *general-n*
  construction of the §342 collocation Gauss–Legendre RK method.
  The implicit-target entity is `cor:342D` (Gauss-Legendre order
  condition), which consumes B(2s) + C(s) + D(s); our B(2s) half
  is exactly cycle 309 A.3.
* Lean statement: A = `_collocationA n`, b = `_quadratureWeights n`,
  c = `_zeros n` — the §342 canonical Gauss–Legendre tableau.
* **Definition smuggling check**: ✓ this is the *primary* meaning
  of "the n-stage Gauss-Legendre RK method" (Butcher §342 p. 237).
  All three components are textbook definitions: the abscissae are
  the zeros of `P_n^*`, the weights are the canonical quadrature
  weights, and `A` is the collocation matrix from those abscissae.
  Cycle 309 does NOT smuggle any order conditions into the
  definition; they will be theorems (B(2n) here; C/D/E later).

### `butcherGaussLegendreRK_one_eq`

* Coincidence at `n = 1`. Both sides reduce to the same literal.
* **Tautology check**: `rfl` proof, but the statement is *not*
  vacuous — it asserts two distinct-looking constructions coincide.
  Genuine bookkeeping.

### `butcherGaussLegendreRK_satisfiesB`

* Headline. Lifts cycle 307's algebraic bridge onto a `RKTableau`.
* **Tautology check**: NO — the conclusion `SatisfiesB (2 * n)`
  unfolds via `show` to the cycle 307 bridge's exact statement;
  the `exact` is genuine work routing through cycle 304's `2n`-
  degree exactness theorem, NOT a hypothesis restatement.
* **Identity check**: NO — proof is `intro + show + exact <named
  lemma>`, three steps. Final `exact` cites cycle 307's bridge.
* **Hypothesis strength check**: `(hn : 0 < n)` matches cycle 307's
  bridge requirement. Textbook B(2n) holds for `n ≥ 1` (the n=0
  case is vacuous since `1 ≤ k ≤ 0` is empty); the explicit `0 < n`
  is faithful.
* **Absent theorem check**: cycle 307's
  `butcherShiftedLegendre_quadratureWeights_satisfiesB` exists at
  Section342.lean ~line 6740 (per cycle 307 task results); confirm
  the line with `Grep` if unsure.

### Pre-existing upstream `sorryAx` leak

All §342 theorems consuming `butcherShiftedLegendre_zeros` inherit
the `sorryAx` axiom from cycle 301's `_rootsInIoo_card_ge`. Cycle
308 documented this as **pre-existing and not a regression**;
cycle 309's new theorems will exhibit the same profile. Per cycle
308 task results §"Axiom check", the leak source is precisely
`_rootsInIoo_card_ge`; downstream cleanup is a separate audit
cycle. **Do not flag the `sorryAx` profile as a cycle 309 problem**
— it is the same axiom profile cycle 307 and cycle 308 shipped with.

## §E Risk assessment

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| `RKTableau.SatisfiesB` signature differs from cycle 308 strategy's quoted form | low | Pre-flight `lean_hover_info` (§B.1) confirms the shape before writing A.3 |
| `show` step rejects the unfolding | low–med | Fall back to `simp only [butcherGaussLegendreRK, RKTableau.SatisfiesB]` before `exact` |
| `rfl` fails on A.2 coincidence | low | Fall back to `RKTableau.mk.injEq.mpr ⟨rfl, rfl, rfl⟩` |
| A.4 `n = 2` non-vacuity hits `decide`/`norm_num` recalcitrance on `0 < 2` | very low | Write `by decide` if `by norm_num` doesn't fire |
| Compile time blows up due to large §342 file (~6900 LOC) | low | Cycle 308 reported 35s warm; ~10 LOC delta should not significantly change this |

No high-risk items. This is a near-mechanical port of cycle 308 with
the stage count abstracted from `1` to `n`.

## §F Bottom line

Ship A.1 + A.2 + A.3 + A.4 (≈ 25 LOC across four declarations).
Axiom-clean modulo the upstream `sorryAx` (pre-existing). Sorry count
remains 0. Cycle closes the B(2n) half of the §342 ↔ §321 lift in
full at all `n`. Phase 3 (C(n), D(n), E(n,n)) deferred to cycle
310+.
