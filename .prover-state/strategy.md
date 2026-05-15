# Cycle 255 Strategy — §310 B-series partial sum infrastructure

## A. Context recap (one paragraph)

Cycle 254 shipped `RootedTree.bseriesTerm` (Phase A.0 of `lem:310B`)
axiom-clean in `OpenMath/Chapter3/Section301.lean` (lines 548–620 —
**not** Section310.lean, because `bseriesTerm` depends on `symmetry`
which lives in Section301; placing it in Section310 would invert the
import order — see cycle 254 task results "Placement correction"
section before doing **any** §310 work in cycle 255). Sorry count
across the repo: 0. Semantic sorry count: 11 (unchanged). Cycle 254
worker explicitly listed `TruncatedRootedTree` + `bseriesPartialSum`
as the cycle 255 candidates; this strategy commits to them.

No Aristotle results are pending. No incoming bug reports. No
supervisor-flagged issues for cycle 254 (the prior `attempts.md`
entries about phantom verdicts are loop-maintainer territory, not
worker territory — do NOT chase them).

## B. Target — single-cycle deliverable

Ship **Phase A.1 + A.2** of the `lem:310B` roadmap in
`OpenMath/Chapter3/Section301.lean` (after cycle 254's `bseriesTerm`
non-vacuity examples, before `end RootedTree`):

### P1 (REQUIRED) — `TruncatedRootedTree` subtype

Add the bounded-order subtype with minimal API:

```lean
/-- A rooted tree of order at most `N`. The `TruncatedRootedTree N`
subtype is the natural index set for B-series partial sums truncated
at order `N` (Butcher §310, the `O(h^{N+1})`-residual form). -/
def TruncatedRootedTree (N : ℕ) : Type :=
  { t : RootedTree // order t ≤ N }

namespace TruncatedRootedTree

instance instCoe (N : ℕ) : Coe (TruncatedRootedTree N) RootedTree :=
  ⟨Subtype.val⟩

/-- Order projection: `order (t : TruncatedRootedTree N) ≤ N`. -/
def order {N : ℕ} (t : TruncatedRootedTree N) : ℕ :=
  RootedTree.order t.val

theorem order_le {N : ℕ} (t : TruncatedRootedTree N) : t.order ≤ N :=
  t.property

end TruncatedRootedTree
```

**Do NOT** attempt a `Fintype (TruncatedRootedTree N)` instance.
That requires recursing through the nested-inductive structure of
`RootedTree` and is multi-cycle work (the `Fintype` instance for
`{ t : RootedTree // order t ≤ N }` would need a decidable
finite-enumeration of all rooted trees up to order `N`, which is
mathematically Cayley's formula territory). The `Fintype`-blocked
path remains deferred for at least 3-5 more cycles.

### P2 (REQUIRED) — `bseriesPartialSum` over `Finset RootedTree`

Because `Fintype (TruncatedRootedTree N)` is unavailable, the partial
sum is parameterized by an arbitrary `Finset RootedTree` (hand-
enumerated at call sites for small-order witnesses):

```lean
/-- B-series partial sum over a finite set of rooted trees. For a
small hand-enumerated `S`, this approximates the full B-series
`(310i)` to `O(h^{N+1})` where `N` bounds the orders in `S`. -/
noncomputable def bseriesPartialSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (S : Finset RootedTree) : E :=
  ∑ t ∈ S, bseriesTerm f y₀ h t
```

Plus the basic algebraic facts:

```lean
@[simp]
theorem bseriesPartialSum_empty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) :
    bseriesPartialSum f y₀ h ∅ = 0 := by
  simp [bseriesPartialSum]

theorem bseriesPartialSum_insert
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) {t : RootedTree} {S : Finset RootedTree}
    (ht : t ∉ S) :
    bseriesPartialSum f y₀ h (insert t S) =
      bseriesTerm f y₀ h t + bseriesPartialSum f y₀ h S := by
  simp [bseriesPartialSum, Finset.sum_insert ht]
```

### P3 (REQUIRED) — Non-vacuity witnesses

Compute `bseriesPartialSum` on explicit hand-enumerated Finsets:

```lean
example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesPartialSum f y₀ h {vertex} = h • f y₀ := by
  rw [bseriesPartialSum, Finset.sum_singleton]
  exact bseriesTerm_vertex f y₀ h

example (f : ℝ → ℝ) (y₀ h : ℝ) (hcv : cherry ≠ vertex) :
    bseriesPartialSum f y₀ h {vertex, cherry} =
      h • f y₀ + bseriesTerm f y₀ h cherry := by
  rw [show ({vertex, cherry} : Finset RootedTree) =
        insert vertex {cherry} from rfl,
      bseriesPartialSum_insert _ _ _ (by simp [Finset.mem_singleton, hcv.symm]),
      bseriesPartialSum, Finset.sum_singleton, bseriesTerm_vertex]
```

The `hcv : cherry ≠ vertex` hypothesis is needed because Lean cannot
auto-decide inequality of nested inductive constructors. If
`DecidableEq RootedTree` is missing, fall back to passing the inequality
explicitly. If `DecidableEq RootedTree` is already available (it might
be auto-derived), the example simplifies — check with
`#synth DecidableEq RootedTree` and `Finset.mem_singleton` simp lemma.

### P4 (STRETCH — only if P1-P3 use <60% of cycle)

Add a membership predicate connecting `TruncatedRootedTree N` to a
`Finset` of trees with bounded order:

```lean
/-- If every tree in `S` has order at most `N`, then every `t ∈ S`
lifts to a `TruncatedRootedTree N`. Useful for stating B-series
truncation results indexed by `TruncatedRootedTree N`. -/
theorem exists_truncated_of_forall_order_le
    {N : ℕ} {S : Finset RootedTree}
    (hS : ∀ t ∈ S, RootedTree.order t ≤ N) :
    ∀ t ∈ S, ∃ t' : TruncatedRootedTree N, t'.val = t := by
  intro t ht
  exact ⟨⟨t, hS t ht⟩, rfl⟩
```

Skip P4 entirely if P1-P3 isn't axiom-clean by the 60% cycle mark.

## C. Required forbiddens (do NOT attempt this cycle)

1. **Do NOT attempt full `lem:310B`.** Per cycle 254's faithfulness
   discussion, the full lemma needs:
   - `thm:306A` (Taylor's theorem, multinomial expansion) — multi-
     cycle, unformalized.
   - Labelled-tree quotient infrastructure (`def:300C`) — absent.
   - Orbit-counting combinatorial bridge.
   The pointwise scaffold `bseriesTerm_eq_theta_smul_bseriesTerm` from
   cycle 254 is the only `lem:310B`-adjacent claim allowed.
2. **Do NOT attempt small-r `lem:310B` cases** (e.g., "for
   `TruncatedRootedTree 2`, state and prove `lem:310B`"). The LHS of
   `lem:310B` is a labelled-tree-orbit sum that we cannot state
   without `def:300C`. Hand-enumerating doesn't help.
3. **Do NOT attempt `Fintype (TruncatedRootedTree N)`.** Multi-cycle
   per §B P1 above.
4. **Do NOT attempt `lem_311A_order_two`** (cycle 248 P2(a)). It
   requires the `iteratedFDeriv ℝ 1 ↔ fderiv` Mathlib bridge plus
   chain-rule extraction of `iteratedDeriv 2 yex x₀`. Estimated 150-
   250 LOC and 2 cycles; doesn't fit.
5. **Do NOT pivot to `def:381F` follow-up or `thm:381H`.** Those
   require the multi-cycle Banach fixed-point bridge
   (`thm_381H_deferred.md`).
6. **Do NOT attempt to compile `OpenMath/Chapter4/Section441.lean`**.
   Per `cycle_182_gpfs_slowness.md`, that file's transitive
   Mathlib.Analysis closure triggers 43+ consecutive GPFS timeouts.
   Cycle 255 work is in Section301.lean only.
7. **Do NOT raise `maxHeartbeats` above 200000.** If a `simp` set
   timeout occurs, factor into smaller helpers.
8. **Do NOT introduce `axiom`/`constant` declarations.**
9. **Do NOT introduce sorries.** Cycle 254 was sorry-clean; cycle 255
   must remain sorry-clean. Sorry-first scaffolds for `TruncatedRootedTree`
   or `bseriesPartialSum` are forbidden — both definitions are
   short and have natural inhabitants.
10. **Do NOT edit `scripts/autonomous_loop.py` or the prompt-builder.**
    Tautology-scanner false positives are loop-maintainer territory.
11. **Do NOT rename or audit cycle 254's `bseriesTerm`,
    `bseriesTerm_vertex`, or `bseriesTerm_eq_theta_smul_bseriesTerm`.**
    They are axiom-clean and load-bearing.

## D. Approach (concrete)

1. **Read the placement context** (5 min). Verify cycle 254's
   declarations end at line ~620 of Section301.lean, immediately
   before `end RootedTree`. The new P1-P4 content goes between the
   last cycle 254 example and `end RootedTree` — keep everything
   inside the `OpenMath.Chapter3.Section310.RootedTree` namespace
   block (cycle 254 added bseriesTerm there; cycle 255 continues).

2. **Ship P1 (10 min)**. Five-ish lines: the `TruncatedRootedTree N`
   definition, its `instCoe` instance, the `order` projection, and
   the `order_le` accessor. Verify with `lake env lean
   OpenMath/Chapter3/Section301.lean`; expect a warm rebuild (cycle
   254's edits already populated the cache).

3. **Ship P2 (15 min)**. Three declarations: `bseriesPartialSum`
   (noncomputable def), `bseriesPartialSum_empty` (@[simp] via
   `simp [bseriesPartialSum]` → `Finset.sum_empty`), and
   `bseriesPartialSum_insert` (one-liner via `Finset.sum_insert`).
   All three should close via `simp` after unfolding. Verify with
   `lean_verify` on each.

4. **Ship P3 (15 min)**. Two `example` blocks. The singleton case is
   straightforward via `Finset.sum_singleton` + cycle 254's
   `bseriesTerm_vertex`. The two-element case needs care: if
   `DecidableEq RootedTree` is auto-derived (check via
   `#synth DecidableEq RootedTree`), use `Finset.mem_insert` /
   `Finset.mem_singleton`. If not, pass `cherry ≠ vertex` as an
   explicit hypothesis (this is the safe path — Lean's nested
   inductive `RootedTree` may not auto-derive `DecidableEq`).

   **Discovery loop**: if `cherry ≠ vertex` cannot be proved by
   `decide` (because of nested inductive Bool issues), provide it
   as a hypothesis in the example. Document the discovery in the
   task results for future cycles.

5. **(Optional) Ship P4 (15 min)**. Only if P1-P3 closed cleanly in
   <60% of cycle. P4 is a one-line existence theorem; skip if any
   doubt.

6. **Verification protocol**:
   - `lake env lean OpenMath/Chapter3/Section301.lean` — must exit 0.
   - `lake env lean OpenMath/Chapter3.lean` — regression check; must
     exit 0.
   - `grep -c sorry OpenMath/Chapter3/Section301.lean` — must be 0.
   - Tautology scanner regex
     `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` — must return
     no matches on the new content (run with `Grep`).
   - `lean_verify` on each new public declaration (`TruncatedRootedTree`,
     `TruncatedRootedTree.order`, `TruncatedRootedTree.order_le`,
     `bseriesPartialSum`, `bseriesPartialSum_empty`,
     `bseriesPartialSum_insert`) — must return
     `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).

## E. Mathlib hooks (verify with `lean_local_search` if any drift)

| Goal | Lemma | Risk |
|---|---|---|
| `∑ t ∈ ∅, _ = 0` | `Finset.sum_empty` | low |
| `∑ t ∈ insert x s, f t = f x + ∑ t ∈ s, f t` (when `x ∉ s`) | `Finset.sum_insert` | low |
| `∑ t ∈ {x}, f t = f x` | `Finset.sum_singleton` | low |
| `t ∈ {x} ↔ t = x` | `Finset.mem_singleton` | low |
| `t ∈ insert x s ↔ t = x ∨ t ∈ s` | `Finset.mem_insert` | low |
| `Subtype` coercion | `Subtype.val`, `Subtype.coe_mk` | low |
| `{a, b}` literal `= insert a {b}` | by `rfl` (Lean's `{a, b}` notation) | low |

All low-risk; all are standard Mathlib. Do **not** spend time on a
broad Mathlib search before starting — these names are stable. If a
specific name has drifted, `lean_loogle` on the type pattern returns
the right one in one query.

## F. Risk register and mitigations

### R1 — `DecidableEq RootedTree` may not be auto-derived

If `cherry ≠ vertex` cannot be closed by `decide`, the two-element
P3 example needs to take the inequality as a hypothesis (as shown in
§B P3). This is fine: the example still demonstrates
`bseriesPartialSum_insert` on a non-singleton Finset. Worst case:
skip the two-element example and ship two singleton examples
(`{vertex}` and `{cherry}` separately) — still satisfies non-vacuity.

### R2 — `TruncatedRootedTree`-as-subtype unification quirks

If Lean has trouble unifying `t : TruncatedRootedTree N` with a
`RootedTree` argument expecting `mk children`, the `instCoe`
mechanism may need `@` annotations at call sites. Mitigation: P1's
deliverable does not require any cycle-255 theorem to consume the
subtype; the subtype is *scaffold for future cycles*. If P4 (the
existence theorem) hits a subtype-unification snag, ship P4 with the
weaker `t' = ⟨t, hS t ht⟩` directly (skipping the implicit
coercion), or skip P4 entirely.

### R3 — `bseriesPartialSum_insert`'s simp set might over-fire

If `simp [bseriesPartialSum, Finset.sum_insert ht]` over-rewrites or
loops, fall back to explicit `unfold bseriesPartialSum` + `exact
Finset.sum_insert ht (fun t => bseriesTerm f y₀ h t)`. The `simp`
form is shorter; `unfold` is the safe fallback.

### R4 — Section301.lean is now large (>620 LOC)

If the file's elaboration starts to drag, that's an issue for cycles
256+, not 255. Cycle 255's additions are small (~50-70 LOC) and don't
add new mathlib transitive imports.

### R5 — `Finset` over `RootedTree` might surface decidability obligations

`Finset RootedTree` requires `DecidableEq RootedTree` to construct
non-empty Finsets. If a non-empty Finset literal (`{vertex}`,
`{vertex, cherry}`) fails to elaborate, add `Classical.decEq` as a
private instance scoped to the new content (per memory
`feedback_rootedtree_nested_induction.md`-adjacent practice). Do NOT
add it at file-top scope (would affect cycle 254's content).

## G. Why this target and not something else

**Why NOT pivot to a fresh entity?** Cycles 248–254 have built a
contiguous §310/§311/§312 B-series chain (`theta_eq_one` →
`lem_311A_order_one` → `alphaWeight` → `alphaWeight_pos` → Table
310(II) saturation → `bseriesTerm`). Cycle 254 explicitly suggested
`bseriesPartialSum` as the natural next step. Pivoting now would
orphan the bseriesTerm investment.

**Why NOT attack `lem_311A_order_two` (cycle 248 P2(a))?** That's
genuinely multi-cycle work (the `iteratedFDeriv ℝ 1 ↔ fderiv` bridge
plus chain-rule extraction). The cycle 254 task results' Discovery
section identifies this as cycle 256+ scope.

**Why NOT attack a `thm:302*` enumeration formula?** Those entities
(`thm:302A`, `thm:302B`, `thm:302C`) are combinatorial generating-
function results. They need a `Fintype` instance on
`RootedTree`-of-bounded-order — i.e. the very `Fintype
(TruncatedRootedTree N)` we explicitly defer. No path to a single-
cycle deliverable there.

**Why `TruncatedRootedTree` if we can't ship `Fintype`?** Because
the *definition* and basic API are tractable; the type carries useful
structural information (`order_le`) for stating future bounded-order
theorems. `Fintype` is the hard piece that has to wait.

**Why hand-enumerated `Finset` for `bseriesPartialSum`?** Because
without `Fintype (TruncatedRootedTree N)` we have no canonical
"`Finset` of all trees with order ≤ N" — but a user-supplied `Finset`
works fine for small-order witnesses (e.g. `{vertex, cherry}` is
exactly an order-≤-2 forest). This shifts the burden from the
infrastructure to the call site, which is the correct trade-off for
a single cycle.

## H. Faithfulness assertion

This cycle introduces NO new mathematical content from Butcher.
`TruncatedRootedTree N` is a Lean engineering scaffold (Butcher does
not name it). `bseriesPartialSum` is the natural finite-Finset
version of Butcher's `(310i)` series; once we shipped `bseriesTerm`
in cycle 254, partial sums are immediate.

No new faithfulness divergences. The σ-faithfulness divergence
(Section301's stipulative recursive `symmetry` vs Butcher §300's
automorphism-group definition, issue `symmetry_group_equivalence.md`)
remains the only divergence in this lineage; cycle 255 doesn't touch
it.

## I. Cycle 256+ outlook (informational only — do NOT pre-position)

After cycle 255 ships:

1. **Cycle 256**: `lem_311A_order_two` — the order-2 Taylor expansion
   bridge for `lem:311A`. Requires the `iteratedFDeriv ℝ 1 ↔ fderiv`
   Mathlib bridge (search `lean_loogle "iteratedFDeriv _ 1"` for
   `iteratedFDeriv_one_apply` or
   `ContinuousMultilinearMap.curry0`/`curry1`) plus a small ODE-side
   helper "for `f` C¹ and `yex' = f ∘ yex`, `iteratedDeriv 2 yex x₀ =
   fderiv f y₀ (f y₀)`". Aristotle-batch-friendly. ~150-250 LOC.
2. **Cycle 257**: small-r partial `lem:310B` form — state `lem:310B`
   restricted to a hand-enumerated `Finset` on the RHS, with the LHS
   reformulated as a partial Taylor expansion via the cycle 256
   order-2 result. Builds on cycles 254 + 255 + 256.
3. **Cycle 258+**: the labelled-tree quotient (`def:300C`) work, if/
   when full `lem:310B` becomes load-bearing.

These are notes for the cycle 256 planner; cycle 255 worker should
**not** pre-position any of this.

## J. End-of-cycle checklist (verbatim)

Before commit:

- [ ] `lake env lean OpenMath/Chapter3/Section301.lean` exits 0.
- [ ] `lake env lean OpenMath/Chapter3.lean` exits 0 (regression check).
- [ ] `grep -c sorry OpenMath/Chapter3/Section301.lean` → 0.
- [ ] Tautology-scanner regex returns no matches on cycle 255 additions.
- [ ] `lean_verify` axiom-clean on every new public declaration (no
      `sorryAx`).
- [ ] `task_results/cycle_255.md` written with the standard sections
      (Worked on / Approach / Result / Faithfulness check / Dead ends /
      Discovery / Suggested next approach). Document P4's status
      (shipped or skipped) clearly.
- [ ] `plan.md` row for `lem:310B` **unchanged** (still `[ ]`,
      `unformalized` — cycle 255 ships scaffold, not closure).
- [ ] `lean_status.json` row for `lem:310B` **unchanged**.
- [ ] No `axiom` / `constant` declarations introduced.
- [ ] No `maxHeartbeats` raise.
- [ ] No edits to `scripts/autonomous_loop.py`.

## K. Bottom-line directive

Ship `TruncatedRootedTree N` subtype (P1) + `bseriesPartialSum` over
`Finset` (P2) + two non-vacuity witnesses (P3) in Section301.lean.
~50-80 LOC, axiom-clean, sorry-clean. P4 is optional stretch.

If any step blocks unexpectedly (e.g. `simp` timeout on a partial-sum
identity, `DecidableEq` snag, `Finset` literal elaboration failure),
drop to P1 only and ship the `TruncatedRootedTree` subtype alone —
even just the subtype definition + `order` accessor is enough cycle
255 progress and unblocks cycle 256+'s small-r work. The strategy's
failure mode is **always** "ship less, axiom-clean" rather than
"ship more, broken".
