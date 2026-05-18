# Cycle 380 strategy — Phase α'.1: recursive `inversePolynomial` definition

## Context (read first)

Cycle 379 shipped the Phase α' scoping doc at
`.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` (903 lines,
11 sections). The scoping doc is comprehensive and concrete — it
contains the cycle 380 entry point (§10), three candidate recursive
variants (§5), the closed-form catalog (§3), the gap inventory (§7),
the 4-phase decomposition (§8), and the risk register (§9). **Read
§10, §5, §3, §4, §6, and §7 carefully before any Lean work.**

§422 axiom-clean streak: **43 substantive + 2 doc** (cycles 336–379).
Single grandfathered sorry at `OpenMath/Chapter4/Section422.lean:2279`
(cycle 365's `powRep_sum_eq_of_strict_subtree_agreement` general body).
Section422.lean: 5595 LOC. `grep -c sorry` returns 5 (4 docstring + 1
code).

## Priority 1 — DELIVERABLE: Phase α'.1 recursive `inversePolynomial` (V2 attempt; V1 fallback)

Per scoping doc §8 (Phase α'.1) and §10 (cycle 380 entry point),
ship a recursive definition of `inversePolynomial` that replaces
(or extends) the 8-way `if-then-else` pattern match at
`OpenMath/Chapter4/Section422.lean:4651–4697`. Target: **Variant V2
(fold-over-children, mirror of cycle 358's `_inv_mk` expansion)**
per scoping doc §5.

### Sub-task 1.1 — Preliminaries (do BEFORE writing Lean)

Read in order:

1. **Cycle 358's `elementaryWeightQ_phi_inv_mk` proof body** at
   `OpenMath/Chapter4/Section422.lean:582–630` (the structural seed —
   the recursive `inversePolynomial` must mirror this unfolding).

2. **Cycle 343's `WellFoundedRelation`** at
   `OpenMath/Chapter3/Section301.lean:177` plus
   `order_lt_of_mem_children` at line 167. These are the termination
   witnesses.

3. **The 8 closed-form proofs** at line numbers from scoping doc §6:
   `_vertex` (415), `_cherry` (2376), `_broom₃` (2538), `_mkCherry`
   (2772), `_bushy` (3011), `_mkBroom₃` (3397), `_mkVertexCherry`
   (3798), `_mkMkCherry` (4226). Read each proof body — the per-row
   `(Aᵢ − v)^k` factorisation patterns (Discovery noted in cycle
   368/370) are the seed for the V2 per-child contribution formula.

4. **Memory `feedback_rootedtree_nested_induction.md`**: `induction t`
   / `RootedTree.recOn` fail on nested inductives. Use mutual
   recursion or well-founded recursion via cycle 343's instance.

### Sub-task 1.2 — Derive Family A and Family B closed-form recipes precisely

Per scoping doc §4 and §7 (gap G1 CRITICAL):

**Family A** (single-child ladder, depths 0–3 in current ladder):
* `c_0 = vertex ↦ −c_0` (cycle 341)
* `c_1 = cherry ↦ c_0² − c_1` (cycle 367)
* `c_2 = mk[cherry] ↦ −c_0³ + 2c_0c_1 − c_2` (cycle 369)
* `c_3 = mk[mk[cherry]] ↦ c_0⁴ − 3c_0²c_1 + c_1² + 2c_0c_2 − c_3`
  (cycle 378)

**Family B** (symmetric leaf brooms `mk [vertex^k]`):
* k=1 cherry: `v² − c`
* k=2 broom₃: `−v³ + 2vc − b'`
* k=3 bushy: `v⁴ − 3v²c + 3vb' − B`

The scoping doc §4 attempted a binomial sum recipe but encountered
sign-convention errors mid-derivation. **You must re-derive Family
B precisely from cycle 358's `_inv_mk` formula + the per-row
`(Aᵢ − v)^k` factorisation from cycle 368/370.** The correct recipe
involves expanding `(Aᵢ − v)^k = Σⱼ (k choose j) · Aᵢ^(k−j) · (−v)^j`
per row and summing against `M.b` weights.

Pin the exact formula symbolically (on paper or in a comment block
inside Section422.lean) **before** committing to a Lean definition.

### Sub-task 1.3 — Sketch and verify Variant V2

The strawman from scoping doc §5:

```lean
noncomputable def inversePolynomial : RootedTree → (RootedTree → ℝ) → ℝ
  | RootedTree.mk children => fun f =>
      let v := f RootedTree.vertex
      let recursivePart :=
        children.foldr (fun c acc =>
          acc * (v * <something involving f at c's children>
                  + inversePolynomial c f)) 1
      recursivePart - f (mk children)
  termination_by t => t.order
  decreasing_by exact RootedTree.order_lt_of_mem_children ‹_›
```

The per-child contribution formula is a guess. **Derive the precise
formula from cycle 358's `_inv_mk` unfolding before committing.**

### Sub-task 1.4 — Calibration witnesses BEFORE committing the definition

After drafting `inversePolynomial`, verify on **all 8 ladder trees**
via `unfold + rfl` or `unfold + ring`. Pattern:

```lean
example (f : RT → ℝ) :
    inversePolynomial RootedTree.vertex f = -(f RootedTree.vertex) := by
  unfold inversePolynomial
  ring  -- or rfl if V2 matches definitionally

example (f : RT → ℝ) :
    inversePolynomial RootedTree.cherry f
      = (f RootedTree.vertex)^2 - f RootedTree.cherry := by
  unfold inversePolynomial
  ring
```

— and analogously for `broom₃`, `mk[cherry]`, `bushy`, `mk[broom₃]`,
`mk[vertex, cherry]`, `mk[mk[cherry]]`.

If **any** of the 8 calibration witnesses fails, the recursive shape
is wrong. Iterate on the per-child contribution formula. Do NOT
commit a recursive definition that fails any calibration witness.

### Sub-task 1.5 — Graceful degradation if V2 fails on Family C

Per scoping doc §9 risk R6 and §10 fallback: if V2 cannot match the
Family C closed forms (`mk [broom₃]` with `+2vm`, `mk [vertex,
cherry]` with `+c²` and `+vm`), fall back to a **partial V1**:

* Keep the cycle 374/377/378 explicit `if-then-else` matching for
  Family C trees (`mk [broom₃]`, `mk [vertex, cherry]`).
* Replace only Family A (single-child ladder) and Family B
  (symmetric leaf brooms) branches with the recursive shape.
* Cycle 380 ships this hybrid; cycle 381+ extends Family C.

The hybrid approach preserves all 8 calibration witnesses and the
cycle 365 sorry remains gated on Phase α'.4 (cycle 384+), unaffected.

**Worst-case fallback**: if V2 fails on Family B as well (binomial
sign-convention errors persist), ship a strictly conservative
partial V1 covering only Family A (4 trees: vertex, cherry,
mk[cherry], mk[mk[cherry]]) with the other 4 trees remaining as
explicit `if-then-else` branches. This is a documented Phase α'.1
partial close per the cycle 379 worker's "Suggested next approach"
Option A fallback.

## Priority 2 — DO NOT TOUCH this cycle

* **Phase β bridges migration** (8 bridges at `Section422.lean:4953–
  5200`). Cycle 381+ deliverable. Verification under V2 is a
  mechanical `unfold + rfl` (or `+ ring`) check, but the cycle 378
  worker's discovery hint should be verified separately.
* **Phase γ migration** (`inversePolynomial_eq_of_subtree_agreement`
  at `Section422.lean:5260`). Phase α'.3 work (cycle 383 target).
* **Cycle 365 grandfathered sorry** at `Section422.lean:2279`. Phase
  α'.4 scope (cycle 384+). Sorry count must stay at 5 (1 code + 4
  docstring) this cycle.

## Explicit DO-NOT list

* **Do NOT** attempt the cycle 365 grandfathered sorry in cycle 380.
* **Do NOT** ship a recursive `inversePolynomial` that fails any of
  the 8 calibration witnesses. Falling back to partial V1 is the
  correct graceful degradation.
* **Do NOT** modify the 8 existing per-tree closed-form theorems
  (`elementaryWeightQ_phi_inv_*`) — they are axiom-clean cycle
  341/367–372/378 ships.
* **Do NOT** modify the 8 m=0 corollaries
  (`powRep_sum_eq_of_agreement_at_*_zero`) — same axiom-clean status.
* **Do NOT** modify the 8 Phase β bridges
  (`elementaryWeightQ_phi_inv_eq_inversePolynomial_*`) or the Phase
  γ theorem (`inversePolynomial_eq_of_subtree_agreement`) this cycle.
  Migration is Phase α'.2 / Phase α'.3 work.
* **Do NOT** attempt Variant V3 (strong-induction explicit formula
  with `subtreeMultiset` enumerator). Scoping doc §5 V3 is gap G3
  MEDIUM — deferred unless V2 fails outright AND V1 fallback proves
  inadequate.
* **Do NOT** add a 9th tree to the ladder (e.g. `mk [mk [mk
  [cherry]]]`). Scoping doc §10 flags this as "Alternative entry
  point" (Option B), but the cycle 379 worker recommended Option A
  (Phase α'.1 implementation). Only pivot to a 9th tree if Phase
  α'.1 design proves intractable within one cycle (e.g. Family B
  derivation cannot be pinned).
* **Do NOT** raise `maxHeartbeats` above 200000. If the recursive
  definition or calibration witnesses hit elaboration timeouts,
  decompose the per-child contribution into smaller named helpers.
* **Do NOT** introduce new `axiom`/`constant` declarations.
* **Do NOT** introduce new `sorry`s. Sorry count must stay at 5.
  Graceful degradation = ship a partial V1 (axiom-clean), not a
  V2 with a sorry'd body.
* **Do NOT** edit `extraction/raw_text/`,
  `extraction/formalization_data/entities/`, or
  `scripts/autonomous_loop.py`.

## Aristotle delegation

**Defer Aristotle for cycle 380.** Phase α'.1 is fundamentally a
**design** task (deriving the right recursive shape from empirical
closed forms), not a search task. Aristotle's free compute is better
reserved for cycle 384+ Phase α'.4 (the cycle 365 grandfathered
sorry closure) once the recursive `inversePolynomial` and Phase γ
migration are in place.

If cycle 380's V2 design proves intractable mid-cycle (specifically:
if the Family B binomial recipe G1 cannot be pinned in ~30 minutes
of paper derivation), the cycle 380 worker may submit Variant V3's
combinatorial enumerator design to Aristotle as a stretch goal —
but the cycle 380 main deliverable should be the V2 attempt + V1
fallback, not Aristotle results.

## Faithfulness check

Phase α'.1's recursive `inversePolynomial` is **not** a textbook
entity — it is Lean infrastructure for the eventual `def:422B`
closure. No `lean_status.json` row update for this cycle.

The 8 calibration witnesses (Sub-task 1.4) are the faithfulness
checks: they confirm the recursive shape matches the cycle 341/367–
372/378 closed-form theorems, which are themselves derived from
Butcher §381's `Φ_{η_q⁻¹}(t)` semantics via cycle 358's `_inv_mk`.
If any calibration witness fails, the recursive shape diverges from
the textbook content.

**Discovery slot**: the cycle 373 scoping doc §4.5 noted that σ(t)
does NOT appear in any of the 8 closed-form coefficients. This must
remain true under V2: the per-child contribution formula must depend
only on `f : RootedTree → ℝ` evaluations at subtrees, not on σ or
γ. If V2's draft includes a σ or γ reference, it is wrong.

## Verification commands (cycle 380 worker MUST run before shipping)

```bash
# 1. Section422.lean still builds.
lake env lean OpenMath/Chapter4/Section422.lean

# 2. Sorry count unchanged at 5 (4 docstring + 1 code).
grep -c sorry OpenMath/Chapter4/Section422.lean

# 3. Tautology scanner clean.
rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter4/Section422.lean

# 4. Aggregator builds.
lake env lean OpenMath/Chapter4.lean
```

After build refreshes oleans, verify axiom cleanliness on a scratch
file (do NOT commit the scratch file):

```text
import OpenMath.Chapter4.Section422
#print axioms OpenMath.Chapter4.Section422.inversePolynomial
-- Expected: [propext, Classical.choice, Quot.sound] only.
```

## Cycle 380 deliverable bar

**Minimum acceptable**:
* Partial V1 (Family A only — vertex, cherry, mk[cherry],
  mk[mk[cherry]]) recursive `inversePolynomial`, with Family B and
  Family C remaining as explicit `if-then-else` branches.
* All 8 calibration witnesses pass.
* Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
* Sorry count unchanged at 5 (1 code sorry, grandfathered cycle 365).
* `Section422.lean` builds clean, aggregator builds clean.

**Target**:
* Full V2 recursive `inversePolynomial` covering all 8 ladder trees
  via fold-over-children with a precise per-child contribution
  formula derived from cycle 358's `_inv_mk`.
* All 8 calibration witnesses pass by `unfold + rfl` or `unfold +
  ring`.
* Axiom-clean.

**Stretch**:
* V2 ships AND `inversePolynomial` evaluates correctly on a 9th tree
  (e.g. `mk [mk [mk [cherry]]]` per scoping doc §10 "Alternative
  entry point") — this would be empirical evidence that the recursive
  shape extrapolates correctly to trees outside the ladder, the
  load-bearing property for cycle 384's Phase α'.4 sorry closure.

## Estimated LOC budget

* Recursive `inversePolynomial` definition: ~30–60 LOC (V2) or
  ~80–120 LOC (partial V1 hybrid).
* 8 calibration witnesses: ~80 LOC (~10 LOC per witness).
* Optional 9th-tree stretch verification: ~20 LOC.
* Total: ~130–220 LOC delta in `Section422.lean`.

Cycle 374 (Phase α.1 with 4 pattern-matched trees) was ~75 LOC.
Cycle 377 (Phase α.2 extending to 7 trees) added ~50 LOC of
pattern-match plus ~165 LOC of Phase γ extension. Cycle 380's
recursive replacement should net **−~100 LOC to +~50 LOC** relative
to the current cycle 378 state (eliminating the 8-way `if-then-else`
in exchange for a compact recursive `def`).

## Cycle 380 entry point checklist

Before touching Lean:

- [ ] Read scoping doc `def_422B_phase_alpha_prime_scoping.md` §1, §3,
      §4, §5 V2, §6, §7, §10.
- [ ] Read `Section422.lean:582–630` (cycle 358 `_inv_mk`).
- [ ] Read `Section301.lean:159–177` (cycle 343 termination).
- [ ] Read cycle 368's `elementaryWeightQ_phi_inv_broom₃` proof body at
      `Section422.lean:2538` (the `(Aᵢ − v)^k` factorisation
      pattern).
- [ ] Read `feedback_rootedtree_nested_induction.md` (memory).

Then design (on paper or in a comment block inside Section422.lean):

- [ ] Derive Family A closed-form recipe symbolically.
- [ ] Derive Family B closed-form recipe symbolically (binomial sum
      with correct signs).
- [ ] Sketch V2 per-child contribution formula.

Then implement:

- [ ] Write `inversePolynomial` recursive definition with
      `termination_by t => t.order`.
- [ ] Write 8 calibration `example`s.
- [ ] Verify each calibration witness closes via `unfold + ring` (or
      partial V1 fallback if V2 fails on Family C).

Then verify:

- [ ] `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.
- [ ] Sorry count = 5 (unchanged).
- [ ] `#print axioms` returns `[propext, Classical.choice, Quot.sound]`.
- [ ] Aggregator builds.

Then write task results.

## Risk summary (per scoping doc §9)

* **R1 HIGH** — V2 recursive shape may not match all 8 closed forms
  by `rfl` or `unfold + ring`. **Mitigation**: design the shape to
  mirror cycle 358's `_inv_mk` unfold structure; verify via
  calibration witnesses BEFORE shipping. Fall back to partial V1 if
  V2 fails.
* **R6 MEDIUM** — Family C cross-term recipe (G2) may require new
  combinatorial machinery. **Mitigation**: cycle 380's worst-case
  fallback is the hybrid (Family A recursive + Family B/C
  pattern-match). The hybrid still net-improves over the cycle 378
  state (Family A recursion replaces 4 pattern-match cases).

Per the cycle 379 scoping doc §9 R5 (multi-cycle streak burnout):
`def:422B` has now absorbed 44 consecutive cycles (336–379). The
cycle 380 worker is *expected* to deliver Phase α'.1 partial-or-full
this cycle; cycle 381 will re-scope if cycle 380 ships only Family
A. **Do not over-extend.** Ship the minimum acceptable deliverable
cleanly rather than stretching toward V2 if Family B derivation
takes more than 45 minutes of paper work.
