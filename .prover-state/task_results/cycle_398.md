# Cycle 398 Results

## Worked on

Phase α'.4.3 scoping doc for migrating `inversePolynomial`'s `bushy`
branch from Family B's `inversePolyBroom 3 f` dispatch to a
`trichildPolynomial`-based `inversePolyTree (mk [vertex, vertex,
vertex]) f` dispatch — the last unmigrated ladder tree.

Markdown-only deliverable at
`.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
(668 lines, 10 sections). Mirrors the cycle 385
`def_422B_phase_alpha_prime_family_C_scoping.md` precedent (621 lines
+ §10/§11 cycle 386/387 update appends; drove 11-cycle ladder
386–397).

## Approach

Followed the strategy's Priority 1 deliverable spec verbatim with
adjustments to §7 R3 based on a faithfulness spot-check:

1. **Read predecessor scoping doc** (cycle 385's
   `def_422B_phase_alpha_prime_family_C_scoping.md`) for structural
   precedent — same 10-section organisation, same
   §1-status/§2-closed-form/§3-decomposition/§4-strawman pattern.
2. **Verified cycle 370's closed form** at `Section422.lean:3011`
   and the non-vacuity example at `Section422.lean:3176` (value `1`
   at `⟦explicitEuler⟧`).
3. **Verified cycle 387's `bichildPolynomial`/`inversePolyTree`
   shapes** at `Section422.lean:6283–6423` for the sign-convention
   anchor.
4. **Wrote §3 block decomposition** as a paper-derivation: the 8
   blocks for three-children product expansions, each Block (1)–(8)
   mapped to its contribution to cycle 370's closed form. Sanity
   walk-through at `(t₁, t₂, t₃) = (vertex, vertex, vertex)`
   confirms every term of cycle 370's `+v⁴ − 3v²c + 3v·b' − f bushy`.
5. **Drafted §4/§5 strawmen** for `trichildPolynomial` and
   `trichildCrossTerm`, matching cycle 387's sign convention and
   yielding `trichildCrossTerm vertex vertex vertex f = 3 · f vertex
   · f broom₃` at the all-vertex triple.
6. **Resolved the planner's §7 R3 "RED FLAG"** as a substitution
   error: the planner computed `1⁴ − 3·1²·1 + 3·1·1 − 1 = 0` by
   substituting `c = b' = Φ_η(bushy) = 1`, but at `⟦explicitEuler⟧`
   with `A = 0`, the correct values are `c = b' = Φ_η(bushy) = 0`,
   yielding `1`. This matches cycle 370's example exactly. No
   discrepancy. (See §7 R3 of the scoping doc for the full
   resolution.) Downgraded R3 from "RED FLAG" to "LOW severity,
   strawman internally consistent, cycle 399 still does symbolic
   verification before locking."
7. **§6 ship plan** for cycles 399–401 with concrete LOC budgets
   (~80–100 / ~30 / ~50) and proof recipes mechanically pulled
   from cycles 392/394/395/396/397 templates.
8. **§7 R1–R6 risk inventory** with severities, including the
   structural-recursion pattern-ordering risk (cycle 399 inserts
   `[c₁, c₂, c₃]` BEFORE the existing catch-all and bumps the
   catch-all from `(_ :: _ :: _ :: _)` to `(_ :: _ :: _ :: _ :: _)`).
9. **§8 cycle 399 entry point** with 7 pre-flight steps in order.
10. **§9/§10 cross-references** and self-reference (cycle 398 ships
    this doc; cycle 399 ships P8; cycle 400 ships P9; cycle 401
    ships P5 migration; cycle 402+ revisits cycle 365 grandfathered
    sorry under uniform `inversePolyTree` routing).

## Result

SUCCESS — scoping doc shipped at
`.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
(668 lines). `lean_status.json` `def:422B` row updated
(`cycle_completed_at: 397 → 398`; note extended with cycle 398
summary). No Lean changes; `grep -c sorry` unchanged at 5 (4
docstring + 1 grandfathered cycle 365 code at line 2279).

§422 axiom-clean streak: 60 substantive + 2 doc (336–397) →
**60 substantive + 3 doc** (cycles 336–398).

## Faithfulness check

**No new `def`, `theorem`, or `structure` introduced this cycle.**
Markdown-only ship. Scoping doc itself is documentation, not formal
content; standard faithfulness criteria do not apply.

The scoping doc does not "smuggle" content: §4/§5 explicitly label
their proposals as strawmen, §6.1 step 1 explicitly defers symbolic
verification to cycle 399, and §7 R3 explicitly resolves the
planner's claimed discrepancy by exhibiting the correct
substitution.

`lean_status.json` `def:422B` row: status remains `partial`;
`cycle_completed_at` bumped from 397 to 398; note extended with
cycle 398 summary. `lean_symbol` unchanged at
`OpenMath.Chapter4.Section422.D_element_elementaryWeight`.

## Dead ends

**Planner's §7 R3 "RED FLAG"** turned out to be a substitution
error on the planner's part, not a real discrepancy. The planner
wrote:

> Strawman value: `1⁴ - 3·1²·1 + 3·1·1 - 1 = 1 - 3 + 3 - 1 = 0`.
> ... DISCREPANCY: strawman gives 0, actual gives 1.

But at `⟦explicitEuler⟧` with `A = 0`, the substitution should be
`v = 1, c = 0, b' = 0, Φ_η(bushy) = 0`, yielding `1⁴ = 1`
(matching cycle 370 exactly). The planner accidentally substituted
all kernels to 1 instead of using the actual explicit-Euler values.
The scoping doc §7 R3 documents this resolution explicitly.

The planner's "Priority 3 Optional stretch" section also flagged
this self-correction tentatively (the "wait — `1 - 3 + 3 - 1 = 0`"
sequence in the strategy). My §7 R3 confirms the strawman is
consistent with cycle 370 and no Lean-side `example` ship is needed
this cycle for the disambiguation.

## Discovery

**The planner's R3 substitution error is a recurring failure mode**:
when reasoning about closed-form values at `⟦explicitEuler⟧`, the
default mental model substitutes "all 1's" rather than "`A = 0`
forces all cross-tree kernels to 0." For cycle 399's worker:
**always substitute the actual explicit-Euler tableau values**
(`v = Σ b = 1, A = 0, c = b' = bushy = 0` due to `A = 0`'s
propagation through `derivativeWeight`'s recursive product).

**The strawman §5 cross-term value `3 · f vertex · f broom₃`** can
be paper-verified directly from the §3 block decomposition (no
symbolic Lean derivation needed) by noticing that Blocks (5)/(6)/(7)
at `(v, v, v)` each contribute `Σᵢ bᵢ · 1 · (Σⱼ Aᵢⱼ)² · 1 =
Φ_η(broom₃) = b'` (the inner `1` factors come from
`derivativeWeight j vertex = 1`; the outer `−Σᵢ bᵢ · …` prefactor
cancels with the inv₃ = -v factor). Three blocks × `b'` × `(−1) ·
(−v) = +v·b'` each → `+3v·b'` total. This calculation is what
cycle 399 should verify in Lean to lock the trichild infrastructure.

**Cycle 399's `inversePolyTree` pattern bump risk** (§7 R1) is the
only non-trivial structural risk for the multi-cycle plan. The
current `(_ :: _ :: _ :: _) → 0` catch-all must be bumped to
`(_ :: _ :: _ :: _ :: _)` simultaneously with the
`[c₁, c₂, c₃] → trichildPolynomial ...` insertion. Lean's
exhaustivity checker will catch any mistake here — running `lake
env lean OpenMath/Chapter4/Section422.lean` after the change is
the cheapest verification.

## Suggested next approach

**Cycle 399 (Phase α'.4.1 P8) — trichild infrastructure.** Per the
scoping doc §8 entry point, in order:

1. Re-read cycle 387's `bichildPolynomial` at `Section422.lean:6383`
   for the two-children precedent.
2. Re-read cycle 358's `_inv_mk` at `Section422.lean:582` for the
   per-row product mechanism.
3. Symbolically compute the three-children block decomposition at
   `(vertex, vertex, vertex)` per scoping doc §3 — confirm Blocks
   (5)/(6)/(7) each contribute `+v·b'` and Block (8) contributes
   `−Φ_η(bushy)`.
4. Lock the §5 `trichildCrossTerm vertex vertex vertex f = 3 · f
   vertex · f broom₃` value.
5. Ship `trichildPolynomial` (§4 strawman), `trichildCrossTerm` (§5
   strawman), and extend `inversePolyTree`'s match (insert
   `[c₁, c₂, c₃] → trichildPolynomial ...` BEFORE the catch-all;
   bump catch-all to `(_ :: _ :: _ :: _ :: _)`).
6. Verify all 11 existing `inversePolyTree_*` calibrations still
   pass via `lake env lean`.
7. Optional non-vacuity `example` at
   `f = elementaryWeightQ_phi ⟦explicitEuler⟧` confirming bushy
   evaluates to `1`.

LOC budget: ~80–100. Risk: low-medium.

**Cycle 400 (Phase α'.4.1 P9) — `inversePolyTree_bushy`**
calibration witness (~30 LOC).

**Cycle 401 (Phase α'.4.2 P5) — `bushy` migration**: bridge ship +
`inversePolynomial` body rewrite + Phase α.2 / β.4 / γ retrofits +
Step F derivative fix on cycle 382's
`inversePolyBroom_three_eq_inversePolynomial` (~50 LOC).

**Cycle 402+**: with all 9 ladder trees routing uniformly through
`inversePolyTree`, revisit cycle 365's grandfathered Sub-lemma A
sorry at `Section422.lean:2279`. The cycle 366 heterogeneous-stage
obstacle may yield to the unified recursive structure composed with
cycle 362's
`derivativeWeightWithSrc_eq_of_strict_subtree_agreement`.

**Optional cycle 400+ refactor**: collapse `inversePolynomial`'s
9-branch `if-then-else` cascade to a single `inversePolyTree t f`
call. Cycle 400+ refactor work, post-bushy migration.
