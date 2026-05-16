# Cycle 327 Strategy — §344 Phase D.7: Lobatto IIIB `s = 3` direct-form `RKTableau`

## §A One-line summary

Ship `butcherLobattoIIIBDirect_three : RKTableau 3` direct-form, plus a
`SatisfiesB 4` non-vacuity example, per cycle 326 task results
recommendation. Mechanical port of cycle 326's direct-form pattern
to Butcher Table 344(III) p. 245 Lobatto IIIB s=3 printed values.

## §B Why this target

* **Recommended by cycle 326 task results** Option 1 (LOW complexity).
* **Single-cycle scope**: ~50–80 LOC, no new infrastructure, no
  multi-cycle prerequisites.
* **Continues §344 §D ladder** without taking on multi-cycle reflection
  debt (the cycle 326 "reflections of Radau II" investigation remains
  deferred, see `.prover-state/issues/radau_ia_collocation_divergence.md`).
* **Smallest available `s` for Lobatto IIIB**: per Butcher line 5263
  (`extraction/raw_text/ch03.txt`), Lobatto IIIB s=2 does **not exist**,
  so s=3 is the natural entry.
* **Reflection partner of Lobatto IIIA s=3** (cycle 323 shipped
  Lobatto IIIA s=2 as trapezoidal rule; Lobatto IIIA s=3 = Simpson's
  rule is multi-cycle scope per cycle 325 task results).
* **Order p = 4** at s=3 means `SatisfiesB 4` is the natural non-vacuity
  example.

## §C Pre-flight: textbook values (already verified by strategy author)

Read from `extraction/raw_text/ch03.txt:5426-5434`:

```
Lobatto IIIB   (s = 3, p = 4),
                              0         1/6      -1/6           0
                              1/2       1/6       1/3           0
                              1         1/6       5/6           0
                                        1/6       2/3           1/6
```

Translates to:

* `c = ![0, 1/2, 1]`
* `A = !![1/6, -(1/6), 0; 1/6, 1/3, 0; 1/6, 5/6, 0]`
* `b = ![1/6, 2/3, 1/6]`

Note: `b` and `c` are identical to Lobatto IIIA's at s=3 (Simpson's
quadrature points and weights — both families share the same
quadrature choice per Butcher Table 344(I), but differ on A-matrix
construction: IIIA uses C(s) = plain collocation; IIIB uses D(s)).

## §D Faithfulness audit (per cycle 326 protocol)

The cycle 326 faithfulness audit pattern is **load-bearing**: ALWAYS
verify printed Butcher values before writing Lean. For this cycle
the audit has already happened in §C above — values copied verbatim
from `extraction/raw_text/ch03.txt:5426-5434`. **The strategy author
has verified them; the worker need not re-audit unless suspicious.**

The name `butcherLobattoIIIBDirect_three` makes the construction
provenance explicit: we declare the table values directly, with no
claim that they come from a specific abstract construction
(consistent with the cycle 326 `butcherRadauIADirect_two` naming
convention).

## §E Concrete deliverables

### E.1 (P1, REQUIRED) `butcherLobattoIIIBDirect_three : RKTableau 3`

Inline in `OpenMath/Chapter3/Section344.lean` after cycle 326's
`butcherRadauIADirect_two` (around line ~1745–1760 of HEAD).
Pattern verbatim from cycle 326:

```lean
/-- The Lobatto IIIB `s = 3` Runge–Kutta tableau in its direct form
(Butcher Table 344(III) p. 245). The classical order is
`p = 2s − 2 = 4`. The `b` and `c` agree with Lobatto IIIA `s = 3`
(both come from Lobatto quadrature at `(0, 1/2, 1)` with weights
`(1/6, 2/3, 1/6)`); the `A`-matrix differs (IIIA uses C(s) plain
collocation; IIIB uses D(s)).

Per Butcher Table 344(I) p. 224, Lobatto IIIB at `s = 2` does not
exist (line 5263 in `extraction/raw_text/ch03.txt`), so `s = 3`
is the smallest available stage count. -/
noncomputable def butcherLobattoIIIBDirect_three : RKTableau 3 where
  A := !![1/6, -(1/6), 0; 1/6, 1/3, 0; 1/6, 5/6, 0]
  b := ![1/6, 2/3, 1/6]
  c := ![0, 1/2, 1]
```

### E.2 (P1, REQUIRED) `SatisfiesB 4` non-vacuity example

Lobatto IIIB at s=3 has classical order `p = 2s − 2 = 4`, so the
maximal `B(η)` quadrature order is `η = p = 4`. The example
should prove:

```
∀ k, 1 ≤ k → k ≤ 4 → ∑ⱼ bⱼ · cⱼ^{k-1} = 1/k
```

at the four arms (verified by hand):
* k=1: `1/6 + 2/3 + 1/6 = 1 = 1/1` ✓
* k=2: `(1/6)·0 + (2/3)·(1/2) + (1/6)·1 = 1/3 + 1/6 = 1/2` ✓
* k=3: `0 + (2/3)·(1/4) + (1/6)·1 = 1/6 + 1/6 = 1/3` ✓
* k=4: `0 + (2/3)·(1/8) + (1/6)·1 = 1/12 + 1/6 = 1/4` ✓

All four arms close cleanly with `norm_num`. Recipe (mirrors cycle
326's pattern):

```lean
example : butcherLobattoIIIBDirect_three.SatisfiesB 4 := by
  intro k h1 hk
  interval_cases k <;>
    simp [RKTableau.SatisfiesB, butcherLobattoIIIBDirect_three,
          Fin.sum_univ_three] <;>
    norm_num
```

If `interval_cases k` doesn't fire cleanly, fallback to explicit
match: `match k, h1, hk with | 1, _, _ => ... | 2, _, _ => ... |
3, _, _ => ... | 4, _, _ => ...`. Or use cycle 326's exact pattern
(check the `butcherRadauIADirect_two` `SatisfiesB 3` example at
`Section344.lean` ~line 1745+ for the precise tactic incantation
that the linker accepts here).

## §F Risks and pre-flagged pitfalls

### R1 (low) — Negative literal `-(1/6)` in matrix entry

The `!![...]` matrix-row literal should accept `-(1/6)` as a
ℝ-literal, but Lean's elaborator may complain about expected
positive numerals. Workaround if it does:
* Write `-1/6` (without parens) — may parse differently.
* Or write `(-1 : ℝ)/6` with explicit type ascription.
* Or pull it out as a local: `let n1_6 : ℝ := -1/6` before the
  matrix definition.
* Or refactor entire matrix to `Matrix.of (fun i j => ...)` style
  with explicit per-entry case analysis.

Cycle 324's Radau IIA used `-(1/12)` in **theorem statements**
without trouble, so this is well-trodden territory at the entry
level — the worry is specifically inside `!![...]` literal syntax.
Try `-(1/6)` first; if it fails, switch to `Matrix.of` form.

### R2 (low) — `Fin.sum_univ_three` arity

Cycle 323 used `Fin.sum_univ_two` for Lobatto IIIA s=2's
`SatisfiesB 2` non-vacuity. The s=3 analog `Fin.sum_univ_three`
exists in `Mathlib/Algebra/BigOperators/Fin.lean` with the same
signature. If `simp` doesn't fire, fall back to explicit
`Fin.sum_univ_succ` × 3 unfolding (verified to exist in cycles
322/323/324/325).

### R3 (low) — `noncomputable` annotation

Cycle 326's `butcherRadauIADirect_two` is `noncomputable def`
(check the file). Numeric literals in `RKTableau ℝ` fields are
computable in principle, but the `RKTableau` constructor may
require it. Default: write `noncomputable def` to match cycle 326.
If Lean complains "noncomputable not needed", drop it.

### R4 (very low) — `axiom-clean` regression

Verify with
`#print axioms butcherLobattoIIIBDirect_three` after the build.
Expected: `[propext, Classical.choice, Quot.sound]`.

### R5 (very low) — `interval_cases k` may need explicit bounds

If `interval_cases k` complains, supply explicit bounds via
`interval_cases (h1 : 1 ≤ k) (hk : k ≤ 4)` or destructure the
hypotheses first. Cycle 326's `SatisfiesB 3` example used the
same `interval_cases` pattern; check its exact form before
deviating.

## §G What NOT to do

* **Do NOT attempt plain Lagrange collocation for Lobatto IIIB.**
  Per Butcher Table 344(I), Lobatto IIIB uses D(s), NOT C(s).
  Computing `∫_0^{c_i} L_j(x) dx` over Lobatto abscissae will
  produce values that **differ from Butcher's printed table**
  (same kind of audit failure as cycle 326's Radau IA collocation
  divergence). Just declare the printed values inline.

* **Do NOT attempt to derive Lobatto IIIB from a §343 reflection
  of Lobatto IIIA s=3.** This is the multi-cycle "reflections"
  investigation (Option 2 in cycle 326 task results) — deferred.

* **Do NOT extend the Radau IA collocation/reflection investigation
  in this cycle.** Per `.prover-state/issues/radau_ia_collocation_divergence.md`,
  this is multi-cycle scope.

* **Do NOT attempt Phase B.2 polynomial exactness** (the `thm:344A`
  `2s − 2`/`2s − 3` headline). Multi-cycle, blocked on `thm:314A`.

* **Do NOT attempt Lobatto IIIA s=3 (Simpson's rule).** Per cycle
  325 task results, multi-cycle. The substantive Simpson's-rule
  collocation construction needs more infrastructure than fits
  in one cycle.

* **Do NOT attempt to compile `OpenMath/Chapter4/Section441.lean`.**
  43+ consecutive GPFS timeouts since cycle 182. Skip per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.

* **Do NOT raise `maxHeartbeats`** above 200000.

* **Do NOT introduce `axiom`/`constant`.** Strict axiom-clean target.

* **Do NOT introduce `sorry`.** Strict axiom-clean target.

* **Do NOT modify `scripts/autonomous_loop.py`.** Loop-maintainer
  territory.

* **Do NOT cherry-pick a different "easier" §344 target.** The
  cycle 326 task results explicitly named Lobatto IIIB s=3 as
  the recommended cycle 327 target. Stick to it.

## §H Pre-commit faithfulness checklist

Before committing:

1. **For the new `def butcherLobattoIIIBDirect_three`**: confirm
   `(A, b, c)` match `extraction/raw_text/ch03.txt:5426-5434`
   verbatim. The strategy author has verified above; the worker
   should still spot-check.

2. **For the `SatisfiesB 4` example**: confirm the four arms
   evaluate as computed in §E.2.

3. **Tautology / smuggling sweep**:
   - No `:= h_*` / `exact h_*` / `:= id` proofs in the new
     additions.
   - No new `theorem` re-exports a hypothesis as a conclusion.
   - The `RKTableau` structure has no `Prop` fields, so the
     "Prop field should be consequence" smuggling pattern does
     not apply.

4. **Axiom-clean spot-check**:
   ```
   echo '#print axioms OpenMath.Chapter3.Section344.butcherLobattoIIIBDirect_three' \
     | lake env lean --stdin OpenMath/Chapter3/Section344.lean
   ```
   Expected: `[propext, Classical.choice, Quot.sound]`.

5. **Aggregator build**: `lake env lean OpenMath/Chapter3.lean` exit 0.

6. **Sorry count unchanged**: `grep -c sorry OpenMath/Chapter3/Section344.lean` → 0.

## §I Step-by-step worker instructions

1. **Read** `extraction/raw_text/ch03.txt:5426-5434` and confirm
   Lobatto IIIB s=3 values match §C above. (Sanity check; values
   already pre-verified.)

2. **Open** `OpenMath/Chapter3/Section344.lean`. Locate cycle 326's
   `butcherRadauIADirect_two` (around line 1711–1745). Confirm the
   exact tactic pattern of cycle 326's `SatisfiesB 3` example so
   you can mirror it.

3. **Insert** the `butcherLobattoIIIBDirect_three : RKTableau 3` def
   per §E.1 immediately after cycle 326's `butcherRadauIADirect_two`
   block.

4. **Insert** the `SatisfiesB 4` example per §E.2 immediately after
   the definition.

5. **Compile** with `lake env lean OpenMath/Chapter3/Section344.lean`
   to confirm clean build.

6. **Verify axiom-clean** per §H.4.

7. **Run aggregator** per §H.5.

8. **Update** `extraction/formalization_data/lean_status.json`: this
   is an *instance* of `thm:344A` (not a per-instance entity), so
   no row update is strictly required, but if the `thm:344A` row
   has a cycle-326 note, append a cycle-327 line documenting this
   ship.

9. **Update** `plan.md`'s `thm:344A` row entry to note cycle 327's
   ship in the partial-status paragraph (same pattern as cycle 326).

10. **Write** `.prover-state/task_results/cycle_327.md` per the
    CLAUDE.md template.

11. **Commit** with message
    `"Cycle 327 — §344 Phase D.7: Lobatto IIIB s = 3 direct-form RKTableau."`
    and push.

## §J LOC budget and abort threshold

* **Target**: ~50 LOC (matches cycle 326's `+49 LOC` ship).
* **Soft ceiling**: 100 LOC. If past 80 LOC and not done, STOP and
  ask whether you've drifted from the strategy.
* **Hard abort**: 200 LOC. The cycle 326 deliverable shows this
  pattern is fundamentally a ~50-LOC drop-in; if past 200 LOC
  something is wrong (likely you've started trying to derive the
  A-matrix from collocation or reflection, which §G forbids).

* **Time budget**: ≤60 minutes. The cycle 326 ship is the closest
  precedent.

## §K Failed approaches (DO NOT REPEAT)

From `attempts.md` and prior cycle task results, these are
known-failed paths in adjacent territory — do not retry:

* **Plain collocation for "reflection" tableau families** (cycle 326):
  computing `A_{ij} = ∫_0^{c_i} L_j(x) dx` for Radau IA at s=2
  produced row 0 = `(0, 0)` and row 1 = `(1/3, 1/3)` instead of
  Butcher's `(1/4, -1/4)` and `(1/4, 5/12)`. Same kind of
  divergence applies to Lobatto IIIB (uses D(s), not C(s)).

* **§343 bare `RKTableau.reflection` for "reflection" families**
  (cycle 326): computing `(butcherRadauIIA s=2).reflection` gave
  `Â = !![5/12, 1/4; 5/12, 1/4]` after permutation, NOT Butcher's
  `!![1/4, -1/4; 1/4, 5/12]`. Butcher's "reflections of X" is a
  refined construction beyond §343. Not in scope for this cycle.

* **`Polynomial.ext` + `simp` + `ring` for `Polynomial ℝ` constant
  arithmetic** (cycles 172/173 from §441 work): does not handle
  `C(rational)` arithmetic. Use `Polynomial.funext + ring` if
  needed (cycle 180 recipe). Not relevant to this cycle's direct-
  form ship.

* **Sorry-first scaffolds for multi-cycle targets** (cycles 138/139,
  149/150, 200/201): all rolled back with `score = -2` for sorry
  count regression. Do not introduce sorries.

## §L Follow-up scope for cycle 328+

After cycle 327, the §344 small-`s` ladder will have:

* Radau IIA: s=1 (cycle 322), s=2 (cycle 324)
* Radau IA: s=1 (cycle 325), s=2 direct-form (cycle 326)
* Lobatto IIIA: s=2 (cycle 323)
* Lobatto IIIB: s=3 direct-form (this cycle)

Natural cycle 328 candidates (in order of expected LOC):

* **Radau II s=2 direct form** (Butcher Table 344(II), the D(s)
  choice — distinct from cycle 324's Radau **IIA** which uses
  reflection of Radau I). ~50 LOC direct.
* **Radau I s=2 direct form** (matches plain collocation per the
  cycle 326 audit math; would also be expressible via the cycle
  326 collocation template if a §343-style reflection isn't
  needed). ~50 LOC direct.
* **Lobatto IIIC s=2 direct form** if it exists (Butcher Table
  344(IV) p. 246; per Table 344(I) line 5224, Lobatto IIIC =
  "reflections of Lobatto III" — needs textbook value
  verification first).
* **Lobatto III s=2** (the unsuffixed family, "C(s-1) +
  $a_{1s} = \cdots = a_{ss} = 0$" choice; Table 344(I) line 5221).

The planner for cycle 328 should pick one of these — direct-form
ships are mechanical at this point and the ladder fills out
nicely. The "reflections of X" investigation (cycle 326's
deferred Option 2) remains multi-cycle scope.

## §M Why this is the right cycle 327 target

1. **Cycle 326 task results explicitly recommended it** (Option 1).
2. **Smallest available `s` for a fresh §344 entry** — Lobatto IIIB
   s=2 doesn't exist, so s=3 is the natural target.
3. **Single-cycle scope** with high confidence (matches cycle 326
   shape almost exactly).
4. **No new multi-cycle debt** — explicitly chooses the LOW-
   complexity path from cycle 326's options menu.
5. **Closes a meaningful gap** in the §344 small-`s` coverage matrix
   (Lobatto IIIB family was entirely empty before this).
6. **Pattern is well-tested** — cycle 326 just shipped exactly this
   shape successfully.

Proceed.
