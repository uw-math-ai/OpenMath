# Cycle 400 strategy

## §0 Pre-flight verification (do this FIRST, <2 min)

The cycle 399 supervisor verdict was `score=0` claiming "git diff
shows only 3 prover-state files changed with no modifications to
OpenMath/Chapter4/Section422.lean". **This is the documented
phantom-commit-verdict pattern** (10th occurrence; see
`.prover-state/issues/phantom_commit_verdict_pattern.md`). Cycle
399's substantive ship IS at HEAD. Verify before proceeding:

```bash
git log --oneline -1
# Expected: bcb2b92 Cycle 399 — §422 Phase α'.4.1 P8 trichild infrastructure ship.

git show --stat bcb2b92 -- OpenMath/Chapter4/Section422.lean
# Expected: non-empty diffstat (+63 LOC)

grep -n "^noncomputable def trichildCrossTerm\|^noncomputable def trichildPolynomial" \
  OpenMath/Chapter4/Section422.lean
# Expected: lines 6410 and 6439

wc -l OpenMath/Chapter4/Section422.lean
# Expected: 8101
```

If all four checks pass (they will), the cycle 399 trichild
infrastructure is real and ready for cycle 400's calibration witness.
**Do NOT attempt to re-ship cycle 399's deliverables.** Proceed
directly to §1 below.

If any check fails, escalate via the phantom-verdict issue file and
investigate before any Lean edits.

## §1 Priority 1 — DELIVERABLE: `inversePolyTree_bushy` calibration

Per the cycle 398 scoping doc
(`.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`)
§6.2 and the cycle 399 task results §"Suggested next approach", ship
the calibration theorem that verifies cycle 399's trichild
infrastructure numerically against cycle 370's bushy closed form.

### Target

```lean
/-- *Phase α'.4.1 (cycle 400) — `bushy` calibration witness.*

`inversePolyTree bushy f = (f vertex)^4 − 3·(f vertex)^2·f cherry
+ 3·f vertex·f broom₃ − f bushy` matches cycle 370's
`elementaryWeightQ_phi_inv_bushy`. Since `bushy = mk [vertex, vertex,
vertex]` (three-child), the proof unfolds the triple-children branch
of `inversePolyTree` (cycle 399), rewrites
`inversePolyTree vertex f = -f vertex` via `inversePolyTree_vertex`
three times, expands `trichildPolynomial`, and observes that the
`(vertex, vertex, vertex)` triple matches the if-branch of
`trichildCrossTerm`, evaluating to `3 · f vertex · f broom₃`. Closes
by `ring` after a `show`-bridge that canonicalises `f (mk [vertex])
↔ f cherry` and `f (mk [vertex, vertex, vertex]) ↔ f bushy`. -/
theorem inversePolyTree_bushy (f : RT → ℝ) :
    inversePolyTree RootedTree.bushy f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy
```

### Proof recipe (literal port of cycle 387/392/394/395 pattern)

```lean
  by
  show inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex, RootedTree.vertex]) f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy
  rw [inversePolyTree, inversePolyTree_vertex,
      inversePolyTree_vertex, inversePolyTree_vertex]
  unfold trichildPolynomial
  rw [show trichildCrossTerm RootedTree.vertex RootedTree.vertex
            RootedTree.vertex f
          = 3 * f RootedTree.vertex * f RootedTree.broom₃ by
        unfold trichildCrossTerm
        rw [if_pos ⟨rfl, rfl, rfl⟩]]
  show -(f RootedTree.vertex * -f RootedTree.vertex *
            -f RootedTree.vertex * -f RootedTree.vertex)
        - -f RootedTree.vertex * -f RootedTree.vertex *
            f RootedTree.cherry
        - -f RootedTree.vertex * -f RootedTree.vertex *
            f RootedTree.cherry
        - -f RootedTree.vertex * -f RootedTree.vertex *
            f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy
  ring
```

**Outer `show`**: unfolds `bushy := mk [vertex, vertex, vertex]`
(non-reducible `def` per memory `feedback_ring_def_opacity.md`) so
the `rw [inversePolyTree, ...]` chain can pattern-match the new
fourth recursion arm (cycle 399's `mk [c₁, c₂, c₃]` case). Cycle
387's `inversePolyTree_cherry` uses the same outer-`show` pattern at
`mk [vertex]` (`Section422.lean:6505`).

**`rw [inversePolyTree, inversePolyTree_vertex × 3]`**: steps the
recursion through the new triple-children arm, replacing each
`inversePolyTree vertex f` by `-f vertex`. Three calls because three
children.

**`unfold trichildPolynomial`**: exposes the 6-term backbone
`-(f v · inv₁ · inv₂ · inv₃) − inv₂·inv₃·f(mk [v]) − inv₁·inv₃·f(mk [v])
− inv₁·inv₂·f(mk [v]) + trichildCrossTerm v v v f − f(mk [v,v,v])`
with `inv₁ = inv₂ = inv₃ = -f vertex`.

**Inner `rw [show trichildCrossTerm v v v f = ... by ...]`**: at
`(vertex, vertex, vertex)`, the `if_pos ⟨rfl, rfl, rfl⟩` discharges
the triple-conjunction, giving the value
`3 * f vertex * f broom₃`. Single `if_pos` because there's only one
matched branch in cycle 399's `trichildCrossTerm` definition (the
default case is `0`).

**Inner `show ... = ...`**: bridges `f (mk [vertex]) ↔ f cherry` and
`f (mk [vertex, vertex, vertex]) ↔ f bushy`. Per memory
`feedback_ring_def_opacity.md`, `ring` cannot canonicalise these
non-reducible-`def` aliases — the `show` rewrites the goal into a
purely algebraic form that `ring` can close.

**`ring`**: closes the resulting algebraic identity
`-(v · (-v)³) − 3 · (-v)² · c + 3·v·b' − bushy = v⁴ − 3v²c + 3v·b' − bushy`.

### LOC estimate and insertion site

~30–35 LOC including the docstring. **Insertion site**: place
`inversePolyTree_bushy` immediately after cycle 395's
`inversePolyTree_mkMkCherry` (line 6626) — bushy is order-4 like
`mk [mk [cherry]]`, and slotting them adjacent groups all order-4
ladder-tree calibrations. Alternative: locate cycle 392's
`inversePolyTree_mkBroom₃` and insert nearby — both are
"non-leaf-wrapped" calibration witnesses with the same proof shape
modulo the trichild vs monochild dispatch.

### Verification commands (after edit)

```bash
lake env lean OpenMath/Chapter4/Section422.lean
# Expected: exit 0; only pre-existing grandfathered sorry warning at line 2272

grep -c sorry OpenMath/Chapter4/Section422.lean
# Expected: 5 (unchanged: 4 docstring + 1 grandfathered code)

# Spot-check axiom cleanliness via lean_verify MCP:
# inversePolyTree_bushy → [propext, Classical.choice, Quot.sound]
```

Cycle 400 build time will be slower than recent cycles (warm cache
~14 min per cycle 399 task results §Result, due to the extended
5-arm `inversePolyTree` recursion's equation-compiler unfolding
overhead). Budget accordingly; do NOT panic if `lake env lean` runs
8–15 min on first compile.

## §2 Priority 2 — STRETCH ONLY: Skip the explicit Euler non-vacuity example

Per cycle 398 scoping doc §6.2 step 7 ("Optional non-vacuity
`example`"), an `example` at `f := elementaryWeightQ_phi
⟦explicitEuler⟧` confirming `inversePolyTree bushy f = 1` is
explicitly marked optional. **Skip this cycle**. The calibration
theorem above IS the non-vacuity content; a redundant `example` at
explicit Euler adds compile time without informational value.

## §3 Priority 3 — DO NOT TOUCH

* **Do NOT migrate `inversePolynomial`'s `bushy` branch.** That is
  cycle 401's Phase α'.4.2 P5 deliverable per scoping doc §6.3
  (parallel of cycle 397's `mk [mk [cherry]]` migration recipe with
  bridge theorem `inversePolyTree_bushy_eq_inversePolynomial`).
  Cycle 400 produces *only* the calibration; cycle 401 wires it into
  `inversePolynomial`'s dispatch chain.
* **Do NOT attempt to close the cycle 365 grandfathered sorry**
  (`Section422.lean:2279`,
  `powRep_sum_eq_of_strict_subtree_agreement` general body). That
  requires the full `inversePolynomial` migration of all 9 ladder
  trees plus multi-cycle Phase β/γ extension. After cycle 401, all 9
  trees route through `inversePolyTree` and cycle 402+ can begin
  attacking the sorry.
* **Do NOT extend `trichildCrossTerm` beyond `(vertex, vertex,
  vertex)`.** No other three-children ladder tree exists; the
  default `else 0` branch is correct for all foreseeable Phase α'
  work.
* **Do NOT submit to Aristotle.** This is a pure mechanical proof
  with no `sorry`s to mine; no Aristotle suitability per cycle 399
  strategy §G precedent.
* **Do NOT add explicit-Euler examples for previously-shipped
  calibrations** (e.g. re-witnessing `inversePolyTree_cherry`,
  `inversePolyTree_broom₃` at `⟦explicitEuler⟧`). Cycle 399 didn't
  add any; cycle 400 follows suit.

## §4 What NOT to try — failure modes flagged by memory + history

Memory hits that apply to this cycle:

* **`feedback_ring_def_opacity.md`** — `ring` cannot bridge `f (mk
  [args])` to `f namedTree` when `namedTree` is a non-reducible
  `def` (like `cherry`, `broom₃`, `bushy`). **Apply the recommended
  fix: insert `show ...` to canonicalize before `ring`.** The proof
  recipe in §1 above includes the necessary `show` bridge already.
  Do NOT skip it — the proof will fail with "ring failed" if you
  feed `ring` a goal containing `f (mk [...])` mixed with `f cherry`
  / `f bushy`.

* **`feedback_simp_recursive_def_overunfolds.md`** — `simp
  [recursive-def, name-eq-thm]` over-unfolds. **Use targeted
  `rw [name-eq-thm, ...]` rather than `simp` for the recursion
  steps.** The proof recipe uses `rw [inversePolyTree, ...]` not
  `simp [inversePolyTree, ...]`; do not "improve" this with simp.

* **`feedback_indexed_inductive_cases_disjoint.md`** — not directly
  triggered this cycle (no `cases h` on distinct constructor
  inequalities expected), but the `if_pos ⟨rfl, rfl, rfl⟩`
  discharge in the inner `show trichildCrossTerm ... = ...` uses
  three definitional reflexivities on `vertex = vertex`. This works
  by `decide` semantics on `DecidableEq RootedTree` (cycle 017's
  decidable-equality instance). If `⟨rfl, rfl, rfl⟩` fails to
  type-check, fall back to: `rw [if_pos ⟨by decide, by decide, by
  decide⟩]` or split into intermediate steps.

Cycle history "what was tried" hits that apply:

* **Cycle 392 Discovery (`mk [broom₃]` migration)**: the
  `monochildCrossTerm` extension required an additional `if_neg`
  discharge in `inversePolyTree_cherry`'s proof body. **This does
  NOT apply to cycle 400.** Cycle 399's `trichildCrossTerm` has only
  one populated branch (`(vertex, vertex, vertex)`) plus the
  default; existing calibrations on smaller trees (`vertex`,
  `cherry`, `broom₃`, etc.) match patterns with arity ≤ 2 in the
  `inversePolyTree` recursion, so the new `mk [c₁, c₂, c₃]` arm does
  NOT unify against any of their match patterns. **No retrofitting
  of existing proofs is required.** Verify by running `lake env lean
  OpenMath/Chapter4/Section422.lean` *before* adding
  `inversePolyTree_bushy` — the file should still build with cycle
  399 alone.

* **Cycle 395 Discovery (`mk [mk [cherry]]`)**: the cherry-branch
  extension of `monochildCrossTerm` required two `if_neg` discharges
  before the `if_pos rfl`. For cycle 400's bushy, the
  `trichildCrossTerm` dispatch is `if_pos` directly (single
  non-default branch), so **zero `if_neg` discharges**. The proof
  recipe in §1 has this correct.

* **`feedback_planner_faithfulness_spotcheck.md`** — verify cycle
  370's closed form matches cycle 400's calibration RHS verbatim.
  Cycle 370's
  `elementaryWeightQ_phi_inv_bushy`:

  ```
  Φ_{η_q⁻¹}(bushy) = v⁴ − 3v²·c + 3v·b' − Φ_η(bushy)
  ```

  Cycle 400's target:

  ```
  inversePolyTree bushy f = (f v)^4 − 3·(f v)^2·f cherry
                            + 3·f v·f broom₃ − f bushy
  ```

  With `f := elementaryWeightQ_phi η_q`, these match: `v = f vertex
  = Φ_η(vertex)`, `c = f cherry = Φ_η(cherry)`, `b' = f broom₃ =
  Φ_η(broom₃)`, `f bushy = Φ_η(bushy)`. ✓ **No textbook divergence;
  proceed.**

## §5 Sorry policy + axiom cleanliness

* Sorry count: 5 → 5 (unchanged — only the grandfathered cycle 365
  Sub-lemma A body at line 2279 + 4 docstring references).
* New theorem must be axiom-clean:
  `[propext, Classical.choice, Quot.sound]`. The proof recipe uses
  only `show`, `rw`, `unfold`, `if_pos ⟨rfl, rfl, rfl⟩`, and `ring`
  — all axiom-clean tactics.
* Do NOT introduce `axiom` or `constant` declarations.
* Do NOT raise `maxHeartbeats` above 200000. If the proof exceeds
  heartbeats (unlikely for a 6-line `rw + show + ring` body),
  decompose the inner `show` into two intermediate `have` statements
  for the `f cherry` and `f bushy` rewrites separately.

## §6 Cycle 401+ outlook (informational only, do NOT execute)

After cycle 400 lands the calibration:

* **Cycle 401** (Phase α'.4.2 P5 per scoping doc §6.3): migrate
  `inversePolynomial`'s `bushy` branch from cycle 383's
  `inversePolyBroom 3 f` dispatch to a `inversePolyTree bushy f`
  dispatch. Six edits (mechanical mirror of cycle 397's `mk [mk
  [cherry]]` migration): (1) bridge theorem
  `inversePolyTree_bushy_eq_inversePolynomial` via `unfold
  inversePolynomial + 4 if_neg + if_pos rfl`, (2)
  `inversePolynomial`'s `bushy` branch body migrated, (3) Phase α.2
  calibration `example` updated, (4) Phase β.3 bridge
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy` updated,
  (5) Phase γ branch in `inversePolynomial_eq_of_subtree_agreement`
  updated, (6) cycle 382's
  `inversePolyBroom_three_eq_inversePolynomial` proof body extended.
  Estimated ~50 LOC. **Do NOT attempt in cycle 400.**

* **Cycle 402+**: all 9 ladder trees now route uniformly through
  `inversePolyTree`. The cycle 365 grandfathered Sub-lemma A sorry
  becomes attackable via the unified recursive structure (multi-
  cycle Phase β/γ extension).

## §7 Success criteria (cycle 400 self-check)

1. `OpenMath/Chapter4/Section422.lean` grows by ~30–35 LOC (cycle
   400's calibration witness only).
2. `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 with
   only the grandfathered sorry warning at line 2272.
3. `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5
   (unchanged).
4. `#print axioms OpenMath.Chapter4.Section422.inversePolyTree_bushy`
   returns `[propext, Classical.choice, Quot.sound]`.
5. No existing calibration witness (`inversePolyTree_{vertex,
   cherry, broom₃, mkBroom₃, mkCherry, mkMkCherry, mkCherryCherry,
   mkBroomCherry, mkVertexCherry}`) regresses — verified by
   successful build.
6. §422 axiom-clean streak advances: 61 substantive + 3 doc
   (cycles 336–399) → **62 substantive + 3 doc** (cycles 336–400).
7. `lean_status.json` for `def:422B`: `cycle_completed_at` bumped
   from 399 to 400; status remains `partial`; `lean_symbol` remains
   on the existing partial-ship symbol (do NOT rename — the
   calibration is infrastructure, not a textbook entity closure).
8. `plan.md` for `def:422B`: status row updated with cycle 400 note
   appended to the existing partial-ship entry; row remains `[~]`.

## §8 Bottom line

Ship `inversePolyTree_bushy` calibration theorem (~30–35 LOC) per
the §1 recipe. One theorem, axiom-clean, sorry-clean, regression-
free. Cycle 401 follows with the `bushy` branch migration; cycles
402+ revisit the grandfathered cycle 365 sorry.

The cycle 399 supervisor verdict was a phantom — proceed normally.
