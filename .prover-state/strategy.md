# Cycle 500 Strategy — Phase α'.5.2.1 ship: `tetrachildPolynomial` + `inversePolyTree` 6-arm extension + `inversePolyTree_bushy₄` calibration

## §A. Context

Cycle 499 closed Phase α'.5.2.0 axiom-clean: `elementaryWeightQ_phi_inv_bushy₄` (the order-5 broom quotient-level closed form) + m=0 corollary + non-vacuity witnesses. §422 streak: **72 substantive + 6 doc** (cycles 336–499).

Per `def_422B_phase_alpha_prime_5_2_scoping.md` §6.2 and the cycle 499 task results §"Suggested next approach", cycle 500 ships Phase α'.5.2.1: the **infrastructure layer** consuming cycle 499's closed form. Four deliverables, all axiom-clean target, ~90–110 LOC total per the scoping doc estimate.

Single grandfathered sorry at `Section422.lean:2279` (cycle 365's Sub-lemma A body) is **not** addressable this cycle — Phase α'.5.2.1 builds the dispatch infrastructure that Phase β/γ extension (cycle ~510+) will eventually consume to close it.

## §B. Priority 1 — DELIVERABLE (this cycle)

Ship four named symbols in `OpenMath/Chapter4/Section422.lean`, inserted **immediately after `trichildPolynomial`** at line ~10054 (before the current `inversePolyTree` definition at line 10086). Then extend `inversePolyTree` itself and append the calibration witness.

### B.1 — `tetrachildCrossTerm` (~30 LOC)

Mirror cycle 399's `trichildCrossTerm` design (line 9956+). Single `if-then-else` with the `(vertex, vertex, vertex, vertex)` branch populated from cycle 499's closed form; default → 0.

```lean
/-- *Phase α'.5.2.1 (cycle 500) — quadrilinear cross-term cascade.*

The Block (6)–(15) bilinear + trilinear cross-term contributions to
`Φ_{η_q⁻¹}(mk [t₁, t₂, t₃, t₄])` after Blocks (1)–(5) and (16) are
absorbed into `tetrachildPolynomial`. Per cycle 499's
`elementaryWeightQ_phi_inv_bushy₄` closed form, the symmetric
`(vertex, vertex, vertex, vertex)` quadruple evaluates to
`-6·(f vertex)²·f broom₃ + 4·f vertex · f bushy` (the binomial-row-4
bilinear + trilinear contributions at all-vertex children).

All non-symmetric `k = 4` quadruples currently dispatch to `0` —
Phase α'.5.2.k (cycles 501+) will refine the cascade with named
branches as new closed forms ship. -/
noncomputable def tetrachildCrossTerm
    (t₁ t₂ t₃ t₄ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.vertex
      ∧ t₃ = RootedTree.vertex ∧ t₄ = RootedTree.vertex then
    -6 * (f RootedTree.vertex)^2 * f RootedTree.broom₃
      + 4 * f RootedTree.vertex * f RootedTree.bushy
  else
    0
```

### B.2 — `tetrachildPolynomial` (~25 LOC)

Mirror cycle 399's `trichildPolynomial` design (line 10054+) with one extra child slot per the scoping doc §4 strawman:

```lean
/-- *Phase α'.5.2.1 (cycle 500) — quadruple-children backbone polynomial.*

`tetrachildPolynomial t₁ t₂ t₃ t₄ inv₁ inv₂ inv₃ inv₄ f` is the
closed-form polynomial in `f` and the four child-inverse values
`inv_ℓ = inversePolyTree tℓ f` that captures the inverse-class
`Φ_{η_q⁻¹}` at `mk [t₁, t₂, t₃, t₄]`. Per cycle 358's `_inv_mk`
formula expanded at four children, the per-row product
`Πℓ (inv_ℓ + S_ℓ(i))` decomposes into 16 = 2⁴ blocks; this
polynomial absorbs Blocks (1)–(5) and (16) explicitly and packages
Blocks (6)–(15) via `tetrachildCrossTerm`. Sign convention matches
cycle 387's `bichildPolynomial` and cycle 399's `trichildPolynomial`. -/
noncomputable def tetrachildPolynomial
    (t₁ t₂ t₃ t₄ : RT) (inv₁ inv₂ inv₃ inv₄ : ℝ) (f : RT → ℝ) : ℝ :=
  -(f RootedTree.vertex * inv₁ * inv₂ * inv₃ * inv₄)
    - inv₂ * inv₃ * inv₄ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₁])
    - inv₁ * inv₃ * inv₄ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₂])
    - inv₁ * inv₂ * inv₄ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₃])
    - inv₁ * inv₂ * inv₃ * f (OpenMath.Chapter3.Section310.RootedTree.mk [t₄])
    + tetrachildCrossTerm t₁ t₂ t₃ t₄ f
    - f (OpenMath.Chapter3.Section310.RootedTree.mk [t₁, t₂, t₃, t₄])
```

### B.3 — Extend `inversePolyTree` recursion (~10 LOC)

At line 10086, **insert** a new fourth arm before the catch-all, and **bump** the catch-all pattern from `(_ :: _ :: _ :: _ :: _)` (k≥4 fires) to `(_ :: _ :: _ :: _ :: _ :: _)` (k≥5 fires now). The 6-arm result:

```lean
noncomputable def inversePolyTree : RT → (RT → ℝ) → ℝ
  | OpenMath.Chapter3.Section310.RootedTree.mk [], f =>
      -f RootedTree.vertex
  | OpenMath.Chapter3.Section310.RootedTree.mk [c], f =>
      -(f RootedTree.vertex * inversePolyTree c f)
        + monochildCrossTerm c f
        - f (OpenMath.Chapter3.Section310.RootedTree.mk [c])
  | OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂], f =>
      bichildPolynomial c₁ c₂
        (inversePolyTree c₁ f) (inversePolyTree c₂ f) f
  | OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃], f =>
      trichildPolynomial c₁ c₂ c₃
        (inversePolyTree c₁ f) (inversePolyTree c₂ f)
        (inversePolyTree c₃ f) f
  | OpenMath.Chapter3.Section310.RootedTree.mk [c₁, c₂, c₃, c₄], f =>     -- NEW
      tetrachildPolynomial c₁ c₂ c₃ c₄
        (inversePolyTree c₁ f) (inversePolyTree c₂ f)
        (inversePolyTree c₃ f) (inversePolyTree c₄ f) f
  | OpenMath.Chapter3.Section310.RootedTree.mk
      (_ :: _ :: _ :: _ :: _ :: _), _ => 0                                 -- bumped
```

**CRITICAL ordering**: insert the `[c₁, c₂, c₃, c₄]` arm BEFORE the catch-all, and change the catch-all pattern. Lean evaluates patterns top-down; reversing the order makes the catch-all fire first. Mirror cycle 399's catch-all bump precisely.

**The docstring above `inversePolyTree`** at lines 10066–10085 needs one new bullet listing the `mk [c₁, c₂, c₃, c₄]` arm. Update it.

### B.4 — `inversePolyTree_bushy₄` calibration witness (~35 LOC)

Mechanical port of cycle 400's `inversePolyTree_bushy` recipe (line 10277+) with one extra `inversePolyTree_vertex` rewrite slot and the `tetrachildCrossTerm` `if_pos ⟨rfl, rfl, rfl, rfl⟩` dispatch:

```lean
/-- *Phase α'.5.2.1 (cycle 500) — `bushy₄` calibration witness.*

`inversePolyTree bushy₄ f = -(f vertex)^5 + 4·(f vertex)^3·f cherry
- 6·(f vertex)^2·f broom₃ + 4·f vertex·f bushy - f bushy₄`
matches cycle 499's `elementaryWeightQ_phi_inv_bushy₄`. Since
`bushy₄ = mk [vertex, vertex, vertex, vertex]` (four-child), the
proof unfolds the quadruple-children branch of `inversePolyTree`
(this cycle), rewrites `inversePolyTree vertex f = -f vertex` via
`inversePolyTree_vertex` four times, expands `tetrachildPolynomial`,
and observes that the `(vertex, vertex, vertex, vertex)` quadruple
matches the if-branch of `tetrachildCrossTerm`. Closes by `ring`
after a `show`-bridge canonicalising `f (mk [vertex]) ↔ f cherry`
and `f (mk [vertex, vertex, vertex, vertex]) ↔ f bushy₄`. -/
theorem inversePolyTree_bushy₄ (f : RT → ℝ) :
    inversePolyTree RootedTree.bushy₄ f
      = -(f RootedTree.vertex) ^ 5
        + 4 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
        - 6 * (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
        + 4 * f RootedTree.vertex * f RootedTree.bushy
        - f RootedTree.bushy₄ := by
  show inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex,
         RootedTree.vertex, RootedTree.vertex]) f
      = _
  rw [inversePolyTree, inversePolyTree_vertex]
  unfold tetrachildPolynomial
  rw [show tetrachildCrossTerm RootedTree.vertex RootedTree.vertex
            RootedTree.vertex RootedTree.vertex f
          = -6 * (f RootedTree.vertex)^2 * f RootedTree.broom₃
            + 4 * f RootedTree.vertex * f RootedTree.bushy by
        unfold tetrachildCrossTerm
        rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]]
  -- `show` bridge canonicalises mk [vertex] ↔ cherry and
  -- mk [vertex, vertex, vertex, vertex] ↔ bushy₄ (per memory
  -- feedback_ring_def_opacity.md - ring cannot see through these
  -- non-reducible defs without the explicit bridge).
  -- The exact `show` body must match what Lean's elaborator produces
  -- post-`unfold tetrachildPolynomial` + `rw`. Read cycle 400's
  -- `inversePolyTree_bushy` proof at lines 10283–10310 and adapt
  -- by adding one more `-f vertex` factor per block.
  show _ = _   -- ← REPLACE with explicit goal-matching shape
  ring
```

**Critical implementation note**: the inner `show` block must reproduce **exactly** what Lean's elaborator produces after the `unfold tetrachildPolynomial` + `rw` chain. Read cycle 400's working `inversePolyTree_bushy` proof (lines 10277–10310 in `Section422.lean`) for the goal-matching pattern; the cycle 500 version adds one more `* -f RootedTree.vertex` factor per block plus one extra `(-1)^5 = -1` outer-sign adjustment on Block (1). If `ring` fails, the error message names the residual goal — adjust the `show` to match.

**Important: `RootedTree.bushy₄`** — cycle 499 added this alias at `Section310.lean` per its task results §"Discovery #3"; verify before B.4 via:

```bash
grep -n "bushy₄" OpenMath/Chapter3/Section310.lean
```

If absent (unlikely, but defensive), ship the one-line `noncomputable def RootedTree.bushy₄ : RootedTree := mk [vertex, vertex, vertex, vertex]` at the top of B.4's content in `Section422.lean`. Per memory `feedback_ring_def_opacity.md`, `bushy₄` is non-reducible to `ring`, so the `show` bridge in B.4 is mandatory regardless.

## §C. Priority 2 — Non-vacuity example (5–10 LOC, optional)

After the calibration witness, add an `example` on `⟦explicitEuler⟧` confirming numerical agreement. At explicit Euler `v = 1, c = b' = bushy = bushy₄ = 0`, the closed form evaluates to `-1` (matches cycle 499's `elementaryWeightQ_phi_inv_bushy₄` non-vacuity value). Same recipe as cycle 499's non-vacuity examples.

This is a regression check, NOT a deliverable bar — skip if B.1–B.4 consume the cycle budget.

## §D. What NOT to attempt

1. **Do NOT use `simp [inversePolyTree, inversePolyTree_vertex, …]`** for the calibration proof — per memory `feedback_simp_recursive_def_overunfolds.md`, this over-unfolds the recursive def and the name-equality theorems get linted as unused. The recipe in §B.4 uses targeted `rw` followed by a `show` bridge, then `ring`. Cycle 400's bushy precedent shows exactly this pattern works.

2. **Do NOT attempt to refine `tetrachildCrossTerm` for non-symmetric quadruples** (e.g. `(v,v,v,c)`, `(v,c,c,c)`). Those are Phase α'.5.2.k cycle 501+ deliverables. The `else → 0` default is intentional — it leaves the calibration ladder one-cycle-per-quadruple consistent with cycles 388/389/390/391 (binary), 403/491/492/493/494 (ternary). Cycle 500 is purely infrastructure.

3. **Do NOT attempt to ship Phase β.1 / γ extensions** (the 14-tree ladder dispatch theorems, cycle 496/497 precedents) to incorporate `inversePolyTree_bushy₄`. Those are Phase β.2 extension work (cycle ~510+ per scoping doc §6.4) and require the full Phase α'.5.2 ladder to populate first.

4. **Do NOT attempt to close the cycle 365 grandfathered sorry** at line 2279. Multi-cycle Phase β/γ extension work; Phase α'.5.2.1 is infrastructure for the eventual closure.

5. **Do NOT submit to Aristotle**. These are pure `noncomputable def`s + a mechanical calibration proof. Cycle 400 closed `inversePolyTree_bushy` in one cycle without Aristotle; the cycle 500 ship is structurally identical with one extra child slot. The mechanical recipe in §B.4 is reliable.

6. **Do NOT introduce `axiom` or `constant`** anywhere.

7. **Do NOT raise `maxHeartbeats`** above 200000. If the `ring` step times out on the closed-form algebraic identity, the issue is more likely a `show` mismatch than a genuine elaboration blow-up — re-read the goal and adjust the `show` before considering decomposition.

8. **Do NOT alter the cycle 400 `inversePolyTree_bushy` proof or cycle 387/394/395 `_cherry/_mkCherry/_mkMkCherry` proofs**, even though their patterns no longer pattern-match against the catch-all (since we bumped from k≥4 to k≥5). They all matched on lower-arity arms (0/1/2/3 children), so the catch-all bump is invisible to them. Verify by `lake build OpenMath.Chapter4.Section422` after editing — all existing calibration witnesses should re-compile clean.

9. **Do NOT skip the catch-all bump**. If the bump is missed, the new `[c₁, c₂, c₃, c₄]` arm and the unbumped catch-all `(_ :: _ :: _ :: _ :: _)` overlap at `k = 4`. Lean's pattern matcher will either error on non-exhaustive matching or silently pick the catch-all over the new arm, breaking the calibration. Cycle 399's bump (k≥3 → k≥4 catch-all) is the precise template — mirror its pattern.

## §E. Build cost mitigation

Per cycle 401's measured warm rebuild (1165s with 5-arm `inversePolyTree`), cycle 500's 6-arm extension may push warm rebuild toward ~1400–1500s. Mitigation:

* **Measure after B.3**: run `time lake build OpenMath.Chapter4.Section422` after the recursion extension lands (before B.4). If rebuild exceeds 1500s, document it in task results.
* **Fallback option** (only if rebuild blows past 2000s): extract `tetrachildPolynomial` and `tetrachildCrossTerm` into a new sibling file `OpenMath/Chapter4/Section422TetraChild.lean` and import. The cycle 281 `Section342NormSqHelpers.lean` is the precedent. DO NOT do this preemptively — only if measured cost demands.

## §F. Pre-flight tasks (do these BEFORE Lean edits)

1. **Verify `RootedTree.bushy₄` exists**:
   ```
   grep -n "bushy₄" OpenMath/Chapter3/Section310.lean
   ```
   Expected: a `noncomputable def` of `bushy₄` at Section310.lean (added cycle 499). If absent, ship the one-line alias inline in §B.4.

2. **Read cycle 400's `inversePolyTree_bushy` proof** at `Section422.lean:10277–10310`. The cycle 500 calibration proof in §B.4 is a verbatim extension; the `show` bridge in particular is the most error-prone part and is best understood from the working cycle 400 version. Read it carefully.

3. **Read cycle 399's `trichildPolynomial` + `trichildCrossTerm`** at `Section422.lean:9956–10063`. These establish the sign convention and the `if-then-else` dispatch pattern. `tetrachildPolynomial` is a verbatim extension by one slot.

4. **Verify cycle 499's `elementaryWeightQ_phi_inv_bushy₄`** is present and its RHS matches the §B.4 closed form. Cross-check the binomial coefficients `-1, +4, -6, +4, -1` and the kernel signs.

5. **`grep -c sorry OpenMath/Chapter4/Section422.lean`** to confirm starting count is **5** (4 docstring + 1 grandfathered code at line 2279).

## §G. Cycle 500 ship checklist

After all edits:

- [ ] `Section422.lean` extended by B.1 + B.2 + B.3 + B.4 (~100 LOC).
- [ ] `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 (only existing cycle 365 sorry warning at line 2279).
- [ ] `lake build OpenMath.Chapter4.Section422` exits 0.
- [ ] `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (unchanged).
- [ ] `#print axioms` on all four new public symbols (`tetrachildCrossTerm`, `tetrachildPolynomial`, `inversePolyTree_bushy₄`, plus any new alias if `bushy₄` was added inline) → `[propext, Classical.choice, Quot.sound]` only.
- [ ] All existing `inversePolyTree_*` calibration witnesses (cycle 387/394/395/396/397/400/401/491–494) regression-pass — `lake build OpenMath.Chapter4` exits 0.
- [ ] `lean_status.json` `def:422B` row's `cycle_completed_at` bumped from 499 to 500. Status remains `partial`.
- [ ] `plan.md` `def:422B` row updated with cycle 500 closure annotation.
- [ ] `task_results/cycle_500.md` documents the ship per the standard template (Worked on / Approach / Result / Faithfulness check / Dead ends / Discovery / Suggested next approach).

## §H. Expected cycle outcomes

**Likely (90%)**: ship all four B-section deliverables clean. Total ~100 LOC, axiom-clean, build clean. §422 streak advances to **73 substantive + 6 doc** (cycles 336–500). The cycle 501 worker enters with the `inversePolyTree` 6-arm dispatch fully calibrated at `bushy₄` and ready for the next non-symmetric quadruple closed form (target per scoping doc §5.3: `mk [vertex, vertex, vertex, cherry]`, order 6, ~250–300 LOC for the Phase α'.5.2.k=1 ship combining the closed form + cross-term branch + calibration).

**Possible deviation (8%)**: build cost on the 6-arm extension exceeds 2000s and forces the §E sibling-file extraction. In that case, cycle 500 ships the four deliverables across two files; cycle 501's planner re-scopes the LOC budget per the new file layout.

**Unlikely (<2%)**: the calibration `ring` step fails to close after the `show` bridge — likely indicates the `unfold tetrachildPolynomial` + `rw` chain produces a different goal shape than cycle 400's bushy template predicts. Remediation: read the `lake env lean` error message, update the `show` block to match the actual goal, retry. If multiple attempts fail (>3 tries within 30 min), the cycle 500 worker may extract Phase β.2 sketch into cycle 501 strategy and ship only B.1–B.3 (deferring the calibration to cycle 501 with the partial recursion extension in place).
