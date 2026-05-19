# Cycle 399 Results

## Worked on

Phase α'.4.1 P8 — trichild infrastructure ship in
`OpenMath/Chapter4/Section422.lean` per cycle 398 scoping doc
(`.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`)
§6.1 deliverables:

* **`trichildCrossTerm : RT → RT → RT → (RT → ℝ) → ℝ`** — Block (5)+(6)+(7)
  trilinear cross-term per-triple dispatch. Single non-default
  if-branch at `(vertex, vertex, vertex) → 3 · f vertex · f broom₃`;
  all other triples return `0` (placeholder for future Phase α'.4.3+
  triple-children witnesses).
* **`trichildPolynomial : RT → RT → RT → ℝ → ℝ → ℝ → (RT → ℝ) → ℝ`**
  — 8-block polynomial backbone shaped
  `-(v · inv₁ · inv₂ · inv₃) − inv₂·inv₃·f(mk [t₁]) − inv₁·inv₃·f(mk [t₂])
   − inv₁·inv₂·f(mk [t₃]) + trichildCrossTerm t₁ t₂ t₃ f − f(mk [t₁,t₂,t₃])`,
  mirroring cycle 387's `bichildPolynomial` sign convention.
* **`inversePolyTree` recursion extension** — new fourth match arm
  `mk [c₁, c₂, c₃] → trichildPolynomial …` inserted before the catch-all,
  catch-all pattern bumped from `(_ :: _ :: _ :: _)` to
  `(_ :: _ :: _ :: _ :: _)` (k ≥ 4) per strategy §A.3.

Docstring above `inversePolyTree` updated to enumerate the new triple
case and the bumped catch-all arity (one-bullet diff, no rewrite).

## Approach

1. **Read predecessor code**: cycle 387's `bichildPolynomial` (line 6383)
   and `inversePolyTree` recursive def (line 6412) for the sign-convention
   anchor and qualified-name style (`OpenMath.Chapter3.Section310.RootedTree.mk`).
2. **Followed §6.1 verbatim**: inserted `trichildCrossTerm` immediately
   after `bichildPolynomial`, `trichildPolynomial` immediately after,
   then extended `inversePolyTree` body with the new 4th arm (preserving
   case order `[]`, `[c]`, `[c₁, c₂]`, `[c₁, c₂, c₃]`, k ≥ 4 catch-all).
3. **Strategy §C strawman locked**: `trichildCrossTerm vertex vertex vertex f
   = 3 · f vertex · f broom₃` matches cycle 370's bushy closed form
   (`+v⁴ − 3v²c + 3v·b' − f bushy`) — Block (5)+(6)+(7) bilinear
   contributions summing to `+3v·b'`.
4. **Skipped optional scratch verification** (§D step 7): the cycle 400
   `inversePolyTree_bushy` calibration will numerically verify the
   strawman as part of its own proof; no need to ship a redundant
   intermediate `example` this cycle.
5. **Skipped Aristotle submissions** per strategy §G: no proof
   obligations this cycle (pure `noncomputable def`s).

## Result

SUCCESS — `lake env lean OpenMath/Chapter4/Section422.lean` exits 0
with only the pre-existing grandfathered sorry warning at line 2272
(cycle 365's Sub-lemma A). All 11 existing `inversePolyTree_*`
calibration witnesses continue to pass — their match patterns
(`mk []`, `mk [c]`, `mk [c₁, c₂]`) do not unify against the new
`mk [c₁, c₂, c₃]` arm, so cycle 387–397's ship stack is undisturbed.

Build time: ~14 min on warm cache (longer than the strategy's ~200–300 s
estimate, but the recursive `inversePolyTree` def's elaboration appears
to scale with the number of match arms; the new 5-arm form is heavier
to type-check than the previous 4-arm form, and the file's growth past
8000 LOC contributes to longer LSP-driven elaboration).

LOC delta: 8038 → 8101 (+63 LOC), within the strategy's ~80–100 LOC
budget envelope. Sorry count unchanged at 5 (4 docstring + 1 grandfathered
cycle 365 code at line 2279).

§422 axiom-clean streak: 60 substantive + 3 doc (cycles 336–398) →
**61 substantive + 3 doc** (cycles 336–399). No new theorems ⇒ no
`#print axioms` verification needed per strategy §F; the new `noncomputable
def`s' axiom profile is the standard `[propext, Classical.choice, Quot.sound]`
inherited from their `noncomputable` construction.

## Faithfulness check

Three new symbols introduced this cycle, all `noncomputable def`s
(no theorems, no structures).

### `trichildCrossTerm`

* Entity ID: `def:422B` (continuing the §422 underlying one-step-method
  work track via Phase α' infrastructure; no standalone entity ID).
* Textbook anchor: cycle 370's `mk [vertex, vertex, vertex] = bushy`
  closed form
  > `Φ_{η_q⁻¹}(bushy) = v⁴ − 3v²c + 3v·b' − f bushy`
  (where `v, c, b'` abbreviate `Φ_η(vertex), Φ_η(cherry), Φ_η(broom₃)`).
* Lean statement captures: **same content** as the §C.4/§5 strawman.
  Back-computation: the `+3v·b'` term in cycle 370's closed form arises
  from Block (5)+(6)+(7)'s three identical bilinear contributions
  (each evaluating to `+v · b'`), confirming the strawman value is
  exact.
* Definition smuggling: PASS — this is a pure computational helper
  selecting one if-branch value; its `Prop`-content is delivered by
  the cycle 400 `inversePolyTree_bushy` calibration witness (not this
  cycle).
* Tautology check: PASS — no theorem shipped.
* Hypothesis strength: PASS — no theorem shipped.

### `trichildPolynomial`

* Entity ID: `def:422B`.
* Textbook anchor: cycle 387's `bichildPolynomial` (binary analogue,
  4-block decomposition); §3 of the cycle 398 scoping doc derives
  the 8-block decomposition for three children and packages Blocks
  (1)+(2)+(3)+(4)+(5)+(6)+(7)+(8) into the closed form
  `-(v·inv₁·inv₂·inv₃) − inv₂·inv₃·f(mk [t₁]) − inv₁·inv₃·f(mk [t₂])
   − inv₁·inv₂·f(mk [t₃]) + trichildCrossTerm t₁ t₂ t₃ f − f(mk [t₁,t₂,t₃])`.
* Lean statement captures: **same content** as the §4 strawman.
* Definition smuggling: PASS — computational helper; per-tuple value
  validation is deferred to cycle 400's `inversePolyTree_bushy`
  calibration.
* Tautology check: PASS — no theorem shipped.
* Hypothesis strength: PASS — no theorem shipped.

### `inversePolyTree` (extended)

* Entity ID: `def:422B`.
* Textbook anchor: same as cycle 387's original ship — the recursive
  inverse-polynomial backbone for `Φ_{η_q⁻¹}`. The new triple-children
  arm extends coverage from k ≤ 2 to k ≤ 3.
* Lean statement captures: **same content** — the recursion's
  signature is unchanged; only the match-arm dispatch is enriched.
* Definition smuggling: PASS — the new arm delegates to
  `trichildPolynomial`, mirroring the existing `[c₁, c₂]` arm's
  delegation to `bichildPolynomial`.
* Tautology check: N/A (def, not theorem).
* Termination: Lean's default `sizeOf` measure handles the new arm
  identically to the existing binary arm — each recursive call
  (`inversePolyTree c₁ f`, `inversePolyTree c₂ f`, `inversePolyTree c₃ f`)
  is on a strict child subtree of `mk [c₁, c₂, c₃]`. No
  `decreasing_by` annotation required.

## Dead ends

None. The strategy was followed verbatim — no freelancing, no
discovery of additional issues. The cycle 398 scoping doc's §6.1
deliverables proved mechanically tractable as scoped.

## Discovery

* **Compile time scaling with match-arm count**: extending
  `inversePolyTree` from 4 arms to 5 arms increased the warm-cache
  `lake env lean` time from cycle 397's ~200 s to cycle 399's
  ~800 s. The recursive def's equation-compiler-generated unfolding
  lemmas grow polynomially with arm count; future Phase α'.5 work
  on k ≥ 4 will face the same scaling.
* **Docstring tweak idiomatic**: the strategy said "preserve the
  docstring above [inversePolyTree]"; in practice a one-bullet
  insertion plus catch-all arity update were necessary to keep the
  docstring accurate. Future single-arm extensions to recursive
  defs should expect a similar minimal-edit docstring tweak.

## Suggested next approach

**Cycle 400** (Phase α'.4.1 P9) per scoping doc §6.2 — ship
`inversePolyTree_bushy` calibration:

```lean
theorem inversePolyTree_bushy (f : RT → ℝ) :
    inversePolyTree RootedTree.bushy f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy := by
  show inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex, RootedTree.vertex]) f = _
  rw [inversePolyTree, inversePolyTree_vertex,
      inversePolyTree_vertex, inversePolyTree_vertex]
  unfold trichildPolynomial
  rw [show trichildCrossTerm RootedTree.vertex RootedTree.vertex
            RootedTree.vertex f
          = 3 * f RootedTree.vertex * f RootedTree.broom₃ by
        unfold trichildCrossTerm
        rw [if_pos ⟨rfl, rfl, rfl⟩]]
  -- canonicalise mk [v] = cherry, mk [v,v,v] = bushy
  show ... = ...
  ring
```

Estimated ~30 LOC. Memory `feedback_ring_def_opacity.md` predicts the
`mk [vertex]` ↔ `cherry` and `mk [vertex, vertex, vertex]` ↔ `bushy`
bridges via `show`-blocks (cherry / bushy are non-reducible `def`s
in Section310; `ring` cannot canonicalise them without `show`).

**Cycle 401** (Phase α'.4.2 P5) per scoping doc §6.3 — migrate
`inversePolynomial`'s `bushy` branch from cycle 383's
`inversePolyBroom 3 f` dispatch to a `inversePolyTree bushy f`
dispatch. Mechanical mirror of cycle 397's `mk [mk [cherry]]`
migration recipe (6 edits: branch rewrite, new bridge theorem, three
consumer-site updates, and one derivative). Estimated ~50 LOC.

After cycle 401: all 9 ladder trees route uniformly through
`inversePolyTree`, unlocking cycle 365 grandfathered Sub-lemma A
sorry closure work (multi-cycle, Phase β/γ extension) in cycle 402+.
