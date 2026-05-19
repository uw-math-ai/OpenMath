# Cycle 396 Results

## Worked on

Phase α'.4.2 P3 — migration of `inversePolynomial`'s `mk [cherry]` branch
from `inversePolyChain 2 f` to `inversePolyTree (mk [cherry]) f`. Strict
mechanical mirror-port of cycle 393's `mk [broom₃]` migration and cycle
391's `mk [vertex, cherry]` migration. **Third Phase α'.4.2 migration**
(cycles 391, 393, 396 done; cycles 397+ target `bushy`,
`mk [mk [cherry]]`).

File touched: `OpenMath/Chapter4/Section422.lean` only (plus
bookkeeping).

## Approach

Per cycle 396 strategy, five planned edits + one derivative fix:

1. **Step B body migration** — `inversePolynomial`'s 4th branch
   (`mk [cherry]`, line 6798–6800) rewritten from
   `inversePolyChain 2 f` to
   `inversePolyTree (mk [cherry]) f`. Mirrors cycle 391/393 branch
   shape verbatim.
2. **Step A bridge theorem** — `inversePolyTree_mkCherry_eq_inversePolynomial`
   added immediately after cycle 393's
   `inversePolyTree_mkBroom₃_eq_inversePolynomial`. Proof: `unfold
   inversePolynomial`, then three `if_neg`s (vertex, cherry, broom₃)
   followed by `if_pos rfl`. After Step B, both sides literally reduce
   to `inversePolyTree (mk [cherry]) f`, closing by the implicit `rfl`
   after the `rw` cascade.
3. **Step C** — Phase α.1 (cycle 374) `mk [cherry]` calibration
   `example` (line ~6875): `inversePolyChain_two` replaced with
   `inversePolyTree_mkCherry`. Both unfold to the same closed form
   `-(f vertex)^3 + 2·f vertex·f cherry - f (mk [cherry])`.
4. **Step D** — Phase β.1 bridge
   `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry` (line
   ~7361): `inversePolyChain_two` → `inversePolyTree_mkCherry`.
5. **Step E** — Phase γ
   `inversePolynomial_eq_of_subtree_agreement` `mk [cherry]` branch
   (line ~7672): both `inversePolyChain_two` instances replaced with
   `inversePolyTree_mkCherry` (Phase γ rewrites once per `f` and `g`
   side, mirroring cycle 393's double-replacement).
6. **Derivative edit (not in strategy)** — cycle 380's Phase α'.1
   bridge `inversePolyChain_two_eq_inversePolynomial` proof: after
   migration, the goal becomes `inversePolyChain 2 f = inversePolyTree
   (mk [cherry]) f`. Closed by appending `inversePolyChain_two,
   inversePolyTree_mkCherry` to the existing `rw` (both routes reduce
   to the same closed form). Theorem statement unchanged; only proof
   body extended by two rewrite tokens. Docstring tweaked to note the
   cycle 396 post-migration dispatch.

## Result

SUCCESS.

* `lake build OpenMath.Chapter4.Section422` exits 0 (warm rebuild 502s).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5
  (unchanged — only the cycle 365 grandfathered Sub-lemma A body
  sorry at line 2279).
* `#print axioms` verification (`/tmp/verify_axioms.lean`):
  * `inversePolyTree_mkCherry_eq_inversePolynomial`:
    `[propext, Classical.choice, Quot.sound]` ✓
  * `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry`:
    `[propext, Classical.choice, Quot.sound]` ✓
  * `inversePolynomial_eq_of_subtree_agreement`:
    `[propext, Classical.choice, Quot.sound]` ✓
  * `inversePolyTree_mkCherry`:
    `[propext, Classical.choice, Quot.sound]` ✓ (regression spot-check)
  * `inversePolyTree_mkMkCherry`:
    `[propext, Classical.choice, Quot.sound]` ✓ (regression spot-check)
  * `inversePolyChain_two_eq_inversePolynomial`:
    `[propext, Classical.choice, Quot.sound]` ✓ (post-derivative-edit
    axiom-clean confirmation)
* §422 axiom-clean streak: 58 → **59 substantive + 2 doc** (336–396).
* LOC delta: Section422.lean +~40 LOC (Step A theorem ~30 LOC + small
  derivative-edit + body migration); within budget.

## Faithfulness check

This cycle introduced **one** new theorem
(`inversePolyTree_mkCherry_eq_inversePolynomial`) and modified the
body of one existing `noncomputable def`
(`inversePolynomial`'s `mk [cherry]` branch) plus four downstream
proof-only updates.

### `inversePolynomial`'s `mk [cherry]` branch body (Step B)

* **Entity ID**: `def:422B` (the underlying-one-step-method capstone
  that `inversePolynomial` feeds into).
* **Textbook statement** (from
  `extraction/formalization_data/entities/def_422B.json` —
  `def:422B` is Butcher §422 p. 358 eq. (422a)):
  > Butcher §422 defines the (422a) condition equationally; the
  > inverse-polynomial `inversePolynomial` is a Lean-side scaffold
  > computing the closed form of `Φ_{η⁻¹}(t)` per tree in the
  > 9-tree ladder, factored through cycle 387's recursive
  > `inversePolyTree` once Phase α'.4.2 lands.
* **Lean statement captures**: same content. The pre-migration body
  `inversePolyChain 2 f` and the post-migration body `inversePolyTree
  (mk [cherry]) f` both unfold to the cycle 369 closed form `-v³ +
  2vc - m`, witnessed concurrently by cycle 380's
  `inversePolyChain_two_eq_inversePolynomial` (now with extended
  proof) and cycle 394's `inversePolyTree_mkCherry`.
* **Justification for divergence**: no divergence — the migration is
  a refactor that swaps one recursive helper for another with the
  same closed form. The Phase β.1 / Phase γ consumers are all
  updated to bridge through `inversePolyTree_mkCherry` instead of
  `inversePolyChain_two`, preserving their semantics.

### `inversePolyTree_mkCherry_eq_inversePolynomial` (Step A — new theorem)

* **Entity ID**: helper bridge (not a named Butcher theorem; mirrors
  cycle 391's `inversePolyTree_mkVertexCherry_eq_inversePolynomial`
  and cycle 393's `inversePolyTree_mkBroom₃_eq_inversePolynomial`).
* **Textbook statement**: N/A — internal Lean-side bridge.
* **Lean statement captures**: `inversePolyTree (mk [cherry]) f =
  inversePolynomial (mk [cherry]) f`. Post-migration, both sides
  literally reduce to `inversePolyTree (mk [cherry]) f`; the `rw`
  cascade closes by implicit `rfl`. **Tautology check** (CLAUDE.md
  pre-commit): the conclusion is `inversePolyTree (mk [cherry]) f =
  inversePolynomial (mk [cherry]) f`, which is NOT a hypothesis (the
  theorem has only `f : RT → ℝ` as input). **Identity check**: the
  proof is not `exact h`; it threads through
  `unfold inversePolynomial` + 3 `if_neg` discharges + `if_pos rfl`,
  proving genuine definitional equality across the
  `inversePolynomial` branch dispatch. **Hypothesis strength check**:
  the only hypothesis is `f : RT → ℝ` (the input function), which
  matches the textbook quantification at the per-tree level.
* **Justification for divergence**: none — the bridge is the
  standard Family A / Family C glue lemma shipped per cycle 379
  scoping doc §5.

## Dead ends

None. The strategy's recipe was directly executable. One small
surprise: the cycle 380 bridge `inversePolyChain_two_eq_inversePolynomial`
needed a derivative-edit (not listed in the strategy's 5 steps) because
its proof relied on the pre-migration body literally being
`inversePolyChain 2 f`. After Step B, the RHS evaluates to
`inversePolyTree (mk [cherry]) f`, leaving the goal `inversePolyChain
2 f = inversePolyTree (mk [cherry]) f` unsolved. Fix: append
`inversePolyChain_two, inversePolyTree_mkCherry` to the existing `rw`
cascade so both sides reduce to their common closed form. The first
build attempt caught this (single error at line 7085 after the
migration); the fix was one rewrite-list extension. This is
analogous to cycle 393's experience with downstream consumers of the
migrated branch.

## Discovery

**Cycle 393 / 391 migrations did not require an analog of the cycle
380 bridge update because there is no `inversePolyBroom_*` or
`inversePolyChain_*` named bridge theorem proved by `unfold
inversePolynomial; rw [...if_pos rfl]` for those branches.** Cycle
380's `inversePolyChain_two_eq_inversePolynomial` is the only such
named bridge in the file that lives one level *above* the per-tree
calibration `example`s and *below* the Phase β bridges. The Phase
α'.4.2 migration recipe should therefore include a **"check for
upstream `inversePolyChain_*_eq_inversePolynomial` named bridges"**
step alongside the five strategy steps. For cycle 397+ (`bushy`
migration), the analogous bridge to scrutinise is
`inversePolyBroom_three_eq_inversePolynomial` (cycle 383); for cycle
398+ (`mk [mk [cherry]]`), it's
`inversePolyChain_three_eq_inversePolynomial` (cycle 380).

**Tooling friction**: `lake env lean <file>` does **not** update the
`.olean` cache, only typechecks. Downstream `#print axioms` (via a
separate import file) requires `lake build OpenMath.Chapter4.Section422`
to refresh the `.olean`. Confirmed empirically: the first `#print
axioms` attempt ran against a stale 23:45 olean and reported
`Unknown constant` for the new theorem (Lean session imported the old
file's contents); after `lake build`, the same script resolved all 6
theorems and reported each as axiom-clean.

## Suggested next approach

**Cycle 397** (per strategy and cycle 395 task results' "Suggested
next approach"): ship `inversePolyTree_bushy` calibration witness
(Phase α'.4.1 P8). `bushy = mk [vertex, vertex, vertex]` is a
three-leaf-children tree; `inversePolyTree`'s recursive case at this
arity needs scrutiny to confirm the closed form matches cycle 370's
`elementaryWeightQ_phi_inv_bushy` (`v⁴ + …`). The current
`inversePolyTree` dispatch (per cycle 387 ship) handles `[]`, `[c]`,
`[c₁, c₂]`, and `(_::_::_::_) → 0` for arity ≥ 3 — so `bushy` falls
into the default-zero branch. The cycle 397 deliverable is to
**extend** `inversePolyTree`'s recursion to a `[c₁, c₂, c₃]` case
covering `bushy` (and via cycle 386 precedent, possibly to
arbitrary-arity children with a `Finset.sum`-style closed form). The
P8 calibration witness `inversePolyTree_bushy` then closes the
arity-3 piece and unblocks cycle 398's Phase α'.4.2 `bushy`
migration.

**Cycle 398** (after cycle 397 P8 lands): Phase α'.4.2 `bushy`
migration (parallel of cycles 391/393/396). Replace
`inversePolynomial`'s `bushy` branch body `inversePolyBroom 3 f` with
`inversePolyTree RootedTree.bushy f`. Update cycle 383's
`inversePolyBroom_three_eq_inversePolynomial` analogously to cycle
396's derivative edit. Plus the standard 5 strategy steps (A: bridge
theorem; B: body migration; C: calibration `example`; D: Phase β
bridge; E: Phase γ branch — twice for `f` and `g` sides).

**Cycle 399** (or earlier if cycle 397's arity-3 extension covers
multiple ladder trees): Phase α'.4.2 `mk [mk [cherry]]` migration.
Cycle 395's `inversePolyTree_mkMkCherry` is the calibration. Recipe
mirrors cycle 396 step-for-step (single-child arity-1 branch).

**Cycle 400+**: Once all 9 ladder trees dispatch through
`inversePolyTree`, the Phase β.1 / Phase β.2 bridges
(`elementaryWeightQ_phi_inv_eq_inversePolynomial_*`) can be
*collapsed* to a single dispatch lemma routing through
`inversePolyTree`'s recursion. Cycle 365 grandfathered Sub-lemma A's
body (`powRep_sum_eq_of_strict_subtree_agreement` at line 2279)
becomes attackable once the recursive structure is uniform: cycle 365
task results noted the obstacle was the heterogeneous `Fin (M.1 *
(m+1))` summation ranges; under a unified `inversePolyTree`-style
recursion, the parametricity statement of cycle 362's
`derivativeWeightWithSrc_eq_of_strict_subtree_agreement` may compose
cleanly with the recursive descent, finally closing the sole code-level
sorry in §422.
