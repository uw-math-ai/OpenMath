# Cycle 393 Results

## Worked on

§422 Phase α'.4.2 mechanical port of cycle 391's `mk [vertex, cherry]`
migration recipe to the `mk [broom₃]` branch. Five sub-deliverables
all shipped:

- **B.1** New public bridge theorem
  `inversePolyTree_mkBroom₃_eq_inversePolynomial`
  (`Section422.lean:7166`).
- **B.2** `inversePolynomial`'s `mk [broom₃]` branch body migrated
  from the explicit 5-term closed form
  `v⁴ - 3v²c + vb' + 2vm - Φ_η(mk [broom₃])` to the dispatch
  `inversePolyTree (mk [broom₃]) f` (Section422.lean:6725-6727).
- **B.3** Phase α.2 calibration witness `example` for `mk [broom₃]`
  (Section422.lean:6863) — appended `inversePolyTree_mkBroom₃` to
  the trailing `rw` chain so the existing proof closes against the
  post-migration RHS.
- **B.4** Phase β.3 bridge `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkBroom₃`
  (Section422.lean:7355) — same `inversePolyTree_mkBroom₃` append.
- **B.5** Phase γ `inversePolynomial_eq_of_subtree_agreement`
  `h_mkBroom` branch (Section422.lean:7691) — appended
  `inversePolyTree_mkBroom₃` twice (once per `f` and `g` side)
  before the `hv, hc, hb, hmc, hmb` substitutions.

## Approach

Read cycle 391's commit (`5f76ad1`) verbatim as the template. Counted
the `if_neg` arms required for the bridge by reading the current
`inversePolynomial` body in `Section422.lean:6714+`: the `mk [broom₃]`
branch is the 6th in the if-chain (vertex, cherry, broom₃, mk[cherry],
bushy, **mk[broom₃]**, mk[vertex,cherry], mk[mk[cherry]]), so the
proof requires **5 `if_neg` discharges** before the final `if_pos rfl`
(one less than cycle 391's `mk [vertex, cherry]` ship which is the
7th branch and needs 6 `if_neg`s).

Sequence: B.2 first (so the bridge's `if_pos rfl` exposes
`inversePolyTree (mk [broom₃]) f` on both sides) → B.3 (update the
existing calibration witness against the new RHS) → B.1 (write the
new bridge theorem) → B.4 / B.5 (downstream consumer updates). Single
`lake env lean` invocation after all edits compiles clean modulo
the grandfathered cycle 365 sorry warning. `lake build` then refreshes
the .olean for axiom verification.

## Result

**SUCCESS** — all five sub-deliverables landed.

- `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 (only
  the grandfathered cycle 365 sorry warning at line 2272).
- `lake build OpenMath.Chapter4.Section422` exits 0 (cold build
  214 s).
- `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (4 docstring
  + 1 grandfathered cycle 365 code sorry — unchanged).
- `#print axioms inversePolyTree_mkBroom₃_eq_inversePolynomial`
  → `[propext, Classical.choice, Quot.sound]`.
- Regression check: all 7 cumulative `inversePolyTree_*` calibration
  witnesses (vertex, cherry, broom₃, mkBroom₃, mkCherryCherry,
  mkBroomCherry, mkVertexCherry) re-verify axiom-clean. Both Phase β
  bridges (`_eq_inversePolynomial_mkBroom₃`,
  `_eq_inversePolynomial_mkVertexCherry`) and
  `inversePolynomial_eq_of_subtree_agreement` likewise axiom-clean.
- Section422.lean: 7823 → 7866 LOC (+43 LOC; near cycle 391's +46 LOC
  baseline and well under the strategy's 80 LOC ceiling).
- §422 axiom-clean streak: **56 substantive + 2 doc** (336–393).

## Faithfulness check

Single new public theorem this cycle:
`inversePolyTree_mkBroom₃_eq_inversePolynomial`.

- **Entity ID**: no direct textbook entity — this is an infrastructure
  bridge for Phase α'.4.2 Family C migration of
  `inversePolynomial`'s `mk [broom₃]` branch from the explicit
  closed form to a recursive `inversePolyTree` dispatch.
- **Tautology check**: conclusion uses `inversePolyTree` (recursive)
  on LHS and `inversePolynomial` (pattern-match) on RHS — distinct
  symbols; equality is non-trivial. NOT vacuous. After B.2's body
  migration both sides reduce definitionally to the same
  `inversePolyTree (mk [broom₃]) f` term, so the bridge is the
  identity-of-call-sites at this branch, but the unfold + rewrite
  chain does real work to align the two recursion shapes.
- **Identity check**: proof is the canonical `unfold + 5 × if_neg
  + if_pos rfl` pattern from cycle 391; does substantive unfolding
  to align the two recursion shapes. Not a hypothesis re-export.
- **Hypothesis strength check**: only hypothesis is `f : RT → ℝ`
  (function-level). No extra strengthening over cycle 391's parallel
  bridge.

For the `inversePolynomial` body migration: not a new theorem; the
value of `inversePolynomial (mk [broom₃]) f` is unchanged — cycle
392's `inversePolyTree_mkBroom₃` already proved the dispatch matches
the 5-term closed form verbatim, so all 4 downstream consumers
(calibration witness, Phase β bridge, Phase γ branch, plus the new
bridge B.1 itself) compose correctly through this rewrite.

For the three consumer updates (B.3 / B.4 / B.5): no new theorems
introduced; existing proof chains extended by one or two
`inversePolyTree_mkBroom₃` rewrites to bridge to the post-migration
RHS. Faithfulness preserved by construction since the cycle 392
calibration is value-preserving.

## Dead ends

None — the cycle 391 template ported verbatim with no surprises.
The only judgment call was the `if_neg` arm count (5 for cycle 393
vs 6 for cycle 391), verified by reading the current
`inversePolynomial` body before writing the bridge.

## Discovery

- The `mk [broom₃]` branch sits at position 6 in `inversePolynomial`
  (one slot earlier than `mk [vertex, cherry]` at position 7). The
  fixed if-chain ordering — vertex, cherry, broom₃, mk[cherry],
  bushy, mk[broom₃], mk[vertex,cherry], mk[mk[cherry]] — directly
  determines the `if_neg` arm count for every Family A/C bridge.
  Cycle 394+ can predict counts at sight: `mk [mk [cherry]]` is
  position 8 → 7 `if_neg`s; future `bushy`/`mk [cherry]`/`mk
  [cherry, cherry]` etc. positions depend on where they sit in the
  current chain (and whether their branch has already migrated).
- The cycle 392 `inversePolyTree_mkBroom₃` calibration witness's
  value-preserving guarantee is what makes the Phase α'.4.2 ladder
  a mechanical port rather than a re-derivation: each migration
  cycle only needs to wire a 4-line `rw` chain through 5 sites
  (the bridge + 3 consumers + the body itself), provided the
  prior cycle's calibration matches the pre-migration explicit
  form.
- The double `inversePolyTree_mkBroom₃` rewrite in the Phase γ
  branch (`rw [..., if_pos rfl, inversePolyTree_mkBroom₃,
  inversePolyTree_mkBroom₃, hv, hc, hb, hmc, hmb]`) parallels
  cycle 391's `inversePolyTree_mkVertexCherry, inversePolyTree_mkVertexCherry`
  — the second rewrite fires on the `g` side after the first
  rewrites the `f` side, both within the same `rw` block. This
  is structurally cleaner than a `rw` followed by a `conv =>`
  block targeting the `g` side specifically.

## Suggested next approach

Per strategy §H (and the cycle 392 worker's prior recommendation):

* **Cycle 394 (next substantive ship)**: extend `monochildCrossTerm`
  for `c = mk [cherry]` branch using cycle 378's closed form
  `v⁴ − 3v²c + c² + 2vm − M_mkMkCherry`. The delta from the naive
  body `-(v · inversePolyTree (mk [cherry]) f) - f (mk [mk [cherry]])`
  needs precise computation. Ship `inversePolyTree_mkMkCherry`
  calibration witness alongside; estimated ~50 LOC.
* **Cycle 395+**: continue Phase α'.4.2 per-tree migrations
  (`bushy` is Family B / position 5 → 4 `if_neg`s; `mk [cherry]`
  is Family A / position 4 → 3 `if_neg`s; etc.) until all 8 ladder
  trees dispatch through `inversePolyTree`. Then Phase β/γ
  consumers can be simplified (their explicit case-splits collapse
  to a single dispatch through the recursive def), and the cycle
  365 grandfathered sorry at `Section422.lean:2272` becomes
  attackable via the unified recursive structure.
* **Do NOT attempt yet**: the cycle 365 grandfathered sorry (still
  blocked on Phase α'.4.2 closure for all 8 trees); cross-term
  extension to `c = mk [mk [cherry]]` (further down the ladder);
  `Section441.lean` (GPFS-blocked); new textbook entities (closure
  path is Phase α'.4 completion, not new entities).
