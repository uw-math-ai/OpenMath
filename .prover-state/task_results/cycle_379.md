# Cycle 379 Results

## Worked on

§422 Phase α' scoping doc (predecessor to recursive `inversePolynomial`
design). Sole deliverable: a markdown scoping document at
`.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` (903
lines, 11 sections §1–§11) per cycle 379 strategy Priority 1.

This is a zero-Lean cycle following the cycle 373 precedent
(`def_422B_subLemmaA_inductive_plan.md`, 1399 lines), authorised by
the cycle 378 worker's Option A recommendation and the cycle 379
planner's explicit Priority 1 directive.

## Approach

Followed the cycle 373 scoping-doc template:

* §1 Status & blocker — pivot rationale from cycle 378 D1 discovery,
  reference to cycle 373 zero-Lean precedent.
* §2 Current `inversePolynomial` definition — quoted the 8-way
  `if-then-else` shape from `Section422.lean:4651–4697` verbatim,
  catalogued all 8 matched branches with their orders and cycle
  numbers.
* §3 Closed-form catalog — 8-row table with order, σ(t), and closed
  form per tree. σ(t) values verified by `Section301.lean`
  reference theorems (lines 351, 358, 370, 382, 394, 407, 419 —
  all `rfl`).
* §4 Structural pattern analysis — split into Family A
  (single-child ladder), Family B (symmetric leaf brooms), Family
  C (heterogeneous children). Family A pattern is the cycle 378 D1
  insight; Family B is the binomial expansion (with sign
  conventions to be nailed down in cycle 380); Family C remains
  the hard open problem.
* §5 Three recursive shape variants (V1 partition-based, V2 fold-
  over-children, V3 strong-induction explicit formula). V2
  recommended as cycle 380's first attempt.
* §6 Project-hook inventory — all 8 closed-form theorems, 8
  corollaries, 8 Phase β bridges, Phase γ theorem, and termination
  infrastructure with verified line numbers at HEAD `d072990`.
* §7 Gap inventory — 6 gaps (G1–G6) prioritised CRITICAL/HIGH/
  MEDIUM with mitigations.
* §8 4-phase decomposition (α'.1 → α'.4) targeting closure of the
  cycle 365 grandfathered sorry at `Section422.lean:2279` by cycle
  384+.
* §9 Risk assessment — 6 risks (R1–R6) with severity and rollback
  precedents (cycles 200/201, 149/150).
* §10 Cycle 380 entry point — concrete 5-step first task.
* §11 Self-reference & cross-links — predecessor scoping docs,
  cycle 378 cross-links, source material, Lean files, memory
  cross-links.

Aristotle: not used this cycle. The deliverable is markdown-only;
no proof obligations to delegate. Per the strategy's "Things to
AVOID" §, Aristotle's free compute is better reserved for the cycle
365 grandfathered sorry (Phase α'.4 scope, cycle 384+).

## Result

**SUCCESS** — scoping doc shipped at
`.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` with
all 11 required sections, 903 lines (within the strategy's 600–900
target). `grep -c sorry OpenMath/Chapter4/Section422.lean` returns
5 (unchanged from cycle 378). No Lean code touched; build state
unchanged.

Verification checklist (from strategy):

1. Scoping doc exists at prescribed path ✓
2. All cited file paths and line numbers verified by `grep -n` ✓
   (in particular §6 hook inventory and §3 σ(t) values)
3. 8-tree catalog table complete and matches `Section422.lean`
   verbatim ✓
4. Cycle 373 precedent reference explicit ✓ (in §1, §5
   recommendation, §11 cross-links)
5. `lake env lean OpenMath/Chapter4/Section422.lean` NOT run this
   cycle (doc-only) ✓
6. `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5 ✓
   (unchanged)
7. Standard cycle bookkeeping (this file + heartbeat +
   history.jsonl) — in progress

§422 axiom-clean streak: **43 substantive + 2 doc** (cycles 336–379;
cycles 373 and 379 are the doc-only entries).

## Faithfulness check

No new `def`, `structure`, or `theorem` was introduced this cycle.
The deliverable is a markdown scoping document; faithfulness
checklist sections (tautology / identity / definition smuggling /
hypothesis strength checks) are not applicable.

The scoping doc itself does include conjectured closed-form
formulas (§4 Family B binomial sum, Family A depth-4 prediction).
These are flagged as **conjectures to be verified in cycle 380+**,
not as proved facts. The §4 spot-checks deliberately exhibit a
sign-convention error mid-derivation to highlight G1 (Family B
closed-form derivation) as a CRITICAL gap for cycle 380.

## Dead ends

None. The scoping doc shipped on first draft per the strategy's
prescription; the only mid-draft refinement was the §4 Family B
sign-convention spot-check (which exposed G1 as a real gap rather
than a clean recipe — this is preserved in the doc as a flagged
research question).

## Discovery

### D1 — Family A coefficient counts may follow Catalan numbers

The 4 single-child trees `{vertex, cherry, mk[cherry],
mk[mk[cherry]]}` have closed-form coefficient counts `1, 2, 3, 5`.
This is consistent with the Catalan numbers `C_n = 1, 1, 2, 5, 14,
...` (after a depth-0 anomaly) — the cycle 378 worker noted this
pattern but did not specify Catalan. The cycle 379 §4 conjectured
a depth-4 closed form with 7 terms, which does NOT match Catalan
(which predicts 14) but does match a "previous-depth + 2 new mixed
terms" extrapolation.

**Actionable**: cycle 380 should ship `mk [mk [mk [cherry]]]`
(depth-4 single-child) as a 9th closed-form data point. If the
result is 7 terms, the linear extrapolation is correct. If it's
13–14 terms, the Catalan conjecture is favoured. Either result
narrows the recursive shape design.

### D2 — Family C cross-term mixing is the load-bearing open problem

The §4 analysis of cycles 371 and 372 (the two Family C ladder
trees) revealed that the closed-form cross-terms (`+2vm` in
`mk [broom₃]`, `+c²` and `+vm` in `mk [vertex, cherry]`) cannot
be predicted by Family A or B alone. This is gap G2 in §7 and
risk R6 in §9.

**Implication**: Phase α'.1's recursive shape (V2 candidate)
must include an explicit Family C cross-term recipe, OR fall back
to a partial V1 with Family C cases listed explicitly. The cycle
380 worker should plan for V2 failing on Family C and have V1 as
a fallback.

### D3 — σ(t) is provably absent from the recursive shape

The cycle 373 scoping doc §4.5 discovery slot ("σ does NOT appear
in any closed form") is fully preserved through cycle 378. The
recursive `inversePolynomial` must therefore depend only on `f
: RT → ℝ` evaluated at subtrees of `t`, not on any combinatorial
invariant of `t` itself.

**Implication**: Variant V3 (strong-induction explicit formula
with `subtreeMultiset` enumerator) cannot use σ(t) in its
coefficient table. The enumerator must produce real-number
coefficients via subtree counting only — likely related to
Connes-Kreimer Hopf algebra antipode coefficients (signed forest
sums) but with rational coefficients, not σ-dependent.

## Suggested next approach

### Option A (RECOMMENDED) — Phase α'.1 implementation (cycle 380)

Proceed per the §10 cycle 380 entry point. Cycle 380's first task
is to re-read cycle 358's `_inv_mk` proof body and the 8 closed-form
proofs, then derive the Family A and Family B closed-form formulas
precisely (G1, gap-CRITICAL). With those in hand, attempt Variant
V2 (fold-over-children recursive shape) with per-child contribution
formula. Verify on all 8 ladder trees by `unfold + ring` BEFORE
committing the recursive definition.

If V2 fails on Family C (most likely candidate: `mk [vertex,
cherry]` with the `c²` term), cycle 380 ships a partial Variant V1
(Family A only) with documented Family B/C gaps for cycle 381.

### Option B (acceptable fallback) — Targeted 9th tree as G2 disambiguation

If cycle 380's worker estimates Phase α'.1 implementation cannot fit
in one cycle (e.g., the Family B / C derivations need more than half
a cycle each), ship a "9th tree" closed form as targeted Family C
data acquisition instead. Recommended candidate:
`mk [cherry, cherry]` (order 5, σ = 2) — tests Family C with two
identical non-leaf children, which is the simplest unexplored
case.

This is the cycle 378 worker's "Option B" (rejected by cycle 379
planner as treadmill, but acceptable as targeted Phase α' prep
when explicitly scoped as G2 disambiguation).

### Option C (NOT recommended) — Pivot to a different entity

The cycle 378 task results note `def:422B` is at a natural
strategic checkpoint, but the cycle 379 scoping doc explicitly
plans the next 4–6 cycles around Phase α'. Pivoting mid-stream
would discard the scoping investment. Re-evaluate after Phase α'
lands (cycle 384+).

### Risk register entry for cycle 380

* **R1 (HIGH)** — V2 recursive shape may not match all 8 closed
  forms by `rfl`. Verify via calibration witnesses BEFORE
  committing the recursive `def` ship.
* **R6 (MEDIUM)** — Family C cross-term mixing recipe (G2) may
  require new combinatorial machinery. Fall back to partial V1
  (Family A only) if cycle 380 cannot find a clean Family C
  recipe.
* **R4 (LOW)** — Well-founded recursion termination should be
  automatic via cycle 343's `WellFoundedRelation` instance +
  `order_lt_of_mem_children`. If `decreasing_by` annotations are
  needed, the precedent is straightforward.
