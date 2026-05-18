# Cycle 385 Results

## Worked on

§422 Phase α'.4 Family C scoping doc (markdown-only deliverable per
cycle 385 strategy). No Lean changes. The scoping doc distills the
three Family C closed-form witnesses (cycles 371, 372, 384) into a
concrete multi-cycle plan for a unified `inversePolyTree` recursion
that handles heterogeneous-children trees, generalising cycle 380's
Family A `inversePolyChain` and cycle 382's Family B
`inversePolyBroom`.

## Approach

Authored a single new markdown file
`.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
(621 lines) covering the nine sections specified in the cycle 385
strategy:

* §1 Status & blocker — Phase α' progress to date; cycle 365
  grandfathered sorry context; why Phase α'.4 unblocks closure.
* §2 The three Family C witnesses (full catalog) — closed forms
  transcribed verbatim from `Section422.lean` cycles 371/372/384,
  with σ(t), order, leading sign, self-term sign, and cross-term
  coefficients tabulated.
* §3 Structural observations — §3.1 per-child product pattern, §3.2
  the four-block decomposition of binary-children products
  (const·const, const·A-sum, A-sum·const, bilinear A-sum·A-sum), §3.3
  why Families A and B miss the bilinear cross-term.
* §4 Conjectured `inversePolyTree` recursion — Variant V4 sketch +
  `bichildPolynomial` helper proposal + higher-arity (k ≥ 3)
  deferral.
* §5 Phase decomposition — α'.4.0 (one more data point), α'.4.1
  (recursive def ship), α'.4.2 (Family C branch migration), with
  cycle assignments and LOC budgets.
* §6 Risk assessment — 7 risks rated, R1 (under-determined recursion)
  flagged HIGH with cycle 386 mitigation.
* §7 Cycle 386 entry point — `mk [broom₃, cherry]` (order 6,
  asymmetric two-non-leaf-children), 10–12 RHS terms predicted,
  ~250 LOC budget.
* §8 Cross-references — predecessor scoping docs (cycles 336, 357,
  373, 379), Lean ship line numbers, task results, source material,
  memory cross-links.
* §9 Self-reference & success criteria — cycle-by-cycle outlook
  through Phase α'.5; what cycle 385 deliberately does NOT do.

Also bumped `lean_status.json` `def:422B` row's `cycle_completed_at`
to 385 and appended a cycle 385 doc-ship note (status remains
`partial`); appended a cycle 385 update to `plan.md`'s `def:422B`
row.

Process: cross-checked each closed form against the actual theorem
statements in `Section422.lean` (cycle 371 lines 3397–3624; cycle
372 lines 3798–4051; cycle 384 lines 4655–4961) before transcribing.
All elementary-weight kernels and sign conventions match.

## Result

SUCCESS — single deliverable shipped, no Lean changes, all
bookkeeping updated.

* `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
  — 621 lines (within the 400–600 strategy range, with §3.2 cross-term
  detail pushing slightly over).
* `extraction/formalization_data/lean_status.json` — `def:422B`
  cycle_completed_at bumped 383 → 385; status unchanged at
  `partial`; cycle 385 doc-ship note appended.
* `plan.md` — `def:422B` row gets cycle 385 doc-ship note appended.
* No Lean file modifications (`git diff --stat` shows only
  `.prover-state/`, `extraction/formalization_data/`, and `plan.md`).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (unchanged;
  4 docstring + 1 grandfathered code sorry at line 2279).
* §422 axiom-clean streak advances: 48 substantive + 1 doc
  (cycles 336–384) → **48 substantive + 2 doc** (cycles 336–385).

## Faithfulness check

No new `def` or `theorem` introduced this cycle (markdown-only ship).
The closed-form transcriptions in §2 of the scoping doc are
verbatim quotes from cycles 371/372/384 ship statements; cross-checked
against `Section422.lean` line numbers cited in §8 of the scoping
doc.

Tautology / identity / definition-smuggling / hypothesis-strength
checks all trivially pass: zero new Lean content.

## Dead ends

None. The cycle was deliberately scoped to a single markdown
deliverable per the cycle 373 / 379 precedent of zero-Lean scoping
cycles. No exploratory Lean attempts were made (cycle 385 strategy
§"Priority 3 — NO LEAN CODE THIS CYCLE" forbade them).

One mild ambiguity surfaced while transcribing §3.2 (block-(4)
bilinear cross-term): the *exact* mechanism by which the cycle 384
closed form contains `+ 2 · Φ_η(cherry) · Φ_η(mk [cherry])` is
empirically unclear from inspection of the 8-term polynomial alone.
The scoping doc flags this ambiguity in §4.2 and proposes the cycle
386 `mk [broom₃, cherry]` witness as the disambiguation mechanism.
This is not a dead end — it is the design's known unknown, which
is exactly what cycle 386 is for.

## Discovery

D1. **The cycle 384 closed form features two distinct
`v² · (single-elementary-weight)` terms with different coefficients**
(`−v² · b'` and `−2 · v² · m`), in contrast to the cycle 371/372
closed forms where each elementary-weight kernel appears at most
once. Hypothesis: when both children of `mk [t₁, t₂]` are
non-leaf and identical, the bilinear cross-term double-counts (the
factor `2` on `v² · m`) certain depth-2 contributions. The cycle
386 asymmetric witness `mk [broom₃, cherry]` will test whether
*distinct* non-leaf children produce single-counted versions of
each contribution. This is the load-bearing data point for the
Phase α'.4.1 recursive design.

D2. **The self-term sign is uniformly `−1` across all three Family
C witnesses**, regardless of order parity. This is consistent with
the cycle 358 `elementaryWeightQ_phi_inv_mk` structure: the
inverse-class evaluation at any `mk [...]` tree subtracts
`Φ_η(t)` directly, with no additional sign flip from the
recursion. (Family A's `inversePolyChain` and Family B's
`inversePolyBroom` both also have `−1` self-term coefficients —
this is structural, not coincidental.)

D3. **Cross-term coefficient signs are NOT uniform within an
order** — cycle 384's order-5 closed form has coefficients
`+4, −3, −1, −2, +2, +2` (six cross-terms with mixed signs), while
cycle 371/372's order-4 closed forms have uniformly `−3` for the
`v² · c` cross-term and varied positive coefficients elsewhere.
The Phase α'.4.1 recursive design must derive these coefficients
algorithmically from the bilinear-expansion combinatorics, not
catalog them as constants.

D4. **Section422.lean's `inversePolynomial` is now mid-refactor**:
Phases α.1 (cycle 374) shipped the if-then-else cascade; Phases
α'.1 / α'.3 (cycles 380–383) migrated Family A (`vertex`,
`cherry`, `mk [cherry]`, `mk [mk [cherry]]` branches) to dispatch
to `inversePolyChain` and Family B (`broom₃`, `bushy`) to dispatch
to `inversePolyBroom`. The remaining Family C branches
(`mk [broom₃]`, `mk [vertex, cherry]`, `mk [cherry, cherry]`) still
embed their closed-form expressions inline — these are the targets
of Phase α'.4.2 (cycle 388+) migration. The scoping doc's §5.3
documents this migration explicitly.

## Suggested next approach

**Cycle 386 entry (per scoping doc §7)**: ship the 10th-tree
Family C witness `Φ_{η_q⁻¹}(mk [broom₃, cherry])`.

* Target tree: `mk [broom₃, cherry]` (order 6, σ = 1, asymmetric
  two-non-leaf-children).
* Predicted RHS shape: 10–12 polynomial terms in 7–8 distinct
  elementary-weight kernels.
* Leading sign: `+v⁶` (order-6 even parity).
* Self-term: `−Φ_η(mk [broom₃, cherry])`.
* New kernels potentially introduced: `mk [vertex, broom₃]` (the
  block-(4) cross-term analogue of cycle 384's surprise).
* Proof template: cycle 384's `mk [cherry, cherry]` recipe with the
  binary product over `(broom₃, cherry)` instead of
  `(cherry, cherry)`; both factor unfolds now differ (no squaring
  shortcut). Inner cherry-factor via cycle 367's `h_dws_cherry`;
  inner broom₃-factor via cycle 368's `h_dws_broom₃` (extended for
  the inverse).
* LOC budget: ~250 LOC.

Stretch (if cycle 386 has slack): ship the R2 symmetry-pair
`mk [cherry, broom₃]` (~100 LOC additional) to empirically confirm
the bilinear block's permutation-invariance.

**Cycle 387+ outlook** (per scoping doc §5.2 / §5.3):

* α'.4.1 ships recursive `inversePolyTree` (Variant V4) +
  `bichildPolynomial` helper, with 10 calibration witnesses
  matching each currently-shipped closed form. ~300–500 LOC,
  potentially across two cycles.
* α'.4.2 migrates `inversePolynomial`'s Family C branches to
  dispatch to `inversePolyTree`. ~100–150 LOC, parallel to
  cycles 381 / 383.
* Post-Phase α'.4: Phase α'.5 handles k ≥ 3 heterogeneous-children
  trees (deferred per §4.3); then Phase β/γ extension closes
  cycle 365's grandfathered sorry at `Section422.lean:2279`.

**Streak preservation**: the §422 axiom-clean streak now stands at
48 substantive + 2 doc cycles (336–385). The cycle 386 ship is on
the §422 track; the next pivot opportunity is post-Phase α'.4.2,
estimated 4–5 cycles out. No fresh-entity pivot recommended
before then (compound momentum on the `def:422B` closure track
remains the highest-EV trajectory).
