# Cycle 375 Results

## Worked on

Phase β.1 of `def_422B_subLemmaA_inductive_plan.md` (cycle 373
scoping doc; cycle 375 strategy §C). Shipped **5 new axiom-clean
theorems** in `OpenMath/Chapter4/Section422.lean` (lines 4310–4426,
appended just before the closing
`end OpenMath.Chapter4.Section422`):

1. `elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex`
2. `elementaryWeightQ_phi_inv_eq_inversePolynomial_cherry`
3. `elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃`
4. `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry`
5. `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder`
   (aggregator over the four-tree disjunction)

Each per-tree bridge states
`elementaryWeightQ_phi η_q⁻¹ t = inversePolynomial t
(elementaryWeightQ_phi η_q)` and reduces by `unfold +
rw [if_neg... if_pos rfl] + exact <cycle 341/367/368/369 theorem>`.

The cycle 365 grandfathered sorry at line 2279 is untouched.

## Approach

Per the cycle 375 strategy's bottom-line directive (§J), shipped
exactly the 4 per-tree bridges plus the optional aggregator (§C.5).

Implementation steps:

1. Pre-flight (per §F): verified that
   `elementaryWeightQ_phi_inv_vertex` (line 415),
   `elementaryWeightQ_phi_inv_cherry` (line 2376),
   `elementaryWeightQ_phi_inv_broom₃` (line 2538), and
   `elementaryWeightQ_phi_inv_mkCherry` (line 2772) all have the
   expected signature `(η_q : Quotient PhiEquivalent.setoidSigma) :
   ...`.
2. Confirmed the four cycle 374 calibration `example`s compile at
   HEAD (they do — the `unfold + rw [if_*]` recipe is established).
3. Wrote the 4 per-tree bridges, each following the template
   `unfold inversePolynomial; rw [if_neg (by decide), …, if_pos
   rfl]; exact elementaryWeightQ_phi_inv_<tree> η_q`.
4. Wrote the aggregator using `rcases ht with h | h | h | h <;>
   subst h` and four `exact` applications.
5. Used the fully qualified `OpenMath.Chapter3.Section310.RootedTree.mk
   [RootedTree.cherry]` for the `mk [cherry]` literal, per cycle
   374 Discovery #1.
6. `lake env lean OpenMath/Chapter4/Section422.lean` — clean exit
   (only the cycle 365 grandfathered sorry warning at line 2272).
7. `lake build OpenMath.Chapter4.Section422` — clean rebuild
   (8037/8037 jobs, 372 s).
8. `#print axioms` on each of the 5 new theorems via a temporary
   axiom-check file (`OpenMath/Chapter4/axiom_check_cycle375.lean`)
   confirmed `[propext, Classical.choice, Quot.sound]` only — i.e.
   no `sorryAx`, no project-specific axioms.

## Result

**SUCCESS** —

- `lake env lean OpenMath/Chapter4/Section422.lean` exits clean
  (only the pre-existing cycle 365 grandfathered sorry warning).
- `lake build OpenMath.Chapter4.Section422` rebuilds clean
  (no errors, 8037/8037 jobs).
- `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (unchanged
  from HEAD; same 1 code sorry + 4 docstring mentions).
- `#print axioms` on each of the 5 new theorems →
  `[propext, Classical.choice, Quot.sound]` (standard only).

The §422 axiom-clean streak advances from 39 substantive + 1 doc
(through cycle 374) to **40 substantive + 1 doc** (through cycle
375). The streak is preserved.

## Faithfulness check

### Five new `theorem`s — per-tree and aggregator bridges

These five theorems are **internal infrastructure** for the multi-cycle
`def:422B` formalization (Sub-lemma A → Sub-lemma B → `def:422B`
chain). They are not textbook-named concepts; no individual
`formalization_data` entity exists. Their role is the Phase β.1
deliverable promised by the cycle 373 scoping doc §5 and explicitly
called for by cycle 374's "Suggested next approach" §A.

Each per-tree bridge re-states that, on the matched tree,
`elementaryWeightQ_phi η_q⁻¹ t` equals the closed-form polynomial
`inversePolynomial t (elementaryWeightQ_phi η_q)` — i.e. the cycle
374 `inversePolynomial` definition agrees with the cycle 341 / 367
/ 368 / 369 closed forms on the four trees.

**Tautology check**: none of the five theorems have the conclusion
appearing verbatim as a hypothesis. The only hypothesis is `η_q :
Quotient PhiEquivalent.setoidSigma` (plus `t : RT` and `ht :
disjunction` for the aggregator). The conclusion is an `Eq`
between two `ℝ`-valued expressions, neither of which appears as a
hypothesis.

**Identity check**: each per-tree proof is `unfold + rw chain +
exact <cycle ladder theorem>`. The `exact <cycle ladder theorem>`
step is mathematically substantive — it dispatches to a non-trivial
closed-form theorem (the cycle 367/368/369 proofs are each ~100–200
lines of `Quotient.inductionOn` + sum-of-products manipulation).
The bridge is NOT a vacuous re-export — it converts the
mathematical content of those closed forms into the
`inversePolynomial`-typed statement required by Phase β.

**Hypothesis strength check**: each bridge has exactly the
hypothesis `η_q : Quotient PhiEquivalent.setoidSigma` (the
quotient-level group element). No additional preconsistency,
stability, or order hypotheses are imposed — matching the
underlying cycle 341/367/368/369 theorems.

**Definition smuggling check**: no new `def`s, `structure`s, or
`class`es introduced this cycle. All five are theorems consuming
the cycle 374 `inversePolynomial` definition. Not applicable.

**Absent theorem check**: each `exact elementaryWeightQ_phi_inv_<tree>`
call has been verified to resolve to the actual cycle 341/367/368/369
theorem (file lines confirmed via `grep` at the start of cycle).

## Dead ends

None this cycle. The cycle 374 worker's discovery (the `unfold + rw
[if_neg (by decide)... if_pos rfl]` recipe) ported verbatim from
the four calibration `example`s to the four per-tree bridges. The
only new ingredient was the trailing `exact <cycle ladder theorem>`
to close the residual goal after the `if_*` cascade reduces
`inversePolynomial`.

The fully qualified `OpenMath.Chapter3.Section310.RootedTree.mk
[RootedTree.cherry]` was used from the start (per cycle 374
Discovery #1), avoiding any name-resolution detour.

## Discovery

1. **Sign normalization is `rfl` after `if_pos`**: cycle 341
   `elementaryWeightQ_phi_inv_vertex` states the conclusion as
   `... = - elementaryWeightQ_phi η_q RootedTree.vertex` (Lean
   syntactic `Neg.neg`), while `inversePolynomial`'s `vertex`
   branch unfolds to `-(elementaryWeightQ_phi η_q RootedTree.vertex)`
   (parenthesized). These are literally the same term in Lean's
   AST after elaboration — `exact` closes without need for `Eq.symm`
   or `neg_neg` rewrites. Confirms that future Phase β.x bridges
   should not need any sign-bookkeeping after the `if_*` cascade.

2. **The aggregator pattern `rcases <disjunction> with h | h | h |
   h <;> subst h` plus `exact` per branch composes cleanly with
   the per-tree bridges**. This means future Phase β.x aggregators
   over an N-tree ladder can use the same recipe with N branches
   and N exacts — no need for `Decidable.casesOn` or other
   constructor-level machinery.

3. **Phase γ feasibility check**: `inversePolynomial` being a
   pattern match (not a recursion) means
   `inversePolynomial_eq_of_subtree_agreement` (Phase γ in the
   issue plan §5) reduces to four trivial case splits: each
   matched closed form's RHS depends only on `f` at strict
   subtrees of the matched tree (by inspection of the four
   matched closed forms `vertex`, `cherry`, `broom₃`,
   `mk [cherry]`). This is shorter than Phase β.1 itself,
   confirming the issue plan §I cycle 376 outlook estimate.

## Suggested next approach

For the cycle 376 planner. Per the issue plan §5–§7 and §I:

**Option A — Phase α.2 (3 more pattern-match branches)** —
extend `inversePolynomial` to the three remaining cycle 370–372
closed forms (`bushy`, `mk [broom₃]`, `mk [vertex, cherry]`).
Three additional `else if` branches in the definition plus three
additional Phase β.2 per-tree bridges. ~30–50 LOC total. Strictly
easier than the alternatives, advances Phase α/β simultaneously.

**Option B — Phase γ (subtree-agreement of `inversePolynomial`)** —
ship `inversePolynomial_eq_of_subtree_agreement`: if `f` and `g`
agree on every strict subtree of `t`, then `inversePolynomial t f
= inversePolynomial t g`. Per Discovery #3 above, this reduces to
four trivial case splits given the current pattern-match form.
This is Phase γ in the issue plan §5; cycle 376 may ship it in
~50–80 LOC.

**Option C — Phase β.2 plumbing** — if any downstream Sub-lemma A
body work in cycles 377+ requires the per-tree bridges as
`∀ t : RT, ...` rather than the on-ladder form, ship the
`Quotient.lift`-style wrapper now. Likely **not needed** since the
aggregator from cycle 375 covers the use case.

**Recommended cycle 376 plan**: **Option B (Phase γ)**. Given
Discovery #3's "shorter than Phase β.1" estimate, Phase γ is the
highest-leverage single-cycle deliverable. Option A is easier but
provides less Sub-lemma A progress; Option C is unlikely to be
needed.

**Do NOT** in cycle 376:

- Discharge the cycle 365 grandfathered sorry at line 2279 (still
  Phase ε, projected cycle 378+).
- Pivot to a fresh entity (`def:422B` remains the active
  multi-cycle target).
- Add new sorries beyond the cycle 365 grandfathered one.
- Re-prove the cycle 341/367/368/369 closed forms — the Phase β.1
  bridges quote them directly.
