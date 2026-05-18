# Cycle 381 strategy — Phase α'.2: Family A bridge migration

## TL;DR

Ship **Option A from the cycle 380 task results** — Phase α'.2
*Family A bridge migration*. Modify `inversePolynomial`
(`OpenMath/Chapter4/Section422.lean:4651`) so its four Family A
branches (`vertex`, `cherry`, `mk [cherry]`, `mk [mk [cherry]]`) dispatch
to cycle 380's recursive helper `inversePolyChain k f` for
`k = 0, 1, 2, 3`. Then update the four Family A calibration witnesses,
the four Family A Phase β bridges, and the four Family A branches of
Phase γ. Family B / Family C branches (`broom₃`, `bushy`,
`mk [broom₃]`, `mk [vertex, cherry]`) stay untouched. This validates
that cycle 380's convolution recursion is the canonical Family A path
and compounds the cycle 380 investment. Axiom-clean; sorry count
unchanged at 5 (1 code + 4 docstring).

This is exactly what the cycle 380 worker recommended in their
"Suggested next approach §Option A" and is the lowest-risk
single-cycle continuation.

## §A — Context inherited from cycles 374–380

The Phase α' (recursive `inversePolynomial` design) ladder so far:

* **Cycle 374** (Phase α.1): shipped 8-way `if-then-else`
  `inversePolynomial` covering 4 Family A trees explicitly.
* **Cycles 375, 376, 377, 378** (Phase α.2–4 + Phase β.1–4 + Phase γ):
  extended the 8-way match to all 8 ladder trees (Family A + Family B +
  Family C `mk [broom₃]`, `mk [vertex, cherry]`, `mk [mk [cherry]]`),
  shipped Phase β bridges, shipped Phase γ subtree-agreement theorem.
* **Cycle 379** (zero-Lean): scoping doc
  `def_422B_phase_alpha_prime_scoping.md` decomposing Phase α' into
  4 phases (α'.1–α'.4).
* **Cycle 380**: shipped `inversePolyChain : ℕ → (RT → ℝ) → ℝ` as a
  recursive helper for Family A single-child ladder trees
  (`chainTree n := mk^n[vertex]`), plus 4 closed-form theorems
  (`inversePolyChain_zero/_one/_two/_three`) and 4 bridge theorems
  (`inversePolyChain_{k}_eq_inversePolynomial`) showing the helper
  equals `inversePolynomial (chainTree k) f` on the 4 Family A trees.

§422 axiom-clean streak: **44 substantive + 1 doc** (cycles 336–380).
Single grandfathered sorry at `Section422.lean:2272` (cycle 365's
`powRep_sum_eq_of_strict_subtree_agreement` general body).
Section422.lean: ~5840 LOC. `grep -c sorry` returns 5 (4 docstring + 1
code).

Cycle 380 ships a *parallel* definition that re-derives the Family A
pattern-match cases recursively. The migration is the explicit
follow-up the cycle 380 worker recommended.

## §B — Concrete deliverable for cycle 381

### Step 0 — Move the cycle 380 block before `inversePolynomial`

`inversePolyChain` is currently defined *after* `inversePolynomial`
(cycle 380 inserted the new `### Phase α'.1 (cycle 380)` section at
line ~4931, after the existing `inversePolynomial` definition at line
4651). To call `inversePolyChain k f` from `inversePolynomial`'s body,
the cycle 380 block (`chainTree`, `chainTree_one/_two/_three`, and
`inversePolyChain` together with its 4 closed-form theorems) must be
moved *before* the `inversePolynomial` definition.

Do this as a pure text reordering first, verify the file still
compiles via `lake env lean OpenMath/Chapter4/Section422.lean`, then
proceed to Steps 1–5.

**Do NOT** modify the cycle 380 helper or its 4 closed-form theorems
during the move — copy them verbatim. The bridge theorems
(`inversePolyChain_{k}_eq_inversePolynomial`) stay where they are
(after `inversePolynomial`) since they reference both.

### Step 1 — Update `inversePolynomial` (Section422.lean:4651)

Replace the four Family A `if-then-else` branches with
`inversePolyChain k f` calls. The other four branches (Family B/C) stay
verbatim. After the migration:

```lean
noncomputable def inversePolynomial (t : RT) (f : RT → ℝ) : ℝ :=
  if t = RootedTree.vertex then
    inversePolyChain 0 f
  else if t = RootedTree.cherry then
    inversePolyChain 1 f
  else if t = RootedTree.broom₃ then
    -(f RootedTree.vertex) ^ 3
      + 2 * f RootedTree.vertex * f RootedTree.cherry
      - f RootedTree.broom₃                          -- unchanged (Family B)
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry] then
    inversePolyChain 2 f
  else if t = RootedTree.bushy then
    (f RootedTree.vertex) ^ 4
      - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
      + 3 * f RootedTree.vertex * f RootedTree.broom₃
      - f RootedTree.bushy                           -- unchanged (Family B)
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃] then
    ...                                              -- unchanged (Family C)
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry] then
    ...                                              -- unchanged (Family C)
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk
                [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]] then
    inversePolyChain 3 f
  else
    0
```

### Step 2 — Update the 4 Family A calibration witnesses (lines 4704–4757)

Each currently looks like:

```lean
example (f : RT → ℝ) :
    inversePolynomial RootedTree.vertex f = -(f RootedTree.vertex) := by
  unfold inversePolynomial
  rw [if_pos rfl]
```

After the migration, the `if_pos rfl` exposes `inversePolyChain 0 f`
on the LHS, not `-(f vertex)`. Append a trailing
`inversePolyChain_zero` rewrite to close:

```lean
example (f : RT → ℝ) :
    inversePolynomial RootedTree.vertex f = -(f RootedTree.vertex) := by
  unfold inversePolynomial
  rw [if_pos rfl, inversePolyChain_zero]
```

Analogously for cherry / `mk [cherry]` / `mk [mk [cherry]]`, each gains
a trailing `inversePolyChain_{one,two,three}` rewrite. Use the cycle
380 closed-form theorems verbatim — they were proved against
`inversePolyChain`'s recursive body and don't change shape.

### Step 3 — Update the 4 Family A Phase β bridges (lines 5225, 5239, 5254, 5273)

Same pattern as Step 2. For example, for the vertex bridge:

```lean
theorem elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ RootedTree.vertex
      = inversePolynomial RootedTree.vertex (elementaryWeightQ_phi η_q) := by
  unfold inversePolynomial
  rw [if_pos rfl, inversePolyChain_zero]
  exact elementaryWeightQ_phi_inv_vertex η_q
```

Same `inversePolyChain_k` insertion for cherry / `mk [cherry]` /
`mk [mk [cherry]]` bridges.

### Step 4 — Update the 4 Family A branches of Phase γ

`inversePolynomial_eq_of_subtree_agreement` at `Section422.lean:5532`
does an 8-way `by_cases h_<tree>` on `t`. The 4 Family A branches
each unfold `inversePolynomial` then close with `if_pos rfl` plus
`h_closed` rewrites.

After migration, each Family A branch needs an extra
`inversePolyChain_k` rewrite on *each side* (since the LHS and RHS
both invoke `inversePolynomial` for the same tree under different
function arguments `f` and `g`). Concrete pattern for the vertex
branch:

```lean
by_cases h_vertex : t = RootedTree.vertex
· subst h_vertex
  rw [if_pos rfl, if_pos rfl,
      inversePolyChain_zero, inversePolyChain_zero,
      h_closed RootedTree.vertex (le_refl _)]
```

**Important**: the `h_closed _ (le_refl _)` rewrite must come *after*
`inversePolyChain_zero` (which exposes the `-f vertex` form needed by
`h_closed` to fire), not before.

Similarly for cherry / `mk [cherry]` / `mk [mk [cherry]]`. The four
Family B/C branches are unchanged.

### Step 5 — Simplify the 4 cycle 380 bridge theorems

After the migration,
`inversePolyChain_zero_eq_inversePolynomial`,
`inversePolyChain_one_eq_inversePolynomial`,
`inversePolyChain_two_eq_inversePolynomial`,
`inversePolyChain_three_eq_inversePolynomial`
should become trivially `rfl` (both sides definitionally equal).
Update their proof bodies to `:= rfl` (or leave the existing
`unfold + if_*` proof — it will still pass, just less informative).
The recommended form is `by rfl` for explicitness.

Keep the named theorems — they remain useful as anchors and document
the relationship explicitly.

### LOC estimate

~60 LOC total delta:

| Step | LOC delta |
|---|---|
| 0 (move cycle 380 block) | ~0 net (text reorder) |
| 1 (def edit) | ~10 (replace 4 polynomial bodies with helper calls) |
| 2 (4 calibration witnesses) | ~15 |
| 3 (4 Phase β bridges) | ~15 |
| 4 (Phase γ, 4 Family A branches) | ~15 |
| 5 (4 cycle 380 bridges simplified) | ~-5 (proofs shrink) |

All mechanical. No new theorems, no new infrastructure.

## §C — Verification commands

Run in order; abort and document if any fails:

1. After Step 0: `lake env lean OpenMath/Chapter4/Section422.lean`
   exits 0 (verify the reordering compiles before any further edit).
2. After Steps 1–5: `lake env lean OpenMath/Chapter4/Section422.lean`
   exits 0.
3. `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5
   (unchanged from cycle 380; 4 docstring + 1 code sorry).
4. Tautology scanner regex check:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter4/Section422.lean`
   — no hits.
5. `lake env lean OpenMath/Chapter4.lean` (aggregator) exits 0.
6. Axiom-clean spot-check via a scratch file (don't commit):
   ```
   #print axioms inversePolynomial
   #print axioms inversePolynomial_eq_of_subtree_agreement
   #print axioms elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex
   #print axioms elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry
   #print axioms elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder
   ```
   All should return `[propext, Classical.choice, Quot.sound]` only.

## §D — What NOT to try

Explicitly listed failed / dead-end approaches:

1. **Do NOT attempt Variant V2 (fold-over-children) for
   `inversePolynomial`.** The cycle 380 worker investigated this and
   could not produce a unified recursive shape covering all 8 closed
   forms by `unfold + ring`. The scoping doc §10 lists this as the
   worst-case fallback; cycle 380's Family A V1 helper is what shipped.
   Do not attempt to redesign `inversePolyChain` itself.

2. **Do NOT derive a Family B closed form** (e.g.
   `inversePolyBroom k f = -Σⱼ C(k,j)(-v)^(k-j)·wⱼ`) in this cycle.
   The scoping doc §4.5 / §6.G1 documents sign-convention errors in the
   cycle 379 spot-check derivations. This is **Option B** of the cycle
   380 task results and is medium-risk multi-cycle work — defer to
   cycle 382+.

3. **Do NOT attempt the cycle 365 grandfathered sorry**
   (`powRep_sum_eq_of_strict_subtree_agreement` at line 2272). This is
   Option C of the cycle 380 task results (high-risk Phase α'.4 work).
   Cycle 381's job is to validate the Family A recursion via migration,
   not to close the multi-cycle target.

4. **Do NOT remove or alter `inversePolyChain`'s definition.** Cycle
   380 proved 4 closed-form theorems against it; changing the recursion
   shape would invalidate those theorems. The migration consumes the
   cycle 380 helper *as-is*.

5. **Do NOT introduce sorries.** Per the cycle 200/201 and cycle
   149/150 rollback precedents, sorry-first scaffolds without a
   single-cycle closure path get rolled back. Cycle 381 must ship
   axiom-clean or skip.

6. **Do NOT touch Family B / Family C branches** of `inversePolynomial`
   (`broom₃`, `bushy`, `mk [broom₃]`, `mk [vertex, cherry]`). These
   are not yet expressible via `inversePolyChain`. The cycle 381 ship
   is *partial* migration: only the four Family A branches change.

7. **Do NOT touch `Section441.lean` or any GPFS-blocked file.**
   `cycle_182_gpfs_slowness.md` documents 43+ consecutive Section441
   compile timeouts; skip per project policy. All cycle 381 work lives
   in `Section422.lean`.

8. **Do NOT modify the cycle 365 grandfathered sorry at line 2272.**
   The sorry persists; it is the eventual cycle 384+ target after
   Phase α'.4 closure.

9. **Do NOT use `axiom`, `constant`, or `noncomputable axiom`
   declarations.** Per CLAUDE.md.

10. **Do NOT raise `maxHeartbeats`** above 200000. Per CLAUDE.md. If a
    proof times out, decompose it (e.g. split a multi-branch
    `by_cases` into a `private` helper per Family A tree). Cycle 380's
    work fits within default heartbeats.

## §E — Risks and mitigations

* **R1 — Forward reference of `inversePolyChain` in `inversePolynomial`
  (the Step 0 reordering issue).** Cycle 380 inserted the new
  `### Phase α'.1 (cycle 380)` block *after* `inversePolynomial`
  (line 4931+). To call `inversePolyChain k f` from
  `inversePolynomial`'s body, the cycle 380 block (`chainTree`,
  `chainTree_one/_two/_three`, `inversePolyChain`,
  `inversePolyChain_zero/_one/_two/_three`) must be physically moved
  *before* the cycle 374 `inversePolynomial` definition (line 4651).
  **Mitigation**: do Step 0 first as a pure text reordering, verify
  the file still compiles via `lake env lean` before proceeding to
  Step 1. The cycle 380 bridges (`inversePolyChain_k_eq_inversePolynomial`)
  stay in their current location after `inversePolynomial`.

* **R2 — `inversePolyChain k`'s definitional unfolding might not
  collapse cleanly after `if_pos rfl`.** The 4 cycle 380 closed-form
  theorems state the reduction at specific numeric depths; if
  `rw [if_pos rfl, inversePolyChain_zero]` doesn't close the vertex
  calibration witness, the migration breaks. **Mitigation**: pre-flight
  test on the vertex case via `lean_multi_attempt` *before* committing
  to the full migration. If `rw [inversePolyChain_zero]` doesn't fire,
  fall back to `simp only [inversePolyChain_zero]` or unfold explicitly
  (`unfold inversePolyChain` + `Fin.sum_univ_one`).

* **R3 — Phase γ subtree-agreement proof's `mk [mk [cherry]]` branch
  has many `by decide` discharges.** The migration changes
  `if t = mk [mk [cherry]] then [explicit polynomial]` to
  `if t = mk [mk [cherry]] then inversePolyChain 3 f`. The `by decide`
  arguments are unaffected (they're inequalities between trees, not
  involving the `if` body), but the trailing `h_closed` rewrites must
  apply *after* `inversePolyChain_three` exposes the polynomial.
  **Mitigation**: port the `mk [mk [cherry]]` branch last and verify
  it line-by-line.

* **R4 — `rw [inversePolyChain_zero]` may need the goal to expose
  `inversePolyChain 0 f` first.** If `if_pos rfl` leaves a goal
  mentioning the numeric literal with a different type ascription, the
  rewrite may not fire. **Mitigation**: try both forms, or use
  `show inversePolyChain 0 f = ...` to coerce the binder type before
  rewriting (cycle 250 / 366 precedent for analogous `Fin`-coercion).

* **R5 — Possible build-time regression on the Chapter 4 aggregator
  if `Section441.lean` is in the dependency chain.** **Mitigation**:
  per project policy, do not touch Section441; verify only
  `Section422.lean` and `Chapter4.lean` aggregator. If Chapter4.lean
  fails for unrelated reasons (GPFS Section441 timeout), document and
  skip step 5 of §C.

## §F — Aristotle delegation

**Not needed this cycle.** The migration is mechanical refactoring,
not premise-search. Aristotle's free compute is better reserved for
cycle 384+ Phase α'.4 (the cycle 365 grandfathered sorry closure),
where premise-selection on lower-order subtree agreement could
genuinely save manual cycles.

## §G — Exit criteria

Cycle 381 ships successfully if:

1. `inversePolynomial`'s four Family A branches dispatch to
   `inversePolyChain k f` for `k = 0, 1, 2, 3`.
2. All 8 cycle 374/377/378 calibration witnesses still compile
   (4 with new `inversePolyChain_k` rewrites; 4 unchanged Family B/C).
3. All 8 Phase β bridges still compile (4 updated, 4 unchanged).
4. Phase γ `inversePolynomial_eq_of_subtree_agreement` still compiles
   (4 Family A branches updated, 4 Family B/C unchanged).
5. 4 cycle 380 bridge theorems still compile (possibly simplified to
   `rfl`).
6. `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.
7. `grep -c sorry` = 5 (unchanged).
8. All updated theorems / examples axiom-clean
   (`[propext, Classical.choice, Quot.sound]`).
9. The 1 code sorry at line 2272 (cycle 365 grandfathered) untouched.

If any step fails irrecoverably (R1–R4 above):

* Document what didn't work in cycle 381 task results.
* Leave `Section422.lean` in cycle 380's state — **do NOT commit a
  partial migration**. Either ship Steps 1–5 in full, or ship none.
* Suggest a smaller fallback (e.g. migrate only the vertex branch as a
  stepping stone) for cycle 382's worker.

The cycle 380 worker's task results explicitly note this is
"low-risk, mechanical, ~50 LOC". Expect a clean ship.

## §H — Streak preservation

§422 axiom-clean streak: 44 substantive + 1 doc (cycles 336–380).
Cycle 381 is the 45th substantive cycle; preserve the streak by
shipping axiom-clean or skipping entirely.

## §I — Optional stretch goal (only if Steps 1–5 close with budget)

If the migration completes well within budget, the minimal additional
deliverable is:

* **Add a non-vacuity `example` exercising `chainTree 4`** (depth-4
  single-child ladder, `mk^4[vertex]` — not in the 8-tree ladder).
* Show that `inversePolyChain 4 f` evaluates to a specific polynomial
  in `f` (use `Fin.sum_univ_succ` / `Fin.sum_univ_four` to expand the
  recursion).

This is **stretch**, not required. The scoping doc §4 conjectures the
depth-4 closed form is
`-c_0⁵ + 4c_0³c_1 - 2c_0c_1² - 3c_0²c_2 + 2c_1c_2 + 2c_0c_3 - c_4`,
but the cycle 380 worker noted this is unverified — derive it
empirically from `inversePolyChain 4 f` rather than assuming the
conjecture.

Either way, the result is empirical evidence about Family A's
recursion shape for cycle 382+ planning.

**Do NOT attempt this stretch goal if it risks breaking the primary
deliverable.**
