# Cycle 390 Strategy

## §A. Status verification (run first, ~3 min)

1. `git log --oneline -1` — confirm HEAD is `2d079b6` (cycle 389).
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` — confirm 5
   (4 docstring refs + 1 grandfathered code sorry at line 2272).
3. `wc -l OpenMath/Chapter4/Section422.lean` — confirm ~7321 LOC.

If any disagrees, stop and re-read `task_results/cycle_389.md`.

## §B. Audit findings — cycle 389 worker's option 2 recommendation is PARTIALLY BLOCKED

The cycle 389 task results §"Suggested next approach" recommended
option 2 (Phase α'.4.2 migration of `inversePolynomial`'s remaining
two Family C branches `mk [broom₃]` and `mk [vertex, cherry]` to
dispatch through `inversePolyTree`). **The recommendation is half-right
but missed a structural blocker for `mk [broom₃]`.**

### Paper-algebra verification (do not skip)

`inversePolyTree (mk [broom₃]) f` dispatches via cycle 387's
single-child case at `Section422.lean:6347-6349`:

```
| mk [c], f => -(f vertex * inversePolyTree c f) - f (mk [c])
```

Computing for `c = broom₃` with cycle 389's
`inversePolyTree broom₃ f = -v³ + 2vc - b'`:

  `inversePolyTree (mk [broom₃]) f`
    = `-(v · (-v³ + 2vc - b')) - f(mk [broom₃])`
    = `v⁴ - 2v²c + vb' - M_mkBroom`

But cycle 371's `elementaryWeightQ_phi_inv_mkBroom₃` closed form
gives **`v⁴ - 3v²c + vb' + 2vm - M_mkBroom`**.

They differ by `-v²c + 2vm`. The recursion is **wrong** at this case
because the single-child case in `inversePolyTree` only handles
single-leaf children correctly — it has no cross-term machinery for
single non-leaf children. **`mk [broom₃]` migration is structurally
blocked** and would require either a new `monochildCrossTerm` helper
or a fundamental refactor of `inversePolyTree`'s single-child branch.

Conversely, `inversePolyTree (mk [vertex, cherry]) f` dispatches via
cycle 387's binary case to `bichildPolynomial vertex cherry (-v) (v²-c) f`.
Working this out:

  `bichildPolynomial vertex cherry (-v) (v² - c) f`
    = `-(v · (-v) · (v² - c)) - (-v) · f(mk [cherry])
       - (v² - c) · f(mk [vertex]) + bichildCrossTerm vertex cherry f
       - f(mk [vertex, cherry])`
    = `v²(v² - c) + v · m - (v² - c) · c + cross-term - V`
    (using `mk [vertex] = cherry`)
    = `v⁴ - 2v²c + c² + vm + cross-term - V`

Cycle 372 target: `v⁴ - 3v²c + c² + vb' + vm - V`.

So `bichildCrossTerm vertex cherry f` must equal **`-v²c + vb'`**
(equivalently: `-(f vertex)² · f cherry + f vertex · f broom₃`).
With this branch added to `bichildCrossTerm`, the binary case
**works** — migration of `mk [vertex, cherry]` becomes feasible.

### Cycle 390 plan: complete the binary case first; defer single-child

Don't attempt to fix the single-child case in cycle 390 (multi-cycle
infrastructure work — needs design of `monochildCrossTerm` plus
recomputing every existing single-child branch). Instead, ship the
straightforward continuation of cycles 388/389:

**Cycle 390 ship: Phase α'.4.1 P4 — `(vertex, cherry)` cross-term +
`inversePolyTree_mkVertexCherry` calibration witness.**

This continues the cycle 388 / 389 pattern (each adds one
`bichildCrossTerm` branch + one calibration witness) and unblocks
**half** of Phase α'.4.2 migration for cycle 391.

## §C. Priority 1 — DELIVERABLES

Three sub-deliverables, all in `OpenMath/Chapter4/Section422.lean`,
all axiom-clean target `[propext, Classical.choice, Quot.sound]`.
Follow this exact order:

### C.1 — P1: refine `bichildCrossTerm` for `(vertex, cherry)` pair

**Location**: `Section422.lean:6271-6297` (current `bichildCrossTerm`
definition with two `if-then-else` branches: `(cherry, cherry)` and
`(broom₃, cherry)`).

**Action**: insert a third `else if` branch between the
`(broom₃, cherry)` branch and the final `else 0`. The value (derived
in §B above) is:

```lean
  else if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.cherry then
    -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
      + f RootedTree.vertex * f RootedTree.broom₃
```

**Important**: this branch must come AFTER `(broom₃, cherry)`
(neither condition can match the other due to `broom₃ ≠ vertex`,
so the order doesn't affect semantics, but matching the
cycle-389-strategy convention of listing branches in the order they
were shipped keeps git blame clean).

**Docstring update**: append a sentence to the cycle 386/388/389
docstring noting "Cycle 390 ships the `(vertex, cherry)` cross-term
back-computed from cycle 372's
`elementaryWeightQ_phi_inv_mkVertexCherry` closed form by
subtracting the `bichildPolynomial` backbone at
`(inv_v, inv_c) = (-v, v² - c)`. Value: `-v²c + vb'`."

### C.2 — P2: ship calibration witness `inversePolyTree_mkVertexCherry`

**Location**: place IMMEDIATELY after cycle 389's
`inversePolyTree_mkBroomCherry` (around `Section422.lean:6481+`).

**Statement**:

```lean
/-- *Phase α'.4.1 P4 (cycle 390) — calibration witness for
`mk [vertex, cherry]` (asymmetric leaf+non-leaf two-children,
order 4).*

Confirms `inversePolyTree (mk [vertex, cherry]) f` evaluates to
cycle 372's `elementaryWeightQ_phi_inv_mkVertexCherry` 6-term
closed form under `f = elementaryWeightQ_phi η_q`:

`Φ_{η_q⁻¹}(mk [vertex, cherry])
  = v⁴ - 3v²c + c² + v·b' + v·m - Φ_η(mk [vertex, cherry])`

where `v, c, b', m = Φ_η` at `vertex, cherry, broom₃, mk [cherry]`.

This is the 4th calibration witness in the Phase α'.4.1 ladder
(after `vertex`/cycle 387, `cherry`/cycle 387, `mk [cherry, cherry]`/
cycle 388, `broom₃`/cycle 389, `mk [broom₃, cherry]`/cycle 389).
Combined with the C.1 cross-term refinement, it certifies the
recursive `inversePolyTree` evaluates correctly at this Family C
binary-children order-4 tree. -/
theorem inversePolyTree_mkVertexCherry (f : RT → ℝ) :
    inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + (f RootedTree.cherry) ^ 2
        + f RootedTree.vertex * f RootedTree.broom₃
        + f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry]) := by
  rw [inversePolyTree,
      inversePolyTree_vertex,
      inversePolyTree_cherry]
  unfold bichildPolynomial
  rw [show bichildCrossTerm RootedTree.vertex RootedTree.cherry f
        = -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
          + f RootedTree.vertex * f RootedTree.broom₃ by
    unfold bichildCrossTerm
    rw [if_neg (by decide : ¬ (RootedTree.vertex = RootedTree.cherry
                                 ∧ RootedTree.cherry = RootedTree.cherry))]
    rw [if_neg (by decide : ¬ (RootedTree.vertex = RootedTree.broom₃
                                 ∧ RootedTree.cherry = RootedTree.cherry))]
    rw [if_pos ⟨rfl, rfl⟩]]
  -- The unfolded `bichildPolynomial` LHS has `f(mk [vertex])` and
  -- `f(mk [cherry])` literally; we want to fold `mk [vertex] = cherry`
  -- before `ring`. Use a `show` to expose the post-unfold goal in
  -- folded form, then `ring`.
  show -(f RootedTree.vertex * -(f RootedTree.vertex)
            * ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry))
        - -(f RootedTree.vertex)
            * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - ((f RootedTree.vertex) ^ 2 - f RootedTree.cherry)
            * f RootedTree.cherry
        + (-((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
            + f RootedTree.vertex * f RootedTree.broom₃)
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
      = _
  ring
```

**Critical**: the `show` block exposes the unfolded
`bichildPolynomial` LHS in folded form (substituting
`mk [vertex] = cherry` definitionally via `rfl`-level Lean
reduction). If the `show` shape doesn't match Lean's actual
unfolded form, use `lean_term_goal` after `unfold bichildPolynomial`
to inspect the current goal state and adjust the `show` accordingly.

**Fallback A** (if `show` block fails to match): drop the `show`
entirely and try a direct `rw [show
(OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.vertex] : RT)
= RootedTree.cherry from rfl]` before `ring`. The `rfl`-level fold
of `mk [vertex] = cherry` should let `ring` close the rest.

**Fallback B** (if `ring` can't close): decompose into intermediate
named `have` steps mirroring cycle 388/389's recipe. The identity is
degree-4 in 6 indeterminates (`v, c, b', m, mk[vertex, cherry]`,
plus the `mk [cherry]` weight as `m`); well within `ring`'s default
budget (cycle 389 closed a degree-6 9-indeterminate identity in one
`ring` call), so Fallback B is unlikely to be needed.

### C.3 — P3 (stretch, OPTIONAL): partial Phase α'.4.2 migration for `mk [vertex, cherry]`

If C.1 and C.2 both close cleanly AND `#print axioms` confirms
axiom-clean, attempt the **partial Phase α'.4.2 migration** for
the `mk [vertex, cherry]` branch of `inversePolynomial` only.

**Action**: at `Section422.lean:6601-6610`, replace the explicit
polynomial body of the `mk [vertex, cherry]` branch:

```lean
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry] then
    (f RootedTree.vertex) ^ 4
      - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
      + (f RootedTree.cherry) ^ 2
      + f RootedTree.vertex * f RootedTree.broom₃
      + f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
```

with:

```lean
  else if t = OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry] then
    inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) f
```

Then ship a bridge theorem:

```lean
/-- *Phase α'.4.2 partial (cycle 390) — Family C bridge migration
for `mk [vertex, cherry]`.* Parallel to cycles 381 (Family A) and
383 (Family B). The migration is partial because `mk [broom₃]`
remains as an explicit polynomial body — its migration requires
single-child non-leaf cross-term infrastructure deferred to
cycle 391+. -/
theorem inversePolyTree_mkVertexCherry_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]) f
      = inversePolynomial
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry]) f := by
  unfold inversePolynomial
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_pos rfl]
```

(Six `if_neg` discharges for vertex/cherry/broom₃/mk[cherry]/bushy/
mk[broom₃] inequality, then `if_pos rfl` for the matched
`mk [vertex, cherry]` branch.) After migration the RHS body **IS**
`inversePolyTree ... f`, so both sides are syntactically equal — the
`if_pos rfl` step closes the goal completely.

**Skip C.3 if there are ANY surprises in C.1 / C.2** — the migration
adds rewiring risk:

* the existing calibration witnesses for `mk [vertex, cherry]`
  (from cycle 377 era at `Section422.lean:~4250-4290`, search for
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkVertexCherry`)
  may have proofs that consume the old explicit polynomial body and
  break under migration. Need to re-verify these stay axiom-clean.
* Phase γ `inversePolynomial_eq_of_subtree_agreement` (search for
  this theorem in `Section422.lean`, likely around line 4400-4500)
  has 8-way `by_cases` over the trees in `inversePolynomial`'s
  pattern-match; one branch handles `mk [vertex, cherry]`. After
  migration, this branch needs an extra `rw
  [inversePolyTree_mkVertexCherry]` step to substitute the recursive
  form's value before the standard agreement argument closes.

Cycle 391 ships the migration as its dedicated deliverable if C.3
is skipped this cycle.

## §D. NOT-do list for cycle 390

* **Do NOT** attempt to fix the single-child non-leaf case
  (`mk [broom₃]` dispatch in `inversePolyTree`). This requires
  designing a `monochildCrossTerm` helper and recomputing every
  existing single-child branch (cycle 381's Family A migration
  consumers in particular). Multi-cycle infrastructure work,
  out-of-scope for cycle 390.

* **Do NOT** attempt `mk [broom₃]` migration in `inversePolynomial`.
  Per §B above, `inversePolyTree (mk [broom₃]) f` evaluates to
  `v⁴ - 2v²c + vb' - M_mkBroom`, which **does not** match cycle
  377's explicit body `v⁴ - 3v²c + vb' + 2vm - M_mkBroom`.
  Migration would silently break the semantics of `inversePolynomial`
  on this tree (any consumer that relies on it being correct for
  `mk [broom₃]` would start failing).

* **Do NOT** add a `(vertex, broom₃)`, `(broom₃, vertex)`, or
  `(broom₃, broom₃)` branch to `bichildCrossTerm`. Cycle 389
  worker's option 1 (`broom₃, broom₃`) was correctly flagged as
  multi-cycle (requires shipping a `mk [broom₃, broom₃]` order-7
  closed form via `elementaryWeightQ_phi_inv_*` first). Cycle 390
  ships only the `(vertex, cherry)` branch.

* **Do NOT** ship any Phase β bridges this cycle. Cycle 389
  worker's option 3 (4 Phase β bridges for Family C closed forms
  to elementaryWeightQ_phi form) is broader than option 2 and lacks
  the immediate consumer that option 2 partial migration provides.
  Defer to cycle 392+.

* **Do NOT** modify the grandfathered cycle 365 sorry at line
  2272 of `Section422.lean`. It's the cycle 367+ Phase β/γ-completion
  multi-cycle target; not in scope.

* **Do NOT** introduce `axiom` or `constant` declarations.

* **Do NOT** raise `maxHeartbeats` above the default 200000.
  If `ring` stalls on P2's identity (low risk per cycle 389's
  precedent — degree-6 9-indeterminate identity closed in one
  `ring` call), use Fallback B in §C.2.

* **Do NOT** pivot to a fresh entity. Cycle 389's score = 2 confirms
  the §422 streak is productive; cycle 390 maintains it.

* **Do NOT** edit `scripts/autonomous_loop.py` (loop-maintainer
  territory per `CLAUDE.md`).

## §E. Risk assessment

| Risk | Likelihood | Mitigation |
|---|---|---|
| `show` block shape mismatch in P2 | medium | Inspect goal with `lean_term_goal` and adjust; Fallback A drops `show` for a `rw` of `mk [vertex] = cherry` |
| `ring` can't close P2 identity | low | Identity is degree-4 in 6 indeterminates; cycle 389 closed degree-6 9-indeterminate identities in one `ring` call |
| `by decide` fails on `(vertex = cherry ∧ _)` etc. | very low | Cycles 388/389 used `by decide` successfully for analogous `RT × RT` pair inequalities |
| P1 introduces if-branch ordering bug | very low | Cycle 388/389 added two branches without ordering issues; the third branch is structurally similar |
| Hidden `bichildCrossTerm` simp side-effects on cycle 388/389 calibration witnesses | low | §G compile + verification protocol explicitly re-checks `#print axioms` on the cycle 388/389 witnesses after C.1 |
| Compile time exceeds 6 min for full file rebuild | medium | Cycle 389's full rebuild took 309s; cycle 390 adds ~50 LOC so expect ~330s. If exceeds 600s, decompose C.2 into a private helper. |
| C.3 migration breaks downstream cycle 377-era calibration witnesses | medium-low (if attempted) | Skip C.3 at the first sign of trouble; cycle 391 handles it. The bridge theorem itself is one-line `rfl` after migration. |

## §F. Compile + verification protocol

After each of C.1, C.2, C.3 (if pursued):

1. `lake build OpenMath.Chapter4.Section422` — must exit 0.
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` — must report
   exactly **5** (4 docstring refs + 1 grandfathered code sorry).
3. After C.1: `#print axioms inversePolyTree_mkCherryCherry`
   AND `#print axioms inversePolyTree_mkBroomCherry` — both
   must report `[propext, Classical.choice, Quot.sound]`
   (regression check that the cross-term extension doesn't
   break cycles 388/389 calibration witnesses).
4. After C.2: `#print axioms inversePolyTree_mkVertexCherry` must
   report `[propext, Classical.choice, Quot.sound]`.
5. After C.3 (if pursued): `#print axioms
   inversePolyTree_mkVertexCherry_eq_inversePolynomial` AND each
   of the cycle-377-era `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkVertexCherry`
   theorems AND `inversePolynomial_eq_of_subtree_agreement` —
   all must report `[propext, Classical.choice, Quot.sound]`.

If ANY check fails, document in `task_results/cycle_390.md` and
roll back the failing piece. Sorry count must stay at 5 — that's
the supervisor policy hard line.

## §G. Bookkeeping at cycle end

* `lean_status.json` — `def:422B` row stays `partial`,
  `cycle_completed_at` → 390. **Do NOT** add `inversePolyTree`
  itself as a new entity row; it's internal infrastructure for
  the deferred `def:422B` recursion.
* `plan.md` — update the §422 paragraph (currently ends at cycle
  389) with one new sentence: "Cycle 390 ships Phase α'.4.1 P4
  `(vertex, cherry)` cross-term refinement + `inversePolyTree_mkVertexCherry`
  calibration witness, completing the binary-children cross-term
  library for Family C order-4 trees."
  (If C.3 also ships, append: "Phase α'.4.2 partial migration of
  `mk [vertex, cherry]` branch in `inversePolynomial` to dispatch
  through `inversePolyTree`.")
* `task_results/cycle_390.md` — standard format (Worked on, Approach,
  Result, Faithfulness check, Dead ends, Discovery, Suggested next
  approach).

## §H. Cycle 391+ outlook

After cycle 390:

* **Cycle 391 entry point (primary)**: design and ship the
  `monochildCrossTerm` infrastructure to fix `inversePolyTree`'s
  single-child non-leaf case (~150 LOC). This unblocks `mk [broom₃]`
  migration in cycle 392+ and completes the Family C migration
  story. Concretely: extend the single-child case in `inversePolyTree`
  to call `monochildCrossTerm c f` (similar to `bichildCrossTerm`
  for binary), back-compute the values from cycles 369/371/378
  closed forms.

* **Cycle 391 alternative**: if cycle 390 ships only C.1+C.2,
  cycle 391 can ship C.3 (Phase α'.4.2 partial migration for
  `mk [vertex, cherry]`) as its primary deliverable, deferring
  `monochildCrossTerm` to cycle 392+.

* **Cycle 392+**: complete `mk [broom₃]` migration via
  `monochildCrossTerm`; ship Phase β bridges for Family C
  closed forms (broader option 3 from cycle 389); attack the
  cycle 365 grandfathered sorry once full Family C migration lands.

The cycle 389 worker's option 1 (`broom₃, broom₃` cross-term) and
option 3 (Phase β bridges) remain on the post-cycle-390 menu but
both grow tangentially — option 1 requires a multi-cycle order-7
closed-form ship; option 3 is broad. Cycle 390's focused
single-cross-term addition preserves the cycle 388/389 axiom-clean
pattern and sets up the partial migration that's the lowest-risk
single-cycle deliverable on the §422 ladder.

## §I. Summary

**Cycle 390 ships**: one new `else if` branch in `bichildCrossTerm`
for `(vertex, cherry)` (~6 LOC) + one new `theorem
inversePolyTree_mkVertexCherry` (~50 LOC including docstring) +
optionally one-line migration of `inversePolynomial`'s
`mk [vertex, cherry]` branch + one-line bridge theorem (~15 LOC
if C.3 pursued). Both new public symbols axiom-clean
`[propext, Classical.choice, Quot.sound]`; sorry count unchanged at
5; §422 streak advances to **53 substantive + 2 doc** cycles
(336–390).
