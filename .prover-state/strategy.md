# Cycle 389 Strategy — §422 Phase α'.4.1 P3 (`(broom₃, cherry)` cross-term)

## §A Status verification (P0, 5 min)

Cycle 388 shipped clean (score 2). Confirm at HEAD before starting:

```bash
git log --oneline -1
# Expected: ce128f4 Cycle 388 — §422 Phase α'.4.1 P1+P2 `(cherry, cherry)`...

grep -c sorry OpenMath/Chapter4/Section422.lean
# Expected: 5 (4 docstring refs + 1 grandfathered code sorry at line 2272)
```

If verification fails, escalate; do NOT start P1.

## §B This cycle's deliverable

Ship the `(broom₃, cherry)` cross-term refinement of `bichildCrossTerm`
plus the calibration witness `inversePolyTree_mkBroomCherry` that
reconciles `inversePolyTree (mk [broom₃, cherry]) f` against cycle 386's
14-term closed-form theorem `elementaryWeightQ_phi_inv_mkBroomCherry`
(`Section422.lean:3397+`).

This continues the cycle 385 scoping doc's Phase α'.4.1 ladder
(cycle 387 shipped vertex+cherry; cycle 388 added `(cherry, cherry)`;
cycle 389 adds `(broom₃, cherry)`).

## §C Three sub-deliverables in dependency order

### P1 (PREREQUISITE, ~25 LOC, LOW risk) — `inversePolyTree_broom₃`

Ship a calibration witness for `inversePolyTree` at broom₃:

```lean
theorem inversePolyTree_broom₃ (f : RT → ℝ) :
    inversePolyTree RootedTree.broom₃ f
      = -(f RootedTree.vertex)^3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f RootedTree.broom₃ := by
  show inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex]) f = _
  rw [inversePolyTree, inversePolyTree_vertex]
  unfold bichildPolynomial bichildCrossTerm
  -- (vertex, vertex) ≠ (cherry, cherry), so cross-term collapses to 0
  rw [if_neg (by decide)]
  ring
```

**Why needed**: `mk [broom₃, cherry]`'s binary-case unfolding produces
`bichildPolynomial broom₃ cherry (inversePolyTree broom₃ f)
(inversePolyTree cherry f) f`. P3's proof needs `inversePolyTree broom₃ f`
in its closed-form expansion — having a named lemma is much cleaner
than inlining a double-layer recursive unfold inside a 60-line proof.

**Algebra check** (verify on paper before writing Lean):
- `broom₃ = mk [vertex, vertex]` (binary children, NOT single-child).
- `inv₁ = inv₂ = inversePolyTree vertex f = -v`.
- `bichildPolynomial vertex vertex (-v) (-v) f`
  = `-(v·(-v)·(-v)) - (-v)·f(mk[vertex]) - (-v)·f(mk[vertex]) + 0 - f(mk[vertex,vertex])`
  = `-v³ + v·c + v·c + 0 - b'` = `-v³ + 2vc - b'`. ✓
- Matches cycle 368's `elementaryWeightQ_phi_inv_broom₃` closed form.
- **Cross-term at `(vertex, vertex)` is correctly `0`** by default; do
  NOT modify `bichildCrossTerm` for this case.

**Placement**: in `Section422.lean` immediately after
`inversePolyTree_cherry` (~line 6346), before
`inversePolyTree_mkCherryCherry` (cycle 388 ship at line ~6356).

### P2 (~25 LOC including docstring, LOW risk) — refine `bichildCrossTerm` for `(broom₃, cherry)`

Extend the cycle 388 if-then-else dispatch to handle `(broom₃, cherry)`.
The back-computed cross-term value (algebra in §D below) is:

```
bichildCrossTerm broom₃ cherry f =
  -2·v⁴·c
  + 3·v²·c²
  + v³·b'
  - v·b'·c
  + 2·v³·m
  - 2·v·c·m
  - 3·v²·vc
  + 2·v·cc
  + v·vb'
```

(shorthand: `v = f vertex, c = f cherry, b' = f broom₃,
m = f (mk[cherry]), vc = f (mk[vertex,cherry]),
cc = f (mk[cherry,cherry]), vb' = f (mk[vertex,broom₃])`).

Update the def to:

```lean
noncomputable def bichildCrossTerm (t₁ t₂ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = RootedTree.cherry ∧ t₂ = RootedTree.cherry then
    -- cycle 388 (cherry, cherry) value
    2 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
      - 2 * f RootedTree.vertex * (f RootedTree.cherry) ^ 2
      - (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
  else if t₁ = RootedTree.broom₃ ∧ t₂ = RootedTree.cherry then
    -- cycle 389 (broom₃, cherry) value, back-computed from cycle 386
    -2 * (f RootedTree.vertex) ^ 4 * f RootedTree.cherry
      + 3 * (f RootedTree.vertex) ^ 2 * (f RootedTree.cherry) ^ 2
      + (f RootedTree.vertex) ^ 3 * f RootedTree.broom₃
      - f RootedTree.vertex * f RootedTree.broom₃ * f RootedTree.cherry
      + 2 * (f RootedTree.vertex) ^ 3 *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      - 2 * f RootedTree.vertex * f RootedTree.cherry *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
      - 3 * (f RootedTree.vertex) ^ 2 *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.cherry, RootedTree.cherry])
      + f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.broom₃])
  else 0
```

Update the docstring to mention cycle 389 alongside cycle 388.

**Verification of cycle 388's case after P2**: the existing
`(cherry, cherry)` dispatch must still work. The first if-branch
still fires on `⟨rfl, rfl⟩` for cherry inputs; P2's new branch only
fires when the first conjunction fails. Cycle 388's calibration
witness `inversePolyTree_mkCherryCherry` should remain axiom-clean
— re-verify with `#print axioms` after P2 lands.

### P3 (SUBSTANTIVE, ~60 LOC, MEDIUM risk) — `inversePolyTree_mkBroomCherry`

The calibration headline for cycle 389:

```lean
theorem inversePolyTree_mkBroomCherry (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.broom₃, RootedTree.cherry]) f
      = (f RootedTree.vertex)^6
        - 5 * (f RootedTree.vertex)^4 * f RootedTree.cherry
        + 5 * (f RootedTree.vertex)^2 * (f RootedTree.cherry)^2
        + 2 * (f RootedTree.vertex)^3 * f RootedTree.broom₃
        - 2 * f RootedTree.vertex * f RootedTree.broom₃ * f RootedTree.cherry
        + 3 * (f RootedTree.vertex)^3 *
            f (mk [RootedTree.cherry])
        - 4 * f RootedTree.vertex * f RootedTree.cherry *
            f (mk [RootedTree.cherry])
        + f RootedTree.broom₃ * f (mk [RootedTree.cherry])
        - (f RootedTree.vertex)^2 *
            f (mk [RootedTree.broom₃])
        + f RootedTree.cherry *
            f (mk [RootedTree.broom₃])
        - 3 * (f RootedTree.vertex)^2 *
            f (mk [RootedTree.vertex, RootedTree.cherry])
        + 2 * f RootedTree.vertex *
            f (mk [RootedTree.cherry, RootedTree.cherry])
        + f RootedTree.vertex *
            f (mk [RootedTree.vertex, RootedTree.broom₃])
        - f (mk [RootedTree.broom₃, RootedTree.cherry])
      := by
  rw [inversePolyTree, inversePolyTree_broom₃, inversePolyTree_cherry]
  unfold bichildPolynomial
  unfold bichildCrossTerm
  -- First if-branch (cherry, cherry) does NOT fire (broom₃ ≠ cherry):
  rw [if_neg (by decide)]
  -- Second if-branch (broom₃, cherry) fires:
  rw [if_pos ⟨rfl, rfl⟩]
  ring
```

**Copy the RHS verbatim** from cycle 386's
`elementaryWeightQ_phi_inv_mkBroomCherry` at
`Section422.lean:3397+` to avoid transcription errors. The cycle 386
RHS has 14 terms; the P3 statement must match exactly (modulo
`Φ_η ↦ f` substitution).

**`ring`'s job**: collapse a degree-6 polynomial identity in 9
indeterminates (v, c, b', m, M_broom, vc, cc, vb', bc). After the
substitutions, backbone contributes ~15 monomials, cross-term adds 9
more, and the cycle 386 RHS is 14 monomials. `ring` should close in
under 200000 heartbeats; if not, see §F graceful degradation.

## §D Cross-term back-computation (paper algebra)

Verify this on paper before writing the §C P2 value.

**Backbone** of `bichildPolynomial broom₃ cherry inv_b inv_c f`:

With `inv_b = -v³ + 2vc - b'` and `inv_c = v² - c`:

* `-(v · inv_b · inv_c)`:
  `-v · (-v³ + 2vc - b') · (v² - c)`
  = `v · (v³ - 2vc + b') · (v² - c)`
  = `v · (v⁵ - v³c - 2v³c + 2vc² + v²b' - b'c)`
  = `v⁶ - 3v⁴c + 2v²c² + v³b' - vb'c`.

* `-inv_b · f(mk[cherry])` = `(v³ - 2vc + b')·m` = `v³m - 2vcm + b'm`.

* `-inv_c · f(mk[broom₃])` = `(c - v²)·M_broom`
   = `c·M_broom - v²·M_broom`.

* `-f(mk[broom₃, cherry])` = `-bc`.

**Backbone sum**:
`v⁶ - 3v⁴c + 2v²c² + v³b' - vb'c + v³m - 2vcm + b'm
   - v²·M_broom + c·M_broom - bc`

**Cycle 386 closed form (target)**:
`v⁶ − 5v⁴c + 5v²c² + 2v³b' − 2vb'c + 3v³m − 4vcm + b'm
   − v²·M_broom + c·M_broom − 3v²·vc + 2v·cc + v·vb' − bc`

**Cross-term = Target − Backbone** (term-by-term):
- `v⁴c`: `-5 - (-3)` = `-2`  →  `-2v⁴c`
- `v²c²`: `5 - 2` = `3`  →  `+3v²c²`
- `v³b'`: `2 - 1` = `1`  →  `+v³b'`
- `vb'c`: `-2 - (-1)` = `-1`  →  `-vb'c`
- `v³m`: `3 - 1` = `2`  →  `+2v³m`
- `vcm`: `-4 - (-2)` = `-2`  →  `-2vcm`
- `b'm`, `v²·M_broom`, `c·M_broom`, `v⁶`, `bc`: cancel
- `v²·vc`: `-3 - 0` = `-3`  →  `-3v²·vc`
- `v·cc`: `2 - 0` = `2`  →  `+2v·cc`
- `v·vb'`: `1 - 0` = `1`  →  `+v·vb'`

**Result** (9 terms):
`-2v⁴c + 3v²c² + v³b' - vb'c + 2v³m - 2vcm - 3v²·vc + 2v·cc + v·vb'`

This must equal `bichildCrossTerm broom₃ cherry f`. Match each term
to the §C P2 Lean definition before writing the code.

**Sanity check**: the cross-term consumes vc (cycle 372), cc
(cycle 384), and vb' (cycle 386 NEW kernel). The cycle 385 scoping
doc §3.2 predicted Block (4) bilinear cross-term would surface
order-5 kernels shifted from each child by `vertex`; cycle 386's
empirical witness confirmed `vb' = mk[vertex, broom₃]` as the new
kernel. Cycle 389's back-computation closes the loop: the abstract
recursive definition must reproduce all three surfaced order-5
kernels.

## §E Faithfulness check (mandatory before commit)

For each new symbol introduced (`inversePolyTree_broom₃`, refined
`bichildCrossTerm`, `inversePolyTree_mkBroomCherry`):

- **Entity ID**: none (all three are internal infrastructure for
  the unified `inversePolyTree` recursion).
- **`bichildCrossTerm` `(broom₃, cherry)` value back-computed from
  cycle 386's quotient-level theorem**: this is **NOT** definition
  smuggling. The value is pinned by independent empirical data
  (cycle 386 shipped `elementaryWeightQ_phi_inv_mkBroomCherry`
  axiom-clean before cycle 389 existed). The calibration witness
  `inversePolyTree_mkBroomCherry` is a non-vacuous theorem
  connecting two independent expressions (recursive `inversePolyTree`
  evaluation vs cycle 386's hand-derived closed form).
- **Tautology check**: P1, P3 RHS ≠ any hypothesis (only `f : RT → ℝ`).
- **Identity check**: P3 proof body is `rw + unfold + unfold + rw +
  rw + ring`, real algebraic work. ✓
- **Hypothesis strength**: P1 and P3 universal in `f`, no extra
  hypotheses. ✓

Run `#print axioms` on all three new public symbols:
```
inversePolyTree_broom₃
bichildCrossTerm                    -- def, axiom-clean expected after refinement
inversePolyTree_mkBroomCherry
```
Expected: `[propext, Classical.choice, Quot.sound]`
(`Classical.choice` from if-then-else `Decidable` resolution,
matching cycle 388).

Also re-verify cycle 388's `inversePolyTree_mkCherryCherry` remains
axiom-clean after the `bichildCrossTerm` refinement:
```
#print axioms OpenMath.Chapter4.Section422.inversePolyTree_mkCherryCherry
```
Expected: same `[propext, Classical.choice, Quot.sound]` —
P2's new `else if` branch is inserted AFTER the cherry-cherry branch,
so cycle 388's `rw [if_pos ⟨rfl, rfl⟩]` still fires on the outer
branch and the cycle 388 calibration is unchanged.

## §F Graceful degradation

If P3's `ring` times out (heartbeats > 200000 — plausible given 9
indeterminates and degree 6):

**Fallback A (preferred)**: split the proof into two named lemmas:
1. `bichildPolynomial_broom₃_cherry_expansion` (private): expand the
   backbone without cross-term (using `inv_b = -v³ + 2vc - b'` and
   `inv_c = v² - c` verbatim), leaving `bichildCrossTerm broom₃ cherry f`
   as an opaque term. Close via `unfold + ring` on the smaller
   backbone polynomial (~10 monomials).
2. `inversePolyTree_mkBroomCherry`: apply the expansion lemma, then
   unfold `bichildCrossTerm`, apply `if_neg` and `if_pos`, then close
   the smaller residue identity (backbone + 9-term cross-term =
   14-term cycle 386 RHS) via `ring`.

**Fallback B (if A also stalls)**: ship P1 + P2 only. P3 deferred to
cycle 390. Sorry count remains 5 (no new sorries). §422 streak
remains intact: P1 alone is a 1-theorem axiom-clean ship; P2 alone
is a definition refinement that doesn't introduce theorems. Document
the P3 deferral in `task_results/cycle_389.md` with the §D backbone
derivation preserved verbatim for cycle 390's worker.

**Do NOT introduce `sorry` scaffolds** — follow the cycle
138/149/200/201 rollback precedent: no sorry-first scaffolds for
multi-cycle deliverables without a credible single-cycle close.
P1+P2 partial ship is the strategy-endorsed fallback.

## §G What NOT to attempt this cycle

- **NO** symmetric `(cherry, broom₃)` case. `mk [cherry, broom₃]` is
  a *syntactically different* tree from `mk [broom₃, cherry]` (Lean's
  `List` is ordered); cycle 386 only shipped the latter, so cycle 389
  only needs the latter's cross-term. The reversed-order tree would
  require its own quotient-level closed form first.
- **NO** Phase α'.4.2 migration of `inversePolynomial`'s Family C
  branches (cycle 391+ scope).
- **NO** attempt to close cycle 365's grandfathered sorry at line
  2272 (multi-cycle Phase β/γ extension; needs all Family A/B/C
  branches migrated first).
- **NO** new tree closed-forms beyond what's needed for P1/P2/P3.
  Specifically, do NOT attempt to ship
  `elementaryWeightQ_phi_inv_mkVertexBroom₃` (the new kernel `vb'`
  from cycle 386). Treat `vb'` as an opaque `f (mk [vertex, broom₃])`
  value in the cross-term polynomial — the calibration witness is
  parametric in `f` so no quotient-level theorem about `vb'` is
  needed.
- **NO** pivot to a fresh entity. The §422 streak is healthy (51
  substantive + 2 doc cycles, cycle 388 scored 2). Family C ladder
  continuation per cycle 385 scoping doc §5 is the planned path.
- **NO** `simp [inversePolyTree, ...]` cascades — per
  `feedback_simp_recursive_def_overunfolds.md`, recursive defs
  combined with name-equality theorems under `simp` over-unfold.
  Use targeted `rw [inversePolyTree, inversePolyTree_broom₃,
  inversePolyTree_cherry]` followed by `unfold bichildPolynomial` +
  `unfold bichildCrossTerm` + `rw [if_neg, if_pos]` + `ring`.
- **NO** `simp +zetaDelta` or `maxHeartbeats` bumps. If `ring`
  doesn't close, decompose per §F Fallback A.
- **NO** modification of cycle 388's `(cherry, cherry)` branch in
  `bichildCrossTerm`. Only EXTEND the if-then-else cascade; do not
  rewrite existing branches.

## §H Reference paths

- Cycle 387 / 388 deliverables (current state, the codebase to extend):
  `OpenMath/Chapter4/Section422.lean` lines 6200–6420 (Phase α'.4.1
  block: `bichildCrossTerm`, `bichildPolynomial`, `inversePolyTree`,
  `inversePolyTree_vertex`, `inversePolyTree_cherry`,
  `inversePolyTree_mkCherryCherry`).
- Cycle 386 closed form (target for P3 RHS):
  `OpenMath/Chapter4/Section422.lean:3397+`
  (`elementaryWeightQ_phi_inv_mkBroomCherry`). **Copy-paste the RHS
  verbatim for P3** to avoid transcription errors.
- Cycle 368 closed form (sanity check for P1's RHS):
  `Section422.lean:2538+` (`elementaryWeightQ_phi_inv_broom₃`).
- Phase α'.4 scoping:
  `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`.
- Family A precedent (single-child ladder, cycle 380):
  `inversePolyChain` at `Section422.lean:5400+` — for reference on
  recursive-helper definition style.
- Family B precedent (broom-binomial, cycle 382):
  `inversePolyBroom` at `Section422.lean:5800+` — for reference on
  multi-tree closed-form ladder style.

## §I LOC budget

| Sub-deliverable | LOC | Cumulative | Risk |
|---|---|---|---|
| P1 `inversePolyTree_broom₃` | ~25 | 25 | LOW |
| P2 `bichildCrossTerm` refinement | ~25 (incl docstring update) | 50 | LOW |
| P3 `inversePolyTree_mkBroomCherry` | ~60 | 110 | MEDIUM |

**Total**: ~110 LOC. Well within reasonable cycle scope.

§422 axiom-clean streak target: 51 → **52** substantive + 2 doc
(cycles 336–389). Cycle 389 score target: 2 (substantive ship
without faithfulness divergence).

## §J Cycle 390+ outlook (do NOT pre-implement)

After cycle 389 lands:
- Cycle 390 could attempt `(broom₃, broom₃)` cross-term if a
  `mk [broom₃, broom₃]` quotient-level closed-form is shipped first
  (would require a separate cycle to ship
  `elementaryWeightQ_phi_inv_mkBroomBroom` — multi-cycle).
- Alternatively cycle 390 begins Phase α'.4.2 (Family C branch
  migration of `inversePolynomial` to dispatch through
  `inversePolyTree`, parallel to cycles 381/383 for Families A/B).
- Or Phase β bridges for the existing Family C trees (cycles 371,
  372, 384, 386) at the quotient level: each needs an analog of
  cycle 375's bridge from `elementaryWeightQ_phi (η_q⁻¹) t =
  inversePolynomial t (elementaryWeightQ_phi η_q)`.

Cycle 389 stays focused on P1+P2+P3 — defer outlook decisions.

## §K Concrete order of operations for the worker

1. **(5 min)** §A status verification.
2. **(20 min)** §D paper algebra: verify the cross-term value matches
   §C P2's listed coefficients. If the paper algebra disagrees with
   §C P2, **STOP** and re-derive — the cycle 389 strategy file may
   have a transcription error, and shipping an incorrect cross-term
   value would silently propagate the bug.
3. **(15 min)** P1: write `inversePolyTree_broom₃`, run
   `lake env lean OpenMath/Chapter4/Section422.lean`, verify clean.
4. **(15 min)** P2: extend `bichildCrossTerm` with the second
   if-branch. Verify cycle 388's `inversePolyTree_mkCherryCherry`
   still compiles axiom-clean.
5. **(30–45 min)** P3: write `inversePolyTree_mkBroomCherry`. Copy
   cycle 386's RHS verbatim. Compile.
6. **(10 min)** `#print axioms` on all three new public symbols
   + cycle 388 regression check.
7. **(10 min)** task_results/cycle_389.md + lean_status update +
   commit.

Total: ~2 hours. Single-cycle deliverable.
