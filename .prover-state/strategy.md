# Cycle 394 strategy — extend `monochildCrossTerm` for `c = cherry`; ship `inversePolyTree_mkCherry`

## §A — Posture

§422 axiom-clean streak stands at **56 substantive + 2 doc** (336–393).
Sorry count is 1 (cycle 365 grandfathered at `Section422.lean:2272`).
No Aristotle results pending. Cycle 393 just shipped Phase α'.4.2 `mk [broom₃]`
migration cleanly. The natural next ship is the next Phase α'.4.1 cross-term
refinement, per cycle 393's "Suggested next approach" — but with a
correction to the cycle 393 worker's plan based on a recursion trace
(see §B below).

**Do NOT pivot to a new entity.** The §422 ladder is the active work track,
the recipe is mechanical, and the cycle 365 closure (Phase β/γ wired to
cycle 394+ migrations of all 8 ladder trees) is the milestone the work
compounds toward.

**Do NOT attempt `Section441.lean` work** — 43+ consecutive GPFS timeouts
since cycle 182. Skip per `cycle_182_gpfs_slowness.md`.

## §B — The recursion trace (READ THIS BEFORE WRITING ANY CODE)

The cycle 393 worker's "Suggested next approach" recommends shipping
`monochildCrossTerm` extension for `c = mk [cherry]` + `inversePolyTree_mkMkCherry`
calibration matching cycle 378's `mk [mk [cherry]]` closed form. **That plan
skips an intermediate dependency.** The recursion at `mk [mk [cherry]]` reads:

```
inversePolyTree (mk [mk [cherry]]) f
  = -(f vertex · inversePolyTree (mk [cherry]) f)
    + monochildCrossTerm (mk [cherry]) f
    - f (mk [mk [cherry]])
```

This is the `[c]` branch with `c = mk [cherry]`. The inner term
`inversePolyTree (mk [cherry]) f` is itself another `[c]` branch
(with `c = cherry`):

```
inversePolyTree (mk [cherry]) f
  = -(f vertex · inversePolyTree cherry f)
    + monochildCrossTerm cherry f
    - f (mk [cherry])
  = -(v · (v² - c)) + monochildCrossTerm cherry f - m       (cycle 387 cherry)
  = -v³ + vc + monochildCrossTerm cherry f - m
```

Target for `mk [cherry]` (cycle 369 closed form, `Section422.lean:2772`):
`-v³ + 2vc - m`. So **`monochildCrossTerm cherry f` must equal `vc`**, i.e.
`f vertex * f cherry`. Currently it defaults to `0`, so
`inversePolyTree (mk [cherry]) f` evaluates to `-v³ + vc - m` — **wrong by `vc`**.

**Until the `cherry` branch of `monochildCrossTerm` lands, `inversePolyTree`
gives the wrong value at `mk [cherry]`, and any cycle 395+ attempt to ship
`inversePolyTree_mkMkCherry` will start from a broken foundation.** Cycle 394
fixes this layer first.

## §C — Priority 1 ship (substantive, ~50 LOC)

### Step 1 — extend `monochildCrossTerm` at `Section422.lean:6339-6344`

Add one new `else if` branch between the existing `c = broom₃` branch
and the default `else 0`:

```lean
noncomputable def monochildCrossTerm (c : RT) (f : RT → ℝ) : ℝ :=
  if c = RootedTree.broom₃ then
    -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
  else if c = RootedTree.cherry then                            -- NEW
    f RootedTree.vertex * f RootedTree.cherry                    -- NEW
  else 0
```

Update the docstring (lines 6314–6338) bullet list to include:

* `c = cherry` → `v · c` where `c = f cherry`. Validated by cycle 369's
  `mk [cherry]` closed form `-v³ + 2vc - m`, which differs from the naive
  body `-(v · (v² - c)) - m = -v³ + vc - m` by exactly `+vc`.

### Step 2 — fix the cycle 387 `inversePolyTree_cherry` proof at line 6428

Cherry's recursion is `cherry = mk [vertex]`, so the `[c]` branch fires
with `c = vertex`. The existing proof reads:

```lean
rw [inversePolyTree, inversePolyTree_vertex,
    show monochildCrossTerm RootedTree.vertex f = 0 by
      unfold monochildCrossTerm; rw [if_neg (by decide)]]
```

After Step 1, `monochildCrossTerm` has two `if_neg` discharges before the
default `else 0`. Update to:

```lean
rw [inversePolyTree, inversePolyTree_vertex,
    show monochildCrossTerm RootedTree.vertex f = 0 by
      unfold monochildCrossTerm; rw [if_neg (by decide), if_neg (by decide)]]
```

The two `by decide` discharges close `vertex ≠ broom₃` and `vertex ≠ cherry`
respectively. **The rest of the proof body is unchanged.**

### Step 3 — verify cycle 389 `inversePolyTree_broom₃` and cycle 392 `inversePolyTree_mkBroom₃` are unaffected

* `inversePolyTree_broom₃` (line 6445): broom₃ is two-child (`mk [vertex,
  vertex]`), routes through `bichildPolynomial`, never invokes
  `monochildCrossTerm`. **No change needed.**
* `inversePolyTree_mkBroom₃` (line 6491): invokes `monochildCrossTerm broom₃`.
  After Step 1, `broom₃` is still the *first* branch of `monochildCrossTerm`,
  so `if_pos rfl` still fires correctly. **No change needed.**
* `inversePolyTree_mkCherryCherry` (cycle 388, line 6519): uses
  `bichildPolynomial`, not `monochildCrossTerm`. Unaffected.
* `inversePolyTree_mkBroomCherry` (cycle 389, line 6561): bichild. Unaffected.
* `inversePolyTree_mkVertexCherry` (cycle 390): bichild. Unaffected.
* `inversePolyTree_mkVertexCherry_eq_inversePolynomial` (cycle 391) and
  `inversePolyTree_mkBroom₃_eq_inversePolynomial` (cycle 393): pure `unfold +
  if_neg/if_pos` bridges; don't touch `monochildCrossTerm`'s body. Unaffected.

### Step 4 — ship new calibration witness `inversePolyTree_mkCherry`

Insert after `inversePolyTree_mkBroom₃` (line 6507) and before
`inversePolyTree_mkCherryCherry` (line 6509). Closed form matches cycle 369
verbatim:

```lean
/-- *Phase α'.4.1 (cycle 394) — `mk [cherry]` calibration witness.*

`inversePolyTree (mk [cherry]) f` matches cycle 369's
`elementaryWeightQ_phi_inv_mkCherry` closed form `-v³ + 2vc - m`
(under `f = elementaryWeightQ_phi η_q`). The proof unfolds the
single-child branch of `inversePolyTree`, rewrites the recursive
`inversePolyTree cherry f` via `inversePolyTree_cherry`, exposes
`monochildCrossTerm cherry f` via the cycle 394 `else if c = cherry`
branch (one `if_neg` for the `broom₃` discharge, then `if_pos rfl`),
and closes by `ring`. -/
theorem inversePolyTree_mkCherry (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) f
      = -(f RootedTree.vertex) ^ 3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) := by
  rw [inversePolyTree, inversePolyTree_cherry]
  rw [show monochildCrossTerm RootedTree.cherry f
        = f RootedTree.vertex * f RootedTree.cherry by
        unfold monochildCrossTerm
        rw [if_neg (by decide), if_pos rfl]]
  ring
```

LOC budget: ~25 LOC including docstring.

### Step 5 — sanity examples (Priority 2, optional)

Two anonymous `example`s after the new theorem, mirroring cycle 392/393 style.

If the `elementaryWeightQ_phi`-evaluation example turns out to need >10 LOC
of `simp` plumbing to evaluate at `⟦⟨1, explicitEuler⟩⟧` at vertex/cherry/mk[cherry],
**drop it** — Priority 1 is the headline; the cycle 369 closed form already
provides the corresponding non-vacuity at the textbook level.

A pure-`f` non-vacuity (e.g. `inversePolyTree (mk [cherry]) (fun _ => 1) = -2`)
is acceptable and cheap.

## §D — Verification (mandatory before commit)

1. `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 (only the
   cycle 365 grandfathered sorry warning at `:2272` should appear).
2. `lake build OpenMath.Chapter4.Section422` exits 0.
3. `grep -c sorry OpenMath/Chapter4/Section422.lean` returns **5** (4 docstring
   + 1 grandfathered cycle 365 sorry — unchanged).
4. `#print axioms inversePolyTree_mkCherry` returns
   `[propext, Classical.choice, Quot.sound]`.
5. Regression: `#print axioms` on each of the prior `inversePolyTree_*`
   calibrations (`_vertex, _cherry, _broom₃, _mkBroom₃, _mkCherryCherry,
   _mkBroomCherry, _mkVertexCherry`) still returns axiom-clean. The cycle 387
   `inversePolyTree_cherry` is the one whose proof body changed in Step 2;
   re-verify it explicitly.
6. Aggregator: `lake env lean OpenMath/Chapter4.lean` exits 0.

## §E — Approaches explicitly ruled out (do NOT retry)

* **Do NOT** try to ship `inversePolyTree_mkMkCherry` this cycle (cycle 393
  worker's literal recommendation). Per §B, `inversePolyTree (mk [cherry])
  f` is the wrong value with `monochildCrossTerm cherry = 0`, so the
  recursion's inner term doesn't match cycle 378's closed form. Cycle 395
  is the right cycle for `mk [cherry]` + `mkMkCherry` (after this cycle's
  `cherry` branch lands).

* **Do NOT** skip Step 2 (the `inversePolyTree_cherry` proof update).
  Cherry's recursion fires the `[c]` branch with `c = vertex`, and the
  existing proof's `show monochildCrossTerm vertex f = 0` block needs
  one extra `if_neg (by decide)` after the new branch is inserted.
  Compile will fail with `unsolved goals: if (vertex = cherry) ...`
  otherwise.

* **Do NOT** change the sign of `monochildCrossTerm cherry`'s value. The
  derivation in §B is concrete: target `-v³ + 2vc - m`, current naive
  body produces `-v³ + vc - m`, delta is `+vc`. **Cycle 250 precedent on
  definition smuggling**: per `cycle_250_strategy_alpha_definition_error.md`,
  paper-verify the closed-form algebra *before* writing the Lean. The
  algebra in §B is paper-verified.

* **Do NOT** introduce new `sorry`/`axiom`/`constant`.

* **Do NOT** raise `maxHeartbeats` above 200000.

* **Do NOT** modify `inversePolynomial` (the if-then-else dispatch). The
  `mk [cherry]` branch migration of `inversePolynomial` is Phase α'.4.2
  cycle 396+ work (after the next two cycles fix the recursion values).

* **Do NOT** attempt `Section441.lean` work. 43+ GPFS timeouts; see issue file.

* **Do NOT** use `simp [monochildCrossTerm, ...]` to unfold the new branch
  (per memory `feedback_simp_recursive_def_overunfolds.md`). Use targeted
  `rw [if_neg (by decide), if_pos rfl]` inside a `show ... = <value> by
  unfold monochildCrossTerm; ...` block, mirroring the cycle 392 template.

## §F — Faithfulness check (do for the new theorem and the `monochildCrossTerm` extension)

* **Entity ID**: no textbook entity directly; infrastructure for Phase α'.4
  ladder consolidation toward closing the cycle 365 grandfathered sorry.
* **`monochildCrossTerm cherry` value**: paper-derived in §B from cycle 369's
  closed form for `Φ_{η_q⁻¹}(mk [cherry])`. The value `f vertex * f cherry`
  is the unique closed-form correction that makes the recursive `inversePolyTree`
  match the cycle 369 quotient-level theorem at `mk [cherry]`. NOT
  definition-smuggled — back-computed from a shipped, axiom-clean theorem.
* **`inversePolyTree_mkCherry` tautology check**: LHS is the recursive
  `inversePolyTree (mk [cherry]) f`, RHS is the textbook polynomial
  `-v³ + 2vc - m`. Equality is substantive (the recursion unfolds via
  `inversePolyTree_cherry` + new `monochildCrossTerm cherry` branch + `ring`).
  Not an identity-via-hypothesis closure.
* **Hypothesis strength**: only `f : RT → ℝ`. Matches cycle 392 precedent.
* **Identity check**: proof is the canonical 3-step `rw + show ... by unfold;
  rw [if_neg, if_pos rfl] + ring` template from cycle 392. Substantive.

## §G — Cycle 395+ outlook (do NOT do this cycle)

* **Cycle 395 (next substantive)**: extend `monochildCrossTerm` for
  `c = mk [cherry]` branch using cycle 378's `mk [mk [cherry]]` closed form
  `v⁴ - 3v²c + c² + 2vm - M_mkMkCherry`. With cycle 394's `cherry` branch in
  place, the recursion at `mk [mk [cherry]]` gives (after the `mk [cherry]`
  inner recursion):
  - `inversePolyTree (mk [mk [cherry]]) f`
  - `= -(v · inversePolyTree (mk [cherry]) f) + monochildCrossTerm (mk [cherry]) f - f (mk [mk [cherry]])`
  - `= -(v · (-v³ + 2vc - m)) + monochildCrossTerm (mk [cherry]) f - M`
  - `= v⁴ - 2v²c + vm + monochildCrossTerm (mk [cherry]) f - M`
  - Target: `v⁴ - 3v²c + c² + 2vm - M`
  - So `monochildCrossTerm (mk [cherry]) f = -v²c + c² + vm`. Paper-verified.
* **Cycle 396+**: Phase α'.4.2 migration of `inversePolynomial`'s
  `mk [cherry]` branch (parallel of cycles 391, 393). Position 4 in the
  current if-chain → 3 `if_neg`s needed for the bridge.
* **Cycle 397+**: `bushy` branch (Family B, position 5 → 4 `if_neg`s); the
  `mk [mk [cherry]]` branch (position 8 → 7 `if_neg`s); etc.

## §H — Recap of the deliverable bar

Ship in cycle 394:
* 1 extension to `monochildCrossTerm` (one new `else if` branch, ~3 lines).
* 1 docstring update (~5 lines).
* 1 minor proof adjustment in `inversePolyTree_cherry` (~1 line: add second `if_neg`).
* 1 new public theorem `inversePolyTree_mkCherry` (~25 lines including docstring).
* (Optional) 1 non-vacuity example via pure-`f` evaluation.

Total: ~30–40 LOC. Axiom-clean. Sorry count unchanged (5).
§422 streak: 56 → **57 substantive + 2 doc** (336–394).
