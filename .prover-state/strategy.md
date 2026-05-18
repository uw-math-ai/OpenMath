# Cycle 382 strategy

## A. Status

Cycle 381 closed Phase α'.2 (Family A bridge migration) axiom-clean,
score=1. The §422 axiom-clean streak now stands at **46 substantive
+ 1 doc** (cycles 336–381). Section422.lean: ~5870 LOC, sorry count
**5 lines = 4 docstring + 1 code** (the grandfathered cycle 365 sorry
at line 2272). No pending Aristotle results.

State of `inversePolynomial` (Section422.lean:4810+):
* Family A branches (vertex, cherry, mk [cherry], mk [mk [cherry]])
  dispatch to `inversePolyChain k f` for `k = 0, 1, 2, 3` — cycle 381.
* Family B/C branches (bushy, mk [broom₃], mk [vertex, cherry],
  broom₃) still use explicit `if-then-else` polynomial bodies.

## B. Cycle 382 target — Phase α'.3 Family B `inversePolyBroom` helper

Per cycle 381 worker's "Suggested next approach" Option B
(recommended). Mirror cycle 380's `inversePolyChain` ship pattern,
but for the **broom family** (multi-leaf trees `mk [vertex, …, vertex]`).
Do **NOT** migrate Family B branches in `inversePolynomial` this
cycle — that is cycle 383+ work (parallel to cycle 380→381).

Define a closed-form sum helper (NOT a convolution recurrence — the
broom family does not have the single-child convolution structure
that `inversePolyChain` exploits) and prove four small-`k` closed
forms matching cycles 341/367/368/370.

## C. Concrete deliverables

Append a new Phase α'.3 block to `OpenMath/Chapter4/Section422.lean`
immediately after cycle 380's `inversePolyChain_three` (~line 4760)
and BEFORE cycle 381's reordered Family A block boundary. Six
new public declarations.

### 1. `broomTree : ℕ → RT` definition

```lean
/-- *Phase α'.3 (cycle 382) — `k`-leaf broom tree.*
`broomTree 0 = vertex`, `broomTree (k+1) = mk (List.replicate (k+1) vertex)`.
Concretely: `broomTree 1 = cherry`, `broomTree 2 = broom₃`,
`broomTree 3 = bushy`. -/
def broomTree : ℕ → RT
  | 0 => RootedTree.vertex
  | n + 1 =>
    OpenMath.Chapter3.Section310.RootedTree.mk
      (List.replicate (n + 1) RootedTree.vertex)
```

### 2. Three name-equality theorems (each `by rfl`)

```lean
theorem broomTree_one : broomTree 1 = RootedTree.cherry := rfl
theorem broomTree_two : broomTree 2 = RootedTree.broom₃ := rfl
theorem broomTree_three : broomTree 3 = RootedTree.bushy := rfl
```

If `rfl` fails for `broomTree_two` / `broomTree_three`, fall back to
`by simp [broomTree, List.replicate, RootedTree.broom₃,
RootedTree.bushy]` or `by decide`.

### 3. `inversePolyBroom : ℕ → (RT → ℝ) → ℝ` definition

The closed-form sum (NOT a recurrence):

```lean
/-- *Phase α'.3 (cycle 382) — Family B closed-form helper.*

For the `k`-leaf broom tree `broomTree k`,
`inversePolyBroom k f` evaluates to `Φ_{η⁻¹}(broomTree k)` (when
`f = Φ_η`) via the binomial-style closed form derived by
expanding `(M.inverse.elementaryWeight vertex + Σⱼ M.A i j)^k =
(Aᵢ − v)^k` (cycle 368 Discovery) and summing against `M.b i`.

Closed form:
`inversePolyBroom k f = Σⱼ∈range(k+1), (-1)^(k+1+j) · C(k,j) ·
                          (f vertex)^(k-j) · f (broomTree j)`. -/
noncomputable def inversePolyBroom (k : ℕ) (f : RT → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ (k + 1 + j) * (Nat.choose k j : ℝ)
      * (f RootedTree.vertex) ^ (k - j)
      * f (broomTree j)
```

### 4. Four closed-form calibration theorems

Mirror cycle 380's `inversePolyChain_{zero,one,two,three}` pattern:

```lean
theorem inversePolyBroom_zero (f : RT → ℝ) :
    inversePolyBroom 0 f = -f RootedTree.vertex

theorem inversePolyBroom_one (f : RT → ℝ) :
    inversePolyBroom 1 f
      = (f RootedTree.vertex) ^ 2 - f RootedTree.cherry

theorem inversePolyBroom_two (f : RT → ℝ) :
    inversePolyBroom 2 f
      = -(f RootedTree.vertex) ^ 3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f RootedTree.broom₃

theorem inversePolyBroom_three (f : RT → ℝ) :
    inversePolyBroom 3 f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy
```

Match the cycle 341 (vertex), 367 (cherry), 368 (broom₃), 370 (bushy)
closed forms **verbatim**.

## D. Proof recipe per closed-form theorem

For each `inversePolyBroom_k`:

1. `unfold inversePolyBroom`.
2. `simp only [Finset.sum_range_succ, Finset.sum_range_zero]` to
   expand the sum into `k+1` explicit summands plus a `0` base.
3. `simp only [broomTree, broomTree_one, broomTree_two,
   broomTree_three, Nat.choose]` to evaluate the `broomTree j`
   calls at concrete `j` and the binomial coefficients.
4. `push_cast` if Nat→ℝ casts (on `Nat.choose k j`) need normalising.
5. `ring` to combine and verify the polynomial identity.

If `simp` can't reduce `(-1 : ℝ) ^ (k+1+j)` to literal ±1 at concrete
`k, j`, add explicit `show (-1 : ℝ)^_ = ...` rewrites with `(-1)^3 = -1`
etc. discharged by `norm_num`. The cycle 380 `inversePolyChain_three`
proof shows a clean `ring`-closed pattern when the sum is fully
expanded.

**Pitfall to avoid (cycle 379 §4 sign-convention error)**: The cycle
379 scoping doc §4 Family B derivation tried the formula
`Σⱼ C(k,j) · v^(k-j) · (-1)^j · wⱼ` and produced wrong signs at
`k = 2`. The correct sign factor is `(-1)^(k+1+j)`, not `(-1)^j`.
I (planner) re-verified the formula against all four data points
(k = 0, 1, 2, 3) before writing this strategy. Verification table:

| k | j | (-1)^(k+1+j) | C(k,j) | term | expected |
|---|---|---|---|---|---|
| 0 | 0 | -1 | 1 | -v | -v ✓ |
| 1 | 0 | +1 | 1 | +v² | +v² ✓ |
| 1 | 1 | -1 | 1 | -c | -c ✓ |
| 2 | 0 | -1 | 1 | -v³ | -v³ ✓ |
| 2 | 1 | +1 | 2 | +2vc | +2vc ✓ |
| 2 | 2 | -1 | 1 | -b' | -b' ✓ |
| 3 | 0 | +1 | 1 | +v⁴ | +v⁴ ✓ |
| 3 | 1 | -1 | 3 | -3v²c | -3v²c ✓ |
| 3 | 2 | +1 | 3 | +3vb' | +3vb' ✓ |
| 3 | 3 | -1 | 1 | -B | -B ✓ |

**Do not "fix" the sign — it is right.**

## E. Verification checklist

Per cycle 380 / 381 precedent:

* `lake env lean OpenMath/Chapter4/Section422.lean` → exit 0.
* `lake env lean OpenMath/Chapter4.lean` (aggregator) → exit 0.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` → **5**
  (unchanged: 4 docstring references + 1 grandfathered code sorry
  at line 2272).
* `#print axioms` on each of the 4 new theorems (`broomTree_one`,
  `_two`, `_three`, plus the 4 closed-form theorems) → must show
  `[propext, Classical.choice, Quot.sound]` only. `broomTree` and
  `inversePolyBroom` definitions: ditto via `#print axioms` on
  any consumer.
* Existing cycle 367/368/370 closed-form theorems
  (`elementaryWeightQ_phi_inv_cherry`, `_broom₃`, `_bushy`) — must
  remain axiom-clean. Spot-check via `lake env lean` exit 0 alone;
  do not edit these.
* Tautology scanner regex
  `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` over
  Section422.lean → 0 hits.

## F. What NOT to do this cycle

1. **Do NOT migrate Family B branches in `inversePolynomial`.**
   The four Family B/C branches (`broom₃`, `bushy`, `mk [broom₃]`,
   `mk [vertex, cherry]`) stay as explicit `if-then-else` polynomial
   bodies. Migration is cycle 383+ work (parallel to cycle 380 → 381
   for Family A).
2. **Do NOT touch the cycle 365 grandfathered sorry** at
   `Section422.lean:2272`. That's Phase α'.4 territory (multi-cycle).
3. **Do NOT define Family C helpers** (`mk [broom₃]`, `mk [vertex,
   cherry]`). Family C is structurally different (heterogeneous
   children) and needs its own scoping. Cycle 384+ if at all.
4. **Do NOT submit Aristotle batches.** No pending results, and this
   work is mechanical (parallel to cycle 380); manual is faster.
5. **Do NOT write a scoping doc** in `.prover-state/issues/`. Cycle
   379's scoping-doc-only ship scored 1 then 0 (OFF-STRATEGY). This
   cycle ships Lean code primary.
6. **Do NOT try the formula `Σⱼ C(k,j) · v^(k-j) · (-1)^j · wⱼ`**
   (cycle 379 §4 attempt — wrong signs at `k = 2`). Use
   `(-1)^(k+1+j)` per §D above. The sign verification table in §D
   confirms the formula matches all 4 closed forms exactly.
7. **Do NOT add new tree aliases to Section310.lean.** `vertex`,
   `cherry`, `broom₃`, `bushy` all already exist there (verified
   lines 108–118). Reference them as
   `RootedTree.vertex` / `RootedTree.cherry` etc.
8. **Do NOT touch `chainTree` / `inversePolyChain` / Family A**.
   Those are cycle 380/381 territory.
9. **Do NOT bump `lean_status.json` for `def:422B`** — it stays
   `partial`. The `inversePolyBroom` helper is internal
   infrastructure, not a textbook entity closure. Plan.md row
   `[~] def:422B` likewise unchanged.
10. **Do NOT raise `maxHeartbeats`**. If a closed-form proof stalls,
    decompose with explicit `show (-1 : ℝ)^n = ...; norm_num`
    pre-rewrites before retrying.

## G. LOC budget

Total ~80–120 LOC including docstrings (parallel to cycle 380's
~75 LOC `inversePolyChain` ship):

* `broomTree` def + docstring: ~10 LOC
* 3 name-equality theorems: ~10 LOC
* `inversePolyBroom` def + docstring: ~25 LOC
* 4 closed-form theorems with docstrings: ~50–70 LOC (each
  ~12–18 LOC including docstring)

If the worker hits 150 LOC, something has gone wrong — stop and
re-verify the sign convention against §D's verification table.

## H. Build budget

Section422.lean cold rebuild was ~270–360 s in recent cycles (270 s
in cycle 364, 352 s in cycle 365, ~160 s warm in cycle 366). Budget
~6 minutes per `lake env lean` invocation. Plan for at most
**3 compile cycles**: (1) after defining `broomTree` + 3 names,
(2) after defining `inversePolyBroom` + the four closed forms,
(3) after axiom-clean verification on a scratch file.

## I. Graceful degradation

If only `broomTree`, `inversePolyBroom`, and 2 of the 4 closed-form
theorems compile cleanly within budget, ship them and defer
`inversePolyBroom_two`/`_three` to cycle 383. **Do not commit any
`sorry`-bearing scaffolds** (cycle 200/201, 149/150 rollback
precedents) — the helper definition is fine on its own but every
closed-form theorem must be axiom-clean.

If even `broomTree_two` / `_three` fail `rfl`/`decide`, ship them
via `by simp [broomTree, List.replicate, RootedTree.broom₃,
RootedTree.bushy]` (these are explicit definitions, so simp closure
is guaranteed).

## J. Order of operations

1. Read cycle 380's `inversePolyChain` block (Section422.lean:~4659–
   4760) for the proof-recipe template. The cycle 380 closure
   pattern (`rw [inversePolyChain, Fin.sum_univ_X]; show ...; rw
   [...inductive eqs...]; ring`) is the model.
2. Insert the new Phase α'.3 block immediately after cycle 380's
   `inversePolyChain_three` and before cycle 381's
   `inversePolyChain_zero_eq_inversePolynomial` bridge block.
3. Write `broomTree` + 3 name theorems. Run
   `lake env lean OpenMath/Chapter4/Section422.lean` to verify
   `rfl` works for all three.
4. Write `inversePolyBroom` def. Compile.
5. Write `inversePolyBroom_zero`. Compile + axiom-check.
6. Write `inversePolyBroom_one`. Compile + axiom-check.
7. Write `inversePolyBroom_two`. Compile + axiom-check.
8. Write `inversePolyBroom_three`. Compile + axiom-check.
9. Final aggregator build: `lake env lean OpenMath/Chapter4.lean`.

## K. Cycle 383+ outlook

After cycle 382's Family B helper ships:

* **Cycle 383**: Family B bridge migration (parallel to cycle 381).
  Replace the explicit polynomial bodies in `inversePolynomial`'s
  `broom₃` and `bushy` branches with `inversePolyBroom 2 f` and
  `inversePolyBroom 3 f` respectively. Update the matching cycle
  368/370 Phase β bridges + the Phase γ subtree-agreement theorem
  + add 2 bridge theorems `inversePolyBroom_{two,three}_eq_inversePolynomial`.
* **Cycle 384+**: Family C scoping + helper. The two Family C trees
  (`mk [broom₃]`, `mk [vertex, cherry]`) have heterogeneous children
  and won't fit into a single integer-parametrised helper. Likely
  needs a separate `inversePolyFamilyC` helper indexed by tree
  shape, or per-tree closed forms without an umbrella helper.
* **Cycle 385+**: Phase α'.4 closure of cycle 365 grandfathered
  sorry. Requires Family A + B + C closed forms via a full
  recursive `inversePolynomial` covering arbitrary `t`, plus the
  global bridge `elementaryWeightQ_phi_inv_eq_inversePolynomial`.

This cycle is one step in the chain; ship it cleanly and move on.
