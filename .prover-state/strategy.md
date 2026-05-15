# Cycle 270 Strategy — §310/§311 Phase E.1 order-5 (Phase 2 of 2):
# `lem_311A_order_five_partialSum` 17-tree bridge

## §0 Where we are

Cycle 269 SHIPPED axiom-clean the order-5 per-tree library: nine new
`bseriesExactTerm_*_scalar` theorems (all 9 unordered rooted trees of
order 5 — Butcher Table 310(II) row r=5) plus the `bushy₄` def alias.
Bell-coefficient cross-check vs cycle 259's `lem_311A_order_five`
verified all five monomial-grouped sums match `(1, 7, 4, 11, 1)`
verbatim.

State at HEAD (`003706a Cycle 269 …`):
- `Section310.lean`: `vertex`, `cherry`, `broom₃`, `bushy`, `bushy₄`
  aliases all present.
- `Section301.lean`: 13 per-tree `bseriesExactTerm_*_scalar` closed
  forms (4 order-≤-3 from cycles 266–267, 4 order-4 from cycle 268,
  9 order-5 from cycle 269).
- `Section311.lean`: `lem_311A_order_{one..five}` scalar closed-form
  Taylor specialisations (cycles 248, 256–259) +
  `lem_311A_order_{two,three,four}_partialSum` bridges (cycles
  266–268).

Zero sorries. No pending Aristotle. No consultant advice. No
semantic regressions. Clean follow-up cycle in the §310/§311 thread.

## §1 Target

**P1 (MUST SHIP)**: `lem_311A_order_five_partialSum` at
`OpenMath/Chapter3/Section311.lean`. The 17-tree partial-sum bridge
restating cycle 259's `lem_311A_order_five` using the
`bseriesExactPartialSum` API. Closes §310/§311 Phase E.1 fully up to
order 5 in the scalar setting (matching cycle 259's deliberate
order-5 cutoff in the per-tree chain).

**P2 (NICE-TO-HAVE, ~10 LOC)**: A non-vacuity witness on the trivial
ODE `f := 0, yex := const y₀` exercising the new bridge — confirms
the residual is identically zero on a degenerate ODE.

## §2 Approach (concrete recipe)

This is a 1:1 mechanical port of cycle 268's order-4 bridge
(`lem_311A_order_four_partialSum`) at one extra order. **Re-read
cycle 268's proof body in `OpenMath/Chapter3/Section311.lean` before
starting** — the recipe transfers verbatim with one extra Finset
element per `_insert` step.

### §2.1 Statement signature

```lean
theorem lem_311A_order_five_partialSum {f : ℝ → ℝ}
    (hf : ContDiff ℝ 4 f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C6 : ContDiff ℝ 6 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h => yex (x₀ + h)
              - bseriesExactPartialSum f y₀ h
                  {RootedTree.vertex,
                   RootedTree.cherry,
                   RootedTree.broom₃,
                   RootedTree.mk [RootedTree.cherry],
                   RootedTree.bushy,
                   RootedTree.mk [RootedTree.vertex, RootedTree.cherry],
                   RootedTree.mk [RootedTree.broom₃],
                   RootedTree.mk [RootedTree.mk [RootedTree.cherry]],
                   RootedTree.bushy₄,
                   RootedTree.mk [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry],
                   RootedTree.mk [RootedTree.vertex, RootedTree.broom₃],
                   RootedTree.mk [RootedTree.vertex, RootedTree.mk [RootedTree.cherry]],
                   RootedTree.mk [RootedTree.cherry, RootedTree.cherry],
                   RootedTree.mk [RootedTree.bushy],
                   RootedTree.mk [RootedTree.mk [RootedTree.vertex, RootedTree.cherry]],
                   RootedTree.mk [RootedTree.mk [RootedTree.broom₃]],
                   RootedTree.mk [RootedTree.mk [RootedTree.mk [RootedTree.cherry]]]})
      =O[nhds 0] (fun h => h ^ (5 + 1))
```

The hypotheses MUST match cycle 259's `lem_311A_order_five`
verbatim (`hf : ContDiff ℝ 4 f`, `hyex_C6 : ContDiff ℝ 6 yex`,
`hyex_x₀`, `hyex_ode`). Any divergence would be a strengthening
or weakening relative to the base lemma.

The 17-tree Finset breakdown:
- 1 order-1 tree: `vertex`
- 1 order-2 tree: `cherry`
- 2 order-3 trees: `broom₃`, `mk [cherry]`
- 4 order-4 trees: `bushy`, `mk [vertex, cherry]`, `mk [broom₃]`,
  `mk [mk [cherry]]`
- 9 order-5 trees (cycle 269): `bushy₄`, `mk [vertex, vertex,
  cherry]`, `mk [vertex, broom₃]`, `mk [vertex, mk [cherry]]`,
  `mk [cherry, cherry]`, `mk [bushy]`, `mk [mk [vertex, cherry]]`,
  `mk [mk [broom₃]]`, `mk [mk [mk [cherry]]]`

### §2.2 Non-membership lemmas (16 of them)

Inside the proof body, establish 16 non-membership facts via the
cycle 268 idiom. Each is of the form:

```lean
have hT_not_in_S : T ∉ S := by
  simp [RootedTree.vertex, RootedTree.cherry, RootedTree.broom₃,
        RootedTree.bushy, RootedTree.bushy₄, RootedTree.mk.injEq]
```

where `S` is the iteratively-shrinking remaining Finset. **Note the
simp set includes `RootedTree.bushy₄`** (new this cycle vs cycle
268's simp set).

**Pre-flagged risk R1**: 16 non-membership lemmas may push the
`simp` elaboration time beyond cycle 268's. If a single `simp` call
stalls (>30s by `lake env lean` clock), factor the non-membership
facts into a private named lemma block outside the main theorem,
or split the `simp` set per-tree (e.g.,
`simp only [RootedTree.mk.injEq, List.cons.injEq]` to skip the
heavy alias unfolding when the structural distinctness suffices).

### §2.3 Iterated `_insert` unfolds + final `_singleton`

Apply `bseriesExactPartialSum_insert` 16 times then
`bseriesExactPartialSum_singleton` once. Cycle 268's chain is the
template:

```lean
rw [bseriesExactPartialSum_insert _ _ _ _ _ h_T₁_not_in_S₁]
rw [bseriesExactPartialSum_insert _ _ _ _ _ h_T₂_not_in_S₂]
... (14 more times) ...
rw [bseriesExactPartialSum_singleton]
```

Each unfold produces a `bseriesExactTerm f y₀ h <tree> + <rest>`
shape that the next unfold or substitution can consume.

### §2.4 Per-tree closed-form substitution (13 substitutions)

After the unfolds, substitute each of the 13 closed forms:

- 4 from cycles 266–267: `bseriesExactTerm_vertex`,
  `bseriesExactTerm_cherry_scalar`,
  `bseriesExactTerm_broom₃_scalar`,
  `bseriesExactTerm_mkCherry_scalar`.
- 4 from cycle 268: `bseriesExactTerm_bushy_scalar`,
  `bseriesExactTerm_mkVertexCherry_scalar`,
  `bseriesExactTerm_mkBroom₃_scalar`,
  `bseriesExactTerm_mkMkCherry_scalar`.
- 9 from cycle 269: `bseriesExactTerm_bushy₄_scalar`,
  `bseriesExactTerm_mkVertexVertexCherry_scalar`,
  `bseriesExactTerm_mkVertexBroom₃_scalar`,
  `bseriesExactTerm_mkVertexMkCherry_scalar`,
  `bseriesExactTerm_mkCherryCherry_scalar`,
  `bseriesExactTerm_mkBushy_scalar`,
  `bseriesExactTerm_mkMkVertexCherry_scalar`,
  `bseriesExactTerm_mkMkBroom₃_scalar`,
  `bseriesExactTerm_mkMkMkCherry_scalar`.

After substitution, the partial sum equals the closed-form Taylor
polynomial of `yex` around `x₀` truncated at order 5:

```
h • f y₀
+ (h²/2) • (f' · f)
+ (h³/6) • (f'' · f² + (f')² · f)
+ (h⁴/24) • (f''' · f³ + 4·f'' · f' · f² + (f')³ · f)
+ (h⁵/120) • (f'''' · f⁴ + 7·f''' · f' · f³ + 4·(f'')² · f³
              + 11·f'' · (f')² · f² + (f')⁴ · f)
```

(All derivatives at `y₀`.)

### §2.5 Coefficient verification (faithfulness load-bearing)

Monomial groupings for order-5 contributions, after multiplying
each tree's coefficient by `120 / (σ · γ)`:

| Monomial | Trees contributing | Coefficient sum |
|----------|--------------------|-----------------|
| `f''''·f⁴` | T1 (bushy₄, σ=24, γ=5) | 120/120 = 1 |
| `f'''·f'·f³` | T2 (mk[v,v,cherry], σ=2, γ=10), T6 (mk[bushy], σ=6, γ=20) | 6 + 1 = 7 |
| `(f'')²·f³` | T3 (mk[v,broom₃], σ=2, γ=15) | 4 |
| `f''·(f')²·f²` | T4 (mk[v,mk[cherry]], σ=1, γ=30), T5 (mk[cherry,cherry], σ=2, γ=20), T7 (mk[mk[v,cherry]], σ=1, γ=40), T8 (mk[mk[broom₃]], σ=2, γ=60) | 4 + 3 + 3 + 1 = 11 |
| `(f')⁴·f` | T9 (mk[mk[mk[cherry]]], σ=1, γ=120) | 1 |

All five sums match cycle 259's Bell coefficients `(1, 7, 4, 11, 1)`
verbatim. The cycle 269 worker already verified this on paper;
cycle 270 worker must confirm the `ring` step closes the residual
identity without coefficient drift.

### §2.6 Close via `IsBigO.congr'`

The new statement's residual `yex(x₀+h) - bseriesExactPartialSum f
y₀ h S` differs from cycle 259's
`yex(x₀+h) - <closed-form polynomial>` only by definitional
equality (via the `_insert`/`_singleton` unfolds + per-tree closed
forms + `smul_eq_mul` + `ring`).

Closure tactic mirrors cycle 268:

```lean
have hbase := lem_311A_order_five hf hyex_x₀ hyex_C6 hyex_ode
refine hbase.congr' ?_ Filter.EventuallyEq.rfl
filter_upwards with h
-- Goal: yex (x₀ + h) - bseriesExactPartialSum ... = yex (x₀ + h) - <closed form>
congr 1
-- Goal: bseriesExactPartialSum ... = <closed form>
rw [bseriesExactPartialSum_insert ...] -- ×16
rw [bseriesExactPartialSum_singleton]
rw [bseriesExactTerm_vertex,
    bseriesExactTerm_cherry_scalar,
    bseriesExactTerm_broom₃_scalar,
    bseriesExactTerm_mkCherry_scalar,
    bseriesExactTerm_bushy_scalar,
    bseriesExactTerm_mkVertexCherry_scalar,
    bseriesExactTerm_mkBroom₃_scalar,
    bseriesExactTerm_mkMkCherry_scalar,
    bseriesExactTerm_bushy₄_scalar,
    bseriesExactTerm_mkVertexVertexCherry_scalar,
    bseriesExactTerm_mkVertexBroom₃_scalar,
    bseriesExactTerm_mkVertexMkCherry_scalar,
    bseriesExactTerm_mkCherryCherry_scalar,
    bseriesExactTerm_mkBushy_scalar,
    bseriesExactTerm_mkMkVertexCherry_scalar,
    bseriesExactTerm_mkMkBroom₃_scalar,
    bseriesExactTerm_mkMkMkCherry_scalar]
simp only [smul_eq_mul]
ring
```

**Pre-flagged risk R2**: The final `ring` may time out if the
expression is large (17 terms × 5 derivatives). If so, decompose
into per-order groupings (`ring_nf` then `linarith`-style sum
identities) OR factor out `h^k` from each order's contribution to
shrink the per-monomial `ring` problem.

## §3 What NOT to try

1. **Do NOT attempt the polymorphic-`E` lift of any per-tree closed
   form.** Cycle 265's HIGH-risk flag on multilinear-map plumbing
   for arbitrary `E : Type*` is still live. This is cycle 271+
   scope and requires its own multi-cycle plan.

2. **Do NOT define new `RootedTree` aliases.** All 17 trees needed
   for the bridge already have either the canonical `mk [...]`
   form or established aliases (`vertex`, `cherry`, `broom₃`,
   `bushy`, `bushy₄`).

3. **Do NOT touch the cycle 269 per-tree theorems or rename them.**
   They are axiom-clean and Bell-coefficient verified. Cycle 270
   only consumes them via `rw`.

4. **Do NOT pursue `lem:310B` directly.** The full lem:310B is the
   8–14 cycle multi-phase roadmap in
   `.prover-state/issues/lem_310B_plan.md`. Cycle 270 deliverable
   closes Phase E.1 only; Phase E.2+ is a separate planner call.

5. **Do NOT attempt to compile `OpenMath/Chapter4/Section441.lean`.**
   43 consecutive GPFS timeouts since cycle 182. Skip per
   `.prover-state/issues/cycle_182_gpfs_slowness.md`. Worker MUST
   NOT smoke-test §441 this cycle.

6. **Do NOT raise `maxHeartbeats` above 200000.** If a `simp` or
   `ring` step times out, decompose into named private helpers per
   risk R1/R2 mitigations.

7. **Do NOT introduce sorries.** Cycle 200/201 rollback precedent
   forbids sorry-first scaffolds without a credible single-cycle
   close path. Cycle 268's 8-tree bridge precedent shows the
   17-tree bridge is single-cycle achievable.

8. **Do NOT introduce `axiom`/`constant` declarations.**

9. **Do NOT modify `scripts/autonomous_loop.py`.** Per
   `.prover-state/issues/tautology_scanner_false_positives.md`,
   scanner/prompt-builder issues are loop-maintainer territory.

10. **Do NOT alter cycle 259's `lem_311A_order_five` statement or
    proof.** It is the load-bearing base lemma for the `.congr'`
    closure.

## §4 Faithfulness checks (mandatory before commit)

1. **Statement faithfulness**: the new
   `lem_311A_order_five_partialSum` must be a *restatement* of
   cycle 259's `lem_311A_order_five` using the
   `bseriesExactPartialSum` API, NOT a strengthening or weakening.
   Hypotheses `(hf, hyex_x₀, hyex_C6, hyex_ode)` should match cycle
   259's exactly. Verify by side-by-side diff of the two
   signatures.

2. **Coefficient cross-check**: confirm the 17-tree expansion's
   order-5 polynomial coefficient is exactly cycle 259's
   `(1, 7, 4, 11, 1)`. The table in §2.5 is the source of truth;
   the worker MUST manually verify each per-tree coefficient against
   the corresponding cycle 269 theorem before invoking `ring`.

3. **Axiom check**: `#print axioms
   OpenMath.Chapter3.Section311.lem_311A_order_five_partialSum`
   must return only `[propext, Classical.choice, Quot.sound]`.

4. **Sorry count**: `grep -c sorry OpenMath/Chapter3/Section311.lean`
   must remain 0.

5. **Tautology scanner**:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'
   OpenMath/Chapter3/Section311.lean` must return no hits.

6. **Aggregator check**: `lake env lean OpenMath/Chapter3.lean`
   must succeed.

## §5 LOC budget and abort threshold

- **Statement**: ~25 LOC (mostly the 17-tree Finset literal).
- **Body**: ~450 LOC (cycle 268's 8-tree bridge was ~290 LOC;
  scales roughly linearly per non-membership lemma + per-tree
  substitution; the additional 9 trees add ~160 LOC).
- **Non-vacuity witness (P2)**: ~10 LOC.
- **Total estimate**: ~500 LOC.

**Abort threshold**: if progress stalls at 700 LOC with the bridge
incomplete, ABORT:
- Ship cycle 269's deliverable unchanged (no rollback — it's at
  HEAD).
- Document the stall in `task_results/cycle_270.md` with the
  specific failure mode (e.g., `ring` timeout on 17-monomial
  closure, `simp` blowup on non-membership lemma N).
- Cycle 271 worker re-attempts with the partial draft preserved at
  `.prover-state/cycle_270_partial.lean` (analogous to cycle 182's
  GPFS-blocked draft preservation pattern).

## §6 Verification commands (run at end of cycle)

```bash
lake env lean OpenMath/Chapter3/Section311.lean
grep -c sorry OpenMath/Chapter3/Section311.lean
# expected: 0

echo '#print axioms OpenMath.Chapter3.Section311.lem_311A_order_five_partialSum' \
  | lake env lean --stdin OpenMath/Chapter3/Section311.lean
# expected: [propext, Classical.choice, Quot.sound]

rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section311.lean
# expected: no hits

lake env lean OpenMath/Chapter3.lean
# expected: clean exit
```

## §7 Update commitments after cycle 270 lands

1. **`extraction/formalization_data/lean_status.json`**: `lem:311A`
   row stays `partial` (the full textbook `lem:311A` is the
   combinatorial labelling lemma over `T_S^*` requiring `def:300C`;
   cycle 270 only extends the scalar specialisation chain). Update
   the row's `notes` field to mention the cycle 270 partial-sum
   bridge at order 5.

2. **`plan.md`**: `lem:311A` row's cycle marker bumped from 269 to
   270, with closure note for the 17-tree order-5 partial-sum
   bridge. Sub-bullet noting Phase E.1 is now fully closed up to
   order 5 in the scalar setting.

3. **`.prover-state/issues/lem_310B_plan.md`** §"Phase E.1"
   subsection (after cycle 269 update lines): append a "Cycle 270
   update" noting the 17-tree partial-sum bridge SHIPPED and Phase
   E.1 is fully closed up to order 5 in the scalar setting.

4. **`.prover-state/task_results/cycle_270.md`**: standard cycle
   results template with mandatory faithfulness check section
   confirming the Bell coefficient cross-check (§2.5 of this
   strategy is the template).

**Do NOT update `lean_status.json` for `lem:310B`** (still
`unformalized` — Phase E.1 closure is one stepping stone of the
multi-phase roadmap, not closure of the headline lemma).

## §8 Suggested cycle 271+ pivot (NOT for this cycle's worker)

After cycle 270 closes Phase E.1 up to order 5, the planner has
three credible directions per cycle 269 task results:

1. **Polymorphic-`E` lift** of cycle 266–269 closed forms (Phase
   D.2 / E.2). MEDIUM-HIGH risk multilinear-map plumbing. Cycle
   265's HIGH-risk flag is still live.

2. **Pivot to `lem:342A`** (shifted Legendre polynomials
   orthogonality on `[0,1]`). Independent single-cycle target per
   `lem_310B_plan.md` §8.2. Recommended if the planner wants a
   clean ship and a break from the §310/§311 thread.

3. **Multi-cycle assault on `lem:310B` Phase A.3** (full recursive
   `TreeAutomorphism` strengthening to close the σ-faithfulness
   gap), per the cycle 261 blueprint and the cycle 264 follow-up
   note in `lem_310B_plan.md`.

Cycle 270 worker does NOT need to make this call — leave it for
cycle 271's planner.
