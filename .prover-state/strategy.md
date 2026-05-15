# Cycle 259 strategy

## Context

Cycle 258 SHIPPED `lem_311A_order_four` (+ private helper
`iteratedDeriv_four_via_ode`) axiom-clean in
`OpenMath/Chapter3/Section311.lean`. Sorry count 0. The order-N
Taylor chain now stands at orders 1 (cycle 248), 2 (cycle 256),
3 (cycle 257), 4 (cycle 258) — four consecutive single-cycle
ships, all axiom-clean.

The cycle 258 worker explicitly flagged "diminishing returns now
genuinely real beyond order 5". The implication: order 5 is the
**last natural mechanical extension** of this chain. After order 5,
substantive §311 work requires `lem:310B` infrastructure (labelled
rooted-tree quotients + B-series sum machinery), which is multi-cycle.

**No Aristotle results pending. No sorries to incorporate.**

## P1 (primary, ship this) — `lem_311A_order_five`

Ship the order-5 Taylor specialisation of `lem:311A` in
`OpenMath/Chapter3/Section311.lean` immediately after cycle 258's
`lem_311A_order_four`, following the mechanical port pattern of
cycles 257 → 258. Axiom-clean expected; sorry count stays 0.

### Verified Bell coefficients (DO NOT use the cycle 258 worker's hint)

The cycle 258 task results §"Suggested next approach" wrote
"Bell coefficients 1, 11, 7, 26, 1 — verify before porting".
**These coefficients are WRONG.** I re-derived from scratch
by differentiating cycle 258's order-4 closed form once more
under `y' = f(y)`:

```
iteratedDeriv 4 yex = f'''·f³ + 4·f''·f'·f² + (f')³·f
```

Differentiating term-by-term (using `d/dt g(y) = g'(y)·f(y)` and
the product rule):

- `d/dt[f'''(y)·f(y)³] = f''''·f⁴ + 3·f'''·f'·f³`
- `d/dt[4·f''(y)·f'(y)·f(y)²] = 4·f'''·f'·f³ + 4·f''²·f³ + 8·f''·f'²·f²`
- `d/dt[(f'(y))³·f(y)] = 3·f''·f'²·f² + (f')⁴·f`

Summing (with all derivatives evaluated at `y₀` after collapsing
via `yex x₀ = y₀` + `hyex_ode`):

```
iteratedDeriv 5 yex x₀
  = f''''(y₀)·f(y₀)⁴
    + 7·f'''(y₀)·f'(y₀)·f(y₀)³
    + 4·f''(y₀)²·f(y₀)³
    + 11·f''(y₀)·f'(y₀)²·f(y₀)²
    + f'(y₀)⁴·f(y₀)
```

**Correct coefficient list: 1, 7, 4, 11, 1.** (Worker's
"1, 11, 7, 26, 1" had the middle three wrong — 11/7 swapped,
4 became 26.) Independently re-derive on paper before keying
anything in, but trust these over the cycle 258 task results.

The order-5 B-series truncation (RHS of the headline `IsBigO`):

```
y₀ + h·f(y₀)
  + (h²/2)·f'(y₀)·f(y₀)
  + (h³/6)·(f''(y₀)·f(y₀)² + f'(y₀)²·f(y₀))
  + (h⁴/24)·(f'''(y₀)·f(y₀)³ + 4·f''(y₀)·f'(y₀)·f(y₀)² + f'(y₀)³·f(y₀))
  + (h⁵/120)·(f''''(y₀)·f(y₀)⁴ + 7·f'''(y₀)·f'(y₀)·f(y₀)³
              + 4·f''(y₀)²·f(y₀)³ + 11·f''(y₀)·f'(y₀)²·f(y₀)²
              + f'(y₀)⁴·f(y₀))
```

Residual is `=O[nhds 0] (fun h => h^(5+1))`.

### Hypotheses

Mirror cycle 258 with the regularity bumped one step:

- `(hf_C4 : ContDiff ℝ 4 f)` — one more order than cycle 258
  (`ContDiff ℝ 3 f`).
- `(hyex_x₀ : yex x₀ = y₀)` — unchanged.
- `(hyex_C6 : ContDiff ℝ 6 yex)` — one more than cycle 258
  (`ContDiff ℝ 5 yex`), to match `taylor_isLittleO (n := 6)`.
- `(hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x)` — unchanged.
- Stay scalar `f : ℝ → ℝ`, `yex : ℝ → ℝ` (cycle 257/258 convention).

### Mechanical recipe (port cycle 258 verbatim with one extra layer)

1. **Helper `iteratedDeriv_five_via_ode`** (private). Pattern: extend
   cycle 258's function-level identity machinery one more order.
   Concretely:
   - Reuse `(hyex_ode x).deriv` (`deriv yex = f ∘ yex`) at function level.
   - Establish three function-level identities, lifting cycle 258's
     pointwise arguments to every `x`:
     * `iteratedDeriv 2 yex = fun x => deriv f (yex x) * f (yex x)`
     * `iteratedDeriv 3 yex = fun x => f''(y) · f(y)² + (f'(y))² · f(y)`
     * `iteratedDeriv 4 yex = fun x => f'''(y) · f(y)³
                                       + 4·f''(y)·f'(y)·f(y)²
                                       + (f'(y))³·f(y)`
   - Peel `iteratedDeriv 5 yex x₀ = deriv (iteratedDeriv 4 yex) x₀`
     via `iteratedDeriv_succ`.
   - Differentiate the three-term sum from the order-4 identity using
     `deriv_add` × 2 + `deriv_mul` (for products of two functions)
     and `deriv_fun_pow` (for `f(y)^k` factors, `k ∈ {2, 3}`).
   - Each `deriv f^(k)(y)` chain step: `deriv_comp` + `(hyex_ode x).deriv`.
   - For `Differentiable ℝ (deriv (deriv (deriv f)))`, use
     `hf_C4.deriv'.deriv'.differentiable_deriv_two`. Cycle 258
     discovery: `ContDiff.deriv'` reduces `ContDiff ℝ (n+1) f`
     to `ContDiff ℝ n (deriv f)`, composing cleanly. One more
     application than cycle 258.
   - Close with `ring`.

2. **Main theorem `lem_311A_order_five`**: mechanical port of cycle
   258 with:
   - `taylor_isLittleO (n := 6)` (one more than cycle 258's `n := 5`).
   - One extra `Finset.sum_range_succ` unfold in `hT_eval`.
   - New sextic-residual `O(h⁶)` step using
     `Asymptotics.isBigO_const_mul_self` on
     `(h⁶/720)·iteratedDeriv 6 yex x₀`.
   - Identify `iteratedDeriv {1,2,3,4} yex x₀` via cycle 248's
     `F_tau_eval`, cycle 256/257's helper structure, and cycle 258's
     `iteratedDeriv_four_via_ode`. Identify `iteratedDeriv 5 yex x₀`
     via the new `iteratedDeriv_five_via_ode`.
   - Collapse `h^(5+1) = h^6` by `funext` / `ring`.

3. **Non-vacuity example.** Reuse cycle 258's pattern:
   ```lean
   example (y₀ x₀ : ℝ) :
     ∃ _ : True, ... := by
     constructor
     · trivial
     · -- apply lem_311A_order_five with f := fun _ => 0,
       -- yex := fun _ => y₀
       ...
   ```
   Hypotheses discharged via `contDiff_const` and `hasDerivAt_const`.
   Residual collapses to identically zero; `IsBigO` closes by
   `Asymptotics.isBigO_zero` after the closed-form RHS reduces to `y₀`.

### Risks (pre-flagged)

- **R1 (Bell coefficient typo)**: If the worker uses the cycle 258
  hint's "1, 11, 7, 26, 1" instead of the verified "1, 7, 4, 11, 1",
  `ring` will fail to close `hderiv5_x0` because the polynomial
  identity won't match. **Mitigation**: copy the coefficients from
  the P1 §"Verified Bell coefficients" subsection above; ignore the
  cycle 258 task-results hint.
- **R2 (`hf_C4.deriv'.deriv'.differentiable_deriv_two` lookup)**: This
  is the cycle 258-discovered idiom — verify it composes for one more
  layer. If it doesn't fire (e.g. Mathlib API drift), fall back to
  `differentiable_iteratedDeriv` with explicit unfolding via
  `iteratedDeriv_succ`.
- **R3 (`taylor_isLittleO (n := 6)`)**: One more `Finset.sum_range_succ`
  unfold than cycle 258. The `hT_eval` simp-expansion should still
  close cleanly; if it stalls, factor into helper sub-steps.
- **R4 (heartbeat overrun)**: Order-5 is the largest expansion yet.
  If a single proof step overflows 200000 heartbeats (CLAUDE.md
  ceiling), decompose via private helpers — separate the algebraic-
  identity step from the Taylor-application step (cycle 150's
  `matrix7_oneMinusZSmul_det` precedent).
- **R5 (universe / NormedSpace generalisation)**: Stay scalar
  `ℝ → ℝ` per cycles 257/258; do not attempt to generalise.

## P2 stretch (only if P1 lands quickly) — Scope cycle 260+ pivot

Write a new markdown-only issue file at
`.prover-state/issues/lem_310B_plan.md` containing:

1. **Textbook target.** Quote the exact statement of `lem:310B` from
   `extraction/formalization_data/entities/lem_310B.json` and from
   `extraction/raw_text/ch03.txt` (Butcher §310 around p. 167).

2. **Infrastructure inventory.** Enumerate what's already shipped in
   `OpenMath/Chapter3/Section301.lean` and Section311 that supports
   `lem:310B`:
   - `RootedTree`, `density`, `symmetry`, `alphaWeight` (cycles 017,
     030, 250, 251).
   - `theta_eq_one` (cycle 249).
   - `bseriesTerm`, `bseriesAlphaTerm`, `bseriesPartialSum`,
     `bseriesAlphaPartialSum`, `TruncatedRootedTree` (cycles 254–256).
   - `lem_311A_order_one` through `_order_five` (after cycle 259).
   - `elementaryDiff` (cycle 030).

3. **Missing infrastructure.** Identify the gaps:
   - `def:300C` labelled rooted-tree quotient (`LabelledTree`,
     automorphism group, σ-witness Finset enumeration).
   - The `T_S^*`-indexed sum structure (Butcher §310 page 167).
   - The combinatorial bridge from `α(t)`'s closed form
     `r(t)!/(σ(t)·γ(t))` to the labelled-tree count.

4. **Phased plan.** Sketch a 5–8 cycle decomposition with concrete
   deliverables per cycle. Each cycle must ship axiom-clean and have
   a credible single-cycle close — no multi-cycle sorries (cf. cycles
   200/201 rollback precedent for `thm:381H`).

5. **Cycle 260 entry-point recommendation.** Either:
   - (a) Start with `def:300C` (labelled-tree quotient scaffolding),
     or
   - (b) Pivot to a fresh entity (`lem:342A`/`lem:342B`/`thm:351B`/
     `thm:317A`) and defer `lem:310B` until the labelled-tree
     infrastructure is naturally pulled in. For each pivot candidate,
     quote one sentence from its JSON entity file showing why it
     doesn't depend on `lem:310B` (or admit it does).

Keep it under 400 LOC of markdown. **Do not write Lean code for P2.**

## What NOT to do this cycle

- **Do NOT use the cycle 258 worker's "1, 11, 7, 26, 1" coefficient
  hint.** Use the verified "1, 7, 4, 11, 1" coefficients from P1's
  §"Verified Bell coefficients" subsection.
- **Do NOT attempt `lem_311A_order_six` or higher.** The chain
  terminates at order 5 by deliberate cutoff.
- **Do NOT attempt full `lem:310B` Lean code this cycle.** P2 is
  markdown-only scoping; commit to the labelled-tree infrastructure
  build only after cycle 260's planner picks it as the target.
- **Do NOT introduce sorries** anywhere in the codebase. CLAUDE.md
  forbids; precedent cycles 138/149/200/201 all rolled back sorry-first
  scaffolds. If `lem_311A_order_five` doesn't close cleanly within
  budget, revert and ship P2 only.
- **Do NOT compile `OpenMath/Chapter4/Section441.lean`.** 43 consecutive
  GPFS timeouts (cycles 182–239). See
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.
- **Do NOT attempt the `Equivalent → PhiEquivalent` bridge** for
  `thm:381H` — still multi-cycle Banach-machinery work per
  `.prover-state/issues/thm_381H_deferred.md`.
- **Do NOT raise `maxHeartbeats` above 200000.** If a `ring` or
  `taylor_isLittleO` step overflows, decompose via private helpers
  (cycle 150 / cycle 158 / cycle 160 precedent).
- **Do NOT edit `scripts/autonomous_loop.py`.** Tautology-scanner
  false positives are loop-maintainer territory; see
  `.prover-state/issues/tautology_scanner_false_positives.md`.
- **Do NOT generalise** `lem_311A_order_five` to `N : Type*` with
  `[NormedAddCommGroup N] [NormedSpace ℝ N]`. Cycles 257/258 stayed
  scalar `ℝ → ℝ`; maintain the convention.
- **Do NOT touch cycle 258's `lem_311A_order_four` or
  `iteratedDeriv_four_via_ode`.** They are axiom-clean and load-bearing
  for cycle 259's `hderiv4_x0` reference inside the new helper.
- **Do NOT submit `lem_311A_order_five` to Aristotle.** The mechanical
  port pattern is well-established (4 consecutive single-cycle ships);
  Aristotle latency would slow rather than help.

## Verification checklist (post-edit, before commit)

1. `lake env lean OpenMath/Chapter3/Section311.lean` — exit 0.
2. `lake env lean OpenMath/Chapter3.lean` (aggregator) — exit 0.
3. `lake build OpenMath.Chapter3.Section311` — exit 0 (refresh `.olean`).
4. `grep -c sorry OpenMath/Chapter3/Section311.lean` — `0`.
5. `#print axioms OpenMath.Chapter3.Section311.lem_311A_order_five`
   → `[propext, Classical.choice, Quot.sound]` only.
6. `#print axioms OpenMath.Chapter3.Section311.lem_311A_order_four`
   unchanged from cycle 258 (`[propext, Classical.choice, Quot.sound]`).
7. Tautology scanner regex
   `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` on
   `OpenMath/Chapter3/Section311.lean` — no matches.
8. Non-vacuity `example` for `lem_311A_order_five` compiles.

## Faithfulness notes

`lem_311A_order_five` is the **fifth specialisation** in the
order-N partial-formalisation chain of `lem:311A`. The full textbook
statement (labelled-tree quotient `T_S^*` indexed sum, see
`entities/lem_311A.json`) remains unformalized — multi-cycle scope
gated on `def:300C`. Cycle 259's deliverable captures the
order-5 Taylor-polynomial *consequence* of `lem:311A` along
autonomous ODE `y' = f(y)`, exactly as cycles 248/256/257/258 did
for orders 1/2/3/4.

`lean_status.json` row for `lem:311A` stays `unformalized` per the
cycle 248 convention. Update only the cycle 259 progress note in
`plan.md` (mention `lem_311A_order_five` shipped, sextic-residual
`O(h⁶)` bound, completing the deliberate-cutoff order-N chain).

The private helper `iteratedDeriv_five_via_ode` carries no entity
ID and needs no `lean_status` update; it's downstream infrastructure
for the main theorem.

## End-of-cycle checklist

- `lem_311A_order_five` shipped axiom-clean (P1).
- `iteratedDeriv_five_via_ode` private helper landed.
- Non-vacuity `example` in place.
- `plan.md` `lem:311A` row note bumped to cycle 259 (mentioning
  the deliberate stop at order 5).
- (P2 stretch, if landed) `.prover-state/issues/lem_310B_plan.md`
  created with phased multi-cycle scoping.
- `.prover-state/task_results/cycle_259.md` documenting:
  - What was tried.
  - What worked / failed.
  - Faithfulness check on `lem_311A_order_five` and
    `iteratedDeriv_five_via_ode`.
  - Dead ends (if any).
  - Discovery (e.g. confirmation of Bell coefficients 1/7/4/11/1
    — flag the cycle 258 task-results hint as wrong).
  - Suggested cycle 260 approach (pivot decision: lem:310B
    infrastructure vs fresh entity).
- Sorry count repo-wide remains 0.
- Commit message format: `Cycle 259 — §311 lem_311A_order_five
  + iteratedDeriv_five_via_ode SHIPPED.`
