# Cycle 258 Strategy

## A. State at cycle start

- Branch tip: `01f9ab1 Cycle 257 — §311 lem_311A_order_three SHIPPED`.
- Sorry count: 0 across the repo.
- No pending Aristotle results.
- Cycles 248 / 256 / 257 shipped `lem_311A_order_one` / `_two` / `_three`
  in `OpenMath/Chapter3/Section311.lean`. Each is a Taylor specialisation
  for `ℝ → ℝ` scalars, axiom-clean. The recipe is now mechanical: bump
  `taylor_isLittleO (n := k+1)`, add one chain-rule helper for
  `iteratedDeriv k yex x₀`, evaluate Taylor polynomial, translate to
  `nhds 0`, decompose into Taylor-residual + leading polynomial term,
  combine via `IsLittleO.isBigO.add`, collapse `h^(p+1)`.
- Cycle 256 shipped α-weighted B-series machinery
  (`bseriesAlphaTerm`, `bseriesAlphaPartialSum`) in
  `OpenMath/Chapter3/Section301.lean`; cycle 256 P3 added a thin
  cross-section bridge in Section311.

## B. Pre-flight investigation — why we are NOT pivoting away from §311

Cycle 257 task results §"Suggested next approach" listed three
candidates: (1) polymorphic refactor of the order-1/2/3 trio
(multi-cycle); (2) small-`r` `lem:310B` cases (multi-cycle, blocked on
labelled-tree machinery); (3) pivot to `lem:312B` or `lem:313A`.

Direct entity inspection (`extraction/formalization_data/entities/`):

* `lem:312B` (Elementary Weight Summation Formula) and `lem:313A`
  (Taylor expansion of approximate solution) **both** list `lem:310B`
  as a transitive dependency. Their textbook proofs explicitly invoke
  Lemma 310B (see `proof_text` field). `lem:310B` is unformalized and
  multi-cycle (requires labelled rooted-tree quotient `def:300C`, not
  built).
* Therefore neither `lem:312B` nor `lem:313A` is single-cycle
  shippable in faithful form. A surface-level "lift to Lean" without
  consuming the genuine combinatorial content would be definition
  smuggling (rule violation per CLAUDE.md and
  `feedback_planner_faithfulness_spotcheck.md`).

The polymorphic refactor (option 1) is genuinely valuable but
multi-cycle. The right single-cycle deliverable is therefore to
**continue the order-N Taylor chain at order 4** — mechanical port of
cycle 257, axiom-clean by construction, sorry count stays 0.

## C. P1 (mandatory) — Ship `lem_311A_order_four`

Add to `OpenMath/Chapter3/Section311.lean`, immediately after cycle
257's `lem_311A_order_three`. Shape mirrors cycle 257 with one extra
chain-rule layer.

### C.1 Private chain-rule helper `iteratedDeriv_four_via_ode`

Establish the closed form of `iteratedDeriv 4 yex x₀` under the
autonomous ODE constraint. Differentiate cycle 257's closed form of
`iteratedDeriv 3 yex` (viewed pointwise) along the ODE.

**Paper derivation** (verify on paper, then port to Lean):
Let `G(y) := f''(y)·f(y)² + f'(y)²·f(y)`. Then
`d/dx G(yex(x)) = G'(yex)·yex' = G'(yex)·f(yex)`.

`G'(y) = f'''(y)·f(y)² + f''(y)·2·f(y)·f'(y)
       + 2·f'(y)·f''(y)·f(y) + f'(y)²·f'(y)
       = f'''(y)·f(y)² + 4·f''(y)·f'(y)·f(y) + f'(y)³`.

So:
```
iteratedDeriv 4 yex x₀
  = G'(y₀) · f(y₀)
  = f'''(y₀) · f(y₀)³
    + 4 · f''(y₀) · f'(y₀) · f(y₀)²
    + f'(y₀)³ · f(y₀)
```

**Lean proof sketch** (verify each step with `lean_hover_info` /
`lean_loogle` before commit):

1. `iteratedDeriv 4 yex x₀ = deriv (iteratedDeriv 3 yex) x₀`
   via `iteratedDeriv_succ`.
2. Pointwise identification of `iteratedDeriv 3 yex` as a function:
   ```
   (iteratedDeriv 3 yex : ℝ → ℝ)
     = fun x => deriv (deriv f) (yex x) * f (yex x) ^ 2
              + deriv f (yex x) ^ 2 * f (yex x)
   ```
   via `funext` + cycle 257's chain-rule argument at every `x`
   (not just `x₀`).
3. `deriv_add` to split the sum, then `deriv_mul` × 2 to break each
   product. Each subterm reduces to `deriv (g ∘ yex) x₀` for some
   `g`, then `deriv_comp` and `(hyex_ode x₀).deriv` and
   `rw hyex_x₀` finish.
4. `ring` aggregates into the four-term expression above.

Hypothesis profile (verify minimum required):
- `ContDiff ℝ 3 f` — needed for `Differentiable ℝ (deriv (deriv f))`,
  the second-derivative differentiability for the inner chain rule.
- `ContDiff ℝ 5 yex` — needed for `taylor_isLittleO (n := 5)` plus
  the order-4 chain-rule evaluation.
- `yex x₀ = y₀` (carried from cycle 257).
- `∀ x, HasDerivAt yex (f (yex x)) x` (autonomous ODE).

### C.2 Main theorem `lem_311A_order_four`

Signature:
```lean
theorem lem_311A_order_four
    {f : ℝ → ℝ} (hf_C3 : ContDiff ℝ 3 f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C5 : ContDiff ℝ 5 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h : ℝ => yex (x₀ + h) -
        (y₀
          + h * f y₀
          + h ^ 2 / 2 * (deriv f y₀ * f y₀)
          + h ^ 3 / 6 * (deriv (deriv f) y₀ * f y₀ ^ 2
                         + deriv f y₀ ^ 2 * f y₀)
          + h ^ 4 / 24 * (deriv (deriv (deriv f)) y₀ * f y₀ ^ 3
                          + 4 * deriv (deriv f) y₀ * deriv f y₀ * f y₀ ^ 2
                          + deriv f y₀ ^ 3 * f y₀)))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (4 + 1))
```

Body recipe verbatim from cycle 257 with these mechanical edits:

* `taylor_isLittleO (n := 5)` (was 4 in cycle 257).
* `hT_eval` evaluates degree-5 polynomial — one extra
  `Finset.sum_range_succ` unfold beyond cycle 257.
* Reuse `hderiv1_x0`, `hderiv2_x0`, `hderiv3_x0` verbatim from
  cycle 257; add new
  `hderiv4_x0 := iteratedDeriv_four_via_ode hf_C3 hyex_x₀ hyex_C5 hyex_ode`.
* `hdiff_eq` rewrites the goal into Taylor-residual plus
  `h^5 / 120 * iteratedDeriv 5 yex x₀`. We do **not** identify
  `iteratedDeriv 5 yex x₀`'s closed form — we only need the quintic
  residual as `O(h^5)`.
* `hquintic` is
  `(fun h => h^5/120 * iteratedDeriv 5 yex x₀) =O[nhds 0] (fun h => h^5)`
  via `Asymptotics.isBigO_const_mul_self`.
* Final `hres.isBigO.add hquintic`, collapse `h ^ (4 + 1) = h ^ 5`
  via `funext` + `ring`.

### C.3 Non-vacuity witness

Add a non-vacuity `example` consuming `lem_311A_order_four` with
`f := 0`, `yex := fun _ => y₀`. The B-series collapses to `y₀`,
residual is identically zero, hypotheses discharge via
`contDiff_const`, `hasDerivAt_const`.

## D. P2 (stretch — only if P1 ships with ≥ 30 min budget) — Table 310(II) α-witness via bseriesAlphaPartialSum

Cycles 252/253 saturated Butcher Table 310(II) rows r=4 and r=5 with
α-witness `example`s on individual trees in Section301. Cycle 256
shipped `bseriesAlphaPartialSum` but no example currently consumes it
at orders > 2.

Add **one** axiom-clean `example` (in Section301 or Section311 —
worker's choice based on imports) showing that
`bseriesAlphaPartialSum f y₀ h S` at `S := {vertex, cherry, broom₃}`
equals the explicit cubic expansion. The α-values for these three trees
are all 1 (cycle 251 witnesses), so the partial sum simplifies to
`bseriesAlphaTerm f y₀ h vertex + bseriesAlphaTerm f y₀ h cherry
+ bseriesAlphaTerm f y₀ h broom₃`. Close via
`bseriesAlphaPartialSum_insert` × 2 + `bseriesAlphaPartialSum_empty`
+ `ring`.

**Do NOT** attempt a labelled-tree-counted summation — that is the
`lem:310B` content and is multi-cycle blocked.

**Do NOT** attempt to connect this partial sum to
`lem_311A_order_three`'s Taylor residual — the bridge requires
`F(t)(y₀)` evaluation lemmas at `cherry` and `broom₃`, which is
cycle 259+ infrastructure (each tree's `F`-value needs to match a
specific composition of `f`/`f'`/`f''` evaluated at `y₀`, and the
matching is `lem:310B`-flavoured).

## E. P3 (do NOT attempt) — explicit non-targets

* Do **not** attempt `lem:312B` or `lem:313A`. Both depend on
  `lem:310B`; their textbook proofs route through Lemma 310B
  explicitly. Surface-level reformulations would be definition
  smuggling.
* Do **not** attempt `lem:310B` in any form (general or small-`r`).
  Per `extraction/raw_text/ch03.txt` and cycle 254's strategy, the
  LHS requires labelled rooted-tree quotient infrastructure
  (`def:300C`) not built; ~5–8 cycles total.
* Do **not** attempt the polymorphic refactor of the
  `lem_311A_order_one/two/three/four` family. The
  `iteratedDeriv` → `iteratedFDeriv` bridge is genuinely multi-cycle
  and the `ContinuousMultilinearMap` plumbing is heavy. Single-cycle
  attempts will stall.
* Do **not** compile `OpenMath/Chapter4/Section441.lean`. Per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`, 43+ consecutive
  GPFS timeouts. Skip the smoke test entirely; cycle 258 has no
  §441 deliverable.
* Do **not** introduce new sorries. Sorry count must remain 0
  (cycle 200/201 rollback precedent — sorry-first scaffolds without
  a credible single-cycle close are rejected by the supervisor).
* Do **not** raise `maxHeartbeats`. If `ring` stalls at degree 5,
  decompose by adding an intermediate `hT_eval_step` lemma to split
  the long `simp only` chain in `hT_eval`.
* Do **not** edit `scripts/autonomous_loop.py` (tautology scanner
  false-positive bug remains loop-maintainer territory per
  `.prover-state/issues/tautology_scanner_false_positives.md`).

## F. Faithfulness rules

For `lem_311A_order_four`:

* Entity ID: `lem:311A` (continues the partial-formalisation chain
  documented in `plan.md`).
* Faithfulness divergences inherited from cycles 248/256/257:
  - `ℝ → ℝ` scalar form (vs textbook's polymorphic `N`-valued).
  - Closed-form chain-rule expression (vs textbook's elementary-
    differential notation `F(τ)`, `F([τ])`, etc.). At orders 1–4,
    each elementary differential term `F(t)(y₀)` corresponds 1:1 to
    a specific composition of `f`, `f'`, `f''`, `f'''` evaluated at
    `y₀`.
* `lean_status.json` row for `lem:311A` stays `unformalized` per
  cycles 248/256/257 convention. Only Taylor specialisations are
  shipped; full combinatorial labelling content (`def:300C` +
  `T_S^*` enumeration) remains absent.

For `iteratedDeriv_four_via_ode`:
* Private helper. No textbook entity. No status update needed.
* `ContDiff ℝ 3 f` and `ContDiff ℝ 5 yex` are the minimum
  regularity (one more order of each than cycle 257). Document in
  docstring.

## G. Mandatory pre-commit checks

After writing the proofs, run:

1. `lake env lean OpenMath/Chapter3/Section311.lean` — must exit 0
   (clean compile of the affected file).
2. `lake env lean OpenMath/Chapter3.lean` — must exit 0 (aggregator
   build, catches downstream breakage).
3. `grep -c sorry OpenMath/Chapter3/Section311.lean` — must equal 0.
4. `#print axioms` on `lem_311A_order_four` and
   `iteratedDeriv_four_via_ode` — must return
   `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
5. Tautology scanner regex check via Grep:
   pattern `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`
   on `OpenMath/Chapter3/Section311.lean` — must return no matches.
6. Regression-check cycle 257's `lem_311A_order_three` axiom-clean
   status (`#print axioms`) — should be unchanged.
7. Update `.prover-state/task_results/cycle_258.md` with full
   deliverable record per the §"Task Results Format" template in
   CLAUDE.md.

## H. Risk register

* **R1 (medium)**: `iteratedDeriv_four_via_ode`'s differentiability
  obligations may not match Mathlib's API surface exactly.
  Mitigation: early in the cycle, search via
  `lean_loogle "ContDiff _ 3 _ → Differentiable _ (deriv (deriv _))"`
  and `lean_hover_info` on candidate names; if the convenient API
  isn't there, fall back to chaining manual
  `hf_C3.differentiable_one` / `(hf_C3.deriv_of_lt 3 …).differentiable`
  calls. Worst case ~30 LOC of explicit differentiability plumbing.
* **R2 (low)**: `deriv_mul` on a sum-of-two-products may require
  explicit `Differentiable.add` plumbing before `deriv_mul` fires.
  Mitigation: introduce intermediate `have hsum_diff : Differentiable
  ℝ (fun x => ...) := Differentiable.add ...` step.
* **R3 (low)**: `hT_eval`'s `ring` step at degree 5 may be slow.
  Mitigation: if `ring` stalls past 30 seconds, factor the closed
  form into a `show` step that pre-computes the polynomial in
  `hT_eval`'s body and use `linarith`/`field_simp` instead. If still
  too slow, split `hT_eval` into two halves (degree-3 partial +
  degree-4/5 correction).
* **R4 (low)**: tautology-scanner false-positive flag on bindings
  like `hderiv4_x0 := iteratedDeriv_four_via_ode ...`. Mitigation:
  name the binding `hderiv4_x0` WITHOUT a leading underscore
  (cycle 257 used `hderiv1_x0`, `hderiv2_x0`, `hderiv3_x0` — same
  pattern); if the scanner still flags it, switch to
  `have hderiv4 := ...` followed by `set hderiv4_x0 := hderiv4` or
  inline the expression at the use site.

## I. Cycle 259+ outlook

After cycle 258 closes (whether shipping P1 alone or P1 + P2), three
viable next moves:

1. **Order-5 Taylor** — continues the chain. The order-5 chain rule
   has a 5-term Bell-style expansion; one more layer of mechanical
   work. Diminishing returns are now genuinely real beyond order 5.
2. **Plan a multi-cycle assault on `lem:310B` infrastructure** — scope
   the labelled rooted-tree machinery (`def:300C`-like vertex set
   indexing) in a new issue file first; commit to a 5–8 cycle plan
   before writing code. This is the highest-leverage long-term move.
3. **Pivot to a §3 entity independent of `lem:310B`**. Candidates
   (verify entity JSONs first):
   - `thm:351B` (A-stability criterion for RK methods).
   - `lem:342A` / `lem:342B` (Gaussian quadrature; check whether
     they need `def:310A` machinery).
   - `thm:317A` (Independence of elementary weights) — likely
     `lem:310B`-blocked, verify.

Cycle 258's planner can pick freely from these. Order-4 should be
shipped clean before any planning pivot is committed.

## J. Decisive directive

**Ship `lem_311A_order_four` + `iteratedDeriv_four_via_ode` in
`OpenMath/Chapter3/Section311.lean` axiom-clean, sorry count 0.**
P2 (Table 310(II) order-3 partial-sum witness) is optional; skip if
budget is tight. P3 targets are off-limits.
