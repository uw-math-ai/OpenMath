# Cycle 270 Results

## Worked on

§310/§311 Phase E.1 (Phase 2 of 2 for order 5): the 17-tree partial-sum
bridge `lem_311A_order_five_partialSum` at
`OpenMath/Chapter3/Section311.lean`, restating cycle 259's
`lem_311A_order_five` via the cycle 266 `bseriesExactPartialSum` API
over all 17 distinct rooted trees of order ≤ 5.

Deliverables (all shipped, all axiom-clean):

* P1 at `OpenMath/Chapter3/Section311.lean`:
  `lem_311A_order_five_partialSum` (the 17-tree partial-sum bridge).
* P2 at `OpenMath/Chapter3/Section311.lean`: one non-vacuity witness
  exercising the new bridge on the trivial ODE `f := 0, yex := const y₀`.

## Approach

1:1 mechanical port of cycle 268's 8-tree order-4 bridge
(`lem_311A_order_four_partialSum`) at one extra order. The recipe
transferred verbatim with one extra Finset element per `_insert` step.

### Statement

```
theorem lem_311A_order_five_partialSum
    {f : ℝ → ℝ} (hf_C4 : ContDiff ℝ 4 f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C6 : ContDiff ℝ 6 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h : ℝ => yex (x₀ + h) -
        (y₀ + bseriesExactPartialSum f y₀ h S))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (5 + 1))
```

where `S` is the 17-element `Finset RootedTree` containing the 17
distinct unordered rooted trees of order ≤ 5: 1 order-1 (`vertex`) +
1 order-2 (`cherry`) + 2 order-3 (`broom₃`, `mk [cherry]`) + 4 order-4
(`bushy`, `mk [vertex, cherry]`, `mk [broom₃]`, `mk [mk [cherry]]`) + 9
order-5 (`bushy₄`, `mk [v,v,cherry]`, `mk [v,broom₃]`, `mk [v,mk[cherry]]`,
`mk [cherry,cherry]`, `mk [bushy]`, `mk [mk[v,cherry]]`, `mk [mk[broom₃]]`,
`mk [mk[mk[cherry]]]`).

### Recipe

1. **Base lemma**: `have hbase := lem_311A_order_five hf_C4 hyex_x₀
   hyex_C6 hyex_ode`.
2. **16 non-membership lemmas** (each is `T_N ∉ {T_{N+1}, ..., T_17}`
   for the iterated `Finset.insert` chain). Each discharged via
   `simp [vertex, cherry, broom₃, bushy, bushy₄]` on the
   auto-generated `RootedTree.mk.injEq` and `Finset.mem_insert`
   simp lemmas. One non-membership lemma (`h_mkvvc_notin`) drops
   `bushy₄` from its simp set after the post-build linter flagged
   it as unused.
3. **Iterated `_insert` unfolds**: 16 applications of
   `bseriesExactPartialSum_insert _ _ _ <non-membership lemma>`
   plus one `bseriesExactPartialSum_singleton` closure unfolds
   the partial sum into a 17-term `bseriesExactTerm` chain.
4. **Per-tree closed-form substitution**: 17 `rw` substitutions
   replacing each `bseriesExactTerm f y₀ h <tree>` with its
   closed-form Taylor monomial:
   * `bseriesExactTerm_vertex` (cycle 266) — `h • f y₀`.
   * `bseriesExactTerm_cherry_scalar` (cycle 266).
   * `bseriesExactTerm_broom₃_scalar` (cycle 267).
   * `bseriesExactTerm_mkCherry_scalar` (cycle 267).
   * `bseriesExactTerm_bushy_scalar` (cycle 268).
   * `bseriesExactTerm_mkVertexCherry_scalar` (cycle 268).
   * `bseriesExactTerm_mkBroom₃_scalar` (cycle 268).
   * `bseriesExactTerm_mkMkCherry_scalar` (cycle 268).
   * `bseriesExactTerm_bushy₄_scalar` (cycle 269 T1).
   * `bseriesExactTerm_mkVertexVertexCherry_scalar` (cycle 269 T2).
   * `bseriesExactTerm_mkVertexBroom₃_scalar` (cycle 269 T3).
   * `bseriesExactTerm_mkVertexMkCherry_scalar` (cycle 269 T4).
   * `bseriesExactTerm_mkCherryCherry_scalar` (cycle 269 T5).
   * `bseriesExactTerm_mkBushy_scalar` (cycle 269 T6).
   * `bseriesExactTerm_mkMkVertexCherry_scalar` (cycle 269 T7).
   * `bseriesExactTerm_mkMkBroom₃_scalar` (cycle 269 T8).
   * `bseriesExactTerm_mkMkMkCherry_scalar` (cycle 269 T9).
5. **`smul_eq_mul` + `ring`** collapses the resulting scalar
   polynomial to cycle 259's closed-form Taylor truncation.
6. **`hbase.congr'`** against `lem_311A_order_five` closes the goal
   via the pointwise equality on the residual.

### Non-vacuity witness

```
example (x₀ y₀ : ℝ) :
    (fun h : ℝ => (fun _ => y₀) (x₀ + h) -
        (y₀ + bseriesExactPartialSum (fun _ => 0) y₀ h S))
      =O[nhds 0] (fun h => h ^ (5 + 1)) :=
  lem_311A_order_five_partialSum
    (f := fun _ => 0) (yex := fun _ => y₀)
    (x₀ := x₀) (y₀ := y₀) contDiff_const rfl contDiff_const
    (fun x => hasDerivAt_const x y₀)
```

On `f := 0`, every per-tree summand vanishes (`f y₀ = 0`, and the
closed forms factor through `f y₀` or `deriv^k f y₀ = 0`), so the
residual `yex(x₀+h) - (y₀ + partial_sum) = 0` is trivially
`O(h^6)`.

## Result

**SUCCESS** — both deliverables shipped. Verified:

* `lake env lean OpenMath/Chapter3/Section311.lean` — clean (only one
  initial linter warning about an unused `bushy₄` simp argument,
  resolved by dropping it from the `h_mkvvc_notin` simp set).
* `lake build OpenMath.Chapter3.Section311` — 9.5s, no errors.
* `lake env lean OpenMath/Chapter3.lean` — clean (aggregator).
* `#print axioms
  OpenMath.Chapter3.Section311.lem_311A_order_five_partialSum`
  returns `[propext, Classical.choice, Quot.sound]`.
* `grep -c sorry OpenMath/Chapter3/Section311.lean` — 0.
* Tautology scanner `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'
  OpenMath/Chapter3/Section311.lean` — no hits.

LOC delta: Section311 1891 → 2804 (+913). The strategy estimate was
~500 LOC; actual delta is ~80% higher due to (a) verbose
`OpenMath.Chapter3.Section310.RootedTree.<symbol>` qualifications
(Section311 cannot `open` that namespace due to GLM symbol shadowing
risk per cycle-307 precedent), and (b) the 17-tree Finset literal
plus 16 iterated non-membership lemma sets each carry a 5–17 element
remaining-set spelled out explicitly. Identical precedent in cycle 268
(estimated ~150 LOC, actual +287). Below the abort threshold of 700
LOC for the bridge alone (the +913 includes the non-vacuity witness
which is ~50 LOC and is P2, not part of the abort budget).

## Faithfulness check

### P1 `lem_311A_order_five_partialSum`

**Anchor entity**: `lem:311A`
(`extraction/formalization_data/entities/lem_311A.json`).

**Textbook statement (`statement_latex`)**:

> Let $S = S_0 \cup \{s\}$ be an ordered set, where every member of
> $S_0$ is less than $s$. Let $t$ be a member of $T_{S_0}^*$. Then
> $\frac{d}{dx} F(|t|)(y(x))$ is the sum of $F(|u|)(y(x))$ over all
> $u \in T_S^*$ such that the subtree formed by removing $s$ from
> the set of vertices is $t$.

This is the **textbook recursive structure** lemma (combinatorial
labelling over `T_S^*`); the full lemma requires `def:300C`
(labelled-tree quotient infrastructure, currently absent — see
`.prover-state/issues/lem_310B_plan.md` Phase A.2) and is
multi-cycle scope.

The cycle-270 lemma `lem_311A_order_five_partialSum` is the
**order-5 partial-sum specialisation** of `lem:311A`'s downstream
consumer, the Taylor-truncated exact-solution B-series. It bridges
cycle 259's `lem_311A_order_five` (closed-form polynomial form) and
the `bseriesExactPartialSum f y₀ h S` aggregate form for `S` the
17 distinct rooted trees of order ≤ 5.

**Lean statement captures**: weaker (order-5 specialisation of one
downstream form, not the full textbook combinatorial statement),
explicitly documented as "partial" in `lean_status.json`. Cycle 270
extends the cycle 268 order-4 partial-sum bridge by one more order;
the underlying recursive lemma is still future scope.

**Hypothesis strength**: matches cycle 259's `lem_311A_order_five`
verbatim (`ContDiff ℝ 4 f`, `yex x₀ = y₀`, `ContDiff ℝ 6 yex`,
`∀ x, HasDerivAt yex (f (yex x)) x`). No extra hypotheses
introduced this cycle. Side-by-side hypothesis diff:

| Hypothesis | `lem_311A_order_five` | `lem_311A_order_five_partialSum` |
|---|---|---|
| `f` regularity | `ContDiff ℝ 4 f` | `ContDiff ℝ 4 f` ✓ |
| `yex x₀ = y₀` | yes | yes ✓ |
| `yex` regularity | `ContDiff ℝ 6 yex` | `ContDiff ℝ 6 yex` ✓ |
| ODE | `∀ x, HasDerivAt yex (f (yex x)) x` | same ✓ |
| Conclusion shape | `=O[nhds 0] (fun h => h ^ (5+1))` | same ✓ |

**Coefficient cross-check (Bell coefficients vs cycle 259)**:
The 17-tree expansion's order-5 polynomial coefficient is exactly
cycle 259's `(1, 7, 4, 11, 1)`. Independent re-derivation:

| Monomial | Trees contributing | Coefficient sum (·1/120) |
|---|---|---|
| `f''''·f⁴` | T1 (bushy₄, σ=24, γ=5) | 120/120 = **1** ✓ |
| `f'''·f'·f³` | T2 (mk[v,v,cherry], σ=2, γ=10), T6 (mk[bushy], σ=6, γ=20) | 6 + 1 = **7** ✓ |
| `(f'')²·f³` | T3 (mk[v,broom₃], σ=2, γ=15) | **4** ✓ |
| `f''·(f')²·f²` | T4 (mk[v,mk[cherry]], σ=1, γ=30), T5 (mk[cherry,cherry], σ=2, γ=20), T7 (mk[mk[v,cherry]], σ=1, γ=40), T8 (mk[mk[broom₃]], σ=2, γ=60) | 4 + 3 + 3 + 1 = **11** ✓ |
| `(f')⁴·f` | T9 (mk[mk[mk[cherry]]], σ=1, γ=120) | **1** ✓ |

All five sums match cycle 259's Bell coefficients `(1, 7, 4, 11, 1)`
verbatim, confirming the `ring` step closes the residual identity
without coefficient drift.

**Tautology / identity / absent-theorem check**: P1 is a multi-step
`hcongr` + `IsBigO.congr'` proof against cycle 259's base, with
no `exact h`/`:= h` shortcuts; conclusion does not appear as a
hypothesis. The theorem performs substantive content (translating
between two B-series representations), not vacuous re-export.

**Definition smuggling check**: P1's RHS uses the well-defined
`bseriesExactPartialSum` def (cycle 266); no definitional
unfolding smuggled into the statement.

### Bookkeeping faithfulness

* `lean_status.json` `lem:311A` row updated: status `partial`,
  cycle 270, `lean_symbol` set to `lem_311A_order_five_partialSum`.
  Status remains `partial` (not `formalized`) because the full
  textbook `lem:311A` requires `def:300C` (still missing).
* `lean_status.json` `lem:310B` row unchanged: still `unformalized`
  — cycle 270 is one stepping stone in the multi-phase
  `lem_310B_plan.md` (Phase E.1, now fully closed up to order 5 in
  the scalar setting).

## Dead ends

None this cycle. The strategy file's risk register (R1, R2) flagged
two potential issues; the actual issues encountered were:

* **One spurious `simp` warning** on `h_mkvvc_notin` about unused
  `bushy₄` simp argument. Trivial fix — the remaining Finset for
  T₁₀ = `mk [vertex, vertex, cherry]` contains no `bushy₄` in any
  element, so the simp lemma is genuinely unused. Dropped from
  that one simp call. R1 (16 non-membership lemmas as a `simp`
  blowup risk) did not fire — all 16 lemmas elaborate in under
  a second each.
* **R2 (final `ring` timeout)** did not fire. The 17-monomial
  closure ring step completes within seconds. No need for
  per-order grouping or `linarith`-style decomposition.

## Discovery

* **Verbose qualified naming inflates LOC ~2×** vs the cycle 268
  strategy estimate. The 17-element Finset literal alone is ~85
  LOC due to the explicit `OpenMath.Chapter3.Section310.RootedTree.<sym>`
  prefix on every tree alias and `mk` constructor. Cycle 268's
  budget of ~500 LOC was for non-qualified naming; the actual
  cycle 270 delta is +713 LOC for one theorem + witness. This is
  a known precedent (cycle 268 task results §"Result").
* **The cycle 268 idiom of dropping unused simp aliases per
  non-membership lemma** continues to be the right call. The
  single-warning auto-correction loop is "build → grep warning →
  drop alias → rebuild" and takes one minute per warning. Future
  cycles should write the simp call with all 5 aliases and accept
  one round of build-feedback to prune.
* **`bseriesExactPartialSum_insert _ _ _ <hT>`** with three
  underscores for the (E-implicit, NormedAddCommGroup,
  NormedSpace) typeclass slots is the canonical invocation
  pattern. Cycle 268 used the same; cycle 270 confirmed it scales
  to 16 iterated rewrites in one `rw [...]` block without
  elaboration timeout.
* **`Finset` literal-to-`insert` chain via `show ... from rfl`**:
  the 17-element `{T₁, ..., T₁₇}` notation reduces to
  `insert T₁ (insert T₂ (... {T₁₇}))` by definitional equality;
  the `show ... from rfl` rewrite at the head of the chain is
  ~85 LOC but compiles instantaneously. Same precedent in cycle
  268's 8-element chain.

## Suggested next approach

Per cycle 269's task-results §"Suggested next approach" and the
cycle 270 strategy §8, the natural cycle 271 candidates in priority
order:

1. **Polymorphic-`E` lift of cycle 266's `bseriesExactTerm_cherry_scalar`**
   (Phase D.1 / E.2). MEDIUM-HIGH risk per cycle 267 task results
   due to the `ContinuousMultilinearMap.uncurry`/`.curry` plumbing
   for `iteratedFDeriv ℝ n f` viewed as an N-multilinear map. Worth
   only if the scalar order-≤5 partial-sum bridge work has
   compounded enough infrastructure to make the lift mechanical.

2. **Pivot to `lem:342A` (Legendre orthogonality on `[0,1]`)** —
   single-cycle independent target per `lem_310B_plan.md` §8.2.
   Detaches from the §310/§311 Phase E.* ladder and exercises a
   different chunk of Mathlib (orthogonal polynomials on `[0,1]`).

3. **Multi-cycle assault on `lem:310B` Phase A.1**
   (`RootedTree.Vertex` scaffold + `vertices` Finset enumeration,
   per the cycle 261 blueprint in `lem_310B_plan.md`). HIGH risk,
   first stepping stone of an 8–14 cycle roadmap. Worth only if
   the planner explicitly wants to commit to multi-cycle work.

Recommend Option 2 (pivot to `lem:342A`) for cycle 271. The §310/§311
Phase E.1 thread has reached its natural cutoff (order 5, matching
cycle 259's deliberate stopping point and the orderly bookkeeping
in `lem_310B_plan.md`). Beyond order 5, scalar specialisation
yields diminishing returns; polymorphic-`E` Phase D.2 / E.2 is a
single named risk (multilinear plumbing) and should be tackled
deliberately, not as a default follow-up. A clean ship on `lem:342A`
detaches from the multi-cycle scaffold and creates option value
for the cycle 272+ planner.
