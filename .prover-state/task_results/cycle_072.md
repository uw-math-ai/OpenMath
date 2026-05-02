# Cycle 072 Results

## Worked on

- **Priority 0** (committed): land cycle 071's staged work
  (`Section404.lean` +173 lines: `runningMaxAbs` def + 4 helper lemmas
  + `IsHomogeneousSolution.const_smul` + `unbounded_homogeneous_contra`;
  `Section405.lean` scaffold for `convergent_isStable`).
- **Priority 1** (closed): the lone remaining sorry at
  `Section405.lean:145` — `hstart_tendsto`, the sub-claim that the
  piecewise function `start h i = if 0 < h then y i.val / ζ (⌈1/h⌉) else 0`
  tends to `0` as `h → 0`.
- **Priority 2** (done): updated `lean_status.json` to mark `thm:405A`
  and `thm:243A` as `formalized`; updated `plan.md` to flip both `[~]`
  markers to `[x]` and bumped progress counter `41 → 43`.

## Approach

### `hstart_tendsto`

Two-sided limit at `h = 0`, decomposed via `nhdsLE_sup_nhdsGT 0`
(`𝓝[≤] 0 ⊔ 𝓝[>] 0 = 𝓝 0`) into right- and left-tail limits, then
recombined via `Filter.Tendsto.sup` and `rwa [nhdsLE_sup_nhdsGT]`.

Right tail (`0 < h`): `start h i = y i.val / ζ (⌈1/h⌉)`. Composition
chain
1. `tendsto_inv_nhdsGT_zero` — `1/h → ∞` as `h → 0⁺` (rewriting
   `1/h = h⁻¹` with `one_div`).
2. `tendsto_nat_ceil_atTop` — `⌈x⌉₊ → ∞` as `x → ∞`.
3. `hζ_atTop` — `ζ n → ∞` as `n → ∞`.
4. `Filter.Tendsto.const_div_atTop` — `c / g → 0` when `g → ∞`.

Plus a `filter_upwards [self_mem_nhdsWithin]` + `if_pos` to congrue
the `start h i` form to the explicit quotient.

Left tail (`h ≤ 0`): the if-branch is `else`, so `start h i = 0`,
giving the constant-zero limit via `tendsto_const_nhds` after
`if_neg`.

### Aristotle parallel run

Submitted a self-contained version of the lemma (`hstart_tendsto.lean`,
project ID `85495285-334f-4611-aa11-d77e92c4e3d8`) at the start of the
cycle. Aristotle returned a closed proof in ~8 minutes using the same
high-level chain (`tendsto_inv_nhdsGT_zero` → `tendsto_nat_ceil_atTop`
→ `hζ_atTop.comp` → `tendsto_const_nhds.div_atTop`) but combining the
two branches via `Metric.tendsto_nhds_nhds` rather than the
filter-sup decomposition. Kept my manual proof since it landed first
and is more idiomatic (per cycle 071 precedent for
`runningMaxAbs_atTop_of_unbounded`). Aristotle's run validated the
mathematical strategy.

## Result

**SUCCESS.** `convergent_isStable` (`thm:405A`) is fully closed, no
sorries remain in `Section405.lean`. With `thm:405A`, `thm:405B`,
`thm:405C` all formalized, `thm:243A`'s reverse direction
(`convergent → stable ∧ consistent`) is now closed; combined with
the cycle-068/069 forward direction, the iff packager
`isConvergent_iff_isStable_and_isConsistent` is fully proved. Both
`Section404.lean` and `Section405.lean` build cleanly with only
pre-existing unused-variable lints (no errors, no sorry warnings).

## Faithfulness check

### `convergent_isStable` (`thm:405A`, primary deliverable)

- Entity ID and textbook statement (quoted from `entities/thm_405A.json`):
  > "A convergent linear multistep method is stable."
- Lean statement: `(M : LinearMultistepMethod k) (hConv : M.IsConvergent) : M.IsStable`. **Same content.**
- The proof relies on the strengthened `IsConvergent` predicate
  (per `is_convergent_strengthened.md`, accepted from cycle 068);
  the textbook proof's IVP hypotheses are bundled into `IsConvergent`'s
  joint-Lipschitz / `ContDiff` / bounded clauses.
- The trivial-IVP setup (`f ≡ 0`, `yex ≡ 0`, `x = 1`) matches
  Butcher's textbook proof verbatim (he uses the same trivial IVP
  with starting values rescaled by `ζ_n`).
- Tautology check: ✓ (conclusion `M.IsStable` is not a hypothesis).
- Identity check: ✓ (proof is a non-trivial scaffold using 6 helpers
  plus the new `hstart_tendsto`).
- Hypothesis strength check: ✓ (no hypotheses beyond what
  `IsConvergent` already supplies and the textbook requires).

### `hstart_tendsto` (private have-clause, not a top-level theorem)

Inline filter-chasing, not a Butcher entity. Faithfulness check N/A.

### `runningMaxAbs` and 6 helpers (cycle 071 staged, committed this cycle)

Pure infrastructure (Section404.lean), not Butcher entities.
Faithfulness check N/A. Definitions match the standard
"running max of `|y i|` over `i ≤ n`" recursion.

### Axiom check

`#print axioms LinearMultistepMethod.convergent_isStable` returns
the canonical Mathlib base only (`propext`, `Classical.choice`,
`Quot.sound`).

## Dead ends

### Initial filter-sup approach with `rw [← nhdsLE_sup_nhdsGT 0]`

First attempt:
```lean
rw [← nhdsLE_sup_nhdsGT (0 : ℝ)]
exact Filter.Tendsto.sup h_left h_right
```
Failed: `rw [← ...]` rewrote **both** `nhds 0` instances in the goal
(source filter and target filter), so the post-rewrite goal became
`Tendsto _ (𝓝[≤] 0 ⊔ 𝓝[>] 0) (𝓝[≤] 0 ⊔ 𝓝[>] 0)` and `Tendsto.sup`
couldn't unify `h_left`'s target `𝓝 0` with the spurious sup-target.
Fixed by avoiding the rewrite-on-goal pattern: produce the combined
fact first, then rewrite at the hypothesis:
```lean
have h_combined : Tendsto _ (𝓝[≤] 0 ⊔ 𝓝[>] 0) (nhds 0) :=
  h_left.sup h_right
rwa [nhdsLE_sup_nhdsGT] at h_combined
```

## Discovery

- **`Filter.Tendsto.const_div_atTop`** (Mathlib
  `Topology.Algebra.Order.Field`, line 225): `Tendsto g l atTop →
  Tendsto (fun n ↦ r / g n) l (𝓝 0)`. Cleaner than going through
  `Filter.Tendsto.div_atTop` with `tendsto_const_nhds` explicitly.
- **`nhdsLE_sup_nhdsGT`** (Mathlib `Topology.Order.LeftRight`):
  `𝓝[≤] a ⊔ 𝓝[>] a = 𝓝 a`. The clean filter-decomposition for
  splitting a two-sided limit into left- and right-tails when the
  function has a piecewise definition at the limit point.
- **Rewrite-scoping pitfall**: when both source and target of a
  `Tendsto` carry the same filter (e.g. `Tendsto _ (𝓝 0) (𝓝 0)`),
  a naked `rw` rewrites both. Either use `nth_rw` or — better —
  produce the desired hypothesis form first and rewrite *at* it.
- **Aristotle solved this in ~8 minutes** — `hstart_tendsto`-shaped
  filter-chasing goals are well within Aristotle's range. Worth
  batch-submitting future filter-limit lemmas.

## Suggested next approach

§405 is now fully closed (all four §405 entries `thm:405A/B/C` plus
the iff packager `thm:243A` are `formalized`). The next unblocked
Chapter 4 cluster is the §410 order-conditions block:

1. **`thm:410A`** (Criteria for order) — entry point for §410, unblocks
   `thm:410B` / `thm:410C` / `thm:410D`. Per `plan.md` line 186, this
   is the natural next deliverable. Read `entities/thm_410A.json`
   first; expect Taylor-expansion / generating-function machinery.
2. **`thm:422A`** (underlying one-step method for LMM) and
   **`thm:422C`** (LMM convergence) form a parallel §422 cluster.
   Consider after `thm:410A` since §422 likely depends on §410's
   order conditions.
3. The §441 maximum-order theorems (`lem:441A`, `lem:441B`,
   `thm:441C`) and §443 stability constants are downstream of
   §410 and §431; defer.
4. The cross-chapter `thm:243A` no longer needs special treatment —
   the deferral is resolved.

For cycle 073, recommend the planner schedule **`thm:410A`** as the
single Lean target. The Taylor-expansion / generating-function
algebra may require `noncomputable def`-style shape (similar to
§310 trees); plan to read `thm_410A.json` and `thm_410B.json`
together so the §410 cluster's shared infrastructure (likely
generating-function definitions or order-coefficient lemmas) is
designed once, not retrofitted.

Tooling hint: when chaining Tendsto facts through a piecewise
definition, the `nhdsLE_sup_nhdsGT` decomposition + `Tendsto.sup`
pattern used here is reusable; consider lifting it into a small
helper lemma if `thm:410` introduces further piecewise / sign-split
definitions.
