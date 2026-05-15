# Cycle 267 Results

## Worked on

§310/§311 Phase E.1 extension to order 3 (per strategy P1–P4):

* **P1**: `bseriesExactTerm_broom₃_scalar` — scalar closed form
  `bseriesExactTerm f y₀ h broom₃ = h³/6 · (f''(y₀) · f(y₀)²)`.
* **P2**: `bseriesExactTerm_mkCherry_scalar` — scalar closed form
  `bseriesExactTerm f y₀ h (mk [cherry]) = h³/6 · ((f'(y₀))² · f(y₀))`.
* **P3**: `lem_311A_order_three_partialSum` — order-3 Taylor expansion
  bridge using `bseriesExactPartialSum f y₀ h {vertex, cherry, broom₃,
  mk [cherry]}` in place of cycle 257's closed-form polynomial.
* **P4**: Non-vacuity witness for `lem_311A_order_three_partialSum`
  at `f := 0, yex := const y₀`.

## Approach

Followed the strategy as written. Two files modified:

### `OpenMath/Chapter3/Section301.lean` (+~110 LOC)

Added inside the existing `OpenMath.Chapter3.Section310.RootedTree`
namespace, immediately after cycle 266's
`bseriesExactTerm_cherry_scalar`:

1. **`bseriesExactTerm_broom₃_scalar`** (P1, ~35 LOC):
   * `unfold bseriesExactTerm broom₃` to expose
     `(h^r / (σ·γ)) • elementaryDiff f y₀ (mk [vertex, vertex])`.
   * `rfl`-reduce `order/symmetry/density (mk [vertex, vertex]) =
     (3, 2, 3)`, matching cycle 251's α-witness coefficients.
   * Compute `elementaryDiff f y₀ (mk [vertex, vertex]) =
     iteratedFDeriv ℝ 2 f y₀ (fun i : Fin 2 => f y₀)` via the
     inline-reused cycle 266 `elementaryDiff f y₀ vertex = f y₀` step.
   * Apply **the key new hook**:
     `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` from
     `Mathlib.Analysis.Calculus.IteratedDeriv.Defs`, which states
     `iteratedFDeriv 𝕜 n f x m = (∏ i, m i) • iteratedDeriv n f x`
     — the canonical scalar collapse for *all* `n` (generalises
     cycle 266's `iteratedFDeriv_one_apply` recipe).
   * Collapse the product via `Fin.prod_univ_two`, the iterated
     derivative via `iteratedDeriv_succ` + `iteratedDeriv_one`
     (giving `iteratedDeriv 2 f y₀ = deriv (deriv f) y₀`), then
     `smul_eq_mul` + `push_cast` + `ring` for the final cast
     normalization.

2. **`bseriesExactTerm_mkCherry_scalar`** (P2, ~40 LOC):
   * Same recipe as P1, but at depth 1 (the outer `iteratedFDeriv`).
   * Inner intermediate: `elementaryDiff f y₀ cherry = deriv f y₀ *
     f y₀` is re-derived inline (cloned from cycle 266's
     `bseriesExactTerm_cherry_scalar` proof's `hED` block).
   * Outer collapse via `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`
     at `n = 1` + `Fin.prod_univ_one` + `iteratedDeriv_one` →
     `(deriv f y₀ * f y₀) * deriv f y₀ = (deriv f y₀)² * f y₀`.

### `OpenMath/Chapter3/Section311.lean` (+~130 LOC)

Added immediately after cycle 266's `lem_311A_order_two_partialSum`:

1. **`lem_311A_order_three_partialSum`** (P3, ~110 LOC):
   * Get base = `lem_311A_order_three hf_C2 hyex_x₀ hyex_C4 hyex_ode`
     (cycle 257 closed-form `O(h^(3+1))`).
   * Establish six pairwise distinctness facts
     (`vertex ≠ cherry`, `vertex ≠ broom₃`, `vertex ≠ mk [cherry]`,
     `cherry ≠ broom₃`, `cherry ≠ mk [cherry]`, `broom₃ ≠ mk [cherry]`)
     via `simp` on the `RootedTree.mk.injEq` auto-generated lemma
     applied to the literal child lists.
   * Establish three iterated non-membership facts via the pairwise
     distinctness.
   * `hcongr` `funext` lemma: rewrite
     `{vertex, cherry, broom₃, mk [cherry]}` as a chain of three
     `insert` applications + one `_singleton` closure; collapse each
     summand via the four per-tree closed forms
     (`bseriesExactTerm_vertex` + `bseriesExactTerm_cherry_scalar`
     + P1 + P2); `smul_eq_mul` + `ring` to normalize the resulting
     polynomial in `h`.
   * Close with `hbase.congr'` against `hcongr`.

2. **P4 non-vacuity witness**: trivial ODE `f := 0, yex := const y₀`
   discharges via direct application of
   `lem_311A_order_three_partialSum`.

## Result

**SUCCESS** — all P1, P2, P3, P4 deliverables shipped. No Backup A/B/C
fallback needed; Risk R1 (`iteratedFDeriv ℝ 2` plumbing) collapsed to
one rewrite via `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`.

* `lake env lean OpenMath/Chapter3/Section301.lean`: exits 0.
* `lake env lean OpenMath/Chapter3/Section311.lean`: exits 0.
* `lake build OpenMath.Chapter3`: 2861 jobs, 0 errors.
* `grep -c sorry OpenMath/Chapter3/Section{301,311}.lean`: both 0.
* Tautology-scanner regex
  (`:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`) on both files:
  no matches.
* Axiom verification on all three new public theorems
  (`bseriesExactTerm_broom₃_scalar`,
  `bseriesExactTerm_mkCherry_scalar`,
  `lem_311A_order_three_partialSum`): each depends only on
  `[propext, Classical.choice, Quot.sound]`.

## Faithfulness check

### `bseriesExactTerm_broom₃_scalar` (P1, new `theorem`)

* **Textbook anchor**: Butcher §312 + Table 310(II), row r=3, first
  tree (`f''(f, f)`). The exact-solution B-series coefficient at the
  broom₃ tree is `h^r / (σ · γ) · F(t)(y₀) = h³ / (2·3) · f''(y₀)·f(y₀)²
  = h³/6 · f''(y₀)·f(y₀)²`.

  Quoted from `extraction/formalization_data/entities/def_312A.json`
  (the §312 elementary-weights anchor — there is no per-tree row
  JSON for this scalar closure; the entity covers the §312 framework
  recursively, and Table 310(II) provides the per-tree witnesses):

  > "Then the 'elementary weights' Φ(t), the 'internal weights' Φᵢ(t)
  > and the 'derivative weights' (ΦᵢD)(t) for t ∈ T … are defined by
  > (312a)–(312d). … An alternative formula for Φ(t), which uses the
  > vertex and edge characterization of each tree t, is given in the
  > following lemma."

  The scalar closure here is the special case of the exact-solution
  Taylor B-series (the `1/r!`-weighted form, equivalent to
  `α(t)/r!` · `F(t)(y₀)`) at the broom₃ tree.

* **Lean statement captures**: same content as Butcher's Taylor
  expansion at the broom₃ tree. Restricted to scalar `ℝ → ℝ`
  because the polymorphic version requires the multilinear-map
  curry chain (cycle 268+ scope per cycle 266 task results §
  "Suggested next approach").

* **Definition smuggling**: no — RHS is an explicit closed form,
  not a definitional unfolding.

* **Hypothesis strength**: no hypotheses beyond `f : ℝ → ℝ`,
  `y₀ h : ℝ`. The textbook is silent on smoothness for the per-tree
  identity at a specific point; only the broader Taylor convergence
  needs `f ∈ C^r`. The pointwise identity holds whenever the relevant
  derivatives exist; the `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`
  hook treats `iteratedFDeriv 𝕜 n f x` as a multilinear map that
  collapses on scalar inputs regardless of smoothness — Mathlib's
  default value `0` outside the differentiable case is consistent
  with the closed form.

### `bseriesExactTerm_mkCherry_scalar` (P2, new `theorem`)

* **Textbook anchor**: Butcher §312 + Table 310(II), row r=3, second
  tree (the depth-2 chain `f'(f' · f)`). The exact-solution B-series
  coefficient at `mk [cherry]` is `h^r / (σ · γ) · F(t)(y₀) =
  h³ / (1·6) · (f'(y₀))² · f(y₀) = h³/6 · (f'(y₀))² · f(y₀)`.

* **Lean statement captures**: same content as Butcher's Taylor
  expansion at the depth-2 chain tree. Same scalar restriction as
  P1, same justification.

* **Definition smuggling**: no — RHS is an explicit closed form.

* **Hypothesis strength**: same as P1; no smoothness hypotheses
  needed for the pointwise identity.

### `lem_311A_order_three_partialSum` (P3, new `theorem`)

* **Textbook anchor**: Butcher §311 + Theorem 311B (Taylor expansion
  of the exact solution, order-3 truncation form). Quoted from
  `extraction/formalization_data/entities/lem_311A.json`:

  > "Let S = S₀ ∪ {s} be an ordered set, where every member of S₀
  > is less than s. Let t be a member of T_{S₀}*. Then d/dx F(|t|)(y(x))
  > is the sum of F(|u|)(y(x)) over all u ∈ T_S* such that the
  > subtree formed by removing s from the set of vertices is t."

  The Lean lemma here is **not** the full `lem:311A` (which requires
  labelled-tree quotient infrastructure `def:300C`, multi-cycle scope);
  rather, it is the order-3 specialisation of the *consequence*
  `thm:311B` (Taylor expansion of the exact solution at order p), now
  restated using `bseriesExactPartialSum` in place of the explicit
  closed-form polynomial.

* **Lean statement captures**: same content as cycle 257's
  `lem_311A_order_three`, restated using
  `bseriesExactPartialSum f y₀ h {vertex, cherry, broom₃, mk [cherry]}`.
  Definitionally equivalent; the bridge is `IsBigO.congr'`.

* **Tautology check**: conclusion involves `bseriesExactPartialSum`,
  which does not appear in any hypothesis.

* **Identity check**: proof is multi-step (six pairwise distinctness
  lemmas → three non-membership lemmas → `hcongr` `funext` collapse
  → `IsBigO.congr'` bridge to cycle 257). Not vacuous.

* **Hypothesis strength**: matches cycle 257's `lem_311A_order_three`
  hypotheses exactly (`ContDiff ℝ 2 f`, `yex x₀ = y₀`,
  `ContDiff ℝ 4 yex`, `∀ x, HasDerivAt yex (f (yex x)) x`). No
  strengthening.

* **Absent-theorem check**: no "will be proved with sorry" or "is
  stated below" promises in the new code.

### Pre-commit checklist

* **Tautology check**: no theorem conclusion equals one of its
  hypotheses literally.
* **Identity check**: no proof is just `exact h`; all three new
  theorems are multi-step computations.
* **Definition-smuggling check**: no new `def` or `structure`
  introduced this cycle; only theorems on existing infrastructure.
* **Hypothesis strength check**: hypotheses match cycle 257's
  `lem_311A_order_three` and Butcher's textbook coefficients
  exactly.
* **Absent-theorem check**: no promised content missing.

## Dead ends

One minor friction during P3:

* **Initial `simp [Finset.mem_singleton, vertex, cherry]` pattern
  (from cycle 266) didn't fully discharge the three iterated
  non-membership lemmas** for the four-tree set. Mitigation: split
  into six pairwise `≠` facts (each closed by `simp [vertex, cherry,
  broom₃]` on `RootedTree.mk.injEq`), then chain via `simp [h_pair_ne]`
  for the iterated `∉ {…}` goals. ~5 LOC overhead vs cycle 266; no
  cycle stalled. The pattern generalises cleanly to larger tree sets
  (cycle 268's order-4 partial sum will need 10 pairwise distinctness
  + 6 iterated non-membership facts).

## Discovery

* **`iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` is the canonical
  scalar collapse at all orders.** Mathlib's
  `Mathlib.Analysis.Calculus.IteratedDeriv.Defs:238` states
  `iteratedFDeriv 𝕜 n f x m = (∏ i, m i) • iteratedDeriv n f x` for
  scalar-valued multilinear inputs. Combined with `Fin.prod_univ_*`
  and `iteratedDeriv_succ` × `n`, this collapses
  `iteratedFDeriv ℝ n f y₀ ![v₁, …, vₙ]` to
  `(∏ i, vᵢ) * (deriv^n f) y₀` in O(n) rewrites — a cleaner and
  more general path than cycle 266's `iteratedFDeriv_one_apply +
  fderiv_eq_smul_deriv` ad-hoc collapse. **Recommendation for future
  per-tree closed-form proofs at order ≥ 3**: prefer this lemma over
  the cycle-266 ad-hoc recipe.

* **`RootedTree.mk.injEq` + `simp` discharges tree distinctness
  cleanly.** The four distinct trees in the partial-sum bridge
  (`vertex = mk []`, `cherry = mk [mk []]`, `broom₃ = mk [mk [], mk []]`,
  `mk [cherry] = mk [mk [mk []]]`) are pairwise distinguished by
  their child lists; `simp [vertex, cherry, broom₃]` unfolds each
  alias and applies `RootedTree.mk.injEq` automatically. For order-4
  partial sums (10 pairwise distinctness + 6 iterated non-membership),
  the same pattern should compile in ~30 LOC overhead.

* **Risk R1 collapsed.** The strategy's pre-flight warning that the
  2-fold `iteratedFDeriv` plumbing for broom₃ could stall past 45
  minutes was outdated — `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`
  fires in one rewrite. Backup A (scalar P2-only + re-scoped P3) and
  Backup B (coefficient bridges without `iteratedFDeriv`) were not
  needed. Future planners should remove the R1 warning from the cycle
  268+ strategy templates and instead flag the polymorphic-`E` lift
  (cycle 265's HIGH-risk concern) as the next infrastructure hurdle.

## Suggested next approach

Strategy §I outlook listed three cycle 268+ candidates. In rough
preference order:

1. **Order-4 partial-sum bridge** (`lem_311A_order_four_partialSum`).
   Same recipe as cycle 267 at one higher Taylor degree: four new
   per-tree closed forms (`mk [vertex, vertex, vertex]`,
   `mk [vertex, cherry]`, `mk [broom₃]`, `mk [mk [cherry]]`) using
   the `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod + Fin.prod_univ_three`
   recipe + cycle 258's `lem_311A_order_four` as base.
   Estimated ~250 LOC (4 per-tree closed forms × ~40 LOC each + ~90
   LOC for the partial-sum bridge with 10 pairwise distinctness facts
   + 6 iterated non-membership facts). Single cycle, axiom-clean
   target. Compounds cycles 266/267 work; the
   `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` recipe scales
   to arbitrary tree depth.

2. **Polymorphic-`E` lift** of cycle 266's `bseriesExactTerm_cherry_scalar`
   (Phase D.1 / Phase E.2 continuation). The cycle 265 HIGH-risk
   `iteratedFDeriv ℝ 1 ↔ fderiv` plumbing applies at a single
   concrete tree (cherry) — easier than over an abstract truncation.
   Cycle 268 would lift just the cherry case; broom₃ and mk[cherry]
   defer to cycle 269+. ~80–120 LOC, single cycle, **MEDIUM-HIGH risk**
   (the `ContinuousMultilinearMap.uncurry` / `.curry` plumbing has
   to be exercised end-to-end).

3. **`lem:342A`** (Legendre orthogonality on `[0,1]`) — single-cycle,
   `lem:310B`-independent target if cycles 268+ §310/§311 work
   wants a refresher. Per `lem_310B_plan.md` §8.2.

Recommend **(1)** for momentum. The recipe from cycle 267 ports
mechanically; the only new combinatorics is the 4-tree distinctness
+ non-membership set, which doubles vs cycle 267 but stays within
the `simp [vertex, cherry, broom₃]` pattern. After (1), cycle 269
can pivot to (2) once the scalar order-≤4 partial-sum bridge is
complete and the multilinear-map plumbing is the only remaining
gap.
