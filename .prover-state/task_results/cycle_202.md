# Cycle 202 Results

## Worked on

`OpenMath/Chapter3/Section381.lean` Banach fixed-point foundation:
1. **P1** — Ship `RKStageMap_contracting`, packaging
   `RKStageMap_lipschitz` + smallness hypothesis as a `ContractingWith`
   instance.
2. **P2** — Generalise `RKStageMap`, `RKStageMap_dist_le`, and
   `RKStageMap_lipschitz` from scalar `f : ℝ → ℝ` to normed `ℝ`-space
   `f : N → N` (where `[NormedAddCommGroup N] [NormedSpace ℝ N]`).
3. Preserve the cycle 201 `paddedEuler` `LipschitzWith 0` non-vacuity
   witness through the generalisation (no edit required — `ℝ` is
   itself a normed `ℝ`-space, so the example specialises cleanly).

Skipped P0 (§441 Phase C.2 smoke test) per strategy — 21 consecutive
GPFS timeouts cycles 182–201; no diagnostic value in a 22nd attempt.
Skipped P3 (`equivalent_self`) — would have left at least one sorry
behind (smallness arithmetic and `fixedPoint_unique` API selection),
which the cycle 200→201 rollback precedent forbids.

## Approach

### Imports

Added `import Mathlib.Topology.MetricSpace.Contracting` to bring
`ContractingWith` into scope.

### P2 mechanical port (definition + two theorems)

Lines 1582–1670 of cycle 201's scalar `RKStageMap` block replaced
with the normed-space version:

```
{f : ℝ → ℝ}                   →   {N : Type*} [NormedAddCommGroup N]
                                    [NormedSpace ℝ N] {f : N → N}
y₀ : ℝ                         →   y₀ : N
RKStageMap : ... → (Fin s → ℝ) →   RKStageMap : ... → (Fin s → N)
h * Σⱼ M.A i j * f (Y j)      →   h • Σⱼ M.A i j • f (Y j)
Real.dist_eq                   →   dist_eq_norm
abs_mul                        →   norm_smul + Real.norm_eq_abs
Finset.abs_sum_le_sum_abs      →   norm_sum_le
ring (for the algebraic eq)    →   rw [add_sub_add_left_eq_sub, ← smul_sub]
ring (sum_congr inner)         →   rw [← smul_sub]
```

The bound `|h| · L · Σ_{i,j} |aᵢⱼ|` is unchanged — only the carrier
of `y₀` and the codomain of `f` differ. The cycle 201 `Finset.single_le_sum`
row-sum bound transfers verbatim.

Critical hcomp/heq line — the only non-trivial port:

```lean
have heq : (M.RKStageMap h f y₀ Y i) - (M.RKStageMap h f y₀ Y' i)
    = h • ∑ j, M.A i j • (f (Y j) - f (Y' j)) := by
  simp only [RKStageMap]
  rw [show y₀ + h • ∑ j, M.A i j • f (Y j) - (y₀ + h • ∑ j, M.A i j • f (Y' j))
      = h • (∑ j, M.A i j • f (Y j) - ∑ j, M.A i j • f (Y' j)) by
        rw [add_sub_add_left_eq_sub, ← smul_sub],
      ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by rw [← smul_sub]
```

The cycle-201 hcomp closed `dist (RKStageMap ... Y i) (RKStageMap ... Y' i)`
to `|h| * |...|` via `Real.dist_eq` and `abs_mul`. The normed-space
analogue uses `dist_eq_norm` (`= ‖x - y‖`) and `norm_smul`
(`‖c • x‖ = ‖c‖ * ‖x‖`), then `Real.norm_eq_abs` to keep the outer
coefficient as `|h|` rather than `‖h‖`. The inner per-summand bound
similarly uses `norm_smul + Real.norm_eq_abs` to keep `|M.A i j|`.

`module` tactic was unnecessary — `rw [add_sub_add_left_eq_sub, ← smul_sub]`
suffices for the outer algebraic identity, and `rw [← smul_sub]` alone
for each inner summand. The strategy's `module` / `simp [smul_sub,
sub_smul, smul_sum]` fallback was not needed.

### P1 — `RKStageMap_contracting`

Trivial packaging of the cycle 201 `RKStageMap_lipschitz` (now
generalised) plus the smallness hypothesis. `ContractingWith K f`
unfolds to `K < 1 ∧ LipschitzWith K f` (Mathlib
`Topology/MetricSpace/Contracting.lean` line 40), so the proof is
just an anonymous-constructor pair.

```lean
theorem RKStageMap_contracting {s : ℕ} (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [NormedSpace ℝ N] (h : ℝ)
    {f : N → N} {L : NNReal} (hf : LipschitzWith L f) (y₀ : N)
    (hLt : |h| * L * (∑ i : Fin s, ∑ j : Fin s, |M.A i j|) < 1) :
    ContractingWith ⟨|h| * L * (∑ i, ∑ j, |M.A i j|), _⟩
      (M.RKStageMap h f y₀) :=
  ⟨by exact_mod_cast hLt, M.RKStageMap_lipschitz h hf y₀⟩
```

The `exact_mod_cast hLt` handles the `NNReal → ℝ` comparison
direction — the goal after `refine ⟨?_, _⟩` is in NNReal-comparison
form `(⟨..., _⟩ : ℝ≥0) < 1`, and the underlying value is
`|h| * L * Σ |aᵢⱼ| : ℝ`. `exact_mod_cast` matches the cast
boilerplate without needing explicit `NNReal.coe_lt_one`.

## Result

**SUCCESS** — all four targets compile clean, axiom-clean,
sorry-count 0.

**Verification:**

```
$ time lake env lean OpenMath/Chapter3/Section381.lean
real    0m6.568s     # warm-cache rebuild ≈7s
```

Two pre-existing `unused variable heq` warnings at lines 577 and 1783
(both inside other theorems' bodies, unrelated to cycle 202 edits —
inherited from earlier cycles).

**Axiom check** via `lean_verify` (MCP):

| Theorem                      | Axioms                                       |
|------------------------------|----------------------------------------------|
| `RKStageMap`                 | `[propext, Classical.choice, Quot.sound]`    |
| `RKStageMap_dist_le`         | `[propext, Classical.choice, Quot.sound]`    |
| `RKStageMap_lipschitz`       | `[propext, Classical.choice, Quot.sound]`    |
| `RKStageMap_contracting`     | `[propext, Classical.choice, Quot.sound]`    |

**Sorry count:** 0 (unchanged from cycle 201).

**Tautology scanner:** No matches.

**paddedEuler non-vacuity:** Still compiles. `paddedEuler.A = 0` and
`ℝ` is itself a normed `ℝ`-space, so the existing example body
(`simp [RKTableau.RKStageMap, paddedEuler]` reducing to `fun _ _ => y₀`,
then `LipschitzWith.const`) transfers without edit.

## Faithfulness check

P1 and P2 are infrastructure (no textbook entity ID). They exist to
formalise the tacit "for `h` sufficiently small" qualifier Butcher
uses throughout §380 — Banach's fixed-point theorem applied to
`RKStageMap` yields existence/uniqueness of implicit-stage solutions.

### `RKStageMap` (def)

- No textbook entity ID — this is a Lean infrastructure definition
  with no Butcher counterpart, set up to consume Mathlib's
  `ContractingWith` API.
- The definition's *fixed points* are exactly the implicit stage
  vectors of Butcher §312's autonomous problem
  `Yᵢ = y₀ + h · Σⱼ aᵢⱼ · f(Yⱼ)`. The form `Y ↦ (fun i, y₀ + h • Σⱼ M.A i j • f (Y j))`
  ensures `Y = RKStageMap M h f y₀ Y ↔ Yᵢ = y₀ + h • Σⱼ M.A i j • f (Y j)` for all `i`,
  matching `IsRKOneStep`'s stage equation verbatim.
- Polymorphic `N` matches `IsRKOneStep` (line 922) and `Equivalent`
  (line 967), which take `{N : Type*} [NormedAddCommGroup N]
  [NormedSpace ℝ N]`.
- No hypothesis strengthening — this is a definition with no
  hypotheses to compare.

### `RKStageMap_dist_le`, `RKStageMap_lipschitz`, `RKStageMap_contracting` (theorems)

- No textbook entity IDs — these are technical lemmas implementing
  the standard "implicit-method stage equations have unique solutions
  for small `h`" argument (Butcher §380's tacit qualifier).
- Lipschitz hypothesis on `f` (`LipschitzWith L f`) matches
  Butcher's "satisfying a Lipschitz condition" verbatim and matches
  the hypothesis already present in `Equivalent` (line 968).
- The smallness condition `|h| · L · Σ |aᵢⱼ| < 1` is a *stronger*
  condition than the tightest possible (sup-norm row form
  `|h| · L · max_i Σⱼ |aᵢⱼ|` would suffice). This is strategic
  looseness — the cycle 201 planner explicitly chose the entrywise
  bound to avoid PiLp instance fiddliness, and the cycle 202
  strategy confirms it. The downstream `equivalent_self` proof
  (cycle 203) only needs *some* `h₀ > 0` for which contraction
  holds; any smallness bound that scales linearly in `h` works.
  Documented in the strategy "NOT to do" section item 3.
- No tautology check applies — no theorem conclusion appears among
  its hypotheses.
- No definition smuggling — `ContractingWith` is the standard Mathlib
  definition (Topology/MetricSpace/Contracting.lean), reused
  verbatim.

## Dead ends

None this cycle. The mechanical port was straightforward; no
fallback to `module` tactic was needed (cycle 201's `ring`-style
algebra translated to `rw [add_sub_add_left_eq_sub, ← smul_sub]` and
`rw [← smul_sub]` for the inner summand).

## Discovery

1. **`exact_mod_cast` handles NNReal/ℝ packaging cleanly.** The
   `ContractingWith.1` goal `(⟨|h| · L · Σ |aᵢⱼ|, _⟩ : ℝ≥0) < 1` is
   automatically reduced from the ℝ-form hypothesis
   `|h| · L · Σ |aᵢⱼ| < 1` via `exact_mod_cast`. Avoids needing
   explicit `NNReal.coe_lt_one.mp` or `NNReal.coe_mk` rewrites.

2. **`rw [add_sub_add_left_eq_sub, ← smul_sub]` is the normed-module
   analogue of `ring`.** The cycle 201 hcomp/heq's `by ring` step
   for the algebraic identity `(y₀ + h·A) - (y₀ + h·B) = h·(A - B)`
   doesn't have a single tactic equivalent in a module, but the
   two-step rewrite is concise and self-contained. The
   `add_sub_add_left_eq_sub` lemma in Mathlib gives
   `(a + b) - (a + c) = b - c` directly, then `← smul_sub` does the
   distributive step. No need for the strategy's suggested
   `module` tactic or `simp [smul_sub, sub_smul, smul_sum]`.

3. **`paddedEuler` example survives generalisation untouched.** The
   `simp [RKTableau.RKStageMap, paddedEuler]` rewrite reduces
   `RKStageMap h f y₀ Y i` to `y₀ + h • Σⱼ 0 • f (Y j)` to
   `y₀ + h • 0` to `y₀`, all via `simp` lemmas that fire on the
   `•` form just as readily as the `*` form. No specialisation
   required — `simp` does the work, including the `0 • _ = 0`
   simplification.

4. **The cycle 201 entrywise bound has zero porting friction.** The
   row-sum upper bound argument (`Finset.single_le_sum` over
   `fun i' => ∑ j, |M.A i' j|`) is purely about the matrix entries
   `|M.A i j|`, independent of the codomain. The cycle 201 cost of
   choosing the loose entrywise bound (over sup-norm row form) pays
   off in cycle 202 as exactly zero port cost on this fragment.

## Suggested next approach

### Cycle 203 — `equivalent_self` (P3 from cycle 202 strategy, deferred)

The cycle 202 strategy's P3 stretch recipe is now feasible: all the
infrastructure pieces are landed. Remaining gaps to fill:

1. **Arithmetic discharge of `|h| * L * C < 1` from `h ≤ h₀ := 1 / (2 * (L * C + 1))`.**
   Requires case-split on `L * C = 0` vs `L * C > 0`. With `h > 0`,
   `|h| = h`, so the goal is `h * L * C < 1`. From `h ≤ 1/(2(L·C+1))`
   and `L·C + 1 ≥ 1 > 0`:
   - if `L·C = 0`: `h * L * C = 0 < 1`. ✓
   - if `L·C > 0`: `h * L * C ≤ L·C / (2(L·C+1)) < L·C / (L·C+1) < 1`. ✓

   This is `nlinarith` territory; the planner may want to write a
   small `aux` lemma in advance.

2. **`fixedPoint_unique'` API name.** Mathlib's `ContractingWith`
   namespace has `eq_or_edist_eq_top_of_fixedPoints` (line 74 of
   `Contracting.lean`) which gives `x = y ∨ edist x y = ∞`. For
   `Fin s → N` with `N` a normed `ℝ`-space, `edist x y ≠ ∞`
   automatically (it's a metric space, finite edist), so the
   `∨ edist x y = ∞` disjunct is dismissible. The right cycle-203
   name is `eq_or_edist_eq_top_of_fixedPoints`, not the strategy's
   guessed `fixedPoint_unique'`.

3. **`IsFixedPt` packaging.** The cycle 203 worker needs
   `IsFixedPt (M.RKStageMap h f y₀) Y` from the stage equations
   `∀ i, Y i = y₀ + h • Σⱼ M.A i j • f (Y j)`. Definitionally
   `IsFixedPt f x := f x = x` (Mathlib). The stage equations give
   `Y i = (M.RKStageMap h f y₀ Y) i`, which `funext` lifts to
   `Y = M.RKStageMap h f y₀ Y`, then `.symm` for the fixed-point
   direction.

Cycle 203 LOC estimate: ~80 lines including arithmetic helper.

### Cycle 204 — `PEquivalent → Equivalent` direction of `thm:381H`

Once `equivalent_self` is in hand, combining with the existing
`Equivalent` partial structure and the cycle 188 P-equivalence
witnesses should give the `PEquivalent → Equivalent` implication of
`thm:381H`. That closes one of the three deferred iff-directions in
`thm_381H_deferred.md`, opening the path to re-introducing the
cycle-200 scaffold at the lower sorry-count threshold the cycle-201
rollback note requires.

### GPFS reality check

22nd consecutive cycle of §441 Phase C.2 timeout would be expected.
Per cycle 202 strategy, no time spent on it this cycle. If GPFS
recovers between cycles 202 and 203, the next planner picks it up
naturally.
