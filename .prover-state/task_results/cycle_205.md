# Cycle 205 Results

## Worked on

Two new infrastructure theorems in `OpenMath/Chapter3/Section381.lean`:

1. **P1**: `RKStageMap_fixedPoint_exists` — Banach existence half complementing
   cycle 204's `RKStageMap_fixedPoint_unique`. Under the cycle 202 smallness
   condition `|h| · L · C < 1` and `[CompleteSpace N]`, exhibits a stage tuple
   `Y : Fin s → N` with `M.RKStageMap h f y₀ Y = Y`.
2. **P2**: `IsRKOneStep_exists` — direct corollary packaging the stage tuple
   from P1 into an `IsRKOneStep` witness via the output formula
   `y₁ := y₀ + h • Σᵢ M.b i • f (Y i)`.

Skipped (per strategy §A): §441 Phase C.2 GPFS smoke test (25th consecutive cycle).

## Approach

### P1 — Banach existence

The strategy laid out the mechanical Mathlib-API-discovery work. `lean_loogle "ContractingWith"`
quickly surfaced `ContractingWith.fixedPoint` with signature:

```
ContractingWith.fixedPoint {α} [MetricSpace α] {K} (f : α → α) (hf : ContractingWith K f)
    [Nonempty α] [CompleteSpace α] : α
```

plus the spec lemma `ContractingWith.fixedPoint_isFixedPt : Function.IsFixedPt f (fixedPoint f hf)`,
and `Function.IsFixedPt f x` unfolds to `f x = x` definitionally
(`Function.IsFixedPt.eq` confirms). So the proof body collapsed to three lines:

```lean
have hContract := M.RKStageMap_contracting h hf y₀ h_small
haveI : Nonempty (Fin s → N) := ⟨fun _ => y₀⟩
exact ⟨ContractingWith.fixedPoint _ hContract, hContract.fixedPoint_isFixedPt⟩
```

The `Nonempty (Fin s → N)` instance is supplied explicitly via the constant
function `fun _ => y₀`; Lean's automatic instance synthesis does not derive
`Nonempty` from a single witness in scope.

`CompleteSpace (Fin s → N)` is synthesised automatically via `Pi.completeSpace`
from `[CompleteSpace N]`. No explicit `haveI` needed there.

### P2 — IsRKOneStep corollary

The fixed-point equation `M.RKStageMap h f y₀ Y = Y` applied pointwise via `congrFun`
gives `(M.RKStageMap h f y₀ Y) i = Y i`, which by the definition of `RKStageMap`
is `y₀ + h • ∑ j, M.A i j • f (Y j) = Y i` (defeq, no simp needed). Taking
`.symm` flips this to the form `IsRKOneStep` wants for `hY_stage i`. Body:

```lean
obtain ⟨Y, hY_fix⟩ := M.RKStageMap_fixedPoint_exists h hf y₀ h_small
refine ⟨y₀ + h • ∑ i, M.b i • f (Y i), Y, ?_, rfl⟩
intro i
exact (congrFun hY_fix i).symm
```

Defeq path matches the cycle 203 `equivalent_self` body which used the inverse
direction `(hY_stage i).symm` — confirming `RKStageMap` β-reduction is
recognised by Lean's definitional checker.

## Result

**SUCCESS.** Both theorems compile cleanly and are axiom-clean
(`[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no other axioms).

Verification:
- `lake env lean OpenMath/Chapter3/Section381.lean` completes in ~26 s warm
  (vs. cycle 204 baseline ~4.6 s — overhead is the LSP cold-start from
  cycle 205's edit invalidating the cache; warm rebuild after touch is faster).
- `grep -c sorry OpenMath/Chapter3/Section381.lean` → 0.
- Tautology scanner (`grep -nE ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'`) → 0 hits.
- Cycle 203/204 theorems (`RKStageMap_contracting`, `RKStageMap_fixedPoint_unique`,
  `equivalent_self`, `Equivalent.symm`) still axiom-clean — no regressions.
- New theorems via `lean_verify`:
  - `OpenMath.Chapter3.Section312.RKTableau.RKStageMap_fixedPoint_exists` → `[propext, Classical.choice, Quot.sound]`.
  - `OpenMath.Chapter3.Section312.RKTableau.IsRKOneStep_exists` → `[propext, Classical.choice, Quot.sound]`.

LOC: ~50 lines added (24 for P1 with docstring, 21 for P2 with docstring,
5 lines of separator/spacing).

## Faithfulness check

### `RKStageMap_fixedPoint_exists` (P1)

- **Entity ID**: none — infrastructure abstraction, not a Butcher-named lemma.
- **Lean statement captures**: standard Banach existence on a contracting map.
  Direct application of Mathlib's `ContractingWith.fixedPoint` to cycle 202's
  `RKStageMap_contracting`. Hypotheses match what `RKStageMap_contracting`
  consumes; conclusion is the natural existential.
- **Hypothesis strength**: `[CompleteSpace N]` is new vs. cycle 204's uniqueness
  lemma. Necessary because `ContractingWith.fixedPoint` requires Cauchy
  completion (this is the content of Banach's theorem). Documented in the
  docstring as fired automatically for finite-dimensional N (ℝ, ℝⁿ).
- **Definition smuggling**: N/A (no new def/class/structure).
- **Tautology check**: conclusion `∃ Y, M.RKStageMap h f y₀ Y = Y` is not among
  the hypotheses. No `h_*` introduced ⇒ no tautology scanner hits.
- **Identity check**: 3-line tactic body invoking Mathlib's Banach existence
  via the `ContractingWith` packaging. Not vacuous — packs cycle 202's
  contraction packaging into the standard existence form.

### `IsRKOneStep_exists` (P2)

- **Entity ID**: none — corollary, not Butcher-named.
- **Lean statement captures**: existence of one-step output for any RK tableau
  on a complete N at small `h`. Direct corollary of P1 via the standard RK
  output formula `y₁ := y₀ + h • Σᵢ M.b i • f (Y i)`.
- **Hypothesis strength**: same as P1 — `[CompleteSpace N]` + Lipschitz `f` +
  smallness `|h| · L · C < 1`.
- **Definition smuggling**: N/A.
- **Tautology check**: conclusion `∃ y₁, M.IsRKOneStep f y₀ h y₁` is not among
  the hypotheses.
- **Identity check**: ~4-line body — extracts P1's stage tuple, constructs the
  output, and discharges the stage equations via defeq `.symm`. Not vacuous.

## Dead ends

None. Strategy §B/§C recipes worked on first attempt. The Mathlib API name
discovery (`ContractingWith.fixedPoint`) succeeded on the first `lean_loogle`
query without falling back to the `efixedPoint` or manual-Cauchy-sequence
alternatives sketched in §J.

## Discovery

1. **`ContractingWith.fixedPoint` exists in Mathlib at full strength.** Located
   in `Mathlib.Topology.MetricSpace.Contracting`, takes `[MetricSpace α]` +
   `[Nonempty α]` + `[CompleteSpace α]`. The companion spec lemma
   `fixedPoint_isFixedPt` provides the `Function.IsFixedPt` witness, which is
   definitionally `f x = x` per `Function.IsFixedPt.eq`. No need for the
   `efixedPoint` variant or manual Cauchy-sequence construction.

2. **`Nonempty (Fin s → N)` is NOT automatic from `y₀ : N`.** Even though
   `y₀ : N` is in scope, Lean's instance synthesis doesn't promote a value
   to a `Nonempty` instance. Must explicitly supply
   `haveI : Nonempty (Fin s → N) := ⟨fun _ => y₀⟩`. The constant function
   works for all `s` (including `s = 0`, where any function is trivially
   well-typed).

3. **`CompleteSpace (Fin s → N)` IS automatic** via `Pi.completeSpace`
   from `[CompleteSpace N]` on a finite index type. No `haveI` workaround
   needed.

4. **Defeq path for fixed-point ↔ stage equation extraction confirmed.**
   `congrFun (hY_fix : F Y = Y) i : F Y i = Y i` and `F = RKStageMap h f y₀`
   makes `F Y i = y₀ + h • ∑ j, M.A i j • f (Y j)` defeq, so a bare
   `.symm` closes the `IsRKOneStep` `hY_stage i` goal — no `simp only [RKStageMap]`
   unfold needed (mirroring cycle 203's `equivalent_self` body which used
   the inverse direction).

5. **Both prior known caveats avoided.** The cycle 204 `Equivalent.symm`
   discovery — universe-polymorphic shared `.{u}` annotation across
   `Equivalent` references — does NOT apply here since `Equivalent` doesn't
   appear in either signature. Standard `{N : Type*}` polymorphism suffices.

## Suggested next approach

Per strategy §I, ordered by priority:

1. **Planner decision on `Equivalent.trans` blocking question.** With P1+P2 now
   landed, the path forward for trans is either:
   - **(a)** Strengthen the `Equivalent` definition with `[CompleteSpace N]`.
     trans becomes a ~15 LOC corollary using `IsRKOneStep_exists` (cycle 205 P2).
     Faithfulness cost: definition narrows to complete normed spaces. Requires
     re-verifying cycle 030's `equivalent_explicitEuler_self`, cycle 203's
     `equivalent_self`, cycle 204's `Equivalent.symm` + `paddedEuler_equivalent_self`
     still compile under the extra typeclass binder.
   - **(b)** Side-hypothesis variant — awkward because N is bound inside the def.
   - **(c)** Defer trans entirely; ship 2/3 of equivalence-relation closure
     (refl from cycle 203, symm from cycle 204) and route around for now.
   This is a planner judgment call; the worker layer should not freelance the
   def change.

2. **`PReducesTo → Equivalent`** (deferred direction (2) of `thm:381H`).
   Now unblocked by `IsRKOneStep_exists`. Estimated 2–3 cycles; requires the
   iteration-invariant "`Yᵢ⁽ᵏ⁾ = Yⱼ⁽ᵏ⁾` for `i, j` in same partition block"
   plus an `IsRKOneStep` extraction recipe leveraging the cycle 205 existence
   helper.

3. **`paddedEuler` non-vacuity witness for `IsRKOneStep_exists`** (cycle 205
   §D, optional, deferred). Concrete check that the existence helper fires
   non-vacuously — ~5 LOC. Low priority since cycle 204's
   `paddedEuler_equivalent_self` already serves as the concrete-method
   non-vacuity sanity check for the broader Banach FP chain.

4. **A different §380 entity** (`thm:382A`, `thm:382B`, `thm:384A`, `thm:386A`)
   if the cycle 206 planner judges def:381F closure of less value than
   opening a new sub-cluster.

5. **§441 Phase C.2 GPFS smoke test** — only if a loop-maintainer signal
   indicates GPFS recovery. Otherwise continue the 25+ consecutive skip pattern.
