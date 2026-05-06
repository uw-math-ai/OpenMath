# Cycle 160 Results

## Worked on

Mechanical refactor at p = 0 in `OpenMath/Chapter5/Section530.lean`:
extracted the cycle-153 inline T1+T2 closure (used verbatim by cycles
153, 156, and 159 at the i = 0 channel) into a free-standing private
helper, mirroring cycle 158's `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`
extraction at p = 1. Net result: cycles 158 + 160 together form a
complete shared-machinery cover for the explicit-Euler i = 0 channel
at p ∈ {0, 1}.

## Approach

1. **Located the four sites** with `lean_file_outline`:
   - cycle 158 helper at lines 955-1085 (template),
   - cycle 153 (`explicitEulerGLM_hasOrderZero_trivialStarting`),
   - cycle 156 i = 0 channel
     (`padded2DEulerGLM_hasOrderZero_padCompatStarting`),
   - cycle 159 i = 0 channel
     (`padded3DEulerGLM_hasOrderZero_pad3CompatStarting`).

2. **Designed the helper signature** to match cycle 158's shape but
   with weaker hypotheses (only `HasDerivAt yex (f y₀) x₀`, no
   `ContDiff ℝ 2`, no full ODE relation) and an `O(h)` (not `O(h²)`)
   conclusion:
   ```lean
   private theorem taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
       {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
       {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
       (hyex_x₀ : yex x₀ = y₀)
       (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
       (fun h : ℝ =>
           ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
             - (yex (x₀ + h) + h * f (yex (x₀ + h))))
         =O[nhds (0 : ℝ)] (fun h : ℝ => h)
   ```
   Body: `hsplit` decomposes into T1 + T2; T1 = `(y₀ + h·f y₀) − yex(x₀+h)`
   is `o(h)` via `hasDerivAt_iff_isLittleO_nhds_zero`, hence `O(h)`;
   T2 = `h · (f(y₀ + h·f y₀) − f(yex(x₀+h)))` is `O(h)` via
   `LipschitzWith.dist_le_mul` combined with continuity-driven
   `|·| ≤ 1` eventually near `h = 0`.

3. **Placed the helper** before
   `explicitEulerGLM_hasOrderZero_trivialStarting` (cycle 153, the
   first consumer in file order). Note: the strategy specified
   placing it "immediately before the cycle 158 helper", but cycle
   153 is the first consumer of the new helper, so the helper has
   to be defined first to respect Lean's forward-only declaration
   order. The cycle 158 helper retains its position between cycle
   153 and cycle 154.

4. **Refactored each consumer site**: dropped the inline T1+T2 body
   (~70 LOC each); reshaped the `hcongr` rewrite to drop the trailing
   `ring` step (the helper accepts the `((·) + h·f(·)) − (·)` shape
   that `rw [hSM, hES]` produces directly, so no `ring` is needed);
   discharged with one line:
   ```lean
   exact taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
     hf_lip hyex_x₀ hyex_deriv
   ```

5. **Verified**: full Section530 + Chapter5 build clean; axioms
   (`[propext, Classical.choice, Quot.sound]`) on all thirteen
   relevant declarations.

## Result

SUCCESS — all primary deliverables landed.

* **New helper**:
  `OpenMath.Chapter5.Section530.taylor_lipschitz_explicitEuler_orderZero_diff_isBigO`
  — axiom-clean.
* **Three call sites refactored**:
  - `explicitEulerGLM_hasOrderZero_trivialStarting` (cycle 153)
  - `padded2DEulerGLM_hasOrderZero_padCompatStarting` (cycle 156,
    i = 0 channel; i = 1 zero-collapse untouched)
  - `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` (cycle 159,
    i = 0 channel; i = 1, i = 2 zero-collapse untouched)
* **Cycle 158 helper + p = 1 consumers re-verified axiom-clean**
  to confirm no upstream breakage:
  - `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`
  - `explicitEulerGLM_hasOrderOne_trivialStarting`
  - `padded2DEulerGLM_hasOrderOne_padCompatStarting`
  - `padded3DEulerGLM_hasOrderOne_pad3CompatStarting`
* **Six def:530C wrappers re-verified axiom-clean**:
  - `explicitEulerGLM_hasOrderZero`, `explicitEulerGLM_hasOrderOne`
  - `padded2DEulerGLM_hasOrderZero`, `padded2DEulerGLM_hasOrderOne`
  - `padded3DEulerGLM_hasOrderZero`, `padded3DEulerGLM_hasOrderOne`
* **LOC delta**: 2034 → 1951 LOC (−83 LOC). Smaller than the
  strategy's projected −290 because each cycle 153/156/159 inline
  T1+T2 body was ~70 LOC (not ~130 as estimated), and the new helper
  body itself is ~100 LOC. Three × ~70 = 210 saved, minus 100 for
  the helper, plus ~30 LOC of doc comments on the helper, gives the
  observed −83 LOC.
* **Sorry count**: 0 → 0 (unchanged).
* **Tautology-scanner regex**
  `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` clean on
  `OpenMath/Chapter5/Section530.lean`.

## Faithfulness check

**No new mathematical content was introduced this cycle.** The new
private helper packages the existing cycles 153 / 156 / 159 closure
body into a named lemma; no statement has been weakened, strengthened,
or reformulated. The cycle 158 helper precedent (cycle 158 task results)
established that this kind of refactor does not warrant a per-entity
faithfulness check: the helper is not a textbook entity, it is a
proof-structure decomposition.

For completeness, the new helper:

* **Entity ID**: NONE — it is a private internal helper, not a
  textbook entity.
* **Lean statement**: faithful by construction — it is the literal
  `=O[nhds 0]` claim that all three p = 0 witnesses (cycles 153 / 156
  / 159) used inline.
* **Hypothesis check**: helper takes
  `hyex_x₀ : yex x₀ = y₀` and
  `hyex_deriv : HasDerivAt yex (f y₀) x₀`, identical to cycle 153's
  hypotheses. No hypothesis strengthening.

The three refactored consumers retain their original signatures,
hypotheses, and conclusions verbatim. Only the proof body changes,
which is mathematically irrelevant per cycle 158's precedent.

## Dead ends

None. The refactor was straightforward; the cycle 158 precedent gave
the exact pattern. The only mid-course correction: the strategy
specified placing the new helper "immediately before the cycle 158
helper", but the cycle 158 helper sits *between* cycle 153 and cycle
154 in the current file order, while cycle 153 is the new helper's
first consumer. The strategy's ordering would have required also
moving cycle 153 below cycle 158 (a substantial re-shuffle the
strategy did not authorize). Pragmatic resolution: place the new
helper before cycle 153 instead. The helpers don't need to be
syntactically adjacent for the dependency graph to work; only the
forward-declaration constraint matters.

## Discovery

* **The `hcongr` reshape simplification**: cycle 156's original
  `hcongr` produced
  `((y₀ + h·f y₀) − yex(x₀+h)) + h · (f(...) − f(...))`
  via `rw [hSM, hES]; ring`. The refactored `hcongr` produces
  `((y₀ + h·f y₀) + h · f(y₀ + h·f y₀)) − (yex(x₀+h) + h · f(yex(x₀+h)))`
  via `rw [hSM, hES]` alone (no `ring`), because that's the literal
  result of substituting the SM and ES closed forms. Saves one line
  per call site and avoids triggering ring normalization on a
  λ-abstracted goal.
* **Strategy LOC estimate over-budgeted**: cycle 158 actually saved
  76 LOC for two consumers; this cycle saved 83 LOC for three
  consumers. The cycle-158 "−290 expected" estimate assumed each
  inline body was ~130 LOC (matching cycle 158's helper body), but
  cycle 153's body is only ~70 LOC because p = 0 doesn't need the
  Taylor expansion machinery. Actual savings are ~25-30 LOC per
  consumer, after accounting for the unmoved hcongr/hpow scaffolding
  and the new helper's own LOC cost. This is the correct yardstick
  for future helper-extraction cycles in this area.

## Suggested next approach

Cycles 158 + 160 close the i = 0 channel refactor at p ∈ {0, 1}.
Concrete options for cycle 161, in order of payoff:

1. **`r`-parametric padded GLM family
   `paddedRDEulerGLM (r : ℕ)`** (cycle 156/159 worker's deferred
   suggestion; aligns with the strategy's "future r-extension"
   compounded payoff). Define
   `paddedRDEulerGLM : ∀ r ≥ 1, GeneralLinearMethod 1 r` plus a
   uniform `padRCompatStartingMethod : ∀ r ≥ 1, StartingMethod r`,
   then prove
   `padRDEulerGLM_hasOrder{Zero,One}_padRCompatStarting` by induction
   on `r`. Each inductive step's i = 0 channel is one of the two
   cycles 158 / 160 helpers; the i ≥ 1 cases zero-collapse uniformly
   via `Asymptotics.isBigO_zero`. This **eliminates** the cycle 156 /
   159 / (hypothetical 161 r = 4) duplication entirely, replacing
   six pairs of theorems (r ∈ {2, 3, 4} × p ∈ {0, 1}) with one pair.
   Estimated 2-3 cycle effort but shrinks Section530 by another
   ~500 LOC and obviates all future r-extension work.

2. **Backup A from this cycle's strategy: r = 4 lift**. Mechanical
   port of cycle 159's r = 3 infrastructure to r = 4. Validates
   cycles 158 + 160 helpers at a fourth call site each. Score
   expectation: 2. Held in reserve.

3. **Higher-order GLM order witness**: explicit Euler is a
   1st-order method, so its SM−ES diff is genuinely `O(h²)` (not
   `O(h³)`). A `p = 2` non-vacuity witness requires a higher-order
   GLM such as RK2 or midpoint. New helper machinery: a Taylor-degree-3
   variant of the cycle 158 helper. Multi-cycle effort.

4. **Pivot to Path B (implicit method via fixed-point)** —
   multi-cycle infrastructure deferred per
   `.prover-state/issues/def_530B_scaffold_strategy.md`. Not yet
   ripe.

5. **Pivot away from def:530B/C entirely** to a fresh entity
   (e.g. `def:451A`, `def:422B`, `thm:381G`, `thm:521B`). Each
   requires multi-cycle setup work; consider after the def:530B/C
   r-parametric refactor lands.

The recommended target is **option 1 (`r`-parametric family)**
because it leverages the cycles 158 + 160 helpers in their natural
form (one-line per channel), eliminates the existing r ∈ {2, 3}
duplication rather than extending it, and locks in a structurally
clean Section530 before any pivot to higher-order methods or to
Path B.
