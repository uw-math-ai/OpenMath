# Cycle 159 Results

## Worked on

Lifted the cycle 156/157 r = 2 padded-Euler Path-A non-vacuity grid
to r = 3 for `def:530B` and `def:530C`, mirroring the cycle 156 →
cycle 157 lift exactly. Two new substantive witnesses
(`padded3DEulerGLM × pad3CompatStartingMethod` at p = 0 and p = 1),
plus their `def:530C` wrappers, plus the supporting infrastructure
(`padded3DEulerGLM` def in Section520, plus six theorems and three
defs in Section530). The p = 1 witness's i = 0 channel is a one-line
invocation of cycle 158's helper
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`, validating its
portability to a third call site.

No Aristotle traffic this cycle — all deliverables are mechanical
extensions of cycles 156/157/158 with proven proof shapes; manual
closure was strictly faster than waiting on Aristotle.

## Approach

1. Loaded the formalization data for `def:530B` and `def:530C` from
   `extraction/formalization_data/entities/`; confirmed both
   textbook statements; confirmed the cycle 157 saturation at r = 2
   and that the cycle 158 refactor extracted the p = 1 helper.

2. **Step 1** (Section520.lean, +13 LOC): added `padded3DEulerGLM :
   GeneralLinearMethod 1 3` immediately after `padded2DEulerGLM`
   with `A = !![0]`, `U = !![1, 0, 0]`, `B = !![1; 0; 0]`,
   `V = !![1, 0, 0; 0, 0, 0; 0, 0, 0]`. No new Section520
   corollaries (Section520 r = 3 stability/A-stability theorems are
   out of scope for this cycle per the planner).

3. **Step 2** (Section530.lean, +51 LOC): added `pad3CompatMethod`
   (3-arm pattern match; index 0 → `trivialGeneralizedRK`, indices 1
   and 2 → `zeroGeneralizedRK`), `pad3CompatStartingMethod`,
   `pad3CompatStartingMethod_isNonDegenerate` (closed via
   `StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero` at index 0),
   and `pad3CompatStartingMethod_constituents_isExplicit` (3-arm
   `fin_cases i`; index 0 cites `trivialGeneralizedRK_isExplicit`;
   indices 1 and 2 close via `intro a b _; fin_cases a; fin_cases b;
   rfl`).

4. **Step 3** (Section530.lean, +13 LOC): added
   `padded3DEulerGLM_isExplicit` after `padded2DEulerGLM_isExplicit`;
   identical proof shape (`A = !![0]` is vacuously strict-lower-
   triangular at `s = 1`).

5. **Step 4** (Section530.lean, +18 LOC): added
   `pad3CompatStartingMethod_applyExplicit` after
   `padCompatStartingMethod_applyExplicit`; closed form is
   `![y₀ + h * f y₀, 0, 0]`. Index 0 cites
   `trivialGeneralizedRK_explicitApply` (cycle 152 helper); indices 1
   and 2 cite `zeroGeneralizedRK_explicitApply` (cycle 156 private
   helper).

6. **Step 5** (Section530.lean, ~155 LOC): added
   `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` (p = 0).
   Three-arm `fin_cases i` proof:
   * **i = 0 channel** — same algebraic shape as cycle 156's i = 0:
     SM[0] / ES[0] closed-form rewrites yield
     `(y₀ + h·f y₀) + h·f(y₀ + h·f y₀)` and `yex(x₀+h) + h·f(yex(x₀+h))`;
     T1 + T2 decomposition (T1 little-o(h) via `HasDerivAt`, T2 O(h)
     via Lipschitz + continuity-driven eventual `|·| ≤ 1`).
   * **i = 1 channel** — SM[1] = ES[1] = 0; close by
     `Asymptotics.isBigO_zero`.
   * **i = 2 channel** — identical to i = 1.

7. **Step 6** (Section530.lean, ~135 LOC): added
   `padded3DEulerGLM_hasOrderOne_pad3CompatStarting` (p = 1).
   Three-arm `fin_cases i` proof:
   * **i = 0 channel** — SM[0] / ES[0] closed-form rewrites identical
     to cycle 157's i = 0; an `h^(1+1) = h^2` collapse; then a
     one-line `exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
     hf_lip hyex_x₀ hyex_C2 hyex_ode`. Third call site for the
     cycle 158 helper.
   * **i = 1 channel** — zero-collapse with exponent `h^(1+1)`,
     identical structure to cycle 157's i = 1.
   * **i = 2 channel** — identical to i = 1.

8. **Step 7** (Section530.lean, +30 LOC): added
   `padded3DEulerGLM_hasOrderZero` (def:530C wrapper, p = 0) and
   `padded3DEulerGLM_hasOrderOne` (def:530C wrapper, p = 1) as
   4-line existential closures exhibiting `pad3CompatStartingMethod`
   as the witness, citing
   `pad3CompatStartingMethod_isNonDegenerate`,
   `pad3CompatStartingMethod_constituents_isExplicit`, and the
   underlying `..._pad3CompatStarting` theorems.

9. **First-pass build error**: the initial `simp` invocations in the
   SM[i] closed-form lemmas (lines 1761/1801/1873/1929/1969 and the
   two `..._isBigO` parent rewrites) failed to fully reduce
   `∑ x : Fin 3, ![…] x * ![…] x`. The cycle 156 r = 2 closures
   work because Mathlib has `Fin.sum_univ_two` as a default-tagged
   simp lemma but `Fin.sum_univ_three` is not auto-tagged. Fixed by
   adding `Fin.sum_univ_three` to the simp set in all five SM[i]
   closed-form rewrites. After this fix, the file compiled cleanly.

10. **Verification** (mandatory):
    * `lake env lean OpenMath/Chapter5/Section520.lean` exits 0.
    * `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
    * `lake env lean OpenMath/Chapter5.lean` exits 0 (full module).
    * `grep -c sorry` on both files → 0.
    * Tautology-scanner regex
      `':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'` → 0 hits.
    * `lean_verify` axiom-clean
      (`[propext, Classical.choice, Quot.sound]`) on all eight new
      theorems:
      - `pad3CompatStartingMethod_isNonDegenerate`
      - `pad3CompatStartingMethod_constituents_isExplicit`
      - `padded3DEulerGLM_isExplicit`
      - `pad3CompatStartingMethod_applyExplicit`
      - `padded3DEulerGLM_hasOrderZero_pad3CompatStarting`
      - `padded3DEulerGLM_hasOrderOne_pad3CompatStarting`
      - `padded3DEulerGLM_hasOrderZero`
      - `padded3DEulerGLM_hasOrderOne`
    * No regression on cycle 153/154/155/156/157/158 theorems —
      re-verified axiom-clean (all eight pre-existing
      `def:530B`/`def:530C` Path-A theorems plus the cycle 158
      helper's transitive consumers).

## Result

**SUCCESS.** All seven planned steps landed; all verification gates
pass. The substantive deliverables are the four new theorems
* `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` (p = 0,
  `def:530B`)
* `padded3DEulerGLM_hasOrderOne_pad3CompatStarting` (p = 1,
  `def:530B`)
* `padded3DEulerGLM_hasOrderZero` (p = 0, `def:530C`)
* `padded3DEulerGLM_hasOrderOne` (p = 1, `def:530C`)

plus the four supporting infrastructure theorems and three new
defs (one in Section520, two in Section530).

* Section520.lean: 1678 → 1691 LOC (+13).
* Section530.lean: 1524 → 2034 LOC (+510).
* Total file delta: +523 LOC.
* Sorry count: 0 → 0 (unchanged).
* `lean_status.json`: `def:530B` and `def:530C` cycle bumped from
  157 to 159; both remain `partial` (Path B implicit branch still
  deferred).
* `plan.md`: `def:530B` and `def:530C` rows extended with cycle 159
  notes mirroring cycles 156/157's note style.
* `.prover-state/issues/def_530B_scaffold_strategy.md`: appended a
  "Cycle 159 update — r = 3 non-vacuity witnesses landed" section
  with the eight enumerated artefacts and the verification outcome.

## Faithfulness check

For each new declaration introduced this cycle:

### `padded3DEulerGLM` (Section520, def)
* Not a textbook entity — internal infrastructure (per CLAUDE.md
  "If Mathlib is missing something, build it yourself as a helper
  lemma"). Lifts cycle 133's `padded2DEulerGLM` from r = 2 to r = 3.
* No textbook entity matches; no statement to deviate from.

### `pad3CompatMethod`, `pad3CompatStartingMethod` (Section530, def)
* Internal infrastructure; not textbook entities.
* Mirror of cycle 156's `padCompatMethod` / `padCompatStartingMethod`
  with the index range extended from `Fin 2` to `Fin 3`. Same
  trivial-channel-at-index-0 + zero-channel-elsewhere construction.

### `pad3CompatStartingMethod_isNonDegenerate` (theorem)
* Internal supporting non-vacuity infrastructure.
* **Tautology check**: ✓ — conclusion is
  `pad3CompatStartingMethod.IsNonDegenerate`; no hypothesis has this
  form (no hypotheses).
* **Identity check**: ✓ — the proof is
  `rw [...]; refine ⟨0, ?_⟩; show (1 : ℝ) ≠ 0; exact one_ne_zero`,
  not `exact h_*`.
* **Hypothesis strength check**: ✓ — no hypotheses.
* **Absent theorem check**: ✓ — body is self-contained.

### `pad3CompatStartingMethod_constituents_isExplicit` (theorem)
* Internal supporting infrastructure.
* All four checks pass identically to cycle 156's
  `padCompatStartingMethod_constituents_isExplicit`.

### `padded3DEulerGLM_isExplicit` (theorem)
* Internal supporting infrastructure.
* All four checks pass identically to cycle 156's
  `padded2DEulerGLM_isExplicit`.

### `pad3CompatStartingMethod_applyExplicit` (theorem)
* Internal supporting infrastructure (closed form for the SE
  operator on `pad3CompatStartingMethod`).
* All four checks pass identically to cycle 156's
  `padCompatStartingMethod_applyExplicit`.

### `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` (theorem)
* Entity ID and textbook statement: not a direct entity — this is
  the r = 3 × p = 0 corner of the Path A non-vacuity grid for
  `def:530B`. Witnesses
  `HasOrderRelativeTo_explicit padded3DEulerGLM
   pad3CompatStartingMethod _ _ 0 f yex x₀ y₀` under
  `LipschitzWith L f`, `yex x₀ = y₀`, and `HasDerivAt yex (f y₀) x₀`
  — exactly the cycle 156 hypothesis pack at r = 3.
* Lean statement captures: same content as cycles 153 and 156's
  p = 0 witnesses, just at the r = 3 GLM/starting-method shape.
* Tautology / identity / strength / absent checks: ✓ on all four.

### `padded3DEulerGLM_hasOrderOne_pad3CompatStarting` (theorem)
* Entity ID and textbook statement: not a direct entity — this is
  the r = 3 × p = 1 corner of the Path A non-vacuity grid for
  `def:530B`. Witnesses
  `HasOrderRelativeTo_explicit padded3DEulerGLM
   pad3CompatStartingMethod _ _ 1 f yex x₀ y₀` under
  `LipschitzWith L f`, `yex x₀ = y₀`, `ContDiff ℝ 2 yex`, and
  `∀ x, HasDerivAt yex (f (yex x)) x` — exactly the cycle 154/157
  hypothesis pack at r = 3.
* Lean statement captures: same content as cycles 154 and 157's
  p = 1 witnesses, just at the r = 3 GLM/starting-method shape.
* Tautology / identity / strength / absent checks: ✓ on all four.

### `padded3DEulerGLM_hasOrderZero` (def:530C wrapper, p = 0)
* Entity ID and textbook statement (def:530C, Butcher §530, p. 432):
  > A general linear method M has order p if there exists a
  > non-degenerate starting method S such that M has order p
  > relative to S.
* Lean statement captures: same content. The wrapper is the
  existential closure of the cycle-156-style underlying
  `..._pad3CompatStarting` theorem at r = 3, exhibiting
  `pad3CompatStartingMethod` as the existential witness with
  non-degeneracy via `pad3CompatStartingMethod_isNonDegenerate`.
* Tautology / identity / strength / absent checks: ✓ on all four.

### `padded3DEulerGLM_hasOrderOne` (def:530C wrapper, p = 1)
* Entity ID and textbook statement: same as the p = 0 wrapper
  (def:530C is parametric over p).
* Lean statement captures: same content; analogous existential
  closure for p = 1 instead of p = 0.
* Tautology / identity / strength / absent checks: ✓ on all four.

### `padded3DEulerGLM_hasOrderZero` and `padded3DEulerGLM_hasOrderOne`
together saturate the r = 3 corner of the Path-A non-vacuity grid
for `def:530C`. The textbook def:530C is now witnessed at r ∈
{1, 2, 3} × p ∈ {0, 1}.

## Dead ends

The first compile attempt failed because the `simp` set in the
SM[i] closed-form rewrites did not reduce `∑ x : Fin 3, …`; the
cycle 156 r = 2 closures had been silently relying on
`Fin.sum_univ_two` being a default-tagged simp lemma whereas
`Fin.sum_univ_three` is not. Adding `Fin.sum_univ_three` to the
simp set fixed all five sites.

This was a 5-minute fix, so it doesn't qualify as a "dead end" —
just a build-loop iteration. No real dead end this cycle; the
strategy was conservative (had a backup-plan tier defined for the
case Step 5 stalled past 3 hours, and a deeper backup if Step 5
stalled past 4 hours), but the first signature shape compiled
cleanly after the simp fix.

## Discovery

* **`Fin.sum_univ_two` is auto-tagged `@[simp]` but
  `Fin.sum_univ_three` is not.** This is implicit in the cycle 156
  closure's working without explicit hints, and was the only
  build-loop iteration this cycle. For future r ≥ 3 padded
  closures, add `Fin.sum_univ_three` (or the appropriate
  `Fin.sum_univ_<r>` for higher r) to the simp set explicitly.

* **The cycle 158 helper transferred immediately at the third call
  site.** The strategy explicitly suggested a fallback if the
  helper's hypothesis pack were insufficient at r = 3, but the
  one-line `exact ...` closure compiled on the first attempt. The
  helper's (a) direct-subtraction conclusion shape and (b) closed
  form on `(y₀, x₀, h, yex, f)` rather than on the GLM/starting-
  method shape was exactly the right abstraction layer for r-lift
  portability.

* **The r = 3 lift roughly tripled the file size of the
  HasOrderRelativeTo_explicit infrastructure.** Cycle 157 produced
  a 2-arm `fin_cases i` proof; cycle 159 produces a 3-arm proof.
  The structural inflation suggests an `r`-parametric padded GLM
  family `paddedRDEulerGLM (r : ℕ)` (with the corresponding
  `padRCompatStartingMethod`) could compress all current witnesses
  via `r`-induction. However, this is a multi-cycle refactor and
  is not a clean pivot from the current cycle's substantive work.

* **The cycle 158 helper has compounded LOC savings now.** Without
  the helper, cycle 159's p = 1 witness's i = 0 channel would have
  been a third copy of the ~135 LOC Taylor + Lipschitz body
  (totaling ~405 LOC across the three sites). With the helper, the
  three sites total ~30 LOC of glue + ~140 LOC for the helper itself
  = ~170 LOC, a saving of ~235 LOC vs the unrefactored shape.

## Suggested next approach

For the planner to consider next cycle:

1. **Generalising the cycle 158 helper over the Taylor degree.**
   This was deferred from cycle 159 in favour of the substantive
   r = 3 lift. With the helper now validated at three call sites
   (cycles 154, 157, 159), the parameterisation is a clean
   single-cycle refactor: index over `Nat.succ p` Taylor degree to
   absorb cycles 153/156 i = 0 (p = 0 cases) plus 154/157/159 i = 0
   (p = 1 cases) into a single helper. The arithmetic gain:
   |cycles 153/156 i = 0 closures| ≈ 200 LOC × 2 sites = 400 LOC
   absorbed; new parametric helper ≈ 250 LOC; net saving ≈ 150 LOC
   on top of cycle 158's −76 LOC.

2. **Path A r = 4 non-vacuity witnesses.** A clean port of the
   cycle 156 → 157 → 159 lift to r = 4 would produce
   `padded4DEulerGLM × pad4CompatStartingMethod` at p ∈ {0, 1}; the
   cycle 158 helper still applies at the i = 0 channel. The
   structural inflation from r = 3 to r = 4 is modest (~150 LOC),
   so this is a +1 cycle, not a +2 cycle. However, this is
   incremental — the substantive interest peters out beyond r = 3
   without an `r`-parametric refactor.

3. **`r`-parametric padded GLM family.** Define
   `paddedRDEulerGLM (r : ℕ) : GeneralLinearMethod 1 (r + 1)` and
   `padRCompatStartingMethod (r : ℕ) : StartingMethod (r + 1)` and
   prove the order-zero / order-one witnesses by induction on r.
   This is a multi-cycle refactor and would saturate the entire
   Path-A non-vacuity grid for arbitrary r at p ∈ {0, 1}. Combined
   with suggestion 1 (Taylor-degree parametrisation) it would
   saturate the entire Path-A grid at p ∈ {0, 1} for arbitrary r in
   a single capstone witness. Multi-cycle but with high payoff.

4. **`thm:532A`** remains blocked on the §31x rooted-tree
   elementary-differential infrastructure (per cycles 157/158 task
   results). Multi-cycle.

5. **`thm:550A` general-`n`** remains blocked per
   `thm_550A_general_n.md`. Multi-cycle.

6. **A higher-order GLM for substantive p ≥ 2 witnesses.** Explicit
   Euler is a 1st-order method; its SM−ES diff is genuinely O(h²),
   not O(h³). A substantive p = 2 witness requires a higher-order
   GLM such as RK2 (Heun) or midpoint, which is a multi-cycle
   infrastructure effort.

The cleanest cycle 160 candidate is suggestion 1
(Taylor-degree parametrisation of cycle 158's helper), which
compounds the cycle 158/159 LOC savings without opening any new
infrastructure scope.
