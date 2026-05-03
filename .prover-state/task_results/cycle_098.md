# Cycle 098 Results

## Worked on

* **Priority 0a (scanner-cleanup, MANDATORY)**: rename
  `h_dot`/`h_inner`/`h_mono` → `hdot`/`hinner`/`hmono` in
  `Section514.lean` (cycle 097 false positives) and `Section404.lean`
  (pre-existing baseline hit at lines 5774–5779). Eliminates the
  tautology-scanner false positives without changing semantics.
* **Priority 1 (option iii of `u_prime_equals_u_bridge.md`)**:
  strengthen `def:512A GeneralLinearMethod.IsConvergent` to expose the
  internal-stage limit, enabling future extraction of `U·u' = 𝟙` for
  `cesaro_residual_tendsto_zero` (gated to a future cycle).
* Re-verify the cycle 093 §513 consumer (`convergent_isStable`) and
  cycle 096 §514 consumer (`convergence_witness_isVfixed`) under the
  new signature — both axiom-clean.
* New issue file documenting the faithfulness-divergent strengthening.

## Approach

1. Renamed underscore-prefixed `have` bindings to non-underscore form
   to bypass the tautology-scanner false positive (cycle 014/015
   precedent).
2. Re-read `Section512.lean::138-160` (`IsConvergent`),
   `Section513.lean::344-495` (cycle 093 consumer), and
   `Section514.lean::436-532` (cycle 096 `convergence_witness_isVfixed`).
3. Wrote the design note `glm_isconvergent_strengthened.md`
   documenting the proposed shape (kept `M.IsGLMSolution` existential,
   added a separate stage parameter `Y_int : ℕ → Fin s → ℝ` for the
   diagonal stage), the bridge motivation, and the downstream impact
   on §513/§514.
4. Modified `IsConvergent` to add `Y_int` as an extra universal
   parameter, an explicit stage equation as a hypothesis (so consumers
   pick a coherent stage choice), and a stage-limit conclusion
   `Tendsto Y_int atTop (nhds (fun _ => yex x))`.
5. Updated §513 to construct `Y_int m i := ∑ j, M.U i j * Y m m j`
   (stage equation collapses for `f ≡ 0`); destructured the now-pair
   conclusion to keep the existing `hconv` flow intact.
6. Updated §514's `convergence_witness_isVfixed` to construct
   `Y_int n i := (∑ j, M.A i j * (h * f 0)) + (U *ᵥ Y n n) i` (stage
   equation reduces to a constant rewrite of `f` since it is constant
   for `f ≡ 1`); destructured the pair conclusion.
7. Updated the docstring of `cesaro_residual_tendsto_zero` to record
   how the strengthening unblocks closure in a future cycle.
8. Verified `lake build OpenMath.Chapter5` succeeds; axiom-checked
   `convergent_isStable` (clean) and
   `convergent_preconsistent_isConsistent` (only the pre-existing
   `cesaro_residual_tendsto_zero` `sorryAx`).

## Result

**SUCCESS** — both Priority 0a and Priority 1 deliverables landed.

* Sorry count unchanged: 1 (`cesaro_residual_tendsto_zero`).
* Tautology-scanner regex matches: 0 across `OpenMath/`.
* `convergent_isStable` axioms: `[propext, Classical.choice, Quot.sound]`.
* `convergent_preconsistent_isConsistent` axioms:
  `[propext, sorryAx, Classical.choice, Quot.sound]` — `sorryAx` is
  the pre-existing single `sorry`, not a new gap.
* `lake build OpenMath.Chapter5`: 2775/2775 jobs succeed.

### Aristotle batch decision

This cycle is a *definitional* strengthening with manual adapter
work. Both adapters are by-construction (the §513 stage equation
reduces to `0 = 0` for `f ≡ 0`; the §514 stage equation reduces by
`simp only [hf_def]` for `f ≡ 1`). No genuinely-loaded sub-lemma was
suitable for Aristotle. The remaining `cesaro_residual_tendsto_zero`
sorry requires open mathematical work (extraction of `U·u' = 𝟙`
from the new stage-limit + a uniqueness step for preconsistency
vectors); attempting it via Aristotle this cycle is premature
because the proof outline must first be drafted by hand. Submitting
to Aristotle on a closure-blocked sorry would consume free compute
on a job that cannot succeed without further setup.

## Faithfulness check

### Modified `def`: `GeneralLinearMethod.IsConvergent` (Section512.lean:138)

* Entity: `def:512A` (Butcher §512, p. 409).
* Textbook statement (quoted from `entities/def_512A.json`):

  > "A general linear method `(A, U, B, V)`, is 'convergent' if for any
  > initial value problem `y'(x) = f(y(x)), y(x₀) = y₀`, subject to the
  > Lipschitz condition `‖f(y) − f(z)‖ ≤ L ‖y − z‖`, there exist a
  > non-zero vector `u ∈ ℝ^r`, and a starting procedure
  > `φ : (0, ∞) → ℝ^r`, such that for all `i = 1, 2, …, r`,
  > `lim_{h→0} φ_i(h) = u_i y(x₀)`, and such that for any `x > x₀`, the
  > sequence of vectors `y^{[n]}`, computed using `n` steps with
  > stepsize `h = (x − x_0)/n` and using `y^{[0]} = φ(h)` in each case,
  > converges to `u y(x)`."

* Lean statement captures: **stronger than textbook**.
* Justification for divergence: the textbook constrains only the
  *output* sequence `Y n n`; the strengthening additionally requires
  a coherent internal-stage sequence `Y_int n` whose diagonal tends
  to `(fun _ => yex(x))`. This is needed because `U·u' = 𝟙` is
  provably NOT extractable from the textbook statement (cycle 097
  closed off "option (b)" of `u_prime_equals_u_bridge.md`). The
  strengthening parallels the LMM precedent
  (`is_convergent_strengthened.md`) and is documented as a
  faithfulness divergence in `glm_isconvergent_strengthened.md`.
* All consumers (cycle 093 §513, cycle 096 §514) re-verified
  axiom-clean under the new signature.

### No new `theorem` or `structure` introduced this cycle.

## Dead ends

None — the design choice of *keeping* `M.IsGLMSolution` (rather than
unfolding it inline as the strategy's recommended Step-2 sketch
suggested) avoided restructuring the per-step equation; consumers
only needed to additionally produce `Y_int` and prove the stage
equation, which collapses for both `f ≡ 0` and `f ≡ 1` because `f`
is constant.

The first attempt at the §513 stage-equation proof used `rw [hf_def]; simp`,
which reverse-folded `(fun _ => 0)` back to a different name (since
both `f` and `yex` were `fun _ => 0` in scope) and produced a
mismatched goal. Replaced with an explicit
`Finset.sum_eq_zero` + `ring` to avoid the simp ambiguity.

The first attempt at the §514 stage-equation proof used
`congr 1; refine Finset.sum_congr rfl ...; rw [hf_def]`, but `congr 1`
already closed the goal definitionally (since `f` is constant on
both `0 : ℝ` and `Y_int n j`), leaving "no goals to be solved" for
the `refine`. Replaced with a single `simp only [hf_def]`.

## Discovery

* **Compile artefact gotcha**: running `lake env lean
  OpenMath/Chapter5/Section512.lean` does NOT update
  `.lake/build/lib/lean/.../Section512.olean` — only the
  `.olean.hash` and `.ilean` files. Downstream files (Section513,
  Section514) loaded against this section then see the **stale** def.
  Fix: run `lake build OpenMath.Chapter5.Section512` (~120s) to
  refresh the persistent olean. Saved this insight for future
  definition-changing cycles.

* **Stage equation triviality for constant `f`**: when the IVP's RHS
  is constant (as in §513's `f ≡ 0` and §514's `f ≡ 1`), the stage
  equation `Y_int n i = ∑ A i j * (h * f (Y_int n j)) + (U *ᵥ Y n n) i`
  becomes a literal definition of `Y_int n` in terms of `Y n n` (no
  fixed-point machinery needed). The strengthening is therefore
  consumer-cheap when the RHS is constant — exactly the regime where
  §513 and §514 instantiate it.

## Suggested next approach

For cycle 099+:

1. **Close `cesaro_residual_tendsto_zero`** using the strengthened
   def. Sketch:
   * Apply `hConv` to `f ≡ 1`, `yex = id`, `x = 1`, with
     `Y n m := M.glmConstOneIterate (1/n) m` and the stage choice
     above. Extract both diagonal limits:
     * `Y n n → u'` (already used in cycle 096).
     * `Y_int n → (fun _ => 1)` (NEW from the strengthening).
   * The stage equation gives
     `Y_int n i = (1/n) • (A𝟙)_i + (U *ᵥ Y n n) i`. Take limits:
     `1 = 0 + (U *ᵥ u')_i`, so `(U *ᵥ u') = 𝟙`.
   * Combined with `(V *ᵥ u') = u'` (cycle 096
     `convergence_witness_isVfixed`), `u'` is a preconsistency
     vector. The bridge to `u' = u` then needs a uniqueness step
     (option (c) of `u_prime_equals_u_bridge.md`) — but for sub-lemma
     C the closure may be possible without strict identification:
     subtract per-`k` `V^k *ᵥ u' = u'` (since `V *ᵥ u' = u'`) and
     `U *ᵥ u' = 𝟙` reduces the Cesàro statement to the difference of
     limits being `u' - u`.
   * If `u' ≠ u` is admissible (i.e. multi-dim `ker(I-V)`), the
     statement of sub-lemma C may need to use `u'` rather than the
     `IsPreconsistent`'s `u`, OR a separate uniqueness lemma is
     needed.

2. **Sub-lemma D (`cesaro_inverse_I_minus_V`)** remains the other
   blocker for `thm:514A` — multi-cycle mean-ergodic infrastructure.
   Independent of cycle 098's strengthening.

3. The `LinearMap.orthogonal_range_eq_ker_adjoint` factoring (cycle
   097's "Suggested next approach" item 4) was deferred this cycle
   because Priority 1 succeeded. Worth picking up as a low-risk side
   refactor in any future cycle.
