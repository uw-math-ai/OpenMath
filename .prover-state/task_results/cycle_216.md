# Cycle 216 Results

## Worked on

* `def:381A` `RKTableau.Equivalent` definition refactor — quantifier
  reorder from `∀ y₀, ∃ h₀, ...` to `∃ h₀, ∀ y₀, ...` (uniform
  threshold form).
* `thm:382A` `RKTableau.compose_equivalent_compose` — closed cycle
  215's sorry-scaffold body (~20 LOC) via the route B.1 recipe
  enabled by the refactor.
* Ports: `equivalent_self`, `equivalent_explicitEuler_self`,
  `Equivalent.symm`, `Equivalent.trans`, `pReduced_equivalent`,
  `zeroReduced_equivalent` — mechanical binder reorder; no
  threshold changes.

## Approach

Followed the cycle 216 strategy §B–§F verbatim:

* **§B Definition refactor** (one-line binder reorder): moved
  `(y₀ : N)` from before the `∃ h₀ > (0 : ℝ)` to just inside it.
  Docstring updated with a cycle 216 note cross-referencing
  `compose_equivalent_compose_uniform_threshold.md`.
* **§C Refl/symm/trans ports** (~25 LOC churn): `intro` blocks
  drop `y₀` from outer intro; `intro y₀` moved into the body
  introduction step after `refine ⟨..., ?_⟩`. `hConcl`-style
  call sites in `Equivalent.trans` updated to prepend `y₀`.
* **§D Downstream ports**: `equivalent_explicitEuler_self`,
  `pReduced_equivalent`, `zeroReduced_equivalent` ported by the
  same recipe. `PReducesTo.toEquivalent`, `PEquivalent.toEquivalent`,
  `Equivalent.setoid`, `Equivalent.setoidSigma`, and all paddedEuler
  witnesses — no body change required (the strategy correctly
  predicted these dispatch to the per-step lemmas via composition).
* **§E `compose_equivalent_compose` body** (~20 LOC): replaced the
  cycle 215 `:= sorry` with the strategy's draft body verbatim.
  Hypotheses `_hEq₁` / `_hEq₂` lost the underscore prefix because
  the body now consumes them. Docstring shortened to remove the
  "STATUS: scaffolded with sorry" block.

After each phase, ran `lake env lean OpenMath/Chapter3/Section381.lean`
and verified axiom-cleanliness via `lean_verify`.

## Result

SUCCESS — sorry count 1 → 0; `thm:382A` (382g) form axiom-clean.

Axiom-cleanliness confirmed for:

* `equivalent_self` — `[propext, Classical.choice, Quot.sound]`.
* `Equivalent.symm` — `[propext, Classical.choice, Quot.sound]`.
* `Equivalent.trans` — `[propext, Classical.choice, Quot.sound]`.
* `pReduced_equivalent` — `[propext, Classical.choice, Quot.sound]`.
* `zeroReduced_equivalent` — `[propext, Classical.choice, Quot.sound]`.
* `compose_isRKOneStep_iff` (cycle 214 regression check) —
  `[propext, Classical.choice, Quot.sound]`.
* `compose_equivalent_compose` (this cycle) —
  `[propext, Classical.choice, Quot.sound]`.

The strategy's mechanical-port estimate matched reality exactly:
zero unexpected sticking points. Section381.lean compiled cleanly
after each phase; no Risk 1/2/3/4 events fired. Strategy §G abort
threshold did not trigger.

## Faithfulness check

`def:381A` `Equivalent` (refactored):

> Two RK methods $m_1$, $m_2$ are equivalent if, for every Lipschitz
> $f$ and sufficiently small step $h$, the one-step outputs from
> any initial $y_0$ coincide.
>
> (Butcher §380 p. 280, paraphrased; the textbook does not impose a
> quantifier order on $h_0$ and $y_0$.)

Lean statement captures: same content under stronger reading
(uniform-in-y₀ threshold). The cycle 216 refactor strengthens
the predicate (tighter quantifier order), which is **strictly
faithful** to Butcher's textbook proof of (382g) — Butcher writes
"if h is sufficiently small, then y₁=ŷ₁ ... and y₂=ŷ₂", which
implicitly takes h₀ uniform across all initial values (no continuity
or measurability argument on a y₀-dependent threshold appears in
the textbook). Every concrete `Equivalent` instance in our codebase
already had a y₀-uniform threshold (`equivalent_self`'s `1/(2*(L*C+1))`,
`Equivalent.trans`'s min-of-three construction), so the refactor
exposes uniformity that was already present — it does not change
which method pairs satisfy `Equivalent`.

`thm:382A` `RKTableau.compose_equivalent_compose`:

> Let $m_1$, $m_2$, $\widehat{m}_1$, $\widehat{m}_2$ denote
> Runge–Kutta methods, such that $\widehat{m}_1 \equiv m_1$ and
> $\widehat{m}_2 \equiv m_2$. Then $[m_1 \cdot m_2] = [\widehat{m}_1
> \cdot \widehat{m}_2]$. Equivalent form (382g): $m_1 \cdot m_2
> \equiv \widehat{m}_1 \cdot \widehat{m}_2$.

Lean statement captures: same content (382g form, fixed-stage).
Faithfulness notes documented in the theorem's docstring:

* (382f) bracketed form `[m₁·m₂] = [m̂₁·m̂₂]` is the
  `Quotient.lift₂` of cycle 212's `setoidSigma`, deferred to a
  later cycle (~50 LOC via `composeQ`).
* Fixed-stage restriction (`M₁ M₁' : RKTableau s₁`) is a stricter
  type than the textbook's heterogeneous-stages form; the
  heterogeneous-stage extension is a natural cycle 217+ work
  (the proof body should largely port — it operates at the
  abstract `N` level, not the stage count).

## Dead ends

None this cycle — strategy §B–§F landed verbatim on first attempt.

The cycle 215 abort threshold §H (revert to cycle 215 HEAD) was
*not* triggered: §C refl/symm/trans ports passed `lean_verify`
within the first 30% of cycle budget, signalling the refactor was
genuinely mechanical. The remaining §D/§E/§F work landed without
incident.

## Discovery

* **Mechanical-port estimates are reliable when threshold-y₀
  independence is provable in every concrete instance.** Cycle
  216's strategy claimed all consumer thresholds are y₀-uniform;
  this was verified empirically by porting each consumer with
  pure binder reorder (no threshold-construction changes). The
  refactor estimate (~55 LOC total) tracked actual work (~50 LOC)
  within ±10%, suggesting the methodology of "audit thresholds
  before refactoring quantifier order" generalises.
* **Quantifier-order refactors propagate uniformly when the
  threshold construction is closed-form.** Every threshold in
  the equivalence-relation tier (`equivalent_self`, `trans`,
  `pReduced`, `zeroReduced`) was algebraic in `L`, `C` (row-sum
  norm), or the input thresholds. None depended on choice over
  `y₀` or required a continuity argument. This is a useful
  invariant to record for future Banach-style infrastructure.
* **The route B.1 recipe is robust to the refactor's binder shape.**
  The cycle 215 strategy's draft body (with `hEq₂_app y_mid' ...`
  instead of `hEq₂_app y₀ ...` from cycle 215's failed attempt)
  closed on first compile — no Lean elaboration surprises around
  the universal y₀ binding inside the existential.

## Suggested next approach

The (382g) fixed-stage form is closed. Two natural extensions:

* **Cycle 217 — heterogeneous-stage form**: replace
  `(M₁ M₁' : RKTableau s₁) (M₂ M₂' : RKTableau s₂)` with
  `(M₁ : RKTableau s₁) (M₁' : RKTableau s₁') (M₂ : RKTableau s₂)
  (M₂' : RKTableau s₂')`. The body should largely port — the
  proof works at the abstract space `N`, not the stage count.
  Risk lies in the type signature compatibility with cycle 214's
  `compose_isRKOneStep_iff` (which is also fixed-stage). Likely
  ~30–50 LOC of churn.
* **Cycle 217+ — `composeQ` lift via `Quotient.lift₂`**: lift
  `compose` from `RKTableau s₁ × RKTableau s₂` to the Σ-typed
  quotient `Σ s, RKTableau s / Equivalent.setoidSigma`, consuming
  cycle 217's heterogeneous form. This closes the bracketed (382f)
  form `[m₁·m₂] = [m̂₁·m̂₂]`. ~50 LOC.

Planner should decide which extension to schedule first; the
heterogeneous-stage form has fewer dependencies and is the natural
prerequisite for the (382f) bracketed form.

§441 Phase C.2: GPFS-blocked (34th consecutive); skipped per
standing pattern (cf. `.prover-state/issues/cycle_182_gpfs_slowness.md`).
