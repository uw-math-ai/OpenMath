# Cycle 341 Results

## Worked on

`def:422B` Phase D pre-infrastructure (per strategy §B): τ-additivity
of `elementaryWeightQ_phi` under the §383 quotient group. This is
load-bearing infrastructure for cycle 342's Phase D.1 closed-form
`η(τ)` base-case solver. All four priorities P0+P1+P2+P3 shipped,
plus P4's three non-vacuity examples.

## Approach

Followed the strategy §B priority order verbatim. Sorry-first wasn't
needed — the recipes were concrete enough to write proofs directly.

**P0 — `RKTableau.derivativeWeightWithSrc_vertex`:** Two-line proof
following the strategy's recipe — `show
derivativeWeightWithSrcProd M₁ i [] = 1; rfl`. The empty-list base
case of the mutual definition is definitional.

**P1 — `elementaryWeightQ_phi_mul_vertex`:** Followed the strategy's
binary `Quotient.inductionOn` pattern (with `with | _ p => ?_` syntax,
then `obtain` to destructure the sigma representatives). After
`elementaryWeightQ_phi_composeQ_phi_mk`-rewrite, `congr 1` was
expected to peel the matching `M₁`-summand and leave the bottom-block
sum identity. **Surprise:** `congr 1` closed BOTH subgoals by
reflexivity. The bottom-block sum `Σ i, M₂.b i ·
derivativeWeightWithSrc M₁ i τ` and the RHS's
`elementaryWeightQ_phi ⟦⟨s₂, M₂⟩⟧ τ = M₂.elementaryWeight τ` are
definitionally equal because `derivativeWeightWithSrc M₁ i τ` and
`derivativeWeight i τ` both reduce to `1` via their respective
empty-list base cases. So P0 is independent infrastructure, NOT
invoked in P1's proof. P0 remains a standalone named theorem for
downstream consumers (cycle 342+).

**P2 — `elementaryWeightQ_phi_inv_vertex`:** Followed the strategy's
recipe. Applied `mul_inv_cancel η_q : η_q * η_q⁻¹ = 1`, then
`elementaryWeightQ_phi_eq_of_eq` at τ, then P1, then the definitional
unfold `(1 : Q) = Quotient.mk _ ⟨0, RKTableau.id⟩` (via `rfl`-`have`),
then `elementaryWeightQ_phi_id`, then `linarith`.

**P3 — `elementaryWeightQ_phi_zpow_vertex`:** Internal `∀ m : ℕ`
helper via induction (zero case: `pow_zero` + `(1 : Q)` unfold +
`elementaryWeightQ_phi_id` + `simp`; succ case: `pow_succ` + P1 +
`push_cast; ring`), then `cases n with` on `Int` constructors. The
`ofNat` branch needed `Int.ofNat_eq_natCast` (the
`Int.ofNat_eq_coe` deprecation warning that initially appeared was
fixed by switching to `_natCast`). The `negSucc` branch: `zpow_negSucc`
+ `elementaryWeightQ_phi_inv_vertex` + `h_nat (m + 1)` + `push_cast;
ring`.

**P4 — Non-vacuity examples:** Three one-line `rw` + arithmetic
closures. (a) `Φ_{D·D}(τ) = 2`: `rw [P1, D_element_elementaryWeight_vertex]; norm_num`.
(b) `Φ_{D⁻¹}(τ) = -1`: `rw [P2, D_element_elementaryWeight_vertex]`.
(c) `Φ_{D³}(τ) = 3`: `rw [P3, D_element_elementaryWeight_vertex]; norm_num`.

## Result

**SUCCESS** — all four priorities shipped axiom-clean.

* `lake env lean OpenMath/Chapter4/Section422.lean` — exit 0, no errors, no warnings.
* `lake env lean OpenMath/Chapter4.lean` (aggregator) — exit 0, no errors.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` — 0.
* `#print axioms` on all 4 new public theorems: `[propext,
  Classical.choice, Quot.sound]` only.
* Section422.lean: 350 → 484 LOC (+134 LOC; strategy budgeted
  80–120, slight over due to docstring expansion on the section
  header and per-theorem rationale).

## Faithfulness check

For each new `theorem` introduced this cycle:

**`RKTableau.derivativeWeightWithSrc_vertex` (P0)**

- Entity ID: no Butcher entity (project-internal helper for §383
  quotient infrastructure, analog of cycle 187's
  `RKTableau.derivativeWeight_vertex`).
- Lean statement: `M₂.derivativeWeightWithSrc M₁ i RootedTree.vertex = 1`.
- Captures: definitional consequence of the mutual definition's
  empty-list base case at `Section381.lean:2690`. Real mathematical
  work (a named fact about a function's value at a specific input).
  Not a tautology — the conclusion `… = 1` does not appear among
  the hypotheses. Not just `exact h` — the proof is a definitional
  unfold via `show … = 1; rfl`.

**`elementaryWeightQ_phi_mul_vertex` (P1)**

- Entity ID: no direct Butcher entity (project-internal Phase D
  pre-infrastructure for `def:422B`).
- Lean statement: `Φ_{η·η'}(τ) = Φ_η(τ) + Φ_{η'}(τ)` for all
  `η, η' : Quotient PhiEquivalent.setoidSigma`. This is the
  τ-restriction of the general fact that Butcher's `Φ` is a group
  homomorphism on a particular sub-Hopf algebra (the order-1 piece).
- Captures: the additivity-at-τ identity that makes the (422a)
  equation linear in `η(τ)`. Real mathematical work (combines the
  representative-level decomposition `compose_elementaryWeight_decomp`
  with the τ-collapse of bottom-block sums). Not a tautology;
  the proof invokes nontrivial infrastructure (`composeQ_phi_mk`,
  `elementaryWeightQ_phi_composeQ_phi_mk`).

**`elementaryWeightQ_phi_inv_vertex` (P2)**

- Entity ID: no direct Butcher entity (Phase D pre-infrastructure).
- Lean statement: `Φ_{η⁻¹}(τ) = -Φ_η(τ)`. Corollary of P1 + the
  identity-class elementary weight `0` at τ.
- Captures: the inversion identity needed for Butcher's
  `η^{-i}` factors in (422a). Real mathematical work — `linarith`
  closes a non-trivial linear combination after the rewrites.
  Not a tautology.

**`elementaryWeightQ_phi_zpow_vertex` (P3)**

- Entity ID: no direct Butcher entity (Phase D pre-infrastructure).
- Lean statement: `Φ_{η^n}(τ) = (n : ℝ) · Φ_η(τ)` for all `n : ℤ`.
  The closed-form scaling law that gives Butcher's `η^{-i}(τ) = -i ·
  η(τ)` factor in (422a) at `u = τ`.
- Captures: the full integer-power scaling needed to make Eq422a
  at `u = τ` linear in `η(τ)`. Real mathematical work — combines
  positive-integer induction (via `pow_succ` + P1) with the
  negative branch (via `zpow_negSucc` + P2). Not a tautology.

No `def` introduced this cycle, no new `structure`/`class` introduced.
All four new theorems pass:
* TAUTOLOGY CHECK — no conclusion appears verbatim as a hypothesis.
* IDENTITY CHECK — none are `exact h` re-exports; all do real
  rewriting/induction work.
* DEFINITION SMUGGLING CHECK — N/A (no new definitions).
* HYPOTHESIS STRENGTH CHECK — P1/P2/P3 are stated for *arbitrary*
  `η_q : Q` with no `IsPreconsistent`/`IsStable` hypotheses (the
  cycle 340 design discipline: predicates/lemmas don't carry
  existence hypotheses).

## Dead ends

None — proofs followed the strategy recipes nearly verbatim. The
only friction:

1. **Initial `congr 1` post-fluff:** wrote 4 lines (`rw
   [elementaryWeightQ_phi_mk, RKTableau.elementaryWeight_eq]; refine
   Finset.sum_congr rfl ?_; intro i _; rw
   [derivativeWeightWithSrc_vertex, derivativeWeight_vertex]`) after
   `congr 1` per the strategy's recipe step 5–8. Build flagged "No
   goals to be solved" on the first follow-up line — `congr 1`
   already closed everything by reflexivity. Removed the dead lines.

2. **Deprecation warning:** `Int.ofNat_eq_coe` is deprecated in
   favor of `Int.ofNat_eq_natCast`. Switched. (Strategy's recipe
   suggested `zpow_natCast` and `Int.cast_natCast` / `Int.cast_negSucc`
   abstractly; the actual hammer that worked was the unfold to nat
   coercion via `Int.ofNat_eq_natCast`.)

3. **Axiom check requires `lake build` not `lake env lean`:** the
   `#print axioms` invocations on freshly-edited declarations fail
   if oleans aren't rebuilt. Initial attempt with `lake env lean
   /tmp/check_axioms_cycle341.lean` reported "Unknown constant" for
   all four new names because the existing olean was older than the
   source file. Resolved by running `lake build
   OpenMath.Chapter4.Section422` once to regenerate the olean
   (8034/8034 build steps, 229s on this target alone via replay).
   Worth remembering: the axiom-check workflow needs an olean for
   the changed file, not just an in-memory compile.

## Discovery

* **Definitional collapse of bottom-block sum at τ:** the bottom-block
  sum `Σ i, M₂.b i · derivativeWeightWithSrc M₁ i τ` is
  definitionally equal to `M₂.elementaryWeight τ` — both reduce
  pointwise to `Σ i, M₂.b i · 1`. So P1's `congr 1` step closes
  the entire identity via reflexivity, without needing to invoke
  P0 or `derivativeWeight_vertex`. This means P0 is independent
  infrastructure (still useful for downstream consumers and as a
  named API entry), but `Quotient`-class statements at τ may be
  simpler than expected in future cycles. **Lesson for cycle 342:**
  if the Phase D.1 base case at `u = τ` collapses similarly, the
  `η(τ)` solver may be shorter than the scoping doc's 50–80 LOC
  estimate.

* **`Quotient.inductionOn` with `with | _ p => ?_` syntax:** the
  strategy's binary form (consecutive single-argument inductions)
  works cleanly; no need to fall back to `Quotient.inductionOn₂`.

* **`congr 1` is more aggressive than expected at definitional
  level:** when both sides of a `congr 1` peel reduce by `rfl`,
  it closes ALL subgoals, not just the surface congruence. Useful
  to know — future cycles should write `congr 1; <rest>` with the
  understanding that `<rest>` may be unnecessary if the residual
  goals are definitionally trivial.

* **`lake build OpenMath.Chapter4.Section422` end-to-end time:**
  229s on the §422-target replay path (with 8033 other targets in
  cache). This is fast for an axiom-check workflow; ~4 min round
  trip from edit → axiom verification.

## Suggested next approach

**Cycle 342 — Phase D.1 closed-form `η(τ)` base-case solver** per
`def_422B_path.md` Phase D.1 row. With cycle 341's τ-additivity
lemmas (P1/P2/P3) in hand, Eq422a at `u = τ` collapses to a linear
equation in `η(τ)`:

```
0 − Σᵢ M.α i.succ · (-(i+1) · η(τ))
  − Σᵢ M.β i · ((-i · η(τ)) + 1) = 0
```

(The `+ 1` on the β-side comes from cycle 337's
`D_element_elementaryWeight_vertex = 1` plus P1 additivity applied
to `η_q ^ (-i) * D_element`.) Ring this into a closed form for
`η(τ)`:

```
(Σᵢ (i+1) · M.α i.succ + Σᵢ i · M.β i) · η(τ) = Σᵢ M.β i
```

(modulo sign convention). Stability + preconsistency guarantee the
coefficient is non-zero (cycle 178's
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent`, transported to
the `Σ i · αᵢ` form).

**Concrete sub-steps for cycle 342:**

1. (Optional, scaling-dependent) Define an `Eq422aAt M η_q u` per-tree
   predicate or extract `Eq422a_at_tree : Eq422a M η_q → ∀ u, …`
   to make the `u = τ` slice statable as its own theorem.
2. Specialize Eq422a body at `u = RootedTree.vertex`: rewrite via
   P3 on the α-side (`Φ_{η_q ^ (-(i+1))}(τ) = -(i+1) · η(τ)`) and
   P1+P3 on the β-side (`Φ_{η_q ^ (-i) · D}(τ) = -i · η(τ) + 1`).
3. Ring-normalize to extract the linear coefficient of `η(τ)`.
4. State and prove `eta_tau_closed_form : (coefficient) ≠ 0 →
   η(τ) = (constant) / (coefficient)`.
5. Bridge the `≠ 0` hypothesis to `M.IsPreconsistent ∧ M.IsStable`
   via cycle 178's `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`
   (potentially needs a transport lemma from `ρPoly'_eval_one =
   Σ i · αᵢ` to the actual coefficient shape).

**LOC budget:** the cycle 340 task results estimated Phase D.1 at
50–80 LOC; cycle 341's discovery that `congr 1` may collapse more
than expected at τ-level might reduce this further. If the Phase D.1
ship spills, decompose: ship the Eq422a-at-τ specialization first,
defer the stability bridge to a separate cycle.

**Anti-pattern reminders for cycle 342 (per cycle 341 strategy §E):**

* Do NOT attempt Phase D.2 (well-founded recursion) or D.3 (inductive
  step) in cycle 342 — those are dedicated future cycles.
* Do NOT raise `maxHeartbeats`. If Phase D.1's ring step stalls,
  decompose into a per-side specialization.
* Do NOT introduce sorries — better to ship the τ-slice specialization
  alone than the full closed-form with a stability sorry.
