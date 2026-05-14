# Cycle 214 Results

## Worked on

P1 — `RKTableau.compose_isRKOneStep_iff` (forward direction + iff
packaging), the second half of the **Gap A** bridge in
`.prover-state/issues/compose_isRKOneStep_iff_scoping.md`. Closes
the path-to-`thm:382A` Gap A in full. Added to
`OpenMath/Chapter3/Section381.lean` namespace
`OpenMath.Chapter3.Section312.RKTableau`, immediately after cycle
213's `compose_of_isRKOneStep`.

P2 — `example` non-vacuity demonstrating the `.mp` direction on
the cycle 213 `paddedEuler.compose paddedEuler` witness — extracts
an intermediate value `y_mid` from the known composite output
`(y₀ + H • f y₀) + H • f (y₀ + H • f y₀)`. Lives in the
`Section381` namespace right after the cycle 213 example.

P3 stretch — Skipped (the iff + non-vacuity landed within budget
but the scoping doc for `thm:382A` via the (382g) form is folded
into the Cycle 214 update appended to
`.prover-state/issues/compose_isRKOneStep_iff_scoping.md` rather
than a separate file, since the algorithmic structure is already
captured in the existing `thm_382A_path.md`.)

## Approach

Mirror cycle 213's reverse-direction body shape, substituting
**projections** for `Fin.append`:

- Destructure `(M₁.compose M₂).IsRKOneStep f y₀ H y_final` into
  the composite stage tuple `Y_compose : Fin (s₁+s₂) → N` along
  with the per-stage equations `hY_compose_stage` and the output
  equation `hY_compose_out`.
- **Define** `y_mid := y₀ + H • ∑ i, M₁.b i • f (Y_compose
  (Fin.castAdd s₂ i))` algebraically in the `refine ⟨..., ?_,
  ?_⟩` (no Banach existence theorem needed).
- Witness `M₁.IsRKOneStep f y₀ H y_mid` using top projection
  `fun i₁ => Y_compose (Fin.castAdd s₂ i₁)`:
  - Stage equation: `hY_compose_stage (Fin.castAdd s₂ i₁)`
    +`Fin.sum_univ_add` + `simp only [compose_A_topLeft,
    compose_A_topRight, zero_smul, Finset.sum_const_zero,
    add_zero]` collapses the bottom-block half to zero.
  - Output equation: closes by `rfl` (the witness tuple makes the
    M₁-output formula evaluate to exactly the y_mid definition).
- Witness `M₂.IsRKOneStep f y_mid H y_final` using bottom
  projection `fun i₂ => Y_compose (Fin.natAdd s₁ i₂)`:
  - Stage equation: `hY_compose_stage (Fin.natAdd s₁ i₂)` +
    `Fin.sum_univ_add` + `simp only [compose_A_botLeft,
    compose_A_botRight]` + `rw [smul_add, ← add_assoc]` regroups
    the M₁-output block as `y_mid`; `exact hstage` closes by
    definitional collapse.
  - Output equation: same pattern, `simp only [compose_b_castAdd,
    compose_b_natAdd]` + `rw [smul_add, ← add_assoc]` + `exact
    hY_compose_out`.
- Reverse direction is a single `exact compose_of_isRKOneStep M₁
  M₂ h₁ h₂` (cycle 213).

## Result

**SUCCESS** — `compose_isRKOneStep_iff` shipped axiom-clean
([propext, Classical.choice, Quot.sound]) on the first
compilation attempt. Section381.lean warm rebuild 6.126s, sorry
count remains 0.

P2 example also shipped on first compilation. Cycle 213's
`compose_of_isRKOneStep` and cycle 212's
`Equivalent.setoidSigma` re-verified axiom-clean — no regressions.

### Critical observation — overrides cycle 212's scoping doc §4.2

The scoping doc anticipated the forward direction would need
`IsRKOneStep_exists` (cycle 205) + Lipschitz + smallness for
existential `y_mid` extraction. **It does not.** The forward
direction works by *projection*, not existence — given a
composite stage tuple `Y_compose`, the M₁ and M₂ stage tuples are
*already* `Y_compose ∘ Fin.castAdd s₂` and `Y_compose ∘ Fin.natAdd
s₁` (no need to existentially construct them via Banach); the
intermediate `y_mid` is defined algebraically from the M₁ block;
the M₂ block's stage and output equations close because the M₁
output formula appears verbatim inside the composite stage and
output equations after `Fin.sum_univ_add` + `compose_A_*` simp.

This means **no `[CompleteSpace N]`, no Lipschitz, no smallness
hypothesis** appears in the iff's signature — the iff is a purely
structural identity, matching cycle 213's `compose_of_isRKOneStep`
on the analytic-hypothesis front. The 35-LOC proof body is
strictly within budget.

## Faithfulness check

For each new theorem introduced this cycle:

- **`compose_isRKOneStep_iff`**: this is *infrastructure* for
  `thm:382A`, not a direct textbook entity (no
  `extraction/formalization_data/entities/*.json` row to consult).
  The structural identity (Butcher §382 (382b–e), p. 285) reads:
  one step of `M₁.compose M₂` factors as sequential `M₁` then
  `M₂` steps at the *same* step size `H` (no rescaling). Both
  directions in the iff capture exactly this identity. The Lean
  statement is **stronger than the textbook** in one direction —
  the textbook claims the algebraic identity only for *one*
  particular intermediate value `y_mid`; the iff additionally
  asserts existence of such `y_mid` from the composite output
  (forward) and packaging into the composite (reverse). This is
  the natural sufficient infrastructure for proving `thm:382A`
  per the (382g) reformulation path; documented in the docstring
  + the Cycle 214 update appended to
  `.prover-state/issues/compose_isRKOneStep_iff_scoping.md`.
- **Hypothesis strength check**: the textbook §382 narrative does
  not impose Lipschitz, smallness, or completeness for the (382b–e)
  identity (it is a purely algebraic substitution). Cycle 214's
  iff matches this — *zero* analytic hypotheses on `f`, `H`, or
  `N` beyond the normed-space typeclasses required for the
  `IsRKOneStep` predicate itself. The cycle 212 scoping doc's
  anticipation of Lipschitz/smallness in the forward direction
  was conservative; the actual proof needs none.
- **Tautology check**: conclusion is an iff, neither direction
  appears as a hypothesis. ✓
- **Identity check**: forward direction is ~30 LOC of substantive
  algebra; reverse direction is a 1-line invocation of cycle 213's
  `compose_of_isRKOneStep`. Neither side is a vacuous re-export. ✓
- **Definition smuggling check**: no new `def` or `structure`
  introduced this cycle. ✓

For the P2 `example`: type signature uses standard `IsRKOneStep`
and existential `y_mid`; closes by `.mp` of the iff applied to
the cycle 213 reverse-direction composition. No textbook entity
correspondence — pure non-vacuity.

## Dead ends

None. The proof body matched the strategy recipe (§C.1 of the
cycle 214 strategy) exactly — no tactic stalls, no Risk 1–7
escalations triggered. Specifically:

- **Risk 1** (simp does not close M₁ stage exactly): did not fire.
  The recommended simp set
  `[compose_A_topLeft, compose_A_topRight, zero_smul,
  Finset.sum_const_zero, add_zero]` collapsed the bottom-block
  contribution exactly as anticipated.
- **Risk 2** (`Fin.append_*` lemmas in forward direction): did
  not fire. They were correctly *omitted* from the simp set per
  the strategy recipe; the proof closes without them.
- **Risk 3** (`← add_assoc` parenthesisation mismatch): did not
  fire. The single `rw [smul_add, ← add_assoc]` was sufficient
  for both the M₂ stage and output equations.
- **Risk 4** (`IsRKOneStep` destructure shape): the
  `⟨Y_compose, hY_compose_stage, hY_compose_out⟩` pattern worked
  cleanly, matching cycle 213's destructure shape.
- **Risk 5** (`set` propagation issues): avoided — inlined
  anonymous lambdas as recommended.
- **Risk 6** (`.{u}` universe annotation): not needed (confirmed
  axiom-clean without).
- **Risk 7** (`0 • f _` collapse): handled by `zero_smul +
  Finset.sum_const_zero` in the simp set; fired without backup
  lemmas.

## Discovery

1. **The forward direction is algebraic, not analytic.** The cycle
   212 scoping doc anticipated the forward direction would need
   the full cycle 204/205 Banach machinery (uniqueness of stage
   fixed points + existence of one-step output). It does not —
   given a composite stage tuple `Y_compose`, you can *project*
   directly onto top and bottom blocks and define `y_mid`
   algebraically. The cycle 204/205 machinery is preserved unused
   in cycle 214; it will re-enter only for `thm:382A`'s proof
   itself, where `Equivalent`'s universal quantification over
   outputs forces using one-step uniqueness.

2. **`rfl` works for M₁'s output equation by definitional
   collapse.** When you define `y_mid := y₀ + H • ∑ i, M₁.b i • f
   (Y_compose (Fin.castAdd s₂ i))` and then witness M₁.IsRKOneStep
   with stage tuple `fun i₁ => Y_compose (Fin.castAdd s₂ i₁)`, the
   M₁ output equation `y_mid = y₀ + H • ∑ i, M₁.b i • f (Y i)`
   has RHS that β-reduces to *exactly* the y_mid definition. So
   `refine ⟨..., ?_, rfl⟩` works cleanly — no further tactic
   needed for the M₁ output side.

3. **`exact hstage` after `rw [smul_add, ← add_assoc]` closes by
   definitional unfolding of `y_mid`.** Once the M₁-output block
   `(y₀ + H • ∑ j₁, M₁.b j₁ • f (Y_compose (Fin.castAdd s₂ j₁)))`
   is left-grouped, Lean recognises it as syntactically identical
   to the `y_mid` introduced in the outer `refine ⟨_, ?_, ?_⟩`,
   and `exact hstage` (or `exact hY_compose_out`) closes the M₂
   stage/output goals without further tactics.

4. **The iff packaging is cheap once both directions exist.**
   `refine ⟨forward, reverse⟩` with the reverse direction being a
   one-line `compose_of_isRKOneStep` call adds zero meaningful
   LOC; cycle 213's `compose_of_isRKOneStep` lives standalone and
   is *also* the reverse direction of `compose_isRKOneStep_iff`.

## Suggested next approach

**Cycle 215 P1**: pursue `thm:382A` via the (382g) reformulation
per `.prover-state/issues/thm_382A_path.md` and the Cycle 214
update in `compose_isRKOneStep_iff_scoping.md`:

```
theorem compose_equivalent_compose
    (M₁ M̂₁ : RKTableau s₁) (M₂ M̂₂ : RKTableau s₂)
    (hEq₁ : M₁.Equivalent M̂₁) (hEq₂ : M₂.Equivalent M̂₂) :
    (M₁.compose M₂).Equivalent (M̂₁.compose M̂₂)
```

This is the (382g) form of thm:382A — avoids Gap B (the Σ-typed
quotient packaging, which would require building a `composeQ`
lift on top of cycle 212's `setoidSigma`). The proof structure:

1. Unpack `hEq₁` and `hEq₂` (each gives a threshold + Lipschitz
   gate yielding output uniqueness).
2. Construct the composite smallness threshold (minimum of three
   terms: `hEq₁`'s threshold, `hEq₂`'s threshold, and a fresh
   `H₀ := 1/(2·(L·(C₁+C₂)+1))` floor for the composite tableau's
   row sums).
3. For a `(M₁.compose M₂).IsRKOneStep f y₀ H y₁` hypothesis at
   small `H`: apply cycle 214's `compose_isRKOneStep_iff.mp` to
   extract `y_mid` and the M₁/M₂ steps.
4. Use cycle 205's `IsRKOneStep_exists` on `M̂₁` at `(f, y₀, H)`
   small to obtain `ŷ_mid` with `M̂₁.IsRKOneStep f y₀ H ŷ_mid`;
   `hEq₁` then forces `y_mid = ŷ_mid`.
5. Similarly via `M̂₂` and `hEq₂`: get `ŷ_final` from
   `M̂₂.IsRKOneStep f ŷ_mid H ŷ_final` with `y_final = ŷ_final`.
6. Re-pack via `compose_of_isRKOneStep` (cycle 213) into
   `(M̂₁.compose M̂₂).IsRKOneStep f y₀ H y_final`.

Estimated 60–100 LOC across cycle 215 (algebraic half) and cycle
216 (smallness threshold wiring). Note: this proves a fixed-stage
form `s₁ = s₁` and `s₂ = s₂` — the Σ-typed heterogeneous form is
a separate, downstream concern.

**Alternative cycle 215 stretch**: tighten the cycle 214 iff's
docstring with a concrete Butcher equation cross-reference (e.g.
literally reproduce equations (382b)–(382e) from page 285 as a
comment block) — purely documentation, no Lean changes. Skip if
cycle 215 P1 lands in full.
