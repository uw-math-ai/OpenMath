# Cycle 208 Results

## Worked on

§380 def:381F → def:381A bridge (cycle-208 PRIMARY P1) and two
`paddedEuler` non-vacuity witnesses (P2), plus the bundled umbrella
corollary `PEquivalent.toEquivalent_and_toPhiEquivalent` (stretch P3).
Closes the second of four iff-directions of `thm:381H` (after cycle
187's `PEquivalent.toPhiEquivalent`), leaving the remaining two
(`Equivalent → PEquivalent` and `PhiEquivalent → PEquivalent`) blocked
on `thm:381G` per
`.prover-state/issues/thm_381H_deferred.md`.

All four new theorems land in `OpenMath/Chapter3/Section381.lean`:

* `OpenMath.Chapter3.Section312.RKTableau.PEquivalent.toEquivalent`
  (P1, ~10 LOC incl. docstring, after `PReducesTo.toEquivalent`).
* `OpenMath.Chapter3.Section312.RKTableau.PEquivalent.toEquivalent_and_toPhiEquivalent`
  (P3 stretch corollary, ~6 LOC, immediately after P1).
* `OpenMath.Chapter3.Section381.paddedEuler_equivalent_pReduced`
  (P2 step-constructor witness, ~5 LOC).
* `OpenMath.Chapter3.Section381.paddedEuler_equivalent_zeroReduced`
  (P2 zeroStep-constructor witness, ~5 LOC).

## Approach

### P1: `PEquivalent.toEquivalent`

`PEquivalent M M'` unfolds to `∃ sBar Mbar, PReducesTo M Mbar ∧
PReducesTo M' Mbar` (Section381.lean:429). After `obtain` to extract
both reductions, the composition is mechanical: cycle 207's
`PReducesTo.toEquivalent` (Section381.lean:2121) lifts each leg to
`Equivalent`, then cycle 206's `Equivalent.trans` combined with cycle
204's `Equivalent.symm` closes the diamond `M ↔ Mbar ↔ M'`. Universe
annotation `.{u}` applied per cycle 204 discovery: `Equivalent.{u}` is
universe-polymorphic and `symm`/`trans` require shared `.{u}` to bind
universes across multiple references in the signature.

### P2: paddedEuler witnesses

Both are one-line bodies composing existing P-reductions with cycle
207's `PReducesTo.toEquivalent`:
* `paddedEuler_pReducesTo_pReduced.toEquivalent` (cycle 186 → cycle 207).
* `paddedEuler_pReducesTo_zeroReduced.toEquivalent` (cycle 188 → cycle 207).

Both ride dot-notation through the `RKTableau` namespace alias
established by Section381's `open OpenMath.Chapter3.Section312` block
on line 2136, mirroring the existing `paddedEuler_equivalent_self`
ergonomics on Section381.lean:2241.

### P3: Umbrella corollary

Pure ergonomics: `⟨h.toEquivalent, h.toPhiEquivalent⟩` returns the two
closed directions of `thm:381H` packaged together. Universe
annotation `.{u}` applied on the `Equivalent` conjunct.

## Result

**SUCCESS** — all four theorems verify axiom-clean
(`[propext, Classical.choice, Quot.sound]`), file compiles with no
new warnings beyond the two pre-existing unused-variable linter
notices (Section381.lean:577 and 2245, both on `heq` patterns
unrelated to cycle 208). Sorry count: 0 → 0. Warm rebuild observed
~5–10s.

### Universe-inference correction during cycle execution

The strategy's canonical body
```lean
exact Equivalent.trans hM.toEquivalent hM'.toEquivalent.symm
```
**did not elaborate** — Lean reports
`Invalid field 'symm': The environment does not contain 'Function.symm'`,
because `hM'.toEquivalent` has the unfolded ∀-form
(`∀ (f : ?m → ?m) (L : NNReal), ...`) rather than a structure named
`Equivalent`, so dot-notation `.symm` resolves against the inferred
`Function`/`(.→.)` namespace rather than `Equivalent`. Applied the
strategy's documented Risk-1 fallback verbatim:
```lean
exact Equivalent.trans hM.toEquivalent
  (Equivalent.symm hM'.toEquivalent)
```
This elaborates cleanly — the explicit `Equivalent.symm` reference
constrains the universe parameter via `Equivalent.symm.{u}`'s
signature, which is what dot-notation lookup couldn't achieve. The
fallback was anticipated; total cost was one failed compile + one
edit. No deeper redesign required.

## Faithfulness check

### `PEquivalent.toEquivalent`

* Entity ID: implicit consequence of `thm:381H` (Butcher §380, p. 304):
  > "Two methods M, M' are def:381A-equivalent iff they are
  > def:381F-equivalent iff they are def:381B-equivalent."
* Lean statement captures: **same content** — the def:381F → def:381A
  direction exactly, via the diamond `M → Mbar ← M'` of P-reductions
  composed through `Equivalent`'s equivalence-relation structure
  (refl/symm/trans shipped in cycles 203/204/206).
* Hypothesis strength: no extras. Only `PEquivalent M M'` is required;
  the `[CompleteSpace N]` is built into `Equivalent`'s definition
  itself (cycle 206) and is a no-op at every concrete normed-space
  call site.

### `PEquivalent.toEquivalent_and_toPhiEquivalent`

* Entity ID: pure ergonomic packaging of the two closed `thm:381H`
  directions; no new content.
* Lean statement captures: **same content** — anti-symmetric conjunction
  of `h.toEquivalent` (cycle 208) and `h.toPhiEquivalent` (cycle 187).
* Hypothesis strength: identical to the constituent theorems.

### `paddedEuler_equivalent_pReduced`, `paddedEuler_equivalent_zeroReduced`

* Entity ID: non-vacuity witnesses, no textbook entity attached.
* Lean statement captures: **same content** as the underlying
  `paddedEuler_pReducesTo_pReduced` (cycle 186) and
  `paddedEuler_pReducesTo_zeroReduced` (cycle 188), lifted through
  cycle 207's `PReducesTo.toEquivalent` bridge.
* Hypothesis strength: none (closed-form witnesses on the canonical
  2-stage padded explicit-Euler tableau).

## Dead ends

### §441 Phase C.2 — 28th-consecutive GPFS skip

Strategy §A directed skipping `lake env lean
OpenMath/Chapter4/Section441.lean` per the 27-cycle pattern of GPFS
olean-loading timeouts (cycles 182–207). Did not run the smoke test.
See `.prover-state/issues/cycle_182_gpfs_slowness.md` and
`.prover-state/issues/phantom_commit_verdict_pattern.md` — loop-
maintainer territory, not worker-resolvable.

### `.symm` dot-notation failure

Documented under §Result above. The strategy's first-choice proof
body was rejected because `Equivalent` is a `def` returning ∀-form
`Prop`, not a structure exporting `.symm`. The pre-anticipated
fallback succeeded without redesign.

## Discovery

1. **`.symm` dot-notation discipline for `def`-shaped equivalences.**
   `Equivalent`'s definition is `∀ {N} [...] (f) (L) ..., ∃ h₀ > 0, ...`
   — a ∀-form `Prop`, not a structure. Dot-notation `h.symm` therefore
   looks up `symm` in the **head normal form** of `h`'s type, which is
   `Function`/`(.→.)` — and produces the bogus
   `Function.symm`-not-found error rather than finding
   `Equivalent.symm`. Workaround: write `Equivalent.symm h` (fully
   qualified function application) instead of `h.symm` (dot-notation).
   Same applies to `Equivalent.trans` if a downstream consumer ever
   tries `h₁.trans h₂` on `Equivalent` arguments. **Pre-emptively
   apply** in future `Equivalent`-chain proofs. This is **not** a
   universe-inference issue per se — it's a structural mismatch
   between dot-notation and ∀-defined predicates. Cycle 204's
   universe-annotation discovery (`.{u}` on signatures + `@Equivalent`
   in goals) remains separately valid for binding universes across
   theorem signatures.

2. **`paddedEuler_pReducesTo_*` namespace bridging works through the
   Section381 `open OpenMath.Chapter3.Section312` block.** Section381
   begins with `open OpenMath.Chapter3.Section310
   OpenMath.Chapter3.Section312` (line 2136), so dot-notation
   `paddedEuler_pReducesTo_pReduced.toEquivalent` resolves
   `.toEquivalent` against `RKTableau.PReducesTo.toEquivalent` cleanly
   — no explicit `open RKTableau` or fully qualified prefix needed.
   The witness theorems read identically to the strategy's proposed
   text; no namespace alias required.

3. **Two-of-four-directions umbrella corollary is cheap.** The
   `PEquivalent.toEquivalent_and_toPhiEquivalent` packaging compiles
   in ~5 LOC and serves as a single hand-hold for downstream consumers
   wanting both equivalence-direction conclusions from a single
   P-equivalence hypothesis. When the remaining two directions become
   formalizable (post-`thm:381G`), this corollary will likely retire in
   favour of the full four-way iff scaffold.

## Suggested next approach

1. **§382 composition group (def:382A, thm:382A, etc.).** Cycle 207's
   task results suggested this as the next non-blocking expansion.
   Now that `thm:381H` has its 2 closeable directions shipped, §382
   is the natural progression for new entity work — separate cluster,
   separate planning cycle.

2. **Newman-style confluence for `PReducesTo` (multi-cycle).** Would
   unblock full `Equivalent.trans` without the
   irreducible-middle-hypothesis sidestep. Per
   `.prover-state/issues/p_reduction_confluence_gap.md`, this is 4–5
   cycles of infrastructure work. Useful if downstream needs require
   def:381E `reducedMethod` uniqueness; not required for cycle 208's
   bridge.

3. **`thm:381G` formalization (multi-cycle).** Would unblock the
   remaining two `thm:381H` directions
   (`Equivalent → PEquivalent` and `PhiEquivalent → PEquivalent`).
   Per cycle 199's recon, estimated 2–3 cycles of prerequisite work
   (thm:314A + subalgebra-of-elementary-weights infrastructure in
   ℝˢ). At that point the four-way iff scaffold can be re-introduced
   (sorry count 0 → 2, dropping to 0 across 2 cycles of closure).

4. **More `paddedEuler`-style non-vacuity witnesses for downstream
   §380 lemmas.** Cycle 208 added two; the existing pattern (witness
   per constructor path through cycle 207's bridge) is cheap and
   confirms each new theorem fires non-vacuously. Useful as cheap
   sanity-check filler when budget remains after a primary deliverable.

5. **`PReducesTo.toPhiEquivalent` already exists (Section381.lean:1577)
   — consider an `RKTableau.PReducesTo.toEquivalent_and_toPhiEquivalent`
   bundled bridge at the `PReducesTo` level**, paralleling the
   `PEquivalent` umbrella from this cycle. Pure ergonomics; ~5 LOC.
   Skip if no consumer wants it.
