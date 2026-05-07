# Cycle 185 Results

## Worked on

`def:381F` follow-up — `PEquivalent.trans_of_middle_not_pReducible`
(Priority 2 of the cycle 185 strategy). Phase C.2 of `lem:441A`
remained GPFS-blocked for the 5th consecutive cycle.

## Approach

### Priority 0 — GPFS health probe (per strategy)

Pre-flight: `ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[
]*[0-9]+ +D"` returned nothing — no zombie D-state processes from
prior sessions.

Smoke test: `time timeout 300 lake env lean
OpenMath/Chapter4/Section441.lean` (HEAD, unchanged since cycle 184).
**Timed out at exactly 300s** with near-zero CPU (0.272s user,
0.511s sys over 300s wall). EXIT=143. Per the strategy decision
tree:

> Times out at 300s OR exits non-zero: GPFS still degraded OR HEAD
> is broken. Skip Priority 1, go directly to Priority 2.

This is the **5th consecutive Section441 compile timeout** (cycles
182 × 2, 183, 184, 185). Sub-second CPU usage rules out HEAD being
broken — this is the same GPFS pathology described in
`cycle_182_gpfs_slowness.md`.

### Priority 2 — `def:381F` follow-up

Verified Section381.lean compiles healthy as a baseline: `lake env
lean OpenMath/Chapter3/Section381.lean` finished in 70s on the first
build, ~4s on subsequent rebuilds (cache-hit on the .olean
dependencies). Section441's GPFS pathology is specific to its larger
mathlib transitive load (`Mathlib.Analysis.*` heavy); Section381's
`Mathlib.Topology.MetricSpace.Lipschitz` import is light.

The strategy proposed `PEquivalent.trans_of_middle_irreducible` with
a strong `IsPIrreducible := ∀ {sBar} P, ¬IsPReducibleVia M P`
predicate. Inspection of the existing `PReducesTo.step` constructor
revealed a **latent soundness gap**:

* The docstring (`Section381.lean:386–392`) states "each non-trivial
  P-reduction strictly decreases the stage count (`sBar < s`)".
* But the `step` constructor (lines 393–401 HEAD) had no `sBar < s`
  hypothesis. The discrete partition (`sBar = s`, each stage in its
  own block) trivially satisfies `IsPReducibleVia` (vacuously, since
  every block is a singleton, so the row-sum-constancy condition
  reduces to `M.A i J = M.A i J`).
* So the strategy's strong `IsPIrreducible` predicate would never
  hold (every method admits the trivial discrete-partition step),
  and consequently the proposed `trans_of_middle_irreducible` had
  no non-vacuous instances.

Fix: tighten the `step` constructor with an `_hLt : sBar < s`
hypothesis, aligning the implementation with the existing docstring
promise. With this in place, `¬IsPReducible M` (which already
requires `sBar < s`) directly rules out the `step` constructor for
any reduction starting from `M`, and the lemma machinery falls into
place.

### Implementation

In `OpenMath/Chapter3/Section381.lean`:

1. **Tightened `PReducesTo.step`** (lines ~393–404 in current HEAD):
   added `(_hLt : sBar < s)` between the partition `P` and the
   row-sum-constancy witness `_h`. Updated the constructor's
   docstring to explain why non-triviality is required (the
   discrete-partition admissibility issue).

2. **Updated the existing `paddedEuler` example** (line ~530 in
   current HEAD): passed `(by decide)` for the new `1 < 2`
   hypothesis on `pairPartition : PPartition 2 1`.

3. **Added `eq_of_not_isPReducible_of_pReducesTo`** in the
   `OpenMath.Chapter3.Section312.RKTableau` namespace block. By case
   analysis on `PReducesTo M M'`: the `refl` case gives `s' = s` and
   `HEq M' M`; the `step P hLt hVia _` case extracts a witness
   `⟨sBar, hLt, P, hVia⟩ : M.IsPReducible`, contradicting `hIrr`.

4. **Added `PEquivalent.trans_of_middle_not_pReducible`** with arg
   order `(h₁₂) (h₂₃) (hIrr)` for dot notation. Proof: `refine`
   `⟨s₂, M₂, ?_, ?_⟩` first (so that `M₂` appears in both
   sub-goals, forcing `subst hsA` to substitute `sA → s₂` rather
   than the reverse — initial attempts without `refine`-first ran
   into Lean's `subst` direction heuristic substituting `s₂ → sA`,
   leaving the `⟨s₂, M₂, ...⟩` term ill-typed). For each sub-goal,
   destructure the existential, apply
   `eq_of_not_isPReducible_of_pReducesTo`, `subst hsA`,
   `obtain rfl : MA = M₂ := eq_of_heq hMA`, then `exact h1A` /
   `exact h3B`.

5. **Added a non-trivial witness** at end-of-file:
   `paddedEuler.PEquivalent paddedEuler` constructed via
   `hEquiv.trans_of_middle_not_pReducible hEquiv.symm hMid_irr`
   where `hEquiv : paddedEuler.PEquivalent (paddedEuler.pReduced
   pairPartition)` (via the `step` constructor with the new
   non-triviality witness `1 < 2`). The middle method
   `paddedEuler.pReduced pairPartition` has 1 stage; its
   irreducibility follows from the same `sBar < 1 ⇒ sBar = 0 ⇒
   Fin 0` argument used in `explicitEuler_isIrreducible`. This
   witness exercises both `step` (in both directions) and `trans`
   together — strictly beyond cycle 184's reflexive witness.

## Result

**SUCCESS**.

* `lake env lean OpenMath/Chapter3/Section381.lean`: exit 0, ~4s
  steady-state.
* `grep -c sorry OpenMath/Chapter3/Section381.lean`: 0.
* `lean_verify` axiom report on both new theorems:
  `[propext, Classical.choice, Quot.sound]` — axiom-clean.
* Tautology scanner
  (`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'`): no hits.

Phase C.2 of `lem:441A` remained blocked: the 5th consecutive
local-compile timeout on `Section441.lean` is logged in
`cycle_182_gpfs_slowness.md`. The cycle 182 draft + cycle 184
namespace fix is still preserved at
`.prover-state/cycle_182_draft_section441.lean` and ready to ship
once GPFS recovers.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `OpenMath.Chapter3.Section312.RKTableau.eq_of_not_isPReducible_of_pReducesTo`

- Entity ID and textbook statement: helper lemma; not a Butcher
  entity. The mathematical statement encodes the obvious fact that
  an irreducible source has no non-trivial reduction.
- Lean statement: given `M : RKTableau s` with `¬M.IsPReducible`,
  any `PReducesTo M M'` forces `s' = s ∧ HEq M' M`. This holds
  *because* the `step` constructor now requires `sBar < s` (cycle
  185 tightening), which combined with `M.IsPReducibleVia P`
  furnishes `M.IsPReducible := ⟨sBar, hLt, P, hVia⟩` —
  contradicting the hypothesis.
- Hypothesis strength: minimal — only `¬IsPReducible` (not the
  full `IsIrreducible := ¬IsZeroReducible ∧ ¬IsPReducible`,
  matching the level required for `PReducesTo` which is purely
  about P-reduction).

### `OpenMath.Chapter3.Section312.RKTableau.PEquivalent.trans_of_middle_not_pReducible`

- Entity ID and textbook statement: helper lemma; the textbook
  (Butcher §380, def:381F) does not directly state transitivity of
  P-equivalence — it defines P-equivalence as "each method reduces
  to the same reduced method", which suggests transitivity is
  morally a `≃`-relation property but the textbook doesn't prove
  it. The full transitivity over arbitrary middle methods requires
  P-reduction confluence (any two reduction sequences from a common
  source can be completed to a common target), which is not
  formally addressed in Butcher §380.
- Lean statement captures: a *restricted* transitivity through a
  non-P-reducible middle method. **Weaker** than full transitivity
  — the irreducible-middle hypothesis is strictly more than the
  textbook's literal statement (which has no such hypothesis).
- Justification for divergence: full transitivity requires
  confluence machinery that is multi-cycle work and depends on
  finite-stage well-foundedness arguments not yet developed; the
  restricted form is the minimum non-vacuous transitivity that
  composes with the existing reflexivity / symmetry / step
  infrastructure. The non-trivial witness
  `paddedEuler.PEquivalent paddedEuler` (via the irreducible
  1-stage middle `paddedEuler.pReduced pairPartition`)
  demonstrates the hypothesis is non-vacuously satisfiable on a
  textbook-relevant tableau.

### `OpenMath.Chapter3.Section381.PReducesTo` (constructor change)

- Entity ID: helper inductive (introduced cycle 184).
- Change: the `step` constructor now requires `_hLt : sBar < s`.
  Existing docstring at lines 386–392 already promised this
  ("each non-trivial P-reduction strictly decreases the stage
  count (`sBar < s`)"); the cycle 185 change closes a gap between
  the docstring and the implementation.
- Faithfulness: this **strengthens** the relation (a strict subset
  of the prior relation), which preserves all prior witnesses
  (the only prior consumer was the `paddedEuler` example using
  `pairPartition : PPartition 2 1` with `1 < 2`). No prior
  theorem is invalidated; the cycle 184 reflexivity / symmetry /
  `of_pReducesTo` lemmas all still type-check.
- Definition smuggling check: the textbook's notion of P-reduction
  is explicitly the one that *strictly decreases stages* (the new
  reduced method has `ŝ` stages with `ŝ < s`, otherwise the
  reduction is degenerate). The tightened constructor is more
  faithful, not less.

## Dead ends

### Initial proof of `trans_of_middle_not_pReducible` without `refine`-first

First attempt:
```lean
obtain ⟨sA, MA, h1A, h2A⟩ := h₁₂
obtain ⟨sB, MB, h2B, h3B⟩ := h₂₃
obtain ⟨hsA, hMA⟩ := eq_of_not_isPReducible_of_pReducesTo hIrr h2A
obtain ⟨hsB, hMB⟩ := eq_of_not_isPReducible_of_pReducesTo hIrr h2B
subst hsA
subst hsB
obtain rfl : MA = M₂ := eq_of_heq hMA
obtain rfl : MB = M₂ := eq_of_heq hMB
exact ⟨s₂, M₂, h1A, h3B⟩
```

Failed with `Unknown identifier 'M₂' / 's₂'` after the first
`subst`. Lean's `subst` heuristic substituted `s₂` with `sA`
(eliminating `s₂` from the context) rather than the desired `sA`
with `s₂`. Likely cause: `s₂` and `sA` are both ℕ-valued FVars,
neither is in the goal at the time of `subst`, and Lean's
heuristic chose to keep the more recently introduced one (`sA`).

Fix: `refine ⟨s₂, M₂, ?_, ?_⟩` *before* the `obtain` /
`subst`, so that each sub-goal contains `M₂` (and hence `s₂`),
forcing `subst` to substitute `sA → s₂` to maintain the goal's
type. This is a generic Lean 4 idiom for HEq / dependent-rewrite
proofs over type-changing substitutions.

### `subst` direction is **not** the same as `obtain rfl`'s direction

I initially expected `obtain rfl : MA = M₂` to substitute `MA` with
`M₂` (eliminating `MA`). It does not — same heuristic as `subst`,
chooses based on recency / dependencies. The `refine`-first
restructuring also fixed this issue.

## Discovery

* **GPFS slowness is file-specific, not cluster-wide**: the cycle
  185 smoke test on Section381.lean (70s clean compile, ~4s
  rebuild) confirms the cluster filesystem is reachable for *some*
  Lean elaboration. Section441.lean's specific transitive mathlib
  load (`Mathlib.Analysis.Polynomial.*`, `Complex.*` heavy) hits
  the slow path. This narrows the diagnostic — likely a hot olean
  cache miss / GPFS prefetch behavior specific to large dependency
  closures, not a wholesale cluster outage.
* **The cycle 184 `PReducesTo` infrastructure had a latent
  soundness gap**: the docstring already promised `sBar < s` for
  non-trivial steps, but the constructor didn't enforce it. The
  discrete partition (sBar = s, identity block-index) trivially
  satisfies `IsPReducibleVia` (the row-sum-constancy reduces to a
  single-singleton equality), so without `sBar < s` the strategy's
  proposed `IsPIrreducible` predicate was vacuously unsatisfiable.
  Future cycles introducing inductive reduction relations should
  audit non-trivial-step hypotheses against the
  `IsPReducibleVia`-vacuously-true case.
* **`refine` before `obtain` is the right Lean 4 idiom for
  HEq-flavored proofs**: when an existential's anonymous fresh
  variable shares a type with a theorem-declared FVar (e.g. both
  are ℕ), `subst` preferences may go the wrong direction. Putting
  the goal-shaping `refine ⟨...⟩` first makes the desired FVar
  appear in the sub-goals, forcing `subst` to keep it.

## Suggested next approach

### Priority for cycle 186

1. **Probe GPFS for Section441 again** (the cycle 185 strategy's
   step 0). If the smoke test completes in <5 min, **immediately
   ship Phase C.2** (replace HEAD with cycle 182 draft + cycle 184
   namespace fix). The diff is preserved in
   `.prover-state/cycle_182_draft_section441.lean` and
   `lem_441A_phase_C_scoping.md` cycle 184 update.
2. **If GPFS still degraded** (6th consecutive timeout), escalate
   per the `cycle_182_gpfs_slowness.md` recommendation —
   loop-maintainer should consult cluster admin for the GPFS
   prefetch / olean fetch pathology. While waiting, possible
   `def:381F` follow-ups:
   - `PEquivalent` extension to fold in 0-reduction (per the
     cycle 184 strategy note: "extending PReducesTo by a
     0-reduction constructor and re-using the same `∃ Mbar` shape
     for `PEquivalent`"). This would make `PEquivalent` faithful
     to the *full* def:381F (P+0 reduction), not just the P-only
     flavour. ~50 LOC.
   - Begin exploring P-reduction confluence for full
     `PEquivalent.trans` (no irreducible-middle hypothesis). High
     risk — confluence requires either an induction on stage
     count (well-founded) or a normalization argument; the
     textbook is silent on this.

### Risk note

The cycle 185 strategy proposed the strong `IsPIrreducible := ∀ P,
¬IsPReducibleVia M P` predicate — but as documented above, this is
vacuously unsatisfiable on every method (the discrete partition
trivially satisfies `IsPReducibleVia`). The planner should be
aware of this trap when proposing future P-reduction-style theorems
— the right predicate is `¬IsPReducible := ¬∃ sBar (h : sBar < s)
P, IsPReducibleVia M P`, which is the negation of the *non-trivial*
P-reducibility.
