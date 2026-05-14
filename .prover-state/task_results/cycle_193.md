# Cycle 193 Results

## Worked on

* **Priority 0 (smoke test)**: `OpenMath/Chapter4/Section441.lean` —
  13th consecutive GPFS-blocked timeout (logged).
* **Priority 2 (substantive)**:
  `RKTableau.PEquivalent.eq_of_both_isIrreducible` —
  canonical-form half of def:381E (irreducible P-equivalent methods
  coincide up to heterogeneous-stage `HEq`).
* **Priority 3 (stretch)**: `RKTableau.PReducesTo.toPhiEquivalent` —
  direct-alias caller-ergonomics corollary, one-hop bridge from a
  P-reduction to Φ-equivalence.

## Approach

### Priority 0 — Section441.lean smoke test

Pre-flight `ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D"`
showed no D-state zombies. Single `time timeout 300 lake env lean
OpenMath/Chapter4/Section441.lean` invocation: EXIT=143 (SIGTERM from
timeout), real 5m0.029s, user 0m0.231s, sys 0m0.479s (CPU = 0.24% of
wall — identical pattern to cycles 182–192). Logged in
`.prover-state/issues/cycle_182_gpfs_slowness.md` as "Cycle 193
update (13th timeout)". One-shot per cycle-193 strategy directive;
did not re-attempt.

### Priority 2 — `PEquivalent.eq_of_both_isIrreducible`

Placed in `OpenMath.Chapter3.Section312.RKTableau` namespace
immediately after cycle 190's `eq_of_isIrreducible_of_middle`
(Section381.lean:565–584). Statement and proof follow the cycle-193
strategy verbatim: `obtain` the existential common reduct from the
`PEquivalent M M'` hypothesis, apply cycle-188's
`eq_of_isIrreducible_of_pReducesTo` to each `PReducesTo` leg under
the respective `IsIrreducible` hypothesis, then `subst` both
resulting stage-equality witnesses (sMid → s, then s → s') and
chain the two `HEq`s via `h₂heq.symm.trans h₁heq` to produce
`HEq M' M`. The direct `subst h₁eq; subst h₂eq` path worked as the
strategy's primary suggestion — no need to fall back to manual
HEq-chain manipulation. Verified via `lean_hover_info` on
`eq_of_isIrreducible_of_pReducesTo` first that the signature
returns `s' = s ∧ M' ≍ M` (not the other direction); this matched
the strategy's assumption and the proof needed no adjustment.

**Non-vacuity witness**: the strategy proposed using
`paddedEuler_isIrreducible`, but `paddedEuler` is in fact
P-reducible (`paddedEuler_isPReducible`, Section381.lean:655), so
no such irreducible witness exists. Substituted the existing
private 1-stage irreducible witness
`paddedEuler_pReduced_pairPartition_isIrreducible`
(Section381.lean:1244–1267, cycle 190) and an `example` exercising
the canonical-form theorem on `(paddedEuler.pReduced
pairPartition).PEquivalent (paddedEuler.pReduced pairPartition)`
via `PEquivalent.refl`. Same type-level heterogeneous-stage
plumbing test as the strategy intended (the conclusion type
`∃ heq : 1 = 1, HEq … …` is well-formed *precisely because* the
theorem accepts heterogeneous stage indices).

### Priority 3 — `PReducesTo.toPhiEquivalent`

Two-line direct alias of cycle-187's `PhiEquivalent.of_pReducesTo`.
Placed in the `OpenMath.Chapter3.Section312.RKTableau` namespace
block at Section381.lean:1218–1226 (immediately after the existing
`PEquivalent.toPhiEquivalent`), which already `open`s
`OpenMath.Chapter3.Section381` so `PhiEquivalent.of_pReducesTo` is
in scope unqualified. The strategy's note about checking the
qualifier was thus moot — the existing namespace structure
accommodates the direct reference.

### Verification protocol (strategy §"Verification protocol")

1. `lake env lean OpenMath/Chapter3/Section381.lean` exit 0, warm
   rebuild 3.7s ✓ (matches the ~4s target).
2. `grep -c "^[^/-]*\bsorry\b" OpenMath/Chapter3/Section381.lean`
   → 0 ✓.
3. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PEquivalent.eq_of_both_isIrreducible`
   → axioms `[propext, Classical.choice, Quot.sound]` ✓.
4. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PReducesTo.toPhiEquivalent`
   → axioms `[propext, Classical.choice, Quot.sound]` ✓.
5. Regression spot-check `lean_verify
   OpenMath.Chapter3.Section381.paddedEuler_pEquivalent_pReduced`
   → axioms `[propext, Classical.choice, Quot.sound]` ✓ (no
   regression).

## Result

**SUCCESS** — both Priority 2 + Priority 3 shipped, all
verification protocol checks pass, Section441.lean Priority 0
expected-and-logged 13th GPFS timeout.

## Faithfulness check

### `theorem PEquivalent.eq_of_both_isIrreducible`

* **Textbook reference**: def:381F (Butcher §380, p. 303) — "Two
  Runge–Kutta methods are 'P-equivalent' if each of them reduces
  to the same reduced method." Quoted from
  `extraction/formalization_data/entities/def_381F.json`.
* The new theorem proves a **structural consequence**, not the
  definition itself: it shows that *if* two P-equivalent methods
  are individually irreducible, *then* they must coincide up to
  HEq. This is the canonical-form half of def:381E (the existence
  + uniqueness of "the reduced method" — uniqueness is what
  `eq_of_both_isIrreducible` is the witnesses for, since two
  candidate reduced forms reached from the same common chain must
  be equal).
* **Lean statement captures**: same content as the textbook
  "reduces to the same reduced method" implies "irreducible
  endpoints of a P-equivalence are equal" structural fact, modulo
  the heterogeneous-stage `HEq` formulation that the Lean encoding
  forces (since Lean's `RKTableau s` and `RKTableau s'` for `s ≠
  s'` are distinct types, equality of two irreducible P-equivalent
  methods must be expressed via the existence of a stage-count
  equality + an HEq across it).
* **Tautology check**: conclusion `∃ heq : s' = s, HEq M' M` does
  not appear as any hypothesis. The three hypotheses are
  `M.IsIrreducible`, `M'.IsIrreducible`, and `PEquivalent M M'` —
  structurally distinct. **Pass.**
* **Identity check**: proof is `obtain × 3 + subst × 2 +
  HEq.symm.trans` — composes cycle 188's
  `eq_of_isIrreducible_of_pReducesTo` and Lean's HEq calculus,
  not just `exact h`. **Pass.**
* **Hypothesis strength check**: all three hypotheses are
  consumed. Both `IsIrreducible`s gate the
  `eq_of_isIrreducible_of_pReducesTo` applications on the two
  legs; `PEquivalent` provides the existential middle. Cannot
  weaken. **Pass.**
* **Definition smuggling check**: not a `def` or `structure`. N/A.

### `theorem PReducesTo.toPhiEquivalent`

* **Textbook reference**: not a named textbook theorem; it is a
  caller-ergonomics shim that exposes cycle 187's
  `PhiEquivalent.of_pReducesTo` (which *is* the formal §380
  "reducibility implies same elementary weights" content) under
  a more discoverable name in dot notation on `PReducesTo`.
* **Lean statement captures**: same content as cycle 187's
  `PhiEquivalent.of_pReducesTo`, repackaged as a member-style
  corollary on `PReducesTo`. The two are definitionally equal.
* **Tautology check**: conclusion `PhiEquivalent M M'` does not
  appear as any hypothesis (`PReducesTo M M'` is structurally
  different — it is a relation indexed by an inductive type, not
  the `∀ τ, M.elementaryWeight τ = M'.elementaryWeight τ` body of
  `PhiEquivalent`). **Pass.**
* **Identity check**: proof is `PhiEquivalent.of_pReducesTo h` —
  it does merely re-export an existing theorem under a new name.
  This is intentional: the docstring marks it explicitly as a
  caller-ergonomics shim. The theorem does no new mathematical
  work, and its inclusion is solely so downstream code can write
  `h.toPhiEquivalent` on a `PReducesTo` hypothesis without first
  wrapping it through `PEquivalent.of_pReducesTo`. Per the
  cycle-193 strategy §"Pre-commit faithfulness checklist" entry
  for this theorem ("trivial direct corollary. Documents itself
  in the docstring as a caller-ergonomics shim, not a new
  mathematical claim. Pass."), this is acceptable as a
  documented, non-load-bearing alias. **Pass with caveat.**
* **Hypothesis strength check**: single hypothesis
  `h : PReducesTo M M'` — exactly the input the wrapped theorem
  requires. Cannot weaken. **Pass.**
* **Definition smuggling check**: not a `def` or `structure`. N/A.

### `example` (non-vacuity witness)

* Not a `def`/`theorem` — exercises type-level plumbing only,
  produces no new identifier in the namespace. No faithfulness
  checks apply.

## Dead ends

None this cycle. Both priorities shipped on first attempt without
proof-tactic fallback. The strategy's anticipated `subst` failure
mode (where the second `subst` could fail because the variable was
already substituted by the first) did not materialise — the direct
`subst h₁eq; subst h₂eq` worked cleanly because `h₁eq : sMid = s`
substitutes `sMid` (leaving `s` as the residual stage variable),
after which `h₂eq : sMid = s'` becomes `s = s'` and `subst h₂eq`
substitutes the freer `s'` (the existential-bound RHS) by `s`,
which is exactly what the conclusion `∃ heq : s' = s, HEq M' M`
needs.

## Discovery

The strategy's proposed non-vacuity witness (line 65 of the
strategy: `paddedEuler_isIrreducible paddedEuler_isIrreducible
(PEquivalent.refl paddedEuler)`) referenced a non-existent
identifier: `paddedEuler_isIrreducible` does not appear in
Section381.lean because `paddedEuler` is in fact P-reducible (the
named witnesses `paddedEuler_isPReducible` and
`paddedEuler_isZeroReducible` at lines 656 and 705 demonstrate
this explicitly). The actual irreducible witness in the file is
`paddedEuler_pReduced_pairPartition_isIrreducible` (private,
1-stage, line 1244), which I used instead. The substitution
preserved the strategy's intent (exercising the heterogeneous-
stage type-level plumbing on a non-trivial irreducible witness)
and the example compiles axiom-clean.

This is the second strategy-template/file-content discrepancy in
recent cycles (cycle 192 hit a similar issue with `#print axioms`
against a `/tmp/*.lean` external file reading stale `.olean`
cache); the pattern suggests the planner may benefit from a
pre-write `lean_local_search`/`grep` confirmation of every named
identifier in the proposed proof body before publishing the
strategy. Logging as a discovery rather than escalating as an
issue: the inline substitution was trivial (one-line example
swap) and did not block the cycle.

## Suggested next approach

* **def:381F next substantive step**: the natural Option-3B
  follow-up is *transitivity of P-equivalence through an
  irreducible end-point* (dual to cycle 188's
  `trans_of_middle_isIrreducible`). Specifically, if
  `PEquivalent M₁ M₂`, `PEquivalent M₂ M₃`, and `M₁` (or `M₃`) is
  irreducible, the new `eq_of_both_isIrreducible` combined with
  symmetry should yield `PEquivalent M₁ M₃` *and* let downstream
  callers identify which method "wins" the canonical form. ~30
  LOC, follows the cycle 188/190/193 proof template.
* **Alternative — `def:381E reducedMethod` construction**: the
  long-deferred (`.prover-state/issues/reduced_method_deferred.md`)
  iterated reduce-until-irreducible fixed-point construction
  remains the canonical multi-cycle target. With cycle 193's
  `eq_of_both_isIrreducible` in hand, uniqueness of the reduced
  method (the "same reduced method" clause of def:381F) is now
  *closeable* — only existence (the well-founded recursion proof
  that iterated reduction terminates at an irreducible) remains
  open. A cycle dedicated to setting up the
  `WellFoundedRelation` instance for `PReducesTo` (or for stage
  count) could unblock the existence direction.
* **Section441 smoke-test cadence**: if GPFS recovers and Phase
  C.2 ships, cycle 182's preserved draft with the cycle-184
  namespace fix at line 1529 is ready to land as-is.
  Loop-maintainer escalation via
  `.prover-state/issues/phantom_commit_verdict_pattern.md` and
  `cycle_182_gpfs_slowness.md` is in flight; worker continues to
  log timeouts at one-shot-per-cycle cadence.

## Aristotle status

No pending jobs. No new submissions this cycle (strategy
Priority 2 proof template was self-contained — cycle 188/190's
infrastructure carried the proof in 6 lines, well under any
threshold for Aristotle offload).
