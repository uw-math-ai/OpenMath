# Cycle 235 Results

## Worked on
§383 Phase 4.3 inverse axiom: `inverse_phiEquivalent_inverse` —
the third axiom needed for the `Group` instance on
`Quotient PhiEquivalent.setoidSigma`. Plus (as bonus, via the
chosen proof path) both inverse absorption laws at the
`PhiEquivalent` level: `compose_inverse_phiEquivalent` and
`inverse_compose_phiEquivalent`.

## Approach

Aristotle-first per strategy §B.4. Submitted sorry-first scaffold
(project `ed3d2ff9-086c-4c94-aa8a-d31bff207fd7`) with full
context including (a) cycle 232's `gen_dws_eq`/`gen_dwsp_eq`
trailing-factor trick as a pattern hint and (b) empirical
small-tree closed forms. Slept 30 min. Single poll showed
IN_PROGRESS at 10 %. Pivoted to manual fallback per strategy.

During the read-references-while-sleeping phase, uncovered a key
structural observation: comparing the recursion of
`M.inverse.derivativeWeight` (which uses
`M.inverse.A i j = M.A i j − M.b j`) against cycle 225's
`derivativeWeightWithSrc`, the `−M.b j` correction precisely
mediates between two clean identities:

- (★★) `M.inverse.derivativeWeight i t
       = M.derivativeWeightWithSrc M.inverse i t`
- (★★★) `M.inverse.derivativeWeightWithSrc M i t
       = M.derivativeWeight i t`

Both proved by mutual structural induction on the rooted-tree /
list-of-trees pair. The `−M.b j` correction either gets absorbed
into the source-leaf `M.elementaryWeight c` (★★★) or appears as
`−M.inverse.elementaryWeight c` (★★).

From (★★) and (★★★), the absorption laws drop out by direct
calculation against cycle 225's `compose_elementaryWeight_decomp`:
- (M.inverse.compose M).elementaryWeight t
  = M.inverse.elementaryWeight t + ∑ M.b · M.dWWS M.inverse
  = M.inverse.elementaryWeight t + ∑ M.b · M.inverse.dW    [★★]
  = M.inverse.elementaryWeight t + (−M.inverse.elementaryWeight t)
  = 0 = id.elementaryWeight t.
- (M.compose M.inverse).elementaryWeight t
  = M.elementaryWeight t + ∑ M.inverse.b · M.inverse.dWWS M
  = M.elementaryWeight t − ∑ M.b · M.derivativeWeight     [★★★]
  = M.elementaryWeight t − M.elementaryWeight t = 0.

`inverse_phiEquivalent_inverse` then follows by standard monoid
uniqueness-of-inverse:
  M'.inverse ≡ id · M'.inverse                           [cycle 229 symm]
            ≡ (M.inverse · M) · M'.inverse                [left abs symm]
            ≡ M.inverse · (M · M'.inverse)                [cycle 233 assoc]
            ≡ M.inverse · (M' · M'.inverse)               [cycle 226 left]
            ≡ M.inverse · id                              [right abs]
            ≡ M.inverse                                   [cycle 229]

## Result

SUCCESS — three new public symbols shipped axiom-clean:
`inverse_phiEquivalent_inverse`, `compose_inverse_phiEquivalent`,
`inverse_compose_phiEquivalent`. Plus four private mutual helpers
in two `mutual ... end` blocks: (★★) per-tree + list-helper, and
(★★★) per-tree + list-helper. Three `paddedEuler` non-vacuity
witnesses (one per public symbol). Sorry count remains 0 (50th
consecutive clean cycle since cycle 201 rollback). Warm rebuild
6.4 s.

Aristotle (project `ed3d2ff9-086c-4c94-aa8a-d31bff207fd7`) was
IN_PROGRESS at 10 % on single permitted poll — manual fallback
overtook it.

## Faithfulness check

### `inverse_phiEquivalent_inverse`

- Entity ID: `thm:384A` (§384 group homomorphism Φ between groups
  G₁ → G; cycle 235 ships the inverse axiom of the codomain
  `Group` instance, NOT the homomorphism Φ itself).
- Textbook statement (`thm:384A`, §384 p. 311):
  > Let Φ : T → R be the elementary weight function associated
  > with (A, b, c) and Φ̃ : T → R the elementary weight function
  > associated with (Ã, b̃, c̃). Let Φ̂ : T → R denote the
  > elementary weight function for the product method as
  > represented by (382a). Then Φ̂ = Φ Φ̃.
- Lean statement captures: weaker — cycle 235 ships only inverse
  well-definedness at the `PhiEquivalent` level (the inverse
  axiom of the codomain group), not the homomorphism Φ. The
  codomain group structure is built axiom-by-axiom over cycles
  233 (associativity) / 234 (identity) / 235 (inverse). The full
  thm:384A also requires (a) finishing the §383 `Group` instance
  (cycle 236 absorption laws lifted to `composeQ_phi`, cycle 237+
  `Group.ofLeftAxioms`) and (b) shipping Φ as a `MonoidHom`
  (cycle 238+).
- Justification for divergence: matches cycles 233/234's
  partial-axiom-shipping pattern. Strategy §B and §F both note
  the cycle 235 deliverable is "the inverse axiom of the codomain
  Group", not the homomorphism. Documented in plan.md thm:384A
  row.
- Tautology check: hypothesis `hPhi : PhiEquivalent M M'`;
  conclusion `PhiEquivalent M.inverse M'.inverse`. No verbatim
  overlap.
- Identity-only proof check: NOT a one-line `exact h` — proof is
  a 6-step `refine ... .trans ?_` chain through cycle
  229/226/232/233 infrastructure.
- Hypothesis strength check: minimal — just one `PhiEquivalent`.
- Definition smuggling check: no new `class` / `structure`.
- Absent theorem check: theorem exists at HEAD, not just a
  promise.

### `compose_inverse_phiEquivalent` / `inverse_compose_phiEquivalent`

These are bonus deliverables (cycle 236's intended targets at
the `PhiEquivalent` level). Their faithfulness traces to
`thm:382B`'s textbook content: the §382 group's inverse
absorption laws, which §383 inherits structurally because the
inverse method's elementary-weight reflects the §382-level
absorption laws once one passes through the (★★)/(★★★)
structural identities. Both axiom-clean.

### `(★★)` / `(★★★)` private helpers

These are technical infrastructure (private). Their content is
fully derivable from the public definitions of `derivativeWeight`
(cycle 312), `derivativeWeightWithSrc` (cycle 225), and
`RKTableau.inverse` (cycle 220). The mutual structural-recursion
proof is the standard pattern (see cycles 224/225/226/228/229/
230/231 for analogous mutual blocks). No textbook claim attached.

## Dead ends

None — the manual approach worked on first compile after one
round of straightforward syntactic fixes (mutual recursion needed
`mutual ... end` blocks; one `Finset.sum_neg_distrib` rewrite
had wrong direction; one `PhiEquivalent.refl` namespace
disambiguation in a non-vacuity example).

## Discovery

**D1 (the cycle's main insight, generalizable).** The §382
structural inverse `M.inverse.A i j = M.A i j − M.b j` has a
clean "antipode at depth one" interpretation: the −M.b j
correction is *exactly* what cycle 225's `derivativeWeightWithSrc`
needs to thread an `elementaryWeight` correction into the
cons-step recursion. Specifically, comparing recursions:

- `M.inverse.derivativeWeightProd i (c :: cs)
   = (∑ j (M.A i j − M.b j) · M.inverse.dW j c) · M.inverse.dWP i cs`
- `M.derivativeWeightWithSrcProd M.inverse i (c :: cs)
   = (M.inverse.eW c + ∑ j M.A i j · M.dWWS M.inverse j c)
       · M.dWWSP M.inverse i cs`

After distributing the LHS subtraction and pulling `∑ −M.b j ·
M.inverse.dW j c = +M.inverse.eW c` (definitionally), the two
recursions become identical. The mutual induction closes
immediately — `congr 1` after rewriting both sides yields a
linear-algebraic identity dischargeable by `ring`.

**D2 (Aristotle vs manual race).** Submitted at cycle start;
single poll at +30 min showed IN_PROGRESS at 10 % (same pattern
as cycle 226's stalled right-action). Manual proof closed in
~30 min after the polling decision (no further iteration
attempts beyond two trivial syntax fixes). For "interesting"
PhiEquivalent-level claims, the bottleneck is finding the right
generalization; once found, the Lean proof tends to be short.

**D3 (single-cycle multi-axiom ship).** Strategy intended cycle
235 to ship only `inverse_phiEquivalent_inverse` with cycle 236
to follow with the absorption laws. The (★★)/(★★★) path
collapsed these into one cycle because the absorption laws come
"for free" from the helpers, and `inverse_phiEquivalent_inverse`
needs only abstract monoid plumbing once the absorption laws
hold. Cycle 236 can now focus purely on quotient-level lifting
(`composeQ_phi_inverse_{left,right}` via `Quotient.inductionOn`
+ `Quotient.sound`), which is a much smaller cycle.

**D4 (Lean syntactic gotchas).** (a) `Finset.sum_neg_distrib`
has direction `∑ −f = −∑ f` (forward, not the conventional `−∑
→ ∑ −`). When the goal has `∑ M.inverse.b · X` on LHS, first
rewrite to `∑ −(M.b · X)` form via `inverse_b`/`neg_mul`, then
forward `Finset.sum_neg_distrib`. (b) `PhiEquivalent.refl` lives
in `namespace OpenMath.Chapter3.Section381`, not
`Section312.RKTableau`, so non-vacuity examples in the §381
namespace must use the unqualified form. (c) Mutual recursion
across two theorems requires `mutual ... end` blocks (not just
naming both before the second uses the first).

## Suggested next approach

**Cycle 236.** Lift the cycle-235 absorption laws to the
quotient via `Quotient.inductionOn`:

```lean
theorem composeQ_phi_inverse_right (q : Quotient PhiEquivalent.setoidSigma) :
    composeQ_phi q (inverseQ_phi q)
      = Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩ := by
  refine Quotient.inductionOn q ?_
  rintro ⟨s, M⟩
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (compose_inverse_phiEquivalent M)
```

Plus the symmetric `composeQ_phi_inverse_left` and the
`inverseQ_phi` definition itself (which lifts cycle 235's
`inverse_phiEquivalent_inverse` via `Quotient.lift`). Very small
cycle — likely <50 LOC.

**Cycle 237+.** Package `instance : Group (Quotient
PhiEquivalent.setoidSigma)` via `Group.ofLeftAxioms` (or
`Group.ofRightAxioms` depending on what Mathlib provides),
consuming cycle 233's `composeQ_phi_assoc`, cycle 234's
`composeQ_phi_id_left`, and cycle 236's
`composeQ_phi_inverse_left`. Analog of cycle 222's §382
`instGroup`.

**Cycle 238+.** Ship Φ as a `MonoidHom` from the §382 group to
the §383 group via `Quotient.lift` (well-definedness:
`Equivalent → PhiEquivalent` direction, still deferred per
`.prover-state/issues/thm_381H_deferred.md`). This is the "final
step" of `thm:384A`.

§441 Phase C.2 GPFS-blocked (40th consecutive, skipped per
strategy §A).
