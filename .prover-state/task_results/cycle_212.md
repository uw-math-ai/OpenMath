# Cycle 212 Results

## Worked on

§380 / §382 infrastructure track (10th–11th consecutive cycle since cycle 203):

- **P1**: `RKTableau.Equivalent.setoidSigma.{u} : Setoid (Σ s : ℕ, RKTableau s)`
  — heterogeneous Σ-typed setoid in `OpenMath/Chapter3/Section381.lean` at
  lines 1910–1928, immediately after cycle 211's fixed-stage
  `Equivalent.setoid.{u}`. Packages cycles 203/204/206's
  `equivalent_self` / `Equivalent.symm.{u}` / `Equivalent.trans.{u}`
  through Σ-type projections `.1` / `.2` into a Setoid on
  `Σ s : ℕ, RKTableau s`.
- **P2**: three non-vacuity witnesses for `Equivalent.setoidSigma` at lines
  2317–2354 of `Section381.lean` (after `paddedEuler_equivalent_pReduced`):
  W1 (homogeneous reflexivity at `⟨2, paddedEuler⟩`), W2 (heterogeneous-stage
  equivalence `⟨2, paddedEuler⟩` ↔ `⟨1, paddedEuler.pReduced pairPartition⟩`
  via cycle 208's `paddedEuler_equivalent_pReduced`), W3 (`Quotient.mk`
  well-formedness via `Quotient.sound` lifting W2's relation witness to
  quotient-class equality).
- **P3 stretch**: `.prover-state/issues/compose_isRKOneStep_iff_scoping.md`
  (~280 lines of markdown, zero Lean code) — Gap A scoping doc pre-positioning
  cycle 213+ for the structural bridge `compose_isRKOneStep_iff`.

## Approach

### P1 — canonical recipe verbatim

Wrote the strategy's canonical recipe verbatim (anonymous-constructor
`Setoid` with `r p q := @Equivalent.{u} p.1 q.1 p.2 q.2` and `iseqv := ⟨fun
p => @equivalent_self p.1 p.2, fun {p q} h => @Equivalent.symm.{u} p.1 q.1
p.2 q.2 h, fun {p q r} h₁ h₂ => @Equivalent.trans.{u} p.1 q.1 r.1 p.2 q.2
r.2 h₁ h₂⟩`). All universe references pinned to `u` via explicit `.{u}`
annotations on every component, with Σ-projections `.1` and `.2` written out
explicitly.

No fallback needed — the canonical recipe compiled cleanly on first attempt
(6.2s warm rebuild).

### P2 — `show <bare Equivalent>` per Risk 2 mitigation

All three witnesses use the `show paddedEuler.Equivalent <target>` reframing
pattern from cycle 211's W2/W3 examples to bypass Lean's implicit-lambda
introduction on `Setoid.r`'s ∀-shaped unfold. W3 uses `apply Quotient.sound`
followed by `show ...; exact ...` per Risk 3 mitigation (setoid-flavoured
wrapper around `Quot.sound`).

### P3 — scoping doc

Read Butcher §382 (extraction/raw_text/ch03.txt:8671+) to resolve the
c-scaling question flagged by `thm_382A_path.md`. Derived the answer from
both:

1. **Algebraic unfold of `compose` def at `Section381.lean:2480`**: the
   composite output formula `y₀ + H · Σᵢ (Fin.append M₁.b M₂.b) i · f(...)`
   splits via `Fin.append`'s definition into `y_mid + H · Σⱼ M₂.b j · f(Y_bot
   j)` where `y_mid := y₀ + H · Σⱼ M₁.b j · f(Y_top j)`. The step-size
   parameter `H` appears verbatim in both sub-steps — *no `H/2` rescaling*.

2. **Textbook consistency**: Butcher §382 (382b–e) writes `h` throughout for
   both sub-steps. The bottom-block abscissas `1 + c̄ᵢ` (under preconsistency)
   exceed `[0, 1]` because the composite step naturally advances time by `2h`
   while keeping the *step-size parameter* equal to `h`.

Resolution: forward direction `(M₁.compose M₂).IsRKOneStep f y₀ H y_final ↔
∃ y_mid, M₁.IsRKOneStep f y₀ H y_mid ∧ M₂.IsRKOneStep f y_mid H y_final`,
with the same `H` in all three places.

Doc structure: target statement, c-scaling resolution, proposed Lean
signature (both the full iff form and a stripped-down reverse-only form
`compose_of_isRKOneStep` requiring no smallness), proof sketches for both
directions, LOC breakdown (~150 LOC total, recommended split: cycle 213
ships reverse, cycle 214 ships forward), cross-references to cycles
204/205/207/209, recommended sorry-first entry point, non-blockers, open
questions on Mathlib `Fin.append` lemma names.

## Result

**SUCCESS** — all three priorities landed cleanly.

- **P1**: instance compiles and is axiom-clean
  (`[propext, Classical.choice, Quot.sound]` via `lean_verify`). 22 LOC
  (12-line docstring + 10-line instance body). Section381.lean warm rebuild
  6.2s.
- **P2**: all three witnesses compile. ~30 LOC total across three examples.
  Section381.lean warm rebuild 6.1s.
- **P3**: 280 lines of markdown scoping doc. Zero Lean code (per strategy).

Sorry count remains 0 repo-wide. No new axioms. No new warnings.

## Faithfulness check

### `RKTableau.Equivalent.setoidSigma.{u}` — instance, not a textbook entity

- Entity ID: none (Mathlib idiom; pure Lean infrastructure).
- Textbook statement: N/A — this is a Setoid wrapper around the existing
  textbook-faithful `def:381A` `Equivalent` predicate (cycle 204's
  faithfulness already audited).
- **Tautology check**: NO. The `iseqv` field is structural packaging
  delegating to three substantive axiom-clean theorems from cycles 203
  (refl), 204 (symm), 206 (trans). It is NOT `iseqv := ⟨trivial, trivial,
  trivial⟩`.
- **Identity check**: NO. The instance is a typeclass binding that consumes
  refl/symm/trans, not a re-export.
- **Definition smuggling check**: NO. `Setoid` is Mathlib's standard
  equivalence-relation typeclass; the relation `r` faithfully restricts the
  textbook `Equivalent.{u}` predicate to dependent-pair inputs `p.1, q.1,
  p.2, q.2`.
- **Hypothesis strength check**: no hypotheses (the instance is
  unconditional on `Σ s : ℕ, RKTableau s`).

### W1, W2, W3 — `example`s, not named entities

No textbook entities to check; these are typeclass-resolution sanity tests.
None claim a textbook result; all use existing axiom-clean witnesses
(`paddedEuler.equivalent_self` cycle 203, `paddedEuler_equivalent_pReduced`
cycle 208) routed through the new Setoid.

## Dead ends

None this cycle. The canonical recipe compiled on first attempt.

The `apply Quotient.sound` form for W3 was preemptively chosen (per Risk 3)
over a direct `Quot.sound paddedEuler_equivalent_pReduced` term — the latter
*might* have worked too, but `Quotient.sound` is the setoid-flavored wrapper
explicitly designed for `Setoid.r`-shape input and was strictly safer given
the implicit-lambda trap experienced in cycle 211.

## Discovery

### Σ-typed setoid universe-polymorphism works identically to fixed-stage setoid

The cycle 211 universe-metavariable issue with `Equivalent.{u}` is fully
mitigated by writing `.{u}` on every component (instance head, `r` body,
each `iseqv` field) — this pattern lifts to Σ-types without modification.
The Σ-projection `.1` / `.2` does not introduce any new universe
metavariables because `RKTableau s : Type` is a concrete-universe family
parameterized by `s : ℕ` (no universe polymorphism in the indexing).

### C-scaling resolution for compose: no H/2 rescaling

Re-deriving from `compose`'s definition (`Section381.lean:2480`):
`(M₁.compose M₂).b = Fin.append M₁.b M₂.b` — the b-coefficients are
*appended without rescaling*. Combined with the bottom-block `A` rows
(`compose_A_botLeft = M₁.b j`, `compose_A_botRight = M₂.A i j`), the
composite output formula at step size `H` factors algebraically as
`y_mid + H · Σⱼ M₂.b j · f(Y_bot j)` where `y_mid := y₀ + H · Σⱼ M₁.b j ·
f(Y_top j)`. Both sub-steps use the same `H`. This resolves a question
flagged by `thm_382A_path.md` and informs cycle 213's `compose_isRKOneStep_iff`
signature.

### `Quotient.sound` vs `Quot.sound`: prefer the former for Setoid-wrapped relations

Cycle 211 used a `rfl`-based Quotient witness (no relation lifting needed).
Cycle 212's W3 is the first instance in this codebase that genuinely lifts
a relation through `Quotient.mk` to produce a class-equality. `Quotient.sound`
(setoid-aware) cleanly accepts `Setoid.r`-shape input and routes through
`show <bare predicate>` reframing without further intervention; `Quot.sound`
(raw quotient) would require additional unfolding.

## Suggested next approach

### Cycle 213 — Gap A reverse direction (`compose_of_isRKOneStep`)

The scoping doc `compose_isRKOneStep_iff_scoping.md` recommends a 2-cycle
split:

- **Cycle 213** (~40 LOC, no smallness analysis): ship the reverse direction
  `compose_of_isRKOneStep : M₁.IsRKOneStep f y₀ H y_mid →
  M₂.IsRKOneStep f y_mid H y_final → (M₁.compose M₂).IsRKOneStep f y₀ H
  y_final`. Pure algebraic assembly via `Fin.append Y₁ Y₂` and cycle 209's
  `compose_A_*` simp lemmas. No smallness, no Lipschitz, no Banach machinery.

- **Cycle 214** (~70 LOC): ship the forward direction using cycle 205's
  `IsRKOneStep_exists` on `M₁`'s top-block stage tuple, with smallness
  threshold `1 / (2 · ((L:ℝ) · C₁ + 1))` where `C₁ := Σᵢ Σⱼ |M₁.A i j|`.

- **Cycle 215**: ship thm:382A via the (382g) reformulation `m₁ · m₂ ≡
  m̂₁ · m̂₂` using the now-complete `compose_isRKOneStep_iff` to unpack
  Equivalent's universal quantification.

### Alternative entry point — `Fin.append` Mathlib lemma audit

Before cycle 213 starts on `compose_of_isRKOneStep`, a short investigation
of Mathlib's `Fin.append` lemmas would be helpful:

- `Fin.append_castAdd` / `Fin.append_natAdd` — likely both exist.
- `Fin.sum_univ_addCases` or `Fin.sum_append` for splitting a sum over
  `Fin (s₁ + s₂)` into top-block + bottom-block — may need a helper if not
  in Mathlib.

A ~20-LOC pre-cycle helper file at `OpenMath/Chapter3/Section381/FinAppendHelpers.lean`
(or inlined in `Section381.lean`) could pre-stage these lookups. If they
turn out to all exist in Mathlib, the helper file is unnecessary.

### Optional: cycle 213 might also include a `compose_assoc_HEq` retry

Cycle 210 deferred `compose_assoc` due to HEq plumbing exceeding the 30-LOC
budget. With the Σ-typed setoid now in scope, an alternative formulation
could be `compose_assoc_at_setoid` (heterogeneous Equivalent rather than
HEq-Eq) — but this should NOT be a primary deliverable for cycle 213; the
reverse direction of `compose_isRKOneStep_iff` is strictly more valuable.

### No new blockers

No new issue files. The cycle 211 `thm_382A_path.md` doc remains current,
augmented this cycle by `compose_isRKOneStep_iff_scoping.md`.

§441 Phase C.2 GPFS-blocked (30th consecutive, skipped per
`cycle_182_gpfs_slowness.md` standing escalation).
