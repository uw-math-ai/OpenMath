# Cycle 218 Results

## Worked on

§382 `thm:382A` bracketed (382f) form `[m₁ · m₂] = [m̂₁ · m̂₂]` via the
`composeQ` quotient lift on cycle 212's `Equivalent.setoidSigma`,
plus the corollary that gives the bracketed form directly.

Specifically, P1+P2+P3 from cycle 218 strategy §B:

- **P1**: `RKTableau.composeQ.{u} : Quotient Equivalent.setoidSigma.{u}
  → Quotient Equivalent.setoidSigma.{u} → Quotient Equivalent.setoidSigma.{u}`
  (`noncomputable def`, ~15 LOC including docstring).
- **P2 W1** (homogeneous): `composeQ ⟦⟨2, paddedEuler⟩⟧² =
  ⟦⟨2+2, paddedEuler.compose paddedEuler⟩⟧` (closed by `rfl`,
  ~8 LOC).
- **P2 W2** (heterogeneous): `composeQ ⟦⟨2, paddedEuler⟩⟧² =
  composeQ ⟦⟨1, paddedEuler.pReduced pairPartition⟩⟧²` (closed via
  `composeQ_eq_of_equivalent` + cycle 208's `paddedEuler_equivalent_pReduced`
  × 2, ~15 LOC).
- **P3**: `RKTableau.composeQ_eq_of_equivalent.{u}` — the bracketed
  (382f) form of `thm:382A`. Body is `show Quotient.mk _ _ =
  Quotient.mk _ _; exact Quotient.sound (compose_equivalent_compose
  ...)` (~10 LOC including docstring).

All three deliverables shipped clean. Total ~50 LOC across
`OpenMath/Chapter3/Section381.lean`.

## Approach

Followed cycle 218 strategy §B linearly:

1. **(0 min)** Loaded `extraction/formalization_data/entities/thm_382A.json`
   confirming the bracketed (382f) form `[m₁ · m₂] = [m̂₁ · m̂₂]` is
   the textbook statement; cycle 218's corollary captures it directly.
2. **(2 min)** Baseline build `lake env lean OpenMath/Chapter3/Section381.lean`
   returned 8.4s (cold) / 6.1s (warm) — well within tolerance, no
   GPFS degradation on §381 (33rd consecutive cycle of stable health
   since cycle 184).
3. **(1 min)** One `lean_loogle` query on `Quotient.lift₂` to confirm
   Mathlib signature: `{α β φ : Sort _} {s₁ : Setoid α} {s₂ : Setoid β}
   (f : α → β → φ) (c : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁
   = f a₂ b₂) (q₁ : Quotient s₁) (q₂ : Quotient s₂) : φ`. Single
   query, no further search needed. Also surfaced `Quotient.lift₂_mk`
   reduction lemma (used implicitly by `rfl` on the W1 P2 example).
4. **(10 min)** Wrote P1 `composeQ` inserted at line ~2733
   (immediately after cycle 217's `compose_equivalent_compose` body
   at line 2731, inside the `OpenMath.Chapter3.Section312.RKTableau`
   namespace which ends at line 2744). First-compile error: spurious
   `.{u}` annotations on `RKTableau s` (`RKTableau` is not
   universe-polymorphic — only `Equivalent` is). Fixed in 30s by
   removing `.{u}` from `RKTableau` references; kept on
   `Equivalent.setoidSigma.{u}` and the function-binder universe
   `composeQ.{u}` itself.
5. **(2 min)** Wrote P3 `composeQ_eq_of_equivalent` corollary
   immediately after `composeQ`. Same `.{u}` correction. Compiled
   on first re-attempt.
6. **(5 min)** Wrote P2 examples at end of file (in
   `OpenMath.Chapter3.Section381` namespace, after cycle 217's
   heterogeneous example at line ~2913). W1 closed by `rfl`; W2
   closed by `composeQ_eq_of_equivalent paddedEuler_equivalent_pReduced
   paddedEuler_equivalent_pReduced`. Both compiled first try.
7. **(2 min)** `lean_verify` on all four landmarks: cycle 218's
   `composeQ` + `composeQ_eq_of_equivalent`; cycle 217's
   `compose_equivalent_compose`; cycle 212's `Equivalent.setoidSigma`;
   cycle 214's `compose_isRKOneStep_iff`. All five returned axioms
   `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
   regressions on prior cycle work.
8. **(10 min)** Updated `lean_status.json` (bumped `thm:382A` row's
   `lean_symbol` to `composeQ_eq_of_equivalent` and `note` field
   to record cycle 218's two new symbols), `plan.md` (extended
   `thm:382A` line with cycle 218 entry), and `.prover-state/issues/thm_382A_path.md`
   (appended "Cycle 218 update — `composeQ` shipped, (382f) bracketed
   form CLOSED" section with R1–R5 risk register retrospective and
   cycle 219+ outlook).

## Result

**SUCCESS**. All three deliverables (P1 `composeQ`, P2 ×2 examples,
P3 `composeQ_eq_of_equivalent`) shipped clean on first compile after
the `.{u}` correction.

Section381.lean warm rebuild: 6.155s after edits (baseline was 6.109s
pre-edit), well within the cycle 218 strategy §F tolerance of 30s.

Sorry count: 0 → 0 (no change, no regression).

Axioms verified:
- `OpenMath.Chapter3.Section312.RKTableau.composeQ` → `[propext, Classical.choice, Quot.sound]`
- `OpenMath.Chapter3.Section312.RKTableau.composeQ_eq_of_equivalent` → same
- Cycles 217, 214, 212 landmarks: all unchanged, same axioms.

**Both textbook forms of `thm:382A` are now closed**:
- (382g) un-bracketed heterogeneous: `m₁ · m₂ ≡ m̂₁ · m̂₂` (cycles
  215–217's `compose_equivalent_compose`).
- (382f) bracketed: `[m₁ · m₂] = [m̂₁ · m̂₂]` (cycle 218's
  `composeQ_eq_of_equivalent`).

`thm:382A`'s row in `lean_status.json` stays at `formalized` and
`lean_symbol` is rewritten from `compose_equivalent_compose` to
`composeQ_eq_of_equivalent` (the latter is the literal
textbook-statement form).

## Faithfulness check

### `RKTableau.composeQ` (cycle 218 new `def`)

This is **infrastructure** (a quotient lift), not a named textbook
concept — Butcher does not name `composeQ` per se; it is the natural
lift of `RKTableau.compose` to `Quotient Equivalent.setoidSigma`
that makes the bracketed form of `thm:382A` even statable.
Faithfulness-check items:

- **Tautology check**: N/A (definition, not theorem).
- **Identity check**: body is `Quotient.lift₂ (fun p q => Quotient.mk
  _ ⟨p.1 + q.1, p.2.compose q.2⟩) (...)` — does real mathematical
  work (lifts a binary operation across a setoid quotient).
- **Definition smuggling**: the underlying operation
  `p.2.compose q.2` is cycle 209's already-verified `RKTableau.compose`;
  no smuggling.
- **Hypothesis strength**: N/A (definition).

### `RKTableau.composeQ_eq_of_equivalent` (cycle 218 new theorem)

- **Entity ID**: `thm:382A` (bracketed (382f) form), textbook statement quoted from
  `extraction/formalization_data/entities/thm_382A.json`:
  > Let $m_1$, $m_2$, $\widehat{m}_1$, $\widehat{m}_2$ denote
  > Runge--Kutta methods, such that $\widehat{m}_1 \equiv m_1$ and
  > $\widehat{m}_2 \equiv m_2$. (382f) Then $[m_1 \cdot m_2] =
  > [\widehat{m}_1 \cdot \widehat{m}_2]$.

- **Lean statement captures**: same content (bracketed (382f) form
  directly).
- **Tautology check**: hypothesis is `Equivalent` × 2, conclusion is
  equality of `Quotient.mk` classes. Distinct, no tautology.
- **Identity check**: body is `show ... = ...; exact Quotient.sound
  (compose_equivalent_compose ...)`. The `Quotient.sound` step does
  real work (it is the canonical bridge from `≈` to `Quotient.mk =
  Quotient.mk`); not just `exact h`.
- **Definition smuggling**: cycle 217's `compose_equivalent_compose`
  proves the (382g) form `m₁·m₂ ≡ m̂₁·m̂₂` directly (not the (382f)
  conclusion); the lift through `Quotient.sound` translates ≡ to =
  on classes. This is the canonical category-theoretic move and is
  the textbook's own argument ("Proof. We note that an equivalent
  statement is m₁·m₂ ≡ m̂₁·m̂₂.").
- **Hypothesis strength**: `Equivalent` × 2 matches the textbook's
  hypothesis `m̂₁ ≡ m₁ ∧ m̂₂ ≡ m₂` exactly. No extra hypotheses.

### P2 W1 example (homogeneous)

- Asserts `composeQ ⟦⟨2, paddedEuler⟩⟧² = ⟦⟨2+2, paddedEuler.compose
  paddedEuler⟩⟧`, closed by `rfl`. This is a definitional
  consequence of `Quotient.lift₂_mk` and the body of `composeQ`.
  Non-vacuity verification on the canonical 2-stage witness; no
  textbook entity, no faithfulness gap.

### P2 W2 example (heterogeneous)

- Asserts `composeQ ⟦⟨2, paddedEuler⟩⟧² = composeQ ⟦⟨1,
  paddedEuler.pReduced pairPartition⟩⟧²`, closed via
  `composeQ_eq_of_equivalent paddedEuler_equivalent_pReduced
  paddedEuler_equivalent_pReduced`. Exercises the corollary on the
  genuinely heterogeneous stage sums `(2+2) ≠ (1+1)`. No textbook
  entity, no faithfulness gap.

## Dead ends

**Universe annotation `.{u}` on `RKTableau`**: first compile attempt
included `RKTableau.{u} s₁` annotations in the binders. Lean rejected
with "too many explicit universe levels for `OpenMath.Chapter3.Section312.RKTableau`"
(line 2752, line 2772, line 2773 — six error sites). `RKTableau` is
not universe-polymorphic (it just packages `Matrix (Fin s) (Fin s) ℝ`,
`Fin s → ℝ`, `Fin s → ℝ` — all monomorphic types). Only `Equivalent`
needs `.{u}` because it quantifies over the test field `N : Type u`.

Fix: removed `.{u}` from `RKTableau` references; kept on
`Equivalent.setoidSigma.{u}` and on the function definition itself
(`composeQ.{u}`, `composeQ_eq_of_equivalent.{u}`). Compiled clean
after.

Recoverable in ~30s; the cycle 218 strategy §C did not pre-flag this
as a risk because the cycle 217 work all had `RKTableau` without `.{u}`
in binders (only `Equivalent` carried the annotation). I added `.{u}`
out of universe-polymorphism caution; Lean caught it on first compile.

## Discovery

1. **`Quotient.lift₂_mk` does the heavy lifting for the W1 `rfl`
   example.** Without it, the W1 example would need explicit
   unfolding through `Quotient.lift₂` reduction. Mathlib provides
   `Quotient.lift₂_mk : Quotient.lift₂ f h ⟦a⟧ ⟦b⟧ = f a b` as a
   `@[simp]` lemma, which is enough for `rfl` to close the example
   via definitional reduction.

2. **The cycle 217 strategy's `congr 1 <;> exact Quotient.sound ...`
   recipe for the heterogeneous P2 example is overkill.** The cleaner
   route is to use cycle 218's `composeQ_eq_of_equivalent` corollary
   directly, which is shorter and self-documenting.

3. **`compose_equivalent_compose` is consumed exactly once in cycle
   218's body** (inside the `Quotient.lift₂` respect obligation),
   but indirectly enables BOTH the lifted operation `composeQ` AND
   the bracketed-form corollary — a 1:2 leverage ratio that
   illustrates the value of bottom-up infrastructure cycles. Cycle
   217's investment (heterogeneous-stage generalization) pays off
   here.

4. **`noncomputable` is required even though both sides of `composeQ`
   are constructive.** This is because `Quotient.lift₂` uses
   `Quot.lift` under the hood, which is itself `noncomputable` in
   Lean's kernel. Pragmatically irrelevant for our use case (we never
   execute `composeQ`; we only reason about it propositionally).

5. **The respect obligation for `Quotient.lift₂` destructures cleanly
   without `Setoid.r` unfolding.** Cycle 212's `setoidSigma`'s `.r`
   field is defined as `r p q := @Equivalent.{u} p.1 q.1 p.2 q.2`,
   so when Lean elaborates the rintro `⟨s₁, M₁⟩ ⟨s₂, M₂⟩ ⟨s₁', M₁'⟩
   ⟨s₂', M₂'⟩ hEq₁ hEq₂`, the hypotheses `hEq₁` and `hEq₂` are
   inferred as `@Equivalent s₁ s₁' M₁ M₁'` and `@Equivalent s₂ s₂'
   M₂ M₂'` directly. The prophylactic `show @Equivalent.{u} (s₁ + s₂)
   (s₁' + s₂') ...` is for the conclusion after `apply Quotient.sound`,
   not for the hypotheses.

## Suggested next approach

**Cycle 219 target — §382 group structure (identity)**: define the
identity element of `Quotient Equivalent.setoidSigma` (Butcher §382
calls it the "neutral" element; likely either the 0-stage tableau
or `explicitEuler`). Prove `composeQ ⟦identity⟧ q = q` and `composeQ
q ⟦identity⟧ = q` for all `q`. Required machinery: `Quotient.ind`
to reduce to representatives + cycle 217's `compose_equivalent_compose`
(or a new identity-specific equivalence lemma).

**Cycle 220 target — §382 group structure (inverse)**: Butcher §382
constructs the inverse element via a specific transformation of `(c,
A, b)`. Read §382 carefully (page 306 of the PDF) for the exact
formula. Prove `composeQ ⟦M⟧ ⟦M.inverse⟧ = ⟦identity⟧` and the
reverse.

**Cycle 221+ target — §382 group structure (associativity)**: cycle
210's deferred `compose_assoc` (HEq plumbing issue) may now become
tractable via `Quotient.sound` on an `Equivalent`-level associativity.
Specifically:
- Define a `compose_assoc_equivalent` lemma:
  `(M₁.compose M₂).compose M₃ ≡ M₁.compose (M₂.compose M₃)`
  (note: even the `≡` form has HEq concerns because of `(s₁+s₂)+s₃
  ≠ s₁+(s₂+s₃)` definitional but not HEq-on-the-nose). Probably
  needs to be stated as `Equivalent` on Σ-types (using
  `setoidSigma`'s relation).
- Then `composeQ_assoc : composeQ (composeQ a b) c = composeQ a
  (composeQ b c)` follows by `Quotient.ind₃` + `Quotient.sound` on
  the `Equivalent`-level lemma.

**Cycle 222+ target — §382 group instance**: once identity, inverse,
and associativity are in hand, package as `Group (Quotient
Equivalent.setoidSigma)`. This is the textbook content of `thm:382A`
plus `thm:382B`, `lem:383A`, ... — the §382 group of Runge–Kutta
methods.

**Other unblocked work**: §441 Phase C.2 remains GPFS-blocked (34th
consecutive cycle of pathology since cycle 184). Per the long-standing
remediation, this is loop-maintainer territory; cycle 218 did not
attempt it. If the GPFS issue is resolved upstream, cycle 219+ could
unblock §441 work.

**Recommendation for the planner**: cycle 219 should ship the identity
element + its one-sided absorptions. This is the smallest single-cycle
group-axiom step and naturally builds on cycle 218's `composeQ`. The
inverse element (cycle 220+) requires more careful reading of Butcher
§382 to nail down the exact construction formula.
