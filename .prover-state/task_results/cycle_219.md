# Cycle 219 Results

## Worked on

§382 group identity element on `Quotient Equivalent.setoidSigma` —
six new symbols closing the first of the four deliverables in the
cycle 218 cycle 219+ outlook (identity, inverse, associativity, and
the `Group` instance package). Per cycle 219 strategy §B, all six
priorities P1–P6 shipped — the "strong cycle" outcome.

## Approach

Linear execution of the cycle 219 strategy §B recipe, in priority
order P1 → P6, with axiom-clean checkpoints between each:

- **P1** (`RKTableau.id : RKTableau 0`): defined as `{A := 0, b := 0,
  c := 0}`, leveraging the `Zero` instances inferred on `Matrix (Fin 0)
  (Fin 0) ℝ` (via `Pi.Zero` on a Matrix's underlying function type)
  and on `Fin 0 → ℝ` (via `Pi.Zero`). The strategy's `Fin.elim0`
  fallback was unnecessary — `0` works cleanly, matching the style
  of `paddedEuler`'s `A := 0, c := 0` from line 155.

- **P2** (`@[simp] id_isRKOneStep_iff`): both directions of the iff
  collapse via `simpa` through Lean's automatic empty `Fin 0` sum
  simplification (no explicit `Fin.sum_univ_zero` or `Finset.sum_empty`
  needed in the simp set). The reverse direction provides `Fin.elim0`
  as the empty stage-tuple witness with `fun i => Fin.elim0 i` for the
  vacuous-stage-equations proof.

- **P3** (`compose_id_equivalent`, right identity): used the cycle 219
  strategy §B.2 P3 recipe verbatim — factor the composite step via
  cycle 214's `compose_isRKOneStep_iff.mp`, collapse the right-factor
  `id.IsRKOneStep` via P2, rewrite, then discharge against
  `M.equivalent_self` (cycle 203).

- **P4** (`id_compose_equivalent`, left identity): mirror of P3 with
  sides swapped. The strategy's caveat about heterogeneous-stage
  `(0 + s)` vs `(s + 0)` (defeq) panned out — `0 + s` is NOT defeq but
  the proof body never inspects the stage count (works at abstract
  `IsRKOneStep` level), so the signature change is purely cosmetic.

- **P5** (`composeQ_id_left`, `composeQ_id_right`): used
  `Quotient.inductionOn` (cleaner than `Quotient.ind` — no explicit
  `motive` needed); destructure the underlying Σ-pair via `rintro`;
  reduce `composeQ ⟦⟨0, id⟩⟧ ⟦⟨s, M⟩⟧` to `⟦⟨0+s, id.compose M⟩⟧`
  definitionally through `Quotient.lift₂_mk` (handled by `show
  Quotient.mk _ _ = Quotient.mk _ _`); apply `Quotient.sound` on
  the absorption lemma from P3/P4.

- **P6** (non-vacuity): two `example`s in `namespace Section381`
  exercising the quotient laws on `⟦⟨0, RKTableau.id⟩⟧` and
  `⟦⟨2, paddedEuler⟩⟧`. Both proofs are one-line `composeQ_id_left _`
  / `composeQ_id_right _` calls.

GPFS smoke test (strategy §A): §441 Phase C.2 timed out at 300s
(36th consecutive timeout since cycle 184). One-line log appended to
`.prover-state/issues/cycle_182_gpfs_slowness.md`; §441 path skipped
per strategy.

## Result

SUCCESS — all six P1–P6 deliverables shipped axiom-clean.

- `OpenMath.Chapter3.Section312.RKTableau.id` — `[propext,
  Classical.choice, Quot.sound]`
- `OpenMath.Chapter3.Section312.RKTableau.id_isRKOneStep_iff` —
  `[propext, Classical.choice, Quot.sound]`
- `OpenMath.Chapter3.Section312.RKTableau.compose_id_equivalent` —
  `[propext, Classical.choice, Quot.sound]`
- `OpenMath.Chapter3.Section312.RKTableau.id_compose_equivalent` —
  `[propext, Classical.choice, Quot.sound]`
- `OpenMath.Chapter3.Section312.RKTableau.composeQ_id_left` —
  `[propext, Classical.choice, Quot.sound]`
- `OpenMath.Chapter3.Section312.RKTableau.composeQ_id_right` —
  `[propext, Classical.choice, Quot.sound]`

Cycle 218's `composeQ` and `composeQ_eq_of_equivalent` re-verified
axiom-clean — no regressions. Section381.lean cold rebuild 50.488s
(within strategy §F tolerance; cold-cache build since this is the
first build after cycle 218 + cluster restart between cycles 218→219).
Sorry count remains 0 in code (the lone grep hit on `\bsorry\b` is
inside a cycle 215 docstring: "sorry-scaffold via the route B.1 recipe
enabled by the cycle 216 ...").

All pre-flagged R1–R6 risks from cycle 219 strategy §C did NOT fire:

- **R1 (empty-Finset.sum unfolding)**: `simpa` discharged both
  directions of `id_isRKOneStep_iff` without explicit lemma assistance.
- **R2 (`Fin.elim0` vs `0` for `RKTableau.id` body)**: `0` worked
  cleanly for all three fields.
- **R3 (heterogeneous universe annotation in P4)**: `.{u}` on
  `Equivalent` worked first compile.
- **R4 (`compose_isRKOneStep_iff` arity at `M = id`)**: Lean inferred
  `s₁ = 0` from `RKTableau.id`'s type.
- **R5 (`Quotient.ind` motive inference in P5)**:
  `Quotient.inductionOn` chosen, no motive specification needed.
- **R6 (spurious `.{u}` on `RKTableau`)**: applied only to
  `Equivalent.{u}` and `Equivalent.setoidSigma.{u}`, never to
  `RKTableau` references (mindful of cycle 218's dead end).

## Faithfulness check

### `def RKTableau.id : RKTableau 0` (new — infrastructure for `thm:382A`)

- Entity ID and textbook statement: not a Butcher-named definition;
  this is a Lean-side infrastructure element supporting the §382 group
  identity element. Butcher §382 names the identity informally: "the
  identity of the group is the trivial method that performs no
  computation." The 0-stage tableau is the unique no-op:
  - `b : Fin 0 → ℝ` is the empty function, so `∑ i : Fin 0, b i • ...
    = 0`, meaning the output update is `y₁ = y₀ + h • 0 = y₀`.
  - `A : Matrix (Fin 0) (Fin 0) ℝ` is the zero matrix (vacuously,
    since there are no entries).
  - `c : Fin 0 → ℝ` is the zero function (vacuously).
- Lean statement captures: **same content** as Butcher's informal
  description of "the trivial no-op method."
- Note: `RKTableau.explicitEuler` is NOT the identity — it advances by
  `H • f y₀` (a 1-stage method with `b := fun _ => 1`), which is
  exactly the wrong behavior for a no-op.

### `theorem id_isRKOneStep_iff` (new — reduction lemma)

- Entity ID and textbook statement: not a Butcher-named theorem;
  this is a Lean-side reduction lemma that mechanically discharges
  the `id.IsRKOneStep f y₀ h y₁ ↔ y₁ = y₀` simplification used by
  the absorption laws below.
- Lean statement captures: **same content** as the definitional
  unfolding of `IsRKOneStep` at `s = 0` (empty sum = 0; `h • 0 = 0`;
  `y₀ + 0 = y₀`).

### `theorem compose_id_equivalent` and `theorem id_compose_equivalent` (new — §382 group identity at the `Equivalent` level)

- Entity ID and textbook statement (from `extraction/formalization_data/entities/thm_382A.json`):
  > "the equivalence classes of Runge–Kutta methods form a group
  > under composition."
- Lean statement captures: **part of the group axiom set** — these
  are the left and right absorption laws (`id * m = m` and `m * id =
  m`) at the underlying `Equivalent` predicate level (Butcher §382's
  group operates on equivalence classes, but the absorption laws lift
  trivially from `Equivalent`-level statements via `Quotient.sound`).
- Hypothesis strength: minimal — `compose_id_equivalent` is HOMOGENEOUS
  (since `s + 0 = s` in Lean 4), `id_compose_equivalent` is
  heterogeneous (`0 + s` vs `s`) but the proof never inspects stage
  counts. No extra hypotheses beyond `(M : RKTableau s)`.

### `theorem composeQ_id_left` and `theorem composeQ_id_right` (new — §382 group identity at the `Quotient` level)

- Entity ID and textbook statement: see `thm:382A` above. These are
  the *literal* textbook content of "id is the identity element of
  the group" — Butcher §382 operates on equivalence classes, and
  these theorems state the absorption laws on the quotient directly.
- Lean statement captures: **same content** as Butcher's "id is the
  identity element of the §382 group" — `composeQ ⟦id⟧ q = q` and
  `composeQ q ⟦id⟧ = q` for all `q : Quotient setoidSigma`.
- Hypothesis strength: minimal — no extra hypotheses, immediate
  consequences of `id_compose_equivalent` and `compose_id_equivalent`
  via `Quotient.inductionOn` + `Quotient.sound`.

Tautology / identity / definition-smuggling checks: all pass. The
proofs are non-trivial (factor the composite step via cycle 214's
iff, collapse the trivial factor via P2, dispatch the remaining
uniqueness obligation against `equivalent_self`). No `Prop` field
sneaking a conclusion into a hypothesis; no proof reduces to a single
`exact h`.

## Dead ends

None. All six P1–P6 deliverables shipped on first compile after the
single edit pass. The strategy's pre-flighted recipes for P3 and P4
(`compose_isRKOneStep_iff.mp` + `id_isRKOneStep_iff` + `equivalent_self`)
worked verbatim — no proof-tactic surgery required.

## Discovery

- **`simpa` defaults already handle the empty `Fin 0` sum collapse.**
  R1 anticipated needing explicit `Finset.sum_empty` or
  `Fin.sum_univ_zero` lemmas; in practice `simpa using hout` and
  `simpa using hy` discharge the iff both ways. Lean's default simp
  set knows that `∑ i : Fin 0, f i = 0` and that `0 + x = x` and `h •
  0 = 0` — chaining these gives `y₁ = y₀` from `y₁ = y₀ + h • ∑ i :
  Fin 0, id.b i • f (Y i)` in one shot.

- **`Quotient.inductionOn` is cleaner than `Quotient.ind` for
  point-and-shoot quotient theorems.** The strategy suggested
  `Quotient.ind` with explicit `motive`, but `Quotient.inductionOn q
  ?_` followed by `rintro ⟨s, M⟩` is shorter and the motive is
  inferred from the goal type. This pattern works whenever the
  motive is a single-quotient-argument equality.

- **`s + 0` HOMOGENEOUS vs `0 + s` HETEROGENEOUS asymmetry, again.**
  This came up earlier in cycle 210's `compose_assoc` HEq plumbing.
  Lean 4's `Nat.add` recurses on the second argument, so `s + 0`
  unfolds to `s` (defeq) but `0 + s` requires `Nat.zero_add` (not
  defeq). For `compose_id_equivalent` this is invisible; for
  `id_compose_equivalent` the heterogeneous signature is unavoidable
  but the proof body never inspects the stage count, so the
  asymmetry costs nothing.

- **`Quotient.lift₂_mk` reduction is implicit in `show` + apply
  pattern.** Cycle 218 used `rfl` directly after `composeQ ⟦p⟧ ⟦q⟧
  = ⟦⟨p.1+q.1, p.2.compose q.2⟩⟧`. Cycle 219's P5 uses `show
  Quotient.mk _ _ = Quotient.mk _ _` followed by `exact Quotient.sound
  ...` — the `show` collapses the `composeQ ⟦⟨0, id⟩⟧ ⟦⟨s, M⟩⟧` LHS to
  `Quotient.mk _ ⟨0+s, id.compose M⟩` definitionally, and the
  `Quotient.mk` form on both sides lets `Quotient.sound` fire.

- **The §382 group identity is exactly one cycle of work.** P1–P6
  shipped in the "strong cycle" outcome from the strategy's
  minimum-viable threshold. This validates the cycle 218 outlook
  that identity → inverse → associativity is a tractable 3-cycle
  sequence, with `Group` instance bookkeeping as cycle 222+.

## Suggested next approach

**Cycle 220 — §382 inverse element.** Per cycle 218 + cycle 219
outlooks, the next deliverable is Butcher's §382 inverse-method
construction. Distinct cycle with its own pre-flight scoping:

1. Read Butcher §382's inverse-construction formula carefully (the
   textbook transforms `(c, A, b)` non-trivially; the formula is in
   the §382 narrative around equations 382h or 382i).
2. Implement `RKTableau.inverse : RKTableau s → RKTableau s` (or
   perhaps `RKTableau s → RKTableau s'` if stage count changes).
3. Prove `compose_inverse_equivalent : M.compose M.inverse ≡ id`
   and `inverse_compose_equivalent : M.inverse.compose M ≡ id`
   at the `Equivalent` level.
4. Lift to `composeQ` via `Quotient.inductionOn` + `Quotient.sound`,
   mirroring cycle 219's P5 pattern.

**Cycle 221+ — §382 associativity.** Per cycle 218's `compose_assoc`
outlook (now cycle 219's update to `compose_assoc_HEq_plumbing.md`):
the on-the-nose `RKTableau`-level `compose_assoc` HEq blocker is
finessable via `Quotient.sound` on an `Equivalent`-level
`compose_assoc` claim. Cycle 221+ ships:

1. `compose_equivalent_compose_assoc : @Equivalent (s₁ + (s₂ + s₃))
   ((s₁ + s₂) + s₃) (M₁.compose (M₂.compose M₃))
   ((M₁.compose M₂).compose M₃)` — proved at the abstract
   `IsRKOneStep` level (same technique as cycle 217's heterogeneous
   `compose_equivalent_compose`).
2. `composeQ_assoc : composeQ (composeQ p q) r = composeQ p (composeQ
   q r)` via `Quotient.inductionOn₃` + `Quotient.sound`.

**Cycle 222+ — `instance : Group (Quotient Equivalent.setoidSigma)`.**
Pure bookkeeping once identity (cycle 219), inverse (cycle 220), and
associativity (cycle 221+) are in place. Mathlib's `Group` typeclass
requires `mul`, `mul_assoc`, `one`, `one_mul`, `mul_one`, `inv`,
`mul_left_inv` — all available from the cycle 219–221 deliverables.

GPFS recovery for §441 Phase C.2 remains tracked separately (36
consecutive timeouts since cycle 184). Do not pivot to §441 unless
GPFS smoke test passes; otherwise stay on the §382 group track,
which has 3+ cycles of clearly-bounded, axiom-clean deliverables
remaining.
