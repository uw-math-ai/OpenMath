# Cycle 217 strategy — heterogeneous-stage `compose_equivalent_compose`

## §A — Context

Cycle 216 closed the cycle 215 sorry by refactoring `Equivalent` to
uniform-threshold form (`∃ h₀, ∀ y₀, ...`) and shipping the
**fixed-stage** (382g) form of `thm:382A`:

```
theorem compose_equivalent_compose.{u}
    {s₁ s₂ : ℕ}
    (M₁ M₁' : RKTableau s₁) (M₂ M₂' : RKTableau s₂)
    (hEq₁ : @Equivalent.{u} s₁ s₁ M₁ M₁')
    (hEq₂ : @Equivalent.{u} s₂ s₂ M₂ M₂') :
    @Equivalent.{u} (s₁ + s₂) (s₁ + s₂) (M₁.compose M₂) (M₁'.compose M₂')
```

Sorry count 0; axiom-clean. The cycle 216 task results' "Suggested
next approach" identifies the **heterogeneous-stage form** as the
natural cycle 217 deliverable: replace `M₁ M₁' : RKTableau s₁` and
`M₂ M₂' : RKTableau s₂` with `M₁ : RKTableau s₁`,
`M₁' : RKTableau s₁'`, `M₂ : RKTableau s₂`, `M₂' : RKTableau s₂'`
(four distinct stage counts). This is a prerequisite for the
`composeQ` lift via `Quotient.lift₂` on cycle 212's
`Equivalent.setoidSigma` (cycle 218+ work).

**Why this is one cycle of work**: the cycle 216 body operates at
the abstract `N` level (the normed space) and uses
`compose_isRKOneStep_iff` independently on `(M₁, M₂)` and
`(M₁', M₂')`. It never assumes the stage counts on the two sides
match. The proof should port verbatim under a four-stage-counts
signature change.

Read these files before coding:
* `OpenMath/Chapter3/Section381.lean` lines 2677–2729 (the cycle 216
  `compose_equivalent_compose` with full body).
* `OpenMath/Chapter3/Section381.lean` lines 2643–2675 (cycle 214's
  `compose_isRKOneStep_iff` — already shape-polymorphic in `(s₁, s₂)`).
* `OpenMath/Chapter3/Section381.lean` lines 968–986 (`Equivalent`
  definition, cycle 216 uniform-threshold form, heterogeneous-stage
  by design).
* `.prover-state/issues/thm_382A_path.md` (Cycles 217+ outlook section).

§441 Phase C.2: GPFS-blocked for 34+ consecutive cycles; **skip** per
the standing pattern (cf. `.prover-state/issues/cycle_182_gpfs_slowness.md`).

## §B — Priority 1: heterogeneous-stage `compose_equivalent_compose`
(~10 LOC churn, body unchanged)

**Step B.1.** In `OpenMath/Chapter3/Section381.lean`, generalize the
cycle 216 `compose_equivalent_compose` at lines 2708–2729. Replace
the existing theorem with:

```lean
theorem compose_equivalent_compose.{u}
    {s₁ s₁' s₂ s₂' : ℕ}
    (M₁ : RKTableau s₁) (M₁' : RKTableau s₁')
    (M₂ : RKTableau s₂) (M₂' : RKTableau s₂')
    (hEq₁ : @Equivalent.{u} s₁ s₁' M₁ M₁')
    (hEq₂ : @Equivalent.{u} s₂ s₂' M₂ M₂') :
    @Equivalent.{u} (s₁ + s₂) (s₁' + s₂')
      (M₁.compose M₂) (M₁'.compose M₂') := by
  intro N _ _ _ f L hL
  obtain ⟨H₁, hH₁_pos, hEq₁_app⟩ := hEq₁ f L hL
  obtain ⟨H₂, hH₂_pos, hEq₂_app⟩ := hEq₂ f L hL
  refine ⟨min H₁ H₂, lt_min hH₁_pos hH₂_pos, ?_⟩
  intro y₀ H hH_pos hH_le y_final y_final' h_step h_step'
  have hH_le_H₁ : H ≤ H₁ := le_trans hH_le (min_le_left _ _)
  have hH_le_H₂ : H ≤ H₂ := le_trans hH_le (min_le_right _ _)
  obtain ⟨y_mid, h_M₁_step, h_M₂_step⟩ :=
    (compose_isRKOneStep_iff M₁ M₂ f y₀ H y_final).mp h_step
  obtain ⟨y_mid', h_M₁'_step, h_M₂'_step⟩ :=
    (compose_isRKOneStep_iff M₁' M₂' f y₀ H y_final').mp h_step'
  have hmid_eq : y_mid = y_mid' :=
    hEq₁_app y₀ H hH_pos hH_le_H₁ y_mid y_mid' h_M₁_step h_M₁'_step
  rw [hmid_eq] at h_M₂_step
  exact hEq₂_app y_mid' H hH_pos hH_le_H₂ y_final y_final'
    h_M₂_step h_M₂'_step
```

The body is byte-for-byte identical to cycle 216's body. Only the
signature changes (four stage-count parameters instead of two).

Update the docstring (lines 2677–2707):
* Replace "fixed-stage (382g) form" with "heterogeneous-stage (382g)
  form".
* Remove the "Faithfulness note (fixed-stage restriction)" paragraph
  (lines 2703–2707) — the heterogeneous-stage form *is* the faithful
  statement.
* Add a one-line note: "Cycle 217: generalised from fixed-stage
  (`s₁ s₂ : ℕ`) to heterogeneous-stage (`s₁ s₁' s₂ s₂' : ℕ`); body
  unchanged. The proof operates at the abstract `N` level and uses
  `compose_isRKOneStep_iff` independently on each side, so stage-count
  matching is never required."

**Step B.2.** Compile-and-verify:

```
lake env lean OpenMath/Chapter3/Section381.lean
```

Expected: 0 errors, warm rebuild ≤10s. Then via `lean_verify`:

```
OpenMath.Chapter3.Section312.RKTableau.compose_equivalent_compose
```

Expected axioms: `[propext, Classical.choice, Quot.sound]`.

**Step B.3.** Spot-check downstream consumers — the cycle 216
`example` at lines ~2820+ (`paddedEuler.compose paddedEuler ≡
paddedEuler.compose paddedEuler` via `compose_equivalent_compose
paddedEuler paddedEuler paddedEuler paddedEuler …`). This call site
now passes the four `paddedEuler` arguments with the implicit
`s₁ s₁' s₂ s₂'` all unifying to `2` — should work without source
edit because Lean infers the implicit parameters. If it errors, add
the explicit `(s₁ := 2) (s₁' := 2)` annotations.

## §C — Priority 2: heterogeneous-stage non-vacuity (~10 LOC)

The fixed-stage example exercises only the homogeneous case
(both sides `RKTableau 2`). For the heterogeneous-stage form, add
a *new* example immediately after the existing
`paddedEuler.compose paddedEuler ≡ …` example. Use cycle 208's
`paddedEuler_equivalent_pReduced : paddedEuler.Equivalent
(paddedEuler.pReduced pairPartition)` — a genuine heterogeneous-stage
(`s = 2` vs `s' = 1`) `Equivalent` witness.

Place inside `namespace OpenMath.Chapter3.Section381` (where the
existing `paddedEuler` examples live, near line ~2820+). The witness:

```lean
/-- *Non-vacuity for the heterogeneous-stage cycle 217 form of
`compose_equivalent_compose` (`thm:382A` 382g).* Composing
`paddedEuler` (2-stage) with `paddedEuler` (2-stage) is `Equivalent`
to composing `paddedEuler.pReduced pairPartition` (1-stage) with
`paddedEuler.pReduced pairPartition` (1-stage) — a genuinely
heterogeneous-stage assertion (`4 = 2 + 2` on the left, `2 = 1 + 1`
on the right). Routes through cycle 208's
`paddedEuler_equivalent_pReduced` applied twice. -/
example :
    @RKTableau.Equivalent
      (2 + 2) (1 + 1)
      (paddedEuler.compose paddedEuler)
      ((paddedEuler.pReduced pairPartition).compose
        (paddedEuler.pReduced pairPartition)) :=
  RKTableau.compose_equivalent_compose
    paddedEuler (paddedEuler.pReduced pairPartition)
    paddedEuler (paddedEuler.pReduced pairPartition)
    paddedEuler_equivalent_pReduced
    paddedEuler_equivalent_pReduced
```

The explicit `@RKTableau.Equivalent (2 + 2) (1 + 1)` qualification
documents the heterogeneous-stage shape clearly. If Lean accepts a
less-qualified form (e.g. with the stage counts inferred), prefer
that.

## §D — Priority 3 (stretch): scoping doc for `composeQ` lift

If §B and §C land cleanly with cycle budget remaining, **scope** (not
implement) cycle 218's `composeQ` lift. Append a "Cycle 217 update —
heterogeneous form closed" section to
`.prover-state/issues/thm_382A_path.md` documenting:

* The heterogeneous-stage closure (one paragraph).
* The cycle 218 entry point: define
  `composeQ : Quotient setoidSigma → Quotient setoidSigma →
    Quotient setoidSigma` via `Quotient.lift₂` consuming cycle 217's
  heterogeneous `compose_equivalent_compose`. Sketch the
  `Quotient.lift₂`-respect obligation: given
  `⟨s₁, M₁⟩ ≈ ⟨s₁', M₁'⟩` and `⟨s₂, M₂⟩ ≈ ⟨s₂', M₂'⟩` (heterogeneous
  Σ-typed setoid relation), conclude `⟨s₁ + s₂, M₁.compose M₂⟩ ≈
  ⟨s₁' + s₂', M₁'.compose M₂'⟩`. The first two relations unfold to
  heterogeneous `Equivalent` directly; the conclusion is exactly
  cycle 217's theorem.
* Risk: `Quotient.lift₂` over Σ-typed setoid requires the binary
  operation to "respect both arguments"; this is the dependent-stages
  version where the output's first projection is `s₁ + s₂` (depends
  on both inputs). May need `Quotient.hrecOn₂` if standard
  `lift₂` doesn't accept the dependent-output shape. **Flag for
  cycle 218's planner**, don't try to resolve now.

Estimated stretch effort: ~20 minutes of writing if §B+§C close
cleanly. **Do NOT** start the `composeQ` definition this cycle —
that's cycle 218.

**Do NOT** introduce any sorries to ship a partial `composeQ`. The
P1+P2 deliverables alone meet the cycle bar.

## §E — Anticipated risks and mitigations

* **Risk 1: implicit-parameter unification fails on the cycle 216
  example call site.** The cycle 216 example writes
  `compose_equivalent_compose paddedEuler paddedEuler paddedEuler
  paddedEuler paddedEuler_equivalent_self paddedEuler_equivalent_self`.
  Under the new four-stage-count signature, all four `s` parameters
  unify to `2` via the `paddedEuler : RKTableau 2` annotation. If
  Lean still complains, add `(s₁ := 2) (s₁' := 2) (s₂ := 2)
  (s₂' := 2)` named arguments.
* **Risk 2: `compose_isRKOneStep_iff M₁ M₂` and
  `compose_isRKOneStep_iff M₁' M₂'` produce different sum-types.**
  This *can't* matter — each `compose_isRKOneStep_iff` is shape-
  polymorphic in its two `RKTableau` arguments. The two
  `.mp` results land in their respective composite types
  `RKTableau (s₁ + s₂)` and `RKTableau (s₁' + s₂')`. The proof
  threading is the same; only `y_final`/`y_final'` differ. No
  HEq plumbing required.
* **Risk 3: cycle 216 docstring rewrite introduces a stale
  cross-reference.** Audit lines 2677–2707 carefully — the cycle 216
  text mentions "fixed-stage (382g) form" and a faithfulness note
  about the heterogeneous-stage extension being cycle 217+ work.
  Both lines become outdated; rewrite or remove them. Cross-references
  to `compose_equivalent_compose_uniform_threshold.md` and
  `thm_382A_path.md` remain valid.
* **Risk 4: GPFS pathology re-emerges and `lake env lean` times out
  on Section381.lean.** Section381.lean has been compiling healthily
  (warm rebuild ~5–7s) for 33 consecutive cycles. If a timeout
  fires, retry once after killing any zombie processes; if it
  persists, ship via incremental edits and fall back to a single
  smaller deliverable.

None of these risks are blockers. The cycle 216 mechanical-port
methodology applies: the body is identical, so the only failure
modes are signature-related.

## §F — What NOT to try

* **Do NOT** revert cycle 216's refactor. The uniform-threshold form
  is essential and is the proof's enabling condition.
* **Do NOT** add `HEq` plumbing or `Fin.cast` machinery. The cycle 217
  proof has no stage-count arithmetic — it's all `Equivalent`
  composition at the abstract `N` level.
* **Do NOT** attempt the `composeQ` definition or its `Quotient.lift₂`
  body. That's cycle 218 work; scoping doc only.
* **Do NOT** introduce sorries. The §B body is byte-for-byte cycle
  216's body; either it ports cleanly or there is a Lean elaboration
  issue (which should be a one-line fix, not a sorry).
* **Do NOT** rename `RKTableau.compose_equivalent_compose` to a new
  name like `compose_equivalent_compose_hetero`. The existing name
  is the right name for the (382g) form regardless of stage shape;
  generalising in place is faithful to the textbook signature.
* **Do NOT** attempt §441 Phase C.2 verification. 34+ GPFS-blocked
  consecutive cycles; pivot territory remains active.
* **Do NOT** spawn agents or batch Aristotle for this cycle — the
  body is mechanical and Aristotle's premise-search is unhelpful
  for signature-only generalizations.

## §G — Success criteria

1. Sorry count stays at 0 across the repo.
2. `compose_equivalent_compose` has the four-stage-count signature
   shown in §B.1.
3. `lean_verify` on
   `OpenMath.Chapter3.Section312.RKTableau.compose_equivalent_compose`
   returns `[propext, Classical.choice, Quot.sound]`.
4. The §C heterogeneous-stage example compiles.
5. `lean_verify` re-confirms cycle 214's `compose_isRKOneStep_iff`
   and cycle 213's `compose_of_isRKOneStep` are still axiom-clean
   (no regressions).
6. Section381.lean warm rebuild ≤10s.
7. Update `plan.md` thm:382A row: extend the existing cycle 216
   entry with "Cycle 217: heterogeneous-stage (382g) form
   (`{s₁ s₁' s₂ s₂' : ℕ}`) shipped; body unchanged from cycle 216,
   only the signature generalised. Axiom-clean.".
8. Update `lean_status.json` thm:382A row: bump cycle reference to
   217; note that the heterogeneous-stage form (382g) is now
   formalised. The bracketed (382f) form `[m₁·m₂] = [m̂₁·m̂₂]`
   still awaits the `composeQ` Quotient lift (cycle 218+).
9. Write `.prover-state/task_results/cycle_217.md` documenting the
   port methodology (was it as mechanical as predicted?), any minor
   surprises, and the cycle 218 entry point.

## §H — Abort threshold

If the §B body fails to compile and the fix requires more than a
one-line change (e.g. a tactic doesn't fire, or the
`compose_isRKOneStep_iff` call doesn't elaborate against the
heterogeneous shape), **abort and revert** to cycle 216 HEAD —
the worker has 30 minutes to diagnose the issue and produce a
1-2-line fix; beyond that, the assumption of "mechanical port"
is wrong and a fresh planning cycle is needed. Do NOT ship a
sorry-scaffolded heterogeneous version; that re-introduces the
cycle 215 issue.

If §B closes but §C fails (e.g. `paddedEuler_equivalent_pReduced`
can't be threaded through `compose_equivalent_compose` because of
an implicit-argument issue), ship §B alone and defer §C to cycle 218
alongside the `composeQ` work.

## §I — Time budget

* §B (P1): ~30 minutes (10 LOC signature change + body verbatim
  port + docstring rewrite + compile + lean_verify).
* §C (P2): ~15 minutes (10 LOC heterogeneous-stage example +
  compile).
* §D (P3 stretch): ~15 minutes if shipping (markdown only,
  documentation update to `thm_382A_path.md`).
* Total: ~1 hour for P1+P2; ~75 minutes with P3.

If §B alone consumes >45 minutes, the mechanical-port assumption
has failed and §H abort threshold should fire. The cycle 216
budget came in well under 1 hour, suggesting this cycle should
too.
