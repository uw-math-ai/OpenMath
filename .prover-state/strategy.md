# Cycle 218 Strategy — `composeQ` via `Quotient.lift₂` (§382 quotient lift)

## §A. Status entering cycle 218

- **Sorry count: 0** across the repo. No regressions to clean up.
- **No pending Aristotle results.** Nothing to incorporate.
- **No active blockers** flagged in `.prover-state/issues/` for the
  §382 track.
- Cycle 217 shipped the heterogeneous-stage (382g) form
  `RKTableau.compose_equivalent_compose` (axiom-clean,
  `[propext, Classical.choice, Quot.sound]`). The body is
  byte-for-byte the cycle 216 body, working at the abstract `N`
  level via cycle 214's `compose_isRKOneStep_iff` applied
  independently on each side.
- Cycle 212 shipped `RKTableau.Equivalent.setoidSigma : Setoid (Σ s : ℕ,
  RKTableau s)`, the heterogeneous Σ-typed setoid (axiom-clean).
- **§441 Phase C.2 is GPFS-blocked** (34 consecutive timeouts since
  cycle 184). Per the long-standing remediation: **skip Phase C.2
  this cycle**, do not attempt the cycle 182 draft compile, no smoke
  test on `OpenMath/Chapter4/Section441.lean`. The cluster pathology
  is loop-maintainer territory (see
  `.prover-state/issues/cycle_182_gpfs_slowness.md`).

## §B. Cycle 218 target: `composeQ` (bracketed (382f) form)

**Ship `RKTableau.composeQ` via `Quotient.lift₂` on cycle 212's
`Equivalent.setoidSigma`**, plus a corollary capturing the bracketed
(382f) form `[m₁·m₂] = [m̂₁·m̂₂]` from `thm:382A`.

This is the natural cycle-218 continuation pre-scoped in the cycle
217 task results §"Suggested next approach" and in
`.prover-state/issues/thm_382A_path.md` (Cycle 217 update section).
The mathematical content of thm:382A in the bracketed form is
**one cycle of bridging away**: the respect obligation for
`Quotient.lift₂` is discharged by cycle 217's
`compose_equivalent_compose` applied directly.

### §B.1 P1 deliverable — `composeQ` (~12 LOC)

In `OpenMath/Chapter3/Section381.lean`, in the namespace
`OpenMath.Chapter3.Section312.RKTableau`, immediately after cycle
212's `Equivalent.setoidSigma` (around line 1928) or after cycle 217's
`compose_equivalent_compose` example block (around line 2860 —
**use the latter** since it co-locates the operation with its
respect-obligation discharger):

```lean
/-- The composition operation `compose` lifted to equivalence classes of
Runge–Kutta tableaux on the heterogeneous Σ-typed setoid (cycle 212's
`Equivalent.setoidSigma`). Well-defined by cycle 217's
`compose_equivalent_compose` (heterogeneous-stage (382g) form of
thm:382A): the respect obligation reduces to that theorem applied to
the destructured Σ-pair relation.

This is the bracketed (382f) form's underlying operation —
`[m₁·m₂] = composeQ ⟦m₁⟧ ⟦m₂⟧`. -/
noncomputable def composeQ :
    Quotient Equivalent.setoidSigma →
    Quotient Equivalent.setoidSigma →
    Quotient Equivalent.setoidSigma :=
  Quotient.lift₂
    (fun p q => Quotient.mk Equivalent.setoidSigma ⟨p.1 + q.1, p.2.compose q.2⟩)
    (by
      rintro ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ ⟨s₁', M₁'⟩ ⟨s₂', M₂'⟩ hEq₁ hEq₂
      apply Quotient.sound
      exact compose_equivalent_compose M₁ M₁' M₂ M₂' hEq₁ hEq₂)
```

Estimated 8–15 LOC including docstring.

### §B.2 P2 deliverables — non-vacuity examples (~12 LOC)

Right after `composeQ`, two examples in `namespace OpenMath.Chapter3.Section381`
(or kept in the `RKTableau` namespace if the dot-notation reads
cleaner — pick whichever lets `paddedEuler` resolve unqualified):

**W1** (homogeneous): `composeQ` on two reflexive `⟦⟨2, paddedEuler⟩⟧`
yields `⟦⟨4, paddedEuler.compose paddedEuler⟩⟧`:

```lean
example :
    RKTableau.composeQ
      (Quotient.mk RKTableau.Equivalent.setoidSigma ⟨2, paddedEuler⟩)
      (Quotient.mk RKTableau.Equivalent.setoidSigma ⟨2, paddedEuler⟩) =
    Quotient.mk RKTableau.Equivalent.setoidSigma
      ⟨2 + 2, paddedEuler.compose paddedEuler⟩ :=
  rfl
```

If `rfl` fails (likely under a `noncomputable def` that uses
`Quotient.lift₂` — Lean should still recognise the definitional
unfolding through `Quotient.lift_mk` reduction), fall back to:

```lean
example : ... := by
  rw [RKTableau.composeQ]
  rfl
```

or use `Quotient.lift_mk` / `Quotient.lift₂_mk` explicitly. Try `rfl`
first; if it fails, follow Risk-1 mitigation in §C.

**W2** (heterogeneous, the *actually relevant* witness): `composeQ`
identifies the two heterogeneous representatives from cycle 217's
P2 example. Using cycle 208's `paddedEuler_equivalent_pReduced`
twice, the two classes are equal:

```lean
example :
    RKTableau.composeQ
      (Quotient.mk RKTableau.Equivalent.setoidSigma ⟨2, paddedEuler⟩)
      (Quotient.mk RKTableau.Equivalent.setoidSigma ⟨2, paddedEuler⟩) =
    RKTableau.composeQ
      (Quotient.mk RKTableau.Equivalent.setoidSigma
         ⟨1, paddedEuler.pReduced pairPartition⟩)
      (Quotient.mk RKTableau.Equivalent.setoidSigma
         ⟨1, paddedEuler.pReduced pairPartition⟩) := by
  congr 1 <;>
    exact Quotient.sound (show paddedEuler.Equivalent
      (paddedEuler.pReduced pairPartition) from paddedEuler_equivalent_pReduced)
```

If `congr 1` does not peel both arguments cleanly, fall back to two
explicit `rw [Quotient.sound paddedEuler_equivalent_pReduced]` or
construct the equality via `Quotient.sound` directly on the composite
side citing the cycle 217 P2 heterogeneous example.

### §B.3 P3 stretch — bracketed (382f) form corollary (~10 LOC)

Append a corollary stating thm:382A's bracketed form directly:

```lean
/-- *(382f) bracketed form of thm:382A.* If `M₁ ≡ M̂₁` and `M₂ ≡ M̂₂` in
the heterogeneous-stage sense, then their equivalence classes under
composition coincide: `[M₁ · M₂] = [M̂₁ · M̂₂]`. Immediate corollary of
cycle 217's `compose_equivalent_compose` via `Quotient.sound`. -/
theorem composeQ_eq_of_equivalent
    {s₁ s₁' s₂ s₂' : ℕ}
    {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
    {M₂ : RKTableau s₂} {M₂' : RKTableau s₂'}
    (hEq₁ : @Equivalent s₁ s₁' M₁ M₁')
    (hEq₂ : @Equivalent s₂ s₂' M₂ M₂') :
    composeQ
      (Quotient.mk Equivalent.setoidSigma ⟨s₁, M₁⟩)
      (Quotient.mk Equivalent.setoidSigma ⟨s₂, M₂⟩) =
    composeQ
      (Quotient.mk Equivalent.setoidSigma ⟨s₁', M₁'⟩)
      (Quotient.mk Equivalent.setoidSigma ⟨s₂', M₂'⟩) := by
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (compose_equivalent_compose M₁ M₁' M₂ M₂' hEq₁ hEq₂)
```

This is the literal Lean-readable form of Butcher's claim
`[m₁ · m₂] = [m̂₁ · m̂₂]`. **Ship this if P1+P2 land cleanly.**

## §C. Risk register and mitigations

Per the cycle 217 task results, three risks were pre-flagged. Plan
the mitigations *before* coding:

### R1 — `Quotient.lift₂` may need explicit setoid arguments

The strategy's first attempt uses Mathlib's curried form. If Lean
complains about ambiguous source/target setoids, switch to:

```lean
noncomputable def composeQ :
    Quotient Equivalent.setoidSigma →
    Quotient Equivalent.setoidSigma →
    Quotient Equivalent.setoidSigma :=
  @Quotient.lift₂
    (Σ s : ℕ, RKTableau s) (Σ s : ℕ, RKTableau s)
    (Quotient Equivalent.setoidSigma)
    Equivalent.setoidSigma Equivalent.setoidSigma
    (fun p q => Quotient.mk _ ⟨p.1 + q.1, p.2.compose q.2⟩)
    (...)
```

Pre-flight check: run **one** `lean_loogle` query
`Quotient.lift₂` to confirm the Mathlib name and arity. **Limit
loogle/leansearch usage to ≤ 3 queries total this cycle** — search
tools are rate-limited (3/30s) and the cycle 217 work had no
search issues, so this should be sufficient. If the name has
drifted, alternative forms to try: `Quotient.lift_on₂`, `Quotient.map₂`,
or `Quot.lift₂`. The unbundled `Quot` flavour generally does not
need explicit setoid args.

### R2 — `setoidSigma`'s bundled `iseqv` may need `show` reframing

When destructuring `hEq₁ : Equivalent.setoidSigma.r p p'` via
`rintro`, the goal may unfold `Setoid.r` to its bundled form
(an existence statement over `iseqv`) rather than the desired
`Equivalent` predicate. Mitigation: insert a `show
p.2.Equivalent p'.2` after the `rintro` so the goal type becomes
the heterogeneous `Equivalent` predicate cycle 217 expects.

If that fails, the cycle 212 task results (or
`OpenMath/Chapter3/Section381.lean` around the `setoidSigma`
definition) shows the exact `Setoid.r` unfolding shape — match
it.

### R3 — Mathlib API name drift between `Quotient.lift₂` / `.lift_on₂`

Same as R1 mitigation: confirm with a single `lean_local_search` or
`lean_hover_info` on `Quotient.lift₂` early in the cycle, before
writing the body.

### R4 (new) — `noncomputable` requirement

`Quotient.lift₂` produces a `Quotient`-typed value via
`Classical.choice` under the hood; `composeQ` will need to be
declared `noncomputable`. This is already in the §B.1 sketch; do
not drop the keyword.

### R5 (new) — implicit arity on `compose_equivalent_compose`

Cycle 217's signature takes **four implicit `s` parameters** plus
**four explicit `RKTableau` parameters** plus **two explicit
`Equivalent` hypotheses**. In the `rintro` block, pass the four
tableaux explicitly to `compose_equivalent_compose` (do not rely
on Lean to infer them from `hEq₁`/`hEq₂`, since those have implicit
binders too).

## §D. What NOT to attempt this cycle

**Do not** attempt any of the following — each has been ruled out
or pre-scoped as multi-cycle:

- **`Section441.lean` smoke test or Phase C.2 retry.** 34th
  consecutive GPFS timeout precedent. Skip entirely.
- **§382 group axioms (identity, inverse, associativity).** These
  are cycle 219+ work. Cycle 218's deliverable is the `composeQ`
  operation alone; group structure builds on top.
- **`compose_assoc` (HEq plumbing).** Cycle 210 deferred this; see
  `.prover-state/issues/compose_assoc_HEq_plumbing.md`. Cycle 218's
  `composeQ` operation may make `compose_assoc` more tractable
  *eventually* (via `Quotient.sound` on representatives), but that
  is a cycle 219+ exploration, not this cycle's deliverable.
- **`thm:381H` scaffold reintroduction.** Per
  `.prover-state/issues/thm_381H_deferred.md`, scaffold was rolled
  back in cycle 201 to drive sorry count back to 0. Re-introduce
  only when at least one direction is single-cycle closeable.
- **Search-tool spam.** Limit `lean_loogle` / `lean_leansearch` /
  `lean_state_search` to ≤ 3 total queries (rate-limited 3/30s).
  The cycle 217 work needed zero queries; cycle 218's API is
  closely related and should need at most one `Quotient.lift₂`
  name check.
- **Refactoring cycle 217's `compose_equivalent_compose`.** Its
  signature and body are correct; cycle 218 consumes it as a black
  box.
- **`maxHeartbeats` bumps.** Not needed — `Quotient.lift₂` is a
  one-liner.
- **`axiom`/`constant` declarations.** Never.

## §E. Abort thresholds

Hard rules for cycle 218 to remain a clean ship:

1. **Sorry count must remain 0.** If P1 (`composeQ` definition) does
   not compile, do NOT sorry-scaffold it. Roll back to HEAD and
   document the obstruction in a new
   `.prover-state/issues/composeQ_lift_blocker.md` file. The cycle
   then becomes a structural-investigation cycle (analogous to
   cycles 215 / 200) and the deliverable is the issue file plus
   non-vacuity ground work for cycles 219+. Per the supervisor's
   strict "sorry count must not increase" policy.
2. **If P1 lands but P2 (`rfl` examples) fails**, ship P1 + P3
   only. P2 is non-blocking — the `composeQ_eq_of_equivalent`
   corollary is the textbook content; concrete numerical
   reductions on `paddedEuler` are nice-to-have but not load-bearing.
3. **If R1 (search-tool name drift) consumes more than ~15 minutes**
   without resolution, switch to the unbundled `Quot.lift₂` /
   `Quot.mk` API and adapt. The mathematical content is the same.
4. **If the cycle 217 example (line ~2860) does not compile after
   P1 is added** (e.g. due to name resolution conflicts on `composeQ`),
   the issue is cosmetic; rename `composeQ` to `RKTableau.composeQ`
   explicitly at the cycle 217 example call site or move
   `composeQ` to a fresh namespace block.
5. **If any cycle 213/214/216/217 axiom-clean theorem regresses**
   to a non-axiom-clean state (e.g. `sorryAx` reappears), roll back
   the cycle 218 changes and abort. Run `lean_verify` on the four
   landmarks (`compose_of_isRKOneStep`, `compose_isRKOneStep_iff`,
   `compose_equivalent_compose`, `Equivalent.setoidSigma`) as part
   of the verification step.

## §F. Step-by-step execution plan

Linear, ~20 LOC across one file edit:

1. **(5 min) Smoke-check Section381 baseline.** Run
   `lake env lean OpenMath/Chapter3/Section381.lean` once to
   establish baseline rebuild time (~4–7s warm). If it exceeds 30s
   without compilation errors, GPFS may be degrading the §381 line —
   abort the cycle and document. (Section381 has compiled cleanly
   for 32 consecutive cycles, so this is a precaution, not an
   expected failure.)

2. **(2 min) Optional one-shot Mathlib name verification.** If
   uncertain, run `lean_hover_info` on `Quotient.lift₂` at any
   pre-existing usage in the codebase (search via `Grep` first for
   "Quotient.lift" in `OpenMath/` to find call sites), or
   `lean_loogle` with pattern `"Quotient.lift₂"`. Skip this step
   if you remember the API.

3. **(10 min) Write `composeQ` (P1).** Add the definition at
   `OpenMath/Chapter3/Section381.lean` immediately after cycle 217's
   homogeneous + heterogeneous P2 examples (around line 2860 — use
   `Grep` to locate the cycle 217 example). Compile. If a type
   error fires, consult R1/R5 mitigations.

4. **(5 min) Write P2 examples.** Two `example` blocks: W1
   homogeneous via `rfl`, W2 heterogeneous via the cycle 208
   bridge. Compile. If `rfl` fails on W1, use `by simp` or
   `by rw [Quotient.lift₂_mk]` (whichever Mathlib provides for the
   reduction lemma).

5. **(5 min) Write P3 corollary `composeQ_eq_of_equivalent`.**
   The body is `show ...; exact Quotient.sound
   (compose_equivalent_compose ...)`. Compile.

6. **(2 min) Verify axiom-cleanliness.** Run `lean_verify` on:
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ` —
     expect `[propext, Classical.choice, Quot.sound]` (no
     `sorryAx`).
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ_eq_of_equivalent` —
     same expectation.
   - `OpenMath.Chapter3.Section312.RKTableau.compose_equivalent_compose`
     (cycle 217) — expect no regression.
   - `OpenMath.Chapter3.Section312.RKTableau.Equivalent.setoidSigma`
     (cycle 212) — expect no regression.
   - `OpenMath.Chapter3.Section312.RKTableau.compose_isRKOneStep_iff`
     (cycle 214) — expect no regression.

7. **(5 min) Update tracking files.**
   - `extraction/formalization_data/lean_status.json`: bump the
     `thm:382A` row's `note` field to record cycle 218's `composeQ`
     and `composeQ_eq_of_equivalent`. Status stays `partial` if
     bracketed form is the only headline — though arguably this
     cycle CLOSES thm:382A in full (both (382f) bracketed and
     (382g) heterogeneous), in which case bump to `formalized`.
     Read the existing row carefully and follow the convention
     (likely the row uses `formalized` only after every textbook
     form is shipped; with the bracketed corollary in hand
     `formalized` is justified).
   - `plan.md`: extend the `thm:382A` row with a cycle 218 entry
     noting `composeQ` and the (382f) bracketed corollary. If the
     status mark on the row changes (e.g. `[x]` retained from
     cycle 216 — verify by reading the existing row), update
     accordingly.
   - `.prover-state/issues/thm_382A_path.md`: append a "Cycle 218
     update — `composeQ` shipped" section recording the deliverable.
     Note that the path forward is now §382 group axioms
     (identity / inverse / associativity), cycles 219+.
   - `.prover-state/task_results/cycle_218.md`: write the standard
     cycle-results document per CLAUDE.md template (Worked on,
     Approach, Result, Faithfulness check, Dead ends, Discovery,
     Suggested next approach).

8. **(2 min) Commit + push.** Single commit, summary starting
   "Cycle 218 — §382 `RKTableau.composeQ` ...".

Total estimated wall-clock: **~35–40 minutes** of focused work
(under the 1-hour-per-cycle target).

## §G. Outlook for cycles 219+ (do not start this cycle)

With cycle 218's `composeQ` in hand, the natural cycle 219 target
is **§382 group structure**: identity element, inverse element, and
associativity on `Quotient Equivalent.setoidSigma`. Concrete sketch
for the planner of cycle 219:

- **Identity**: the empty 0-stage tableau (or `explicitEuler` —
  check Butcher §382 for the exact identity element; the cycle 030
  `equivalent_explicitEuler_self` witness suggests `explicitEuler`
  is in the trivial class). Show `composeQ ⟦identity⟧ q = q` and
  `composeQ q ⟦identity⟧ = q` for all `q`.
- **Inverse**: Butcher §382's textbook inverse construction
  (negate `b`, transpose `A`? — need to read §382 carefully).
- **Associativity**: this is where cycle 210's deferred
  `compose_assoc` re-enters. With `composeQ` in hand, associativity
  on `Quotient` may be tractable via `Quotient.sound` on a clean
  `Equivalent`-level associativity, even if HEq-on-the-nose
  `compose_assoc` remains stuck.

These are cycle 219+ work; **do not start them this cycle**. Cycle
218 ships `composeQ` and the bracketed corollary, period.
