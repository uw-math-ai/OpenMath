# Cycle 223 Strategy — PhiEquivalent setoid infrastructure (§383 group-homomorphism path, Phase 1)

## §A. Status snapshot

- **Sorry count: 0.** All commits clean since the cycle 201 rollback.
- **§382 group story COMPLETE**: cycles 219/220/221/222 closed the four
  axioms; `instance : Group (Quotient Equivalent.setoidSigma)` ships
  at `Section381.lean:3270` axiom-clean.
- **§441 Phase C.2 GPFS-blocked**: 39 consecutive timeouts (cycles
  182–222). **Skip the Section441.lean smoke test entirely this cycle.**
  Continue to log the timeout in `cycle_182_gpfs_slowness.md` only if
  the supervisor demands it; otherwise pivot directly to §C P1 below.
  The pathology has been pure cluster-side GPFS load for 41 days;
  further worker-side attempts are wasted compute.
- **No pending Aristotle results.** No jobs submitted in cycle 222.
- **PhiEquivalent already has refl/symm/trans** at
  `Section381.lean:129/133/139` (cycle 030 era, proven via trivial
  `Eq` properties). This is the load-bearing input for the cycle 223
  setoid construction below.

## §B. Where to focus

The cycle 222 task results' "Suggested next approach" identifies the
§383 group-homomorphism path as cycle 223 P1. The first concrete
deliverable on that path is **setoid infrastructure for
`PhiEquivalent`** — the PhiEquivalent analog of cycles 211/212's
`Equivalent.setoid` and `Equivalent.setoidSigma`. This is a clean,
low-risk single-cycle target.

## §C. Priorities (linear execution per §F)

### P1 — `PhiEquivalent.setoid.{u}` (fixed-stage setoid instance)

Ship in `OpenMath/Chapter3/Section381.lean`, immediately AFTER cycle
211's `Equivalent.setoid` at line 1914. Roughly ~18 LOC. The
signature mirrors `Equivalent.setoid` line-by-line:

```lean
/-- *Setoid instance on fixed-stage `RKTableau s` for def:381B.*
Combines `PhiEquivalent.refl`, `PhiEquivalent.symm`, `PhiEquivalent.trans`
(all cycle 030 era, lines 129–142) into the standard Mathlib `Setoid`
typeclass, enabling `Quotient (RKTableau.PhiEquivalent.setoid s)` as
the natural ambient type for fixed-stage Φ-equivalence classes of
Runge–Kutta methods. Companion to cycle 211's `Equivalent.setoid` —
the §382 group lives on `Equivalent`-quotients; PhiEquivalent quotients
will be the codomain of the §383+ group homomorphism `Φ`. -/
instance PhiEquivalent.setoid.{u} (s : ℕ) : Setoid (RKTableau s) where
  r M M' := PhiEquivalent M M'
  iseqv := ⟨PhiEquivalent.refl, PhiEquivalent.symm, PhiEquivalent.trans⟩
```

Note: PhiEquivalent is **NOT universe-polymorphic** (unlike cycle 206's
`Equivalent`, whose internal `∀ {N : Type*}` introduces a universe
variable). PhiEquivalent's body quantifies over `RootedTree`, not over
external types, so the `.{u}` annotation is **cosmetic only**. Use
`.{u}` for visual parity with cycle 211/212; if Lean complains about
an unused universe variable (R1 in §G), drop the annotation.

**Non-vacuity P1.E1** (~3 LOC, immediately after the P1 instance):

```lean
example : @Setoid.r _ (RKTableau.PhiEquivalent.setoid 2) paddedEuler
    paddedEuler := PhiEquivalent.refl paddedEuler
```

### P2 — `PhiEquivalent.setoidSigma.{u}` (heterogeneous Σ-typed setoid)

Ship immediately after P1.E1, mirroring cycle 212's `Equivalent.setoidSigma`
construction (line 1930). Roughly ~12 LOC body + ~10 LOC docstring:

```lean
/-- *Heterogeneous Σ-typed setoid for def:381B `PhiEquivalent`.*
Companion to cycle 223's `PhiEquivalent.setoid s` (fixed-stage): this
Σ-typed variant is needed for the §383+ Φ-quotient
`Quotient PhiEquivalent.setoidSigma`, which will be the codomain of
the (eventual) group homomorphism from cycle 222's
`Quotient Equivalent.setoidSigma`. Two methods with *different* stage
counts may live in the same Φ-equivalence class because PhiEquivalent
is itself heterogeneous-stage (def:381B's `∀ t, derivativeWeight M t =
derivativeWeight M' t` doesn't compare stage counts directly). -/
instance PhiEquivalent.setoidSigma.{u} : Setoid (Σ s : ℕ, RKTableau s) where
  r p q := @PhiEquivalent p.1 q.1 p.2 q.2
  iseqv :=
    ⟨fun p => PhiEquivalent.refl p.2,
     fun {p q} h => PhiEquivalent.symm h,
     fun {p q r} h₁ h₂ => PhiEquivalent.trans h₁ h₂⟩
```

**Non-vacuity P2.E1** (homogeneous, ~3 LOC):

```lean
example : @Setoid.r _ RKTableau.PhiEquivalent.setoidSigma
    ⟨2, paddedEuler⟩ ⟨2, paddedEuler⟩ := PhiEquivalent.refl paddedEuler
```

**Non-vacuity P2.E2** (heterogeneous, ~5 LOC, consumes cycle 187's
`pReduced_phiEquivalent`):

```lean
example : @Setoid.r _ RKTableau.PhiEquivalent.setoidSigma
    ⟨2, paddedEuler⟩ ⟨1, paddedEuler.pReduced pairPartition⟩ :=
  pReduced_phiEquivalent paddedEuler
    paddedEuler_isPReducibleVia_pairPartition
```

**CAVEAT**: verify the exact name `paddedEuler_isPReducibleVia_pairPartition`
exists at the expected line — cycle 186 promoted it from an inline
example to a public theorem. Run
`grep -n "paddedEuler_isPReducibleVia"
OpenMath/Chapter3/Section381.lean` first; adjust the call if the
name is slightly different (e.g. `paddedEuler_isPReducibleVia_pair`
or similar). The `pairPartition` symbol must also be in scope —
verify with `grep -n "def pairPartition\|noncomputable def pairPartition"`.

**Non-vacuity P2.E3** (`Quotient.mk` well-formedness, ~5 LOC, mirrors
cycle 212's W3 witness):

```lean
example :
    @Quotient.mk _ RKTableau.PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩
      = @Quotient.mk _ RKTableau.PhiEquivalent.setoidSigma
          ⟨1, paddedEuler.pReduced pairPartition⟩ :=
  Quotient.sound (pReduced_phiEquivalent paddedEuler
    paddedEuler_isPReducibleVia_pairPartition)
```

### P3 (STRETCH — only if P1 + P2 land cleanly in < 40 min)

**`compose_phiEquivalent_compose`** — heterogeneous-stage well-definedness
for the future `composeQ_phi` lift on `Quotient PhiEquivalent.setoidSigma`.
Analog of cycle 217's `compose_equivalent_compose`. Place immediately
after `composeQ_eq_of_equivalent` (~line 2820 area):

```lean
/-- *Heterogeneous-stage well-definedness of `compose` on
`PhiEquivalent`.* If `M₁ ≡_Φ M̂₁` and `M₂ ≡_Φ M̂₂` then
`M₁.compose M₂ ≡_Φ M̂₁.compose M̂₂`. Respect obligation for the
(cycle 224+) `composeQ_phi : Quotient PhiEquivalent.setoidSigma →
... → ...` operation via `Quotient.lift₂`. Analog of cycle 217's
`compose_equivalent_compose`. -/
theorem compose_phiEquivalent_compose
    {s₁ s₁' s₂ s₂' : ℕ}
    (M₁ : RKTableau s₁) (M₁' : RKTableau s₁')
    (M₂ : RKTableau s₂) (M₂' : RKTableau s₂')
    (hEq₁ : PhiEquivalent M₁ M₁')
    (hEq₂ : PhiEquivalent M₂ M₂') :
    PhiEquivalent (M₁.compose M₂) (M₁'.compose M₂') := by
  sorry  -- DO NOT SHIP — see §D point 1.
```

**WARNING ON P3:** the body of `compose_phiEquivalent_compose` is
**NOT a trivial port of cycle 217**. Cycle 217 worked at the abstract
`IsRKOneStep` level (using cycle 214's `compose_isRKOneStep_iff` to
factor composite one-steps). PhiEquivalent is defined via
`derivativeWeight`, a recursive function over `RootedTree` with a
*different* structural recursion. The proof likely requires tracking
how `derivativeWeight (M₁.compose M₂) t` unfolds across the block
decomposition of compose's `A`/`b`/`c` fields — non-trivial.

**If you cannot identify a clear ≤ 50-LOC proof path inside 10
minutes of inspection of cycle 187's `derivativeWeight_pReduced`
(line ~1251) and `derivativeWeightProd_pReduced` (private mutual
helper), ABORT P3 entirely.** Do NOT ship P3 as a `sorry`-scaffold
— sorry count 0 → 1 triggers the supervisor's "sorry-increase"
deduction (cycle 215 was scored −2, cycle 200 was scored −2 for
the same reason). The cycle's clean state matters more than P3
progress. Defer the entire `compose_phiEquivalent_compose`
deliverable to cycle 224 if uncertain.

## §D. What NOT to try

1. **Do NOT ship P3 as a `sorry`-scaffold.** Cycles 200 and 215 both
   scored −2 for sorry count rising 0 → 1 (or 0 → 3). The supervisor
   strictly penalises sorry-increase. P3 ships only if the body
   compiles cleanly; otherwise it is deferred to cycle 224. Cycle
   223's clean-state ship of P1 + P2 alone is a substantive single-
   cycle deliverable.

2. **Do NOT attempt the body of `compose_phiEquivalent_compose`
   speculatively.** Cycle 217's recipe (route through
   `compose_isRKOneStep_iff` + abstract-`N`-level uniqueness) does
   not transfer cleanly because PhiEquivalent operates at the
   `derivativeWeight` / rooted-tree level, not the `IsRKOneStep` /
   normed-space level. The two proofs share only the high-level
   block-decomposition pattern, not the tactical recipe. If you
   identify a ≤ 50-LOC path, ship it; otherwise defer.

3. **Do NOT introduce `composeQ_phi` or the `Group` instance on
   `Quotient PhiEquivalent.setoidSigma` in cycle 223.** Those are
   cycle 224 (composeQ_phi + composeQ_phi well-definedness +
   id_left/right) and cycle 225 (Group instance via
   `Group.ofLeftAxioms`) deliverables. Cycle 223's job is the
   setoid foundation only.

4. **Do NOT attempt thm:381G or thm:381H this cycle.** Per the cycle
   222 task results' option 3, both would benefit from the §382 group
   but are multi-cycle commitments requiring `thm:314A` (unformalized)
   and the combine-two-tableaux construction (~50–100 LOC of new
   infrastructure). Pick them up after the §383 group-homomorphism
   path lands (cycles 226+).

5. **Do NOT attempt the Section441.lean smoke test.** 39 consecutive
   GPFS timeouts establish the pathology; further worker-side compile
   attempts are wasted compute. The pathology is cluster-side, not
   code-side.

6. **Do NOT modify `scripts/autonomous_loop.py` or any loop
   infrastructure.** Per CLAUDE.md and the standing
   `phantom_commit_verdict_pattern.md` issue.

7. **Do NOT raise `maxHeartbeats` or `set_option` anything globally.**
   Setoid definitions are elaboration-light; default heartbeats
   suffice.

8. **Do NOT introduce `axiom` or `constant` declarations** — even
   speculatively for P3. Sorry-first is allowed for clearly-scoped
   future deferrals (but not in cycle 223 per point 1); `axiom` is
   never.

9. **Do NOT cherry-pick easier entities outside the §380-§383
   trajectory.** The cycle 222 task results explicitly identified
   the §383 group-homomorphism path as the next pivot; cycle 223's
   P1/P2 are the foundation for that path. Pivoting to e.g.
   `lem:342A` or `thm:302C` would interrupt momentum.

## §E. Faithfulness check (run BEFORE commit)

For each of P1, P2, (and P3 if shipped):

- **`PhiEquivalent.setoid`**: textbook reference is def:381B (Butcher
  §380, "Φ-equivalent"). The setoid just packages refl/symm/trans
  into Mathlib's typeclass; **no definition smuggling**. No new
  content vs. cycle 030's PhiEquivalent definition. Pure typeclass
  packaging.

- **`PhiEquivalent.setoidSigma`**: companion to cycle 212's
  `Equivalent.setoidSigma`. **No textbook entity directly**; this is
  supplementary infrastructure for the §383 quotient path. Document
  the supplementary nature in the docstring (similar to cycle 212's
  pattern).

- **`compose_phiEquivalent_compose`** (P3 IF shipped): respect
  obligation for the future `composeQ_phi`. Textbook reference is
  implicit in §383's claim that Φ is a (group) homomorphism — the
  multiplicativity `Φ_{m₁ · m₂} = Φ_{m₁} * Φ_{m₂}` in Butcher §383
  is the analog at the forest-convolution level; the *quotient*
  analog is this well-definedness theorem.

Run `lean_verify` on the new instances:
- `OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoid`
- `OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma`

Both should return `[propext, Classical.choice, Quot.sound]` (the
standard trio embedded in PhiEquivalent's `Eq`-based body — the
same trio as cycle 211/212).

**Regression check**: cycle 222's `instGroup` and earlier landmarks
(`composeQ_eq_of_equivalent`, `compose_isRKOneStep_iff`,
`Equivalent.setoid`, `Equivalent.setoidSigma`) should remain
axiom-clean. Spot-check at least `composeQ_eq_of_equivalent` and
`instGroup` with `lean_verify`.

## §F. Execution order

1. **(2 min)** Read lines 124–148 of Section381.lean to confirm
   `PhiEquivalent` definition + refl/symm/trans signatures match the
   §C.P1 template. Adjust the P1 template if the actual signature
   diverges (e.g. if `PhiEquivalent.trans` takes explicit `s s'
   s''` arguments — in which case use the `fun {p q r} h₁ h₂ =>
   PhiEquivalent.trans h₁ h₂` form per cycle 212's setoidSigma
   pattern).

2. **(3 min)** Verify the exact name `paddedEuler_isPReducibleVia_pairPartition`
   and `pairPartition` exist in Section381.lean. Use `grep -n
   "paddedEuler_isPReducibleVia"` and `grep -n "pairPartition"`. If
   names differ, adjust P2.E2 / P2.E3 accordingly. If `pairPartition`
   is local to an inline example, simplify P2.E2 / P2.E3 to use only
   `paddedEuler_phiEquivalent_self` or similar (the heterogeneous
   non-vacuity is nice-to-have, not load-bearing).

3. **(8 min)** Ship P1 (`PhiEquivalent.setoid` + P1.E1 example).
   Compile via `lake env lean OpenMath/Chapter3/Section381.lean`.
   Expected warm rebuild: ~4–6s (matches cycle 219–222 pattern).
   `lean_verify` on `PhiEquivalent.setoid` — expect
   `[propext, Classical.choice, Quot.sound]`.

4. **(15 min)** Ship P2 (`PhiEquivalent.setoidSigma` + P2.E1 + P2.E2
   + P2.E3 examples). Compile + `lean_verify` on the two new
   instances. Spot-check `composeQ_eq_of_equivalent` and `instGroup`
   axioms remain `[propext, Classical.choice, Quot.sound]`.

5. **(5 min ABORT-OR-PROCEED CHECKPOINT)** If P1 + P2 took ≤ 30 min
   AND you can identify a clear ≤ 50-LOC closure path for
   `compose_phiEquivalent_compose` from inspecting
   `derivativeWeight_pReduced`'s proof structure (cycle 187 era),
   proceed to P3. Otherwise, ABORT P3 entirely (do NOT
   sorry-scaffold; the clean state matters more than P3 progress).

6. **(if P3 proceeds, ≤ 30 min)** Ship P3 with a fully-proved body
   (no sorry). Compile + `lean_verify`. **If proof stalls past 25
   minutes, REVERT the P3 attempt entirely** and commit P1 + P2
   only.

7. **(5 min)** Optionally update `extraction/formalization_data/lean_status.json`
   if a row for def:381B benefits from the new setoid reference; do
   so only if cleanly possible. `plan.md` typically does not need
   changes for setoid-only deliverables; leave it untouched unless
   the def:381B row's note can be tightened.

8. **(5 min)** Write `.prover-state/task_results/cycle_223.md`
   per the template in CLAUDE.md. Document:
   - Worked on: PhiEquivalent setoid infrastructure (P1 + P2 [+ P3]).
   - Approach: cycle 211/212 templates ported to PhiEquivalent.
   - Result: SUCCESS, axiom-clean, sorry count remains 0.
   - Faithfulness: setoid packaging only; no new textbook content.
   - Discovery: any R1–R5 hiccups encountered (universe annotation,
     witness naming, etc.).
   - Suggested next approach: cycle 224 should ship
     `compose_phiEquivalent_compose` (if not shipped in P3) +
     `composeQ_phi` + `composeQ_phi_id_left`/`_right` (PhiEquivalent
     analogs of cycle 218's `composeQ` + cycle 219's identity laws).

9. **(2 min)** Commit + push. Use a commit message in the cycle
   222/221/220-style with a concise summary in the first line.

## §G. Anticipated risks

- **R1 — universe annotation drift.** `PhiEquivalent` does NOT have
  an internal `∀ {N : Type*}` (unlike `Equivalent` cycle 206), so the
  `.{u}` annotation is cosmetic. If Lean complains about an unused
  universe variable, drop the `.{u}` from both setoid declarations.
  One-character fix, < 30 seconds.

- **R2 — `PhiEquivalent.trans` argument order.** Cycle 030's
  `PhiEquivalent.trans` signature at line 139 takes `{s s' s''}`
  with method args `{M : RKTableau s} {M' : RKTableau s'}
  {M'' : RKTableau s''}` per the snippet above. When packaging into
  `iseqv`, the eta-expanded form `fun {p q r} h₁ h₂ =>
  PhiEquivalent.trans h₁ h₂` should work. If `PhiEquivalent.trans`
  takes implicit args that don't unify, supply them explicitly
  (cycle 212's setoidSigma pattern).

- **R3 — `paddedEuler_isPReducibleVia_pairPartition` may not exist
  under that exact name.** Per §F.2, verify with grep before
  writing P2.E2. If the exact name doesn't match, alternatives:
  - Use `paddedEuler_pReducesTo_pReduced` (cycle 186) and route
    through cycle 187's `PReducesTo.toPhiEquivalent`.
  - Use `paddedEuler_phiEquivalent_zeroReduced` (line 2215, cycle 188)
    which already establishes a heterogeneous PhiEquivalent witness
    in a different form.
  - Drop the heterogeneous P2.E2 / P2.E3 examples entirely and ship
    only P2.E1 (homogeneous). The non-vacuity quality suffers
    slightly but the setoid still has exercised refl.

- **R4 — `pairPartition` scope.** If `pairPartition` is local to an
  inline example, derive a partition inline or use a different
  reduction witness (see R3 alternatives).

- **R5 — `Quotient.sound` may need explicit setoid annotation in
  P2.E3.** Cycle 212 used `@Quotient.mk _ RKTableau.Equivalent.setoidSigma`
  with explicit instance argument; mirror for PhiEquivalent. If
  underscore-inferred setoid fails, supply explicitly.

- **R6 — P3 body genuinely is multi-cycle.** Per §C and §D, ABORT
  P3 at the first sign of difficulty. The cycle's core deliverable
  (P1 + P2) is independent of P3.

- **R7 — namespace drift.** `PhiEquivalent` lives inside
  `namespace OpenMath.Chapter3.Section312.RKTableau` (the parent
  namespace of all the §380 work). Place the new setoid declarations
  inside the same namespace block as `Equivalent.setoid` /
  `Equivalent.setoidSigma`. Verify with `grep -B 5 "instance
  Equivalent.setoid"` to find the namespace context.

## §H. LOC budget

- P1: ~18 LOC (instance + example + docstring).
- P2: ~25 LOC (instance + 3 examples + docstring).
- P3 (if shipped): ~50 LOC body + ~10 LOC docstring.

Total P1 + P2: ~45 LOC. Total with P3: ~105 LOC. Both well below
cycle 222's delivery size (~150 LOC), which closed cleanly.

## §I. Why this cycle plan is right

1. **Topo-sort priority.** §383's group-homomorphism path is the
   natural continuation after cycle 222's §382 group. PhiEquivalent
   setoid is the prerequisite for the (cycle 224+) `composeQ_phi`
   lift, which is the prerequisite for the (cycle 225+) Group
   instance on `Quotient PhiEquivalent.setoidSigma`, which is the
   prerequisite for the (cycle 226+) GroupHom from
   `Quotient Equivalent.setoidSigma` to
   `Quotient PhiEquivalent.setoidSigma`. That GroupHom is the
   textbook content of `thm:384A` ("A homomorphism between two
   groups", currently `[ ]` in plan.md).

2. **Low risk.** Cycles 211/212 are exact templates; the port to
   PhiEquivalent is a substitution exercise. R1–R7 in §G are minor
   cosmetic hiccups, not blockers.

3. **Independent of GPFS pathology.** Section381.lean compiles
   healthily (cycle 222 warm rebuild 9.657s, well under 10s).
   Section441.lean GPFS issues do not affect this cycle.

4. **Mathematical content.** PhiEquivalent's setoid form unlocks
   reasoning about Φ-equivalence classes as a quotient type — a step
   Butcher's §383 takes implicitly when stating "the Φ-equivalence
   classes form an algebraic structure". The new setoid instances
   are our formal record of that step.

5. **Continuity with prior cycles.** Cycle 222's task results
   explicitly recommend the §383 path. Cycle 223 = first concrete
   step on that path.

---

**Bottom line:** P1 + P2 are the safe bet. P3 is a stretch — only
ship if the proof body is obviously tractable. The cycle's success
criterion is **sorry count remains 0** with `PhiEquivalent.setoid`
and `PhiEquivalent.setoidSigma` both axiom-clean and exercised by
non-vacuity witnesses.
