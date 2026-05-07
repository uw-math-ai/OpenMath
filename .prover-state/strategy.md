# Cycle 188 Strategy

## Status snapshot

* HEAD: `75e5797` "Cycle 187 — §380 PhiEquivalent.of_pReducesTo
  (P-reduction ⇒ Φ-equivalence); §441 Phase C.2 GPFS-blocked (7th)"
* Sorry count: **0** project-wide.
* §441 Phase C.2 has been GPFS-blocked for **seven consecutive
  cycles** (cycles 182–187). The cycle 182 proof draft is preserved
  at `.prover-state/cycle_182_draft_section441.lean` with the cycle
  184 namespace fix (line 1529) recorded in
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.
* No pending Aristotle results (cycle 184 polled
  `7c4d0ffb-…` to COMPLETE_WITH_ERRORS; the namespace fix is already
  extracted; further submissions are paused per cycle 187 strategy).

## CRITICAL — ignore the "stuck on" framing in the prompt

The cycle 188 prompt's "What I'm stuck on" framing — about the
factor-of-2 between `a₁ = 2·ρ'(1)` and Butcher's stated `ρ'(1) = a₁`
— is a **stale `attempts.md` carry-over from cycle 174**, not an
open blocker. It was diagnosed as a Butcher textbook typo
(p. 376) by:

* The cycle 174 consultant note
  (`.prover-state/issues/consultant_advice_cycle_174.md` §A) — full
  algebraic re-derivation + numerical sanity checks on explicit
  Euler (`a₁ = 2`, `ρ'(1) = 1`) and BDF2 (`a₁ = 4/3`, `ρ'(1) = 2/3`).
* The cycle 180 consultant note
  (`.prover-state/issues/consultant_advice_cycle_180.md`) — re-
  verification + escalation that this phantom keeps propagating.

**Phase B of `lem:441A` is fully closed at HEAD** (cycle 179 headline
at `OpenMath/Chapter4/Section441.lean:913`,
`aPoly_coeff_one_pos_of_stable_preconsistent`, axiom-clean). DO NOT
audit the cycle 174 chain. DO NOT redirect the proof strategy. The
chain `a₁ = −2α'(1)` → `ρ'(1) = −α'(1)` → `a₁ = 2·ρ'(1)` →
`ρ'(1) > 0` → `a₁ > 0` is mathematically faithful and was independently
re-verified by two consultants.

If you need to confirm: run

```
git log -1 --format='%H %s'
grep -c sorry OpenMath/Chapter4/Section441.lean
grep -n "aPoly_coeff_one_pos_of_stable_preconsistent" \
  OpenMath/Chapter4/Section441.lean
```

You should see the cycle 187 commit, sorry count 0, and the Phase B
headline at line 913.

## Priority 0 — GPFS smoke test (≤5 min budget, then move on)

Run exactly once at the start of the cycle:

```
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

* **If EXIT=0 in <5 min** (GPFS recovered): proceed to **Priority 1**.
* **If EXIT=124 (timeout)** — the 8th consecutive timeout: do not
  retry. Do not poll Aristotle (no pending jobs). Append one row to
  `.prover-state/issues/cycle_182_gpfs_slowness.md` documenting the
  8th timeout (CPU/wall numbers from the `time` output) and pivot
  to **Priority 2**. Worker MUST NOT modify
  `scripts/autonomous_loop.py` or attempt cluster-side fixes — that
  is loop-maintainer territory per CLAUDE.md.

Do NOT spend more than 5 minutes total on Priority 0.

## Priority 1 — Phase C.2 (only if Priority 0 EXIT=0)

Steps:

1. Copy `.prover-state/cycle_182_draft_section441.lean` over
   `OpenMath/Chapter4/Section441.lean`.
2. Apply the cycle 184 namespace fix at line 1529:
   `M.αPoly_complex_root_norm_ge_one_of_stable hStable hψ_ne hψ_isRoot`
   →
   `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable M hStable hψ_ne hψ_isRoot`
3. `lake env lean OpenMath/Chapter4/Section441.lean` — must exit 0
   in <8 min. If it exits with errors, surface them but DO NOT
   attempt new tactic engineering this cycle; the draft is
   Aristotle-audited modulo the namespace fix.
4. `lean_verify` the three new public theorems
   (`ρPoly_complex_root_norm_le_one_of_stable`,
   `αPoly_complex_root_norm_ge_one_of_stable`,
   `aPoly_complex_root_re_nonpos_of_stable`) — expect
   `[propext, Classical.choice, Quot.sound]` only.
5. Update `extraction/formalization_data/lean_status.json`,
   `plan.md`, and `lem_441A_phase_C_scoping.md` to mark Phase C.2
   closed.

If anything in steps 3–5 fails: revert `Section441.lean` to HEAD
and pivot to Priority 2. Do NOT leave the file with sorries or
errors.

## Priority 2 — 0-reduction analogue of cycle 187 work (~150 LOC)

This is the main expected deliverable. Builds directly on cycle
187's `PhiEquivalent.of_pReducesTo` and closes the lacuna its
docstring identifies (`OpenMath/Chapter3/Section381.lean:830-832`):

> "The 0-reduction analogue will fold in cleanly when the 0-step
> `PReducesTo` constructor is added (see `def:381E` deferred-
> construction issue)."

### Deliverable A — extend `RKTableau.PReducesTo` with `zeroStep`

In `OpenMath/Chapter3/Section381.lean`, in the
`RKTableau.PReducesTo` inductive at line 393, add a third
constructor between `step` and the closing `end`:

```lean
  /-- One 0-reduction step: `M` is 0-reducible via `inP1` (P₀
  non-empty), and the result `M.zeroReduced inP1` reduces further
  (in zero or more steps) to `M''`. The non-emptiness `hP0` keeps
  this faithful to Butcher §380 def:381C, which requires P₀ to
  contain at least one stage; without it, the trivial all-stages-
  in-P₁ partition would admit vacuous "0-reductions" that do not
  decrease the stage count. -/
  | zeroStep {s s'' : ℕ}
      {M : RKTableau s} {M'' : RKTableau s''}
      (inP1 : Fin s → Bool) (_hP0 : ∃ i, inP1 i = false)
      (_h : M.IsZeroReducibleVia inP1) :
      PReducesTo (M.zeroReduced inP1) M'' → PReducesTo M M''
```

Note the field ordering matches `step`: partition data first,
non-triviality side-condition second, the
`IsZeroReducibleVia`/`IsPReducibleVia` predicate third, then the
recursive `PReducesTo`. This matches the destructuring discipline
used by `eq_of_not_isPReducible_of_pReducesTo` (which currently
matches on `refl` and `step`; see Deliverable C below).

### Deliverable B — `zeroReduced_phiEquivalent`

Add a new public theorem mirroring `pReduced_phiEquivalent`
(`Section381.lean:782`):

```lean
theorem zeroReduced_phiEquivalent {s : ℕ}
    (M : RKTableau s) {inP1 : Fin s → Bool}
    (h : M.IsZeroReducibleVia inP1) :
    PhiEquivalent M (M.zeroReduced inP1)
```

**Proof structure** (analogous to cycle 187's `pReduced_phiEquivalent`
but simpler — the embedding `zeroReducedEmb` is an *injection*, not
a representative choice, so no `Classical.choose` plumbing):

1. **Two private mutual helpers**
   `derivativeWeight_zeroReduced` (over `RootedTree`) and
   `derivativeWeightProd_zeroReduced` (over `List RootedTree`):

   ```
   ∀ (t : RootedTree) (I : Fin sBar'),
     M.derivativeWeight (zeroReducedEmb inP1 I) t
       = (M.zeroReduced inP1).derivativeWeight I t
   ```

   where `sBar' := (Finset.univ.filter (fun i => inP1 i = true)).card`.

   In the `t :: ts` recursive step the inner sum is

   ```
   ∑ j : Fin s, M.A (emb I) j * M.derivativeWeight j t
   ```

   Use `Finset.sum_filter_ne` (or a direct `Finset.sum_subset` /
   `Finset.sum_eq_sum_of_subset_of_zero_on_sdiff`) to discard the
   `inP1 j = false` terms — they vanish because `M.A (emb I) j = 0`
   when `emb I ∈ P₁` and `j ∈ P₀` (this is the second clause of
   `IsZeroReducibleVia`, `h.2 (emb I) j (emb_inP1_eq_true …) hj`).
   The surviving sum over `{j | inP1 j = true}` reindexes via
   `zeroReducedEmb` to a sum over `Fin sBar'`. Use
   `Finset.sum_image`-style or the bijection lemma
   `Equiv.sum_comp` to perform the reindex, then apply the
   `derivativeWeight_zeroReduced` IH on each summand.

2. **Main theorem `zeroReduced_phiEquivalent`** uses the helpers
   plus the outer `Σ_i b_i Φᵢ(t)` decomposition: split the sum at
   `inP1 i`, kill the `inP1 i = false` half via `h.1` (which gives
   `M.b i = 0`), reindex the surviving half via `zeroReducedEmb`,
   and apply `derivativeWeight_zeroReduced`.

**Required helper — `zeroReducedEmb_inP1_eq_true`**: prove
`inP1 (zeroReducedEmb inP1 I) = true` for every `I`. The embedding
is defined to land in the filtered subtype (see
`Section381.lean:219-228`), so this should be a one-line `simp` or
`Finset.mem_filter`-driven extraction. Look for existing supporting
lemmas around `zeroReducedEmb` first; if absent, add this as a
private helper before the mutual block.

### Deliverable C — extend `PhiEquivalent.of_pReducesTo`

Update the existing `induction h with` (line 836) to handle the
new `zeroStep` constructor:

```lean
  | refl M => exact PhiEquivalent.refl M
  | step P _hLt hVia _hRest IH =>
      exact PhiEquivalent.trans (pReduced_phiEquivalent _ hVia) IH
  | zeroStep inP1 _hP0 hVia _hRest IH =>
      exact PhiEquivalent.trans (zeroReduced_phiEquivalent _ hVia) IH
```

Also extend `eq_of_not_isPReducible_of_pReducesTo`
(`Section381.lean:439`): currently it matches on `refl` and `step`.
Decide whether the `zeroStep` case needs a new hypothesis on
non-0-reducibility, OR whether the existing
`hIrr : ¬ M.IsPReducible` is genuinely insufficient and the lemma
needs renaming/strengthening. The cleanest move is probably to
**add a parallel lemma** `eq_of_not_isReducible_of_pReducesTo` that
takes both `¬ M.IsPReducible` and `¬ M.IsZeroReducible` (i.e.
`M.IsIrreducible` per `Section381.lean:354`) and case-splits on
all three constructors. Mark the original lemma as deprecated only
if downstream usage allows it; otherwise leave it in place and add
the stronger sibling.

`PEquivalent.trans_of_middle_not_pReducible` (line 472) consumes
`eq_of_not_isPReducible_of_pReducesTo` — if you keep the original,
its proof is unaffected; if you rename, update the call site here.

### Deliverable D — non-vacuity witness using `zeroStep`

Add a small witness exercising the new constructor on a tableau
that is genuinely 0-reducible (paddedEuler is the obvious choice
— line 605 already has
`paddedEuler.IsZeroReducibleVia ![true, false]`):

```lean
example :
    RKTableau.PReducesTo paddedEuler
      (paddedEuler.zeroReduced ![true, false]) :=
  RKTableau.PReducesTo.zeroStep ![true, false]
    (by decide)  -- ∃ i, inP1 i = false
    (by …)       -- IsZeroReducibleVia witness, reuse the example at line 605
    (RKTableau.PReducesTo.refl _)
```

If the existing `example` at line 605 is convertible to a `theorem`
without breaking elaboration, do that and reuse it; otherwise inline
the same `decide`-style proof.

### Hypothesis discipline

**Faithfulness check for Deliverable A** — the `_hP0 : ∃ i, inP1 i = false`
side condition is faithful to Butcher §380 def:381C ("there is at
least one stage in P₀"; see `Section381.lean:202-216`); without it,
the trivial all-stages-in-P₁ partition would admit vacuous
0-reductions that don't decrease the stage count, paralleling the
cycle 185 fix to `step`'s `_hLt : sBar < s` requirement.

**Faithfulness check for Deliverable B** — Butcher's narrative around
0-reduction (§380, p. 302) treats Φ-preservation as obvious because
deleted stages have weight zero; we formalise this via the two clauses
of `IsZeroReducibleVia`. Document in the docstring of
`zeroReduced_phiEquivalent` that this is the textbook's implicit
"deleted stages don't contribute to elementary weights" observation.

## What NOT to do this cycle

* Do NOT audit cycle 174's `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
  bridge (line 455 of `Section441.lean`). The factor-of-2 is a
  Butcher typo, independently re-verified by two consultants.
* Do NOT rewrite `bdf2LMM_aPoly_eq` via `Polynomial.ext` —
  cycles 172/173 stalled on this; the cycle 180 `Polynomial.funext +
  ring` recipe (`Section441.lean:947`) is the canonical closure.
* Do NOT poll Aristotle — no pending jobs from cycle 187.
* Do NOT submit new Aristotle jobs this cycle — the cycle 184
  C.2 proof is fully audited and only awaits GPFS recovery.
* Do NOT modify `scripts/autonomous_loop.py` — see
  `tautology_scanner_false_positives.md` and
  `phantom_commit_verdict_pattern.md`. The "stuck on"-framing
  phantom in the prompt is a separate occurrence of the same
  prompt-builder bug.
* Do NOT raise `maxHeartbeats` above 200000.
* Do NOT introduce `axiom` / `constant` declarations.
* Do NOT attempt the full `def:381E` reduced-method fixed-point
  construction this cycle — that is multi-cycle infrastructure (see
  `.prover-state/issues/reduced_method_deferred.md`). Deliverables
  A–D above add the 0-reduction *step* to `PReducesTo`, which is
  strictly less ambitious and unblocks future cycles' work on
  `def:381F`'s textbook formulation, `thm:381G`, and `thm:381H`.
* Do NOT use `conv_lhs => ext j` on `Finset.sum`-shaped goals — it
  doesn't descend through the sum's λ-binder. Use
  `Finset.sum_congr rfl (fun j _ => …)` plus an explicit
  `have hSumRewrite` rewrite (cycle 187 discovery).
* Do NOT attach docstrings to the `mutual` keyword itself — Lean
  rejects with "unexpected token 'mutual'". Attach to each individual
  private theorem inside the block (cycle 187 fix).

## Verification gate

Before committing:

1. `lake env lean OpenMath/Chapter3/Section381.lean` exits 0.
2. `grep -c sorry OpenMath/Chapter3/Section381.lean` returns 0.
3. `lean_verify` on `pReduced_phiEquivalent` (cycle 187, regression
   check), `zeroReduced_phiEquivalent` (new), and
   `PhiEquivalent.of_pReducesTo` (now extended) — all expected to
   return `[propext, Classical.choice, Quot.sound]`.
4. Tautology-scanner regex check:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section381.lean`
   should return no new entries beyond pre-existing rows.
5. Pre-commit faithfulness checklist (CLAUDE.md):
   * For each new theorem: textbook reference, hypothesis-strength
     audit, no tautological `:= h` closer that smuggles a hypothesis
     as a conclusion.
   * Document the `_hP0` side condition's role in the
     `zeroStep` docstring.

## Backup plan if Deliverable B stalls

If the mutual induction in `zeroReduced_phiEquivalent` blows up on
the reindexing step (the `j ↦ zeroReducedEmb inP1 …` bijection),
DO NOT commit a `sorry`. Fall back to:

* Ship Deliverable A only (extend `PReducesTo` with `zeroStep`),
  plus Deliverable D's non-vacuity witness, plus a
  `zeroReduced_phiEquivalent` theorem that takes additional
  faithfulness-preserving hypotheses (e.g. specialised to the
  case `s' := (filter inP1).card`) — but only if it can be closed
  fully axiom-clean. If not, ship A + D only and document
  Φ-preservation as a deferred follow-up for cycle 189 in
  `.prover-state/issues/reduced_method_deferred.md` (extend the
  existing entry).
* Deliverable C's `zeroStep` case in `PhiEquivalent.of_pReducesTo`
  cannot land without B; if B fails, leave Deliverable C out as
  well, and add a TODO comment at line 836 documenting the gap.

## Backup plan if Priority 2 stalls entirely

If Deliverable A's inductive constructor refuses to elaborate
(unlikely but possible if Lean's mutual-inductive checker objects
to the heterogeneous stage counts), fall back to:

* **Plan B**: promote the `paddedEuler.IsZeroReducibleVia`
  example at `Section381.lean:605` to a public named theorem
  `paddedEuler_isZeroReducibleVia_split` and pair it with a
  derived `paddedEuler.IsZeroReducible` named witness. Pure
  promotion work, ~10 LOC, axiom-clean, mirrors cycle 186's
  inline-example-to-named-theorem promotion pattern.
* **Plan C**: pivot to scoping `thm:381G` (irreducible methods are
  stage-distinguishable) — read
  `extraction/formalization_data/entities/thm_381G.json` and write
  a sorry-free predicate-level deliverable plus a non-vacuity
  witness if tractable in one cycle.

Plan C requires reading the JSON and is exploratory; only fall back
to it if Plans A and B both stall.
