# Cycle 232 Strategy

## §A. State summary

- **Sorry count: 0** (45th consecutive clean cycle since the cycle 201
  rollback). Maintain this — any sorry increase is heavily penalized.
- **Last cycle (231)**: shipped axiom-clean
  `derivativeWeightWithSrc_compose_natAdd` +
  `derivativeWeightWithSrcProd_compose_natAdd` (mutual pair, both
  `private`, ~95 LOC) — the bottom-block companion to cycle 230's
  top-block. Three-factor `paddedEuler` non-vacuity witness shipped.
- **Both per-stage infrastructure lemmas now exist** for cycle 232's
  `compose_assoc_phiEquivalent`:
  - cycle 230: top-block `derivativeWeightWithSrc_compose_castAdd`
  - cycle 231: bottom-block `derivativeWeightWithSrc_compose_natAdd`
- **§441 Phase C.2 GPFS-blocked** (46th consecutive cycle of timeout
  pathology on `Section441.lean` smoke test). Per CLAUDE.md and the
  cycle 196+ pattern, **skip the §441 smoke test entirely** this
  cycle. Do NOT run `lake env lean OpenMath/Chapter4/Section441.lean`.
- **Aristotle right-action job** (project
  `176aa964-db7b-40f8-a01c-05247c186ec5`): IN_PROGRESS at 29% as of
  cycle 231 (growth: 9% → 11% → 17% → 24% → 29% over cycles
  227–231, ≈2–7%/cycle). Single poll permitted at cycle start;
  several-day ETA at current rate.

## §B. Aristotle poll (do this FIRST, exactly once)

Run **once** at cycle start:
```
mcp__aristotle__get_status project_id="176aa964-db7b-40f8-a01c-05247c186ec5"
```

**Decision tree:**

- **COMPLETE with successful proof** → SUSPEND the cycle 232 path-B
  plan below. Instead:
  1. Extract Aristotle's proof of the right-action M₂-side sum
     equality.
  2. Incorporate it into `OpenMath/Chapter3/Section381.lean` as
     `compose_phiEquivalent_compose_right` (the M₂-varying
     counterpart of cycle 226's `compose_phiEquivalent_compose_left`).
  3. Combine left + right actions into the full
     `compose_phiEquivalent_compose` (the bilinear
     PhiEquivalent-respecting lemma).
  4. Build the full `composeQ_phi : Quotient PhiEquivalent.setoidSigma
     → Quotient PhiEquivalent.setoidSigma → Quotient
     PhiEquivalent.setoidSigma` via `Quotient.lift₂` consuming the
     full `compose_phiEquivalent_compose`.
  5. Update `lean_status.json` (`thm:384A` cycle 232, lean_symbol
     pointing at `composeQ_phi`).
  6. Update `plan.md` `thm:384A` row.
  7. Update `.prover-state/issues/cycle_226_compose_phi_right_action.md`
     with the closure record.

- **COMPLETE_WITH_ERRORS** → Examine the Aristotle output for any
  surfaced bugs or partial progress. If a one-line fix is
  identified, apply it; otherwise discard and proceed with path B.

- **IN_PROGRESS at any percentage / FAILED / any other status** →
  Proceed with **path B** below. Do NOT re-poll. Do NOT cancel the
  job (it costs nothing to leave running and may still complete).

## §C. Path B (default): ship `compose_assoc_phiEquivalent`

This is the cycle 231 task results' "Suggested next approach". With
cycles 230 + 231 + 225 + 226 all closed, the three-factor
associativity at the PhiEquivalent level is the natural next
deliverable and the last missing piece before the §383 `Group`
instance on `Quotient PhiEquivalent.setoidSigma`.

### C.1 Target

Ship in `OpenMath/Chapter3/Section381.lean` (inside `namespace
OpenMath.Chapter3.Section312.RKTableau`):

```lean
theorem compose_assoc_phiEquivalent
    {s₁ s₂ s₃ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
    @PhiEquivalent ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
      ((M₁.compose M₂).compose M₃)
      (M₁.compose (M₂.compose M₃))
```

This is the heterogeneous-stage `PhiEquivalent`-level analog of
cycle 221's `compose_equivalent_compose_assoc` at the `Equivalent`
level (lines ~3060 of Section381.lean). The signature accepts the
heterogeneous stage counts because `PhiEquivalent` works at the
elementary-weight / rooted-tree level, not at the dynamical
`IsRKOneStep` level — there is no stage-count constraint imposed by
the definition.

### C.2 Insertion site

Place immediately after cycle 231's bottom-block mutual pair (around
Section381.lean line ~3025 in HEAD), still inside an
`open OpenMath.Chapter3.Section310 ... end` wrapper structure so
`RootedTree` resolves correctly. If cycle 231's `end` closed the
previous wrapper, open a fresh wrapper for cycle 232's theorem.

### C.3 Proof recipe

Unfold the `PhiEquivalent` definition: the goal becomes

```
∀ t : RootedTree,
  ((M₁.compose M₂).compose M₃).elementaryWeight t
    = (M₁.compose (M₂.compose M₃)).elementaryWeight t
```

(Both sides are scalars in ℝ, so `PhiEquivalent` reduces to
elementwise equality on rooted trees.)

For each side, apply `compose_elementaryWeight_decomp` (cycle 225,
M₂-side, source-threaded form) to expose the structure:

**LHS** = `((M₁.compose M₂).compose M₃).elementaryWeight t`
  = `(M₁.compose M₂).elementaryWeight t
       + ∑ i : Fin s₃, M₃.b i * M₃.derivativeWeightWithSrc (M₁.compose M₂) i t`
  (one application of cycle 225 with `(M_left, M_right) = (M₁.compose M₂, M₃)`)
  = `M₁.elementaryWeight t
       + ∑ i : Fin s₂, M₂.b i * M₂.derivativeWeightWithSrc M₁ i t
       + ∑ i : Fin s₃, M₃.b i * M₃.derivativeWeightWithSrc (M₁.compose M₂) i t`
  (second application with `(M_left, M_right) = (M₁, M₂)` on the first
  term).

**RHS** = `(M₁.compose (M₂.compose M₃)).elementaryWeight t`
  = `M₁.elementaryWeight t
       + ∑ i : Fin (s₂+s₃), (M₂.compose M₃).b i
           * (M₂.compose M₃).derivativeWeightWithSrc M₁ i t`
  (one application of cycle 225 with `(M_left, M_right) = (M₁, M₂.compose M₃)`).

To match LHS and RHS:
1. **Split the RHS `Fin (s₂+s₃)` sum** via `Fin.sum_univ_add` into
   top-block (`Fin.castAdd s₃ j` for `j : Fin s₂`) and bottom-block
   (`Fin.natAdd s₂ k` for `k : Fin s₃`) halves.
2. **Apply `compose_b_castAdd` and `compose_b_natAdd`** (cycle 209,
   simp lemmas at Section381.lean lines ~2501–2519) to evaluate
   `(M₂.compose M₃).b (Fin.castAdd s₃ j) = M₂.b j` and
   `(M₂.compose M₃).b (Fin.natAdd s₂ k) = M₃.b k`.
3. **Apply cycle 230** (`derivativeWeightWithSrc_compose_castAdd`)
   on the top-block per-summand to reduce
   `(M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.castAdd s₃ j) t
     = M₂.derivativeWeightWithSrc M₁ j t`.
4. **Apply cycle 231** (`derivativeWeightWithSrc_compose_natAdd`)
   on the bottom-block per-summand to reduce
   `(M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.natAdd s₂ k) t
     = M₃.derivativeWeightWithSrc (M₁.compose M₂) k t`.
5. After these reductions, the RHS becomes
   `M₁.elementaryWeight t
       + ∑ j : Fin s₂, M₂.b j * M₂.derivativeWeightWithSrc M₁ j t
       + ∑ k : Fin s₃, M₃.b k * M₃.derivativeWeightWithSrc (M₁.compose M₂) k t`
6. **Match LHS = RHS**: term-for-term equality after the above
   reductions. Close via `ring` (or `rfl` if the associativity
   matches definitionally).

Estimated **40–80 LOC** for the full theorem body.

### C.4 Proof structure (concrete sketch)

```lean
theorem compose_assoc_phiEquivalent
    {s₁ s₂ s₃ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
    @PhiEquivalent ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
      ((M₁.compose M₂).compose M₃)
      (M₁.compose (M₂.compose M₃)) := by
  intro t
  -- Unfold both sides via cycle 225's decomp.
  rw [compose_elementaryWeight_decomp (M₁.compose M₂) M₃ t]
  rw [compose_elementaryWeight_decomp M₁ M₂ t]
  rw [compose_elementaryWeight_decomp M₁ (M₂.compose M₃) t]
  -- Split the RHS Fin (s₂+s₃) sum.
  rw [Fin.sum_univ_add]
  -- Simp evaluates compose_b at castAdd / natAdd.
  simp only [compose_b_castAdd, compose_b_natAdd]
  -- Per-summand: route top-block via cycle 230, bottom-block via cycle 231.
  rw [show (∑ j : Fin s₂, M₂.b j
              * (M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.castAdd s₃ j) t)
         = ∑ j : Fin s₂, M₂.b j * M₂.derivativeWeightWithSrc M₁ j t
         from Finset.sum_congr rfl (fun j _ => by
           rw [derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j])]
  rw [show (∑ k : Fin s₃, M₃.b k
              * (M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.natAdd s₂ k) t)
         = ∑ k : Fin s₃, M₃.b k
              * M₃.derivativeWeightWithSrc (M₁.compose M₂) k t
         from Finset.sum_congr rfl (fun k _ => by
           rw [derivativeWeightWithSrc_compose_natAdd M₁ M₂ M₃ t k])]
  -- Now both sides match up to associativity of `+`.
  ring
```

**Risk**: the per-summand `rw [show ... from Finset.sum_congr ...]`
may need the cycle 230 / 231 lemmas applied at `t` as the rooted
tree (not `M₁.elementaryWeight t` form). Double-check the
`derivativeWeightWithSrc_compose_castAdd` signature — it operates
on `t : RootedTree` (NOT on the elementary weight); the rewrite at
the per-summand level should be a direct application.

If the per-summand congruence approach trips on motive issues
(higher-order metavariables in `Finset.sum_congr`), fall back to:
```lean
have h_top : ∀ j : Fin s₂,
    M₂.b j * (M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.castAdd s₃ j) t
      = M₂.b j * M₂.derivativeWeightWithSrc M₁ j t := fun j =>
  by rw [derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j]
have h_bot : ∀ k : Fin s₃, ... := fun k =>
  by rw [derivativeWeightWithSrc_compose_natAdd M₁ M₂ M₃ t k]
rw [Finset.sum_congr rfl (fun j _ => h_top j),
    Finset.sum_congr rfl (fun k _ => h_bot k)]
ring
```

### C.5 P2 non-vacuity witness

Add a three-factor `paddedEuler` `example` (~3–5 LOC) at the bottom of
the file, near cycles 230 / 231's witnesses:

```lean
example : @PhiEquivalent ((2 + 2) + 2) (2 + (2 + 2))
    ((paddedEuler.compose paddedEuler).compose paddedEuler)
    (paddedEuler.compose (paddedEuler.compose paddedEuler)) :=
  compose_assoc_phiEquivalent paddedEuler paddedEuler paddedEuler
```

This is a near-trivial application of the new theorem at the canonical
non-trivial witness method.

### C.6 LOC budget

Total cycle 232 LOC delta:
- `compose_assoc_phiEquivalent` body: ~40–80 LOC
- P2 non-vacuity: ~5 LOC
- **Total target: ~50 LOC, hard cap 100 LOC.**

If LOC exceeds 100 by mid-cycle, this signals the per-summand
congruence isn't firing cleanly. In that case **abort** and ship a
narrower deliverable (see §E.1).

## §D. What NOT to try

1. **Do NOT attempt the right-action M₂-side sum equality manually.**
   Cycle 226's task results document the four ruled-out approaches
   (direct tree induction, decomposition-then-reapply, reduction
   via `PhiEquivalent → Equivalent`, per-summand reasoning). All
   four fail. The right-action requires either:
   - the Connes-Kreimer coproduct formalization (5–10 cycles), or
   - Aristotle's job completing (currently 29%, several-day ETA), or
   - a Taylor expansion / B-series infrastructure (also multi-cycle).

   See `.prover-state/issues/cycle_226_compose_phi_right_action.md`
   for the full record.

2. **Do NOT run the §441 GPFS smoke test.** Forty-six consecutive
   cycles have shown the same 5-min timeout with near-zero CPU on
   `Section441.lean`. Skipping is mandatory per CLAUDE.md.

3. **Do NOT introduce `axiom`/`constant` declarations.** Cycle 232
   has all infrastructure pieces in hand (cycles 225 / 226 / 230 /
   231); the closure is purely structural.

4. **Do NOT raise `maxHeartbeats` above 200000.** The `ring` step
   at the end of the proof closes a 3-term-summed equation with
   opaque atoms; this should be well within default heartbeats per
   cycle 231's experience.

5. **Do NOT rebuild the cycle 225 `compose_elementaryWeight_decomp`
   in M₁-side form.** It's already in M₂-side form (cycle 231
   audit confirmed this at Section381.lean lines 2819–2833) and
   cycle 232's plan exploits this shape directly.

6. **Do NOT attempt the full `composeQ_phi` lift this cycle.**
   That lift requires the FULL `compose_phiEquivalent_compose`
   (which has both the left action — shipped cycle 226 — and the
   right action — still blocked). Associativity alone is the cycle
   232 deliverable; the `composeQ_phi` is downstream of the
   right-action.

7. **Do NOT modify cycles 224 / 225 / 226 / 230 / 231 lemmas.**
   They are axiom-clean and load-bearing. Any refactoring there
   risks breaking the cycle 232 closure.

8. **Do NOT cherry-pick a different target.** The cycle 231 task
   results explicitly recommend `compose_assoc_phiEquivalent`; the
   §383 group-homomorphism path is the standing project priority
   per the cycle history. Pivoting to a fresh entity is not
   warranted — the existing infrastructure stack is at peak
   readiness for this specific deliverable.

9. **Do NOT apply the cycle 230 discovery "two `congr 1` rule"
   blindly.** Cycle 231 discovery #2 documents the rule depends on
   whether the bracket shapes match symmetrically. For cycle 232,
   the LHS and RHS have the elementary-weight terms unfolded into
   *different* shapes after the cycle 225 rewrites, so the
   `Finset.sum_congr` approach is more reliable than `congr` peeling.

## §E. Abort thresholds and fallbacks

### E.1 If the per-summand congruence fails

If `Finset.sum_congr` + per-summand `rw [derivativeWeightWithSrc_*]`
trips on motive issues or higher-order unification, try in this order:
1. **Named `have` extraction** of the per-tree equation (sketched in
   §C.4 fallback above).
2. **Direct `simp only [derivativeWeightWithSrc_compose_castAdd,
   derivativeWeightWithSrc_compose_natAdd]`** to discharge per-summand
   rewrites — but be cautious: these are `private` lemmas, so simp
   only fires if the call site is in the same namespace block.
3. **Auxiliary private lemma** `compose_assoc_phiEquivalent_aux`
   that does the elementary-weight-level matching, with the public
   theorem as a one-line wrapper.

### E.2 If `ring` doesn't close the final step

The final step should be `a + b + c = a + b + c` (LHS and RHS match
up to commutativity / associativity of `+`). If `ring` fails:
1. Try `linarith [...opaque atoms...]` — unlikely to work but cheap.
2. Use `rw [add_assoc]` / `rw [← add_assoc]` to manually align the
   two trees.
3. Check whether the goal still has unresolved metavariables
   (incomplete reductions from §C.3 steps 2–4).

### E.3 If warm rebuild > 30 seconds

Per cycle 231 strategy §F.3, a warm rebuild exceeding 30s on
`Section381.lean` is a red flag suggesting accidentally heavy proof
content. Profile via `lean_profile_proof` on the new theorem;
likely culprit is over-eager `simp` discharging too much before the
manual `rw` steps. Fix by adding `simp only [explicit_lemma_list]`
rather than `simp` with default sets.

### E.4 If LOC delta exceeds 100

Abort the full `compose_assoc_phiEquivalent` and ship a narrower
deliverable instead. Candidates (any one suffices for cycle 232):
- **Auxiliary lemma**: ship just the per-tree associativity equation
  at the elementary-weight level (`(M₁.compose M₂).compose M₃
  .elementaryWeight t = M₁.compose (M₂.compose M₃) .elementaryWeight
  t`) without the `PhiEquivalent` wrapper. ~30 LOC.
- **Refactor**: extract a `compose_elementaryWeight_assoc` private
  helper that handles the structural rearrangement, with cycle 232's
  full theorem deferred to cycle 233.

Sorry count MUST remain 0 — a partial scaffold with `sorry` is
worse than shipping a narrower theorem.

## §F. Risks (pre-flight checklist)

Verify these BEFORE writing the proof body:

1. **R1: `compose_elementaryWeight_decomp` arity** — Section381.lean
   line ~2819. Confirm signature:
   ```
   compose_elementaryWeight_decomp (M_left : RKTableau s_left)
     (M_right : RKTableau s_right) (t : RootedTree) :
     (M_left.compose M_right).elementaryWeight t
       = M_left.elementaryWeight t
           + ∑ i : Fin s_right,
               M_right.b i * M_right.derivativeWeightWithSrc M_left i t
   ```
   If arity or shape differs, adapt the §C.3 plan. Use
   `lean_hover_info` on the symbol if unsure.

2. **R2: `compose_b_castAdd` / `compose_b_natAdd` fire under
   `simp only`** — Section381.lean lines ~2501–2519. Confirm they
   reduce `(M₂.compose M₃).b (Fin.castAdd s₃ j)` to `M₂.b j`
   directly.

3. **R3: `Fin.sum_univ_add` splits the sum correctly** — confirm by
   reviewing cycle 230 / 231 proofs at Section381.lean lines
   ~2880 / 2980. Both cycles use this; same usage applies.

4. **R4: cycle 230 / 231 mutual lemma applicability** — confirm
   that the two new theorems are applicable in the per-summand
   form:
   - `derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j` :
     `(M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.castAdd s₃ j) t
       = M₂.derivativeWeightWithSrc M₁ j t`
   - `derivativeWeightWithSrc_compose_natAdd M₁ M₂ M₃ t k` :
     `(M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.natAdd s₂ k) t
       = M₃.derivativeWeightWithSrc (M₁.compose M₂) k t`

   The `t` argument should be supplied (these are universally quantified
   over `t : RootedTree`). If the signature has explicit/implicit
   binders that conflict, adapt the call site.

5. **R5: Namespace and `private` visibility** — cycle 230 / 231 lemmas
   are declared `private`. Verify cycle 232's theorem lives in the
   **same** namespace block (`OpenMath.Chapter3.Section312.RKTableau`),
   inside an `open OpenMath.Chapter3.Section310 ... end` wrapper so
   `RootedTree` resolves. If the wrapper from cycle 231 is already
   closed at the insertion site, open a fresh one.

6. **R6: Heterogeneous stage Σ-projection** — the goal type
   `@PhiEquivalent ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃)) ...` uses
   `PhiEquivalent` with explicit stage counts. Use `@PhiEquivalent`
   (with explicit `@`) to ensure both stage counts are passed in
   the right positions. Cycles 224 / 225 / 226 / 230 / 231 already
   use this convention for `@PhiEquivalent`.

7. **R7: `PhiEquivalent` unfolding** — the proof begins with
   `intro t`. Confirm `PhiEquivalent` is definitionally
   `∀ t : RootedTree, M.elementaryWeight t = M'.elementaryWeight t`
   (or similar) at Section381.lean's `PhiEquivalent` definition.
   If the definition has additional structure (e.g. an existential
   wrapper), adapt the unfolding step.

## §G. Verification & cleanup

After the body compiles:

1. **`lean_verify`** axiom check on:
   - `OpenMath.Chapter3.Section312.RKTableau.compose_assoc_phiEquivalent`

   Expected: `[propext, Classical.choice, Quot.sound]` only.

2. **Regression spot-check** axiom-cleanliness on:
   - `derivativeWeightWithSrc_compose_castAdd` (cycle 230)
   - `derivativeWeightWithSrc_compose_natAdd` (cycle 231)
   - `compose_phiEquivalent_compose_left` (cycle 226)
   - `composeQ_phi_left_act` (cycle 227)
   - `composeQ_phi_left_act_id_left` / `_id_right` (cycles 228 / 229)

3. **Warm rebuild** of `Section381.lean`: target < 30s (per cycle
   231's 6.35s baseline; the new theorem should add < 2s of
   elaboration). Note: first compile after the edit will take
   1m+ (cold cache); the WARM baseline is the 2nd or 3rd compile.

4. **Update `plan.md`** `thm:384A` row: append cycle 232 outcome:
   "cycle 232 shipped `compose_assoc_phiEquivalent`
   (three-factor associativity at PhiEquivalent level, ~50 LOC,
   axiom-clean)".

5. **Update `lean_status.json`** for `thm:384A`: bump cycle to 232,
   status stays `partial` (full homomorphism Φ still requires
   right-action + `composeQ_phi`).

6. **Append to `.prover-state/issues/cycle_226_compose_phi_right_action.md`**:
   - cycle 232 update note (associativity shipped at the
     PhiEquivalent level; the right-action remains open).
   - cycle 233 outlook: if Aristotle still IN_PROGRESS (now 6th
     poll-cycle), either continue path-B infrastructure
     (e.g. mixed identity lemmas, or composability proofs in the
     `composeQ_phi_left_act` API) or pivot to a fresh entity if
     path-B momentum is exhausted.

7. **Write `.prover-state/task_results/cycle_232.md`** documenting
   the closure following the CLAUDE.md template (Worked on /
   Approach / Result / Faithfulness check / Dead ends / Discovery /
   Suggested next approach).

## §H. Commit

After verification passes:
```
git add OpenMath/Chapter3/Section381.lean plan.md \
        extraction/formalization_data/lean_status.json \
        .prover-state/issues/cycle_226_compose_phi_right_action.md \
        .prover-state/task_results/cycle_232.md \
        .prover-state/strategy.md
git commit -m "Cycle 232 — §383 group-hom path Phase 3 follow-up: \
compose_assoc_phiEquivalent SHIPPED axiom-clean."
```

(Use a single-line subject ≤ ~120 chars; the body can be longer
following the cycle 230 / 231 pattern.)

## §I. Bottom line

**Cycle 232 ships `compose_assoc_phiEquivalent` via path B (three-
factor associativity at the PhiEquivalent level).** This is the
direct continuation of cycle 231's bottom-block mutual pair and the
last per-stage infrastructure piece before the §383 group-
homomorphism path can build the `Group` instance on
`Quotient PhiEquivalent.setoidSigma`. ~50 LOC, axiom-clean,
sorry count remains 0 (46th consecutive clean cycle).

If Aristotle's right-action job completes during the cycle (29%
poll at start), pivot to §B and ship the full
`compose_phiEquivalent_compose` + `composeQ_phi` instead.
