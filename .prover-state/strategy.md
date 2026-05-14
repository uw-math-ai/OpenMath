# Cycle 233 Strategy — §383 Group instance Phase 4.1: `compose_assoc_phiEquivalent`

## TL;DR

Ship **`compose_assoc_phiEquivalent`** (associativity of `compose` at
the `PhiEquivalent` level, three-factor heterogeneous-stage form) plus
its quotient-level corollary **`composeQ_phi_assoc`**. This is a clean
single-cycle deliverable that exploits the cycle 230 + 231 mutual
lemmas and cycle 225's `compose_elementaryWeight_decomp` end-to-end,
mirroring cycle 221's `compose_equivalent_compose_assoc` template at
the elementary-weight (not IsRKOneStep) level. Estimated ~50–80 LOC,
axiom-clean. **Sorry count must remain 0**.

§441 Phase C.2 still GPFS-blocked (46 consecutive cycles); skip per
established protocol.

## §A — Skip §441

Smoke test `time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`
on HEAD has timed out 46 consecutive cycles with near-zero CPU. Do
**NOT** re-test. Do **NOT** touch `Section441.lean`. The cycle 182
draft + cycle 184 namespace fix remain preserved at
`.prover-state/cycle_182_draft_section441.lean`; do **NOT** copy in
or attempt local compile. Per `cycle_182_gpfs_slowness.md`, this is
loop-maintainer territory.

If for some reason a smoke test does pass (<5 min), STOP the cycle 233
work, escalate via `phantom_commit_verdict_pattern.md`, and ship the
cycle 182 draft + namespace fix instead. Otherwise: ignore §441
entirely.

## §B — No Aristotle submission

Cycle 232 just consumed Aristotle (project `176aa964-…` COMPLETE);
cycle 233's deliverable is small enough (~50–80 LOC) that a fresh
submission would not finish in this cycle. **Do not submit anything
to Aristotle this cycle.** Save the queue slot for whatever cycle
234+ needs.

## §C — Primary deliverable: `compose_assoc_phiEquivalent`

### C.1 — Target signatures

Two theorems, both axiom-clean, both inside
`namespace OpenMath.Chapter3.Section312.RKTableau` (same namespace
context as cycle 221's `compose_equivalent_compose_assoc` and cycle
232's `compose_phiEquivalent_compose`).

**P1** — the elementary-weight-level associativity:

```lean
theorem compose_assoc_phiEquivalent {s₁ s₂ s₃ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
    @PhiEquivalent ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
      ((M₁.compose M₂).compose M₃) (M₁.compose (M₂.compose M₃))
```

**P2** — the quotient-level corollary (a `Quotient.inductionOn₃` +
`Quotient.sound` one-liner, mirroring cycle 221's `composeQ_assoc`
at `Section381.lean:4092-4098`):

```lean
theorem composeQ_phi_assoc
    (p q r : Quotient PhiEquivalent.setoidSigma) :
    composeQ_phi (composeQ_phi p q) r = composeQ_phi p (composeQ_phi q r)
```

### C.2 — Where to place them

Insert **P1** in the file immediately after cycle 232's
`compose_phiEquivalent_compose` block (currently ending at
`Section381.lean:3227`'s `end`). Open a fresh `section / open
OpenMath.Chapter3.Section310 / end` wrapper around P1 because the
cycle 232 section already closed — the namespace context
(`namespace OpenMath.Chapter3.Section312.RKTableau`) stays, only the
`open` directive resets. Verify by re-reading lines 3220–3230 first.

Insert **P2** immediately after `composeQ_phi_eq_left_act_mk` (cycle
232 simp lemma, the last symbol of cycle 232's `composeQ_phi` block).
P2 does not need `open Section310` because it only mentions
`composeQ_phi`, `PhiEquivalent.setoidSigma`, and `Quotient`.

### C.3 — Proof recipe for P1 (concrete, ~30 LOC)

The proof works at the elementary-weight level by applying cycle 225's
`compose_elementaryWeight_decomp` twice on the LHS (outer + inner) and
once on the RHS (outer), then expanding the RHS bottom-block sum using
`Fin.sum_univ_add` together with cycle 230's
`derivativeWeightWithSrc_compose_castAdd` and cycle 231's
`derivativeWeightWithSrc_compose_natAdd`. Cycle 230 and 231 are
`private` lemmas but live in the same file, so they are accessible.

```lean
theorem compose_assoc_phiEquivalent {s₁ s₂ s₃ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
    @PhiEquivalent ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
      ((M₁.compose M₂).compose M₃) (M₁.compose (M₂.compose M₃)) := by
  intro t
  -- LHS: apply decomp at outer `(M₁ · M₂) · M₃`, then inner `M₁ · M₂`.
  rw [compose_elementaryWeight_decomp (M₁.compose M₂) M₃ t,
      compose_elementaryWeight_decomp M₁ M₂ t]
  -- RHS: apply decomp at outer `M₁ · (M₂ · M₃)`.
  rw [compose_elementaryWeight_decomp M₁ (M₂.compose M₃) t]
  -- Goal now (modulo + associativity):
  --   (M₁.eW t + ∑ j, M₂.b j * M₂.dWWS M₁ j t)
  --     + ∑ k, M₃.b k * M₃.dWWS (M₁·M₂) k t
  --   = M₁.eW t + ∑ i, (M₂·M₃).b i * (M₂·M₃).dWWS M₁ i t
  -- Expand the RHS `(M₂·M₃).b` sum via Fin.sum_univ_add + cycle 230/231.
  rw [show
        (∑ i : Fin (s₂ + s₃),
            (M₂.compose M₃).b i * (M₂.compose M₃).derivativeWeightWithSrc M₁ i t)
          = (∑ j : Fin s₂, M₂.b j * M₂.derivativeWeightWithSrc M₁ j t)
            + ∑ k : Fin s₃,
                M₃.b k * M₃.derivativeWeightWithSrc (M₁.compose M₂) k t
      from ?_]
  · ring
  -- Auxiliary sum equality, closing the `show ... from ?_` obligation.
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [compose_b_castAdd,
        derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [compose_b_natAdd,
        derivativeWeightWithSrc_compose_natAdd M₁ M₂ M₃ t k]
```

**Critical: argument order for cycle 230/231 mutual lemmas.** Both
take `(t : RootedTree) (j : Fin _)` — tree FIRST, stage SECOND.
Confirmed by:

- Cycle 230 definition at `Section381.lean:2887-2898` (tree first).
- Cycle 230 usage at `Section381.lean:2928` (`derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j'`).
- Cycle 232 usages at `Section381.lean:3007` and `:3017`:
  `rw [derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j₁]` and
  `rw [derivativeWeightWithSrc_compose_natAdd M₁ M₂ M₃ t j₂]`.

**Trust these call sites verbatim** for the argument order in cycle
233's `rw` invocations.

### C.4 — Proof recipe for P2 (~6 LOC)

```lean
theorem composeQ_phi_assoc
    (p q r : Quotient PhiEquivalent.setoidSigma) :
    composeQ_phi (composeQ_phi p q) r = composeQ_phi p (composeQ_phi q r) := by
  refine Quotient.inductionOn₃ p q r ?_
  rintro ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ ⟨s₃, M₃⟩
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (compose_assoc_phiEquivalent M₁ M₂ M₃)
```

This is the verbatim port of cycle 221's `composeQ_assoc`
(`Section381.lean:4092-4098`) with `compose_equivalent_compose_assoc`
swapped for `compose_assoc_phiEquivalent` and `composeQ` swapped for
`composeQ_phi`. If P1 is axiom-clean, P2 is automatic.

### C.5 — Mandatory P3 non-vacuity witnesses

Place **two** axiom-clean `example` blocks near the end of the file,
inside `namespace OpenMath.Chapter3.Section381` (look for the existing
trailing-example region after cycle 232's witnesses; pattern follows
cycle 232's `example` placements).

**P3.1 — three-factor `paddedEuler` PhiEquivalent witness**:

```lean
example :
    @PhiEquivalent ((2 + 2) + 2) (2 + (2 + 2))
      ((paddedEuler.compose paddedEuler).compose paddedEuler)
      (paddedEuler.compose (paddedEuler.compose paddedEuler)) :=
  RKTableau.compose_assoc_phiEquivalent paddedEuler paddedEuler paddedEuler
```

**P3.2 — quotient-level associativity on three copies of
`⟦⟨2, paddedEuler⟩⟧`**:

```lean
example :
    let q : Quotient RKTableau.PhiEquivalent.setoidSigma :=
      Quotient.mk RKTableau.PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩
    RKTableau.composeQ_phi (RKTableau.composeQ_phi q q) q =
      RKTableau.composeQ_phi q (RKTableau.composeQ_phi q q) :=
  RKTableau.composeQ_phi_assoc _ _ _
```

These exercise both new theorems on a concrete tableau and confirm
the proofs fire end-to-end. Cross-check the `Quotient.mk
PhiEquivalent.setoidSigma` syntax against cycle 232's heterogeneous
non-vacuity examples (in the same trailing region) — adapt to
whatever explicit-namespace form those use.

## §D — Pre-flight checks (mandatory, ~5 min)

Before editing, run these to verify the infrastructure:

1. **Verify cycle 230/231 mutual-lemma names and argument order**:
   ```
   grep -n "derivativeWeightWithSrc_compose_castAdd\|derivativeWeightWithSrc_compose_natAdd" \
     OpenMath/Chapter3/Section381.lean | head -20
   ```
   Expected: definitions around lines 2887, 2959; usages at 2928,
   3007, 3017. Argument order `(M₁ M₂ M₃ t j)` at each call site.

2. **Verify `compose_elementaryWeight_decomp` signature**:
   ```
   grep -A 5 "private theorem compose_elementaryWeight_decomp" \
     OpenMath/Chapter3/Section381.lean
   ```
   Confirm signature: `(M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (t :
   RootedTree)` returning the M₁/M₂ decomposition.

3. **Verify `compose_b_castAdd` / `compose_b_natAdd` simp lemmas
   exist**: lines 2560 / 2565 per the file outline. Already-used
   inside `compose_elementaryWeight_decomp` at lines 2831, 2833.

4. **Verify cycle 221's template**: read
   `Section381.lean:4046-4098` (the `compose_equivalent_compose_assoc`
   + `composeQ_assoc` block). These are the structural models for
   cycle 233's P1 and P2.

5. **Verify cycle 232's namespace context**: read
   `Section381.lean:3218-3227` to confirm
   `compose_phiEquivalent_compose` is in `namespace
   OpenMath.Chapter3.Section312.RKTableau` and the `section ... end`
   wrapper closed at line 3227.

If any pre-flight check fails (file moved, name changed, etc.), STOP
and report the divergence rather than freelancing.

## §E — Pre-flagged risks

**R1 — Argument order for cycle 230/231 mutual lemmas in `rw`**: the
mutual lemmas use `(t : RootedTree) (j : Fin _)` order — tree first,
stage second. Confirmed by existing call sites at lines 2928, 3007,
3017. Use this order verbatim. If `rw` fails because of motive /
unification issues, the explicit form `rw
[derivativeWeightWithSrc_compose_castAdd (M₁ := M₁) (M₂ := M₂) (M₃ :=
M₃) (t := t) (j := j)]` may be needed.

**R2 — `Fin.sum_univ_add` direction**: `rw [Fin.sum_univ_add]`
rewrites `∑ i : Fin (n + m), f i` LEFT-TO-RIGHT to `(∑ j : Fin n, f
(castAdd m j)) + ∑ k : Fin m, f (natAdd n k)`. This is the direction
used by `compose_elementaryWeight_decomp`'s body (line 2828). If the
`show ... from ?_` hole doesn't close cleanly, verify direction by
removing the `?_` placeholder, inserting `?`, reading the residual
goal.

**R3 — `Quotient.inductionOn₃` motive**: P2's proof uses
`Quotient.inductionOn₃` (not `Quotient.ind₃` — different motive
inference). Cycle 221's `composeQ_assoc` uses
`Quotient.inductionOn₃` successfully; follow that template
verbatim.

**R4 — `PhiEquivalent` heterogeneous-stage `@` prefix**: `@PhiEquivalent
((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))` makes the heterogeneous-stage
nature explicit. The `@` prefix is essential because Lean's
elaborator will try to unify the two stage counts otherwise. Same
idiom as cycle 221's `@Equivalent.{u} ((s₁ + s₂) + s₃) (s₁ + (s₂ +
s₃))` (note: cycle 221 also uses universe `.{u}` because
`Equivalent`'s body is universe-polymorphic; **`PhiEquivalent` is
NOT universe-polymorphic** so no `.{u}` annotation is needed —
confirmed by cycle 223 strategy notes documenting that
`PhiEquivalent.setoid` and `.setoidSigma` dropped `.{u}`).

**R5 — Namespace placement**: cycle 232's
`compose_phiEquivalent_compose` is inside `namespace
OpenMath.Chapter3.Section312.RKTableau` (look at the namespace
structure around lines 2849, 3198, 3218). P1 must go in the same
namespace. P2 must also go in the same namespace because it
references `composeQ_phi` (also in `…Section312.RKTableau`).

**R6 — `compose_b_*` simp lemma firing**: `@[simp] compose_b_castAdd
: (M₁.compose M₂).b (Fin.castAdd s₂ j) = M₁.b j` unfolds
LEFT-TO-RIGHT. In the P1 auxiliary, the `show ... from ?_` goal will
have `(M₂.compose M₃).b (Fin.castAdd s₃ j)` on the LHS, which `rw
[compose_b_castAdd]` rewrites to `M₂.b j`. Mirror for
`compose_b_natAdd`.

**R7 — Cycle 230/231 lemma visibility**: both are `private`. In Lean
4, `private` declarations are visible within the same file (not just
the same namespace), so they are accessible from a new theorem in
the same file. If a "private declaration not visible" error fires,
something else is wrong — re-check the file path.

**R8 — `congr 1` depth on the RHS sum-decomposition auxiliary**: the
`show ... from ?_` aux goal has shape `∑ i, _ = (∑ j, _) + ∑ k, _`.
After `rw [Fin.sum_univ_add]`, the LHS becomes `(∑ j, _) + ∑ k, _`
matching the RHS structurally. `congr 1` peels off the outer `_ +
_`, leaving two sub-goals: `∑ j, _ = ∑ j, _` and `∑ k, _ = ∑ k, _`.
Each closes by `Finset.sum_congr rfl + per-summand rw`. If `congr 1`
fails, try `congr` (let it auto-pick depth).

**R9 — Section/end wrapper imbalance**: when inserting P1's new
`section / open OpenMath.Chapter3.Section310 / end` wrapper, ensure
the `end` is matched. After inserting, `grep -c "^section$"
Section381.lean` and `grep -c "^end$" Section381.lean` should each
increase by 1 (i.e. the difference stays the same). The supervisor's
end-of-file check catches imbalances.

## §F — Time and LOC budget

- P1 (`compose_assoc_phiEquivalent`): ~30 LOC body + ~15 LOC
  docstring.
- P2 (`composeQ_phi_assoc`): ~6 LOC body + ~10 LOC docstring.
- P3 non-vacuity examples: ~15 LOC total.
- Total: ~80 LOC, well below the cycle 232 deliverable's ~280 LOC
  size.

Warm rebuild of `Section381.lean` should complete in <20 s. If the
first warm rebuild takes >60 s, something is wrong — kill and
inspect the diagnostics; don't assume timeout means GPFS recovery.

## §G — Mandatory pre-commit checks

Before `git add` / `git commit`:

1. **`grep -c sorry OpenMath/Chapter3/Section381.lean`** — must be 0.
   Cycle 232's deliverables left sorry count at 0; do not regress.
2. **`lake build OpenMath.Chapter3.Section381`** — must exit 0
   (warnings on `linter.unusedSimpArgs` are tolerable; errors are
   not).
3. **`#print axioms`** on both new public theorems, via either
   `lean_verify` MCP (in-file, fresh-olean) or a
   `/tmp/check_axioms.lean` helper after `lake build`. Expected:
   `[propext, Classical.choice, Quot.sound]` only. **No
   `sorryAx`.**
4. **Regression spot-checks (lean_verify, one each)**:
   - `OpenMath.Chapter3.Section312.RKTableau.compose_phiEquivalent_compose`
     (cycle 232 landmark)
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi` (cycle
     232 landmark)
   - `OpenMath.Chapter3.Section312.RKTableau.compose_equivalent_compose_assoc`
     (cycle 221 — the analog template at the `Equivalent` level)

   All three should remain `[propext, Classical.choice, Quot.sound]`.

5. **Faithfulness check (mandatory per CLAUDE.md)**:
   - Open `extraction/formalization_data/entities/thm_384A.json` for
     the textbook `thm:384A` statement.
   - Confirm that `compose_assoc_phiEquivalent` captures the
     "associativity at the elementary-weight level" content. Strictly
     speaking, `thm:384A` is "Φ is a group homomorphism", which
     decomposes as: (a) associativity of `composeQ_phi` (this cycle's
     P2), (b) preservation of identity (a future cycle's work —
     cycle 228/229's partial-action identity laws need to be
     generalized to full-binary identity laws on `composeQ_phi`),
     (c) preservation of inverses (a future cycle's work). Cycle 233
     ships part (a) only.
   - **Document the divergence** in P1's docstring: this is the
     associativity axiom at the elementary-weight level, mirroring
     cycle 221's `compose_equivalent_compose_assoc` at the
     `Equivalent` level. The full `Group` instance (combining
     associativity, identity, inverse axioms) on `Quotient
     PhiEquivalent.setoidSigma` remains a multi-cycle deliverable;
     this cycle ships the associativity piece.

## §H — Failure modes and recovery

**F1 — P1 proof fails on `rw [compose_elementaryWeight_decomp ...]`
chain**: the lemma signature may have drifted. Check via
`lean_hover_info` or `lean_local_search` for
`compose_elementaryWeight_decomp` — verify its current signature
matches `(M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (t : RootedTree) :
(M₁.compose M₂).elementaryWeight t = M₁.elementaryWeight t + ∑ i, …`.
If it does, the rw should fire. If it doesn't, fall back to
`unfold compose_elementaryWeight_decomp` or rewriting via the
underlying `Fin.sum_univ_add` + `derivativeWeight_compose_*` chain
directly (as inlined at lines 2824-2833).

**F2 — `rw [Fin.sum_univ_add]` fails on the auxiliary `show ... from
?_` hole**: try the explicit form `rw [show ∑ i : Fin (s₂ + s₃), _ =
_ + _ from Fin.sum_univ_add (...)]` with explicit instantiation. If
that also fails, fall back to `Finset.sum_eq_sum_of_image` or an
explicit `Finset.sum_bij` reindex. As a last resort, rewrite the goal
via `show` to expose the bare sum and apply `Fin.sum_univ_add` at the
universe-polymorphic position.

**F3 — Cycle 230/231 mutual lemma `rw` fails with "could not
synthesize implicit argument"**: pass named arguments
`(M₁ := M₁) (M₂ := M₂) (M₃ := M₃) (t := t) (j := j)`. Try named-arg
form first; if that also fails, the signature has drifted —
investigate.

**F4 — P3 non-vacuity `example` fails**: most likely cause is
incorrect `paddedEuler` stage count (`2`) in the type annotation.
`paddedEuler : RKTableau 2`. Three-factor composite at stage counts
`((2 + 2) + 2)` vs `(2 + (2 + 2))` is heterogeneous (because Lean's
`Nat.add` is right-associative-recursive). Use `@PhiEquivalent` to
defeat unification. Trace cycle 232's heterogeneous P2 examples for
the exact pattern.

**F5 — If P1 cannot be closed cleanly in the cycle budget (>60 min of
real work on the proof body)**: abort P1, **revert** any partial
edits, and ship **P3 alternative**: promote a couple of inline
`example` blocks from cycle 232 to named theorems (analogous to cycle
186/196's example→theorem promotions). This is a smaller deliverable
that keeps sorry count at 0 and provides marginal value while
preserving the cycle's clean-record. **Do NOT ship a sorry-scaffold
of P1** — sorry-increase has cost cycles 200/215 −2 each.

## §I — Cycle 234+ outlook

Once cycle 233 lands P1+P2:

1. **Cycle 234**: full-binary identity laws on `composeQ_phi`. Two
   theorems generalizing cycles 228/229's partial-action identities
   to `Quotient.inductionOn` arguments: `composeQ_phi_id_left :
   composeQ_phi ⟦⟨0, RKTableau.id⟩⟧ q = q` and
   `composeQ_phi_id_right : composeQ_phi q ⟦⟨0, RKTableau.id⟩⟧ = q`.
   Each ~10 LOC.

2. **Cycle 235**: inverse respects PhiEquivalent. This is the §383
   analog of cycle 222's `inverse_equivalent_inverse`. Requires
   showing `PhiEquivalent M M' → PhiEquivalent M.inverse M'.inverse`
   — non-trivial; likely needs a tree-induction argument on the
   elementary weight of the inverse method. May need an Aristotle
   batch.

3. **Cycle 236+**: inverse absorption laws (`composeQ_phi q
   (inverseQ_phi q) = ⟦id⟧` and symmetric). Requires cycle 235 plus
   §383's textbook inverse-construction analysis.

4. **Cycle 237+**: assemble the `Group` instance on `Quotient
   PhiEquivalent.setoidSigma` via `Group.ofLeftAxioms`, consuming
   cycles 233/234/235/236.

5. **Cycle 238+**: define the homomorphism Φ : `Quotient
   Equivalent.setoidSigma → Quotient PhiEquivalent.setoidSigma`
   (already half-implicit via cycle 207-208's bridge lemmas) and
   prove it is a group homomorphism (the literal `thm:384A`
   statement). With the §382 group (cycle 222) and §383 group (cycle
   237) both available, this becomes a `MonoidHom` packaging
   exercise.

Cycle 233 is one of four substantive pieces toward the §383 `Group`
instance + `thm:384A` formalization. After it lands, the path to
closing `thm:384A` is well-scoped at ~5–7 cycles.

## §J — DO NOT

- Do NOT attempt §441 Phase C.2 (GPFS-blocked, 46 cycles).
- Do NOT submit anything to Aristotle.
- Do NOT raise `maxHeartbeats` above 200000 (CLAUDE.md hard limit).
- Do NOT introduce `axiom`/`constant` declarations.
- Do NOT ship a sorry-scaffold of P1 if the proof stalls — abort and
  ship P3 alternative (named theorem promotions).
- Do NOT edit `scripts/autonomous_loop.py` (loop-maintainer only).
- Do NOT modify cycles 230/231's mutual lemmas — they're load-bearing
  for the cycle 232 right-action and this cycle's associativity.
- Do NOT add `.{u}` annotations to `PhiEquivalent`-flavored theorems
  — `PhiEquivalent` is NOT universe-polymorphic (per cycle 223
  discovery).
