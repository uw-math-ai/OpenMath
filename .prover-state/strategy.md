# Cycle 219 Strategy — §382 group identity element on `Quotient Equivalent.setoidSigma`

## §A. GPFS smoke test (mandatory; ≤2 min)

§441 Phase C.2 has been GPFS-blocked for **35 consecutive cycles** (since
cycle 184). Worker MUST run **one** smoke test at start-of-cycle and abort
the §441 path if it times out:

```bash
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

* If it completes in <60s with EXIT=0 ⇒ GPFS recovered. Pivot to applying
  the cycle 182 draft + cycle 184 namespace fix per
  `.prover-state/issues/lem_441A_phase_C_scoping.md` Phase C.2 plan.
  This OVERRIDES the rest of this strategy.
* If it times out (EXIT=124) or shows the same near-zero CPU pattern
  (<2% CPU over 5 min wall) ⇒ skip §441, proceed with §B below. Append
  one line to `.prover-state/issues/cycle_182_gpfs_slowness.md`
  recording the 36th consecutive timeout. Do NOT escalate further;
  loop-maintainer is already notified via that issue.
* Do NOT spend more than the single smoke test on §441. Do NOT poll
  Aristotle for the cycle 183 draft submission (the namespace fix is
  already extracted; nothing new to gain by re-polling).

## §B. Primary deliverable — §382 group identity element

Cycle 218 closed both textbook forms of `thm:382A` (the bracketed (382f)
form via `composeQ_eq_of_equivalent` and the un-bracketed (382g) form
via `compose_equivalent_compose`). The natural cycle 219 next step is
the §382 group structure on `Quotient Equivalent.setoidSigma`,
specifically the **identity element** plus its **left and right
absorption laws**.

This is the cycle 218 task results' explicit "Suggested next approach"
recommendation: cycle 219 ships the identity + one-sided absorptions;
cycle 220 ships inverses; cycle 221+ associativity (which finally
finesses cycle 210's deferred `compose_assoc` HEq plumbing through
`Quotient.sound`).

### B.1. Why the 0-stage tableau is the right identity

In Butcher's §382 group, the identity satisfies `M ∘ id ≡ M` and
`id ∘ M ≡ M` for all `M`. Reading the cycle 209 `compose` definition
at `OpenMath/Chapter3/Section381.lean:2487`:

* `(M₁.compose M₂).b = Fin.append M₁.b M₂.b`
* The output of one composite step is `y₀ + H · ∑ᵢ (M₁.compose M₂).b i · f(Yᵢ)`.

If `M₁ : RKTableau 0` (the 0-stage tableau), its `b : Fin 0 → ℝ` is
the empty function. The 0-stage tableau contributes no stages and no
weight, so composing it on either side "does nothing". The textbook
identity is the no-op tableau.

`explicitEuler` is NOT the identity (it advances by `H · f(y₀)`,
which is exactly what we don't want from the identity).

### B.2. Concrete deliverables (priority order)

#### P1 — `RKTableau.id : RKTableau 0` (definition, ~5 LOC)

Insert at `OpenMath/Chapter3/Section381.lean` immediately after cycle
218's `composeQ_eq_of_equivalent` (around line ~2780, inside
`namespace OpenMath.Chapter3.Section312.RKTableau`):

```lean
/-- The §382 group identity element — the trivial 0-stage Runge–Kutta
tableau. Its single one-step output is `y₀` (the input value),
because the empty stage tuple gives an empty sum in the output
formula `y₁ = y₀ + h • ∑ (i : Fin 0), b i • f (Y i) = y₀`.

Together with `compose` (cycle 209), this furnishes the identity
element of the §382 group of equivalence classes of Runge–Kutta
methods (Butcher §382). The left and right absorption laws
`id.compose M ≡ M` and `M.compose id ≡ M` are proved as
`id_compose_equivalent` and `compose_id_equivalent` below; their
quotient-level corollaries `composeQ ⟦⟨0, id⟩⟧ q = q` and
`composeQ q ⟦⟨0, id⟩⟧ = q` follow by `Quotient.ind` + `Quotient.sound`. -/
def id : RKTableau 0 where
  A := fun i _ => Fin.elim0 i
  b := fun i => Fin.elim0 i
  c := fun i => Fin.elim0 i
```

(The `Fin.elim0` discharges the empty-domain functions; alternatively
the `0` literal if Lean infers `Zero` on the matrix and vector types.
Try `Fin.elim0` first; fall back to `0` if Lean accepts it more
cleanly. Don't spend more than 5 minutes on syntactic shape — the
type matters, not the body.)

#### P2 — `id_isRKOneStep_iff` helper (~10 LOC)

The 0-stage IsRKOneStep predicate collapses to `y₁ = y₀`. Ship as a
clean iff lemma immediately after `RKTableau.id`:

```lean
@[simp] theorem id_isRKOneStep_iff
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (y₀ : N) (h : ℝ) (y₁ : N) :
    RKTableau.id.IsRKOneStep f y₀ h y₁ ↔ y₁ = y₀ := by
  constructor
  · rintro ⟨Y, _hstage, hout⟩
    -- The output sum ∑ (i : Fin 0), id.b i • f (Y i) is empty.
    simp [RKTableau.id] at hout
    exact hout
  · intro hy
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · simp [RKTableau.id]; exact hy
```

This is the load-bearing reduction lemma for both P3 and P4 below.

#### P3 — `compose_id_equivalent` (right identity, easier; ~25 LOC)

Note: `s + 0 = s` IS definitionally equal in Lean 4 (`Nat.add` recurses
on the second argument). So this is a HOMOGENEOUS-stage `Equivalent
(s := s)` claim — no HEq plumbing needed.

Recipe:

```lean
theorem compose_id_equivalent.{u} {s : ℕ} (M : RKTableau s) :
    @Equivalent.{u} (s + 0) s (M.compose RKTableau.id) M := by
  intro N _ _ _ f L hL
  -- Reuse M's own equivalent_self threshold (cycle 203).
  obtain ⟨h₀, hh₀_pos, hM_uniq⟩ := M.equivalent_self f L hL
  refine ⟨h₀, hh₀_pos, ?_⟩
  intro y₀ H hH_pos hH_le y₁ y₁' h_compose h_M
  -- Decompose h_compose via cycle 214's iff:
  -- (M.compose id).IsRKOneStep f y₀ H y₁ ↔
  --   ∃ y_mid, M.IsRKOneStep f y₀ H y_mid ∧ id.IsRKOneStep f y_mid H y₁
  obtain ⟨y_mid, h_M_step, h_id_step⟩ :=
    (compose_isRKOneStep_iff M RKTableau.id f y₀ H y₁).mp h_compose
  -- id.IsRKOneStep f y_mid H y₁ ⇒ y₁ = y_mid (by P2)
  rw [id_isRKOneStep_iff] at h_id_step
  rw [h_id_step]
  -- Now y_mid and y₁' are both M.IsRKOneStep outputs from y₀; M's
  -- output uniqueness (equivalent_self) closes.
  exact hM_uniq y₀ H hH_pos hH_le y_mid y₁' h_M_step h_M
```

#### P4 — `id_compose_equivalent` (left identity; ~25 LOC)

This is the heterogeneous case `0 + s` vs `s`. While `0 + s = s` is
NOT defeq (it requires `Nat.zero_add`), the proof works at the
abstract `IsRKOneStep` level which doesn't inspect stage counts —
identical in shape to cycle 217's heterogeneous
`compose_equivalent_compose`.

Recipe (mirror of P3 with sides swapped):

```lean
theorem id_compose_equivalent.{u} {s : ℕ} (M : RKTableau s) :
    @Equivalent.{u} (0 + s) s (RKTableau.id.compose M) M := by
  intro N _ _ _ f L hL
  obtain ⟨h₀, hh₀_pos, hM_uniq⟩ := M.equivalent_self f L hL
  refine ⟨h₀, hh₀_pos, ?_⟩
  intro y₀ H hH_pos hH_le y₁ y₁' h_compose h_M
  obtain ⟨y_mid, h_id_step, h_M_step⟩ :=
    (compose_isRKOneStep_iff RKTableau.id M f y₀ H y₁).mp h_compose
  rw [id_isRKOneStep_iff] at h_id_step
  rw [h_id_step] at h_M_step
  exact hM_uniq y₀ H hH_pos hH_le y₁ y₁' h_M_step h_M
```

#### P5 — Quotient identity laws (≤15 LOC, stretch goal)

With cycle 218's `composeQ` and the two absorption lemmas from P3/P4
in hand, the Quotient-level identity laws follow by `Quotient.ind` +
`Quotient.sound`:

```lean
theorem composeQ_id_left.{u} (q : Quotient Equivalent.setoidSigma.{u}) :
    composeQ (Quotient.mk' ⟨0, RKTableau.id⟩) q = q := by
  refine Quotient.ind (motive := fun q => composeQ _ q = q) ?_ q
  rintro ⟨s, M⟩
  -- composeQ ⟦⟨0,id⟩⟧ ⟦⟨s,M⟩⟧ = ⟦⟨0+s, id.compose M⟩⟧ by Quotient.lift₂_mk
  -- Need: ⟦⟨0+s, id.compose M⟩⟧ = ⟦⟨s, M⟩⟧, i.e. setoidSigma related.
  apply Quotient.sound
  show @Equivalent.{u} (0 + s) s (RKTableau.id.compose M) M
  exact id_compose_equivalent M

theorem composeQ_id_right.{u} (q : Quotient Equivalent.setoidSigma.{u}) :
    composeQ q (Quotient.mk' ⟨0, RKTableau.id⟩) = q := by
  refine Quotient.ind (motive := fun q => composeQ q _ = q) ?_ q
  rintro ⟨s, M⟩
  apply Quotient.sound
  show @Equivalent.{u} (s + 0) s (M.compose RKTableau.id) M
  exact compose_id_equivalent M
```

These are the actual textbook content of "id is the identity element of
the §382 group". P5 should ship if P1–P4 land within budget; otherwise
defer to cycle 220 (alongside the inverse work).

#### P6 — Non-vacuity / sanity examples (~10 LOC)

After P5, exercise the laws on `paddedEuler` (in
`namespace OpenMath.Chapter3.Section381`, after the cycle 218 examples
near line ~2950):

```lean
example :
    composeQ (Quotient.mk' ⟨0, RKTableau.id⟩)
             (Quotient.mk' ⟨2, paddedEuler⟩)
      = Quotient.mk' ⟨2, paddedEuler⟩ :=
  composeQ_id_left _

example :
    composeQ (Quotient.mk' ⟨2, paddedEuler⟩)
             (Quotient.mk' ⟨0, RKTableau.id⟩)
      = Quotient.mk' ⟨2, paddedEuler⟩ :=
  composeQ_id_right _
```

### B.3. Minimum-viable cycle threshold

* **Must ship**: P1 (definition) + P2 (iff helper) + at least one of
  P3 or P4 (one absorption law). Sorry count must remain at 0.
* **Should ship**: P1 + P2 + P3 + P4 (both absorption laws) — the
  full §382-group-identity at the `Equivalent` level.
* **Stretch**: P1–P6 — the full `Quotient`-level identity laws with
  non-vacuity witnesses.

If only P1 + P2 + P3 ship, that's a +1 cycle (substantive but
incomplete). If P1–P4 ship, that's the standard cycle. If P1–P6 ship,
that's a strong cycle and unblocks cycle 220 to focus entirely on
inverses.

## §C. Risk register (pre-flighted, with mitigations)

### R1 (medium, mitigation pre-staged) — Empty-Finset.sum unfolding

`id.IsRKOneStep f y₀ H y₁` requires the worker to prove
`y₁ = y₀ + H • ∑ (i : Fin 0), id.b i • f(Y i)` collapses to
`y₁ = y₀`. The empty sum reduces via `Finset.sum_empty` (or
`Fin.sum_univ_zero`) to `0`, and `H • 0 = 0`, then `y₀ + 0 = y₀`.
`simp [RKTableau.id]` should fire all of this; if it doesn't, add
`Finset.sum_empty` or `Fin.sum_univ_zero` explicitly to the simp set.

If `simp` still fails, decompose: `have hsum : (∑ (i : Fin 0), ...) = 0
:= Finset.sum_empty` (or `Fin.sum_univ_zero`) followed by `rw [hsum,
smul_zero, add_zero]`.

### R2 (low) — `Fin.elim0` for the `RKTableau.id` definition

The `A : Matrix (Fin 0) (Fin 0) ℝ` field could be defined as:
* `fun i _ => Fin.elim0 i` (case-split on the impossible domain)
* `0` (the zero matrix, if Lean infers `Zero` on `Matrix (Fin 0) (Fin 0) ℝ`)
* `Matrix.of (fun i _ => Fin.elim0 i)`

Try `fun i _ => Fin.elim0 i` first (matches `b` and `c` style). If
Lean rejects, fall back to `0`. If both fail, use
`Matrix.of (fun i _ => Fin.elim0 i)`. Don't spend more than 5 minutes
on this — the definition's body matters less than its type.

### R3 (low) — Heterogeneous-stage `Equivalent.{u}` annotation in P4

P4's signature uses `@Equivalent.{u} (0 + s) s ...` — explicit `.{u}`
on the universe and explicit instance annotation on the source/target
stage counts. This pattern is from cycle 217 (which generalised
`compose_equivalent_compose` to heterogeneous stages). If Lean infers
the universe correctly, the `.{u}` may be omittable; if it complains
about universe metavariables (cycle 204/206 precedent), add the
explicit annotation back.

### R4 (medium) — `compose_isRKOneStep_iff` arity at `M = id`

Cycle 214's iff takes `M₁ : RKTableau s₁` and `M₂ : RKTableau s₂` as
explicit arguments. When invoked with `M₁ := RKTableau.id` (so
`s₁ := 0`), Lean should infer `s₁ = 0` from the type of `RKTableau.id`,
but if it complains about the implicit `s₁` not being inferred, pass
`s₁ := 0` explicitly: `compose_isRKOneStep_iff (s₁ := 0) RKTableau.id
M f y₀ H y₁`.

### R5 (low) — `Quotient.ind` motive inference in P5

`Quotient.ind` requires the `motive` to be specified when not
trivially inferable. The recipe above passes
`motive := fun q => composeQ _ q = q`; if Lean infers a different
motive and complains, supply it explicitly with the underscore
replaced by the concrete identity-class expression.

### R6 (negligible) — RKTableau is NOT universe-polymorphic

Cycle 218 hit this: spurious `.{u}` annotations on `RKTableau s`
binders cause "too many explicit universe levels" errors. Only
`Equivalent.{u}` and `Equivalent.setoidSigma.{u}` carry universe
annotations. The `RKTableau` references in P3/P4 should NOT have
`.{u}`.

## §D. Pre-flighted Mathlib hooks (no MCP search needed for cycle 219)

All needed Mathlib lemmas are already in scope from prior cycles:

| Need | Lemma | Source |
|------|-------|--------|
| Empty `Fin 0` sum | `Fin.sum_univ_zero` or `Finset.sum_empty` | `Mathlib.Algebra.BigOperators.Fin` |
| Empty function | `Fin.elim0` | `Mathlib.Data.Fin.Basic` |
| Quotient induction | `Quotient.ind` | `Init.Core` |
| Quotient soundness | `Quotient.sound` | `Init.Core` |
| Cycle 214's iff | `RKTableau.compose_isRKOneStep_iff` | `Section381.lean:2670` |
| Cycle 203's M.equivalent_self | `RKTableau.equivalent_self` | `Section381.lean:1802` |
| Cycle 218's composeQ | `RKTableau.composeQ` | `Section381.lean:~2750` |
| Cycle 218's lift₂_mk reduction | `Quotient.lift₂_mk` | `Init.Core` (auto-fires by `rfl`) |

If MCP search is needed for any other lemma, **rate-limit-conserve**:
do at most one `lean_loogle` and one `lean_local_search` for the
entire cycle. Cycle 218 used exactly one loogle and shipped clean.

## §E. Build and verification protocol

1. Edit `OpenMath/Chapter3/Section381.lean` per §B above.
2. Run `time lake env lean OpenMath/Chapter3/Section381.lean`. Expect
   warm rebuild ~6s; cold ~8s (per cycles 213–218 baseline). If it
   exceeds 30s wall, something is wrong — abort and re-examine.
3. Run `lean_verify` on each new symbol:
   * `OpenMath.Chapter3.Section312.RKTableau.id` — should be a
     definition with no axiom output, or `[propext, Classical.choice,
     Quot.sound]` if any classical machinery sneaks in.
   * `OpenMath.Chapter3.Section312.RKTableau.id_isRKOneStep_iff` —
     `[propext, Classical.choice, Quot.sound]`.
   * `OpenMath.Chapter3.Section312.RKTableau.compose_id_equivalent` —
     same.
   * `OpenMath.Chapter3.Section312.RKTableau.id_compose_equivalent` —
     same.
   * (P5/P6) the Quotient laws and examples — same.
4. Re-verify cycle 218 landmarks (`composeQ`,
   `composeQ_eq_of_equivalent`) and cycle 217's
   `compose_equivalent_compose` for no-regression. All should remain
   axiom-clean.
5. Sorry count must remain at 0:
   `grep -c '\bsorry\b' OpenMath/Chapter3/Section381.lean` → 0.

## §F. Tolerances and abort thresholds

* **Cycle compile time**: warm rebuild >30s ⇒ investigate before
  committing; >60s ⇒ abort and roll back, file an issue.
* **R4 firing**: if `compose_isRKOneStep_iff` arity issues require >15
  minutes of debugging, ship P1 + P2 + P3 only and defer P4.
* **R1 firing**: if the empty-Finset.sum collapse takes >30 minutes
  to discharge, ship P1 + P2 only with a clean signature for P3/P4
  documented in `.prover-state/issues/thm_382A_path.md`. Sorry count
  must NOT rise.
* **Total cycle time**: target ~45 minutes for P1–P4; ~60 minutes for
  P1–P6. If approaching 90 minutes, ship what's done and defer the
  rest.

## §G. Post-cycle housekeeping

After successful build + axiom verification:

1. Update `extraction/formalization_data/lean_status.json`:
   * `thm:382A` row stays `formalized` (cycle 218's bracketed form is
     the headline; cycle 219 adds group-structure infrastructure not a
     new entity-level closure).
   * Append a brief `note` field addition noting the cycle 219
     identity-element work, similar to cycle 217/218 cumulative notes
     on `def:381A`'s row.

2. Update `plan.md`:
   * Extend the `thm:382A` row's note with one-line cycle 219 summary.
   * If P5+P6 ship (Quotient laws + non-vacuity), the §382 group
     structure progress is substantive enough to mention in the row's
     forward-looking pointer.

3. Update `.prover-state/issues/thm_382A_path.md`:
   * Append a "Cycle 219 update — §382 group identity element shipped"
     section documenting the four/six new symbols + the cycle 220
     entry point (inverse element). ~30–60 lines.

4. Update `.prover-state/issues/compose_assoc_HEq_plumbing.md`:
   * Append a "Cycle 219 update" note that the Quotient-level
     associativity (cycle 221+ target) can now be approached via
     `Quotient.sound` on an `Equivalent`-level `compose_assoc`,
     finessing the on-the-nose HEq blocker. The `composeQ_assoc`
     theorem becomes a `Quotient.ind₃` + `Quotient.sound` corollary
     of an `Equivalent`-level associativity claim.

5. Write `.prover-state/task_results/cycle_219.md` per the standard
   template (Worked on / Approach / Result / Faithfulness check / Dead
   ends / Discovery / Suggested next approach).

## §H. What NOT to try

* **Do NOT attempt cycle 210's deferred `compose_assoc` HEq plumbing
  directly.** That blocker (`compose_assoc_HEq_plumbing.md`) is
  finessable through `Quotient.sound` (cycle 221+ target), NOT through
  HEq dance. Cycle 219 ships identity, period.

* **Do NOT attempt the inverse element this cycle.** Butcher §382's
  inverse construction requires reading the textbook carefully (the
  formula transforms `(c, A, b)` non-trivially). That's a cycle 220
  deliverable with its own pre-flight scoping.

* **Do NOT use `explicitEuler` as the identity.** It's a 1-stage method
  that advances by `H · f(y₀)`, not the no-op identity. The 0-stage
  tableau is the unique no-op.

* **Do NOT modify `compose`, `Equivalent`, `setoidSigma`, or
  `composeQ`.** All four are settled (cycles 209, 206, 212, 218
  respectively); cycle 219 only adds new symbols, doesn't refactor
  existing ones.

* **Do NOT re-poll Aristotle for the cycle 183 §441 draft submission.**
  The namespace fix is already extracted; nothing new to gain.

* **Do NOT introduce `axiom` or `constant` declarations.** Per
  CLAUDE.md.

* **Do NOT increase `maxHeartbeats`.** If a proof times out, decompose
  per CLAUDE.md.

* **Do NOT spend cycle time on the GPFS phantom-verdict pattern.**
  Cycles 176–197 documented this exhaustively; the loop maintainer
  is notified. One smoke test is enough.

* **Do NOT cherry-pick easier fresh-entity work** (e.g. opening
  `def:451A` or `def:422B`) instead of the §382 group identity.
  The §382 group structure is the strategically most valuable
  immediate continuation given cycle 218's `composeQ` infrastructure
  is one cycle old. Pivoting to a fresh entity now would strand
  `composeQ` without a clear next consumer.

## §I. Rationale for prioritization

Cycle 218 successfully closed both forms of `thm:382A` and shipped
`composeQ` as the group operation. Cycles 219 (identity), 220
(inverse), and 221+ (associativity) form the natural three-cycle
sequence to package `Quotient Equivalent.setoidSigma` as a Lean
`Group` instance.

Each step is cleanly bounded and has a known recipe:

* **Cycle 219 (identity)**: pre-flighted in this strategy (§B).
* **Cycle 220 (inverse)**: requires reading Butcher §382's inverse
  construction formula. Distinct cycle of work, with its own pre-flight.
* **Cycle 221+ (associativity)**: finesses cycle 210's deferred
  `compose_assoc` HEq blocker via Quotient. Distinct cycle.
* **Cycle 222+ (Group instance)**: package as `instance : Group
  (Quotient Equivalent.setoidSigma)`. Pure bookkeeping once the
  three axioms are in place.

This is a 4-cycle commitment to closing §382's group structure. Each
cycle is bounded and produces axiom-clean theorems. After §382
group structure is complete, natural follow-ons include §383 (group
homomorphisms via Φ), §384 (homomorphism to the elementary-weight
group), and §388 (subgroups and quotient groups) — all of which
consume the §382 `Group` instance directly.

If §441 GPFS recovers at any point in this 4-cycle window, that
work takes precedence (cycle 182 draft + cycle 184 namespace fix are
ready to ship). Until then, the §382 group track is the right
investment.
