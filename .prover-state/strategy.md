# Cycle 358 Strategy — Phase D.3.a of `def:422B`

## §A — Headline target

**Ship Phase D.3.a** per `.prover-state/issues/def_422B_phase_D_3_scoping.md`
§5 and §7: the per-tree elementary-weight expansion lemmas that
generalise cycle 341's vertex-case P1/P2/P3 (`elementaryWeightQ_phi_{mul,inv,zpow}_vertex`)
to arbitrary trees `t = mk children`.

This is the **mandatory** cycle 358 deliverable. Cycle 357 closed the
5-LMM × 3-theorem consumer matrix at `r(t) = 1`; Phase D.3 is the
unique remaining multi-cycle content gap before Phase E sealing.

**Do NOT attempt D.3.b in this cycle.** D.3.b (linear coefficient
extraction "coefficient of η(t) in η⁻ⁱ(t) = i(−1)^r(t)") consumes
D.3.a as input; one-phase-per-cycle is the discipline (cycle 343's
Phase D.2 alone is the precedent).

## §B — Why this target, not something else

* **Sorry count is 0** at HEAD; no rollback work pending.
* **No pending Aristotle results** to incorporate.
* **No blocker issue** is actionable as worker work this cycle —
  `eq422a_eta_phase_D_prime_step_2_scoping.md` (β-side non-negativity)
  is genuinely multi-cycle infrastructure work parallel to Phase D.3
  and not a single-cycle ship.
* **Phase D.3.a is well-scoped** (~150 LOC, 1 cycle estimate) per the
  cycle 357 scoping doc §5.
* The 22-cycle §422 streak (cycles 336–357) has consistently scored
  2 since cycle 353; continue compounding before pivoting.

Alternative pivot candidates (cycle 359+ if planner judges §422
streak length is a problem): `def:442A` (principal sheet, definition-
only ship), `thm:535A` (one-step underlying method for GLMs),
`thm:541A` (DIMSIM types). These are NOT cycle 358's job.

## §C — Concrete deliverables

### §C.1 — Three named theorems (the headline)

Append the following three theorems to
`OpenMath/Chapter4/Section422.lean` immediately after cycle 341 P3
(`elementaryWeightQ_phi_zpow_vertex` at line ~433, ending ~460).
Place them BEFORE the section heading for cycle 342's
`Eq422a_at_vertex_linear` block (so the Phase D pre-infrastructure
remains grouped).

**D.3.a.1 — `elementaryWeightQ_phi_mul_mk`** (additivity in
representative form). Recommended signature:

```lean
/-- *Phase D.3.a (cycle 358) — representative-form additivity:* at an
arbitrary tree `t`, the elementary weight of a §383 group product
decomposes into the LHS-representative's elementary weight plus a
bottom-block contribution involving the source-method-threaded
`derivativeWeightWithSrc` of the RHS representative. Lifts cycle 239's
`elementaryWeightQ_phi_composeQ_phi_mk` from `composeQ_phi` notation to
the `*` notation used by `Eq422a`.

At `t = vertex` the bottom-block collapses to `M₂.elementaryWeight
vertex` and recovers cycle 341 P1's symmetric additivity — but at
arbitrary `t` the bottom-block depends on `M₁`'s elementary weights,
so the asymmetric representative form is unavoidable. -/
theorem elementaryWeightQ_phi_mul_mk
    {s₁ s₂ : ℕ}
    (M₁ : OpenMath.Chapter3.Section312.RKTableau s₁)
    (M₂ : OpenMath.Chapter3.Section312.RKTableau s₂)
    (t : RootedTree) :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩) *
         (Quotient.mk PhiEquivalent.setoidSigma ⟨s₂, M₂⟩)) t
      = elementaryWeightQ_phi
          (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩) t
        + ∑ i : Fin s₂, M₂.b i * M₂.derivativeWeightWithSrc M₁ i t
```

Proof (mechanical port of cycle 341 P1's `_vertex` proof at line 408):
```lean
  show elementaryWeightQ_phi (composeQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩)
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₂, M₂⟩)) t = _
  exact elementaryWeightQ_phi_composeQ_phi_mk M₁ M₂ t
```

The `show` step unfolds `*` to `composeQ_phi` via cycle 236's
`instMul_phi`. Estimated ~10 LOC including docstring.

**D.3.a.2 — `elementaryWeightQ_phi_inv_mk`** (inverse, characterization
form). Recommend the **indirect form** via `mul_inv_cancel`:

```lean
/-- *Phase D.3.a (cycle 358) — representative-form inverse
characterization:* at an arbitrary tree `t`, the elementary weight
of the §383 group inverse satisfies the linear equation derived from
`η_q * η_q⁻¹ = 1` and `Φ_1(t) = 0`. Generalises cycle 341 P2's
`_vertex` to arbitrary trees, returning a characterization rather
than a closed form (the bottom-block residual couples
`η_q⁻¹`'s representative with `M`'s). -/
theorem elementaryWeightQ_phi_inv_mk
    {s : ℕ} (M : OpenMath.Chapter3.Section312.RKTableau s)
    (t : RootedTree) :
    elementaryWeightQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)⁻¹ t
      = - elementaryWeightQ_phi
            (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) t
        - (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc
            (Classical.choose
              (?_ : ∃ M', Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩⁻¹
                          = Quotient.mk PhiEquivalent.setoidSigma ⟨s, M'⟩)) i t)
```

**Risk flag**: the `Classical.choose` representative extraction is
ugly. A cleaner formulation: use cycle 236's `inverseQ_phi_mk`
(check Section381.lean around line 4260 for the exact name and
shape) which should give a definitional reduction
`⟦⟨s, M⟩⟧⁻¹ = ⟦⟨s, M.inverse⟩⟧` for cycle 222's `M.inverse :
RKTableau s`. Then the RHS becomes:

```lean
    elementaryWeightQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M.inverse⟩) t
      = - elementaryWeightQ_phi
            (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) t
        - ∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i t
```

This is the same shape as D.3.a.1 with `M₁ := M.inverse, M₂ := M`,
applied to `mul_inv_cancel`'s identity. **Use this form** if
`inverseQ_phi_mk` exists.

Proof (mirroring cycle 341 P2 at line 419–425): obtain
`h_cancel : ⟦⟨s, M⟩⟧ * ⟦⟨s, M⟩⟧⁻¹ = 1` from `mul_inv_cancel`. Apply
`elementaryWeightQ_phi_eq_of_eq` (cycle 239) at `t` to get
`Φ_{M·M⁻¹}(t) = Φ_1(t) = 0`. Use cycle 239's `elementaryWeightQ_phi_id`
to collapse `Φ_1(t) = 0`. Use D.3.a.1 to expand the LHS, then
rearrange.

If the closed form via `inverseQ_phi_mk` is unavailable, ship the
characterization form

```lean
elementaryWeightQ_phi η_q⁻¹ t + elementaryWeightQ_phi η_q t
  + (∑ i, M.b i * M.derivativeWeightWithSrc <inv-rep> i t) = 0
```

as an `iff`/`=`-shaped predicate (with the representative-form
caveat documented). Estimated ~20–30 LOC.

**D.3.a.3 — `elementaryWeightQ_phi_zpow_mk`** (integer power,
representative form). Recommended signature:

```lean
/-- *Phase D.3.a (cycle 358) — representative-form integer power:*
at an arbitrary tree `t`, the elementary weight of the §383 integer
power expands via repeated application of D.3.a.1 (positive exponents)
or D.3.a.2 (negative exponents). Generalises cycle 341 P3's `_vertex`
to arbitrary trees. -/
theorem elementaryWeightQ_phi_zpow_mk
    {s : ℕ} (M : OpenMath.Chapter3.Section312.RKTableau s)
    (t : RootedTree) (n : ℤ) :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) ^ n) t
      = ... (recursive expansion in n) ...
```

**Risk flag (high)**: the bottom-block residual at integer power may
not have a simple closed form. At `t = vertex` cycle 341 P3 closed
because the bottom-block collapsed to `M₂.elementaryWeight vertex`
on every iteration. At arbitrary `t`, each `pow_succ` step introduces
a fresh bottom-block depending on the previous power's representative
— the recursion does not telescope.

**Recommended fallback for D.3.a.3**: ship only the **natural-number
base case** as a recursive identity (e.g. `Φ_{η^(m+1)}(t) = ... + Σ
M.b i · M.derivativeWeightWithSrc (η^m's rep) i t`), and document
that the closed form generalising cycle 341 P3 is deferred to Phase
D.3.b (where the coefficient extraction will need to unpack the
recursion explicitly).

**If D.3.a.3's recursive identity won't close in a single cycle**,
ship D.3.a.1 + D.3.a.2 only and defer D.3.a.3 to cycle 359 per the
§C.4 graceful-degradation plan.

### §C.2 — Non-vacuity witnesses

After each named theorem, append a small `example` exercising it at
a concrete higher-order tree such as `RootedTree.cherry` (= `mk
[vertex]`). Recommended pattern (mirror cycle 341 P4 non-vacuity at
line 462+):

```lean
/-- Non-vacuity for D.3.a.1 at `cherry`. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) *
         (Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩)) RootedTree.cherry
      = elementaryWeightQ_phi
          (Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩) RootedTree.cherry
        + ∑ i : Fin 1,
            RKTableau.explicitEuler.b i *
            RKTableau.explicitEuler.derivativeWeightWithSrc
              RKTableau.explicitEuler i RootedTree.cherry :=
  elementaryWeightQ_phi_mul_mk
    RKTableau.explicitEuler RKTableau.explicitEuler RootedTree.cherry
```

One `example` per shipped theorem (so 3 if all three land, 2 if
D.3.a.3 is deferred). Estimated ~20–30 LOC.

### §C.3 — Mandatory pre-flight (do these BEFORE writing any code)

1. **Read `elementaryWeightQ_phi_composeQ_phi_mk`** at
   `OpenMath/Chapter3/Section381.lean:4730–4742`. Confirm the output
   shape:
   `(M₁.compose M₂).elementaryWeight t = M₁.elementaryWeight t +
   Σ i, M₂.b i · M₂.derivativeWeightWithSrc M₁ i t`. This is the
   load-bearing lemma; D.3.a.1's proof is a one-line `exact`.

2. **Read cycle 341 P1's proof body** at
   `OpenMath/Chapter4/Section422.lean:395–409`. The recipe is:
   `Quotient.inductionOn` × 2, `obtain ⟨s, M⟩ := p`, `show ... = _`,
   `rw [elementaryWeightQ_phi_composeQ_phi_mk]`, `congr 1`. D.3.a.1's
   proof drops the `Quotient.inductionOn` (since the signature takes
   representatives directly) and the `congr 1` (since we want the
   asymmetric form, not the symmetric vertex collapse).

3. **Verify cycle 236's `inverseQ_phi_mk` exists and check its shape**
   at `OpenMath/Chapter3/Section381.lean` (search around line 4260):
   does `⟦⟨s, M⟩⟧⁻¹` unfold definitionally to `⟦⟨s, M.inverse⟩⟧` for
   cycle 222's `M.inverse : RKTableau s`? If yes, D.3.a.2 ships in
   the clean form. If no, D.3.a.2 ships the characterization form
   per §C.1.

4. **Confirm `RKTableau.derivativeWeightWithSrc` is in scope** at the
   call site (`Section422.lean`). It is — cycle 239's
   `elementaryWeightQ_phi_composeQ_phi_mk` uses it, and Section422
   already imports Section381.

5. **Aristotle alive check**: if delegating any sub-lemma, run
   `mcp__aristotle__list_projects` to confirm Aristotle is up.
   Single submission per CLAUDE.md discipline. **Not expected to be
   needed**: D.3.a.1 is a 5-line proof; D.3.a.2 / D.3.a.3 are
   mechanical ports of cycle 341 P2 / P3.

### §C.4 — Graceful degradation (if D.3.a.3 stalls)

If D.3.a.3's integer-power expansion proves intractable in a single
cycle (high risk per §C.1):

* **Ship D.3.a.1 + D.3.a.2 only** (~30 LOC + 2 examples). This is a
  legitimate Phase D.3.a partial ship.
* Update `.prover-state/issues/def_422B_phase_D_3_scoping.md` §5 to
  split D.3.a into D.3.a.{1,2} (cycle 358) and D.3.a.3 (cycle 359).
* Cycle 359 worker then has a focused, scoped D.3.a.3 target.

**Do NOT ship D.3.a.3 with a `sorry`.** Per the cycle 200/201 and
149/150 rollback precedents, sorry-first scaffolds for multi-cycle
multi-sub-phase targets get rolled back. Partial ship is fine; sorry
is not.

### §C.5 — Documentation updates

* `extraction/formalization_data/lean_status.json`: `def:422B` row
  cycle reference bumps 357 → 358, status remains `partial` (Phase
  D.3.a is not Phase E sealing).
* `plan.md`: append a single line to the `def:422B` partial-state
  paragraph documenting cycle 358's Phase D.3.a ship.
* `.prover-state/issues/def_422B_phase_D_3_scoping.md`: append a
  "Cycle 358 update" subsection to §5 noting the Phase D.3.a
  deliverables (which sub-deliverables shipped, which deferred).
* `.prover-state/task_results/cycle_358.md`: standard sections.

## §D — Risks (NOT mistakes — anticipate these)

### §D.1 — RHS shape design

The cycle 358 worker must decide: do the three theorems use the
**asymmetric representative form** (cycle 239's `_mk` shape) or do
they attempt a **quotient-invariant abstract form**?

**Recommend asymmetric.** Reasons:

* Cycle 239's `elementaryWeightQ_phi_composeQ_phi_mk` (the
  load-bearing decomposition) is already representative-form. Its
  docstring at line 4727–4729 explicitly states "the bottom-block
  sum's stage count `s₂` does not descend to the abstract
  Φ-quotient."
* Cycle 341 P1's `_vertex` form is symmetric only because the bottom
  block collapses at vertex. At arbitrary `t`, no such collapse
  occurs.
* Phase D.3.b's linear-coefficient extraction will need the
  asymmetric form anyway.

Don't attempt the abstract form unless D.3.a.1's proof closes in
under 5 LOC — at which point the asymmetric form is essentially free
and you've gained nothing by abstracting.

### §D.2 — `RKTableau` namespace prefix verbose-ness

The theorems sit in `Section422`'s namespace
`OpenMath.Chapter4.Section422`, but reference `RKTableau` which lives
in `OpenMath.Chapter3.Section312.RKTableau`. Cycle 341's existing
code uses long prefixes (`OpenMath.Chapter3.Section312.RKTableau.id`)
without complaint. If signature lines get unwieldy, add a `local
open OpenMath.Chapter3.Section312 in` block around the new theorems,
matching whatever pattern cycle 341 used.

### §D.3 — `inverseQ_phi_mk` definitional unfolding for D.3.a.2

The recommended clean form for D.3.a.2 depends on cycle 236's
`inverseQ_phi_mk` giving a definitional reduction
`⟦⟨s, M⟩⟧⁻¹ = ⟦⟨s, M.inverse⟩⟧`. If `inverseQ_phi_mk` is `@[simp]`
or `rfl`, this should work via `show`. If it's a propositional
equality, use `rw [inverseQ_phi_mk]` instead.

**If `M.inverse` doesn't exist** (cycle 222 may have shipped only
the quotient-level `inverseQ_phi` without a representative-level
`RKTableau.inverse`), ship the characterization form per §C.1's
fallback wording.

### §D.4 — `composeQ_phi` definitional unfolding

Cycle 341 P1's proof uses `show` to expose `*` as `composeQ_phi`.
This works because `instMul_phi.mul = composeQ_phi` definitionally.
If `show` fails on the new theorems, fall back to:

```lean
have h_mul : (Quotient.mk _ ⟨s₁, M₁⟩) * (Quotient.mk _ ⟨s₂, M₂⟩)
    = composeQ_phi (Quotient.mk _ ⟨s₁, M₁⟩)
                   (Quotient.mk _ ⟨s₂, M₂⟩) := rfl
rw [h_mul]
```

One extra line, more robust to elaboration order issues.

### §D.5 — Mathlib hook drift

All hooks used are project-internal (cycle 239, cycle 236, cycle
341, cycle 222). No new Mathlib lemmas required. Low risk.

### §D.6 — Cycle-336-style rollback risk

The scoping doc §6.2 explicitly flags Phase D.3.a wrong-shape as a
risk. **Mitigation**: do not commit to a signature until §C.3
pre-flight is done. If `elementaryWeightQ_phi_composeQ_phi_mk`'s
shape doesn't match the strawman in §C.1, stop and file a sub-issue
rather than writing `sorry`-bearing scaffolding.

## §E — What NOT to try

* Do **NOT** attempt D.3.b (linear coefficient extraction) in cycle
  358. Per scoping doc §5 and §7.
* Do **NOT** attempt D.3.c (`Σᵢ i·αᵢ ≠ 0` from stability). Multi-
  cycle prerequisite work requiring polynomial-root infrastructure.
* Do **NOT** attempt the `noncomputable def underlyingOneStepMethod_aux`
  recursion (D.3.d). Multi-cycle, needs D.3.a–c first.
* Do **NOT** introduce sorries. Partial ship (D.3.a.1 + D.3.a.2 only,
  defer D.3.a.3) is acceptable; sorry-first scaffolds are not. The
  cycle 200/201 (`thm:381H`) and 149/150 (`def:530B`) rollback
  precedents apply.
* Do **NOT** modify cycle 239 `elementaryWeightQ_phi_composeQ_phi_mk`,
  cycle 236 `inverseQ_phi` / `composeQ_phi` infrastructure, cycle
  222 `RKTableau.inverse`, or cycle 341 P1/P2/P3 vertex theorems.
  Build on top of them.
* Do **NOT** ship a "symmetric quotient-invariant" form for D.3.a.1
  unless it closes in under 5 LOC. The asymmetric representative
  form is correct, matches cycle 239's load-bearing shape, and
  Phase D.3.b needs it.
* Do **NOT** rename `elementaryWeightQ_phi_composeQ_phi_mk` or
  shadow it. The new theorems are wrappers, not replacements.
* Do **NOT** attempt to lift `derivativeWeightWithSrc` to the
  quotient level. It's a representative-only construct by design
  (see `Section381.lean:2660–2700` for the mutual recursion
  structure).
* Do **NOT** modify `scripts/autonomous_loop.py` or any harness
  code. Loop-maintainer territory per
  `tautology_scanner_false_positives.md`.
* Do **NOT** attempt to compile `OpenMath/Chapter4/Section441.lean`
  (43+ consecutive GPFS timeouts since cycle 182 per
  `cycle_182_gpfs_slowness.md`). Phase D.3.a does NOT need it; cite
  §451 ρ-stability via existing exports (`bdf2LMM_isStable`,
  `bdf3LMM_isStable`) without recompiling §441.
* Do **NOT** raise `maxHeartbeats`. If a proof stalls, decompose
  into smaller helpers or accept the partial-ship route in §C.4.
* Do **NOT** pivot to a fresh entity unless §C.3 pre-flight reveals
  Phase D.3.a's recommended shape is genuinely wrong. Cycle 357
  shipped a 22-cycle §422 streak at score 2 — continue compounding
  unless there's a hard blocker.

## §F — Cycle budget

* §C.3 pre-flight (5 mins): read 3 file regions, confirm shapes.
* §C.1 D.3.a.1 (10 mins): one-line proof + docstring + non-vacuity.
* §C.1 D.3.a.2 (20 mins): mul_inv_cancel route + docstring +
  non-vacuity. If `inverseQ_phi_mk` doesn't give a clean form, ship
  characterization form per §C.1.
* §C.1 D.3.a.3 (30 mins, high-risk): port cycle 341 P3 verbatim with
  `t` instead of `vertex`. If bottom-block residual blows up, ship
  partial.
* §C.2 non-vacuity (10 mins): up to 3 `example`s on
  `RKTableau.explicitEuler`.
* §C.5 documentation (10 mins): lean_status, plan.md, scoping doc
  update, cycle_358.md.
* Aggregate compile + axiom check (5 mins).

**Total**: ~90 mins. Comfortable single-cycle budget.

## §G — Success criteria (in priority order)

1. **Three named theorems shipped axiom-clean** (D.3.a.1 + D.3.a.2
   + D.3.a.3), each with non-vacuity. Sorry count 0. Cycle scores 2.
2. **D.3.a.1 + D.3.a.2 shipped, D.3.a.3 deferred to cycle 359 with
   scoping doc updated.** Sorry count 0. Cycle scores 2 with
   graceful-degradation note in task results.
3. **D.3.a.1 shipped only.** Sorry count 0. Cycle scores 1 with
   substantial structural progress; D.3.a.2 + D.3.a.3 punted to
   cycle 359 with explicit scope re-decomposition.
4. **Pre-flight reveals Phase D.3.a's recommended shape is wrong;
   filed sub-issue, no Lean shipped.** Sorry count 0. Cycle scores
   1 if the sub-issue is concrete and actionable for cycle 359;
   else 0.

Avoid criterion 4 if at all possible — it's the cycle-336 §A.0
pre-flight equivalent and signals a planning gap. If §C.3 pre-flight
confirms `elementaryWeightQ_phi_composeQ_phi_mk`'s shape matches the
strawman, proceed to criterion 1.

## §H — Cycle 359+ outlook

If Phase D.3.a closes cleanly (criterion 1):

* **Cycle 359**: Phase D.3.b (linear coefficient extraction). Per
  scoping doc §5: ~100 LOC, depends on D.3.a, ships
  `coeff_eta_t_in_eta_zpow_neg` (the textbook "coefficient of η(t)
  in η⁻ⁱ(t) is i(−1)^r(t)" claim).
* **Cycle 360**: Phase D.3.c (`Σᵢ i·αᵢ ≠ 0` from stability via
  ρ'(1) ≠ 0). Mathlib polynomial-root infrastructure-dependent;
  ~80 LOC, low Aristotle suitability.
* **Cycle 361**: Phase D.3.d (`underlyingOneStepMethod_aux` recursion
  + spec lemma). Closes `thm:422A` substantive content; ~120 LOC.
* **Cycle 362**: Phase E (lift + seal `def:422B`).

Phase D.3.a is the critical-path enabler. If it ships, the §422
ladder has 4 more cycles before sealing.

If Phase D.3.a partial (criterion 2 or 3):

* Cycle 359 worker absorbs the deferred D.3.a sub-deliverables
  before moving to D.3.b. Adds one cycle to the §422 horizon.

## §I — Quick reference summary

| Field | Value |
|---|---|
| Headline target | Phase D.3.a of `def:422B` |
| Source plan | `.prover-state/issues/def_422B_phase_D_3_scoping.md` §7 |
| Three deliverables | `elementaryWeightQ_phi_{mul,inv,zpow}_mk` |
| Load-bearing hook | `elementaryWeightQ_phi_composeQ_phi_mk` (cycle 239, Section381.lean:4730) |
| Vertex precedent | cycle 341 P1/P2/P3 (Section422.lean:395–460) |
| Sorry budget | 0 (no sorries allowed; partial ship preferred over scaffolding) |
| LOC budget | ~150 (10 + 30 + 60 + 30 + 20) |
| Cycle budget | ~90 min |
| Pre-flight | §C.3 mandatory |
| Graceful degradation | §C.4 (ship D.3.a.1+2, defer D.3.a.3) |
| Out of scope | D.3.b/c/d; Phase E sealing; β-side non-negativity; fresh entity pivot |
