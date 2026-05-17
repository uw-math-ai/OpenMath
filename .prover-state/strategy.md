# Strategy — cycle 361

## TL;DR

Ship **Phase D.3.b inductive-step infrastructure** in
`OpenMath/Chapter4/Section422.lean`:
1. **P1 (load-bearing)**: ship the ℤ-form lift
   `elementaryWeightQ_phi_zpow_mk` (cycle 360 explicitly deferred this).
2. **P2 (substantive)**: ship `linearResidualAt_depends_only_on_strict_subtrees`
   (the "depends only on strict subtrees" parametricity claim) via
   strong induction on `t.order` using cycle 343's
   `WellFoundedRelation RootedTree := measure RootedTree.order`.
3. **Fallback** (if P2 stalls): extend the cycle 360 closed-form
   ladder with `linearResidualAt_two_mk_eq` (mechanical port of
   `_one_mk_eq` at `i = 2`).

Target: 80–120 LOC, axiom-clean, sorry count 0. Per the cycle 360
task results §"Suggested next approach", this is the natural
single-cycle deliverable. §422 streak extends to 27 axiom-clean
cycles.

**No Aristotle this cycle.** The strong-induction structure is
delicate and poorly suited; cycle 360's worker noted this
explicitly. Manual closure only.

## §A — Context

* **Cycle 360 shipped** (axiom-clean, 0 sorries): four new public
  symbols at `OpenMath/Chapter4/Section422.lean:1797–1969`:
  - `linearResidualAt (i : ℕ) (η_q : Q) (t : RT) : ℝ` (def)
  - `coeff_eta_t_in_eta_zpow_neg` (split form)
  - `linearResidualAt_vertex_eq_zero` (base case at τ)
  - `linearResidualAt_one_mk_eq` (closed form at `i = 1` at any tree)
* **Cycle 360 deferred** the ℤ-form lift `elementaryWeightQ_phi_zpow_mk`
  per the cycle 359 task results' §C.4 graceful degradation. The
  exact signature was left to be pinned by Phase D.3.b's consumption
  requirements — which is cycle 361's job.
* **§422 streak**: 26 consecutive axiom-clean cycles (336–360).
* **Scoping doc**: `.prover-state/issues/def_422B_phase_D_3_scoping.md`
  §5 ladder: D.3.b (signature + base cases, cycle 360 ✅) → D.3.b
  (inductive step, **cycle 361 target**) → D.3.c
  (`sum_i_alpha_ne_zero_of_stable`, cycle 362) → D.3.d
  (`underlyingOneStepMethod_aux`, cycle 363) → Phase E sealing
  (cycle 364).
* **GPFS** for Section441 still degraded (43+ consecutive timeouts).
  Section422 compiles fine — keep all work there.

## §B — Cycle 361 deliverables (priority order)

### P1 (load-bearing) — ℤ-form lift `elementaryWeightQ_phi_zpow_mk`

**Target signature**:

```lean
theorem RKTableau.elementaryWeightQ_phi_zpow_mk
    {s : ℕ} (M : RKTableau s) (n : ℤ) (t : RootedTree) :
    elementaryWeightQ_phi (⟦⟨s, M⟩⟧ ^ n) t =
      -- representative-form closed expression depending on:
      --   * n's sign (ofNat vs negSucc),
      --   * cycle 359's `M.powRep` for the positive-power side,
      --   * cycle 358's `M.inverse` for the negative-power side
      sorry
```

**Implementation strategy**: case-split on `n` via
`match n with | Int.ofNat m => … | Int.negSucc m => …`:

* **`n = Int.ofNat m` case**: `⟦M⟧ ^ ↑m = ⟦M.powRep m⟧` (cycle 359's
  `powRep_quotient_eq`). Then `elementaryWeightQ_phi ⟦M.powRep m⟧ t`
  reduces to representative form via cycle 226's
  `elementaryWeightQ_phi_mk`.
* **`n = Int.negSucc m` case**: `⟦M⟧ ^ (Int.negSucc m) = (⟦M⟧^(m+1))⁻¹`
  via `zpow_negSucc`. Compose cycle 359's `powRep_quotient_eq` with
  cycle 358's `elementaryWeightQ_phi_inv_mk` (or compose cycle 222's
  `inverseQ_phi_mk` with the positive case at `m + 1`).

**LOC budget**: ~30–50 LOC. Most lines are sign-case bookkeeping.

**Why P1 first**: cycle 360's `linearResidualAt_one_mk_eq` only
handles `i = 1` via the special-case bridge `Nat.cast_one + zpow_neg_one`.
For general `i ≥ 2`, the inductive step (P2) needs to evaluate
`Φ_{η_q^(-i)}(t)` at arbitrary trees, which requires this lift.

### P2 (substantive) — `linearResidualAt_depends_only_on_strict_subtrees`

**Target signature** (per scoping doc §5 cycle-361 slot):

```lean
theorem RKTableau.linearResidualAt_depends_only_on_strict_subtrees
    (i : ℕ) (η_q η_q' : Quotient PhiEquivalent.setoidSigma) (t : RT)
    (h_strict : ∀ s : RT, s.order < t.order →
      elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    linearResidualAt i η_q t = linearResidualAt i η_q' t
```

**Proof recipe**:

1. Apply strong induction on `t.order` via cycle 343's
   `WellFoundedRelation RootedTree := measure RootedTree.order`. The
   recipe is:
   ```lean
   induction t using WellFoundedRelation.wf.induction with
   | _ t ih => …
   ```
   or equivalently use `WellFounded.induction` on the underlying
   `wf` field of the cycle 343 instance.
2. **Vertex base case** (`t = vertex`, `r(t) = 1`, no strict subtrees):
   `h_strict` is vacuous; both sides reduce to `0` via cycle 360's
   `linearResidualAt_vertex_eq_zero`.
3. **Inductive case** (`t = mk children`, `r(t) ≥ 2`):
   - Pick representatives `⟨s, M⟩ ∈ η_q` and `⟨s', M'⟩ ∈ η_q'` via
     `Quotient.inductionOn₂`.
   - Unfold `linearResidualAt` via P1's ℤ-form lift, exposing the
     residual as a representative-form expression involving
     `derivativeWeightWithSrc … j t` (and the primed counterpart).
   - Use the structural fact: `derivativeWeightWithSrc` at
     `t = mk children` recursively decomposes as a product over
     `c ∈ children`. Every recursive call hits a `c` with
     `c.order < t.order` (cycle 343's `order_lt_of_mem_children`).
   - Apply `h_strict` at each strict subtree to swap `M`'s
     elementary weights for `M'`'s, then apply the IH at each
     strict subtree to swap inner residuals.

**LOC budget**: ~50–80 LOC. The induction structure is the bulk.

**Risk profile**: MEDIUM-HIGH. The structural recursion through
`derivativeWeightWithSrc` is non-trivial. If P2 stalls past 60–90
min into the cycle, **fall back to §C below**.

### P3 (optional stretch) — Phase D.3.c parallel scoping

If P1 + P2 land cleanly with budget remaining, write a short
scoping appendix to `.prover-state/issues/def_422B_phase_D_3_scoping.md`
§5 Phase D.3.c (~30 lines) verifying Mathlib's polynomial-root-
multiplicity API for `sum_i_alpha_ne_zero_of_stable`. **No Lean
code for D.3.c this cycle** — D.3.c is the cycle 362 deliverable.

## §C — Graceful degradation fallback

If P2's strong-induction proof stalls past 60 minutes:

1. **Ship P1 standalone** (the ℤ-form lift). This unblocks downstream
   D.3.b/c/d work even without the parametricity claim.
2. **Ship `linearResidualAt_two_mk_eq`** as a mechanical port of
   cycle 360's `_one_mk_eq` at `i = 2`. Apply P1 at `n = -2`, use
   `zpow_neg` + `zpow_two` to expose `(η_q⁻¹)^2`, then compose
   cycle 358's `_inv_mk` with cycle 359's `_pow_succ_mk`. ~15 LOC.
3. **Ship `linearResidualAt_two_mk_eq` non-vacuity** on `explicitEuler`
   at `cherry`. ~3 LOC.
4. **Update scoping doc** to push the inductive step to cycle 362.

The fallback ladder preserves the streak (axiom-clean, no sorries)
while making concrete forward progress.

## §D — What NOT to try

* **Do NOT submit P2 to Aristotle.** Cycle 360 task results
  Discovery #3 noted parametricity-style induction is poorly
  suited to Aristotle's search. Manual closure only.
* **Do NOT rewrite `RootedTree.Vertex` infrastructure.** The cycle 343
  `WellFoundedRelation` + `order_lt_of_mem_children` infrastructure
  is sufficient. Avoid building new vertex/subtree machinery this
  cycle.
* **Do NOT use `induction t with | mk children ih =>`** for the P2
  proof. Per memory `feedback_rootedtree_nested_induction.md`,
  direct `induction t` fails on nested inductives. Use strong
  induction on `t.order` via the cycle 343 `WellFoundedRelation`
  instance.
* **Do NOT attempt Phase D.3.c (`sum_i_alpha_ne_zero_of_stable`)
  in the same cycle as P2.** Per scoping doc §5, D.3.c is a cycle
  362 deliverable. The polynomial-root-multiplicity Mathlib hooks
  (`Polynomial.rootMultiplicity`, derivative-of-multiple-root lemma)
  need separate verification; mixing with D.3.b risks both.
* **Do NOT raise `maxHeartbeats` above 200000.** If the P2 proof's
  inductive step is slow, decompose into private mutual helpers per
  cycle 358's `derivativeWeightWithSrc_subst_M₁` pattern.
* **Do NOT introduce `sorry`/`axiom`/`constant` declarations.** The
  cycle 200/201/149/150 rollback precedent applies. Either P2 lands
  axiom-clean or we fall back to §C without sorries.
* **Do NOT modify `Section441.lean`** — GPFS-blocked (43+ timeouts).
  Keep all work in `Section422.lean`.
* **Do NOT touch `RKTableau.id`'s `b` field signature** or any other
  upstream §381/§422 infrastructure. Cycle 337's `D_phi`/`D_element`
  design depends on the `b₀=1` implicit convention; modifying it
  would cascade-break the 26-cycle §422 chain.
* **Do NOT skip P1 and attempt P2 directly.** P2 at `i ≥ 2` needs
  the ℤ-form lift; cycle 360's `_one_mk_eq` special-case bridge
  (`Nat.cast_one + zpow_neg_one`) does not generalise.

## §E — Mathlib hooks to verify early (≤15 min budget)

Run `lean_local_search` / `lean_hover_info` on these *before*
writing P1/P2 proofs:

1. `Int.recOn` / `match n with | .ofNat m | .negSucc m` —
   for P1's sign case-split. `match` is likely cleanest.
2. `zpow_natCast` (or `zpow_ofNat`), `zpow_negSucc`, `zpow_neg`,
   `zpow_two` — the integer-power bridges. All confirmed present at
   HEAD via cycle 339's `D_element_zpow_*` non-vacuity ships.
3. `WellFoundedRelation.wf` field accessor and `WellFounded.induction`
   — for P2's strong induction. Cycle 343's instance lives at
   `OpenMath/Chapter3/Section301.lean:177`.
4. `RootedTree.order_lt_of_mem_children` (cycle 343) at
   `Section301.lean` — confirms subtree-strict-descent.
5. `Quotient.inductionOn` / `Quotient.inductionOn₂` — for P2's
   representative extraction (used pervasively cycles 226–360).

If any hook is missing or has drifted, file `.prover-state/issues/`
sub-issue and fall back to §C.

## §F — Faithfulness check pre-flight (mandatory before commit)

For P1 + P2:

* **Tautology check**: P1's conclusion is an explicit closed-form
  expression; does NOT appear as hypothesis. ✓ P2's conclusion is
  `linearResidualAt i η_q t = linearResidualAt i η_q' t`; the
  `h_strict` hypothesis is strictly weaker (only constrains values
  at strict subtrees). ✓
* **Identity check**: P1 invokes `powRep_quotient_eq` (cycle 359),
  `elementaryWeightQ_phi_mk` (cycle 226), and
  `elementaryWeightQ_phi_inv_mk` (cycle 358). All substantive. P2
  invokes strong induction + cycle 343 descent + cycle 360 base
  case + P1. All substantive.
* **Hypothesis strength check**: P2's `h_strict` quantifies over
  *strict* subtrees only (matching Butcher's "no other terms in
  η⁻ⁱ(t) with orders greater than r(t) − 1" verbatim). Stronger
  hypotheses would not be needed; weaker (e.g. only immediate
  children) might not suffice for the induction. Match to textbook
  exact.
* **Definition smuggling check**: P1's signature directly captures
  the on-quotient integer-power evaluation; no smuggling. P2's
  signature is parametricity, not the underlying coefficient claim
  — but per scoping doc §6.3, quotient-level statements are the
  project pattern, and the coefficient claim of cycle 360's
  `coeff_eta_t_in_eta_zpow_neg` already pins the η(t) coefficient
  as exactly `i·(-1)^r(t)`. P2's role is the "depends only on
  lower orders" half of the textbook claim. Match exact.

## §G — Time budget

| Phase                                  | Budget       |
|----------------------------------------|--------------|
| Mathlib hook verification (§E)         | ≤ 15 min     |
| P1 (ℤ-form lift)                       | 45–60 min    |
| P2 (parametricity inductive step)      | 60–90 min    |
| Faithfulness check + axiom verify      | ≤ 15 min     |
| `lake build` + `#print axioms`         | ≤ 5 min      |
| Task results + lean_status + plan.md   | 15 min       |
| **Cycle total**                        | **~3 hours** |

If §E reveals a Mathlib gap or P1 takes >60 min, abort P2 and ship
§C fallback (P1 + `linearResidualAt_two_mk_eq` + non-vacuity).
Either outcome preserves the streak; P2 success is the bonus.

## §H — Post-cycle housekeeping

1. **task_results/cycle_361.md** — standard sections per CLAUDE.md.
2. **lean_status.json** — leave `def:422B` row at `partial` (Phase E
   sealing still pending).
3. **plan.md** — append cycle 361 closure note to the `def:422B` row.
4. **def_422B_phase_D_3_scoping.md** — append "Cycle 361 update"
   subsection documenting P1 + P2 (or §C fallback) ships, mirroring
   cycles 358/359/360 update format.
5. **memory** — if a non-obvious Mathlib hook surprise comes up
   during §E verification, save a feedback memory.

## §I — Recap

* **Primary**: P1 (ℤ-form lift) + P2 (parametricity inductive step).
* **Fallback**: P1 + `linearResidualAt_two_mk_eq` + non-vacuity.
* **Both paths**: axiom-clean, 0 sorries, §422 streak extends to 27.
* **No Aristotle, no scaffolds, no GPFS-blocked files.**
* **Concrete entry point**: open `OpenMath/Chapter4/Section422.lean`
  at the end (after cycle 360's `linearResidualAt_one_mk_eq` block,
  line ~1900) and append P1.
