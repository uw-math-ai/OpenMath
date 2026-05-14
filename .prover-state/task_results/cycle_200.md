# Cycle 200 Results

## Worked on

* **Priority 1 — `thm:381H` statement-only scaffold** (Butcher §380, p. 304,
  "Equivalence of equivalences"). Shipped
  `OpenMath.Chapter3.Section312.RKTableau.equivalent_iff_pEquivalent_iff_phiEquivalent`
  at `OpenMath/Chapter3/Section381.lean:1613` with one of four iff
  directions closed axiom-clean and three tracked sorries documented in
  `.prover-state/issues/thm_381H_deferred.md`.
* **P0 — GPFS smoke test on Section441.lean** — 20th consecutive timeout
  (cycle 182–200; 19 calendar days). Logged in
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.

## Approach

### P0 GPFS smoke test

* Pre-flight `ps -u $USER` showed no D-state processes.
* `time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean` →
  EXIT=124, real 5m0.032s, user 0m0.245s, sys 0m0.718s. CPU = 0.32% of
  wall. Identical near-zero-CPU pattern to cycles 182–199.
* Per strategy decision tree: pathological state confirmed, pivoted to
  Priority 1 without retry.

### Priority 1 — thm:381H

1. **Verified file state**: HEAD = `3ac0841` (cycle 199), 1720 LOC,
   0 sorries — matched strategy expectations.

2. **Read textbook prose**: `extraction/raw_text/ch03.txt:8627–8667` —
   the four-direction proof structure (P-equivalence ⇒ equivalence ⇒ Φ
   omitted, then the three direct implications + one contradiction).
   Quoted textbook statement (line 8627–8628):
   > Two Runge–Kutta methods are equivalent if and only if they are
   > P-equivalent and if and only if they are Φ-equivalent.

3. **Read entity JSON**: `extraction/formalization_data/entities/thm_381H.json`.
   Confirmed `statement_text` matches the raw text. No discrepancy.
   Dependencies list cites `def:381D` and `def:381F` (LLM-identified);
   the textbook proof additionally invokes thm:381G in two of four
   directions but the JSON doesn't list it explicitly — noting here
   for future pipeline auditing.

4. **Pre-flight Grep** on `Section381.lean` verified:
   * `Equivalent` at line 967 in `RKTableau` namespace (no extra
     hypotheses — matches Butcher's def:381A).
   * `PEquivalent` at line 428 in `RKTableau` namespace.
   * `PhiEquivalent` at line 122 in `Section381` namespace
     (universally quantified over `RootedTree`).
   * `PEquivalent.toPhiEquivalent` at line 1553 — confirmed it does
     real work (destructures the existential common reduct, applies
     `PhiEquivalent.of_pReducesTo` to both legs which itself recurses
     through `pReduced_phiEquivalent` / `zeroReduced_phiEquivalent`,
     cycles 187/188 era).

5. **Statement form decision**: Per strategy, used the two-iff
   conjunction
   `(Equivalent M M' ↔ PEquivalent M M') ∧ (PEquivalent M M' ↔ PhiEquivalent M M')`
   rather than `List.TFAE`. Reads as direct transcription of the
   textbook's chained-iff phrasing and is symmetric to the existing
   §381 idiom.

6. **Proof body**:
   * `refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩` to split the conjunction and the
     two iffs into four goals.
   * Direction `PEquivalent → PhiEquivalent`: closed in one line via
     `exact PEquivalent.toPhiEquivalent`.
   * Other three directions: `intro _h; sorry` with per-sorry comments
     citing the textbook lines and the blocking infrastructure
     (thm:381G or Banach fixed-point), cross-referenced to
     `thm_381H_deferred.md`.

7. **Insertion site**: Placed in the `RKTableau` namespace block at
   `Section381.lean:1545–1642` (the small block opened to host
   `PEquivalent.toPhiEquivalent` and `PReducesTo.toPhiEquivalent`),
   immediately after `PReducesTo.toPhiEquivalent`. This keeps the
   cycle 187 lemma and its consumer co-located.

8. **Verification**:
   * `time lake env lean OpenMath/Chapter3/Section381.lean` → EXIT=0,
     real 0m53.948s (within the 60s expected envelope). Three sorry
     warnings, two pre-existing unused-variable warnings.
   * `#print axioms OpenMath.Chapter3.Section312.RKTableau.equivalent_iff_pEquivalent_iff_phiEquivalent`
     → `[propext, sorryAx, Classical.choice, Quot.sound]` — matches
     the "acceptable" target from the strategy (sorryAx expected
     given three tracked deferrals).
   * Sorry count: 3 (verified via `grep -n "  sorry$"`).
   * File size: 1720 → 1793 LOC (+73 LOC for theorem + docstring).

9. **Issue file**: `.prover-state/issues/thm_381H_deferred.md` written
   with per-direction breakdown of which textbook lines + which
   blocking infrastructure each sorry depends on, plus an estimated
   cycle budget table.

10. **Bookkeeping**:
    * `lean_status.json`: thm:381H → `partial` with `lean_file`,
      `lean_symbol`.
    * `plan.md`: thm:381H row from `[ ]` → `[~]` with cycle 200
      summary.

## Result

**SUCCESS** — Strategy Priority 1 delivered within target sorry
budget (3 of "at most 4"). File compiles axiom-clean modulo three
tracked sorries each with a precise blocker citation. Cycle 200 is
a clean landmark: the cycle caps the 8-cycle PEquivalent arc
(cycles 192–200) by shipping the textbook landmark theorem
`thm:381H` as a stable, well-documented scaffold ready for
thm:381G + Banach-fixed-point continuation work in later cycles.

## Faithfulness check

### `equivalent_iff_pEquivalent_iff_phiEquivalent` (thm:381H)

* **Entity ID**: `thm:381H` (Butcher §380, p. 304)
* **Textbook statement** (quoted from `entities/thm_381H.json`
  `statement_text`, cross-verified against `raw_text/ch03.txt:8627–8628`):
  > Two Runge–Kutta methods are equivalent if and only if they
  > are P-equivalent and if and only if they are Φ-equivalent.
* **Lean statement**:
  ```
  theorem equivalent_iff_pEquivalent_iff_phiEquivalent
      {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') :
      (Equivalent M M' ↔ PEquivalent M M') ∧
      (PEquivalent M M' ↔ PhiEquivalent M M')
  ```
* **Lean statement captures**: **same content**. The textbook's
  chained-iff phrasing ("A iff B iff C") is encoded as the two-iff
  conjunction `(A ↔ B) ∧ (B ↔ C)`, which is logically equivalent
  to TFAE on {A, B, C}.
* **Hypothesis strength**: matches Butcher exactly — universally
  quantified over `(M : RKTableau s) (M' : RKTableau s')`, no extra
  irreducibility / preconsistency / stability hypotheses. This is
  the "all methods" variant from cycle 200 strategy's faithfulness
  reminder, not a restricted special case.
* **Tautology check**: conclusion is a two-iff conjunction; no
  hypothesis appears verbatim as the conclusion. ✓
* **Identity check**: only one of four directions is closed and
  that closure is via `PEquivalent.toPhiEquivalent` which performs
  real recursion through the P-reduction proof tree (not `:= h`
  or `:= Iff.rfl`). The remaining three directions are explicit
  `sorry`s with comments. ✓
* **Definition smuggling check**: `Equivalent` (def:381A),
  `PEquivalent` (def:381F), and `PhiEquivalent` (def:381B) are
  all defined independently in the file from their textbook
  meanings, not as characterizations of each other. Confirmed
  by re-reading lines 122 (PhiEquivalent: ∀ tree elementary
  weights agree), 428 (PEquivalent: common reduct via PReducesTo),
  and 967 (Equivalent: same one-step output for every Lipschitz
  autonomous IVP at small step). Thm:381H is a genuine
  interrelation result, not a smuggle. ✓

## Dead ends

None — strategy was followed straight through. No tactic attempts
failed because three of four directions were explicitly deferred
per strategy guidance, and the closed direction is a one-line
`exact`.

## Discovery

* The cycle 198 entity JSON for `thm:381H` doesn't list `thm:381G`
  as a dependency despite the textbook proof of two of four
  directions citing it directly. This is an extraction-pipeline
  imprecision (LLM-derived dependencies missed an implicit
  thm:381G invocation through Butcher's prose). Not actionable
  for cycle 200 worker but should be flagged for future
  pipeline auditing — `extraction/extensions/extra_references.json`
  could add `thm:381H → thm:381G` once thm:381G is formalised.
* The `PEquivalent → Equivalent` direction is **not** blocked on
  thm:381G — it's blocked on Banach fixed-point convergence for
  the implicit-stage iteration. This is a strictly easier
  prerequisite than thm:381G + tableau-combine and could be
  attacked independently in a future cycle. The deferred-sorries
  issue file structures the three sorries by their distinct
  blockers for this reason.
* The two-iff conjunction form
  `(A ↔ B) ∧ (B ↔ C)` reads more naturally than
  `List.TFAE [A, B, C]` for a 3-way equivalence — destructuring
  via `refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩` gives the four directions as
  named tactic-mode goals in a predictable order, which is
  easier to maintain than the `tfae_have` machinery would have
  been.

## Suggested next approach

For the cycle 201 planner. Several roughly-parallel options
(distinct dependency tracks):

1. **Banach-fixed-point track** (unblocks `PEquivalent → Equivalent`):
   ~2–3 cycles. Build `ContractingWith` infrastructure for the
   implicit-stage iteration `Yᵢ = y₀ + h • Σⱼ aᵢⱼ • f(Yⱼ)` at small
   `h`. Lower mathematical risk than thm:381G — Mathlib has
   `ContractingWith` and `fixedPoint` lemmas already; the work is
   mostly packaging the RK stage system into Mathlib's expected
   form. Side benefit: unblocks `Equivalent M M` reflexivity (the
   issue file `equivalent_self_general_deferred.md` from cycle 188
   era).

2. **thm:381G prerequisite track** (unblocks both `PhiEquivalent → PEquivalent`
   and `Equivalent → PEquivalent`): ~4–5 cycles total. Per cycle 199
   recon, requires thm:314A (independence of elementary
   differentials, itself 2–3 cycles) + subalgebra-of-elementary-
   weights infrastructure in ℝˢ (another 1–2 cycles). High
   mathematical complexity but unblocks two sorries simultaneously.

3. **Confluence track** (unblocks general
   `pEquivalent_irreducible_reduct_unique`, complements but
   doesn't directly unblock thm:381H sorries): per
   `p_reduction_confluence_gap.md` from cycle 199. Closes
   `PEquivalent.trans` and `def:381E reducedMethod` infrastructure
   gaps but is orthogonal to thm:381H.

4. **Section441 GPFS** — 20 consecutive timeouts. Recommend the
   strategy explicitly stop attempting the smoke test for a while
   (e.g. skip P0 for cycles 201–205 and re-test once) since 20
   data points confirm pathological state. Saves ~5 minutes per
   cycle without losing diagnostic value. Alternative: investigate
   whether the Section441 file can be split into smaller
   subfiles to reduce the olean-load surface.

5. **Promote underused cycle 198/199 examples** — cosmetic but
   the `example :` blocks at `Section381.lean:1693–1719` from
   cycle 196/199 could be promoted to named lemmas if any
   downstream uses arise. Low-priority.

**Recommendation**: Track 1 (Banach fixed-point). Lowest risk,
single concrete deliverable (`PEquivalent → Equivalent`), and
the infrastructure unblocks an orthogonal §380 sorry
(`Equivalent` reflexivity) as a side benefit. Track 2
(thm:381G/thm:314A) is the higher-value but longer path; track 1
gets cycle 201 a clean ship while track 2 spins up in parallel
later.
