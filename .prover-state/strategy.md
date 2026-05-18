# Cycle 378 strategy — §422 Sub-lemma A: extend the 7-tree ladder to `mk [mk [cherry]]` (8th tree, depth-3 ladder)

## A. State of play (read first)

* **Sorry count: 1 code sorry** at `OpenMath/Chapter4/Section422.lean:2279` —
  the cycle 365 grandfathered Sub-lemma A body
  `powRep_sum_eq_of_strict_subtree_agreement`. This sorry quantifies
  `∀ t : RootedTree`, so it is gated on Phase α' (recursive
  `inversePolynomial` covering arbitrary trees), which is multi-cycle.
* **§422 axiom-clean streak**: 42 substantive + 1 doc (cycles 336–377).
  Preserve.
* **7-tree ladder fully bridged** (cycle 377): `inversePolynomial`
  pattern-matches on `vertex, cherry, broom₃, mk [cherry], bushy,
  mk [broom₃], mk [vertex, cherry]`, with Phase β (forward bridge,
  per-tree + `_on_ladder` aggregator) and Phase γ (closed-subtree
  agreement) covering all 7.
* **Plan ahead**:
  `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` —
  Phase decomposition α → β → γ → δ → ε. Phase δ (general `m` via
  `powRep` induction) requires the inner-tableau heterogeneity issue
  (cycle 366 analysis) to be resolved, which requires Phase α'
  (recursive `inversePolynomial`).

## B. Why cycle 378 is NOT Phase δ or Phase α'

The cycle 377 worker's suggestion "Phase δ.B (general m via powRep
induction)" sounds tractable but has a fundamental obstacle. The
induction step `Φ_{η_q^(-(m+1))}(t) = Φ_{η_q'^(-(m+1))}(t)` requires
expanding via cycle 358's `_mul_mk`:

```
Φ_{η_q^(-m) · η_q⁻¹}(mk cs) = Φ_{η_q^(-m)}(mk cs) +
    Σⱼ M_q⁻¹.b j · M_q⁻¹.derivativeWeightWithSrc M_p j (mk cs)
```

The `M_q⁻¹.b` and `M_p` are representative-specific. Comparing the
η_q-side and η_q'-side requires bridging across **different stage
counts** (the inner-tableau heterogeneity from cycle 366). That
bridge is exactly the missing infrastructure Phase α' provides
(via a polynomial reformulation independent of stage counts).

So Phase δ on the ladder hits the same wall as the sorry'd
Sub-lemma A body. Don't attempt it without Phase α' machinery.

Phase α' itself is a multi-cycle research effort: the closed forms
for the 7 trees (cycles 341/367–372) don't fit a single obvious
recursive scheme. The combinatorial structure of the coefficients
(`Σⱼₖₗ b_j A_{jk} A_{kl} = Φ_η(mk [cherry])`, etc.) requires
careful analysis. Defer to a multi-cycle planning effort.

## C. Cycle 378 target: ship `mk [mk [cherry]]` (depth-3 ladder of cherry)

This is cycle 372 worker's deferred Option 2 from its task results.
It is the **8th tree** in the ladder, mechanistically extending
cycles 369 (`mk [cherry]`) and 371 (`mk [broom₃]`) with one more
depth layer. Provides empirical data for the future Phase α'
combinatorial-recipe identification.

### Closed-form value (pre-computed; worker should verify and ship)

Let `v := Φ_η(vertex)`, `c := Φ_η(cherry)`, `m := Φ_η(mk [cherry])`,
`M := Φ_η(mk [mk [cherry]])`. The textbook claim:

```
Φ_{η_q⁻¹}(mk [mk [cherry]]) = v⁴ − 3v²·c + c² + 2v·m − M
```

**Derivation** (worker should re-derive on paper before shipping).
Apply cycle 358's `elementaryWeightQ_phi_inv_mk`:

```
Φ_{⟦M⟧⁻¹}(mk [mk [cherry]])
  = − Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j (mk [mk [cherry]])
```

Unfold the inner `derivativeWeightWithSrc` four times (tree has
depth 4: `mk [mk [cherry]]` → `mk [cherry]` → `cherry` → `vertex`):

```
M.derivativeWeightWithSrc M.inverse j (mk [mk [cherry]])
  = M.inverse.eW (mk [cherry])
    + Σ_k M.A_{jk} · [M.inverse.eW cherry
                      + Σ_l M.A_{kl} · [M.inverse.eW vertex
                                        + Σ_m M.A_{lm}]]
  = (−v³ + 2vc − m)
    + Σ_k M.A_{jk} · (v² − c)
    + Σ_k M.A_{jk} · Σ_l M.A_{kl} · (−v)
    + Σ_k M.A_{jk} · Σ_l M.A_{kl} · Σ_m M.A_{lm}
```

Sum against `M.b j`, using
* `Σⱼ b_j = v`,
* `Σ_jk b_j A_{jk} = c`,
* `Σ_jkl b_j A_{jk} A_{kl} = m`,
* `Σ_jklm b_j A_{jk} A_{kl} A_{lm} = M`:

```
Σ_j M.b j · M.derivativeWeightWithSrc M.inverse j (mk [mk [cherry]])
  = (−v³ + 2vc − m)·v + (v² − c)·c + (−v)·m + M
  = −v⁴ + 2v²c − vm + v²c − c² − vm + M
  = −v⁴ + 3v²c − c² − 2vm + M
```

Negate: `Φ_{⟦M⟧⁻¹}(mk [mk [cherry]]) = v⁴ − 3v²c + c² + 2vm − M`. ✓

**Sanity check on `explicitEuler`** (v = 1, c = 0, m = 0, M = 0):
Predicted value = `1 − 0 + 0 + 0 − 0 = 1`. ✓

### Six deliverables (mirror cycles 371/372)

1. **Closed-form theorem** `elementaryWeightQ_phi_inv_mkMkCherry`:
   place after cycle 372's `elementaryWeightQ_phi_inv_mkVertexCherry`
   in `Section422.lean`. Recipe = cycle 371 `_mkBroom₃` template
   (depth-2 ladder) extended with one extra unfold layer:
   * `Quotient.inductionOn` on `η_q` to obtain `⟨s, M⟩`.
   * Reuse cycle 367/368/369-era helpers `h_inv_v`, `h_vertex`,
     `h_dw_cherry`, `h_cherry`, `h_dw_broom₃`, `h_broom₃`,
     `h_dw_mkCherry`, `h_mkCherry`, `h_dws_mkCherry`.
   * Add new helpers for the depth-3 cons-case unfold:
     `h_inv_mkCherry` (lift cycle 369's quotient-level
     `elementaryWeightQ_phi_inv_mkCherry` to the representative
     `Φ_{M.inverse}(mk [cherry]) = -v³ + 2vc - m`-form via cycle
     358 `_inv_mk` + `derivativeWeightWithSrcProd` unfolds),
     `h_dw_mkMkCherry`/`h_mkMkCherry`/`h_dws_mkMkCherry`.
   * `h_sum` block: cycle 358 `_inv_mk` to expand the LHS, per-summand
     `derivativeWeightWithSrcProd` unfold via `h_dws_mkMkCherry +
     h_inv_v + ring`, sum distribution via 3× `Finset.sum_add_distrib`
     / `Finset.sum_sub_distrib`, factor constants via 3×
     `← Finset.mul_sum`, back-substitute `← h_mkMkCherry`,
     `← h_mkCherry`, `← h_cherry`, `← h_vertex`, close with `ring`.
   * Axiom-clean target: `[propext, Classical.choice, Quot.sound]`.

2. **m=0 corollary** `powRep_sum_eq_of_agreement_at_mkMkCherry_zero`:
   place immediately after deliverable 1. Five agreement hypotheses
   (`h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkMkCherry`).
   Proof: 4-line via the cycle 366 `zero_add + Nat.cast_one +
   zpow_neg_one` bridge to convert `^(-((0+1):ℕ):ℤ)` to `⁻¹`, then
   `elementaryWeightQ_phi_inv_mkMkCherry` on both sides, then
   substitute. Axiom-clean.

3. **Phase α.4 extension**: append a NINTH `else if` branch to
   `inversePolynomial` at `Section422.lean:4234–4270`:
   ```lean
   else if t = OpenMath.Chapter3.Section310.RootedTree.mk
                 [OpenMath.Chapter3.Section310.RootedTree.mk
                   [RootedTree.cherry]] then
     (f RootedTree.vertex) ^ 4
       - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
       + (f RootedTree.cherry) ^ 2
       + 2 * f RootedTree.vertex
           * f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
       - f (OpenMath.Chapter3.Section310.RootedTree.mk
             [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]])
   else
     0
   ```
   Insert between the `mk [vertex, cherry]` branch (cycle 377) and
   the `else 0` fallback.

4. **Phase α.4 calibration witness**: `example` confirming
   `inversePolynomial (mk [mk [cherry]]) f = ...closed form...`.
   Proof: `unfold inversePolynomial` + chain of 7 `if_neg
   (by decide : ...)` + `if_pos rfl` (matching the 7 trees that
   come before in the chain).

5. **Phase β.4 bridge**:
   `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry`. Place
   after cycle 377's `_mkVertexCherry` bridge. Proof recipe
   identical to cycle 375/377 bridges: `unfold inversePolynomial` +
   7 `if_neg` + `if_pos rfl` + `exact
   elementaryWeightQ_phi_inv_mkMkCherry η_q`. Axiom-clean.

6. **Phase β aggregator refresh + Phase γ extension** (FORCED by
   pre-flight `lake build` per cycle 377 precedent):
   * Upgrade `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder`
     from a 7-way to an 8-way disjunction. Add `t = mk [mk [cherry]]`
     to the `rcases ht with h | h | h | h | h | h | h | h` and add
     a corresponding `exact ... _mkMkCherry η_q` line.
   * Extend `inversePolynomial_eq_of_subtree_agreement` with one new
     `by_cases` block for `mk [mk [cherry]]` (mirroring cycle 376/377
     blocks: `subst`, `have h_<v,c,broom₃,mkCherry,mkMkCherry>` × 5
     from `h_closed`, 7 `if_neg (by decide)` per side, `if_pos rfl`
     per side, then back-substitute via the 5 `h_<subtree>`s).
   * The final default branch must gain ONE MORE `if_neg
     h_mkMkCherry` per side.

### Non-vacuity witnesses

* Closed-form witness on `⟦explicitEuler⟧`: pinning
  `Φ_{⟦explicitEuler⟧⁻¹}(mk [mk [cherry]]) = 1` (computed above).
* Reflexive m=0 witness on `⟦explicitEuler⟧` with five `rfl`
  agreement hypotheses.

## D. Verification commands (run at end of cycle)

```bash
lake build OpenMath.Chapter4.Section422
grep -c sorry OpenMath/Chapter4/Section422.lean
# Expected: still 5 lines (4 docstring refs + 1 grandfathered sorry)

# Axiom check on the 4 new public theorems
echo '#print axioms
  OpenMath.Chapter4.Section422.elementaryWeightQ_phi_inv_mkMkCherry
#print axioms
  OpenMath.Chapter4.Section422.powRep_sum_eq_of_agreement_at_mkMkCherry_zero
#print axioms
  OpenMath.Chapter4.Section422.elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry
#print axioms
  OpenMath.Chapter4.Section422.elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder' \
  | lake env lean --stdin OpenMath/Chapter4/Section422.lean
# Expected: all return [propext, Classical.choice, Quot.sound]
```

## E. What NOT to try

* **Do NOT attempt Phase δ.B (general m via powRep induction)** even
  on the 7-tree ladder. The cycle 366 heterogeneity wall blocks the
  obvious induction step: `Φ_{η_q^(-(m+1))}(t) = Φ_{η_q^(-m) ·
  η_q⁻¹}(t)` expands via cycle 358's `_mul_mk` to a sum involving
  representative-specific `M.b` and `derivativeWeightWithSrc M`
  data, and comparing across η_q and η_q' requires Phase α'.

* **Do NOT attempt to redefine `inversePolynomial` as a recursive
  function (Phase α')** in this cycle. The combinatorial structure
  of coefficients is non-obvious — the closed forms for the 8 trees
  don't fit a single recursive scheme (e.g., `f cherry` appears in
  `broom₃`'s closed form even though `cherry` is not a child of
  `broom₃`). Phase α' is multi-cycle research; a separate scoping
  doc may be appropriate for cycle 379+.

* **Do NOT close the cycle 365 grandfathered sorry** at
  `Section422.lean:2279`. It quantifies `∀ t : RootedTree` and so
  is gated on Phase α'.

* **Do NOT attempt structural `induction t` on `RootedTree`.** Per
  memory `feedback_rootedtree_nested_induction.md`, `induction t` /
  `RootedTree.recOn` fail on nested inductive types. Use `match` or
  `mutual` blocks if such induction becomes needed.

* **Do NOT pivot to a fresh entity** unless cycle 378's primary
  deliverable falls through. The §422 streak (42 cycles) is
  valuable and the deliverable here is concrete and one-cycle
  achievable.

* **Do NOT skip the pre-flight `lake build`** after the Phase α.4
  branch insertion (Step 3). Per cycle 377 precedent, the default
  branch of Phase γ breaks every time `inversePolynomial` grows a
  new branch, so the Phase γ patch is forced by the build failure.
  Run the build, observe the default-branch goals shape, then patch
  Phase γ accordingly.

* **Do NOT use `norm_num` to bridge `-((m+1 : ℕ) : ℤ) = Int.negSucc m`.**
  Per memory `feedback_neg_natCast_int_negsucc_rfl.md`, the bridge
  is definitional `rfl`; `norm_num` leaves an unsolved goal with
  display-ambiguity. Use the cycle 366 `zero_add + Nat.cast_one +
  zpow_neg_one` chain for the m=0 corollary.

* **Do NOT touch `RKTableau.symmetry` or any σ-related code.** Out
  of scope.

## F. Sequencing guidance for the worker

1. **(5 min) Read cycle 371 (`elementaryWeightQ_phi_inv_mkBroom₃`)**
   at `Section422.lean:3397–3503` and cycle 372
   (`elementaryWeightQ_phi_inv_mkVertexCherry`) at lines 3798–3915.
   These are the most recent depth-2 / heterogeneous closed-form
   ships and provide the template for cycle 378's helper-chain
   layout.

2. **(20 min) Ship deliverable 1** (closed-form theorem). This is
   the load-bearing piece; expect ~250 LOC including helpers. Be
   careful with the depth-3 unfold; mirror cycle 369's `_mkCherry`
   helpers exactly with one more wrap layer for `h_inv_mkCherry`
   and `h_dw_mkMkCherry`/`h_mkMkCherry`/`h_dws_mkMkCherry`.

3. **(5 min) Ship deliverable 2** (m=0 corollary). ~25 LOC.

4. **(5 min) Ship deliverable 3** (Phase α.4 branch in
   `inversePolynomial`). **STOP and run `lake build
   OpenMath.Chapter4.Section422`.** Expect Phase γ's default branch
   to break with goals shape `if t = mk [mk [cherry]] then ... else
   0 = ...`. Note the goals; proceed to Step 7.

5. **(5 min) Ship deliverable 4** (Phase α.4 calibration witness).
   ~10 LOC.

6. **(10 min) Ship deliverable 5** (Phase β.4 bridge). ~20 LOC.

7. **(20 min) Ship deliverable 6** (β aggregator refresh + γ
   extension). The γ extension is the trickiest piece: insert ONE
   new `by_cases h_mkMkCherry` block between cycle 377's
   `mk [vertex, cherry]` block and the final default branch. Mirror
   the cycle 377 `mk [vertex, cherry]` block recipe verbatim with
   one fewer `if_neg` per side (since `mk [mk [cherry]]` is later
   in the chain than `mk [vertex, cherry]`). Then add `if_neg
   h_mkMkCherry` per side to the final default branch.

8. **(5 min) Verify**: `lake build`, `#print axioms` on each new
   theorem.

9. **(5 min) Update plan files**: bump cycle reference in
   `lean_status.json` for `def:422B` row (still `partial`); add a
   short `plan.md` annotation; append a "Cycle 378 update"
   subsection to
   `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`
   recording the 8-tree ladder closure.

10. **(15 min) Write `task_results/cycle_378.md`**.

Total budget: ~95 min. If the closed-form theorem (step 2) overruns
significantly, ship deliverables 1+2+3 only and defer 4–6 to cycle
379. Per cycle 377 precedent the build doesn't actually break until
Phase α extension fires, so partial ship is feasible. **Do not ship
a sorry-bearing scaffold** — if any deliverable can't close
axiom-clean, omit it and document.

## G. Faithfulness checklist (per CLAUDE.md)

* `elementaryWeightQ_phi_inv_mkMkCherry`: infrastructure theorem, no
  Butcher entity ID. Statement matches the algebraically-derived
  closed form `v⁴ − 3v²c + c² + 2vm − M` exactly.
* `powRep_sum_eq_of_agreement_at_mkMkCherry_zero`: infrastructure
  corollary of the closed form; no Butcher entity ID.
* `_eq_inversePolynomial_mkMkCherry`: Phase β bridge; no Butcher
  entity ID.
* `_on_ladder` (refresh): aggregator; preserves cycle 375/377
  signature with one more disjunct.
* `inversePolynomial` (extension): pattern-match definition; new
  branch matches the closed form for the new tree.
* `inversePolynomial_eq_of_subtree_agreement` (extension): preserves
  cycle 376/377 signature; adds one more `by_cases` block.
* Tautology check: no theorem's conclusion is verbatim a hypothesis.
* Identity check: no theorem closes by `exact h` for a pre-existing
  `h` without intermediate work.
* Hypothesis strength check: closed-form hypothesis (`η_q : Quotient
  …`) is minimal; m=0 witness adds five subtree-agreement
  hypotheses matching the closed form's subtree dependencies.

## H. Why this is the right cycle 378 move

* Preserves the 42-cycle §422 axiom-clean streak.
* Concrete one-cycle deliverable; mechanical extension of established
  pattern (cycle 371 template + cycle 369 one-more-layer).
* Provides one more empirical data point for Phase α' coefficient
  identification — a depth-3 ladder case beyond cycles 369/371's
  depth-2 cases.
* The 8th tree fills a missing slot: depth-3 single-child ladder
  (the natural extension after cycles 369 mk [cherry] depth-2 and
  371 mk [broom₃] depth-2). After this, the ladder will span:
  - depth 1: vertex, cherry, broom₃ (orders 1, 2, 3)
  - depth 2: mk [cherry], bushy, mk [broom₃], mk [vertex, cherry]
  - depth 3: **mk [mk [cherry]]** (new)
* Defers the genuinely-hard work (Phase α' recursive definition) to
  a future cycle with proper scoping.

## I. Risk register

* **R1 — closed-form value verification**: the derivation above
  gives `v⁴ − 3v²c + c² + 2vm − M`. The worker should re-derive on
  paper before shipping the theorem statement, OR verify
  numerically on `explicitEuler` (predicted 1) plus one more method
  before committing the closed form. **Risk: MEDIUM.** Mitigation:
  prove `Φ_{⟦explicitEuler⟧⁻¹}(mk [mk [cherry]]) = 1` as a tiny
  side example BEFORE shipping the general closed-form theorem; if
  it fails, the closed-form value above is wrong and needs
  re-derivation.
* **R2 — depth-3 helper chain complexity**: cycles 369/371 used 4
  helpers (`h_dw_X`/`h_X`/`h_dws_X`/`h_inv_X`); cycle 378 needs the
  same chain extended one layer. **Risk: LOW.** Mitigation: follow
  cycle 371 line-by-line, with `h_inv_mkCherry` introduced as a
  representative-form lift of cycle 369's quotient theorem
  `elementaryWeightQ_phi_inv_mkCherry` via cycle 358
  `_inv_mk`+`derivativeWeightWithSrc` unfolds.
* **R3 — Phase γ default branch grows by 1**: the final `else`
  branch of `inversePolynomial_eq_of_subtree_agreement` will need
  one more `if_neg h_mkMkCherry` per side. **Risk: LOW.** Forced by
  `lake build`; just follow the goals shape.
* **R4 — name resolution for `mk [mk [cherry]]`**: per cycle 374's
  documented gotcha, top-level `RootedTree.mk` resolves to
  Mathlib's `_root_.RootedTree.mk` unless fully qualified. Use
  `OpenMath.Chapter3.Section310.RootedTree.mk
    [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]`
  in the `inversePolynomial` extension. **Risk: LOW** (well-known).
* **R5 — GPFS slowness on Section422**: Section422 has been stable
  throughout cycles 336–377 (cold rebuilds ~3–5 min). No history
  of timeouts. **Risk: LOW.**

If cycle 378 closes all 6 deliverables cleanly, the §422 streak
advances to **43 substantive + 1 doc** (cycles 336–378).
