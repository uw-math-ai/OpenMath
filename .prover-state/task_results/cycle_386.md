# Cycle 386 Results

## Worked on

Phase α'.4.0 Family C 10th witness ship per cycle 385 scoping doc §7:
the closed form `elementaryWeightQ_phi_inv_mkBroomCherry` for
`Φ_{η_q⁻¹}(mk [broom₃, cherry])` at the order-6 asymmetric
two-non-leaf-children tree (σ = 1), plus the m=0 corollary
`powRep_sum_eq_of_agreement_at_mkBroomCherry_zero` and two
non-vacuity `example`s on `⟦explicitEuler⟧`.

## Approach

1. **Paper-derivation (~45 min, mandatory step per strategy).** Applied
   cycle 358's `elementaryWeightQ_phi_inv_mk` formula recursively
   through the §3.2 four-block decomposition:
   - Block (1) const · const = inv_b' · inv_c · v
   - Block (2) const · A-sum = inv_b' · (m − v·c)
   - Block (3) A-sum · const = inv_c · (v²c − 2v·m + M_broom₃)
   - Block (4) A-sum · A-sum (bilinear) = −v³·b' + 3v²·vc − 2v·cc
                                          − v·vb' + bc
   Inv-substitutions: inv_v = −v, inv_c = v²−c (cycle 367), inv_b' =
   −v³ + 2vc − b' (cycle 368). Closed form computed in 9 kernels and
   sanity-checked against ⟦explicitEuler⟧ (v=1, all others=0): prediction
   `+1 = v⁶`.

2. **Lean ship (mirrors cycle 384 mkCherryCherry template line-by-line).**
   - `Quotient.inductionOn η_q` + `rintro ⟨s, M⟩`.
   - Reused cycle 367/368/369/371/372/384 helpers verbatim
     (h_inv_v, h_vertex, h_dw_cherry, h_cherry, h_dws_cherry,
     h_dw_broom₃, h_broom₃, h_dws_broom₃, h_inv_cherry,
     h_inv_broom₃, h_dw_mkCherry, h_mkCherry, h_dw_mkBroom₃,
     h_mkBroom₃, h_dw_mkVertexCherry, h_mkVertexCherry,
     h_dw_mkCherryCherry, h_mkCherryCherry).
   - Three NEW helpers for the new kernels:
     - `h_dw_mkVertexBroom₃` / `h_mkVertexBroom₃`: order-5 asymmetric
       leaf + non-leaf two-children kernel (Block (4) surface).
     - `h_dw_mkBroomCherry` / `h_mkBroomCherry`: self-kernel.
     - `h_dws_mkBroomCherry`: two-non-leaf-children cons-case
       derivativeWeightWithSrc unfold (outer broom₃ + tail [cherry]
       pattern, combining cycle 368-style and cycle 367-style inner
       unfolds).
   - Main computation:
     ```
     rw [elementaryWeightQ_phi_inv_mk M ..., elementaryWeightQ_phi_mk × 9]
     have h_sum : ... := by
       have h_subst : ... := by
         refine Finset.sum_congr rfl (fun i _ => ?_)
         rw [h_dws_mkBroomCherry i, h_inv_broom₃, h_inv_cherry, h_inv_v]
         have h_inner_expand_1 : ... := by ... [cycle 372 pattern]
         have h_inner_expand_2 : ... := by ... [cycle 371 pattern]
         rw [h_inner_expand_1, h_inner_expand_2]; ring
       rw [h_subst, Finset.sum_add_distrib × 8, ← Finset.mul_sum × 8,
           ← h_mkBroomCherry, ← h_mkVertexBroom₃, ← h_mkCherryCherry,
           ← h_mkVertexCherry, ← h_mkBroom₃, ← h_mkCherry, ← h_broom₃,
           ← h_cherry, ← h_vertex]
       ring
     rw [h_sum]; ring
     ```
   - m=0 corollary: 9 agreement hypotheses + `zpow_neg_one` reduction
     + `rw [_inv_mkBroomCherry, _inv_mkBroomCherry, h_<each>]`.
   - Non-vacuity example: 18 explicit `have` blocks (one `_zero` and
     one `_<kernel>` per kernel) at `⟦explicitEuler⟧`.

3. **Verification.** `lake env lean OpenMath/Chapter4/Section422.lean`
   exits 0 with only the expected grandfathered sorry warning. Both
   new public theorems pass `#print axioms` with
   `[propext, Classical.choice, Quot.sound]`.

## Result

**SUCCESS** — both new public theorems shipped axiom-clean, both
non-vacuity examples accepted, sorry count unchanged at 5. §422
axiom-clean streak: cycles 336–386 = 49 substantive + 2 doc.

* `elementaryWeightQ_phi_inv_mkBroomCherry` — axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).
* `powRep_sum_eq_of_agreement_at_mkBroomCherry_zero` — axiom-clean.
* Two `example`s (closed-form pinning to `+1` + m=0 reflexive via
  9 `rfl`s) accepted.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (4 docstring
  + 1 grandfathered code sorry from cycle 365).
* Section422.lean: 6520 → 7321 LOC (+801 LOC, exceeded 250 LOC budget;
  see §10.5 in updated scoping doc for accounting).

## Faithfulness check

* **Entity ID**: `def:422B` (continuing §422 underlying one-step-method
  work track; the new theorem is a Phase α'.4.0 helper that lifts the
  cycle 384 mkCherryCherry pattern to the asymmetric 10th data point).

* **Textbook statement quoted from `extraction/formalization_data/
  entities/def_422B.json`**: this cycle ships a Phase α'.4.0 helper
  theorem, not the def:422B headline itself. The headline (Phase E
  lift + seal) remains projected for the 390s per cycle 385 scoping
  doc §5 — the cycle 365 grandfathered sorry remains the blocker.

* **Lean statement captures**: `elementaryWeightQ_phi_inv_mkBroomCherry`
  is an algebraic identity stating that
  `Φ_{η_q⁻¹}(mk [broom₃, cherry])` equals a specific 14-term
  polynomial in `Φ_η` at 9 strictly-smaller-order trees (vertex,
  cherry, broom₃, mk [cherry], mk [broom₃], mk [vertex, cherry],
  mk [cherry, cherry], mk [vertex, broom₃]) plus the self-kernel
  `Φ_η(mk [broom₃, cherry])`. This is **same content** as the
  paper-derivation; no hypotheses, no smuggled structure.

* **Definition smuggling check**: PASS. No new `def` or `structure`
  introduced. Both new symbols are `theorem`s over existing
  definitions.

* **Tautology check**: PASS. LHS uses `Φ_{η_q⁻¹}`, RHS is a polynomial
  in `Φ_{η_q}` at distinct trees (the self-kernel appears with
  coefficient `−1` as a true RHS term, NOT as a hypothesis).

* **Identity check**: PASS. Neither proof is `exact h` or similar.
  Main proof is a genuine 350-LOC algebraic computation via Finset
  sum decomposition + `ring`.

* **Hypothesis strength check**: PASS. The only hypothesis on the
  main theorem is `η_q : Quotient PhiEquivalent.setoidSigma`. The
  m=0 corollary has 9 agreement hypotheses; each corresponds to a
  distinct kernel surfaced by the closed form (no redundancy, no
  strengthening beyond what the closed-form factors demand).

* **Absent theorem check**: PASS. All cycle 386 `theorem`/`example`
  declarations referenced in docstrings exist in the file (verified
  via `lake env lean` clean exit + `grep -n` cross-check).

## Dead ends

None substantive. The proof followed cycle 384's template directly.
One minor adjustment: cycle 384 uses one `h_inner_expand` for the
linear `S¹_i` factor, cycle 386 needed BOTH `h_inner_expand_1` (linear)
and `h_inner_expand_2` (squared, from cycle 371's broom₃ pattern)
because the asymmetric tree has both linear (cherry) and squared
(broom₃) inner sums.

The strategy's stretch Priority 2 (`mk [cherry, broom₃]` reverse-pair)
was deferred — Priority 1 ship took the full cycle budget given the
LOC blow-up. This is consistent with the strategy's risk-assessment
("If hitting 400 LOC, ship Priority 1 only").

## Discovery

* **Two new kernels surface in Block (4), not one.** Per scoping doc
  §3.2, Block (4) was expected to surface one or two kernels. Cycle
  386's closed form has both `cc = Φ_η(mk [cherry, cherry])` (known
  from cycle 384) AND `vb' = Φ_η(mk [vertex, broom₃])` (NEW order-5
  kernel) in Block (4). The pattern is: Block (4) bilinear cross-term
  for `mk [t₁, t₂]` (with `t₁ > t₂` in some sense) surfaces (i) the
  self-kernel `mk [t₁, t₂]`, (ii) any "leaf-shifted" kernel
  `mk [vertex, t₁']` where `t₁'` is obtained from `t₁` by "absorbing"
  one A-factor from `t₂`'s outer linear part. For
  `(t₁, t₂) = (broom₃, cherry)`: cherry's β factor is
  `∑_j A_{ij}·∑_k A_{jk}`, whose outer `∑_j A_{ij}` arm "moves into"
  broom₃'s γ factor `∑_j A_{ij}·(∑_k A_{jk})²` to yield
  `α · γ = (∑_j A_{ij})·(∑_j A_{ij}·(∑_k A_{jk})²)` =
  `Φ_η(mk [vertex, broom₃])`.

* **Phase α'.4.1 design implication.** The `bichildPolynomial t₁ t₂`
  helper that Phase α'.4.1 will introduce must accommodate this
  shifted-kernel pattern. From cycle 384 (`mk [cherry, cherry]`,
  symmetric, t₁ = t₂ = cherry) the shifted kernel was
  `mk [vertex, cherry]`; from cycle 386 (`mk [broom₃, cherry]`,
  asymmetric, t₁ = broom₃, t₂ = cherry) it is `mk [vertex, broom₃]`.
  Cycle 387's recursive design must encode this shift via a
  per-child polynomial-in-Φ_η machinery.

* **LOC trajectory.** The 250 LOC budget was exceeded by ~3× due to
  inline helper reuse + 18 `have` blocks for the 9-kernel non-vacuity
  example. Cycles 371 (5 kernels, ~250 LOC), 372 (6 kernels, ~280 LOC),
  384 (6 kernels, ~470 LOC including m=0 + examples), 386 (9 kernels,
  ~800 LOC including m=0 + examples). The non-vacuity example bloats
  roughly quadratically (or more) in the kernel count. Phase α'.4.1's
  recursive ship should amortise this cost.

## Suggested next approach

Cycle 387 — Phase α'.4.1 entry per scoping doc §5.2:

* **Recommended**: ship recursive `inversePolyTree` (Variant V4) +
  `bichildPolynomial` helper, with calibration witnesses against the
  10 ladder trees (cycles 341 vertex, 367 cherry, 368 broom₃, 369
  mkCherry, 371 mkBroom₃, 372 mkVertexCherry, 378 mkMkCherry, 384
  mkCherryCherry, plus today's 386 mkBroomCherry — 9 Family C / B / A
  data points; plus bushy is the 10th if we count it as Family B).
  Estimated 300–500 LOC, may span 2 cycles. The cycle 386 data point
  is sufficient empirical anchor; the recursive design should now
  be unambiguous.

* **Alternative if Phase α'.4.1 stalls**: one more α'.4.0 data point.
  Candidates:
  - `mk [cherry, broom₃]` = today's deferred Priority 2 (reverse-pair
    confirmation, ~100 LOC mirroring the cycle 386 body with factors
    swapped — should be the cleanest single-cycle continuation).
  - `mk [vertex, broom₃]` = k=2, leaf + non-leaf, order 5. This is
    actually the NEW kernel surfaced today; shipping its closed form
    would round out the order-5 Family C data with cherry/cherry,
    cherry/vertex, vertex/cherry, vertex/broom₃, broom₃/vertex.
  - `mk [broom₃, broom₃]` = k=2, symmetric two-broom, order 7.

* **Pivot ALTERNATIVE**: §422 has high compound momentum (49
  substantive + 2 doc cycles). Pivoting to a fresh entity (`def:451A`,
  `thm:535A`, `thm:541A`, `def:442A`) remains cycle 389+ territory
  per strategy.

Phase E sealing of `def:422B` continues to be projected for the 390s
given Sub-lemma A's general body remains the multi-cycle blocker. The
recursive `inversePolyTree` shipped in Phase α'.4.1 will be the
machinery that closes Sub-lemma A's case-analysis-on-tree-shape branch
for k ≥ 2 children.
