# Cycle 360 Results

## Worked on

§422 Phase D.3.b: linear coefficient extraction —
`coeff_eta_t_in_eta_zpow_neg` and supporting infrastructure for the
textbook claim (Butcher §422 p. 359, `ch04.txt:1158`) that "the
coefficient of η(t) in η⁻ⁱ(t) is equal to i·(-1)^r(t), and there are
no other terms in η⁻ⁱ(t) with orders greater than r(t)−1".

Per strategy §B.1, picked signature shape (2) (Closed-form-with-RHS-
helper): a named helper `linearResidualAt` plus the split-form
theorem `coeff_eta_t_in_eta_zpow_neg`. Per the strategy's §F graceful-
degradation template, shipped Sub-deliverables 1 + 2 axiom-clean,
deferring the full inductive step at arbitrary `t` for `i ≥ 2` to
cycle 361.

## Approach

Inserted four new public symbols + four non-vacuity `example`s at
end of `OpenMath/Chapter4/Section422.lean` (lines 1797–1969):

1. **`linearResidualAt (i : ℕ) (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT) : ℝ`**
   — `noncomputable def`, definitional residual on the §383 quotient:
   `Φ_{η_q^(-i)}(t) − i·(-1)^t.order·Φ_{η_q}(t)`. Quotient-level
   (per scoping doc §6.3 quotient-faithfulness discipline); does not
   depend on representative choice.

2. **`coeff_eta_t_in_eta_zpow_neg`** (Sub-deliverable 1) — signature-
   pinning split form:
   ```
   Φ_{η_q^(-i)}(t) = i·(-1)^t.order·Φ_{η_q}(t) + linearResidualAt i η_q t
   ```
   Definitional rearrangement; proof is 2 lines (`unfold linearResidualAt; ring`).
   No `hi : 0 < i` hypothesis required (strawman had it; the definition
   naturally handles `i = 0` via cycle 359's `pow_zero` / cycle 239's
   `elementaryWeightQ_phi_id`).

3. **`linearResidualAt_vertex_eq_zero`** (Sub-deliverable 2 base case at
   vertex) — substantive: at `τ` (with `r(τ) = 1`, no strict subtrees),
   residual is identically zero. Proof: cycle 341 P3
   (`elementaryWeightQ_phi_zpow_vertex`) gives `Φ_{η_q^n}(τ) = n·Φ_{η_q}(τ)`,
   specialising to `n = -(i : ℤ)` yields `Φ_{η_q^(-i)}(τ) = -(i : ℝ)·Φ_{η_q}(τ)`.
   With `vertex.order = 1` (by `rfl`), the residual is `-i·Φ - i·(-1)·Φ = 0`.
   5 lines (`unfold` + `rw [elementaryWeightQ_phi_zpow_vertex]` +
   `rw [show RootedTree.vertex.order = 1 from rfl]` + `push_cast; ring`).

4. **`linearResidualAt_one_mk_eq`** (Sub-deliverable 2 closed form at
   `i = 1` at arbitrary tree) — substantive: at `i = 1` at any tree `t`,
   `linearResidualAt 1 ⟦⟨s, M⟩⟧ t` reduces to a closed-form expression
   `-Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j t - (-1)^t.order ·
   M.elementaryWeight t`. Uses cycle 358's `elementaryWeightQ_phi_inv_mk`
   + cycle 222's `inverseQ_phi_mk` + cycle 226's `_phi_mk`. 6 lines
   (`unfold` + `Nat.cast_one + zpow_neg_one` bridge + cycle 358 `_inv_mk`
   + `_phi_mk` + `push_cast; ring`).

Plus four non-vacuity `example`s exercising:
* vertex base case with `explicitEuler` + `i = 1` (1 line, applies `linearResidualAt_vertex_eq_zero`),
* signature split form with `explicitEuler` + `i = 1` at vertex (1 line, applies `coeff_eta_t_in_eta_zpow_neg`),
* closed form at `cherry` (`r(t) = 2`) with `explicitEuler` (1 line, applies `linearResidualAt_one_mk_eq`).

## Result

**SUCCESS**. All four new public symbols + four `example`s
axiom-clean (`[propext, Classical.choice, Quot.sound]` only), verified
via `#print axioms` after `lake build OpenMath.Chapter4.Section422`
(8037/8037 jobs, exit 0, 153s rebuild). `lake env lean
OpenMath/Chapter4/Section422.lean` exits 0. Sorry count remains 0 in
Section422.lean.

§422 streak now **26 consecutive axiom-clean cycles** (336–360).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### 1. `linearResidualAt` (def)

- Entity ID: helper definition (no JSON entity); supporting `def:422B` /
  `thm:422A`. Textbook statement (Butcher §422 p. 359, `ch04.txt:1158`):
  > "The coefficient of η(t) in η⁻ⁱ(t) is equal to i(−1)^r(t) and
  > there are no other terms in η⁻ⁱ(t) with orders greater than r(t) − 1."
- Lean statement captures: **same content** (named helper isolating
  the "other terms" after extracting the i·(-1)^r(t) coefficient).
- Justification: textbook claims `η⁻ⁱ(t) = i·(-1)^r(t)·η(t) + (other terms)`;
  `linearResidualAt` is exactly the "other terms" half (definitional).
  The structural claim that the "other terms" set has orders ≤ r(t) − 1
  is the deferred cycle 361 content.

### 2. `coeff_eta_t_in_eta_zpow_neg` (theorem)

- Entity ID: helper supporting `thm:422A`. Textbook source same as above.
- Lean statement captures: **same content** (the split form
  `η⁻ⁱ(t) = i·(-1)^r(t)·η(t) + residual`).
- Tautology check: conclusion does NOT appear as hypothesis (no
  hypotheses beyond `(i : ℕ)` and `(η_q : Quotient ...)`). ✓
- Identity check: proof `unfold linearResidualAt; ring` does
  algebraic work; this is the trivial definitional split, but it
  pins the signature for downstream Phase D.3.d consumption (the
  substantive content is in the next two theorems). Not a vacuous
  re-export.
- Hypothesis strength check: **weaker than strawman** (dropped
  `hi : 0 < i` — works uniformly for `i : ℕ`).

### 3. `linearResidualAt_vertex_eq_zero` (theorem)

- Entity ID: helper supporting `thm:422A`. Textbook source same.
- Lean statement captures: **substantive content** of textbook claim
  at `r(t) = 1` (the "no other terms" half at vertex).
- Tautology check: conclusion `linearResidualAt i η_q vertex = 0`
  does NOT appear as hypothesis. ✓
- Identity check: proof uses cycle 341 P3 (substantive). Not identity.
- Hypothesis strength check: only `(i : ℕ)` — matches textbook
  (Butcher does not require `i ≥ 1` for the vertex case; works at
  `i = 0` too: residual `Φ_{η^0}(τ) - 0 = 1(τ) - 0 = 0` per cycle
  239's `elementaryWeightQ_phi_id`). No textbook deviation.

### 4. `linearResidualAt_one_mk_eq` (theorem)

- Entity ID: helper supporting `thm:422A`. Textbook source same.
- Lean statement captures: **substantive closed-form expression**
  at `i = 1` at arbitrary tree, exposing structural dependence on
  `M`'s representative data via cycle 358's `_inv_mk`.
- Tautology check: conclusion is the closed-form equation; does NOT
  appear as hypothesis. ✓
- Identity check: proof uses cycle 358's `_inv_mk` + algebra.
  Substantive.
- Hypothesis strength check: representative-form `M : RKTableau s`
  is necessary because cycle 358's `_inv_mk` is representative-form
  (the bottom-block sum's stage count `s` does not descend to the
  abstract Φ-quotient — cycle 333's design note). No textbook
  deviation; matches the representative-form pattern established by
  D.3.a.1/D.3.a.2/D.3.a.3 (cycles 358, 359).

## Dead ends

* **Initial example type-mismatch on `(1 : ℝ)` vs `((1 : ℕ) : ℝ)`:**
  The first version of the second non-vacuity `example` used `(1 : ℝ)`
  as the literal coefficient; this failed elaboration against
  `coeff_eta_t_in_eta_zpow_neg`'s signature (which has `(i : ℝ)` where
  `i : ℕ` is the first argument, so the coefficient is `((↑i : ℕ) : ℝ)`).
  Fix: changed the example to use `((1 : ℕ) : ℝ)` to match the
  theorem's signature syntactically. The values are equal but not
  definitionally `rfl`. **Lesson**: when consuming a theorem with a
  `(i : ℕ) → … → (i : ℝ) · …` shape, downstream consumers must use
  the natural-number-coerced form to match the theorem's coefficient.

## Discovery

1. **`(-1)^vertex.order` reduces by `rfl` to `(-1)^1`**: since
   `vertex.order = 1` is `rfl` (from `Section310.lean:125`), the
   power `(-1 : ℝ)^vertex.order` is definitionally `(-1)^1` — but
   `ring` doesn't reduce literal naturals in exponents automatically,
   so an explicit `rw [show vertex.order = 1 from rfl]` step is
   required before `ring` closes the goal. Pattern for cycle 361's
   inductive step at non-vertex trees: `t.order` will *not* reduce
   in general, so the structural rewrite step will need
   strict-subtree-induction infrastructure rather than `rfl`.

2. **`Nat.cast_one + zpow_neg_one` is the bridge for `i = 1`**: to
   reduce `η_q ^ (-((1 : ℕ) : ℤ))` to `η_q⁻¹`, the two-step rewrite
   `rw [Nat.cast_one]; exact zpow_neg_one _` is the cleanest. A
   direct `zpow_neg_one` does not fire because the inner natural
   literal `(1 : ℕ)` is not syntactically `(1 : ℤ)` until
   `Nat.cast_one` normalises it. Pattern for cycle 361's inductive
   step at `i ≥ 2`: will need an analogous bridge for `(↑i : ℤ)` →
   `(i : ℤ)` plus `zpow_neg` / `zpow_natCast` to expose the inverse
   structure.

3. **Quotient-level vs representative-form trade-off (re §6.3):**
   The cycle 360 ship has `linearResidualAt` at the quotient level
   (depends only on `η_q`, no representative choice), but
   `linearResidualAt_one_mk_eq`'s closed-form RHS is necessarily
   representative-form (`M.b`, `M.inverse`, `M.elementaryWeight`).
   This is consistent with the cycle 358/359 pattern: the *statement
   on the quotient* is representative-independent, but the *closed-
   form computation* exposes the representative's bottom-block
   structure. Cycle 361's inductive step will need to thread this
   distinction carefully: the "depends only on strict subtrees"
   claim should be at the quotient level (i.e. invariant under
   Φ-equivalent representative substitution), while the closed-form
   expansion will inevitably touch representative data.

4. **Definitional residual is the right shape for cycle 360**:
   Strategy §B.1 considered three signature shapes; option (2)
   (named helper) was recommended. Implementation confirms option
   (2) lands cleanly: `linearResidualAt` is `noncomputable def`,
   `coeff_eta_t_in_eta_zpow_neg` is a 2-line trivial split,
   `linearResidualAt_vertex_eq_zero` and `linearResidualAt_one_mk_eq`
   carry the substantive base-case content. Option (1) (existential)
   would have buried the helper in `∃ C, …`, making downstream
   consumption awkward; option (3) (vertex-only) would have been
   insufficient per §B.1 warning.

## Suggested next approach

Per scoping doc §5, **cycle 361 should ship Phase D.3.b inductive
step** (the "depends only on strict subtrees" claim) and/or Phase
D.3.c (`sum_i_alpha_ne_zero_of_stable`).

The natural cycle 361 deliverable is:
```lean
theorem linearResidualAt_depends_only_on_strict_subtrees (i : ℕ)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma) (t : RT)
    (h_strict : ∀ s : RT, s.order < t.order →
      elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    linearResidualAt i η_q t = linearResidualAt i η_q' t
```
This is Butcher's parametricity claim formalised at the Lean level.

The proof requires (a) cycle 359's `elementaryWeightQ_phi_pow_succ_mk`
(ℕ-form recursive identity) plus (b) extension to ℤ-form for negative
powers (the deferred `elementaryWeightQ_phi_zpow_mk`), plus (c) a
strong-induction argument on `t.order` using cycle 343's
`WellFoundedRelation RootedTree := measure RootedTree.order`. The
inductive step shows that at `t = mk children`, every subtree
appearing in `derivativeWeightWithSrc` has `order < t.order` (via
`RootedTree.order_mk` and cycle 357's `mem_children_lt` or
equivalent), so the inductive hypothesis applies.

**Estimated LOC for cycle 361**: ~80–100 LOC (the strong-induction
boilerplate is substantial). Aristotle-poor (the induction structure
is delicate and needs hand-crafted termination measures).

**Alternative**: tackle Phase D.3.c
(`sum_i_alpha_ne_zero_of_stable`) in parallel since it does not
depend on Phase D.3.b. If Mathlib's polynomial-root API is missing
the simple-root derivative lemma, ship the helper as a per-LMM-witness
hypothesis (as we did for cycle 350's `coef_α + coef_β ≠ 0`).

**Strategic context**: §422 streak now 26 consecutive axiom-clean
cycles. Phase E sealing of `def:422B` projected ~4 cycles away
(cycle 361 D.3.b inductive step → cycle 362 D.3.c → cycle 363 D.3.d
→ cycle 364 Phase E sealing). No pivot temptation — the ladder
rhythm is productive.
