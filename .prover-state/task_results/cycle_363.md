# Cycle 363 Results

## Worked on

* **P1** (Phase D.3.c, mandatory): ship the load-bearing α-side
  non-vanishing fact `Σᵢ ((i.val + 1 : ℕ) : ℝ) · M.α i.succ ≠ 0`
  under `IsStable + IsPreconsistent + 0 < k` as a corollary of cycle
  344's strict-positivity result. One new theorem
  `sum_i_alpha_ne_zero_of_stable_preconsistent` in
  `OpenMath/Chapter4/Section422.lean` plus a BDF2 non-vacuity
  `example` routing through `bdf2LMM_isStable` (cycle 346) and
  `bdf2LMM_isPreconsistent` (cycle 175).
* **P2** (Phase D.3.b parametricity Step 2 SCOPING audit, mandatory):
  paper computation of `linearResidualAt 1 ⟦M⟧ cherry` and
  `linearResidualAt 2 ⟦M⟧ cherry` on two distinct RK methods
  (`explicitEuler` and Heun's 2-stage method) to validate cycle 360's
  coefficient choice against Butcher's textbook claim (§422 p. 338,
  `ch04.txt:1163`). Documented findings in
  `.prover-state/issues/def_422B_phase_D_3_scoping.md` §10
  ("Cycle 363 audit" subsection).

## Approach

### P1 (15 min)

Direct one-line `ne_of_gt` invocation on cycle 344's
`coef_α_pos_of_stable_preconsistent`:

```lean
theorem sum_i_alpha_ne_zero_of_stable_preconsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hk : 0 < k) (hStab : M.IsStable) (hPre : M.IsPreconsistent) :
    (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ) ≠ 0 :=
  ne_of_gt (coef_α_pos_of_stable_preconsistent M hk hStab hPre)
```

The BDF2 non-vacuity witness instantiates this on `bdf2LMM` with
`hk := by norm_num` and the existing stability/preconsistency
witnesses. Both ship axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

### P2 (90 min)

Computed `Φ_{⟦M⟧⁻¹}(cherry)` via cycle 358's `elementaryWeightQ_phi_inv_mk`
+ cycle 224's `derivativeWeightWithSrc` recursion at `cherry = mk [vertex]`.
The unfolding produces a closed form
`Φ_{⟦M⟧⁻¹}(cherry) = -[M.elementaryWeight vertex · M.inverse.elementaryWeight vertex
+ M.elementaryWeight cherry]`. Applying
`M.inverse.elementaryWeight vertex = -M.elementaryWeight vertex` (a direct
consequence of `M.inverse.b j = -M.b j` from
`Section381.lean:4118`) yields:

```
η⁻¹(cherry) = η(vertex)² − η(cherry)
```

So the coefficient of `η(cherry)` in `η⁻¹(cherry)` is **−1**, not
Butcher's claimed `1·(-1)^2 = +1`. Cross-verified at `i = 2` (via
`elementaryWeightQ_phi_mul_mk` applied to
`⟦M.inverse⟧ · ⟦M.inverse⟧`) and at `t = fork = mk [vertex, vertex]`
(order 3). Pattern: the actual coefficient is **`-i`** (constant
in `r(t)`), not Butcher's `i·(-1)^r(t)`.

Numerical witnesses (both methods have `η(vertex) = 1` so a
strict-subtree-only residual would yield the same value):

| Method | η(vertex) | η(cherry) | cycle 360 `linearResidualAt 1 ⟦M⟧ cherry` | corrected `linearResidualAt' 1 ⟦M⟧ cherry` |
|---|---|---|---|---|
| `explicitEuler` | 1 | 0 | `1` | `1` |
| Heun (2-stage) | 1 | 1/2 | `0` | `1` |

cycle 360's value differs between methods at fixed `η(vertex)` ⇒ NOT
strict-subtree-dependent. Corrected form (subtract `-i·η(t)` instead
of `i·(-1)^r(t)·η(t)`) is strict-subtree-dependent in both cases.

## Result

**SUCCESS — both P1 and P2 shipped per the strategy.**

### P1

* New theorem `sum_i_alpha_ne_zero_of_stable_preconsistent` in
  `OpenMath/Chapter4/Section422.lean` after
  `coef_α_pos_of_stable_preconsistent` (line ~939).
* BDF2 non-vacuity `example`.
* Both axiom-clean
  (`#print axioms OpenMath.Chapter4.Section422.sum_i_alpha_ne_zero_of_stable_preconsistent`
  returns `[propext, Classical.choice, Quot.sound]`).
* `lake build OpenMath.Chapter4.Section422` exits 0 (250 s build).
* Sorry count remains 0.
* §422 axiom-clean streak: **28 → 29** consecutive cycles (336–363).

### P2

* Audit doc appended to
  `.prover-state/issues/def_422B_phase_D_3_scoping.md` §10 as
  "Cycle 363 audit" subsection (~7 KB of markdown).
* Concrete numerical computations on both `explicitEuler` and Heun's
  method documented; tabulated comparison of cycle 360's
  `linearResidualAt` value vs the corrected form's value.
* Cycle 364 entry-point recipe: ship the definition fix as a
  focused single cycle (~40–60 LOC restating cycle 360/361 closed
  forms with corrected sign; all proofs mechanical
  `unfold; push_cast; ring`-class).
* Cycle 365+ entry point: attempt Phase D.3.b parametricity Step 2
  under the corrected definition.

## Faithfulness check

### `sum_i_alpha_ne_zero_of_stable_preconsistent`

* **Entity ID and textbook statement** (quoted from
  `extraction/raw_text/ch04.txt:1163`):
  > "The coefficient of η(t) in η⁻ⁱ(t) is equal to i(−1)^r(t) and there
  > are no other terms in η⁻ⁱ(t) with orders greater than r(t)−1. […]
  > Hence, to satisfy (422a), with both sides evaluated at t, it is
  > only necessary to solve the equation
  > (−1)^{r(t)−1} Σᵢ i·αᵢ · η(t) = C,
  > where C depends only on lower order trees. The proof by induction
  > on r(t) is now complete, because **the coefficient of η(t) is
  > non-zero, by the stability of the method**."

* **Lean statement captures**: SAME content (modulo the `(-1)^{r(t)-1}`
  sign factor which is a non-vanishing absolute value bracket — see
  Discovery §2 below). My theorem states `Σᵢ (i+1)·αᵢ ≠ 0`, which
  matches Butcher's "the coefficient of η(t) is non-zero" claim in
  absolute value. The non-vanishing fact is sign-invariant: whether
  the coefficient is `(-1)^{r(t)-1}·Σᵢ i·αᵢ` or just `Σᵢ i·αᵢ`
  (the two formulations differ at even `r(t) ≥ 2` per the P2 audit),
  both require `Σᵢ i·αᵢ ≠ 0` as the stability-derived non-vanishing
  condition. My Lean statement encodes exactly this.

* **Cast convention**: my `((i.val + 1 : ℕ) : ℝ)` matches the §422
  `coef_α(M)` convention from cycle 342's
  `coef_α_eq_ρPoly_deriv_at_one_of_preconsistent` (line 882) and
  cycle 344's `coef_α_pos_of_stable_preconsistent` (line 934), not
  the `((i : ℕ) + 1 : ℝ)` form of cycle 250's `SatisfiesEq404b`
  (cycle 342's `coef_α_eq_sum_β_of_isConsistent` extracts the
  `push_cast`+`ring` bridge between the two).

* **No definition smuggling**: this is a pure corollary of cycle
  344's strict-positivity result via `ne_of_gt`. No new definitions
  introduced. The strict positivity itself was derived in cycle 344
  by composition with cycle 178's
  `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`, which is a
  genuine §441 theorem about the α-characteristic polynomial.

### `example` (BDF2 non-vacuity)

* Anonymous; instantiates the new theorem on `bdf2LMM` with
  `hk := by norm_num`, `bdf2LMM_isStable` (cycle 346), and
  `bdf2LMM_isPreconsistent` (cycle 175). No new mathematical content;
  pure non-vacuity sanity.

## Dead ends

None. P1 closed on first attempt; P2 audit went through cleanly.

A minor diagnostic moment: the initial `#print axioms` check failed
with "Unknown constant" because the cached `Section422.olean` was
stale (timestamp predating the edit). `lake build
OpenMath.Chapter4.Section422` regenerated the olean cleanly (no
errors, only pre-existing simp-unused-arg warnings in
`Section410.lean`); the axiom check then succeeded. This is a
harness/cache artifact, not a code issue.

## Discovery

### §1. The Heun-method falsification of cycle 360's coefficient

The crispest empirical falsification of cycle 360's coefficient is
the two-method comparison: `explicitEuler` and Heun's 2-stage method
both have `η(vertex) = 1`, but cycle 360's `linearResidualAt 1`
yields different values (1 vs 0). Since `cherry`'s only strict
subtree is `vertex`, a strict-subtree-only residual MUST agree
between methods with the same `η(vertex)`. cycle 360's residual fails
this; the corrected form (with `−i` in place of `i·(-1)^r(t)`)
satisfies it (both yield 1, = `η(vertex)²`).

This falsification is reproducible in Lean via two
`#eval`-equivalent paper computations — no Lean code change required
to verify; the cycle 358 `elementaryWeightQ_phi_inv_mk` + cycle 360
`linearResidualAt_one_mk_eq` closed forms compute symbolically to
the values quoted above.

### §2. The textbook's `(-1)^{r(t)-1}` factor is spurious

Per the audit table at `def_422B_phase_D_3_scoping.md` §10:

| r(t) | Tree | Coefficient of η(t) in η⁻¹(t) | Butcher's `(-1)^r(t)` |
|---|---|---|---|
| 1 | vertex | **−1** | −1 ✓ |
| 2 | cherry | **−1** | +1 ✗ |
| 3 | fork = mk [vertex, vertex] | **−1** | −1 ✓ |

Under our Φ-quotient encoding (cycle 234's `elementaryWeightQ_phi`
lifted from `M.elementaryWeight` to `Quotient PhiEquivalent.setoidSigma`),
the coefficient is **always −1** at i = 1, regardless of `r(t)`.
Butcher's textbook claim happens to match at odd `r(t)` and
mismatch at even `r(t)`.

I conjecture two possible reasons for the textbook discrepancy:
(a) Butcher implicitly uses a different sign convention for `η^{-i}`
(e.g. a transposed/antipode-twisted group structure where
multiplication carries signs); (b) a textbook typo not corrected
across editions. Neither matters for our purposes — the corrected
form `coefficient = -i` is what our quotient encoding produces, so
that's what we should use.

**This does NOT undermine P1's non-vanishing claim**: both
formulations of (422a)'s η(t)-coefficient at tree t agree up to
sign: `(-1)^{r(t)-1}·Σᵢ i·αᵢ` (Butcher's display) vs `−Σᵢ i·αᵢ`
(our encoding). The non-vanishing condition `Σᵢ i·αᵢ ≠ 0` is
identical.

### §3. Why cycle 362's parametricity Step 1 is unaffected

Cycle 362's `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
is a structural property of `derivativeWeightWithSrc` itself —
"given strict-subtree agreement of source-method elementary weights,
the `derivativeWeightWithSrc` values agree". It says nothing about
`linearResidualAt`'s coefficient choice. cycle 364's redefinition
of `linearResidualAt` doesn't touch cycle 362's theorem; cycle 365+
Step 2 will combine cycle 362's structural lemma with the corrected
`linearResidualAt` to derive the strict-subtree dependence claim.

### §4. The corrected `linearResidualAt` makes Step 2 structurally clean

Under cycle 360's (incorrect) definition, the cycle 361 closed form
`linearResidualAt_succ_mk_eq` reads:

```
linearResidualAt (m+1) ⟦M⟧ t
  = -(∑ⱼ (M.powRep (m+1)).2.b j · …) − (m+1)·(-1)^t.order·M.elementaryWeight t
```

The cycle 362 worker noted the substantive Step 2 obstacle was that
the second term reads `M.elementaryWeight` AT `t` itself (not at
strict subtrees of t). Under the corrected definition, the closed
form becomes:

```
linearResidualAt' (m+1) ⟦M⟧ t
  = -(∑ⱼ (M.powRep (m+1)).2.b j · …) + (m+1)·M.elementaryWeight t
```

The `(m+1)·M.elementaryWeight t` term now has the OPPOSITE sign
from the analogous contribution implicit in the powRep-sum.
Specifically: by cycle 235-style identities lifted to composite
representatives, the powRep-sum at `t = mk children` contains a
factor `(M.powRep (m+1)).2.inverse.elementaryWeight c`-type term
that, when expanded via the inverse identity, produces a
`-(m+1)·M.elementaryWeight t` contribution. The CORRECTED
`+(m+1)·M.elementaryWeight t` term cancels this exactly, leaving
only strict-subtree-dependent residuals.

This was the obstacle cycle 362 flagged as multi-cycle work. Under
the corrected definition, the cancellation is structural rather than
adversarial. Cycle 365+ Step 2 becomes plausibly tractable.

### §5. Implementation note: `lake env lean` doesn't update olean

`lake env lean <file>` checked the file (no errors) but did NOT
update the cached `.lake/build/lib/lean/.../*.olean`. Subsequent
`#print axioms` queries against the new symbol failed with "Unknown
constant" until `lake build` was invoked. Workaround: always invoke
`lake build OpenMath.Chapter4.Section422` (or `lake build`) before
axiom-checks on newly-added symbols. This is a known harness
behavior, documented for future workers.

## Suggested next approach

### Cycle 364 (P1, mandatory): ship the `linearResidualAt` definition fix

Per the cycle 363 P2 audit findings:

1. **Change cycle 360's definition** (line 1868 of
   `OpenMath/Chapter4/Section422.lean`):
   ```lean
   -- BEFORE (cycle 360):
   noncomputable def linearResidualAt (i : ℕ) (η_q : ...) (t : RT) : ℝ :=
     elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
       - (i : ℝ) * (-1)^t.order * elementaryWeightQ_phi η_q t

   -- AFTER (cycle 364):
   noncomputable def linearResidualAt (i : ℕ) (η_q : ...) (t : RT) : ℝ :=
     elementaryWeightQ_phi (η_q ^ (-(i : ℤ))) t
       + (i : ℝ) * elementaryWeightQ_phi η_q t
   ```

2. **Update 4 cycle 360/361 closed-form theorems** (`coeff_eta_t_in_eta_zpow_neg`,
   `linearResidualAt_vertex_eq_zero`, `linearResidualAt_one_mk_eq`,
   `linearResidualAt_succ_mk_eq`):
   * Remove `(-1)^t.order` factor from each.
   * Flip the sign of the `M.elementaryWeight t` term where it
     appears (in the two closed forms `_one_mk_eq` and `_succ_mk_eq`).
   * Proofs remain `unfold; rw; push_cast; ring`-class.

3. **Update 4–6 non-vacuity `example`s** to match new theorem signatures.

4. **LOC delta**: +40 to +60 (mechanical sign updates; no new content).

5. **Risk**: very low. `lake build` time will be ~250 s.

**Cycle 364 entry-point reading list**:
* `.prover-state/issues/def_422B_phase_D_3_scoping.md` §10
  "Cycle 363 audit" subsection (full recipe).
* `.prover-state/task_results/cycle_363.md` Discovery §2 + §4 (this
  document).
* `OpenMath/Chapter4/Section422.lean` lines 1858–2150 (the cycle
  360/361 ship to edit).

### Cycle 365+ (P0+, single-cycle): Phase D.3.b parametricity Step 2

After cycle 364's definition fix lands, attempt the parametricity
claim `linearResidualAt_depends_only_on_strict_subtrees`:

```lean
theorem linearResidualAt_depends_only_on_strict_subtrees (i : ℕ)
    {η_q η_q' : Quotient PhiEquivalent.setoidSigma} (t : RT)
    (h : ∀ s : RT, s.order < t.order →
         elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    linearResidualAt i η_q t = linearResidualAt i η_q' t
```

Recipe (per audit §4):

1. Unfold both sides via the (corrected) `linearResidualAt_succ_mk_eq`.
2. The `(i+1)·M.elementaryWeight t` term in both sides cancels
   *internally* (within each side) against the
   `(M.powRep (i+1)).2.inverse.elementaryWeight`-induced
   contribution in the powRep-sum.
3. After internal cancellation, both sides depend only on
   `elementaryWeightQ_phi` at strict subtrees of t.
4. Apply cycle 362's
   `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` to the
   residual sum to close.

Estimated LOC: 150–250 (depends on how cleanly the internal
cancellation in step 2 packages — may need a dedicated
"`(m+1)`-fold composite inverse decomposition" sub-lemma).

### Cycle 366+ (P1+, multi-cycle): Phase D.3.d + Phase E sealing

After Step 2 closes:
* **D.3.d**: `noncomputable def underlyingOneStepMethod_aux` —
  well-founded recursion on `RootedTree.order` solving (422a)
  inductively at each tree. Uses cycle 363 P1's non-vanishing fact
  as the denominator for the η(t) recursion. ~80–120 LOC.
* **Phase E**: lift `underlyingOneStepMethod_aux` to
  `Quotient PhiEquivalent.setoidSigma` and seal `def:422B`
  (`thm:422A` existence as a side-effect). ~60–100 LOC.

§422 streak: target **32 consecutive axiom-clean cycles** (336–367)
at full Phase E completion.
