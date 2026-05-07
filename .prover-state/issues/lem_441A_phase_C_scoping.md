# Issue: scoping the Phase C half of `lem:441A` (`aᵢ ≥ 0` for `i ∈ [2, k]`)

## Status

**Phase B is closed** (cycles 174–179): for every stable preconsistent
LMM with `0 < k`, `0 < M.aPoly.coeff 1`. The headline theorem is
`LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent` in
`OpenMath/Chapter4/Section441.lean:913`.

The remaining half of Butcher's Lemma 441A (`aᵢ ≥ 0` for `i = 2, …, k`)
is **Phase C**. This issue file scopes Phase C as multi-cycle work and
must be read by the cycle 181+ planner before any proof attempt is
green-lit. Cycle 180 produces this file; no Phase C proof body is in
scope for cycle 180.

## Section 1: Textbook argument (Butcher §441 p. 376)

The relevant paragraph (`extraction/raw_text/ch04.txt:1998–2008`,
preserved verbatim with the OCR glitches present in the source):

> Write ζ for a possible zero of a so that, because of the relationship
> between this polynomial and α, it follows that
>     (1−ζ) / (1+ζ)
> is a zero of α, unless it happens that ζ = −1, in which case there is
> a drop in the degree of α. In either case, we must have Re(ζ) ≤ 0.
> Because all zeros of a are real, or occur in conjugate pairs, the
> polynomial a can be decomposed into factors of the form `z − ξ` or
> of the form `z² − 2ξz + (ξ² + η²)`, where the real number ξ cannot be
> positive. This means that all factors have only terms with
> coefficients of the same sign, and accordingly this also holds for
> a itself. These coefficients must in fact be non-negative because
> a₁ > 0.

Distilled, the argument has five steps.

### Step C.A — Möbius transformation

The Möbius substitution `ψ(ζ) := (1 − ζ) / (1 + ζ)` is the canonical
bijection between the closed unit disk minus `{−1}` and the closed
left half-plane (and is its own inverse, `ψ ∘ ψ = id` on the relevant
domain). The textbook formula

  `a(z) = (1 + z)^k − Σᵢ αᵢ (1 + z)^{k−i} (1 − z)^i`

gives, after dividing through by `(1 + z)^k` (formally, on
`{z : ℂ | z ≠ −1}`),

  `a(z) / (1 + z)^k = 1 − Σᵢ αᵢ ψ(z)^i = α(ψ(z))`,

where `α(w) = w^k − α₁ w^{k−1} − ⋯ − αₖ` is the §410 polynomial (note:
the textbook's `α` here is what the cycle-174 file calls `αPoly`'s
"renormalised" form; we will need the precise sign/leading-coefficient
bridge from `aPoly` to one of `αPoly` or `ρPoly` for Phase C). After
clearing denominators by multiplying through by `(1 + z)^k`,

  `a(z) = (1 + z)^k · α(ψ(z))`,

so for any `ζ ≠ −1`:

  **`a(ζ) = 0` ⇔ `α(ψ(ζ)) = 0`** (over ℂ).

The case `ζ = −1` is handled separately: the textbook notes "there is
a drop in the degree of α" — equivalently, `a` has a root at `−1` if
and only if `α₀ = 1 − Σᵢ αᵢ = 0` (which is precisely the `IsConsistent`
condition); the corresponding root at infinity for `α` is OK.

### Step C.B — Stability ⇒ left-half-plane roots of `a`

By Butcher's `IsStable` (def 403A), all complex roots of the
characteristic polynomial `ρ` (equivalently `α`, modulo the `ρ ↔ α`
sign bridge already proved in cycle 174) lie in the closed unit disk
`|w| ≤ 1`, with simple roots on `|w| = 1`. Composing with the Möbius
bridge of Step C.A:

  for every complex root `ζ` of `a`, `Re(ζ) ≤ 0`,

since `Re(ψ⁻¹(w)) ≤ 0 ⇔ |w| ≤ 1` (the Möbius transformation maps the
closed unit disk to the closed left half-plane, modulo the `ζ = −1 ↔
w = ∞` boundary case).

The boundary case `ζ = −1` gives `Re(ζ) = −1 ≤ 0`, no problem.

### Step C.C — Real factorisation via conjugate-pair quadratics

Over ℝ, every real polynomial factors as a product of (a) real linear
factors `X − ξ` with `ξ ∈ ℝ`, and (b) real quadratic factors
`X² − 2(Re ζ)X + |ζ|²` corresponding to conjugate-root pairs `{ζ, ζ̄}`
with `ζ ∉ ℝ`. The leading coefficient is the product of the
leading coefficients of the factors (here all 1, except possibly an
overall `aₖ` constant — but `a` has leading coefficient `aₖ` which by
preconsistency / §441 conventions equals … well, this needs a careful
audit of `aPoly`'s leading coefficient, which is currently *not*
extracted as a named lemma in `Section441.lean`).

By Step C.B, every linear factor `X − ξ` has `ξ ≤ 0`, equivalently
`X − ξ = X + |ξ|` has *non-negative* coefficients. Every quadratic
factor `X² − 2(Re ζ)X + |ζ|²` has

* leading coefficient `1 ≥ 0`,
* `X` coefficient `−2(Re ζ) ≥ 0` (since `Re ζ ≤ 0`),
* constant coefficient `|ζ|² ≥ 0`.

So every real factor of `a` has non-negative coefficients.

### Step C.D — Product of polynomials with non-negative coefficients

If `p, q ∈ ℝ[X]` both have `coeff i ≥ 0` for all `i`, then so does
`p * q`, because `(p * q).coeff i = Σ_{j ≤ i} p.coeff j · q.coeff (i − j)`
is a sum of products of non-negative reals. Iterating over the
factorisation of Step C.C, `aᵢ ≥ 0` for all `i`.

### Step C.E — Sign-consistency closure

The textbook's last sentence is subtle: "all factors have only terms
with coefficients of the same sign" — in our convention all factors
have non-negative coefficients, so we get `aᵢ ≥ 0` directly without
needing the `a₁ > 0` strengthening for the closure. Butcher's phrasing
"these coefficients must in fact be non-negative because a₁ > 0" reads
as an alternative argument: if all factors had non-positive
coefficients, then `a₁` would be `≤ 0`, contradicting Phase B. We
sidestep that by working with non-negative-coefficient factors
throughout.

(NOTE: Butcher's wording suggests a possible sign ambiguity in the
factorisation; in the formalisation we should always normalise factors
to leading coefficient `+1` so the sign convention is unambiguous.)

## Section 2: Mathlib hooks needed

For each step, the candidate Mathlib lemma. Availability is annotated
**[CONFIRMED present]**, **[LIKELY present, verify]**, or
**[LIKELY MISSING, build helper]**. Verifications were partial in cycle
180 (Lean MCP search rate-limited); cycle 181+'s first task is to
re-verify with `lean_local_search` / `lean_loogle` before committing to
a phase plan.

### Step C.A hooks (Möbius bridge)

* `Polynomial.aeval` and `Polynomial.eval₂` for evaluating `α` at
  `ψ(z) = (1 − z) / (1 + z)`. **[CONFIRMED present]**
* `Polynomial.map` (lifts `ℝ[X] → ℂ[X]` via `Complex.ofReal` ring hom).
  **[CONFIRMED present]**
* `Polynomial.IsRoot.of_map` / `Polynomial.IsRoot.map` for transferring
  roots between ℝ and ℂ. **[LIKELY present, verify]**
* `Polynomial.aeval_eq_zero_iff_isRoot` family. **[LIKELY present,
  verify]**

The Möbius bridge as a polynomial identity is **most cleanly stated**
as

```lean
theorem aPoly_eq_one_plus_X_pow_mul_alphaPoly_psi
    {k : ℕ} (M : LinearMultistepMethod k) :
    M.aPoly = (1 + Polynomial.X) ^ k *
              (M.αPolyOrρPoly).comp ((1 - X) * (... ⁻¹))
```

— but division of polynomials is not closed in `ℝ[X]`. The standard
trick is to prove the *bivariate* identity

  `(1 + X)^k · (α applied to (1 − X)/(1 + X)) = aPoly`

as an identity in the *function field* `ℝ(X)`, or equivalently in
`ℝ[X]` after clearing denominators using `Polynomial.scaleRoots` or a
hand-rolled `MobiusTransformOfPolynomial`. **This is the highest-risk
step for Phase C.1.** A workable definition is

```lean
noncomputable def mobiusTransform (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i in Finset.range (p.natDegree + 1),
    Polynomial.C (p.coeff i) *
    (1 - Polynomial.X) ^ i * (1 + Polynomial.X) ^ (p.natDegree - i)
```

i.e. the explicit "homogenize then evaluate at `(1 - X, 1 + X)`"
construction. The identity `aPoly = mobiusTransform αPoly` (modulo
sign/normalisation conventions) should then be a `Finset.sum_congr` +
manipulation argument.

### Step C.B hooks (stability ⇒ left-half-plane)

* `IsStable` is defined in `OpenMath/Chapter4/Section404.lean` —
  audit whether it currently exposes the closed-unit-disk root location
  for `α` (or `ρ`) directly, or only as a consequence of the bounded-
  homogeneous-solution definition.
* If `IsStable` only gives bounded homogeneous solutions, we need an
  intermediate lemma: stability ⇒ all complex roots of `M.ρPoly` (or
  `αPoly`) lie in the closed unit disk. **This is likely already
  formalised as a private helper** in cycle 175's
  `geomSeq_isHomogeneousSolution_of_ρPoly_isRoot` recipe — extract and
  promote to a public lemma if so.
* For the simple-roots-on-the-boundary part: cycle 176's
  `idSeq_isHomogeneousSolution_of_preconsistent_ρPoly_deriv_zero` is
  the prototype, but Phase C only needs the **closed-disk location**,
  not the simple-root strengthening (which is what Phase B used). So
  this hook is `geomSeq_isHomogeneousSolution_of_ρPoly_isRoot`-style.

### Step C.C hooks (real factorisation)

* `Polynomial.roots` over ℂ — multiset of complex roots with
  multiplicity. **[CONFIRMED present]** (Mathlib.Algebra.Polynomial.Roots)
* `Polynomial.aroots` — multiset of roots in a base extension.
  **[CONFIRMED present]**
* `Polynomial.Splits` over `ℂ` (via `IsAlgClosed.splits` instance).
  **[LIKELY present, verify]** (also referenced in cycle 170's
  `Section431.lean`).
* `Polynomial.prod_multiset_X_sub_C_of_splits` or
  `Polynomial.eq_prod_roots_of_splits` — turns `splits` into the
  product representation `p = leadingCoeff p · ∏(X − rᵢ)`. **[LIKELY
  present, verify]**
* `Complex.normSq`, `Complex.mul_conj`, `Complex.add_conj`
  (`z + conj z = 2 · z.re`). **[LIKELY present, verify]** — the key
  identity is `(X − ζ) · (X − conj ζ) = X² − 2(Re ζ)X + |ζ|²` over ℂ,
  which then descends to ℝ since the coefficients are real.
* `Polynomial.X_sub_C_mul_X_sub_C_eq` — likely **[LIKELY MISSING,
  build helper]**: a lemma saying
  `(X − Polynomial.C ζ) * (X − Polynomial.C (conj ζ)) = X² − Polynomial.C (2·z.re) X + Polynomial.C (Complex.normSq ζ)`
  is custom Phase C infrastructure and almost certainly needs to be
  built as a private helper.
* `Polynomial.lifts` / `Polynomial.RestrictScalars` for showing the
  conjugate-pair quadratic over ℂ descends to a real polynomial.
  **[LIKELY present, verify]**

The cleanest path is probably:

1. Work entirely over ℂ first.
2. Use `Polynomial.eq_prod_roots_of_splits` to write
   `aPoly.map ofReal = leadingCoeff · ∏(X − ζᵢ)` over ℂ[X].
3. Pair conjugate roots: the multiset of roots is closed under
   `Complex.conj` because `aPoly` has real coefficients
   (`Polynomial.roots_map_conj` or similar lemma — **[LIKELY present,
   verify]**).
4. Group the multiset into real-root and conjugate-pair-quadratic
   pieces.
5. Each conjugate-pair quadratic over ℂ equals (the map of) a real
   quadratic with non-negative coefficients (Step C.A on
   `Polynomial.lifts`).
6. Real linear factors: each real root `ξ` of `aPoly` (over ℝ) maps
   to a root `ξ : ℂ` of `aPoly.map ofReal`; the `Re(ζ) ≤ 0` bound from
   Step C.B forces `ξ ≤ 0`, so `(X − ξ) = (X + |ξ|)` has non-negative
   coefficients.

### Step C.D hooks (non-negative product closure)

* `Polynomial.coeff_mul`. **[CONFIRMED present]**
* `Polynomial.natDegree_mul`. **[CONFIRMED present]**
* `Finset.sum_nonneg`. **[CONFIRMED present]**

The induction is on factor count; each base case is non-negativity of
a single factor's coefficients (Step C.C), each inductive step is

```lean
(p * q).coeff i = Σ_{j ≤ i} p.coeff j * q.coeff (i - j)
```

which is a sum of products of non-negatives, hence non-negative.
**Custom helper required**: cycle 181 should ship this as a public
`Polynomial.coeff_nonneg_of_factor_coeffs_nonneg` (or check Mathlib via
`lean_loogle "Polynomial.coeff_nonneg"`).

### Step C.E hooks (closure)

No additional Mathlib hooks. Combine Steps C.A through C.D.

### Genuine Mathlib gaps (sub-blockers)

If verification confirms any of the following are missing, file as
a sub-issue:

1. **`Polynomial.roots_map_conj` (or equivalent)**: real-coefficient
   polynomial's complex-root multiset is closed under conjugation.
   This is a conceptually simple statement but may not have a direct
   Mathlib name. Alternative: prove inline via `Polynomial.eval_map` +
   `Complex.conj_eval` bridges.
2. **`Polynomial.prod_X_sub_C_conjugate_pair_eq`**: the product
   `(X − C ζ) · (X − C (conj ζ))` equals (the lift of) a specific real
   quadratic. This is custom Phase C infrastructure — build as a
   helper.

## Section 3: Phasing

Each phase is bounded to 1–2 cycles. **Phase C is multi-cycle and must
NOT be attempted as a single deliverable.** The 4-phase split below
mirrors Phase B's successful B.1.β → B.2 → B.3 Step 1 → B.3 Step 2 →
B.4 cadence.

### Phase C.1 — Möbius algebraic bridge (1–2 cycles)

Deliverables:

* `private noncomputable def mobiusTransform : Polynomial ℝ → Polynomial ℝ`
  (or an equivalent, possibly using `Polynomial.scaleRoots`).
* `theorem aPoly_eq_mobiusTransform_alphaPoly_or_rhoPoly`: the
  algebraic identity bridging `aPoly` and one of `αPoly` / `ρPoly`
  under the Möbius substitution.
* `theorem aPoly_isRoot_iff`: ζ is a root of `aPoly` (over ℂ) iff
  either `ψ(ζ)` is a root of `α` (over ℂ) or `ζ = −1` AND
  `αPoly.degree < k`.
* BDF2 sanity witness on `bdf2LMM.aPoly`: explicit verification that
  the Möbius bridge holds at `bdf2LMM`.

LOC budget: ~150 LOC (definition + identity proof + BDF2 witness).

Aristotle suitability: medium — the algebraic identity is the bottleneck
and is structural rather than computational.

#### Cycle 181 update (2026-05-07) — Phase C.1 SHIPPED

Cycle 181 closed Phase C.1 in full. Delivered (axiom-clean,
sorry-clean, ~250 LOC):

* `mobiusTransform : ℕ → Polynomial ℝ → Polynomial ℝ` — homogenised
  parameterised version (degree `n` independent of `p.natDegree`,
  per the §441 textbook substitution `ψ(z) = (1−z)/(1+z)` with the
  Lean convenience that `n = k` is fixed by the LMM step count, not
  by `αPoly.natDegree` which can drop below `k` when `αₖ = 0`).
* `aPoly_eq_mobiusTransform_αPoly` — the algebraic bridge
  `M.aPoly = mobiusTransform k (Section410.αPoly M)`. Proof:
  `Polynomial.funext` recipe (cycle 180 template) + `Finset.sum_range_succ'`
  + αPoly coefficient computations (`αPoly_coeff_zero`, `αPoly_coeff_succ`)
  + `Fin.sum_univ_eq_sum_range` reindex + `ring`.
* `aPoly_aeval_eq_mul_αPoly_aeval` — multiplicative bridge for
  `ζ : ℂ` with `1 + ζ ≠ 0`:
  `aPoly.aeval ζ = (1 + ζ)^k · αPoly.aeval ((1 − ζ) / (1 + ζ))`.
  Proof: routes through the polynomial bridge + `eval₂` expansion +
  `field_simp` to factor out `(1 + ζ)^k`.
* `aPoly_aeval_eq_zero_iff_αPoly_aeval_at_mobiusArg` — complex-side
  root bridge for `ζ ≠ −1`. Direct corollary of the multiplicative
  identity + `mul_eq_zero` + `pow_ne_zero`.
* `bdf2LMM_aPoly_eq_mobiusTransform` and
  `bdf2LMM_mobiusTransform_αPoly_eq` — BDF2 sanity witnesses
  composing with cycle 180's `bdf2LMM_aPoly_eq` closed form.

Bridge target chosen: `αPoly` (Section410). Reasoning: Butcher's
textbook substitution `α(w) = 1 − Σᵢ αᵢ w^i` matches our §410 sign
convention `αPoly = 1 − Σᵢ αᵢ X^(i+1)` directly; routing through
`ρPoly = z^k − α₁z^{k−1} − ⋯ − αₖ` would have required an
additional reflection identity. The factorisation
`a(z) = (1+z)^k · α(ψ(z))` then follows by direct substitution.

`ζ = −1` boundary case: NOT handled separately in cycle 181. The
strategy listed it as optional and the cycle's deliverable bar
was met without it. Recommended for Phase C.2 (where it pairs
naturally with the `αₖ = 0` → degree-drop analysis under
stability).

Phase C.2 ready to start in cycle 182.

### Phase C.2 — Stability ⇒ `aPoly` roots in closed left half-plane (1 cycle)

Deliverables:

* `theorem aPoly_root_re_nonpos_of_stable`: for stable `M`,
  `∀ ζ ∈ aPoly.aroots ℂ, ζ.re ≤ 0`.
* Composition of Phase C.1's bridge with `IsStable`'s closed-unit-disk
  root location for `α` (or `ρ`).
* If `IsStable` does not directly provide the root location, an
  intermediate lemma `ρPoly_root_abs_le_one_of_stable` extracted from
  the cycle 175 private helper recipe.

LOC budget: ~80 LOC.

Aristotle suitability: medium — the composition is short but routes
through several Möbius / complex-arithmetic identities.

### Phase C.3 — Real factorisation + non-negative-coefficient closure (1–2 cycles)

This is the **highest-risk phase**. Deliverables:

* `private theorem aPoly_real_factorisation`: `aPoly` factors over `ℝ[X]`
  as a product of real linear factors `X − ξ` (with `ξ ≤ 0`) and real
  quadratic factors `X² + b·X + c` (with `b, c ≥ 0`).
* `private theorem coeff_nonneg_of_real_linear_factor_nonneg_const`
  and `coeff_nonneg_of_real_quadratic_factor_nonneg`.
* `private theorem coeff_nonneg_of_product_of_nonneg_coeff_factors`:
  the product of polynomials with non-negative coefficients has
  non-negative coefficients. (Verify Mathlib doesn't already have this.)

LOC budget: ~250–400 LOC (highest in Phase C).

Aristotle suitability: low — heavily structural, conjugate-pair
manipulation, multi-step decomposition.

**Mathlib infrastructure risk**: this phase blocks if Mathlib lacks
real-factorisation tooling. Alternative routes:

* Direct manipulation of `Polynomial.roots` over ℂ + manual
  conjugate-pair grouping. Higher LOC.
* `Polynomial.lifts` for the Schur-style "real polynomial as image of
  a real polynomial product under map ofReal" argument.
* For BDF2 specifically (k = 2): direct evaluation of `aPoly = (4/3)X +
  (8/3)X²` shows `a₂ = 8/3 ≥ 0` without invoking the general argument
  — this is the Phase C.bypass for BDF2 sanity.

### Phase C.4 — Combine and close `lem:441A` (1 cycle)

Deliverables:

* `theorem aPoly_coeff_nonneg_of_stable_preconsistent`: for `i ∈ [2, k]`
  and stable preconsistent `M`, `0 ≤ M.aPoly.coeff i`.
* Combine Phase C.1–C.3 outputs.
* Update `extraction/formalization_data/lean_status.json`: `lem:441A`
  goes from `partial` to `formalized`.
* BDF2 sanity witness: `bdf2LMM_aPoly_coeff_two_nonneg` (already
  partially anticipated by the Priority 2 stretch goal of cycle 180).

LOC budget: ~50 LOC.

Aristotle suitability: high — short closure proof.

## Section 4: Risk assessment

### LOC estimates

| Phase | LOC | Cycles | Cumulative |
| ----- | --- | ------ | ---------- |
| C.1   | ~150 | 1–2 | 150–300  |
| C.2   | ~80  | 1   | 230–380  |
| C.3   | ~300 | 1–2 | 530–680  |
| C.4   | ~50  | 1   | 580–730  |

Best case 4 cycles, worst case 6 cycles.

### Mathlib infrastructure risk per phase

* **Phase C.1 (medium)**: Möbius polynomial identity. Risk: division
  in `ℝ[X]` is not a ring operation, requiring careful homogenization.
  Mitigation: the explicit `mobiusTransform` definition above
  sidesteps division entirely.
* **Phase C.2 (low)**: relies on Phase C.1 + an `IsStable` ⇒ disk-root
  location helper which is likely already implicit in cycle 175's
  private aux. Risk: extracting the helper may force a refactor of
  the existing `geomSeq_isHomogeneousSolution_of_ρPoly_isRoot`.
* **Phase C.3 (HIGH)**: real factorisation via conjugate-pair
  quadratics is the textbook's slickest trick but Mathlib's polynomial
  factorisation API is *complex-side*, not *real-side*. The descent
  from ℂ-factorisation to ℝ-factorisation may require building one or
  two custom helpers (estimated +100 LOC). Mitigation: file a
  `polynomial_real_factorisation_via_conjugate_pairs.md` sub-issue
  during Phase C.3 if a key Mathlib hook is missing, and fall back to
  the direct-multiplication-of-multisets approach.
* **Phase C.4 (low)**: pure composition.

### Aristotle suitability per phase

* **Phase C.1**: medium. Submit the algebraic identity in pieces —
  the per-coefficient check, the polynomial-equality skeleton.
* **Phase C.2**: medium. Submit the composition with `IsStable`-side
  helpers as separate Aristotle jobs.
* **Phase C.3**: low. Heavily structural; manual proof preferred.
* **Phase C.4**: high. Short combine.

### Alternative routes if a phase blocks

* **Phase C.1 alternative**: bypass the explicit Möbius polynomial via
  pointwise evaluation — prove `∀ ζ : ℂ, aPoly.aeval ζ = 0 ↔
  α.aeval (ψ ζ) = 0` directly without the polynomial-identity bridge.
  Costs about the same; less reusable downstream.
* **Phase C.3 alternative — Schur-style**: if real factorisation
  blocks, route via the companion matrix and Schur decomposition (this
  is the Jordan-canonical-form path, also blocked per
  `jordan_canonical_form_missing.md`). Not a viable alternative
  without resolving the Jordan/Schur Mathlib gap separately.
* **Phase C.bypass for BDF2 only**: direct closed-form evaluation of
  `bdf2LMM.aPoly` at coefficient indices `0, 1, 2` (Priority 2 of cycle
  180; ships `aᵢ ≥ 0` for the canonical example without committing to
  Phase C infrastructure). This satisfies the BDF2 sanity bar but does
  NOT close `lem:441A` in general.

## Section 5: Cross-references

* `lem_441A_alpha_prime_negative.md` — the existing parent issue
  tracking the full `lem:441A` closure. **Update that file's "Cycle 179
  update" section to mark Phase B as closed and link to this issue
  for Phase C tracking.**
* `lem_441B_misinterpretation.md` — sibling `§441` cluster issue
  documenting interpretation pitfalls; relevant for the `αPoly` /
  `aPoly` distinction and the universal `c_{2i}` constants.
* `jordan_canonical_form_missing.md` — parallel infrastructure gap;
  not a blocker for Phase C but informative as a `Polynomial`-over-`ℂ`
  matrix-side blocker.
* `rouche_theorem_missing.md` — sibling `Polynomial`-over-`ℂ` complex-
  analytic infrastructure issue.
* `phantom_commit_verdict_pattern.md` — cycle 180 issue documenting
  why prior cycles' `attempts.md` rows reporting "Section441.lean was
  never staged" should be ignored.
* `OpenMath/Chapter4/Section410.lean::αPoly` — companion §410
  generating polynomial.
* `OpenMath/Chapter4/Section441.lean::ρPoly` — characteristic
  polynomial used by Phase B (cycle 174 onward).
* `OpenMath/Chapter4/Section441.lean::aPoly_coeff_one_pos_of_stable_preconsistent`
  — Phase B's headline (cycle 179, line 913).
* `OpenMath/Chapter4/Section441.lean::aPoly_coeff_zero_of_preconsistent`
  — `a₀ = 0` under preconsistency (cycle 173). Note: this means Phase
  C only needs `aᵢ ≥ 0` for `i ∈ [2, k]`, since `a₀ = 0 ≥ 0` and
  `a₁ > 0 ≥ 0` are already shipped.
* `extraction/formalization_data/entities/lem_441A.json` — the
  textbook statement and dependencies.
* `extraction/raw_text/ch04.txt:1998–2008` — verbatim Butcher §441
  text for Phase C's argument.

## Recommendation for cycle 181 planner

1. Re-verify the Mathlib hook availability in §2 with
   `lean_local_search` / `lean_loogle` (cycle 180 was rate-limited).
2. Choose **Phase C.1** as the cycle 181 target. Bounded (1–2 cycles),
   medium Aristotle suitability, no high-risk Mathlib gaps.
3. Defer **Phase C.3** until after C.1/C.2 are shipped — it's the
   high-risk phase and benefits from having the upstream infrastructure
   already validated.
4. Do NOT attempt Phase C in a single cycle.
5. Continue the BDF2-sanity-witness discipline established in Phase B
   (cycles 175–179): every new generic theorem in §441 should have a
   numerical companion theorem on `bdf2LMM`.
