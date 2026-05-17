# Issue: Phase D′ Step 2 scoping — `0 ≤ coef_β(M)` from `IsStable + IsConsistent` alone

## Status

Scoping document for **Phase D′ Step 2** of the `def:422B` underlying
one-step-method chain. Cycle 347 closed **Phase D′ Step 1** (the
`coef_β ↔ βPoly'(1)` polynomial bridge at `OpenMath/Chapter4/
Section422.lean:957`). The remaining work — deriving the β-side non-
negativity hypothesis

    0 ≤ ∑ i : Fin (k + 1), (i.val : ℝ) * M.β i
      = (Section410.βPoly M).derivative.eval 1   (cycle 347 bridge)

from `M.IsStable + M.IsConsistent` alone — is **multi-cycle work** and
must NOT be attempted as a single Lean deliverable. Cycle 348 produces
this file; cycle 349+ planners use it to break Phase D′ Step 2 into
single-cycle deliverables without re-scoping.

The cycle 200/201 (`thm:381H` deferred direction) rollback precedent
and the cycle 149/150 (`def:530B` operator-body sorry-first) rollback
precedent jointly require this scoping commitment *before* any worker
writes Lean code for the Phase D′ Step 2 derivation.

Predecessors:

* `.prover-state/issues/def_422B_path.md` — the multi-phase parent plan
  for `def:422B` (cycle 336 commitment).
* `.prover-state/issues/lem_441A_phase_C_scoping.md` — the sibling
  α-side scoping doc (cycle 180; template for this file).
* `.prover-state/issues/lem_441A_alpha_prime_negative.md` — cycle
  174–179 α-side closure (`ρ'(1) > 0` and `a₁ > 0`) which is the
  template the Phase D′ Step 2 derivation seeks to mirror.

## §1 Textbook source

The β-side characterization is **not** as standardised in Butcher §403
/ §441 as the α-side `ρ'(1) > 0` story is. This section establishes
that fact by quoting the candidate textbook regions verbatim and
identifying which equations could plausibly constrain
`Σᵢ i·βᵢ` (= `βPoly'(1)`) from `IsStable + IsConsistent` alone.

### §1.1 Butcher §403 (Stability) — `extraction/raw_text/ch04.txt:145–164`

The §403 definition of stability (Def 403A) is purely an
α-side condition on the homogeneous recurrence (403a):

> For a general initial value problem, the computed solution satisfies
> [eq with both α and β], …
> However, for the one-dimensional problem for which f(x, y) = 0, we
> have the simpler difference equation
>     yn = α₁ yn−1 + α₂ yn−2 + · · · + αk yn−k.               (403a)
> Definition 403A A linear multistep method [α, β] is 'stable' if the
> difference equation (403a) has only bounded solutions.

**Key observation**: stability constrains only `α` (the characteristic
polynomial `ρ`). It says **nothing** about `β`. So `IsStable` alone
provides no β-side constraint.

### §1.2 Butcher §404 (Consistency) — `extraction/raw_text/ch04.txt:166–236`

The consistency conditions (404a) + (404b):

> 1 = α₁ + α₂ + · · · + αk.                                   (404a)
> α₁ + 2α₂ + · · · + kαk = β₀ + β₁ + · · · + βk.              (404b)

In the project's notation,

* (404a) ⇔ `M.IsPreconsistent`,
* (404a) ∧ (404b) ⇔ `M.IsConsistent` (the conjunction is shipped at
  `Section404.lean:135`).

Equation (404b) gives a **linear equation in the β coefficients**
relating `Σᵢ βᵢ` (= our `sum_β`) to `Σᵢ i·αᵢ` (= our `coef_α`). Note
**carefully**: (404b) does *not* mention `Σᵢ i·βᵢ` = our `coef_β`. The
LHS of (404b) is α-side; the RHS is the *unweighted* sum of β.
**Consistency therefore does not directly characterise `coef_β`.**

The cycle 345 lemma `coef_α_eq_sum_β_of_isConsistent` at
`Section422.lean:818` is the Lean form of (404b).

### §1.3 Butcher §410 (Criteria for order) — `extraction/raw_text/ch04.txt:619–700`

Theorem 410A gives the Taylor expansion of the local-truncation error
as

    α(exp(−z)) − zβ(exp(−z)) = C₀ + C₁ z + C₂ z² + · · ·         (410c)

Order p ⇔ `C₀ = C₁ = · · · = Cp = 0`. Coefficient comparison gives:

* `C₀ = 1 − Σᵢ αᵢ = 0` ⇔ preconsistency.
* `C₁ = Σᵢ i·αᵢ − Σᵢ βᵢ = 0` ⇔ (404b).
* `C₂ = −(1/2!)·Σᵢ i²·αᵢ + Σᵢ i·βᵢ = 0`.

The third bullet rearranges to

    Σᵢ i·βᵢ = (1/2)·Σᵢ i²·αᵢ ⇔ order ≥ 2 (i.e. C₂ = 0).

**Key consequence**: `coef_β = Σᵢ i·βᵢ` is determined by `Σᵢ i²·αᵢ`
*only when order ≥ 2 holds*. Our hypothesis is `IsConsistent` (order
≥ 1), not order ≥ 2, so this equation does **not** pin `coef_β` from
`IsStable + IsConsistent` alone. It does, however, suggest that under
order ≥ 2, `coef_β = (1/2)·Σᵢ i²·αᵢ`, and stability gives some
constraints on the α-side moments. **This is one candidate route
(Route D below)**.

### §1.4 Butcher §441 (Maximum order) — `extraction/raw_text/ch04.txt:1933–2068`

§441 introduces *Möbius-transformed* polynomials

    a(z) = a₀ + a₁ z + · · · + ak z^k = (1 + z)^k · α((1−z)/(1+z))
    b(z) = b₀ + b₁ z + · · · + bk z^k = (1 + z)^k · β((1−z)/(1+z))

Lemma 441A (lines 1975–2008) characterizes the *Möbius-transformed*
α-coefficients `aᵢ`:

> Lemma 441A If the method under consideration is stable then a₁ > 0
> and aᵢ ≥ 0, for i = 2, 3, . . . , k.

There is no analogous Lemma 441B' characterising the *Möbius-
transformed* β-coefficients `bᵢ`. Lemma 441B (line 2011) instead
characterises the **Taylor coefficients** `c₂, c₄, . . .` of
`z / log((1+z)/(1−z))`:

> Lemma 441B The coefficients c₂, c₄, . . . are all negative.

Theorem 441C (the Dahlquist barrier) then combines the *signs* of
`aᵢ` and `c₂ᵢ` to bound the attainable order. **The β-polynomial `b`
is referenced only as a remainder term**: `a(z)·(stuff) − b(z) =
O(zᵖ)`. So §441 does *not* directly characterise `b`'s coefficient
signs or `β`'s derivative-at-1.

**Conclusion of §1.4**: The β-side analog of Lemma 441A — "stable ⇒
`bᵢ ≥ 0`" or "stable ⇒ `βPoly'(1) ≥ 0`" — is **NOT in the textbook
as a freestanding lemma**. Any β-side route must be derived from
secondary structure (e.g. (404b), the order-2 condition, or one-leg-
method §452 algebra).

### §1.5 Butcher §452 (One-leg ↔ LMM transformation) — `extraction/raw_text/ch04.txt:2465–2480`

The §452 transformation between a one-leg method and its underlying
LMM uses the *fractional time offset*

    x̄ₙ = xₙ − (Σᵢ i·βᵢ / Σᵢ βᵢ) h,                              (452a)

i.e., `(coef_β) / (sum_β)` is the fractional time offset for the one-
leg method. By (404b) under consistency, the denominator equals
`coef_α`, which is strictly positive under stability + preconsistency
(cycle 344's `coef_α_pos_of_stable_preconsistent`). So the ratio
`coef_β / coef_α` is well-defined under `IsStable + IsConsistent`.

**Interpretation**: `coef_β ≥ 0` ⇔ the one-leg evaluation point `x̄ₙ`
lies at or to the *left* of `xₙ`. This is a structural property of the
underlying one-leg method, but **the textbook does not state it as a
theorem under `IsStable + IsConsistent` alone**. The one-leg
formulation is used to *define* G-stability in §451, not to derive
sign constraints on β.

### §1.6 Summary

The textbook **does not** provide a direct lemma of the form
"`IsStable + IsConsistent ⇒ 0 ≤ Σᵢ i·βᵢ`". The strongest available
textbook routes are:

* (404b) gives `coef_α = sum_β` under consistency, but this is the
  *unweighted* β-sum, not `coef_β = Σᵢ i·βᵢ`.
* §410 order conditions give `Σᵢ i·βᵢ = (1/2)·Σᵢ i²·αᵢ` under order
  ≥ 2, but our hypothesis is only order ≥ 1.
* §441 sign lemmas are about the *Möbius-transformed* `aᵢ`, not the
  raw `βᵢ` and not the derivative `βPoly'(1)`.
* §452 interprets `coef_β/coef_α` as a one-leg time offset, but
  doesn't constrain its sign.

This is the central obstruction the cycle 349+ workers must confront.
**Phase D′ Step 2 may not be closable under exactly `IsStable +
IsConsistent`**; it may require a strengthening of hypotheses (e.g. to
order ≥ 2, or to additional sign conditions on β) that must be
documented per the cycle 250 `alphaWeight` precedent on definition
smuggling.

## §2 What we need to prove

### §2.1 Target theorem (coefficient form)

```lean
theorem coef_β_nonneg_of_stable_consistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hConsistent : M.IsConsistent) :
    0 ≤ ∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i
```

### §2.2 Target theorem (polynomial form, equivalent via cycle 347)

```lean
theorem βPoly_deriv_eval_one_nonneg_of_stable_consistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hConsistent : M.IsConsistent) :
    0 ≤ (Section410.βPoly M).derivative.eval 1
```

The two forms are interchangeable by cycle 347's
`coef_β_eq_βPoly_deriv_at_one` at `Section422.lean:957`.

### §2.3 Downstream consumer (the unconditional corollary)

The Phase D′ Step 2 goal motivates a Phase D′ Step 3 follow-up:

```lean
theorem Eq422a_at_vertex_eta_eq_of_stable_consistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hConsistent : M.IsConsistent)
    {η_q : Quotient PhiEquivalent.setoidSigma}
    (hEq : Eq422a M η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex
      = (∑ i : Fin (k + 1), M.β i)
          / ((∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
              + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i))
```

This drops cycle 345's `hβ_nn` hypothesis from
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent` at
`Section422.lean:793` and simultaneously upgrades the
preconsistency-only hypothesis to full consistency. The unconditional
corollary is the ultimate deliverable; Phase D′ Step 2 is the
prerequisite.

### §2.4 Faithfulness note

A `coef_β ≥ 0` theorem under `IsStable + IsConsistent` would be a
genuine mathematical result about consistent stable LMMs. The
textbook (§1 above) does not state it directly; if cycle 349+
derives it via the algebraic route below, the resulting theorem is a
**helper lemma**, not a textbook entity. There is no `entities/<id>.
json` to register it against. The faithfulness-check obligation is
that the derivation cite the textbook lemmas it composes, and that
the hypothesis list match the strongest available consistency-side
constraint without smuggling in `order ≥ 2` (which would be
strengthening the hypotheses beyond what is stated).

## §3 Existing infrastructure inventory (verified at HEAD)

All declarations below verified by `grep -n` / file-position spot
checks against HEAD `1b0fdef`. The header `[OK]` confirms presence;
absent symbols are flagged `[MISSING]`.

### §3.1 From `OpenMath/Chapter4/Section422.lean` (1000 lines)

* `[OK]` `Eq422a` (line 327) — Definition of the (422a) predicate.
* `[OK]` `coef_α_eq_ρPoly_deriv_at_one_of_preconsistent` (line 704)
  — cycle 344 α-side bridge.
* `[OK]` `coef_α_pos_of_stable_preconsistent` (line 737) — cycle 344
  α-side positivity (composition of cycle 344 bridge + cycle 178
  `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`).
* `[OK]` `Eq422a_at_vertex_eta_eq_of_stable_preconsistent` (line 793)
  — cycle 345 conditional corollary (carries `hβ_nn` hypothesis;
  Phase D′ Step 2 target is to drop this).
* `[OK]` `coef_α_eq_sum_β_of_isConsistent` (line 818) — cycle 345
  Lean form of (404b).
* `[OK]` `coef_β_nonneg_of_β_nonneg` (line 881) — cycle 346 pointwise
  helper (premise version we aim to strengthen).
* `[OK]` `bdf2LMM_β_nonneg` (line 891) — cycle 346 pointwise β
  non-negativity for BDF2.
* `[OK]` `bdf2LMM_coef_β_nonneg` (line 900) — cycle 346 composed
  coefficient non-negativity for BDF2.
* `[OK]` `coef_β_eq_βPoly_deriv_at_one` (line 957) — cycle 347
  β-side bridge (Phase D′ Step 1).
* `[OK]` `βPoly_deriv_eval_one_nonneg_of_β_nonneg` (line 993) —
  cycle 347 corollary (pointwise-β premise version of the polynomial
  goal).

**Important caveat**: `coef_α` and `coef_β` are *not* named Lean
declarations. They are **mathematical notation in docstrings/comments**
for the explicit sums

    coef_α(M) = ∑ i : Fin k,       ((i.val + 1 : ℕ) : ℝ) * M.α i.succ
    coef_β(M) = ∑ i : Fin (k + 1), ((i.val     : ℕ) : ℝ) * M.β i

Theorems state these forms explicitly via `∑` rather than a named
abbreviation. Cycle 349+ workers should follow this convention (no
new abbreviation `def coef_β := ∑ …` is needed unless theorem statements
become unwieldy).

### §3.2 From `OpenMath/Chapter4/Section410.lean` (1072 lines)

* `[OK]` `αPoly` (line 95).
* `[OK]` `βPoly` (line 103). Definition: `Σ_{i:Fin (k+1)} C(M.β i) · X^i`.
* `[OK]` `βPoly_explicitEuler` (line 179): `βPoly explicitEulerLMM = X`.
* `[OK]` `βPoly_natDegree_le` (line 219): `(βPoly M).natDegree ≤ k`.
* `[OK]` `ρPoly` (line 592).

### §3.3 From `OpenMath/Chapter4/Section404.lean` (5815 lines)

* `[OK]` `LinearMultistepMethod.IsPreconsistent` (line 69).
* `[OK]` `LinearMultistepMethod.SatisfiesEq404b` (line 124).
* `[OK]` `LinearMultistepMethod.IsConsistent` (line 135): conjunction
  of `IsPreconsistent` and `SatisfiesEq404b`.
* `[OK]` `LinearMultistepMethod.IsStable` (line 202).
* `[OK]` `explicitEulerLMM`, `implicitEulerLMM` with full Is*
  witnesses.

### §3.4 From `OpenMath/Chapter4/Section441.lean` (1227 lines)

* `[OK]` `aPoly` (line 111) — §441 Möbius-transformed α polynomial.
* `[OK]` `ρPoly_no_real_root_gt_one` (line 504) — cycle 175.
* `[OK]` `ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent` (line
  599) — cycle 176.
* `[OK]` `ρPoly_pos_on_Ioi_one` (line 707) — cycle 177.
* `[OK]` `ρPoly_deriv_eval_one_pos_of_stable_preconsistent` (line 767)
  — cycle 178 (α-side template for the cycle 349+ β-side analog).
* `[OK]` `bdf2LMM_isPreconsistent` (line 837).
* `[OK]` `aPoly_coeff_one_pos_of_stable_preconsistent` (line 913) —
  cycle 179.
* `[OK]` `mobiusTransform` (line 1041) — cycle 181's homogenised
  Möbius polynomial transform.

### §3.5 From `OpenMath/Chapter4/Section451.lean` (307 lines)

* `[OK]` `bdf2LMM` (line 140).
* `[OK]` `bdf2LMM_isStable` (line 287) — cycle 346.
* `[MISSING]` `bdf2LMM_isConsistent`. Only `bdf2LMM_isPreconsistent`
  (Section441 line 837) exists; the (404b) half is unshipped. **Cycle
  349+ entry point may need to ship this as a 5-line precursor witness
  (`SatisfiesEq404b` numeric check on `(4/3) + 2·(-1/3) = 0 + 2/3 = 2/3`,
  giving LHS = 2/3, RHS = 2/3, so `IsConsistent = ⟨isPreconsistent,
  SatisfiesEq404b⟩` follows).**

### §3.6 Mathlib hooks (to verify before Phase D′.2.x)

Each cycle 349+ phase should re-verify the listed hooks via
`lean_local_search` / `lean_loogle`:

* `Polynomial.derivative_eval` family — cycle 347 already uses
  `derivative_C_mul_X_pow`, `eval_finset_sum`, `derivative_sum`.
* `Polynomial.coeff_natDegree` and `Polynomial.leadingCoeff_eq` for
  leading-coefficient sign analysis (Route A precursor).
* `Polynomial.continuousOn` and `IntermediateValueTheorem` variants for
  real-analytic Route A (sign-on-(1,∞) analog of cycle 177).
* `Finset.sum_nonneg`, `mul_nonneg` (used by cycle 346).
* `Polynomial.aroots`, `Polynomial.Splits`, `IsAlgClosed.splits`
  (Route C — complex root-location of `βPoly`).

## §4 Candidate routings

The cycle 349+ worker must choose between (at least) the following
four routes. Each is annotated with **LOC budget**, **cycle count**,
**Mathlib-hook completeness**, and **risk of dead end**.

### Route A — α-side template port (mirror cycle 175–178 on β-side)

**Plan**: replicate the cycle 175–178 chain replacing `ρPoly` with
`βPoly`:

1. `βPoly_no_real_root_gt_one` (Route A.1): mirror cycle 175.
2. `βPoly_deriv_eval_one_ne_zero_of_stable_consistent` (Route A.2):
   mirror cycle 176, but routing via stability + consistency (NOT
   stability + preconsistency, since stability alone doesn't constrain
   β).
3. `βPoly_pos_on_Ioi_one` (Route A.3): mirror cycle 177.
4. `βPoly_deriv_eval_one_pos_of_stable_consistent` (Route A.4): mirror
   cycle 178.

**Critical risk (R2 in §6)**: the α-side chain works because `ρPoly`
has *known leading coefficient `+1`* (Section410: `ρPoly =
X^k − α₁X^(k−1) − · · · − αk`). This makes "ρ → +∞ as z → +∞" trivial.

`βPoly` has leading coefficient `M.β k`, which is **not fixed by
stability or consistency**:

* For *explicit* LMMs (like explicitEulerLMM, AdamsBashforth-`k`), the
  convention is `β k = 0`, so `βPoly` has degree `< k`. Route A's
  "go to +∞" argument trivially fails.
* For *implicit* LMMs (like BDF2), `β k` may have any sign. For BDF2,
  `β 0 = 2/3, β 1 = β 2 = 0`, so `βPoly = (2/3) · 1 = 2/3` (a
  constant). Again "go to +∞" doesn't apply.

So Route A is **structurally inappropriate** for `βPoly`. Killing
Route A early saves cycle 349's planning bandwidth.

* LOC budget: ~300 LOC (if it worked).
* Cycle count: 4–5.
* Mathlib hook completeness: high (same as cycles 175–178).
* Risk of dead end: **HIGH** — leading-coefficient obstruction is
  fundamental.

**Verdict**: NOT RECOMMENDED. Do not port; flag and move on.

### Route B — Consistency-driven (404b composition)

**Plan**: use (404b) directly via cycle 345's
`coef_α_eq_sum_β_of_isConsistent`. We have

    coef_α(M) = ∑ᵢ βᵢ = sum_β(M)            (404b)

and `0 < coef_α(M)` under stability + preconsistency (cycle 344).
Hence `0 < sum_β(M)`. **But this gives `sum_β > 0`, not `coef_β ≥ 0`.**

The two quantities differ: `coef_β = Σ i·βᵢ` weights each `βᵢ` by
its index, while `sum_β = Σ βᵢ` weights uniformly. No textbook
equation directly bridges them.

* LOC budget: ~50 LOC.
* Cycle count: 1.
* Mathlib hook completeness: full (everything already shipped).
* Risk of dead end: **HIGH** — proves the *wrong* quantity. Useful
  as a precursor (`sum_β > 0`), but does not close Phase D′ Step 2.

**Verdict**: SHIP THE PRECURSOR (`sum_β_pos_of_stable_consistent`) as
a 1-cycle Phase D′.2.0 deliverable; do NOT mistake it for closure.

### Route C — Stability-polynomial / boundary-locus argument

**Plan**: Dahlquist-stability of an LMM is characterized in textbook
§432 ("Examples of the boundary locus method", ch04.txt:1569) by the
joint behaviour of `ρ` and `σ` (Butcher's σ = our `βPoly`). The
boundary-locus condition is

    R(z) := σ(z) / ρ(z) = h               (boundary locus map)

For Dahlquist stability, the unit-circle image of `R` plus interior
constraints gives boundary conditions on σ. **If §432 provides a
sign-definite constraint on `σ'(1)`** under stability, that would
close Phase D′ Step 2.

* LOC budget: ~400+ LOC (boundary-locus formalisation is heavy).
* Cycle count: 4–6.
* Mathlib hook completeness: low — `Polynomial.roots` over ℂ
  is available, but complex-analytic root-location (Schur, Routh-
  Hurwitz) is *not* yet in Mathlib in a clean form.
* Risk of dead end: **HIGH** — depends on Mathlib's complex-analytic
  infrastructure (the same blocker as `jordan_canonical_form_missing.
  md` and `rouche_theorem_missing.md`).

**Verdict**: DEFER. If Routes B/D both fail, revisit Route C in a
multi-cycle scoping doc of its own (mirror of cycle 180's `lem_441A_
phase_C_scoping.md` structure for the α-side Möbius-transform path).

### Route D — Order-2 strengthening + §410 algebraic identity

**Plan**: From §1.3, under order ≥ 2:

    coef_β = (1/2) · Σᵢ i² · αᵢ                                   (*)

Show separately that `IsStable + IsConsistent + order ≥ 2 ⇒ 0 ≤ Σᵢ i²
· αᵢ`, then divide by 2.

* LOC budget: ~150 LOC.
* Cycle count: 2.
* Mathlib hook completeness: high (only `Finset.sum_le_sum` family).
* Risk of dead end: MEDIUM. The hypothesis-strengthening **weakens
  the target theorem** (no longer about `IsStable + IsConsistent`
  alone). For downstream `Eq422a_at_vertex_eta_eq` use, this is
  acceptable if all consumers are order-2 LMMs; for the textbook
  `def:422B`, the original hypothesis pair is `IsStable +
  IsPreconsistent` (cycle 345 used preconsistency, not full
  consistency), so even order-2 may be a strict strengthening.

**Verdict**: PROMISING. Cycle 349 should first verify whether
`0 ≤ Σᵢ i²·αᵢ` is itself derivable from `IsStable + IsConsistent`
(no order-2 needed) — this would be a **substantive intermediate
lemma**, possibly via the §441 Möbius-transformed `aᵢ ≥ 0` chain
(cycle 181+ infrastructure).

### Route E — Reformulate the Eq422a corollary to use `sum_β` instead

**Plan**: revisit cycle 345's
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent`. The hypothesis
`hβ_nn : 0 ≤ coef_β(M)` is used to guarantee that the denominator
`coef_α + coef_β` is non-zero (so the linear equation in `η(τ)` can be
solved). But under `IsStable + IsConsistent`, we already have
`0 < coef_α` (cycle 344), so the denominator is non-zero **without**
needing `coef_β ≥ 0` — as long as we can rule out
`coef_α + coef_β = 0`, which holds whenever `coef_β ≥ −coef_α + ε`.

Reading the cycle 345 proof (`Section422.lean:804–806`): the
`hβ_nn` hypothesis is consumed *only* to discharge the non-vanishing
of the denominator via `linarith [hα_pos, hβ_nn]`. **Replacing it
with a weaker `coef_β > −coef_α` would suffice.**

The intermediate sufficient condition: `coef_α + coef_β ≠ 0`. Under
`IsConsistent`, by (404b), `coef_α = sum_β`, so

    coef_α + coef_β = sum_β + coef_β = Σᵢ (i + 1) · βᵢ
                                     = (1 + something)

If we can show `Σᵢ (i + 1) · βᵢ ≠ 0` under `IsStable + IsConsistent`,
the corollary closes without `coef_β ≥ 0`.

* LOC budget: ~80 LOC.
* Cycle count: 1–2.
* Mathlib hook completeness: high.
* Risk of dead end: MEDIUM — depends on whether `Σᵢ (i + 1) · βᵢ ≠ 0`
  is *easier* than `coef_β ≥ 0`. Possibly equivalent in difficulty.

**Verdict**: ALTERNATIVE WORTH EXPLORING. If Route D's intermediate
lemma proves intractable, Route E may sidestep the obstruction by
weakening the hypothesis on `coef_β` from non-negativity to non-
vanishing-when-summed-with-`coef_α`.

### §4.6 Route comparison summary

| Route | LOC | Cycles | Mathlib OK | Dead-end risk |
|---|---|---|---|---|
| A (template port) | 300 | 4–5 | high | **HIGH** (leading-coeff obstr) |
| B (404b alone) | 50 | 1 | full | **HIGH** (proves wrong thing) |
| C (boundary locus) | 400+ | 4–6 | low | HIGH (complex-analytic gap) |
| D (order-2 + Σi²·αᵢ ≥ 0) | 150 | 2 | high | MEDIUM (hyp strengthening) |
| E (reformulate corollary) | 80 | 1–2 | high | MEDIUM (equiv difficulty) |

**Recommendation**: Cycle 349 begins with Route E (lowest LOC, no
hypothesis-strengthening, sidesteps the textbook obstruction). If
Route E proves equivalent in difficulty, fall back to Route D's
intermediate lemma `0 ≤ Σᵢ i²·αᵢ` under `IsStable + IsConsistent`,
because that result is independently useful for §410 order-2 sign
analysis and §441 Phase C corollaries.

## §5 Phase decomposition

Subject to revision based on cycle 349's textbook re-reading and
hook verification.

### Phase D′.2.0 — Precursor witnesses + scoping continuation (1 cycle)

Deliverables:

1. Ship `bdf2LMM_isConsistent` (the missing (404b) half) at
   `Section451.lean` or `Section441.lean`. ≈10 LOC. This unblocks the
   downstream BDF2 sanity witnesses for Routes D and E.
2. Ship `sum_β_pos_of_stable_consistent` as a Route B precursor:
   ```lean
   theorem sum_β_pos_of_stable_consistent
       {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
       (hStable : M.IsStable) (hConsistent : M.IsConsistent) :
       0 < ∑ i : Fin (k + 1), M.β i := by
     rw [← coef_α_eq_sum_β_of_isConsistent M hConsistent]
     exact coef_α_pos_of_stable_preconsistent M hk hStable hConsistent.1
   ```
   ≈10 LOC. This is the *correct* `sum_β > 0` claim, separate from
   the `coef_β ≥ 0` Phase D′ Step 2 target.
3. Decide between Route D and Route E for Phase D′.2.1 based on
   cycle-349 re-reading of `extraction/raw_text/ch04.txt` §410, §441,
   §432.

LOC budget: ~30 LOC.

Aristotle suitability: high (both precursors are 1-line composition
proofs).

### Phase D′.2.1 — Either Route D or Route E (1–2 cycles)

**If Route E chosen**:

Deliverable: refactor
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent` to consume a weaker
hypothesis `h : coef_α(M) + coef_β(M) ≠ 0` and produce the corollary

```lean
theorem Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weaker
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hPre : M.IsPreconsistent)
    (h_denom_ne : (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
                  + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i) ≠ 0)
    {η_q : ...} (hEq : Eq422a M η_q) : ...
```

Then derive a `IsConsistent`-only corollary by showing `coef_α +
coef_β = Σᵢ (i + 1) · βᵢ ≠ 0` under consistency.

LOC budget: ~100 LOC (refactor + new corollary + BDF2/explicitEuler
witnesses).

**If Route D chosen**:

Deliverable: prove `0 ≤ Σᵢ i² · αᵢ` under `IsStable + IsConsistent`.
This requires either (a) routing through §441's `aᵢ ≥ 0` chain (cycle
181+ Möbius infrastructure), or (b) a direct argument from the
characteristic-polynomial `ρ` second derivative at 1. The direct
argument's analog of cycle 178 is

    ρ''(1) = Σᵢ i(i−1)·αᵢ = Σᵢ i²·αᵢ − Σᵢ i·αᵢ = Σᵢ i²·αᵢ − coef_α,

so `Σᵢ i²·αᵢ = ρ''(1) + coef_α ≥ 0` would follow if `ρ''(1) ≥
−coef_α`, which requires more α-side machinery than cycle 178
provides.

LOC budget: ~150 LOC.

### Phase D′.2.2 — Close `coef_β_nonneg_of_stable_consistent` (1 cycle)

Deliverable: ship the chosen-route headline theorem. If Route E,
this phase ships nothing new (Phase D′.2.1 already closes the
corollary). If Route D, this phase shifts from `0 ≤ Σᵢ i²·αᵢ` to
`0 ≤ coef_β` via (*) of §1.3, requiring order ≥ 2 as an additional
hypothesis (and a faithfulness-doc note flagging the strengthening).

LOC budget: ~50 LOC.

### Phase D′.2.3 — Unconditional `Eq422a` corollary (1 cycle)

Deliverable: ship

```lean
theorem Eq422a_at_vertex_eta_eq_of_stable_consistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hConsistent : M.IsConsistent)
    {η_q : ...} (hEq : Eq422a M η_q) : ...
```

dropping the cycle 345 `hβ_nn` hypothesis. If Phase D′.2.2 yielded
`coef_β ≥ 0`, this is a direct composition (≈10 LOC). If Phase
D′.2.1 chose Route E, the corollary is already shipped and this phase
trivially exists; ship only BDF2 + explicitEuler sanity witnesses
(≈30 LOC).

LOC budget: ~40 LOC.

### Phase summary

| Phase | LOC | Cycles | Cumulative |
|---|---|---|---|
| D′.2.0 (precursors) | 30 | 1 | 30 |
| D′.2.1 (D or E) | 100–150 | 1–2 | 130–180 |
| D′.2.2 (close) | 0–50 | 0–1 | 130–230 |
| D′.2.3 (corollary) | 10–40 | 1 | 140–270 |

**Best case** (Route E): 3 cycles total, ~140 LOC.
**Worst case** (Route D, order-2 strengthening): 5 cycles total,
~270 LOC.

## §6 Risk assessment

* **R1 — Textbook obstruction**: §1 establishes that no direct
  textbook lemma characterises `coef_β ≥ 0` under `IsStable +
  IsConsistent`. **Mitigation**: cycle 349 begins with the §410 / §432
  / §441 re-reading to confirm or refute the obstruction. If
  confirmed, document the gap and adopt Route E (which sidesteps the
  obstruction) rather than Route D (which strengthens hypotheses).

* **R2 — `βPoly` leading coefficient is sign-indefinite**: §410's
  `βPoly = Σ_{i:Fin (k+1)} M.β i · X^i` has leading coefficient
  `M.β k`, which can be zero (explicit LMMs), positive (BDF), or
  negative (in principle). This rules out **Route A** (no clean "go
  to +∞" argument). **Mitigation**: cycle 349 must not attempt the
  template port; flag Route A as ruled out in the cycle's first
  hour.

* **R3 — GPFS slowness on Section441**: cycles 182–224 documented
  persistent GPFS timeouts on `lake env lean OpenMath/Chapter4/
  Section441.lean`. Section422 has compiled cleanly throughout
  cycles 336–347 (≤300s warm rebuilds). **Mitigation**: keep all
  Phase D′.2.x deliverables in Section422; do not require Section441
  recompiles. The Möbius-transform infrastructure is already in
  Section441 at HEAD (lines 504–1041) but accessing it from
  Section422 only requires the `import` to remain stable, not a
  fresh Section441 compile.

* **R4 — Faithfulness divergence**: per cycle 250's `alphaWeight`
  precedent, if Phase D′ Step 2 strengthens the hypotheses (e.g. to
  order ≥ 2) or adds non-textbook sign conditions, the resulting
  theorem deviates from the natural textbook interpretation.
  **Mitigation**: every Phase D′.2.x deliverable must include a
  faithfulness-check entry in its task results documenting (a) the
  exact hypothesis pair, (b) whether the textbook supports it, and
  (c) the downstream use (e.g. Phase D′.2.3 corollary may legitimately
  consume a stronger hypothesis if it produces a weaker conclusion).

* **R5 — Multi-cycle streak burnout**: `def:422B` has now absorbed
  12 consecutive cycles (336–347). Phase D′ Step 2 adds 3–5 more.
  At cycle 15+ on a single entity, planner attention drift becomes a
  failure mode (analogous to the cycle 200/201 rollback after a
  similar streak). **Mitigation**: the cycle 348 scoping doc serves
  the dual purpose of documenting the route *and* providing a hard
  checkpoint at which the cycle 349+ planner can verify that
  continued investment is warranted (vs. pivoting per `cycle_336_
  pivot_options.md`).

* **R6 — Route C dead-end on Mathlib gap**: if Routes B/D/E all fail
  and the only remaining option is Route C, the boundary-locus /
  complex-analytic infrastructure is parallel to
  `jordan_canonical_form_missing.md` and `rouche_theorem_missing.md`.
  Phase D′ Step 2 would block until those gaps are closed.
  **Mitigation**: this is the Phase E pivot trigger — if Phase
  D′.2.x stalls at the Mathlib gap, the planner pivots to
  `thm:535A` / `thm:541A` (the cycle 336 pivot menu) rather than
  attempting Schur/Routh-Hurwitz formalisation.

## §7 Cycle 349 entry point

Concrete deliverable for the cycle 349 worker:

### §7.1 First 30 minutes (textbook re-reading)

1. Re-read `extraction/raw_text/ch04.txt:1933–2068` (§441 in full).
   Confirm there is no Lemma 441B' constraining `bᵢ ≥ 0` or `b₁ > 0`
   that this scoping doc missed.
2. Read `ch04.txt:1569–1730` (§432 boundary locus). Look for a
   sign-definite constraint on `σ'(1)` under stability. **If found,
   Route C becomes viable and this scoping doc should be amended.**
3. Read `ch04.txt:619–700` (§410) once more. Confirm equation (*)
   `Σᵢ i·βᵢ = (1/2)·Σᵢ i²·αᵢ` under order ≥ 2 (Route D).
4. Read `ch04.txt:2465–2502` (§452 transformations). Look for any
   sign constraint on the one-leg `x̄ₙ` offset.

### §7.2 Next 30 minutes (Mathlib hook verification)

1. `lean_local_search "Polynomial.derivative_eval"` — confirm cycle
   347's hooks remain stable.
2. `lean_local_search "Finset.sum_pow_mul"` — search for a
   `Σᵢ i²·βᵢ` family helper.
3. `lean_local_search "Polynomial.eval₂"` — verify Route D's order-
   condition Taylor-coefficient machinery.

### §7.3 Cycle 349 default deliverable (Phase D′.2.0)

Ship the §5 Phase D′.2.0 precursors:

* `bdf2LMM_isConsistent` at `Section451.lean`. ≈10 LOC.
* `sum_β_pos_of_stable_consistent` at `Section422.lean`. ≈10 LOC.
* Optionally, a BDF2 numerical witness `bdf2LMM_sum_β_pos`. ≈5 LOC.

If textbook re-reading confirms Route E is viable, also begin Phase
D′.2.1 Route E refactor (≈100 LOC, may slip to cycle 350).

If textbook re-reading reveals an unexpected route (e.g. §432
boundary-locus constraint), **amend this scoping doc rather than
implementing**, and defer Phase D′.2.1 to cycle 350+.

## §8 Cross-references

* `.prover-state/issues/def_422B_path.md` — parent multi-phase plan
  for `def:422B`.
* `.prover-state/issues/lem_441A_phase_C_scoping.md` — sibling α-side
  scoping template (cycle 180; structural model for this file).
* `.prover-state/issues/lem_441A_alpha_prime_negative.md` — α-side
  Phase B closure (cycles 174–179); template for the per-step
  derivation pattern.
* `.prover-state/issues/cycle_182_gpfs_slowness.md` — Section441
  GPFS-compile blocker (43+ consecutive timeouts since cycle 182).
* `.prover-state/issues/cycle_250_strategy_alpha_definition_error.md`
  — faithfulness precedent on definition smuggling.
* `.prover-state/issues/cycle_336_pivot_options.md` — pivot menu if
  Phase D′ Step 2 stalls.
* `OpenMath/Chapter4/Section410.lean:103` — `βPoly` definition (`Σ
  M.β i · X^i`, leading coefficient `M.β k`).
* `OpenMath/Chapter4/Section410.lean:592` — `ρPoly` definition (`X^k
  − Σ M.α i.succ · X^(k-i-1)`, leading coefficient `+1`).
* `OpenMath/Chapter4/Section422.lean:327` — `Eq422a` predicate.
* `OpenMath/Chapter4/Section422.lean:704` — cycle 344 α-side bridge
  `coef_α_eq_ρPoly_deriv_at_one_of_preconsistent` (template for the
  unsuccessful Route A port).
* `OpenMath/Chapter4/Section422.lean:737` — cycle 344 α-side
  positivity `coef_α_pos_of_stable_preconsistent` (consumed by
  Routes B and E).
* `OpenMath/Chapter4/Section422.lean:793` — cycle 345 conditional
  corollary (the `hβ_nn`-carrying form Phase D′ Step 2 aims to
  unconditionalise).
* `OpenMath/Chapter4/Section422.lean:818` — cycle 345 (404b) form
  `coef_α_eq_sum_β_of_isConsistent` (Routes B and E base lemma).
* `OpenMath/Chapter4/Section422.lean:881` — cycle 346 pointwise
  helper `coef_β_nonneg_of_β_nonneg` (premise version of the Phase
  D′ Step 2 target).
* `OpenMath/Chapter4/Section422.lean:957` — cycle 347 β-side bridge
  `coef_β_eq_βPoly_deriv_at_one`.
* `OpenMath/Chapter4/Section441.lean:767` — α-side template target
  `ρPoly_deriv_eval_one_pos_of_stable_preconsistent` (Route A model
  if leading-coefficient obstruction is resolved — but R2 rules this
  out).
* `OpenMath/Chapter4/Section441.lean:913` — α-side template target
  `aPoly_coeff_one_pos_of_stable_preconsistent` (cycle 179).
* `extraction/raw_text/ch04.txt:145–164` — §403 stability (α-side
  only).
* `extraction/raw_text/ch04.txt:166–236` — §404 consistency
  (404a/404b).
* `extraction/raw_text/ch04.txt:619–700` — §410 order conditions.
* `extraction/raw_text/ch04.txt:1933–2068` — §441 Möbius transform +
  Lemma 441A / 441B / Theorem 441C.
* `extraction/raw_text/ch04.txt:2280–2463` — §451 G-stability.
* `extraction/raw_text/ch04.txt:2465–2502` — §452 one-leg ↔ LMM
  transformation (`coef_β / sum_β` as fractional time offset).

## §9 Cycle 351 update — Phase D′.2.2 Route D Step 1 closed

Cycle 351 shipped the **Phase D′.2.2 Route D Step 1** algebraic
identity in `OpenMath/Chapter4/Section422.lean`:

```lean
theorem coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two
    {k : ℕ} (M : LinearMultistepMethod k)
    (hOrder : M.HasOrderAtLeast 2) :
    (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i)
      = (1 / 2) *
        ∑ i : Fin k, (((i.val + 1 : ℕ) : ℝ))^2 * M.α i.succ
```

Plus the BDF2 order-2 precursor `bdf2LMM_hasOrderAtLeast_two` and
the per-method sanity witness `bdf2LMM_coef_β_eq_half_sum_i_sq_alpha`.

**Derivation**: unfold `C M 2 = C M (1 + 1)` via the `j + 1` branch
of `Section410.C`. The α-sum's `(-(i.val + 1))^2 = (i.val + 1)^2`
(even power) and the β-sum's `(-i.val)^1 = -(i.val)` (odd power)
collapse signs; factorials `1! = 1` and `2! = 2` reduce. Result:
`C M 2 = -(1/2) · Σᵢ (i+1)²·α(i.succ) + Σᵢ i · β i`. Setting this
to zero yields the identity. Both half-sums proved via
`Finset.sum_congr` + `push_cast` + `ring`. The final algebraic
combination closes via `linarith`.

**LOC delta**: Section422.lean: 1204 → ~1320 LOC (+~115 LOC for P1
main + BDF2 precursor + BDF2 witness + docstrings).

**Status of Phase D′.2.2**:

* Step 1 (algebraic identity `coef_β ↔ Σ i²·α`): **CLOSED**.
* Step 2 (`0 ≤ Σᵢ i²·αᵢ` under stability + preconsistency +
  order ≥ 2): **STILL OPEN**. Per the cycle 351 strategy, this
  requires either a `ρ''(1) ≥ 0` argument (second-derivative-of-ρ
  route) or the §441 Möbius infrastructure. Not single-cycle
  attempted in cycle 351 — see strategy §"Cycle 352+ outlook".

**Remaining work for the unconditional Phase D′ corollary**:

After Step 2 closes, the composition produces `coef_β ≥ 0` under
stability + preconsistency + order ≥ 2. Combined with cycle 344's
`coef_α_pos_of_stable_preconsistent`, this yields `coef_α + coef_β >
0` (strict positivity, since `coef_α > 0`), which discharges the
`h_denom_ne` side hypothesis of
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` — the
unconditional cycle 350 surface.

**Faithfulness note (cycle 351)**: the Route D Step 1 lemma
strengthens the textbook §410 / §422 condition `IsConsistent`
(order ≥ 1) to `HasOrderAtLeast 2` (order ≥ 2). This is a
documented hypothesis-strengthening — see the inline docstring
on `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`. The
cycle 350 Route E surface
(`Eq422a_at_vertex_eta_eq_of_stable_consistent`) remains the
cycle 350 weakened-form for callers without order ≥ 2 in hand.

