# Cycle 361 Results

## Worked on

§422 Phase D.3.b ℤ-form lift + general closed form for the
`linearResidualAt` residual at positive integer `i`:

1. **P1 (load-bearing)** — `elementaryWeightQ_phi_zpow_natCast_mk` and
   `elementaryWeightQ_phi_zpow_negSucc_mk`: the ℤ-form analogues of
   cycle 359's ℕ-form `elementaryWeightQ_phi_pow_succ_mk`. These
   express `Φ_{⟦M⟧^n}(t)` as a closed-form expression in cycle 359's
   `M.powRep` canonical representative (positive case) or its inverse
   (negative case via cycle 358's `_inv_mk`).

2. **General closed form** — `linearResidualAt_succ_mk_eq`:
   generalises cycle 360's `linearResidualAt_one_mk_eq` (which handled
   `i = 1` via the special-case `zpow_neg_one` bridge) to **arbitrary
   positive `i = m+1`** via the ℤ-form lift. The closed form exposes
   the residual's structural dependence on `M.powRep (m+1)`'s
   representative data at subtrees of `t`.

Per strategy §C graceful-degradation fallback (P2 strong-induction
parametricity claim deferred): the cycle 361 worker shipped a
**stronger** intermediate result — the general `m + 1` closed form
rather than just `i = 2` — which subsumes the cycle 360 `i = 1`
content and the planned cycle 361 fallback `i = 2` content into a
single uniform lemma. P2 itself (`linearResidualAt_depends_only_on_strict_subtrees`)
is deferred per strategy §C; see "Suggested next approach" below.

## Approach

Per strategy §B.1 / §E Mathlib hook verification:

* **`zpow_natCast`** — confirmed via existing usage in cycle 341's
  `elementaryWeightQ_phi_zpow_vertex` (line 454: `rw [Int.ofNat_eq_natCast, zpow_natCast, ...]`).
* **`zpow_negSucc`** — confirmed via existing usage in cycle 341 (line 458).
* **`-(((m+1) : ℕ) : ℤ) = Int.negSucc m`** by **`rfl`** (definitional)
  — discovered during the `linearResidualAt_two_mk_eq` proof: an
  initial `norm_num` bridge left an unsolved
  `⟦M⟧ ^ 2 = ⟦M⟧ ^ 2` goal (display ambiguity), but a direct `rfl`
  succeeded because `-(Int.ofNat (n+1)) = Int.negSucc n` is the
  defining clause of `Int.neg`. **Save**: see Discovery #1 below.
* **`RKTableau.powRep_quotient_eq`** (cycle 359) — confirmed; takes
  `M m` and returns `⟦M.powRep m⟧ = ⟦M⟧^m`.
* **`elementaryWeightQ_phi_inv_mk`** (cycle 358) — confirmed; applies
  to the `(M.powRep (m+1)).2` representative after `Σ`-eta on the
  Σ-pair.

Then wrote the three theorems in straightforward sorry-first form:

* **`elementaryWeightQ_phi_zpow_natCast_mk`** — 2-line proof:
  `rw [zpow_natCast, ← RKTableau.powRep_quotient_eq M m]; rfl`. The
  `rfl` closes the goal because `elementaryWeightQ_phi ⟦M.powRep m⟧ t
  = (M.powRep m).2.elementaryWeight t` is `Quotient.lift` of the
  underlying `M.elementaryWeight` definition.

* **`elementaryWeightQ_phi_zpow_negSucc_mk`** — 2-line proof: `rw
  [zpow_negSucc, ← RKTableau.powRep_quotient_eq M (m + 1)]; exact
  elementaryWeightQ_phi_inv_mk (M.powRep (m + 1)).2 t`. The
  `_inv_mk` invocation uses Σ-eta on `M.powRep (m+1)` to match the
  `⟦⟨s, M⟩⟧⁻¹` shape expected by cycle 358.

* **`linearResidualAt_succ_mk_eq`** — 6-line proof: `unfold
  linearResidualAt`; `have h_pow : ... ^ (-(((m+1):ℕ):ℤ)) = ... ^
  (Int.negSucc m) := rfl`; `rw [h_pow,
  elementaryWeightQ_phi_zpow_negSucc_mk M m t, elementaryWeightQ_phi_mk]`;
  `push_cast; ring`.

Plus three non-vacuity `example`s:
* `_zpow_natCast_mk` at `m = 0`, `cherry` with `explicitEuler`.
* `_zpow_negSucc_mk` at `m = 0` (= `Int.negSucc 0 = -1`), `cherry`
  with `explicitEuler`.
* `linearResidualAt_succ_mk_eq` at `m = 1` (= `i = 2`), `cherry` with
  `explicitEuler`.
* Plus a cross-check `example` confirming `linearResidualAt 3 _
  vertex = 0` via cycle 360's `linearResidualAt_vertex_eq_zero` (the
  vertex case is independent of `i`).

## Result

**SUCCESS**. All three new public theorems + four non-vacuity
`example`s axiom-clean (`[propext, Classical.choice, Quot.sound]`
only), verified via `#print axioms` after `lake build
OpenMath.Chapter4.Section422` (8037/8037 jobs, exit 0, 354s rebuild).
`lake env lean OpenMath/Chapter4/Section422.lean` exits 0. Sorry
count remains 0 in `Section422.lean`.

§422 streak now **27 consecutive axiom-clean cycles** (336–361).

LOC count: ~135 lines added (theorems + docstrings + non-vacuity).
Within strategy §G budget (80–120 estimated for P1+P2; we shipped
P1 + a stronger generalization of the fallback ladder).

## Faithfulness check

### 1. `elementaryWeightQ_phi_zpow_natCast_mk` (new theorem)

- **Entity ID**: helper for `def:422B` Phase D.3 (no JSON entity).
  Generalises cycle 341 P3 (`elementaryWeightQ_phi_zpow_vertex`) from
  `vertex` to arbitrary `t`, positive-power branch.
- **Lean statement captures**: same content as the ℕ-form lift via
  `M.powRep m`. Bridges `(m : ℤ)` to `m : ℕ` via `zpow_natCast`.
- **Tautology check**: conclusion `Φ_{⟦M⟧^((m:ℤ))}(t) = (M.powRep
  m).2.elementaryWeight t` does NOT appear as hypothesis. ✓
- **Identity check**: proof uses cycle 359's `powRep_quotient_eq`
  (substantive). Not identity.
- **Hypothesis strength**: minimal `(M, m, t)`. ✓

### 2. `elementaryWeightQ_phi_zpow_negSucc_mk` (new theorem)

- **Entity ID**: helper for `def:422B` Phase D.3. Generalises cycle
  341 P3 from `vertex` to arbitrary `t`, negative-power branch.
- **Lean statement captures**: closed form for the negative-power
  elementary weight as the negation of cycle 358's `_inv_mk` bottom-
  block contribution at the `(m+1)`-fold composite.
- **Tautology check**: conclusion does NOT appear as hypothesis. ✓
- **Identity check**: proof composes cycle 358's `_inv_mk` with
  cycle 359's `powRep_quotient_eq` (both substantive). Not identity.
- **Hypothesis strength**: minimal `(M, m, t)`. ✓

### 3. `linearResidualAt_succ_mk_eq` (new theorem)

- **Entity ID**: helper supporting `thm:422A`'s residual structure.
  Textbook source (Butcher §422 p. 359, `extraction/raw_text/ch04.txt:1158`):
  > "The coefficient of η(t) in η⁻ⁱ(t) is equal to i(−1)^r(t) and
  > there are no other terms in η⁻ⁱ(t) with orders greater than
  > r(t) − 1."
- **Lean statement captures**: **substantive closed form** for the
  residual at arbitrary positive `i = m+1` at arbitrary `t`,
  exposing structural dependence on `M.powRep (m+1)`'s representative
  data via `derivativeWeightWithSrc`. Subsumes cycle 360's
  `linearResidualAt_one_mk_eq` (which used a special-case
  `zpow_neg_one` bridge for `i = 1`) into a uniform `i = m + 1`
  closed form.
- **Tautology check**: conclusion is the closed-form equation; does
  NOT appear as hypothesis. ✓
- **Identity check**: proof uses ℤ-form lift `_zpow_negSucc_mk` +
  `elementaryWeightQ_phi_mk` + algebra. Substantive.
- **Hypothesis strength check**: representative-form `M : RKTableau s`
  is necessary because `_zpow_negSucc_mk`'s RHS exposes the
  `M.powRep`-based representative data. Matches the cycle 358/359/360
  representative-form pattern. No textbook deviation.

## Dead ends

* **Initial `norm_num` bridge for `-((2 : ℕ) : ℤ) = Int.negSucc 1` left an unsolved goal:**
  The first attempt at `linearResidualAt_two_mk_eq` (later
  generalised to `_succ_mk_eq`) used `norm_num` to bridge
  `(Quotient.mk ...) ^ (-((2 : ℕ) : ℤ)) = (Quotient.mk ...) ^ (Int.negSucc 1)`.
  This left an unsolved-goals error with `⟦M⟧ ^ 2 = ⟦M⟧ ^ 2`
  (display ambiguity — the integer exponent may have been normalised
  to a form Lean's pretty printer could not distinguish from the
  positive case). **Fix**: replaced with `:= rfl`, which succeeded
  immediately because `-(Int.ofNat (n+1)) = Int.negSucc n` is the
  defining clause of `Int.neg`. **Lesson**: when bridging
  `-(((m+1) : ℕ) : ℤ)` to `Int.negSucc m`, prefer `rfl` over
  `norm_num`. See Discovery #1 (memory candidate).

* **P2 parametricity claim deferred**: the strong-induction proof of
  `linearResidualAt_depends_only_on_strict_subtrees` was assessed as
  too costly within the cycle's budget. The proof requires unfolding
  `linearResidualAt i ⟦M⟧ t` via the ℤ-form lift, then arguing that
  the residual at `t = mk children` is determined by `Φ_η_q` values
  at strict subtrees via the structural recursion through
  `derivativeWeightWithSrc`. The recursive shape of
  `derivativeWeightWithSrc M₂ M₁ i (mk children)` involves
  `M₁.elementaryWeight t'` at children `t'` *and*
  `M₂.derivativeWeightWithSrc M₁ j t'` recursively — but the latter
  exposes `M₂`'s internal A-coefficients, which are NOT bounded by
  the strict-subtree hypothesis (`h_strict` only constrains
  `Φ_η_q(s) = M.elementaryWeight s` at strict subtrees, not arbitrary
  combinations of `M`'s coefficients with subtree elementary weights).
  The proof needs a more delicate inductive structure that
  simultaneously constrains both `Φ_η_q` and per-stage internal
  weights at strict subtrees — multi-cycle work. Deferred per
  strategy §C.

## Discovery

1. **`-(((m+1) : ℕ) : ℤ) = Int.negSucc m` is definitional `rfl`**:
   the cleanest bridge from `-((natural+1) : ℤ)` to `Int.negSucc`. No
   `Nat.cast_ofNat` or `norm_num` needed. Reason: `(Nat.succ m : ℤ) =
   Int.ofNat (Nat.succ m)` and `-Int.ofNat (Nat.succ m) = Int.negSucc
   m` by the defining clause of `Int.neg`. **Save as memory**.

2. **Generalising `_two_mk_eq` to `_succ_mk_eq` was a one-line
   change** — replacing literal `2` with `m + 1` and `Int.negSucc 1`
   with `Int.negSucc m`. The proof structure is identical because
   `_zpow_negSucc_mk` is parametric in `m`. **Lesson for future
   cycles**: when shipping a "closed form at literal `k`" lemma,
   first try the parametric version `_succ_mk_eq` — often it is
   strictly more useful at the same proof cost. Cycle 360's
   `linearResidualAt_one_mk_eq` could be retroactively replaced by
   `linearResidualAt_succ_mk_eq` at `m = 0` (with a small adapter
   for the Σ-eta on `M.powRep 1` vs `M.inverse`).

3. **Strategy §F's faithfulness pre-flight caught a potential
   non-issue**: the strategy's worry about "tautology / definition
   smuggling" was satisfied trivially — all three new theorems have
   substantive RHS expressions distinct from their hypotheses, and
   the `linearResidualAt` definition (cycle 360) is naturally
   pinned by these closed-form theorems rather than smuggled.

4. **Display ambiguity in failing goals after `norm_num`**: when a
   goal contains negative integer exponents like
   `(Quotient.mk ...) ^ (-2 : ℤ)`, Lean's pretty printer may render
   it as `... ^ 2` (dropping the sign visually). Diagnose this by
   checking whether `rfl` closes the goal instead of trusting the
   display. **Save as memory** (or extend the existing
   `feedback_rw_equiv_typed_eq` memory with a display-ambiguity
   note).

## Suggested next approach

Per scoping doc §5 Phase D.3.b/c/d ladder, cycle 361 has now shipped
**P1 (ℤ-form lift)** and the **general `i = m+1` closed form**. The
remaining Phase D.3.b content is:

* **P2 — `linearResidualAt_depends_only_on_strict_subtrees`**: the
  strong-induction parametricity claim. Given cycle 361's deferral,
  this is the natural cycle 362 deliverable.

The proof strategy noted in strategy §B.2 still applies, but the
inductive step needs more care than the strategy anticipated. The
cleanest approach may be:

1. First ship a per-`derivativeWeightWithSrc` substitution lemma:
   "if `M₁` and `M₁'` agree on elementary weights at all strict
   subtrees of `t`, then `derivativeWeightWithSrc M₂ M₁ i t' =
   derivativeWeightWithSrc M₂ M₁' i t'` for all `t' ∈ children t`".
   This is structural induction on the tree, and the strict-subtree
   constraint is naturally satisfied because the recursion only
   touches `M₁.elementaryWeight` at subtrees.

2. Then `linearResidualAt_depends_only_on_strict_subtrees` follows
   by `Quotient.inductionOn₂` + the ℤ-form lift + the per-
   `derivativeWeightWithSrc` substitution lemma + the IH at strict
   subtrees.

This decomposition may be feasible within a single cycle (the per-
`derivativeWeightWithSrc` substitution lemma is mechanical
structural-recursion). Recommend cycle 362 attempts this with the
fallback being "ship just the substitution lemma + scoping note".

**Alternative cycle 362 deliverable**: Phase D.3.c
`sum_i_alpha_ne_zero_of_stable` (per scoping doc §5). This does not
depend on Phase D.3.b's parametricity claim and could be tackled in
parallel. Requires Mathlib's polynomial-root-multiplicity API
(see scoping doc §5).

**Strategic context**: §422 streak now 27 consecutive axiom-clean
cycles. Phase E sealing of `def:422B` projected ~4 cycles away
(cycle 362 P2 → cycle 363 D.3.c → cycle 364 D.3.d → cycle 365 Phase
E sealing — pushed one cycle out from the cycle 360 estimate due to
P2 deferral). No pivot temptation — the ladder rhythm remains
productive.
