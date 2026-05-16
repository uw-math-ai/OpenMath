# Cycle 305 Strategy — `lem:342B` Phase B.2 (Weight Positivity)

## Context

**Cycle 304 shipped Phase B.1 cleanly** (headline 2n-degree exactness
`butcherShiftedLegendre_quadrature_exact_lt_two_n` + P2 consistency
witness `butcherShiftedLegendre_quadratureWeights_sum_eq_one`,
+~130 LOC, axiom-clean, 0 sorries). File now 6418 LOC. No Aristotle
results pending. No blockers reported.

**`lem:342B` roadmap**: Phase A.1 (cycle 301, zero finset) → A.2 (cycle
302, canonical enumeration) → A.2.b (cycle 303, Lagrange weights + <n
exactness) → **B.1 (cycle 304, 2n-degree exactness) ← DONE** → **B.2
(THIS CYCLE, positivity `0 < bⱼ`)** → B.3 (cycle 306, uniqueness).
After B.3 lands, `lem:342B` row flips to `formalized`.

## This cycle: Phase B.2 — positivity of quadrature weights

### Target

```lean
theorem butcherShiftedLegendre_quadratureWeights_pos (n : ℕ) (hn : 0 < n)
    (j : Fin n) :
    0 < butcherShiftedLegendre_quadratureWeights n j
```

i.e. each Gaussian quadrature weight `bⱼ` is strictly positive. This
is the "positive numbers b₁, …, bₛ" clause of Butcher's `lem:342B`
statement (§342 p. 237).

### Approach — verbatim execution of Butcher's textbook recipe

Butcher (p. 237):

> To prove the bᵢ are positive, let φ(x) denote the square of the
> polynomial formed by dividing Pₛ*(x) by x − cᵢ. Substitute into
> (342h), and the result follows.

Concretely, the proof breaks into 5 steps. Ship each as a `private`
auxiliary lemma where useful; only the headline
`butcherShiftedLegendre_quadratureWeights_pos` needs to be public.

#### Step 1: define the test polynomial `φⱼ`

Define
```lean
private noncomputable def butcherShiftedLegendre_lagrangeFactor
    (n : ℕ) (hn : 0 < n) (j : Fin n) : Polynomial ℝ :=
  butcherShiftedLegendre n /ₘ (Polynomial.X - Polynomial.C
    (butcherShiftedLegendre_zeros n hn j))
```

(Polynomial division by the monic `X - C cⱼ`; use Mathlib's
`Polynomial.divByMonic` — verify name with `lean_local_search "divByMonic"`
or `lean_loogle "Polynomial./ₘ"`.)

Then define
```lean
private noncomputable def butcherShiftedLegendre_lagrangeFactorSq
    (n : ℕ) (hn : 0 < n) (j : Fin n) : Polynomial ℝ :=
  (butcherShiftedLegendre_lagrangeFactor n hn j) ^ 2
```

This is the textbook φⱼ — a non-negative-valued polynomial of degree
`2(n - 1) < 2n`.

#### Step 2: degree bound

```lean
private lemma butcherShiftedLegendre_lagrangeFactorSq_natDegree_lt
    (n : ℕ) (hn : 0 < n) (j : Fin n) :
    (butcherShiftedLegendre_lagrangeFactorSq n hn j).natDegree < 2 * n
```

Proof: `lagrangeFactor.natDegree ≤ n - 1` since `(X - C cⱼ)` is monic
of degree 1 and `Pₙ*.natDegree = n` (cycle 273's
`butcherShiftedLegendre_natDegree`). Use
`Polynomial.natDegree_divByMonic` (verify name). Then square doubles:
`(p^2).natDegree ≤ 2 · p.natDegree` via `Polynomial.natDegree_pow_le`
or compute directly. Combine with `n ≥ 1 ⇒ 2(n - 1) < 2n` via `omega`.

#### Step 3: φⱼ(cₖ) = 0 for k ≠ j (Lagrange-style vanishing)

```lean
private lemma butcherShiftedLegendre_lagrangeFactor_eval_zeros_ne
    (n : ℕ) (hn : 0 < n) (j k : Fin n) (hjk : k ≠ j) :
    (butcherShiftedLegendre_lagrangeFactor n hn j).eval
      (butcherShiftedLegendre_zeros n hn k) = 0
```

Proof: `lagrangeFactor n j · (X - C cⱼ) = Pₙ*` (the
`divByMonic` identity — Mathlib's `Polynomial.modByMonic_add_div` or
`Polynomial.divByMonic_eq_iff` flavour; verify via
`lean_local_search "divByMonic"`). Evaluate both sides at `cₖ`. The
RHS is `Pₙ*(cₖ) = 0` by cycle 302's `butcherShiftedLegendre_zeros_isRoot`.
The factor `(cₖ - cⱼ) ≠ 0` by cycle 302's
`butcherShiftedLegendre_zeros_injective` applied to `hjk`. Conclude
the other factor is 0.

Corollary (immediate):
```lean
private lemma butcherShiftedLegendre_lagrangeFactorSq_eval_zeros_ne
    (n : ℕ) (hn : 0 < n) (j k : Fin n) (hjk : k ≠ j) :
    (butcherShiftedLegendre_lagrangeFactorSq n hn j).eval
      (butcherShiftedLegendre_zeros n hn k) = 0
```

via `Polynomial.eval_pow` and `0^2 = 0`.

#### Step 4: φⱼ(cⱼ) > 0 (the load-bearing step)

```lean
private lemma butcherShiftedLegendre_lagrangeFactorSq_eval_self_pos
    (n : ℕ) (hn : 0 < n) (j : Fin n) :
    0 < (butcherShiftedLegendre_lagrangeFactorSq n hn j).eval
      (butcherShiftedLegendre_zeros n hn j)
```

Routes through proving `(lagrangeFactor n j).eval cⱼ ≠ 0`, then
squaring via `sq_pos_of_ne_zero` (or `pow_two_pos_of_ne_zero`; verify
the right name).

To show `(lagrangeFactor n j).eval cⱼ ≠ 0`: by the `divByMonic`
identity `(X - C cⱼ) * lagrangeFactor n j = Pₙ*` (re-orient as
needed), differentiate both sides. Product rule gives
`Pₙ*'(x) = lagrangeFactor n j (x) + (x - cⱼ) · (lagrangeFactor n j)'(x)`.
Evaluate at `cⱼ`: `Pₙ*'(cⱼ) = lagrangeFactor n j (cⱼ)`. So it suffices
to show `Pₙ*'(cⱼ) ≠ 0`.

The fact that `cⱼ` is a *simple* root of `Pₙ*` (hence `Pₙ*'(cⱼ) ≠ 0`)
follows from cycle 301's distinct-roots result: `Pₙ*` has `n` distinct
real zeros (the canonical `butcherShiftedLegendre_zeros`), and `Pₙ*`
has degree `n`, so each root has multiplicity exactly 1.

**Mathlib hooks to verify**:
- `Polynomial.derivative_eval_root_simple` or
  `Polynomial.eval_derivative_ne_zero_of_isRoot_of_rootMultiplicity_one`
  (one of these should give `Pₙ*'(cⱼ) ≠ 0` from simple-root
  hypothesis; verify with `lean_local_search "rootMultiplicity"` and
  `lean_local_search "derivative_root"`).
- An alternative cleaner route: search for an `eval_divByMonic` hook
  that directly gives the evaluation of `Pₙ* /ₘ (X - C cⱼ)` at `cⱼ`
  in closed form (possibly as `Pₙ*.derivative.eval cⱼ` already).
  **Verify this hook exists before committing to the longer proof.**

If neither hook is available, fall back to showing `Pₙ*` has rootMultiplicity 1
at each cⱼ via cycle 301's `butcherShiftedLegendre_n_distinct_real_zeros`
together with `Polynomial.card_roots_le_natDegree` + the n-distinct-zeros
bound forcing all multiplicities to be exactly 1.

#### Step 5: integral positivity + headline closure

```lean
private lemma butcherShiftedLegendre_lagrangeFactorSq_integral_pos
    (n : ℕ) (hn : 0 < n) (j : Fin n) :
    0 < ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre_lagrangeFactorSq n hn j).eval x
```

Proof: the integrand is non-negative everywhere (it's a square) and
strictly positive at `cⱼ ∈ (0, 1)` (Step 4 + the `_mem_Ioo` cycle 302
lemma). Continuity (polynomial) + a non-vanishing point in the open
interval forces the integral to be positive.

**Mathlib hooks**:
- `intervalIntegral.integral_pos` (verify name) — likely the right
  shape: continuous, non-negative on the interval, positive at one
  interior point.
- Or `MeasureTheory.integral_pos_iff_support_of_nonneg_ae` for the
  measure-theoretic version, then bridge to interval integral.

**Headline closure**:

Apply Phase B.1's `butcherShiftedLegendre_quadrature_exact_lt_two_n n
hn (butcherShiftedLegendre_lagrangeFactorSq n hn j) hdeg` (with `hdeg`
from Step 2):
```
∫₀¹ φⱼ(x) dx = ∑ₖ bₖ · φⱼ(cₖ).
```

Split the RHS sum: use `Finset.sum_eq_single j` to isolate the `k = j`
term (the others vanish by Step 3's corollary). RHS reduces to
`bⱼ · φⱼ(cⱼ)`. So `bⱼ · φⱼ(cⱼ) = ∫₀¹ φⱼ dx > 0` (Step 5). Combined
with `φⱼ(cⱼ) > 0` (Step 4) and the elementary `a · b > 0 ∧ b > 0 ⇒ a > 0`
(e.g. `pos_of_mul_pos_left` or `lt_div_iff` reorder; verify),
conclude `bⱼ > 0`.

### Estimated scope

~150–200 LOC across 5–6 private auxiliaries plus the headline.
Mathlib hook verification is the main risk — budget 15 minutes
upfront with `lean_local_search` / `lean_loogle` for:

1. `Polynomial.divByMonic` API: `natDegree_divByMonic`,
   the canonical identity `(X - C r) * (p /ₘ (X - C r)) = p` when
   `(X - C r) ∣ p`, etc.
2. Simple-root derivative non-vanishing: search for
   `derivative.*root.*simple`, `rootMultiplicity.*one`,
   `eval_derivative_ne_zero`.
3. `intervalIntegral.integral_pos` with non-negativity + interior
   positivity hypotheses.
4. `pow_pos`, `sq_pos_of_ne_zero`, or `pow_two_pos_of_ne_zero` for
   `x ≠ 0 ⇒ 0 < x^2`.

### Aristotle directive: DO NOT submit

Phase B.2's recipe is concrete and the Mathlib hooks are well-
established (`Polynomial.divByMonic` plumbing has been in Mathlib
for years). Manual closure is faster than a poll cycle. Save the
Aristotle slot.

## What NOT to try

- **DO NOT** redefine `butcherShiftedLegendre_quadratureWeights` — the
  cycle 303 Lagrange-basis definition is correct and the textbook
  Phase B.1 proof routes through it.
- **DO NOT** attempt to prove positivity by a *direct* argument on
  the Lagrange weight formula `bⱼ = ∫₀¹ Lⱼ(x) dx`. The Lagrange basis
  polynomial `Lⱼ` changes sign on `(0, 1)` (it equals 1 at `cⱼ` and
  0 at the other `cₖ`s, so it must oscillate), so its integral has
  no obvious sign. Butcher's φⱼ-square trick is the canonical recipe;
  don't deviate.
- **DO NOT** use `rw [intervalIntegral.integral_add ...]` style for
  the polynomial unfolding — per cycle 304's discovery, prefer `calc`
  blocks with each step's conclusion type pinned, so Lean's HO
  unification doesn't blow up on the integrand.
- **DO NOT** raise `maxHeartbeats` above 200000 — decompose the
  step-4 derivative argument if needed.
- **DO NOT** introduce `axiom` / `constant` declarations.
- **DO NOT** ship Phase B.2 with sorries. If any step stalls past 60
  minutes of focused work, file an issue at
  `.prover-state/issues/lem_342B_phase_B2_stall.md` documenting the
  specific Mathlib hook gap and ship the closed sub-steps separately
  (Step 1 + 2 + 3 are mechanical; Step 4 is the only real risk).
- **DO NOT** preemptively extract to `Section342Quadrature.lean`.
  Per strategy §F of cycle 304's task results, evaluate extraction
  only after B.2 + B.3 ship AND if compile time exceeds 90s. File
  is 6418 LOC now; estimated ~6600 LOC after Phase B.2 — still
  manageable.

## Faithfulness check requirement

Before commit, verify:
- `butcherShiftedLegendre_quadratureWeights_pos`'s statement matches
  Butcher's "there exist positive numbers b₁, …, bₛ" clause of
  `lem:342B` verbatim (positivity of each `bⱼ`, not just non-negativity).
- No hypothesis stronger than `0 < n` is introduced (the textbook only
  requires `s ≥ 1`, matching our `hn : 0 < n`).
- The `φⱼ`-square test polynomial is genuinely the textbook φ from
  Butcher p. 237 (the square of `Pₙ*(x) / (x - cⱼ)`, not some
  variant).
- The auxiliary lemmas don't smuggle in conclusions as hypotheses
  (e.g. Step 4's `(lagrangeFactor n j).eval cⱼ ≠ 0` must be proved
  from cycle 301's distinct-roots fact + the derivative argument,
  NOT taken as a hypothesis).

## Build commands

```bash
lake env lean OpenMath/Chapter3/Section342.lean    # primary verification
```

The aggregator `OpenMath/Chapter3.lean` should also build, but is
slower; run only after `Section342.lean` passes.

## Verify axiom-cleanness

```lean
#print axioms butcherShiftedLegendre_quadratureWeights_pos
-- Expected: [propext, Classical.choice, Quot.sound]
```

If any other axiom appears (especially `sorryAx`), the proof is
incomplete — do not commit.

## Stretch (only if Phase B.2 closes in ≤ 60 min)

**Phase B.3** — uniqueness of weights (~50 LOC):

```lean
theorem butcherShiftedLegendre_quadratureWeights_unique (n : ℕ) (hn : 0 < n)
    (b : Fin n → ℝ)
    (hb : ∀ φ : Polynomial ℝ, φ.natDegree < n →
       ∫ x in (0 : ℝ)..1, φ.eval x = ∑ j, b j * φ.eval (butcherShiftedLegendre_zeros n hn j)) :
    b = butcherShiftedLegendre_quadratureWeights n
```

Proof: apply `hb` to each Lagrange basis polynomial `Lⱼ`
(`Polynomial.Lagrange.basis (Finset.univ : Finset (Fin n))
(butcherShiftedLegendre_zeros n hn) j`). The Kronecker-delta property
`Lⱼ(cₖ) = δⱼₖ` (Mathlib's `Lagrange.basis_eq_one_iff` or similar; this
is what cycle 303 used) collapses the sum to `b j`. The LHS is exactly
the definition of `butcherShiftedLegendre_quadratureWeights n j`. So
`b j = quadratureWeights n j` for all `j`, hence `b = quadratureWeights`
by `funext`.

If B.3 lands, **`lem:342B` is fully formalized** — flip
`lean_status.json` row from `partial` to `formalized`, update plan.md
to `[x]`, and the lem:342B work is done. After B.3, the next entity
target (per plan.md Ch.3 ordering) would be `cor:342D` (Gaussian
quadrature Runge-Kutta order condition) or one of the §351 stability
entities.

If B.3 doesn't fit, save for cycle 306 with no harm done; B.2 alone
is a substantive ship.

## Cycle 305 checklist

Before commit:
1. `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
2. `grep -c sorry OpenMath/Chapter3/Section342.lean` returns 0.
3. `#print axioms butcherShiftedLegendre_quadratureWeights_pos` shows
   only `[propext, Classical.choice, Quot.sound]`.
4. Pre-commit faithfulness check (per CLAUDE.md) passes — quoted
   textbook statement, Lean type match, no definition smuggling, no
   tautology, no hypothesis strengthening.
5. Task results written to `.prover-state/task_results/cycle_305.md`
   per the CLAUDE.md template.
6. `plan.md` lem:342B row updated to reflect Phase B.2 closure (still
   `[~]` partial unless B.3 also lands).
7. `extraction/formalization_data/lean_status.json` cycle reference
   bumped on the `lem:342B` row.
