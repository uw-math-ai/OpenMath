# Cycle 181 Results

## Worked on

Phase C.1 of `lem:441A` (Butcher §441 p. 376) — the Möbius algebraic
bridge between `aPoly` and `αPoly`. Per the cycle 181 strategy this
was the main deliverable; Phase B was closed in cycle 179. Priority
0 git verification confirmed the cycle 180 commit is at the branch
tip and Section441.lean is at 977 LOC, 0 sorries, axiom-clean.

## Approach

1. **Priority 0 verification** (5 min) — confirmed the cycle 180
   commit, Phase B landmarks, and BDF2 closed form are all present.
   No phantom-verdict regression on this cycle.

2. **Bridge target analysis** (10 min) — inspected
   `Section410.αPoly = 1 − Σᵢ αᵢ X^(i+1)` and `Section410.ρPoly =
   X^k − Σᵢ αᵢ X^(k−(i+1))`. The textbook substitution
   `a(z) = (1+z)^k · α(ψ(z))` with `ψ(z) = (1−z)/(1+z)` and
   `α(w) = 1 − Σᵢ αᵢ w^i` matches our `αPoly` directly (no
   reflection needed). Selected `αPoly` as the bridge target.

3. **Definition** — chose a parameterised
   `mobiusTransform (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ`
   instead of the strategy's `p.natDegree`-based version, because
   `αPoly.natDegree` can drop below `k` when `αₖ = 0` (Adams-style
   methods), which would break the simple `aPoly = mobiusTransform
   αPoly` equality. The parameterised form `aPoly = mobiusTransform
   k αPoly` holds unconditionally. Strategy explicitly allowed this
   ("build a thin wrapper if neither matches exactly").

4. **Algebraic bridge** — used the cycle 180 `Polynomial.funext`
   recipe. Helper lemmas:
   * `αPoly_coeff_zero : (αPoly M).coeff 0 = 1`
   * `αPoly_coeff_succ : (αPoly M).coeff (j.val + 1) = -M.α j.succ`
     (for `j : Fin k`)

   Main proof: `Polynomial.funext` → `Finset.sum_range_succ'` (peel
   off `i = 0`) → substitute coefficients → `Fin.sum_univ_eq_sum_range`
   reindex → `ring`.

5. **Multiplicative bridge** (Step 3a) — `aPoly_aeval_eq_mul_αPoly_aeval`
   for `ζ : ℂ` with `1 + ζ ≠ 0`:
   `aPoly.aeval ζ = (1 + ζ)^k · αPoly.aeval ((1 − ζ) / (1 + ζ))`.
   Proof: rewrite via `aPoly_eq_mobiusTransform_αPoly`, expand
   `mobiusTransform` summands using `eval₂_*` lemmas, factor
   `(1 + ζ)^k = (1 + ζ)^i · (1 + ζ)^(k−i)`, close with `field_simp`.

6. **Complex root bridge** (Step 3b) —
   `aPoly_aeval_eq_zero_iff_αPoly_aeval_at_mobiusArg` for `ζ ≠ −1`.
   Direct corollary: `mul_eq_zero` + `pow_ne_zero`.

7. **BDF2 witnesses** (Step 4) —
   * `bdf2LMM_aPoly_eq_mobiusTransform` (one-liner specialisation).
   * `bdf2LMM_mobiusTransform_αPoly_eq` — composes with cycle 180's
     `bdf2LMM_aPoly_eq` to give the closed form
     `mobiusTransform 2 (αPoly bdf2LMM) = C(4/3) X + C(8/3) X²`.

## Result

SUCCESS — Phase C.1 closed in full (Priority 1 stretch + Step 4):

* `mobiusTransform` definition shipped (axiom-clean).
* `aPoly_eq_mobiusTransform_αPoly` proved (axiom-clean).
* `aPoly_aeval_eq_mul_αPoly_aeval` proved (axiom-clean).
* `aPoly_aeval_eq_zero_iff_αPoly_aeval_at_mobiusArg` proved (axiom-clean).
* Two BDF2 sanity witnesses shipped.
* +250 LOC to `Section441.lean`. New total: 1227 LOC, 0 sorries.

`#print axioms` on each new declaration returns only
`[propext, Classical.choice, Quot.sound]`.

Priority 2 (cycle 174 typo docstring) NOT shipped — the existing
cycle 175 note at lines 447–454 of `Section441.lean` already
documents the Butcher §441 p. 376 typo with numerical witnesses on
explicit Euler and BDF2; the strategy's proposed addition would
duplicate this content. Skipped without prejudice.

The optional `ζ = −1` boundary case (degree-drop in αPoly) was NOT
shipped. Strategy listed it as optional; recommended deferring to
Phase C.2 where it pairs naturally with the `αₖ = 0` analysis
under stability.

## Faithfulness check

For each new `def` or `theorem`:

### `mobiusTransform`

Entity: not a textbook entity (helper definition for §441).

Textbook source: Butcher §441 p. 376, the formula
`a(z) = (1+z)^k − Σᵢ αᵢ (1+z)^(k−i) (1−z)^i` and the substitution
`α(w) = 1 − Σᵢ αᵢ w^i` with `w = ψ(z) = (1−z)/(1+z)`.

> "We have `a(z) = (1+z)^k · α((1−z)/(1+z))` ... This is a
> *Möbius transform* substitution; the homogenised polynomial
> `Σᵢ αᵢ' · (1−z)^i · (1+z)^(n−i)` (where `αᵢ'` are α's coefficients
> and `n` is a fixed total degree) clears the `(1+z)` denominator."

Lean statement captures: same content. The parameterised form
`mobiusTransform n p = Σᵢ₌₀ⁿ p.coeff i · (1−X)^i · (1+X)^(n−i)`
homogenises at total degree `n` (independent of `p.natDegree`),
matching the standard projective interpretation of the substitution.

No definition smuggling — the named concept is "homogenised Möbius
transform of a polynomial at total degree n", and the Lean encoding
is the standard formula.

### `αPoly_coeff_zero` / `αPoly_coeff_succ` (private helpers)

Entity: not textbook entities.

These are direct coefficient computations on the §410 αPoly
definition. They unfold the definition and use standard
`Polynomial.coeff_*` lemmas. No mathematical content beyond what's
already encoded in `Section410.αPoly`.

### `aPoly_eq_mobiusTransform_αPoly`

Entity: `lem:441A` (sub-step toward the full closure).

Textbook statement (Butcher §441 p. 376):
> "We have `a(z) = (1+z)^k · α((1−z)/(1+z))`, where `α(w) = 1 −
> α₁w − ⋯ − αₖw^k`."

Lean statement captures: same content, in homogenised polynomial form
`M.aPoly = mobiusTransform k (Section410.αPoly M)`. The
homogenisation is the polynomial-algebra encoding of the textbook's
rational-function identity. Equivalent — no division, no implicit
hypotheses on `1 + z ≠ 0` (because the identity holds in `ℝ[X]`
without any pointwise condition).

Tautology / identity / smuggling / strength checks: all pass.
Conclusion is not a hypothesis (LMM is the only hypothesis). Proof
is a substantive ~50-line algebraic identity, not `exact h`.
Hypothesis is the minimal `(M : LinearMultistepMethod k)` — no
extra strength.

### `aPoly_aeval_eq_mul_αPoly_aeval`

Entity: `lem:441A` (sub-step).

Textbook statement: same Butcher §441 p. 376 identity, evaluated at
a complex argument `ζ` with `1 + ζ ≠ 0` (so that `ψ(ζ)` is defined).

Lean statement: `aPoly.aeval ζ = (1 + ζ)^k · αPoly.aeval ((1−ζ)/(1+ζ))`
under hypothesis `1 + ζ ≠ 0`. Same content as the textbook
substitution, with the explicit hypothesis Butcher implicitly
assumes (but does not write down).

No tautology / identity / smuggling. Proof routes through
`aPoly_eq_mobiusTransform_αPoly` + `eval₂` algebra + `field_simp`;
~25 lines of substantive work.

### `aPoly_aeval_eq_zero_iff_αPoly_aeval_at_mobiusArg`

Entity: `lem:441A` (sub-step).

Textbook source: Butcher §441 p. 376 reads "`ζ` is a root of `a`
iff `(1−ζ)/(1+ζ)` is a root of `α`" (modulo the boundary `ζ = −1`).

Lean statement: same content for `ζ ≠ −1`. Boundary case `ζ = −1`
(corresponding to a degree drop `αₖ = 0`) deferred to Phase C.2.

Hypothesis `ζ ≠ −1` matches the textbook implicit constraint (the
substitution `(1−ζ)/(1+ζ)` is undefined at `ζ = −1`).

No tautology / smuggling. Proof is `mul_eq_zero` + `pow_ne_zero`
disposal.

### BDF2 witnesses (`bdf2LMM_aPoly_eq_mobiusTransform`,
### `bdf2LMM_mobiusTransform_αPoly_eq`)

Numerical instances of the bridge on the canonical BDF2 LMM. No
faithfulness question — they specialise the generic theorems to a
concrete witness.

## Dead ends

None for cycle 181. The proofs went through on first attempt with
the cycle 180 `Polynomial.funext` recipe (algebraic bridge) and
the standard `eval₂` + `field_simp` recipe (multiplicative bridge).

One minor friction: the initial `field_simp + ring` step in
`aPoly_aeval_eq_mul_αPoly_aeval` left a `No goals to be solved`
error on the trailing `ring`, because `field_simp` already closed
the goal. Fixed by removing the redundant `ring`.

## Discovery

* **Parameterised `mobiusTransform`**: the textbook substitution is
  natural to encode as `mobiusTransform (n : ℕ) (p : Polynomial ℝ)`
  taking an explicit total degree, NOT `p.natDegree`-based. The
  reason is that `αPoly.natDegree ≤ k` (cycle 073) but can be `< k`
  when `αₖ = 0`; the bridge `aPoly = mobiusTransform k αPoly`
  requires the LHS total degree `k` to be invariant. Future
  Möbius-style identities should use the same parameterised form.

* **`Polynomial.funext` + `Finset.sum_range_succ'` + `Fin.sum_univ_eq_sum_range`**
  is a clean recipe for bridging `Fin k` sums (used by `aPoly`) to
  `range (k+1)` sums (used by `mobiusTransform`). Reusable for any
  future identity that crosses these two indexing conventions.

* **`eval₂` + `field_simp`** is the right recipe for transferring
  polynomial-level identities to evaluations at a complex argument
  with a non-vanishing denominator. The `aeval_def` rewrite to
  `eval₂` avoids the `•`-vs.-`*` scalar friction.

* **Cycle 175's typo note already covers Priority 2.** No need to
  revisit; the existing acknowledgement at Section441.lean:447–454
  is sufficient.

## Suggested next approach

Cycle 182 should attempt **Phase C.2** (stability ⇒ `aPoly` roots
in closed left half-plane). Specifically:

1. **`ρPoly_root_abs_le_one_of_stable`**: extract the cycle 175
   "complex roots of ρ are inside the closed unit disk under
   stability" private helper to a public lemma. Stability already
   gives this for ρ; the bridge then transfers to αPoly via the
   fact that ρ and α are related by a polynomial reflection
   `αPoly z = z^k · ρPoly (1/z)` (or similar — verify the exact
   form first).

2. **`αPoly_aroot_abs_le_one_of_stable`**: roots of α (over ℂ)
   are inside the closed unit disk under stability.

3. **`aPoly_aroot_re_nonpos_of_stable`**: combine Phase C.1's
   `aPoly_aeval_eq_zero_iff_αPoly_aeval_at_mobiusArg` with
   step 2 + the standard fact that `ψ` (the inverse Möbius)
   maps the closed unit disk minus `{−1}` to the closed left
   half-plane.

4. **`ζ = −1` boundary case**: handle `aPoly.aeval (−1) = 0 ↔
   αₖ = 0 ↔ αPoly.degree < k`. The `αₖ = 0` degenerate case
   under stability is also where a separate analysis applies.

LOC budget for Phase C.2: ~80–100 LOC.

Phase C.3 (real factorisation) is the high-risk phase — a generic
"polynomial with all roots in closed left half plane factors into
linear and quadratic factors with non-negative coefficients"
lemma. Defer to cycle 183+.

The cycle 181 deliverable bar (target + stretch) was met without
needing Aristotle. Phase C.2 should be similarly tractable
manually, but if the `ρ ↔ α` reflection bridge is missing in
Section410, that may need Aristotle support.
