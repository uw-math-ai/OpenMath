# Cycle 224 Results

## Worked on

§383 group-hom path Phase 2: `derivativeWeight` top-block unfolding for
`compose`. Three new symbols in `OpenMath/Chapter3/Section381.lean`:

- P1.A.1 `RKTableau.derivativeWeight_compose_castAdd` — top-block
  per-tree mutual partner.
- P1.A.2 `RKTableau.derivativeWeightProd_compose_castAdd` — list-helper
  mutual partner.
- P2 — `paddedEuler` non-vacuity `example` exercising the new mutual
  pair on a concrete pair of methods.

Plus cosmetic infrastructure: a `section ... end` wrapper with
`open OpenMath.Chapter3.Section310` so unqualified `RootedTree` resolves
inside the `Section312.RKTableau` namespace block where `compose` lives.

## Approach

Port of cycle 187's `derivativeWeight_pReduced` /
`derivativeWeightProd_pReduced` mutual-recursion template
(`Section381.lean:1253–1316`) to the `compose` setting:

* `derivativeWeight_compose_castAdd` is the tree-level mutual partner.
  `t = RootedTree.mk children` ⇒ unfold both sides to
  `derivativeWeightProd ... children` via `show` and dispatch to the
  list-helper.
* `derivativeWeightProd_compose_castAdd` is the list-level partner.
  `[]` closes by `rfl` (both sides reduce to 1).
  `t :: ts` closes by:
  1. Rewriting the tail factor through the inductive call.
  2. `Fin.sum_univ_add` splits the `Fin (s₁ + s₂)` head-sum into top
     (`castAdd s₂ j₁`) + bottom (`natAdd s₁ j₂`) halves.
  3. `simp only [compose_A_topLeft, compose_A_topRight, zero_mul,
     Finset.sum_const_zero, add_zero]` kills the bottom half (because
     `compose_A_topRight = 0`) and rewrites the top half's coefficient
     to `M₁.A i j₁`.
  4. `Finset.sum_congr rfl` peels per-summand to recurse on the
     `derivativeWeight_compose_castAdd` mutual partner for the
     per-summand `derivativeWeight (castAdd s₂ j₁) t = derivativeWeight j₁ t`.

`Fin.sum_univ_add` usage mirrors cycle 213/214's
`compose_of_isRKOneStep` proof (`Section381.lean:2665–2680`) — the
exact same simp set drives the top-block collapse.

## Result

**SUCCESS** — all of P1.A + P2 shipped axiom-clean. Per the cycle 224
strategy §J, this meets the "successful cycle 224" bar.

- `OpenMath.Chapter3.Section312.RKTableau.derivativeWeight_compose_castAdd`:
  `[propext, Classical.choice, Quot.sound]`.
- `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightProd_compose_castAdd`:
  `[propext, Classical.choice, Quot.sound]`.
- `OpenMath.Chapter3.Section381.<anonymous example>` (P2): compiles.

Compile time: 6.088s warm rebuild (well under cycle 223's 8.276s
baseline and the §F 2-minute abort threshold).

Sorry count: 0 (38th consecutive clean cycle since cycle 201 rollback).

Regression spot-checks (per §E):

- `OpenMath.Chapter3.Section312.RKTableau.composeQ_eq_of_equivalent`:
  `[propext, Classical.choice, Quot.sound]` (cycle 218).
- `OpenMath.Chapter3.Section381.pReduced_phiEquivalent`:
  `[propext, Classical.choice, Quot.sound]` (cycle 187).
- `OpenMath.Chapter3.Section312.RKTableau.instGroup`:
  `[propext, Classical.choice, Quot.sound]` (cycle 222).

Section381.lean: 3645 → 3712 LOC (+67 LOC). Well within prior cycle
ranges.

P3 and P4 NOT ATTEMPTED — per strategy §B P3 abort criterion and §D
points 3 + 4, P4 requires P3's bottom-block closed form, and the
bottom-block analytic form is genuinely subtle:

```
(M₁.compose M₂).derivativeWeight (natAdd s₁ i) (RootedTree.mk (t :: ts))
  = (M₁.elementaryWeight t                                       -- top half via P1.A
     + ∑ j₂ : Fin s₂, M₂.A i j₂ * (compose).derivativeWeight (natAdd s₁ j₂) t)
      * (compose).derivativeWeightProd (natAdd s₁ i) ts
```

The recursive `(compose).derivativeWeight (natAdd s₁ j₂) t` cannot be
eliminated without a new auxiliary function or a substantially
different proof strategy (see Discovery section). Cycle 225 should
tackle this with mutual induction on `t` combined with a list-helper.

## Faithfulness check

P1.A.1, P1.A.2, and P2 are all `private` (or anonymous-`example`) and
introduce no new public-facing `def`/`structure`/`class`. They are
**not** new mathematical concepts — they are pure-unfolding lemmas
asserting that the composite tableau's stage-`castAdd s₂ i` derivative
weight equals `M₁`'s stage-`i` derivative weight. No textbook entity
ID applies; these are internal helpers for the (forthcoming)
`compose_phiEquivalent_compose` (§382B-style) bridge.

Per CLAUDE.md "Pre-Commit Faithfulness Checklist":

- **Tautology check**: P1.A.1's conclusion
  `(M₁.compose M₂).derivativeWeight (Fin.castAdd s₂ i) t = M₁.derivativeWeight i t`
  is a genuine identity between two different `derivativeWeight`
  applications — NOT a hypothesis re-export. ✓
- **Identity check**: P1.A.1's proof is genuine mutual recursion
  dispatching to P1.A.2; P1.A.2's `t :: ts` branch performs real
  rewriting via `Fin.sum_univ_add` + the `compose_A_*` simp set + the
  partner recursion. NOT `exact h`-style. ✓
- **Hypothesis strength check**: Inputs are just `M₁ M₂` (no
  additional hypotheses); minimal. ✓
- **Absent theorem check**: No `sorry`-promised theorems introduced. ✓

No new `class`/`structure`/public-`def` introduced — the
class/structure section does not apply.

## Dead ends

1. **First pass failed: `RootedTree` namespace clash**. The mutual
   block lives inside `namespace OpenMath.Chapter3.Section312.RKTableau`
   (line 2508 onward) where only `open OpenMath.Chapter3.Section381`
   is in scope. Unqualified `RootedTree` resolved to a different
   `RootedTree` (causing
   `Application type mismatch: ... expected Section310.RootedTree`).

   **Fix**: wrap the mutual block in a `section ... end` with a local
   `open OpenMath.Chapter3.Section310` to bring the right `RootedTree`
   into scope. Cycle 187's helpers escape this because they live in
   the `Section381` namespace block (line 997–1564) which has the
   right opens at line 999. Wrapping is the minimal-risk fix; opening
   `Section310` at the top of the namespace block would also work but
   affects the whole block.

2. **P3 attempted on paper, declined**. The bottom-block formula
   above contains a recursive `(compose).derivativeWeight (natAdd s₁ j₂) t`
   term that does not eliminate cleanly. A naive port of the top-block
   recipe (`Fin.sum_univ_add` then simp the four `compose_A_*` lemmas)
   produces two non-zero halves: the `compose_A_botLeft = M₁.b j₁`
   half collapses to `M₁.elementaryWeight t` via P1.A, BUT the
   `compose_A_botRight = M₂.A i j₂` half retains a
   `(compose).derivativeWeight (natAdd s₁ j₂) t` factor that requires
   the bottom-block mutual partner. The mutual call structure thus
   has to thread through `t`'s subtrees — heavier than the top-block
   recipe and requires a substantially redesigned proof skeleton.

## Discovery

1. **Namespace scoping trick for `RootedTree` access from
   `Section312.RKTableau` blocks**: when a private helper inside the
   `RKTableau` namespace needs `RootedTree`, wrap it in:

   ```lean
   section
   open OpenMath.Chapter3.Section310

   <mutual or theorem here>

   end
   ```

   Avoids polluting the surrounding namespace block. The pattern is
   reusable for any future `RKTableau`-namespace helper that pattern-
   matches on `RootedTree.mk`.

2. **Top-block vs. bottom-block asymmetry for `compose`**:
   - Top block (stages `castAdd s₂ i`): clean closed form
     `derivativeWeight = M₁.derivativeWeight`. The bottom half of
     `Fin.sum_univ_add` zeroes out because `compose_A_topRight = 0`.
   - Bottom block (stages `natAdd s₁ i`): NO closed form in
     M₁/M₂ separately. The bottom-block A-row is `(M₁.b, M₂.A)`, so
     splitting the `Fin (s₁+s₂)` sum yields one half that collapses
     to `M₁.elementaryWeight t` (via cycle 224's
     `derivativeWeight_compose_castAdd` on the top half) and another
     half whose `derivativeWeight (natAdd s₁ j₂) t` factor is exactly
     the bottom-block mutual partner.

   This asymmetry is consistent with the cycle 213/214 pattern where
   `compose_of_isRKOneStep` had to thread M₁'s output through
   M₂'s starting value via `← hY₁_out` — the bottom block is where
   M₁ and M₂ genuinely interact, not where they decouple.

3. **`Fin.sum_univ_add` + `compose_A_*` simp set is the cleanest
   driver** for sums over the composite tableau. Cycle 213/214 used
   exactly this in `compose_of_isRKOneStep` (lines 2665/2671/2676);
   cycle 224's `derivativeWeightProd_compose_castAdd` uses it in
   the recursive `t :: ts` case. Expect cycle 225's bottom-block work
   to use the same simp set as the backbone.

4. **`derivativeWeightProd ... [] = 1` reduces definitionally**, so
   the base case of the mutual partner closes by `rfl`. Same as cycle
   187 base case (`derivativeWeightProd_pReduced ... [] = rfl`).

## Suggested next approach

For cycle 225, the natural next deliverable is the **bottom-block
analog** that handles `(M₁.compose M₂).derivativeWeight (natAdd s₁ i) t`.
Two possible shapes:

**Option A — Closed-form-via-auxiliary-function**: introduce an
auxiliary `M₂.derivativeWeightWithSrc (M₁ : RKTableau s₁) (i : Fin s₂)
(t : RootedTree) : ℝ` that recursively evaluates `t` with `M₂.A`
inside but using `M₁.elementaryWeight` at each leaf-replacement. Then
prove `(M₁.compose M₂).derivativeWeight (natAdd s₁ i) t =
M₂.derivativeWeightWithSrc M₁ i t`. This auxiliary function may also
satisfy a clean `elementaryWeight` identity that feeds into
`compose_phiEquivalent_compose`.

**Option B — Direct mutual induction on `t` and a list-helper**:
mirror cycle 187's pattern but with the bottom-block recursion. The
`derivativeWeightProd` mutual partner now has to track *both* M₁'s
top-block per-tree weights AND M₂'s bottom-block per-tree weights at
the same time. Likely needs a stronger induction statement.

Option A may be cleaner from a theorem-proving perspective (the
auxiliary function gives a name to the recursive object). Option B is
closer to cycle 187's template.

The end goal for `compose_phiEquivalent_compose` (cycle 224's deferred
P4) is to show, for any `t`:

```
∑ i : Fin (s₁+s₂), (M₁.compose M₂).b i * (M₁.compose M₂).derivativeWeight i t
  = ∑ i : Fin (s₁'+s₂'), (M₁'.compose M₂').b i * (M₁'.compose M₂').derivativeWeight i t
```

The top-block split now closes via cycle 224's P1.A pair plus
`hPhi₁ t` (yielding `M₁.elementaryWeight t = M₁'.elementaryWeight t`).
The bottom-block split closes iff cycle 225 lands a usable
bottom-block formula compatible with `hPhi₂` per-tree.

Once cycle 225 lands the bottom-block half:
- Cycle 226: ship `compose_phiEquivalent_compose` + `composeQ_phi`
  (lift to `Quotient PhiEquivalent.setoidSigma` via `Quotient.lift₂`).
- Cycle 227: ship `composeQ_phi_id_left`/`_right` (identity laws on
  the new quotient).
- Cycle 228: ship `Group` instance on `Quotient PhiEquivalent.setoidSigma`.
- Cycle 229: ship `thm:384A` (Φ as a group homomorphism between the
  two quotients).

That puts the formal "Φ is a group homomorphism" deliverable ~5
cycles out from cycle 224, contingent on the bottom-block formula
landing cleanly in cycle 225.

§441 Phase C.2 GPFS-blocked (41st consecutive, skipped per cycle 224
strategy §A).
