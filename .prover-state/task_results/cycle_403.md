# Cycle 403 Results

## Worked on

Phase α'.5.0 deliverable per cycle 402 scoping doc §6.1
(`.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`):
**`elementaryWeightQ_phi_inv_mkVertexVertexCherry`** — the
order-5 asymmetric two-leaf + cherry three-children tree
`mk [vertex, vertex, cherry]` quotient-level closed form for
`Φ_{η_q⁻¹}` (first non-symmetric `k = 3` empirical witness for
`inversePolyTree`), plus matching `m=0` corollary and two
non-vacuity `example`s on `⟦explicitEuler⟧`.

Insertion point: `OpenMath/Chapter4/Section422.lean:5924`
(immediately after cycle 386's `mk [broom₃, cherry]` m=0 example
and before the cycle 380 Phase α'.1 `inversePolyChain` section
header).

## Approach

### Pre-flight (cycle 402 §8 entry checklist)

1. **Read scoping doc** `def_422B_phase_alpha_prime_5_scoping.md` §6.1
   (Phase α'.5.0 deliverable spec) and §C (paper derivation), §I
   (do-NOTs), §J (faithfulness check).
2. **Symbolic verification** per strategy §I R3: re-derived the
   per-row inverse-derivative against cycle 384 `mkCherryCherry`'s
   proof body. **DISCOVERED that strategy §C was WRONG** — see
   Discovery section below.
3. **Submitted Aristotle batch** (project
   `76b5de82-5da4-4465-bd21-42ae5422a676`) per CLAUDE.md
   §Aristotle-first mandate at cycle start, in parallel with
   manual closure.
4. **Read cycle 370 `bushy` and cycle 372 `mkVertexCherry` ships**
   for combined helper/recipe reuse.

### Main ship

Wrote the cycle 403 block (~480 LOC inclusive of docstrings):

* **Theorem** `elementaryWeightQ_phi_inv_mkVertexVertexCherry`
  with corrected 7-kernel RHS (see Discovery #1 below for why
  bushy was needed as a 7th kernel beyond the strategy's 6).
* **14 helper `have` blocks** inside the proof: 11 reused
  verbatim from cycles 367/368/369/372 + 2 new bushy helpers
  reused from cycle 370 + 3 new cycle 403 helpers
  (`h_dw_mkVertexVertexCherry`, `h_mkVertexVertexCherry`,
  `h_dws_mkVertexVertexCherry`).
* **Main computation**: `_inv_mk` + 7 `_mk` rewrites + `h_sum`
  algebraic kernel folding + `ring`.
* **m=0 corollary**
  `powRep_sum_eq_of_agreement_at_mkVertexVertexCherry_zero` with
  7 agreement hypotheses (vertex, cherry, broom₃, bushy,
  mk [cherry], mk [vertex, cherry], mk [v, v, c]).
* **Two non-vacuity `example`s** on `⟦explicitEuler⟧` (closed-form
  witness evaluating to `−1`, reflexive m=0 with all 7
  agreements discharged by `rfl`).

### Verification

* `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 with
  only the grandfathered cycle 365 sorry warning at line 2272.
* `lake build OpenMath.Chapter4.Section422` succeeded (164 s on
  warm cache).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5
  (unchanged: 4 docstring + 1 grandfathered cycle 365 code).
* `#print axioms elementaryWeightQ_phi_inv_mkVertexVertexCherry`
  → `[propext, Classical.choice, Quot.sound]` ✓
* `#print axioms powRep_sum_eq_of_agreement_at_mkVertexVertexCherry_zero`
  → `[propext, Classical.choice, Quot.sound]` ✓

### Aristotle

Submitted at cycle start with the full theorem statement + the
simpler `h_dws_mkVertexVertexCherry` helper as fallback. Reached
15% progress after ~1 hour. Manual closure succeeded first;
canceled the Aristotle project to release the cycle 403 worker.

## Result

**SUCCESS** — Phase α'.5.0 ships axiom-clean. §422 streak: 63
substantive + 4 doc (336–402) → **64 substantive + 4 doc**
(336–403).

Section422.lean: 8178 → 8788 LOC (+610 net, exceeds strategy's
250–300 LOC budget by ~310). The overshoot is due to:

1. **Cycle 370 bushy helper inline reuse** (~40 LOC). Strategy
   §D mentioned reusing cycle 367/368/369/372 helpers but didn't
   account for the cycle 370 `h_dw_bushy` + `h_bushy` helpers
   needed because the corrected closed form uses `bushy` as a
   kernel.
2. **7-kernel non-vacuity example** (~14 `have` blocks ≈ 100
   LOC) vs strategy-predicted 6-kernel case (12 blocks ≈ 80 LOC).
3. **Header documentation** (`/-! ###` section + theorem
   docstrings) ~80 LOC documenting the bushy-kernel discovery
   for future cycles' reference.
4. **Helper proof bodies** for the 3 new cycle 403 helpers were
   slightly longer than projected because the three-children
   cons-case requires both a `h_prod_step_cherry` and a
   `h_prod_step_vc` intermediate (vs cycle 372's single
   intermediate for two-children).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `elementaryWeightQ_phi_inv_mkVertexVertexCherry`

* **Entity ID**: `def:422B` (continuing the §422
  underlying-one-step-method work track via Phase α'.5
  infrastructure). Status remains `partial` — Phase α'.5.0 is
  one stepping stone of the 7–13 cycle plan in
  `def_422B_phase_alpha_prime_5_scoping.md`. `cycle_completed_at`
  bumped 402 → 403.
* **Textbook statement** (Butcher §387, §422 page references via
  cycle 358 `_inv_mk` infrastructure): the §383 inverse class
  `η_q⁻¹` extends the underlying one-step-method `D ∈ G` via
  group inverse; its elementary weight at the rooted tree
  `mk [v, v, c]` is determined by the cycle 358 `_inv_mk`
  formula `Φ_{⟦M⟧⁻¹}(t) = −Σᵢ M.b i · M.derivativeWeightWithSrc
  M.inverse i t`. The cycle 403 theorem ships the algebraic
  expansion of this formula at `t = mk [v, v, c]` into a
  polynomial in lower-order Φ_η values.
* **Lean statement captures**: same content. The Lean signature
  is a pure-algebraic identity between `Φ_{η_q⁻¹}` at the named
  tree and a polynomial in 6 lower-order `Φ_η` kernels (vertex,
  cherry, broom₃, bushy, mk [cherry], mk [vertex, cherry])
  + a `−Φ_η(mk [v, v, c])` self-term.
* **Definition smuggling check**: PASS — no new `def` or
  `structure` introduced. Only a `theorem` over existing
  definitions (`elementaryWeightQ_phi`, `RootedTree.mk`,
  `Quotient.lift`, etc.).
* **Tautology check**: PASS — LHS is `Φ_{η_q⁻¹}`, RHS is a
  polynomial in `Φ_{η_q}` values at *distinct* trees including
  the self-tree. Non-trivial.
* **Identity check**: PASS — the proof body is ~310 LOC of
  substantive `_inv_mk`-unfold + sum-distribution chain, not
  `exact h`.
* **Hypothesis strength check**: PASS — only hypothesis is
  `η_q : Quotient PhiEquivalent.setoidSigma`. No extras.
* **Absent theorem check**: N/A — no promised but unwritten
  content.

### Divergence from cycle 402 strategy §B

The strategy's §B prescribed a **6-kernel** closed form (vertex,
cherry, broom₃, mk [cherry], mk [vertex, cherry], mk [v, v, c])
based on the §C paper derivation `(-v + Aᵢ)² · ((v² - c) + Bᵢ)`.

Cycle 403 worker's symbolic verification (per strategy §I R3
"do NOT trust §C without symbolic verification") **found this
incorrect**. The cherry-child factor in `derivativeWeightWithSrc`
contains `∑ⱼ Aᵢⱼ · derivativeWeightWithSrc M.inverse j cherry =
∑ⱼ Aᵢⱼ · (-v + ∑ₖ Aⱼₖ) = -v·Aᵢ + Bᵢ`, not just `Bᵢ`. The
correct per-row factor is `(-v + Aᵢ)² · ((v² - c) - v·Aᵢ + Bᵢ)`,
which when summed against `Σᵢ bᵢ` requires the kernel
`Σᵢ bᵢ · Aᵢ³ = Φ_η(bushy)`.

Justification for divergence: **the strategy was empirically
incorrect, caught at the pre-flight verification step that the
strategy itself prescribed (§I R3)**. The corrected 7-kernel
form uses `Φ_η(bushy)` as a 7th kernel; this is **not a new
kernel** in the sense of requiring new infrastructure — cycle
370's `bushy` ship provides the needed helper `h_bushy` reused
verbatim.

This is consistent with the cycle 398 §7 R3 precedent (paper
derivations can have subtleties) and the strategy's §K
verification checklist explicitly cites `#print axioms` for the
new theorem as a verification mechanism (which passed
axiom-clean despite the corrected RHS).

### `powRep_sum_eq_of_agreement_at_mkVertexVertexCherry_zero`

* **Entity ID**: same `def:422B` (Sub-lemma A specialised witness
  at `t = mk [v, v, c], m = 0`, paralleling cycles
  366/367/368/369/370/371/372/378/384/386's m=0 corollaries).
* **Textbook statement**: derived from Sub-lemma A
  `powRep_sum_eq_of_strict_subtree_agreement` at the given tree
  and exponent.
* **Lean statement captures**: same content. Hypotheses are the
  7 agreement equations at the 7 kernels of cycle 403's closed
  form.
* **Definition smuggling / tautology / identity / hypothesis
  strength**: all PASS — same diagnostic as the closed-form
  theorem above. Proof is 3-line `h_pow + rw` chain composing
  cycle 403's closed form with the 7 agreement substitutions,
  parallel to cycle 384's recipe.
* Strategy §E corollary signature had 6 agreement hypotheses
  (vertex, cherry, broom₃, mk [cherry], mk [vertex, cherry],
  mk [v, v, c]); cycle 403 corollary has 7 (added `h_bushy`)
  for the same reason as the closed form theorem.

## Dead ends

None. The Aristotle batch ran for ~1 hour with no usable
returns (15% progress at cancellation, no incremental partial
proofs surfaced). Manual closure succeeded first per the
strategy's §G expectation ("**Do NOT** wait beyond 30 min —
manual closure is well within cycle budget").

## Discovery

### Discovery #1 (LOAD-BEARING): cherry-child factor in derivativeWeightWithSrc per-row expansions includes a `-v·Aᵢ` term

For per-row inverse-derivative expansions at trees with cherry
(or higher-order non-leaf) children, the inner sum
`∑ⱼ Aᵢⱼ · derivativeWeightWithSrc M.inverse j cherry` evaluates
via cycle 367's `h_dws_cherry` to:
```
∑ⱼ Aᵢⱼ · (M.inverse.elementaryWeight vertex + ∑ₖ Aⱼₖ)
  = ∑ⱼ Aᵢⱼ · (-v + ∑ₖ Aⱼₖ)
  = -v · ∑ⱼ Aᵢⱼ + ∑ⱼ Aᵢⱼ · ∑ₖ Aⱼₖ
  = -v·Aᵢ + Bᵢ
```
NOT just `Bᵢ`. Both terms must be carried forward. The cycle
402 strategy §C derivation omitted the `-v·Aᵢ` term, leading
to a 6-kernel statement that was wrong by `−v·bushy`,
`-2v²b'` (`broom₃` coefficient changed from `−v²` to `−3v²`),
and a `+v·bushy` term.

**Recommendation**: future Phase α'.5 cycles should verify
paper derivations against cycle 384 `mkCherryCherry` and cycle
386 `mkBroomCherry` proof bodies (both correctly include the
`-v·Aᵢ`-style terms) BEFORE locking the closed-form RHS.

### Discovery #2: `Φ_η(bushy)` as a 7th kernel for any tree with `[..., vertex, vertex, cherry, ...]` substructure

The cycle 403 closed form requires `Φ_η(bushy)` as the kernel
identification for `Σᵢ bᵢ · Aᵢ³`. This kernel arises from the
`Aᵢ² · (-v · Aᵢ)` cross-term in the per-row factor expansion.

Any future Phase α'.5 tree with 2+ vertex children followed by
a non-leaf child will need this kernel. The cycle 370 `bushy`
ship's helpers (`h_dw_bushy`, `h_bushy`) can be reused
verbatim.

### Discovery #3: `rw` with `M.elementaryWeight` `← h_*` folds work cleanly at any expression size

The cycle 403 main computation's final `rw [h_subst, ...
Finset.sum_add_distrib × 6, ← Finset.mul_sum × 6, ← h_<kernel>
× 7]; ring` worked on the first try with no `ring` timeout —
suggesting the strategy's projected ~250 LOC budget was for
the back-fold step only; the actual budget needed
includes helper proof bodies (~3× the back-fold cost).

### Discovery #4: `lake env lean Section422.lean` does NOT update olean cache

When verifying axiom-cleanness with `#print axioms` via a
separate test file `import OpenMath.Chapter4.Section422`, the
import reads the cached olean — which is stale if you edited
`Section422.lean` without running `lake build`. Solution:
always run `lake build OpenMath.Chapter4.Section422`
(rebuilds olean) before `#print axioms` verification, even if
direct `lake env lean Section422.lean` already passed.
(Worker hit this issue in cycle 403; ~5 min lost diagnosing
"Unknown identifier" before realizing the cache was stale.)

## Suggested next approach

Per cycle 402 scoping doc §6.2 and §L, **cycle 404** ships
Phase α'.5.1:

1. **`inversePolyTree_mkVertexVertexCherry` calibration witness**
   (~30 LOC, mechanical mirror of cycle 400's
   `inversePolyTree_bushy` template scaled to the asymmetric
   `(vertex, vertex, cherry)` triple).
2. **`trichildCrossTerm` dispatch extension** with a new branch
   matching the cycle 403 closed form's structure (~20 LOC,
   back-computed by comparing cycle 403's RHS to
   `inversePolyTree`'s 8-block decomposition for
   `(vertex, vertex, cherry)`).

### Back-computation for `trichildCrossTerm` at `(vertex, vertex, cherry)`

Cycle 403's closed form for `Φ_{η_q⁻¹}(mk [v, v, c])`:
```
−v⁵ + 4v³c − 2vc² − 3v²b' + cb' + v·bushy − v²m + 2v·vc − M_vvc
```

`trichildPolynomial` 8-block decomposition (cycle 399 ship,
analogous to cycle 387's `bichildPolynomial`):
```
trichildPolynomial t₁ t₂ t₃ inv₁ inv₂ inv₃ f
  = -(v · inv₁ · inv₂ · inv₃)              -- Block (1)
    - inv₂ · inv₃ · f(mk [t₁])              -- Block (2)
    - inv₁ · inv₃ · f(mk [t₂])              -- Block (3)
    - inv₁ · inv₂ · f(mk [t₃])              -- Block (4)
    + trichildCrossTerm t₁ t₂ t₃ f          -- Blocks (5)+(6)+(7)
    - f(mk [t₁, t₂, t₃])                    -- Block (8)
```

For `(t₁, t₂, t₃) = (vertex, vertex, cherry)`:
- `inv₁ = inv₂ = inversePolyTree vertex f = -v`
- `inv₃ = inversePolyTree cherry f = v² - c`
- Block (1): `-(v · -v · -v · (v² - c)) = v³(v² - c) - 0 = v⁵ - v³c`
   Wait — let me recompute: `-(v · (-v) · (-v) · (v² - c)) = -(v · v² · (v² - c)) = -v³(v² - c) = -v⁵ + v³c`.
- Block (2): `-((-v) · (v² - c) · f(mk[vertex])) = -(-v(v²-c)·c) = vc(v²-c) = v³c - vc²`
- Block (3): same as Block (2) (t₂ = t₁ = vertex). `= v³c - vc²`
- Block (4): `-((-v) · (-v) · f(mk[cherry])) = -(v² · m) = -v²m`
- Block (5)+(6)+(7): `trichildCrossTerm vertex vertex cherry f` (unknown, to be solved for)
- Block (8): `-f(mk [vertex, vertex, cherry]) = -M_vvc`

Sum (without trichildCrossTerm):
```
  (-v⁵ + v³c)            -- Block (1)
+ (v³c - vc²)            -- Block (2)
+ (v³c - vc²)            -- Block (3)
+ (-v²m)                 -- Block (4)
+ (-M_vvc)               -- Block (8)
=  -v⁵ + 3v³c - 2vc² - v²m - M_vvc
```

Comparing to cycle 403's actual closed form:
```
-v⁵ + 4v³c - 2vc² - 3v²b' + cb' + v·bushy - v²m + 2v·vc - M_vvc
```

Required `trichildCrossTerm vertex vertex cherry f` =
```
(actual) - (sum without trichildCrossTerm)
= (4v³c - 3v³c) + (- 3v²b' + cb' + v·bushy + 2v·vc)
= v³c - 3v²b' + cb' + v·bushy + 2v·vc
```

So:
```
trichildCrossTerm vertex vertex cherry f
  = f vertex · f cherry · (f vertex)²              -- v³c term, but wait
                                                    -- v³c is v·v·v·c... hmm
```

Actually let me reparametrize. With `v := f vertex, c := f cherry,
b' := f broom₃, m := f (mk [cherry]), vc := f (mk [vertex, cherry]),
bushy := f bushy`:

`trichildCrossTerm vertex vertex cherry f`
`= v³c - 3v²b' + cb' + v·bushy + 2v·vc`

Or:
```
trichildCrossTerm vertex vertex cherry f
  = (f vertex)³ · f cherry
    - 3 · (f vertex)² · f broom₃
    + f cherry · f broom₃
    + f vertex · f bushy
    + 2 · f vertex · f (mk [vertex, cherry])
```

That's a 5-term cross-term, which is consistent with the cycle 386
precedent (the `mkBroomCherry` cross-term needed Block (4) leaf+non-leaf
mixed kernel `Φ_η(mk [vertex, broom₃])`). For `(vertex, vertex, cherry)`,
similarly mixed kernels arise: `bushy`, `mk [vertex, cherry]`.

Cycle 404 worker should verify this back-computation symbolically
before locking the `trichildCrossTerm` branch, per the lessons of
cycle 403.

### Beyond cycle 404

Cycle 405+ continues the Phase α'.5.1 witness ladder per scoping
doc §3.3 candidate list. Eventual Phase α'.5.2 cycles can migrate
specific `inversePolynomial` branches to dispatch through
`inversePolyTree` if/when the heterogeneous `k = 3` trees become
ladder consumers (default per scoping doc §6.3: NO migration —
the candidate trees are NOT on the current 9-ladder dispatch
list). Phase α'.5.3 (`k = 4` `tetrachildPolynomial`) deferred
to cycle 408+.

## Closing

§422 axiom-clean streak: **64 substantive + 4 doc** cycles
(336–403). Phase α'.5.0 deliverable closed. Cycle 404 entry
point fully concrete (back-computed `trichildCrossTerm` value
above) and ~50 LOC; one of the smallest cycles in the §422
streak.
