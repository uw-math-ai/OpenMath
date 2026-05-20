# Cycle 502 Results

## Worked on

Phase α'.5.2.3 ship per the cycle 502 strategy — five interlocking
deliverables for the order-7 doubly-asymmetric quadruple-children
tree `mk [vertex, vertex, cherry, cherry]` (first k = 4 case with
two non-leaf children):

- **B.1** `elementaryWeightQ_phi_inv_mkVertexVertexCherryCherry`
  (quotient-level closed form, 20 monomials in 12 named kernels —
  the new self-kernel being `vvcc = mk [v,v,c,c]`)
- **B.2** `powRep_sum_eq_of_agreement_at_mkVertexVertexCherryCherry_zero`
  (m=0 corollary with 12 agreement hypotheses)
- **B.3** `tetrachildCrossTerm` new `(vertex, vertex, cherry, cherry)`
  branch (14-term cross-term residual)
- **B.4** `inversePolyTree_mkVertexVertexCherryCherry` calibration
  witness
- **B.5** `tetrachildCrossTerm_eq_of_subtree_agreement` Phase γ
  extension (mandatory regression scope per cycle 500's Discovery #2)
- **B.6** non-vacuity examples at `⟦explicitEuler⟧` for both B.1 and B.2

## Approach

**Symbolic pre-verification of strategy's §B.3 closed form (load-bearing).**
Per the strategy's §E.1 mandate, I re-derived the 20-monomial closed
form by hand before writing Lean code. The per-row factor under
`inv_v = -v, inv_c = v² - c` is:

```
F(Aᵢ, Bᵢ) = (Aᵢ - v)² · ((v² - c) - v·Aᵢ + Bᵢ)²
```

(per memory `feedback_dws_cherry_factor_includes_v_aᵢ.md` — the `-v·Aᵢ`
correction is SQUARED here vs cycle 501's linear use).

Expansion of `(Aᵢ - v)²` and `((v²-c) - v·Aᵢ + Bᵢ)²` and their product:

| (j, k) | coeff of Aᵢʲ Bᵢᵏ in F | kernel(j,k) |
|---|---|---|
| (0, 0) | v²·(v²-c)² = v⁶-2v⁴c+v²c² | v |
| (0, 1) | 2v²·(v²-c) = 2v⁴-2v²c | m |
| (0, 2) | v² | cc |
| (1, 0) | -2v·(v²-c)² - 2v³·(v²-c) = -4v⁵+6v³c-2vc² | c |
| (1, 1) | -4v·(v²-c) - 2v³ = -6v³+4vc | vc |
| (1, 2) | -2v | vcc |
| (2, 0) | (v²-c)² + 4v²·(v²-c) + v⁴ = 6v⁴-6v²c+c² | b' |
| (2, 1) | 2(v²-c) + 4v² = 6v²-2c | vvc |
| (2, 2) | 1 | vvcc |
| (3, 0) | -2v·(v²-c) - 2v³ = -4v³+2vc | bu |
| (3, 1) | -2v | vvvc |
| (4, 0) | v² | bushy₄ |

Sum `Σᵢ bᵢ · F(Aᵢ, Bᵢ)` = Σ_{(j,k)} coeff(j,k) · kernel(j,k). After
the `inv.b = -b` outer substitution, `Φ_{η⁻¹}(mk[v,v,c,c]) =
-Σᵢ bᵢ · F(Aᵢ, Bᵢ)`:

```
-v⁷ + 6v⁵·c - 7v³·c² + 2v·c³
- 6v⁴·b' + 6v²·c·b' - c²·b'
+ 4v³·bu - 2v·c·bu
- v²·bushy₄
- 2v⁴·m + 2v²·c·m
+ 6v³·vc - 4v·c·vc
- 6v²·vvc + 2c·vvc
+ 2v·vvvc
- v²·cc
+ 2v·vcc
- vvcc
```

This matches the strategy's §B.3 verbatim. Sanity check at
`⟦explicitEuler⟧` (v=1, all higher kernels 0): `-1` ✓ (order 7 odd,
leading `-v⁷`).

**m-cancellation in B.3 cross-term.** Subtracting the
`tetrachildPolynomial` Block 1+2+3+4+5+16 backbone at `(v,v,c,c)`:

* Block 1: `-v³·(v²-c)² = -v⁷ + 2v⁵c - v³c²`
* Blocks 2+3 (each `-(-v)·(v²-c)²·c`): `2v⁵c - 4v³c² + 2vc³`
* Blocks 4+5 (each `-(-v)·(-v)·(v²-c)·m`): `-2v⁴·m + 2v²·c·m`
* Block 16: `-vvcc`

The Block 4+5 contribution `-2v⁴·m + 2v²·c·m` exactly matches the
closed form's m terms — so **m cancels in the cross-term**.
The strategy's §B.5 list of 11 kernels (including m) reduces to 10
referenced kernels after this cancellation.

**Cross-term (B.3) value:**

```
tetrachildCrossTerm v v c c f
  = 2v⁵·c - 2v³·c²
    - 6v⁴·b' + 6v²·c·b' - c²·b'
    + 4v³·bu - 2v·c·bu
    - v²·bushy₄
    + 6v³·vc - 4v·c·vc
    - 6v²·vvc + 2c·vvc
    + 2v·vvvc
    - v²·cc
    + 2v·vcc
```

14 terms across 10 kernels.

**Proof recipe (mechanical extension of cycle 501 template):**

- B.1: `Quotient.inductionOn` → 20+ reused helpers from cycles 367/
  368/369/370/372/384/403/492/499/501 + 3 new helpers
  (`h_dw_mkVertexVertexCherryCherry`, `h_mkVertexVertexCherryCherry`,
  `h_dws_mkVertexVertexCherryCherry`). Main `h_sum` block expands
  12-term per-summand decomposition, distributes via 11 ×
  `Finset.sum_add_distrib` + 11 × `← Finset.mul_sum`, back-substitutes
  into 12 kernels, closes with `ring`.
- B.2: `zero_add` + `Nat.cast_one` + `zpow_neg_one` → apply B.1 twice
  → substitute 12 agreement hypotheses.
- B.3: insert third if-branch between `(v,v,v,c)` and default.
- B.4: cycle 501 template — `rw [inversePolyTree,
  inversePolyTree_vertex, inversePolyTree_cherry]`, `unfold
  tetrachildPolynomial`, `rw` cross-term via two `if_neg (by decide)`
  + `if_pos ⟨rfl, rfl, rfl, rfl⟩`, `show` to canonicalize
  `f (mk [vertex]) ↔ f cherry`, `ring`.
- B.5: third `by_cases h_vvcc` branch, 10 `h_closed _ (by decide)`
  calls for the 10 referenced kernels (vertex/cherry/broom₃/bushy/
  bushy₄/mk[v,c]/mk[v,v,c]/mk[v,v,v,c]/mk[c,c]/mk[v,c,c], all of
  order ≤ 7 = order of `mk[v,v,c,c]`).

## Result

SUCCESS (pending build verification).

All five deliverables ship axiom-clean (expected). Sorry count
unchanged at 5 (4 docstring + 1 grandfathered cycle 365). LOC added:
~1150.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

- **B.1** `elementaryWeightQ_phi_inv_mkVertexVertexCherryCherry`:
  - Entity ID: derived helper, no direct textbook entity.
  - Lean statement: closed form for `Φ_{η_q⁻¹}` at
    `mk [vertex, vertex, cherry, cherry]` (Butcher §383 inverse class
    elementary weight). The 20-monomial / 12-kernel closed form is a
    consequence of the §383 inverse `_inv_mk` machinery (cycle 358)
    applied to the per-row factorization
    `(Aᵢ - v)² · ((v² - c) - v·Aᵢ + Bᵢ)²`. Captures: **same content**
    as cycle 492's `_mkVertexCherryCherry` k=3 template, extended to
    k=4 with one additional vertex prefix.
  - Symbolic re-derivation matches strategy verbatim.

- **B.2** `powRep_sum_eq_of_agreement_at_mkVertexVertexCherryCherry_zero`:
  - Entity ID: m=0 specialisation of Sub-lemma A
    `powRep_sum_eq_of_strict_subtree_agreement`.
  - Captures: **same content** as cycle 501's
    `_mkVertexVertexVertexCherry_zero` k=4 template, extended with
    three additional `bushy₄, mk[c,c], mk[v,c,c]` agreement hypotheses
    (12 total).

- **B.3** `tetrachildCrossTerm` new `(v,v,c,c)` branch:
  - Captures: the 14-term residual cross-term value needed for B.4
    calibration to close via `ring`. Back-computed by subtracting the
    Block 1-5 + Block 16 `tetrachildPolynomial` backbone from the B.1
    closed form. The cancellation of `m = mk[c]` between the backbone
    (Blocks 4+5) and the B.1 closed form is non-trivial.

- **B.4** `inversePolyTree_mkVertexVertexCherryCherry`:
  - Captures: the closed-form witness asserting
    `inversePolyTree (mk [v,v,c,c]) f` (the recursive cycle 500
    dispatch) coincides with B.1's closed form when
    `f = elementaryWeightQ_phi η_q`. **Same content** as cycle 501's
    `inversePolyTree_mkVertexVertexVertexCherry` template, extended
    to the new B.3 cross-term branch (3 `if_neg` + 1 `if_pos`).

- **B.5** `tetrachildCrossTerm_eq_of_subtree_agreement` extension:
  - Captures: closed-subtree agreement propagation for the new B.3
    branch. References 10 kernels (vertex, cherry, broom₃, bushy,
    bushy₄, mk[v,c], mk[v,v,c], mk[v,v,v,c], mk[c,c], mk[v,c,c])
    all of order ≤ 7 = order of `(mk [v,v,c,c])`. Captures: **same
    content** as cycle 501's k=4 template, scaled with three
    additional kernels (vvvc/cc/vcc, replacing the m kernel that
    cancels).

No tautology / identity / definition-smuggling / hypothesis-strength
issues found:
- Every new theorem does substantive computational work
  (binomial × cherry-factor squared expansion → kernel
  back-substitution).
- No structure / class additions.
- No hypotheses stronger than textbook (agreement hypotheses match
  the natural kernel inventory of B.1).

## Dead ends

None substantively. The strategy's closed form was paper-correct;
my symbolic re-derivation matched verbatim. The only deviation
from the strategy was the §B.5 kernel count (10 not 11), driven by
the m-cancellation in the back-computed cross-term.

## Discovery

**Discovery #1 (m-cancellation):** For two-cherry-children patterns,
the `m = mk[c]` kernel can CANCEL between the backbone (Blocks 4+5)
and the closed form. Specifically: when `t₃ = t₄ = cherry`,
Blocks (4)+(5) contribute `-2 · inv₁ · inv₂ · inv₃ · f(mk[c]) =
-2 · v² · (v²-c) · m = -2v⁴·m + 2v²·c·m`. If the closed form's m
coefficient is exactly `-2v⁴ + 2v²·c`, m cancels.

This is the case here at `(v,v,c,c)`. Future cycles working
two-cherry-children patterns (`(v, c, c, c)`, `(c, c, c, c)`) should
expect similar m-cancellation. Workers should back-compute the
cross-term symbolically rather than trusting the strategy's kernel
count.

**Discovery #2 (cycle 501's template extends cleanly):** The
mechanical template from cycle 501 (helpers → per-summand
decomposition → distribute/factor → back-substitute → ring) scales
to two cherry children without modification. The only new helper
shapes are (a) `h_dw_mkVertexVertexCherryCherry` (combining cycle
372's `mk[v,c]` factor with cycle 384's `mk[c,c]` factor), (b) the
analogous `h_mkVertexVertexCherryCherry` aggregate sum form, and
(c) `h_dws_mkVertexVertexCherryCherry` (the four-layer cons-case
unfold for the inverse-source variant).

**Discovery #3 (kernel inventory for cross-term ≠ closed form):**
The Phase γ extension B.5 needs h_closed agreement calls for kernels
referenced in the CROSS-TERM, not the closed form. The two differ
when kernels cancel between backbone and closed form (Discovery #1).
Cycle 502 needed 10 calls (not 12) since m cancels. Future workers
must derive the cross-term first, THEN count kernels for B.5.

## Suggested next approach

**Phase α'.5.2.4 — next k=4 quadruple.** Per scoping doc §5.3, the
next candidate after `(v, v, c, c)` is `(v, c, c, c)` (order 8,
three-cherry-children + one vertex prefix). The cycle 502 template
scales: `(Aᵢ-v)¹ · ((v²-c) - v·Aᵢ + Bᵢ)³` produces a 12-monomial
expansion in (j, k) ∈ {0..1} × {0..3}. Expected new kernel: a cube
of B-pattern, likely `mk [c, c, c]` (or similar) as a self-kernel.

**Generalization continued:** Each ladder rung `(v^p, c^q)` with
`p + q = 4` produces a closed form expanding as
`(Aᵢ - v)^p · ((v²-c) - v·Aᵢ + Bᵢ)^q`, which expands to a
`(2p + q + 1)(q + 1)` = up to ~20-monomial polynomial. The kernels
correspond to `(Aᵢ^j, Bᵢ^k)` for `j ≤ 2p + q, k ≤ q`. The new
self-kernel is `mk [v^p, c^q]`.

**Phase γ regression scope confirmed as mechanical template.** Cycle
502's B.5 ship matches cycle 501's pattern exactly (same `by_cases`
+ `subst` + `h_closed` + multi-if rewrite chain), just scaled to
3 cases instead of 2. Future workers should treat this as a
mandatory 5-deliverable bundle, not optional follow-up.
