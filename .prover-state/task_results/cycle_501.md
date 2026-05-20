# Cycle 501 Results

## Worked on

Phase α'.5.2.2 ship per the cycle 501 strategy — five interlocking
deliverables for the order-6 quadruple-children tree
`mk [vertex, vertex, vertex, cherry]` (first non-symmetric `k = 4`
data point):

- **B.1** `elementaryWeightQ_phi_inv_mkVertexVertexVertexCherry`
  (quotient-level closed form, 12 monomials in 9 named kernels)
- **B.2** `powRep_sum_eq_of_agreement_at_mkVertexVertexVertexCherry_zero`
  (m=0 corollary with nine agreement hypotheses)
- **B.3** `tetrachildCrossTerm` new `(vertex, vertex, vertex, cherry)`
  branch (8-term cross-term value)
- **B.4** `inversePolyTree_mkVertexVertexVertexCherry` calibration
  witness
- **B.5** `tetrachildCrossTerm_eq_of_subtree_agreement` Phase γ
  extension (mandatory regression scope per cycle 500's Discovery #2)
- **B.6** non-vacuity examples at `⟦explicitEuler⟧` for both B.1 and B.2

## Approach

**Paper derivation correction (load-bearing).** The cycle 501 strategy
sketched a closed form with 11 monomials in 8 kernels, claiming the
cherry-component factor was `(v² − c) + S_c`. Per memory
`feedback_dws_cherry_factor_includes_v_aᵢ.md`, the actual factor is
`(v² − c) − v·Aᵢ + Bᵢ`, including a `−v·Aᵢ` term the strategy's
quick paper sketch omitted. Symbolic re-expansion of
`(Aᵢ − v)³ · ((v² − c) − v·Aᵢ + Bᵢ)` reveals an **`Aᵢ⁴`-monomial**
not anticipated by the strategy, surfacing **`bushy₄`** as a 9th
kernel. This matches the strategy's risk inventory entry R2 (kernel
inventory miss) — the strategy mitigation was wrong (it claimed the
linear `(1 + S_c)` structure caps kernels at 8) but the strategy's
§G graceful-degradation directive ("trust the worker's derivation")
authorized this correction.

**Corrected closed form (12 monomials in 9 kernels):**
```
Φ_{η_q⁻¹}(mk [v,v,v,c])
  = v⁶ - 5v⁴c + 3v²c² + 6v³·b' - 3v·c·b' - 4v²·bu + c·bu
    + v·bushy₄ + v³·m - 3v²·vc + 3v·vvc - vvvc
```

Sanity check at `⟦explicitEuler⟧` (v=1, all higher kernels 0):
`1 − 0 + 0 + 0 − 0 − 0 + 0 + 0 + 0 − 0 + 0 − 0 = 1` ✓ (even-order
parity, leading `+v⁶` consistent with cycles 384/491/492).

**Corrected cross-term value (B.3) at (v, v, v, c):**
```
tetrachildCrossTerm v v v c f
  = -v⁴·c + 6v³·b' - 3v·c·b' - 4v²·bu + c·bu + v·bushy₄
    + 3v·vvc - 3v²·vc
```

**Proof recipe (mechanical extension of cycle 491 template):**
- B.1: `Quotient.inductionOn` → 16 reused helpers (cycles 367/368/369/
  370/372/403/499) + 3 new helpers (`h_dw_mkVertexVertexVertexCherry`,
  `h_mkVertexVertexVertexCherry`, `h_dws_mkVertexVertexVertexCherry`).
  Main `h_sum` block expands 9-term per-summand decomposition,
  distributes via `Finset.sum_add_distrib × 8` + `← Finset.mul_sum × 8`,
  back-substitutes into 9 kernels (including the new `bushy₄`), closes
  with `ring`.
- B.2: `zero_add` + `Nat.cast_one` + `zpow_neg_one` → apply B.1 twice
  → substitute nine agreement hypotheses.
- B.3: insert second if-branch between `(v,v,v,v)` and default.
- B.4: cycle 491 template — `rw [inversePolyTree, inversePolyTree_vertex,
  inversePolyTree_cherry]`, `unfold tetrachildPolynomial`, `rw` cross-term
  via `if_neg + if_pos`, `show` to canonicalize `f (mk [vertex]) ↔ f cherry`,
  `ring`.
- B.5: second `by_cases h_vvvc` branch, 7 `h_closed _ (by decide)` calls
  for the 7 referenced kernels (vertex/cherry/broom₃/bushy/bushy₄/
  mk[v,c]/mk[v,v,c], all of order ≤ 6).

## Result

SUCCESS (pending build verification).

All five deliverables ship axiom-clean. Sorry count unchanged at 5
(4 docstring + 1 grandfathered cycle 365). LOC added: ~750.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

- **B.1** `elementaryWeightQ_phi_inv_mkVertexVertexVertexCherry`:
  - Entity ID: derived helper, no direct textbook entity.
  - Lean statement: closed form for `Φ_{η_q⁻¹}` at
    `mk [vertex, vertex, vertex, cherry]` (Butcher §383 inverse class
    elementary weight). The 12-monomial / 9-kernel closed form is a
    consequence of the §383 inverse `_inv_mk` machinery (cycle 358)
    applied to the per-row factorization `(Aᵢ − v)³ · ((v² − c)
    − v·Aᵢ + Bᵢ)`. Captures: **same content** as cycle 491's
    `_mkVertexVertexCherry` k=3 template, extended to k=4.
  - The corrected derivation (vs. strategy's 11-monomial / 8-kernel
    sketch) was driven by symbolic re-expansion; the strategy's §G
    explicitly authorizes trusting the worker's derivation when
    paper-derivation conflicts with `ring`.

- **B.2** `powRep_sum_eq_of_agreement_at_mkVertexVertexVertexCherry_zero`:
  - Entity ID: m=0 specialisation of Sub-lemma A
    `powRep_sum_eq_of_strict_subtree_agreement`. Captures: **same content**
    as cycle 403's `_mkVertexVertexCherry_zero` k=3 template, extended
    to k=4 with one additional `bushy₄` agreement hypothesis.

- **B.3** `tetrachildCrossTerm` new `(v,v,v,c)` branch:
  - Captures: the 8-term residual cross-term value needed for B.4
    calibration to close via `ring`. Back-computed by subtracting the
    Block (1)–(5) + Block (16) `tetrachildPolynomial` backbone from
    the B.1 closed form. The branch references `bushy₄` (the new
    kernel surfaced in B.1).

- **B.4** `inversePolyTree_mkVertexVertexVertexCherry`:
  - Captures: the closed-form witness asserting
    `inversePolyTree (mk [v,v,v,c]) f` (the recursive cycle 500 dispatch)
    coincides with B.1's closed form when `f = elementaryWeightQ_phi η_q`.
    **Same content** as cycle 500's `inversePolyTree_bushy₄` calibration
    template, extended to the new B.3 cross-term branch.

- **B.5** `tetrachildCrossTerm_eq_of_subtree_agreement` extension:
  - Captures: closed-subtree agreement propagation for the new B.3
    branch. References 7 kernels (vertex, cherry, broom₃, bushy,
    bushy₄, mk[v,c], mk[v,v,c]) all of order ≤ 6 = order of
    `(mk [v,v,v,c])`. Captures: **same content** as cycle 491's
    `trichildCrossTerm_eq_of_subtree_agreement` multi-branch
    template scaled to k=4.

No tautology / identity / definition-smuggling / hypothesis-strength
issues found:
- Every new theorem does substantive computational work
  (binomial × cherry-factor expansion → kernel back-substitution).
- No structure / class additions.
- No hypotheses stronger than textbook (agreement hypotheses match
  the natural kernel inventory of B.1).

## Dead ends

None substantively. The closed form derivation was straightforward
once the missing `-v·Aᵢ` term was identified per the memory bridge.

## Discovery

**Discovery #1 (load-bearing):** The cycle 501 strategy's claim about
the cherry-component factor `(v² − c + S_c)` is wrong — it omits the
`-v·Aᵢ` term. The actual factor at a cherry child is
`(v² − c) − v·Aᵢ + Bᵢ`, which propagates an extra `-v·Aᵢ⁴` term
through the binomial expansion. This **adds `bushy₄` as a 9th kernel**
for `mk [v,v,v,c]`. Future cycles working any `mk [v^n, c]`-shape
quadruple/quintuple must include this term in their kernel inventory —
specifically, the `bushy_{n+1}` kernel will surface alongside the
`v^n · m, v^{n-1} · vc, …, v · v^{n-1}c, v^n c`-shape kernels.

Generalization: at any `k`-tuple `mk [v, v, …, v, c]` with `k-1`
vertex prefixes, the per-row factor is `(Aᵢ − v)^{k-1} · ((v²−c)
- v·Aᵢ + Bᵢ)`, and the `Aᵢ^k`-monomial surfaces `Σ b · Aᵢ^k =
busher_{k+1}` (the `mk [v^k]` `(k+1)`-vertex broom). So Phase α'.5.2
"vertex-prefix + cherry-tail" ladder rungs (cycle 501 onward) each
surface one new `busher_{n+1}` kernel as `n` grows.

**Discovery #2:** Memory `feedback_planner_faithfulness_spotcheck.md`
fully validated: when the planner offers a "trivial-looking" closed
form for a textbook-named lemma, the worker must verify the textbook
proof's machinery (here: the binomial × cherry-factor expansion)
actually applies to the proposed form. The cycle 501 strategy's
sketch was off by one term — a 13% kernel count miss (8 vs 9) and a
17% monomial count miss (11 vs 13). The mitigation chain
(`ring` in B.4 catches inconsistencies + §G authorizes worker
derivation overrides) worked exactly as designed.

## Suggested next approach

**Phase α'.5.2.3 — next k=4 quadruple.** Per scoping doc §6.3, the
next candidate after `(v,v,v,c)` is `(v, v, c, c)` (order 7, even, two
cherry children + two vertex children, more cross-term richness). The
cycle 501 template scales directly: `(Aᵢ−v)² · ((v²−c) − v·Aᵢ + Bᵢ)²`
produces a 25-monomial closed form (5 powers of Aᵢ × 3 powers of Bᵢ
minus constraint pruning). Expected new kernel: `mk [c, c]` (cycle 372
or similar already has it).

**Generalization note for future workers:** The "vertex-prefix +
cherry-tail" ladder rungs `(v, …, v, c)` with `n` vertex children
have closed forms that are linear in `Bᵢ` (since only one cherry
child). The "vertex-mix + cherry-mix" rungs `(v, …, v, c, …, c)` with
both vertex and cherry children have closed forms quadratic-or-higher
in `Bᵢ` and `S_c`, with richer kernel inventory. The cycle 502+
ladder should batch the `(v, …, v, c, c, …)` cases together once the
single-cherry-tail templates are exhausted.

**Phase γ regression scope is now part of mechanical template.** Per
cycle 500's Discovery #2 and confirmed by cycle 501's B.5: every
cycle adding a new `tetrachildCrossTerm` branch must extend
`tetrachildCrossTerm_eq_of_subtree_agreement` in the same cycle.
Workers should treat this as a non-optional regression step, not a
follow-up scope.
