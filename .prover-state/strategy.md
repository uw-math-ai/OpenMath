# Cycle 403 strategy — Phase α'.5.0 ship: `mk [vertex, vertex, cherry]`

## §A. No blocker. Pivot directly to Phase α'.5.0.

Cycle 402 shipped `.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`
(956 lines) as a markdown-only scoping doc per the cycle 401 task
results' Option 1 recommendation. The doc explicitly names cycle 403
as the **Phase α'.5.0 implementation cycle** with target tree
`mk [vertex, vertex, cherry]` (order 5, k=3, asymmetric two-leaf
+ cherry children — the **first non-symmetric `k = 3` empirical
witness** for `inversePolyTree`).

Read scoping doc §3.2 (preliminary paper derivation), §6.1 (Phase
α'.5.0 deliverable specification), §7 (risks), and §8 (cycle 403
entry point) before writing Lean code.

## §B. Target: `elementaryWeightQ_phi_inv_mkVertexVertexCherry`

Ship a single closed-form theorem in
`OpenMath/Chapter4/Section422.lean`, placed immediately after cycle
372's `elementaryWeightQ_phi_inv_mkVertexCherry` (at ~line 4062).
Plus the matching `m=0` corollary
`powRep_sum_eq_of_agreement_at_mkVertexVertexCherry_zero` per the
cycle 367/368/369/370/371/372/384/386 template.

**Statement** (predicted closed form, paper-derived in §C below —
DO verify symbolically before finalising the RHS):

```lean
theorem elementaryWeightQ_phi_inv_mkVertexVertexCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      = -(elementaryWeightQ_phi η_q RootedTree.vertex) ^ 5
        + 3 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q RootedTree.cherry
        - 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * (elementaryWeightQ_phi η_q RootedTree.cherry) ^ 2
        + 2 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry])
        - (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        - (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + elementaryWeightQ_phi η_q RootedTree.cherry
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) := by
  ...
```

**8 distinct elementary-weight kernels** on RHS: `vertex`, `cherry`,
`broom₃`, `mk [cherry]`, `mk [vertex, cherry]` (cycle 372 kernel),
`mk [vertex, vertex, cherry]` (the self-kernel). No new kernel
introduced — `mk [vertex, cherry]` was already shipped by cycle 372.

## §C. Paper derivation (verify symbolically before locking RHS)

Notation: `v = Φ_η(vertex)`, `c = Φ_η(cherry)`, `b' = Φ_η(broom₃)`,
`m = Φ_η(mk [cherry])`, `vc = Φ_η(mk [vertex, cherry])`.

Per-row inverse-derivative factor (cycle 358 `_inv_mk` expansion at
the three-child tree `mk [vertex, vertex, cherry]`):

```
M.inverse.derivativeWeightWithSrc i (mk [vertex, vertex, cherry])
  = ((-v) + Aᵢ) · ((-v) + Aᵢ) · ((v² - c) + Bᵢ)
```

where `Aᵢ := Σⱼ Aᵢⱼ` and `Bᵢ := Σⱼ Aᵢⱼ · Σₖ Aⱼₖ`. The cherry-child
factor uses cycle 367's `inv_cherry = v² - c` plus the inner
`Σⱼ Aᵢⱼ · derivativeWeight j cherry = Bᵢ`.

Expanding `(-v + Aᵢ)² · ((v² - c) + Bᵢ)`:

```
= (v² - 2v·Aᵢ + Aᵢ²) · ((v² - c) + Bᵢ)
= v²(v² - c)            + v²·Bᵢ
  - 2v(v² - c)·Aᵢ       - 2v·Aᵢ·Bᵢ
  + (v² - c)·Aᵢ²        + Aᵢ²·Bᵢ
```

Summing against `M.b i` and collapsing via:

* `Σᵢ bᵢ · 1 = v` (constant factors out)
* `Σᵢ bᵢ · Aᵢ = c` (Φ_η(cherry))
* `Σᵢ bᵢ · Aᵢ² = b'` (Φ_η(broom₃))
* `Σᵢ bᵢ · Bᵢ = m` (Φ_η(mk [cherry]))
* `Σᵢ bᵢ · Aᵢ · Bᵢ = vc` (Φ_η(mk [vertex, cherry]))
* `Σᵢ bᵢ · Aᵢ² · Bᵢ = Φ_η(mk [vertex, vertex, cherry])` (self-kernel)

gives

```
Σᵢ bᵢ · F(i)
  =  v²(v²-c)·v + v²·m
   - 2v(v²-c)·c - 2v·vc
   + (v²-c)·b' + Φ_η(mk[v,v,c])
  =  v⁵ - v³c + v²m
   - 2v³c + 2vc² - 2v·vc
   + v²b' - cb' + Φ_η(mk[v,v,c])
  =  v⁵ - 3v³c + 2vc² + v²m - 2v·vc + v²b' - cb' + Φ_η(mk[v,v,c])
```

By cycle 358 `_inv_mk` the inverse closed form is the **negation**:

```
Φ_{η⁻¹}(mk [v,v,c])
  = -v⁵ + 3v³c - 2vc² + 2v·vc - v²b' - v²m + cb' - Φ_η(mk [v,v,c])
```

— matches the §B `theorem` statement above (8 terms, leading `-v⁵`
sign appropriate to **odd** order-5 parity, consistent with cycle
384's `mkCherryCherry` closed form which also leads with `-v⁵`).

**Critical pre-flight task**: verify this expansion symbolically by
reading the cycle 384 `mkCherryCherry` proof body
(`Section422.lean:4655–4961`) and cycle 370 `bushy` proof body
(`Section422.lean:3011–3169`), and mentally re-running the
per-summand `ring` step. The cycle 398 §7 R3 precedent — paper
derivations can have sign subtleties — applies. If symbolic
verification disagrees with §C above, **fix the §B RHS and the proof
recipe before committing**.

## §D. Proof recipe (hybrid of cycle 370 bushy + cycle 372 mkVertexCherry templates)

Cycle 384's `elementaryWeightQ_phi_inv_mkCherryCherry`
(Section422.lean lines 4655–4961, ~250 LOC body) is the closest
structural template for an order-5 two-non-leaf-children tree. The
cycle 403 ship combines:

* **Cycle 370 bushy template** for the two-vertex-children portion
  of the per-row factor `(-v + Aᵢ)²` (the `h_dws_bushy` helper
  pattern with three-fold cons-case unfold scaled down to two).
* **Cycle 372 mkVertexCherry template** for the cherry-child factor
  `((v² - c) + Bᵢ)` (the `h_dws_cherry` + `h_inv_cherry` pattern).

### Helper reuse (verbatim from cycles 367/368/369/372)

* `h_inv_v` (cycle 367) — `M.inverse.elementaryWeight vertex = -v`
* `h_vertex` (cycle 367) — `M.elementaryWeight vertex = Σ b`
* `h_dw_cherry`, `h_cherry`, `h_dws_cherry` (cycle 367) — cherry weights
* `h_dw_broom₃`, `h_broom₃` (cycle 368) — broom₃ weights
* `h_inv_cherry` (cycle 369 representative-lift) —
  `M.inverse.elementaryWeight cherry = v² - c`
* `h_dw_mkCherry`, `h_mkCherry` (cycle 369) — mk[cherry] weights
* `h_dw_mkVertexCherry`, `h_mkVertexCherry` (cycle 372) —
  mk[vertex, cherry] weights

### New helpers (cycle 403 ships)

* `h_dw_mkVertexVertexCherry` — closed form for
  `M.derivativeWeight i (mk [vertex, vertex, cherry])`. Three-child
  cons-case unfold. Final closed form:
  `(Σⱼ Aᵢⱼ)² · (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)`.

* `h_mkVertexVertexCherry` — `M.elementaryWeight (mk [v,v,c]) =
  Σᵢ bᵢ · (Σⱼ Aᵢⱼ)² · (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)`. Trivial after `h_dw_*`.

* `h_dws_mkVertexVertexCherry` — closed form for
  `M.derivativeWeightWithSrc M.inverse i (mk [v,v,c])`. Final closed
  form: `(-v + Aᵢ)² · ((v² - c) + Bᵢ)` where `Aᵢ = Σⱼ Aᵢⱼ`,
  `Bᵢ = Σⱼ Aᵢⱼ · Σₖ Aⱼₖ`.

### Main computation

After `refine Quotient.inductionOn η_q ?_; rintro ⟨s, M⟩` and
declaring all helpers above:

```lean
rw [elementaryWeightQ_phi_inv_mk M (mk [vertex, vertex, cherry]),
    elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
    elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
    elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
    elementaryWeightQ_phi_mk]
have h_sum : (∑ i : Fin s, M.b i *
              M.derivativeWeightWithSrc M.inverse i (mk [v,v,c])) = ... := by
  have h_subst : ... := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dws_mkVertexVertexCherry i, h_inv_v]
    ring
  rw [h_subst]
  -- 6 Finset.sum_(add|sub)_distrib + 5 ← Finset.mul_sum
  -- + back-substitution: ← h_mkVertexVertexCherry, ← h_mkVertexCherry,
  --    ← h_broom₃, ← h_mkCherry, ← h_cherry, ← h_vertex
  -- + ring
  ...
rw [h_sum]; ring
```

The per-summand integrand `(-v + Aᵢ)² · ((v² - c) + Bᵢ)` distributes
into 6 terms (per §C). Each term, after `Finset.sum_congr + ring`,
gets folded into one of the 6 elementary-weight kernels via
`← Finset.mul_sum`. Final `ring` closes the algebraic identity.

### Constant consolidation (cycle 372 Discovery, applicable here)

When two integrand terms share a tail summed against `Σ bᵢ · Aᵢ` (e.g.
the `-2v³ · Aᵢ` and `2vc · Aᵢ` terms), fold their constants together
as `(-2v³ + 2vc) · (bᵢ Aᵢ)` BEFORE `Finset.sum_distrib`. This avoids
two separate `← h_cherry` applications and lets `ring` close the
arithmetic. See cycle 372 `mkVertexCherry` proof at
`Section422.lean:3798-4061` for the canonical pattern.

## §E. m=0 corollary

```lean
theorem powRep_sum_eq_of_agreement_at_mkVertexVertexCherry_zero
    {η_q η_q' : Quotient PhiEquivalent.setoidSigma}
    (h_v : elementaryWeightQ_phi η_q vertex
            = elementaryWeightQ_phi η_q' vertex)
    (h_c : elementaryWeightQ_phi η_q cherry
            = elementaryWeightQ_phi η_q' cherry)
    (h_b : elementaryWeightQ_phi η_q broom₃
            = elementaryWeightQ_phi η_q' broom₃)
    (h_m : elementaryWeightQ_phi η_q (mk [cherry])
            = elementaryWeightQ_phi η_q' (mk [cherry]))
    (h_vc : elementaryWeightQ_phi η_q (mk [vertex, cherry])
            = elementaryWeightQ_phi η_q' (mk [vertex, cherry]))
    (h_vvc : elementaryWeightQ_phi η_q (mk [vertex, vertex, cherry])
            = elementaryWeightQ_phi η_q' (mk [vertex, vertex, cherry])) :
    elementaryWeightQ_phi (η_q ^ (-((0 + 1 : ℕ) : ℤ)))
        (mk [vertex, vertex, cherry])
      = elementaryWeightQ_phi (η_q' ^ (-((0 + 1 : ℕ) : ℤ)))
        (mk [vertex, vertex, cherry])
```

Proof template (mirror cycle 384 m=0 corollary):

```lean
have h_pow : ∀ ζ : Quotient _, ζ ^ (-((0 + 1 : ℕ) : ℤ)) = ζ⁻¹ := by
  intro ζ
  rw [zero_add, Nat.cast_one]
  exact zpow_neg_one ζ
rw [h_pow η_q, h_pow η_q',
    elementaryWeightQ_phi_inv_mkVertexVertexCherry η_q,
    elementaryWeightQ_phi_inv_mkVertexVertexCherry η_q',
    h_v, h_c, h_b, h_m, h_vc, h_vvc]
```

## §F. Non-vacuity `example`s

Two `example`s on `⟦explicitEuler⟧`:

1. **Closed-form witness**:
   `Φ_{⟦explicitEuler⟧⁻¹}(mk [v,v,c])` should evaluate to **`-1`** at
   explicit Euler.

   At explicit Euler: `v = 1, c = b' = m = vc = Φ_η(mk[v,v,c]) = 0`
   (since `A = 0` makes all non-vertex elementary weights zero).
   Closed form gives:
   ```
   -1⁵ + 3·1³·0 - 2·1·0² + 2·1·0 - 1²·0 - 1²·0 + 0·0 - 0 = -1
   ```
   ✓ (matches the cycle 384 `mkCherryCherry` non-vacuity pattern; the
   leading `-v⁵` survives, all other terms vanish at explicit Euler).

2. **Reflexive m=0**: `η_q = η_q' = ⟦explicitEuler⟧` with all 6
   agreement hypotheses discharged by `rfl × 6`.

## §G. Aristotle batch (Priority 0 — submit at cycle start, do not wait)

Per `CLAUDE.md` §"Aristotle-first (MANDATORY)" and the scoping doc
§8.1 recommendation:

Submit a single Aristotle project at cycle 403 start with:
* The full `elementaryWeightQ_phi_inv_mkVertexVertexCherry` theorem
  statement (§B).
* The m=0 corollary statement (§E).
* The three new sub-helpers (`h_dw_mkVertexVertexCherry`,
  `h_mkVertexVertexCherry`, `h_dws_mkVertexVertexCherry`) as named
  in-context targets.
* Include cycle 370/372/384 closed forms (`elementaryWeightQ_phi_inv_bushy`,
  `elementaryWeightQ_phi_inv_mkVertexCherry`,
  `elementaryWeightQ_phi_inv_mkCherryCherry`) as cited template
  examples in the prompt — Aristotle has previously closed analogous
  inverse-closed-form theorems (e.g. cycle 281's `342d` general
  norm-square).

Sleep 30 min, single-poll, incorporate any clean returns. **Do NOT
wait beyond 30 min** — manual closure is well within cycle budget,
and the cycle 386 worker found that Aristotle is unreliable for
order-5+ closed-form ships (cycle 386 timed out and was manually
closed).

## §H. Manual ship (Priority 1)

If Aristotle returns nothing usable (likely), ship manually per §D
recipe. **LOC budget**: ~250–300 (cycle 384 was 250, cycle 386 was
521 due to a more substantive expansion). Expect ~300 LOC including
helpers + non-vacuity examples; if you blow past 400 LOC, audit for
unused helpers and consider extracting reusable pieces.

Insert the new theorem at `Section422.lean:~4062` (immediately after
`elementaryWeightQ_phi_inv_mkVertexCherry` closes). The m=0 corollary
immediately follows. The two non-vacuity `example`s go at the file's
bottom, alongside existing examples (after cycle 386's `mkBroomCherry`
examples).

## §I. What NOT to do

* **Do NOT freelance a pivot to a fresh entity.** Cycle 401 wrote a
  clear continuation path; cycle 402 confirmed Phase α'.5.0 is the
  right next step. Pivoting now would waste cycle 402's scoping
  investment.
* **Do NOT trust §C's paper derivation without symbolic verification.**
  Per cycle 398 §7 R3 — paper derivations can have sign or coefficient
  subtleties. Read cycle 384's `mkCherryCherry` and cycle 370's
  `bushy` proof bodies, and mentally check the per-summand expansion,
  BEFORE locking the §B RHS. The Aristotle submission, if attempted,
  also serves as a verification — if it disagrees with §C, audit
  before manual ship.
* **Do NOT skip the Aristotle submission.** CLAUDE.md mandates it.
  Even if you expect manual closure, run the batch.
* **Do NOT introduce `inversePolyTree_mkVertexVertexCherry`
  calibration witness OR extend `trichildCrossTerm`.** That is Phase
  α'.5.1, cycle 404+ work. Cycle 403 ships **only** the closed-form
  quotient-level witness + m=0 corollary, mirroring the cycle 384
  Phase α'.5.0 pattern (cycle 384 did NOT ship a corresponding
  `inversePolyTree_*` calibration in the same cycle).
* **Do NOT touch the cycle 365 grandfathered sorry** at
  `Section422.lean:2279`. Multi-cycle Phase β/γ extension; deferred.
* **Do NOT use `simp [inversePolyTree, ...]`** anywhere in this ship
  — Phase α'.5.0 does not extend `inversePolyTree`. Per memory
  `feedback_simp_recursive_def_overunfolds.md`, that simp pattern
  over-unfolds recursive defs.
* **Do NOT raise `maxHeartbeats`** anywhere. The cycle 384 ship
  closed within default 200000; cycle 403 should too.
* **Do NOT introduce sorries.** §422 axiom-clean streak is at 63
  substantive + 4 doc (cycles 336–402). Cycle 403 must preserve it.
* **Do NOT attempt to compile `Section441.lean`** on GPFS. 43+
  consecutive timeouts since cycle 182. Skip per
  `cycle_182_gpfs_slowness.md`.
* **Do NOT modify `scripts/autonomous_loop.py`** or the
  prompt-builder. Tautology-scanner / phantom-verdict bugs are
  loop-maintainer territory.
* **Do NOT attempt to fix the cycle 398 `lean_status.json` JSON-escaping
  bug** flagged in cycle 402 task results §"Discovery" #1. Your
  cycle 403 append must use correctly-escaped `\"` for any inner
  double quotes, but leave the cycle 398 prose untouched. Bundle a
  JSON-fixup ship into a future low-priority cycle.

## §J. Faithfulness check (mandatory before commit)

For the new theorem:

* **Entity ID**: `def:422B` (continuing the §422 underlying
  one-step-method work track via Phase α' / α'.5 infrastructure).
  Status remains `partial` — Phase α'.5.0 is one stepping stone of
  the 7–13 cycle plan in `def_422B_phase_alpha_prime_5_scoping.md`.
* **Lean statement captures**: per §B, the closed form for
  `Φ_{η_q⁻¹}(mk [vertex, vertex, cherry])`. The Lean signature is a
  pure-algebraic identity between `Φ_{η_q⁻¹}` at a named tree and a
  polynomial in 6 lower-order `Φ_η` kernels + a `-Φ_η(mk[v,v,c])`
  self-term.
* **Definition smuggling check**: PASS — no new `def` or
  `structure` introduced. Only a `theorem` over existing definitions
  (`elementaryWeightQ_phi`, `RootedTree.mk`, etc.).
* **Tautology check**: PASS — LHS is `Φ_{η_q⁻¹}`, RHS is a
  polynomial in `Φ_{η_q}` values at *distinct* trees including the
  self-tree. Non-trivial.
* **Identity check**: PASS — the proof is a substantive
  ~250 LOC `_inv_mk`-unfold + sum-distribution chain, not `exact h`.
* **Hypothesis strength**: PASS — only hypothesis is `η_q :
  Quotient PhiEquivalent.setoidSigma`. No extras.
* **Absent theorem check**: N/A — no promised but unwritten content.

## §K. Verification checklist (run before committing)

1. `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5
   (unchanged — 4 docstring + 1 grandfathered cycle 365 code at
   line 2279).
3. `#print axioms elementaryWeightQ_phi_inv_mkVertexVertexCherry`
   returns `[propext, Classical.choice, Quot.sound]`.
4. `#print axioms powRep_sum_eq_of_agreement_at_mkVertexVertexCherry_zero`
   returns same.
5. Update `extraction/formalization_data/lean_status.json` `def:422B`
   row's `cycle_completed_at` to 403 with cycle 403 note appended.
   (⚠️ Use correctly-escaped `\"` for any inner double quotes per
   §I above.)
6. Update `plan.md` `def:422B` row's tail with cycle 403 ship
   summary.
7. Write `.prover-state/task_results/cycle_403.md` per CLAUDE.md
   format.

## §L. Cycle 404+ outlook (for the next planner, do not implement)

After cycle 403's `mk [vertex, vertex, cherry]` closed form lands,
cycle 404 ships Phase α'.5.1:
* `inversePolyTree_mkVertexVertexCherry` calibration witness (~30
  LOC, mechanical, uses cycle 400's `inversePolyTree_bushy` template
  scaled to the asymmetric triple).
* `trichildCrossTerm` dispatch extension with a new branch
  `if (t₁, t₂, t₃) = (vertex, vertex, cherry) then <closed-form cross-term>`
  (~20 LOC, back-computed from the cycle 403 closed form's structure).

Cycle 405+ continues the witness library at further `k = 3` trees
per scoping doc §3.3 candidate list.

## §M. Bottom-line directive for cycle 403

Ship `elementaryWeightQ_phi_inv_mkVertexVertexCherry` + m=0 corollary
+ 2 non-vacuity examples in `OpenMath/Chapter4/Section422.lean`
immediately after cycle 372's `mkVertexCherry` block (~line 4062).
Mirror cycle 384's `mkCherryCherry` proof structure, with cherry-child
factor handled per cycle 372 and two-vertex-children factor handled
per cycle 370. Submit Aristotle batch at cycle start (parallel
speculation), close manually within ~250–300 LOC if Aristotle returns
nothing usable. Update bookkeeping files. Preserve §422 streak.

§422 axiom-clean streak after cycle 403 (if successful):
**64 substantive + 4 doc** (cycles 336–403).
