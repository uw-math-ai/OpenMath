# Cycle 372 strategy — §422 Phase D.3.b Step 2 `mk [vertex, cherry]` closed form ship

## §A. State entering cycle 372

* §422 Phase D.3.b axiom-clean streak: **37 cycles** (336–371).
* `OpenMath/Chapter4/Section422.lean` last cycle shipped:
  `elementaryWeightQ_phi_inv_mkBroom₃` (closed form for `mk [broom₃]`,
  the depth-2 ladder of `broom₃`) + its m=0 corollary + 2 examples.
* Sorry count: 5 lines total (4 docstring references + 1 grandfathered
  code sorry from cycle 365 at `Section422.lean:2279`, the body of
  Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`).
* Witness library (6 trees): vertex, cherry, broom₃, mk [cherry],
  bushy, mk [broom₃]. Five of order ≤ 3, plus order-4 trees with
  **symmetric children** (bushy = 3 identical leaves) or single-child
  ladders (mk [cherry], mk [broom₃]).
* No Aristotle jobs pending.

## §B. Target — Option 1 from cycle 371 worker's recommendation

Ship `elementaryWeightQ_phi_inv_mkVertexCherry` (closed form for the
**first asymmetric order-4 tree** `mk [vertex, cherry]`) plus its m=0
Sub-lemma A specialisation. This is the substantive next structural
test: heterogeneous children, introducing a new elementary-weight name
(the order-4 asymmetric tree's weight) and a new `c²` quadratic
self-term cross-product structure not present in any prior witness.

### B.1 Closed-form statement (paper-derived and verified)

For `t = mk [vertex, cherry]` (= `mk [vertex, mk [vertex]]`, the
"vertex-cherry pair" order-4 tree):

```
Φ_{η_q⁻¹}(mk [vertex, cherry])
  = v⁴ − 3v²·c + c² + v·b' + v·m − Φ_η(mk [vertex, cherry])
```

where the abbreviated names denote:
* `v  := Φ_η(vertex)`
* `c  := Φ_η(cherry)`
* `b' := Φ_η(broom₃)`     (= `Φ_η(mk [vertex, vertex])`)
* `m  := Φ_η(mk [cherry])` (= `Φ_η(mk [mk [vertex]])`)
* The new term `Φ_η(mk [vertex, cherry])` is its own elementary weight.

**Sanity check at `explicitEuler`** (v=1, c=0, b'=0, m=0, new=0):
`1 − 0 + 0 + 0 + 0 − 0 = 1`. Direct computation of
`Φ_{⟦explicitEuler⟧⁻¹}(mk [vertex, cherry])` via cycle 358's
`elementaryWeightQ_phi_inv_mk` + dwws unfold gives `-1 · -1 = 1` (the
outer minus from `inv_mk`'s `-Σ`, and the inner per-row product at
i=0 is `(-1 + 0) · (1 + 0) = -1`). Match. ✓

### B.2 Derivation summary (for the docstring + sanity)

`dwws(M, M.inverse, i, mk [vertex, cherry])` unfolds as the product
of two children's `derivativeWeightWithSrcProd` contributions:

```
dwwsp(i, [vertex, cherry])
  = (inv_v + Σⱼ Aᵢⱼ · dwws(j, vertex)) · dwwsp(i, [cherry])
  = (inv_v + Σⱼ Aᵢⱼ · 1) · (inv_c + Σⱼ Aᵢⱼ · dwws(j, cherry))
  = (inv_v + Sᵢ) · (inv_c + Σⱼ Aᵢⱼ · (inv_v + Σₖ Aⱼₖ))
```

with `Sᵢ := Σⱼ Aᵢⱼ`, `inv_v = -v` (cycle 367 `h_inv_v`), and
`inv_c = v² - c` (cycle 367 `elementaryWeightQ_phi_inv_cherry`,
lifted via cycle 369's `h_inv_cherry`). Per-row product expansion
distributes the 6 summands of the σbᵢ-weighted total to:

| Per-row term                            | After Σbᵢ                     |
|-----------------------------------------|-------------------------------|
| `(-v) · (v² - c)` = `-v³ + vc`          | `-v³·Σbᵢ + vc·Σbᵢ` = `-v⁴ + v²c` |
| `(-v) · (-v·Sᵢ)` = `v²·Sᵢ`              | `v² · c`                       |
| `(-v) · (Σⱼ Aᵢⱼ·Σₖ Aⱼₖ)` = `-v · innerᵢ` | `-v · m`                      |
| `Sᵢ · (v² - c)` = `v²·Sᵢ − c·Sᵢ`        | `v²·c − c²`                    |
| `Sᵢ · (-v·Sᵢ)` = `-v·Sᵢ²`               | `-v · b'`                      |
| `Sᵢ · (Σⱼ Aᵢⱼ·Σₖ Aⱼₖ)`                  | `Φ_η(mk [vertex, cherry])` (new) |

Sum: `-v⁴ + v²c + v²c − v·m + v²c − c² − v·b' + new`
   = `-v⁴ + 3v²·c − c² − v·b' − v·m + Φ_η(mk [vertex, cherry])`.

Apply the `inv_mk` outer minus: `M.inverse.eW(mk [vertex, cherry])
  = -Σᵢ bᵢ · dwws(i, mk [vertex, cherry])
  = v⁴ − 3v²·c + c² + v·b' + v·m − Φ_η(mk [vertex, cherry])`,

which matches §B.1 above. ✓

## §C. Recipe — cycle 372 ship plan

### C.1 Architecture — append to `OpenMath/Chapter4/Section422.lean`

Insert two new public theorems plus two non-vacuity `example`s
immediately after cycle 371's `powRep_sum_eq_of_agreement_at_mkBroom₃_zero`
witness example (end of file). Use the **cycle 369 `_mkCherry`
recipe** at `Section422.lean:2772-2888` as the structural template —
the outer is a single-child unfold there but the inner cherry layer
is shared with cycle 372's target. Then extend the outer to two
children using cycle 371's `_mkBroom₃` two-child unfold pattern.

### C.2 Required helpers (reuse + new)

**Reuse verbatim** from cycle 369/371's proofs (already in file):

* `h_inv_v` (cycle 367) — `M.inverse.elementaryWeight vertex = -v`.
* `h_vertex` (cycle 367) — `M.elementaryWeight vertex = Σ b`.
* `h_dw_cherry` (cycle 367) — `M.derivativeWeight i cherry = Σⱼ Aᵢⱼ`.
* `h_cherry` (cycle 367) — `M.elementaryWeight cherry = Σᵢ bᵢ · Sᵢ`.
* `h_dws_cherry` (cycle 367) — `M.derivativeWeightWithSrc M.inverse i cherry
    = inv_v + Σⱼ Aᵢⱼ`.
* `h_dw_broom₃` (cycle 368) — `M.derivativeWeight i broom₃ = Sᵢ²`.
* `h_broom₃` (cycle 368) — `M.elementaryWeight broom₃ = Σᵢ bᵢ · Sᵢ²`.
* `h_inv_cherry` (cycle 369, one-liner representative-lift):
  ```lean
  have h_inv_cherry : M.inverse.elementaryWeight RootedTree.cherry
      = (M.elementaryWeight RootedTree.vertex) ^ 2
        - M.elementaryWeight RootedTree.cherry :=
    elementaryWeightQ_phi_inv_cherry
      (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
  ```
* `h_dw_mkCherry` (cycle 369) — `M.derivativeWeight i (mk [cherry])
    = Σⱼ Aᵢⱼ · Σₖ Aⱼₖ`.
* `h_mkCherry` (cycle 369) — `M.elementaryWeight (mk [cherry])
    = Σᵢ bᵢ · Σⱼ Aᵢⱼ · Σₖ Aⱼₖ`.

**New helpers** (3 named + 1 inline):

1. `h_dw_mkVertexCherry : ∀ i, M.derivativeWeight i (mk [vertex, cherry])
   = (Σⱼ Aᵢⱼ) · (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)`. Two-child unfold via the cons-case
   recursion: `derivativeWeightProd i (vertex :: [cherry]) =
   derivativeWeight_via_vertex_factor · derivativeWeightProd i [cherry]`.
   The vertex factor is `Σⱼ Aᵢⱼ · derivativeWeight j vertex = Σⱼ Aᵢⱼ · 1
   = Σⱼ Aᵢⱼ` (use `RKTableau.derivativeWeight_vertex + mul_one`); the
   cherry factor follows cycle 369's `h_dw_mkCherry` recipe.

   ```lean
   have h_dw_mkVertexCherry : ∀ i : Fin s,
       M.derivativeWeight i
           (OpenMath.Chapter3.Section310.RootedTree.mk
             [RootedTree.vertex, RootedTree.cherry])
         = (∑ j : Fin s, M.A i j) * (∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k) := by
     intro i
     show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex)
           * M.derivativeWeightProd i [RootedTree.cherry] = _
     have h_vertex_factor :
         ∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.vertex
           = ∑ j : Fin s, M.A i j := by
       refine Finset.sum_congr rfl (fun j _ => ?_)
       rw [RKTableau.derivativeWeight_vertex, mul_one]
     have h_cherry_factor :
         M.derivativeWeightProd i [RootedTree.cherry]
           = ∑ j : Fin s, M.A i j * ∑ k : Fin s, M.A j k := by
       show (∑ j : Fin s, M.A i j * M.derivativeWeight j RootedTree.cherry)
             * M.derivativeWeightProd i [] = _
       rw [show M.derivativeWeightProd i [] = 1 from rfl, mul_one]
       refine Finset.sum_congr rfl (fun j _ => ?_)
       rw [h_dw_cherry j]
     rw [h_vertex_factor, h_cherry_factor]
   ```

2. `h_mkVertexCherry : M.elementaryWeight (mk [vertex, cherry])
   = Σᵢ bᵢ · (Σⱼ Aᵢⱼ) · (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)`. One `Finset.sum_congr`
   on `h_dw_mkVertexCherry`.

3. `h_dws_mkVertexCherry : ∀ i, M.derivativeWeightWithSrc M.inverse i (mk [vertex, cherry])
   = (inv_v + Σⱼ Aᵢⱼ) · (inv_c + Σⱼ Aᵢⱼ · (inv_v + Σₖ Aⱼₖ))`.
   Two-child unfold of `derivativeWeightWithSrcProd`. The vertex
   factor uses `RKTableau.derivativeWeightWithSrc_vertex` (= 1)
   inside the per-summand `mul_one`; the cherry factor uses
   `h_dws_cherry` for the inner `dws(j, cherry)`.

   ```lean
   have h_dws_mkVertexCherry : ∀ i : Fin s,
       M.derivativeWeightWithSrc M.inverse i
           (OpenMath.Chapter3.Section310.RootedTree.mk
             [RootedTree.vertex, RootedTree.cherry])
         = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j : Fin s, M.A i j)
           * (M.inverse.elementaryWeight RootedTree.cherry
              + ∑ j : Fin s, M.A i j
                  * (M.inverse.elementaryWeight RootedTree.vertex
                     + ∑ k : Fin s, M.A j k)) := by
     intro i
     show (M.inverse.elementaryWeight RootedTree.vertex
             + ∑ j : Fin s, M.A i j
                 * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex)
           * M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry] = _
     have h_vertex_factor :
         ∑ j : Fin s, M.A i j * M.derivativeWeightWithSrc M.inverse j RootedTree.vertex
           = ∑ j : Fin s, M.A i j := by
       refine Finset.sum_congr rfl (fun j _ => ?_)
       rw [RKTableau.derivativeWeightWithSrc_vertex, mul_one]
     have h_cherry_factor :
         M.derivativeWeightWithSrcProd M.inverse i [RootedTree.cherry]
           = M.inverse.elementaryWeight RootedTree.cherry
             + ∑ j : Fin s, M.A i j
                 * (M.inverse.elementaryWeight RootedTree.vertex
                    + ∑ k : Fin s, M.A j k) := by
       show (M.inverse.elementaryWeight RootedTree.cherry
               + ∑ j : Fin s, M.A i j
                   * M.derivativeWeightWithSrc M.inverse j RootedTree.cherry)
             * M.derivativeWeightWithSrcProd M.inverse i [] = _
       rw [show M.derivativeWeightWithSrcProd M.inverse i [] = 1 from rfl, mul_one]
       congr 1
       refine Finset.sum_congr rfl (fun j _ => ?_)
       rw [h_dws_cherry j]
     rw [h_vertex_factor, h_cherry_factor]
   ```

### C.3 Main `h_sum` shape — 6-term closed form

```lean
have h_sum :
    (∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry]))
      = M.elementaryWeight
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry])
        - M.elementaryWeight RootedTree.vertex
            * M.elementaryWeight RootedTree.broom₃
        - M.elementaryWeight RootedTree.vertex
            * M.elementaryWeight
                (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 3 * (M.elementaryWeight RootedTree.vertex) ^ 2
            * M.elementaryWeight RootedTree.cherry
        - (M.elementaryWeight RootedTree.cherry) ^ 2
        - (M.elementaryWeight RootedTree.vertex) ^ 4 := by
  ...
```

Then `rw [h_sum]; ring` closes the main theorem.

**Recipe inside `h_sum`** (following cycle 371's `h_subst` pattern):

1. `h_subst`: `Finset.sum_congr rfl (fun i _ => ?_)`. Per-summand:
   `rw [h_dws_mkVertexCherry i, h_inv_cherry, h_inv_v]`, then expand
   the inner factor `(inv_c + Σⱼ Aᵢⱼ · (inv_v + Σₖ Aⱼₖ))` per the §B.2
   table.

   **Critical**: `ring` does NOT distribute scalars over `Finset.sum`
   (cycle 371 dead-end #1). The inner `Σⱼ Aᵢⱼ · (-v + Σₖ Aⱼₖ)` needs
   a sub-`Finset.sum_congr` + `ring` to expand to
   `(Σⱼ Aᵢⱼ · -v + Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)` = `(-v · Σⱼ Aᵢⱼ + Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)`
   via `Finset.sum_add_distrib` + `← Finset.mul_sum`. Mirror cycle 371's
   `h_inner_expand` pattern.

   After the inner expansion, the per-row product is a sum of 6
   scalar terms × `bᵢ`; `ring` closes the residual identity.

2. `rw [h_subst, Finset.sum_add_distrib, Finset.sum_sub_distrib, ...]`
   to distribute the outer sum over the 6 terms. Likely 5 distribution
   rewrites total.

3. `← Finset.mul_sum × 4`: factor out the four outer scalar constants.
   Per cycle 371 dead-end #2, use **`Finset.mul_sum`** (constant on
   left), NOT `Finset.sum_mul`. The four constants on the left of
   `M.b i` are likely `M.eW(vertex)`, `(M.eW(vertex))²`, `M.eW(cherry)`,
   `(M.eW(vertex))⁴`. (One sum `Σᵢ bᵢ · (...integrand for mkVertexCherry...)`
   matches `← h_mkVertexCherry` directly, no constant factoring.)

4. Back-substitute: `← h_mkVertexCherry, ← h_broom₃, ← h_mkCherry,
   ← h_cherry, ← h_vertex`.

5. Close with `ring` on the residual algebraic identity.

### C.4 m=0 corollary `powRep_sum_eq_of_agreement_at_mkVertexCherry_zero`

Five agreement hypotheses (vertex, cherry, broom₃, mk [cherry],
mk [vertex, cherry]). Follow cycle 369/371's template:

```lean
theorem powRep_sum_eq_of_agreement_at_mkVertexCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    (h_mkCherry : elementaryWeightQ_phi η_q
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
              = elementaryWeightQ_phi η_q'
                    (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]))
    (h_mkVertexCherry : elementaryWeightQ_phi η_q
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.cherry])
                    = elementaryWeightQ_phi η_q'
                          (OpenMath.Chapter3.Section310.RootedTree.mk
                            [RootedTree.vertex, RootedTree.cherry])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ))))
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.cherry])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ))))
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.vertex, RootedTree.cherry]) := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_mkVertexCherry,
      elementaryWeightQ_phi_inv_mkVertexCherry,
      h_vertex, h_cherry, h_broom₃, h_mkCherry, h_mkVertexCherry]
```

### C.5 Non-vacuity examples (2)

1. **Closed-form witness at `⟦explicitEuler⟧`**: should pin
   `Φ_{⟦explicitEuler⟧⁻¹}(mk [vertex, cherry]) = 1`. Follows cycle
   371's pattern with 5 `have h_*_zero` / `have h_*` blocks (vertex,
   cherry, broom₃, mk [cherry], mk [vertex, cherry]) each using
   `simp [RKTableau.explicitEuler, RKTableau.derivativeWeight_vertex,
   ...]`. Close with `rw [h_vertex, h_cherry, h_broom₃, h_mkCherry,
   h_mkVertexCherry]; ring` (gives `1⁴ − 3·1²·0 + 0² + 1·0 + 1·0 − 0
   = 1`).

2. **Reflexive m=0 witness**: discharge all 5 agreement hypotheses
   by `rfl` (5 `rfl`s, analogous to cycle 371's `rfl × 5`).

## §D. What NOT to try (failure modes documented in attempts.md)

* **Do NOT use `ring` to distribute scalars over `Finset.sum`** (cycle
  371 dead-end #1, cycles 367–370 all hit this). Always pre-distribute
  via `Finset.sum_add_distrib` / `Finset.sum_sub_distrib` /
  `Finset.sum_congr + ring` per-summand before final `ring`.

* **Do NOT use `Finset.sum_mul` when the constant is on the left**;
  the matching lemma is `Finset.mul_sum` (cycle 371 dead-end #2). For
  `const * Σ f`, use `← Finset.mul_sum`. For `(Σ f) * const`, use
  `← Finset.sum_mul`.

* **Do NOT try to prove the general Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`**
  body this cycle. Cycle 366's sub-approaches 4.a/4.b
  (Quotient.inductionOn₂ + cycle 362 substitution; strong induction
  on t.order) both fail on the heterogeneous-inner-tableau obstacle
  (LHS/RHS sums range over `Fin (M.1 * (m+1))` vs `Fin (M'.1 * (m+1))`
  with no representative-invariant bridge). The grandfathered sorry
  at `Section422.lean:2279` stays; do not touch it.

* **Do NOT pivot to a fresh entity.** The §422 Phase D.3.b ladder is
  building a witness library for the eventual Sub-lemma A inductive
  attack; breaking the streak mid-ladder loses compounded momentum.
  Per cycle 371's worker recommendation, cycle 372 ships one more
  asymmetric data point, then cycle 373's planner decides between
  one more witness (option 2: `mk [mk [cherry]]`) or pivot to
  multi-cycle Sub-lemma A scoping doc.

* **Do NOT extend the broomₖ ladder** (k ≥ 4). Cycle 370 already
  shipped `bushy` (k=3). Further broom ladder extension provides no
  new structural information; the binomial pattern is established.

* **Do NOT label the new mk[vertex, cherry] theorem with a textbook
  entity ID** in `lean_status.json`. The closed-form witnesses are
  Phase D.3.b internal infrastructure, not textbook entities.

* **Do NOT use `norm_num` to bridge `-(((m+1):ℕ):ℤ) = Int.negSucc m`**
  — it is definitional `rfl`. Use `zero_add + Nat.cast_one +
  zpow_neg_one` for the `m = 0` case (cycle 371 template; see memory
  `feedback_neg_natCast_int_negsucc_rfl.md`).

* **Do NOT submit to Aristotle.** The cycle 371 worker closed the
  analogous `mk [broom₃]` proof in one cycle without Aristotle; cycle
  372 should follow the same discipline. The cycle 371 recipe is
  directly applicable.

* **Do NOT modify cycle 365's Sub-lemma A signature or the linearResidualAt
  predicate.** Those are stable infrastructure consumed downstream.

## §E. Concrete recipe template (copy from cycle 371 `_mkBroom₃`)

The cycle 371 `elementaryWeightQ_phi_inv_mkBroom₃` proof (added in
the latest commit, end of `Section422.lean`) is the closest
structural template for cycle 372:

* Both involve a single outer `mk` layer wrapping further children
  — but cycle 371's `mk [broom₃]` has ONE child (`broom₃`), while
  cycle 372's `mk [vertex, cherry]` has TWO children. The two-child
  unfold pattern comes from cycle 368's `broom₃` (= `mk [vertex,
  vertex]`) proof structure, NOT cycle 371's.

* The inner cherry handling uses cycle 369's `h_inv_cherry`
  representative-lift one-liner and cycle 367's `h_dws_cherry`.

* The closed form's 6-term structure with `c²` is genuinely new —
  no prior witness has a `(Φ_η subtree)²` non-leading term outside
  the leading `v⁴` and the `v²·c` cross-terms.

**Reuse strategy**: copy cycle 369's helper block (helpers through
`h_dws_mkCherry`) verbatim, then add cycle 368's `h_dw_broom₃` and
`h_broom₃` (since broom₃ appears in the closed form), then add the
3 new helpers from §C.2 (`h_dw_mkVertexCherry`, `h_mkVertexCherry`,
`h_dws_mkVertexCherry`) modeled on cycle 371's `h_dws_mkBroom₃`
two-child unfold template.

The main `h_sum` is the **only genuinely new substantive computation**;
follow §C.3 above and budget for 1–2 iterations on the per-summand
`ring` + sum-distribution + `← Finset.mul_sum` chain.

## §F. Ship criteria (cycle 372 deliverable bar)

* `OpenMath/Chapter4/Section422.lean` compiles clean
  (`lake env lean ...` exits 0) with only the existing cycle 365
  Sub-lemma A body sorry warning.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (unchanged).
* `#print axioms elementaryWeightQ_phi_inv_mkVertexCherry` returns
  `[propext, Classical.choice, Quot.sound]`.
* `#print axioms powRep_sum_eq_of_agreement_at_mkVertexCherry_zero`
  returns `[propext, Classical.choice, Quot.sound]`.
* `#print axioms linearResidualAt_depends_only_on_strict_subtrees`
  remains `[propext, sorryAx, Classical.choice, Quot.sound]`
  (unchanged — Sub-lemma A still sorry'd).
* §422 axiom-clean streak extends to **38** (336–372).
* Witness library extends to **7 trees**: vertex, cherry, broom₃,
  mk [cherry], bushy, mk [broom₃], mk [vertex, cherry].
* Update `.prover-state/issues/def_422B_phase_D_3_scoping.md` with
  cycle 372 closure paragraph (append after the cycle 371 update).

## §G. Fallback if compile stalls or per-summand `ring` fails

If the §C.3 `h_subst` per-summand `ring` cannot close the expansion
of `(-v + Sᵢ) · (inv_c + Σⱼ Aᵢⱼ · (-v + Σₖ Aⱼₖ))`:

* **Option G.1**: split the inner factor `inv_c + Σⱼ Aᵢⱼ · (-v + Σₖ Aⱼₖ)`
  into three named intermediates before applying the outer product.
  Introduce a `have h_inner_factor : (Σⱼ Aᵢⱼ · (-v + Σₖ Aⱼₖ))
  = -v·Σⱼ Aᵢⱼ + Σⱼ Aᵢⱼ · Σₖ Aⱼₖ` via per-summand
  `Finset.sum_congr + ring` + `Finset.sum_add_distrib` +
  `← Finset.mul_sum`. Substitute back via `rw [h_inner_factor]` in
  the per-summand context, then `ring`.

* **Option G.2**: introduce per-row intermediates `Sᵢ := Σⱼ Aᵢⱼ`
  and `Tᵢ := Σⱼ Aᵢⱼ · Σₖ Aⱼₖ` via `set` tactic, write the 6-term
  expansion as an explicit `calc` block, and let `ring` operate on
  a polynomial in `M.eW(v)`, `M.eW(cherry)`, `bᵢ`, `Sᵢ`, `Tᵢ`
  without any sums. (Possibly overkill for cycle 372 — cycle 371's
  direct approach worked.)

* **Option G.3 (graceful degradation)**: if `h_sum` cannot close in
  a single cycle, ship only `elementaryWeightQ_phi_inv_mkVertexCherry`
  with a `sorry`'d `h_sum` block and defer the m=0 corollary +
  examples to cycle 373. Sorry count would rise 1 → 2; this is the
  **explicit graceful degradation** authorized per cycle 365 precedent
  (`linearResidualAt_depends_only_on_strict_subtrees` shipped headline
  with one body sorry).

  **Prefer Option G.1 or G.2 over G.3.** Cycle 371 closed its
  analogous `mk [broom₃]` h_sum in one cycle (with one rebuild iter)
  by carefully expanding the inner square pre-distribute; the same
  discipline at one less power (cubic → quadratic) should work.

## §H. Cycle 373+ outlook (post-cycle-372)

After cycle 372 ships option 1, cycle 373's planner has three
substantive directions per cycle 371 §G:

1. **Option 2** (`mk [mk [cherry]]`, depth-3 ladder, one more
   data point). Mechanistically a smaller step than option 1 — the
   depth-3 ladder extends cycle 369 `_mkCherry` and cycle 371
   `_mkBroom₃` patterns with an extra ladder wrap.

2. **Option 3 (RECOMMENDED for cycle 373)**: pivot to scoping the
   inductive Sub-lemma A attack. 7 closed-form witnesses (vertex,
   cherry, broom₃, mk [cherry], bushy, mk [broom₃], mk [vertex,
   cherry]) is sufficient to inform a multi-cycle scoping doc
   analogous to `lem_310B_plan.md`. This is the path off the
   witness-accumulation treadmill toward Phase D.3.d and Phase E
   sealing of `def:422B`.

3. **Pivot to a fresh entity** (e.g. `def:451A` G-stable per
   `cycle_336_pivot_options.md`). Reasonable but loses the
   compounded streak momentum (38 consecutive axiom-clean §422
   cycles by cycle 372). Probably premature.

This strategy file does NOT bind cycle 373 — it ends at cycle 372's
ship.
