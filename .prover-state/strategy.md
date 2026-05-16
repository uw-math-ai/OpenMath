# Cycle 315 Strategy

## TL;DR

Ship `thm:342C` clause **(342p)** `B(2s) ∧ E(s, s) ⇒ D(s)` in
`OpenMath/Chapter3/Section321.lean` — the structural converse of
cycle 314's clause (342o). This is the **first Vandermonde-converse**
clause and unlocks the bidirectional B+E ⇔ D portion of the §342C
algebraic toolkit. Aim for ~130–160 LOC, axiom-clean.

## Why this target

Cycle 314 task results explicitly recommended the Vandermonde-converse
pair (342n)+(342p) as the highest-strategic-value next step. Reading
the four-option menu in the task results §"Suggested next approach":

* (1) **Vandermonde converses (342n)/(342p)** — recommended primary;
  builds the inversion infrastructure for the §342C iff.
* (2) `thm:344A` Radau/Lobatto — multi-cycle, premature without (1).
* (3) `cor:359B`/`lem:359A` — likely multi-cycle and dependency-heavy.

**Key discovery this strategy session**: Mathlib's
`Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero`
(`.lake/packages/mathlib/Mathlib/LinearAlgebra/Vandermonde.lean:258`)
delivers Vandermonde non-singularity directly:

```
theorem eq_zero_of_forall_pow_sum_mul_pow_eq_zero [IsDomain R]
    {f v : Fin n → R} (hf : Function.Injective f)
    (hfv : ∀ i : Fin n, (∑ j : Fin n, v j * f j ^ (i : ℕ)) = 0) :
    v = 0
```

This is **exactly** what (342p) needs after a routine algebraic
manipulation. The cycle 314 worker's ~150-LOC-each estimate was made
without knowing about this helper; with it, (342p) closes in ~130 LOC.

## Why (342p) before (342n)

Both clauses use the same Vandermonde inversion, but they differ in
side hypotheses:

* **(342p) `B(2s) ∧ E(s, s) ⇒ D(s)`**: needs only
  `Function.Injective M.c` (distinct abscissae). The Vandermonde
  matrix is `(c_j^{l-1})_{l,j}`, non-singular iff `c_j` distinct.
* **(342n) `B(2s) ∧ E(s, s) ⇒ C(s)`**: needs **both**
  `Function.Injective M.c` AND `∀ i, M.b i ≠ 0`. The Vandermonde
  appears as `diag(b) · V`, requiring both factors invertible.

Ship (342p) first as the cleaner single-cycle deliverable. (342n)
is cycle 316's target.

## Target (P1, mandatory)

**Theorem name**: `satisfiesD_of_satisfiesB_satisfiesE`
in namespace `OpenMath.Chapter3.Section312.RKTableau`, inserted in
`OpenMath/Chapter3/Section321.lean` immediately after cycle 314's
`satisfiesE_of_satisfiesB_satisfiesD` block.

**Signature**:

```lean
theorem satisfiesD_of_satisfiesB_satisfiesE {s : ℕ}
    (M : RKTableau s) (hc : Function.Injective M.c)
    (hB : M.SatisfiesB (2 * s)) (hE : M.SatisfiesE s s) :
    M.SatisfiesD s
```

**New import** to add at top of `Section321.lean`:
`import Mathlib.LinearAlgebra.Vandermonde`

## Required side hypothesis: `Function.Injective M.c`

Butcher §342's textbook proof says "the matrix multiplier is non-
singular" — implicitly assuming distinct abscissae. In our Lean
formalisation we surface this explicitly as a hypothesis. Document
it in the docstring as a faithfulness note.

The canonical Gauss-Legendre tableau satisfies `Function.Injective M.c`
automatically (cycle 302's `butcherShiftedLegendre_zeros_strictMono`
+ `StrictMono.injective`). The 1-stage `gaussLegendre1Stage` consumer
discharges injectivity vacuously by `fin_cases`.

## Proof recipe (~130 LOC)

Structure:

### Step 0 — outer intro and goal setup

```lean
intro j k hk1 hk
have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk1
have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
```

### Step 1 — define the residual vector `v : Fin s → ℝ`

`v j' := (∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ') − (bⱼ'/k)(1 − cⱼ'^k)` (the D(s)
residual at exponent k, indexed by stage j').

```lean
set v : Fin s → ℝ := fun j' =>
    (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j')
      - (M.b j' / (k : ℝ)) * (1 - M.c j' ^ k)
  with v_def
```

### Step 2 — prove `v = 0` via Vandermonde

```lean
have hv_zero : v = 0 := by
  refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hc ?_
  intro i  -- i : Fin s
  set l : ℕ := i.val + 1
  have hl1 : 1 ≤ l := Nat.succ_le_succ (Nat.zero_le _)
  have hl_le_s : l ≤ s := i.isLt
  have hl_pos : 0 < (l : ℝ) := by exact_mod_cast hl1
  have hl_ne : (l : ℝ) ≠ 0 := ne_of_gt hl_pos
  have hkl_pos : 0 < (k : ℝ) + (l : ℝ) := by positivity
  have hkl_ne : (k : ℝ) + (l : ℝ) ≠ 0 := ne_of_gt hkl_pos
  -- Goal: ∑ j' : Fin s, v j' * M.c j' ^ (i : ℕ) = 0
  -- Use l - 1 = i.val:
  have hi_eq : (i : ℕ) = l - 1 := by omega
  rw [hi_eq]
  -- Now: ∑ j' : Fin s, v j' * M.c j' ^ (l - 1) = 0
  simp only [v_def]
  -- ... see Step 3 below ...
```

### Step 3 — the analytic core

The mathematics:

```
∑ⱼ' v(j') · c_j'^{l-1}
  = ∑ⱼ' c_j'^{l-1} · (∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ' − (bⱼ'/k)(1 − cⱼ'^k))
  = [first term] − [second term]
  first  = ∑ᵢⱼ' bᵢ cᵢ^{k-1} aᵢⱼ' c_j'^{l-1}    [sum-swap]
         = 1/(l(k+l))                            [by hE (k, l)]
  second = (1/k) (∑ⱼ' bⱼ' c_j'^{l-1} − ∑ⱼ' bⱼ' c_j'^{k+l-1})
         = (1/k) (1/l − 1/(k+l))                 [by hB at l and k+l]
         = 1/(l(k+l))                            [arithmetic]
  Difference = 0.
```

Recommended factoring into two named `have` steps:

```lean
have h_first :
    (∑ j' : Fin s,
        (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j') * M.c j' ^ (l - 1))
      = 1 / ((l : ℝ) * ((k : ℝ) + (l : ℝ))) := by
  -- Pull c j'^(l-1) inside the inner sum, then swap sums, then apply hE.
  have h_pull :
      (fun j' : Fin s =>
        (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j') * M.c j' ^ (l - 1))
      = (fun j' : Fin s =>
        ∑ i : Fin s,
          M.b i * M.c i ^ (k - 1) * M.A i j' * M.c j' ^ (l - 1)) := by
    funext j'
    rw [Finset.sum_mul]
  rw [show (∑ j' : Fin s,
            (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j') * M.c j' ^ (l - 1))
         = ∑ j' : Fin s,
             ∑ i : Fin s,
               M.b i * M.c i ^ (k - 1) * M.A i j' * M.c j' ^ (l - 1)
       from by congr 1; exact h_pull]
  rw [Finset.sum_comm]
  exact hE k hk1 hk l hl1 hl_le_s

have h_second :
    (∑ j' : Fin s,
        (M.b j' / (k : ℝ)) * (1 - M.c j' ^ k) * M.c j' ^ (l - 1))
      = 1 / ((l : ℝ) * ((k : ℝ) + (l : ℝ))) := by
  -- Per-j' rewrite: factor (1/k), then split via (1 − c^k) · c^(l-1).
  have h_per_j : ∀ j' : Fin s,
      (M.b j' / (k : ℝ)) * (1 - M.c j' ^ k) * M.c j' ^ (l - 1)
        = (1 / (k : ℝ)) *
            (M.b j' * M.c j' ^ (l - 1) - M.b j' * M.c j' ^ ((k + l) - 1)) := by
    intro j'
    have h_exp : k + (l - 1) = (k + l) - 1 := by omega
    have h_pow_split : M.c j' ^ k * M.c j' ^ (l - 1)
        = M.c j' ^ ((k + l) - 1) := by
      rw [← pow_add, h_exp]
    field_simp
    linear_combination
      -- The identity is `(b/k)·(1 - c^k)·c^(l-1) = (1/k)·(b·c^(l-1) - b·c^(k+l-1))`.
      -- After field_simp the goal will be a polynomial identity that
      -- `ring` closes given h_pow_split. If `linear_combination` is
      -- tricky to invoke, use `rw [← h_pow_split]; ring` instead.
      sorry
  -- Apply h_per_j inside the sum, distribute (1/k), apply hB twice.
  rw [Finset.sum_congr rfl (fun j' _ => h_per_j j')]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have hB_l :
      (∑ j' : Fin s, M.b j' * M.c j' ^ (l - 1)) = 1 / (l : ℝ) := by
    have := hB l hl1 (by omega)
    convert this
  have hB_kl :
      (∑ j' : Fin s, M.b j' * M.c j' ^ ((k + l) - 1))
        = 1 / ((k : ℝ) + (l : ℝ)) := by
    have h := hB (k + l) (by omega) (by omega)
    push_cast at h
    convert h using 2
  rw [hB_l, hB_kl]
  -- Goal: (1 / k) * (1 / l - 1 / (k + l)) = 1 / (l * (k + l))
  field_simp
  ring

-- Combine h_first and h_second.
calc (∑ j' : Fin s,
        ((∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j')
          - (M.b j' / (k : ℝ)) * (1 - M.c j' ^ k)) * M.c j' ^ (l - 1))
    = (∑ j' : Fin s,
        (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j') * M.c j' ^ (l - 1))
      - (∑ j' : Fin s,
        (M.b j' / (k : ℝ)) * (1 - M.c j' ^ k) * M.c j' ^ (l - 1)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intros; ring
  _ = 1 / ((l : ℝ) * ((k : ℝ) + (l : ℝ)))
      - 1 / ((l : ℝ) * ((k : ℝ) + (l : ℝ))) := by rw [h_first, h_second]
  _ = 0 := by ring
```

### Step 4 — extract `v j = 0` and rearrange to D(s)

```lean
have hvj : v j = 0 := congrFun hv_zero j
simp only [v_def] at hvj
linarith
```

**Note**: `v_def` is the `with v_def` artifact from `set`. If you
forget that, use `show v j = 0` and unfold manually.

## Non-vacuity (P2, mandatory after P1 lands)

Add an `example` exercising the new theorem on `gaussLegendre1Stage`,
mirroring cycle 313/314's pattern:

```lean
example : RKTableau.gaussLegendre1Stage.SatisfiesD 1 := by
  apply RKTableau.satisfiesD_of_satisfiesB_satisfiesE
  · -- Function.Injective gaussLegendre1Stage.c (vacuous at s = 1)
    intro i j _
    fin_cases i; fin_cases j; rfl
  · -- gaussLegendre1Stage.SatisfiesB 2
    intro k h1 hk
    interval_cases k <;>
      (simp [RKTableau.SatisfiesB, gaussLegendre1Stage]; norm_num)
  · -- gaussLegendre1Stage.SatisfiesE 1 1
    intro k h1 hk l hl1 hl
    interval_cases k; interval_cases l
    simp [RKTableau.SatisfiesE, gaussLegendre1Stage]; norm_num
```

The `Function.Injective` clause is vacuously true at `s = 1` since
both `i` and `j` reduce to `(0 : Fin 1)` and `rfl` closes. The B(2)
and E(1,1) witnesses are pattern-match with cycle 313/314's
analogous examples — same `simp`/`norm_num` recipe.

## Stretch (P3, only if P1+P2 close in <120 minutes)

Ship clause **(342n)** `B(2s) ∧ E(s, s) ⇒ C(s)` with additional
hypothesis `(hb : ∀ i, M.b i ≠ 0)`. Structurally identical: define
`v i := M.b i * (residual_C i k)`, apply the same Vandermonde
lemma, then divide by `M.b i` to extract the C(s) residual = 0.

Faithfulness note for (342n): the `b nonzero` hypothesis is NOT
explicit in Butcher §342 — Butcher implicitly assumes non-vanishing
weights. Cycle 305's `butcherShiftedLegendre_quadratureWeights_pos`
confirms this for the canonical Gauss-Legendre tableau. Document
the divergence clearly in the docstring.

**Do NOT attempt P3 unless P1+P2 close cleanly and quickly.** Pushing
to 250+ LOC in one cycle risks elaboration stalls (cf. cycle 166's
Section454 monolithic-proof timeout). Better to ship (342p) clean
than to land a partial (342n).

## What NOT to try

* **Do NOT reprove Vandermonde non-singularity from scratch.**
  Mathlib's `eq_zero_of_forall_pow_sum_mul_pow_eq_zero` is the
  intended shortcut. Path A from cycle 314's task results explicitly
  anticipates "non-singular Vandermonde-style matrix argument"; this
  Mathlib lemma IS that argument, packaged.

* **Do NOT use `eq_zero_of_forall_index_sum_pow_mul_eq_zero`**
  (the swapped variant). Our setup has the residual `v` multiplied
  by `c^{l-1}` on the right; the `_pow_sum_mul_pow_` version matches
  this shape:
  `∀ i : Fin n, (∑ j : Fin n, v j * f j ^ (i : ℕ)) = 0 → v = 0`.

* **Do NOT try to invert cycle 313's (342m) proof "backwards".**
  That proof builds E(s,s) FROM C(s); it doesn't invert. The
  Vandermonde argument is the genuinely new piece.

* **Do NOT add a `0 < s` hypothesis.** At `s = 0`, the universally
  quantified `∀ j : Fin 0, ∀ k, …` is vacuous and the theorem holds
  trivially. Matches cycle 313/314 signatures.

* **Do NOT freelance to (342n) before (342p) closes.** P3 is
  explicitly gated on P1+P2 success.

* **Do NOT submit to Aristotle for the analytic step.** This is
  routine algebra with named Mathlib hooks; manual proof is faster
  than Aristotle round-trip. Aristotle is for genuinely hard
  searches; this is not one.

* **Do NOT split (342p) into a "Phase 1 statement-only scaffold"
  and a "Phase 2 closure".** The cycle 200/201 / 149/150 rollback
  precedents make sorry-first scaffolds unacceptable when single-
  cycle closure is feasible — and per the Mathlib-helper discovery
  above, single-cycle closure IS feasible here.

## Common pitfalls (verified in cycles 311–314)

1. **Inner `field_simp` may close the goal alone.** Cycle 314 hit
   "No goals" after `field_simp` followed by an unneeded `ring`.
   If you see that error, just remove the trailing `ring`.

2. **`push_cast` is needed before `field_simp`** to normalise
   `((k + l : ℕ) : ℝ)` to `(k : ℝ) + (l : ℝ)`. Without it,
   `field_simp` may not recognise `(k + l) ≠ 0` correctly.

3. **`Finset.sum_comm` works for `∑ᵢ ∑ⱼ → ∑ⱼ ∑ᵢ`** over
   `Finset.univ × Finset.univ`. No primed variant needed.

4. **`set` artifacts**: `set v := expr with v_def` creates a
   hypothesis `v_def : v = expr`. To unfold `v` later, use
   `simp only [v_def]` or `show` reframing. **A bare `set v := expr`
   without `with` does NOT create the hypothesis** — easy mistake.

5. **`Mathlib.LinearAlgebra.Vandermonde` is NOT transitively imported**
   by `Mathlib.Algebra.BigOperators.Fin` or by the `Section312` chain.
   Explicit `import` line needed at the top of `Section321.lean`.

6. **Pow arithmetic `c^k · c^(l-1) = c^((k+l)-1)`** needs care:
   `← pow_add` gives `c^(k + (l-1))`, then `omega` shows
   `k + (l - 1) = (k + l) - 1` (using `1 ≤ l`). Lean's Nat-subtraction
   is truncating, so `omega` is the right tactic to verify the
   identity, not `ring`.

7. **`Finset.sum_sub_distrib`** is the canonical name in current
   Mathlib (NOT `Finset.sum_sub` or `sub_sum`). It's at
   `Mathlib.Algebra.BigOperators.Basic` and transitively imported.

## Verification checklist (run at end of cycle)

1. `lake env lean OpenMath/Chapter3/Section321.lean` exits 0.
2. `lake build OpenMath.Chapter3` (full chapter) exits 0.
3. `grep -c sorry OpenMath/Chapter3/Section321.lean` returns 0.
4. `#print axioms
   OpenMath.Chapter3.Section312.RKTableau.satisfiesD_of_satisfiesB_satisfiesE`
   returns `[propext, Classical.choice, Quot.sound]` only.
5. Cycle 313/314 regression check: `#print axioms` on
   `satisfiesE_of_satisfiesB_satisfiesC` and
   `satisfiesE_of_satisfiesB_satisfiesD` returns the same axiom set
   (no regression).

## Faithfulness check (mandatory per CLAUDE.md)

`satisfiesD_of_satisfiesB_satisfiesE`:

* **Textbook entity**: `thm:342C` clause (342p), Butcher §342, p. 238.
* **Statement quoted from
  `extraction/formalization_data/entities/thm_342C.json`**:
  > `B(2s) \land E(s, s) \Rightarrow D(s)`     (342p)
* **Lean statement captures**: same content, **plus** the extra
  hypothesis `Function.Injective M.c` (distinct abscissae).
* **Faithfulness divergence**: the textbook implicitly assumes
  distinct abscissae via "the matrix multiplier is non-singular";
  we surface this explicitly. The Gauss-Legendre tableau satisfies
  injectivity automatically (cycle 302), so downstream consumers
  are unaffected. Document in the theorem docstring.
* **Tautology check**: ✓ Conclusion `M.SatisfiesD s` does NOT appear
  among hypotheses (B and E are distinct §321 predicates).
* **Identity check**: ✓ Proof is substantive (~130 LOC) including
  a Vandermonde-inversion appeal and two-step algebraic factoring;
  not `exact h_*`.
* **Definition smuggling check**: ✓ No new defs/structures; consumes
  §321's existing B/D/E predicates (audited cycle 306).
* **Hypothesis strength check**: All four hypotheses are minimal:
  `B(2s)` used at exponents `l` and `k+l` (both ≤ 2s);
  `E(s, s)` used at all `(k, l) ∈ [1, s]²`; `Function.Injective M.c`
  required for the Vandermonde matrix to be invertible. None can
  be weakened.
* **Absent theorem check**: N/A — no comments promising deferred
  content.

## Cycle structure suggestion

* **0–25 min**: Read this strategy. Verify the Mathlib Vandermonde
  lemma signature with `lean_local_search` or by reading
  `.lake/packages/mathlib/Mathlib/LinearAlgebra/Vandermonde.lean:258`.
  Add the `import Mathlib.LinearAlgebra.Vandermonde` line.

* **25–60 min**: Shape the proof skeleton (Steps 0/1/2/4 + the
  `hv_zero` outer structure with `h_first` and `h_second` left as
  named `sorry`s initially). Confirm the file still compiles with
  the two sorries.

* **60–110 min**: Fill `h_first` (sum-swap + hE application). Should
  be the easier of the two — ~25 LOC.

* **110–160 min**: Fill `h_second` (per-`j'` rewrite + hB twice +
  arithmetic). Harder — ~50 LOC. The `linear_combination` in the
  per-`j'` rewrite may need to be replaced with explicit
  `rw [← h_pow_split]; ring` if `linear_combination` doesn't fire.

* **160–175 min**: P2 non-vacuity example on `gaussLegendre1Stage`.

* **175–195 min**: Faithfulness check + axiom check + commit message
  + push.

If you blow past 195 min on the analytic core, **extract sub-results
as private named helpers** rather than inlining. Cycle 166→167 lesson:
extraction beats monolithic proofs when elaboration stalls.

## Cycle 316+ outlook

* **Cycle 316**: ship (342n) `B(2s) ∧ E(s, s) ⇒ C(s)` using the
  same Vandermonde recipe + the extra `b i ≠ 0` hypothesis. With
  (342p) in hand as a template, this is a guaranteed single-cycle
  ship (~150 LOC).

* **Cycle 317+**: pivot to one of:
  - **`thm:344A` Radau/Lobatto methods** — concrete-tableau ship,
    consumes the full §321 B/C/D/E toolkit.
  - **`thm:342C` G(2s) clauses (342j)/(342k)/(342l)** — blocked on
    `thm:314A` elementary-differential infrastructure
    (see `lem_310B_plan.md`); multi-cycle.
  - **`lem:359A`** (V and W transformations) — first user of
    `lem:342A`/`lem:342B` outside the direct §342 chain.

The planner for cycle 316 will revisit this list once (342p) lands.
