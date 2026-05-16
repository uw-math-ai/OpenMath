# Strategy — cycle 316

## TL;DR

Ship `thm:342C` clause **(342n)** — `B(2s) ∧ E(s, s) ⇒ C(s)` —
as `RKTableau.satisfiesC_of_satisfiesB_satisfiesE` in
`OpenMath/Chapter3/Section321.lean`, the matching Vandermonde-
converse partner of cycle 315's (342p). With (342n) shipped, all
four "purely algebraic" §342C clauses (m, n, o, p) are formalised;
remaining (342j/k/l) are blocked on `thm:314A` elementary-
differential infrastructure and are out of scope.

Single-cycle target, axiom-clean, ~150 LOC. The cycle 315 proof of
(342p) is the structural template: same `Matrix.eq_zero_of_forall_
pow_sum_mul_pow_eq_zero` machinery, same two-sub-sum decomposition,
same Vandermonde injectivity hypothesis on `M.c`, **plus** a new
non-vanishing-weights hypothesis `hb : ∀ i, M.b i ≠ 0`.

No Aristotle results pending. No outstanding sorries. No blockers
from issue files. This is a clean continuation cycle.

---

## §A. Target

`OpenMath.Chapter3.Section312.RKTableau.satisfiesC_of_satisfiesB_satisfiesE`
in `OpenMath/Chapter3/Section321.lean`, immediately after cycle 315's
`satisfiesD_of_satisfiesB_satisfiesE` (currently lines 402–498).

**Statement (Butcher §342, p. 238, clause 342n):**

```lean
/-- *Butcher §342, clause (342n).*

`B(2s) ∧ E(s, s) ⇒ C(s)` — the Vandermonde-converse direction of
clause (342m). For an RK tableau `M` with `s` stages, distinct
abscissae (`Function.Injective M.c`), and non-vanishing weights
(`∀ i, M.b i ≠ 0`), the quadrature condition `B(2s)` together
with the pair condition `E(s, s)` implies the interpolation/
collocation condition `C(s)`.

Textbook proof sketch (Butcher §342, p. 238): Fix the exponent
`k ∈ [1, s]`. Define the C-residual
`u i := ∑ⱼ Aᵢⱼ cⱼ^(k-1) - cᵢ^k / k`.
For every `l ∈ [1, s]`, the weighted Vandermonde sum
`∑ᵢ (bᵢ · u i) · cᵢ^(l-1)` splits as
* (first half, exact-quadrature side) `∑ᵢⱼ bᵢ cᵢ^(l-1) Aᵢⱼ cⱼ^(k-1)`,
  which equals `1 / (k(k+l))` by `E(s, s)` at `(l, k)`.
* (second half, integration side) `(1/k) ∑ᵢ bᵢ cᵢ^(k+l-1)`,
  which equals `1 / (k(k+l))` by `B(2s)` at `k+l` (using `2 ≤ k+l ≤ 2s`).
Their difference is zero, so the matrix `(b · u, V[c])` has zero
column sums for every `l ∈ [1, s]`. Because the abscissae are
distinct, the Vandermonde matrix `(cⱼ^(l-1))_{l, j}` is invertible,
forcing `bᵢ · uᵢ = 0` for every `i`. With non-vanishing weights,
`uᵢ = 0`, i.e. `C(s)` at stage `i` and exponent `k`. -/
theorem satisfiesC_of_satisfiesB_satisfiesE {s : ℕ}
    (M : RKTableau s)
    (hc : Function.Injective M.c)
    (hb : ∀ i : Fin s, M.b i ≠ 0)
    (hB : M.SatisfiesB (2 * s))
    (hE : M.SatisfiesE s s) :
    M.SatisfiesC s
```

---

## §B. Approach — verbatim port of cycle 315 with three changes

Cycle 315's `satisfiesD_of_satisfiesB_satisfiesE` body (lines 405–498
of `Section321.lean`) is the structural template. The three changes:

1. **Residual structure is "per-i" instead of "per-j".** C(s) is
   indexed by stage `i`; D(s) is indexed by stage `j`. Define the
   weighted residual `w` so it sits on the row index `i`:

   ```lean
   set u : Fin s → ℝ := fun i' =>
       (∑ j : Fin s, M.A i' j * M.c j ^ (k - 1))
         - M.c i' ^ k / (k : ℝ)
     with u_def
   set w : Fin s → ℝ := fun i' => M.b i' * u i' with w_def
   ```

2. **Roles of `k` and `l` swap inside `E(s, s)`.** Cycle 315 applied
   `hE k hk1 hk l hl1 hl_le_s` (i.e. the lemma's `k` matched the
   theorem's `k`). Here we need the matrix sum
   `∑ᵢⱼ bᵢ cᵢ^(l-1) Aᵢⱼ cⱼ^(k-1)`, so apply
   `hE l hl1 hl_le_s k hk1 hk` (swap the two Vandermonde exponents).
   The output `1/(k·(l+k))` then matches the (342n) target
   `1/(k·(k+l))` up to `add_comm`, closed by a trailing `ring`.

3. **Final extraction needs `hb`.** After `congrFun hw_zero i` gives
   `w i = 0`, i.e. `M.b i * u i = 0`, use `mul_eq_zero.mp` plus
   `hb i` to extract `u i = 0`:

   ```lean
   have hwi : w i = 0 := congrFun hw_zero i
   simp only [w_def] at hwi
   rcases mul_eq_zero.mp hwi with hbi | hui
   · exact absurd hbi (hb i)
   · simp only [u_def] at hui
     linarith
   ```

   The final `linarith` rearranges `(∑ⱼ Aᵢⱼ cⱼ^(k-1)) - cᵢ^k / k = 0`
   into the C(s) form `∑ⱼ Aᵢⱼ cⱼ^(k-1) = cᵢ^k / k`.

### §B.1. Body skeleton (concrete)

```lean
theorem satisfiesC_of_satisfiesB_satisfiesE {s : ℕ}
    (M : RKTableau s)
    (hc : Function.Injective M.c)
    (hb : ∀ i : Fin s, M.b i ≠ 0)
    (hB : M.SatisfiesB (2 * s)) (hE : M.SatisfiesE s s) :
    M.SatisfiesC s := by
  intro i k hk1 hk
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk1
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  -- Define C-residual u and its b-weighted form w.
  set u : Fin s → ℝ := fun i' =>
      (∑ j : Fin s, M.A i' j * M.c j ^ (k - 1))
        - M.c i' ^ k / (k : ℝ)
    with u_def
  set w : Fin s → ℝ := fun i' => M.b i' * u i' with w_def
  -- Vandermonde inversion: show w = 0.
  have hw_zero : w = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hc ?_
    intro p  -- p : Fin s
    set l : ℕ := p.val + 1 with l_def
    have hl1 : 1 ≤ l := Nat.succ_le_succ (Nat.zero_le _)
    have hl_le_s : l ≤ s := p.isLt
    have hl_pos : 0 < (l : ℝ) := by exact_mod_cast hl1
    have hl_ne : (l : ℝ) ≠ 0 := ne_of_gt hl_pos
    have hkl_real_pos : 0 < (k : ℝ) + (l : ℝ) := by positivity
    have hkl_real_ne : (k : ℝ) + (l : ℝ) ≠ 0 := ne_of_gt hkl_real_pos
    have hp_eq : (p : ℕ) = l - 1 := by simp [l_def]
    rw [hp_eq]
    simp only [w_def, u_def]
    -- (1) first half: ∑ᵢ bᵢ · (∑ⱼ Aᵢⱼ cⱼ^(k-1)) · cᵢ^(l-1) = 1/(k(k+l))
    have h_first :
        (∑ i' : Fin s,
            M.b i' * (∑ j : Fin s, M.A i' j * M.c j ^ (k - 1))
              * M.c i' ^ (l - 1))
          = 1 / ((k : ℝ) * ((k : ℝ) + (l : ℝ))) := by
      -- Reshape factors to match E(s, s)'s shape
      --   bᵢ · cᵢ^(l-1) · Aᵢⱼ · cⱼ^(k-1).
      rw [show (∑ i' : Fin s,
                  M.b i' * (∑ j : Fin s, M.A i' j * M.c j ^ (k - 1))
                    * M.c i' ^ (l - 1))
              = ∑ i' : Fin s, ∑ j : Fin s,
                  M.b i' * M.c i' ^ (l - 1) * M.A i' j * M.c j ^ (k - 1) by
          apply Finset.sum_congr rfl
          intro i' _
          rw [Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring]
      -- E(s, s) at exponents l (outer) and k (inner) gives 1/(k·(l+k)).
      have hE_eval := hE l hl1 hl_le_s k hk1 hk
      rw [hE_eval]
      -- Bridge 1/(k·(l+k)) = 1/(k·(k+l)).
      ring
    -- (2) second half: ∑ᵢ bᵢ · (cᵢ^k / k) · cᵢ^(l-1) = 1/(k(k+l))
    have h_second :
        (∑ i' : Fin s,
            M.b i' * (M.c i' ^ k / (k : ℝ)) * M.c i' ^ (l - 1))
          = 1 / ((k : ℝ) * ((k : ℝ) + (l : ℝ))) := by
      have h_per_i : ∀ i' : Fin s,
          M.b i' * (M.c i' ^ k / (k : ℝ)) * M.c i' ^ (l - 1)
            = (1 / (k : ℝ)) * (M.b i' * M.c i' ^ ((k + l) - 1)) := by
        intro i'
        have h_exp : k + (l - 1) = (k + l) - 1 := by omega
        have h_pow_split : M.c i' ^ k * M.c i' ^ (l - 1)
            = M.c i' ^ ((k + l) - 1) := by
          rw [← pow_add, h_exp]
        rw [← h_pow_split]
        field_simp
      rw [Finset.sum_congr rfl (fun i' _ => h_per_i i')]
      rw [← Finset.mul_sum]
      have hkl_lo : 1 ≤ k + l := by omega
      have hkl_hi : k + l ≤ 2 * s := by omega
      have hB_kl :
          (∑ i' : Fin s, M.b i' * M.c i' ^ ((k + l) - 1))
            = 1 / ((k + l : ℕ) : ℝ) :=
        hB (k + l) hkl_lo hkl_hi
      rw [hB_kl]
      push_cast
      field_simp
    -- Difference of the two sums is zero.
    calc (∑ i' : Fin s,
              M.b i' *
                ((∑ j : Fin s, M.A i' j * M.c j ^ (k - 1))
                  - M.c i' ^ k / (k : ℝ))
                * M.c i' ^ (l - 1))
        = (∑ i' : Fin s,
              M.b i' * (∑ j : Fin s, M.A i' j * M.c j ^ (k - 1))
                * M.c i' ^ (l - 1))
          - ∑ i' : Fin s,
              M.b i' * (M.c i' ^ k / (k : ℝ)) * M.c i' ^ (l - 1) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intros; ring
      _ = 1 / ((k : ℝ) * ((k : ℝ) + (l : ℝ)))
          - 1 / ((k : ℝ) * ((k : ℝ) + (l : ℝ))) := by
            rw [h_first, h_second]
      _ = 0 := by ring
  -- Extract u i = 0 via mul_eq_zero + hb.
  have hwi : w i = 0 := congrFun hw_zero i
  simp only [w_def] at hwi
  rcases mul_eq_zero.mp hwi with hbi | hui
  · exact absurd hbi (hb i)
  · simp only [u_def] at hui
    linarith
```

### §B.2. Verification + naming check

After writing the proof:

* `lake build OpenMath.Chapter3` — expect exit 0.
* `grep -c sorry OpenMath/Chapter3/Section321.lean` — expect 0.
* `#print axioms
   OpenMath.Chapter3.Section312.RKTableau.satisfiesC_of_satisfiesB_satisfiesE` —
   expect `[propext, Classical.choice, Quot.sound]`, matching cycles
   313/314/315 exactly.

---

## §C. Non-vacuity witness

Add immediately after the cycle 315 abstract-route example
(line ~633 of `Section321.lean`):

```lean
/-- Cycle 316 non-vacuity: the canonical Gauss–Legendre 1-stage tableau
satisfies `C(1)` via the abstract bridge
`RKTableau.satisfiesC_of_satisfiesB_satisfiesE`. This re-derives the
existing `gaussLegendre1Stage.SatisfiesC 1` example through the new
(342n) clause, exercising `hc`, `hb`, `hB`, and `hE` together. -/
example : gaussLegendre1Stage.SatisfiesC 1 :=
  gaussLegendre1Stage.satisfiesC_of_satisfiesB_satisfiesE
    (by  -- hc : Function.Injective gaussLegendre1Stage.c
      intro i j _
      fin_cases i; fin_cases j; rfl)
    (by  -- hb : ∀ i, gaussLegendre1Stage.b i ≠ 0
      intro i
      fin_cases i
      simp [gaussLegendre1Stage])
    (by  -- hB (2)
      -- inline if no named lemma exists; mirror the existing
      -- `gaussLegendre1Stage.SatisfiesB 2` example body.
      intro k h1 hk
      interval_cases k <;> simp [gaussLegendre1Stage] <;> norm_num)
    (by  -- hE (1, 1)
      intro k h1 hk l h1' hl
      interval_cases k <;> interval_cases l <;>
        simp [gaussLegendre1Stage] <;> norm_num)
```

**IMPORTANT: verify the exact non-vacuity body** by reading the
existing `gaussLegendre1Stage.SatisfiesB 2`, `SatisfiesC 1`,
`SatisfiesD 1`, `SatisfiesE 1 1` examples in `Section321.lean`
(lines ~561, 567, 572, 578) before writing the cycle 316 example.
The `hc`, `hB`, `hE` blocks should be *copy-paste* from existing
examples, NOT freshly written. If `gaussLegendre1Stage`'s `b 0` is
defined as `1`, the `hb` block reduces to `simp [gaussLegendre1Stage]`
or `exact one_ne_zero` after `fin_cases i`; if `b 0` is some other
non-zero constant, adapt the `simp` set.

**Faithfulness fallback if `simp [gaussLegendre1Stage]` doesn't
reduce `b 0` to a literal:** unfold via `show gaussLegendre1Stage.b
0 ≠ 0` and then `simp` / `norm_num` / `exact one_ne_zero` chain.

---

## §D. What NOT to try (verified pitfalls)

Listed from cycle 315's debugging log plus (342n)-specific risks:

1. **Do NOT add a trailing `ring` after `field_simp` in `h_per_i`.**
   Cycle 315 hit "No goals to be solved" with that pattern. After
   `rw [← h_pow_split]; field_simp` the goal closes cleanly; any
   subsequent tactic fails. Inherited verified pitfall.

2. **Do NOT apply `hE k hk1 hk l hl1 hl_le_s` in `h_first`.** That's
   the cycle 315 order (for the D(s) shape with `cᵢ^(k-1)` outer
   and `cⱼ^(l-1)` inner). For (342n) the shape is *reversed*:
   `cᵢ^(l-1)` outer and `cⱼ^(k-1)` inner. The correct invocation is
   `hE l hl1 hl_le_s k hk1 hk` (swap the two pairs of args).
   Verify by reading the goal after the `show ... = ∑ i' ∑ j, ...`
   rewrite: the matrix sum should be `bᵢ · cᵢ^(l-1) · Aᵢⱼ · cⱼ^(k-1)`.
   If it reads with the swapped exponents, the rewrite failed —
   reread pitfall #5 below.

3. **Do NOT skip the `ring` after `rw [hE_eval]` in `h_first`.**
   `E(s, s)` evaluates to `1/(l·(k+l))` in the lemma's notation,
   which under the variable swap becomes `1/(k·(l+k))`. We need
   `1/(k·(k+l))` — these differ only by `add_comm` on the
   denominator. The trailing `ring` resolves this. If `ring` is
   absent, the proof fails at the calc step where `h_first` is
   substituted.

4. **Do NOT use `mul_eq_zero.elim`.** Use `rcases mul_eq_zero.mp hwi
   with hbi | hui` — the `rcases` form gives named branches the
   `absurd` / `linarith` recipe expects. Equivalent: `obtain hbi |
   hui := mul_eq_zero.mp hwi`.

5. **Do NOT forget the `Finset.sum_mul` / `Finset.mul_sum`
   reordering in `h_first`.** Unlike cycle 315 where the residual
   factored as `b · c^(k-1) · A` (outer factor already on left), in
   (342n) the residual structure is `b · (∑ⱼ A · c^(k-1)) · c^(l-1)`.
   To match `E(s, s)`'s `b · c^(l-1) · A · c^(k-1)` shape requires
   both `Finset.sum_mul` (distribute outer `c^(l-1)` into the
   inner sum) and `Finset.mul_sum` (distribute outer `b · _` into
   the inner sum). The cleanest recipe is the explicit `show ... =
   ∑ i ∑ j, ...; apply Finset.sum_congr rfl; intro i _; rw
   [Finset.sum_mul, Finset.mul_sum]; apply Finset.sum_congr rfl;
   intro j _; ring` block in §B.1.

6. **Do NOT introduce `Function.Injective M.c` via implicit `[…]`
   typeclass syntax.** It's a `Prop`-valued explicit hypothesis,
   not a class. Pass as `(hc : Function.Injective M.c)`, matching
   cycle 315.

7. **Do NOT raise `maxHeartbeats`.** Default is sufficient.
   Decompose into named sub-lemmas if any step times out.

8. **Do NOT update `lean_status.json` for `thm:342C` to
   `formalized`.** Three of seven §342C clauses (j, k, l) remain
   blocked on `thm:314A`. Status stays `partial`.

9. **Do NOT attempt (342j), (342k), or (342l).** Multi-cycle,
   blocked on `thm:314A` / `lem:310B` per
   `.prover-state/issues/lem_310B_plan.md`. Out of scope.

10. **Do NOT add a `0 < s` hypothesis.** At `s = 0` both the C(s)
    `∀ i : Fin 0` quantifier and the Vandermonde `∀ p : Fin 0`
    hypothesis are vacuous, so the proof closes trivially.
    Match cycle 315's signature.

11. **Do NOT use `Finset.sum_sub` (singular).** The Mathlib name
    is `Finset.sum_sub_distrib` (confirmed used twice in cycle 315
    at the difference-of-sums step). Other names (`sub_sum`,
    `Finset.sub_sum`) do not exist.

---

## §E. Faithfulness check (run before commit)

For the new theorem `satisfiesC_of_satisfiesB_satisfiesE`:

* **Entity ID**: `thm:342C`, clause (342n), Butcher §342, p. 238.
* **Textbook statement** (from
  `extraction/formalization_data/entities/thm_342C.json`):
  > `B(2s) ∧ E(s, s) ⇒ C(s)` (342n)
* **Lean statement captures**: **same content**, **plus** two
  extra explicit hypotheses:
  - `Function.Injective M.c` (distinct abscissae — same as cycle
    315 for (342p); Butcher's implicit Vandermonde non-singularity).
  - `∀ i, M.b i ≠ 0` (non-vanishing weights — Butcher's implicit
    "diagonal multiplier is invertible" extension for the converse
    direction of C(s)).
* **Justification for divergence**: Butcher's proof of (342n) says
  "the matrix `(bᵢ cⱼ^{l-1})ᵢⱼ` is non-singular", conjoining two
  conditions: distinct abscissae (Vandermonde core) and
  non-vanishing weights (diagonal multiplier). We surface both
  explicitly. The Gauss–Legendre tableau satisfies both via cycle
  302's `butcherShiftedLegendre_zeros_strictMono` (injectivity) and
  cycle 305's `butcherShiftedLegendre_quadratureWeights_pos`
  (positivity ⇒ non-vanishing).
* **Tautology check**: ✓ Conclusion `M.SatisfiesC s` does NOT
  appear among hypotheses.
* **Identity check**: ✓ Proof is substantive (~140 LOC) including
  a Vandermonde inversion, two named sub-sums (`h_first`,
  `h_second`), and the `mul_eq_zero` extraction.
* **Definition smuggling**: ✓ No new defs/structures.
* **Hypothesis strength**: All four hypotheses minimal. `B(2s)` at
  `k+l ∈ [2, 2s]`. `E(s, s)` at all `(l, k) ∈ [1, s]²`.
  `Function.Injective M.c` required for Vandermonde invertibility.
  `∀ i, M.b i ≠ 0` required to extract `u i = 0` from
  `bᵢ · u i = 0`. None can be weakened.
* **Absent theorem check**: N/A.

For the non-vacuity `example`: standard pattern; verify the cited
existing `gaussLegendre1Stage.SatisfiesB 2` / `SatisfiesE 1 1`
example bodies exist at HEAD (lines ~561, 578) before consuming.

---

## §F. Housekeeping after the theorem lands

1. **`plan.md` — `thm:342C` row update**: append one sentence to the
   existing cycle 315 paragraph:

   > Cycle 316 ships the matching converse clause (342n)
   > `B(2s) ∧ E(s, s) ⇒ C(s)` as
   > `RKTableau.satisfiesC_of_satisfiesB_satisfiesE` — same
   > Vandermonde-inversion recipe as (342p) with an additional
   > `∀ i, M.b i ≠ 0` hypothesis surfacing Butcher's implicit
   > diagonal-multiplier non-singularity. All four "purely
   > algebraic" §342C clauses (342m, 342n, 342o, 342p) now shipped;
   > the remaining G(2s) clauses (342j/k/l) remain blocked on
   > `thm:314A`.

2. **`plan.md` — `cor:342D` row update**: append one line to the
   existing cycle 315 paragraph noting (342n) is now shipped, with
   the same "still requires G(2s) clauses blocked on thm:314A"
   caveat. Do NOT mark `cor:342D` as formalized.

3. **`lean_status.json` — `thm:342C` row**: keep status `partial`;
   update `cycle_last_modified` to 316; update notes to reflect
   (342n) closure (all four purely-algebraic clauses shipped).

4. **`task_results/cycle_316.md`**: standard template (Worked on /
   Approach / Result / Faithfulness check / Dead ends / Discovery /
   Suggested next approach), citing
   `satisfiesC_of_satisfiesB_satisfiesE` as the headline.

5. **Commit message**: `Cycle 316 — §342 thm:342C clause (342n):
   Vandermonde converse B(2s) ∧ E(s,s) ⇒ C(s).`

---

## §G. Suggested cycle 317+ outlook

With (342m/n/o/p) all formalised, the next single-cycle targets in
order of leverage:

1. **`thm:344A` Radau and Lobatto methods** (§344). Concrete
   tableau constructions analogous to cycle 308's
   `butcherGaussLegendreRK`. Likely 2–3 cycles for the Radau IA/IIA
   and Lobatto IIIA/IIIB/IIIC families. Independent of `thm:314A`.
2. **`lem:359A` V and W transformations** (§359). Single named
   transformation lemmas; downstream §357/§358 unlock.
3. **`lem:351A` / `thm:351B` A-stability criteria** (§351). Verify
   Mathlib's `Polynomial.IsRoot` plumbing first.
4. **Pivot to Chapter 4 §441 `lem:441A` Phase C** per
   `.prover-state/issues/lem_441A_phase_C_scoping.md`. Multi-cycle
   but incremental.

The cycle 317 planner should re-check `lem_310B_plan.md` to see
whether any Phase A.3 / Phase B work has been freelanced in
intervening cycles, and pick a path that doesn't duplicate effort.

---

## §H. Abort threshold

* **Soft abort (ship partial)**: if the manual proof exceeds ~3
  hours of focused work or hits ~250 LOC without closure, ship a
  no-op cycle 316 (no new theorems, task results documenting the
  stall). Do NOT introduce `sorry`; the cycle 200/201 rollback
  precedent forbids sorry-first scaffolds without single-cycle
  close.
* **Hard abort (rollback)**: if three structured attempts fail to
  compile, revert Section321.lean, preserve the draft at
  `.prover-state/cycle_316_draft.lean`, and document the dead end
  in `.prover-state/issues/thm_342C_clause_342n_stall.md`.

Neither is anticipated. Cycle 315 closed (342p) in a single cycle
with essentially identical structure; (342n) adds only the
`mul_eq_zero` extraction (~5 LOC) and the `Finset.sum_mul` /
`Finset.mul_sum` reorder in `h_first` (~10 LOC). Target: ~150 LOC,
single cycle, axiom-clean.
