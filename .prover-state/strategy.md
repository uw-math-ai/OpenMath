# Cycle 333 Strategy — §344 Phase D.13: Lobatto IIIA `s = 3` collocation-form `RKTableau` + coincidence theorem

## A. Context

Cycle 332 closed cleanly. `Section344.lean` is 2273 LOC, sorry count 0,
axiom-clean, no pending Aristotle results. The cycle 332 task results
recommended option 1 (mechanical port to Lobatto IIIA `s = 3`); this
strategy executes that recommendation.

The §344 small-`s` ladder is now structured as follows (after cycle 332):

| `s` | family       | direct-form          | collocation-form         | coincidence shipped? |
|-----|--------------|----------------------|--------------------------|----------------------|
| 1   | Radau IA     | `butcherForwardEulerRK` | `butcherRadauIA_one`     | yes (cycle 325)      |
| 1   | Radau IIA    | `butcherBackwardEulerRK` | `butcherRadauIIA_one`    | yes (cycle 322)      |
| 2   | Lobatto IIIA | `butcherTrapezoidalRK` | `butcherLobattoIIIA_two` | yes (cycle 323)      |
| 2   | Radau I (C(s))   | `butcherRadauIDirect_two` | `butcherRadauI_collocation_two` | yes (cycle 332) |
| 2   | Radau IIA    | `butcherRadauIIADirect_two` | `butcherRadauIIA_two` | yes (cycle 324)      |
| 2   | Radau I (reflections) | `butcherRadauIADirect_two` | none (divergent) | n/a (cycle 326)  |
| 2   | Radau II (D(s)) | `butcherRadauIIDirect_two` | none (divergent) | n/a (cycle 328) |
| 2   | Lobatto IIIC | `butcherLobattoIIICDirect_two` | none (divergent) | n/a (cycle 330) |
| 2   | Lobatto III  | `butcherLobattoIIIDirect_two` | none (divergent) | n/a (cycle 331) |
| 3   | Lobatto IIIB | `butcherLobattoIIIBDirect_three` | none (divergent) | n/a (cycle 327) |
| 3   | Lobatto IIIA | **MISSING**          | **MISSING**              | **cycle 333 target** |

Cycle 333 fills the missing `s = 3` Lobatto IIIA row. Per Butcher
Table 344(I) line "Lobatto IIIA — Lobatto quadrature — C(s)", this is
a C(s)-family entry and will coincide with plain Lagrange collocation
at the Lobatto nodes `(0, 1/2, 1)` — exactly the cycle 332 template
applied to a 3-leaf tree. All prerequisite infrastructure is in place:

* `butcherLobatto_zeros_three` (cycle 320) — abscissae `(0, 1/2, 1)`.
* `butcherLobatto_quadratureWeights_three` (cycle 321) — weights
  `(1/6, 2/3, 1/6)` (Simpson's rule).
* `butcherLobatto_quadratureWeights_three_apply_{zero,one,two}` —
  closed-form evaluations of each weight (Section344.lean lines
  1024–1125).
* Lagrange basis evaluations at `(0, 1/2, 1)` are already worked out
  inside the cycle 321 weight proofs:
  - `L_0(x) = 2x² − 3x + 1` (lines 1030–1038)
  - `L_1(x) = −4x² + 4x` (lines 1068–1076)
  - `L_2(x) = 2x² − x` (lines 1103–1111)

## B. Deliverables (Priority 1 = ship; Priority 2 = stretch)

### B.1 P1 — `butcherLobatto_collocationA_three` definition

```lean
/-- The 3-stage Lobatto IIIA collocation A-matrix.
For each `(i, j)`, the entry is the Lagrange-collocation integral
`∫₀^{c_i} L_j(x) dx` evaluated at the Lobatto abscissae
`c = (0, 1/2, 1)` with Lagrange basis `L_0, L_1, L_2`. -/
noncomputable def butcherLobatto_collocationA_three
    (i j : Fin 3) : ℝ :=
  ∫ x in (0 : ℝ)..butcherLobatto_zeros_three i,
    (Lagrange.basis Finset.univ butcherLobatto_zeros_three j).eval x
```

Place immediately after cycle 332's `butcherRadauI_collocation_two_eq_direct`
(currently the last declaration, line ~2273) inside the
`OpenMath.Chapter3.Section344` namespace.

### B.2 P1 — Nine `_apply` evaluation theorems

Closed-form values per Butcher Table 344(I) "Lobatto IIIA `s = 3`":

```
A = !![ 0,     0,     0   ;
        5/24,  1/3,  -1/24;
        1/6,   2/3,   1/6 ]
```

Theorem signatures (name pattern matches cycles 323/324/332):

```lean
butcherLobatto_collocationA_three_apply_zero_zero  : ... = 0
butcherLobatto_collocationA_three_apply_zero_one   : ... = 0
butcherLobatto_collocationA_three_apply_zero_two   : ... = 0
butcherLobatto_collocationA_three_apply_one_zero   : ... = 5/24
butcherLobatto_collocationA_three_apply_one_one    : ... = 1/3
butcherLobatto_collocationA_three_apply_one_two    : ... = -1/24
butcherLobatto_collocationA_three_apply_two_zero   : ... = 1/6
butcherLobatto_collocationA_three_apply_two_one    : ... = 2/3
butcherLobatto_collocationA_three_apply_two_two    : ... = 1/6
```

**Proof recipes by row** (port from existing templates):

* **Row 0 (3 theorems, ~6 LOC each)**: identical to cycle 323's
  `butcherLobatto_collocationA_two_apply_zero_*` (lines 1263–1280).
  `unfold` + `show` + `simp [butcherLobatto_zeros_three,
  intervalIntegral.integral_same]`. The upper limit collapses to
  `c_0 = 0` so the integrand is irrelevant.

* **Row 1 (3 theorems, ~50–65 LOC each — the substantive work)**:
  Port from cycle 324's
  `butcherRadauII_collocationA_two_apply_one_*` (lines 1501–1574,
  the `c_i = 1/3` template). Pattern:
  1. `unfold butcherLobatto_collocationA_three`, `show` the
     integral form.
  2. `h_erase`: `(Finset.univ : Finset (Fin 3)).erase ⟨j, _⟩ =
     {two-element set}` via `decide`.
  3. `h_ne`: pairwise inequality of the two remaining indices via
     `decide`.
  4. `h_eval`: the basis polynomial evaluation — **reuse the
     closed forms from cycle 321 verbatim** (lines 1030–1038 for
     `L_0`, 1068–1076 for `L_1`, 1103–1111 for `L_2`). Each goes
     `rw [Lagrange.basis, h_erase, Finset.prod_pair h_ne,
     Polynomial.eval_mul, Lagrange.basisDivisor, Lagrange.basisDivisor] +
     simp [butcherLobatto_zeros_three, eval_*] + ring`.
  5. `simp_rw [h_eval]` to substitute the polynomial closed form
     into the integrand.
  6. `show ∫ x in (0:ℝ)..butcherLobatto_zeros_three ⟨1,_⟩, <poly> = <value>`.
  7. `have h_c1 : butcherLobatto_zeros_three ⟨1, by omega⟩ = 1/2 := rfl`.
  8. `rw [h_c1]`.
  9. Integrability witnesses on `[0, 1/2]`:
     ```lean
     have hi_x : IntervalIntegrable (fun x : ℝ => x)
         MeasureTheory.volume 0 (1/2) :=
       continuous_id.intervalIntegrable 0 (1/2)
     have hi_x2 : IntervalIntegrable (fun x : ℝ => x ^ 2)
         MeasureTheory.volume 0 (1/2) :=
       (continuous_pow 2).intervalIntegrable 0 (1/2)
     ```
  10. Compute the two pivotal integrals over `[0, 1/2]`:
      ```lean
      have hx : ∫ x in (0 : ℝ)..(1/2), x = 1 / 8 := by
        have hp1 := integral_pow (a := (0 : ℝ)) (b := 1/2) 1
        simp only [pow_one, Nat.cast_one] at hp1
        rw [hp1]; norm_num
      have hx2 : ∫ x in (0 : ℝ)..(1/2), x ^ 2 = 1 / 24 := by
        rw [integral_pow]; norm_num
      ```
  11. Split via `intervalIntegral.integral_add` / `_sub` /
      `_const_mul` (the exact splits depend on the polynomial —
      `2x² − 3x + 1` needs add+sub+sub+const, `−4x² + 4x` needs
      add+const_mul+const_mul, `2x² − x` needs sub+const_mul+id);
      close with `hx2`, `hx`, and `norm_num`.

  **Hint**: the row-1 cycle 321 weight proofs (Section344.lean lines
  1024–1125) use the exact same simp recipes on `[0, 1]`; port them
  with `1 → 1/2` and adjust the final arithmetic values
  (`1/2 → 1/8` for `∫ x`, `1/3 → 1/24` for `∫ x²`).
  Expected values per linearity:
  - `∫₀^(1/2) (2x² − 3x + 1) = 2·(1/24) − 3·(1/8) + (1/2)
                              = 1/12 − 3/8 + 1/2 = 5/24` ✓
  - `∫₀^(1/2) (−4x² + 4x) = −4·(1/24) + 4·(1/8)
                          = −1/6 + 1/2 = 1/3` ✓
  - `∫₀^(1/2) (2x² − x) = 2·(1/24) − (1/8)
                        = 1/12 − 1/8 = −1/24` ✓

* **Row 2 (3 theorems, ~10–30 LOC each — alias route first, port
  as fallback)**: The collocation integral at `c_2 = 1` IS the
  quadrature weight integral by definition. **Try the alias route
  first:**
  ```lean
  theorem butcherLobatto_collocationA_three_apply_two_zero :
      butcherLobatto_collocationA_three ⟨2, by omega⟩ ⟨0, by omega⟩ = 1 / 6 := by
    unfold butcherLobatto_collocationA_three
    show ∫ x in (0 : ℝ)..butcherLobatto_zeros_three ⟨2, by omega⟩,
        (Lagrange.basis Finset.univ butcherLobatto_zeros_three
            ⟨0, by omega⟩).eval x = 1 / 6
    have h_c2 : butcherLobatto_zeros_three ⟨2, by omega⟩ = 1 := rfl
    rw [h_c2]
    -- Goal: ∫ x in (0:ℝ)..1, L_0(x) = 1/6
    -- This is definitionally `butcherLobatto_quadratureWeights_three ⟨0, _⟩`
    -- (with `c_2 = 1` substituted). The weight `_apply_zero` proves the same
    -- integral = 1/6, so reuse it.
    exact butcherLobatto_quadratureWeights_three_apply_zero
  ```
  If `exact` doesn't unify (because `butcherLobatto_quadratureWeights_three`'s
  unfolded body has `1` literally vs the post-`rw` goal having
  `1`), try `show butcherLobatto_quadratureWeights_three ⟨0, by omega⟩ = 1/6;
  exact butcherLobatto_quadratureWeights_three_apply_zero` after the
  `rw [h_c2]`.

  **Fallback** (if alias fails): port the cycle 321 weight `_apply`
  proof body verbatim (~30 LOC each), with the only change being the
  enclosing `unfold` switching from `_quadratureWeights_three` to
  `_collocationA_three`. The body is identical: same `h_erase`, same
  `h_eval`, same integrability witnesses on `[0, 1]`, same `h2`/`h1`
  closures, same simp set.

### B.3 P1 — Assembled `RKTableau` `butcherLobattoIIIA_three`

```lean
/-- **The 3-stage Lobatto IIIA `RKTableau`** assembled from the
canonical Lagrange weights, zeros, and collocation A-matrix of the
Lobatto quadrature. At `s = 3` this is Simpson's rule with
`c = (0, 1/2, 1)`, `b = (1/6, 2/3, 1/6)`,
`A = !![0, 0, 0; 5/24, 1/3, -1/24; 1/6, 2/3, 1/6]`. -/
noncomputable def butcherLobattoIIIA_three :
    OpenMath.Chapter3.Section312.RKTableau 3 where
  A := butcherLobatto_collocationA_three
  b := butcherLobatto_quadratureWeights_three
  c := butcherLobatto_zeros_three
```

### B.4 P1 — Direct-form `butcherLobattoIIIADirect_three`

```lean
/-- **Direct Lobatto IIIA `s = 3` tableau** for cross-validation,
declared inline rather than via collocation. Butcher Table 344(I)
p. 226. -/
noncomputable def butcherLobattoIIIADirect_three :
    OpenMath.Chapter3.Section312.RKTableau 3 where
  A := !![0, 0, 0; 5/24, 1/3, -1/24; 1/6, 2/3, 1/6]
  b := ![1/6, 2/3, 1/6]
  c := ![0, 1/2, 1]
```

### B.5 P1 — Coincidence theorem `butcherLobattoIIIA_three_eq_direct`

```lean
/-- **Coincidence**: the cycle-333 collocation-assembled Lobatto IIIA
tableau at `s = 3` equals the direct Simpson's-rule tableau.
Validates that the C(s)-variant family coincides with plain Lagrange
collocation, mirroring the cycles 322 (Radau IIA s=1), 323 (Lobatto
IIIA s=2), 324 (Radau IIA s=2), 325 (Radau IA s=1), and 332 (Radau I
C(s) s=2) C(s)-coincidence theorems. -/
theorem butcherLobattoIIIA_three_eq_direct :
    butcherLobattoIIIA_three = butcherLobattoIIIADirect_three := by
  refine OpenMath.Chapter3.Section312.RKTableau.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i j; fin_cases i <;> fin_cases j
    all_goals first
      | (show butcherLobatto_collocationA_three _ _ = _
         rw [butcherLobatto_collocationA_three_apply_zero_zero]; rfl)
      | -- ... 8 more arms following the same pattern, OR write 9 explicit arms
        sorry
  · funext j; fin_cases j
    · show butcherLobatto_quadratureWeights_three ⟨0, by omega⟩ = _
      rw [butcherLobatto_quadratureWeights_three_apply_zero]; rfl
    · show butcherLobatto_quadratureWeights_three ⟨1, by omega⟩ = _
      rw [butcherLobatto_quadratureWeights_three_apply_one]; rfl
    · show butcherLobatto_quadratureWeights_three ⟨2, by omega⟩ = _
      rw [butcherLobatto_quadratureWeights_three_apply_two]; rfl
  · funext i; fin_cases i <;> rfl
```

If the `all_goals first | ...` chain is hard to write correctly,
fall back to **9 explicit arms** for the `A`-field — one `· show
butcherLobatto_collocationA_three ⟨i, _⟩ ⟨j, _⟩ = _; rw [the
matching _apply]; rfl` for each `(i, j) ∈ Fin 3 × Fin 3`. This is
the same shape as cycle 332's 4-arm `A`-field proof (lines
2242–2256), just scaled.

Template recipe identical to cycle 332's
`butcherRadauI_collocation_two_eq_direct` (lines 2232–2273); just
scale `fin_cases` from 2 to 3 dimensions (9 arms for `A`, 3 for `b`,
3 for `c`). Each `A` arm: `rw [butcherLobatto_collocationA_three_apply_<i>_<j>]; rfl`.
Each `b` arm: `rw [butcherLobatto_quadratureWeights_three_apply_<j>]; rfl`.
Each `c` arm: `rfl` (pattern-matched abscissae reduction).

### B.6 P1 — Non-vacuity example `SatisfiesB 4`

Lobatto IIIA `s = 3` achieves classical order `p = 2s − 2 = 4`. The
B(4) quadrature condition `∑ⱼ bⱼ · cⱼ^(k−1) = 1/k` for
`k ∈ {1, 2, 3, 4}` is therefore the maximal quadrature condition.

```lean
/-- **Non-vacuity**: Lobatto IIIA `s = 3` (Simpson's rule) achieves
classical order `2s − 2 = 4`, so `B(4)` is the maximal quadrature
condition. Verified via the cycle-333 coincidence theorem. -/
example : butcherLobattoIIIA_three.SatisfiesB 4 := by
  rw [butcherLobattoIIIA_three_eq_direct]
  intro k h1 h4
  interval_cases k
  all_goals (simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]; norm_num)
```

If `simp + norm_num` chain over-/under-reduces on any arm, fall back
to explicit per-arm `unfold` + `show ∑ i : Fin 3, _ = _` +
`Fin.sum_univ_three` + `simp [butcherLobattoIIIADirect_three]; norm_num`.

### B.7 P2 stretch — `SatisfiesC 3` certificate

C(s) at `s = 3`: `∑ⱼ Aᵢⱼ cⱼ^(k−1) = cᵢ^k / k` for `i ∈ Fin 3`,
`k ∈ {1, 2, 3}`. Nine arms (3 stages × 3 exponents):

```lean
example : butcherLobattoIIIA_three.SatisfiesC 3 := by
  rw [butcherLobattoIIIA_three_eq_direct]
  intro i k h1 h3
  fin_cases i <;> interval_cases k <;>
    (simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]; norm_num)
```

If LOC pressure mounts (Phase 1 already at 500+ LOC), defer this to
a follow-up cycle.

## C. Sequencing recommendation

Total estimated LOC: ~450–550 (cycle 332 was ~150 with 4 entries;
cycle 333 has 9 entries plus 9 coincidence arms; some of the 9
entries are degenerate or alias-reused, so net new substantive work
is ~3 row-1 entries × 60 LOC = 180 LOC + 3 row-2 alias entries × 15
LOC = 45 LOC + 3 row-0 degenerate × 6 LOC = 18 LOC + assembled
tableaux + coincidence + B/C examples).

If LOC budget tight, split into two cycles:

* **Cycle 333 (this cycle, P1 only)**: B.1–B.6 (definition + 9
  `_apply` + assembled tableau + direct tableau + coincidence
  theorem + `SatisfiesB 4`). ~450 LOC. Skip B.7.
* **Cycle 334 (follow-up)**: B.7 `SatisfiesC 3` certificate plus a
  pivot to a fresh entity (see §I below for outlook).

If the row-2 alias route (B.2 paragraph) works definitionally, the
LOC drops to ~350 and B.7 fits comfortably in this cycle.

## D. What NOT to do

* **Do NOT** attempt the general-`s` `thm:344A` polynomial-exactness
  headline. That is Phase B.2 of the cycle 317–332 plan and is
  multi-cycle work (Butcher §344 p. 244 proof requires polynomial
  division and the `B(2s − 1)`/`B(2s − 2)` order arguments not yet
  in scope).

* **Do NOT** pursue Lobatto IIIB `s = 3` collocation. Cycle 327's
  audit established Lobatto IIIB is a D(s)-variant family (not C(s))
  and diverges from plain collocation. Direct-form
  `butcherLobattoIIIBDirect_three` is already shipped (cycle 327).

* **Do NOT** start a Phase D.14 (`s = 3` Radau I/IIA collocation
  ladders). Those families require Radau `s = 3` abscissae
  infrastructure which is NOT yet shipped (cycle 320 only delivered
  `s = 1, 2` for Radau I and Radau II).

* **Do NOT** submit to Aristotle this cycle. Per cycle 332's
  discovery #1, the cycle 323/324/332 template is fully mechanical;
  an Aristotle round-trip would waste compute. If a row-1 `_apply`
  proof stalls in a way the template doesn't predict, document the
  divergence and ship the remaining P1 deliverables; do NOT
  fire-and-forget.

* **Do NOT** modify `extraction/raw_text/` or any
  `extraction/formalization_data/entities/*.json` file. These are
  regenerated; hand-edits would be overwritten.

* **Do NOT** introduce sorries. Phase D.13 must close axiom-clean
  or be deferred. Use the cycle 149/200/263 rollback precedent: if
  any P1 deliverable cannot close cleanly, leave it out of the
  cycle and ship the rest.

* **Do NOT** raise `maxHeartbeats`. If a `simp [..., Fin.sum_univ_three]`
  call stalls, decompose into explicit `show ∑ i : Fin 3, _ = _` +
  `Fin.sum_univ_three` + per-term `simp only` + `ring` / `norm_num`.

* **Do NOT** edit `scripts/autonomous_loop.py`. The phantom
  consultant-prompt-firing pattern (cycles 015, 040, 174, 180, 248,
  263) is loop-maintainer territory.

* **Do NOT** attempt the `all_goals first | ...` golf if it's
  brittle. Write 9 explicit arms for the `A`-field coincidence
  proof; the LOC cost is ~25 lines and matches cycle 332's pattern
  scaled up.

## E. Risk assessment

| Risk | Mitigation |
|------|------------|
| `intervalIntegral` lemma names drift between cycles 321 (`[0,1]`) and 333 (`[0,1/2]`) | All lemmas (`integral_add`, `integral_sub`, `integral_const_mul`, `integral_pow`, `integral_one`) are interval-bound-agnostic. Use them verbatim with `b = 1/2` and `b = 1` instead of `b = 1` everywhere. |
| Row-2 alias route fails definitionally | Port the cycle 321 weight `_apply` proof bodies verbatim (~30 LOC each). Same simp set, same recipe. Increases total LOC by ~45 LOC; still within budget. |
| `Fin.sum_univ_three` not in default simp set | It exists in `Mathlib.Algebra.BigOperators.Fin`. Already used in `Fin.sum_univ_two` companion calls in cycles 323–331 with no issues. |
| Lagrange basis evaluation `simp` blow-up | Already characterised by cycle 321 (lines 1030–1038, 1068–1076, 1103–1111). Reuse the proof bodies verbatim. |
| `decide` slow on `(Finset.univ : Finset (Fin 3)).erase ⟨j, _⟩` | Pre-shipped: cycle 321 already used this pattern at `Fin 3`. Confirmed working. |
| Coincidence theorem's 9-arm `fin_cases i <;> fin_cases j` blows up | Cycle 332's 4-arm version closed cleanly; 9-arm version is 2.25× larger but each arm is a one-line `rw + rfl`. If `<;>` chain stalls, write 9 explicit arms. |
| `SatisfiesB 4` arm at `k = 3` requires `∫₀^1 x² = 1/3` cancellations that don't fire under `simp + norm_num` | Fall back to explicit `show ∑ i : Fin 3, b i * (c i)^2 = 1/3` + `Fin.sum_univ_three` + `simp` + `norm_num`. The arithmetic is `(1/6)·0 + (2/3)·(1/4) + (1/6)·1 = 1/6 + 1/6 = 1/3` ✓. |

## F. Verification gates

Before committing:

1. `lake env lean OpenMath/Chapter3/Section344.lean` exits 0.
2. `lake env lean OpenMath/Chapter3.lean` exits 0.
3. `grep -c sorry OpenMath/Chapter3/Section344.lean` returns 0.
4. `#print axioms OpenMath.Chapter3.Section344.butcherLobattoIIIA_three_eq_direct`
   returns `[propext, Classical.choice, Quot.sound]` only.
5. `#print axioms OpenMath.Chapter3.Section344.butcherLobatto_collocationA_three_apply_one_zero`
   returns the same.

## G. Faithfulness check (run before commit per CLAUDE.md)

For each new `def` and `theorem`:

* `butcherLobatto_collocationA_three`: defined as the integral
  `∫₀^{c_i} L_j(x) dx` at the Lobatto abscissae. Matches the
  textbook collocation construction (Butcher §342 p. 237 form,
  reused at §344 for the C(s) family per Table 344(I)).
* Nine `_apply` theorems: concrete arithmetic identities matching
  Butcher Table 344(I) p. 226 "Lobatto IIIA" row at `s = 3`.
  Quote in commit message.
* `butcherLobattoIIIA_three`: definitional assembly of cycle 320
  zeros + cycle 321 weights + this cycle's collocation matrix.
* `butcherLobattoIIIADirect_three`: direct inline declaration of
  Butcher's printed Table 344(I) values. NOT a redefinition of the
  collocation construction; it is a separate object that the
  coincidence theorem bridges.
* `butcherLobattoIIIA_three_eq_direct`: equality theorem composing
  nine non-trivial collocation rewrites + three weight rewrites +
  three `rfl` reductions. Does real work; not a tautology.
* `SatisfiesB 4` example: certifies the order condition at the
  maximal degree `p = 2s − 2 = 4` (Lobatto IIIA `s = 3`'s classical
  order). Not vacuous: at `k = 2`, the identity is
  `(1/6)·0 + (2/3)·(1/2) + (1/6)·1 = 1/2 = 1/2` — non-trivial.

No new `class` or `structure` introduced. No `Prop` fields with
ambiguous hypothesis-vs-conclusion status. No hypotheses stronger
than the textbook.

## H. Aristotle status

No active projects. Do not submit this cycle (see §D bullet 4).

## I. Cycle 334 outlook (worker may sketch in task results)

After cycle 333 lands:

* **§344 small-`s` ladder near-saturated** at `s ≤ 3` for Lobatto
  IIIA and IIIB (the only families with `s = 3` printed in Butcher
  Table 344(I) p. 225–226). Radau `s = 3` would require new
  abscissae infrastructure (multi-cycle).
* **Natural pivots** (planner's choice — write a scoping doc cycle
  if the deliverable bar is too high for a single cycle):
  - `def:422B` (underlying one-step method for LMM, §422) —
    definition-only, single cycle.
  - `def:442A` (principal sheet, §442) — definition-only.
  - `thm:535A` (underlying one-step method for GLM, §535) —
    ~2–3 cycles per the Chapter 5 task results.
  - `thm:541A` (types of DIMSIM methods, §541) — multi-cycle, would
    want a scoping doc first.
* **Phase B.2 of `thm:344A`** (polynomial-exactness headline) —
  multi-cycle, requires the `B(2s − 1)` / `B(2s − 2)` order-
  condition machinery.

Recommend the planner pick a fresh entity for cycle 334 to break the
long §344 streak (which will be 17 consecutive cycles after this
one). `def:422B` or `def:442A` is the lowest-risk single-cycle
pivot.

## J. Step-by-step worker checklist

1. Read cycle 332's `butcherRadauI_collocation_two_eq_direct`
   (Section344.lean lines 2114–2273) end-to-end. This is the
   verbatim template.
2. Read cycle 323's `butcherLobatto_collocationA_two_*` and
   `butcherLobattoIIIA_two_eq_trapezoidal` (lines 1255–1399) to
   confirm the row-0 (degenerate) closure pattern and the
   coincidence theorem shape.
3. Read cycle 321's `butcherLobatto_quadratureWeights_three_apply_*`
   (lines 1024–1125) to confirm the basis evaluation closed forms
   for `L_0, L_1, L_2` and reuse them verbatim.
4. Write `butcherLobatto_collocationA_three` def + 9 `_apply`
   theorems in the order: 3 row-0 (degenerate, easy), 3 row-2
   (alias route, easy if it works), 3 row-1 (substantive,
   ~50–65 LOC each).
5. Write `butcherLobattoIIIA_three` + `butcherLobattoIIIADirect_three`
   defs (each 5 LOC).
6. Write `butcherLobattoIIIA_three_eq_direct` coincidence theorem
   (9 + 3 + 3 = 15 arms; estimated 30–50 LOC).
7. Write `SatisfiesB 4` `example` (4 arms; estimated 15 LOC).
8. (Optional P2) Write `SatisfiesC 3` `example` (9 arms; estimated
   15 LOC).
9. Run all 5 verification gates from §F. Commit only if all pass.
10. Update `extraction/formalization_data/lean_status.json` and
    `plan.md` for `thm:344A` (still partial) with cycle 333 note.
11. Write `.prover-state/task_results/cycle_333.md` per CLAUDE.md
    template.
