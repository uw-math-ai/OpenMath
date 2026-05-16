# Cycle 326 Strategy — §344 Phase D.6: Radau IA `s = 2` `RKTableau`

## §A — Status snapshot

- Cycle 325 shipped §344 Phase D.5 (Radau IA `s = 1`, forward Euler
  analogue), axiom-clean, 5 new public symbols, +80 LOC.
  Section344.lean: 1631 → 1711 LOC. Sorry count 0.
- §344 Phase D is now saturated at `s = 1` for the Radau pair
  (Radau IIA cycle 322, Radau IA cycle 325) and at `s = 2` for
  Lobatto IIIA (cycle 323) and Radau IIA (cycle 324). Lobatto
  requires `s ≥ 2`, so the `s = 1` ladder is complete.
- No Aristotle results pending. No blocker issues filed against
  the §344 path.
- The cycle 325 task results explicitly recommend **Radau IA `s = 2`
  as the primary cycle-326 candidate** — a single-cycle mechanical
  port of cycle 324's Radau IIA `s = 2` template.

## §B — Target

Ship `butcherRadauIA_two : RKTableau 2` in
`OpenMath/Chapter3/Section344.lean`, the canonical `s = 2` Radau IA
collocation tableau (Butcher Table 344(I), p. 245), threading
cycles 317 / 320 / 321's prior infrastructure into a concrete
`Section312.RKTableau 2`. This completes the §344 small-`s` Radau
pair to `(s = 1, 2)` on both ends (IA and IIA).

## §C — Pre-flight verification (run BEFORE writing Lean)

Three cheap checks (file-read / grep) to confirm the cycle 324
template lifts cleanly. Run all three first, in parallel:

1. **Confirm `butcherRadauI_zeros_two` values** by reading the
   `_zeros_two` def shipped cycle 320 in
   `OpenMath/Chapter3/Section344.lean` (search for
   `butcherRadauI_zeros_two`). Should be `(0, 2/3)`. Verify
   `butcherRadauI_zeros_two ⟨0, _⟩ = 0 := rfl` and
   `butcherRadauI_zeros_two ⟨1, _⟩ = 2/3 := rfl` would close.
2. **Confirm `butcherRadauI_quadratureWeights_two_apply_{zero,one}`
   exist** as public theorems (cycle 321 shipped them). They should
   give `(1/4, 3/4)`.
3. **Confirm `butcherRadauI_two : Polynomial ℝ` was shipped Phase A
   cycle 317** (around `Section344.lean:179`).

If any check fails, STOP and re-scope before writing Lean. All
three are expected to pass; failure here would indicate a confused
upstream and is the cheap way to find it.

## §D — Faithfulness audit (run BEFORE writing Lean) — load-bearing

**Critical pre-flight question**: does Butcher's Radau IA `s = 2`
tableau (Table 344(I), p. 245) coincide with the plain collocation
formula `A_{ij} = ∫₀^{c_i} L_j(x) dx` evaluated at the Radau I
abscissae `(0, 2/3)`?

For cycle 324's Radau IIA `s = 2` the answer was YES: cycle 324's
`butcherRadauII_collocationA_two` is the plain collocation matrix at
`(1/3, 1)`, and it matches Butcher's Table 344(II) values
`!![5/12, -1/12; 3/4, 1/4]`.

For Radau IA at `s = 2` the textbook table is
`!![1/12, -1/12; 1/4, 5/12]`. Verify by direct computation that
this matches the plain collocation matrix at `(0, 2/3)`:

- `L_0(x)` interpolates `L_0(0) = 1, L_0(2/3) = 0` ⟹
  `L_0(x) = (x − 2/3) / (0 − 2/3) = 1 − (3/2)x`.
- `L_1(x)` interpolates `L_1(0) = 0, L_1(2/3) = 1` ⟹
  `L_1(x) = x / (2/3) = (3/2)x`.
- `A ⟨0, _⟩ ⟨0, _⟩ = ∫₀^0 L_0 dx = 0` ✓ (matches `1/12`? — see
  audit note below)
- `A ⟨0, _⟩ ⟨1, _⟩ = ∫₀^0 L_1 dx = 0` ✓ (matches `-1/12`? — see
  audit note below)
- `A ⟨1, _⟩ ⟨0, _⟩ = ∫₀^{2/3} (1 − (3/2)x) dx
                   = 2/3 − (3/2)·(2/3)²/2 = 2/3 − 1/3 = 1/3`
- `A ⟨1, _⟩ ⟨1, _⟩ = ∫₀^{2/3} (3/2)x dx = (3/2)·(2/3)²/2 = 1/3`

The computed `(0, *)` row `(0, 0)` does NOT match Butcher's
`(1/12, -1/12)`, and the computed `(1, *)` row `(1/3, 1/3)` does
NOT match Butcher's `(1/4, 5/12)`. **This indicates Radau IA `s = 2`
is NOT the plain collocation tableau** — Butcher's construction is
distinct (it places the first abscissa at 0 but determines `A` via
*backward* collocation conditions, not the standard
`A_{ij} = ∫₀^{c_i} L_j(x) dx`).

Cross-check via `B(p)` / `C(p)` consistency: my computed `(1, *)`
row sums to `2/3 = c_1 ✓` (satisfies `C(1)`); Butcher's row also
sums to `1/4 + 5/12 = 2/3 ✓`. So both are valid Runge–Kutta tableaux
satisfying the same `C(1)` condition at these abscissae — they
differ on the *remaining* degrees of freedom.

### Branch decision

Read `extraction/raw_text/ch03.txt` for the §344 paragraph that
introduces Table 344(I). Specifically:

- If Butcher EXPLICITLY constructs Radau IA via plain collocation
  (and my arithmetic above is wrong somewhere — recompute), take
  **Branch A** and proceed with the cycle 324 template verbatim.
- If Butcher constructs Radau IA via a DIFFERENT recipe (most
  likely: collocation at `(0, 2/3)` followed by enforcement of
  `B(2)` or some Radau-specific condition that adjusts the A-matrix
  away from plain collocation), take **Branch B** and pivot to
  Lobatto IIIB `s = 2` (the reflection partner of Lobatto IIIA
  shipped cycle 323), filing an issue
  `.prover-state/issues/radau_ia_collocation_divergence.md`
  documenting why the cycle 324 template does not lift.

This audit is the MOST IMPORTANT step of the cycle. Do it before
writing any Lean.

## §E — Recipe for Branch A (cycle 324 template, verbatim swaps)

If §D audit confirms Branch A:

### Substitutions

- `RadauII` → `RadauI` throughout symbol names.
- Substantive integration upper limit:
  cycle 324 used `[0, 1/3]` (Radau II's left abscissa);
  cycle 326 uses `[0, 2/3]` (Radau I's right abscissa).
- Abscissa `rfl`-rewrites:
  - `_zeros_two ⟨0, _⟩ = 0 := rfl` (Radau I left-abscissa is `0`).
  - `_zeros_two ⟨1, _⟩ = 2/3 := rfl` (Radau I right-abscissa).
- Lagrange basis closed forms (per §D):
  `L_0(x) = 1 − (3/2)x`, `L_1(x) = (3/2)x`.
- A-matrix target values (re-confirm from §D audit):
  - `(0, 0)`, `(0, 1)`: vacuous (integral over `[0, 0]`); close via
    `intervalIntegral.integral_same`. Same closer as cycle 323's
    `(0, *)` Lobatto IIIA entries and cycle 325's `(0, 0)` Radau IA
    `s = 1` entry.
  - `(1, 0)`, `(1, 1)`: substantive integration on `[0, 2/3]`.
    Close via the cycle 324 `[0, 1/3]` recipe with upper-limit
    swap. Concrete:
    ```
    unfold butcherRadauI_collocationA_two
    show ∫ x in (0 : ℝ)..butcherRadauI_zeros_two ⟨1, _⟩,
         (Lagrange.basis Finset.univ butcherRadauI_zeros_two ⟨j, _⟩).eval x = _
    have h_erase : (Finset.univ : Finset (Fin 2)).erase ⟨j, _⟩ = {⟨1−j, _⟩} := by decide
    -- Lagrange basis collapse to closed-form polynomial via prod_singleton + basisDivisor
    have h_eval : ∀ x : ℝ, (Lagrange.basis …).eval x = (closed form) := …
    simp_rw [h_eval]
    have h_c1 : butcherRadauI_zeros_two ⟨1, _⟩ = 2/3 := rfl
    rw [h_c1]
    have h_int_witness : IntervalIntegrable id volume 0 (2/3) :=
      continuous_id.intervalIntegrable 0 (2/3)
    have hx : ∫ x in (0 : ℝ)..(2/3), x = (2/3)^2 / 2 := by
      rw [integral_pow]; ring
    -- split via intervalIntegral.integral_sub / _const_mul / _const
    -- close via norm_num
    ```

### Five new public symbols (matching cycle 324 ship shape)

1. `butcherRadauI_collocationA_two : Fin 2 → Fin 2 → ℝ` —
   `(i, j) ↦ ∫₀^{c_i} L_j(x) dx` over the Radau I two-leaf
   abscissae.
2. Four `_apply` theorems:
   - `butcherRadauI_collocationA_two_apply_zero_zero` — `= 0`.
   - `butcherRadauI_collocationA_two_apply_zero_one` — `= 0`.
   - `butcherRadauI_collocationA_two_apply_one_zero` — substantive,
     value per §D audit.
   - `butcherRadauI_collocationA_two_apply_one_one` — substantive,
     value per §D audit.
3. `butcherRadauIA_two : RKTableau 2` — threading
   cycle 320's `_zeros_two`, cycle 321's `_quadratureWeights_two`,
   and this cycle's `_collocationA_two`.
4. `butcherRadauIADirect_two : RKTableau 2` — direct form
   `c = (0, 2/3)`, `b = (1/4, 3/4)`, `A = !![a₀₀, a₀₁; a₁₀, a₁₁]`
   with values matching the `_apply` theorems.
5. `butcherRadauIA_two_eq_direct` — coincidence theorem via
   `RKTableau.mk.injEq` + `funext + fin_cases` per field (cycle
   324 template).

### Non-vacuity stretch

`SatisfiesB 3` example: Radau IA `s = 2` achieves classical order
`2s − 1 = 3`, so `B(3)` is maximal. Close via
`rw [butcherRadauIA_two_eq_direct]; intro k h1 hk; interval_cases k <;>
simp [butcherRadauIADirect_two, Fin.sum_univ_two] <;> norm_num`.

Per cycle 325's discovery, start the per-arm closer with just
`simp [direct]` and add `Fin.sum_univ_two` / `norm_num` only if
needed.

## §F — Recipe for Branch B (Lobatto IIIB `s = 2`)

If §D audit reveals Radau IA at `s = 2` is not the plain
collocation tableau:

1. Write a one-paragraph issue file
   `.prover-state/issues/radau_ia_collocation_divergence.md`
   quoting Butcher's §344 construction and noting that the plain
   collocation formula gives a different A-matrix at the Radau I
   abscissae.
2. Pivot the cycle deliverable to **Lobatto IIIB `s = 2`**, the
   reflection partner of Lobatto IIIA shipped cycle 323. Lobatto
   IIIB at `s = 2` has `c = (0, 1)`, `b = (1/2, 1/2)`,
   `A = !![1/2, 0; 1/2, 0]` (Butcher §344). The reflection identity
   in cycle 343's already-shipped `thm:343A` should reduce the
   construction to a transformation of cycle 323's Lobatto IIIA.
3. Same five-symbol ship shape (collocation A def + four `_apply`
   theorems + direct form + coincidence theorem + `SatisfiesB`
   non-vacuity), adjusted for Lobatto IIIB's specific values.

## §G — Verification checklist (run before commit)

1. `lake env lean OpenMath/Chapter3/Section344.lean` — exit 0, no
   diagnostics.
2. `lake build OpenMath.Chapter3` — succeeds.
3. `grep -c sorry OpenMath/Chapter3/Section344.lean` — must be `0`.
4. `#print axioms` on each new symbol returns
   `[propext, Classical.choice, Quot.sound]`.
5. The `SatisfiesB ?` non-vacuity example compiles.
6. Tautology-scanner regex
   `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` returns no new
   hits on cycle 326 additions.

## §H — Faithfulness checklist (CLAUDE.md pre-commit)

For each new `def`, `RKTableau` instance, and `theorem`:

- Quote the textbook source (Butcher §344, Table 344(I) p. 245 for
  Branch A; corresponding Lobatto IIIB section for Branch B).
- Confirm the Lean A-matrix values match the textbook table values.
  **If §D audit indicates Branch A but the `_apply` values do NOT
  match Butcher's Table 344(I)** (e.g. `(1, 0)` is `1/3` rather than
  `1/4`), STOP and re-audit before commit — this is a smuggling
  failure mode that must not slip past pre-commit.
- For `butcherRadauIA_two_eq_direct`: this is a coincidence theorem
  doing real work (bridging the abstract collocation construction
  to the classical direct form). Not vacuous.
- For the `SatisfiesB` example: documents that the abstract tableau
  recovers the textbook order condition; not vacuous.

## §I — Risk register

- **R1 (HIGH)**: §D faithfulness audit. The Radau IA `s = 2`
  divergence between plain collocation and Butcher's Table 344(I)
  values is real per my §D arithmetic. Mitigation: §D textbook
  re-read is mandatory; Branch B pivot is available.
- **R2 (LOW)**: closed-form Lagrange basis polynomial arithmetic.
  Mitigation: paper-compute first; cycle 324 / 325 templates are
  the reference recipes.
- **R3 (LOW)**: `integral_pow` upper-limit cast. Mitigation:
  cycle 324's incantation `integral_pow (a := 0) (b := 1/3) 1`
  with `1/3 → 2/3` swap.
- **R4 (LOW)**: `SatisfiesB 3` arithmetic across 3 arms.
  Mitigation: cycle 324's closer pattern verbatim.

## §J — What NOT to try

- Do **NOT** attempt Lobatto IIIA `s = 3` (Simpson's rule) — still
  multi-cycle scope per cycles 323 / 324 / 325 task results.
- Do **NOT** attempt Phase B.2 polynomial exactness (`thm:344A`
  headline) — multi-cycle.
- Do **NOT** raise `maxHeartbeats`. If substantive integration
  arms stall, decompose into private helper integrals (one per
  monomial) per CLAUDE.md.
- Do **NOT** introduce `axiom` or `constant`. If Branch B fires
  for an unresolvable reason, file an issue and pivot Lobatto IIIB.
- Do **NOT** submit to Aristotle this cycle. Mechanical port from a
  shipped template is faster manually than Aristotle's 30-min
  round-trip; the cycle 322 / 323 / 324 / 325 ladder shows the
  manual recipe is reliable.
- Do **NOT** skip the §C pre-flight or the §D textbook audit. The
  R1 risk is real and unaddressed; cycle 171's misinterpretation
  pattern is a cautionary precedent.
- Do **NOT** add `Fin.sum_univ_two` / `norm_num` to `SatisfiesB`
  closers preemptively — cycle 325 showed they fire "unused"
  warnings when the form is simple enough. Start minimal
  (`simp [direct]`) and add arguments only if needed.
- Do **NOT** commit Branch A `_apply` values that conflict with
  Butcher's Table 344(I) — that would be definition smuggling
  (claiming the collocation construction matches the textbook
  values when it does not).

## §K — Cycle 327+ outlook (do not pursue this cycle)

After Branch A or B closes:
- If Branch A succeeded (Radau IA `s = 2` shipped): Lobatto IIIB
  `s = 2` is the natural cycle 327 candidate (reflection partner
  of Lobatto IIIA, ~150 LOC mechanical port via `thm:343A`).
- If Branch B fired (Lobatto IIIB `s = 2` shipped): return to the
  Radau IA audit in a future cycle with a clearer understanding of
  Butcher's construction; the divergence issue file is the
  scoping anchor.
- Either way, Lobatto IIIA `s = 3` (Simpson's rule) and Phase B.2
  polynomial exactness remain multi-cycle scope; only attempt
  after the planner schedules a multi-cycle effort.
