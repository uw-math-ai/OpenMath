# Cycle 213 Results

## Worked on

P1 (primary): `RKTableau.compose_of_isRKOneStep` — reverse direction of the
(forthcoming) `compose_isRKOneStep_iff` bridge for §382. Closes **Gap A
(reverse)** of the path to `thm:382A` per
`.prover-state/issues/compose_isRKOneStep_iff_scoping.md`.

P2: Non-vacuity witnesses on `paddedEuler` — `paddedEuler_isRKOneStep`
(general single-step witness, parameterised over `f, y₀, H`) and an
`example` chaining two `paddedEuler_isRKOneStep` calls through the new
`compose_of_isRKOneStep` to exhibit a concrete output of the 4-stage
`paddedEuler.compose paddedEuler`.

P3 (stretch, ≤10 min): `Fin.append` / `Fin.sum_univ_add` Mathlib audit
for cycle 214's forward direction.

The strategy's optional iff-scaffold (sorry'd `compose_isRKOneStep_iff`)
was **SKIPPED** by default to keep sorry count at 0 (per strategy §B and
the cycle-200 supervisor scoring incident).

## Approach

### P1 — `compose_of_isRKOneStep`

Followed strategy §C verbatim:

1. Unpack `h₁ : M₁.IsRKOneStep f y₀ H y_mid` as `⟨Y₁, hY₁_stage, hY₁_out⟩`
   and likewise `h₂` as `⟨Y₂, hY₂_stage, hY₂_out⟩`.
2. Provide `Fin.append Y₁ Y₂ : Fin (s₁ + s₂) → N` as the composite stage
   tuple via `refine ⟨Fin.append Y₁ Y₂, ?_, ?_⟩`.
3. **Stage equation goal**: `intro i; induction i using Fin.addCases with
   | left i₁ => … | right i₂ => …`.
   - Top block (`Fin.castAdd s₂ i₁`): `rw [Fin.append_left, Fin.sum_univ_add]`
     then `simp only [compose_A_topLeft, compose_A_topRight,
     Fin.append_left, Fin.append_right, zero_smul, Finset.sum_const_zero,
     add_zero]` collapses the top-right block's `0`-row to nothing, leaving
     `Y₁ i₁ = y₀ + H • ∑ j, M₁.A i₁ j • f (Y₁ j)` which is exactly
     `hY₁_stage i₁`.
   - Bottom block (`Fin.natAdd s₁ i₂`): same shape but with
     `compose_A_botLeft` (= `M₁.b j`) and `compose_A_botRight` (=
     `M₂.A i₂ j`) and no zeroing. Distribute via `smul_add`, regroup via
     `← add_assoc`, then `← hY₁_out` swaps
     `y₀ + H • ∑ j₁, M₁.b j₁ • f (Y₁ j₁)` for `y_mid`. Close with
     `hY₂_stage i₂`.
4. **Output equation goal**: `rw [Fin.sum_univ_add]`, then `simp only` with
   `compose_b_castAdd / b_natAdd / Fin.append_left / Fin.append_right`,
   then `smul_add / ← add_assoc / ← hY₁_out`. Close with `hY₂_out`.

### P2 — paddedEuler witnesses

`paddedEuler.A = 0`, so for the constant stage tuple `Y := fun _ => y₀`
the stage equation `Y i = y₀ + H • ∑ j, 0 • f y₀` reduces to `y₀ = y₀`
under `simp [paddedEuler]`. The output equation `y₀ + H • f y₀ = y₀ + H •
∑ i, ![1,0] i • f y₀` closes via `simp [paddedEuler, Fin.sum_univ_two]`.

Chaining two calls of this witness through `compose_of_isRKOneStep` (with
`y_mid := y₀ + H • f y₀`) yields the composite output
`(y₀ + H • f y₀) + H • f (y₀ + H • f y₀)` — explicit-Euler-twice, as
expected from `paddedEuler` being a padded explicit-Euler frame.

### P3 — `Fin.append` audit

Used `lean_loogle` to verify the exact Mathlib names for cycle 214:

- `Fin.append _ _ (Fin.castAdd _ _)` → `Fin.append_left {m n : ℕ} {α : Sort*}
  (u : Fin m → α) (v : Fin n → α) (i : Fin m) :
  Fin.append u v (Fin.castAdd n i) = u i`
  (module `Mathlib.Data.Fin.Tuple.Basic`).
- `Fin.append _ _ (Fin.natAdd _ _)` → `Fin.append_right {m n : ℕ} {α : Sort*}
  (u : Fin m → α) (v : Fin n → α) (i : Fin n) :
  Fin.append u v (Fin.natAdd m i) = v i`
  (same module).
- `∑ _ : Fin (_ + _), _` → `Fin.sum_univ_add {M : Type*} [AddCommMonoid M]
  {a b : ℕ} (f : Fin (a + b) → M) :
  ∑ i, f i = ∑ i, f (Fin.castAdd b i) + ∑ i, f (Fin.natAdd a i)`
  (module `Mathlib.Algebra.BigOperators.Fin`).

All three were used directly in `compose_of_isRKOneStep` without any
helper-lemma fallback; Risk 1 (custom `Fin.sum_univ_addCases` helper) did
not fire.

## Result

**SUCCESS.**

- `compose_of_isRKOneStep` (theorem body, ~22 LOC, ~33 LOC including
  ~11-line docstring) compiles axiom-clean on first attempt — strategy's
  proof recipe survived verbatim, no Risk-1/2/3/4/5 fallbacks needed.
- `paddedEuler_isRKOneStep` (~6 LOC) and the chained `example` (~5 LOC)
  compile axiom-clean.
- `lake env lean OpenMath/Chapter3/Section381.lean`: exits 0.
- `grep -c sorry OpenMath/Chapter3/Section381.lean`: **0**.
- Warm rebuild time: **5.927s** (well under strategy's 30s budget).
- Predecessors `Equivalent.setoid.{u}` (cycle 211) and
  `Equivalent.setoidSigma.{u}` (cycle 212) re-checked axiom-clean
  (`[propext, Classical.choice, Quot.sound]` baseline) — no regressions.

### Mathlib-lemma-usage report (per strategy §H item 2)

| Lemma name | Verified | Used as |
|---|---|---|
| `Fin.append_left` | verified-present (Mathlib.Data.Fin.Tuple.Basic) | `Fin.append Y₁ Y₂ (Fin.castAdd s₂ i₁) = Y₁ i₁` |
| `Fin.append_right` | verified-present (Mathlib.Data.Fin.Tuple.Basic) | `Fin.append Y₁ Y₂ (Fin.natAdd s₁ i₂) = Y₂ i₂` |
| `Fin.sum_univ_add` | verified-present (Mathlib.Algebra.BigOperators.Fin) | top-block + bottom-block sum split |
| `compose_A_topLeft/topRight/botLeft/botRight` | verified-present (cycle 209) | composite-A evaluation per block |
| `compose_b_castAdd/b_natAdd` | verified-present (cycle 209) | composite-b evaluation per block |
| `zero_smul` / `Finset.sum_const_zero` / `add_zero` | Mathlib primitives | collapse top-right zero block |
| `smul_add` / `← add_assoc` | Mathlib primitives | distribute `H • (S₁ + S₂)` and regroup |

## Faithfulness check

`compose_of_isRKOneStep` is **infrastructure** for `thm:382A`, not a
textbook entity per se — no `extraction/formalization_data/entities/*.json`
file to consult.

- **Entity ID**: N/A (infrastructure helper, traced to Butcher §382
  equations 382b–e). The textbook prose: "The result of applying one
  step of method `m₁` followed by one step of `m₂` is identical to one
  step of the composite method `m₁·m₂`" (Butcher §382, p. 285).
- **Lean statement captures**: same content (reverse direction only —
  forward direction deferred to cycle 214).
- **Tautology check**: NO. The conclusion `(M₁.compose M₂).IsRKOneStep
  f y₀ H y_final` is genuinely *constructed* from `h₁` and `h₂` via the
  `Fin.append` stage tuple — neither hypothesis matches the conclusion
  verbatim (they're stated over the smaller stage spaces `Fin s₁` and
  `Fin s₂`).
- **Identity check**: NO. The proof builds a stage tuple via `Fin.append`
  and discharges two non-trivial obligations (per-stage and output).
- **Hypothesis strength**: minimal — no Lipschitz, no smallness, no
  `CompleteSpace`. The hypotheses are exactly what the algebraic block
  assembly needs.
- **Definition smuggling**: not applicable — no new definitions.
- **Absent theorem**: not applicable — no `sorry`-promised follow-ups.

For `paddedEuler_isRKOneStep`:

- **Entity ID**: N/A (concrete non-vacuity witness; not a textbook claim).
- **Tautology / identity / hypothesis-strength checks**: pass (the proof
  builds a constant stage tuple and discharges A=0 and b=![1,0]
  arithmetic; no hidden assumptions).

## Dead ends

None this cycle. The proof recipe from `.prover-state/issues/compose_isRKOneStep_iff_scoping.md`
§4.1 closed on the first attempt — strategy's pre-anticipated risks 1–5
all did **not** fire:

- Risk 1 (`Fin.sum_univ_add` name): exact name confirmed via `lean_loogle`
  before code; no helper-lemma fallback.
- Risk 2 (`Fin.append` evaluation): `Fin.append_left` / `Fin.append_right`
  worked verbatim.
- Risk 3 (composite `.b` field unfolding): cycle 209's
  `compose_b_castAdd` / `compose_b_natAdd` fired via `simp only` without
  needing direct compose unfolding.
- Risk 4 (`•` vs `*` and `ring`): the proof never invoked `ring`;
  `smul_add` distributed correctly under `•` and `← hY₁_out` /
  `← add_assoc` did the algebraic regrouping over `•` without any
  `module` tactic.
- Risk 5 (`IsRKOneStep` field-name mismatch): the destructor
  `⟨Y, hstage, hout⟩` matched the anonymous-existential field structure
  of `def IsRKOneStep` (no named projections — it's an `∃ Y, _ ∧ _`).

## Discovery

1. **`Fin.sum_univ_add` is a clean, direct rewrite.** The lemma
   `∑ i, f i = ∑ i, f (Fin.castAdd b i) + ∑ i, f (Fin.natAdd a i)` plays
   beautifully with `Fin.append_left` / `Fin.append_right`: after the
   split, the bound variables are still `i`, and simp drills through to
   replace the `Fin.append` applications and the `compose_A_*` /
   `compose_b_*` lookups in one pass. This will scale straight to cycle
   214's forward direction without any new lemma plumbing.

2. **`induction i using Fin.addCases with | left | right` is the idiomatic
   case-split.** Cleaner than the `lt_or_ge i.val s₁` pattern used in
   `compose_isExplicit_iff` (cycle 210), because the former avoids the
   need to manually rebuild `Fin.castAdd`/`Fin.natAdd` views via
   `Fin.ext`. For per-`i` reasoning over `Fin (s₁ + s₂)`,
   `Fin.addCases` is strictly preferred. The cycle 210 style is still
   appropriate for iff statements that quantify *jointly* over `i, j`,
   where the asymmetric `lt_or_ge` split keeps the omega arithmetic
   centralised.

3. **`← hY₁_out` swap is structurally robust under `← add_assoc` regrouping.**
   The pattern `rw [smul_add, ← add_assoc, ← hY₁_out]` is a 3-step
   regroup-and-collapse that worked identically for *both* the
   bottom-block stage equation and the output equation. This is now a
   reusable idiom for any §382-style two-block algebraic identity that
   needs to absorb `M₁`'s output through cycle 209's bottom-left
   `compose_A_botLeft = M₁.b j` block.

4. **No `.{u}` annotations needed.** The theorem operates entirely at
   the `IsRKOneStep` level (which has its own universe story via
   `{N : Type*}` and `[NormedAddCommGroup N] [NormedSpace ℝ N]`),
   not at the `Equivalent.{u}` level. Cycles 204/211/212's universe
   discipline is local to `Equivalent` and does not propagate here.

## Suggested next approach

Cycle 214 (next): **forward direction of `compose_isRKOneStep_iff`**.

The scoping doc (§4.2) estimates ~70 LOC and identifies the Lipschitz +
small-`H` smallness threshold as the load-bearing dependency. Recommended
entry point:

1. State the full iff theorem with `(M₁.compose M₂).IsRKOneStep f y₀ H y_final
   ↔ ∃ y_mid, M₁.IsRKOneStep f y₀ H y_mid ∧ M₂.IsRKOneStep f y_mid H y_final`
   under the smallness threshold `H ≤ H₀` for `H₀ := 1 / (2 * ((L:ℝ) * C₁ + 1))`
   where `C₁ := Σ i j, |M₁.A i j|` (cycle 207 pattern).
2. Reverse direction trivially routes through cycle 213's
   `compose_of_isRKOneStep` (under whatever `H` works — the smallness
   isn't load-bearing on this leg).
3. Forward direction: project the composite stage tuple `Y_compose` onto
   `Y_top := Y_compose ∘ Fin.castAdd s₂` and `Y_bot := Y_compose ∘
   Fin.natAdd s₁`, show `Y_top` is an `M₁.RKStageMap` fixed point via
   cycle 209's `compose_A_topLeft` + `compose_A_topRight = 0`, define
   `y_mid := y₀ + H • Σᵢ M₁.b i • f (Y_top i)`, and exhibit
   `M₂.IsRKOneStep f y_mid H y_final` via `Y_bot` after absorbing
   `y_mid` through `compose_A_botLeft = M₁.b j` (same `← hY₁_out`-style
   collapse).
4. Composite output equation closes via cycle 213's `Fin.sum_univ_add` +
   `compose_b_castAdd / b_natAdd` pattern, mirror-image of cycle 213's
   output equation.

Cycle 215 candidate: ship `thm:382A` (well-definedness of `[·]` on
Equivalent classes) via the (382g) reformulation per `thm_382A_path.md`
§Recommended plan, which avoids needing the Σ-typed setoid lift (Gap B
remainder).

§441 Phase C.2 GPFS-blocked (31st consecutive); skip per strategy §A.
