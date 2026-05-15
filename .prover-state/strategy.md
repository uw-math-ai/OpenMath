# Cycle 245 strategy — `lem:319A` Phase 2 via MMatrix relocation

## TL;DR

Cycle 244 supervisor verdict (`score=−1`, "SEMANTIC REGRESSION: 2 suspected
vacuous proof(s) introduced") is a **scanner false positive** of the
documented D1/D2 pattern. Lines 167–168 of `OpenMath/Chapter3/Section319.lean`
are `(hY_out : ...) (hZ_out : ...)` — *hypothesis declarations* in the
`output_diff_recurrence` signature, not proof bodies. The cycle 244 work
landed cleanly (commit `8c30ec5`, +282 LOC, 0 sorries, 3 axiom-clean
theorems). **Do not unwind cycle 244 work; do not chase the scanner.**

Cycle 245 ships **Phase 2 of `lem:319A`** via the planner's Option α
(relocate `MMatrix.lean` to a chapter-neutral location), producing the
headline `‖y₁ − z₁‖ ≤ (1 + h L^†) ‖y₀ − z₀‖` bound. This unblocks
`thm:319B` (Global truncation error theorem, the §319 capstone) for
cycle 246+.

## §A — Aristotle-results inbox

Empty. No pending submissions. Aristotle path not used this cycle —
the deliverable is a structural relocation + a 60-LOC headline proof
composing existing M-matrix machinery (cycle 106) with cycle 244's
Phase 1 recurrences. No prover support needed.

## §B — Priority 0: verify cycle 244 phantom (≤ 3 min)

The supervisor's "2 suspected vacuous proofs" verdict is the same
shape documented in
`.prover-state/issues/tautology_scanner_false_positives.md` (bug D2 —
over-firing, possibly compounded by D1 line-drift). Verify quickly:

```bash
git show --stat 8c30ec5 -- OpenMath/Chapter3/Section319.lean
# Expected: 1 file changed, 282 insertions(+)

wc -l OpenMath/Chapter3/Section319.lean
grep -c sorry OpenMath/Chapter3/Section319.lean
# Expected: 282 / 0
```

The flagged lines 167–168 are theorem-signature hypothesis bindings:

```
(hY_out : y₁ = y₀ + h • ∑ i, M.b i • f (Y i))
(hZ_out : z₁ = z₀ + h • ∑ i, M.b i • f (Z i))
```

These are **not** vacuous proofs. **Do NOT rename, do NOT inline, do
NOT modify Section319.lean to silence the scanner.** The supervisor's
prompt-builder bug is loop-maintainer territory per `CLAUDE.md` and
`tautology_scanner_false_positives.md` §D. Note the phantom in
`attempts.md` (`Cycle 245 confirmation` row) and move on.

## §C — Priority 1: relocate `MMatrix.lean` (the main deliverable)

### §C.1 — The move

Current state (verified by the planner this cycle):

* `OpenMath/Chapter5/MMatrix.lean` (171 LOC) depends only on Mathlib
  imports (`Matrix.Mul`, `Matrix.Basic`, `LinearAlgebra.Matrix.*`,
  `Analysis.Matrix.Normed`, `Analysis.SpecificLimits.Normed`).
* All lemmas live under `namespace Matrix` (not under
  `OpenMath.Chapter5.MMatrix`). The file path is purely the import key
  — **callers reference `Matrix.EntrywiseNonneg.*` etc., not
  `OpenMath.Chapter5.MMatrix.*`**. So moving the file is mechanical:
  only the `import` line in two consumers changes.
* Two consumers: `OpenMath/Chapter5.lean` (root aggregator) and
  `OpenMath/Chapter5/Section515.lean`. (Verified by Grep.)

**Move target**: `OpenMath/Matrix/MMatrix.lean` (a new chapter-neutral
module). Pattern is consistent with other utility-outside-chapter
placements that future cycles will need.

### §C.2 — Concrete steps

1. **Verify the target directory.** Run `ls OpenMath/Matrix 2>&1` via
   Bash. If the directory does not exist, run `mkdir -p OpenMath/Matrix`.
2. **Copy the file verbatim**:
   `cp OpenMath/Chapter5/MMatrix.lean OpenMath/Matrix/MMatrix.lean`.
   The file's `namespace Matrix ... end Matrix` block stays intact —
   no contents need editing.
3. **Update the two consumer imports** with Edit:
   * `OpenMath/Chapter5.lean`: change `import OpenMath.Chapter5.MMatrix`
     → `import OpenMath.Matrix.MMatrix`.
   * `OpenMath/Chapter5/Section515.lean`: same rename.
4. **Optional** (do this if `OpenMath.lean` or another root aggregator
   exists — check first with `Read OpenMath.lean`): add a category
   aggregator `OpenMath/Matrix.lean` with `import OpenMath.Matrix.MMatrix`
   and add `import OpenMath.Matrix` to the root list. Skip if the root
   already imports `OpenMath.Chapter5` (which transitively imports
   MMatrix).
5. **Delete the old file** *after* steps 2–4 succeed:
   `git rm OpenMath/Chapter5/MMatrix.lean`.
6. **Smoke-test Section515 (the load-bearing consumer)**:
   `time timeout 120 lake env lean OpenMath/Chapter5/Section515.lean`
   should complete with exit 0. Section515 is ~3000 LOC and used to
   take ~30 s warm cache; a fresh import path may invalidate the cache,
   so allow up to 2 min.
7. **Smoke-test Chapter 5 aggregator**:
   `time timeout 60 lake env lean OpenMath/Chapter5.lean` should exit 0.

If step 6 or 7 fails: revert via `git checkout
OpenMath/Chapter5/`, `git restore --staged --worktree OpenMath/Matrix/`,
and bail to **Backup B5** (Option β — inline derivation inside
Section319).

### §C.3 — Update Section319.lean to import the relocated module

After §C.2 succeeds, append to the import block of
`OpenMath/Chapter3/Section319.lean` (currently lines 1–3):

```lean
import OpenMath.Matrix.MMatrix
```

(Add after the `import Mathlib.Analysis.Normed.Group.Basic` line.
Imports should remain sorted/grouped consistently with the existing
style.)

Smoke-test: `time timeout 60 lake env lean OpenMath/Chapter3/Section319.lean`
should still exit 0 (the file has nothing new yet; the new import is a
no-op until §D adds Phase 2 content).

## §D — Priority 2: ship Phase 2 of `lem:319A` (the headline bound)

With MMatrix relocated and imported into Section319, build the
headline theorem composing cycle 244's recurrences (D1, D2) with cycle
106's M-matrix inversion.

### §D.1 — Target signature

Insert in `namespace OpenMath.Chapter3.Section312.RKTableau` of
`OpenMath/Chapter3/Section319.lean`, after cycle 244's
`lem_319A_recurrences`:

```lean
/-- **Butcher §319 lem:319A** — global truncation error of one RK step.
For Lipschitz `f` and step size `h ≤ h₀` with the M-matrix smallness
`‖(h₀ * L) • M.A.map (·|·|)‖_F < 1`, the output-difference
is bounded by `(1 + h L^†) ‖y₀ - z₀‖` for some non-negative `L^†`. -/
theorem lem_319A {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y₀ z₀ : N} {h h₀ : ℝ} (hh : 0 < h) (hh_le : h ≤ h₀)
    (hh₀ : 0 ≤ h₀)
    (h_norm : ‖((h₀ * L) • M.A.map (fun a => |a|))‖ < 1) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ∀ y₁ z₁,
        M.IsRKOneStep f y₀ h y₁ → M.IsRKOneStep f z₀ h z₁ →
        ‖y₁ - z₁‖ ≤ (1 + h * L_dag) * ‖y₀ - z₀‖
```

The existential packaging avoids exposing the precise `L^†` formula at
the top-level signature; downstream consumers (`thm:319B`) only need
the bound to exist and be non-negative.

### §D.2 — Proof recipe (composing cycle 106 + cycle 244)

Open `Matrix.Norms.Frobenius` scope (cycle 124 precedent — Section515
uses this; see `Section515.lean:2257`). Inside the proof:

1. **Set up the M-matrix**. Define `K := (h₀ * L) • M.A.map (fun a => |a|)`
   in `Matrix (Fin s) (Fin s) ℝ`. By the `h_norm` hypothesis, `‖K‖ < 1`.
   `K.EntrywiseNonneg` follows from `0 ≤ h₀ * L` (composition of
   `hh₀` and `hL`) plus entrywise non-negativity of `|·|`
   (`Matrix.EntrywiseNonneg.smul` + `abs_nonneg`).

2. **Invoke cycle 106's M-matrix inverse-positivity**:
   `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one hK_nn h_norm`
   gives `(Ring.inverse (1 - K)).EntrywiseNonneg`. Use it together
   with `Matrix.EntrywiseNonneg.mulVec_nonneg` (also cycle 106) on the
   constant vector `(fun _ => (1 : ℝ))` to get a non-negative vector
   `w := Ring.inverse (1 - K) *ᵥ (fun _ => (1 : ℝ))` satisfying
   `∀ i, 0 ≤ w i`.

3. **Define `L^†`**: set
   `L_dag := L * ∑ i, |M.b i| * w i`.
   Non-negativity: `0 ≤ L_dag` follows from `0 ≤ L`, `0 ≤ |M.b i|`,
   and `0 ≤ w i` via `Finset.sum_nonneg` and `mul_nonneg`.

4. **Open the universal**: introduce `y₁, z₁, hY, hZ`. Invoke cycle
   244's `lem_319A_recurrences hL hf_lip (le_of_lt hh) hY hZ` to
   obtain stage tuples `Y, Z : Fin s → N` plus the per-index stage
   inequality `hStage` and the output inequality `hOut`.

5. **Bound stage differences via the M-matrix comparison principle**.
   Set `vM := fun i => ‖Y i - Z i‖`. From `hStage` rewritten as
   `vM i ≤ ‖y₀ - z₀‖ + h * L * ∑ j, |M.A i j| * vM j`, and using
   `h * L ≤ h₀ * L` (from `hh_le` and `hL`), the entrywise
   inequality `vM ≤ ‖y₀ - z₀‖ • (1 - K)⁻¹ *ᵥ (fun _ => 1)`
   follows from cycle 106's `nonneg_of_one_sub_mulVec_nonneg`
   applied to `‖y₀ - z₀‖ • w - vM` (after rearranging the linear
   system). Write this as
   `hVM_bound : ∀ i, vM i ≤ ‖y₀ - z₀‖ * w i`.

6. **Substitute into the output recurrence**. From `hOut`:
   ```
   ‖y₁ - z₁‖ ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * vM i
            ≤ ‖y₀ - z₀‖ + h * L * ∑ i, |M.b i| * (‖y₀ - z₀‖ * w i)
              [by hVM_bound, Finset.sum_le_sum, mul_le_mul_of_nonneg_left
               via |M.b i| nonneg]
            = ‖y₀ - z₀‖ + h * (L * ∑ i, |M.b i| * w i) * ‖y₀ - z₀‖
              [Finset.mul_sum + ring]
            = (1 + h * L_dag) * ‖y₀ - z₀‖.
   ```

   Each rewrite is one or two `simp`/`rw`/`ring` steps.

### §D.3 — Non-vacuity witness (mandatory)

Add an `example` at the bottom of `Section319.lean` (in the file-local
namespace `OpenMath.Chapter3.Section319`):

```lean
/-- Non-vacuity: at `paddedEuler` with `f := id` and any
non-negative `h ≤ 1/2`, the M-matrix smallness holds trivially
(because `paddedEuler.A = 0`), so `lem_319A` produces a usable
`L^†` and contraction bound. -/
example (h h₀ : ℝ) (hh : 0 < h) (hh₀ : 0 ≤ h₀) (hh_le : h ≤ h₀)
    (y₀ z₀ y₁ z₁ : ℝ)
    (hY : paddedEuler.IsRKOneStep id y₀ h y₁)
    (hZ : paddedEuler.IsRKOneStep id z₀ h z₁) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ‖y₁ - z₁‖ ≤ (1 + h * L_dag) * ‖y₀ - z₀‖ := by
  have hLip : LipschitzWith (1 : ℝ).toNNReal (id : ℝ → ℝ) := by
    rw [Real.toNNReal_one]; exact LipschitzWith.id
  -- paddedEuler.A = 0 ⇒ M.A.map abs = 0 ⇒ smul = 0 ⇒ ‖0‖ < 1.
  have hzero : (h₀ * (1 : ℝ)) • paddedEuler.A.map (fun a => |a|)
                = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    -- evaluate paddedEuler.A i j = 0 by definition (cycle 209 simp set)
    simp [paddedEuler, Matrix.smul_apply, Matrix.map_apply]
  have hnorm : ‖((h₀ * (1 : ℝ)) • paddedEuler.A.map (fun a => |a|))‖ < 1 := by
    rw [hzero]; simpa using zero_lt_one
  obtain ⟨L_dag, hL_nn, hbound⟩ :=
    paddedEuler.lem_319A (L := 1) (h₀ := h₀)
      (by norm_num) hLip hh hh_le hh₀ hnorm
  exact ⟨L_dag, hL_nn, hbound y₁ z₁ hY hZ⟩
```

The `simp [paddedEuler, ...]` line may need tweaking to match the
exact unfold tactics that worked in the cycle 244 example
(`Section319.lean` near line 230). Mirror that example's idiom.

## §E — What NOT to do

* **DO NOT rename `hY_out` / `hZ_out`** in `Section319.lean` to placate
  the scanner. Those names are correct; the scanner is wrong. The
  documented `h_<name>` → `h<name>` workaround does not apply (the
  scanner is tripping on something else — multi-line theorem-signature
  parsing or the `h • ...` notation). The file is correct as-is.
* **DO NOT edit `scripts/autonomous_loop.py`** from the worker.
  Loop-maintainer territory per `CLAUDE.md` and
  `tautology_scanner_false_positives.md`.
* **DO NOT attempt the inline M-matrix derivation (Option β)** as the
  *primary* path. Relocating MMatrix.lean is ~15 minutes; inlining the
  ~80 LOC Neumann-series derivation duplicates code and worsens
  maintenance. Option β is **Backup B5** only.
* **DO NOT redefine** `Matrix.EntrywiseNonneg`,
  `inv_one_sub_of_norm_lt_one`, or `nonneg_of_one_sub_mulVec_nonneg`
  locally in Section319. Use the relocated module.
* **DO NOT introduce `axiom`/`constant`** for `L^†` or for the
  M-matrix inverse. Cycle 106's Neumann-series proof is constructive.
* **DO NOT raise `maxHeartbeats`** above 200000. The proof above is
  modular by design; if a single tactic stalls, decompose.
* **DO NOT strengthen the smallness hypothesis** beyond
  `‖(h₀ * L) • M.A.map (fun a => |a|)‖ < 1` (Frobenius operator
  norm form). Cycle 106 takes exactly this shape; matching it is
  free.
* **DO NOT poll any Aristotle project.** No submissions in flight.
* **DO NOT attempt `thm:319B`** (Global truncation error theorem, the
  §319 capstone) in cycle 245. That is cycle 246+.

## §F — Risks (predicted failure modes)

* **R1 — `MMatrix` namespace bleed**: the file's `namespace Matrix
  ... end Matrix` block stays intact across the move. **No callers
  cite `OpenMath.Chapter5.MMatrix.…` directly** (verified by the
  cycle 106 design — lemma names live under `Matrix.*`). The import
  rename in §C.2 step 3 is mechanical. *(Severity: very low.)*

* **R2 — Section515 cascade**: cycle 124's
  `aux_515D_iterated_V_bound_linfty` consumes M-matrix lemmas. After
  the relocation it should compile (only the import path changes;
  Lemma names unchanged). Smoke test in §C.2 step 6 catches any
  regression. *(Severity: low-medium.)*

* **R3 — Scope creep**: do NOT attempt `thm:319B` in cycle 245. Phase
  2 + relocation is already 2 substantial deliverables. *(Severity:
  process risk only.)*

* **R4 — Smallness threshold form mismatch**: cycle 106's
  `inv_one_sub_of_norm_lt_one` takes `‖M‖ < 1` (Frobenius scope, the
  default on `Matrix _ _ ℝ` when opening `Matrix.Norms.Frobenius`).
  Make sure §D.2's proof body opens that scope. *(Mitigation: copy the
  cycle 124 idiom from `Section515.lean:2257`.)*

* **R5 — `M.A.map abs` vs entrywise `|·|`**: prefer `.map (fun a => |a|)`
  matching cycle 106's API. Cycle 244's Phase 1 uses `|M.A i j|`
  entrywise (different context); Phase 2 must use the `.map`-style to
  align with the M-matrix machinery. *(Mitigation: pattern-match cycle
  106's API exactly.)*

* **R6 — Stage-difference inequality not in M-matrix shape**: §D.2
  step 5 may need a careful rewrite to expose
  `(1 - K) *ᵥ (‖y₀ - z₀‖ • w - vM) ≥ 0` componentwise before invoking
  the comparison principle. If the rewrite stalls, factor out a
  private helper `vM_le_inv_bound` and ship Phase 2 in stages.
  *(Mitigation: decompose into private helpers; see §G Backup B2.)*

## §G — Backup plans (sorted, highest-priority first)

* **B1** — Both deliverables ship: relocation + `lem_319A` headline +
  non-vacuity example. Update `lean_status.json` (`lem:319A`:
  `partial` → `formalized`) and `plan.md` (`[~]` → `[x]`).
  **Cycle 245 = 2 named deliverables**, plus an example.

* **B2** — Relocation succeeds, Phase 2 partial closure (e.g. the
  stage-difference bound lands as a private helper but the final
  output substitution hits an algebraic glitch). **Ship relocation +
  the private helper + a scoping update to
  `lem_319A_phase2_progress.md`.** `lem:319A` row stays `partial`.

* **B3** — Relocation succeeds but Section515 cascade breaks (R2
  fires). Revert the move, ship Option β instead (Backup B5).

* **B4** — Relocation triggers an unexpected lake/cache issue
  (e.g. olean refuses to invalidate). Revert, ship Option β.

* **B5 (Option β — inline)**: copy the two cycle 106 lemmas (
  `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one` and
  `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`) into a
  `private` section at the top of `Section319.lean`, with a comment
  citing this strategy doc's §C as the reason for duplication. Then
  build §D's Phase 2 proof on top. ~80 LOC of duplication; clean
  fallback.

* **B6 (pivot)** — If all of B1–B5 fail in the first hour, abort §319
  and pivot:
  * **B6a**: `lem:310B "Elementary Differential Weight Formula"`
    (Ch.3 §310) — pure tree combinatorics, low cross-coupling,
    builds on cycle 232+ elementaryWeight infrastructure.
  * **B6b**: `thm:443A "Order arrows for linear multistep methods"`
    (Ch.4 §441) — natural continuation of cycle 240's Section441B.
  * **B6c**: `lem:311A "The Taylor expansion of the exact solution"`
    (Ch.3 §311) — fresh §311 ground.

  Pick whichever has the shortest path to a single-cycle axiom-clean
  shipment. Document the §319 abort in
  `Section319_cycle_245_abort.md`.

## §H — Faithfulness check (for `lem_319A` Phase 2)

* **Entity ID**: `lem:319A`. Textbook statement (Butcher §319 p. 188):
  > "Then `‖y₁ − z₁‖ ≤ (1 + h L^†) ‖y₀ − z₀‖`, where
  > `L^† = L |b|^T (I − h₀ L |A|)^{−1} 𝟙`."

* **Lean statement captures**: **same content modulo packaging**. The
  existential `∃ L_dag, 0 ≤ L_dag ∧ ...` exposes `L^†` as an opaque
  non-negative constant; downstream consumers treat it as such, and
  the closed form `L * ∑ i, |M.b i| * w i` (where `w := (1 - K)⁻¹ *ᵥ
  𝟙`) is the textbook formula expressed in Lean. The two are
  equivalent.

* **Documented divergence — smallness hypothesis**: textbook
  `h₀ L ρ(|A|) < 1` (spectral-radius form) vs Lean
  `‖(h₀ * L) • M.A.map abs‖ < 1` (Frobenius operator-norm form).
  Frobenius dominates spectral, so the Lean hypothesis is **stronger**
  than the textbook's. This matches cycle 107's precedent for
  `aux_515B_eta_contraction` and is the M-matrix machinery's
  built-in hypothesis shape.

* **Tautology check**: conclusion `‖y₁ - z₁‖ ≤ (1 + h * L_dag) *
  ‖y₀ - z₀‖` is not present verbatim in any hypothesis. ✓

* **Identity check**: proof is `lem_319A_recurrences` (cycle 244) +
  M-matrix inverse-positivity (cycle 106) + algebraic substitution.
  Real work, not re-export. ✓

* **Hypothesis strength**: `hL`, `hf_lip`, `hh`, `hh_le`, `hh₀`,
  `h_norm` are all textbook hypotheses (modulo R4's Frobenius-vs-
  spectral divergence). ✓

* **Absent-theorem check**: cycle 244 promised D1, D2, and a
  bundled wrapper. All three are present at `Section319.lean:?` (use
  `lean_file_outline` to verify). Cycle 245 promises Phase 2; the
  end-of-cycle `task_results/cycle_245.md` must list it concretely.

## §I — Time budget

| Step | Target | Hard cap |
|---|---|---|
| §B (verify phantom) | 3 min | 5 min |
| §C (relocate MMatrix) | 15 min | 30 min |
| §D.1 (signature) | 5 min | 10 min |
| §D.2 (proof body) | 50 min | 75 min |
| §D.3 (non-vacuity example) | 10 min | 20 min |
| Docs (`lean_status.json`, `plan.md`, `task_results/cycle_245.md`) | 10 min | 15 min |

If §C exceeds 30 min, bail to Backup B5. If §D.2 exceeds 75 min, ship
what's available and document the rest in
`Section319_phase2_progress.md` (Backup B2).

## §J — Pre-commit checklist

* [ ] `lake env lean OpenMath/Chapter3/Section319.lean` exits 0.
* [ ] `lake env lean OpenMath/Chapter5/Section515.lean` exits 0
  (R2 verification).
* [ ] `lake env lean OpenMath/Chapter5.lean` exits 0.
* [ ] `grep -c sorry OpenMath/Chapter3/Section319.lean` returns `0`.
* [ ] `grep -c sorry OpenMath/Chapter5/Section515.lean` returns the
  cycle 124 baseline (`0`).
* [ ] `lean_verify
  OpenMath.Chapter3.Section312.RKTableau.lem_319A` returns
  `[propext, Classical.choice, Quot.sound]` only.
* [ ] If B1: `git log --stat -1` shows the `OpenMath/Chapter5/MMatrix.lean
  → OpenMath/Matrix/MMatrix.lean` rename plus the two import edits
  plus the Section319 additions.
* [ ] `attempts.md`: append a `Cycle 245 confirmation` row noting the
  cycle 244 phantom verdict and pointing at
  `tautology_scanner_false_positives.md`.
* [ ] If B1: bump `lean_status.json` `lem:319A` from `partial` to
  `formalized` and update `plan.md`'s §319 row to `[x]` with the
  cycle 245 closure note.
* [ ] If B2: leave `partial`/`[~]` and write
  `.prover-state/issues/lem_319A_phase2_progress.md` documenting
  what landed and what's left.
* [ ] If B5: append a `divergence note` to `lem_319A`'s docstring
  documenting the inline M-matrix copy.

## §K — Cycle 246 outlook

After Phase 2 lands:

* **Cycle 246**: `thm:319B "Global truncation error bound via local
  error accumulation"` — the §319 capstone. Composes `lem:319A`
  (one-step contraction) iteratively over `n` steps to bound global
  truncation error against the local-error accumulation lemma. Builds
  directly on cycle 245's `lem_319A` and probably a §301-style local
  error helper.

* **Cycle 247+**: pivot decisions based on `thm:319B` closure.
  Natural candidates:
  * `lem:310B` (Elementary Differential Weight Formula, §310) —
    pure combinatorics.
  * `thm:443A` (Order arrows for LMM, §441) — §441 continuation
    after Section441B (cycle 240).
  * `lem:311A` (Taylor expansion of exact solution, §311) — fresh
    §311 entry.
  * `thm:386A` (Recursive formula for the product, §386) — natural
    continuation of cycles 232–239's §383/§384 group-hom path.

  Pick whichever pairs best with the §319 family or whichever offers
  the shortest single-cycle deliverable.
