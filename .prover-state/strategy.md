# Cycle 202 strategy

## TL;DR

Build directly on cycle 201's Banach fixed-point foundation in
`OpenMath/Chapter3/Section381.lean`. Two concrete targets, both
axiom-clean, both touching only Section381:

1. **P1** — Ship `RKStageMap_contracting`: package
   `RKStageMap_lipschitz` (cycle 201) plus the smallness hypothesis
   `|h| * L * (∑ᵢⱼ |aᵢⱼ|) < 1` as a `ContractingWith` instance.
   Short (~30 LOC). Validates the foundation is correctly shaped for
   Mathlib's fixed-point API.
2. **P2** — Generalize `RKStageMap`, `RKStageMap_dist_le`,
   `RKStageMap_lipschitz`, and the `paddedEuler` witness from scalar
   `f : ℝ → ℝ` to a normed-space-valued `f : N → N` with
   `[NormedAddCommGroup N] [NormedSpace ℝ N]`. Mechanical port — the
   inequality structure is identical, only `abs / Real.dist` must be
   replaced with `‖·‖ / dist`. Required because `IsRKOneStep` (the
   downstream consumer) is polymorphic; without it cycle 201's
   foundation is dead-ended at scalar problems.

Sorry-count target: 0 → 0 (everything axiom-clean).

Cycle 203 picks up from here with `equivalent_self` (general
reflexivity, closing half of `equivalent_self_general_deferred.md`)
once both P1 and P2 are landed.

---

## Skip P0 (no GPFS smoke test)

The §441 Phase C.2 compile has timed out **21 consecutive cycles**
(cycles 182–201, ≈20 calendar days, all with EXIT=124 / negligible
CPU). The loop-maintainer escalation is in place at
`.prover-state/issues/cycle_182_gpfs_slowness.md`. Running a 22nd
smoke test wastes 5 minutes for no information. **Do not attempt the
Section441 compile this cycle.** If GPFS recovers between cycles, the
next planner will pick it up; until then the §441 work is genuinely
blocked at the maintainer level, not the worker level.

(One quick `time timeout 120 lake env lean OpenMath/Chapter4/Section441.lean &`
in background while you do P1/P2 is fine if you want the 22nd data
point logged, but don't *wait* on it.)

---

## P1 — Ship `RKStageMap_contracting` (~30 LOC, single theorem)

### Statement

Place immediately after `RKStageMap_lipschitz` in
`OpenMath/Chapter3/Section381.lean` (currently at line ~1670, inside
`namespace OpenMath.Chapter3.Section312.RKTableau`):

```lean
/-- *Contracting form* of `RKStageMap_lipschitz`. When the step size
`h` is small enough that `|h| * L * (∑ᵢⱼ |aᵢⱼ|) < 1`, the implicit-
stage iteration map `RKStageMap` is a contraction on `Fin s → ℝ`,
hence has a unique fixed point by Banach. This is the cycle-202
foundation for closing `equivalent_self` (def:381A reflexivity) at
arbitrary `M`; the smallness condition matches Butcher's tacit
"for h sufficiently small" qualifier in §380. -/
theorem RKStageMap_contracting {s : ℕ} (M : RKTableau s) (h : ℝ)
    {f : ℝ → ℝ} {L : NNReal} (hf : LipschitzWith L f) (y₀ : ℝ)
    (hLt : |h| * L * (∑ i : Fin s, ∑ j : Fin s, |M.A i j|) < 1) :
    ContractingWith
      ⟨|h| * L * (∑ i : Fin s, ∑ j : Fin s, |M.A i j|),
       mul_nonneg (mul_nonneg (abs_nonneg _) L.coe_nonneg)
         (Finset.sum_nonneg fun _ _ =>
           Finset.sum_nonneg fun _ _ => abs_nonneg _)⟩
      (M.RKStageMap h f y₀) := by
  refine ⟨?_, M.RKStageMap_lipschitz h hf y₀⟩
  -- Goal: (⟨..., _⟩ : NNReal) < 1
  exact hLt
```

### Closure recipe

`ContractingWith K f` is defined as `K < 1 ∧ LipschitzWith K f` in
Mathlib (`Mathlib.Topology.MetricSpace.Contracting`). So this is just
two-component packaging:

* The `K < 1` half is `hLt` — but note the coercion direction. In
  Mathlib `ContractingWith` puts `K < 1` first; the comparison is
  `(K : ℝ≥0) < 1`. With `K := ⟨|h| * L * sum, hK_nn⟩ : NNReal`, the
  cast `((K : NNReal) : ℝ) = |h| * L * sum` makes `hLt` discharge it
  directly. If the `refine` produces a goal in `NNReal`-comparison
  form (`K < 1` as NNReal), use `NNReal.coe_lt_one.mp` or
  `show (K : ℝ) < 1`.
* The `LipschitzWith K f` half is verbatim
  `M.RKStageMap_lipschitz h hf y₀`.

### Verification

```bash
# Single rebuild (warm cache from cycle 201 makes this ~5s).
lake env lean OpenMath/Chapter3/Section381.lean
```

Then check axioms via Lean LSP:

```
lean_verify "OpenMath.Chapter3.Section312.RKTableau.RKStageMap_contracting"
```

Expected: `[propext, Classical.choice, Quot.sound]`.

### Common pitfalls

* **`ContractingWith` uses an explicit `NNReal` parameter, not
  `K : ℝ` with a positivity proof.** Cycle 201's
  `RKStageMap_lipschitz` already constructs the right NNReal; reuse
  it verbatim. Do NOT introduce a fresh NNReal — the elaborator must
  see the same anonymous constructor `⟨..., _⟩` in both
  `RKStageMap_lipschitz`'s output type and `RKStageMap_contracting`'s
  output type, otherwise the second conjunct won't unify.
* **NNReal coercion direction.** `((⟨x, hx⟩ : NNReal) : ℝ) = x`
  by `NNReal.coe_mk`; `((⟨x, hx⟩ : NNReal) < 1)` reduces to `x < 1`
  via `NNReal.coe_lt_one` — but you may not need this if the
  underlying `Subtype.lt` unfolds correctly. Try the bare
  `exact hLt` first; if it fails, wrap in `show (... : ℝ) < 1` or
  reach for `NNReal.coe_lt_coe` / `NNReal.lt_iff_lt_of_le_iff_le`.

---

## P2 — Generalize `RKStageMap` to normed-space `N`

### Why this is necessary

`IsRKOneStep` (line 922 of Section381.lean) is defined for
`{N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]` and
`f : N → N`. So is `Equivalent` (line 967):

```lean
def Equivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') : Prop :=
  ∀ {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (L : ℝ≥0) (_hL : LipschitzWith L f) (y₀ : N),
    ∃ h₀ > (0 : ℝ), ...
```

Cycle 201's scalar `RKStageMap` cannot bridge to either of these. The
cycle-203+ `equivalent_self M` proof needs the polymorphic version.

### Mechanical port — what to change

In `OpenMath/Chapter3/Section381.lean` lines 1582–1670 (the
`RKStageMap` def + two theorems), replace:

```
{f : ℝ → ℝ}                   →   {N : Type*} [NormedAddCommGroup N]
                                    [NormedSpace ℝ N] {f : N → N}
y₀ : ℝ                         →   y₀ : N
RKStageMap : ... → (Fin s → ℝ) →   RKStageMap : ... → (Fin s → N)
y₀ + h * Σⱼ M.A i j * f (Y j)  →   y₀ + h • Σⱼ M.A i j • f (Y j)
abs / Real.dist                →   ‖·‖ / dist (already metric API)
```

The proof bodies for `RKStageMap_dist_le` and `RKStageMap_lipschitz`
**transfer almost verbatim** because every step uses metric/normed
inequalities that work uniformly:

* `dist_pi_le_iff` — works for `Fin s → N` whenever `N` is a
  `PseudoMetricSpace` (which follows from `NormedAddCommGroup`).
* `Finset.abs_sum_le_sum_abs` — replace with
  `norm_sum_le` on the inner
  `‖∑ⱼ M.A i j • (f(Y j) - f(Y' j))‖ ≤ ∑ⱼ ‖M.A i j • (f(Y j) - f(Y' j))‖`.
* `abs_mul` — replace with `norm_smul` for the scalar action:
  `‖M.A i j • v‖ = ‖M.A i j‖ * ‖v‖`. Note that for `M.A i j : ℝ`,
  `‖M.A i j‖ = |M.A i j|` (real-norm = absolute value), so the
  outer coefficient `|M.A i j|` stays the same in the bound — use
  `Real.norm_eq_abs` to bridge.
* `LipschitzWith.dist_le_mul` — works unchanged (it's already on
  generic metric spaces).
* `dist_le_pi_dist` — works unchanged.
* `Finset.single_le_sum` — works unchanged.
* `Real.dist_eq` (uses `abs`) — replace with
  `dist_eq_norm` (the generic version: `dist x y = ‖x - y‖`).

The cycle-201 `hcomp`'s critical line

```lean
have heq : (M.RKStageMap h f y₀ Y i) - (M.RKStageMap h f y₀ Y' i)
    = h * ∑ j, M.A i j * (f (Y j) - f (Y' j)) := by
  simp only [RKStageMap]
  rw [show y₀ + h * ∑ j, M.A i j * f (Y j)
        - (y₀ + h * ∑ j, M.A i j * f (Y' j))
      = h * (∑ j, M.A i j * f (Y j) - ∑ j, M.A i j * f (Y' j)) by ring,
      ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring
```

becomes (note `•` everywhere):

```lean
have heq : (M.RKStageMap h f y₀ Y i) - (M.RKStageMap h f y₀ Y' i)
    = h • ∑ j, M.A i j • (f (Y j) - f (Y' j)) := by
  simp only [RKStageMap]
  rw [show y₀ + h • ∑ j, M.A i j • f (Y j)
        - (y₀ + h • ∑ j, M.A i j • f (Y' j))
      = h • (∑ j, M.A i j • f (Y j) - ∑ j, M.A i j • f (Y' j)) by
        simp [smul_sub, sub_smul, add_sub_add_left_eq_sub, smul_sum],
      ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by simp [smul_sub]
```

If `ring` / `simp` on the smul-sub algebra is brittle, fall back to
the `module` tactic (which handles linear-combinations in a normed
module the way `ring` handles ring identities).

### `RKStageMap_lipschitz` port

The `LipschitzWith ⟨...⟩` constant is unchanged — the bound
`|h| * L * (∑ |aᵢⱼ|)` is the same real number whether the codomain
is `ℝ` or `N`. Only the body of the proof changes (one-line wrapper
around the new `_dist_le`).

### `paddedEuler` non-vacuity witness

In the cycle-201 example at the bottom (paddedEuler `LipschitzWith 0`
witness), the only change is to specialise back to `f : ℝ → ℝ` for
the example — the scalar instance still works because `ℝ` is itself
a normed space over `ℝ`. The example body becomes:

```lean
example (f : ℝ → ℝ) (y₀ : ℝ) :
    LipschitzWith 0 (paddedEuler.RKStageMap (h := 1) f y₀) := by
  -- (Same body as cycle 201 — funext + simp [paddedEuler, RKStageMap]
  -- + LipschitzWith.const, all of which generalize.)
```

If keeping the example as `f : ℝ → ℝ` with `paddedEuler : RKTableau 2`
on `ℝ` still type-checks, leave it. Otherwise add a sibling example
on a generic `N`.

### Verification

```bash
lake env lean OpenMath/Chapter3/Section381.lean
```

Then via Lean LSP:

```
lean_verify "OpenMath.Chapter3.Section312.RKTableau.RKStageMap"
lean_verify "OpenMath.Chapter3.Section312.RKTableau.RKStageMap_dist_le"
lean_verify "OpenMath.Chapter3.Section312.RKTableau.RKStageMap_lipschitz"
lean_verify "OpenMath.Chapter3.Section312.RKTableau.RKStageMap_contracting"
```

All four should return `[propext, Classical.choice, Quot.sound]`.

### Common pitfalls

* **`ring` vs `module` vs `simp [smul_sub, sub_smul, smul_sum]`.**
  `ring` does not work in modules over `ℝ` because it expects a
  commutative ring structure on the value type. Use `module` (Mathlib
  tactic for module-linear identities) or hand-rolled `simp`. If both
  fail, `linear_combination` with explicit terms works in modules.
* **Scalar-action ambiguity.** `h • ∑ j, ...` and `∑ j, h • ...`
  might not be definitionally equal — use `Finset.smul_sum` to
  commute. Similarly `M.A i j • (a - b) = M.A i j • a - M.A i j • b`
  requires `smul_sub`, not `mul_sub`.
* **`norm_sum_le` is the right name** (not `Finset.norm_sum_le`):
  `‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖`. Verify with
  `lean_local_search "norm_sum"` if the name fails.
* **`Real.norm_eq_abs` bridges `‖x : ℝ‖ = |x|`.** Use it to keep the
  bound expressed as `|M.A i j|` rather than `‖M.A i j‖`.
* **Naming clash on `dist_eq_norm`.** Mathlib has both `dist_eq_norm`
  (additive groups) and `NormedAddCommGroup.dist_eq` (the simp lemma
  derived from the instance). Either works; `dist_eq_norm` is shorter.

### Aristotle option

If P2 stalls on the `module`/`smul`-arithmetic, submit just the
generalization to Aristotle as a tightly-scoped batch — the generic
ports of `_dist_le` and `_lipschitz` are exactly the kind of "rewrite
the proof by analogy" task Aristotle handles well. **Do not submit
P1** (it's a 30-LOC packaging that should close in 2 minutes
manually).

---

## P3 (stretch — only if P1+P2 land cleanly with cycle budget remaining)

If P1 and P2 both compile clean within ~60 minutes of cycle time,
you have an opening to begin `equivalent_self M` for general `M`.
The recipe (Butcher §380 tacit argument, formalised):

```lean
open scoped NNReal in
theorem equivalent_self {s : ℕ} (M : RKTableau s) :
    M.Equivalent M := by
  intro N _ _ f L hL y₀
  -- Choose h₀ small enough that the contraction condition holds.
  set C : ℝ := ∑ i : Fin s, ∑ j : Fin s, |M.A i j| with hC_def
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- h₀ := 1 / (2 * (L * C + 1))   -- guarantees |h| ≤ h₀ ⇒ |h|·L·C ≤ 1/2 < 1
  refine ⟨1 / (2 * (L * C + 1)), by positivity, ?_⟩
  intro h hh_pos hh_le y₁ y₁' hRK hRK'
  -- Both stage solutions are fixed points of the (now-contracting) map.
  have hContract : ContractingWith ⟨|h| * L * C, by positivity⟩
      (M.RKStageMap h f y₀) := by
    apply M.RKStageMap_contracting h hL y₀
    -- Need |h| * L * C < 1, from hh_le.
    sorry  -- arithmetic; cycle 203
  obtain ⟨Y, hY_stage, hy₁⟩ := hRK
  obtain ⟨Y', hY'_stage, hy₁'⟩ := hRK'
  have hYfix : M.RKStageMap h f y₀ Y = Y := by
    funext i; exact (hY_stage i).symm
  have hY'fix : M.RKStageMap h f y₀ Y' = Y' := by
    funext i; exact (hY'_stage i).symm
  have hUnique : Y = Y' :=
    hContract.fixedPoint_unique' hYfix hY'fix
  rw [hy₁, hy₁', hUnique]
```

Multiple sorries here — the arithmetic discharge of
`|h| * L * C < 1` from `h ≤ 1/(2(L·C+1))` is non-trivial (needs
case-split on `L * C = 0`). And `hContract.fixedPoint_unique'` may
not be the right Mathlib name; check
`lean_local_search "ContractingWith.fixedPoint_unique"` or similar.
**If this stretch goal would leave a sorry behind, do not commit
it.** Just land P1+P2 and write the recipe into the cycle 202 task
results for cycle 203 to consume.

---

## NOT to do (failed approaches, supervisor policy, blocked work)

1. **Do NOT attempt the §441 Phase C.2 compile.** 21 consecutive
   GPFS timeouts (cycles 182–201). Loop-maintainer territory;
   running it again yields no information.
2. **Do NOT reintroduce the cycle-200 `thm:381H` scaffold.** Cycle
   201 rolled it back specifically because sorry count went 0 → 3.
   Per the cycle 201 rollback note in
   `.prover-state/issues/thm_381H_deferred.md`, re-introduction
   must wait until at least one of the three remaining iff-directions
   can close in the same cycle (so sorry count goes 0 → 2 max). That
   requires either (a) closing `PEquivalent → Equivalent` first
   (cycles 202–203 path), or (b) thm:381G prerequisites (4–5 cycles
   of separate work).
3. **Do NOT tighten the Lipschitz bound to the sup-norm row form
   `|h| · L · max_i Σⱼ |aᵢⱼ|`.** Cycle 201 strategically chose the
   loose entrywise bound `|h| · L · Σ_{i,j} |aᵢⱼ|` to avoid PiLp
   instance fiddliness. The loose form scales linearly in `h` and
   is sufficient for Banach FP. Tightness is a future-cycle
   refinement; don't burn cycle 202 on it.
4. **Do NOT bump `maxHeartbeats` above 200000.** If a proof stalls,
   decompose into named helpers — never raise the budget. Per
   CLAUDE.md.
5. **Do NOT introduce `axiom` or `constant` declarations.** Every
   new declaration must be axiom-clean
   (`[propext, Classical.choice, Quot.sound]` only).
6. **Do NOT poll Aristotle multiple times in one cycle.** If you
   submit P2 to Aristotle as a fallback, single-poll discipline
   applies (CLAUDE.md). Submit, sleep ~30 min, check once.
7. **Do NOT delete or modify cycle-201 work beyond the P2
   generalisation.** `RKStageMap`, `RKStageMap_dist_le`,
   `RKStageMap_lipschitz` are foundational — the P2 generalisation
   replaces their bodies but keeps their names and roles. Keep the
   cycle-201 docstrings (they correctly describe the new generalised
   form too, with minimal edits).
8. **Do NOT modify `scripts/autonomous_loop.py`.** Workers do not
   touch the loop machinery (CLAUDE.md). The phantom-verdict /
   GPFS / scanner issues are loop-maintainer territory.

---

## Verification checklist (before commit)

```bash
# 1. Single-file compile of Section381.
time lake env lean OpenMath/Chapter3/Section381.lean
# Expect ~10s warm rebuild; flag if > 60s.

# 2. Sorry count.
grep -cE "^[[:space:]]+sorry$" OpenMath/Chapter3/Section381.lean
# Expect 0.

# 3. Tautology scanner.
grep -E ":=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$" \
  OpenMath/Chapter3/Section381.lean
# Expect no matches (rename `h_<name>` → `h<name>` if any appear,
# per the standing tautology_scanner_false_positives.md workaround).

# 4. Axiom check on every new theorem (use lean_verify MCP).
#    All must return [propext, Classical.choice, Quot.sound].
```

If sorry count rises above 0 or any new theorem fails axiom check,
**revert the offending edit and re-attempt next cycle**. Do not
commit a regression. Sorry-count discipline (the cycle 200 → 201
rollback precedent) is non-negotiable.

---

## Faithfulness checklist (if P3 stretch is attempted)

For `equivalent_self M` (textbook def:381A reflexivity):

* Entity: not a textbook-named theorem; def:381A's reflexivity is
  asserted implicitly by Butcher when he writes "M is equivalent
  to M". The Lean type matches def:381A applied diagonally.
* No new hypothesis strengthening — the smallness `h₀` choice is
  internal (existentially quantified, matching def:381A's
  `∃ h₀ > 0, ...` shape).
* Documents the cycle-202 entry in
  `equivalent_self_general_deferred.md` as RESOLVED for the
  diagonal case.

For P1/P2 (no faithfulness concern — these are infrastructure with
no textbook counterpart).

---

## Cycle 203 preview (so you know where this leads)

Once P1 + P2 land:

* **Cycle 203**: ship `equivalent_self` (general reflexivity) by the
  P3 recipe above. ~80 LOC. Closes half of
  `equivalent_self_general_deferred.md`. Sorry-count 0 → 0.
* **Cycle 204**: lift `equivalent_self` to a P-equivalence-aware
  variant by combining with the P-partition iteration invariant —
  i.e. start the `PEquivalent → Equivalent` direction of `thm:381H`.
* **Cycle 205+**: re-introduce the `thm:381H` scaffold with at most
  2 remaining sorries (the `PhiEquivalent → PEquivalent` and
  `Equivalent → PEquivalent` directions, both blocked on `thm:381G`).

This is the spine of §380 closure. Stay on it until either GPFS
recovers (then re-attack §441 Phase C.2) or one of the §380 cycles
runs out of room.
