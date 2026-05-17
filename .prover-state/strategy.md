# Cycle 344 Strategy

## TL;DR

**Primary target**: Ship the `coef_α(M) = ρ'(1)` algebraic bridge
between cycle 342's `Eq422a`-coefficient notation in `Section422.lean`
and cycle 178's `ρPoly` machinery in `Section441.lean`. Then derive
the positivity corollary `coef_α(M) > 0` for stable preconsistent
LMMs as a one-line consequence of cycle 178's
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent`.

**Why this, not Phase D.3**: the cycle 343 worker's suggested next
step (scaffold `underlyingEta_aux` for Phase D.3) is genuinely
multi-cycle work (100-200 LOC per `def_422B_path.md` §5) and has no
credible single-cycle clean ship. The cycle 343 worker also flagged
a "stability bridge" backup option (`coef_α + coef_β > 0`), but that
variant is NOT a trivial corollary: algebraically
`coef_α + coef_β = β(1) + β'(1)` where β(z) = Σ βᵢ zⁱ, and stability
+ preconsistency alone do not force `β'(1) ≥ 0`. **However**, the
structurally simpler bridge `coef_α(M) = ρ'(1)` IS a clean
preconsistency-only identity and unlocks the positivity claim
`coef_α > 0` directly. This is the right granularity for cycle 344.

**No sorry-first scaffolds.** Per cycle 149/200 rollback precedent,
do not introduce `sorry`. Either ship axiom-clean or skip.

---

## What to ship

All deliverables live in `OpenMath/Chapter4/Section422.lean`,
appended after cycle 342's `Eq422a_at_vertex_eta_eq` block (around
line 672, just before the `end OpenMath.Chapter4.Section422` line).

### P1 (load-bearing, ~30-50 LOC) — `coef_α(M) = ρ'(1)` under preconsistency

Target theorem (signature):

```lean
theorem coef_α_eq_ρPoly_deriv_at_one_of_preconsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hPre : M.IsPreconsistent) :
    (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
      = M.ρPoly.derivative.eval 1
```

Bridge derivation (verified by hand): cycle 178's
`ρPoly_deriv_eval_one_unconditional` (Section441.lean:375) gives
`ρ'(1) = k - Σ M.α i.succ · (k - (i.val + 1))`. Distributing the
subtraction inside the sum and using preconsistency
`Σ M.α i.succ = 1` to collapse `k - k·1 = 0`, the residual sum is
exactly `Σ M.α i.succ · (i.val + 1) = coef_α(M)`.

**Recipe**:

1. `rw [M.ρPoly_deriv_eval_one_unconditional]` — exposes the RHS
   `k - ∑ M.α i.succ · (k - (i.val + 1))`.
2. Use `Finset.sum_congr rfl` + a per-element `ring` step to rewrite
   each summand `M.α i.succ * (k - (i.val + 1))` as
   `M.α i.succ * k - M.α i.succ * (i.val + 1)`.
3. Split via `Finset.sum_sub_distrib`: `∑ (a - b) = ∑ a - ∑ b`.
4. Pull `k` out of `∑ M.α i.succ * k` via `← Finset.sum_mul`,
   yielding `(∑ M.α i.succ) * k`.
5. Substitute `∑ M.α i.succ = 1` using `hPre` (note: `hPre`'s
   shape per `Section404.lean:69-71` is `1 = ∑ i : Fin k, M.α i.succ`,
   so use `← hPre`).
6. Close with `ring`: the goal reduces to
   `∑ (i+1)·α = k - (1 · k - ∑ α·(i+1)) = ∑ α·(i+1)`.

If step 5 has Nat/ℝ cast mismatches (`(i.val + 1 : ℕ) : ℝ` vs
`(i.val : ℝ) + 1`), insert `push_cast` between steps 4 and 5.
Memory `feedback_satisfieseq404b_cast.md` records this cast-bridging
pattern.

**Fallback for step closure**: if the strict `rw + ring` chain
stalls, try `linear_combination hPre * ... + ...` against the
expanded LHS-minus-RHS. Or `lean_multi_attempt` the closing
tactic at the post-step-4 position.

**Faithfulness**: the `IsPreconsistent` definition at
`Section404.lean:69-71` reads
`def IsPreconsistent : Prop := 1 = ∑ i : Fin k, M.α i.succ`. The
hypothesis `hPre` directly provides the right shape. The identity
itself is a textbook fact (Butcher §441 p. 376; consultant
`consultant_advice_cycle_174.md` §A independently verified
`ρ'(1) = Σ i·αᵢ`).

### P2 (~5-10 LOC) — Positivity corollary

```lean
theorem coef_α_pos_of_stable_preconsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hk : 0 < k) (hStab : M.IsStable) (hPre : M.IsPreconsistent) :
    0 < ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ := by
  rw [coef_α_eq_ρPoly_deriv_at_one_of_preconsistent M hPre]
  exact M.ρPoly_deriv_eval_one_pos_of_stable_preconsistent hk hStab hPre
```

Direct composition of P1 with cycle 178's
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent`
(Section441.lean:767).

### P3 (stretch, ~20-30 LOC) — Non-vacuity examples

Two examples confirming the bridge on concrete methods:

```lean
/-- Non-vacuity for P1: `explicitEulerLMM`'s `coef_α = 1` matches
the §441 closed form `ρ'(1) = 1` at k=1, α₁ = 1. -/
example :
    (∑ i : Fin 1, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.explicitEulerLMM.α i.succ) = 1 := by
  simp [OpenMath.Chapter4.Section404.explicitEulerLMM, Fin.sum_univ_one]

/-- Non-vacuity for P1: `bdf2LMM`'s `coef_α = 2/3` matches cycle 176's
`bdf2LMM_ρPoly_deriv_eval_one_eq = 2/3` at k=2, α₁=4/3, α₂=-1/3:
1·(4/3) + 2·(-1/3) = 4/3 - 2/3 = 2/3. -/
example :
    (∑ i : Fin 2, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section451.bdf2LMM.α i.succ) = 2 / 3 := by
  simp [OpenMath.Chapter4.Section451.bdf2LMM, Fin.sum_univ_two]
  norm_num
```

**Worker check**: verify the BDF2 namespace at the start of cycle.
Grep `grep -rn "def bdf2LMM" OpenMath/Chapter4/` — should be in
`Section451.lean` per `lem_441A_alpha_prime_negative.md` cycle 175
update. If it's at a different path, adjust the qualified name.

If the bdf2LMM example requires a fresh import that breaks the
Section422 compile, ship only the explicitEulerLMM example.

---

## What NOT to do

* **Do NOT attempt Phase D.3** (inductive η-recursion on RootedTree).
  Per `def_422B_path.md` §5 and §6, it's 100-200 LOC and at HIGH risk.
  The cycle 343 worker's "Suggested next approach" of a sorry-first
  `underlyingEta_aux` scaffold with a TODO body is exactly the
  pattern that triggered cycle 149→150 (def:530B) and cycle 200→201
  (thm:381H) rollbacks. **Do not introduce `sorry`.**

* **Do NOT attempt the `coef_α + coef_β > 0` bridge.** This is NOT a
  trivial corollary of stability + preconsistency. Algebraically:
  `coef_α + coef_β = σ(1) + σ'(1)` where σ(z) = Σ βᵢ zⁱ. For stable
  preconsistent M, only `coef_α = ρ'(1) > 0` is forced by cycle 178;
  `σ'(1) ≥ 0` is method-specific. The cycle 343 worker's "quick win"
  framing for this bridge underestimated the analytical content.
  Numerical sanity: explicit Euler `σ'(1) = 1`, implicit Euler
  `σ'(1) = 0`, trapezoidal `σ'(1) = 1/2`, BDF2 `σ'(1) = 0` — all
  ≥ 0 in these standard cases but not always strictly positive, and
  no obvious general bound from cycle 178's machinery.

* **Do NOT rewrite `Eq422a_at_vertex_eta_eq`** (cycle 342) to consume
  `coef_α_pos_of_stable_preconsistent` instead of the explicit
  non-vanishing hypothesis. The cycle 344 ship is purely additive:
  add P1 and P2 as new theorems; leave cycle 342's signature alone.
  Removing the explicit hypothesis would require also threading
  `coef_β` positivity (or non-vanishing of the sum), which is not
  in scope.

* **Do NOT pivot to a fresh entity** unless P1 stalls in compile.
  The §422 streak (cycles 336-343, eight consecutive ships) compounds
  value — P1 + P2 directly enable cycle 345's Phase D.3 attempts
  because the recursive solver will need to invoke
  `coef_α + coef_β ≠ 0` at every step, and having `coef_α > 0` as a
  separate fact simplifies threading.

* **Do NOT submit to Aristotle.** P1 + P2 + P3 are small mechanical
  computations; no premise selection needed. Manual closure is
  faster than the polling cycle (cycles 343/342/341 all closed
  manually under ~60 min).

* **Do NOT touch `Section441.lean` directly.** Its history of GPFS
  timeouts (cycles 182-237, 43+ consecutive timeouts at one point)
  is documented in `cycle_182_gpfs_slowness.md`. The cycle 344 ship
  imports Section441 but does not edit it.

---

## Recipe specifics

### Pre-flight: Section441 import smoke test

**Before editing Section422.lean**, verify Section441.lean still
builds cleanly:

```bash
time timeout 60 lake env lean OpenMath/Chapter4/Section441.lean
```

Expected: exit 0 in < 60s (recent post-cycle-237 builds have been
healthy). If it times out:
- Log the timeout to `.prover-state/issues/cycle_182_gpfs_slowness.md`
  as a fresh entry.
- Retry with `time timeout 300 lake env lean ...` (5-min budget).
- If still failing, ship P1 alone without P2/P3 (P1 only needs
  `ρPoly_deriv_eval_one_unconditional` which doesn't require
  cycle 178's positivity result; but the import statement still
  pulls the whole Section441.lean transitive closure, so a
  Section441 compile failure may cascade). Worst case: pivot to a
  fresh entity per the abort ladder below.

If Section441.lean builds, the import in Section422.lean is safe.

### Imports needed in Section422.lean

Check the existing import block at the top of Section422.lean.
The file currently imports `OpenMath.Chapter3.Section381` (for the
§383 quotient group machinery) and indirectly `Section404`. For
cycle 344's P1/P2 you need explicit access to:

* `LinearMultistepMethod.ρPoly` (Section441.lean:313)
* `LinearMultistepMethod.ρPoly_deriv_eval_one_unconditional`
  (Section441.lean:375)
* `LinearMultistepMethod.ρPoly_deriv_eval_one_pos_of_stable_preconsistent`
  (Section441.lean:767)

Add the import line:

```lean
import OpenMath.Chapter4.Section441
```

If the namespace is not auto-opened, qualify references as
`OpenMath.Chapter4.Section404.LinearMultistepMethod.ρPoly` etc.
(the lemmas live in the `Section404.LinearMultistepMethod`
namespace per the Section441.lean source).

### Axiom-clean verification

After shipping P1/P2/P3, run:

```bash
echo '#print axioms OpenMath.Chapter4.Section422.coef_α_eq_ρPoly_deriv_at_one_of_preconsistent' \
  | lake env lean --stdin OpenMath/Chapter4/Section422.lean
echo '#print axioms OpenMath.Chapter4.Section422.coef_α_pos_of_stable_preconsistent' \
  | lake env lean --stdin OpenMath/Chapter4/Section422.lean
```

Expected output: `[propext, Classical.choice, Quot.sound]` (the
standard trio). If `sorryAx` appears, the proof is incomplete —
fix before commit. **Workaround for stale .olean cache** (per
cycle 343 task results §Dead ends): if `#print axioms` reports
"unknown constant", add the `#print axioms` directives inline at
the bottom of Section422.lean, run via single `lake env lean
OpenMath/Chapter4/Section422.lean` invocation, capture the output,
then remove the directives before commit.

---

## End-of-cycle housekeeping

1. **No `lean_status.json` changes needed**: P1+P2+P3 are
   infrastructure additions to a `[~] partial` entity (`def:422B`).
   The entity stays partial; cycle reference bump (342 → 344) is
   optional and may be skipped.
2. **plan.md** — no changes needed; the `[~]` mark is correct.
   Optionally update the long inline note on `def:422B` with a one-
   line cycle 344 addendum.
3. **task_results/cycle_344.md** — standard sections per CLAUDE.md.
   In §"Suggested next approach" recommend Phase D.3 (now that the
   positivity bridge is in hand) OR a pivot to `thm:302A`/`thm:302C`
   for variety. The Phase D.3 entry point in `def_422B_path.md`
   §"Cycle 344 entry point" is unchanged.
4. **`def_422B_path.md`** — append a "Cycle 344 update" section
   under §A.0.2 closure (or its own section) recording the bridge
   ship. Note that the cycle 342 §"Cycle 343 entry point" Phase D.2
   prediction held; the cycle 343 §"Cycle 344 entry point" Phase D.3
   prediction was sidestepped for granularity reasons but remains
   the cycle 345+ target.
5. **No new issue file needed** — the cycle 344 ship is purely
   additive, no new blockers surfaced.
6. **memory** — no new memory entries needed; the cast bridging in
   P1 is already captured by `feedback_satisfieseq404b_cast.md`.

---

## Abort / fallback ladder

* **If P1 compiles and closes axiom-clean**: ship P1+P2+P3 as
  planned. Cycle 344 closes clean.
* **If P1 closes but P2 fails on Section441 import**: ship P1 + P3
  (explicitEulerLMM example only). Phase B.2 corollary
  `coef_α > 0` deferred to cycle 345; not a regression.
* **If P1's proof recipe stalls after 30 min**: time-box and
  `lean_multi_attempt` the closing step at the post-step-4
  position. If still stuck, decompose: ship
  `coef_α_eq_ρPoly_deriv_at_one_unconditional` (without
  preconsistency, just the algebraic sum-split as an intermediate
  identity) as a private helper, then P1 becomes a one-line
  application + `hPre`. Cycle worker is allowed to define such a
  private helper if it brings the proof under budget.
* **If the Section441 import causes Section422 compile to balloon
  past 5 min**: skip P2/P3 entirely. Ship only P1 with the
  necessary lemma re-stated inline as a `have` (consume cycle 178's
  `ρPoly_deriv_eval_one_unconditional` once at the top of P1's
  proof). This avoids transitive Section441 load.
* **If P1 fails AND Section441 import is broken**: pivot to a fresh
  entity. Recommended single-cycle candidates from plan.md:
  - `thm:302A` (combinatorial questions, §302) — pure tree
    combinatorics, depends only on cycle 254-270 infra. Read
    `extraction/formalization_data/entities/thm_302A.json` first.
  - `thm:302C` (rooted tree enumeration formulas, §302) — similar
    profile. Read entity JSON first.
  - **AVOID** `thm:302B` (generating function identity) — requires
    `PowerSeries` infrastructure (cycle 237 precedent: it took a
    dedicated `Section441B.lean` file to sidestep GPFS issues).

---

## Verification checklist before commit

- [ ] `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.
- [ ] `lake env lean OpenMath/Chapter4.lean` (aggregator) exits 0.
- [ ] `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 0.
- [ ] Tautology scanner: `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter4/Section422.lean` returns no hits.
- [ ] `#print axioms` on P1 and P2 returns `[propext, Classical.choice, Quot.sound]` only.
- [ ] No new files created in `.prover-state/issues/` (cycle 344 is purely additive).
- [ ] `task_results/cycle_344.md` written following the CLAUDE.md template.

If all six pass, commit with message:
`Cycle 344 — §422 Phase D infrastructure: coef_α↔ρ'(1) bridge + positivity corollary shipped.`
