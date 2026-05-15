# Cycle 247 Strategy — `thm:319B` Phase 2 (geometric sum closed form)

## TL;DR

Cycle 246 shipped Phase 1 of `thm:319B` (`accumulation_recurrence`, the
inductive accumulation inequality) axiom-clean. **Cycle 247 ships Phase 2**:
specialise `δ_k ≤ C h^{p+1}` and bound the geometric sum to recover the
textbook headline bound on the global truncation error. After Phase 2,
`thm:319B` is fully formalized and the §319 Butcher chapter is complete
(both `lem:319A` and `thm:319B` formalized).

**Important meta-note**: Cycle 246's score = −1 was a tautology-scanner
false positive (`semantic_sorry_count 4→8`). The actual sorry count is 0;
the new "hits" at `Section319.lean` are scanner false positives on
hypothesis declarations / docstring patterns in the cycle-246 additions,
exactly the documented over-firing pattern from
`tautology_scanner_false_positives.md`. **DO NOT attempt to "fix" any
code in response to the −1 score.** Trust `grep -c sorry` (= 0) and
`lean_verify` output. Per CLAUDE.md, scanner patches are loop-maintainer
territory; the worker must not edit `scripts/autonomous_loop.py`.

---

## §A. Priority 0 — verify the current state

Run these once at the start of the cycle to confirm Phase 1 ships:

```bash
git log -1 --format='%H %s'
# Expected: d21babd Cycle 246 — §319 thm:319B Phase 1 (accumulation recurrence) SHIPPED.

grep -c sorry OpenMath/Chapter3/Section319.lean
# Expected: 0

wc -l OpenMath/Chapter3/Section319.lean
# Expected: ~871 (cycle 246 grew it from 474)
```

If these match, proceed to §B. If any disagree, escalate via a short
heartbeat note and do not attempt Phase 2 until reconciled.

**DO NOT run the §441 GPFS smoke test** — 43 consecutive timeouts (cycles
182–239) confirm the pathology is entrenched cluster-side. The cycle 247
deliverable is §319, not §441; §441 Phase C remains GPFS-blocked.

---

## §B. Substantive target: `thm:319B` Phase 2

### Textbook statement (from `entities/thm_319B.json` + cycle 246 task results)

> Provided the local truncation error has the bound
> `‖y(x_k) − ŷ_k‖ ≤ C h^{p+1}` for all `k = 1, …, n`, and the conditions
> of Lemma 319A hold, the global truncation error has the bound
>
>   `‖y(x_n) − y_n‖ ≤ (exp(L^†(x_n − x_0)) − 1) / L^† · C h^p`     (if L^† > 0)
>
> degenerating to
>
>   `‖y(x_n) − y_n‖ ≤ (x_n − x_0) · C h^p`                          (if L^† = 0).

Cycle 246's `accumulation_recurrence` (`Section319.lean`) ships:

```
‖yex_n − traj_n‖ ≤ (1 + h L^†)^n · ‖yex_0 − traj_0‖
                  + ∑_{k=0}^{n-1} (1 + h L^†)^{n-1-k} · δ_k
```

Phase 2 specialises this to the textbook headline. The four ingredient
steps are listed in cycle 246's "Suggested next approach".

### Phase 2 deliverable structure

Three new public theorems in `OpenMath/Chapter3/Section319.lean`, plus
two private helpers. All in the existing namespace from cycles 244–246.

#### D1 (private helper): `geometric_sum_one_plus`

Closed form (or near-closed form) for the geometric sum
`∑_{k < n} (1 + a)^(n - 1 - k)`. Split into two private helpers:

```lean
private lemma geometric_sum_one_plus_pos (a : ℝ) (n : ℕ) (ha : 0 < a) :
    ∑ k : Fin n, (1 + a)^(n - 1 - k.val) = ((1 + a)^n - 1) / a := …

private lemma geometric_sum_one_plus_zero (n : ℕ) :
    ∑ k : Fin n, (1 + (0 : ℝ))^(n - 1 - k.val) = (n : ℝ) := …
```

Pull `(C * h^(p+1))` out of the sum via `Finset.mul_sum` (or its flipped
sibling); the geometric helper handles the remainder.

#### D2 (private helper): `pow_one_add_le_exp`

```lean
private lemma pow_one_add_le_exp (a : ℝ) (n : ℕ) (ha : 0 ≤ a) :
    (1 + a)^n ≤ Real.exp ((n : ℝ) * a) := …
```

#### D3 (main public theorem): `RKTableau.thm_319B`

The headline bound. Statement sketch (fix names / binders precisely
when writing):

```lean
theorem thm_319B
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {s : ℕ} (M : RKTableau s)
    {f : N → N} {L : ℝ≥0} (hL_pos : 0 < (L : ℝ))
    (hLip : LipschitzWith L f)
    {h₀ : ℝ} (hh₀_pos : 0 < h₀)
    (hsmall : ‖(h₀ * (L : ℝ)) • M.A.map (·|·|)‖ < 1)
    {h : ℝ} (hh_pos : 0 < h) (hh_le : h ≤ h₀)
    {C : ℝ} (hC_nn : 0 ≤ C) {p : ℕ}
    {n : ℕ}
    {yex : Fin (n + 1) → N} {traj : Fin (n + 1) → N}
    (htraj : M.IsRKTrajectory f h traj)
    (h_init_eq : yex 0 = traj 0)
    (h_lte : M.HasLocalTruncationErrorBound f h yex
              (fun _ => C * h^(p + 1))) :
    ∃ L_dag : ℝ, 0 ≤ L_dag ∧
      ‖yex (Fin.last n) - traj (Fin.last n)‖
        ≤ (if L_dag = 0
            then (n : ℝ) * h
            else (Real.exp (L_dag * ((n : ℝ) * h)) - 1) / L_dag)
          * C * h^p
```

Proof recipe per §C.2 below.

#### D4 (non-vacuity witness): `paddedEuler` example

Mirror cycle 246's D6 pattern. The `f := id` choice on `paddedEuler`
makes everything degenerate (Lipschitz constant 1 works, `A = 0` makes
smallness trivial). Construct a constant-`y` trajectory + the trivial
local-truncation bound (e.g. `δ k := 0`, so `C := 0`, `p := 0`); verify
the headline reduces to `0 ≤ 0`.

---

## §C. Concrete tactic plan

### §C.1 — The geometric-sum identity

For `a ∈ ℝ`, `a ≠ 0`, the standard identity is
`∑_{i=0}^{n-1} x^i = (x^n - 1) / (x - 1)`. With `x := 1 + a`:
`∑_{i=0}^{n-1} (1 + a)^i = ((1 + a)^n - 1) / a`.

For our shape `∑_{k < n} (1 + a)^(n - 1 - k)`:
- Reindex `i := n - 1 - k`; as `k` ranges `0..n-1`, so does `i`.
- The reindexed sum equals `∑_{i=0}^{n-1} (1 + a)^i`.
- Apply the closed form.

In Lean over `Fin n`:

1. **Reindex** via `Finset.sum_range_reflect`. Statement form:
   `∑ i ∈ Finset.range n, f (n - 1 - i) = ∑ i ∈ Finset.range n, f i`.
   Convert `Fin n` sum to `Finset.range n` sum first via
   `Fin.sum_univ_eq_sum_range` (or `Finset.sum_fin_eq_sum_range`).

2. **Closed form** for `a ≠ 0`: use `geom_sum_eq` from
   `Mathlib.Algebra.GeomSum`. Statement (verify exact form with
   `lean_hover_info`):
   `∀ {α : Type*} [CommRing α] {x : α}, x ≠ 1 →
     ∀ n : ℕ, ∑ i ∈ Finset.range n, x^i = (x^n - 1) / (x - 1)`.
   Apply with `x := 1 + a`, side condition `1 + a ≠ 1 ↔ a ≠ 0`.
   The denominator `(1 + a) - 1 = a` simplifies via `add_sub_cancel_left`.

3. **`a = 0` case**: each summand is `(1 + 0)^(n - 1 - k.val) = 1`,
   so the sum is `n`. Direct via `simp` + `Finset.sum_const` +
   `Finset.card_fin`.

**Risk R1**: `geom_sum_eq` may exist under a slightly different name
(`Finset.geom_sum_eq`, or in `Mathlib.Algebra.GeomSum`). Verify
EARLY with `lean_local_search "geom_sum"`. If it doesn't fire,
prove by direct induction on `n` (~12 LOC):
```
∑_{i < n+1} x^i = ∑_{i < n} x^i + x^n
                = (x^n - 1)/(x-1) + x^n      [by IH]
                = ((x^n - 1) + x^n (x - 1))/(x-1)
                = (x^{n+1} - 1)/(x-1)
```

**Risk R2**: `Finset.sum_range_reflect` shape may differ slightly
(some Mathlib versions index from `1`, or use `Finset.Ico 0 n`).
Verify with `lean_hover_info`. If shape mismatch, work via
`Finset.sum_bij` with `i ↔ n - 1 - i` directly.

### §C.2 — `thm_319B` proof body

Outline (~120 LOC body):

1. Apply `accumulation_recurrence` to get
   ```
   ∃ L_dag ≥ 0,
     ‖yex_n − traj_n‖
       ≤ (1 + h L_dag)^n · ‖yex_0 − traj_0‖
         + ∑_{k < n} (1 + h L_dag)^(n-1-k) · δ_k
   ```

2. Substitute `δ k := C * h^(p+1)` from `h_lte`. Use
   `h_init_eq : yex 0 = traj 0` to vanish the first term:
   `‖yex 0 − traj 0‖ = ‖0‖ = 0` via `sub_self`.

3. Pull `(C * h^(p+1))` out of the sum (it doesn't depend on `k`):
   ```
   ∑ (1 + h L_dag)^(n-1-k) · (C * h^(p+1))
     = (C * h^(p+1)) · ∑ (1 + h L_dag)^(n-1-k)
   ```
   via `Finset.mul_sum` (or `Finset.sum_mul` flipped) +
   `Finset.sum_congr` to move the constant out.

4. **Case-split on `L_dag = 0` vs `L_dag > 0`** (use `lt_or_eq_of_le`
   on `0 ≤ L_dag`, then `Eq.symm`):

   - **`L_dag = 0` branch**: `h * L_dag = 0`, so `(1 + h * L_dag) = 1`.
     By D1's `geometric_sum_one_plus_zero` (after rewriting
     `h * L_dag = 0`), the sum equals `n`. Conclusion reduces to
     `(C * h^(p+1)) · n ≤ ((n : ℝ) * h) · C * h^p`, which uses
     `h^(p+1) = h * h^p` and closes by `ring` (with appropriate
     `linarith` plumbing if `ring` doesn't directly fire due to
     the `n` cast and the `if-then-else` branch shape).

   - **`L_dag > 0` branch**: by D1's `geometric_sum_one_plus_pos`,
     ```
     ∑ (1 + h L_dag)^(n-1-k) = ((1 + h L_dag)^n - 1) / (h L_dag).
     ```
     Use D2 (`pow_one_add_le_exp`) at `a := h * L_dag` to bound
     `(1 + h L_dag)^n ≤ exp(n h L_dag)`. Use
     `div_le_div_of_nonneg_right` (verify name) with denominator
     `h * L_dag > 0` to lift the bound on the numerator. Combine
     with the `(C * h^(p+1))` factor:
     ```
     (C * h^(p+1)) · (exp(n h L_dag) - 1) / (h L_dag)
       = C · h^p · (exp(L_dag · (n h)) - 1) / L_dag
     ```
     (cancel one `h` from `h^(p+1) / (h L_dag) = h^p / L_dag`,
     reassociate `n · h · L_dag = L_dag · (n · h)`). Close by
     `field_simp [ne_of_gt hh_pos, ne_of_gt hL_dag_pos]` + `ring`.

**Risk R3**: the `field_simp` step in the positive `L_dag` branch
will need explicit `ne_zero` hypotheses passed as arguments to
`field_simp [...]`. Pre-declare them:
```
have hh_ne : h ≠ 0 := ne_of_gt hh_pos
have hL_ne : L_dag ≠ 0 := ne_of_gt hL_dag_pos
```

**Risk R4**: `div_le_div_of_nonneg_right` may instead be named
`div_le_div_of_le_left`, `div_le_div_iff_of_pos`, or
`div_le_div_right`. Verify via `lean_loogle "(_ / _ ≤ _ / _)"`. If
none matches, work around manually: bound numerator first, then
multiply by `(1 / (h * L_dag))` (positive) using `mul_le_mul_of_nonneg_right`.

**Risk R5**: the `if-then-else` shape in the conclusion may not
unify cleanly via `split_ifs`. Use `split_ifs with hL_eq` AFTER
the case-split (so the branch the conclusion takes matches the
branch the proof is in). Alternatively, use a `by_cases hL_eq : L_dag = 0`
at the very top of the proof, and inside each branch substitute
the corresponding form of the `if-then-else` via `rw [if_pos hL_eq]`
or `rw [if_neg hL_eq]`.

### §C.3 — `pow_one_add_le_exp` proof

```lean
private lemma pow_one_add_le_exp (a : ℝ) (n : ℕ) (ha : 0 ≤ a) :
    (1 + a)^n ≤ Real.exp ((n : ℝ) * a) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1pa_nn : 0 ≤ 1 + a := by linarith
    have hpow_nn : 0 ≤ (1 + a) ^ k := pow_nonneg h1pa_nn _
    calc (1 + a) ^ (k + 1)
        = (1 + a) ^ k * (1 + a) := by ring
      _ ≤ Real.exp ((k : ℝ) * a) * Real.exp a := by
          apply mul_le_mul ih (Real.add_one_le_exp a) h1pa_nn
          exact (Real.exp_pos _).le
      _ = Real.exp (((k : ℝ) + 1) * a) := by
          rw [← Real.exp_add]; congr 1; ring
      _ = Real.exp (((k + 1 : ℕ) : ℝ) * a) := by push_cast; ring_nf
```

**Risk R6**: `Real.add_one_le_exp` is the standard Mathlib name (no
deprecation as of recent Mathlib versions). Verify via
`lean_local_search "Real.add_one_le_exp"` — backup names are
`Real.add_one_le_exp_of_nonneg` (less likely) or building from
`Real.one_plus_le_exp` (older).

---

## §D. Mathlib hooks to verify before writing the proof

Confirm with `lean_local_search` or `lean_loogle` EARLY in the cycle
(within the first 15 minutes):

| Goal | Candidate lemma | Backup |
|---|---|---|
| `1 + x ≤ exp x` | `Real.add_one_le_exp` | Direct from `Real.one_le_exp` + `Real.exp_le_exp` |
| Geometric sum closed form | `geom_sum_eq` (in `Mathlib.Algebra.GeomSum`) | Direct induction (~12 LOC) |
| Reindex `Fin n` sum | `Finset.sum_range_reflect` + `Fin.sum_univ_eq_sum_range` | Manual `Finset.sum_bij` |
| Pull constant out of sum | `Finset.mul_sum`, `Finset.sum_mul` | Direct `Finset.sum_congr` |
| `(1 + a)^n ≤ exp(n a)` | Build via D2 (this file §C.3) | (no fallback needed) |
| `(a/c ≤ b/c)` from `a ≤ b` and `0 < c` | `div_le_div_of_nonneg_right` / `div_le_div_right` | Manual `mul_le_mul_of_nonneg_right` plumbing |
| `exp(a + b) = exp a * exp b` | `Real.exp_add` | (no realistic backup needed) |
| `field_simp` cleanup | Mathlib's `field_simp` tactic | Manual `mul_div_assoc` chain |
| `if-then-else` rewrites | `if_pos`, `if_neg`, `split_ifs` | Manual `by_cases` |

Do all the searches BEFORE writing the proof body so you have the
right names in hand.

---

## §E. What NOT to do

### NOT-1. Don't redo Phase 1

Cycle 246's `accumulation_recurrence`, `IsRKTrajectory`,
`HasLocalTruncationErrorBound`, and `lem_319A_extract` are correct and
axiom-clean. Do not modify them. The cycle 246 task results document
the design choices.

### NOT-2. Don't introduce axioms or raise `maxHeartbeats`

If a `ring` or `field_simp` step times out, decompose the algebra into
named sub-lemmas (`have h₁ : ... := by ...; have h₂ : ... := by ...;`
then combine). The Phase 2 algebra is mechanical — there should be no
need for tactics that approach 200000 heartbeats.

### NOT-3. Don't attempt §441 Phase C.2

§441 has 43 consecutive GPFS timeouts spanning cycles 182–239. The
pathology is cluster-side; the worker cannot fix it. Cycle 247
deliverable is §319, full stop.

### NOT-4. Don't try to make `thm_319B` unconditional in `L_dag`

The `if L_dag = 0 then ... else ...` shape is faithful to Butcher's
two-case textbook statement. Don't attempt to unify the two cases
into a single closed-form expression (e.g. via `Real.expm1` or
similar) — that would diverge from the textbook and add risk.

### NOT-5. Don't try to remove the existential `L_dag`

Cycle 245's `lem_319A` and cycle 246's `accumulation_recurrence` both
expose `L_dag` existentially because the precise formula
(`L * ∑ᵢ |bᵢ| * ((I - h₀ L |A|)⁻¹ 𝟙)ᵢ`) is unwieldy for downstream
consumers. Phase 2 inherits the existential shape — keep it.

### NOT-6. Don't extract `L_dag` from `accumulation_recurrence` and ALSO re-extract a separate one from `lem_319A`

Apply `accumulation_recurrence` ONCE at the start of the proof, get the
existential `L_dag`, use the SAME `L_dag` throughout Phase 2's
case-split. Do not re-extract from `lem_319A` or `lem_319A_extract` —
those would produce a different (definitionally equal but not
definitionally identified) `L_dag`, forcing equality plumbing.

### NOT-7. Don't worry about the tautology scanner

Cycle 246's score = −1 was a documented false-positive pattern. Per
`tautology_scanner_false_positives.md`, the scanner over-fires on:
- hypothesis declarations in theorem signatures (lines like
  `(hY_out : ...)` that match `:= h_<word>` regex),
- patterns like `with hw_def` where `hw_def` starts with `h`.

The actual sorry count is 0. **Do not modify code to "fix" scanner
hits.** The remediation is a one-time scanner patch in
`scripts/autonomous_loop.py`, which is loop-maintainer territory.

If new tautology-scanner hits appear in Phase 2 code, leave them alone
and document the pattern in the cycle 247 task results.

---

## §F. Faithfulness check (mandatory before commit)

For the new public theorem `thm_319B`:

- [ ] **Entity ID and textbook statement**: quote from
      `extraction/formalization_data/entities/thm_319B.json` and
      `extraction/raw_text/ch03.txt` (§319 p. 190).
- [ ] **Lean statement captures**: same content / weaker / stronger /
      different. Expect "captures with caveats":
  - Frobenius vs spectral-radius smallness (inherited from cycle 245).
  - Iterated-step trajectory `IsRKTrajectory` vs textbook's prose
    "values produced by `n` steps of the method" (cycle 246 D1).
  - `HasLocalTruncationErrorBound` inequality vs textbook's equality
    `δ_k = ‖y(x_k) − ŷ_k‖` (cycle 246 D2).
  - Existential `L_dag` vs textbook's symbol `L^†` with
    explicit closed-form `L * ∑ᵢ |bᵢ| * ((I - h₀ L |A|)⁻¹ 𝟙)ᵢ`
    (inherited from cycle 245).
- [ ] **Tautology check**: conclusion does not appear verbatim as a
      hypothesis. ✓ (expected — the conclusion is a closed-form
      bound; no hypothesis has that shape).
- [ ] **Identity check**: proof is non-trivial (≥ 80 LOC body
      expected; uses `accumulation_recurrence` + geometric sum +
      case split). ✓
- [ ] **Hypothesis strength check**: no extra hypotheses beyond what
      cycle 245's `lem_319A` requires plus the new
      `HasLocalTruncationErrorBound` (Phase 2's textbook
      precondition) plus `0 < L` (needed for `L_dag` case analysis
      and `lem_319A`'s Lipschitz signature). ✓

After running the checklist:
1. Update `lean_status.json` row for `thm:319B`: `partial` → `formalized`,
   bump cycle reference to 247.
2. Update `plan.md` row: `[~]` → `[x]`.
3. Record progress in the cycle 247 task results: 71 entities done → 72.

---

## §G. Aristotle delegation policy

**Not recommended for cycle 247.** The Phase 2 proof has:
- A clear textbook recipe (4 steps in cycle 246 task results).
- Decomposable algebra (case-split + geometric sum + power-exponential
  bound).
- High Aristotle dependency-management overhead (would need to ship
  all of `accumulation_recurrence`, `IsRKTrajectory`,
  `HasLocalTruncationErrorBound`, `lem_319A_extract` as in-context
  templates plus the `Matrix.EntrywiseNonneg` / `M-matrix` machinery
  from `OpenMath/Matrix/MMatrix.lean`).

Manual closure with the §C plan should succeed in ~250 LOC body across
2 helpers + 1 main theorem + 1 example. If the worker stalls past
60 minutes on any single sub-step, decompose the stuck step into a
narrower named helper and continue. Do NOT submit to Aristotle as a
first move.

If the cycle ends without Phase 2 closure despite genuine progress
(e.g. helpers landed but main theorem stuck), package as a focused
single-sorry-style scaffold and write up the recovery plan in cycle
247 task results.

---

## §H. LOC budget and abort threshold

- D1 helpers (private, geometric sum × 2 variants + pow-exp): ~50 LOC
  + ~40 LOC = ~90 LOC total.
- D3 main theorem `thm_319B`: ~120 LOC body + ~30 LOC docstring.
- D4 non-vacuity example: ~30 LOC.
- Total: ~270 LOC.

**Abort threshold**: if at the 75-minute mark, no helper has compiled
clean, pause and re-evaluate. The most likely cause is a Mathlib hook
mismatch (Risk R1/R2/R6); switch to direct induction proofs of the
geometric and exponential lemmas rather than searching Mathlib further.

**Stretch**: if Phase 2 closes ahead of schedule (e.g. 90 min in with
all 4 deliverables landed), consider:
- Cleaner non-vacuity: a non-trivial `paddedEuler` example with
  `f` non-constant and a real exact solution (e.g. `yex` linear),
  exercising the case-split branch `L_dag > 0`.
- Bookkeeping cleanup: factor the cycle 244/245/246 helpers into
  documentation sub-sections within `Section319.lean` for
  navigability.

Do NOT pursue stretches if Phase 2 isn't already shipped.

---

## §I. Heartbeat / progress reporting

If Phase 2 lands clean:
- Commit message: `Cycle 247 — §319 thm:319B Phase 2 (geometric sum closed form) SHIPPED.`
- Cycle 247 task results should record: which Mathlib hooks were used
  vs alternatives, the case-split structure, and any cycle-248
  follow-up suggestions (likely "§319 fully closed; pivot to another
  Ch.3 §380 entity or open Ch.5 deliverable").

If Phase 2 stalls:
- Commit any landed helpers as a partial step.
- Write cycle 247 task results documenting the stall location and the
  specific Lean error / proof-state snapshot.
- Update an issue file at `.prover-state/issues/thm_319B_phase_2_*.md`
  with the stall's narrow cause for cycle 248 to address.

---

## §J. Summary checklist for cycle 247 worker

- [ ] §A: verify git state and Phase 1 ship at start.
- [ ] §D: verify Mathlib hooks within the first 15 minutes.
- [ ] §B: ship Phase 2 deliverables D1–D4.
- [ ] §C: follow the geometric-sum + pow-exp + case-split recipe.
- [ ] §E: avoid the 7 NOT-todos.
- [ ] §F: run the faithfulness checklist before commit.
- [ ] §H: respect the 75-min abort threshold; decompose if needed.
- [ ] Commit with the §I-format message.
- [ ] Update `lean_status.json`, `plan.md`, write cycle 247 task results.

After Phase 2 ships, `thm:319B` is fully formalized and the §319
Butcher chapter (lem:319A + thm:319B) is **complete** — a substantive
chapter milestone.
