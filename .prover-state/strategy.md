# Strategy — cycle 045

## Context: where cycle 044 left us

Cycle 044 closed the **per-term form** of `thm:406C` as
`LinearMultistepMethod.globalError_recurrence_bound`
(`OpenMath/Chapter4/Section404.lean:1241`), with five new
declarations + a latent-bug fix to `IsLMMSolution`'s sign
convention. The OpenMath/ tree is sorry-free; axiom checks for the
new declarations come back at the standard tripod
`[propext, Classical.choice, Quot.sound]`; `lake build` succeeds at
8027/8027 jobs.

`lean_status.json` records `thm:406C` as `partial` — the cycle-044
deliverable is the per-term shape

```
|n_n − Σ α n_{−i}|
  ≤ h L |β_0| · |n_n|                        -- T_1 (NOT yet absorbed)
    + h L Σ_{i≥1} |β_i| · max |n_{−i}|        -- T_2
    + ((½) Σ i² |α_i| + Σ i |β_i|) L M h²     -- T_3
```

while Butcher's textbook (406c) form (entity `thm:406C` at
`extraction/formalization_data/entities/thm_406C.json`, p.347) is
the **absorbed** form

```
|n_n − Σ α n_{−i}|  ≤  C h max |n_{−i}|  +  D h²
```

obtained by "using (406d) twice" — the (1 − hL|β_0|)-inversion to
absorb `T_1`. Closing this absorption is the natural next step and
will promote `thm:406C` from `partial` → `formalized`.

There is no pending Aristotle work to incorporate.

---

## Primary task — close the textbook (406c) form of `thm:406C`

Add a corollary
`LinearMultistepMethod.globalError_recurrence_bound_textbook` to
`OpenMath/Chapter4/Section404.lean`, after the existing per-term
form (around line 1284, before `end OpenMath.Chapter4.Section404`).

### Proposed signature

```lean
theorem LinearMultistepMethod.globalError_recurrence_bound_textbook
    {k : ℕ} (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)
    {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hh : 0 ≤ h)
    (hsmall : h * L * |M.β 0| < 1)               -- the textbook smallness hypothesis
    (hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y)
    (n : ℕ) (hn : k ≤ n)
    (Mmax : ℝ) (hMmax0 : 0 ≤ Mmax)
    (hMmax : ∀ i : Fin k,
              |yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1))| ≤ Mmax) :
    |yex (x₀ + (n : ℝ) * h) - Y n
        - ∑ i : Fin k, M.α i.succ
            * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1)))|
      ≤ (h * L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                  + ∑ i : Fin k, |M.β i.succ|)
            / (1 - h * L * |M.β 0|)) * Mmax
        + ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
            + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
              * L * M_bound * h^2
            / (1 - h * L * |M.β 0|)
```

This is the absorbed form with **explicit h-dependent constants**.
The textbook's "constants C, D" form (uniform over `h ≤ h_0`)
follows by trivial monotonicity; defer that as a separate corollary
in a future cycle if needed.

If you decide an `∃ C D : ℝ, …` form reads more naturally — that is
also acceptable, but the explicit form is preferred (tighter,
easier for downstream consumers).

### Algebraic argument (Butcher's "use (406d) twice")

Let

```
A := |yex(x₀+n·h) − Y n − Σ_{i=1}^k α_i (yex(x₀+(n-i)·h) − Y(n-i))|        -- LHS
B := |Σ_{i=1}^k α_i (yex(x₀+(n-i)·h) − Y(n-i))|                             -- shifted block
c := h * L * |M.β 0|                                                        -- the small coefficient
K := h * L * (Σ_{i≥1} |β_i|) * Mmax + ((½) Σ i² |α_i| + Σ i |β_i|) L M h²    -- T_2 + T_3
```

Cycle 044 already proved (the per-term form):

```
A ≤ c * |n_n| + K           ... (★)        -- where n_n = yex(x₀+n·h) − Y n
```

(this is exactly `globalError_recurrence_bound`, modulo
unfolding `globalError`).

**Step 1 — bound on `|n_n|`.** Use `|n_n| ≤ B + A` (which follows
from `n_n = (n_n − Σα n_{-i}) + Σα n_{-i}` and `abs_add`) and
substitute into (★):

```
A ≤ c · (B + A) + K
=> (1 − c) · A ≤ c · B + K
=> A ≤ (c · B + K) / (1 − c)         (since 1 − c > 0 by hsmall)
```

**Step 2 — bound `B` by `(Σ|α_i|) · Mmax`.** Triangle inequality
on `B = |Σ α_i (yex(...) − Y(...))|`:

```
B ≤ Σ |α_i| · |yex(...) − Y(...)| ≤ (Σ |α_i|) · Mmax
```

(monotone sum + `hMmax`).

**Step 3 — combine.**

```
A ≤ (c · (Σ|α_i|) · Mmax + h·L·(Σ_{i≥1}|β_i|)·Mmax + D_coeff · h²) / (1 − c)
  = h·L·(|β_0|·Σ|α_i| + Σ_{i≥1}|β_i|)·Mmax / (1−c) + D_coeff · h² / (1−c)
```

Match the proposed RHS — done.

### Lean tactic plan (manual proof, ≤ 50 lines)

The proof should reuse `globalError_recurrence_bound` (cycle 044)
as the per-term step (★), so this is **pure algebra over reals** —
no analysis, no FTC. Sketch:

```lean
  -- Apply the cycle-044 per-term bound.
  have hA := M.globalError_recurrence_bound hcons hL hM hf_lip
                hyex_C1 hyex_ode hf_yex_bound hh hY n hn Mmax hMmax0 hMmax
  -- Reverse triangle: |n_n| ≤ |Σ α_i (yex − Y)| + A.
  have h_abs_nn :
      |yex (x₀ + (n : ℝ) * h) - Y n|
        ≤ |∑ i : Fin k, M.α i.succ
              * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                  - Y (n - (i.val + 1)))|
          + |yex (x₀ + (n : ℝ) * h) - Y n
              - ∑ i : Fin k, M.α i.succ
                  * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                      - Y (n - (i.val + 1)))| := by
    have hrw : yex (x₀ + (n : ℝ) * h) - Y n
              = (∑ i : Fin k, M.α i.succ
                  * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                      - Y (n - (i.val + 1))))
                + (yex (x₀ + (n : ℝ) * h) - Y n
                    - ∑ i : Fin k, M.α i.succ
                        * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                            - Y (n - (i.val + 1)))) := by ring
    rw [hrw]
    exact abs_add _ _
  -- Bound |Σ α_i (yex − Y)| by (Σ|α_i|) · Mmax.
  have h_abs_sum :
      |∑ i : Fin k, M.α i.succ
          * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
              - Y (n - (i.val + 1)))|
        ≤ (∑ i : Fin k, |M.α i.succ|) * Mmax := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMmax i) (abs_nonneg _)
  -- (1 - c) is positive.
  have h_one_sub_c_pos : 0 < 1 - h * L * |M.β 0| := by linarith [hsmall]
  -- Combine: from `A ≤ c |n_n| + K_remainder` and `|n_n| ≤ B + A`,
  -- get `(1-c) A ≤ c·B + K_remainder ≤ c · (Σ|α|)·Mmax + K_remainder`.
  -- Multiplying through: A ≤ ((c · (Σ|α|)) · Mmax + K_remainder) / (1-c).
  -- Final step: divide by (1-c) and rearrange to match goal RHS.
  rw [div_add_div_same, le_div_iff h_one_sub_c_pos]
  -- After rw, the goal is a sum-of-products vs. (1-c)*A. Close by
  -- combining the three named inequalities.
  -- KEY MOVE: introduce intermediate inequality via nlinarith / linarith
  -- with carefully chosen hints (hA, h_abs_nn, h_abs_sum,
  -- mul_nonneg facts, etc.).
  nlinarith [hA, h_abs_nn, h_abs_sum,
             abs_nonneg (yex (x₀ + (n : ℝ) * h) - Y n),
             mul_nonneg hh hL,
             abs_nonneg (M.β 0)]
```

**If `nlinarith` is too slow or fails on the closing step**,
decompose into named intermediate inequalities (cycle 042 / 044
pattern):

1. `h_step1 : A ≤ c * |n_n| + K_remainder` — from `hA`.
2. `h_step2 : c * |n_n| ≤ c * B + c * A` — from `h_abs_nn` × `c ≥ 0`.
3. `h_step3 : (1 - c) * A ≤ c * B + K_remainder` — from `h_step1`,
   `h_step2`, `linarith`.
4. `h_step4 : (1 - c) * A ≤ c * (Σ|α|) * Mmax + K_remainder` —
   from `h_step3`, `h_abs_sum`.
5. Final goal via `(le_div_iff h_one_sub_c_pos).mpr h_step4` +
   `field_simp` / `ring`.

The load-bearing Mathlib lemmas:

| Goal | Lemma |
|---|---|
| `\|a\| ≤ \|b\| + \|a − b\|` | `abs_add` (apply to `b + (a − b) = a`) |
| `\|Σ\| ≤ Σ \|·\|` | `Finset.abs_sum_le_sum_abs` |
| `Σ |c · a| = Σ |c| · |a|` | `abs_mul` + `Finset.sum_le_sum` |
| Pull constant out of sum | `Finset.sum_mul` |
| Divide both sides of inequality | `le_div_iff` (positive divisor) |
| Algebraic simplification | `field_simp; ring` (last resort: `nlinarith`) |

**Do NOT raise `maxHeartbeats`.** If a goal is slow, decompose further.

### After the proof lands

Update `extraction/formalization_data/lean_status.json`:

```json
"thm:406C": {
  "lean_file": "OpenMath/Chapter4/Section404.lean",
  "lean_symbol": "OpenMath.Chapter4.Section404.LinearMultistepMethod.globalError_recurrence_bound_textbook",
  "status": "formalized"
}
```

Note: status field changes from `partial` → `formalized`. The
cycle-044 per-term form remains as a load-bearing intermediate
lemma; the `lean_symbol` field should point at the **textbook**
form (`_textbook` suffix), since that is the entity the textbook
states. Document the per-term form's role as an intermediate
clearly in the docstring.

Also bump `plan.md`'s entity counter from `40 / 175` to `41 / 175`
and toggle the `[ ] thm:406C` marker to `[x]`. (The line currently
reads:
`- [ ] thm:406C **Global error bound for linear multistep methods** (§406)`.)

---

## Stretch task — sanity-check witness for `IsLMMSolution`

Cycle 044's discovery #1 noted that the previous sign bug could
have been caught earlier with a sanity-check theorem against
explicit Euler. Add this lock-in lemma to the same file (place
near `isLMMSolution_zero_iff` at line 337 of
`OpenMath/Chapter4/Section404.lean`):

```lean
/-- Sanity check: explicit Euler's `IsLMMSolution` recurrence reduces to
the textbook step `Y(m+1) = Y(m) + h * f(x₀ + m·h, Y m)`. This lemma
exists to lock in the sign convention of `IsLMMSolution` against
future drift. -/
theorem explicitEulerLMM_step_eq
    {f : ℝ → ℝ → ℝ} {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hY : explicitEulerLMM.IsLMMSolution h x₀ f Y) (m : ℕ) :
    Y (m + 1) = Y m + h * f (x₀ + (m : ℝ) * h) (Y m) := by
  have h_step := hY m
  -- explicitEulerLMM has α 0 = -1, α 1 = 1, β 0 = 0, β 1 = 1.
  -- After Fin.sum_univ_succ + α_zero/β_zero simp, the IsLMMSolution
  -- recurrence simplifies to the explicit Euler step.
  simp [explicitEulerLMM, Fin.sum_univ_succ, Fin.sum_univ_zero,
        LinearMultistepMethod.α_zero] at h_step
  linarith
```

The exact `simp`/`linarith` chain may need tweaking. **Verify
first** with `lean_multi_attempt` what `simp` reduces `h_step` to,
then close with the appropriate tactic.

This is small (≤ 20 lines) and acts as a regression test for the
sign convention.

---

## Tertiary task — `thm:406D` sorry-first scaffold (only if time remains)

`thm:406D` ("Convergence from Stability and Consistency", §406, the
Lax-equivalence direction for LMMs) is the immediate downstream of
`thm:406C`. Its dependents include the cross-chapter `thm:243A`
parked since Chapter 2.

If the primary AND stretch tasks both land with time to spare:

1. Read the textbook statement and proof from
   `extraction/formalization_data/entities/thm_406D.json`.
2. Write a Lean signature with a top-level `sorry`. Verify it
   compiles.
3. Identify and write 3–5 sub-lemma scaffolds (also `sorry`'d).
   Likely candidates:
   - Discrete Grönwall on the global-error sequence `n_m`.
   - Bound on the homogeneous-recurrence solution under
     `IsStable`.
   - The "consistency ⇒ LTE = O(h²)" packaging step
     (already largely in `localTruncationError_bound`).
4. Submit the sub-lemma scaffolds to Aristotle in batch and **stop
   polling per CLAUDE.md** — one check per cycle, max.

Do **NOT** attempt to manually prove `thm:406D` this cycle. Do
**NOT** mark `thm:406D` as `formalized`/`partial` in
`lean_status.json` if only sorry'd (`unformalized` is correct
until at least one sub-lemma is closed manually).

---

## What NOT to do

- Do **NOT** treat any "git commit/push failure" framing in the
  prompt as a real issue. Verify with
  `git log -1 --format='%H %s'` and confirm
  `git rev-parse HEAD == origin/Main/Experiments`. The
  cycle-008/014/015/040 phantoms are documented in
  `.prover-state/issues/consultant_advice_cycle_009.md` §A,
  `consultant_advice_cycle_014.md` §A,
  `consultant_advice_cycle_015.md` §B,
  `consultant_advice_cycle_040.md` §A.
- Do **NOT** revert or modify the cycle-044 `IsLMMSolution`
  sign-fix. It is correct (verified against Butcher (400b) and
  explicit Euler).
- Do **NOT** rewrite `globalError_recurrence_bound` (the per-term
  form). The textbook form is a corollary, not a replacement —
  both will live in the file.
- Do **NOT** raise `maxHeartbeats` above 200000. If `linarith` or
  `nlinarith` chokes on the final algebra, decompose the proof
  into 4–5 named intermediate inequalities (cycle 042/044
  pattern).
- Do **NOT** try to introduce universal quantification over `h_0`
  (the textbook's "for all `h ≤ h_0`" phrasing) in this cycle.
  Stick to the explicit h-dependent constants form. The
  uniform-h_0 form can be a one-line corollary in a future cycle.
- Do **NOT** start `thm:406D`'s actual proof. The sorry-first
  scaffold is the only acceptable cycle-045 deliverable for it.
- Do **NOT** poll Aristotle more than once. CLAUDE.md is explicit.
  The cycle-044 evidence (project `b3dea0fe-…` at 5% after 1h on
  similar algebraic targets) confirms Aristotle adds little value
  for the textbook-form corollary; reserve compute for `thm:406D`'s
  scaffold sub-lemmas if you reach the tertiary task.
- Do **NOT** edit `scripts/autonomous_loop.py` from the worker.
  Per the standing
  `tautology_scanner_false_positives.md` issue.
- Do **NOT** start §142 Schur infrastructure
  (`jordan_canonical_form_missing.md`); §3+/§142 work is
  back-burner.
- Do **NOT** introduce `axiom`/`constant`. Decompose proofs
  instead.

---

## Aristotle plan

**Skip Aristotle for the primary task.** The textbook-form
corollary is pure algebra and reuses the cycle-044 per-term form;
manual proof is faster than Aristotle's exploration. Reserve
Aristotle compute for `thm:406D`'s sub-lemma scaffolds **if and
only if** you reach the tertiary task. One submission per cycle,
one check after 30 min, no more.

---

## Pre-commit faithfulness checklist

Per CLAUDE.md, run for every new `def`/`theorem` introduced this
cycle:

### `globalError_recurrence_bound_textbook` (`thm:406C`)

- Entity ID: `thm:406C`. Quote from `entities/thm_406C.json`:
  > "Then for h_0 sufficiently small so that h_0 |β_0| L < 1 and
  > h < h_0, there exist constants C and D such that
  > ‖n − Σ α_i n_{−i}‖ ≤ C h max ‖n_{−i}‖ + D h² (406c)."
- Lean statement captures: **same content**, with C, D as
  explicit h-dependent rationals (textbook abstracts them as
  unspecified constants depending on `h_0`). Justified divergence:
  the Lean form is strictly tighter and trivially implies the
  textbook form when `h ≤ h_0` and constants are taken at `h_0`.
- Tautology check: clean. Conclusion is a numerical inequality
  with `(1 − h L |β_0|)` in the denominator; no hypothesis
  matches it verbatim.
- Identity check: proof has 4+ distinct steps (apply per-term
  form, reverse triangle, monotone sum, final divide); not a
  single `exact`.
- Hypothesis-strength check: `hsmall : h L |β_0| < 1` is the only
  new hypothesis vs. the per-term form; it is **exactly** the
  textbook smallness condition. No strengthening relative to the
  textbook (the per-term form's hypotheses are inherited
  verbatim).
- Absent-theorem check: `globalError_recurrence_bound` (cycle 044)
  exists at `Section404.lean:1241`; no further promised content.

### `explicitEulerLMM_step_eq` (sanity-check witness)

- Helper, not a Butcher entity. Documents the cycle-044 sign-fix.
- Tautology check: conclusion `Y(m+1) = Y m + h f(...)` does NOT
  match any hypothesis verbatim — the hypothesis is the abstract
  `IsLMMSolution` predicate, not the explicit Euler step.
- Identity check: proof simplifies the predicate via
  `Fin.sum_univ_succ` + `simp`; not a tautology.
- Justification: regression test for `IsLMMSolution`'s sign
  convention.

### `thm:406D` scaffold (only if reached)

- Will introduce `sorry`'d sub-lemmas. Document each as
  "sorry-first; to be closed in cycle 046+". File an issue at
  `.prover-state/issues/thm_406D_scaffold.md` enumerating the
  sub-lemmas and their dependencies.
- Pre-commit: do NOT mark `thm:406D` as `formalized` or `partial`
  in `lean_status.json` if only `sorry`'d. Leave as
  `unformalized` until at least one sub-lemma is closed manually.

---

## Cycle 045 success criteria

- **Minimum acceptable**: `thm:406C` textbook form proved and
  committed; `lean_status.json` updated; `plan.md` counter
  bumped (40/175 → 41/175).
- **Target**: minimum + sanity-check witness
  `explicitEulerLMM_step_eq`.
- **Stretch**: target + `thm:406D` sorry-first scaffold +
  Aristotle batch on its sub-lemmas.

If the textbook-form corollary's algebra resists `linarith` /
`nlinarith` despite decomposition into 4–5 named inequalities,
file an issue at
`.prover-state/issues/406C_textbook_form_blocker.md` describing
the specific algebraic obstruction (e.g. "linarith fails on goals
of shape X with sums of size Y") and fall back to **only the
sanity-check witness** as the deliverable. CLAUDE.md is firm:
"A cycle with zero changes is unacceptable" — but the per-term
form (cycle 044) is already a complete, useful, reusable result,
and the sanity-check witness alone is enough to mark cycle 045
non-trivial.
