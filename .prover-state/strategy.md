# Cycle 169 strategy — close `thm:454A` (`gStable_isAStable`) and the BDF2 corollary

## Standing context

* Sorry count: **0**. Do not regress.
* `thm:454A` (Concluding remarks on G-stability) is the active target.
  Cycle 166 landed `IsAStable` + the explicit-Euler refutability witness;
  cycle 167 landed the `gTopLeft`/`gBottomRight` quadratic-form lemmas;
  cycle 168 landed `algebraic_identity_454A` (the §451e identity over ℂ)
  with thirteen private named sub-pieces 1.A–1.F, **plus** the two
  complex-lift PSD/PD helpers in `OpenMath/Chapter4/Section454Aux.lean`
  (closed by Aristotle, all axiom-clean).
* Aristotle queue: empty (cycle 168's job COMPLETED). No pending poll.
* All §454 / §454Aux artefacts are axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).

What is left to close `thm:454A`:

1. The main theorem itself, `LinearMultistepMethod.gStable_isAStable`
   (Theorem 454A, Butcher §454, p. 387).
2. The BDF2 corollary `bdf2LMM_isAStable` — wires together cycle 165's
   `bdf2LMM_isGStable` and (1).

Both fit in cycle 169 if (1) closes cleanly. If (1) stalls past ~250 LOC
or hits a complex-arithmetic blowup, ship (1) only and defer (2) to
cycle 170.

---

## Priority 1 — `gStable_isAStable` (Theorem 454A)

### Statement

Place this in `OpenMath/Chapter4/Section454.lean`, **inside the existing
`namespace OpenMath.Chapter4.Section404`** block (between the `IsAStable`
def at line 68 and the `end OpenMath.Chapter4.Section404` at line 75 —
or, easier, immediately after that `end`, adding a fresh `namespace
OpenMath.Chapter4.Section404` block dedicated to the theorem). The
file already imports `Section451` (G-stability) and `Section410`
(αPoly/βPoly), so no new top-level imports are needed for the
theorem itself; you DO need

```lean
import OpenMath.Chapter4.Section454Aux
```

added near the top of `Section454.lean` (the file currently does not
import the Aux module).

```lean
/-- **Butcher Theorem 454A — a G-stable LMM is A-stable** (§454, p. 387). -/
theorem LinearMultistepMethod.gStable_isAStable {k : ℕ}
    (M : LinearMultistepMethod k) (hG : M.IsGStable) :
    M.IsAStable := by
  sorry
```

### Proof recipe (sorry-first → close incrementally)

Math sketch (from Butcher, with Lean-friendly bookkeeping):

```
star W ⬝ᵥ ((M.gMatrix G).map ι *ᵥ W)            -- (1)
  = (W^* α) · β  +  (W^* β) · α                  -- (2)
  − (1 − ‖w‖²) · (star W₁ ⬝ᵥ (G.map ι *ᵥ W₁))    -- (3)
```

Take `.re` of both sides:
* LHS .re ≥ 0 by `complexLift_re_dotProduct_nonneg_of_real_posSemidef`
  applied to `M.gMatrix G` (the `hPSD` clause of G-stability).
* The first two terms of RHS sum to `2 · (star α · β).re` (real, since
  `z + star z = 2 · z.re` for `z = star α · β`).
* `(star W₁ ⬝ᵥ (G.map ι *ᵥ W₁)).re > 0` by
  `complexLift_re_dotProduct_pos_of_real_posDef` applied to `G` (the
  `hPD` clause), using `vanW₁ w ≠ 0` because `vanW₁ w 0 = 1 ≠ 0`.
* `1 − ‖w‖² > 0` because `‖w‖ < 1`.

So:
```
0 ≤ 2 · (star (α(w)) · β(w)).re − (positive real) · (positive real)
```

i.e. `0 < (star (α(w)) · β(w)).re`. Then divide by `‖β(w)‖² > 0` (which
is real-positive because `β(w) ≠ 0`) to get `0 < (α(w) / β(w)).re` via
`Complex.div_re` or the direct identity `(α / β).re = (star β · α).re /
‖β‖²` and the algebraic step `(star α · β).re = (star β · α).re` (since
`(star α · β).re = (α · star β).re` for the conjugate-symmetric pair).

### Concrete Lean step plan

Decompose into named `private` helpers (per cycle 167's Stage 2 + cycle
168's Stage 3 named-decomposition playbook). Each helper ≤ 15 LOC.

**Step 1 — extract G-stability data.**
```lean
obtain ⟨G, hSymm, hPD, hPSD⟩ := hG
intro w hw_norm hβw
```
Goal: `0 < (Polynomial.aeval w (αPoly M) / Polynomial.aeval w (βPoly M)).re`.

**Step 2 — set up names.** Introduce shorthand `α := aeval w (αPoly M)`,
`β := aeval w (βPoly M)`, `W := vanW w`, `W₁ := vanW₁ w`. Use `set` so
the hypothesis names are stable.

**Step 3 — apply the algebraic identity.**
```lean
have hid := algebraic_identity_454A M G w
```
This gives Eq (1) = (2) − (3) over ℂ.

**Step 4 — bound the LHS real part from below by 0** (private helper
`gMatrix_quadForm_re_nonneg`):

```lean
private theorem gMatrix_quadForm_re_nonneg
    {k : ℕ} {M : LinearMultistepMethod k} {G : Matrix (Fin k) (Fin k) ℝ}
    (hPSD : (M.gMatrix G).PosSemidef) (w : ℂ) :
    0 ≤ (star (vanW (k := k) w) ⬝ᵥ
          ((M.gMatrix G).map (algebraMap ℝ ℂ) *ᵥ vanW (k := k) w)).re :=
  (OpenMath.Chapter4.Section454Aux
      .complexLift_re_dotProduct_nonneg_of_real_posSemidef hPSD _).1
```

(Note the dot-product convention from Section454Aux uses the same
`star W ⬝ᵥ (A.map ι *ᵥ W)` order — verify by reading the helper's
signature first; if the orientation differs, swap via `dotProduct_comm`
or transpose.)

**Step 5 — strict positivity of the inner-block term** (private helper
`G_quadForm_W₁_re_pos`):

```lean
private theorem G_quadForm_W₁_re_pos
    {k : ℕ} {G : Matrix (Fin k) (Fin k) ℝ} (hPD : G.PosDef) {w : ℂ}
    (hk : 0 < k) :
    0 < (star (vanW₁ (k := k) w) ⬝ᵥ
          (G.map (algebraMap ℝ ℂ) *ᵥ vanW₁ (k := k) w)).re := by
  refine
    OpenMath.Chapter4.Section454Aux
      .complexLift_re_dotProduct_pos_of_real_posDef hPD ?_
  -- vanW₁ w ≠ 0 because vanW₁ w ⟨0, hk⟩ = 1.
  intro hzero
  have h0 : vanW₁ (k := k) w ⟨0, hk⟩ = 1 := by simp [vanW₁_apply]
  have h0' : vanW₁ (k := k) w ⟨0, hk⟩ = 0 := by rw [hzero]; rfl
  rw [h0'] at h0
  exact one_ne_zero h0.symm
```

The `k = 0` case is handled at the **top level** of `gStable_isAStable`:
when `k = 0`, `αPoly M = 1` and `βPoly M = 0` (the empty `Finset.sum`),
so `β(w) = 0` contradicts `hβw`. Use `rcases Nat.eq_zero_or_pos k with
hk0 | hkpos` and dispose of the `k = 0` branch by computing
`Polynomial.aeval w (βPoly M) = 0` from `Fin.sum_univ_zero`.

**Step 6 — `1 − ‖w‖² > 0` over ℂ** (private helper
`one_sub_normSq_re_pos`):

```lean
private theorem one_sub_normSq_re_pos {w : ℂ} (hw : ‖w‖ < 1) :
    (0 : ℝ) < ((1 : ℂ) - ((‖w‖ ^ 2 : ℝ) : ℂ)).re := by
  rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  nlinarith [sq_nonneg ‖w‖, sq_nonneg (1 - ‖w‖), hw, norm_nonneg w]
```

(The exact form of the `(‖w‖^2 : ℝ) : ℂ` coercion in
`algebraic_identity_454A`'s statement is `((‖w‖^2 : ℝ) : ℂ)` —
verify from `Section454.lean:430`.)

**Step 7 — combine into `Re(star α · β) > 0`** (private helper
`star_alpha_beta_re_pos`):

```lean
private theorem star_alpha_beta_re_pos
    {k : ℕ} {M : LinearMultistepMethod k} (hG : M.IsGStable)
    {w : ℂ} (hw : ‖w‖ < 1) (hk : 0 < k) :
    0 < (star (Polynomial.aeval w (αPoly M)) *
          Polynomial.aeval w (βPoly M)).re
```

Proof plan: extract G + hPSD + hPD; apply the identity; take `.re`;
use Steps 4 + 5 + 6; the `(star β · α).re = (star α · β).re`
equality follows from `Complex.add_re`, `Complex.mul_comm`, and
`Complex.conj_mul`-style identities, OR more directly from
`(star x) + x = 2 * x.re` applied at `x := star α · β` plus
recognising `star β · α = star (star α · β)`. This is the only
arithmetic-heavy step; budget 30–40 LOC.

**Step 8 — divide through `‖β‖²`** (private helper
`alpha_div_beta_re_pos_of_star_alpha_beta_re_pos`):

```lean
private theorem alpha_div_beta_re_pos_of_star_alpha_beta_re_pos
    {α β : ℂ} (hβ : β ≠ 0) (h : 0 < (star α * β).re) :
    0 < (α / β).re := by
  rw [Complex.div_re]
  have hnsq : 0 < β.re^2 + β.im^2 := by
    have : β.re^2 + β.im^2 = Complex.normSq β := by
      rw [Complex.normSq]; ring
    rw [this]
    exact Complex.normSq_pos.mpr hβ
  -- (α / β).re = (α.re · β.re + α.im · β.im) / (β.re² + β.im²)
  -- (star α · β).re = α.re · β.re + α.im · β.im (since star α has flipped imaginary).
  have hstar : (star α * β).re = α.re * β.re + α.im * β.im := by
    simp [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hstar] at h
  -- normSq β = β.re² + β.im²; rewrite Complex.div_re's output if needed.
  -- The goal after `rw [Complex.div_re]` is roughly
  --   0 < (α.re * β.re + α.im * β.im) / Complex.normSq β
  -- which matches `h / hnsq` via `div_pos`.
  sorry  -- finalize after verifying Complex.div_re's exact unfolding
```

(Verify the exact unfolding of `Complex.div_re` in Mathlib — it may
already give the desired form modulo ring rearrangement. If
`Complex.div_re` outputs `(α.re * β.re + α.im * β.im) / Complex.normSq β`
directly, then `exact div_pos h hnsq` closes it after recasting
`β.re^2 + β.im^2` to `Complex.normSq β`.)

**Step 9 — assemble.** The main proof becomes a ~15-line composition:

```lean
theorem LinearMultistepMethod.gStable_isAStable ... := by
  intro w hw_norm hβw
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- k = 0 vacuous: βPoly M = 0, so hβw gives False
    exfalso
    apply hβw
    subst hk
    -- βPoly M = ∑ i : Fin 1, C (M.β i) * X^(i.val) — actually Fin (0+1).
    -- Need to compute this carefully. βPoly's exact form is in Section410.
    simp [βPoly]
  exact alpha_div_beta_re_pos_of_star_alpha_beta_re_pos hβw
    (star_alpha_beta_re_pos hG hw_norm hk)
```

**Critical caveat for the `k = 0` branch**: read `βPoly` from
`OpenMath/Chapter4/Section410.lean` first to confirm its exact shape at
`k = 0`. If `βPoly M = ∑ i : Fin (k+1), C (M.β i) * X^i.val`, then at
`k = 0` the sum has one term `C (M.β 0) * X^0 = C (M.β 0)`, which is
NOT trivially zero — `M.β 0` could be non-zero (and indeed for the
trivial `LinearMultistepMethod 0`, `M.β 0` is freely chosen). In that
case the `k = 0` branch needs a different argument. Three options:

1. **(preferred)** Add `(hk : 0 < k)` to `gStable_isAStable`'s
   signature. Faithfulness divergence: textbook implicitly assumes
   `k ≥ 1` (LMMs with `k = 0` are degenerate). Document in the docstring
   and in `lean_status.json`. Mirrors cycle 109's `0 < s` precondition
   on `thm:515D`.
2. Examine whether `IsGStable` at `k = 0` forces `M.β 0 = 0` via the
   gMatrix structure (possible but requires inspection).
3. Inhabit a `LinearMultistepMethod 0` and check whether `IsAStable`
   trivialises.

**Adopt option 1 unless option 2 is provably trivial.** This is the
cleanest unblock.

### Implementation order

1. **First**: read `OpenMath/Chapter4/Section410.lean` (specifically the
   definition of `βPoly`) to determine the `k = 0` behaviour. This
   informs whether option 1 / 2 / 3 above is needed.
2. Write the theorem skeleton + the seven private helper signatures with
   `sorry` bodies. Verify the file compiles (`lake env lean
   OpenMath/Chapter4/Section454.lean`). This validates the helper
   shapes before any proof work.
3. Close Step 6 (`one_sub_normSq_re_pos`) — easy, ~5 LOC.
4. Close Step 4 (`gMatrix_quadForm_re_nonneg`) — one-liner against
   `complexLift_re_dotProduct_nonneg_of_real_posSemidef`.
5. Close Step 5 (`G_quadForm_W₁_re_pos` at `k ≥ 1`) — short.
6. Close Step 8 (`alpha_div_beta_re_pos_of_star_alpha_beta_re_pos`) —
   pure complex arithmetic, ~15 LOC.
7. Close Step 7 (`star_alpha_beta_re_pos`) — the hardest of the seven;
   budget 30–40 LOC. This is where the `algebraic_identity_454A` is
   consumed; `Complex.add_re`, `Complex.sub_re`, `Complex.mul_re`,
   `Complex.ofReal_re`, plus a `linarith`-style finisher should suffice.
8. Close Step 9 (the main theorem). The `k = 0` branch is the only
   non-mechanical bit; if you adopt option 1, add `hk : 0 < k` and the
   branch disappears entirely.

### Scratch notes for the prover

* `Section454Aux.lean` opens `Matrix Complex` at line 35 and uses
  `algebraMap ℝ ℂ` as the lift map. `algebraic_identity_454A` uses the
  same `algebraMap ℝ ℂ`. **Convention is consistent.**
* `Section454Aux`'s namespace is `OpenMath.Chapter4.Section454Aux`. To
  shorten references, you may add `open OpenMath.Chapter4.Section454Aux`
  inside the proof block (or near the top of `Section454.lean` after the
  imports).
* `vanW₁ w 0 = 1` (per `vanW₁_apply` and `pow_zero`); this is the
  non-vanishing witness for Step 5 at `k ≥ 1`.
* If `Complex.div_re` does not unfold to the convenient form, fall back
  to `Complex.div_eq_mul_inv` + `Complex.inv_re` + manual rearrangement
  (more LOC but guaranteed available).
* The `1 - ((‖w‖^2 : ℝ) : ℂ)` term in the identity is **not** equal to
  `(1 : ℂ) - ‖w‖^2` (the latter is ill-typed); always go through the
  explicit ℝ → ℂ coercion, mirroring the way it appears in
  `algebraic_identity_454A`'s statement.
* Section451's `IsGStable` definition (line 111) destructures as
  `⟨G, hSymm, hPD, hPSD⟩`. The `hSymm` field is unused in this proof
  but must still be destructured.

### Pitfalls to avoid

* **DO NOT** unfold `M.gMatrix` directly inside `gStable_isAStable`'s
  body. Cycle 166 stalled Lean elaboration this way; cycles 167 + 168
  fixed it by going through `algebraic_identity_454A` and the named
  block-quadratic-form lemmas. The helper `gMatrix_map_eq` (cycle 168,
  `Section454.lean:320`) is already the only place where `M.gMatrix`
  unfolds; do not duplicate that work.
* **DO NOT** try to prove `(star α · β).re = (star β · α).re` via
  `Complex.mul_comm` alone — the conjugates differ. Use
  `(star α · β) + (star β · α) = 2 · (star α · β).re` (since
  `star β · α = star (star α · β)` and `x + star x = 2 · x.re`).
* **DO NOT** attempt to handle the `k = 0` edge case via complicated
  case analysis — adopt option 1 (`hk : 0 < k` precondition).
* **DO NOT** raise `maxHeartbeats`. Decompose further if any sub-proof
  blows up.
* **DO NOT** modify `OpenMath/Chapter4/Section454Aux.lean`. It is
  axiom-clean and Aristotle-finished; just consume its two public
  theorems.

---

## Priority 2 — `bdf2LMM_isAStable` (BDF2 corollary)

Place this immediately after `gStable_isAStable` in
`Section454.lean` (or in `Section451.lean` after `bdf2LMM_isGStable`,
whichever produces the cleanest namespacing — `Section454.lean` is
preferred since the file already opens both `Section410` and `Section451`).

```lean
/-- **BDF2 is A-stable.** A direct consequence of cycle 165's
`bdf2LMM_isGStable` and Theorem 454A. -/
theorem bdf2LMM_isAStable :
    OpenMath.Chapter4.Section451.bdf2LMM.IsAStable :=
  OpenMath.Chapter4.Section451.bdf2LMM.gStable_isAStable
    (by norm_num)  -- supplies the `hk : 0 < k` precondition (k = 2)
    OpenMath.Chapter4.Section451.bdf2LMM_isGStable
```

(One-liner if option 1 was adopted in Priority 1, with `hk : 0 < 2`
discharged by `norm_num` or `decide`. Verify the namespace path —
`bdf2LMM` lives in `Section451`'s namespace.)

---

## Faithfulness check (mandatory before commit)

For `gStable_isAStable`:

* **Entity ID**: `thm:454A`. Quote from
  `extraction/formalization_data/entities/thm_454A.json`:
  `statement_text` reads "A G-stable LMM is A-stable" (Butcher §454,
  Theorem 454A).
* **Lean signature**: `(M : LinearMultistepMethod k) (hk : 0 < k)
  (hG : M.IsGStable) : M.IsAStable`. Captures the textbook
  implication; the `hk` precondition is a faithfulness divergence
  documented in the docstring (textbook implicitly assumes `k ≥ 1`).
* **`IsAStable` is the boundary-locus form** (already documented in
  `Section454.lean`'s file-level docstring; do not invent a new
  divergence).
* **No new `axiom` / `constant`.** No `maxHeartbeats` bumps.
* **Tautology check**: the hypothesis `hG` is unfolded and consumed
  (G-stability provides `G`, `hPSD`, `hPD` — all three are used).
  Conclusion `0 < (α/β).re` is genuine, not a hypothesis.

For `bdf2LMM_isAStable`: corollary of two prior theorems, no new
mathematical content; the `IsAStable` predicate is non-vacuous in this
direction (positive witness; the negative direction is the cycle 166
`explicitEulerLMM_not_isAStable`).

---

## What NOT to try (failed approaches from the issue history)

* **Inline matrix-vector unfolding under nested if-then-else** — cycle
  166 stalled Lean elaboration ≥10 min this way. The
  `gTopLeft_quadForm_eq` / `gBottomRight_quadForm_eq` (cycle 167) +
  `algebraic_identity_454A` (cycle 168) decomposition is the working
  pattern. **Stay above this layer.**
* **Aristotle batch on the main theorem** — Aristotle had two failed
  long-running general-`n` attempts on `thm:550A` (cycles 141, 151)
  and is unlikely to handle this composition. Manual is faster.
  Aristotle is fine for the helpers that are pure complex arithmetic
  (Step 8) if manual stalls, but the main composition is straightforward.
* **`simp only [Matrix.dotProduct]`** — `dotProduct` is at root namespace
  in current Mathlib, not `Matrix.dotProduct` (recorded mistake from
  cycle 167). Use `show ∑ i, _ * _ = _` to expose sums, OR just rely on
  the existing named `_quadForm_eq` / `_dotProduct_lift` lemmas.
* **Deferring `k = 0`** without adopting option 1 — leaving a `sorry`
  in the `k = 0` branch regresses sorry count and supervisor scores
  negative. Either prove it via `βPoly = 0 ⇒ β(w) = 0` (only if
  `βPoly` at `k = 0` is genuinely zero, verify first), or add the
  `hk : 0 < k` precondition.

---

## Verification before commit (mandatory)

1. `lake env lean OpenMath/Chapter4/Section454.lean` exits 0 (no
   errors, no `sorry` warnings).
2. `grep -c sorry OpenMath/Chapter4/Section454.lean` → 0.
3. `grep -c sorry OpenMath/Chapter4/Section454Aux.lean` → 0
   (unchanged — should still be 0).
4. `lean_verify
   OpenMath.Chapter4.Section404.LinearMultistepMethod.gStable_isAStable`
   returns `[propext, Classical.choice, Quot.sound]` only.
5. `lean_verify
   OpenMath.Chapter4.Section454.bdf2LMM_isAStable` (or whatever
   namespace it lands in) likewise axiom-clean — only if Priority 2 lands.
6. Tautology scanner: `grep -nE
   ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'
   OpenMath/Chapter4/Section454.lean` returns no hits. (If you must
   introduce an `h_*` named hypothesis as a `rw … at` target, rename to
   `h*` per cycle 015's standing workaround.)
7. `lean_status.json` row for `thm:454A` updated to `formalized`,
   cycle 169 (only if Priority 1 lands).
8. `plan.md` Chapter 4 row for `thm:454A` flipped from `[ ]` to `[x]`
   (only if Priority 1 lands).
9. Issue file `.prover-state/issues/thm_454A_stage_2_3_stall.md` updated
   with a "Cycle 169 update — Stage 3 closed" section noting the
   `hk : 0 < k` faithfulness divergence (if option 1 is adopted).

---

## Cycle deliverable bar

* **Minimum (score ≥ 0)**: `gStable_isAStable` closed axiom-clean
  (Priority 1 only). Sorry count remains 0. `bdf2LMM_isAStable`
  deferred to cycle 170 with a one-line note in `task_results/cycle_169.md`.
* **Target (score = 2)**: both Priority 1 and Priority 2 land axiom-clean
  in the same commit. `thm:454A` row flips from `[ ]` to `[x]` in
  `plan.md`. Progress: 70 → 71/175 entities.
* **Stretch (score > 2)**: also begin a fresh entity; recommended pivot
  per cycle 162's backup pivot list — `def:422B` (underlying one-step
  method) or `def:442A` (principal sheet). Both are pure structural
  definitions; non-vacuity should fit in <100 LOC. Skip the stretch if
  Priority 1 takes longer than expected; do not jeopardise the
  axiom-cleanliness of `gStable_isAStable` to chase the stretch.

---

## Backup plans

* **B1 — `star_alpha_beta_re_pos` blows up.** If the Step 7 proof
  exceeds ~80 LOC or hits a `simp` divergence, decompose further:
  introduce a private helper for `(star α · β).re + (star β · α).re =
  2 · (star α · β).re` and a separate helper for the `re`-extraction
  from `algebraic_identity_454A`. Each ≤ 20 LOC. Cycle 168's pattern
  scales here.
* **B2 — `Complex.div_re` shape mismatch in Step 8.** Fall back to
  `Complex.div_eq_mul_inv` + `Complex.normSq_pos` + manual arithmetic.
  If still stuck, factor a private helper `complex_re_div_pos_iff`
  with the exact sign condition.
* **B3 — `k = 0` branch closure stalls.** Adopt option 1 (`hk : 0 < k`
  precondition). Document the divergence and move on.
* **B4 — Step 7 needs the imaginary-part identity.** Note that
  `algebraic_identity_454A`'s LHS has both `.re` and `.im`. The PSD
  helper from Aux gives `(LHS).re ≥ 0 ∧ (LHS).im = 0`. The RHS
  `.im = 0` follows from the `.im = 0` clauses of (2) and (3) since
  both terms are real (the `(star α * β + star β * α)` form is its
  own conjugate, and the inner-block term is real-times-PSD-quadratic).
  But for the proof you only need `.re`, so skip the `.im` analysis
  unless `Complex.add_re` / `Complex.sub_re` rewriting requires it.

If multiple backups fire and the cycle hits the 90-minute soft-budget
mark with no clear path, fall back to **B-Final**: ship the seven
helper skeletons with their `sorry` bodies, plus the closed ones (Steps
4, 6, 8 are easy and should land first). This regresses sorry count 0
→ N for some N ≤ 4, but produces a structurally complete scaffold that
cycle 170 can finish in <30 LOC. **Only invoke B-Final if all of
B1/B2/B3/B4 fail simultaneously.** The cycle 168 worker did not need
any backups; this should be the rare path.
