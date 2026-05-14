# Cycle 243 Results

## Worked on

P1 (shipped): `algebraicStability_residual` — §523 helper bridging
`thm:523A` (the identity) and `thm:523B` (the inequality).

P2a (shipped): `algebraicStability_contracting` — strict-contraction
strengthening of `thm:523B` (parameterised by `c ≥ 1`).

Both theorems live in `OpenMath/Chapter5/Section523.lean` in the
`OpenMath.Chapter5.Section510.GeneralLinearMethod` namespace.

## Approach

### P1 — `algebraicStability_residual`

Followed the planner's spec verbatim. Statement: under the same
hypotheses as `algebraicStability_identity` (symmetric `D`, GLM step
equations `hStage`/`hOut`), the difference
`‖y_next‖²_G − ‖y_prev‖²_G` equals
`2⟨hF, Y⟩_D − ‖hF ⊕ y_prev‖²_M`.

Proof body (2 lines):
```lean
  have hId := M.algebraicStability_identity D G hD h F Y y_prev y_next hStage hOut
  linarith
```

Inserted between the identity's non-vacuity example (line 248) and
the inequality's docstring (line 250), with a co-located non-vacuity
example at `(s, r) = (1, 1)` on `explicitEulerGLM`. Slightly different
location from the strategy's literal text ("between line 222 and line
234"), but keeps each theorem with its example block — semantically
the same content placement.

### P2a — `algebraicStability_contracting`

Followed the planner's spec. Added immediately after the inequality's
non-vacuity example block, with a parallel non-vacuity example.

Proof body (3 lines):
```lean
  have hRes := M.algebraicStability_residual D G hD h F Y y_prev y_next hStage hOut
  have hMq : 0 ≤ … := by simpa using hM_psd.dotProduct_mulVec_nonneg …
  linarith
```

The hypothesis `_hc : 1 ≤ c` is not consumed by `linarith` (the proof
runs for any real `c`), but it is load-bearing for the *meaning*: only
`c ≥ 1` makes the contraction bound stronger than dissipativity at
`c = 1`. Underscore prefix silences the unused-variable linter while
preserving the parameter for callers and documentation.

## Result

**SUCCESS — both P1 and P2a shipped.**

* `OpenMath/Chapter5/Section523.lean` compiles cleanly via
  `lake env lean OpenMath/Chapter5/Section523.lean` (no errors,
  no warnings).
* `mcp__lean-lsp__lean_diagnostic_messages` returns `[]`.
* `grep -c sorry OpenMath/Chapter5/Section523.lean` returns `0`.
* `lean_verify` on
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.algebraicStability_residual`
  returns `[propext, Classical.choice, Quot.sound]` (axiom-clean).
* `lean_verify` on
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.algebraicStability_contracting`
  returns `[propext, Classical.choice, Quot.sound]` (axiom-clean).
* No regression on cycle 241/242 landmarks — the identity, inequality,
  and stability-matrix definitions are untouched; only additive
  insertion after each landmark's non-vacuity example.

## Faithfulness check

### `algebraicStability_residual`

* Entity ID: **none** — this is a helper lemma, NOT a textbook
  entity. Documented in the docstring as the textbook stepping-stone
  between `thm:523A` (identity) and `thm:523B` (inequality). No
  `lean_status.json` row added.
* Textbook statement quoted: N/A (not in `extraction/formalization_data/entities/`).
  The "textbook" framing is Butcher's identity-then-inequality
  expository pattern; the residual form is the natural
  re-arrangement done implicitly in Butcher's proof of `thm:523B`
  on p. 428.
* Lean statement captures: an equation of three real terms; the
  hypotheses are *exactly* those of `algebraicStability_identity`
  (no strengthening, no weakening).
* Tautology check: conclusion (an equality of three terms) is not
  any hypothesis; it is the rearrangement of `hId`. ✓
* Identity check: proof is `linarith` after a `have`, not `exact h`.
  ✓
* Hypothesis strength: identical to `algebraicStability_identity`
  (cycle 241). No strengthening. ✓
* Smuggling: no new `def`, `structure`, or `class`. ✓

### `algebraicStability_contracting`

* Entity ID: **none** — this is a strict-contraction strengthening
  of Butcher's `thm:523B`, not a textbook-named entity. Documented
  in the docstring. No `lean_status.json` row added.
* Textbook statement quoted: N/A. Butcher's `thm:523B` is the
  `c = 1` special case (dissipative ⇒ non-expansive); this lemma
  parameterises the contraction strength by `c ≥ 1`.
* Lean statement captures: at `c = 1` it recovers
  `algebraicStability_inequality` (the residual term `(c−1) · …`
  vanishes and `hContract` reduces to `2⟨hF, Y⟩_D ≤ 0`, equivalent
  to the inequality's `hDiss`). For `c > 1` it is a strictly
  stronger conclusion. ✓
* Tautology check: conclusion is an inequality on
  `‖y_next‖²_G + (c−1) · …`, not present as a hypothesis. ✓
* Identity check: proof is `linarith` after two `have`s, not
  `exact h`. ✓
* Hypothesis strength: PSD on `M`, symmetric `D`, contraction
  bound `hContract`, and `c ≥ 1`. The `c ≥ 1` is not consumed by
  the proof but is the load-bearing condition for the lemma's
  intended use case (without it, the conclusion is vacuously
  weaker than `c = 1`). Marked `_hc` to document intentional
  non-use. ✓
* Smuggling: no new `def`, `structure`, or `class`. ✓

## Dead ends

None. P1 elaborated on the first attempt; P2a elaborated cleanly
with one cosmetic linter fix (rename `hc` → `_hc`).

## Discovery

* The `algebraicStability_identity` ↔ `algebraicStability_inequality`
  pipeline has a clean three-form structure now: **identity**
  (cycle 241) → **residual** (cycle 243) → **inequality**
  (cycle 242). Future §523 work (e.g. quantitative bounds,
  perturbation analysis) can route through the residual form to
  avoid re-deriving the rearrangement.
* The `_hc` underscore-prefix idiom is the cleanest way to keep
  a semantically-meaningful but proof-unused hypothesis in a
  signature without triggering linter warnings. Documenting via
  docstring is the right complement.

## Suggested next approach

### Cycle 244 candidate (planner-friendly note)

After §523's three-form completion, the natural next ship is a
fresh `[ ]` entity from `plan.md` that is NOT blocked by the
deferred clusters (AN-stability, Jordan canonical form, Rouché's
theorem, §441-GPFS, §388 tree-horizontal-product, §380
thm:381G/thm:381H).

**Recommended target**: `lem:319A` (Global truncation error, RK).
This is the RK analogue of `thm:212A` (Euler's global truncation
error), which is already formalised in `OpenMath/Chapter2/Section213.lean`.
The structural pattern should transfer with modest adaptation:
the Lipschitz-stability argument is identical, only the local
truncation error bound changes from one-step to RK-stage form.

**Estimated dependencies** (cycle 244 planner should verify):
- Local truncation error of an RK method (likely `lem:319B` or
  similar — must be in place or stated with `sorry`).
- Lipschitz continuity of the RK increment function.
- The Gronwall-style induction lemma used in `thm:212A`.

**Estimated LOC**: 80–120 (proof) + 20–30 (non-vacuity at
`explicitEulerRK` if such an instance exists in §322).

**Recommended Lean file location**: new file
`OpenMath/Chapter3/Section319.lean` or appended to whichever §319
file already exists. (Planner should grep for `Section319` first.)

**Risk**: medium. The proof pattern is well-trodden, but the
RK-specific Lipschitz bound on the increment function may require
new helper lemmas about sums-of-Lipschitz-functions.

**Alternative**: `cor:550C` (companion-matrix derivative basis
inverse). Lower risk if the cycle 138–150 doubly-companion-matrix
infrastructure suffices, but verifying that requires reading
seven prior cycles' deliverables. Recommend `lem:319A` as primary;
`cor:550C` as fallback.
