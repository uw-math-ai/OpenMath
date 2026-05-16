# Cycle 320 Results

## Worked on

§344 Phase C.2 — six small-`s` abscissae functions for the
Radau I, Radau II, and Lobatto quadrature families
(`butcherRadauI_zeros_one`, `butcherRadauI_zeros_two`,
`butcherRadauII_zeros_one`, `butcherRadauII_zeros_two`,
`butcherLobatto_zeros_two`, `butcherLobatto_zeros_three`) plus
their 17 supporting `_isRoot` / `_strictMono` / `_mem_Icc`
theorems. Builds directly on cycle 319's explicit-root theorems.

## Approach

Followed the cycle 320 strategy verbatim:

1. **Definitions**. Each abscissae function is a `noncomputable
   def : Fin s → ℝ` with pattern matching on `⟨k, _⟩` for
   `k = 0, 1, [2]`. Bodies are the exact rational roots shipped
   in cycle 319 (`(0)`, `(0, 2/3)`, `(1)`, `(1/3, 1)`, `(0, 1)`,
   `(0, 1/2, 1)`).

2. **`_isRoot` theorems**. `fin_cases i` unfolds the pattern
   match, and each branch cites the appropriate conjunct from
   the cycle 319 `_roots` / `_root` theorem.

3. **`_strictMono` theorems** (only the five multi-stage cases).
   `intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
   [<defname>]` closes most branches (the false-hypothesis ones
   from `simp_all` discharging `hij : k < k` etc., plus the
   `0 < 1` real branches via `simp_all` arithmetic). For the
   two cases with fractional residue (Radau II `1/3 < 1` and
   Lobatto three `0 < 1/2`, `1/2 < 1`) a trailing `norm_num`
   sequenced via newline closes the lone residual goal — the
   `unnecessarySeqFocus` linter confirmed only one goal
   remained after `simp_all`, so `; norm_num` (newline) is the
   correct combinator.

4. **`_mem_Icc` theorems**. `fin_cases i + simp [<defname>,
   Set.mem_Icc] + norm_num` (newline-sequenced where residue
   exists). For Radau I/II `_one` and Lobatto `_two` `simp`
   alone closes everything; for Radau I/II `_two` and Lobatto
   `_three` a trailing `norm_num` closes the fractional
   residue.

5. **Verification**. `lake env lean
   OpenMath/Chapter3/Section344.lean` and `lake env lean
   OpenMath/Chapter3.lean` both clean (no warnings, no
   errors). `lean_verify` on four representative theorems
   (`butcherRadauI_zeros_two_isRoot`,
   `butcherRadauII_zeros_two_strictMono`,
   `butcherLobatto_zeros_three_strictMono`,
   `butcherLobatto_zeros_three_mem_Icc`) all show axioms
   `[propext, Classical.choice, Quot.sound]` only.

## Result

**SUCCESS.** All six abscissae definitions and 17 supporting
theorems shipped axiom-clean. Section344.lean grew from 585 to
763 LOC (178 net LOC, within the ~150 LOC strategy estimate
with the docstring/comment overhead).

No sorries introduced. No `axiom` / `constant` declarations.
No `maxHeartbeats` bumps. No Aristotle calls (per strategy —
deliverables too small/mechanical to benefit).

## Faithfulness check

Six new `noncomputable def`s:

* **`butcherRadauI_zeros_one : Fin 1 → ℝ`** = `(0)`.
  Anchor entity `thm:344A`. Textbook (Butcher §344 p. 244)
  does not name the abscissa arrays explicitly at small-`s`;
  they are derived from `thm:344A` part I:
  > For the Radau I formula, `c_1 = 0`.
  Lean statement captures: same content (single abscissa,
  value `0`). No equivalence lemma needed; the
  `_isRoot` theorem is the bridge.

* **`butcherRadauI_zeros_two : Fin 2 → ℝ`** = `(0, 2/3)`.
  Derived from `thm:344A` part I plus cycle 319's
  `butcherRadauI_two_roots` (explicit roots of `butcherRadauI
  2 = 6X² − 4X = 2X(3X − 2)`).
  Lean statement captures: same content.

* **`butcherRadauII_zeros_one : Fin 1 → ℝ`** = `(1)`.
  Derived from `thm:344A` part II:
  > For the Radau II formula, `c_s = 1`.
  Lean statement captures: same content.

* **`butcherRadauII_zeros_two : Fin 2 → ℝ`** = `(1/3, 1)`.
  Derived from `thm:344A` part II plus cycle 319's
  `butcherRadauII_two_roots`.
  Lean statement captures: same content.

* **`butcherLobatto_zeros_two : Fin 2 → ℝ`** = `(0, 1)`.
  Derived from `thm:344A` part III:
  > For the Lobatto formula, `c_1 = 0`, `c_s = 1`.
  Lean statement captures: same content.

* **`butcherLobatto_zeros_three : Fin 3 → ℝ`** = `(0, 1/2, 1)`.
  Derived from `thm:344A` part III plus cycle 319's
  `butcherLobatto_three_roots`.
  Lean statement captures: same content.

Seventeen new theorems (six `_isRoot` + five `_strictMono`
+ six `_mem_Icc`):

* **Tautology check**: none of the conclusions appear as
  hypotheses (none of these theorems have hypotheses beyond
  the `i j : Fin n` arguments).

* **Identity check**: each `_isRoot` proof is `fin_cases i +
  exact <cycle 319 root>` — real work via `Fin` unfolding plus
  cycle 319 citation; the abscissae values are NOT identical
  to the roots' Lean expressions until `fin_cases` reduces.
  `_strictMono` and `_mem_Icc` proofs delegate to `simp_all` /
  `norm_num` arithmetic on the concrete rational values.

* **Definition smuggling check**: each abscissae function is
  a packaging of explicit roots into the `Fin s → ℝ`
  enumeration form expected by `RKTableau`. The naming
  reflects "Radau I abscissae at `s` stages"; the
  pattern-match bodies are the textbook root values; the
  ordering matches Butcher's `c_1 < c_2 < … < c_s`
  convention. No definitional smuggling — the underlying
  mathematical content is the cycle 319 explicit roots,
  exposed in a different shape.

* **Hypothesis strength check**: all 17 theorems are
  universal numerical facts over the `Fin n` index space. No
  hypotheses beyond `i j : Fin n`. Minimal-strength
  signatures.

* **Absent theorem check**: nothing promised but missing.
  Every theorem declared in the strategy is present.

## Dead ends

None this cycle — all deliverables landed on the first
implementation pass. The only minor course-correction was
cleaning up `<;> norm_num` lint warnings: `simp_all` is
powerful enough to close all branches in the Radau I
`(0, 2/3)` and Lobatto `(0, 1)` `_strictMono` cases (no
trailing `norm_num` needed), but leaves a single residual
goal for the Radau II and Lobatto-three cases (closed by
`norm_num` sequenced via newline rather than `<;>`).

## Discovery

* **`simp_all` + `fin_cases` is a clean closure tactic for
  `Fin n` strict-monotonicity proofs**. Across all five
  `_strictMono` proofs, the pattern `intro i j hij; fin_cases
  i <;> fin_cases j <;> simp_all [<defname>]` closes all
  false-hypothesis branches (where `hij : k < k` or `hij :
  k < 0` etc.) automatically via `Fin.lt_def` unfolding.
  Real numerical branches close via `simp_all` for
  `0 < 1`-style trivialities, leaving fractional residue for
  `norm_num`. Useful template for future small-`s` `_strictMono`
  proofs.

* **Lint distinction `<;>` vs `;`**: when `simp_all` (or
  `simp`) closes all-but-one branch after `fin_cases ... <;>
  fin_cases ...`, the trailing `<;> norm_num` triggers
  `linter.unnecessarySeqFocus` because only one goal
  remains. The fix is to sequence with newline (equivalent to
  `;`) rather than `<;>`. Saves a small amount of lint noise.

* **`noncomputable def` pattern matching on `Fin n` works
  with the `⟨k, _⟩` shape directly**. No need for
  `Fin.cases`. Each branch reduces by `rfl`, which is what
  makes `fin_cases i` unfold the pattern definitionally.

## Suggested next approach

**Cycle 321 target**: small-`s` Lagrange quadrature weights.
For each of the six abscissae functions, define
`_quadratureWeights : Fin s → ℝ` as
`∫₀¹ (Lagrange.basis Finset.univ (butcher<Family>_zeros_<s>) j).eval x`,
mirroring cycle 303's `butcherShiftedLegendre_quadratureWeights`
construction. Then prove the closed-form numerical values via
paper-verified integration:

| Family       | Stages | Weights                      |
|--------------|--------|------------------------------|
| Radau I      | s=1    | `(1)`                        |
| Radau I      | s=2    | `(1/4, 3/4)`                 |
| Radau II     | s=1    | `(1)`                        |
| Radau II     | s=2    | `(3/4, 1/4)`                 |
| Lobatto      | s=2    | `(1/2, 1/2)` (trapezoidal)   |
| Lobatto      | s=3    | `(1/6, 2/3, 1/6)` (Simpson)  |

~150 LOC estimate. **Risk**: integration step may hit cycle
274/281's `butcherShiftedLegendre_norm_sq_*` heartbeat
territory. Mitigation: split per-stage, define each
`_quadratureWeights_<family>_<s>` as a separate `def`
followed by its `_apply` lemma rather than packaging six
defs into a single multi-target file section.

Cycle 322+ pivot: small-`s` `RKTableau` construction. Radau
IA `s=1` (backward Euler) and Lobatto IIIB `s=2` (trapezoidal
rule) are particularly tractable. General-`s` requires the
cycle 308–312 collocation lift recipe ported to §344's
abscissae.
