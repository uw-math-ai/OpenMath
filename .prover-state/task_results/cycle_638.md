# Cycle 638 Results

## Worked on
§521 LMM-as-GLM `B`-block shape projection lemmas (general `s`),
plus the two stability-matrix row-projection corollaries from the
fallback. All six lemmas live in `OpenMath/LMMAsGLM.lean` next to the
existing `V`-block projections (after `toGLM_V_natAdd_last_apply` /
after `toGLM_stabilityMatrix_apply`).

## Approach
For the four `B`-block projections (1-4 in the strategy):
ported the existing `V`-block recipe verbatim. Each proof is:

```
simp only [toGLM]
have hrow : Fin.cast (Nat.two_mul s)
              (Fin.cast (Nat.two_mul s).symm (Fin.<addCases-side> s j))
            = Fin.<addCases-side> s j := by ext; simp
rw [hrow, Fin.addCases_<left/right>, if_<pos/neg> hj]
```

selecting the appropriate `Fin.addCases_left`/`Fin.addCases_right`
branch and `if_pos hj`/`if_neg hj`.

For the two row corollaries (5-6 in the fallback):
applied `toGLM_stabilityMatrix_apply` and showed the `Bℂ` row entry
is zero by unfolding `Bℂ` to a real-to-complex coercion and applying
the new `B`-block simp lemmas, then closed with `ring`.

## Result
SUCCESS — all six lemmas land:

* `toGLM_B_castAdd_shift_apply` (`@[simp]`)
* `toGLM_B_castAdd_last_apply` (`@[simp]`)
* `toGLM_B_natAdd_shift_apply` (`@[simp]`)
* `toGLM_B_natAdd_last_apply` (`@[simp]`)
* `toGLM_stabilityMatrix_castAdd_shift_apply` (plain theorem)
* `toGLM_stabilityMatrix_natAdd_shift_apply` (plain theorem)

Verification:
* `lake env lean OpenMath/LMMAsGLM.lean` ✅
* `lake env lean OpenMath/RKAsGLM.lean` ✅
* `lake env lean OpenMath/GeneralLinearMethod.lean` ✅

No new live `sorry`. No `maxHeartbeats` change.

## Dead ends
**`simp [GeneralLinearMethod.Bℂ, toGLM_B_..._shift_apply m j hj]`**
inside the corollary proofs left an unsolved goal of the shape
`m.toGLM.B (Fin.cast _ (j.addNat s)) 0 = 0`. The `Fin.natAdd s j`
in the simp-lemma key was being rewritten to `j.addNat s` by another
simp lemma before the projection lemma could fire, so the projection
lemma was reported unused. **Fix**: replaced the bare `simp` with an
explicit `show` that pins the goal to the real-side cast, then
`rw [toGLM_B_..._shift_apply m j hj]` and `simp` to discharge
`((0 : ℝ) : ℂ) = 0`. Recipe to remember for downstream uses of these
`B`-block lemmas: when consuming through `Bℂ`, drop into `m.toGLM.B`
via `show` first to avoid the `natAdd` ↔ `addNat` simp-normal-form
divergence.

## Discovery
* No simp-loop at the existing `Bℂ` consumer in
  `toGLM_stabilityMatrix_apply` — the new `@[simp]` lemmas have
  hypotheses (`hj`) and only fire when the row index is in the exact
  `Fin.cast _ (Fin.castAdd|natAdd s j)` shape, so the generic
  `m.toGLM.Bℂ k 0` consumer at line 664 is unaffected. The `simp`
  call there still closes after `rw [stabilityMatrix_apply]`.
* `Fin.natAdd s j` is *not* simp-normal: simp prefers `j.addNat s`
  (or rewrites the head). This is what cost a debug round on the
  corollaries. Future stability-matrix entrywise lemmas should
  unfold `Bℂ` / `Vℂ` via `show ... = ((... : ℝ) : ℂ)` before invoking
  the new `B`/`V` projection simp lemmas, **not** through a single
  `simp [Bℂ, ...]` call.
* The stability-matrix shift-row collapse is now a one-liner
  (`rw [toGLM_stabilityMatrix_apply]; ... rw [hB]; ring`) which is
  exactly the row sparsity the BDF2 cycle 632 transport used by
  `fin_cases`. For general `s`, this is the structural piece that
  lets the iff-bridge group rows by "shift block (= `V`)" vs
  "implicit row (= `V` + resolvent term)" without enumerating
  `4 × 4` entries.

## Suggested next approach
Two more structural bricks before `LMM.toGLM_isAStable_iff` is
reachable:

1. **Implicit-row stability-matrix projection.** The complement to
   the two new shift-row corollaries: for `j : Fin s` with
   `(j : ℕ) + 1 = s`, give `m.toGLM.stabilityMatrix z` on the row
   `Fin.cast _ (Fin.castAdd s j)` (the `y_{n+s}` output row) in terms
   of `m.α`, `m.β`, and the resolvent `1 / (1 - z * m.β (Fin.last s))`.
   The `natAdd`-last row is even cleaner: by
   `toGLM_V_natAdd_last_apply` the `Vℂ` part is identically zero, so
   that row is purely `z * m.β (Fin.last s) * resolvent * Uℂ 0 l`.
   These two are direct corollaries of the new `B`-block lemmas plus
   the existing `V` projections.

2. **`Matrix.fromBlocks` decomposition for `m.toGLM.stabilityMatrix z`.**
   With (1) in hand, the matrix splits into a 4-block
   `(s × s) ⊕ (s × s)` decomposition where three of the blocks are
   either zero, identity-shift, or `α / β` companion-matrix shape and
   the fourth (the implicit row + `natAdd`-last row contribution) is
   rank-≤1. Cycle 639+ should land a generic
   `Matrix.fromBlocks_charpoly`-style helper or hand-roll the charpoly
   factorisation as `det = z-resolvent * (companion charpoly)`.

3. **Companion-matrix bridge.** Once the charpoly factorises, plug
   in Dahlquist's stability polynomial `ρ(z) - z · σ(z)` and the
   existing `LMM.IsAStable` ↔ companion-matrix root condition to
   close `LMM.toGLM_isAStable_iff`.

Cycle 639 should target step (1) only — both row projections are
~10 lines each and they finalize the row sparsity surface that the
fromBlocks decomposition needs. Do not attempt (2) before (1) lands.

## Aristotle
Did not submit. The four `B`-block lemmas and two corollaries land in
~50 lines total of mechanical proof, well under the cycle budget.
