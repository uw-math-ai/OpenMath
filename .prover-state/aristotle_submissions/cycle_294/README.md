# Cycle 294 Aristotle submissions

## (342g) — `P_n^*` has `n` distinct real zeros in `(0, 1)`

* **File**: `342g_zeros.lean`
* **Project ID**: `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`
* **Submitted**: 2026-05-15 22:11:40 UTC
* **Status at submission**: `QUEUED`
* **Poll cycle**: 295 (single-poll discipline per CLAUDE.md)

### Cited axioms
All from `OpenMath/Chapter3/Section342.lean` at HEAD, axiom-clean:

* `butcherShiftedLegendre_eval_one` (342b)
* `butcherShiftedLegendre_eval_one_sub` (342c, parity)
* `butcherShiftedLegendre_eval_zero`
* `butcherShiftedLegendre_natDegree` = n
* `butcherShiftedLegendre_zero`, `_one`, `_two` (explicit forms for base cases)
* `butcherShiftedLegendre_rodrigues` (342e)
* `butcherShiftedLegendre_orthogonal` (342a, general)
* `butcherShiftedLegendre_norm_sq` (342d, general)
* `butcherShiftedLegendre_orthogonal_to_lower_degree` (cycle 292, **key**)
* `butcherShiftedLegendre_recurrence` (342f, cycle 293)

### Strategy hint provided
Proof by contradiction: form `Q := ∏ᵢ (X − C xᵢ)` from the sign-change
points (`k < n`); `P_n^* · Q` has constant non-zero sign on `(0, 1)`
so its integral is nonzero, contradicting the cycle-292 lemma
`butcherShiftedLegendre_orthogonal_to_lower_degree` applied to `Q`.
Combined with `natDegree P_n^* = n` and `roots.card ≤ natDegree`,
equality is forced.
