# Cycle 273 — Aristotle submission

## Project

`727396d5-14f9-4014-9aad-1f38238a1651`

## Submitted

2026-05-15T12:59:00 UTC

## Target

`butcherShiftedLegendre_orthogonal` — Butcher §342 (342a) orthogonality on `[0, 1]`:

```lean
∀ {m n : ℕ}, m ≠ n →
  ∫ x in (0 : ℝ)..1,
    (butcherShiftedLegendre m).eval x * (butcherShiftedLegendre n).eval x = 0
```

## Hypotheses provided

The submission file ships the (342b), (342c), (342e), and degree results
from cycles 271-272 as named **axioms** so Aristotle can cite them directly
(without having to re-prove them). The axioms are:

* `butcherShiftedLegendre_eval_one`
* `butcherShiftedLegendre_eval_one_sub`
* `butcherShiftedLegendre_rodrigues`
* `butcherShiftedLegendre_natDegree`

## Strategy hint (in submission prompt)

Use Rodrigues' formula `butcherShiftedLegendre_rodrigues` plus integration
by parts `n` times. The boundary terms vanish at `0` and `1` because
`D^k (X^n (1-X)^n)` retains a factor of `X^j (1-X)^{n-k+...}` for every
Leibniz summand at every `k < n`. After `n` integrations by parts, all
derivatives sit on `P_m^*`; since `natDegree P_m^* = m < n`, `D^n P_m^* = 0`.

## Polling

Per CLAUDE.md single-poll discipline: do NOT poll this cycle. Cycle 274's
planner will check status and integrate any successful result.
