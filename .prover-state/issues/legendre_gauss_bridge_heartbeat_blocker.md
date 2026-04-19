# Issue: Legendre bridge and orthogonality exceed the cycle heartbeat budget

## Blocker
The remaining proof of `ButcherTableau.gaussLegendre_B_double` is blocked by the missing low-cost bridge from the recursive `shiftedLegendreP` definition to Mathlib's `Polynomial.shiftedLegendre`, together with a low-cost proof of the coefficient orthogonality identity.

The available Aristotle outputs do contain mathematically useful proofs, but the extracted versions rely on proof scripts that exceed this project's heartbeat constraint:
- the direct bridge theorem times out at `200000` heartbeats in `lean_run_code`
- the explicit coefficient development from Aristotle uses `set_option maxHeartbeats 400000` and `800000`

## Context
Relevant file:
- `OpenMath/Legendre.lean`

Remaining sorrys:
- `ButcherTableau.gaussLegendre_B_double`
- `ButcherTableau.gaussLegendreNodes_of_B_double`

Useful Aristotle results from cycle 153 triage:
- `1d9822aa-9d1d-4d23-abf6-501995a5f6a8`: completed; gives a bridge to `Polynomial.shiftedLegendre`, but its coefficient recurrence proof times out under the project budget
- `de165c89-6ceb-4a51-a674-ee4da6c4264b`: complete with errors; proves an abstract `B_extension_step` once a coefficient/orthogonality package is assumed
- `25f0bc02-fd9c-4e56-a5fe-dcb75e9a92c0` and `88562ee9-0604-4af8-af76-4cd109783926`: completed; contain full explicit coefficient developments, but they require forbidden heartbeat increases

New Aristotle job submitted this cycle:
- `eb87d287-96c7-4a1e-beaa-910fb0143c2b`
  Goal: a `≤200000`-heartbeat bridge / coefficient package for `shiftedLegendreP`

## What was tried
1. Checked all seven inherited Aristotle jobs before editing.
2. Extracted the completed outputs and inspected the generated Lean files and summaries.
3. Ran the best bridge candidate from Aristotle in `lean_run_code` without increasing `maxHeartbeats`.
4. Confirmed the bridge script fails by heartbeat exhaustion at the current project limit.
5. Inspected the more complete orthogonality development and confirmed it explicitly depends on `set_option maxHeartbeats 400000` / `800000`.

## Possible solutions
1. Harvest a cheaper proof from the new Aristotle prompt `eb87d287-96c7-4a1e-beaa-910fb0143c2b` if it returns a lower-cost bridge.
2. Replace the heavy coefficient-comparison proof with a cheaper recurrence proof for the polynomial itself, avoiding `simp_all` over coefficient formulas.
3. Prove only the explicit coefficient formula for `shiftedLegendreP` directly by induction on `n`, then derive orthogonality from the closed form without constructing the full bridge theorem.
4. If the bridge remains too expensive, target a localized inline package inside `gaussLegendre_B_double`: enough coefficients plus the `a_s ≠ 0` and orthogonality facts, but no global theorem.
