# Issue: Forward-difference orthogonality port for Legendre is not yet repo-ready

## Blocker
The cleanest non-integral route for `gaussLegendre_B_double` still seems to be the forward-difference identity

```lean
∑ l in Finset.range (s + 1),
  ((-1 : ℝ) ^ l * ↑(s.choose l) * ↑((s + l).choose s) / ((l : ℝ) + (j : ℝ) + 1)) = 0
```

for `j < s`, but the harvested Aristotle proof does not port directly into `OpenMath/Legendre.lean`.

## Context
Useful completed Aristotle outputs inspected this cycle:
- `25f0bc02-fd9c-4e56-a5fe-dcb75e9a92c0`
- `1d9822aa-9d1d-4d23-abf6-501995a5f6a8`
- `d8e585e3-7786-4769-9999-bcd071014970`

The current target file still has only these two `sorry`s:
- `OpenMath/Legendre.lean:185`
- `OpenMath/Legendre.lean:225`

`lake env lean OpenMath/Legendre.lean` succeeds after reverting the failed port.

## What was tried
- Attempted to transplant the forward-difference proof structure based on:
  - `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`
  - `fwdDiff_iter_eq_sum_shift`
  - the auxiliary polynomial
    `Q_j(X) = ∏_{m ∈ range s, m ≠ j} (X + (m + 1))`
- Tried to express
  `Q_j(l) = s! * choose (l + s) s / (l + j + 1)`
  and factor the alternating sum into the desired orthogonality identity.
- Backed the change out when the port exposed several mismatches at once:
  - `Finset.prod` / `Finset.sum` translation details from the Aristotle file
  - `natDegree_prod` side goals and nonzeroness obligations
  - sign normalization lemmas that did not transfer as written
  - evaluation rewriting for the auxiliary polynomial

## Possible solutions
- Stage the port in a scratch Lean file first, not directly in `OpenMath/Legendre.lean`.
- Minimize the proof to three independently checked lemmas:
  1. degree bound for `Q_j`
  2. closed form for `Q_j.eval (l : ℝ)`
  3. alternating-sum normalization from `fwdDiff_iter_eq_sum_shift`
- Only after those compile cleanly, inline the final orthogonality theorem into the main proof of `gaussLegendre_B_double`.
- If the forward-difference route remains brittle, switch back to the bridge-first plan:
  prove the equivalence between recursive `shiftedLegendreP` and Mathlib's `Polynomial.shiftedLegendre`, then derive orthogonality from coefficients there.
