# Cycle 748 Results

## Worked on

- `plan.md` housekeeping: marked §463 Milne device closed in the §46
  list, removed the redundant Backlog Queue item #4 (Milne device),
  renumbered subsequent items, and rotated the Backlog Queue's §54
  DIMSIM entry into `## Current Target`.
- New file `OpenMath/DIMSIM.lean`: Butcher §54 DIMSIM type 1/2/3/4
  classification scaffold over `GeneralLinearMethod s r`, plus an
  RK-as-GLM type-1 sanity bridge with a forward-Euler witness.

## Approach

1. Read `OpenMath/GeneralLinearMethod.lean` to confirm `IsExplicit`'s
   convention: `∀ i j : Fin s, j.val ≥ i.val → m.A i j = 0`.
2. Read `OpenMath/RKAsGLM.lean` and `OpenMath/RungeKutta.lean` to find
   `toGLM_isExplicit` and `rkEuler_explicit` (the strategy named the
   forward-Euler tableau `rkForwardEuler`; in the codebase it is
   `rkEuler`).
3. Wrote the seven `Prop`-valued predicates exactly as the strategy
   prescribed:
   - `IsLowerTriangular` / `IsStrictLowerTriangular`,
   - `HasConstantDiagonal`,
   - `IsRankOneV`,
   - `IsDIMSIMType1` / `IsDIMSIMType2` / `IsDIMSIMType3` / `IsDIMSIMType4`.
4. Added the three theorem-level bridges: `IsExplicit ⇒
   IsStrictLowerTriangular ⇒ IsDIMSIMType1`, type-2-with-zero-diagonal
   collapse to type 1, and the §502 RK-as-GLM bridge from
   `t.IsExplicit` to `t.toGLM.IsDIMSIMType1`.
5. Concrete witness: `rkEuler_toGLM_isDIMSIMType1` is one application
   of the §502 bridge to `rkEuler_explicit`.

## Result

SUCCESS.

- `lake env lean OpenMath/DIMSIM.lean` compiles cleanly with no output
  (no errors, no warnings).
- `git grep -n 'sorry' OpenMath/DIMSIM.lean` returns nothing.
- File length is 111 lines, well under the 250-line strategy cap.

## Dead ends

None. The strategy's predicate phrasing matched the existing
`IsExplicit` convention up to the standard `Fin.le_iff_val_le_val`
unfolding, so the `IsExplicit ⇒ IsStrictLowerTriangular` bridge is a
single intro plus a `Fin.le_iff_val_le_val.mp` rewrite.

The strategy named the forward-Euler tableau `rkForwardEuler`, but the
codebase calls it `rkEuler`. Used the correct name.

## Discovery

- `GeneralLinearMethod.IsExplicit` and `IsStrictLowerTriangular` are
  *not* definitionally equal even though they unfold to the same
  conjunction up to argument order: `IsExplicit` uses `j.val ≥ i.val`
  and `IsStrictLowerTriangular` uses the bundled `Fin.le`. The bridge
  is `Fin.le_iff_val_le_val.mp`, a one-step rewrite, but it is not
  `id` — useful to know if a future cycle wants to fold the predicate
  back into `IsExplicit`.
- `OpenMath.lean` (the root manifest) does not currently import
  `RKAsGLM`, `MilneDevice`, or other Chapter-5 modules; matching
  existing convention, `DIMSIM` is also left out of the manifest. If a
  future cycle wants `lake build` to pick these up automatically, the
  manifest needs a backfill pass.

## Suggested next approach

1. **Type-3 / type-4 RK sanity check** (deferred this cycle to keep
   the file tight). The RK-as-GLM embedding has `r = 1`, so its
   `1 × 1` `V = 1` is trivially rank-one (`u ≡ 1`, `v ≡ 1`). One
   small lemma `toGLM_isRankOneV : (t.toGLM).IsRankOneV` plus a
   product theorem yields `toGLM_isDIMSIMType3_of_isExplicit` for
   free.
2. **§543 ARK structural conditions** — Almost Runge–Kutta methods
   add a single algebraic condition on `B` and `V`; that is a clean
   predicate-level cycle on top of the §54 surface landed here.
3. **§55 IRKS** (Backlog #6) — needs the doubly-companion-matrix
   construction; meatier than §54 but built on the same predicate
   surface. Best opened only after the §543 ARK predicates exist.
4. **`OpenMath.lean` manifest backfill** — many Chapter-5 modules
   (`RKAsGLM`, `LMMAsGLM`, `MilneDevice`, `DIMSIM`, etc.) are
   compiled individually but not picked up by the root manifest.
   A small bookkeeping cycle could add them so `lake build` covers
   them by default.
