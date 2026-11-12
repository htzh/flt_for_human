/-
  WORKORDER MS-7 row 410 — `Φ = Φ₂` at level two:
  `ModularCurve.ModularPolynomialData.phi_eq_phiTwo`.

  Statement verbatim from `Theorems/Thm_ModularCurve_ModularPolynomialData_phi_eq_phiTwo.lean`;
  proof transcribed from
  `P2M/Sol/S_ModularCurve_ModularPolynomialData_phi_eq_phiTwo.lean` (410 lines,
  pinned `aa2d8b3`), adapted to mathlib `v4.34.0`.

  ## What the proof is

  A `ModularPolynomialData 2` datum has `Φ` of `Y`-degree `ψ(2) = 3`
  (`data.natDegree_eq`), monic (`data.monic`), and vanishing at `j(q²)`
  (`data.eval_eq_zero`); `phiTwo` is written out coefficient by coefficient.
  The proof pins `Φ`'s three lower `Y`-coefficients to `phiTwoC0/C1/C2` by
  comparing `q`-expansions on the four coefficients `q⁻³ … q⁰`:

  * `PhiGen.splits_prime_of_isPrimitiveRoot` at `p = 2`, `ζ = -1` splits `Φ`'s
    `q`-expansion into `(X - q⁴j) · (X - j) · (X - (-j))`, so the three
    elementary symmetric functions of `{q⁴j, j, -j}` are the `q`-expansions of
    `Φ`'s coefficients (`coeff_identities`);
  * each of those is expanded in `q` through the `NF` normal form: a Laurent
    series `x` with `x = q^a · F(q)` and `F`'s first seven coefficients pinned
    by a list of integers (`LJ`, `LC`, `LA`, `L2` and their convolutions
    `nf_AB`, `nf_ACm`, `nf_BCm`, `nf_ABCm`, `nf_J22`, `nf_J23`);
  * `eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero` then upgrades the
    four-coefficient agreement to `data.Φ.coeff k = phiTwo.coeff k` for
    `k ≤ 2` (`natDegree_coeff_le` bounds the `Y`-degree of both sides by 3),
    and `p3`/`pge` finish `k = 3` (both are monic of degree 3) and `k ≥ 4`
    (`phiTwo.coeff k = 0` and `Φ` has `natDegree` 3).

  The `LowCoeffs`/`conv` list algebra is *not* restated here: it is public in
  `ModularCurve/JqCoefficients.lean`, namespace `ModularCurve.JCoeff`
  (`LowCoeffs`, `conv`, `length_conv`, `finset_sum_range_eq_list_sum`,
  `getD_conv`, `LowCoeffs.mul`, `LowCoeffs.congr`), and is imported and used as
  it stands.  The `NF` normal form on top of it (`ofPS`, `coeff_ofPS`,
  `coeff_single_mul_ofPS`, `eq_single_mul_ofPS`, `NF` and its three lemmas) has
  no port copy and is transcribed below.

  ## Public / private split

  Public: only the headline `ModularPolynomialData.phi_eq_phiTwo`.  Everything
  else — the whole `PhiTwoCalc` block — is `private`: nothing outside this
  module consumes the coefficient machinery, so no promotion is owed.  The
  pin's `phi_eq_phiTwo'` and its root-level `solution` wrapper are *inlined*
  into the headline here rather than restated: the pin's engine statement and
  its wrapper have the same shape, so keeping both would be a duplicate
  cluster at `dedup.py --tier shape`.  The headline therefore carries the
  engine's proof term directly.

  ## Deviations from the pin

  * The pin's `set_option maxHeartbeats 3200000 in` on `phi_eq_phiTwo'` is not
    transcribed (FR-0067): the module elaborates at the project's 200 k cap.
  * The pin's `attribute [-simp] ModularForm.val_heckeDiagMatrix …` prelude and
    its `set_option linter.unusedSimpArgs false` are not transcribed: no `simp`
    or `simp only` below meets those lemmas, and no simp argument is unused.
  * The pin's `p2m_open`/`p2m_export` re-export machinery is not needed: the
    port's `JqCoefficients`/`Jq`/`ClassicalModularPolynomials` already carry the
    names at their pin locations.
  * `Mathlib.Tactic.ComputeDegree` is imported for the two `compute_degree!`
    steps (`phiTwo_coeff`'s `natDegree ≤ 3`, `natDegree_phiTwoC`); it is the one
    mathlib import the workorder did not name.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ModularPolynomialData_phi_eq_phiTwo.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_ModularPolynomialData_phi_eq_phiTwo.lean

  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_phi_eq_phiTwo.lean
  spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_phi_eq_phiTwo.lean
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.LevelTwo`.
