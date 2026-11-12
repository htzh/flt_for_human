/-
  T9 — the integrality of the descended coefficients.

  This is the first half of the cone's piece (b): the descended family
  `c : ℕ → LaurentSeries ℚ` of `phiProd` has **integer** `q`-expansion
  coefficients (`PhiGenDescends.intCoeffs`), and consequently a polynomial
  `P ∈ ℚ[X]` with `IntCoeffs (aeval jq P)` already lies in `ℤ[X]`
  (`aeval_jq_intCoeffs_descent`). Together they are what (d)'s
  `exists_modularPolynomialData_coeff_eq` needs to build an element of
  `ℤ[X][Y]`.

  ## Route A shipped (the deviation from FLT's script)

  FLT proves the first statement coefficientwise: it defines
  `CoeffsIntegral f := ∀ m, f.coeff m ∈ integralClosure ℤ K` and proves it is
  closed under `0, 1, -, *, qExpand, qTwist` (six lemmas), then reads the
  integrality of `(phiProd …).coeff k` off three polynomial-coefficient lemmas
  (`coeffsIntegral_coeff_X_sub_C`, `_mul`, `_prod`, ~42 lines). This port takes
  the route the work order calls **Route A**, and runs it over the source ring
  `ℤ[ζ] := Algebra.adjoin ℤ {ζ}` rather than over `𝒪`:

  * `jq`'s coefficients are integers (`intCoeffs_jq`), so `jq` is a series over
    `ℤ[ζ]` (`jqS`);
  * `ζ` is a unit of `ℤ[ζ]` (`zetaUnitS`, inverse `ζ ^ (ℓ - 1)`; `ζ ^ ℓ = 1` is
    the only input), so the conjugates are the same `qExpand`/`qTwist` formula
    over `ℤ[ζ]` (`conjAdjoin i`);
  * the product over `ℤ[ζ]` has `phiProd` as its image (`prod_eq_of_lift`), so
    every coefficient of `phiProd` is the image of an element of `ℤ[ζ]`
    (`coeff_phiProd_mem`);
  * `ℤ[ζ] ≤ 𝒪` (`zetaRing_le`, one `mem_integralClosure_of_pow_eq_one`), so those
    coefficients are integral;
  * the descent `hc` plus injectivity of `coeffEmb` produces the integer.

  Nothing here needs the *image* of the lift under `algebraMap 𝒪 K`, i.e. the
  `conjO`/`phiProdO` theory and `map_phiProdO` of the first version: membership in
  `𝒪` is all `intCoeffs` consumes. That image theory is shelved in
  `Reserve/ModularCurve/PhiGenIntegralityImage.lean`.

  The measured payoff is in `logs/phiGen-port.md` §9: the ~83 lines of FLT's
  `CoeffsIntegral` closure and polynomial-coefficient machinery are replaced by
  the ring structure of `LaurentSeries ↥(ℤ[ζ])` plus the map `ℤ[ζ] → K`, and the
  manual root-of-unity integrality by one `mem_integralClosure_of_pow_eq_one` over
  `X ^ ℓ - 1`.

  **Deviation from the work order's letter.** `poleOrderLE_aeval_jq` could not be
  promoted into `Defs/Jq.lean` (it needs `PoleOrderLE`, defined in
  `Defs/PhiGen.lean`, which imports `Defs/Jq.lean`); it was promoted into
  `Defs/PhiGen.lean` instead, and `coeff_aeval_jq_neg` into `Defs/Jq.lean`. The
  pin's public copy of both is
  `P2M/Sol/S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:

  - `P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.lean` (239) — the
    product's integrality;
  - `P2M/Sol/S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean` (308, of
    which ~108 is the descent and ~180 a duplicated `TPoleOrderLE` block that
    belongs to the pole-bound topic and is **not** ported here).

  The two public statements are verbatim from their `Theorems/` wrappers.

  ## Assumptions

  `LaurentSeries`, `HahnSeries`, `PowerSeries`, `Polynomial`, `integralClosure`,
  `IsIntegrallyClosed.isIntegral_iff` and `mem_integralClosure_iff` are mathlib's;
  `IntCoeffs`, `PhiGenDescends`, `conj`, `phiProd` are the port's `Defs/PhiGen`
  and `jq`, `jq_pow`, `coeff_jq_pow_self`, `coeff_jq_pow_of_lt`, `jNum`,
  `jNumQ`, `coeff_aeval_jq_neg` the port's `Defs/Jq`; `coeffMap`,
  `coeffEmb`, `coeffMap_coeff`, `coeffMap_qExpand`, `ofPowerSeries_coeff_of_neg`
  the port's `Defs/Laurent`/`Defs/Jq`. Names are FLT's verbatim where the pin has
  them.
-/

-- Body retired: this module's content now lives in
-- `FLTForHuman.ModularCurve.ModularEquation.Construction`.
