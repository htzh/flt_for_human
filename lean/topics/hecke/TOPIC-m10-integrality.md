# Topic m10 — tower integrality/finiteness and the Hecke integrality predicates (M10)

**Status: work order drafted (pending the earlier sets).** First topic of
[SET-M4](SET-M4.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** One module, `FLTForHuman/ModularCurve/HeckeInputs/Integrality.lean`,
with the 13 M10 nodes:

**Tower maps (5).**
- `ModularCurve.towerInclBar_isIntegral (L) {N M} [NeZero N] [NeZero M] (h : N ∣ M) :
  (towerInclBar L h).toRingHom.IsIntegral`
- `ModularCurve.towerSubstBar_isIntegral (L) {N M} (ℓ) [Fact ℓ.Prime] (h : N*ℓ ∣ M) :
  (towerSubstBar L N ℓ h).toRingHom.IsIntegral`
- `ModularCurve.towerInclBar_finiteAlong (L) {N M} (h : N ∣ M) :
  FiniteAlong L (towerInclBar L h)`
- `ModularCurve.towerSubstBar_finiteAlong (L) {N M} (ℓ) [Fact ℓ.Prime] (h : N*ℓ ∣ M) :
  FiniteAlong L (towerSubstBar L N ℓ h)`
- `ModularCurve.towerInclBar_surjective_of_dvd_dvd (L) {N M} [NeZero N] [NeZero M]
  (h : N ∣ M) (h' : M ∣ N) : Function.Surjective (towerInclBar L h)`

**The general datum forms (4).**
- `ModularCurve.finiteAlong_heckeAlphaBar_of_modularPolynomialData (L) {ℓ} [NeZero ℓ]
  (data : ModularPolynomialData ℓ) (hℓ : ℓ.Prime) (N) [NeZero N] :
  FiniteAlong L (heckeAlphaBar L N ℓ)`
- `ModularCurve.finiteAlong_heckeBetaBar_of_modularPolynomialData (L) {ℓ} [NeZero ℓ]
  (data) (hsymm : EvalSymm data.Φ) (hℓ : ℓ.Prime) (N) [NeZero N] :
  FiniteAlong L (heckeBetaBar L N ℓ)`
- `ModularCurve.heckeAlphaBarIntegral_of_modularPolynomialData … :
  HeckeAlphaBarIntegral L N ℓ`
- `ModularCurve.heckeBetaBarIntegral_of_modularPolynomialData … :
  HeckeBetaBarIntegral L N ℓ`

**The prime forms (4).**
- `ModularCurve.finiteAlong_heckeAlphaBar_of_prime (L) (N ℓ) [NeZero N] [Fact ℓ.Prime]`
- `ModularCurve.finiteAlong_heckeBetaBar_of_prime (L) (N ℓ) [NeZero N] [Fact ℓ.Prime]`
- `ModularCurve.heckeAlphaBarIntegral_of_prime (L) (N ℓ) [NeZero N] [Fact ℓ.Prime]`
- `ModularCurve.heckeBetaBarIntegral_of_prime (L) (N ℓ) [NeZero N] [Fact ℓ.Prime]`

## 1. Routes

**`finiteAlong_heckeAlphaBar_of_modularPolynomialData` (74).** The pin's private
`dvd_mul_prime_cases`, `gens`, `gens_finite`, `jqNModC_mem_bar`, `isIntegral_gens`.
The route: `laurentBaseChange_modularFunctionFieldFull` (m7) writes the target
field as `adjoin L (gens L N)` with `gens L N = {jqNModC L d | d ∣ N}` (or its
image); `gens_finite`; each generator is integral over the source by
`isIntegral_jqNModC_mul` (m6) applied along `d ∣ N`, then `d * ℓ`; an integral
f.g. algebra extension is finite (`Algebra.Finite.of_fg` / `Module.Finite`).

**`finiteAlong_heckeBetaBar_of_modularPolynomialData` (116).** Adds
`qExpand_jqNModC` and `isIntegralElem_heckeBetaBar_gens`, using
`ModularPolynomialData.eval_jqNModC_of_mul_eq_zero` (m6, the `hsymm` form) to
produce the integrality certificate for the `q ↦ q^ℓ` image.

**`towerInclBar_*` (31/31/6).** `towerInclBar` is an `IntermediateField.inclusion`;
integrality/finiteness are mathlib's (`IntermediateField.isIntegral` /
`Module.Finite` of an inclusion). The pin's `towerInclBar_surjective_of_dvd_dvd`
uses the antisymmetry of `full_degeneracy_le`; `towerInclBar_finiteAlong` cites it
and AC's `finiteAlong_comp`/`finiteAlong_of_surjective`. Keep AC's along-API.

**The four `_of_prime` forms (3 each).** From the general forms with
`exists_modularPolynomialData_evalSymm` (m6) — or the weaker
`exists_phiIrreducible_evalSymm` when `hsymm` is needed.

**Seam.** `FiniteAlong`/`HeckeAlphaBarIntegral`/`HeckeBetaBarIntegral` are m1's
and AC's definitions; `IsIntegral` of the `hecke*Bar` maps is
`(hecke*Bar …).toRingHom.IsIntegral`. mathlib:
`RingTheory.IntegralClosure.IsIntegral.Basic`,
`FieldTheory.IntermediateField.Adjoin.Algebra`.

## 2. Verification

- Append the 13 wrappers to `SOURCES`; the module to `PORT_FILES`.
- checker 0 mismatched / 0 missing; `#print axioms` on the two 74/116 heads.
- Consumer Zone G `[inputs]`: `finiteAlong_heckeAlphaBar_of_prime` at `ℓ = 2`,
  `finiteAlong_heckeBetaBar_of_prime` at `ℓ = 2`, and
  `towerInclBar_isIntegral` for `1 ∣ 2`.

## 3. Budget

**2 goal rounds.** Round 1: the tower maps + the two general `FiniteAlong`
proofs. Round 2: the four `_of_prime` + the two `Integral` general forms +
log/README/consumer.

**Stop early on**: the `gens` integrality needing a `LaurentSeries` ring fact the
pin does not reach; the `_of_prime` derivation not matching the general form's
binders (quote, do not weaken).

## 4. Reporting back

1. Module/line/decl table and checker before/after.
2. The `FiniteAlong` route and the `gens` set's exact definition.
3. The `_of_prime` derivations.
4. Promotion candidates.
