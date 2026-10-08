# AUDIT — mathlib route for the `ds-head` differential / ramification tail

Scope: the four pin nodes of [WORKORDER-ds-head.md](WORKORDER-ds-head.md), pin
`anthropics/fermats-last-theorem@aa2d8b3`, port mathlib `v4.34.0`. Read against the
landed tree, i.e. the modules listed in
[ds-head-recon.md](ds-head-recon.md) §5. Nothing here runs Lean except the `#check`
probe recorded below; the substitution counts come from
`tools/deps/port_advise.py --targets build/readyHead_targets.txt`.

## 1. `#check` probe — the mathlib surface

`lean/ScratchDsHeadAudit.lean` (gitignored) imports
`Mathlib.RingTheory.Kaehler.{Basic,TensorProduct}`, `Mathlib.FieldTheory.Perfect`,
`Mathlib.LinearAlgebra.FiniteDimensional.Defs` and the specific modules the pin's
proof bodies name; run with
`lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false`. Outcomes:

| name | `v4.34.0` | pin use |
|---|---|---|
| `KaehlerDifferential.D` | `(R) (S) [CommRing R] [CommRing S] [Algebra R S] : Derivation R S Ω[S⁄R]` | `v.dCoord`, `differentialCoeff`, `exists_mem_D` |
| `KaehlerDifferential.map` | `Ω[A⁄R] →ₗ[A] Ω[B⁄S]`, needs `[IsScalarTower R A B] [IsScalarTower R S B] [SMulCommClass S A B]` | `kaehlerMap`, both headlines, `Ω`-generation |
| `KaehlerDifferential.map_D` | `map R S A B (D R A x) = D S B (algebraMap A B x)` | `kaehlerMap_dCoord`, the `s12` bridge |
| `KaehlerDifferential.map_surjective` | `Function.Surjective (map R S B B)` | route option for `IsCurveOver.exists_smul_eq` family (not needed) |
| `Derivation.leibniz` | `D (a*b) = a • D b + b • D a` | `differentialCoeff_D_mul` |
| `Derivation.leibniz_pow` | `D (a^n) = n • a^(n-1) • D a` | `differentialCoeff_D_uniformizer_pow` |
| `PerfectField` / `PerfectField.separable_of_irreducible` | as the pin | `s12` prelude, `ℙ¹` profile |
| `Module.finrank`, `Module.nontrivial_of_finrank_eq_succ` | as the pin | `nontrivial_kaehler_of_isCurveOver'`, `degree_canonicalDivisorOf_map` |
| `exists_smul_eq_of_finrank_eq_one` | `finrank K V = 1 → x ≠ 0 → ∀ y, ∃ c, c • x = y` | `IsCurveOver.exists_smul_eq` |
| `IsScalarTower`, `Algebra.IsSeparable` | as the pin | the Hurwitz formula's hypotheses |
| `finsum_eq_sum_of_support_subset` | `Function.support f ⊆ s → ∑ᶠ = ∑ i ∈ s` | `degree_canonicalDivisorOf_map`'s `hfin` |
| `Finsupp.notMem_support_iff` | `a ∉ f.support ↔ f a = 0` | `exists_finset_unramified_off` |
| `Submodule.mem_span_singleton` | `x ∈ R ∙ y ↔ ∃ a, a • y = x` | `s12` prelude |
| `Finset.sum_disjUnion`, `Finset.sum_eq_single_of_mem`, `Finset.sum_apply'` | present | `tameDifferentDivisor` bookkeeping |
| `WithZero.log_le_log` | `x ≠ 0 → y ≠ 0 → (x.log ≤ y.log ↔ x ≤ y)` | `ord_add_eq_min` (imported, not re-proved) |

**Verdict.** Every mathlib name the four nodes' proofs need is present at
`v4.34.0`; no proof body forced a mathlib substitute. The one naming correction:
the pin writes `(KaehlerDifferential.D K F).leibniz` / `.leibniz_pow` by dot
notation, i.e. they are **`Derivation.leibniz` / `Derivation.leibniz_pow`**, not
`KaehlerDifferential.leibniz*` (the naive `#check KaehlerDifferential.leibniz`
fails; grep of `Mathlib/RingTheory/Kaehler/Basic.lean` confirms `map`/`map_D`
live there and the Leibniz rules are `Derivation` fields).

## 2. Reuse wins (substitutions into the port)

`port_advise` on the eight pin files finds **349 declarations**, of which **173
already have a statement-identical declaration in the port (≈2,579 lines not to
re-prove)**. Of those, **160 are importable (public in the port)** and **13 are
port-`private`**. None of the 13 was needed by the three new modules:

```
ord_add_eq_left                              private in  P1/EnginePrelude.lean
uniformizer_ne_zero'_PFFRTP1DC               private in  P1/UnitNormalForm.lean
inv_mem_of_not_mem_centerIdeal               private in  Canonical/HasCanonicalDivisor.lean
div_mem_of_not_mem_centerIdeal               private in  Canonical/HasCanonicalDivisor.lean
inv_s12                                      private in  Canonical/HasCanonicalDivisor.lean
isSeparable_residueField_of_perfectField_of_finiteResidue  private in  Canonical/HasCanonicalDivisor.lean
toKSubalgebra / coe_toKSubalgebra            private in  Canonical/HasCanonicalDivisor.lean
isPrincipalIdealRing_adjoin_s12              private in  Canonical/HasCanonicalDivisor.lean
isDedekindDomain_adjoin_s12                  private in  Canonical/HasCanonicalDivisor.lean
isIntegrallyClosed_adjoin_s12                private in  Canonical/HasCanonicalDivisor.lean
isNoetherianRing_adjoin_s12                  private in  Canonical/HasCanonicalDivisor.lean
adjoin_singleton_s12                         private in  Canonical/HasCanonicalDivisor.lean
```

The reused homes are the landed Riemann–Roch layer:`AlgebraicCurve/P1/{UnitNormalForm,Dictionary,KaehlerIntegral,DivisorAction,PerfectField}.lean`,
`AlgebraicCurve/Canonical/{HasCanonicalDivisor,WeilDifferential}.lean`,
`AlgebraicCurve/Genus/Stichtenoth.lean`, `AlgebraicCurve/Defs/{LocalResidue,Place,
PlaceCalculus,PlacesOverDVR,PushPull}.lean`. The largest rows:
`ord_differentialCoeff_dX_ofHeightOneSpectrum` (103 ln),
`exists_sub_algebraMap_intDegree_neg` (83), `ord_placeInfty_X` (65),
`exists_unit_D_eq_smul_dCoord_s12` (56), `exists_smul_dX_eq` (55),
`dCoordGenerates_of_valSubringKaehlerSpanTop` (43),
`not_dvd_derivative_of_ord_eq_one` (42), `differentialCoeff_ne_zero` (36).

**Caveat confirmed (playbook §2.4).** The pre-port substitution test is
name-anchored, so it both **misses** renamed ports and **over-reports** spurious
last-name matches. On this cone it produced three false positives —
`CanonicalDivisorVariationPrincipal`, `TameLocalDifferentExponent` and
`LocalUnitDerivativeRegular` were each "matched" to `PeriodPair.DiscriminantNeZero`
(a generic `Prop`-valued `def`, 125 copies). All three are in fact **new**, and the
`--prop-bodies`-style reading of the pin body settles it. Likewise
`ValSubringKaehlerSpanTop`/`ValSubringKaehlerFinite`/"`OrdDifferentialWellDefined`"
matched unrelated `PeriodPair` `def`s. Every substitution used by the three
modules was re-checked against the pin statement by name, not by the tool's ratio.

**Verification (`grep -c`).** All 173 substitution rows resolve to a declaration
of that last name in the stated port home (8 rows need an exact-substring check
rather than `\b`, because the name carries an apostrophe:
`not_dvd_num'denom_sub_numdenom'`, `differentialCoeff_add''`,
`uniformizerSubring'`, `irreducible_uniformizerSubring'''`,
`uniformizer_ne_zero'`). The port-private 13 were grepped as declarations, not
uses.

## 3. Recorded negatives

Searches that found nothing, so nobody repeats them:

- **No mathlib Hurwitz / ramification formula for function fields.** Mathlib's
  `Ideal.sum_ramification_inertia` and the `RamificationInertia` API give the
  fundamental identity, which the port already has as
  `Place.sum_ramificationIndex_mul_inertiaDeg`; there is no degree formula
  `2g' − 2 = [F' : F](2g − 2) + deg 𝔡`.
- **No abstract-place ramification index.** Mathlib's ramification vocabulary is
  `Ideal`/`HeightOneSpectrum`-based (`Ideal.ramificationIdx`,
  `Ideal.inertiaDeg`); the pin's `Place.ramificationIndex` /
  `Place.inertiaDeg` are its own, and the port's are in
  `Defs/PushPull.lean` (`ramificationIndex := w.fiber …`-style definition).
- **No "`Ω[F⁄K]` is generated by `dπ` at a place"** statement, and no
  `DCoordGenerates` vocabulary. The pin's `Place.DCoordGenerates` class and
  `dCoordGenerates_of_valSubringKaehlerSpanTop` chain are the new mathematics
  here (already ported in `Canonical/HasCanonicalDivisor.lean`).
- **No canonical-different / `LocalHurwitzExponent` vocabulary.** No
  `CanonicalDifferentDegree`, `HurwitzCanonicalDecomposition`,
  `TameLocalDifferentExponent`, `LocalUnitDerivativeRegular` anywhere in mathlib
  or the port before this set.
- **No `KaehlerDifferential.leibniz` / `leibniz_pow`** under those names (they
  are `Derivation.leibniz` / `Derivation.leibniz_pow`).
- **No mathlib `canonicalDivisorOf_eq_of_forall`-shaped uniqueness lemma** for a
  `Place`-indexed canonical divisor; the pin's version is 1 line (`Finsupp.ext`).

## 4. The union — the pin pair is one file

`map_ne_zero_of_tame` and `two_mul_genus_sub_two_eq_of_degree_canonical` are the
**same pin file**: `SequenceMatcher` ratio **0.977**, the same 83 declarations at
the same line numbers. `port_advise` groups **80 names proved in ≥2 target files,
≈1,137 removable lines**; all 80 are the pair. The port writes the engine
**once** in `Differential/Hurwitz.lean` and keeps the two wrappers as its two
headlines. The dedup was verified by re-running `SequenceMatcher` on the two `S_`
files (`693/700` substantive lines identical) and by a declaration-line `grep -c`
over `FLTForHuman/`: of the pair's 80 once-only names, **70 are new and are
declared exactly once** in `Hurwitz.lean` (0 declared twice) and **10 are the
port-substituted calculus helpers** (`ord_add_eq_min'`, `ord_neg'`,
`ord_algebraMap'`, `ord_pow'`, `differentialCoeff_add'`,
`differentialCoeff_ne_zero'`, `ord_natCast'`, `ord_nonneg_of_mem`,
`mem_of_ord_nonneg`, `mem_iff_ord_nonneg`), imported under their port names rather
than re-declared.

## 5. Binder-spelling rows

`port_advise` §3 flagged 11 same-conclusion/different-binder names and 14
same-name/different-statement names. The port's three new modules resolve them by
**reading both statements**, taking the pin `Theorems/` wrapper as the statement
authority for the four headlines (playbook §4):

- the two headlines (`map_ne_zero_of_tame`,
  `two_mul_genus_sub_two_eq_of_degree_canonical`) are wrapper-spelled in
  `Hurwitz.lean`;
- `genus_ratFunc_eq_zero_of_perfectField` is wrapper-spelled in `RatFunc.lean`;
- `exists_mem_D_eq_smul_D_of_isCurveOver` is wrapper-spelled in `Generation.lean`;
- the `P1` place-infty rows (`ord_placeInfty_X`, `ord_placeInfty_X_pow`,
  `differentialCoeff_placeInfty_D_X_eq`, `ordDifferential_placeInfty_D_ratFuncX`,
  …) are `placeInfty K` in the pin genus file but `p1PlaceInfty K` in the port's
  `P1` cone; they are **not** re-declared (the port's copies already verify
  against the other pin `S_` file that spells `p1PlaceInfty`), and the one
  `P1`-flavoured name the new modules need, `ord_differentialCoeff_dX_ofHeightOneSpectrum`,
  is imported from `P1/UnitNormalForm.lean`.
- `canonicalDivisorOf_eq_of_forall` and `degree_canonicalDivisorOf_ratFunc_of_perfectField_s17`
  are pin-public and are landed at their pin statements.

## 6. Regenerate

```bash
cd tools/deps
python3 port_advise.py --targets build/readyHead_targets.txt --json build/readyHead_advise.json
cd ../../lean
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchDsHeadAudit.lean
```
