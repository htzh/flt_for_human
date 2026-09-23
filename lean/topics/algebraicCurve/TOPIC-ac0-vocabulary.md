# AC0 — the `AlgebraicCurve` vocabulary

**Status (2026-09-22): work order written, not started.** First topic of SET 1; see
[SET-1.md](SET-1.md) for the run brief, the shared build discipline and the shared
definition of done. Read that file first — in particular §2 (build discipline: this
lakefile raises `maxHeartbeats` to 4,000,000, so every build must be wrapped in
`timeout`), §3 (layout and conventions) and §5 (the checker's `norm` must be
extended to strip `AlgebraicCurve.`).

**Audience.** A fresh session opening the third Lean port
([PORTING-AC.md](../../PORTING-AC.md)). Read
[porting-playbook.md](../../porting-playbook.md) §3–§5, §7 and §8 once, then
[PORTING-AC.md](../../PORTING-AC.md) §0–§4 and §6. The pin is
`anthropics/fermats-last-theorem@aa2d8b3`, locally at `~/proj/fermats-last-theorem`.

**Goal.** Write the generic curve vocabulary the whole cone is stated over —
`Place`, `Divisor`, `Pic0`, the ramification/push-pull API, the fibre-centre
dictionary's objects, the along-map API, `SemilinearAut`, and the `P¹` vocabulary
— as `FLTForHuman/AlgebraicCurve/Defs/*.lean`, mathlib-only, in namespace
`AlgebraicCurve`, with statements transcribed from the pin's `Definitions/` files.
Then stand up `spec/AlgebraicCurveConsumer.lean` Zone A and extend
`spec/check_flt_statements.py`.

This is a definitions layer: the FFG Layer-0 treatment applies (transcribe
bottom-up, build after every module, promote nothing prematurely). The measured
risk is low — it is `structure`/`def`/`abbrev` work over mathlib's valuation API,
and the pin's own proofs for the `ord` lemmas are short — but it is also where the
`Place` ↔ `ValuationSubring` ↔ `HeightOneSpectrum` bridge is decided **once**, and
that decision fixes every downstream topic.

## 1. The scouted inventory

Eight port modules. The "keep" set below is the pin declarations the 65-node
corpus references (statement *or* proof body) plus the definitions those
declarations need; the "drop" set is measured, not assumed. **The drops are the
point of the topic**: `PORTING-AC.md` §4.3 budgets ≈1,270 definition-module lines
never written (≈45%).

| port module | pin source | pin lines | ≈ port |
|---|---|---|---|
| `Defs/Place.lean` | `Def_AlgebraicCurve_DivisorClassGroup` 22–179, 456–485 | ~150 | 220–260 |
| `Defs/Divisor.lean` | `Def_AlgebraicCurve_DivisorClassGroup` 179–247 | 68 | 90–110 |
| `Defs/PushPull.lean` | `Def_AlgebraicCurve_DivisorPushPull` (whole, minus drops) | 735 | 600–720 |
| `Defs/PlacesOverDVR.lean` | `Def_AlgebraicCurve_PlacesOverDVR` (whole, minus drops) | 506 | 430–500 |
| `Defs/Correspondence.lean` | `Def_AlgebraicCurve_Correspondence` (whole, minus drops) | 346 | 300–340 |
| `Defs/SemilinearAut.lean` | `Def_AlgebraicCurve_BaseChangeGalois` 15–206 | 192 | 160–190 |
| `Defs/RatFuncPlaces.lean` | `Def_AlgebraicCurve_RatFuncPlaces` 18–236 + `Def_AlgebraicCurve_RatFuncPlaceInfty` 16–44 | 263 | 220–260 |
| `spec/AlgebraicCurveConsumer.lean` (Zone A) | — | — | 80–120 |

The two declarations outside these files that the cone needs, both handled here:

- **`Place.ord_algebraMap`** — stated at `Def_AlgebraicCurve_ConstantReduction.lean:57`
  (line 57–66; the proof needs only `P.ord_coe_unit`), in a heavy unrelated module.
  It is a **T1** node; T1 writes it directly in `Defs/Place.lean` (there is no
  wrapper that says where it lives; `PORTING-AC.md` §8 risk 7 says this explicitly).
  AC0 leaves the file ready for it and does not import ConstantReduction.
- **`RationalFunctionField.placeInfty`** — `Def_AlgebraicCurve_RatFuncPlaceInfty.lean:25`,
  with `nontrivial_valueGroup_inftyValuation` at line 16. **`PORTING-AC.md` §2.2's
  six-module table omits this file**; AC0 adds it to the port (and the port's
  `SOURCES`, so it is diffed) and the reviewer will record the omission in the
  blueprint. Its whole content is 44 lines and is quoted in §3.5 below.

## 2. The keep/drop inventory, per module

Reference counts are the pin's declaration names' occurrences in the 65-node corpus
(the 63 AC + 2 generic `S_` files plus their `Theorems/` wrappers; recipe in
[PORTING-AC.md](../../PORTING-AC.md) §9.1). A name marked **keep** has ≥1 corpus
hit or is needed by a kept declaration's *body*; **drop** has 0 corpus hits and no
kept-body use. **Count before dropping**: for every name you drop, record
`grep -c` in the corpus in the log (§6 of [SET-1.md](SET-1.md)), and for the
big blocks in §2.8 quote the whole-block count.

### 2.1 `Defs/Place.lean` — `Def_AlgebraicCurve_DivisorClassGroup` 22–179, 456–485

Keep, in dependency order:

- `ValuationSubring.not_isField_of_ne_top`, `Place`, `Place.toValuationSubring_injective`,
  `Place.ext` (the `@[ext]` used by every `restrict`/`semilinear` equality),
  `Place.coe_algebraMap`, and the four instances the structure's fields carry:
  `IsPrincipalIdealRing v.toValuationSubring`, `IsDiscreteValuationRing
  v.toValuationSubring`, `Algebra K v.toValuationSubring`, `IsScalarTower K
  v.toValuationSubring F`.
- `Place.ResidueField`, `Place.deg`, `Place.FiniteResidue`,
  `Place.heightOneSpectrum`, `Place.heightOneSpectrum_asIdeal`,
  `Place.adicValuation`, `Place.adicValuation_ne_zero`, `Place.adicValuation_coe`,
  `Place.adicValuation_coe_eq_one_iff`, `Place.adicValuation_coe_irreducible`.
- `Place.ord` and its leaves: `ord_zero`, `ord_one`, `ord_mul`, `ord_inv`,
  `ord_coe_unit`, `ord_coe_irreducible`, `ord_zpow`, `ord_unit_smul_zpow`,
  `exists_unit_mul_zpow`.
- `Place.isPrincipalIdealRing_valuationSubring`, `Place.ofHeightOneSpectrum`,
  `Place.ofHeightOneSpectrum_toValuationSubring` (lines 456–485).

The `Place` structure is the one decision this topic cannot revisit (§4.1). Its
fields, verbatim:

```lean
structure Place where
  toValuationSubring : ValuationSubring F
  algebraMap_mem' : ∀ a : K, algebraMap K F a ∈ toValuationSubring
  ne_top' : toValuationSubring ≠ ⊤
  isPrincipalIdealRing' : IsPrincipalIdealRing toValuationSubring
```

### 2.2 `Defs/Divisor.lean` — `Def_AlgebraicCurve_DivisorClassGroup` 179–247

Keep: `Divisor` (`:= Place K F →₀ ℤ`), `Divisor.degree` (the `Finsupp.liftAddHom`
of `AddMonoidHom.mulRight (v.deg : ℤ)`), `Divisor.degree_single`, `Divisor.degZero`
(`= degree.ker`), `Divisor.mem_degZero`, `Divisor.IsPrincipal`, `Divisor.principal`
(the `AddSubgroup`), `Divisor.mem_principal`, `HasPrincipalDivisors` (the `class`),
`Pic0`, `Pic0.mk`, `Pic0.mk_surjective`, `Pic0.mk_add`, `Pic0.mk_zero`.

**Drop** (blueprint §6): `Pic`, `torsion`, `mem_torsion`, `AbelJacobiCard`. The
exchange cone needs only `Pic0.mk`/`mk_surjective` from the `Pic`/`Pic0` block,
and `Pic` itself is reached by nothing in the cone. Record the counts.

### 2.3 `Defs/PushPull.lean` — `Def_AlgebraicCurve_DivisorPushPull`

This is the largest keep set and the one this topic should expect to spend its time
on. Port it in the pin's own section order; the modules it needs from `Defs/` are
`Divisor` and `Place`.

Keep (by pin span):

- **22–161**, the ord/comap interface and ramification:
  `Place.ord_nonneg_of_mem`, `Place.mem_of_ord_nonneg`, `Place.mem_iff_ord_nonneg`,
  `Place.exists_ord_pos`, `Place.algebraMap_ne_zero`, `Place.comap_algebraMap_ne_top`,
  `Place.mem_comap_iff_ord_nonneg`, `Place.isUnit_mk_comap_iff`,
  `Place.exists_ord_algebraMap_pos`, `Place.ramificationIndex`,
  `Place.ramificationIndex_le_ord`, `Place.ramificationIndex_set_nonempty`,
  `Place.ramificationIndex_pos`, `Place.exists_ord_eq_ramificationIndex`,
  `Place.ramificationIndex_dvd_ord`, `Place.irreducible_mk_comap`,
  `Place.isPrincipalIdealRing_comap`, `Place.restrict`,
  `Place.restrict_toValuationSubring`, `Place.mem_restrict_iff`, `Place.ord_restrict`,
  `Place.ord_algebraMap_ne_zero_of_restrict_eq`, `Place.restrict_fiber_finite`.
- **370–438**, the residue-field map and inertia degree:
  `Place.restrictInclusion`, `Place.coe_restrictInclusion`,
  `Place.instIsLocalHomRestrictInclusion`, `Place.restrictResidueMap`,
  `Place.restrictResidueMap_residue`,
  `Place.instAlgebraResidueFieldRestrictPushforward`,
  `Place.algebraMap_residueField_eq`,
  `Place.instIsScalarTowerResidueFieldRestrictPushforward`, `Place.inertiaDeg`,
  `Place.deg_restrict_mul_inertiaDeg`.
- **448–521**, pushforward: `Divisor.pushforward`, `Divisor.pushforward_single`,
  `Divisor.degree_pushforward`, `Divisor.pushforward_mem_degZero`,
  `Divisor.pushforward_apply`, `Divisor.PushforwardNormFormula`.
- **518–611**, fiber and pullback: `Place.fiber`, `Place.mem_fiber`,
  `Place.restrict_mem_fiber`, `Divisor.pullbackSingleHom`,
  `Divisor.pullbackSingleHom_apply`, `Divisor.pullback`, `Divisor.pullback_single`,
  `Divisor.pullback_single_apply_of_restrict_eq`,
  `Divisor.pullback_single_apply_of_restrict_ne`, `Divisor.pullback_apply`,
  `Divisor.restrict_mem_support_of_mem_support_pullback`,
  `Divisor.pullback_apply_eq_ord`, `Divisor.isPrincipal_pullback`,
  `Divisor.pullback_mem_principal`.
- **611–736**, the identities and the `Pic0` homs: `Divisor.FundamentalIdentity`,
  `Divisor.degree_pullback_single`, `Divisor.degree_pullback`,
  `Divisor.pullback_mem_degZero`, `SumRamificationInertia`,
  `instFundamentalIdentityOfSumRamificationInertia`, `Pic0.pullbackDegZeroHom`,
  `Pic0.coe_pullbackDegZeroHom`, `Pic0.pullbackHom`, `Pic0.pullbackHom_mk`,
  `Pic0.pushforwardDegZeroHom`, `Pic0.coe_pushforwardDegZeroHom`,
  `Pic0.pushforwardHom`, `Pic0.pushforwardHom_mk`. Also keep
  `Divisor.pushforward_eq_of_normFormula` and
  `Divisor.isPrincipal_pushforward_of_normFormula` (494–518): they are what the
  along-layer's principal-divisor lemmas call.

**Drop candidates** (0 corpus hits, no kept body): `Place.ramificationIndex_set_nonempty`
is a `private` helper — keep it `private`; `Place.mapRestrict`,
`Divisor.mapRestrict`, `Divisor.mapRestrict_single` (the along-layer never uses the
restriction push of a divisor). Check each other block with `grep -c` before
dropping.

### 2.4 `Defs/PlacesOverDVR.lean` — `Def_AlgebraicCurve_PlacesOverDVR`

Keep:

- `Place.center`, `Place.mem_center_iff_ord_pos`, `Place.center_ne_bot`,
  `Place.centerHeightOneSpectrum`, `Place.centerHeightOneSpectrum_asIdeal`,
  `Place.valuationSubringAtPrime_centerHeightOneSpectrum_le`,
  `Place.toValuationSubring_eq_of_forall_mem`, `Place.valuationSubringAlgebra`
  (**`@[reducible]` — keep the attribute**), `Place.integralClosureAt`
  (**`abbrev` — keep it an `abbrev`**), and the three instances
  `IsDedekindDomain (integralClosureAt F' v)`, `IsFractionRing (integralClosureAt
  F' v) F'`, `Module.Finite v.toValuationSubring (integralClosureAt F' v)`.
- `Place.algebraMap_integralClosureAt_injective`, `Place.maximalIdeal_ne_bot`,
  `Place.forall_mem_of_restrict_eq`, `Place.fiberCenter`,
  `Place.mem_fiberCenter_iff_ord_pos`, `Place.toValuationSubring_eq_of_restrict_eq`,
  `Place.mem_maximalIdeal_iff_ord_pos'`,
  `Place.algebraMap_integralClosureAt_ne_zero`,
  `Place.ord_algebraMap_integralClosureAt`, `Place.fiberCenter_liesOver`,
  `Place.placeOfPrime`, `Place.placeOfPrime_toValuationSubring`,
  `Place.restrict_placeOfPrime`, `Place.fiberCenter_placeOfPrime`,
  `Place.eq_of_fiberCenter_eq`, `Place.fiberEquiv`, `Place.fiberEquiv_apply`,
  `Place.fiberEquiv_symm_apply`, `Place.finite_setOf_restrict_eq`,
  `Place.fiberOver`, `Place.mem_fiberOver`, `Place.restrict_mem_fiberOver`,
  `Place.restrict_eq_of_mem_fiberOver`,
  `Place.subset_fiberOver_of_forall_restrict_eq`.
- The ord/valuation leaves the fibre argument re-proves privately elsewhere:
  `Place.ord_nonneg_of_mem`, `Place.ord_eq_zero_iff_adicValuation_eq_one`,
  `Place.ord_neg`, `Place.mem_of_eval_monic_eq_zero`,
  `Place.mem_maximalIdeal_iff_ord_pos`. (Some of these are duplicates of
  `Defs/PushPull.lean`/`Defs/Place.lean` declarations at *different* section
  variables; keep the pin's shape and let the checker diff them.)

**Drop** (measured, `PORTING-AC.md` §6): the chart block `chartHom`,
`coe_chartHom`, `mem_center_iff`, `inv_algebraMap_mem`,
`finite_setOf_forall_mem_and_ord_pos` (this last one is real public API for the
Riemann–Roch layer but is not in the cone); `Place.fiberEquiv`'s consumers
`card_fiberOver_eq` and `Place.fiber_eq_fiberOver` are **not** among the 65 nodes —
keep them only if a kept T2/T5 declaration's body needs them, and record the count
either way. `PORTING-AC.md` §6.1 says deferring real API is recorded, not judged
worthless: list the dropped names in the log.

### 2.5 `Defs/Correspondence.lean` — `Def_AlgebraicCurve_Correspondence`

Keep all of: `algebraAlong` (**an `abbrev`, `φ.toRingHom.toAlgebra`** — §3.3),
`isScalarTower_along`, `isIntegral_along`, `FundamentalIdentityAlong`,
`FiniteAlong`, `NormFormulaAlong`, `finrankAlong`, `Divisor.pullbackAlong`,
`Divisor.isPrincipal_pullbackAlong`, `Divisor.degree_pullbackAlong`,
`Divisor.pullbackAlong_mem_degZero`, `Divisor.pushforwardAlong`,
`Divisor.degree_pushforwardAlong`, `Divisor.pushforwardAlong_mem_degZero`,
`Divisor.isPrincipal_pushforwardAlong`, `Divisor.correspondence`,
`Divisor.correspondence_apply`, `Divisor.degree_correspondence`,
`Divisor.correspondence_mem_degZero`, `Divisor.correspondence_mem_principal`,
`Divisor.degZeroCorrespondence`, `Divisor.coe_degZeroCorrespondence`,
`Pic0.correspondence`, `Pic0.correspondence_mk`, `Place.restrictAlong`,
`Place.ramificationIndexAlong`, `Place.inertiaDegAlong`, `Place.ord_restrictAlong`,
`Divisor.pullbackAlong_apply`, `Divisor.pushforwardAlong_single`,
`restrictAlong_congr`, `fiberAlong`, `mem_fiberAlong`,
`Divisor.pullbackAlong_single`, `SeparableAlong`, `IntertwinesAlong`,
`IntertwinesAlong.inv`, `IntertwinesAlong.one`, `IntertwinesAlong.mul`.

Every one of these definitions opens with the same three-line wall

```lean
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
```

Transcribe those literally and in that order; they are what makes the
`Divisor.pullback`/`pushforward` API applicable, and T4's `rfl` bridges depend on
`algebraAlong` staying an `abbrev`.

### 2.6 `Defs/SemilinearAut.lean` — `Def_AlgebraicCurve_BaseChangeGalois` 15–206

Keep: `SemilinearAut` (a `Subgroup (RingAut F × RingAut K)`), `SemilinearAut.mem_iff`,
`toRingAut`, `baseAut`, `commutes`, `toRingAut_one`, `baseAut_one`, `toRingAut_mul`,
`baseAut_mul`, `toRingAut_inv`, `baseAut_inv`, `smul_def`, `inv_smul_def`,
`smul_algebraMap`, `ofAlgAut`, `toRingAut_ofAlgAut`, `baseAut_ofAlgAut`,
`ofAlgAut_smul`, `pointwise_smul_top`, `smulValuationSubringEquiv`,
`coe_smulValuationSubringEquiv_apply`, `smul_toValuationSubring`, `ord_smul`,
`smulResidueRingEquiv`, `smulResidueRingEquiv_algebraMap`, `deg_smul`.

**Drop** the whole Divisor/`Pic0` action-and-torsion section, lines 206–356
(`divisor_smul_def`, `smul_single`, `divisor_smul_apply_smul`, `divisor_smul_apply`,
`degree_smul`, `smul_mem_degZero`, `smul_mem_principal`, `degZeroSMulHom`,
`coe_degZeroSMulHom`, `pic0_smul_mk`, `smul_zsmul`, `smul_mem_torsion`,
`instSMulTorsion`, `coe_torsion_smul`, `instDistribMulActionTorsion`,
`instModuleZModTorsion`, `instSMulCommClassZModTorsion`, `torsionRep`,
`torsionRep_apply`). `PORTING-AC.md` §6 measures this as API for the modular
Hecke/Galois-rep layer, deferred, not worthless. Likewise drop the **other** Galois
action, `Def_AlgebraicCurve_DivisorClassGroup` 262–456 (the `F ≃ₐ[K] F` action on
`Place`/`Divisor`/`Pic0`): a different action from `SemilinearAut K F`, and
`PORTING-AC.md` §6 says the exchange cone needs none of it.

### 2.7 `Defs/RatFuncPlaces.lean` — `Def_AlgebraicCurve_RatFuncPlaces` 18–236 + `RatFuncPlaceInfty`

Keep from `RatFuncPlaces`: `Place.adicValuation_valuationSubring`,
`Place.mem_iff_adicValuation_le_one`,
`Place.isEquiv_adicValuation_of_valuationSubring_eq`,
`Place.mem_maximalIdeal_iff_adicValuation_lt_one`,
`Place.ord_eq_zero_iff_adicValuation_eq_one`,
`Place.isEquiv_adicValuation_ofHeightOneSpectrum`,
`Place.ofHeightOneSpectrum_injective`, `Place.ord_ofHeightOneSpectrum_ne_zero_iff`,
`RationalFunctionField.heightOneSpectrumOfIrreducible`,
`RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal`,
`RationalFunctionField.exists_irreducible_span`,
`RationalFunctionField.finitePlace`, `RationalFunctionField.finitePlace_def`,
`RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum`,
`RationalFunctionField.residueOfHeightOneSpectrum`,
`RationalFunctionField.residueOfHeightOneSpectrum_apply`,
`RationalFunctionField.ker_residueOfHeightOneSpectrum`,
`RationalFunctionField.surjective_residueOfHeightOneSpectrum`,
`RationalFunctionField.residueFieldEquivOfHeightOneSpectrum`,
`RationalFunctionField.deg_ofHeightOneSpectrum`,
`RationalFunctionField.deg_finitePlace`.

**Drop, measured** (`PORTING-AC.md` §3.5): `placeOfPoint` (236–274) and the entire
`Place.Congr` section (274–398: `comapSymmRingEquiv`, `coe_comapSymmRingEquiv_apply`,
`symm_algebraMap_comm`, `congrRingEquiv`, `congrRingEquiv_toValuationSubring`,
`ord_congrRingEquiv`, `congrResidueAlgEquiv`, `deg_congrRingEquiv`, `congrEquiv`,
`congrEquiv_apply`, `congrEquiv_symm_apply`). They occur in the cone only inside
the pin's `attribute [-simp]` walls, which the port does not transcribe — a
non-attribute grep confirms it. Also drop `deg_finitePlace` only if T8 does not
need it; the blueprint §10 says `finitePlace`/`deg_finitePlace` are re-defined
locally by T8's degree file, so prefer **keeping one copy** in `Defs/` and having
T8 use it.

Keep from `RatFuncPlaceInfty` (the file the six-module table omits) — 44 lines,
quoted in full in §3.5 below.

### 2.8 The big-block drops, with the counts to record

| drop | pin | why |
|---|---|---|
| `DivisorClassGroup` 262–456 (Galois `≃ₐ` action) | ~195 | other consumers only |
| `DivisorClassGroup` `Pic`/`torsion`/`AbelJacobiCard` | ~35 | not in cone |
| `BaseChangeGalois` 206–356 (Divisor/Pic0 action, torsion) | ~150 | other consumers only |
| `RatFuncPlaces` 236–398 (`placeOfPoint`, `Place.Congr`) | ~162 | unused (attribute noise only) |
| `PlacesOverDVR` chart block | ~60 | not in cone |

## 3. Route notes, so none of this has to be rediscovered

### 3.1 The bridge is decided once, and it is FLT's shape

`Place` **is** a `ValuationSubring F` with three side conditions. Do not replace it
with a bare `HeightOneSpectrum` or a `FractionalIdeal`: `PORTING-AC.md` §8 risk 2 is
explicit that a switch would redo the whole `Place` API and that keeping the FLT
shape (and `HasPrincipalDivisors`) is the lower-risk fork. The bridge to mathlib is
built *inside* the structure:

- `Place.heightOneSpectrum : HeightOneSpectrum v.toValuationSubring :=
  IsDiscreteValuationRing.maximalIdeal _`;
- `Place.adicValuation : Valuation F ℤᵐ⁰ := v.heightOneSpectrum.valuation F`;
- `Place.ord f := -(WithZero.log (v.adicValuation f))`;
- `Place.isPrincipalIdealRing'` is the field `placeOfPrime` needs
  (`isPrincipalIdealRing_valuationSubring` supplies it for `ofHeightOneSpectrum`).

The classification proofs cross between `v.toValuationSubring` and
`(v.adicValuation).valuationSubring` via `Place.ext` and
`Valuation.isEquiv_iff_valuationSubring`. Expect `exp`/`log` `rfl`/`simp`
identifications to be the friction (T1's named risk); `WithZero.log_exp` and
friends are the lemmas.

### 3.2 mathlib's generic API will not fire under `rw` (playbook §3.5)

`Place.restrict` is `toValuationSubring.comap`: the lemmas about it are
`ValuationSubring.mem_comap`, `ValuationSubring.comap_comap`, and instance
lemmas whose implicit arguments are unresolved in a `rw` pattern. When a `rw` or
`simp only` reports no progress on a goal whose pattern is visibly there, write the
monomorphic helper (proved by `exact`) and rewrite through it. This is the single
most likely repeated obstacle in `PushPull`/`PlacesOverDVR`.

### 3.3 `abbrev`s are the load-bearing part of the along-layer

`algebraAlong φ := φ.toRingHom.toAlgebra`, `Place.integralClosureAt`,
`Divisor`, `Place.fiber`, `Pic0` are `abbrev`s; `Place.valuationSubringAlgebra` and
T6's later `algebraEnv` are `@[reducible] def`s. **Keep the attributes.** T4's
`eA`/`fB`/`fF`/`eF` bridges are `rfl` statements that only hold while
`algebraAlong` unfolds definitionally, and `PlacesOverDVR`'s `IsFractionRing`
instance only fires while `integralClosureAt`/`valuationSubringAlgebra` unfold.
`rw` does not unfold `abbrev` (playbook §3.7): use `change` or `simp only [name]`.

### 3.4 Deprecated `Ideal` aliases (risk 4)

The pin's `Place.ord_restrict` and friends use `Ideal.ramificationIdx_spec` and
`Ideal.sum_ramification_inertia`; the `PlacesOverDVR` block uses
`Ideal.inertiaDeg_algebraMap`/`Ideal.inertiaDeg'_pos`. These are deprecated in
v4.33/v4.34. Write the port against `Ideal.ramificationIdx'`, `Ideal.inertiaDeg'`
and `Ideal.sum_ramification_inertia_eq_finrank` from the first declaration, or the
library carries warnings now and breaks at the next pin. **0 warnings is in the
definition of done.**

### 3.5 `RatFuncPlaceInfty`, quoted (it is 44 lines, all kept)

```lean
theorem nontrivial_valueGroup_inftyValuation :
    Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass (RatFunc.inftyValuation K))) := by
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  refine ⟨Units.mk0 (RatFunc.inftyValuation K RatFunc.X)
    (by rw [RatFunc.inftyValuation.X]; exact exp_ne_zero), ?_, ?_⟩
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · rw [ne_eq, Units.ext_iff, Units.val_mk0, Units.val_one, RatFunc.inftyValuation.X]
    simp

def placeInfty : Place K (RatFunc K) :=
  haveI := nontrivial_valueGroup_inftyValuation K
  { toValuationSubring := (RatFunc.inftyValuation K).valuationSubring
    algebraMap_mem' := fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one (v := RatFunc.inftyValuation K) a
    ne_top' := by
      simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
      infer_instance
    isPrincipalIdealRing' :=
      (Valuation.valuationSubring_isDiscreteValuationRing
        (RatFunc.inftyValuation K)).toIsPrincipalIdealRing }

@[simp]
theorem placeInfty_toValuationSubring :
    (placeInfty K).toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := rfl
```

`PORTING-AC.md` §3.4 says `RatFunc.inftyValuation` is mathlib's and that
`toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum` should be stated against
it, not against a port-local copy. `placeInfty` takes
`[DecidableEq (RatFunc K)]` in the pin — keep the instance (T8's `DecidableEq`
risk).

### 3.6 `FiniteResidue`

`def deg : ℕ := Module.finrank K v.ResidueField` needs no instance. The pin's
`class FiniteResidue : Prop where finite : Module.Finite K v.ResidueField` is 3
lines and is not in the 65 statements; keep it unless the build proves it dead (T8's
`deg_ofHeightOneSpectrum` may want it), and record the call.

## 4. What is different about this topic

- **It is the port's first *generic curve* vocabulary.** Everything so far in
  `FLTForHuman/` is `Elliptic`, `ModularCurve` or generic field theory. This layer
  mentions no modular object at all; a reader should be able to read
  `AlgebraicCurve/Defs/` linearly.
- **There is no `Theorems/` wrapper for most of it.** The checker must diff
  definition modules against `Definitions/Def_AlgebraicCurve_*.lean`. Because the
  checker matches by last name component, ordering matters: put the AC wrappers
  and definition files **after** all existing `ModularCurve` sources so no existing
  match can flip, and among the AC files put a specific wrapper before a
  definition file only when they genuinely collide (log every ordering decision
  that changes a match).
- **The consumer comes before the proofs.** Zone A is `#check`-level: it fixes
  the `Place`/`Divisor`/`Pic0` signatures the rest of the effort builds against,
  and it is the FFG `Universal.lean` lesson — a module can build green and sit in
  no import chain. Zone A must therefore import the modules (not restate them) and
  `#check` the pinned signatures.
- **Shape risk is concentrated in the bridge, not the volume.** The 1,900–2,200
  budgeted lines are transcriptions; what can stall the topic is the choice of
  `Place` shape, the four instances on `v.toValuationSubring`, and the deprecated
  `Ideal` aliases. Budget one goal round for the vocabulary and be suspicious if
  it takes three.

## 5. Budget and stop-early

**2 goal rounds, checkpoint at 1.** The FFG Layer-0 precedent is 137 declarations
in one round; this is fewer, larger declarations over a harder instance API. Two is
the "something structural is wrong" threshold.

**Stop early, and report rather than restate, on**: a `Place`/`Divisor` signature
that will not match its pin definition file (quote the divergence); an instance
that will not fire without changing a structure's fields; or a deprecated `Ideal`
alias whose replacement changes a statement.

## 6. Definition of done

- [ ] `FLTForHuman/AlgebraicCurve/Defs/{Place,Divisor,PushPull,PlacesOverDVR,Correspondence,SemilinearAut,RatFuncPlaces}.lean`
      exist, mathlib-only, namespace `AlgebraicCurve`, statements transcribed from
      the pin's `Definitions/` files with the pin's binders.
- [ ] The §2 keep sets ported; the §2.8 drops not written, each with a `grep -c`
      count in the log. `Place.ord_algebraMap` **not** ported here (T1's, but it
      lands in `Defs/Place.lean`).
- [ ] `spec/AlgebraicCurveConsumer.lean` exists with **Zone A** at 0 errors, and
      its `#check`s are live imports, not restatements.
- [ ] `spec/check_flt_statements.py`: `norm` strips `AlgebraicCurve.`; the AC
      definition files appended to `SOURCES`; `OWN_PROOFS` additions justified;
      final line `N identical, 0 mismatched, 0 missing`.
- [ ] `timeout 300 lake build` green, **0 warnings**, no `sorry` in
      `FLTForHuman/`.
- [ ] `logs/ac-port.md` with the §0 table and the AC0 section (`module | lines |
      decls | FLT source`), plus the drop list and the friction log.
- [ ] `README.md` gains the `AlgebraicCurve/` area in its module table;
      `PORTING-AC.md` status line not touched (report instead).

## 7. Reporting back

Beyond the shared report (§6 of [SET-1.md](SET-1.md)), three things:

1. **The drop list**, per module, with counts — the single most useful number this
   topic produces, because it calibrates `PORTING-AC.md` §4.3's ≈1,270-line
   estimate.
2. **Which of the four `Place` instances needed help.** `IsPrincipalIdealRing`,
   `IsDiscreteValuationRing`, `Algebra K v.toValuationSubring`, `IsScalarTower`:
   if any needed a `haveI`/`letI` or a restatement, say which — that is the bridge
   decision SET 2 will inherit.
3. **The checker's AC ordering.** Which files in which order, and which
   last-name collisions actually bit (`restrict`, `mk`, `deg`, `degree`, `ord`,
   `ext` are the predicted ones).
