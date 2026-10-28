# WORKORDER LEAVESDEF — the leaves' definition layer, six orders

**Set**: [SET-LEAVESDEF.md](SET-LEAVESDEF.md) — read §0 (the measured inventory) and §1 (the traps)
first. Pin = `~/proj/fermats-last-theorem` @ `aa2d8b3`; port root `lean/`, package
`flt_for_human` (Lean v4.33.1 / mathlib v4.34.0).

House rules, all six orders: statements **verbatim** (names, binders, namespaces); proofs adapted
only where mathlib v4.34 moves an API, each deviation reported; no `sorry`/`admit`/`axiom`/
`native_decide`, no `set_option maxHeartbeats`/`synthInstance.maxHeartbeats`, no linter suppression;
zero warnings; no `spec/decl_markers.tsv` row; no other Lean file; no git; no whole-tree build; every
shell command under 2 minutes; a `lake build` under `flock` may be killed while queueing (FR-0060) —
use the background channel or a longer timeout. Report to the manager: declarations added (with pin
line ranges), the `check_port` counts line, the build result/time, axioms, deviations.

---

## LD1 — `CohCarrier.HeckeData` and the `Inst`'s `MLAt`

**Files**: **new** `lean/FLTForHuman/ModularForms/CohCarrier/HeckeData.lean` (pin
`Definitions/Def_CohCarrier_HeckeData.lean`, 92 lines whole); then **insert** `hdata` and `MLAt`
(pin `Def_CohCarrier_Inst.lean:96–109`) into `lean/FLTForHuman/ModularForms/CohCarrier/Inst.lean`.

Transcribe the 17 declarations (`HeckeData`, `FreeAlg`, `thetaTilde`, `mTheta`, `mTheta_isPrime`,
`opSubalgebra`, `op_comm_of_mem`, `opSubalgebra_isMulCommutative`, `opAlgHom`, `opAlgHom_X`,
`moduleFreeAlg`, `ML`, `toML`, `algebraMap_freeAlg_smul`, `V_isScalarTower`, `toMLₒ`,
`toMLₒ_apply`) with their universes `u v w` and the `attribute [local instance] moduleFreeAlg`.
The pin's `example` probes are not declarations: keep them as `example`s only if they elaborate and
cost nothing (they are `inferInstance` checks).
Then in `Inst.lean`, after `opFamily`, add `hdata` (the `HeckeData 𝒪 (H1 M H 𝒪) k` built from
`opFamily` and a commuting hypothesis) and `MLAt` (the `abbrev` of `(hdata …).ML`), plus the pin's
trailing `example` if it adds a real probe. Wires: `HeckeData.lean` gets
`spec-pin: Definitions/Def_CohCarrier_HeckeData.lean`; `Inst.lean` keeps its own wire (it already
names `Def_CohCarrier_Inst.lean`) — add nothing.

## LD2 — the Petersson inner product

**File**: **new** `lean/FLTForHuman/ModularForms/EichlerShimura/Petersson.lean`, transcribing
`Definitions/Def_CuspForm_Petersson.lean` (3 declarations: `CuspForm.peterssonIntegrand`,
`CuspForm.petersson`, `CuspForm.petersson_def`) **and** the `CuspForm` section of
`Definitions/Def_ModularCurve_PeriodOf.lean` (5 declarations: `peterssonIntegrandOf`, `peterssonOf`,
`peterssonOf_def`, `peterssonIntegrandOf_gamma0`, `peterssonOf_gamma0`).

`namespace CuspForm`, `variable (Γ : Subgroup SL(2, ℤ)) {k : ℤ}` for the `…Of` group and
`{N : ℕ} {k : ℤ}` for the `Γ₀(N)` ones, exactly as the pin splits them. The `_gamma0` lemmas are
`rfl` and are the ones the leaves consume. Two `spec-pin:` lines (the two pin modules). The port's
`ModularForms/EichlerShimura/PeriodOf.lean` header records the deferral — mention the new home there
only if you touch that file (you should not: this module imports it).

## LD3 — `PeriodHomPair`

**File**: **new** `lean/FLTForHuman/ModularCurve/PeriodHomPair.lean`, transcribing
`Definitions/Def_ModularCurve_PeriodHomPair.lean` (140 lines, whole, incl. `ExistsPeriodMapLinear`).

`namespace ModularCurve.Period`, in the pin's sections `JConj`/`Char`; `jConjMat` is the `diag(1,-1)`
conjugation with its four `@[simp]` entry lemmas, `_det`, `_trace`, `_mul`, `_jConjMat`, `_one`;
`jConjSL`/`jConjGamma0` the induced monoid homs; `charInvolution` the involution on characters with
its four lemmas; `periodHomPair`/`periodHomPair_def` the pair of period maps. Sits on
`FLTForHuman.ModularForms.EichlerShimura.PeriodPrimitive` (`HasEquivariantPrimitive`, `periodMap`,
`IsEquivariantPrimitive`, `periodHom`) and `Mathlib.LinearAlgebra.Prod`. Two `spec-pin:` lines (the
pin `Def_` and, if the wire has one, the pin `Thm_` wrapper for `periodHomPair` — check
`Theorems/` for a wrapper naming it).

## LD45 — the `Place.congr` block and `Pic0Congr` (one worker, two files, in this order)

**File 1**: **insert** into `lean/FLTForHuman/AlgebraicCurve/Defs/RatFuncPlaces.lean` the 11
declarations of the pin's `Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean` `congr` tail:
`congrRingEquiv`, `congrRingEquiv_toValuationSubring`, `comapSymmRingEquiv`,
`coe_comapSymmRingEquiv_apply`, `congrEquiv`, `congrEquiv_apply`, `congrEquiv_symm_apply`,
`congrResidueAlgEquiv`, `symm_algebraMap_comm`, `ord_congrRingEquiv`, `deg_congrRingEquiv`.
Do **not** touch the module's existing 26 declarations. **The manager has already migrated the
module for you**: it now carries its own four-line `spec-pin:` block (the two pin `Def_` modules and
the two comparable `S_` copies its `HeightOneSpectrum` lemmas are read against) and its
`PORT_FILES` row is deleted; `check_port --force` on the untouched module reports **20 ok / 0
mismatch / 0 missing / 0 own**. So: add the 11 declarations, add **no** `spec-pin` line, and update
the module header's "Dropped (measured, …)" paragraph — it currently says the whole `Place.Congr`
section (274–398) was dropped; after your edit it must say that `placeOfPoint` (236–274) stays
dropped and the `Congr` section is hosted (the leaves' `Pic0Congr` gate), and record the 20 →
31-or-so `check_port` verdict.
**File 2**: **new** `lean/FLTForHuman/AlgebraicCurve/Pic0Congr.lean`, transcribing
`Definitions/Def_AlgebraicCurve_Pic0Congr.lean` (122 lines, 14 declarations: `Divisor.congr` and its
lemmas, `Pic0.degZeroCongr`, its two `coe_` lemmas, `map_principal_degZeroCongr`, `Pic0.congr`).
`Divisor.congr = Finsupp.domCongr (Place.congrEquiv e he)`; the degree induction and the principal
computations are the pin's. Two `spec-pin:` lines (`Def_AlgebraicCurve_Pic0Congr.lean` and — only if
a `Thm_` wrapper exists for it — that wrapper).

## LD6 — the complex-place dictionary and its `Γ`-general form (one worker, two modules)

**File 1**: **new** `lean/FLTForHuman/ModularCurve/ComplexPlaceDictionary.lean`, transcribing
`Definitions/Def_ModularCurve_ComplexPlaceDictionary.lean` (49 lines: `realize` and the
`ComplexPlaceDictionary` structure with its five fields). Sits on `Defs/Fields.lean`
(`modularFunctionFieldFull`), `Defs/Laurent.lean` (`laurentBaseChange`, `LaurentSeries`) and
`AlgebraicCurve/Defs/Place.lean`.
**File 2**: **new** `lean/FLTForHuman/ModularCurve/ComplexPlaceDictionaryOf.lean`, transcribing
`Definitions/Def_ModularCurve_ComplexPlaceDictionaryOf.lean` (102 lines, 11 declarations: `realizeOf`,
`realizeOf_def`, `realizeOf_of_not`, `realizeOf_gamma0`, the `ComplexPlaceDictionaryOf` structure,
`ofGamma0`, `toGamma0`, `pt_ofGamma0`, `pt_toGamma0`, `pt_smul_of_mem`, `ramification_ne_zero`).
**The pin's import of `Def_AlgebraicCurve_DivisorClassGroup` is not needed** — no declaration of
either module names anything from it (SET-LEAVESDEF §0); do not import it, and say so in the header.
Two `spec-pin:` lines per module (its own pin `Def_`; add a `Thm_` wrapper line only if one exists).

## LD7 — `X0ModL`'s three declarations and the `XH` torsion trio (two inserts, one worker)

**File 1**: **insert** into `lean/FLTForHuman/ModularCurve/X0/FunctionFieldFull.lean` the pin
`Definitions/Def_ModularCurve_X0ModL.lean`'s missing three: `coeffMap_jqNModC`, `qExpandAlgHomC`,
`qExpandAlgHomC_apply`. Do not touch the 17 existing declarations of that pin module already in the
port, and do not change the module's `spec-pin` block (it names the pin `Def_`).
**File 2**: **insert** into `lean/FLTForHuman/ModularCurve/XH/FunctionField.lean` the pin
`Definitions/Def_ModularCurve_XH.lean`'s `JH.torsionGaloisRep` + `JH.torsionGaloisRep_apply` +
`JH.coe_torsionGaloisRep_apply` (the torsion trio, 17 lines). The Tate pair (`tateGaloisRep`,
`tateEnd`, their `_apply_coe`) and `JHC` are **not** in this order (they are typed through the absent
`TateModule`, SET-LEAVESDEF §0). If `JH` in the port is an `abbrev`, the trio's statements must use
the same spelling as the pin's (`JH M H`).
