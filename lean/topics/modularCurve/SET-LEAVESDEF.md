# The leaves' definition layer — the deferred Defs, measured and landed

**Status: scoped and landed (2026-10-27); six worker orders, one manager migration.** This is the
last definition layer of the `ModularCurve` column: the vocabulary the **leaves programme**
([TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §0.4/§0.5, 32 rows / 6,797 silo) is written over, plus
the three defs the ready block's wave deferred because no ready row named them
([WORKORDER-MCDEF-definition-wave.md](WORKORDER-MCDEF-definition-wave.md) §0.2). It follows the
recipe in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md).

It is the same audit as the def wave's, one level down: the shelf priced the leaves' gate at
**391 lines over four modules** (`PeriodHomPair` 140, `Pic0Congr` 106, `ComplexPlaceDictionaryOf`
102, `X0ModL` 43). Measured declaration by declaration (a last-name presence scan of every pin
`Def_` module in the leaves' closure against the port tree; the instrument is
`spec/gate_scan.py` plus a module-level variant of it, `tmp/modgate.py` in the wave's scratch), the
real gate is **eight pin modules / ≈700 pin lines**, and one of the shelf's four sits on a *partially
ported* module the shelf never listed:

| pin `Def_` module | public decls | missing | the shelf's line | serves |
|---|---:|---:|---:|---|
| `Def_CohCarrier_HeckeData` | 17 | **17** | — (unlisted) | the leaves' `pair_*` rows; `Inst`'s `hdata`/`MLAt` |
| `Def_CohCarrier_Inst` (`hdata`, `MLAt` only) | 2 | **2** | 80 | same |
| `Def_ModularCurve_PeriodOf` (`CuspForm` section) | 5 | **5** | 21 | L-other's period rows |
| `Def_CuspForm_Petersson` | 3 | **3** | — (unlisted) | the same `_gamma0` lemmas |
| `Def_ModularCurve_PeriodHomPair` | 24 | **24** | 140 | L-other's `periodAlongOf`/parabolic-hom rows |
| `Def_AlgebraicCurve_Pic0Congr` | 15 | **15** | 106 | L-other's `pic0Congr_jOne_jH_bot_compat` |
| `Def_AlgebraicCurve_RatFuncPlaces` (`congr` tail) | 11 | **11** | — (unlisted) | `Pic0Congr`'s `Place.congrEquiv` engine |
| `Def_ModularCurve_ComplexPlaceDictionary` | 2 | **2** | — (unlisted) | `ComplexPlaceDictionaryOf` |
| `Def_ModularCurve_ComplexPlaceDictionaryOf` | 11 | **11** | 102 | L-other's `realizeOf_eq_div` |
| `Def_ModularCurve_X0ModL` | 3 | **3** | 43 | L-x1coeff's `existsUnique_algEquiv_…` |
| `Def_ModularCurve_XH` (`torsionGaloisRep` trio) | 3 | **3** | 35 | the M9 successors |
| **total** | **96** | **96** | **391** | |

**Two corrections to the shelf's figures.** (i) `X0ModL` is **3** lines short, not 43: the shelf
priced the module's missing *span*; the port already has 17 of its 20 declarations and the three
missing ones (`coeffMap_jqNModC`, `qExpandAlgHomC`, `qExpandAlgHomC_apply`) are 3 declarations.
(ii) `Def_AlgebraicCurve_RatFuncPlaces`'s `congr` tail is **not** in the port — the `Place.congrEquiv`
/`congrRingEquiv`/`ord_congrRingEquiv`/`deg_congrRingEquiv` block that `Pic0Congr` is built on — so
`Pic0Congr` is a two-module order, not one. (The port's `RatFuncPlaces.lean` carries the other 26
declarations; its wire stays.)

**Not in this wave.** `Def_EllipticCurve_TateModule` (883 pin lines, 69 declarations) and the four
`ModularCurve_XH` declarations typed through it (`tateGaloisRep`, `tateEnd`, their two `_apply_coe`),
plus `JHC` — the padic-Tate-module topic's T1 plan
([TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md)), and the withheld pair's programme. The
`TateModule` layer is not a *leaf* gate: no leaf row names it, and the two MC rows that do are the
false ready (24) and the withheld pair (610). It stays deferred, now with its exact size on record.

## 0. The six orders

All homes are existing modules (one insertion) or new ones; each order's files are disjoint from the
others' except the one intra-order dependency (`LD45`).

| order | modules | pin lines | home | note |
|---|---|---:|---|---|
| **LD1** | `Def_CohCarrier_HeckeData` + `Inst`'s `hdata`/`MLAt` | 92 + 21 | **new** `ModularForms/CohCarrier/HeckeData.lean`; insert into `ModularForms/CohCarrier/Inst.lean` | mathlib-only imports; the `Inst` insert is the `MLAt` abbrev over `HeckeData` |
| **LD2** | `Def_CuspForm_Petersson` + `PeriodOf`'s `CuspForm` section | 14 + 21 | **new** `ModularForms/EichlerShimura/Petersson.lean` | `CuspForm.peterssonIntegrand`/`petersson` and the `…Of` general-level pair; the port's `PeriodOf.lean` header records the deferral that this order ends |
| **LD3** | `Def_ModularCurve_PeriodHomPair` | 140 | **new** `ModularCurve/PeriodHomPair.lean` | `jConjMat`/`jConjSL`/`jConjGamma0`/`charInvolution`/`periodHomPair` + `ExistsPeriodMapLinear`; sits on `EichlerShimura/PeriodPrimitive.lean` (`HasEquivariantPrimitive`, `periodMap`, `IsEquivariantPrimitive`) |
| **LD45** | `RatFuncPlaces`'s `congr` tail + `Pic0Congr` | ≈100 + 106 | insert into `AlgebraicCurve/Defs/RatFuncPlaces.lean`; **new** `AlgebraicCurve/Pic0Congr.lean` | the order *is* two modules, in dependency order inside one worker |
| **LD6** | `Def_ModularCurve_ComplexPlaceDictionary` + `…Of` | 49 + 102 | **new** `ModularCurve/ComplexPlaceDictionary.lean` + `ModularCurve/ComplexPlaceDictionaryOf.lean` | the `realize`/`realizeOf` choice functions and the `Γ`-general dictionary; sits on `Defs/Fields.lean` (`modularFunctionFieldFull`) and `Defs/Laurent.lean` |
| **LD7** | `X0ModL`'s 3 declarations + `XH`'s torsion trio | 3 + 17 | insert into `ModularCurve/X0/FunctionFieldFull.lean`; insert into `ModularCurve/XH/FunctionField.lean` | two small inserts, different import cones, one worker |

**The manager's lane, landed before dispatch: one migration.** `AlgebraicCurve/Defs/RatFuncPlaces.lean`
was on `PORT_FILES` and had **deliberately dropped** the pin's `Place.Congr` section (its header says
so, measured against `TOPIC-ac0-vocabulary.md` §2.7). The leaves' `Pic0Congr` gate *is* that section,
so the order that needs it pays the migration: the module now carries its own four-line `spec-pin:`
block (the two pin `Def_` modules, plus the two comparable `S_` copies its two `HeightOneSpectrum`
lemmas are read against — without them those two read as `MISMATCH` on a namespace qualifier alone,
FR-0058's family), the `PORT_FILES` row is deleted, and `check_port --force` reports **20 ok / 0
mismatch / 0 missing / 0 own** before the new declarations land. The other four homes are already
wired or new.

The six orders are in
[WORKORDER-LEAVESDEF-orders.md](WORKORDER-LEAVESDEF-orders.md) (one section per order; the preamble
carries the house rules).

## 1. Traps

**LD1.** (i) `HeckeData` is a `structure` over `𝒪`, `V`, `k` with universes `u v w` — keep the
`universe` line. (ii) The `attribute [local instance] moduleFreeAlg` is load-bearing: `toML`'s
`LocalizedModule.mkLinearMap` needs the `FreeAlg`-module on `V`. Keep it local. (iii) The pin's
`example`s are probes, not declarations — keep them as checks or drop them (they are `inferInstance`
probes; the port's `QExpReductionModL` kept one as a named non-declaration check). (iv) `MLAt` in
`Inst` needs `HeckeData` in scope; it is an `abbrev` whose type is `(hdata … ).ML`.

**LD2.** (i) `peterssonIntegrandOf` uses `∑ᶠ q : SL(2, ℤ) ⧸ Γ` — the `finprod`/`Finsupp` coset
representation; the pin's `Def_CuspForm_Petersson` version is over `Γ₀(N)` and the `…Of` version over
an arbitrary `Γ`. (ii) The `peterssonIntegrandOf_gamma0`/`peterssonOf_gamma0` lemmas are `rfl` and are
what the leaves' `ComplexPlaceDictionaryOf` rows consume. (iii) `ModularGroup.fd` (the fundamental
domain) is mathlib/ported — do not restate.

**LD3.** (i) `jConjMat` is the conjugation by `diag(1,-1)` on matrices; its `_mul`/`_det`/`_trace`
lemmas are `fin_cases`/`ring` computations. (ii) `charInvolution` is the involution on the
*characters* of `Additive Γ` and `charInvolution_mem_parabolicHoms` is the real content; the
`periodHomPair` is a pair of period maps. (iii) `ExistsPeriodMapLinear` is the pin's
`Prop`-existential wrapper over `periodMap` — transcribe it; it is not decoration.

**LD45.** (i) The `RatFuncPlaces` tail's `congrRingEquiv` is a `Place`-structure constructor over
`HeightOneSpectrum`; `congrEquiv` is the `Equiv` built from it; `ord_congrRingEquiv` and
`deg_congrRingEquiv` are the order/degree laws. **They go into the existing port module** (its wire
is unchanged; add the `spec-pin` lines for the pin module only if they are not already there — they
are, so add none). (ii) `Pic0Congr`'s `Divisor.congr` is `Finsupp.domCongr (Place.congrEquiv e he)`;
the `degree_congr` induction is the pin's. (iii) `Pic0.congr` is
`QuotientAddGroup.congr _ _ (degZeroCongr e he) (map_principal_degZeroCongr e he)`.

**LD6.** (i) `realize`/`realizeOf` are `Classical.choose` over a `Σ k : ℤ, …` of modular forms —
keep the `if H : … then … else 0` shape and the `dif_pos`/`dif_neg` spelling (in v4.34 `dite`/
`ite`'s lemmas: `dite_eq_left`/`dite_eq_right`/`ite_eq_right`). (ii) The `ComplexPlaceDictionary`
structure's fields include `meromorphicOrderAt_realize` with a `WithTop ℤ` coercion — transcribe the
coercion shape. (iii) `ComplexPlaceDictionaryOf` is the `Γ`-general version with `ofGamma0`/
`toGamma0`; it needs the `Γ₀(N)` dictionary. (iv) `def realize` is a `by classical exact if …`
*term*; `realizeOf_def` is `rfl` and `realizeOf_of_not` uses `dif_neg`.

**LD7.** (i) `X0ModL`'s three: `coeffMap_jqNModC` (the `ℚ`-normalisation of `coeffMap_jqModC`),
`qExpandAlgHomC` (an `AlgHom` from the q-expansion algebra) and its `_apply`. (ii) The `XH` trio is
`JH.torsionGaloisRep n : (ℚ̄ ≃ₐ[ℚ] ℚ̄) →* Module.End (ZMod n) (Pic0.torsion …)` built from
`SemilinearAut.torsionRep` and `arithmeticGalois` — both ported; the two laws are `rfl`. The Tate pair
stays out (§0).

## 2. Gates, per order

As the def wave's gates (that wave's module §2): `check_port` 0 mismatch / 0 missing with every public
declaration `ok`; `#print axioms` on every headline (the defs may have none, the lemmas must be
`[propext, Classical.choice, Quot.sound]`); the module's own build under `flock` (background channel
on a busy tree, FR-0060); silent, no `set_option`/suppression added; `dedup.py --within --tier shape`
0 clusters; the `spec-pin:` block names exactly the pin modules transcribed (LD1/LD2/LD3/LD6: one or
two lines; LD45: the `Pic0Congr` pair *plus* its own pin `Def_`; LD7: the two pin `Def_` modules and
none else); no `spec/decl_markers.tsv` row from a worker.

**The consumer zone for the wave** (`spec/ModularCurveLeavesDefConsumer.lean`, manager-written): the
`HeckeData` tower (`opAlgHom` on a generator, `toMLₒ`, `V_isScalarTower`) composed with a
`CohCarrier` `H1`; the petersson pair's `_gamma0` `rfl` lemmas; `periodHomPair` applied to a
`CuspForm`; `Pic0.congr` on a principal degree-zero divisor; `ComplexPlaceDictionaryOf`'s
`pt_smul_of_mem` and `realizeOf_gamma0`; the `X0ModL` `qExpandAlgHomC` on a power series; and
`JH.torsionGaloisRep`'s two laws.

## 3. What this wave does not do

- **`Def_EllipticCurve_TateModule`** (883 lines / 69 declarations) and the five `Def_ModularCurve_XH`
  declarations typed through it (`tateGaloisRep`, `tateEnd`, their `_apply_coe`, `JHC`) — the
  padic-Tate-module topic and the withheld pair. Size on record now.
- **`Def_AlgebraicCurve_DivisorClassGroup`** (484 lines) — imported by three of the modules above but
  **not used by any of their declarations**: the module-level audit (§0) shows `ComplexPlaceDictionary`,
  `ComplexPlaceDictionaryOf` and `X0ModL` name nothing from it, so the port omits the import. If a
  leaf row turns out to name a class-group declaration, the pin module comes back with that row.
- **The leaves' row work** (32 rows / 6,797 / ≈5,870): this wave is the layer, not the rows.

## 4. The landing — measured (2026-10-27)

Ten modules (six new, four inserted into), **96 declarations, 147 checked `ok` / 0 mismatch / 0
missing / 1 own** (the `own` is the pre-existing `full_degeneracyC_map_le` in
`X0/FunctionFieldFull.lean`), axioms clean, zero warnings, no `set_option` added, no marker row
written by a worker:

| module | verdict | what it hosts |
|---|---|---|
| `ModularForms/CohCarrier/HeckeData.lean` (new, 158 lines) | 17 ok | the `HeckeData` structure, the `FreeAlg`/`mTheta`/`opSubalgebra`/`opAlgHom` tower, `ML`/`toML`/`toMLₒ` |
| `ModularForms/CohCarrier/Inst.lean` (insert) | 7 ok (5 + 2) | `hdata`, `MLAt` |
| `ModularForms/EichlerShimura/Petersson.lean` (new, 95) | 8 ok | the Petersson inner product, both levels, with the two `_gamma0` `rfl` lemmas |
| `ModularCurve/PeriodHomPair.lean` (new, 156 pin) | 24 ok | `jConjMat`/`jConjSL`/`jConjGamma0`/`charInvolution`/`periodHomPair`/`ExistsPeriodMapLinear` |
| `AlgebraicCurve/Defs/RatFuncPlaces.lean` (insert, migrated) | 31 ok (20 + 11) | the pin's `Place.Congr` section |
| `AlgebraicCurve/Pic0Congr.lean` (new, 122 pin) | 15 ok | `Divisor.congr`, `Pic0.degZeroCongr`, `Pic0.congr` |
| `ModularCurve/ComplexPlaceDictionary.lean` (new, 49 pin) | 2 ok | `realize`, `ComplexPlaceDictionary` |
| `ModularCurve/ComplexPlaceDictionaryOf.lean` (new, 116 pin) | 11 ok | `realizeOf` and the `Γ`-general dictionary |
| `ModularCurve/X0/FunctionFieldFull.lean` (insert) | 16 ok / 1 own | `coeffMap_jqNModC`, `qExpandAlgHomC`, `qExpandAlgHomC_apply` |
| `ModularCurve/XH/FunctionField.lean` (insert) | 16 ok | the `JH.torsionGaloisRep` trio |

**The shelf figure does not move, and must not.** `needed` is **992 / 395,624** before and after;
frontier **1,421 / 731,527**; no row entered or left the ready/leaves shelves; `--selfcheck`
consistent. A definition layer is not a premise: the leaves' 32 rows still read `needed = 1` and are
still gated on *statability*, which is what this wave buys.

**Two corrections the wave measured.** (i) `Def_AlgebraicCurve_Pic0Congr` has **15** declarations,
not 14 — the audit's last-name scan had counted its `Divisor.congr` as present because an unrelated
`congr` exists in `ModularForms/Hauptmodul.lean` (FR-0052's shape: a last-name hit that is not the
pin's declaration). (ii) `X0ModL`'s `qExpandAlgHomC` is landed as an **`abbrev` of the port's
`qExpandAlg`**, not a second `def`: the statement is the pin's (the checker matches it at pin :77),
the body is written once (the port's C1 "one map, one proof"), and the module header records the
alias.

**One worker judgement vetoed.** LD3's module briefly carried a second `spec-pin:` line naming
`Thm_ModularCurve_periodHomPair_eichlerShimura.lean` "for provenance": `frontier.py`'s source tier
credits a `spec-pin:` header *before* the statement exists, so that line would have marked the
wrapper's node ported without its statement being in the port — MD-001's failure mode. The line is
deleted; the module's wire is the pin `Def_` module only, and the header says why.

**The consumer zone.** `spec/ModularCurveLeavesDefConsumer.lean`, seven zones
(`heckedata`/`petersson`/`phompair`/`pic0`/`place`/`x0`/`torsion`) — **0 errors, 0 warnings, ~7 s**
at both the 200k and the project cap. Its first draft exposed a real hazard for the leaves' rows and
one worth carrying: *projecting* `opAlgHom`/`toMLₒ` off a `hdata`-built `HeckeData` spins past 200k
heartbeats (the `FreeAlg` field unfolds through the structure literal and the `opFamily` cone), while
the construction itself is cheap — so the zone states the API over an abstract datum and keeps
`hdata` as its own use (FR-0063: bind the datum, never write `(hdata …).<field>` in a statement).

**What remains in the column.** The leaves' **row work** (32 rows / 6,797 / ≈5,870 net), now
statable; the M9 successor (1,176) and the three first-wave successors (611/168/36); the false ready
(24) and the withheld pair (610) — both on `Def_EllipticCurve_TateModule` (883 lines / 69
declarations), whose size is on record here (§0) and belongs to
[TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md).
