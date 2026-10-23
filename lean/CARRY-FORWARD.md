# Carry-forward register

Status of work that is **not done** — deferred API, open follow-ups, cleanup — with the facts
needed to price it. Grep this file for a node name before pricing that node: an entry means its
`lines`/`needed` does not yet account for something its consumers need. Add an entry when part of a
pin file's surface is deferred; delete it when the work lands. The general scoping cautions are in
[porting-playbook.md](porting-playbook.md) §2.1.

Deferred API that has been ported and verified is in `Reserve/`, not here.

## Deferred API

### `Eaux_apply` — a pin-public unfolding lemma with no consumer, deferred from FR1

`Eaux_apply (a b : ℕ) (τ : ℍ) : Eaux a b τ = E₄ τ ^ a * E₆ τ ^ b` is pin-public at
`S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean:605`. It is used
**nowhere** in the pin — a `grep -c` over the whole tree finds the declaration line only — and the
FR1 module does not need it, so [deligneSerre/WORKORDER-FR1-fricke-reciprocity.md](deligneSerre/WORKORDER-FR1-fricke-reciprocity.md)
deferred it rather than open `WeightOne/Gamma0Integral.lean` to append one line. If a consumer ever
appears its home is beside the public `Eaux` in that module (`:1628`), appended at the pin's
signature with a `pin:` row — the treatment `frickeConj` got. Nothing any pin file uses is missing;
the entry is here so that a later reader does not mistake the omission for an oversight.

### `Def_AutomorphicForm_CuspidalSpectrumCarrier` — the carrier definition module behind the deferred centre-cut slab bound

Deferred 2026-10-18 while porting the centre-cut fundamental-domain trio
([logs/centre-cut-fundamental-domain-trio.md](logs/centre-cut-fundamental-domain-trio.md)).
The node
`AutomorphicForm.CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample`
(234 pin lines) is priced `--ready` by `frontier.py`, but its wrapper imports
`Definitions/Def_AutomorphicForm_CuspidalSpectrumCarrier.lean` (288 lines / 31 declarations:
`IsSlabFundamentalDomain`, `fdPins`, `HasModulus`, `weight`, `weightedMeasure`, `Carrier`,
`memberSubmodule`, `cuspMemberSubmodule`, `pairing`, `toCarrier`, `cuspSubcarrier`, `IsLift`, …),
which the port does not have. The frontier does not walk import-only definitions; this is the
playbook §4(a) blindness. The module imports only the already-ported
`Def_AutomorphicForm_CuspidalConstituent` and `Def_NumberField_TateGlobalZeta`, so it is a cheap
definition wave when the node is scheduled. **Do not schedule the 234 off `--ready` until it
lands.** The three sibling nodes landed without it:
`isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre` and the two
`exists_measurableSet_isFundamentalDomain_subset_iUnion_…` twins.

The module is imported by more pin `S_` files than the slab bound: the arch-type-span leaf
`S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`
imports it and uses **none** of its 31 declarations (2026-10-20,
[logs/arch-type-span.md](logs/arch-type-span.md)). A pin `import` is a module-granular fact —
`fltdata.proof_defs` records it that way — so the test for "is this definition module on the
path" is a declaration-level `grep` over the consumer's `S_` file, not its import block. This
entry is unchanged: the module is still owed when the 234-line slab bound is scheduled.

### `Def_ModularCurve_EigenformIdeal` — the gate of `omegaRow_T2`'s definition layer

Deferred 2026-10-20 while porting the nine small-family pairs (WORKORDER-MG3, group C). The 24-line pin
module defines three declarations **in terms of** declarations of another pin definition module:

- `ModularCurve.IsEigenformIdeal (N) (𝔪 : Ideal HeckeAlg) : Prop` :=
  `∃ f IsNormalizedEigenform …, 𝔪 = eigenIdeal (…)` — uses `eigenIdeal`;
- `ModularCurve.EigenformSupportAt` := `EigenformSupport p J (IsEigenformIdeal N)` — uses `EigenformSupport`;
- `ModularCurve.EichlerShimuraDataAt` := `EichlerShimuraDataReduced … (IsEigenformIdeal N)` — uses
  `EichlerShimuraDataReduced`.

All three of `eigenIdeal`, `EigenformSupport`, `EichlerShimuraDataReduced` live in
`Definitions/Def_HeckeGalois_EichlerShimura.lean`, which this register already records as blocked
(`ModularForms/HeckeFiniteAlgebra.lean`, "Still blocked (not this module)"; §`exists_hasEquivariantPrimitiveOf`
above). Homing the 24-line gate therefore means homing that module and its prerequisites first.

**What is deferred is only the gate.** `ModularCurve.omegaRow_T2` (447 pin lines) and its six
`ModularForm`/`ModularCurve` premises reference none of the three declarations
(`rg -c 'eigenIdeal|EigenformSupport|EichlerShimuraDataReduced' P2M/Sol/S_omegaRow_T2.lean` → 0), so the
pair landed without it. **Trigger:** a consumer that states `IsEigenformIdeal`, `EigenformSupportAt` or
`EichlerShimuraDataAt` — i.e. any `Def_HeckeGalois_EichlerShimura` consumer — must home that module (and
then this 24-line gate) first. Do not port a consumer of the three by stubbing them.

### `Def_Compat_Mathlib430` blocks A–C — not homed, only block D is

Decided 2026-10-20 while porting `AddAut.exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem`
(WORKORDER-MG3 group D). The pin module (`Definitions/Def_Compat_Mathlib430.lean`, 340 lines, imported
by 197 pin `S_`/`Theorems` files) vendors four blocks of mathlib **4.30.0** API that `v4.34.0` renamed or
removed:

- **block D** (lines 124–340): `instance : Group (AddAut A)` plus thirteen primed lemmas
  (`coe_mul'`, `mul_apply'`, `inv_def'`, …). **Homed** as `FLTForHuman/Algebra/AddAut/Compat.lean`,
  because v4.34 gives `AddAut` only an *additive* group and the `AddAut` node's statement
  (`(H : Subgroup (AddAut (ZMod M × ZMod M)))`) cannot elaborate without a `Group` instance. `rg` cannot
  see this need — it is a typeclass instance, not a symbol — so a "the compat import is dead" reading is
  wrong here.
- **blocks A–C** (lines 20–122): the v4.30 `Representation`/`Rep` API (`ofMulActionFinsupp*`,
  `leftRegularHomFinsupp*`, and their `Bridge` lemmas). **Not homed**: no port consumer, and vendoring
  old representation API wholesale invites future landings to use it instead of adapting to `v4.34`.
  Trigger: any ported node whose statement or proof names one of those declarations — then home the
  block that is needed, verbatim, at the pin's suffixed names, and record it here.

### `HeckeEis.coresHom_eq_transfer` — a definition gate still deferred; the two `Rat*` gates are homed

Deferred 2026-10-20 at the close of WORKORDER-MG3 phase 2, when the column stopped cutting this front.
Both are statement-level gaps (nothing in the port can be imported for them), and both ask for a pin
definition module the port has never homed:

| node | pin lines | gate module | gate lines | pin importers |
|---|---:|---|---:|---:|
| `HeckeEis.coresHom_eq_transfer` | 59 | `Def_Gamma0HeckeOperatorHom` (`HeckeEis.coresHom`, `transferAux`, `coe_transferAux`) | 304 | 144 |
| ~~`RatAdele.denseRange_algebraMap_add_adeleSingleAt`~~ | ~~309~~ | ~~`Def_LanglandsTunnell_StandardLocalConstantsAt`~~ — **homed 2026-10-20**, `LanglandsTunnell/StandardLocalConstantsAt.lean` (21 ok) | ~~144~~ | **799** |

`rg` over `FLTForHuman/` still finds no `coresHom`/`transferAux`; that gate remains deferred. The
`RatAdele` gate is **resolved**: `Def_LanglandsTunnell_StandardLocalConstantsAt` was homed whole
(2026-10-20) at `LanglandsTunnell/StandardLocalConstantsAt.lean` — 21 declarations, checker 21 ok / 0
mismatch, build 3.9 s — on top of the already-homed `NumberField/AdelicTraceFin.lean` and
`LanglandsTunnell/TateLocalConstantsAt.lean`; the `Def_NumberField_AdelicBox` import is homed too and the
`RestrictedProduct` import is inert, so the node is now statement-ready. Record:
[logs/rat-def-gates.md](logs/rat-def-gates.md). **Trigger** for `HeckeEis` is unchanged: home
`Def_Gamma0HeckeOperatorHom` **whole and verbatim** (playbook §2.3), with its own `spec-pin:` header,
before stating the node.

**Third deferral of the same wave, now resolved:** `RatIdele.exists_norm_apply_eq_ideleNorm_rpow`
(312 pin lines) — its *statement* was always fine (`TateGlobal.ideleNorm` and
`AutomorphicForm.IsIdeleClassChar` are homed) but its *proof* needs the normalizer API of
`Definitions/Def_RatIdele_Normalizer.lean` (`RatIdele.ρ`, `ρ_spec`, `ρ_ne_zero`, `IsNormalizer`).
`Def_RatIdele_Normalizer` was homed whole (2026-10-20) at
`NumberTheory/RatIdele/Normalizer.lean` — 63 declarations, checker 63 ok / 0 mismatch, build 4.0 s — so
the node is now unblocked. The `distribHaarChar` route recorded here still stands: the port's
`AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm`
(`NumberTheory/AdelicModulus.lean:80`) is a *stronger* form whose extra `∏ᶠ` factor is `1` under the pin's
`snd = 1` hypothesis, so take the pin's variant as a two-line corollary rather than restating a third
version. Record: [logs/rat-def-gates.md](logs/rat-def-gates.md).

### The `LocalNewvector` pair of WORKORDER-MG3 — a definition gate bigger than the family

Deferred 2026-10-20 while phase 2 was dispatching. The two nodes — `LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization`
(58 pin lines) and `…exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq` (589) — total
647 pin lines, but **none of the vocabulary they are stated over is homed**. The gate, measured by the group that found it:

| pin module | lines | pin importers | needed for |
|---|---:|---:|---|
| `Def_LocalNewvector_AdelicSpanCarrier` | 179 | **173** | both (`LocalNewvector.AdelicSpan`, `AdelicFnCarrier`, `AdelicSpanSubmodule`) |
| `Def_LocalNewvector_ConductorDatum` | 114 | 56 | both (`fixedSubmodule`, `mem_fixedSubmodule_iff`, `HasNewvectorConductor`, `congruenceK1_le_integralSubgroup`) |
| `Def_RepTheory_GL2CongruenceSubgroup` | 531 | 23 | node 2 (`FLT.SmoothVectors.gl2CongruenceSubgroup` and its API) |
| `Def_LocalLanglands_IntegralSubgroupCompact` | 40 | 17 | node 2 (`FLT.SpectralSide.isCompact_coe_integralSubgroup_padic`) |

≈ **864 pin definition lines for a 647-line family** — it is not a small family, and `AdelicSpanCarrier`
(173 pin importers) and `GL2CongruenceSubgroup` (531 lines) are definition sets with consumers of their
own, so they want an order and a review of their own rather than being a side-charge on a pair.

Two further pin definition modules are touched **only** by the wrappers' `open`/`attribute` lines (so
dropping them leaves no statement effect; record the drift): `Def_LocalNewvector_PrincipalSeriesCarrier`
(255, the `PSCarrier` `attribute [-instance]`/`[-simp]` prelude) and
`Def_AutomorphicForm_DihedralWeightOneLift` (30, an `open … DihedralWeightOne`).

Already homed and *not* owed: `LocalNewvector.padicK1`/`congruenceK0`
(`RepTheory/LocalNewvector/CongruenceSubgroupK1.lean`), `AdelicDock.*`
(`NumberTheory/AdelicDock/LocalEmbedding.lean`), `FLT.SmoothVectors` (`RepTheory/SmoothVectors.lean`),
`AdelicLevel.*`, `LocalGL2.integralSubgroup`, and the `open`-only
`FLT.SpectralSide.isOpen_coe_integralSubgroup_padic`. **Trigger:** the next session that wants these two
nodes homes the four modules **whole and verbatim** (playbook §2.3), `spec-pin:`-header each, before
stating either node.

### The exact-volume / L2 chain — `Def_AutomorphicForm_{Gamma0ExactVolume,FundamentalDomainExactVolume,EisensteinScattering,L2ProductionInstance,L2AutomorphicCarrier,TruncatedDomainPartition}`

Deferred 2026-10-17 while porting `CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus`
(record: [topics/deligneSerre/TOPIC-petersson-hecke-adjointness.md](topics/deligneSerre/TOPIC-petersson-hecke-adjointness.md)). The pin's
`Def_AutomorphicForm_ModularFundamentalDomain.lean` (217 lines) reaches this six-module chain
(1,436 pin lines: 176 + 236 + 278 + 111 + 147 + 488) only for five facts:
`volume_fd_diff_fdo`, `volume_fdo_eq_volume_fd` (from `Gamma0ExactVolume`), `volume_fd_eq`,
`gate_volume_ne_zero` (from `FundamentalDomainExactVolume`) and `measurableSet_smul_fd` (from
`L2ProductionInstance`). The port's
`FLTForHuman/AutomorphicForm/UpperHalfPlane/ModularFundamentalDomain.lean` carries the first two
and the last `private` — short measure-theory proofs over the already-ported
`FundamentalDomainVolume`/`HyperbolicMeasure` — and wires the other 16 public declarations of the
module verbatim.

Deferred:
- the four gate theorems of `ModularFundamentalDomain` (`gate_not_isFundamentalDomain_sl2z`,
  `gate_two_routes`, `gate_factor_two_load_bearing`, `gate_two_routes_ne_zero_ne_top`), the only
  consumers of `volume_fd_eq = ENNReal.ofReal (π / 3)`;
- the whole public surface of the six modules above.

**Not a D-S dependency of its own.** Checked against the 1,396 needed rows of
`frontier.py --ds --include-leaves --list`: no needed node imports any of the six directly; they
enter only through `ModularFundamentalDomain`, which three needed nodes use — this row,
`CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough` and
`CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen`. The latter two additionally need
`Definitions/Def_CuspForm_PeterssonCoset.lean` (744 lines), not ported and not needed here.

### `Def_AutomorphicForm_TwistedOrbital` — the finite-place twisted-orbital subject

> **RESOLVED (2026-10-14).** The whole node landed, together with the base-change chain it needed,
> as the twisted-orbital definition program
> ([topics/automorphicForm/TOPIC-twisted-orbital-defs.md](topics/automorphicForm/TOPIC-twisted-orbital-defs.md),
> W1–W4). `TwistedOrbital.lean` (83/83), `LocalOrbitalBase.lean` (62/62, folding the old
> `IntegralUnits.lean`), `UnitFactorizableOfType.lean` (9/9), the three W3a support nodes, and the
> eight-module chain (`IntegralClosure`, `AdicValuation`-substitutes, `CompletionBaseChange`, the
> `Def_Mathlib_*` supplements, `InfiniteAdeleRing_BaseChangeData`, `M4aHerbrand_ArchSemilocal`,
> `SigmaCentralizer`) are all landed and registered — 119 modules / 3,415 public. The
> unit-factorizable trio then landed at checker **9793 (+3)**, 0 mismatched / 0 missing. **No
> elaborator budget was transcribed**: the pin's `maxHeartbeats 1200000` family and the rest were
> removed by restructuring under the 200k cap. The paragraph below is the pre-resolution record.

Pin node 574 lines / 83 declarations. The archimedean approximate-identity silo names three of
them — `glBorelOf` (:57), `borelSpace_glBorelOf` (:59), `archHaarK` (:401) — which landed in
`FLTForHuman/AutomorphicForm/Adelic/ArchHaar.lean`.

Unported:

- the finite-place twisted-orbital subject (`semiLocalHaar`, `IsTwistedOrbitalIntegral`,
  `AreMatchingOn`, `twistedCentralizer`, …);
- the archimedean `archHaarL`/`archIdent`/`AreMatchingArch`, blocked on the unported
  tensor/base-change chain;
- 13 import-only `Definitions/` closure modules (4,390 pin lines).

Deferred to its own definition-first wave. Forcing it in front of the silo would pull in
`Def_DedekindDomain_Completion_BaseChange`, `Def_M4aHerbrand_ArchSemilocal` and four
`Def_Mathlib_*` supplements for mathematics the silo never states. Measurement:
[topics/automorphicForm/TOPIC-archTestFactor-family.md](topics/automorphicForm/TOPIC-archTestFactor-family.md) §5.

**Update (2026-10-14) — the unit-factorizable trio is blocked by the same chain.** The three
ready-shelf nodes `AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule`
(823), its `_finTestFactor_` sibling (854) and its `_principalLevel_` sibling (971) were scoped as
`WORKORDER-UF1` + `WORKORDER-UF2`. Their **statements** name `IsUnitFactorizableAboveOfType`, so
they need the `SemiLocal`/`AboveTier`/`AboveTierRefined` blocks of this module — and those blocks
are **not** free of the chain: `semiLocalIntegers` names `HeightOneSpectrum.tensorAdicCompletionIntegersTo`
and `semiLocalEval` names `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv`, while
`isCompact_semiLocalIntegralSet` pulls `piIntegers`/`HeightOneSpectrum.Extension`/`semiLocalHomeomorph` and the
`IsModuleTopology.*` instances (`WORKORDER-UF1` §1.2 was wrong to treat `SemiLocal` as chain-free).
Measured minimal closure of those named seeds: **127 declarations / ≈1,966 pin lines across nine
modules** (`Def_DedekindDomain_Completion_BaseChange` 43/792, `Def_DedekindDomain_AdicValuation_InlineSpecific`
31/536, `Def_Mathlib_IsModuleTopology` 22/267, `Def_DedekindDomain_IntegralClosure` 9/157,
`Def_Mathlib_RightActionInstances` 8/102, `Def_NumberField_InfiniteAdeleRing_BaseChangeData` 10/83,
`Def_Mathlib_Topology_Algebra_UniformRing` 1/12, `Def_NumberField_Extension` 1/4,
`Def_AutomorphicForm_UnitFactorizableOfType` 2/13); whole-node it is **3,740 pin lines / 341
declarations** over eleven modules. That is larger than the trio it unlocks (`port_plan`: 1,281 net
new), it is not a citation dependency of the D-S target (`frontier --ds --top 0 --list` shows
**zero** hits for any chain name, while the trio itself is `needed` at 823), and
`Def_DedekindDomain_Completion_BaseChange` carries `set_option maxHeartbeats 1200000` /
`synthInstance.maxHeartbeats 400000`, which collides with the port's never-raise rule.

**Decision: defer the trio, do not port the chain now.** The trio stays in `needed` (deferring a
ready node blocks nothing) and should be re-cut when its larger siblings are taken, so the chain is
paid once: `AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType`
(1,231, `needed`) and, behind them, the `coversModCentre` silo (3,038) and
`twistedConvOp_mem_isotypicCuspSubmodule_…` (2,542). The one chain-free piece landed and is
registered: `FLTForHuman/AutomorphicForm/Adelic/IntegralUnits.lean` (13 public, tier 3) —
the pin's `integralMatrixSet`/`integralUnitsSet`/`IsBiInvariantUnder` block. Records:
[topics/automorphicForm/WORKORDER-UF1-unit-factorizable-defs.md](topics/automorphicForm/WORKORDER-UF1-unit-factorizable-defs.md) §10.

### `MeasureAssembly.archBorel` — duplicate of `AutomorphicForm.glBorelOf`

`AutomorphicForm.MeasureAssembly.archBorel`
(`FLTForHuman/AutomorphicForm/Adelic/RightConvComm/MeasureAssembly.lean:61`) is statement-identical
to the pin's `glBorelOf`, which landed at `AutomorphicForm/Adelic/ArchHaar.lean`. The adapter is
used as a `local instance` in `MeasureAssembly.lean` and in `SliceCentrality.lean:55`. Collapsing
the twin edits two modules of the `RightConvComm` cone. Price:
`build_ladder.py --edit FLTForHuman/AutomorphicForm/Adelic/RightConvComm/MeasureAssembly.lean`.

### `CuspForm.exists_degeneracy_gamma1_hasNebentypus` — two unported definition modules

The frontier lists this row ready (218 silo lines); it is not. Its `S_` file imports and uses
`FreyPackage.ModMCarrier.rescaleSlash_isZeroAt`, and neither of the modules supplying it is ported:

- `Definitions/Def_ModularForm_AtkinLehnerDatum.lean` (157 lines, 21 declarations);
- `Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean` (176 lines, 10 declarations).

It is a different subject from the landed Γ₁/Nebentypus pair (nebentypus under the `V_d`
rescaling) and needs its own definition-first order. Reproduce:
`python3 tools/deps/port_advise.py --nodes CuspForm.exists_degeneracy_gamma1_hasNebentypus`.

### `ModularCurve.exists_hasEquivariantPrimitiveOf` — unported pieces of the period API

Landed with its 28-citer `ModularCurve.Period` API in
`FLTForHuman/ModularForms/EichlerShimura/{PeriodPrimitive,PeriodIntegral,PeriodOf}.lean`
(vocabulary and `Γ₀(N)` lattice; `periodOf`/`periodLatticeOf`/`HasEquivariantPrimitiveOf`/
`periodMapOf`). Not ported, because no consumer of this node reaches them:

- `Def_ModularCurve_PeriodTransfer.lean` (150 raw / 104 content): `conjRel`/`conjSubgroup`/
  `conjPrimitive`, `traceRep`/`transferElt`/`traceSum`, `IsEquivariantPrimitive.traceSum`;
- the `Hecke` section of `Def_ModularCurve_PeriodLattice.lean` (≈185 raw):
  `cuspHeckeGen`/`cuspHeckeAeval`/`cuspHeckeRep`/`dualHeckeRep`/`PeriodLatticeHeckeStable`/
  `periodLatticeModule` — the only piece that pulls in `Def_CuspForm_HeckeAlgebra` and
  `Def_HeckeGalois_EichlerShimura`;
- the `CuspForm` Petersson block of `Def_ModularCurve_PeriodOf.lean` (≈30 raw):
  `peterssonIntegrandOf`/`peterssonOf`.

Trigger: the Hecke-stability consumers (`periodLatticeHeckeEnd*`, `PeriodLatticeHeckeStable`) and
the period-transfer consumers (`IsEquivariantPrimitive.traceSum`).
`Def_ModularCurve_PeriodLattice.lean` is in the checker's `SOURCES` for its `Period` section only;
adding the `Hecke` section must not disturb the names already verified from it.

### `JOne.torsionGaloisRep` / `diamondOneBar` — the unported `Pic0` action/torsion block

Five declarations omitted from the X₁ Hecke/diamond inputs because their prerequisite is unported:

- `JOne.torsionGaloisRep`, `JOne.torsionGaloisRep_apply`, `JOne.coe_torsionGaloisRep_apply`
  (pin `Definitions/Def_ModularCurve_X1.lean:189-207`);
- `diamondOneBar`, `diamondOneBar_apply` (pin `Definitions/Def_ModularCurve_X1Diamond.lean:98-103`).

The missing prerequisite:

- `Pic0.torsion` / `mem_torsion` / `instModuleZModTorsion` (pin
  `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`);
- the `SMul`/`DistribMulAction (SemilinearAut K F)` actions on `Divisor` and `Pic0`,
  `degZeroSMulHom`, `smul_mem_torsion`, `instSMulTorsion`/`instDistribMulActionTorsion`,
  `instSMulCommClassZModTorsion`, `SemilinearAut.torsionRep` (pin
  `Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean:206-356`, ≈150 content lines); decided
  home `AlgebraicCurve/Defs/SemilinearAut.lean`, beside the `Pic0.torsion` block in
  `AlgebraicCurve/Defs/Divisor.lean`;
- `ModularCurve.PicAction` (pin `Definitions/Def_ModularCurve_ArithmeticGalois.lean:85-105`),
  decided home `ModularCurve/Defs/ArithmeticGalois.lean`.

Size ≈170 content lines plus the `Pic0.torsion` block; it edits three frozen files, so it is a
definitions-first mini-set with its own review gate. Consumers: the five declarations above and the
successor targets `ModularCurve.heckeDiamondCommuteBar`,
`ModularCurve.rationalRankTwoNebentypus_family`,
`ModularCurve.moduleFinite_padicInt_tateModule_jOne`, `CuspForm.IsEigenformWith.exists_galoisRepAdic_*`.
Not on the `heckeDiamondInputsAll` cone.

Frontier caveat: `ModularCurve/X1/Defs.lean` and `X1/Diamond.lean` are in `PORT_FILES` and their pin
files in `SOURCES`, so a citer that reaches `JOne.torsionGaloisRep` reads one node closer than it
is. Treat those citers as blocked on this entry.

### `Def_EllipticCurve_FunctionFieldPullback` — the remainder behind `placeOf`/`transEquiv`

`FLTForHuman/WeierstrassCurve/Place/PointPlace.lean` ports only what the `weilPairing0` entry point
consumes: `Point.xc`/`yc` (with `xc_some`/`yc_some`, `nonsingular_xc_yc`, `eq_some_xc_yc`),
`placeOf`/`placeOf_asIdeal`, `transEquiv`. `placeOf` is re-derived over the port's
`CoordinateRing.heightOneSpectrumOfEquation` and `transEquiv` over
`WeierstrassCurve.Affine.translationAlgEquivOf` (`Velu/Engine.lean`); the pin's
`transPull`/`pointPull`/`pointHom` route is not transcribed.

Unported (the node's algebraic content — the pullback/translation/multiplication dictionary):
`genericX`/`genericY`, `evalEval_baseChange_polynomial`, `genericPoint`, `pointHom` and its lemmas,
`pointPull`, `FunctionField.algHom_ext`, `exists_eq_baseChange_of_isIntegral_xc`,
`not_isIntegral_xc_of_ne_baseChange`, `genericPoint_*`, `transPull` (with `map_*`/`transPull_*`),
the `transEquiv_*` lemmas beyond the definition, `negPull`/`negEquiv`/`MulGood`/`mulPull`,
`exists_point_xc_eq`/`infinite_point`.

Consumers: the Frey/Galois-representation and `Elliptic/PeriodPair` cones; port the node whole
before pricing those through `PointPlace.lean`. Frontier caveat: the pin file is in `SOURCES` and
`Place/PointPlace.lean` in `PORT_FILES`, so a citer reaching `transPull`, `pointHom`, `genericPoint`
or `negPull` also reads one node closer than it is.

### `NumberField.TateGlobal.integrable_refMeasure_mul` — blocked on the `v4.34.0` product-measure API

Pin file **B**, `S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5146` (pinned `aa2d8b3`):

```lean
theorem integrable_refMeasure_mul {L} [NormedRing L] {A} {B} {C}
    (hA : Integrable A (archRef μa)) (hB : Integrable B (sRef S μf))
    (hC : Integrable C (deepRef S)) :
    Integrable (fun q => A q.1 * (B q.2.1 * C q.2.2)) (refMeasure S μa μf)
```

The statement carries no measure hypotheses (mathlib `v4.33.0` proved `Integrable.mul_prod`/
`smul_prod`/`op_fst_snd` with `omit [SFinite ν]`). In `v4.34.0` those lemmas carry `[SFinite ν]`,
and the gap is wider than them: `Measure.prod_restrict` needs `[SFinite μ] [SFinite ν]` on the
**unrestricted** factors, and `Measure.prod_eq` needs `SigmaFinite`.

The statement is true and the port already proves the needed s-finiteness — `Integrable f μ` makes
`μ.restrict (Function.support f)` s-finite, which is
`MeasureTheory.sFinite_restrict_support_of_integrable` in
`FLTForHuman/MeasureTheory/Integral/Prod.lean` — but the `v4.34.0` product-measure API cannot
consume it. A general-statement dispatch must first redevelop that API for non-s-finite measures;
it must not change the statement.

The headline `NumberField.TateGlobal.integrable_zetaIntegrand` and the downstream chain are
complete: the declaration's only consumer, `integrableOn_unitsOutside_norm_mul_ideleNorm_rpow`
(B:5190), states the step in a section that carries the Haar hypotheses, and the port inlines the
s-finiteness there. Any other `S_NumberField_TateGlobal_*` file needing the general form is blocked
on the same redevelopment.

### `AlgebraicCurve.linearIndependent_of_constantFieldExtension` — the unported second node

The landed node is
`AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed` (583 lines, silo rank 1)
in `FLTForHuman/AlgebraicCurve/IsCurveOver/ConstantFieldExtension.lean`. The pin proves the same
development a second time in `S_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean`
(579 lines, `[CharZero K]` in place of the separating-transcendental route); **17 of its 21
declarations are statement-identical** to the landed ones.

That second node is unported, is demanded by 16 nodes of the same cone, and cites nothing — a graph
leaf, so `frontier.py --ready` drops it by design and it appears only under `--include-leaves`
(`used_by` 16 / 19). Four further declarations (`algebraMap_mem_adjoin`, `exists_ringHom_adjoin`,
`isIntegral_algebraMap`, `transcendental_algebraMap`) are statement-identical in the unported
`S_AlgebraicCurve_genus_eq_of_constantFieldExtension_of_isAlgClosed.lean`
(lines 344/353/358/368) and want one home. Cut the two as one cluster; scope and prices are in
[topics/algebraicCurve/TOPIC-constant-field-extension.md](topics/algebraicCurve/TOPIC-constant-field-extension.md).

### `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` — the unported C2 row

Not a leaf: its one substantive proof step is the premise
`ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, which is unported — only the `CuspForm`
twin is (`FLTForHuman/ModularForms/WeightOne/Gamma1IntegralBasis.lean:871`) — and the twin cannot
substitute, because the headline's `f` is a `ModularForm (Gamma1 N) k` for arbitrary `k : ℤ` and
the cuspidal subspace does not span the Eisenstein part.

Unported closure under `--frontier sources`: **10 nodes / 5,172 raw `S_` lines** (8 `ModularForm` +
1 `WLight` + the row's 36), headed by `ModularForm.span_frickeRational_E4_pow_E6_pow_eq_top` (1,524)
and `ModularForm.exists_gamma1_frickeRational_sigmaTransport` (772), then the
`…_mem_adjoin_exp`/`…_eq_algEquiv_apply`/`…_mem_range_ratCast` steps and
`ModularForm.exists_mul_E4_pow_mul_E6_pow_eq_iff` (424). The default frontier prices the row at
1 node / 36 lines.

Needs its own definition-layer-first `ModularForm`-side work order, not a row on a `ModularCurve`
shelf. Reproduce:
`python3 tools/deps/frontier.py --target ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1 --frontier sources`.
Record: [topics/modularCurve/WORKORDER-C2-x1-function-field.md](topics/modularCurve/WORKORDER-C2-x1-function-field.md)
§2, §9, and the docstring of `FLTForHuman/ModularCurve/X1/IntegralityJqNModC.lean`.

### `WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`

The D row restated in two-curve form; do not transcribe the pin file. `port_advise` finds **107 of
its 183 declarations** already statement-identical in the port (≈2,077 raw lines; 76 trusted + 31
suspect), of which 26 of the 27 `private` hits are D-2's descent core in
`WeierstrassCurve/Isogeny/IntermediateField.lean` (`iA_*`, `iCa_*`, `iPFA_*`, `iPFE_*`, `iCa_K₀`,
`iP_xP`); 9 of the 31 suspect hits are the tool's type-only `def … : Prop` match against
`PeriodPair.DiscriminantNeZero`, where the `KwD5*` class wrappers are new and the match is not.
`port_plan` prices it at **1,975 net-new** lines, not 3,729.

Genuinely new: the two-curve case — `ι : E'.FunctionField →ₐ[K] E.FunctionField` between
*different* curves, `KwD5BetweenCurvesSubfieldDescent` — which occurs only in this file; every
`∃ K₀ …` in the port is one-curve. The new layer is the `hSD_*`/`cfe_*`/`ChiCompChiEqPhi` block plus
the `NoAC` engine (below), ≈1.1k lines by hand.

Work shape: generalise D-2's landed chain to two curves in place (the descent helpers are already
`private` in `IntermediateField.lean`, so it is a promotion plus a second curve), and let the
headline compose with D-5's. Its only consumer is the 415-line capstone
`eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`. Reproduce:
`port_advise.py --nodes WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`,
then `port_plan.py` on its `--json`.

### The uniformization gate's remaining columns

The gate's unported closure is **13 nodes / 11,880 lines**: the S family (seam/index) 6,537 and the
D-descent family 4,764 (the D family has since landed). The j-line is on the `DeligneSerre` capstone
cone — `frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` lists
14 unported `PeriodPair.*` nodes / 9,071 lines, `jLattice_surjective` among them. Measurement:
[topics/velu/TOPIC-V5-periodpair-uniformization.md](topics/velu/TOPIC-V5-periodpair-uniformization.md)
(15,179 lines; the two classical theorems are on the path, not prelude).

Note: the port's `ModularForms/WeightOne/Defs/PeriodPair.lean` is a **different** object — the
weight-one prelude `periodPairOfTau`/`smulPeriodPair` over mathlib's `PeriodPair` struct.

### The rest of the `AutomorphicForm.LocalIntertwining` cluster

Two of the 19 nodes are ported — `integral_unramifiedWeylIntegrand_adicCompletion` and
`integral_smoothWeylIntegrand_adicCompletion`, sets LI-1/LI-2, with their prelude
(`TateGlobal/{WeylPrelude,WeylShell}.lean`); record:
[topics/automorphicForm/TOPIC-local-intertwining-weyl-integrand.md](topics/automorphicForm/TOPIC-local-intertwining-weyl-integrand.md).
The prelude is now in the port, so the rest are their own new files. Remaining, by the cluster's own
import order:

- **layer 0** — `integral_one_add_norm_sq_cpow_neg_eq_pi_div`,
  `integral_one_add_sq_cpow_neg_eq_GammaReal_div`,
  `integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg`,
  `exists_bound_norm_integral_mixedSpace_archAtom_prod`,
  `integrable_{complex,real}Atom_and_integrable_moebiusShift`, the two
  `bounded_and_tendsto_integral_{weylShift_sub_integral_smoothAtom_adicCompletion,moebiusShift_sub_integral_*Atom}`,
  the two `tendsto_integral_{normSq_rpow_sub_one_mul_complexAtom,sq_rpow_sub_one_mul_realAtom}_nhdsGT_one_half`
  — 5–25 declarations each, and a 13-declaration shared block between
  `bounded_and_tendsto_integral_weylShift_…` and `integrable_smoothAtom_and_integrable_weylShift_adicCompletion`;
- **layer 1** — the two `moebiusShift` rows,
  `exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion`,
  `exists_one_sub_mul_integral_smoothWeylIntegrand_eq_sum`,
  `integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` (1,291 lines, its own
  5-declaration block), `integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg`,
  `integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` (465);
- **layer 2** — `integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`.

### `Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean` — the remainder

Only `higherUnitsAt` is ported (with the smooth headline, in `TateGlobal/WeylSmooth.lean`; the pin
file is in `SOURCES` for that one declaration). The rest of the module — `HasConductorExponentAt`,
`conductorExponentAt`, … — is unported; port the node whole when a consumer needs it.

### `ofReal_pow_cpow` — two `private` re-proofs beside a public port copy

`TateGlobal/WeylShell.lean` and `TateGlobal/WeylSmooth.lean` each re-prove it `private`: the public
port copy at `NumberTheory/NumberField/TateGlobal/EulerFactors.lean:80` is the same identity with the
binders `(x) (m) (s)`, while the LocalIntertwining pin spells them `(a) (s) (k)`, and a `private`
declaration is not importable. Unifying them means generalising the public copy's binders, which
edits a frozen module.

### 23 orphan phantoms — pin headlines the port states only from behind `private`

Found and sized 2026-10-20 ([logs/phantom-landings.md](logs/phantom-landings.md)); the instance that
exposed them (`CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three`) is **landed** in
`NumberTheory/ModularForms/Gamma0Three.lean`, as are `ModularCurve.nuThree_prime` and
`nuThree_mul_of_coprime` in `ModularCurve/Numerics/NuThree.lean`.

`frontier.py`'s `names` tier counts `private` declarations as ported, so a pin headline whose only copy
is `private` leaves the demand while nothing can import it and no checker has diffed it. Scanning every
port module's private declarations against the pin's public `Theorems/` statements
(`tools/deps/phantom_scan.py`, untracked; method in the log) leaves **23, in 14 modules**:

```
Algebra/FaithfulLatticeEigenvector.lean:98             Module.exists_ne_zero_forall_smul_eq_smul_of_algHom
AlgebraicCurve/IsCurveOver/FrobeniusSubfield.lean:386   AlgebraicCurve.existsUnique_pDigits_of_transcendental
AlgebraicCurve/P1/DivisorAction.lean:21                AlgebraicCurve.Place.ord_add_eq_of_lt
AlgebraicCurve/WeilExchange/Transport.lean:293         AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg
ModularCurve/Analytic/Gamma0InvariantCore.lean:116     ModularCurve.PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq
ModularCurve/Analytic/Gamma0InvariantCore.lean:133     ModularCurve.PhiGen.exists_galoisPerm
ModularCurve/Analytic/Gamma0InvariantCore.lean:153     ModularCurve.PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter
ModularCurve/Degree/Roof.lean:61                       ModularCurve.finrankAlong_heckeBetaBar
ModularCurve/Degree/Roof.lean:140                      ModularCurve.finrankAlong_towerInclBar_of_eq
ModularCurve/Degree/Roof.lean:150                      ModularCurve.finrankAlong_towerSubstBar_roof
ModularCurve/Degree/Roof.lean:220                      ModularCurve.laurentBaseChange_adjoin_pair
ModularCurve/ModularPolynomialStarBank.lean:82,88,93   ModularCurve.coeff_jqModC_{pow_self,pow_of_lt,neg_one}   (privated twice: also X0/FunctionFieldFull.lean:82,88,93)
ModularCurve/PhiGenIntegrality.lean:232                ModularCurve.PhiGen.intCoeffs_jq_pow
ModularCurve/PhiGenPoleBounds.lean:270                 ModularCurve.PhiGen.tPoleOrderLE_phiProd_conj_of_ne_zero
ModularCurve/X1/IntegralityJqNModC.lean:89             ModularCurve.qExpansion_E6_eq_map_mk
ModularForms/Hauptmodul.lean:342                       ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty
ModularForms/JqAnalyticModel.lean:570                  ModularCurve.hasSum_jNum_qParam
WeierstrassCurve/IsogenyEndDatum/DualEndData.lean:63    WeierstrassCurve.finite_torsionBy_of_natCast_ne_zero
```

The fix is per node a one-line `private` → public where the statement is the module's own subject, or
a lift into a subject module where it is not — plus the same `spec-pin:` wiring. Sixteen of the
twenty-three are the `ModularCurve` q-expansion / `PhiGen` / degree layer, so one order can take them
as a family. **Do not schedule them off `--ready`-style pricing:** the demand does not currently show
them at all (that is the bug). The batched dependent wave for these refactors is owed and recorded in
[logs/build-time-issues.md](logs/build-time-issues.md) §3b.

The **29 `twin`** hits are *not* on this list: a public declaration elsewhere already states the same
theorem under another name (the pin's `solution`/`impl` wiring, e.g. `Saturation.main`). Leave them.

## Open follow-ups

### `lean_parser.ENCLOSE_RE` swallows a bare `end` followed by `end Name` — full names key one frame too deep

**Open.** `spec/lean_parser.ENCLOSE_RE` matches an `end` and then, optionally, `\s+` plus its name; the
`\s+` crosses newlines, so

```lean
end          -- closes a section
end Foo      -- closes a namespace
```

is read as one event whose endname is the word `end`, and the `end Foo` is swallowed. Every
declaration after it is keyed one frame too deep — observed in
`AutomorphicForm/Adelic/FactorizableTestFnArchSmoothComplex.lean`, where the private twin first came
out as `…IsFactorizableTestFn.Complex.AutomorphicForm.IsFactorizableTestFn.solution`, which is why that
module's engine section is *named* (`section E8Engine`). Matching is by last name and content hash, so
no verdict is wrong today; the damage is confined to full-name keys — `spec/decl_markers.tsv` rows, the
corpus's name column, and any tool that resolves a full name. Exposure, measured 2026-10-23:
**82 adjacencies in 62 port files**, 1,662 in 1,211 pin files.

**Fix.** `\s+` → `[ \t]+` in the two name groups of `ENCLOSE_RE` (and `(?P<indent>\s*)` → `[ \t]*`).
Then rebuild the corpus — `python3 spec/statement_db.py build`; the stamp carries the parser digest, so
every cached verdict invalidates — and re-run `check_port --all` plus `--strict-markers`, expecting
0 mismatch / 0 missing / 0 stale. **Workaround until then**: name every `section` (`section Foo` /
`end Foo`), which makes both `end`s explicit.

### The AC3 engine carries the pin's engine tokens — a checker rename map, then one rename pass

**Open.** `AutomorphicForm/Adelic/ArchCompactOrbit.lean` and `ArchCutProjector.lean` (landed
2026-10-22) ship their public surface under the pin's spellings: `Ecf`, `ρc`, `QM`, `Qc`, `CA`, `CB`,
`projCA`, `goodComponents`, `cutc`, `cutM`, `underSub`, `archRep`, `ArchIsometryProd`, `ℂK`. The target
spelling is [WORKORDER-AC3](automorphicForm/WORKORDER-AC3-arch-cut-projector.md) §3; why they were
kept, and the mechanism that unblocks a rename (a `pin:`-driven rename map applied to the pin side of
the comparison before hashing), are in that order's §3 and §9. **Price**: ~20 lines in
`spec/check_port.py` plus a `--selftest` case with a renamed type inside a statement; then the
fourteen names move in one pass (79 statements, no mathematics), the `pin:` rows are re-pointed and
the two module headers updated. **Trigger**: the pass that opens these modules for another reason —
both sibling consumers (`exists_linearMap_archCutProjector`,
`exists_rightConv_eq_of_archCutProjector`) are unstarted, so the churn is at its minimum today and
grows with the first import.

### `typeSubmodule_eq_typeSpan` is one codomain short — a generic bridge at arbitrary `G`

`AutomorphicForm/Adelic/RightConvComm/SliceCentrality.lean:76` states the type-submodule ↔ type-span
dictionary for `e : H →* GL (Fin 2) (InfiniteAdeleRing F)`, but the archimedean cut lives on
`AdelicGL2 (𝓞 F) F`, so it does not apply there. `AutomorphicForm/Adelic/ArchCutProjector.lean`
(landed 2026-10-22, [WORKORDER-AC3](automorphicForm/WORKORDER-AC3-arch-cut-projector.md) §9) carries a
`private` twelve-line adapter, `typeSubmodule_eq_typeSpanOf`, at arbitrary `G` — the same proof with the
codomain generalized. The generic form (`e : H →* G`, both groups arbitrary) belongs beside
`typeSpan`/`rightRep` in `RepTheory/BiIsotypic.lean`, where the port's generic representation theory
lives; the adapter then goes. Price: an edit to an existing module, so a manager's call with
`tools/deps/build_ladder.py --edit` (twelve lines plus its wire) — **no statement of an existing module
changes**, so the checker is unaffected. Take it when a second cut consumer appears, or when
`BiIsotypic` is opened for another reason. Known not to be needed yet: `exists_rightConv_eq_of_archCutProjector`'s
pin file carries no `Qc`/`projCA`/`cutc`, so that sibling imports `ArchCompactOrbit` and not this bridge.

### The `Γ₁` slash/level toolkit has a home; the copies it replaces are still in place

`FLTForHuman/ModularForms/Level/Gamma1Slash.lean` landed 2026-10-20 as the home of the block the
pin carries as `section Level` of
`S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean`: `ΓGL`,
`restrictF`/`coe_restrictF`, `resLevel`/`coe_resLevel`, `resSL`/`coe_resSL`, `le_conj_of_SL`,
`slashForm`/`coe_slashForm`, the four property transfers `periodic_slash`,
`mdifferentiable_slash`, `bdd_slash`, `analyticAt_slash`, and the `Γ₁` facts `T_mem_Gamma1`,
`one_mem_strictPeriods`, `L_mem_strictPeriods_Gamma`, `Gamma_le_Gamma1` (18 declarations, wired to
the pin file, checker 18 ok). It is **not** a consolidation: the copies below were left in place,
because each sits inside a silo that the port transcribed whole and folding them in is a wave of
its own, to be taken when one of those modules is opened for another reason.

- `restrictF` (`restrictForm` elsewhere): **public at its pin home**,
  `ModularCurve/X1/Defs.lean:53` (+ `coe_restrictForm`, `restrictForm_apply`) — the pin's
  `Restrict` block of `Definitions/Def_ModularCurve_X1.lean`, where it belongs; `private restrictForm`
  at `WeightOne/Gamma0Integral.lean:1349`; `private restrictMF` at `Level/Degeneracy.lean:44`.
  Two private copies of a six-line `ModularForm` constructor remain.
- `T_mem_Gamma1`: public at `WeightOne/Defs/GammaRational.lean:262`,
  `Elliptic/PeriodPair/InvariantsTorsion.lean:1119`,
  `ModularCurve/X1/AtkinLehnerExchange.lean:1241`,
  `ModularForms/Eisenstein/WeightOneMultiplier.lean:645`; private at
  `ModularCurve/X1/Inputs.lean:154`, `HeckeEigenNebentypus.lean:120`.
- `one_mem_strictPeriods`: **the fact is mathlib's** — `Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem`
  for `T ∈ Γ`, and `@[simp] CongruenceSubgroup.strictPeriods_Gamma0`/`strictPeriods_Gamma1` for the
  level instances — so no home and no promotion is wanted: it is a `simp` at the call site
  ([logs/qexp-definition-layer-homes.md](logs/qexp-definition-layer-homes.md) §3). 37 copies remain
  (95 proof lines; 34 of them 1–2-line `simp`/`rw` spellings, the one real re-derivation being
  `ModularCurve/X1/FunctionField.lean:361`). A copy never earns a *promotion*; what it may keep is
  its `by simp` body. The working rule, refined: a single site writes `by simp` and no lemma; a
  `private` one-liner used twice or more in one file may stay (one elaboration in the olean instead
  of N `simp` calls, one point of repair, readable call sites) provided the body is `by simp`; a
  public copy stays only where a pin file states it, and a consumer that needs the fact should write
  `by simp` rather than import the module for it.
- `Gamma_le_Gamma1`: public at `Analytic/NormSqPow.lean:121` and `Defs/GammaRational.lean:272`;
  private at `Gamma0Integral.lean:1959` and `Gamma1IntegralBasis.lean:120`.
- `mul_inv_mem_Gamma1`: private at `X1/DiamondAut.lean:122` (the `γ 0 0` variant) and
  `Gamma0Integral.lean:1460` (the `γ 1 1` variant — the one the pin states).
- `slash_of_neg_mem`: private at `Gamma0Integral.lean:1750`.
- `coe_Eaux`: `Gamma0Integral.lean`'s copy is `private`, so `ModularForms/FrickeReciprocity.lean`
  writes its own two-line copy. That is the FR1 set's **single added twin** in the shape index
  (`shapes.py` on the landed module: 59 theorem/lemmas, one port twin, `coe_Eaux`); promote the
  host's copy in the wave that folds this block.
- `frickeConj`: now public at `ModularForms/HeckeFrickeTrace.lean`
  (`ALTraceIdentity.frickeConj`, appended 2026-10-20 at the pin's `[NeZero L]` signature, with a
  `pin:` row in `spec/decl_markers.tsv`). Two private spellings remain —
  `HeckeFricke.lean:274` (`(p) (g) (hg)`) and `HeckeNebentypusFricke.lean:80` (`(γ) (hγ)` under a
  section variable). They are the same conjugation in three spellings; unifying them means
  rewriting `HeckeFricke`'s call sites, which is not worth it for ten lines. Note when folding:
  the pin's `diagGL (t : ℝ) (ht : 0 < t)` is `Defs/HeckeOperator.heckeDiagMatrix` at a real
  parameter — if a second consumer ever needs the real form, generalise that hub rather than
  copy the pin's version again.

The same file also carries **two different `IsRat`s**: public at `Gamma0Integral.lean:1360`
(`∀ n, ∃ r : ℚ, q.coeff n = (r : ℂ)`, the pin's) and private at `:359`
(`∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = φ`). They are equivalent but not defeq, and a
consumer that opens the wrong namespace proves against the wrong predicate.

### Two promotion candidates the Gauss-prolongation set left closed

Both are in `X1/FunctionFieldResidue.lean`'s reach but not in its surface, so the set that needed them
re-derived them `private` ([logs/qexp-regular-prolongation.md](logs/qexp-regular-prolongation.md)):

* `ModularCurve.laurentBaseChange_le` — `laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ≤
  qExpFunctionFieldC L Γ`, the pin's own 17-line lemma (`S_:301–320`), re-derived `private` in
  `X1/QExpRegularProlongation.lean`. Its home is beside `laurentBaseChange_le_adjoin_gensZ`
  (`FunctionFieldResidue.lean:264`), which is only the *`gensZ`* strengthening; the
  `intFormRatiosC`-target inclusion exists nowhere in that closure (`Degree/LaurentGlue.lean:221`
  proves the stronger equality but is not in the closure). Every future consumer of the pin's
  `exists_frac_form` re-derives it until it is promoted.
* The seven Gauss-block helpers the engine dropped and the new module carries `private`:
  `coe_LamSub` (pin:188), `resHom_apply` (:550), `ι_mem_gaussRing` (:556), `resHom_ι` (:559),
  `ker_resHom` (:594), `coe_smul'` (:636), `exists_smul_mem_gaussRing` (:640). Promote into
  `QExpDeuring` in one pass, with the usual price — they are one block, and the wave is the same
  price for one move or seven. Note when promoting: `gaussProlongation` must stay an `abbrev` (a
  plain `def` breaks the sibling assemblies' `change`/`rw` at `implicit` transparency).

### The `mapGL` entry lemmas have no library home

`mapGL_apply`, `val_mapGL_eq`, `mapGL_injective` and `det_entries` live with their modular-forms
consumers in `FLTForHuman/ModularForms/Analytic/PeterssonCoset.lean`. The group-theory module
`GroupTheory/ModularGroup/FreeProduct` used to import that module for `det_entries` — a dependency
inversion, broken 2026-10-20 by a private local copy (the pin restates the same five lines) — and a
single library home, `LinearAlgebra/Matrix/SpecialLinearGroupMapGL.lean`, is the proper fix once
the five consumers (`Analytic/NormSqPow`, `HeckePrelude`, `SturmBound`, `Analytic/PeterssonCoset`,
and the private copies in `ModularGroup`/`Gamma1Vanishing`) are updated together. Do not move them
piecemeal: the four are general `SL(2, ℤ)`/`mapGL` facts, but moving them changes every unqualified
reference reached through `open CuspForm.PeterssonCoset`.

### `AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional`

Landed at `FLTForHuman/AlgebraicCurve/IsCurveOver/EssFiniteType.lean`. Its consumer test
(`spec/AlgebraicCurveConsumer.lean`, Zone L) is hypothesis-form: the concrete witness
`F = ↥K⟮X⟯` needs the subtype coercion of `RatFunc.X` through `RatFunc.transcendental_X`'s `K⟮X⟯`
notation. The node has no ported consumer — the pin's consumers are the `essFiniteType_*` targets
— so it is a pre-payment, not a link in a chain.

### Patching `class` binder spelling

Four deviations are exempted by dotted name in the checker's `OWN_PROOFS`, all in
`FLTForHuman/Patching/PatchingConstruction.lean`:

- `IsLocalRing.IsAdicTopology` writes `(R)` where the pin
  (`Definitions/Def_Patching_SystemTypes.lean`) writes `(R : Type*)`;
- `Algebra.TopologicallyFG` and `IsPatchingSystem` spell their binders through surrounding
  `variable`s where the pin is explicit;
- `PatchingAlgebra.smulData` has no textual counterpart under that name.

The Patching effort should re-spell the three binders as the pin does and re-home or rename
`smulData`, which removes the exemptions.

### Duplicate `private` norm-formula blocks

Char-free fibre-centre norm formula, two byte-identical `private` copies:
`ord_norm_eq_sum_fiberOver` (29 lines) and `pushforwardNormFormula_of_finiteDimensional` (17
lines), at `AlgebraicCurve/PrincipalDivisors/Transcendence.lean:309`/`:345` and
`WeierstrassCurve/Velu/RestrictAlong.lean:1713`/`:1749`. They cannot be retired by pointing
`Transcendence.lean` at the public home: `Velu/RestrictAlong.lean` already reaches
`Transcendence.lean`, so that would be a cycle. Retiring them means extracting the char-free
formula into a module **below** `Transcendence.lean` and rebuilding that cone once (52-module
cascade, measured); until then both private bodies stay.

`ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal`, statement-identical `private` copies at
`AlgebraicCurve/PrincipalDivisors/Transcendence.lean:138` and
`WeierstrassCurve/Velu/RestrictAlong.lean:1547` (about `v.ord` for a curve's place, unrelated to the
DVR order). Waves are lopsided: `build_ladder.py --edit` prices the `Transcendence` side at
**81 modules / 49,336 lines ≈ 598 s** and the `RestrictAlong` side at 2 modules / 670 lines ≈ 34 s.
Cheap shape: a public home beside `ord` in `AlgebraicCurve/Defs/Place.lean` with both consumers
importing it.

`AlgebraicCurve.Place.isRational_of_deg_eq_one` is public at one FQN in two modules —
`AlgebraicCurve/P1/Dictionary.lean:59` and `WeierstrassCurve/Velu/Discharge.lean:38` — with
byte-identical bodies, so the two modules *are* co-importable (Lean merges identical declarations
silently) but the tree carries two copies. Dedup: keep the lower `P1/` copy, delete or alias the
`Velu/Discharge.lean` one. Same family: `finite_setOf_ord_ne_zero_of_finiteDimensional`
(`P1/EnginePrelude.lean:652` public vs `PrincipalDivisors/Transcendence.lean:387` private).
`Velu/Discharge.lean` is the larger cascade.

### The second-order `XYIdeal` block (`IsogenyEndDatum/DualEndData.lean`)

`DualEndData.lean` carries a generic second-order-at-a-point development:
`derivative_polynomial`, `evalEval_eq_zero_of_mem_span`, `evalEval_derivative_eq_zero_of_mem_span_sq`,
`exists_eq_add_mul_polynomial_of_mem_XYIdeal_sq`, `X_sub_C_dvd_eval_of_mem_span`,
`X_sub_C_sq_dvd_eval_of_mem_span_sq`, `XClass_notMem_XYIdeal_sq`, `ord_placeOfEquation_XClass_self`
and the `ord_ofHeightOneSpectrum_*` family (`:1134`, `:1360`, `:1387`–`:1478`). None is
`IsogenyEndDatum`-specific; the V3 node
`WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add` needs two members of it.

The current cost is `TranslationAlgEquiv.lean`'s import of `DualEndData` (1 m 21 s fixed per
`lake env lean` check, against 23.5 s for the `Engine`-only cone). Trigger for the refactor: when a
third cone needs the block, extract it to a module under `Place/` below `DualEndData` and drop that
import. Price: `build_ladder.py --edit DualEndData.lean` (5 modules / ≈119 s) plus the new home's
dependents.

### The `General`/`NoAC` engine split (`KernelBaseChange.lean`)

`KernelBaseChange.lean:133–420` is landed `General`-only — its section carries `[IsAlgClosed F]
[IsAlgClosed F']` and four `GenusOnePlaceGate`/`IsCentred`/`AbelTheorem` blocks — so it cannot be
instantiated at a subfield. The two-curve descent needs it at `F = K₀`, and therefore transcribes
the pin's `NoAC` engine `private` (≈320 lines). D-1 resolved the same split in the function-field
prelude by making the `NoAC` name the primitive and each `General` name a one-line invocation.

Refactor: restate the engine's section gate-free (`kw_surge_hgf4_bcTensorIota`,
`…bcTensorFracIota`, `…bcTensorFracIotaAlg`, `…bcIota₁`, `…bcTensorFracIotaSeam`,
`…bcIota₁_{finiteAlong,isIntegral,finrankAlong,compat}`), keep the `General` names as one-line
invocations of the gate-free ones, delete the private copies and re-point their file at the
imports. The two D-5 headline statements do not move. `KernelBaseChange.lean` is a leaf, so the
cascade should be small; price with `build_ladder.py --edit`. Do not reopen
`Isogeny/TwoCurveDescent.lean` mid-set.

Related measurement: `gateDescent_of_descent` carries the pin's
`set_option maxHeartbeats 48000000` / `synthInstance.maxHeartbeats 8000000` and ≈120 lines of
`⁄`-spelling instance/`Eq.trans` scaffolding (`S_:2882–2885`); re-measure it if the engine promotion
happens.

### Deprecated-name sweep in frozen modules

The milestone build prints deprecation warnings from frozen port modules:
`WeierstrassCurve/Velu/OrderTwo.lean:224` (`dif_neg` → `dite_eq_right`) and `:452`
(`linter.style.haveILetI` on the pinned `haveI` in `veluQuotient2_j`'s statement), plus `if_neg`/
`if_true`/`TensorProduct.induction_on`/`TensorProduction.inductionOn` in
`WeierstrassCurve/IsogenyEndDatum/DualEndData.lean` and `Isogeny/TwoCurveDescent.lean`. Lake replays
their cached logs, so they do not recompute. New modules of every set are 0-warning; the debt is in
the older ones only. Sweep a maintenance round, one file at a time, priced with
`build_ladder.py --edit`, never mid-set.

### Narrowed linter suppressions are house style

The subject-A modules carry 15 `set_option linter.* false in` suppressions (13
`unusedSectionVars`, 1 `style.haveILetI`, 1 `unusedVariables`), each on a single declaration. They
are forced: Lean auto-includes `[NeZero N]` in a signature when the *value* uses it but the *type*
does not, the linter then reports it unused, and `omit [NeZero N] in` is refused
(`cannot omit referenced section variable`). The pin sets `linter.unusedSectionVars false` /
`linter.unusedVariables false` in 7 of these 8 `S_` files
(`S_ModularCurve_LevelN_isDomain_ring.lean` excepted), and ~190 other port modules set them too. A
work order's "no `set_option linter.*` suppression" line means *no file-wide suppression and no
suppression of a real warning*; each narrowed use is recorded in the set's report.

### Tier-3 theories not in `PORT_FILES`

The completed Dedekind zeta package (`NumberField.exists_completedDedekindZeta_package`, 7,555 pin
lines / 388 public declarations, one consumed headline) is ported as a natural-named theory in
`FLTForHuman/NumberTheory/CompletedDedekindZeta/` plus a thin listed façade carrying the headline.
Its ten pin consumers and the two sibling silos that re-declare the same obligation vocabulary stay
unported by design. Order:
[topics/numberTheory/WORKORDER-Z1-completed-dedekind-zeta.md](topics/numberTheory/WORKORDER-Z1-completed-dedekind-zeta.md).

The cell-dissection / radial-region cluster
([topics/algebraicCurve/TOPIC-cell-dissection.md](topics/algebraicCurve/TOPIC-cell-dissection.md))
is ported the same way. Its pin `S_` files declare the development's lemmas public
(537 across the nine `RadialRegion` nodes, more in the `CellDissection` half); per
playbook §0.5/§4.1 they stay public and stay unwired, in per-node tier-3 engines
`AlgebraicCurve/RadialRegion/Engine/<Node>.lean` (registered with `-- pin:`
provenance), with a thin listed façade `AlgebraicCurve/RadialRegion/<Node>.lean` per
node carrying the wrapper headline. First order:
[topics/algebraicCurve/WORKORDER-R1-radial-rectangle.md](topics/algebraicCurve/WORKORDER-R1-radial-rectangle.md).

## Cleanup families

### Four pin-chapter namespaces still in use

Four modules declare under the pin's transcription-device namespaces, which name a chapter rather
than a theory:

| namespace | declared in | reference sites | consumer modules |
|---|---|---|---|
| `P6B` | `AdelicHaar/AdelicModulus.lean` | 9 | the modulus façade |
| `M4aS4` | `AdelicHaar/{AdelicModulus,PlaceMeasure}.lean` | 6 | `AutomorphicForm/Adelic/WeylIntegrable/{Assembly,LatticeEstimates,UniformBound}.lean` + the two declarers |
| `FltWs24` | `AdelicHaar/ProductFormula.lean` | 5 | the modulus façade |
| `M4aLocalCFT` | `NumberField/TateGlobal/FujisakiCompact.lean` | 59 | most of the T1 `TateGlobal/*` cluster |

Merging one into an existing theory namespace (`NumberField.AdelicHaar`, `NumberField.TateGlobal`)
is the case playbook §3.2 warns about — two chapters can hold the same declaration name with
different statements — so each rename needs a collision check before the wave, and the
`M4aLocalCFT` one is a 59-site job over a frozen cluster. Do them as their own wave when the owning
cluster is next active, keeping every last name so the checker's dotted fallback still matches.

### The WeightOne dedup is closed

`port_graph.py --blocks 20` reports no weight-one cluster; the port's only block is 234 lines and
unrelated (`Transcendence ↔ RestrictAlong`). The statement-identical residue is **14 lines**. The
"≈7,242 removable lines" figure is the pre-rectification, name-based baseline in
`tools/deps/README.md` and is not outstanding work. Current numbers:
[topics/hecke/TOPIC-weightone-rectify-closeout.md](topics/hecke/TOPIC-weightone-rectify-closeout.md).

### Tool hazards

- **`frontier.py` credits a `spec-pin:` header before the module is green.** The `sources`
  tier now reads the `spec-pin:` lines of the port tree, so a node counts as ported as soon
  as the header exists — including while the module is still half-written and does not
  compile (the `names` tier behaves the same way: a partial file already declares some
  names). Harmless for the final reading, misleading mid-wave: do not trust the frontier
  between dispatch and review, and use `check_port` as the gate.
- `spec/unwired_register.py --json` rewrites `lean/spec/UNWIRED-PUBLIC.md` unconditionally, even
  with `--json` — a read-only-looking invocation still writes the register (it is git-ignored
  now, so only the working tree is touched). Use `--check` unless the register is meant to be
  regenerated.
- Re-running `port_advise` on a pin file **after** its engine has landed reports the engine's own
  declarations as substitutions (the tool scans the whole port tree, so every transcribed
  declaration matches itself). Use the advise file generated before the module was written, or
  exclude the new module.
- The checker's `DECL_RE` admits only `private`/`noncomputable`, so a `scoped instance` is
  invisible to `raw_declarations`: `unwired_register.py` skips it (the P1 prelude registers 121 of
  its 124 declarations — `A` 68/70, `B` 53/54), and the statement checker would not diff it if its
  module were wired. The three are present, public and pinned. Teaching the tracked checker to see
  `scoped` changes the global checked surface and needs its own pass with `--selftest`; record in
  `logs/ac-port.md` §13. (The companion defect — `unwired_register.py` dropping the `_root_.`
  absolute prefix, which mis-homed ~161 register rows — was fixed 2026-10-14.)
- `unwired_register.py`'s namespace tracker (`NS_EVENT`) did not admit a modifier before
  `section`, so a `noncomputable section` frame was never pushed while its closing `end` was
  popped — silently dropping the enclosing namespace from every later row (the R3b
  `GridGeometry` engine had ~100 wrong importable names; the port worked around it by writing
  the four `Finset ℂ` defs `noncomputable` and dropping the section). Fixed 2026-10-14:
  `NS_EVENT` accepts an optional `noncomputable|private|protected|public` modifier.
- The same tracker mis-homed 36 `RadialRegion/../ValueDictionary.lean` rows to
  `AlgebraicCurve.Place.AlgebraicCurve.Place.…`: `raw_declarations` prefixes the enclosing
  namespace to a `_root_.`-absolute name, so the right rule is to take the text *after*
  `_root_.` (fixed 2026-10-14), not to substitute it in place.
- The checker's `strip_comments` removes only block comments (`/- … -/`), not `--` line
  comments, while `top_level_cut` finds no `:=` in an equation-style `def` — so a `-- pin:`
  line above the *next* declaration is absorbed into an equation-style def's statement. Harmless
  today (only unlisted tier-3 engines carry per-declaration `-- pin:` comments, and the register
  does not compare statements), but a wired module with that pairing would report a spurious
  mismatch. Fixing it means stripping `--` comments in the tracked checker and re-running its
  selftest; deliberately not a rider on a set (see `logs/ac-port.md` §13).

### Co-import constraint: the gate producer and `Engine`

`WeierstrassCurve/GenusOnePlaceGateCentred.lean` (the producer
`exists_genusOnePlaceGate_isCentred_and_abelTheorem`) cannot be co-imported with
`WeierstrassCurve/IsogenyEndDatum/Engine.lean` — both reach a declaration of
`WeierstrassCurve.Affine.instInfinitePlace`, and no environment holds the two. A consumer that
*produces* the gate instances and one that uses `Engine` must therefore stay in separate `spec/`
files until one instance is reconciled; the capstone
`ModularCurve/ModularPolynomialEvalJ.lean` holds both because it reaches the producer without
importing `Engine`. Rule for the column:
[topics/velu/WORKORDER-P2-basechange.md](topics/velu/WORKORDER-P2-basechange.md) §3.1.
