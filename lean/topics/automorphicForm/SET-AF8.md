# SET-AF8 — right convolution stays in the cusp subrepresentation: a **composition** set, queued

**Status: queued 2026-11-02, not dispatched.** Scoped from measurements only; no Lean was written for
it. It is the row SET-AF5's headline was written for, and it is the column's clean test of the *other*
strategy: this node is **78% already in the port**, so it is a composition set (~840 written lines),
not a transcription set. Dispatch it with
[WORKORDER-AF8-cuspsubrep.md](WORKORDER-AF8-cuspsubrep.md) when the column picks it up.

## 0. The row

`AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep` — **3,833 silo**, **ready** since
SET-AF5 (its only unported premise was `continuous_rightConv_and_contDiff_of_isFactorizableTestFn`,
landed there), premises 3, leverage 1 / 2, readiness return 0. It is the `RepTheory` ↔ `Cusp` bridge:
a right convolution by a factorisable test function of a right translate stays inside the cuspidal
subrepresentation.

## 1. Why this is *not* a mechanical whole-node port

`port_advise` on the row, and the same measurement on SET-AF7's bigCell node for contrast:

| | **SET-AF8** (cusp-subrep) | SET-AF7 (bigCell) |
|---|---:|---:|
| pin lines | 3,833 | 5,407 |
| declarations | **224** | 458 |
| **already in the port** (tier-1, diffed) | **3,015 lines — 78%** | 612 lines — 11% |
| of which **public / importable** | **183 of 185** | n/a (they are not the same theorem) |
| within-file duplicate copies | 39 lines | 0 |
| **net new** | **757** | 4,753 |
| new declarations to write | **50** (837 lines) | 458 |

So the strategy flips. bigCell's prelude was its own, and a mechanical transcription had nothing to
compose (0 within-file duplicates, 11% overlap) — port the text, dedup after. Here the prelude **is**
the port's engine, ported in earlier waves as engines for other rows, under homes whose subject is the
engine and not this row:

| port module | matched declarations |
|---|---:|
| `RepTheory/TypeReproducer.lean` (1,306 lines) | **67** |
| `AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean` | **50** |
| `…/ArchApproxIdentity/EntryBall.lean` | **31** |
| `RepTheory/ConvolutionLimit.lean` (660 lines) | **24** |
| `…/ArchApproxIdentity/Instantiate.lean` | 8 |
| `GroupTheory/BassSerre/MinimalPeriod.lean` · `Adelic/TestFnNearIdentity.lean` · `Adelic/TestFnTop.lean` (2 **private**) | 5 |

Transcribing those 3,000 lines would manufacture duplicates that `dedup` is very unlikely to catch —
it is name-anchored, and the pin's names (`main`, `aux_*`, `tendsto_integral_mul_dconvWith`) have no
port twin at all. That is the AF6 lesson (491 lines per file invisible to a rename) at six times the
scale, with the sign reversed: there the promotion made the reuse real, here a mechanical port would
make it fake.

**The rule this pair establishes** (FR-0109): port overlap ≤ ~20% of declaration lines → mechanical
whole-node port (SET-AF7); ≥ ~50% → composition: import the engine and write only what is new. One
`port_advise` run decides, and it is the *first* thing to run on any large row.

## 2. What has to be written: 50 declarations / 837 lines

A tight cluster, all `aux_*`-prefixed in the pin and all new: the `dconvWith` dominated-convergence
core, the convolution kernel's existence, the tensor form, the `convOpOn`/`convDomain` glue, the
row-isometry quantifier, and the 68-line headline. Appendix B is the full list with spans.

## 3. The plan (one worker order, ≈840 lines)

| step | what |
|---|---|
| **W1** | new `FLTForHuman/AutomorphicForm/Adelic/Cusp/RightConvSubrep.lean` (0 importers, cascade-free): import the engine (§4), transcribe the 50 new declarations from the pin's `S_` file, state the headline at its `Theorems/` wrapper |
| **W2** | gates: `check_port --force` **1 ok / 0 mismatch / 0 missing**; axioms; the module's own build silent under `flock`; `dedup --within` (expect ~0 — nothing is copied twice) and `--cross`; `move_dead` triaged by the rule (dead math → `Reserve`, duplicate/plumbing → delete) |
| **W3** | a `spec/AutomorphicFormSetAF8Consumer.lean` zone composing the headline with SET-AF5's continuity |

**Home.** `Cusp/RightConvSubrep.lean`: the subject is the cuspidal subrepresentation
(`Cusp/Constituent.lean` holds `IsCuspSubrep`, `Cusp/SpectrumSubrep.lean` the lift/closure datum), and
the row is above `RightConvRegularity` (its premise) and above the `ArchApproxIdentity` engine. A new
module rather than an insertion: `SpectrumSubrep.lean` is below the engine's `Instantiate` layer.

## 4. The import surface (the reason the order is cheap)

183 of the 174 matched declarations' copies are **public**, so the order's ground is an import list,
not a transcription. Appendix A is the whole map (pin name → port declaration → module → pin lines),
largest first. Two caveats for the worker:

* **2 of them are `private`** in `Adelic/TestFnTop.lean` — promote them (they are local spellings of
  `continuous_ringEquiv_mixedSpace`-class facts) or re-state them locally; decide after reading their
  statements (FR-0101's rule: promote and delete the local copy if the port's is the same statement).
* **`main` (158 pin lines) is `ArchApproxIdentity.exists_tendsto_integral_of_mem_archCutSubmodule`**
  and **`tendsto_integral_mul_dconvWith` (158) is `ArchApproxIdentity.tendsto_integral_mul_dconvWith`**
  — the two biggest single imports, i.e. a third of the file arrives by two names. Check their
  statements before relying on them (the pin's `main` may be a weaker/stronger form).

## 5. What it does not do

- **No mechanical transcription of the 3,000 ported lines** (§1) — that is the whole point of the row's
  cheapness.
- **No `Def_` node**: the wrapper's `Def_` closure is `ArchApproxIdentity`-side and complete
  (`gate_scan` 0 missing is part of the W1 gate).
- **The eight arch-derivative leaves** (SET-AF6 §9) stay the column's cheapest *unblocking* set; this
  row returns 0 like bigCell, and the two are independent.

## Appendix A — the 174 declarations that are already in the port (import these)

`port_advise`: 185 substitutions, 184 byte-identical; the pin-line span of the matched copies is
3,060, and these 174 rows are 2,974 of the file's 3,811 declaration lines. Sorted by pin lines.

| pin declaration | import | pin lines |
|---|---|---:|
| `tendsto_integral_mul_dconvWith` | `ArchApproxIdentity.tendsto_integral_mul_dconvWith` — RepTheory/ConvolutionLimit.lean | 158 |
| `main` | `ArchApproxIdentity.exists_tendsto_integral_of_mem_archCutSubmodule` — AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean | 158 |
| `dualCoeffFun_transRep_mem_iSup` | `ArchApproxIdentity.dualCoeffFun_transRep_mem_iSup` — RepTheory/TypeReproducer.lean | 144 |
| `contDiffNat_parametricIntegral_postcompCLM` | `ArchApproxIdentity.contDiffNat_parametricIntegral_postcompCLM` — RepTheory/ConvolutionLimit.lean | 144 |
| `exists_reproducer` | `ArchApproxIdentity.exists_reproducer` — RepTheory/TypeReproducer.lean | 109 |
| `one_mem_span_Dm` | `ArchApproxIdentity.one_mem_span_Dm` — RepTheory/TypeReproducer.lean | 100 |
| `exists_finiteDimensional_stable` | `ArchApproxIdentity.exists_finiteDimensional_stable` — RepTheory/TypeReproducer.lean | 93 |
| `tendsto_integral_mul_approxIdentity` | `ArchEntryBall.tendsto_integral_mul_approxIdentity` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 73 |
| `integral_archHaarK_mul_inclArch` | `ArchInfra.integral_archHaarK_mul_inclArch` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 60 |
| `mem_iSup_typeSubmodule_of_intertwines` | `ArchApproxIdentity.mem_iSup_typeSubmodule_of_intertwines` — RepTheory/TypeReproducer.lean | 53 |
| `exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule` | `ArchApproxIdentity.exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule` — RepTheory/TypeReproducer.lean | 53 |
| `exists_bump` | `ArchEntryBall.exists_bump` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 50 |
| `contDiff_parametricIntegral_mul` | `ArchApproxIdentity.contDiff_parametricIntegral_mul` — RepTheory/ConvolutionLimit.lean | 50 |
| `mem_typeSubmodule_of_isRightEquivariantOn` | `ArchApproxIdentity.mem_typeSubmodule_of_isRightEquivariantOn` — RepTheory/TypeReproducer.lean | 49 |
| `coeffFun_transRep_mem_iSup` | `ArchApproxIdentity.coeffFun_transRep_mem_iSup` — RepTheory/TypeReproducer.lean | 49 |
| `Hm_mulVec_injective` | `ArchApproxIdentity.Hm_mulVec_injective` — RepTheory/TypeReproducer.lean | 39 |
| `exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule` | `ArchApproxIdentity.exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule` — RepTheory/TypeReproducer.lean | 38 |
| `hasCompactSupport_dconvWith` | `ArchApproxIdentity.hasCompactSupport_dconvWith` — RepTheory/ConvolutionLimit.lean | 34 |
| `isHaarMeasure_archHaarK` | `ArchApproxIdentity.isHaarMeasure_archHaarK` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 33 |
| `inclArch_entry` | `ArchInfra.inclArch_entry` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 33 |
| `sigmaFinite_archHaarK` | `ArchInfraTopology.sigmaFinite_archHaarK` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 31 |
| `dconvWith_rt_left` | `ArchApproxIdentity.dconvWith_rt_left` — RepTheory/ConvolutionLimit.lean | 30 |
| `exists_approxIdentity` | `ArchEntryBall.exists_approxIdentity` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 29 |
| `dconvWith_inv_mem_iSup` | `ArchApproxIdentity.dconvWith_inv_mem_iSup` — RepTheory/ConvolutionLimit.lean | 27 |
| `reproducer_inv_mem_iSup` | `ArchApproxIdentity.reproducer_inv_mem_iSup` — RepTheory/TypeReproducer.lean | 25 |
| `continuous_twoSided_family` | `ArchApproxIdentity.continuous_twoSided_family` — AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean | 25 |
| `finiteDimensional_spanTranslates` | `ArchApproxIdentity.finiteDimensional_spanTranslates` — RepTheory/TypeReproducer.lean | 24 |
| `apply_Mint` | `ArchApproxIdentity.apply_Mint` — RepTheory/TypeReproducer.lean | 24 |
| `contDiff_parametricIntegral_clm_comp` | `ArchApproxIdentity.contDiff_parametricIntegral_clm_comp` — RepTheory/ConvolutionLimit.lean | 24 |
| `norm_entry_le_one` | `ArchInfra.norm_entry_le_one` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 22 |
| `rt_mem_typeSubmodule_of_commute` | `ArchApproxIdentity.rt_mem_typeSubmodule_of_commute` — RepTheory/TypeReproducer.lean | 22 |
| `exists_isCompact_preimage_mul_inclArch_eq` | `ArchInfra.exists_isCompact_preimage_mul_inclArch_eq` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 20 |
| `haarScalarFactor_map_mul_inclArch` | `ArchInfra.haarScalarFactor_map_mul_inclArch` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 20 |
| `exists_entryBall_subset` | `ArchEntryBall.exists_entryBall_subset` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 20 |
| `rt_mem_typeSubmodule_self` | `ArchApproxIdentity.rt_mem_typeSubmodule_self` — RepTheory/TypeReproducer.lean | 20 |
| `integral_mul_shift` | `ArchApproxIdentity.integral_mul_shift` — RepTheory/ConvolutionLimit.lean | 20 |
| `rt_mem_spanTranslates_of_mem` | `ArchApproxIdentity.rt_mem_spanTranslates_of_mem` — RepTheory/TypeReproducer.lean | 19 |
| `dotProduct_Mint_mulVec` | `ArchApproxIdentity.dotProduct_Mint_mulVec` — RepTheory/TypeReproducer.lean | 19 |
| `dconvWith_smul_left` | `ArchApproxIdentity.dconvWith_smul_left` — RepTheory/ConvolutionLimit.lean | 19 |
| `dist_apply_le_dist_ringEquiv` | `ArchEntryBall.dist_apply_le_dist_ringEquiv` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 18 |
| `rt_noncommPiCoprod_mem` | `ArchApproxIdentity.rt_noncommPiCoprod_mem` — AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean | 18 |
| `continuous_toGL` | `ArchEntryBall.continuous_toGL` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 16 |
| `piRep_single` | `ArchApproxIdentity.piRep_single` — RepTheory/TypeReproducer.lean | 16 |
| `typeSubmodule_piRep_le` | `ArchApproxIdentity.typeSubmodule_piRep_le` — RepTheory/TypeReproducer.lean | 16 |
| `continuous_Pm_apply` | `ArchApproxIdentity.continuous_Pm_apply` — RepTheory/TypeReproducer.lean | 16 |
| `aux_continuous_of_isArchTestFactor` | `AutomorphicForm.continuous_of_isArchTestFactor` — AutomorphicForm/Adelic/TestFnTop.lean **(private)** | 16 |
| `transRep` | `ArchApproxIdentity.transRep` — RepTheory/TypeReproducer.lean | 15 |
| `conjTranspose_mul_Hm_mul` | `ArchApproxIdentity.conjTranspose_mul_Hm_mul` — RepTheory/TypeReproducer.lean | 15 |
| `isMulRightInvariant_muK` | `ArchInfra.isMulRightInvariant_muK` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 14 |
| `isRightEquivariant_dualCoeffFun` | `ArchApproxIdentity.isRightEquivariant_dualCoeffFun` — RepTheory/TypeReproducer.lean | 14 |
| `isClosed_rowIsoSet` | `ArchInfra.isClosed_rowIsoSet` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 13 |
| `continuous_inclArch` | `ArchInfra.continuous_inclArch` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 13 |
| `continuous_adelicArchGLIncl` | `AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl` — AutomorphicForm/Adelic/TestFnNearIdentity.lean | 13 |
| `muK_univ` | `ArchInfra.muK_univ` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 13 |
| `isCompact_entryBall` | `ArchEntryBall.isCompact_entryBall` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 13 |
| `dconvWith_rt_right` | `ArchApproxIdentity.dconvWith_rt_right` — RepTheory/ConvolutionLimit.lean | 13 |
| `dconvWith_mem_iSup_dual` | `ArchApproxIdentity.dconvWith_mem_iSup_dual` — RepTheory/ConvolutionLimit.lean | 13 |
| `archDUI_apply_mem_closedBall` | `ArchApproxIdentity.archDUI_apply_mem_closedBall` — RepTheory/ConvolutionLimit.lean | 13 |
| `archEntries_mul_mul` | `ArchApproxIdentity.archEntries_mul_mul` — AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean | 13 |
| `integral_mul_left_muK` | `ArchInfra.integral_mul_left_muK` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 12 |
| `Mint_const_mul` | `ArchApproxIdentity.Mint_const_mul` — RepTheory/TypeReproducer.lean | 12 |
| `Mint_mul_const` | `ArchApproxIdentity.Mint_mul_const` — RepTheory/TypeReproducer.lean | 12 |
| `dconvWith_add_right` | `ArchApproxIdentity.dconvWith_add_right` — RepTheory/ConvolutionLimit.lean | 12 |
| `dconvWith_add_left` | `ArchApproxIdentity.dconvWith_add_left` — RepTheory/ConvolutionLimit.lean | 12 |
| `convOpL` | `ArchApproxIdentity.convOpR` — RepTheory/ConvolutionLimit.lean | 12 |
| `continuous_inclAdelic` | `ArchInfra.continuous_inclAdelic` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 11 |
| `Pm_inv_apply_eq_dualCoeffFun` | `ArchApproxIdentity.Pm_inv_apply_eq_dualCoeffFun` — RepTheory/TypeReproducer.lean | 11 |
| `reproducer_mem_iSup_dual` | `ArchApproxIdentity.reproducer_mem_iSup_dual` — RepTheory/TypeReproducer.lean | 11 |
| `mem_image_mul_mul_of_ne` | `ArchApproxIdentity.mem_image_mul_mul_of_ne` — RepTheory/ConvolutionLimit.lean | 11 |
| `twoSided` | `ArchApproxIdentity.twoSided` — AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean | 11 |
| `secondCountableTopology_placeGL` | `ArchInfraTopology.secondCountableTopology_placeGL` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 10 |
| `toUnit` | `ArchInfra.toUnit` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 10 |
| `conjTranspose_Pm` | `ArchApproxIdentity.conjTranspose_Pm` — RepTheory/TypeReproducer.lean | 10 |
| `integrable_of_continuous_prod` | `ArchApproxIdentity.integrable_of_continuous_prod` — RepTheory/ConvolutionLimit.lean | 10 |
| `rtStabilizer` | `ArchApproxIdentity.rtStabilizer` — AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean | 10 |
| `isCompact_rowIsoSet` | `ArchInfra.isCompact_rowIsoSet` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 9 |
| `range_toUnit` | `ArchInfra.range_toUnit` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 9 |
| `ringEquiv_mixedSpace_eq` | `ArchEntryBall.ringEquiv_mixedSpace_eq` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 9 |
| `isOpen_detLocus` | `ArchEntryBall.isOpen_detLocus` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 9 |
| `cosetCoord_mul` | `ArchApproxIdentity.cosetCoord_mul` — RepTheory/TypeReproducer.lean | 9 |
| `piRep` | `ArchApproxIdentity.piRep` — RepTheory/TypeReproducer.lean | 9 |
| `star_dotProduct_conjTranspose_mul_mulVec` | `ArchApproxIdentity.star_dotProduct_conjTranspose_mul_mulVec` — RepTheory/TypeReproducer.lean | 9 |
| `Pm_entry_mem_iSup` | `ArchApproxIdentity.Pm_entry_mem_iSup` — RepTheory/TypeReproducer.lean | 9 |
| `Pm_inv_entry_mem_iSup` | `ArchApproxIdentity.Pm_inv_entry_mem_iSup` — RepTheory/TypeReproducer.lean | 9 |
| `convOpR` | `ArchApproxIdentity.convOpR` — RepTheory/ConvolutionLimit.lean | 9 |
| `isCompact_image_mul_mul` | `ArchApproxIdentity.isCompact_image_mul_mul` — RepTheory/ConvolutionLimit.lean | 9 |
| `mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi` | `ArchApproxIdentity.mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi` — RepTheory/TypeReproducer.lean | 8 |
| `continuous_Pm` | `ArchApproxIdentity.continuous_Pm` — RepTheory/TypeReproducer.lean | 8 |
| `Mint_conjTranspose` | `ArchApproxIdentity.Mint_conjTranspose` — RepTheory/TypeReproducer.lean | 8 |
| `mem_contSubmodule` | `ArchApproxIdentity.mem_contSubmodule` — RepTheory/ConvolutionLimit.lean | 8 |
| `dconvWith_smul_right` | `ArchApproxIdentity.dconvWith_smul_right` — RepTheory/ConvolutionLimit.lean | 8 |
| `secondCountableTopology_archGL` | `ArchInfraTopology.secondCountableTopology_archGL` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 7 |
| `Kprod` | `GroupTheory.BassSerre.Gp` — GroupTheory/BassSerre/MinimalPeriod.lean | 7 |
| `KprodTop` | `ArchInfra.KprodTop` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 7 |
| `continuous_archEntries` | `AutomorphicForm.continuous_archEntries` — AutomorphicForm/Adelic/TestFnTop.lean **(private)** | 7 |
| `dist_entry_le` | `ArchEntryBall.dist_entry_le` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 7 |
| `toGL` | `ArchEntryBall.toGL` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 7 |
| `isRightEquivariant_coeffFun` | `ArchApproxIdentity.isRightEquivariant_coeffFun` — RepTheory/TypeReproducer.lean | 7 |
| `piE_mul` | `ArchApproxIdentity.piE_mul` — RepTheory/TypeReproducer.lean | 7 |
| `Mint_mul_right` | `ArchApproxIdentity.Mint_mul_right` — RepTheory/TypeReproducer.lean | 7 |
| `continuous_dconvIntegrand` | `ArchApproxIdentity.continuous_dconvIntegrand` — RepTheory/ConvolutionLimit.lean | 7 |
| `secondCountableTopology_archMatrix` | `ArchInfraTopology.secondCountableTopology_archMatrix` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 6 |
| `archGLMeasurableSpace` | `ArchInfraTopology.archGLMeasurableSpace` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 6 |
| `archGLBorelSpace` | `ArchInfraTopology.archGLBorelSpace` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 6 |
| `archGLMeasurableSpace` | `ArchInfraTopology.archGLMeasurableSpace` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 6 |
| `archGLBorelSpace` | `ArchInfraTopology.archGLBorelSpace` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 6 |
| `one_mem_entryBall` | `ArchEntryBall.one_mem_entryBall` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 6 |
| `continuous_det_apply` | `ArchEntryBall.continuous_det_apply` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 6 |
| `archGLMeasurableSpace` | `ArchInfraTopology.archGLMeasurableSpace` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 6 |
| `archGLBorelSpace` | `ArchInfraTopology.archGLBorelSpace` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 6 |
| `exists_out_mul_eq` | `ArchApproxIdentity.exists_out_mul_eq` — RepTheory/TypeReproducer.lean | 6 |
| `dualCoeffFun` | `ArchApproxIdentity.dualCoeffFun` — RepTheory/TypeReproducer.lean | 6 |
| `le_spanTranslates` | `ArchApproxIdentity.le_spanTranslates` — RepTheory/TypeReproducer.lean | 6 |
| `piE_one` | `ArchApproxIdentity.piE_one` — RepTheory/TypeReproducer.lean | 6 |
| `continuous_apply_apply_of_continuous` | `ArchApproxIdentity.continuous_apply_apply_of_continuous` — RepTheory/TypeReproducer.lean | 6 |
| `isUnit_Hm_det` | `ArchApproxIdentity.isUnit_Hm_det` — RepTheory/TypeReproducer.lean | 6 |
| `Pm_apply_eq_coeffFun` | `ArchApproxIdentity.Pm_apply_eq_coeffFun` — RepTheory/TypeReproducer.lean | 6 |
| `contSubmodule` | `ArchApproxIdentity.contSubmodule` — RepTheory/ConvolutionLimit.lean | 6 |
| `twoSided_apply` | `ArchApproxIdentity.twoSided_apply` — AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean | 6 |
| `secondCountableTopology_infiniteAdeleRing` | `ArchInfraTopology.secondCountableTopology_infiniteAdeleRing` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 5 |
| `mem_rowIsoSet_iff` | `ArchInfra.mem_rowIsoSet_iff` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 5 |
| `inclAdelic` | `ArchInfra.inclAdelic` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 5 |
| `archComponent_inclArch` | `ArchInfra.archComponent_inclArch` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 5 |
| `integral_mul_right_muK` | `ArchInfra.integral_mul_right_muK` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 5 |
| `t2Space_archMatrix` | `ArchInfraTopology.t2Space_archMatrix'` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 5 |
| `t2Space_archMatrix` | `ArchInfraTopology.t2Space_archMatrix'` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 5 |
| `archEntries_eq` | `ArchEntryBall.archEntries_eq` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 5 |
| `continuous_matrixEntries` | `ArchEntryBall.continuous_matrixEntries` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 5 |
| `ringInverse_eq` | `ArchEntryBall.ringInverse_eq` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 5 |
| `coeffFun` | `ArchApproxIdentity.coeffFun` — RepTheory/TypeReproducer.lean | 5 |
| `transRep_apply` | `ArchApproxIdentity.transRep_apply` — RepTheory/TypeReproducer.lean | 5 |
| `rtLinear` | `ArchApproxIdentity.rtLinear` — RepTheory/TypeReproducer.lean | 5 |
| `Pm_mul` | `ArchApproxIdentity.Pm_mul` — RepTheory/TypeReproducer.lean | 5 |
| `hasCompactSupport_of_compactSpace` | `ArchApproxIdentity.hasCompactSupport_of_compactSpace` — RepTheory/TypeReproducer.lean | 5 |
| `integrable_of_continuous` | `ArchApproxIdentity.integrable_of_continuous` — RepTheory/TypeReproducer.lean | 5 |
| `Hm` | `ArchApproxIdentity.Hm` — RepTheory/TypeReproducer.lean | 5 |
| `continuous_PHP` | `ArchApproxIdentity.continuous_PHP` — RepTheory/TypeReproducer.lean | 5 |
| `Dm` | `ArchApproxIdentity.Dm` — RepTheory/TypeReproducer.lean | 5 |
| `continuous_Pm_inv` | `ArchApproxIdentity.continuous_Pm_inv` — RepTheory/TypeReproducer.lean | 5 |
| `locallyCompactSpace_archMatrix` | `ArchInfraTopology.locallyCompactSpace_archMatrix` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 4 |
| `rowIsoSet` | `ArchInfra.rowIsoSet` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 4 |
| `continuous_entry` | `ArchInfra.continuous_entry` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 4 |
| `inclArch` | `ArchInfra.inclArch` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 4 |
| `inclArch_mulSingle` | `ArchInfra.inclArch_mulSingle` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 4 |
| `inclAdelic_mulSingle` | `ArchInfra.inclAdelic_mulSingle` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 4 |
| `KprodMeasurableSpace` | `ArchInfra.KprodMeasurableSpace` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 4 |
| `KprodBorelSpace` | `ArchInfra.KprodBorelSpace` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 4 |
| `matrixEntries` | `ArchEntryBall.matrixEntries` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 4 |
| `detLocus` | `ArchEntryBall.detLocus` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 4 |
| `one_mem_detLocus` | `ArchEntryBall.one_mem_detLocus` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 4 |
| `mul_piInv` | `ArchEntryBall.mul_piInv` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 4 |
| `piInv_mul` | `ArchEntryBall.piInv_mul` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 4 |
| `isUnit_of_forall_ne_zero` | `ArchEntryBall.isUnit_of_forall_ne_zero` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 4 |
| `toGL_eq` | `ArchEntryBall.toGL_eq` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 4 |
| `out_mul_cosetCoord` | `ArchApproxIdentity.out_mul_cosetCoord` — RepTheory/TypeReproducer.lean | 4 |
| `cosetCoord_unique` | `ArchApproxIdentity.cosetCoord_unique` — RepTheory/TypeReproducer.lean | 4 |
| `rt_mul` | `ArchApproxIdentity.rt_mul` — RepTheory/TypeReproducer.lean | 4 |
| `rt_mem_spanTranslates` | `ArchApproxIdentity.rt_mem_spanTranslates` — RepTheory/TypeReproducer.lean | 4 |
| `Pm` | `ArchApproxIdentity.Pm` — RepTheory/TypeReproducer.lean | 4 |
| `Pm_one` | `ArchApproxIdentity.Pm_one` — RepTheory/TypeReproducer.lean | 4 |
| `Pm_inv_mul` | `ArchApproxIdentity.Pm_inv_mul` — RepTheory/TypeReproducer.lean | 4 |
| `Pm_mul_inv` | `ArchApproxIdentity.Pm_mul_inv` — RepTheory/TypeReproducer.lean | 4 |
| `Mint` | `ArchApproxIdentity.Mint` — RepTheory/TypeReproducer.lean | 4 |
| `dconvWith` | `ArchApproxIdentity.dconvWith` — RepTheory/ConvolutionLimit.lean | 4 |
| `mem_rtStabilizer` | `ArchApproxIdentity.mem_rtStabilizer` — AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean | 4 |
| `t2Space_archMatrix'` | `ArchInfraTopology.t2Space_archMatrix'` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 3 |
| `continuous_toUnit` | `ArchInfra.continuous_toUnit` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 3 |
| `entryBall` | `ArchEntryBall.entryBall` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 3 |
| `isClosed_entryBall` | `ArchEntryBall.isClosed_entryBall` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 3 |
| `piInv` | `ArchEntryBall.piInv` — AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean | 3 |
| `cosetCoord` | `ArchApproxIdentity.cosetCoord` — RepTheory/TypeReproducer.lean | 3 |
| `spanTranslates` | `ArchApproxIdentity.spanTranslates` — RepTheory/TypeReproducer.lean | 3 |
| `isTopologicalGroup_archGL` | `ArchInfraTopology.isTopologicalGroup_archGL` — AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean | 2 |
| `EntrySpace` | `GroupTheory.BassSerre.Gp` — GroupTheory/BassSerre/MinimalPeriod.lean | 2 |

## Appendix B — the 50 declarations to write (837 pin lines)

| pin declaration | pin lines | what it is |
|---|---:|---|
| `aux_integral_mul_dconvWith` | 140 | the dominated-convergence core |
| `aux_exists_kernel` | 121 | the convolution kernel's existence |
| `solution` | 68 | **the headline** — `rightConv` of a right translate stays in the cusp subrepresentation |
| `aux_dconvWith_tensor` | 57 | the tensor form of `dconvWith` |
| `aux_rightConv_rightTranslate_eq` | 32 | the re-indexing onto `convOpOn` |
| `exists_contDiff_dconvWith` | 30 | smoothness of `dconvWith` |
| `convOpOn_mem_iSup_typeSubmodule` | 29 | membership in the type submodule |
| `aux_exists_contDiff_dconvWith` | 29 | the arch-smooth instantiation |
| `forall_rowIsometryInclAt` | 26 | the row-isometry quantifier |
| `aux_rightConv_mem_archCutSubmodule` | 26 | membership in the arch cut |
| `aux_exists_archTypeFamily_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule` | 22 | the type-family step |
| `aux_continuous_of_mem_cuspKFiniteSubmodule` | 20 | continuity on the cusp-`Kf` submodule |
| `convDomain` | 19 | the convolution domain |
| `convOpOn` | 17 | the convolution operator |
| `aux_isArchTestFactor_mul_right` | 13 |  |
| `isCompact_rowIsometrySubgroup` | 12 | compactness of the row-isometry subgroup |
| `aux_map_algebraMap_self` | 11 |  |
| `aux_exists_factors_mul_right` | 11 |  |
| `_root_.KAvArch.locallyCompactSpace_archGL` | 10 |  |
| `archRowIsometryInclAt` | 9 | the archimedean row-isometry inclusion |
| `rowIsometryInclAt` | 7 | the row-isometry inclusion |
| `convOpOn_comp_mul` | 7 |  |
| `comp_mul_mem_convDomain` | 7 |  |
| `archComponent_glArch_rowIsometryInclAt` | 7 |  |
| `_root_.KAvArchT.locallyCompactSpace_archGL` | 7 |  |
| `secondCountableTopology_rowIsometrySubgroup` | 6 | second countability |
| `secondCountableTopology_piRowIsometrySubgroup` | 6 |  |
| `piE` | 6 |  |
| `conv_integrand_eq` | 6 |  |
| `convOpOn_apply` | 6 |  |
| `commute_archRowIsometryInclAt` | 6 |  |
| `aux_isFinTestFactor_mul_right` | 6 |  |
| `archComponent_archRowIsometryInclAt` | 5 |  |
| `piRep_apply` | 4 |  |
| `mem_convDomain_iff` | 4 |  |
| `entryBall_mono` | 4 |  |
| `dualCoeffFun_apply` | 4 |  |
| `coeffFun_apply` | 4 |  |
| `aux_isContainedIn_join_right` | 4 |  |
| `aux_isContainedIn_join_left` | 4 |  |
| `aux_archTypeFamilyJoin` | 4 |  |
| `piE_apply` | 3 |  |
| `inclAdelic_apply` | 3 |  |
| `Mint_apply` | 3 |  |
| `rt_apply` | 2 |  |
| `rtLinear_apply` | 2 |  |
| `rt` | 2 |  |
| `muK` | 2 |  |
| `Kw` | 2 |  |
| `Ent` | 2 |  |
| **50 declarations** | **837** | the rest is `aux_*` glue, `piE`/`Kw`/`Ent` shims (2–13 lines each) |

## Appendix C — the read and the reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json | \
  python3 -c "import json,sys; d=json.load(sys.stdin); [print(x) for x in d['ready_rank']['rows'] if 'rightConv_rightTranslate_mem_of_isCuspSubrep' in x['qual']]"
python3 port_advise.py --nodes AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep --json build/af8.json
python3 port_plan.py --json build/af8.json        # 3,833 raw / 3,811 decl / 39 dup / 3,015 in port / 757 net
python3 twin_scan.py --node AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep
```

**Forecast on landing** (the cut's arithmetic, re-based on the read *after* SET-AF7 landed — the
recipe's "read the delta, not the absolute"): `needed` **895 / 362,549 → 894 / 358,716**, frontier
**+1 / +3,833** (1,520 / 764,817 → 1,521 / 768,650), the `AutomorphicForm` ready shelf
**41 / 17,411 → 40 / 13,578** (the row leaves; it readies nothing).
