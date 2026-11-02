# SET-AF3 — the archimedean cut is admissible, and it carries a reproducing kernel

**Status: landed 2026-11-02** — the ground by the manager (§4.1) and the four rows by one worker
dispatch ([WORKORDER-AF3-proofs.md](WORKORDER-AF3-proofs.md)); §1.5 records the landing and §8 the
measured re-read, both after the fact. Read off the D–S shelf after SET-AF2's landing,
with the recipe in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md),
`--include-leaves`, and the **corrected** read (`--unport`, §0.2). No Lean was run while scoping beyond
the manager's own ground module; every other figure is the tools' or the pin's.

The set is **one manager ground module and four rows in two worker modules**: the two pin-`private`
dictionary lemmas both consumer modules need (§4.1, landed) and the four headlines

- 998 `exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule`
  — **the shelf's largest `AutomorphicForm` ready row**, and the row SET-AF2's compactness lemma made ready;
- 459 `finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule` and
  222 `finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule` — the two span leaves
  SET-AF2's §9 pairs with 184;
- 184 `finiteDimensional_span_translates_of_mem_archCutSubmodule` — the packaging of that span as a
  finite-dimensional, continuous, cut-stable module.

**1,863 raw `S_` lines → 1,098 net new math lines**, of which **642 lines are already in the port**
(the `TypeReproducer`, `ArchCutProjector`, `ArchCompactOrbit` and `ArchTypeSpan` engines) — the highest
reuse of any big cluster on the column's shelf. Two new worker modules, eight wire lines, one landed
ground module (2 declarations), no definition gate, no promotion of a *port* declaration, no
migration, no marker, no tree build, no edits to existing modules. The set is a premise of **ten** unported rows / 6,657 silo (§8).

§0 the read and the gate census; §1 the cut; §2 what the rows say; §3 homes; §4 ground prep (and the
manager's landing); §5 traps; §6 gates; §7 calls; §8 reproduce and the forecast; §9 what this set does
not do. **Appendix A** names all 27 `AutomorphicForm` ready rows and **Appendix B** all 84 leaves,
with the gate each one waits on.

## 0. The read

### 0.1 The canonical read, and the corrected one

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af3.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
    --unport AutomorphicForm.continuous_unipotentGL2 --json > build/shelf-af3-corr.json
python3 frontier.py --selfcheck
```

**`--selfcheck` PASS** — every `Thm_` source resolves, the source tier is covered by the name tier,
the frontier is inside the graph; 1,341 `Thm_` sources, 1,506 declared names, 1,506 / 754,033 raw
`S_` lines.

| figure | instrument's read | **corrected read** | SET-AF2 §8 (corrected) |
|---|---:|---:|---:|
| `needed [F terminal]` | 909 / 373,333 | **910 / 373,361** | 910 / 373,361 |
| `needed [literal]` | 922 / 376,808 | **923 / 376,836** | — |
| frontier F (union) | 1,506 / 754,033 | **1,505 / 754,005** | 1,506 / 754,033 |
| … of F, inside the cone | 1,181 / 605,365 | **1,180 / 605,337** | — |
| port cone / avoided R | 2,103 / 982,173 · 140 / 74,620 | same | same |
| ready rows, all namespaces | 60 / 12,914 | **58 / 12,153** | — |
| leaves, all namespaces | 254 / 63,615 | **255 / 63,643** | — |
| `AutomorphicForm` ready rows | 29 / 7,430 | **27 / 6,669** | 27 / 6,669 |
| `AutomorphicForm` leaves | 83 / 17,251 | **84 / 17,279** | 84 / 17,279 |
| `AutomorphicForm` demand | 405 / 171,112 | **406 / 171,140** | 406 / 171,140 |
| withheld by the FR-0044 guard | 4 / 831 | **4 / 831** | 4 / 831 |

**The read is unchanged since SET-AF2's landing**, and this scoping opens on its predecessor's re-read
rather than on a stale absolute: the corrected figures are exactly §8 of that brief. The withheld
block is still the four prunable-subject rows — the two Tate-module rows (327 + 283), the
`Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` row (126) and the `Pic0` torsion
finiteness (95) — none of them this column's.

### 0.2 The correction is the shadow SET-AF2's own landing made (FR-0095)

The instrument's read is wrong in both directions here, and for a reason the recipe now knows: the
new `Adelic/InducedSectionMaximalCompact.lean` proves a `private continuous_unipotentGL2`, whose *last
name* is the unported pin node `AutomorphicForm.continuous_unipotentGL2` (28 silo). The frontier's
ported set is a set of last-name components **including `private` declarations**, so that node reads
as ported: the raw read reports one node / 28 lines better than the truth and puts the two rows whose
sole missing premise is that node (`continuous_rightConv_and_contDiff_of_isFactorizableTestFn` 471,
`isCuspidalFn_isKfSmooth_levelInvariant_…` 290) on the ready shelf, where they cannot be written.

**`--unport AutomorphicForm.continuous_unipotentGL2`** on the same invocation restores every figure:
`needed` 909 / 373,333 → **910 / 373,361**, the AF ready shelf 29 / 7,430 → **27 / 6,669**. The
corrected read is the one this set is cut from, and the two vanished rows are not quoted as ready
anywhere below.

### 0.3 The gate census — at the declaration, not the module

The recipe reads the gate by *module* first. On this shelf that first cut over-reports: **ten of the
port modules that transcribe a pin `Def_` module did not name it in a `spec-pin:` line at all** — they
carried the pin's declarations with `-- pin:` markers (the `ArchCasimir`/`ArchInfra` engine pattern), so a
ported-set test built from `spec-pin:` plus `old_check_stmts.py` read their pin modules as unported.
(§4.5 records the sweep that followed this read: **all thirty-two** such modules were upgraded to
`spec-pin:` wires, so the census below is the shelf as it stood when this brief was cut.)
All ten are in fact complete at the declaration level (`spec/gate_scan.py` from `lean/`: **0 missing**
for `BorelSubgroup` (3/19 used), `EtaFamily` (4/15), `InducedSection` (1/10), `WeylIntertwining` (4/7),
`LinearAlgebra_Countable` (0/1), `TateGlobalZeta` (3/15), `LocalOrbitalBase` (4/61), `TwistedOrbital`
(10/82), `AdelicFourier` (2/15), `TateLocalZeta` (6/23)).

What *is* still a gate is small, and the declaration-level unit is what prices it:

| row | silo | unported gate module | used-and-missing declarations | pin lines |
|---|---:|---|---|---:|
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | `FnTwist` | `det_centralScalar` | 4 |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | `RationalTorusUnipotentQuotient` | `rationalDiagOne`, `rationalTorus`, `rationalTorusUnipotent`, `rationalTorusUnipotentHaar` | 15 |
| `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_…` | 69 | `BoundedGenuineCuspRealization` | `IsBoundedOnSiegelWindows` | 3 |
| `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_…` | 146 | `BoundedGenuineCuspRealization` + `UnramifiedWhittaker_HeckeRecursion` | the above + `placeEmbed` | 11 |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | `UnramifiedWhittaker_HeckeRecursion` | `placeEmbed` | 8 |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | `UnramifiedWhittaker_HeckeRecursion` | `placeEmbed` | 8 |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_…` | 384 | `HeckeEigenfunction` | `uniformizerIdele` | 6 |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | `RationalCentreUnipotentQuotient` | `rationalCentre`, `rationalCentreUnipotent` | 5 |
| `isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | `IwasawaShellIndex` | ten declarations | 44 |
| `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | `IwasawaShellIndex` + `RationalCentreUnipotentQuotient` | `iwasawaShellIndex` + the centre pair | 11 |
| `RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_…` / `RankinSelberg.section_diagOne_mul_…` | 141 + 66 | `NumberField_IdeleProductMeasure` | `ideleBorel`, `borelSpace_ideleBorel` | 5 |

Two corrections the same census forces:

- **`isFundamentalDomain_boxSheet_rationalCentreUnipotent` (340) uses 0/6** declarations of the
  `RationalTorusUnipotentQuotient` module the import line names: module-granular noise, exactly the
  AF2 §0.3 error in the other direction. The gate of the 440 row does not gate the 340 row.
- **Every gate that remains is ≤ 44 pin lines of pin-`private` helpers.** The column's *large*
  definition gates have all landed; what is left of the definition layer is a sweep, not a module
  (§9). The column's remaining shelf is theorem work.

### 0.4 Why this cluster, and not another

The column's three big ungated families named by SET-AF2 §9 are all still there. Priced on the same
read (the `port_advise`/`port_plan` pair, §1.3):

| cluster | rows | raw silo | net new | in-port reuse |
|---|---:|---:|---:|---:|
| **the arch cut's admissibility + kernel** | **4** | **1,863** | **1,098** | **642 (34%)** |
| the arch-derivative chain (`archDerivAt*`/`archDerivAtComplex*`) | 6 | 1,745 | 1,190 | 376 (22%) |
| `LocalIntertwining` (the atom/integral family) | 8 | 1,578 | 1,393 | 58 (4%) |
| `CuspidalConstituent` (the constituent's own lemmas) | 9 | 1,593 | 1,406 | 6 (0.4%) |

The cut cluster wins on four counts. It contains **the head of the AF ready shelf** (998) — the row
SET-AF2's `isCompact_rowIsometrySubgroup_detOne` was a premise of, i.e. the §7 debt of the last set's
landing, which the recipe says opens the next scoping. It contains the two leaves SET-AF2 §9 names as
one set with 184 ("the two belong in one set"). It reuses more of the port than any other cluster
(642 lines: the generic type-reproducer engine, the projector's per-place span lemmas, the compact
orbit carrier), so its net is the lowest of the four. And it is **definition-complete** (§0.5): no
gate, so the manager's layer is the shared ground and the review, not a definition module.

The other three are deferred wholesale (§9): each is a story, none has a gate, and the arch-derivative
chain's own topic already schedules it as the Casimir engine's Set C.

### 0.5 The definition-layer test, machine-checked

`gate_scan` over every `Def_` module the four rows' wrappers and `S_` files import:

| row | module | used | missing |
|---|---|---:|---:|
| 459 | `AdelicMaximalCompact` | 3/37 | **0** |
| 459 | `ArchWeightChar` | 1/19 | **0** |
| 459, 222 | `CuspidalConstituent` | 6/21 | **0** |
| 998, 184 | `CuspidalSpectrumCarrier` | 0/41 | **0** |
| 998, 184 | `FactorizableTestFn` | 0/10 | **0** |
| 998, 184 | `ArchSpherical` | 0/7 | **0** |

The three `0 used` modules are the imports AF2 itself called module-granular noise. `port_advise
--with-defs` closes over the same four modules and adds no other; the statement vocabulary the FR-0049
check looks for is all in the port: `ArchTypeFamily`, `archCutSubmodule`, `archDualCutSubmodule`,
`mem_archCutSubmodule_iff`, `typeSubmodule`, `rowIsometryInclAt₀`, `rowIsometrySubgroup₀`,
`adelicArchGLIncl`, `archComponent`, `archDualCutSubmodule` (`IsotypicCuspSpace`, `ArchType`,
`ArchWeightChar`, `Cusp/Constituent`), and `isCompact_rowIsometrySubgroup_detOne`
(`MaximalCompactFactors`).

`twin_scan` on the four: all **new** (998 prelude 16/22, 459 31/37, 222 2/7, 184 0/5) — none of the four
statements is in the port at another name.

## 1. The cut

### 1.1 The story

`archCutSubmodule F tys` is the subspace of functions on `GL₂(𝔸_F)` whose archimedean translates sit in
finitely many archimedean types `tys`; `archDualCutSubmodule` is its dual twin. The archimedean
compact group `K_∞ = ∏_w K_w` acts on both by right translation, through the product inclusion
`adelicArchGLIncl ∘ ι`.

The mathematics of this set is that this action is **admissible** and that admissibility is what a
reproducing kernel needs:

1. the span of the right translates of **one** cut vector by the compact group is finite-dimensional
   (459), and the same for the dual cut (222);
2. the span of the translates of a cut vector by the *product* is finite-dimensional, continuous,
   inside the cut, and stable under the action (184) — the four properties the flat-family arguments
   consume as hypotheses;
3. a finite-dimensional invariant subspace `E` of the cut therefore carries a **continuous reproducing
   kernel** `e`: conj-invariant, inversion-real (`e κ⁻¹ = conj (e κ)`), lying in the dual type modules
   with `κ ↦ e κ⁻¹` in the type modules, and reproducing every `v ∈ E` by
   `∫ κ, e κ * v (x * adelicArchGLIncl F (ι κ)) ∂μ = v x` (998).

This is the archimedean half of "the cuspidal spectrum is a direct sum of finite-dimensional
isotypic pieces", and it is the reason the flat-family rows of the column can state their hypotheses
at all.

### 1.2 The steps

| step | node (`AutomorphicForm.` dropped) | pin lines | net | gate | order |
|---|---|---:|---:|---|---|
| **G** | (ground) `ext_archComponent`, `adelicArchGLIncl_iota_mulSingle` | 24 | 2 decls | — | **manager, landed** |
| **M1** | `finiteDimensional_span_translates_of_mem_archCutSubmodule` | 184 | 162 | — | 2 |
| **M2** | `finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule` | 459 | 183 | — | 2 |
| **M3** | `finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule` | 222 | 182 | — | 2 |
| **M4** | `exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule` | 998 | 592 | — | 3 |
| | **5 steps** | **1,887** | **≈1,144** | | |

The per-row nets are the single-node `port_plan` readings (each of which sees 0 duplicate copies); the
set's own plan removes the 35 lines the four `S_` files copy from each other, which is why the rows sum
to 1,119 while the set prices **1,098 net**. The ground is not inside either figure — it is the
manager's order, 2 declarations. Both readings are inside the recipe's band.

### 1.3 Pricing

```bash
python3 port_advise.py --with-defs --nodes <the four> --json build/af3-arcut-advise.json
python3 port_plan.py --json build/af3-arcut-advise.json
```

**1,863 raw `S_` lines − 88 boilerplate = 1,775 declaration lines − 35 duplicate copies = 1,740
once-cost − 642 already in the port = 1,098 net new math lines.** 115 substitutions are trusted and
5 suspect (the parser's type-only `def` matches). The in-port 642 is *why this set is cheap*: 374 lines
of the 998 row are the `RepTheory/TypeReproducer` engine (`coeffFun`/`dualCoeffFun`/`transRep`/`piRep`/
`finiteDimensional_spanTranslates`/`exists_reproducer`), 260 of the 459 row are `ArchCompactOrbit` +
`ArchCutProjector` (`orbitSpan`, `placeOrbitSpan`, `finiteDimensional_placeOrbitSpan_*`,
`continuous_archProdIncl`, `isCompact_iSup_range_…`), 22 of the 222 row the same projector lemmas
(the three sum to 656 before the set's own dedup).

**The prelude to port once** (`port_advise`'s *port once* block): three names, ≈46 removable lines —
`rightTranslate_mem_of_mem_iSup_range'` (2 copies; already public in `ArchCutProjector`),
`adelicArchGLIncl_iota_mulSingle` (2 copies, 18 lines) and `ext_archComponent` (2 copies, 6 lines). The
last two are the manager's ground (§4.1); the first is imported.

**`drags`:** the 998 file's engine lists every heavy declaration as `[in-port]`; the 459 file lists
`isCompact_rowIsometrySubgroup₀` and the projector lemmas as in-port too. Nothing in the four files
needs a new engine.

### 1.4 The lanes

| order | who | steps | file (new) | pin lines | why this order |
|---|---|---|---:|---|---:|
| **1** | manager | G | `Adelic/ArchComponentDictionary.lean` | 24 | both consumer modules state over it |
| **2** | worker | M1, M2, M3 | `Adelic/ArchCutSpan.lean` | 865 | one subject: the orbit span on the cut and the dual cut |
| **3** | worker | M4 | `Adelic/ArchCutReproducer.lean` | 998 | the kernel; needs the ground and the ported engine, not M1–M3 |

Orders 2 and 3 are **disjoint files and disjoint imports** (only G and the frozen port modules are
shared), so they can run concurrently; the build lock is the only shared resource.

### 1.5 The landing — the four rows, one worker dispatch

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---:|---|---|
| M1–M3 | `Adelic/ArchCutSpan.lean` (**+482**; 3 public + 7 private) | **3 ok** / 0 / 0 | silent, **4.2 s**, zero warnings | clean ×3 |
| M4 | `Adelic/ArchCutReproducer.lean` (**+567**; 1 public + 1 private) | **1 ok** / 0 / 0 | silent, **8.3 s**, zero warnings | clean ×1 |

**What the set consumed**: 5 steps / 1,887 pin lines (24 ground + 1,863 rows) — **1,059 source lines**
in the two worker modules (482 + 567) against the 1,098 net-new declaration lines priced, plus the
ground's 65. `dedup.py --within` — **0 clusters** in both (10 and 2 declarations); `dedup.py --cross` over the two
modules and the four arch engines they build on — the only cluster is the pre-existing
`ArchKFiniteFamily` / `ArchKFiniteFamilyTheorems` wrapper-over-engine pair (the pin's own pattern, kept
by the recipe), none involving this set; every module silent on `lake env lean` and on its own
`lake build`; the two modules do not import each other; the ground was not edited. The consumer probe `spec/AutomorphicFormSetAF3Consumer.lean` is new, two zones, **0
errors**, and load-bearing (deleting either module breaks the other's zone). Neither pin
`set_option maxHeartbeats` (800,000 / 3,200,000) is transcribed: both modules close at
`-DmaxHeartbeats=1000000`.

**Deviations held for review** (no statement changed; every `check_port` hash matched):

- **M2/M3 share one envelope — and the pin's FD-only lemma is not in the port.** The port merged the
  pin's private `finiteDimensional_orbitSpan_of_mem_archCutSubmodule` into
  `ArchCutProjector.mem_Ecf_of_mem_archCutSubmodule`, which additionally demands `Continuous φ`; the
  FD-only statement exists nowhere in the port. Rather than write the 85-line envelope induction
  twice, M2 and M3 are both derived from the pin's M3 lemma
  `exists_finiteDimensional_stable_of_forall_mem_iSup_typeSubmodule` (transcribed verbatim,
  polymorphic in `W`/`ρ`) plus one shared private 8-line dictionary step
  (`orbitSpan_eq_span` + `rightTranslate_mem_of_mem_iSup_range'`); M2 instantiates with
  `ρ := (tys.rep w i).ρ`, M3 with `ρ.dual`, and each headline is ~12 lines. The set therefore writes
  *fewer* lines than the pin's 459 + 222, with no duplicated engine — but it also means the workorder's
  named engine `placeOrbitSpan_mono_of_mem` **does not exist in the port**: it was a pin declaration
  of the 459 `S_` file, and the order listed it among the port's engines. Its one-line argument is
  inlined.
- **M3's per-place inductions** are stated for an arbitrary finite-dimensional `ρ` (the pin's own
  statement) rather than through the port's
  `finiteDimensional_placeOrbitSpan_of_mem_archTypeSubmoduleAt`: that lemma is stated for `ArchRepAt`,
  whose module is `Fin n → ℂ`, and cannot express the dual representation
  `Module.Dual ℂ (Fin n → ℂ)` that M3 needs. The pin's two proofs (24 + 18 lines) are transcribed.
- **M1**: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`; `comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule`
  → the port's `CuspidalConstituent.rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule`;
  `haveI` → `have` where a local instance is wanted (`linter.style.haveILetI`); the proof-search
  namespaces dropped.
- **M4**: only the two `ArchApproxIdentity` coefficient lemmas are imported from
  `RepTheory/TypeReproducer` (the private `typedCoeff` composes them, in the port's `lam v` binder
  order); the pin's `Pm`/`Hm`/`Dm`/`exists_reproducer` engine is **not** on this row's path — the pin
  builds its own Gram matrix over a basis of the orbit span, so the import is required but the
  positivity engine is unused. `G.IsHermitian` → `Matrix.IsHermitian G` with one specific mathlib
  import (`Mathlib.LinearAlgebra.Matrix.Hermitian`): at `v4.34` field notation does not fire on a
  `let`-bound `Matrix`. The `…finset_sum` family is `…finsetSum`.

## 2. What the rows say

**M1 `finiteDimensional_span_translates_of_mem_archCutSubmodule` (184).** For a product homomorphism
`ι : ∏_w K_w →* GL₂(𝕀_F)` with the componentwise hypothesis `hι`, an arch type family `tys`, and a
continuous `x ∈ archCutSubmodule F tys`, the span of
`{fun g => x (g * adelicArchGLIncl F (ι κ)) | κ}` is finite-dimensional, all its members are
continuous, it lies in `archCutSubmodule F tys`, and it is stable under each right translate
`κ ↦ v (· * adelicArchGLIncl F (ι κ))`. The 184-line `S_` file is the ground's two lemmas, a private
`spanOn ι s f` (the translate span restricted to the products supported at a finite place set `s`) and
a **90-line private `finiteDimensional_spanOn_and_le`** — a `Finset` induction over `s`, the `insert`
step splitting `κ = Pi.mulSingle w (κ w) * κ'`, applying the ground's
`adelicArchGLIncl_iota_mulSingle`, and closing by the ported per-place
`CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`
(`Cusp/ArchTypeSpan.lean`, statement-diffed) with `Submodule.finiteDimensional_iSup` — and a 40-line
`solution` that instantiates the induction at `s = univ` and repackages in the wrapper's four conjuncts.
**That per-place node is the row's only graph premise** (`needs 1`), which is why the row reads ready;
the package is the work.

**M2 `finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule` (459).** For `f ∈ archCutSubmodule F
tys`, the span of the right translates `ψ = rightTranslate F k f` over `k` in the range of the product
`⨆ w, (rowIsometryInclAt₀ F w).range` is finite-dimensional. The pin's proof is the whole
`F4CutWords` block: the arch product group `archProdIncl`, its compactness
(`isCompact_rowIsometrySubgroup₀`, `isCompact_iSup_range_rowIsometryInclAt₀`), the carrier
`Ecf`/`ρc`, `orbitSpan`, the per-place span, and the `orbitSpan_eq_span` dictionary. **All of these are
in the port** (`ArchCompactOrbit`, `ArchCutProjector`, `ArchApproxIdentity/ArchInfra`); the row's own
content is the last 30 lines.

**M3 `finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule` (222).** The same for
`archDualCutSubmodule`. The pin's `S_` proves it from `orbW` and the two private inductions
(`finiteDimensional_orbW_of_mem_typeSubmodule`, `…_of_mem_iSup`); the port's `placeOrbitSpan` is that
`orbW` and the two inductions are `finiteDimensional_placeOrbitSpan_of_mem_archTypeSubmoduleAt`
(statement-diffed) — so this row is 182 net lines, most of them the pin's own statement-level
translation of the dual.

**M4 `exists_continuous_conj_invariant_integral_mul_apply_mul_eq_…` (998).** For a finite-dimensional
`E ≤ archCutSubmodule F tys` of continuous functions, stable under right translation by the product of
row isometries, there is a continuous `e : ∏_w K_w → ℂ` with `e (κ' κ κ'⁻¹) = e κ`, `e κ⁻¹ = conj (e κ)`,
`e` in the dual type modules and `κ ↦ e κ⁻¹` in the type modules, and the reproducing identity above.
The 998-line `S_` file is `TypedCoeff` (the generic coefficient engine, already in the port as
`RepTheory/TypeReproducer`), `TypeIdem` (the two dictionary lemmas, the manager's ground), and then a
≈480-line `solution` that averages `Pm` over the compact group by Haar, proves the integrated matrix
`Hm` invertible (`Hm_mulVec_injective` from a positivity integral), builds the kernel
`e = Σ … Pm …`, and identifies it as the unique reproducing element by an L² argument
(`hL2zero`/`huniq`), then reads off conj-invariance, inversion-reality and the two type-module
memberships. **The row consumes `isCompact_rowIsometrySubgroup_detOne` (SET-AF2's M1-5) for the
`CompactSpace` instance** — this is the AF2-created readiness, and the reason the row is on the shelf
at all.

## 3. Homes — two new worker modules above a landed ground

The "above all premises" search: the rows' premises are `MaximalCompactFactors` (998),
`Cusp/ArchTypeSpan` (184), `ArchCutProjector`/`ArchCompactOrbit`/`ArchInfra` (459, 222) and the
definition layer (`IsotypicCuspSpace`, `ArchType`, `Cusp/Constituent`). **Insertion is impossible for
184 and 998**: `ArchCutProjector` and `ArchTypeSpan` are *premises*, so nothing holding 184 can sit
below them; and `ArchType` is a legacy `PORT_FILES` module (its own migration is out of scope here).
A new module is cascade-free and matches the pin's role split.

| # | module (all new) | imports | holds |
|---|---|---|---|
| 1 | `Adelic/ArchComponentDictionary.lean` (**landed**) | `Adelic/ArchType`, `Adelic/IsotypicCuspSpace` | G (2) |
| 2 | `Adelic/ArchCutSpan.lean` | 1, `Adelic/ArchCutProjector`, `Adelic/ArchApproxIdentity/ArchInfra`, `Adelic/Cusp/ArchTypeSpan`, `Adelic/Cusp/Constituent`, `Adelic/IsotypicCuspSpace` | M1, M2, M3 (3) |
| 3 | `Adelic/ArchCutReproducer.lean` | 1, `RepTheory/TypeReproducer`, `Adelic/MaximalCompactFactors`, `Adelic/IsotypicCuspSpace`, `Adelic/Cusp/Constituent` | M4 (1) |

**Import-direction check.** Module 1 imports only frozen modules; 2 and 3 import 1 and the port, and
nothing of each other. Do **not** let 3 import 2: the two lanes must stay independent, or the second
worker's build drags the first's file in. The ground holds the two dictionary lemmas *public* — both
consumers need them, and neither would be the other's premise if they were private in one of them.

**Namespace.** Keep the pin's `AutomorphicForm`. The rows are stated at the wrappers' binders; the
ground's two declarations are at the pin's names (`ext_archComponent`,
`adelicArchGLIncl_iota_mulSingle`).

**No legacy module, no migration, no promotion.** The two proof modules are new; the ground is new;
no existing module is edited, and no existing port declaration changes visibility (the ground writes
the pin's two *pin-private* helpers public, which the checker reads as `promoted` from the wire's side,
not as a port promotion). `ArchType` is a legacy `PORT_FILES` module and stays untouched (that is
the reason the ground re-states `ext_archComponent` instead of inserting it there: a legacy touch
carries its whole migration, and the mathematics — the dictionary both *rows* use — is a subject of
its own at this point in the tree).

## 4. Ground prep (the manager's)

### 4.1 The ground — landed

`FLTForHuman/AutomorphicForm/Adelic/ArchComponentDictionary.lean` (**+65 lines, 2 declarations**),
wired by two `spec-pin:` lines (the two `S_` files, the pin's own copies being `private`):

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---|---|
| G | `Adelic/ArchComponentDictionary.lean` (**+65**) | **2 ok** / 0 / 0 / 0 own | silent, **3.1 s**, zero warnings | `[propext, Classical.choice, Quot.sound]` ×2 |

Both declarations match the pin's **pin-private** copies through the checker's fallback, which is the
AF2 pattern: a public port declaration whose statement is a pin-*private* one reads `ok`. `dedup
--within` 0 clusters, `move_dead` 0 dead, `unwired_register --check` current. It is tier 1 through its
own wires — no `SOURCES` append, no `PORT_FILES` row, no marker.

### 4.2 The wires the workers write

- Module 2: **six** `spec-pin:` lines — per row the `Theorems/Thm_…` wrapper and the `P2M/Sol/S_…` file
  marked `-- comparable copy` (3 rows × 2).
- Module 3: **two** `spec-pin:` lines — 998's wrapper and its `S_` (`-- comparable copy`).

### 4.3 Markers: none, unless a public helper appears

Every headline is at the wrapper's name and every helper stays `private` (the pin's own helpers are
private; the port's engine modules are imported instead). If a public declaration beyond the four
headlines turns out to be needed, it is a `spec/decl_markers.tsv` row (`own:`), not an in-source
comment — and the manager writes it.

### 4.4 The consumer zone (after the landing)

`spec/AutomorphicFormSetAF3Consumer.lean` (**landed**, 90 lines, 0 errors, two zones, no `#check`):
- **zone A**: the two span rows composed — 184's four-conjunct package applied to a vector known to be
  in the cut, then 459's span finite-dimensionality read off its first conjunct;
- **zone B**: 998's kernel composed with the projector API — the reproducing identity instantiated at
  `x = 1` (so the kernel reproduces `v 1`) and at the dual cut.
The zone's error count is the deliverable metric; the probe must break if either module is deleted.

### 4.5 The definition-wire sweep — landed

The §0.3 finding was not unique to the ten AF-row gates: **thirty-two** port modules transcribed a pin
`Def_` module and wired it with one `-- pin:` marker per declaration instead of a `spec-pin:` header.
All thirty-two are now upgraded, in one manager pass:

| before | after |
|---|---|
| 32 modules, **684** per-declaration `-- pin:` markers, no `spec-pin:` line | 32 modules, **0** markers, **32** `spec-pin: Definitions/Def_….lean` wires |
| 6 of them listed in `PORT_FILES` (legacy route) | those 6 rows retired (`SOURCES` rows kept) |
| declarations tier 3 (registered, not diffed) | tier 1 (statement-diffed) |

**Checker, all 32 modules: 686 ok, 0 mismatch, 0 missing, 6 own, 0 kw.** The six `own:` rows are the
only statements the wire cannot reach, all recorded in `spec/decl_markers.tsv` with the reason: three
statements the pin writes through `Ideal.inertiaDeg'` (deprecated at `v4.34`; the port uses
`Ideal.inertiaDeg`), `AlgEquiv.extendScalars` (`AlgHom.restrictDomain` → `AlgHom.domRestrict`), and one
port-own `IsBiscalar` instance with no pin counterpart. The register fell from 139 modules / 4,024
public declarations to **113 / 3,478**.

The check exposed no mathematics: every failure was a mathlib rename or a port-own helper, and the
shelf is **unchanged** by the sweep (`needed` 910 / 373,361, AF 27 / 6,669, AF leaves 84 / 17,279 — the
same corrected read as §0.1), because the frontier's ported set is by declaration name, not by wire.
All 32 modules build silently after the comment-only edit. This is the prerequisite the AF3 orders
assumed: the rows they import (`BorelSubgroup`, `EtaFamily`, `InducedSection`, `WeylIntertwining`,
`LocalOrbitalBase`, `TwistedOrbital`, `AdelicFourier`, `TateGlobal/Defs`, `TateLocalZeta`,
`LinearAlgebra/Countable`) are tier 1 with a `spec-pin:` wire.

### 4.6 After the landing

`dedup.py --within` on both modules; `dedup.py --cross` against the engines they import;
`move_dead.py --source <module> --target <Reserve/…> --select dead --dry-run` on every module (the
tool needs a target, even for a report); `unwired_register.py --check`; the §8 shelf re-read; and the
FR-0095 shadow diff on the new modules' `private` names against the unported last names.

**Done, with the verdicts**: `dedup --within` 0 clusters ×3 (span 10 declarations, reproducer 2,
ground 2); `dedup --cross` 0 clusters between the set's modules (the arch-engine cross-check returns
only the pre-existing `ArchKFiniteFamily`/`ArchKFiniteFamilyTheorems` wrapper-over-engine pair);
`move_dead --dry-run` **0 declarations / 0 lines** in all three modules. One dedup *fix* came out of
the pass: the ground's `ext_archComponent` was a duplicate of the `private
ArchKFiniteFamily.eq_of_forall_archComponent_eq` proof (a copy `dedup` cannot see, private), and that
module now imports the ground and keeps the name as a one-line alias (`omit [NumberField F]`, so the
unused-section-variable linter stays quiet). `move_dead` also reports one **pre-existing** dead
private block in `ArchKFiniteFamily` (`adelicArchGLInclAt_mul_comm`, 18 lines, referenced by nothing
in the module, identical verdict on the pre-edit file) — left in place: that module is a tier-3 engine
and the block is pin completeness content, the exemption `instructions.md` grants.

## 5. Per-step traps

**M1 (184).** (i) The `solution` is 40 lines but the row's body is the private 90-line
`finiteDimensional_spanOn_and_le`; the statement is a four-conjunct conjunction — keep the wrapper's
conjunct order and the `hxc`/`hxt` binder names. (ii) `ι` and `hι` are *hypotheses*, not instances: do
not instantiate `ι := inclArch F`. (iii) The induction is a `Finset` induction over a place set `s`,
with the `insert` step splitting `κ = Pi.mulSingle w (κ w) * κ'` — that split is where G's
`adelicArchGLIncl_iota_mulSingle` enters, and the per-place finite-dimensionality is the ported
`CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`. (iv)
`[DecidableEq (InfinitePlace F)]` is *not* in this row's binders: write `classical` inside the proof
(the pin's file does), do not add a binder.

**M2 (459).** (i) The `⨆ w, (rowIsometryInclAt₀ F w).range` is a supremum of ranges in
`AdelicGL2 (𝓞 F) F` — the port's `ArchCutProjector.orbitSpan` is stated with the same index; do not
re-spell it as a product group. (ii) `rightTranslate` is `Cusp/Constituent`'s, not a local one. (iii)
`isCompact_rowIsometrySubgroup₀` is `ArchInfra`'s (it carries `[ProperSpace K]`); the pin proves its own
copy at 34 lines — import the port's. (iv) The per-place lemma is ported
(`ArchCutProjector.finiteDimensional_placeOrbitSpan_of_mem_archCutSubmodule`); the *product*-level
combination over `ArchIsometryProd` is this row's own content (the pin's `PartB8`), and
`orbitSpan_eq_span` is the dictionary that lets it be stated on the `⨆`-index. **The landing found the
pin's FD-only `finiteDimensional_orbitSpan_of_mem_archCutSubmodule` is merged, in the port, into
`mem_Ecf_of_mem_archCutSubmodule` with an added `Continuous` hypothesis** — so M2 and M3 were routed
through the pin's `exists_finiteDimensional_stable_of_forall_mem_iSup_typeSubmodule` envelope instead
(§1.5). A future row that needs the FD-only form should promote it in `ArchCutProjector` rather than
re-derive it.

**M3 (222).** The pin's `orbW` is the port's `placeOrbitSpan`; its two private inductions are
*not* the port's `finiteDimensional_placeOrbitSpan_of_mem_archTypeSubmoduleAt`, which is stated for
`ArchRepAt` (`Fin n → ℂ`) and cannot express `Module.Dual ℂ (Fin n → ℂ)` — the landing states them for
an arbitrary finite-dimensional `ρ` (the pin's own statement) and instantiates at `ρ.dual`. The dual
cut's membership normal form is `mem_archDualCutSubmodule_iff` (port), so the `iSup` induction is over
the same `Fin (tys.card w)`.

**M4 (998).** (i) The `E` hypotheses (`hE`, `hEc`, `hEt`, `hEK`) are all explicit; `hEK` states
stability under `adelicArchGLIncl F (ι κ)` for *every* `κ`, and the proof needs it pointwise. (ii) The
statement's `∃ e` body is a six-conjunct conjunction — transcribe in the wrapper's order. (iii) The
pin's `set_option maxHeartbeats 3200000 in solution` is **not** transcribed: run the edit loop at
`-DmaxHeartbeats=1000000` and **report** a wall (the project cap is 4M; this is the row of the set that
may need it), never add `set_option`. (iv) `Pm`/`Hm`/`Dm` are `TypeReproducer`'s — but they are **not on this row's path**: the pin
builds its own Gram matrix over a basis of the orbit span and never touches the positivity engine.
The landing imports only the two `ArchApproxIdentity` coefficient lemmas (the private `typedCoeff`
composes them, in the port's `lam v` binder order); the rest of the engine import is the order's, and
unused. (v) The
`hL2zero` argument integrates `‖g‖²` against the Haar probability: `integrable_const` + `mono'` is the
pin's route and the port's `hint` lemma is its local version. (vi) `e κ⁻¹ = conj (e κ)` is proved from
`∫ κ, e κ * conj (e (κ * s)) = conj (e s)` and right-invariance of `μ` — both sides of the Haar
identity are already ported under `integral_mul_right_eq_self`/`integral_mul_left_eq_self`.

## 6. The gates, per order

As in SET 6–10, SET-AF1/AF2 and the recipe §6:

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; expect the span module
   **3 ok** and the reproducer **1 ok** (the ground is 2 ok, landed).
2. `#print axioms` on all four headlines → `[propext, Classical.choice, Quot.sound]`.
3. Each module's own `lake build` under `flock`/`timeout 110`; **silent** (zero warnings). No tree
   build, no dependents.
4. `dedup.py --within --module <module>`; `move_dead.py` — 0 dead expected (a `Def`-free theorem module
   with four consumers).
5. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats`.
6. The consumer zone of §4.4: its error count, and it must break if either module is deleted.

## 7. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. **the cut** | **the arch-cut quartet: 4 rows / 1,863 silo / 1,098 net**, two worker modules | the alternatives are the arch-derivative chain (1,190 net), `LocalIntertwining` (1,393 net) and `CuspidalConstituent` (1,406 net); this one is the shelf's head, AF2's named pair, and the highest-reuse cluster |
| 2. **the homes** | **two new modules**, span and reproducer, above the landed ground | insertion is impossible for 184/998 (their own premises are the candidate hosts) and `ArchType` is legacy; a new module is cascade-free |
| 3. **the split** | **three span rows in one module, the kernel in the other** | by closure: the span module needs the projector/ArchTypeSpan engines, the reproducer needs only `TypeReproducer` + AF2's compactness; one module would make every span consumer drag the 1,306-line RepTheory engine in |
| 4. **the ground** | **a 2-declaration module, `pin:`-private copies made public at the pin's names**, landed by the manager | both lanes need both lemmas; writing them privately in each module would duplicate 24 lines, and `ArchType`/`ArchKFiniteFamily` are legacy/private homes |
| 5. **the 459 row** | **cut it here, as AF2 §9 scheduled it with 184** | it is the arch-cut sibling of 184, and the two share the `orbitSpan` engine; cutting them apart would pay the engine twice |
| 6. **the dispatch** | **orders 2 and 3 concurrently after order 1** | the files and the imports are disjoint; only the build lock is shared |
| 7. **the merged FD-only lemma** | **do not promote it now**; the envelope route (§1.5) is one engine, not two | promoting `finiteDimensional_orbitSpan_of_mem_archCutSubmodule` in `ArchCutProjector` would put a second envelope engine beside `mem_Ecf_of_mem_archCutSubmodule`; take it when a row states it without `Continuous` and without the `tys`-index |

## 8. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af3.json   # §0.1
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
    --unport AutomorphicForm.continuous_unipotentGL2 --json > build/shelf-af3-corr.json                  # §0.2
python3 frontier.py --selfcheck                                                                          # PASS
python3 port_advise.py --with-defs --nodes <the four> --json build/af3-arcut-advise.json                 # §0.5/§1.3
python3 port_plan.py --json build/af3-arcut-advise.json                                                  # 1,098 net
python3 twin_scan.py --node <each of the four>                                                           # new × 4
# from lean/, the definition gate at the declaration:
python3 spec/gate_scan.py --pin Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean \
    --rows S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule
python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/ArchComponentDictionary.lean       # 2 ok (landed)
```

**What the set consumes**: 5 steps — 24 pin lines of ground (2 declarations, 65 written lines) and
1,863 silo of rows → **1,098 net new math lines**, two new worker modules, eight wire lines, one
landed ground module; 0 edits to existing modules, 0 imports added elsewhere, 0 port promotions, 0
migrations, 0 markers, 0 tree builds.

**Measured after the landing — twice**, as §4.5 requires, because the set's own private helpers could
manufacture a last-name shadow (FR-0095). The raw re-read and the `--unport` one differ by exactly the
AF2 shadow, so the correction is one node / 28 lines again:

| figure | before | forecast | measured (raw) | **measured (corrected)** |
|---|---:|---:|---:|---:|
| `needed [F terminal]` | 910 / 373,361 | 906 / 371,498 | 905 / 371,470 | **906 / 371,498** ✓ |
| `needed [literal]` | 923 / 376,836 | — | 918 / 374,945 | **919 / 374,973** |
| frontier F | 1,505 / 754,005 | — | 1,510 / 755,896 | **1,509 / 755,868** |
| `AutomorphicForm` ready rows | 27 / 6,669 | 25 / 5,487 | 27 / 6,248 | **25 / 5,487** ✓ |
| `AutomorphicForm` leaves | 84 / 17,279 | 82 / 16,598 | 81 / 16,570 | **82 / 16,598** ✓ |
| `AutomorphicForm` demand | 406 / 171,140 | — | 402 / 169,277 | **402 / 169,277** |
| `--selfcheck` | PASS | — | PASS (1,345 `Thm_` / 1,510 names) | PASS |

**Every forecast figure is exact**, and that is the set's own check on §1.3's pricing: 1,863 silo
consumed, 1,098 net written into the tree as 1,059 source lines (482 + 567) plus the ground's 65.

(The two ready rows consumed are 998 and 184; the two leaves are 459 and 222. The raw read's two extra
ready rows are the AF2 shadow pair (471, 290), restored to leaves by the correction — §0.2's mechanism,
not anything this set wrote: neither new module declares a name that shadows an unported node.)

**The rows this set unblocks but does not ready.** The four are a *premise* of ten unported rows /
6,657 silo, and two of them get to two remaining premises:

| row | silo | unported premises before → after |
|---|---:|---|
| `exists_rightConv_eq_of_archCutProjector` | 1,131 | 4 → **2** |
| `exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul` | 412 | 4 → **2** |
| `CuspidalConstituent.iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le` | 364 | 3 → **2** |
| `CuspidalConstituent.iSup_inf_levelInvariantSubmodule_principal_inf_archCutSubmodule_le` | 365 | 3 → **2** |
| `CuspidalSpectrum.exists_idempotent_archTypeProjector` | 1,219 | 6 → 5 |
| `exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact` | 935 | 7 → 5 |
| `exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional` | 860 | 8 → 6 |
| `CuspidalSpectrum.exists_norm_toCarrier_sub_lt` / `…_principal` / `…_of_forall_apply_mul_eq` | 446 / 497 / 428 | 12 → 10 |

So this set makes **no** row ready — unlike AF2, whose gate made three. Its return is the *depth*: it
is the admissibility prerequisite of the whole flat-family chain, and it takes the two nearest rows
(`exists_rightConv_eq_of_archCutProjector` and the `exists_isFactorizableTestFn_…` row) to two
premises each. That is the honest §7 answer, and it is why the recipe's "read the delta" is a count of
premises removed, not of rows created.

## 9. What this set does not do

- **The three big ungated families.** The arch-derivative chain (6 rows / 1,745 silo / 1,190 net), the
  `LocalIntertwining` atom family (8 / 1,578 / 1,393 net) and `CuspidalConstituent` (nine rows / 1,593
  silo / 1,406 net: the six leaves, `rightConv_rightTranslate_…` 35, and the ready 214 and 56) are
  each a story; §9 of SET-AF2 named the first three as the column's next sets, and they stay named
  here. Each is a whole order of its own.
- **The remaining declaration-level gates** (§0.3) — eight small items: `FnTwist.det_centralScalar` (4
  pin lines), `RationalTorusUnipotentQuotient` (15), `RationalCentreUnipotentQuotient` (5),
  `IwasawaShellIndex` (44), `BoundedGenuineCuspRealization` (3), `HeckeEigenfunction` (6),
  `UnramifiedWhittaker_HeckeRecursion.placeEmbed` (8) and `IdeleProductMeasure` (5). Each unblocks at
  most three rows and none is a story by itself; they are a **definition sweep**, not a set — the
  manager's next definition-layer order, to be taken when a row behind one of them is cut.
- **The two vanished AF2 shadow rows** (471, 290). They are not ready; they are waiting on
  `AutomorphicForm.continuous_unipotentGL2`, the leaf, and belong with the factorizable-test-function
  cluster.
- **The ready rows 214 / 56 of `CuspidalConstituent`** and the arch-type-span family. They are the
  next story of the same cut theory (`⨆`-spans inside a cuspidal constituent), but their subject is
  the constituent, not admissibility, so they are not this set.
- **Anything behind the prunable complex-analytic subject**: the withheld 4 / 831. No new `Def_`
  module, no promotion, no migration, no tree build.

## Appendix A — the 27 `AutomorphicForm` ready rows, 6,669 silo (corrected read, **before** the landing)

The set consumed 998 and 184 from this table; the shelf now reads 25 / 5,487 (§8).

| row (`AutomorphicForm.` dropped) | silo | prem | lev | gate |
|---|---:|---:|---|---|
| `exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule` | 998 | 1 | 5/6 | **◀ M4** |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | — |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | — |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4/10 | `FnTwist` 4 |
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14/63 | — |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | — |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | — |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2/2 | — |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3/20 | — |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | — |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | — |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | — |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | — |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | `UnramifiedWhittaker` 8 |
| `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 208 | 2 | 4/12 | — |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | — |
| `finiteDimensional_span_translates_of_mem_archCutSubmodule` | 184 | 1 | 6/7 | **◀ M1** |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | — |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | — |
| `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 146 | 1 | 1/2 | `BoundedGenuineCuspRealization` 3 + `UnramifiedWhittaker` 8 |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | `UnramifiedWhittaker` 8 |
| `isKfSmooth_rightConv` | 70 | 1 | 7/21 | — |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | — |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | — |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | — |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2/3 | — |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | — |

total 27 rows / 6,669 silo. `gate` is the declaration-level gate of §0.3 (`—` = writable today;
a number is the unported pin lines). **◀** marks the set's rows.

## Appendix B — the 84 `AutomorphicForm` leaves, 17,279 silo (corrected read, **before** the landing)

The set consumed 459 and 222 from this table; the shelf now reads 82 / 16,598 (§8).

| row (`AutomorphicForm.` dropped) | silo | prem | lev |
|---|---:|---:|---|
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 0 | 3/4 |
| `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype` | 695 | 0 | 2/2 |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 0 | 2/4 |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 0 | 1/1 |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 0 | 2/2 |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 0 | 1/3 |
| `finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule` | 459 | 0 | 2/3 |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 0 | 1/2 |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 0 | 2/15 |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 0 | 2/7 |
| `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` | 404 | 0 | 2/2 |
| `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` | 401 | 0 | 8/9 |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 0 | 3/4 |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 0 | 1/2 |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 0 | 1/1 |
| `LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div` | 362 | 0 | 1/1 |
| `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` | 347 | 0 | 1/1 |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 0 | 1/2 |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 0 | 2/3 |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 0 | 3/4 |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 0 | 1/1 |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 0 | 1/1 |
| `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` | 298 | 0 | 2/3 |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 0 | 5/10 |
| `archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one` | 250 | 0 | 2/2 |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 0 | 1/1 |
| `finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule` | 222 | 0 | 1/1 |
| `LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift` | 219 | 0 | 1/1 |
| `archDerivAt_commutator_of_isArchSmoothAt` | 208 | 0 | 1/4 |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 0 | 7/20 |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 0 | 4/5 |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 0 | 1/1 |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 0 | 1/4 |
| `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` | 184 | 0 | 8/14 |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 0 | 1/1 |
| `LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift` | 179 | 0 | 1/1 |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 0 | 1/1 |
| `LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` | 170 | 0 | 1/1 |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 0 | 1/5 |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 0 | 1/1 |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 0 | 8/19 |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 0 | 1/2 |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 0 | 4/8 |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 0 | 2/2 |
| `LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` | 147 | 0 | 1/1 |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 0 | 1/14 |
| `RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` | 141 | 0 | 1/1 |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 0 | 1/3 |
| `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` | 133 | 0 | 2/3 |
| `whittakerCoefficient_unipotentGL2_mul` | 123 | 0 | 17/54 |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 0 | 1/1 |
| `apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero` | 117 | 0 | 2/2 |
| `LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod` | 116 | 0 | 1/1 |
| `archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` | 110 | 0 | 2/3 |
| `continuous_whittakerCoefficient` | 108 | 0 | 3/14 |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 0 | 2/3 |
| `apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero` | 107 | 0 | 2/3 |
| `LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 102 | 0 | 1/1 |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 0 | 1/1 |
| `whittakerCoefficient_sum_smul_of_continuous` | 86 | 0 | 10/17 |
| `SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` | 81 | 0 | 1/2 |
| `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 0 | 2/2 |
| `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 0 | 1/1 |
| `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 0 | 2/4 |
| `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` | 71 | 0 | 3/22 |
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` | 70 | 0 | 3/8 |
| `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 0 | 1/1 |
| `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 0 | 1/1 |
| `existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 0 | 2/3 |
| `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` | 62 | 0 | 2/14 |
| `isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 0 | 2/2 |
| `CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 0 | 1/2 |
| `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 0 | 1/1 |
| `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` | 51 | 0 | 5/18 |
| `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 0 | 2/2 |
| `IsKfSmooth.finite_smul_image_of_isCompact` | 40 | 0 | 3/4 |
| `CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 0 | 1/2 |
| `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 0 | 2/10 |
| `continuous_unipotentGL2` | 28 | 0 | 8/122 |
| `exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 0 | 1/1 |
| `eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 0 | 1/1 |
| `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` | 21 | 0 | 17/48 |
| `constantTerm_add` | 13 | 0 | 1/2 |
| `constantTerm_smul` | 11 | 0 | 1/1 |

total 84 leaves / 17,279 silo. **◀** marks the set's leaves (459, 222). The other 82 are deferred
(§9): the arch-derivative chain, `LocalIntertwining`, `CuspidalConstituent`, the rational-quotient and
Iwasawa-shell gates, and the definition sweep of §0.3.
