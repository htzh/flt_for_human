# The right-convolution commutation twins

**Status: scoped, not started** (2026-10-11). This is the work order for the two
`AutomorphicForm` rows at the top of the Deligne–Serre ready shelf. It is written
after the foundation effort ([PORTING-AutomorphicForm.md](../PORTING-AutomorphicForm.md))
landed, which is what put the rows on the shelf, and after the pre-port instruments
were run on them (`port_advise`, `port_plan`; §1). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Method:
[porting-playbook.md](../../porting-playbook.md) §2.1 (measure), §2.3 (whole nodes),
§2.4 (dedup), §2.6 (scout), §3.3 (work order), §3.4 (sets), §3.5 (build ladder), §4
(faithfulness).

| | plain | compact (general) |
|---|---|---|
| node | `AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType` | `…_isLevelSphericalOfType_of_isCompact` |
| `S_` file | 3,440 lines / 277 decls | 3,425 lines / 270 decls |
| carrier | `U(N) = levelOne N ⊓ finiteAdelicGL2Subgroup F` | `U = O ⊓ finiteAdelicGL2Subgroup F`, `O` open, `U` compact |
| consumer | `CuspidalConstituent.exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType` (Schur scalar step) | `CuspidalSpectrum.exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact` → the cuspidal dichotomy |

Both rows are `needed 1` on the shelf. That number is a citation-name test and
**cannot see `Definitions/`**; §3 measures the definition closure the rows really
stand on, and it is the reason this is a two-stage topic and not one set.

## 1. The twin measurement (2026-10-11)

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType \
  --nodes AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact \
  --json build/ds-twin.json
python3 port_plan.py --json build/ds-twin.json --section all
```

- **One factoring unit, not two nodes.** `port_advise` reports 235 names proved in
  both files: **2,923 lines to write once** (2,954 removable across the pair). The
  strongest unit it finds is exactly this pair.
- A direct comparison of last names gives **266 shared**, of which **250 are
  statement-identical**. The 16 that differ are the two `solution` headlines plus
  fourteen helpers — `archNu*` (5), `glArch_eq_one_of_mem`, `isCompact_level_image`,
  `isOpen_level_slab`, `isOpen_glFin_preimage_image_level`,
  `levelSpherical_{continuous,eq_cut,hasCompactSupport}`,
  `convKer_comm_{of_types,slice}`, `adelicKernel_comm` — and every one of them
  differs by the *carrier* alone: `N`/`levelSubgroup F N` in the plain file,
  `U` in the compact one.
- **Budget.** `port_plan`: raw `S_` 6,865; duplicate copies 3,098; boilerplate 52;
  once-cost after dedup 3,715; already in the port 0; **net new math 3,715**
  (≈4.6–5.4k written at the port's measured 1.25–1.45 ratio), before the definition
  layer of §3. `frontier.py` prices the two rows at 3,440 + 3,425 because it prices
  per source-file node; the pair is one 3.7k-line job.
- **The `siblings` verdict is "not a free corollary", and it is right about the
  text.** Plain-only hypotheses: `(N : Ideal (𝓞 F))`, `hN : N ≠ ⊥`,
  `IsLevelSphericalOfType … (productionPinsOf … ).U N`. Compact-only:
  `(U O : Subgroup …)`, `IsCompact U`, `IsOpen O`, `hUO : U = O ⊓ finiteAdelicGL2Subgroup F`.
  Neither is a textual weakening of the other, so the tool will not call the plain
  one derivable. Mathematically the compact statement is nevertheless the general
  one: the plain file *proves* the side facts (`isCompact_level_image'`,
  `isOpen_level_image`, `isOpen_glFin_preimage_image_level`) that the compact file
  *assumes*. §5 makes testing that derivation the scout gate.
- The two rows' only cited theorem premise is
  `NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar` (91 citers) — landed in
  the foundation as `AutomorphicForm/AdelicHaar/MulRightInvariant.lean`. Everything
  else the wrappers name is a definition (§3) or pin `attribute [-simp]` plumbing
  the port drops.

Two instrument notes from this measurement:

- The pre-fix run reported "2 substitutions, 28 lines already in the port"
  (`haar_facts` matched to an unrelated `letI`-headed declaration). That was the
  `top_level_cut` `let`-binding defect, fixed 2026-10-11; the corrected run reports
  **0 substitutions / 0 already in the port**, and net new is 3,715, not 3,687.
- A work order for this topic must **not** quote the shelf's 6,865.

## 2. The mathematics

### 2.1 The statement

Right convolution against adelic Haar measure is the smoothing operator

> $`(\varphi * f)(g) = \int_{G} \varphi(gx) \, f(x) \, d\mu(x)`$, $`G = \mathrm{GL}_2(\mathbb{A}_F)`$

(`rightConv`, `Def_AutomorphicForm_RightConvolution.lean:9`). The theorems say the
two smoothing operators commute,

> $`(\varphi * f) * h = (\varphi * h) * f`$

when $`f`$ is *level-spherical* at $`U`$ and $`h`$ is a *factorizable* test function
bi-invariant under $`U`$, both archimedean-bi-finite of the same type family
$`\langle 1, \tau\rangle`$ with every $`\tau_w`$ irreducible. The two hypotheses are
the two halves of the classical "smooth by the level, test by the type" pair:
`IsLevelSphericalOfType` says $`f`$ is an archimedean factor times the indicator of
the level subgroup's image, and `IsFactorizableTestFn` + `IsArchBiFinite` say
$`h`$ factors over the two projections and is finite under the local type.

### 2.2 The reduction to a kernel identity

The convolution is associative against a Haar measure, and the iterated integral
re-associates by Fubini (`KernelReduction.rc_rc`, plain:742): for continuous
$`\varphi`$ and continuous compactly supported $`f, h`$,

> $`(\varphi * f) * h = \varphi * (h * f)`$

with the kernel $`h * f`$ the two-sided convolution of the two test functions
(`MeasureAssembly.adelicKernel`, `MeasureAssembly.rightConv_rightConv`,
plain:1104–1117). The headline therefore reduces to

> $`h * f = f * h`$

i.e. to the same statement at the level of kernels. Everything below proves that
identity; the last three lines of `solution` are only the re-association.

### 2.3 The projected-Haar frame

The pin abstracts the adelic group into a **frame** (`ProjectedHaar.Frame`,
plain:25–47): group homomorphisms

> $`\pi : G \to A`$, $`\pi_f : G \to B`$, $`\iota : A \to G`$, $`\iota_f : B \to G`$

with $`\pi \circ \iota = \mathrm{id}`$, $`\pi_f \circ \iota_f = \mathrm{id}`$, the
cross-composites trivial, and the **separation** axiom
$`\pi x = \pi y \wedge \pi_f x = \pi_f y \Rightarrow x = y`$. For the adelic group
the frame is `adelicFrame F` (plain:899):

| | adelic frame |
|---|---|
| `π` | `AdelicLevel.glArch` — the archimedean projection `GL₂(𝔸) → GL₂(𝔸_∞)` |
| `πf` | `AdelicLevel.glFin` — the finite projection `GL₂(𝔸) → GL₂(𝔸_fin)` |
| `ι` | `adelicArchGLIncl` |
| `ιf` | `AdelicDock.finEmbed` |

so `A = GL₂(𝔸_∞)`, `B = GL₂(𝔸_fin)`, and separation is the pin's
`eq_of_glArch_eq_of_glFin_eq` (plain:891) — the adelic group *is* the fibre product
of its two projections.

Against a frame and a subgroup $`U_f \le B`$ the engine defines

- `slab Uf = πf ⁻¹' Uf` — the set where the finite part is in the level,
- `level Uf = ker π ⊓ πf ⁻¹' Uf` — the level subgroup of $`G`$,
- `slice h u a = h (ι a · ιf (πf u))` — a two-sided translate of $`h`$,
- `cut fa = 1_{slab} · (fa ∘ π)` — a function living only on the slab and only
  through $`\pi`$,
- `nu = (μ ↾ slab).map π` — the pushed-forward measure on $`A`$, a Haar measure
  when $`μ`$ is one and the slab is open (`nu_isHaarMeasure`, plain:334).

The engine's theorem is `convKer_cut_comm` (plain:275): if $`h`$ is left- and
right-invariant under `level Uf`, then the ambient kernel identity for a cut
function follows from the **projected** identity on the slices:

> $`\mathrm{convKer}_\mu(\mathrm{cut}\,fa, h) = \mathrm{convKer}_\mu(h, \mathrm{cut}\,fa)`$
>
> $`\Longleftarrow \mathrm{convKer}_{\nu}(fa, \mathrm{slice}\,h) = \mathrm{convKer}_{\nu}(\mathrm{slice}\,h, fa)`$.

`MeasureAssembly.levelSpherical_eq_cut` (plain:1365) closes the loop: a
level-spherical $`f`$ *is* a cut, $`f = \mathrm{cut}\,fa`$ for an archimedean
spherical $`fa`$. So the ambient problem has been pushed entirely onto the
archimedean group, with the level folded into $`\nu`$.

### 2.4 Why the slices commute: multiplicity one for the type algebra

The projected identity is `SliceCentrality.convKer_comm_of_types` (plain:3251): for
$`fa`$ arch-spherical and $`\psi`$ with, at every infinite place $`w`$,

> $`\psi \in \mathrm{typeSpan}(\mathrm{leftRep}_w, \tau_w)`$ and
> $`\psi \in \mathrm{typeSpan}(\mathrm{rightRep}_w, \tau_w^{\vee})`$,

one has $`\mathrm{convKer}_{\nu}(fa, \psi) = \mathrm{convKer}_{\nu}(\psi, fa)`$ on
the archimedean Haar measure `archNu`. The invariance of $`h`$ under the level is
what puts each slice in those two spans (`TypeTransfer.isArchFactorBiFinite_slice`,
plain:2147, transported from the ambient group along $`\iota_f \pi_f u`$).

The span condition is a statement about the local representation $`\tau_w`$, and
it is where the real mathematics of the file sits (`BiIsotypic`, plain:2210–3200):

1. **Density.** For a semisimple $`k[K]`$-module $`L`$ isomorphic to a $`\tau`$
   (or $`\tau^\vee`$) isotypic component, the algebra image spans the relevant
   endomorphisms: `asAlgebraHom_mem_span_range`, `mem_span_range`,
   `exists_equiv_pi` (plain:2222–2341).
2. **Contraction.** `exists_matrix_of_commute` and
   `mem_span_range_of_isIsotypicOfType_dual'` (plain:2343–2438) contract a
   $`\tau`$-isotypic and a $`\tau^\vee`$-isotypic module against the pairing.
3. **The engine.** `span_translates_invariants_eq_top'` (plain:2440, 121 lines — the
   largest single shared proof) and its wrapper (plain:2561): the two-sided
   translates of the algebra-invariants span the whole module. `isIrreducible_dual`
   (plain:2584) is the input that needs $`\tau_w`$ irreducible, as the hypotheses
   promise. `le_span_translates_invariants` (plain:2768) is the converse inclusion
   used by the pairing.
4. **Pairing.** `pairing_symm_of_mem_typeSpan` (plain:3068) is the symmetry that
   makes the two kernels equal; `leftRep`/`rightRep`/`invMap` (plain:3107–3155)
   spell the two-sided action on functions, and
   `mem_typeSpan_leftRep_of_inv_mem` (plain:3173) is the $`h(x^{-1})`$ half of
   bi-finiteness.
5. **Assembly.** `SliceCentrality.convKer_comm_slice` (plain:3351) applies the
   above to $`\mathrm{slice}\,h`$; `adelicKernel_comm` (plain:3383) folds it back
   through `ProjectedHaar.convKer_cut_comm`; `solution` (plain:3420) finishes with
   the re-association of §2.2.

The archimedean side carries a second, independent commutation used for
invariance/self-adjointness: `AntiInvolutionHaar.convKer_comm` (plain:461–669) is
generic, and `PlaceClassData.convKer_comm_of_place_invariant` (plain:2046) applies
it to the place-wise anti-involution `thetaArch` of the infinite adeles, via the
conjugacy-normal-form algebra of `RotationConjugacy`/`HalfTurnConjugacy`/
`HalfTurnAxis` (plain:1383–1591).

### 2.5 The two variants

The compact file is the same development with the carrier $`U`$ kept abstract:

- `MeasureAssembly.levelSubgroup F N = levelOne N ⊓ finiteAdelicGL2Subgroup F`
  (plain:1060) is replaced by the hypothesis `hUO : U = O ⊓ finiteAdelicGL2Subgroup F`;
- `finiteAdelicGL2Subgroup F = ker glArch` (the pin's `glArch_eq_one_of_mem`), so
  the hypothesis says exactly that the compact group $`U`$ is cut out of the open
  group $`O`$ by trivial archimedean part;
- the plain file's `hN : N ≠ ⊥` exists only to make `levelOne N` open
  (`isOpen_level_image`), and its compactness comes from `isCompact_level_image'`
  plus injectivity of `glFin` on `ker glArch` (`eq_of_glArch_eq_of_glFin_eq`,
  plain:891).

So the port should write the shared home at the **general** (`U`) spelling and
derive the level-`N` statement, supplying `O := levelOne N` and the two side facts.
That is playbook §5's "generalise near-duplicates" applied across a whole file
rather than across a lemma.

## 3. The cone

### 3.1 The two `S_` files

Layer map of the plain file (the compact file is the same up to ~813 and differs
only in the carrier-carrying declarations; line ranges are sections, so they do not
sum to the file length):

| lines | layer | mathematics | shared? |
|---|---|---|---|
| 25–447 | `ProjectedHaar` | the frame, slab/level/slice/cut, `nu`, `convKer`, `convKer_cut_comm` | generic; identical |
| 461–669 | `AntiInvolutionHaar` | two-sided `convKer_comm` under an anti-involution | generic; identical |
| 675–777 | `KernelReduction` | `convKer`/`rc`, `rc_rc` (Fubini re-association) | generic; identical |
| 786–877 | `SecondCountableAdelic` | second countability, ideal generators | adelic; identical |
| 885–940 | `ProjectedHaar`/adelic | `adelicFrame` and its continuity | identical |
| 949–1011 | `MeasureGlue` | `glBorel`, `haar_facts`, `glArch_eq_one_of_mem`, `glFin_image_level` | adelic; identical |
| 1020–1119 | `MeasureAssembly` | `levelSubgroup`, `archNu`, compact/open level, `adelicKernel`, `rightConv_rightConv` | carrier-dependent |
| 1122–1287 | `KernelSides` | factors, indicators, linearity of `convKer` | generic; identical |
| 1290–1380 | `MeasureAssembly` | test-factor continuity/support, `levelSpherical_eq_cut` | mixed |
| 1383–1591 | `Rotation/HalfTurn/…` | 2×2 matrix algebra over `ℝ`/`ℂ`: rotations, half-turns, normal forms | generic; identical |
| 1594–2062 | `PlaceClassData` | place data, `thetaArch` anti-involution, `convKer_comm_of_place_invariant` | adelic; identical |
| 2067–2205 | `TypeTransfer` | pullback along a hom, type submodules, slice bi-finiteness | generic; identical |
| 2210–3200 | `BiIsotypic` | the multiplicity-one engine of §2.4 | generic; identical |
| 3203–3417 | `SliceCentrality` | `convKer_comm_of_types`, `convKer_comm_slice`, `adelicKernel_comm` | carrier-dependent |
| 3420–3440 | `solution` | the headline | separate |

Reading the column: **the 2,923-line shared block is mostly generic algebra and
representation theory**, not FLT mathematics. `ProjectedHaar`, `AntiInvolutionHaar`,
`KernelReduction`, `KernelSides`, `TypeTransfer`, `BiIsotypic` and the
matrix-conjugacy files mention neither the adeles nor `GL₂`; only `adelicFrame`,
`MeasureGlue`, `MeasureAssembly`, `PlaceClassData`, `SecondCountableAdelic` and
`SliceCentrality` do. By the port's own "a module is a mathematical role, not a
source file" (playbook §3.1) they belong outside `AutomorphicForm/`, and they are
the part most likely to be reusable by the next 129 modules of the layer.

### 3.2 The definition closure — the real price

The wrappers import `Def_AutomorphicForm_CuspidalConstituent`,
`Def_AutomorphicForm_ArchSpherical`, `P2M.Util` and the `S_` file; the two `S_` files
additionally import `Def_AdelicDock_LocalEmbedding`,
`Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace` and
`Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar`. Walking the
`Definitions/` import DAG by hand (the shelf cannot see it):

| | modules | pin lines | decls |
|---|---:|---:|---:|
| definition closure | 51 | 11,258 | 1,138 |
| fully present in the port | 15 | 2,723 | 344 |
| **not (or only partly) present** | **36** | **8,535** | **794** |

Of the closure, ~5,933 lines are declarations actually *named* in the two `S_`
files; ~5,325 lines are import-only (dragged in by the definitional imports of the
named ones). The biggest unported members are `Def_AutomorphicForm_IsotypicCuspSpace`
(1,062 lines / 124 decls), `Def_AutomorphicForm_CentreCutSiegelSet` (561),
`Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace` (576) and
`…_Equiv` (547), `Def_NumberField_AdelicBox` (537, 7/36 present),
`Def_AutomorphicForm_ProductionPinsGeneral` (468),
`Def_NumberField_SiegelVolume` (456), `Def_AutomorphicForm_SiegelCovering` (354) and
`Def_AdelicDock_LocalEmbedding` (372).

**Statement-critical is a small subset.** The only pin declarations the two
*wrappers* name that are not already landed are `IsLevelSphericalOfType`
(`Def_AutomorphicForm_ArchSpherical`, 66 lines), `ArchRepAt`, `ArchTypeFamily`,
`IsArchBiFinite` (`Def_AutomorphicForm_IsotypicCuspSpace`). Everything else in the
statement — `AdelicGL2`, `rightConv`, `IsFactorizableTestFn`, `productionPinsOf`,
`finiteAdelicGL2Subgroup`, `levelOne`, `heckeGen`, `adelicBox`, `IsArchTestFactor`,
`rowIsometrySubgroup₀` — is in the port from the foundation. The long
`attribute [-simp]` list at the head of each wrapper names `RestrictedProduct.*`,
`flatten_*` and `restrictedProductCongr*` lemmas; those are pin-side suppression
plumbing and need no port at all.

**Proof-critical** is the rest: the `S_` bodies name ~19 declarations of
`IsotypicCuspSpace` (the type-submodule/`ArchTypeFamily` vocabulary), 6 of
`AdelicDock_LocalEmbedding`, 6 of `LocalLanglands_HeckePair`, 6 of `ArchType` and
`RepTheory/SmoothVectors`, and the Siegel/cusp vocabulary of `CuspidalConstituent`,
`CentreCutSiegelSet`, `SiegelCoordinates`, `SiegelCovering`, `ArithCuspRealization`
and `SmoothCuspRealization`.

### 3.3 What this does to the plan

The two rows are **not schedulable on their own**. They are the doorway to the
143-module / 25,727-line `Def_(AutomorphicForm|RepTheory|AdelicDock|Deformations)`
layer that [PORTING-AutomorphicForm.md](../PORTING-AutomorphicForm.md) §1 counted as
its optional tail, and the honest sequence is definitions first (§4.3). The good
news is that the *proof* half of the work is unusually cheap per line: one generic
engine, one shared home, two statements.

## 4. The cut

### 4.1 Set D — the definition gate

Cut by mathematics, not by pin file (playbook §2.1). Each node is taken whole.

| set | homes | pin modules | pin lines |
|---|---|---|---:|
| **D-type** | `AutomorphicForm/Adelic/ArchSpherical`, `…/IsotypicCuspSpace` (+ the `AdelicBox` remainder) | ArchSpherical, IsotypicCuspSpace, AdelicBox | ~1,800 |
| **D-cusp** | `AutomorphicForm/Adelic/Cusp/*` | CuspidalConstituent, SmoothCuspRealization, ArithCuspRealization, SigmaAdelicAction | ~900 |
| **D-Siegel** | `AutomorphicForm/Adelic/Siegel/*` | CentreCutSiegelSet, SiegelCoordinates, SiegelCovering, SiegelReduction, WindowedSiegelTopology | ~1,500 |
| **D-measure** | `NumberTheory/AdelicVolume`, `…/AdelicCentre`, `AutomorphicForm/Adelic/Volume` | AdelicCentre, AdelicVolume, SiegelVolume, ContractionDecay, ScalingDichotomy | ~1,000 |
| **D-Hecke** | `AutomorphicForm/Adelic/Hecke*`, `LocalLanglands/*` | AbstractHeckeOperator, LocalLanglands_HeckePair, HeckeCosetSystem, HeckeEigensystem(Map), LocalNewvector_CongruenceSubgroupK1, M4aHerbrand_IdeleClassVocab | ~1,300 |
| **D-pins** | `AutomorphicForm/Adelic/ProductionPins*`, `AdelicDock/LocalEmbedding` | ProductionPins, ProductionPinsCompact, ProductionPinsGeneral, AdelicDock_LocalEmbedding | ~1,000 |
| **D-mathlib** | adopt mathlib, do not port | `Def_Mathlib_*` (8 modules) | ~1,530 |

`D-mathlib` is a decision, not a port: these are pin re-exports of mathlib facts
(`RestrictedProduct` topology/equiv, `Cofinite`, `Group.Units`, `Module.Quotient`,
`Bases`, `ContinuousMonoidHom`) written because the pin had to. Before each is
dropped, `#check` the corresponding mathlib name at `v4.34.0` and record the
substitution in `SOURCES`. That is the recorded-negative discipline of §2.2.

### 4.2 Set P — the proof half

| set | content | home | ≈ written |
|---|---|---|---:|
| **P0** | scout of §5 (`Scratch.lean`) | — | — |
| **P1** | the generic engines, written once and public | `RepTheory/ProjectedHaar.lean`, `RepTheory/TypeSpan.lean`, `RepTheory/BiIsotypic.lean`, `RepTheory/AntiInvolutionHaar.lean` | 2.3k |
| **P2** | the adelic instantiation | `AutomorphicForm/Adelic/RightConvComm/{Frame,MeasureAssembly,PlaceClassData,SliceCentrality}.lean` | 1.0k |
| **P3** | the general headline and the derived level headline | `…/RightConvComm/Compact.lean`, `…/RightConvComm/Level.lean` | 0.4k, or a few dozen lines if P0 succeeds |

P1 and P2 are new files and cascade on nothing (playbook §3.7 phase 2); P3 imports
them. One set per subagent, review between sets (§0.2), one build per wave (§3.5).

### 4.3 Order

Definitions first in their own import order (D-type and D-cusp can run in parallel:
they are disjoint cones), then D-Siegel and D-measure, then D-Hecke and D-pins, then
P1, P2, P3. The pin's own order is not the order (its `S_` file carries the whole
prelude before any of it is consumable). Keep the generic engines last among the
definitions but before P2 — they import only mathlib.

## 5. The scout gate

One `Scratch.lean` probe before P3 decides the whole shape of the topic:

> With `O := levelOne (𝓞 F) F N` and `U := MeasureAssembly.levelSubgroup F N`, can
> `AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType` be derived
> from `…_of_isCompact` by `hUO := rfl` (or `Subgroup.ext`), `IsOpen O` from
> `isOpen_level_image`/`isOpen_glFin_preimage_image_level`, and `IsCompact U` from
> `isCompact_level_image'` plus injectivity of `glFin` on `ker glArch`
> (`eq_of_glArch_eq_of_glFin_eq`)?

- **If yes**, the shared home is written at the $`U`$ spelling once and the plain
  headline is a specialization: the port writes one proof of 2,923 shared lines plus
  a derivation, and the level file shrinks to its public statement and side lemmas.
- **If no** (a hypothesis is genuinely stronger in one direction, or the instance
  transport does not line up), both proofs are transcribed and the dedup is still
  the 2,923-line shared home — P3 grows by ≈3.4k written lines.

The scout also settles the two `def`-level questions: whether `MeasureAssembly.archNu`
must be the pushed-forward measure or can be mathlib's Haar measure on the
archimedean group, and whether the `BiIsotypic` engine can be stated over
`Representation k K V` (as the pin does) rather than over functions on the
archimedean adeles.

## 6. Verification

- **Checker.** Every port module in `PORT_FILES`; every pin source in `SOURCES`
  appended last. Target `0 mismatched / 0 missing`. The 250 statement-identical
  shared names verify through the ordinary last-name lookup; the 16 carrier-carrying
  ones need the `SOURCES` order to put the *interface* copy (the general `U`
  spelling) first, with the level spelling reachable by its dotted name. Re-run the
  checker with `--prop-bodies` if any `def … : Prop` is promoted.
- **Consumer.** `spec/AutomorphicFormConsumer.lean` gains one zone per set, each a
  real executed cross-module composition: for P1 a concrete non-vacuous instance of
  the generic `convKer_cut_comm` on a finite group frame; for P2 the adelic frame's
  separation and `levelSpherical_eq_cut`; for P3 both headlines at a concrete
  `N = ⊤`/`levelOne` and at a compact `U`, proving the same identity two ways.
  Deleting any one module must break the zone.
- **Axioms.** `#print axioms` on both headlines returns
  `[propext, Classical.choice, Quot.sound]`; no `sorry` anywhere, including in
  `def`s.
- **Faithfulness.** Statements are transcribed from the `Theorems/` wrappers, which
  for these two are the statement authority verbatim (they differ from the `S_`
  copies only in the `p2m_exact_reverting` proof term). Public declarations keep the
  wrapper's binders; the `productionPinsOf` hypothesis must stay written as the
  wrapper writes it, not as its `levelSubgroup` unfolding, or the checker reports
  `MISMATCH` (playbook §4).
- **The engines are ours.** `RepTheory/ProjectedHaar` and `RepTheory/BiIsotypic` have
  no pin counterpart of that shape (the pin has them as private blocks inside an
  `S_` file). They need exemption entries only where a ported public name has no pin
  source; the pin-private blocks they replace come in through the dotted fallback.

## 7. Risks

| # | risk | mitigation |
|---|---|---|
| 1 | the def closure is bigger than the shelf suggests | §3.2 table; re-measure after each D set lands, since `D-type`/`D-cusp` unblock others |
| 2 | the level headline is not a corollary of the compact one | the §5 scout; budget P3 at the higher figure until it answers |
| 3 | the two engines are stated over functions but need `Representation`-level generality | scout the `BiIsotypic` statement shape; the pin's own generality (`MonoidAlgebra k K`, `IsSemisimpleModule`) is the guide |
| 4 | instance diamonds in the `archNu`/`glBorel` transport | transcribe the pin's local `letI`/`haveI`; build the measure layer after `D-measure` |
| 5 | same last name, different carrier across the two files | `SOURCES` order; dotted names for the 16 divergent declarations; the checker's pin-private fallback |
| 6 | the generic homes get re-derived by later automorphic work | write them as the pin does (public, general), not as private helpers of one file; they are the reason this topic is worth doing before the other 129 modules |

## 8. Reproduce

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType \
  --nodes AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact \
  --json build/ds-twin.json
python3 port_plan.py --json build/ds-twin.json --section all
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
python3 explore.py AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType
cd ../../lean
timeout 300 python3 spec/check_flt_statements.py
```

## 9. Sources

Pinned at `aa2d8b3`:

- wrappers: [`Thm_…_isLevelSphericalOfType.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean),
  [`Thm_…_of_isCompact.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.lean)
  (statement authority);
- proofs: [`S_…isLevelSphericalOfType.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean),
  [`S_…_of_isCompact.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.lean);
- definitions: [`Def_AutomorphicForm_ArchSpherical.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_ArchSpherical.lean),
  [`Def_AutomorphicForm_IsotypicCuspSpace.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_IsotypicCuspSpace.lean),
  [`Def_AutomorphicForm_RightConvolution.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_RightConvolution.lean),
  [`Def_AutomorphicForm_CarrierPins.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_CarrierPins.lean);
- consumers: [`Thm_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType.lean),
  [`Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact.lean).

In the port: `AutomorphicForm/Adelic/RightConvolution.lean`,
`AutomorphicForm/Adelic/FactorizableTestFn.lean`,
`AutomorphicForm/Adelic/CarrierPins.lean`, `AutomorphicForm/Adelic/ArchWeightChar.lean`,
`AutomorphicForm/AdelicHaar/MulRightInvariant.lean`.
