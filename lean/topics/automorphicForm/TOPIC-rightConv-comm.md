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

**The principal sibling, measured and folded in (2026-10-11).** The third silo
`S_…_isLevelSphericalOfType_principal.lean` (3,498 lines / 284 declarations) is the same
engine with `principalLevel` in place of `levelOne`. Re-running the two commands above with
the third node (`build/ds-trio.json`) gives raw `S_` 10,363; duplicate copies 6,454; distinct
declaration groups 304; **net new math 3,824** — i.e. **+109 lines** for the whole principal
headline. The shared block grows to **3,178 lines / 248 declarations across the three
files**: 269 declarations are shared by all three, 7 more by plain and principal only, and
the principal-only surface is 8 (`solution`, `finitePrincipalLevel`, `weylFin`,
`isOpen/isClosed/isCompact_finitePrincipalLevel`, `mem_principalLevel_iff_glFin`,
`mem_map_conj_iff` — the last already landed as
`AutomorphicForm.TestFnPrincipalLevel.mem_map_conj_iff`). The hand-check the parser cannot
make: `levelSubgroup`, `archNu`, `pins_U` and `glFin_image_level` each carry two *bodies*
under one name (level vs principal vs `U`), which the statement-only checker reads as
identical. The phase is therefore cut as a **trio**: deriving both specializations from the
general `U` spelling is what makes the third one a few dozen lines instead of a second
3.5k-line transcription.

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

*(Superseded 2026-10-11: the W7–W12 waves landed the remaining modules of this closure
and the gate is closed — see §4.7 and [WORKORDER-P-rightConv-comm.md](WORKORDER-P-rightConv-comm.md).)*

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
its optional tail, and the honest sequence is definitions first (§4.9). The good
news is that the *proof* half of the work is unusually cheap per line: one generic
engine, one shared home, two statements.

## 4. The wave plan

The definition gate is several sessions of work, so it is planned as waves, each one
work order and one coherent story, executed in import order. The wave boundary is
the **dependency frontier**, re-measured after each wave: the unported modules all
of whose in-cone `Definitions/` dependencies are already in the port. As of
2026-10-11 that frontier is 15 of the 51 closure modules.

| wave | subject | nodes | why now | state |
|---|---|---|---|---|
| **W1** | the adèlic box | `Def_NumberField_AdelicBox` (finish the half-ported node) | deps landed; the box is named by both headline statements | **landed** |
| **W2** | the centre and the projective quotient | `Def_NumberField_AdelicCentre` | deps landed; the PGL₂ vocabulary the cusp carriers use | **landed** |
| W3 | contraction decay on measure spaces | `Def_MeasureTheory_{ContractionDecay,ScalingDichotomy}` | mathlib-only; generic, so its home is not `AutomorphicForm/` | **landed** |
| W4 | the Siegel window topology | `Def_AutomorphicForm_{WindowedSiegelTopology,SiegelCoordinates}` | deps landed; the windowed-Siegel vocabulary | **landed** |
| W5 | the Hecke/local vocabulary | `Def_AbstractHeckeOperator`, `Def_AutomorphicForm_HeckeEigensystem`, `Def_LocalNewvector_CongruenceSubgroupK1`, `Def_M4aHerbrand_IdeleClassVocab` | mathlib-only; unblocks `ProductionPins*` | **landed** |
| W6 | the mathlib stubs | the eight `Def_Mathlib_*` modules (~1.5k lines) | a decision wave: `#check` each against mathlib, record the substitution, port only the residue | **landed** |
| **W7** | the definition gate, part 1 (ready set + Siegel chain) | `LocalLanglands_{HeckePair,HeckeCosetSystem}`, `AdelicDock_LocalEmbedding`, `AdelicVolume`, `CentreCutSiegelSet`, `SiegelReduction`, `SiegelCovering`, `SiegelVolume`, `SigmaAdelicAction`, `HeckeEigensystemMap`, `SmoothCuspRealization` | 11 modules; deps landed | **landed** |
| **W8** | the production pins and the arithmetic cusp realization | `Def_AutomorphicForm_ProductionPins`, `Def_AutomorphicForm_ArithCuspRealization` | `AdelicBox`/`SiegelVolume`/`SmoothCuspRealization` landed | **landed** |
| W9 | the compact production pins | `Def_AutomorphicForm_ProductionPinsCompact` | after W8's `ProductionPins` | **landed** |
| W10 | the general production pins | `Def_AutomorphicForm_ProductionPinsGeneral` | after W9 + W8's `ArithCuspRealization` + W7's `SiegelCovering` | **landed** |
| W11 | the isotypic cusp space | `Def_AutomorphicForm_IsotypicCuspSpace` | after W10 (+ landed `RightConvolution`, `SigmaAdelicAction`, `ArchWeightChar`) | **landed** |
| W12 | the cuspidal constituent and the archimedean spherical predicate | `Def_AutomorphicForm_CuspidalConstituent`, `Def_AutomorphicForm_ArchSpherical` | after W11; closes the definition gate | **landed** |
| **P0–P3** | the proof half (§4.9) | | the gate is closed; [WORKORDER-P-rightConv-comm.md](WORKORDER-P-rightConv-comm.md) | **landed** |

### 4.1 W1 — the adèlic box

**Subject.** The box `adelicBox K` is a fundamental domain for the diagonal image of
`K` in `𝔸_K`, of finite positive Haar measure and contained in a compact set.

**Why it is first.** Both headline statements name `adelicBox F` (it is an argument
of `productionPinsOf`), and the pin's theorem layer leans on the node hard: 417 pin
files mention `AdelicBox.adelicBox`, 480 the box vocabulary, 51 the continuity lemma
promoted below. It is also the one frontier node that is *half landed* — 7 of its 36
declarations are already in the port — so finishing it removes the "partially ported
file reads as unported" distortion of §2.3 rather than adding to it.

**Scope (whole node).** `Def_NumberField_AdelicBox`, 537 pin lines / 36 declarations,
of which 7 present (`integralFiniteAdeles`, `isOpen/isClosed/isCompact_integralFiniteAdeles`,
`algebraMap_mem_adicCompletionIntegers`, `valued_algebraMap` under
`NumberField.AdelicLevel` in `NumberTheory/AdelicLevel/IdealBall.lean`). The wave
lands the remaining 29 in a new `NumberTheory/AdelicBox.lean`, under the pin's
namespace `NumberField.AdelicBox`, in the pin's order:

- finite adèles: `ball_mem_nhds`, `exists_valued_sub_algebraMap_lt`,
  `exists_valued_algebraMap_sub_lt`, `exists_mul_mem_adicCompletionIntegers`,
  `algebraMap_{mul,add}_apply`, `exists_mul_mem_integralFiniteAdeles`,
  `exists_forall_valued_sub_le`, `exists_algebraMap_add_mem_integralFiniteAdeles`;
- infinite adèles: `infiniteBox`, `continuous_ringEquiv_mixedSpace`,
  `existsUnique_int_add_mem_infiniteBox`;
- the box: `adelicBox`, `existsUnique_algebraMap_add_mem_adelicBox`,
  `measurableSet_{infiniteBox,adelicBox}`,
  `isAddFundamentalDomain_adelicBox{,_adelicAddHaar}`;
- compactness and measure: `properSpace_completion`,
  `norm_apply_le_of_{isReal,isComplex}`,
  `exists_forall_norm_apply_le_of_mem_infiniteBox`,
  `exists_isCompact_infiniteBox_subset`, `exists_isCompact_adelicBox_subset`,
  `exists_isOpen_subset_adelicBox`, `measure_adelicBox_{lt_top,pos}`,
  `adelicAddHaar_adelicBox_{lt_top,pos}`, `isProbabilityMeasure_cond_adelicBox`.

**Route: mathlib-first, then the two ported modules.** `𝔸_K`,
`InfiniteAdeleRing.ringEquiv_mixedSpace`, `ZSpan.fundamentalDomain`,
`ZSpan.exist_unique_vadd_mem_fundamentalDomain`,
`ZSpan.fundamentalDomain_{measurableSet,isBounded}`,
`mixedEmbedding.latticeBasis`, `AdeleRing.principalSubgroup`, `IsAddFundamentalDomain`
and `ProbabilityTheory.cond_isProbabilityMeasure_of_finite` are mathlib `v4.34.0`.
The only port imports are `NumberTheory/AdelicLevel/IdealBall.lean` (the integral
finite adèles — do not re-derive) and, through it, `AdelicHaar`. Recorded negative:
no pin `Definitions/` module other than `AdelicBox` itself is on this path.

**The promotion the wave carries.** `continuous_ringEquiv_mixedSpace` is a *public
pin declaration of this node*, and the port re-derived it as a public helper in
`AutomorphicForm/Adelic/TestFnNearIdentity.lean` (a module whose header already
concedes the copy). W1 gives it its pin home and deletes the local copy, leaving
`TestFnNearIdentity` to import it. Same statement, one home: playbook §3.1.

**Deliverable.** `FLTForHuman/NumberTheory/AdelicBox.lean` (new; header in the house
style, pin line ranges and the promotion recorded), plus the one-file reorg in
`AutomorphicForm/Adelic/TestFnNearIdentity.lean`. Landed: the module builds
warning-free at `4.6 s`, the reorg cascade (`RightConvNeZero{,Principal,Arch}`) is
green, the checker reads `8153 identical / 0 mismatched / 0 missing` (+29, the new
declarations), and `spec/AutomorphicFormConsumer.lean` carries the W1 zone.

**Verification.** Definition layer, so coverage is by name: every one of the 36 pin
declarations present, none renamed. Add the module to `PORT_FILES` and the pin file
to `SOURCES` (last), and add a `spec/AutomorphicFormConsumer.lean` zone that uses
`adelicBox`, `existsUnique_algebraMap_add_mem_adelicBox` and
`isProbabilityMeasure_cond_adelicBox` cross-module.

**Build discipline.** New file: edit loop `timeout 60 lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false NumberTheory/AdelicBox.lean`; the
`TestFnNearIdentity` edit is the wave's only cascade and is built in the same wave;
one `lake build FLTForHuman.NumberTheory.AdelicBox` at the end. No whole-tree build
(§3.5).

### 4.2 W2 — the centre and the projective quotient

**Subject.** `AdelicPGL2 R K = GL₂(𝔸_K) ⧸ center` is the projective linear group of the
adèle ring, with Borel σ-algebra `pglBorel` and Haar measure `adelicPGLHaar`; the centre
is the injective scalar image (`center_eq_range_scalar`, `scalar_injective`).

**Why now.** `Def_NumberField_AdelicCentre` is on the frontier — its only in-cone
`Definitions/` dependency, `Def_NumberField_AdelicHaar`, landed in D1 — and it is the
PGL₂ vocabulary that `Def_NumberField_AdelicVolume`, the Siegel-volume node, names. It is
a clean whole-node port with no promotion: the only non-mathlib input is the landed
`AdelicHaar/GeneralLinear.lean`.

**Scope (whole node).** `Def_NumberField_AdelicCentre`, 107 pin lines / 16 declarations
(pin lines 11–53 the general quotient, 55–103 the `NumberField` case), landed whole in a
new `NumberTheory/AdelicCentre.lean` under the pin's namespace
`NumberField.AdelicCentre`, in the pin's order:

- general: `center_eq_range_scalar`, `scalar_injective`, `AdelicPGL2`,
  `measure_image_mk_{pos,lt_top}`, `image_mk_subset_of_subset_mul_center`, `pglBorel`,
  `borelSpace_pglBorel`;
- `NumberField` case: `isClosed_center`,
  `t2Space/locallyCompactSpace/isTopologicalGroup_adelicPGL2`, `adelicPGLHaar`,
  `isHaarMeasure_adelicPGLHaar`, `adelicPGLHaar_image_{pos,lt_top_of_subset}`.

**Route: mathlib-first.** `Matrix.GeneralLinearGroup.scalar` and its
`center_eq_range_scalar`, `QuotientGroup.continuous_mk`/`isOpenMap_coe`/`eq`,
`Measure.haar`/`Measure.isHaarMeasure_haarMeasure` and the quotient-group
T2/locally-compact/topological-group instances are mathlib `v4.34.0`; the only port
import is `NumberTheory/AdelicHaar/GeneralLinear.lean`, through which the `GL₂(𝔸_K)`
topology and Haar measure arrive. Recorded negative: no pin `Definitions/` module other
than `AdelicCentre` itself is on this path, and none of the 16 declarations already
existed in the port, so the wave carries no promotion and no dedup.

**Drift adapted (statements unchanged).** `Set.mem_setOf_eq` in `isClosed_center` is the
deprecated alias of `Set.mem_ofPred_eq`, so only the proof term changes. The pin's
`letI`/`haveI` walls in `adelicPGLHaar`, `isHaarMeasure_adelicPGLHaar` and the two
`…_image_*` wrappers are kept verbatim, with the file's one
`set_option linter.style.haveILetI false` (house style, as in the other measure modules).

**Deliverable.** `FLTForHuman/NumberTheory/AdelicCentre.lean` (new; header in the house
style with the pin line ranges recorded). Landed: the module builds warning-free at
`7.0 s` (3,449 jobs), the checker reads `8169 identical / 0 mismatched / 0 missing`
(+16, exactly the node's declaration count), and `spec/AutomorphicFormConsumer.lean`
carries the W2 zone.

**Verification.** Definition layer, so coverage is by name: all 16 pin declarations
present, none renamed. The module is in `PORT_FILES` and the pin file in `SOURCES` (both
last). The consumer zone exercises `scalar_injective`, `isHaarMeasure_adelicPGLHaar`,
`adelicPGLHaar_image_pos` and `adelicPGLHaar_image_lt_top_of_subset` cross-module. A
one-token mutation of `measure_image_mk_lt_top`'s statement moved the count to exactly
one `mismatched` and was reverted.

**Build discipline.** New file: edit loop `timeout 300 lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false FLTForHuman/NumberTheory/AdelicCentre.lean`;
then one `lake build FLTForHuman.NumberTheory.AdelicCentre`, and the consumer probe is
the only cross-module check. No whole-tree build (§3.5).

### 4.3 W3 — contraction decay on measure spaces

**Subject.** Two generic measure-theoretic decay engines over an arbitrary group.
`ContractionDecay` cuts a set `S` into the `r`-scaled shells of a positive function
`φ`; if two elements `p, q` contract `φ` by `r` on the high part of `S` and stay in
`S`, the shell images are disjoint and the mass decays geometrically
(`measure_shell_le`), giving the doubling bound
`μ S ≤ 2 * μ (S ∩ φ ⁻¹' Iio (r * c))` and `μ S < ⊤` from the single low shell
(`measure_lt_top_of_measure_inter_lt_top`). `ScalingDichotomy` cuts a positive `f`
on `D` into `ℤ`-slices; a scaling element `z` (`f (z * g) = r * f g`, `D`
invariant) makes every slice the same measure, so `μ D = 0 ∨ μ D = ⊤`.

**Why now.** Both nodes are on the frontier, mathlib-only, and are the decay
arguments behind the Siegel-volume and centre-cut estimates the later waves consume:
the pin's `Def_NumberField_SiegelVolume` imports `ContractionDecay`, and
`Def_NumberField_AdelicVolume` imports `ScalingDichotomy`.

**Scope (whole nodes).** 248 pin lines / 17 declarations, landed whole, one pin
module per home:

- `Def_MeasureTheory_ContractionDecay` (149 lines / 11 declarations) →
  `MeasureTheory/ContractionDecay.lean`, namespace `MeasureTheory.ContractionDecay`:
  `shell`, `shell_zero_eq`, `iUnion_shell`, `pairwise_disjoint_shell`,
  `measurableSet_shell`, `mul_le_of_mem_shell_succ`, `image_mul_shell_succ_subset`,
  `two_mul_measure_shell_succ_le`, `measure_shell_le`,
  `measure_le_two_mul_measure_inter`, `measure_lt_top_of_measure_inter_lt_top`;
- `Def_MeasureTheory_ScalingDichotomy` (99 lines / 6 declarations) →
  `MeasureTheory/ScalingDichotomy.lean`, namespace `MeasureTheory.ScalingDichotomy`:
  `zpowSlice`, `iUnion_zpowSlice`, `pairwise_disjoint_zpowSlice`,
  `measurableSet_zpowSlice`, `preimage_mul_zpowSlice_succ`,
  `measure_eq_zero_or_top_of_mul_preimage_eq`.

**Route: mathlib-first, and a new top-level home.** Both pin modules import only
`Mathlib.MeasureTheory.Group.Measure`; every lemma they use (`exists_nat_pow_near`,
`exists_mem_Ico_zpow`, `zpow_right_strictMono₀`, `measure_preimage_mul`,
`ENNReal.tsum_geometric`, `ENNReal.tsum_const_eq_top_of_ne_zero`, …) is mathlib
`v4.34.0`, and the two files are transcribed verbatim with **no drift adaptation**.
They mention neither the adèles nor `GL₂`, so by the mathematical-role cut
(playbook §3.1) they open the port's `MeasureTheory/` area rather than going under
`AutomorphicForm/`; the pin namespaces are kept. Recorded negative: none of the 17
last names existed in the port, so there is no promotion and no dedup.

**Deliverable.** `FLTForHuman/MeasureTheory/{ContractionDecay,ScalingDichotomy}.lean`
(new; headers in the house style). Landed: both build warning-free at `9.2 s` /
`9.4 s`, the checker reads `8186 identical / 0 mismatched / 0 missing` (+17, exactly
the two nodes' declaration count), and `spec/AutomorphicFormConsumer.lean` carries
the W3 zone.

**Verification.** Definition layer, so coverage is by name: all 17 pin declarations
present, none renamed. Both modules are in `PORT_FILES` and both pin files in
`SOURCES` (last). The consumer zone exercises `iUnion_shell`, `measurableSet_shell`,
`iUnion_zpowSlice`, `measure_le_two_mul_measure_inter`,
`measure_lt_top_of_measure_inter_lt_top` and
`measure_eq_zero_or_top_of_mul_preimage_eq` cross-module — concretely in `ℝˣ` with
the zero measure, the zone pinning a local Borel `MeasurableSpace ℝˣ` so the generic
`[MeasurableMul]` hypotheses have an instance. A one-token mutation of
`shell_zero_eq`'s statement moved the count to exactly one `mismatched` and was
reverted.

**Build discipline.** New files: edit loop `timeout 300 lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false FLTForHuman/MeasureTheory/<file>.lean`;
then one `lake build` of the two modules; the consumer probe is the only cross-module
check. No whole-tree build (§3.5).

### 4.4 W4 — the windowed-Siegel topology

**Subject.** The topology and coordinates of the windowed Siegel set.
`WindowedSiegelTopology` proves the window data continuous — the matrix entries,
`topNormSq`/`rowNormSq`, `localHeight`, `xWindowSq` of `GL₂(K)` and the archimedean
height `archHeight` — and derives that `1` is an interior point of
`integralWindowedSiegelSet c u` for `c < 1` and `u ≠ 0`, that the set is measurable
for the Borel structure, and that it contains a nonempty open subset.
`SiegelCoordinates` supplies the matrix coordinates behind the estimates:
`norm_det_sq_le` and `xWindowSq_nonneg`, the upper-triangular unit `upperUnit` with
its `localHeight`/`xWindowSq` scaling laws, and `xCoord` with the identification
`xWindowSq = ‖xCoord‖ ^ 2`, its affine transformation law, and transport along a
norm-preserving ring hom (with `norm_extensionEmbedding` the infinite-place case).

**Why now.** Both nodes are on the frontier: their only in-cone `Definitions/`
dependency, `Def_AutomorphicForm_WindowedSiegelSet`, landed in D6. They are the
windowed-Siegel vocabulary the centre-cut/cusp wave (W7+) states over, and
`SiegelCoordinates`' `upperUnit`/`xCoord` are the coordinate normal form its analytic
estimates use.

**Scope (whole nodes).** 392 pin lines / 35 declarations, landed whole in the
existing `WindowedSiegel/` theory directory:

- `Def_AutomorphicForm_WindowedSiegelTopology` (131 lines / 10 declarations) →
  `AutomorphicForm/Adelic/WindowedSiegel/Topology.lean`, namespace
  `AutomorphicForm.WindowedSiegel`: `continuous_entry`,
  `continuous_{topNormSq,rowNormSq,det}_gl`, `continuous_{localHeight,xWindowSq}`,
  `continuous_archHeight`, `one_mem_interior_integralWindowedSiegelSet`,
  `measurableSet_integralWindowedSiegelSet`,
  `exists_isOpen_subset_integralWindowedSiegelSet`;
- `Def_AutomorphicForm_SiegelCoordinates` (261 lines / 25 declarations) →
  `AutomorphicForm/Adelic/WindowedSiegel/Coordinates.lean`, namespace
  `AutomorphicForm.SiegelCoordinates`: `norm_det_sq_le`, `xWindowSq_nonneg`,
  `sq_mul_sq_le_rowNormSq_mul`, `localHeight_mul_mul_localHeight_le`, the
  `*_upper_entries_mul` laws, `upperUnit` with its four entry lemmas, the
  `{topNormSq,rowNormSq,coe,localHeight,xWindowSq}_map` transport block,
  `map_upperUnit`, `xCoord`, `ofReal_rowNormSq`, `topNormSq_mul_rowNormSq`,
  `xWindowSq_eq_norm_xCoord_sq`, `xCoord_upper_entries_mul`,
  `xWindowSq_eq_norm_xCoord_map_sq`, `norm_extensionEmbedding`.

**Route: mathlib-first.** The only port import is the landed `WindowedSiegel/Set.lean`
and, through it, `AdelicLevel/{Projections,Level}` and `Adelic/CarrierPins`.
`Units.continuous_val.matrix_elem`/`matrix_det`,
`Matrix.GeneralLinearGroup.mkOfDetNeZero`/`map`,
`RingHom.mapMatrix_apply`/`map_det`, `Complex.mul_conj`/`normSq_eq_norm_sq` and the
infinite-place isometry are mathlib `v4.34.0`; both files are transcribed verbatim
with **no drift adaptation**. Recorded negative: none of the 35 last names existed in
the port, so there is no promotion and no dedup.

**Deliverable.**
`FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/{Topology,Coordinates}.lean` (new;
headers in the house style). Landed: both build warning-free at `3.3 s` / `3.8 s`,
the checker reads `8221 identical / 0 mismatched / 0 missing` (+35, exactly the two
nodes' declaration count), and `spec/AutomorphicFormConsumer.lean` carries the W4
zone.

**Verification.** Definition layer, so coverage is by name: all 35 pin declarations
present, none renamed. Both modules are in `PORT_FILES` and both pin files in
`SOURCES` (last). The consumer zone exercises `continuous_xWindowSq`,
`one_mem_interior_integralWindowedSiegelSet`,
`exists_isOpen_subset_integralWindowedSiegelSet`, `xWindowSq_nonneg`,
`xWindowSq_eq_norm_xCoord_sq` and `localHeight_upper_entries_mul` (the last through
`upperUnit`) cross-module. A one-token mutation of `xWindowSq_nonneg`'s statement
moved the count to exactly one `mismatched` and was reverted.

**Build discipline.** New files: edit loop `timeout 300 lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false
FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/<file>.lean`; then one `lake build`
of the two modules; the consumer probe is the only cross-module check. No whole-tree
build (§3.5).

### 4.5 W5 — the Hecke/local vocabulary

**Subject.** Four definition nodes the `ProductionPins*` / local-Langlands layer is
stated over:

- `AbstractHeckeOperator` — on the fixed points `fixedPoints V A` of a subgroup
  `V ≤ G` acting on an additive commutative monoid `A`, the finite double coset
  `U * {g}` mod `V` defines `HeckeOperator : fixedPoints V A →ₗ[R] fixedPoints U A`,
  together with the `FixedPoints` instances (`AddCommMonoid`, `SMul`, `MulAction`,
  `Module`) that mathlib lacks, the reindexing `eq_finsum_quotient_out_of_bijOn'` that
  makes the value `U`-fixed, and the translation lemma `Set.bijOn_smul`;
- `AutomorphicForm.HeckeEigensystem` — the level/`a`/`b` eigenvalue datum, its
  `twist`, `AgreesAwayFromFinite`, `IsConstantOnFibers`, the Satake recursion
  `satakePow`, the base-change predicates `IsBaseChangeAt`/`IsBaseChangeOf`/
  `IsDescentOf`, and the `CuspidalityNotion`/`DescentPackage` bundles;
- `LocalNewvector` — the congruence subgroups `K₀(ϖⁿ)`/`K₁(ϖⁿ)` of `GL₂(K)` cut out
  by the lower-left (and `(1,1)`) entry mod `(ϖⁿ)`, their level-`0` identification
  with the range of `GL₂(R) → GL₂(K)`, the nesting/monotonicity lemmas, and the
  `p`-adic `padicK0`/`padicK1`;
- `M4aHerbrand` — the principal idèles, `IdeleClassGroup`, the `IdeleGaloisDescent`
  structure with its `unitsAct`/`classAct`, `ideleClassNorm`/`ideleClassDerive`, and
  the `identityDescent` inhabitant.

**Why now.** All four are on the frontier and mathlib-only: each imports nothing from
the pin's `Definitions/`, and they unblock the `ProductionPins*` and local-Langlands
waves. The Hecke-operator and congruence-subgroup nodes are named by
`Def_LocalLanglands_HeckePair`/`HeckeCosetLocal`, `Def_AdelicDock_LocalEmbedding` and
the `CuspForm` adèlic-lift theorems; the eigensystem by
`Def_AutomorphicForm_ProductionNotionGateEigensystems`, `SmoothCuspRealization` and
the Langlands–Tunnell dictionary; the idèle-class vocabulary by
`Def_M4aHerbrand_AdeleBaseChange`/`GenuineDescent` and the
`AutomorphicForm.SigmaAdelicAction`/`AdelicTracePushforward` carriers.

**Organization (the wave's own decision).** The four nodes are cut by mathematical
role, not by pin file (playbook §3.1), into three areas:

| pin node | home | namespace |
|---|---|---|
| `Def_AbstractHeckeOperator` | `RepTheory/AbstractHeckeOperator` | `FixedPoints`, `AbstractHeckeOperator` (top-level `Set.bijOn_smul`) |
| `Def_AutomorphicForm_HeckeEigensystem` | `AutomorphicForm/Adelic/HeckeEigensystem` | `AutomorphicForm` |
| `Def_LocalNewvector_CongruenceSubgroupK1` | `RepTheory/LocalNewvector/CongruenceSubgroupK1` | `LocalNewvector` |
| `Def_M4aHerbrand_IdeleClassVocab` | `NumberTheory/M4aHerbrand/IdeleClassVocab` | `M4aHerbrand` |

`AbstractHeckeOperator` and the congruence subgroups are generic/local representation
theory, so they open `RepTheory/` (the first as a sibling of the D2 foundations, the
second as the head of the `LocalNewvector` family, whose five further pin modules land
later); the eigensystem is automorphic vocabulary, so it sits in
`AutomorphicForm/Adelic/`; the idèle-class group is number-theoretic, so it opens
`NumberTheory/M4aHerbrand/` (13 further pin modules).

**Scope (whole nodes).** 544 pin lines / 48 declarations, landed whole; the
checker-visible surface is 45 (the three anonymous `FixedPoints` instances are
verified by the build, not the text checker).

**Route: mathlib-first.** All four nodes are pure mathlib — no pin `Definitions/`
input at all (the eigensystem's bare `import Mathlib` is replaced by
`NumberField.Basic` / `DedekindDomain.Ideal.Lemmas` / `RamificationInertia.Inertia`,
the house rule). `FixedPoints.addSubmonoid`, `finsum_mem_eq_of_bijOn`,
`Matrix.GeneralLinearGroup.map`, `QuotientGroup.congr`, `Units.mapEquiv`,
`Matrix.adjugate_fin_two` and the `p`-adic integers are mathlib `v4.34.0`; the bodies
are transcribed verbatim. **No promotion and no dedup**: none of the 45 checkable last
names existed in the port. Two drift adaptations, both non-statement: `Ideal.inertiaDeg'`
is deprecated in favour of `Ideal.inertiaDeg` but is kept in the statements for
checker fidelity, so `HeckeEigensystem.lean` carries `set_option linter.deprecated
false`; and the pin's one proof-level `letI` in the Galois product keeps its
`set_option linter.style.haveILetI false` (house style).

**Deliverable.** The four new modules above (headers in the house style). Landed: each
builds warning-free (`3.0 s`–`5.6 s`), the checker reads `8266 identical / 0
mismatched / 0 missing` (+45, exactly the checker-visible surface), and
`spec/AutomorphicFormConsumer.lean` carries the W5 zone.

**Verification.** Definition layer, so coverage is by name: all four pin nodes present
whole, none renamed. All four modules are in `PORT_FILES` and all four pin files in
`SOURCES` (last). The consumer zone exercises `FixedPoints.coe_add`, `Set.bijOn_smul`,
`satakePow` with a concrete `HeckeEigensystem ℚ ℂ` (`twist`/`twist_a`),
`congruenceK1_le_congruenceK0` at `padicK1`/`padicK0`, and `identityDescent`
cross-module. A one-token mutation of `satakePow_zero`'s statement moved the count to
exactly one `mismatched` and was reverted.

**Build discipline.** New files: edit loop `timeout 300 lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false <file>` per module; then one `lake build`
of the four; the consumer probe is the only cross-module check. No whole-tree build
(§3.5).

### 4.6 W6 — the mathlib stubs (a decision wave)

**Subject.** The eight `Def_Mathlib_*` nodes in the twin's `Definitions/` closure
(§3.2): mathlib-adjacent facts the pin needed at mathlib `v4.33.0` and packaged as
`Def_Mathlib_*` modules. The wave audits their 114 declarations against mathlib
`v4.34.0`, substitutes what mathlib has absorbed, and ports the residue.

**The audit (the wave's decision).** Exactly **two** declarations have been absorbed by
mathlib and are substitutions:

- `Submonoid.units_isOpen` → mathlib `Submonoid.isOpen_units`
  (`Mathlib.Topology.Algebra.Group.Units`), identically stated, renamed. This is the
  *whole* `Def_Mathlib_Topology_Algebra_Group_Units` node (7 lines / 1 declaration), so
  it has no port module.
- `RestrictedProduct.singleAddMonoidHom` → mathlib's `@[to_additive]`-generated
  constant of the same fully-qualified name (from the new
  `RestrictedProduct.mulSingleMonoidHom`). `RestrictedProduct_Basic` therefore lands 22
  of the pin's 23 declarations; the binder arrangement differs (mathlib's first explicit
  argument is the submonoid *element* family, the pin's is the *carrier* family), so the
  one call site in `TopologicalSpace` writes `singleAddMonoidHom (G := A) B j`.

Both follow the port's substitution policy: adopt mathlib's declaration and do **not**
re-export the pin name, so a consumer uses mathlib's name; the record is prose — the
module header, the `SOURCES` comment and this section. Because the checker only iterates
over *port* declarations, a substituted pin declaration is never diffed (there is no
`missing` direction), so a renamed substitution is documentation-only and the header is
the pointer for a later transcriber. No `alias` is used.

The remaining **112 declarations are residue**. mathlib `v4.34.0` has the
`RestrictedProduct` base API but none of the pin's additions under any name: a
declaration-name index over all of `Mathlib/` plus targeted statement search finds no
match — it has `Homeomorph.piUnique`/`piEquivPiSubtypeProd` but not the
`ContinuousMulEquiv` forms, `Homeomorph.Lemmas`' `IsEmbedding.toHomeomorph` but not
`IsOpenEmbedding.toHomeomorph`, and the set-indexed
`secondCountableTopology_of_countable_cover` but not the type-indexed `'` variant.

**Homing (the wave's organization).** The residue opens a mathlib-mirroring tree, so the
gaps are obvious and disposable if upstreamed:

| pin node | home |
|---|---|
| `Order_Filter_Cofinite` | `Order/Filter/Cofinite.lean` |
| `Topology_Bases` | `Topology/Bases.lean` |
| `Topology_Algebra_Module_Quotient` | `Topology/Algebra/Module/Quotient.lean` |
| `Topology_Algebra_ContinuousMonoidHom` | `Topology/Algebra/ContinuousMonoidHom.lean` |
| `Topology_Algebra_RestrictedProduct_{Basic,Equiv,TopologicalSpace}` | `Topology/Algebra/RestrictedProduct/{Basic,Equiv,TopologicalSpace}.lean` |
| `Topology_Algebra_Group_Units` | *(substituted; no module)* |

The pin's bare `import Mathlib` is replaced by specific imports throughout (the house
rule), and each header records its pin line/declaration count and its own drift ledger.

**Drift adapted (statements unchanged).** Every statement is verbatim (the checker's 111
new `identical` rows). The proof/body-level adaptations, by module:

- `Order/Filter/Cofinite`: `Set.Countable.setOf_finite` → `ofPred_finite` (deprecated).
- `Topology/Bases`: `IsOpenEmbedding.toHomeomorph` → `IsEmbedding.toHomeomorph` (moved
  to `Homeomorph.Lemmas`).
- `Topology/Algebra/Module/Quotient`: `continuous_finset_sum` → `continuous_finsetSum`
  (deprecated).
- `Topology/Algebra/RestrictedProduct/Equiv` and `…/TopologicalSpace`:
  - the pin's `filter_upwards` witnesses become `hφ.mono …` — `v4.34.0`'s
    `filter_upwards` yields a raw set-membership proof that no longer unifies with
    `RestrictedProduct.map`'s `∀ᶠ`-binder, so `map_apply` stops firing; the two terms are
    definitionally equal by proof irrelevance;
  - `piCongrLeft'_apply`/`piCongrLeft'_symm_apply` are namespace-qualified
    `Equiv.piCongrLeft'_…`;
  - the `RingEquiv`/`LinearEquiv` `map_mul'`/`map_smul'` proofs `change` to the
    underlying `Equiv` spelling (keyed `simp`/`rw` no longer sees through the coercion);
  - `dif_neg` → `dite_eq_right`; `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`;
  - `Equiv.coe_fn_mk`/`coe_fn_symm_mk` no longer reduce under `simp only`, so
    `Equiv.continuous_restrictedProductProd{,_symm}` and
    `Homeomorph.restrictedProductPrincipal` are rewritten through their `@[simps]`
    projection lemmas / an explicit `change … dite …` + `split_ifs`;
  - `map_sum (RestrictedProduct.evalAddMonoidHom …)` is spelled with `(B := C)`.
- The pin's blank-bodied `@[to_additive\n\n  ]` attributes are normalized to
  `@[to_additive]`; the generated companion names are unchanged, and the ones the pin
  carries as hand-written/private companions land as `promoted` through the checker's
  dotted fallback.

**Deliverable.** The seven new modules above (headers in the house style). Landed: all
seven build warning-free (`1.0 s`–`8.4 s`), the checker reads `8377 identical / 0
mismatched / 0 missing` (+111, exactly the residue), and
`spec/AutomorphicFormConsumer.lean` carries the W6 zone.

**Verification.** The residue nodes are in `PORT_FILES` and their pin files in
`SOURCES`; `Def_Mathlib_Topology_Algebra_Group_Units` is in neither (fully substituted).
The consumer zone exercises `Filter.cofinite.sets.countable`,
`Submodule.quotientPiContinuousLinearEquiv`, `ContinuousMulEquiv.piUnique`,
`Submonoid.isOpen_units` (the substitution) and
`RestrictedProduct.secondCountableTopology` cross-module. A one-token mutation of
`RestrictedProduct.secondCountableTopology`'s conclusion moved the count to exactly one
`mismatched` and was reverted.

**Build discipline.** Each module: edit loop `timeout 400 lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false <file>`, then one `lake build` of the
seven; the consumer probe is the only cross-module check. No whole-tree build (§3.5).

### 4.7 W7–W12 — the definition gate, closed

**Measured scope.** Re-walking the twin's `Definitions/` closure after W1–W6
(2026-10-11): 51 modules, **30 fully present, 21 unported (~6,000 pin lines)**, and a
7-batch dependency chain. W7–W12 land 16 of those 21; the gate is closed and the
proof half (§4.9) is schedulable.

**Landed (16 modules; checker +549 over the post-W6 baseline, now 8926 identical /
0 mismatched / 0 missing):**

| set | modules | pin lines |
|---|---|---:|
| W7 ready | `LocalLanglands_HeckePair`, `AdelicDock_LocalEmbedding`, `NumberField_AdelicVolume`, `SiegelReduction`, `SigmaAdelicAction`, `HeckeEigensystemMap` | 1,589 |
| W7 second | `LocalLanglands_HeckeCosetSystem`, `CentreCutSiegelSet` | 697 |
| W7 third | `SmoothCuspRealization`, `SiegelCovering`, `NumberField_SiegelVolume` | 1,053 |
| W8 | `ProductionPins`, `ArithCuspRealization` | 200 |
| W9 | `ProductionPinsCompact` | 92 |
| W10 | `ProductionPinsGeneral` | 468 |
| W11 | `IsotypicCuspSpace` | 1,063 |
| W12 | `CuspidalConstituent`, `ArchSpherical` | 224 |

**Homes (the wave's organization).** `RepTheory/LocalLanglands/{HeckePair,HeckeCosetSystem}.lean`,
`NumberTheory/AdelicDock/LocalEmbedding.lean`, `NumberTheory/{AdelicVolume,SiegelVolume}.lean`,
`AutomorphicForm/Adelic/WindowedSiegel/CentreCutSet.lean`,
`AutomorphicForm/Adelic/Siegel/{Reduction,Covering}.lean`,
`AutomorphicForm/Adelic/Cusp/{SmoothRealization,ArithRealization}.lean`, and
`AutomorphicForm/Adelic/{SigmaAdelicAction,HeckeEigensystemMap,ProductionPins,ProductionPinsCompact,ProductionPinsGeneral,IsotypicCuspSpace}.lean`,
plus `AutomorphicForm/Adelic/Cusp/Constituent.lean` and `AutomorphicForm/Adelic/ArchSpherical.lean`.

**Drift ledger (statements unchanged).** `Finset.prod_le_prod` → `prod_le_prod₀` for
the ordered form (`SiegelReduction`, `CentreCutSiegelSet`, and by default elsewhere);
`mem_setOf_eq`/`Set.mem_setOf_eq` → `ofPred_eq`; `if_pos`/`if_neg` →
`ite_eq_left`/`ite_eq_right`; `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right`;
`continuous_finset_sum` →
`continuous_finsetSum`; `zero_le'` → `zero_le`; `IsOpenEmbedding.toHomeomorph` from
`IsEmbedding`; `haveI := …` in a Prop goal → `have := …`; `Nat.Primes`
semireducibility in `rw` (explicit arguments); and the pervasive one —
`InfiniteAdeleRing` is a semireducible `def` in v4.34.0, so `Matrix.of`/
`Function.update` terms over it stop reducing under `rfl`/`simp`
(`NumberField_AdelicVolume`, `NumberField_SiegelVolume`). `SiegelVolume` restores the
pin's proof terms with the file-level
`set_option backward.isDefEq.respectTransparency false` (the same escape the pin uses
in its own `Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace.lean`).
`ProductionPins` adds `AdelicLevel/HeckeGen` (the pin reaches `heckeGen` transitively);
`ProductionPinsGeneral` adds `Mathlib.NumberTheory.NumberField.ClassNumber` for the
`Finite (ClassGroup (𝓞 F))` instance and drops the pin's trailing `#check`/`#print
axioms` `Battery`. `IsotypicCuspSpace` adds `Mathlib.RepresentationTheory.Basic` for
`Representation` and `Representation.dual_apply`, which the pin reaches transitively
through its stub imports, and keeps a narrow `set_option linter.style.haveILetI false`
for its `letI`/`haveI` walls; `CuspidalConstituent` restates `rightRegular`'s
`map_one'`/`map_mul'` as `change` + `rw`, the pin's `simp [rightTranslate]` no longer
normalizing the `Representation` structure literal's coercion.

**W11 record (the isotypic cusp space, 2026-10-11).** `Def_AutomorphicForm_IsotypicCuspSpace`
was generated whole (1,080 lines, the full pin body) and its first check stalled past the
harness's 600 s bound at the project cap. The cause was not compute: the generated header
replaces the pin's stub imports and the four port modules do not reach `Representation`, so
the `TypePiece` section was ill-typed and its unification spun to `maxHeartbeats`. The
low-cap diagnostic (`timeout 120 lake env lean -DmaxHeartbeats=200000 …`) finished in 49.6 s
with 33 errors on the target lines and separated the two, D-6 §5; with the mathlib import
added the module elaborates green in 7.0 s at the 4,000,000 cap. Landed: `lake build`
warning-free at 7.4 s, a six-probe W11 consumer zone (6.7 s), `#print axioms`
on five representative declarations all `[propext, Classical.choice, Quot.sound]`, and the
checker at `8898 identical / 0 mismatched / 0 missing` (+124 checked declarations).

**W12 record (2026-10-11).** Both modules were transcribed whole, checked at the low cap
first (200,000 heartbeats, 0 errors, 0 warnings), then green at the project cap and
warning-free; `CuspidalConstituent` needed one drift restatement (`rightRegular`'s
structure-literal proofs). Landed: `lake build` at 3.0 s / 3.5 s, a six-probe W12 consumer
zone, `#print axioms` on five representative declarations all
`[propext, Classical.choice, Quot.sound]`, and the checker at `8926 identical /
0 mismatched / 0 missing` (+28, the two nodes' 21 + 7 declarations).

**The gate is closed.** The twin's statements (`IsLevelSphericalOfType` via `ArchSpherical`
and the cuspidal-constituent carriers) are statable on landed definitions and the
proof half (P0–P3, §4.9) can run; the phase order is [WORKORDER-P-rightConv-comm.md](WORKORDER-P-rightConv-comm.md), 3,824
net new math lines in three sets, against a 3,178-line / 248-declaration block the three silos
carry up to three times.

**Residual.** `Def_NumberField_AdelicBox` reads 33/36: its three
`isOpen/isClosed/isCompact_integralFiniteAdeles` rows are the `(𝓞 K)`-specialized
restatements of the general `NumberField.AdelicLevel` versions already home'd in
`AdelicLevel/IdealBall.lean` by W1; they are deliberately not re-derived. The node is
otherwise complete.

**Execution note.** Transcriptions were delegated, but roughly a third of the runs
stalled with no file output and were taken over by the manager (AdelicVolume,
HeckeCosetSystem, CentreCutSiegelSet, and all three of the third set). The reliable
route for these large mathlib-gap-adjacent modules is a direct port plus the
`respectTransparency` escape where noted.

### 4.8 Discipline common to every wave

- **Whole nodes** (§2.3): a module in scope is transcribed in full, not cherry-picked
  for the current target; the residue is content with no consumer anywhere, verified
  by `grep -c`.
- **Cut by mathematical role, not by pin file** (§3.1): one pin `Def_` module may
  become several homes, and a generic block belongs in its own top-level area
  (`MeasureTheory/`, `RepTheory/`), never under `AutomorphicForm/`.
- **Promotions go to the pin's home** (§5): a re-derived copy of a public pin
  declaration is deleted in favour of the pin-named one. The frontier waves are
  cheap now and re-elaborate a cone later.
- **Bound the check before believing a timeout.** For a generated module run the
  low-cap form first — `timeout 120 lake env lean -DmaxHeartbeats=200000
  -DautoImplicit=false <file>` — which finishes in seconds to a minute and still
  shows the target lines. It separates genuine compute from an impossible unification
  or a dropped import (W11's `Representation`; D-6 §5). Only then pay for the
  4,000,000 cap and the `lake build`.
- **No log in the plan.** State lives in the wave table's `why now` column and in
  the records under `logs/`; this file stays forward-looking.

### 4.9 The proof half (after the gate)

| set | content | home | ≈ written |
|---|---|---|---:|
| **P0** | scout of §5 (`Scratch.lean`) | — | — |
| **P1** | the generic engines, written once and public | `RepTheory/ProjectedHaar.lean`, `RepTheory/TypeSpan.lean`, `RepTheory/BiIsotypic.lean`, `RepTheory/AntiInvolutionHaar.lean` | 2.3k |
| **P2** | the adelic instantiation | `AutomorphicForm/Adelic/RightConvComm/{Frame,MeasureAssembly,PlaceClassData,SliceCentrality}.lean` | 1.0k |
| **P3** | the general headline and the derived level headline | `…/RightConvComm/{Compact,Level}.lean` | 0.4k, or a few dozen lines if P0 succeeds |

P1 and P2 are new files and cascade on nothing (playbook §3.7 phase 2); P3 imports
them. One set per subagent, review between sets (§0.2), one build per wave (§3.5).
The pin's own order is not the order: its `S_` files carry the whole prelude before
any of it is consumable. The measured phase order — the three sets, their modules, the
pin line ranges, the build discipline and the stop conditions — is
[WORKORDER-P-rightConv-comm.md](WORKORDER-P-rightConv-comm.md); `port_advise`/`port_plan`
price the trio (the twin plus the `principalLevel` sibling, §1) at 3,824 net new math lines,
of which a 3,178-line / 248-declaration block is carried up to three times and is written
once. **Landed (2026-10-12).** Eleven new modules — the generic engine in
`RepTheory/{TypeSpan,AntiInvolutionHaar,ProjectedHaar,BiIsotypic}.lean`, the adelic instantiation in
`AutomorphicForm/Adelic/RightConvComm/{Frame,PlaceClassData,SliceCentrality,MeasureAssembly}.lean`,
and the three headlines in `…/RightConvComm/{Compact,Level,Principal}.lean` (3,866 written lines
against the 3,824 measured net new math lines).
The compact headline transcribes the compact `solution`; the level and principal headlines are
derivations from the P0 verdict. Checker `9205 identical (648 promoted, 83 renamed), 0 mismatched,
0 missing`; the milestone whole-tree build is green at 9,467 jobs; the consumer carries Zone P;
`#print axioms` on all three headlines is `[propext, Classical.choice, Quot.sound]`.

## 5. The scout gate

One `Scratch.lean` probe before P3 decides the whole shape of the topic:

> With `O := levelOne (𝓞 F) F N` and `U := MeasureAssembly.levelSubgroup F N`, can
> `AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType` be derived
> from `…_of_isCompact` by `hUO := rfl` (or `Subgroup.ext`), `IsOpen O` from
> `isOpen_level_image`/`isOpen_glFin_preimage_image_level`, and `IsCompact U` from
> `isCompact_level_image'` plus injectivity of `glFin` on `ker glArch`
> (`eq_of_glArch_eq_of_glFin_eq`)?

- **If yes**, the shared home is written at the $`U`$ spelling once and the level and
  principal headlines are specializations: the port writes one proof of 3,178 shared
  lines plus two derivations, and each level file shrinks to its public statement and
  side lemmas.
- **If no** (a hypothesis is genuinely stronger in one direction, or the instance
  transport does not line up for one of the two), that `solution` is transcribed and the
  dedup is still the 3,178-line shared home — P3 grows by that file's own lines, not by a
  second engine.

The scout also settles the two `def`-level questions: whether `MeasureAssembly.archNu`
must be the pushed-forward measure or can be mathlib's Haar measure on the
archimedean group, and whether the `BiIsotypic` engine can be stated over
`Representation k K V` (as the pin does) rather than over functions on the
archimedean adeles.

It is step **P0** of [WORKORDER-P-rightConv-comm.md](WORKORDER-P-rightConv-comm.md), which
fixes the expected answer (`hUO := rfl`, the level's own compact/open lemmas) and the
fallback (transcribe both `solution`s behind the same shared home). **Answered yes for both
instantiations** (`lean/tmp/P-scout.lean`): `hUO := rfl` by `productionPinsOf_U`, `hO` from
`AdelicLevel.isOpen_levelOne` and `TestFnPrincipalLevel.isOpen_finitePrincipalLevel`, `hU` from
`IsCompact.image` over the landed finite-level compactness plus the separation
`ProjectedHaar.eq_of_glArch_eq_of_glFin_eq`; so `Level.lean` and `Principal.lean` are a few dozen
lines each and only the compact `solution` is transcribed.

## 6. Verification

- **Checker.** Every port module in `PORT_FILES`; every pin source in `SOURCES`
  appended last. Target `0 mismatched / 0 missing`. Measured (2026-10-11): the shared
  engine's **248 declarations are `private` at the pin** (`private def _root_.ProjectedHaar.…`),
  so they verify through the checker's dotted-name fallback and land as `promoted` (+≈300
  with the one-sided ones); the three headlines match the `Theorems/` wrappers by last name,
  so `identical` moves by exactly +3. Re-run the checker with `--prop-bodies` if any
  `def … : Prop` is promoted.
- **Consumer.** `spec/AutomorphicFormConsumer.lean` gains one zone per set, each a
  real executed cross-module composition: for P1 a concrete non-vacuous instance of
  the generic `convKer_cut_comm` on a finite group frame; for P2 the adelic frame's
  separation and `levelSpherical_eq_cut`; for P3 all three headlines at a concrete
  `N = ⊤`/`levelOne`, at a compact `U`, and at `principalLevel`, proving the same identity
  three ways. Deleting any one module must break the zone.
- **Axioms.** `#print axioms` on all three headlines returns
  `[propext, Classical.choice, Quot.sound]`; no `sorry` anywhere, including in
  `def`s.
- **Faithfulness.** Statements are transcribed from the `Theorems/` wrappers, which
  for these three are the statement authority verbatim (they differ from the `S_`
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
