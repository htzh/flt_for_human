# Carry-forward register

The port's forward-looking register: API deliberately left unported, open
follow-ups, and scoping cautions that have not yet become playbook method.

It is the counterpart of `Reserve/`. `Reserve/` holds deferred API that has been
**ported and verified** and kept off the critical path; this file holds work that
has **not been done**, plus the reasons a frontier figure can be read wrong.

**How to use it.** Before pricing a node — and whenever a frontier figure looks
surprising — grep this file for the node name. An entry means the node's `lines`
or `needed` does not yet account for something its consumers still need. When you
defer part of a pin file's surface, or leave a follow-up, add an entry here; when
you complete one, delete it. The scoping cautions at the end are repeated in
[porting-playbook.md](porting-playbook.md) §2.1, which is where a new session
meets them.

## Deferred API

### `WeierstrassCurve.Affine.hasPrincipalDivisors_functionField` — the Weierstrass place / Riemann–Roch / class-group API

The pin file
`P2M/Sol/S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean`
(pinned `aa2d8b3`, 2,248 raw / ≈1,494 content lines) carries two separable
things, and only the first is ported.

**Ported** (the capstone route, in `FLTForHuman/WeierstrassCurve/`):

- `FunctionFieldQuadratic.lean` — `polyToFunctionField`, `ratFuncToFunctionField`,
  the `Algebra (RatFunc F) W.FunctionField` structure with its scalar towers,
  `yCoord`, `weierstrassQuadratic`, `isIntegral_yCoord` (verbatim from
  `Definitions/Def_WeierstrassCurve_FunctionFieldQuadratic.lean`).
- `FunctionFieldFinite.lean` — the nodes `WeierstrassCurve.Affine.adjoin_yCoord_eq_top`
  and `WeierstrassCurve.Affine.finiteDimensional_ratFunc_functionField`.
- `PrincipalDivisors.lean` — the headline, one application of the ported
  `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc`.

**Deferred**: everything else in the pin file — the
`placeOfEquation` / `IsFinitePlace` / `heightOneSpectrumOfEquation` / `ord`
dictionary and the class-group / Riemann–Roch block
(`geomPlaceOfPoint`, `geomDivisorSum`, `unitIdealOfPoint`, `RRSpace`,
`isPrincipal_of_geomDivisorSum_eq_zero'`, …).

- **Size**: 110 public declarations in the file; 55 are reached by the headline's
  graph citers. The transitive closure the citers need is ≈1,365 raw /
  ≈941 content lines; the whole file is ≈1,494 content.
- **Consumers / trigger**: the headline's 27 graph citers. 12 of them call the
  `placeOfEquation`/`IsFinitePlace` block directly; the rest need only the
  function-field quadratic already ported. Port the API when the first citer is
  taken: `WeierstrassCurve.Affine.IsogenyEndDatum.*`,
  `WeierstrassCurve.exists_veluFunctionFieldHom_*`,
  `WeierstrassCurve.Affine.exists_genusOnePlaceGate_*`, `PeriodPair.*`,
  `ModularCurve.ModularPolynomialData.*`, and the `zmultiples_eq_*` family.
- **Dedup before writing it**: the pin repeats the `placeOfEquation` prelude in
  ~18 `S_` files (one imports this node's wrapper and re-exports the names, the
  rest re-declare it). Port it once as a shared home and measure the
  `(copies − 1) × block` saving first; at ≈940 content lines this crosses the
  playbook's ~1,000-line threshold for staffing as a set (§0.2).
- **Mathlib siblings already exist** for part of it: `smul_basis_eq_zero`,
  `exists_smul_basis_eq`, `smul_basis_mul_Y`, `degree_norm_smul_basis` are in
  `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, so the pin's
  `Def_EllipticCurve_ValuationInfty` basis family is not needed. The silo's
  private `ord_*` lemmas (`min_ord_le_ord_add`, `ord_add_eq_min`, `ord_pow`,
  `ord_ringHom_eq_natDegree_mul`, `le_ord_ringHom_of_natDegree_le`) have **no**
  counterpart in the port and would be new work.
- **Frontier caveat — file-granular shadowing.** Because the port declares the
  headline, all 27 citers lose exactly 1 from `needed`, even though the API they
  call is absent: the citation graph's edges are *file*-granular (the citers
  import the node's `Thm_` wrapper) while the "ported" test is
  *declaration-name*-granular. **Treat those 27 as blocked on this entry** until
  the API lands, whatever the frontier says.

### `ModularCurve.exists_hasEquivariantPrimitiveOf` — the parts of the period API left out

Unlike the Weierstrass entry, this node's shadowing is **resolved**: the
`ModularCurve.Period` API its 28 citers reach was ported with the headline, in
`FLTForHuman/ModularForms/EichlerShimura/{PeriodPrimitive,PeriodIntegral,PeriodOf}.lean`
(vocabulary and `Γ₀(N)` lattice; general `periodOf`/`periodLatticeOf`/
`HasEquivariantPrimitiveOf`/`periodMapOf`). Three pieces of the pin's definition
files were deliberately **not** ported, because no consumer of this node reaches
them:

- `Def_ModularCurve_PeriodTransfer.lean` (150 raw / 104 content): conjugation and
  transfer of equivariant primitives (`conjRel`/`conjSubgroup`/`conjPrimitive`,
  `traceRep`/`transferElt`/`traceSum`, `IsEquivariantPrimitive.traceSum`).
- the `Hecke` section of `Def_ModularCurve_PeriodLattice.lean` (≈185 raw): the
  Hecke-stability of the period lattice (`cuspHeckeGen`/`cuspHeckeAeval`/
  `cuspHeckeRep`/`dualHeckeRep`/`PeriodLatticeHeckeStable`/`periodLatticeModule`).
  This is the only piece that pulls in `Def_CuspForm_HeckeAlgebra` and
  `Def_HeckeGalois_EichlerShimura`.
- the `CuspForm` Petersson block of `Def_ModularCurve_PeriodOf.lean` (≈30 raw):
  `peterssonIntegrandOf`/`peterssonOf`.

**Trigger**: port them when a consumer needs them — the Hecke-stability consumers
(`periodLatticeHeckeEnd*`, `PeriodLatticeHeckeStable`) and the period-transfer
consumers (`IsEquivariantPrimitive.traceSum`) are the nodes to watch. Note that
`Def_ModularCurve_PeriodLattice.lean` is listed in the checker's `SOURCES` for its
`Period` section only; adding the `Hecke` section later must not disturb the
names already verified from it.

### `ModularCurve.JOne.torsionGaloisRep` / `diamondOneBar` — the `Pic0` action/torsion block

Found while porting the X₁ Hecke/diamond inputs
([topics/hecke/TOPIC-x1-hecke-diamond-inputs.md](topics/hecke/TOPIC-x1-hecke-diamond-inputs.md)
SET-X1-A). SET-X1-A landed `ModularCurve/X1/Defs.lean`, `X1/HeckeOperator.lean`,
`X1/Diamond.lean`, `X1/HeckeModule.lean` and the two `AlgebraicCurve` `Along`
lemmas, but deliberately **omitted** five declarations because their prerequisite
is unported:

- `JOne.torsionGaloisRep`, `JOne.torsionGaloisRep_apply`,
  `JOne.coe_torsionGaloisRep_apply` (pin `Definitions/Def_ModularCurve_X1.lean:189-207`);
- `diamondOneBar`, `diamondOneBar_apply` (pin
  `Definitions/Def_ModularCurve_X1Diamond.lean:98-103`).

The missing prerequisite is the `Pic0` action/torsion block:

- `Pic0.torsion` / `mem_torsion` / `instModuleZModTorsion` (pin
  `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`);
- the `SMul`/`DistribMulAction (SemilinearAut K F)` actions on `Divisor` and
  `Pic0`, `degZeroSMulHom`, `smul_mem_torsion`, `instSMulTorsion`/
  `instDistribMulActionTorsion`, `instSMulCommClassZModTorsion`, and
  `SemilinearAut.torsionRep` (pin
  `Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean:206-356`, ≈150 content
  lines). The decided home is `AlgebraicCurve/Defs/SemilinearAut.lean` (see its
  header), beside the deferred `Pic0.torsion` block in
  `AlgebraicCurve/Defs/Divisor.lean`.
- `ModularCurve.PicAction` (pin
  `Definitions/Def_ModularCurve_ArithmeticGalois.lean:85-105`), home
  `ModularCurve/Defs/ArithmeticGalois.lean` (see its header).

**Size**: ≈170 content lines plus the `Pic0.torsion` block; it touches three
already-frozen files, so port it as a **definitions-first mini-set** with its own
review gate, not folded into a theorem set.

**Trigger / consumers**: the five omitted declarations, and the successor targets
`ModularCurve.heckeDiamondCommuteBar`,
`ModularCurve.rationalRankTwoNebentypus_family`,
`ModularCurve.moduleFinite_padicInt_tateModule_jOne` and the
`CuspForm.IsEigenformWith.exists_galoisRepAdic_*` family. It is **not** on the
`heckeDiamondInputsAll` cone.

**Frontier caveat**: because `ModularCurve/X1/Defs.lean` and `X1/Diamond.lean` are
now in the checker's `PORT_FILES` and their pin files in `SOURCES`, a citer that
reaches `JOne.torsionGaloisRep` reads as one node closer while the declaration is
absent — the usual file-granular shadowing. Treat those citers as blocked on this
entry.

## Open follow-ups

- **`AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional`**
  (`FLTForHuman/AlgebraicCurve/IsCurveOver/EssFiniteType.lean`). Its consumer
  test (`spec/AlgebraicCurveConsumer.lean`, Zone L) is hypothesis-form: the
  concrete witness `F = ↥K⟮X⟯` needs the subtype coercion of `RatFunc.X` through
  `RatFunc.transcendental_X`'s `K⟮X⟯` notation, which was not worth the
  fragility. Add it if a later consumer makes the concrete form useful. The node
  also has **no ported consumer** — the pin's consumers are the `essFiniteType_*`
  targets — so it is a pre-payment, not a link in a chain.
- **`WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_two_ne_zero_or`**
  (147 raw, pin `aa2d8b3`) already decomposes along the two prerequisite nodes
  this port took (`adjoin_yCoord_eq_top`, `finiteDimensional_ratFunc_functionField`),
  but cites `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable`
  instead of the char-zero transfer. Check that route when the node is taken.

## Scoping cautions

Three ways a frontier figure misleads, each with the case that taught it. These
are repeated in the playbook §2.1; keep the specific instances here.

- **A citation-leaf is not a leaf.** `needed == 1` on a node with no theorem-node
  premises says nothing about its *definitional* prerequisites, which the
  doc-site citation graph does not carry. `AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn`
  read as a 126-line leaf, but its proof needed `Def_NumberField_AdelicHaar`
  (the adele-ring `T2Space` instances), `Def_NumberField_AdelicLevel` (the
  `glArch`/`glFin` projections) and `Def_AutomorphicForm_FactorizableTestFn`.
  Measure the pin `S_` file's `Definitions/` import closure before trusting a
  leaf.
- **A pin `S_` file's `lines` is an upper bound.** A "solution" file may inline
  its prerequisite nodes and carry an off-path development. The Weierstrass
  headline is 2,248 lines but ~200 on-path (see above). Grep the capstone region
  for the file's other declaration names: if none occur, the rest is off-path.
- **File-granular edges shadow.** Porting a headline whose pin file also carries
  an API prelude makes the file's citers read as unblocked while the API is
  unported (see the Weierstrass entry's caveat).
