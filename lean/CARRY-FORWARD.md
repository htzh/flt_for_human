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

**Status 2026-10-04 (taken by the Vélu Phase A engine).** This entry's trigger —
"the first citer: `WeierstrassCurve.Affine.IsogenyEndDatum.*`,
`WeierstrassCurve.exists_veluFunctionFieldHom_*`" — fired. What landed:

- the `placeOfEquation` / `IsFinitePlace` / `heightOneSpectrumOfEquation` / `ord`
  dictionary and the 50-declaration citers' closure, in
  `FLTForHuman/WeierstrassCurve/Place/Dictionary.lean` (+ the general
  `evalAt`/`ord` additions in `AlgebraicCurve/Defs/PlaceCalculus.lean`);
- the place gate, `AbelTheorem` and the class-group/`Pic0` equivalence from
  `Def_WeierstrassCurve_GenusOnePic0` / `Def_WeierstrassCurve_GenusOnePlaceGateCentred`
  (`placeOfPoint`, `deg_placeOfPoint`, `pointDivisor`, `pointClass`,
  `pic0ToPoint`, `genusOnePic0Equiv`, `divisorSum*`, `IsCentred`) in
  `FLTForHuman/WeierstrassCurve/GenusOnePlaceGate.lean`, plus
  `pointMapOfPushforward` / `IsogenyEndDatum` / `IsogenyHomDatum` in
  `WeierstrassCurve/Isogeny/ConditionalCurrency.lean`;
- the kernel-cardinality engine
  (`natCard_ker_pointMapOfPushforward_eq_finrankAlong_of_separableAlong` and its
  three helper wrappers) in `WeierstrassCurve/Isogeny/NatCard.lean`;
- a **char-free** norm formula and separability chain, transcribed `private` into
  `WeierstrassCurve/Velu/RestrictAlong.lean` (see the follow-up on
  `hasPrincipalDivisors_functionField_of_two_ne_zero_or` below).

**Still deferred from this entry:** the Riemann–Roch-space and integral-ideal
block of the same `S_` file — `rrParam`/`RRSpace`/`basisAux`/`finrank_eq`/
`unitIdealOfPoint`/`unitIdealOfDivisor`/`geomDivisorSum`/
`isPrincipal_of_geomDivisorSum_eq_zero'`/`instAbelTheorem` — which the Vélu route
never needed. Port it when a `genusOnePlaceGate`/RR consumer is taken. The
`geomDivisorSum`/`divisorSum` distinction matters: the gate module has the latter
(from `Def_WeierstrassCurve_GenusOnePic0`), not the former.

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
  **Fired 2026-10-04** for the Vélu citers — see the status block above.
- **Dedup before writing it**: the pin repeats the `placeOfEquation` prelude in
  ~18 `S_` files (one imports this node's wrapper and re-exports the names, the
  rest re-declare it). Port it once as a shared home and measure the
  `(copies − 1) × block` saving first; at ≈940 content lines this crosses the
  playbook's ~1,000-line threshold for staffing as a set (§0.2). Done: one home,
  `WeierstrassCurve/Place/Dictionary.lean`.
- **Mathlib siblings already exist** for part of it: `smul_basis_eq_zero`,
  `exists_smul_basis_eq`, `smul_basis_mul_Y`, `degree_norm_smul_basis` are in
  `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, so the pin's
  `Def_EllipticCurve_ValuationInfty` basis family is not needed. The silo's
  private `ord_*` lemmas (`min_ord_le_ord_add`, `ord_add_eq_min`, `ord_pow`,
  `ord_ringHom_eq_natDegree_mul`, `le_ord_ringHom_of_natDegree_le`) have **no**
  counterpart in the port and would be new work. Done: they live in
  `AlgebraicCurve/Defs/PlaceCalculus.lean`.
- **Frontier caveat — file-granular shadowing.** Because the port declares the
  headline, all 27 citers lose exactly 1 from `needed`, even though the API they
  call is absent: the citation graph's edges are *file*-granular (the citers
  import the node's `Thm_` wrapper) while the "ported" test is
  *declaration-name*-granular. **This caveat was validated by the Vélu plan**:
  its §2 read "import H1 wholesale" from the frontier, while the port in fact
  had only 65 in-port lines of the shared block. The dictionary half is now
  ported; the citers reaching the RR block above remain shadowed by this entry.

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
- **Patching-port `class` binder spelling** (found 2026-10-04, while porting the
  Vélu cluster). The statement checker previously did not match `class`
  declarations at all, so no `class` in the repository had ever been diffed.
  Fixing `DECL_RE` (now `…structure|class|instance`, with `class` field
  extraction) surfaced four **pre-existing** deviations in
  `FLTForHuman/Patching/PatchingConstruction.lean`, none Vélu-related:
  `IsLocalRing.IsAdicTopology` writes `(R)` where the pin
  (`Definitions/Def_Patching_SystemTypes.lean`) writes `(R : Type*)`;
  `Algebra.TopologicallyFG` and `IsPatchingSystem` spell their binders through
  surrounding `variable`s where the pin is explicit; and
  `PatchingAlgebra.smulData` has no textual counterpart under that name. They are
  exempted by dotted name in the checker's `OWN_PROOFS` so the port stays at
  `0 mismatched / 0 missing`. The Patching effort should re-spell the three
  binders as the pin does (a `variable` form is elaboration-equivalent but not
  text-equal, which is what the checker diffs) and re-home or rename `smulData`.
- **`WeierstrassCurve.Affine.hasPrincipalDivisors_functionField_of_two_ne_zero_or`**
  (147 raw, pin `aa2d8b3`) already decomposes along the two prerequisite nodes
  this port took (`adjoin_yCoord_eq_top`, `finiteDimensional_ratFunc_functionField`),
  but cites `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc_of_isSeparable`
  instead of the char-zero transfer. Check that route when the node is taken.
  **Update 2026-10-04:** the Vélu `restrictAlong` headline needed the same
  char-free ingredient and transcribed it `private` into
  `WeierstrassCurve/Velu/RestrictAlong.lean`: the pin's
  `relNorm_eq_pow_of_isMaximal_of_isSeparable`, the fibre-centre norm argument
  re-run without `[CharZero F]` (a char-free
  `Divisor.pushforwardNormFormula_of_finiteDimensional`), and a separability
  chain (`kw_isSeparable_*`, `kw_oddOrderSummingSetFunctionFieldHom_odd_separableAlong`).
  The separability chain is public. The **node**
  `AlgebraicCurve.relNorm_eq_pow_of_isMaximal_of_isSeparable` is now also public
  — promoted beside its `private` helper at the wrapper's exact binders and
  checker-verified against
  `Theorems/Thm_AlgebraicCurve_relNorm_eq_pow_of_isMaximal_of_isSeparable.lean`
  — because the pin exposes that interface publicly and the port had hidden it.
  What remains private is the char-free fibre-centre norm formula (it duplicates
  the port's own `private` `Divisor.pushforwardNormFormula_of_finiteDimensional`
  in `PrincipalDivisors/Transcendence.lean`); promote **one** copy to an
  `AlgebraicCurve` home when this node is taken, rather than re-deriving a third.

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
