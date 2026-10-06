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

### `ModularCurve.exists_hasEquivariantPrimitiveOf` — the parts of the period API left out

This node's shadowing is **resolved**: the
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
  What remains private is the char-free fibre-centre norm formula — it existed as
  **two** `private` copies (this file's and
  `PrincipalDivisors/Transcendence.lean`'s). **Resolved 2026-10-06 (V2 SET-2):** the
  pin-`private`-to-public promotion was done additively in
  `WeierstrassCurve/Velu/RestrictAlong.lean` (+39/−0): the pin names
  `AlgebraicCurve.Divisor.pushforwardNormFormula_of_isSeparable` and
  `AlgebraicCurve.normFormulaAlong_of_separableAlong` are now public wrappers over
  that file's two privates, which stay as the proof bodies. No third copy was
  written and no other module was edited. `Transcendence.lean`'s copy is still
  private; promoting it too would cost a 52-module cascade (measured), so leave it —
  the public home now exists in the RestrictAlong module.

- **Co-import collisions in the `IsogenyEndDatum` / Vélu cones (found 2026-10-06,
  while porting V2).** Two name collisions make pairs of library modules
  **unimportable together**; both are latent (nothing in the library imports the
  pairs, so the tree is green) and both cost the V2 consumers a real test:
  - `WeierstrassCurve.Affine.normFormulaAlong_of_elliptic` is declared in **both**
    `FLTForHuman/WeierstrassCurve/IsogenyEndDatum/Engine.lean` (the H5 copy,
    `[IsAlgClosed F] [CharZero F]`) and
    `FLTForHuman/WeierstrassCurve/Velu/RestrictAlong.lean` (the H4 char-free copy
    with an explicit `hsep`). `lake env lean` on a file importing both fails with
    *environment already contains …*. This is why SET-1's consumer is a separate
    `spec/IsogenyEndDatumConsumer.lean` (Engine cone) and SET-2's zones stay in
    `spec/WeierstrassCurveConsumer.lean` (RestrictAlong cone).
  - `WeierstrassCurve.Affine.instInfinitePlace` is a plain instance at
    `IsogenyEndDatum/Engine.lean:90` and a `scoped instance` at
    `WeierstrassCurve/Place/RRSpace.lean:444`, so
    `WeierstrassCurve/GenusOnePlaceGateCentred.lean` (which imports `RRSpace`) cannot
    be imported alongside `Engine.lean`. SET-1's consumer therefore states the three
    gate instances as hypotheses rather than discharging them from
    `exists_genusOnePlaceGate_isCentred_and_abelTheorem`.
  A refactor round should keep **one** public `normFormulaAlong_of_elliptic` (the H5
  copy is used by six declarations across `Engine`/`DualEndData`; the H4 copy has one
  internal caller) and make the second `instInfinitePlace` agree (one plain, one
  `scoped`/`local`) so the two cones can meet. Both are frozen-module edits: price
  them with `tools/deps/build_ladder.py --edit`, not inline.

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
  its prerequisite nodes and carry an off-path development: the Weierstrass
  headline's pin file is 2,248 lines, of which ~200 are on the headline's path.
  Grep the capstone region for the file's other declaration names: if none occur,
  the rest is off-path.
- **File-granular edges shadow.** Porting a headline whose pin file also carries
  an API prelude makes the file's citers read as unblocked while the API is
  unported; the Weierstrass headline's place/RR/class-group API was such a case
  until it was ported.
