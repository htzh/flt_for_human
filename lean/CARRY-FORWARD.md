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
  (147 raw, pin `aa2d8b3`, with its `…_of_isElliptic` corollary). **Landed in V2
  SET-2** at `WeierstrassCurve/PrincipalDivisorsSeparable.lean:158`/`:172`, on the
  pin's own route: it cites the ported
  `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`, and the
  char-zero transfer the earlier caution worried about was not needed. The open item
  in this bullet is the char-free norm formula beneath it.
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
  `PrincipalDivisors/Transcendence.lean`'s), written twice byte-identically: the
  29-line `ord_norm_eq_sum_fiberOver` and the 17-line
  `pushforwardNormFormula_of_finiteDimensional` are the same text at
  `Transcendence.lean:309`/`:345` and `Velu/RestrictAlong.lean:1713`/`:1749`.
  **Resolved 2026-10-06 (V2 SET-2):** the pin-`private`-to-public promotion was done
  additively in `WeierstrassCurve/Velu/RestrictAlong.lean` (+39/−0): the pin names
  `AlgebraicCurve.Divisor.pushforwardNormFormula_of_isSeparable` and
  `AlgebraicCurve.normFormulaAlong_of_separableAlong` are now public wrappers over
  that file's two privates, which stay as the proof bodies. No third copy was
  written and no other module was edited. (The char-zero pin name
  `AlgebraicCurve.Divisor.pushforwardNormFormula` is separately public over the
  `Transcendence.lean` private, at `:371`.) The duplicate cannot be retired by
  pointing `Transcendence.lean` at the new public home: `Velu/RestrictAlong.lean`
  already reaches `Transcendence.lean`, so that call would be a cycle. Retiring it
  means extracting the char-free fibre-centre norm formula into a module **below**
  `Transcendence.lean` and rebuilding that cone once (a 52-module cascade,
  measured); until then both private bodies stay.

- **Co-import collisions in the `IsogenyEndDatum` / Vélu cones (found 2026-10-06,
  while porting V2).** Name collisions make several pairs of library modules
  **unimportable together**; all are latent (nothing in the library imports a pair,
  so the tree is green) and they cost the V2 consumers real tests. **The criterion is
  the declaration, not the name**: two modules are unimportable together only when
  the same fully-qualified name arrives with *different* declarations — Lean's
  environment merge tolerates byte-identical duplicates silently (verified on
  `isRational_of_deg_eq_one`, below; the error message when they differ is
  `environment already contains …`). The `Engine` cone
  cannot meet `Velu/RestrictAlong.lean`, `Place/RRSpace.lean`, or
  `GenusOnePlaceGateCentred.lean` (which reaches `RRSpace`):
  - `WeierstrassCurve.Affine.normFormulaAlong_of_elliptic` is declared in **both**
    `FLTForHuman/WeierstrassCurve/IsogenyEndDatum/Engine.lean` (`[IsAlgClosed F]
    [CharZero F]`, no `hsep`) and
    `FLTForHuman/WeierstrassCurve/Velu/RestrictAlong.lean` (char-free, explicit
    `hsep`). The two statements are a special case and a general case of one result:
    the char-free copy yields the H5 copy once `SeparableAlong F ι` is supplied —
    exactly what the H5 proof derives from `[IsAlgClosed F] [CharZero F]`. Both copies
    match their respective pin `S_` files, so both declarations are needed, but no
    environment can hold them together. This is why SET-1's consumer is a separate
    `spec/IsogenyEndDatumConsumer.lean` (Engine cone) and SET-2's zones stay in
    `spec/WeierstrassCurveConsumer.lean` (RestrictAlong cone).
  - `WeierstrassCurve.Affine.instInfinitePlace` is a plain instance at
    `IsogenyEndDatum/Engine.lean:90` and a `scoped instance` at
    `WeierstrassCurve/Place/RRSpace.lean:444`. They are not interchangeable: the
    Engine one builds `place` from `placeOfPoint 0` under the genus-one gate, the
    RRSpace one from `exists_not_isFinitePlace` under Dedekind +
    `HasPrincipalDivisors`, and the two are only *provably* equal (through
    `InfinitePlace.eq_of_not_isFinitePlace`), not definitionally. SET-1's consumer
    therefore states the three gate instances as hypotheses rather than discharging
    them from `exists_genusOnePlaceGate_isCentred_and_abelTheorem`.
    **`scoped`/`local` do not avoid the clash** — both still export
    `WeierstrassCurve.Affine.instInfinitePlace` (verified); only renaming one
    declaration, or keeping a single one, lets the cones meet. `private` *does* avoid
    it (Lean mangles the name), which is why the duplicated private proofs above
    coexist.

  A refactor round should keep **one** public `normFormulaAlong_of_elliptic` (the H5
  copy is used by six declarations across `Engine`/`DualEndData`; the H4 copy by one
  internal caller, and the H4 statement is the general one) and rename the other, and
  rename one `instInfinitePlace`. Both are frozen-module edits: price them with
  `tools/deps/build_ladder.py --edit`, not inline, and move the affected consumer
  zones with the renamed pin name (the checker matches by last name).

- **The second-order `XYIdeal` block belongs lower in the DAG (found 2026-10-06, while
  porting V3).** `IsogenyEndDatum/DualEndData.lean` carries the generic
  second-order-at-a-point development — `derivative_polynomial`,
  `evalEval_eq_zero_of_mem_span`, `evalEval_derivative_eq_zero_of_mem_span_sq`,
  `exists_eq_add_mul_polynomial_of_mem_XYIdeal_sq`, `X_sub_C_dvd_eval_of_mem_span`,
  `X_sub_C_sq_dvd_eval_of_mem_span_sq`, `XClass_notMem_XYIdeal_sq`,
  `ord_placeOfEquation_XClass_self`, and the `ord_ofHeightOneSpectrum_*` family
  (`:1134`, `:1360`, `:1387`–`:1478`). None of it is `IsogenyEndDatum`-specific, and
  the V3 node `WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add`
  needs two members of it (`ord_ofHeightOneSpectrum_eq_neg_log` and
  `ord_placeOfEquation_XClass_self`, the latter dragging in the five-lemma support
  chain). The choice was to import the hub — `TranslationAlgEquiv.lean`'s only import,
  at **1 m 21 s** fixed per `lake env lean` check against 23.5 s for the `Engine`-only
  cone — or to duplicate ~130 lines privately; the import was taken. **Trigger for the
  refactor**: when a third cone needs the block, extract it to a module under `Place/`
  (below `DualEndData`, which then imports it) and drop `TranslationAlgEquiv.lean`'s
  heavy import. Price the move with `build_ladder.py --edit DualEndData.lean`
  (5 modules / ≈119 s) plus the new home's dependents.

- **`AlgebraicCurve.Place.isRational_of_deg_eq_one` is public at one FQN in two
  modules (found 2026-10-06, while porting V4).** `AlgebraicCurve/P1/Dictionary.lean:59`
  and `WeierstrassCurve/Velu/Discharge.lean:38` declare the same theorem, and their
  bodies are byte-identical
  (`(AlgebraicCurve.Place.isRational_iff_deg_eq_one v).2 h`). So the two modules **are
  co-importable** (verified: `lake env lean` on a file importing both, exit 0) — Lean
  merges identical declarations silently — but the tree then carries two copies of one
  statement, and the second is invisible to any tool. A dedup, not a collision: keep
  the `P1/` copy (it is the lower module) and delete the `Velu/Discharge.lean` one, or
  re-export it as an alias. Same family as the `finite_setOf_ord_ne_zero_of_finiteDimensional`
  pair (`P1/EnginePrelude.lean:652` public vs `PrincipalDivisors/Transcendence.lean:387`
  private — there the private copy is harmless because `private` mangles the name, but
  it is still two proofs). Price both with `build_ladder.py --edit`; `Velu/Discharge.lean`
  is the larger cascade.

### The `General`/`NoAC` split in the base-change **engine** (`KernelBaseChange.lean`)

D-1 met the pin's `General`/`NoAC` twin pair in the function-field **prelude** and resolved
it the way playbook §5 asks: the `NoAC` name (no `[IsAlgClosed F]`, no gate instances) is the
primitive, and each `General` name is a one-line invocation of it — so both names exist, at
one proof each. D-5's **engine** (`kw_surge_hgf4_bc*` / `bcIota₁*`,
`KernelBaseChange.lean:133–420`) did not get that treatment: it is landed `General`-only, its
section carrying `[IsAlgClosed F] [IsAlgClosed F']` and four
`GenusOnePlaceGate`/`IsCentred`/`AbelTheorem` blocks, so it cannot be instantiated at a
subfield. Found by set D-6 (2026-10-06), whose two-curve descent needs exactly that
instantiation, and which therefore transcribes the pin's `NoAC` engine privately — ≈320 lines
the port could have imported.

**Follow-up for a refactor round (now unblocked — D-6 landed 2026-10-06; do not reopen
`TwoCurveDescent.lean` mid-set):**
restate the engine's section gate-free (`kw_surge_hgf4_bcTensorIota`, `…bcTensorFracIota`,
`…bcTensorFracIotaAlg`, `…bcIota₁`, `…bcTensorFracIotaSeam`, `…bcIota₁_{finiteAlong,isIntegral,
finrankAlong,compat}`), keep the `General` names as one-line invocations of the gate-free
ones, delete D-6's private copies, and re-point D-6 at the imports. The two D-5 headlines'
statements do not move; their proofs should elaborate unchanged, since a weaker section is
harmless to a caller that already has the hypotheses. Price the cascade with
`build_ladder.py --edit` before starting — `KernelBaseChange.lean` is a **leaf**, so the
cascade should be small. Note also that D-6 landed with the pin's own
`set_option maxHeartbeats 48000000` / `synthInstance.maxHeartbeats 8000000` on its
`gateDescent_of_descent` (transcribed from `S_:2882–2885`) and with ≈120 lines of `⁄`-spelling
instance/`Eq.trans` scaffolding; if the engine promotion happens, re-measure that declaration —
its budget and scaffolding may fall.

## Scoping cautions

Ways a frontier figure misleads, each with the case that taught it. These
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
- **A "last tail node" can be the entry to an unported slice (found 2026-10-06, after
  V4; the U, J and D rows all landed 2026-10-06).**
  `IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq` reads as the
  one remaining Phase D item of the H5 column, and `port_advise` prices it at 51
  declarations with a single substitution (≈29 lines) — because the tool prices the
  target's *own* `S_` file. Its `S_` file imports `Def_PeriodPair_Uniformization` and
  five `Theorems/Thm_PeriodPair_*` nodes whose `S_` files total 5,127 lines, inside a
  `PeriodPair` group the E-S scout measured at **9 nodes / 9,836 pin lines**. Price a
  node by its **unported closure**, never by `port_advise`'s own-file figure or by its
  column. **Status.** The ladder's **U row** (the dictionary, `discriminant_ne_zero`,
  `isUniformization_toPoint`) landed as P-SET-1, its **J row** (`jLattice_ofTau`,
  `jLattice_surjective`, plus the lattice prelude) as P-SET-2 —
  `Elliptic/PeriodPair/{Basic,Lattice,Discriminant,Uniformization,JLine}.lean` and the
  neutral `ModularForms/JInvariant.lean` — and its **D row** (the whole base-change/descent
  column) as set **P-2**, D-1…D-5,
  `WeierstrassCurve/Isogeny/{BaseChange,IntermediateField,BaseChangeAlgHom,VariableChangeAlgEquiv,KernelCyclicTransfer,KernelBaseChange}.lean`.
  The remaining ladder is the **S row** (seam/index) and the `rationalHomSet`/torsion
  columns; the gate's unported closure is now 13 nodes / 11,880 lines, of which the
  S family is 6,537 and the D-descent family 4,764 (both still unported at the time of the
  measurement — the D family has since landed). The j-line is on the `DeligneSerre` capstone
  cone (`frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen`
  lists 14 unported `PeriodPair.*` nodes / 9,071 lines, `jLattice_surjective` among
  them), contrary to the earlier reading that the 54-target D-S slice had no
  `PeriodPair` node. The closure measurement is in
  [topics/velu/TOPIC-V5-periodpair-uniformization.md](topics/velu/TOPIC-V5-periodpair-uniformization.md):
  15,179 lines, the two classical theorems on the path rather than prelude, ~4% of the
  then-remaining frontier. Note that the port's
  `ModularForms/WeightOne/Defs/PeriodPair.lean` is a **different** object: the weight-one
  prelude `periodPairOfTau`/`smulPeriodPair` over mathlib's `PeriodPair` struct, not the
  pin's uniformization API.
- **The docs-site closure is inflated at the *proof* level too (found 2026-10-06).** The
  closure over the pin's citation graph puts `PeriodPair.isUniformization_toPoint`,
  `aeval_j_diag_eq_zero_of_finrankAlong_eq`, `functionFieldGeneration` and
  `CerednikDrinfeld.Mumford.PeriodUniformization` inside the closure of step 4's
  `WeierstrassCurve.modularity_of_semistableModel` and of the Langlands–Tunnell node —
  while correctly excluding `mazurStepThree_not_inZeroComponentAt` from the same
  closures. Grepping the `S_` files settles it: those names occur **zero** times in the
  `solution` bodies and at most once in the whole file, on an
  `attribute [-simp] PeriodPair.…` line, which is the pin's `p2m_*` scaffolding
  re-exporting its entire inlined prelude. The consequence is a wrong reading of the
  proof's architecture (it would put the complex uniformization on the `R = T` path).
  **Before believing a closure edge, grep the callee's `solution` body**; the closure is
  an upper bound on what a file *contains*, not on what it *uses*.
- **A co-import collision can be a *producer-vs-classes* choice, not a rename (found
  2026-10-06, P-2 D-1).** `WeierstrassCurve.Affine.instInfinitePlace` is declared twice:
  `Place/RRSpace.lean` (`scoped instance`, the pin's own, hypotheses `[IsAlgClosed F]
  [IsDedekindDomain W.CoordinateRing] [HasPrincipalDivisors …]`) and
  `IsogenyEndDatum/Engine.lean` (a plain `instance`, the port's invention, hypotheses
  `[W.IsElliptic] [GenusOnePlaceGate W] [IsCentred W]`). No environment can import both
  (`environment already contains '…instInfinitePlace._proof_4'`), which had blocked the
  whole P-2 base-change column: D-1 needs the gate classes and D-4/D-5 need `Engine`'s
  seam. The resolution was **not** to rename either instance (`Engine`'s is a port
  declaration already in `OWN_PROOFS`; `RRSpace`'s is the pin's) but to stop importing
  the *producer* module: the classes `GenusOnePlaceGate`/`IsCentred`/`AbelTheorem` live
  in the lighter `WeierstrassCurve/GenusOnePlaceGate.lean`, while
  `GenusOnePlaceGateCentred.lean` is the producer
  `exists_genusOnePlaceGate_isCentred_and_abelTheorem` and is the only importer of
  `RRSpace` in that chain. D-1 now imports `GenusOnePlaceGate.lean` and the pairing with
  `Engine.lean` compiles. **The producer module still cannot be co-imported with
  `Engine`** (`spec/IsogenyEndDatumConsumer.lean` zones 3/5 keep the gate instances as
  hypotheses for that reason); a consumer that *produces* the gate instances and one that
  uses `Engine` must remain separate `spec/` files until one instance is reconciled.
  Rule for the column: [topics/velu/WORKORDER-P2-basechange.md](topics/velu/WORKORDER-P2-basechange.md)
  §3.1.

  **Consequence found 2026-10-06: the S/D capstone is the blocked consumer.** It is no longer
  only a `spec/` inconvenience. `WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`
  (row S's terminal node, the manager's set **SC**) needs **both** sides in one module:
  - the **producer** `exists_genusOnePlaceGate_isCentred_and_abelTheorem`
    (`GenusOnePlaceGateCentred.lean:38` → `Place/RRSpace.lean:444`), because its proof
    descends to a countable `K₀` and then must *supply* the `GenusOnePlaceGate`/`IsCentred`/
    `AbelTheorem` instances that set D-6's headline quantifies over the base-changed curves
    (`obtain ⟨g₁, c₁, a₁⟩ := … (W := (E₀.baseChange (AlgebraicClosure K₀)).toAffine)`, and
    the same for `E₀'`);
  - `Engine.lean`, transitively, because the same proof calls D-6's headline and
    `TwoCurveDescent.lean:55–56` imports `Isogeny/KernelBaseChange.lean`, which imports
    `IsogenyEndDatum/Engine.lean`.
  No environment holds both. **SC cannot be written until this is resolved.**

  **Resolved by policy 2026-10-06 — route (A), and it is a one-word edit.** The user's
  direction: *"if private instances can improve builds we shouldn't be shy to use them — we
  don't have to depend on Lean elab."* That is the playbook's own §2.4 rule ("which side stays
  is the pin-public wrapper; **re-privatize** the pin-private name and keep local aliases so
  untouched consumers keep working"), which this column deviated from when it chose to keep
  ours public and instead split consumers across `spec/` files. Do it properly:

  - **(A) Reconcile the instance — chosen.** Mark `WeierstrassCurve.Affine.instInfinitePlace`
    (`IsogenyEndDatum/Engine.lean:90`) **`private`**. A `private` declaration's name is
    mangled (`_private.<Module>.<n>.<name>`), so it no longer clashes at the environment level
    with `RRSpace.lean:444`'s pin-public `scoped instance` — the same mechanism that already
    lets the port carry two copies of a `private` duplicate elsewhere (see
    "two copies of one statement" below). No renaming, no shim layer, and the instance stays
    findable by instance search downstream, which is what D-4/D-5 rely on. Two consequences to
    reconcile in one build: the checker stops seeing it (it reads only non-private
    declarations), so the compared count drops by one — it is already on `OWN_PROOFS`, so this
    is the expected `-1`, not a loss — and `Engine.lean`'s own consumers
    (`restrictAlong_eq_infinitePlace`, and through it `pointEnd'_eq_of_seam` in D-4/D-5) must
    still elaborate. **Price the cascade with `build_ladder.py --edit` first**: `Engine.lean`
    is not a leaf, and it must not be edited while another set is mid-check, since every D-4/D-5
    module imports it. **Fallback if the confirming build shows a consumer cannot find the
    instance**: rename it instead (`instInfinitePlaceEngine`) and update its users — same
    one-name fix, keeps it public and findable, at the cost of a slightly less tidy name.
    Either way the collision is gone; the two differ only in whether the instance is public.

    **Priced and pre-flighted 2026-10-06** (`build_ladder.py --edit`): the cascade is
    **9 dependent modules / 12,280 lines ≈ 175 s** — `DualEndData` (3,930), `RestrictAlongAdd`
    (2,505), `KernelBaseChange` (1,378), **`TwoCurveDescent` (1,228)**, `TranslationAlgEquiv`
    (1,124), `Vocabulary` (644), `CharPolySquare` (581), `KernelCyclicTransfer` (473),
    `PointEndSubring` (417); tier 2 is
    `lake build TwoCurveDescent CharPolySquare`, tier 3 the full build. The edit itself is one
    word at `Engine.lean:90`. **Why the confirming build is not a formality**: the instance is
    relied on *outside* `Engine.lean` by instance search — `DualEndData.lean:3248–3254`
    (`InfinitePlace.place`, `not_isFinitePlace`) and `KernelBaseChange.lean:902,917` use it
    inside sections that carry only `[W.IsElliptic] [GenusOnePlaceGate W] [IsCentred W]`. So the
    test is two-fold: (i) a `Scratch.lean` importing **both** `IsogenyEndDatum/Engine` and
    `GenusOnePlaceGateCentred` must elaborate (the collision is gone), and (ii)
    `lake build FLTForHuman.WeierstrassCurve.Isogeny.KernelBaseChange
    ...IsogenyEndDatum.DualEndData` must stay green (private instances are still found by
    search across imports). If (ii) fails, take the rename fallback above. Note also that the
    port made `InfinitePlace` a **class** (`Place/Dictionary.lean:674`) on purpose — so the
    pin's `InfinitePlace.place` statement text still elaborates — which is why an *instance*
    exists here at all and why it cannot simply be deleted.

    **DONE AND VERIFIED 2026-10-06.** `Engine.lean:90`'s instance is now `private` (with a
    comment giving the reason), and the three tests that matter all pass:
    (i) `lake build …IsogenyEndDatum.Engine` — green, 3,851 jobs, 38.8 s;
    (ii) `lake env lean` on a probe importing **both** `IsogenyEndDatum/Engine` and
    `GenusOnePlaceGateCentred` — **elaborates in 5.4 s**, where before it failed with
    `environment already contains 'WeierstrassCurve.Affine.instInfinitePlace._proof_4'`. The
    collision is gone, so SC and the `spec/` split can be written;
    (iii) `lake build …IsogenyEndDatum.DualEndData …Isogeny.KernelBaseChange` — green,
    `Build completed successfully (9037 jobs)`, confirming the private instance is still found
    by instance search across imports. **The rename fallback was not needed.**

    **SC landed on this route 2026-10-07.** `ModularCurve/ModularPolynomialEvalJ.lean` holds the
    producer and `Engine` in one environment; the dispatch pre-flight (a stub importing both and
    using `exists_genusOnePlaceGate_isCentred_and_abelTheorem` and `placeOfPoint_zero`)
    elaborates exit 0, and the whole tree is green. The capstone's unported frontier closure is
    now 0 nodes / 0 lines. See `topics/velu/WORKORDER-SC-capstone.md` §7 and
    `logs/velu-port.md` §SC.

    Also measured: because the cascade includes `TwoCurveDescent`, do this edit when no set is
    mid-check — it forces a ~10-minute rebuild of the whole tree.
  - **(B) Re-home the gate construction off `RRSpace`. Do not trust the tempting short
    reading of this route — it was checked and it is not vestigial.** The producer is 79
    lines (`GenusOnePlaceGateCentred.lean:38`) and its body names *none* of `rrParam` /
    `RRSpace` / `basisAux` / `finBasis` / `exists_not_isFinitePlace` — so the `RRSpace` import
    looks droppable. It is not: the producer builds its gate from `geomPointEquivPlace` and
    `geomPlaceOfPoint_surjective`/`deg_geomPlaceOfPoint`, and **every one of those is stated
    under `[InfinitePlace W]`** (`Place/GeometricPlace.lean:57,60,65,87`) — the instance that
    `RRSpace.lean:444`'s scoped definition supplies, activated by
    `open scoped WeierstrassCurve.Affine` at `GenusOnePlaceGateCentred.lean:32`. That is the
    real dependency. Building the same instance without `RRSpace` means moving
    `exists_not_isFinitePlace` (`RRSpace.lean:386`), `deg_eq_one_of_not_isFinitePlace` (:303),
    `eq_of_not_isFinitePlace_of_not_isFinitePlace` (:212) **and
    `mem_iff_natDegree_norm_le` (:189), which does use the RR space**
    (`CoordinateRing.mem_RRSpace_iff_degree_norm_le`, `finrank_eq`) — so (B) may have to move
    the RR-space norm/degree block too. A bounded probe settles it: cut the `RRSpace` import,
    `lake build` the producer, and see which name is missing. A third route — re-proving the
    producer against a gate-free `placeOfPoint` surjectivity — **is not available**:
    `Engine.lean:115` and `:118` both prove surjectivity *from* `(pointEquivPlace W)`, exactly
    as the pin's `S_` file does (`:306–310`), so it is downstream of the gate.
  (B) is the port's own route and adds no collision; (A) is smaller if the cascade is small.
  Either way, **D-6's own module is unaffected** — it takes its gate instances as the `∀`
  binders of the headline and never produces one.
- **Two pin files can declare one name with two different statements (caution, P-2 D-4/D-5,
  resolved for this column).** `ModularCurve.kw_fdn2_qephod_hend7_pmopKerCard_proved` is a
  `Prop` (`KwD5PointMapOfPushforwardKerCard`) in
  `S_WeierstrassCurve_Affine_natCard_ker_pointMapOfPushforward_eq_finrankAlong.lean:526` but
  a `Nat.card … = finrankAlong K ι` theorem in the two D-5 silos, the two S-row files and the
  `conj` file. A declaration name is *one* environment-level key, so the second copy is
  undeclarable in any module whose cone contains `NatCard.lean` — which is the whole D
  column. Nothing is lost: the second copy's content is exactly the already-ported
  `WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong`
  (`IsogenyEndDatum/Vocabulary.lean:161`). Both D-4 and D-5 use the imported lemma and neither
  declares the name; the same rule holds for the S row. The failure mode is an
  elaboration-time `has already been declared`, which the statement checker cannot see.
  Related trap, same column: a same-name declaration's **span** in `port_advise` measures the
  `p2m_*` scaffolding between declarations, not its body — `KwD5BetweenCurvesHoloLift` read as
  748/151/83/25 lines across five files and is byte-identical in all five (`sha256`,
  2026-10-06). Diff normalized bodies, never spans.
- **A row can surface again as a fresh silo the day after it lands (found 2026-10-06,
  after P-2).** `frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen
  --rank-by silo --ready` ranks
  `WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`
  **first, at 3,729 silo lines**, and it is now `hops 1` with an unported closure of **0**
  — because P-2 landed every one of its eighteen cited premises. That is the tell: a node
  whose closure is the column just shipped is the column again, restated. It is the D row
  in two-curve form, not new mathematics:

  - `port_advise` finds **107 of its 183 declarations** with an identical statement
    already in the port (≈2,077 raw lines; 76 trusted + 31 suspect). **26 of the 27**
    `private` hits are D-2's descent core in
    `WeierstrassCurve/Isogeny/IntermediateField.lean` (`iA_*`, `iCa_*`, `iPFA_*`, `iPFE_*`,
    `iCa_K₀`, `iP_xP`). Nine of the 31 suspect hits are the tool's type-only
    `def … : Prop` match against `PeriodPair.DiscriminantNeZero`: the `KwD5*` class wrappers
    are new, the match is not.
  - `port_plan` prices the file at **1,975 net-new** lines, not 3,729.
  - At source level **62%** of the file's substantive lines are verbatim in the five pin
    files P-2 landed — 41% in the D-2 `S_` file alone, 47% in each D-5 silo. (Measure:
    lines ≥12 chars with the `kw_` prefix stripped; an upper bound, since generic tactic
    lines count — but it agrees with the declaration-level 58%.) The descent block
    (`:1799–2386`) is a byte-identical copy of D-2's — same construction, second curve.

  **Correction (2026-10-06, found by set D-6's worker and verified).** The base-change
  engine (`kw_surgehgf4_hfgkd_bc*`, `:2519–2839`) is *not* importable from D-5. It is the
  **`NoAC` spelling** — no `[IsAlgClosed F]`, no gate instances — and the two-curve descent
  needs it at `F = K₀`, a subfield that is neither algebraically closed nor gate-equipped.
  D-5 landed only the `General` twin: `KernelBaseChange.lean:133–141` carries
  `[IsAlgClosed F] [IsAlgClosed F']` and the four `GenusOnePlaceGate`/`IsCentered`/`AbelTheorem`
  blocks as section variables, so `kw_surge_hgf4_bcIota₁` cannot be instantiated at `K₀`.
  This is the same `General`/`NoAC` split D-1 met in the prelude — and D-1 *resolved* it
  (the `NoAC` name is the primitive, the `General` name a one-line invocation) while D-5's
  section did not, so the engine now costs D-6 ≈320 lines it could have imported. The
  statement test could not see this: it matched four of the engine's declarations by type
  and the rest not at all, because the binders differ (`hfin₀`/`ι₀` against `hfin'`/`ι'`).
  D-6 transcribes the `NoAC` engine once, `private`, in its own module, and the
  reconciliation is registered as an open follow-up below.
  - The tail is `s13_stub_ktd`, a twelve-line call into the just-landed
    `isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom`, then a twenty-line
    `solution`.

  What is genuinely new is one **generalization**: D-2 landed the countable descent for an
  endomorphism of a single curve (`KwIsogenyEndDatumSubfieldDescent`, `iCa_*`, `iPFA_*`),
  and the pin's two-curve case — `ι : E'.FunctionField →ₐ[K] E.FunctionField` between
  *different* curves, `KwD5BetweenCurvesSubfieldDescent` — occurs only in this file (every
  `∃ K₀ …` in the port is one-curve). The new layer is the `hSD_*` / `cfe_*` /
  `ChiCompChiEqPhi` block **plus the `NoAC` engine** (the correction above), ≈1.1k lines by
  hand. **Do not port the file**: generalize D-2's
  landed chain to two curves in place (playbook §2.4, "port the general, derive the
  special" — the descent helpers are already written, `private` in `IntermediateField.lean`,
  so the work is promotion plus a second curve, not transcription), and
  the headline becomes a short composition with D-5's. Its only consumer is the 415-line
  capstone `eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`.
  Reproduce:
  `python3 tools/deps/port_advise.py --nodes WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`,
  then `port_plan.py` on its `--json`; the frontier command is the one above.
