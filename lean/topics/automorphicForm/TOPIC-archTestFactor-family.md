# The archimedean approximate-identity family

**Status: the silo LANDED (2026-10-13)**; the four consumer headlines remain out of
scope. This is the planning note for the
`AutomorphicForm` silo
`AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`
and the four headlines that rest on it. It follows the two recent large-silo
efforts — [TOPIC-rightConv-comm.md](TOPIC-rightConv-comm.md) /
[WORKORDER-P-rightConv-comm.md](WORKORDER-P-rightConv-comm.md) and their definition
gate, and [../numberTheory/tateGlobal/TOPIC-tateglobal-analytic-core.md](../numberTheory/tateGlobal/TOPIC-tateglobal-analytic-core.md).
The method is [porting-playbook.md](../../porting-playbook.md) §2.1–§2.6, §3.1–§3.5, §4.
Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`);
port mathlib `v4.34.0`.

The organizing rules this note applies are the ones the recent landings settled:

* **whole nodes** — a pin file (or a pin *subject*) is transcribed entire; the
  declarations the current headline reaches are the floor, not the scope;
* **public API public, checker wiring by consumer** — every ported declaration is
  public at the pin's name, but only modules with a real consumer are listed in
  `spec/check_flt_statements.py`; everything else is registered in
  [spec/UNWIRED-PUBLIC.md](../../spec/UNWIRED-PUBLIC.md) by
  `tools/deps/unwired_register.py`;
* **natural homing** — one module per mathematical role, not one per pin file;
* **build cycle** — new files only, tier-0 at a *low* heartbeat cap, tier-1 per
  module, no whole-tree build, and instance inference is fixed at homing time,
  never papered over with a cap.

## 1. The measurement

### 1.1 The single silo

`frontier.py` prices the target at **1 node / 3,154 raw `S_` lines**, but that is
the `S_` file and nothing below it: the docs-site graph records the node with
`cites 0`, so its closure is itself. Two consequences:

* it **is** in the Deligne–Serre cone (the cone closes at 2,308 nodes) and sits in
  the 1,654-node `needed` demand, but its consumer chain runs to the root through
  `AutomorphicForm.finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule` →
  `LanglandsTunnell` → `FLT.No2BridgeWiring` → `FreyPackage`, not through the
  weight-one column;
* `--ready` and `--hops` **hide it** — a graph leaf with `needed == 1` cannot reach
  `F`, and the ready view drops such nodes. It appears only under
  `--include-leaves`, where it is **rank #2 by silo among 561 leaves**
  (`M4aTorus.completedRayL_fe` 12,126; this node 3,154), and when queried directly.

The real content, from `port_advise` + `port_plan`:

| quantity | value |
|---|---:|
| raw `S_` lines | 3,154 |
| top-level declarations | 200 (194 distinct names) |
| distinct declaration groups | 193 |
| duplicate copies removable in-file | 39 |
| boilerplate (imports/attrs/`p2m`) | 18 |
| once-cost after dedup | 3,097 |
| already in the port (vetted) | **20** |
| **net new math lines** | **3,077** |

The headline's own proof closure is **154 private helpers ≈ 2,778 lines** — 122
theorems / 2,607, 28 `def`s / 163, 4 `abbrev`s / 8 — of which 149 are new and 5
have a port counterpart (20 lines). About **45 declarations / ≈358 lines sit
outside that closure** (bundled instance scaffolding, injectivity lemmas, the
`solution` itself). A demand-faithful port is therefore ≈2.76k lines; a whole-file
port ≈3.08k.

**Reuse is nearly nil.** The only vetted substitutions are

| pin | port | note |
|---|---|---|
| `continuous_adelicArchGLIncl` (13) | `AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl` | public, import |
| `continuous_archEntries` (7) | `AutomorphicForm.continuous_archEntries` | **`private` in the port** — promote or re-derive |

The other two table rows (`EntrySpace`, `Kprod` → `FLTForHuman.Elliptic.Univ.Poly`)
are the parser's type-only *suspect* matches and are wrong; a whole-tree check
confirms the port declares no `Ent`/`EntrySpace`/`Kprod` analogue.

### 1.2 The family

The node's four consumers are themselves silos, and every one is unported:

| consumer | `S_` lines |
|---|---:|
| `…exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule` | 823 |
| `…exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule` | 854 |
| `…exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre` | 3,038 |
| `…exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule` | 971 |

`port_advise`/`port_plan` over the five:

| quantity | the five |
|---|---:|
| raw `S_` lines | 8,840 |
| declaration lines | 8,691 |
| duplicate copies | 1,344 |
| once-cost after dedup | 7,347 |
| already in the port (vetted) | 32 |
| **net new math lines** | **7,315** |
| distinct declaration groups | 510 |

**The family is not a tight merge, and this is the first planning finding.** The
three `isUnitFactorizableAboveOfType` silos share 511 + 151 lines (41 + 7
declarations) among themselves and are a cluster; our silo shares with the other
four only `isHaarMeasure_archHaarK` (4 files), `locallyCompactSpace_archGL`
(5 files), `continuous_adelicArchGLIncl` (5, already ported),
`continuous_archEntries` (5, already ported) and `contSubmodule` (4 pin files) —
about **43 lines / 2 new declarations**. Name-overlap with the 3,038-line
`coversModCentre` silo is exactly the same two ported helpers. So the correct cut
is the archimedean-infra pair as a shared home, then **this silo on its own**;
the unit-factorizable trio and the `coversModCentre` silo are separate sets.

## 2. The mathematics

The headline is the archimedean approximate-identity step of the smoothing
machine: for `f` continuous on `GL₂(𝔸_L)` and of prescribed archimedean type
(`f ∈ archCutSubmodule L tys`), there is a sequence of compactly supported
`C^∞` test factors `fa n` on `GL₂(𝔸_{L,∞})`, each bi-finite for `tys`, with
`∫ f (g · ι(y)) · fa n y dμ(y) → f g`. It is the archimedean half of
`exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule`.

The proof has five movements:

1. **archimedean measure and topology** — `isHaarMeasure_archHaarK`, second
   countability of `𝔸_{L,∞}`, its matrix ring and `GL₂`, the product Haar `muK` on
   `∏_w rowIsometrySubgroup₀`, the inclusion `inclArch : ∏_w K_w → GL₂(𝔸_{L,∞})`
   and its adèlic companion, and `integral_archHaarK_mul_inclArch`;
2. **row-isometry compactness and entry balls** — `isCompact_rowIsometrySubgroup₀`,
   the ball system `entryBall` / `detLocus` / `toGL`, `exists_bump`,
   `exists_approxIdentity`, `tendsto_integral_mul_approxIdentity`;
3. **the type-reproducer engine** — `piRep`, the coefficient maps
   `coeffFun`/`dualCoeffFun`/`transRep`, the translate span
   (`rt`, `spanTranslates`, `exists_finiteDimensional_stable`) and the positivity
   engine `Mint`/`Hm`/`Dm`/`exists_reproducer`/`Pm_entry_mem_iSup` that realizes
   `1` in the span of the integrated projections;
4. **the double-convolution limit** — `contSubmodule`, `dconvWith`, `convOpR`/`convOpL`,
   the type-membership lemmas, compact support, `tendsto_integral_mul_dconvWith`,
   and the parametric-integral differentiability
   (`contDiffNat_parametricIntegral_postcompCLM`, `contDiff_parametricIntegral_mul`);
5. **the instantiation** — `Ent`/`twoSided`, `exists_contDiff_dconvWith`, `main`,
   `solution`.

Movements 3 and 4 are generic representation theory / group convolution and
mention neither the adèles nor `GL₂`; movement 1, 2 and 5 are adèlic.

## 3. The layer map and the natural homes

The `S_` file's `section`s and pin ranges (they are sections, so they do not sum
to the file length):

| pin lines | pin section | mathematics | role |
|---|---|---|---|
| 9–36 | `Carry1`/`Q09` | `isHaarMeasure_archHaarK` | adèlic measure |
| 38–130 | `Q09AIarchC` | second countability, `archMatrix`/`archGL` topology, Borel, σ-finite | adèlic topology |
| 147–236 | `Q09AIarch.Compact` | `rowIsoSet`, `isCompact_rowIsometrySubgroup₀` | compact subgroups |
| 238–344 | `Q09AIarch.Setting` | `Kw`, `Kprod`, `inclArch`/`inclAdelic`, continuity | adèlic inclusion |
| 346–405 | `Q09AIarch.HaarKprod` | `KprodTop`, `muK`, invariance and integral lemmas | product Haar |
| 407–509 | `Q09AIarch.Alpha4` | `exists_isCompact_preimage_mul_inclArch_eq`, `haarScalarFactor_map_mul_inclArch`, `integral_archHaarK_mul_inclArch` | Haar scaling |
| 520–874 | `Q09AIarchG` | `matrixEntries`, `entryBall`, `detLocus`, `toGL`, `exists_bump`, `exists_approxIdentity`, `tendsto_integral_mul_approxIdentity` | balls and bump |
| 877–920 | `Q09RowIso` | row-isometry component/injectivity | compact subgroups |
| 926–1647 | `Q09` (`TypePiece`…`MultiPlace`) | `piRep`, `coeffFun`/`dualCoeffFun`/`transRep`, `rt`, `spanTranslates`, `exists_finiteDimensional_stable` | type engine (generic) |
| 1657–2131 | `Q09` (`Delta`/`Mint`) | `piE`, `Pm`, `Mint`, `Hm`, `Dm`, `exists_reproducer`, `Pm_entry_mem_iSup` | repr. engine (generic) |
| 2141–2206 | `Q09.ZetaB0` | `Pm_entry_mem_iSup` tail | repr. engine |
| 2216–2617 | `Q09.ZetaB` | `contSubmodule`, `dconvWith`, `convOpR`/`convOpL`, type membership, support, limit | convolution (generic) |
| 2626–2856 | `Q09` (`DominatedDUIEngine`/`ScalarWeighted`) | `tendsto_integral_mul_dconvWith`, parametric-integral `ContDiff` | convolution (generic) |
| 2859–3134 | `Q09.Instantiate` | `Ent`, `twoSided`, `exists_contDiff_dconvWith`, `main` | adèlic assembly |
| 3137–3153 | `Carry6` | `solution` | headline |

**Proposed homes** (indicative; the manager re-cuts a boundary, never moves a
declaration across a dependency):

| module | contents | ≈ lines |
|---|---|---:|
| `AutomorphicForm/Adelic/ArchHaar.lean` (**landed**) | **definition gate** (§5): `glBorelOf`, `borelSpace_glBorelOf`, `archHaarK` | 68 |
| `AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean` | `isHaarMeasure_archHaarK`, `Kw`/`Kprod`, `muK`, `inclArch`/`inclAdelic`, `integral_archHaarK_mul_inclArch`, row-isometry compactness | 700 |
| `AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean` | `matrixEntries`…`tendsto_integral_mul_approxIdentity` | 450 |
| `RepTheory/TypeReproducer.lean` | movement 3, generic | 1,150 |
| `RepTheory/ConvolutionLimit.lean` | movement 4, generic | 700 |
| `AutomorphicForm/Adelic/ArchApproxIdentity/Instantiate.lean` | `Ent`, `twoSided`, `rtStabilizer`, `exists_contDiff_dconvWith`, `main`; **tier 3** | 280 |
| `AutomorphicForm/Adelic/ArchApproxIdentity.lean` | the headline only, at the wrapper's name; **tier-1 façade** | 20 |

`ArchInfra` should **import rather than re-prove** what the port already has:
`RightConvComm/Frame.lean`'s `SecondCountableAdelic` block, `Adelic/ArchType.lean`'s
`adelicArchGLIncl`, `IsotypicCuspSpace.lean`'s `archRowIsometryInclAt₀` and
`typeSubmodule`, `Adelic/CarrierPins.lean`, and the `AdelicHaar/*` layer. What the
port lacks is the `rowIsoSet` compactness, the `Kprod` product Haar and the whole
`Mint`/`dconvWith` engine.

## 4. Public API and checker wiring

* **All 193 declarations are public** at their pin-natural names; the pin's
  `private` helpers are either promoted to the pin name (when a public statement
  mentions them) or stay `private` with a local re-derivation (the two-body trap of
  WORKORDER-P §1 is the model).
* **Tier 1 (listed in `PORT_FILES`)** is exactly the façade's headline plus, once a
  consumer exists, the definition-gate module. The `identical` delta must equal
  that public surface.
* **Tier 3 (registered, unlisted)** is everything else. Every transcribed
  declaration carries `-- pin: <name> (<file>:<line>)` immediately above it so
  `tools/deps/unwired_register.py` fills the `pin original` column; run the
  register at the end of every wave and treat a `—` as a defect.
* The four consumer headlines are **separate sets**; only this silo's headline is
  in scope here. The unit-factorizable trio and the `coversModCentre` silo are
  named as out of scope.

## 5. The definition gate

The `S_` file imports exactly **one** pin `Definitions/` module,
`Definitions/Def_AutomorphicForm_TwistedOrbital.lean` (574 lines / 83
declarations). Hand-walking its transitive closure finds **14 unwired modules /
4,390 pin lines**, but the silo names only **three** declarations from any of them:

| pin declaration | pin line | port |
|---|---|---|
| `glBorelOf` | `TwistedOrbital.lean:57` | absent by name; `MeasureAssembly.archBorel` is statement-identical (`:= borel _`) |
| `borelSpace_glBorelOf` | `:59` | absent public; `MeasureAssembly.borelSpace_arch` is `private scoped` |
| `archHaarK` | `:401` | **absent under any name** (`archNu` is a `U`-dependent pushforward, not `Measure.haar`) |

`glBorelOf` and `archHaarK` occur literally in `solution`; `borelSpace_glBorelOf`
is definition-transitively required by `archHaarK`'s body. The other 13 modules —
`UnitFactorizableOfType`, `Completion_BaseChange`, `SigmaCentralizer`,
`M4aHerbrand_ArchSemilocal`, `LocalOrbitalBase`, `DedekindDomain_IntegralClosure`,
the four `Mathlib_*` supplements, `InfiniteAdeleRing_BaseChangeData`,
`Localization_BaseChange`, `Algebra_Algebra_Hom`, `NumberField_Extension` — are
**named 0/N** by the `S_` file. The twisted-orbital subject of `TwistedOrbital`
(`semiLocalHaar`, `IsTwistedOrbitalIntegral`, `AreMatchingOn`, `archHaarL`,
`archIdent`, `AreMatchingArch`, …) is not named either.

**The cut, landed.** Home the archimedean-Haar subject
`{glBorelOf, borelSpace_glBorelOf, archHaarK}` — the part with known consumers —
in `AutomorphicForm/Adelic/ArchHaar.lean` (68 lines, namespace `AutomorphicForm`,
the pin's own), keeping the pin's declaration texts: `glBorelOf` is the pin's
`@[reducible] def := borel _`, never a registered `MeasurableSpace` instance, so it
cannot diamond with mathlib's Borel instance. The rest of `TwistedOrbital` (the
finite-place twisted-orbital subject, 83 − 3 declarations, plus
`archHaarL`/`archIdent`/`AreMatchingArch` whose dependency is the unported
tensor/base-change chain) is its **own** definition wave; it has no consumer here,
and forcing it in front of this silo would drag `Completion_BaseChange` +
`M4aHerbrand_ArchSemilocal` + the `Def_Mathlib_*` supplements. This is the
split-by-mathematical-role precedent the foundation used for
`Def_NumberField_AdelicHaar` and `Def_AutomorphicForm_AdelicLsXi`.

**Postscript — the pre-existing `glBorelOf` twin.** The port's
`MeasureAssembly.archBorel` (`RightConvComm/MeasureAssembly.lean:61`) and its
`local instance` uses in `SliceCentrality.lean:55` are statement-identical to
`glBorelOf` specialized at `InfiniteAdeleRing F`. D0 did **not** collapse them:
`archBorel` is a port-only adapter carrying a `[Field F] [NumberField F]` binder
shape, so replacing it means editing two modules of the `RightConvComm` cone. It
is registered as a dedup follow-up in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md); until then the two `borel _` defs
coexist harmlessly.

**Verification of the gate.** Coverage by name: the three declarations present, at
the pin's names; tier-0 green at the 200,000 heartbeat cap with 0 warnings;
tier-1 `3,447 jobs` green; the register gains one module / three declarations, each
with a `pin original`. The checker is unchanged (9,237 identical / 0 mismatched /
0 missing / 38 own) because the module is tier 3. It is added to `PORT_FILES` and
`TwistedOrbital.lean` to `SOURCES` (both last) only when the façade is wired.

## 6. The instance stack and the build cycle

This is the part the recent orders call out, and it is solved **at homing time**,
not deferred.

The `S_` file's first 500 lines are almost entirely instance plumbing: it
re-declares `archGLMeasurableSpace`/`archGLBorelSpace` three times,
`t2Space_archMatrix` three times, `locallyCompactSpace_archGL` twice, and the
`SecondCountableTopology` facts for `𝔸_{L,∞}`, its matrix ring, `GL₂`, the place
completions and `∏_w rowIsometrySubgroup₀`; it also carries `private scoped
instance`s for `CompactSpace (Kw w)`, `IsProbabilityMeasure muK`,
`IsMulLeftInvariant muK` and `IsHaarMeasure muK`. The port already has most of
these **`private scoped`** in `RightConvComm/Frame.lean` (so the *instances* are
found by search but the *names* are not importable) and public topology instances
in `AdelicHaar/{Adele,GeneralLinear}.lean`.

The plan:

1. `AutomorphicForm/Adelic/ArchHaar.lean` carries the definition gate. It needed
   **no new instance stack**: `archHaarK` elaborates at the pin's text against
   mathlib's `LocallyCompactSpace K∞` (`InfiniteAdeleRing` is the Pi type
   `(v : InfinitePlace K) → v.Completion`) and the port's public
   `t2Space_infiniteAdeleRing`, with the matrix and `GL₂` instances supplied by the
   pin's own `inferInstanceAs` and
   `Units.isClosedEmbedding_embedProduct.locallyCompactSpace` inside the body.
   `InfiniteAdeleRing` is a `def`, so the instances stay explicit rather than left
   to unfold the Pi type — the TateGlobal lesson on `Function.update`.
2. The `S_` file's own `secondCountableTopology_*` / `archGLMeasurableSpace` /
   `archGLBorelSpace` / `t2Space_archMatrix` block is the pin's file-local
   plumbing: the port's `RightConvComm/Frame.lean` keeps its versions `private
   scoped`, so the silo modules re-derive the few facts they need as `private`
   declarations, exactly as the pin does. The genuinely `scoped` ones (the `Kprod`
   probability measure and its invariance) stay local to the module whose section
   binds them, per WORKORDER-T1 §3.5 — invisible to the checker, deliberately not
   promoted.
3. **`maxHeartbeats` is never raised**, file-wide or per declaration. The tier-0
   loop is `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false
   <file>`; the first declaration to exceed the low cap is the culprit, diagnosed
   with `set_option trace.Meta.synthInstance true` in a scratch copy and fixed by
   supplying the instance (`letI`/`haveI`, `@`-application, `inferInstanceAs` with
   the elaborated type) or by avoiding the unfolding that hides it. The port's
   current automorphic modules re-elaborate in 5–9 s at the 200,000 cap, so the
   baseline is healthy; a new module outside that band is an inference defect.
4. **New files only.** D0 landed as one new file with no cascade. No promotion is
   needed: the silo's `continuous_archEntries` is a pin-`private` proof helper, so
   a `private` local re-derivation is the right treatment and
   `TestFnNearIdentity.continuous_archEntries` stays `private`. The one candidate
   hub edit is the `archBorel` dedup of §5, deliberately deferred. No whole-tree
   build.

## 7. The plan

Two stages, the first a gate for the second.

**Stage 1 — the definition gate (one set; landed).**
`AutomorphicForm/Adelic/ArchHaar.lean`, 68 lines / 3 declarations, as in §5–§6. No
promotion, no cascade. `glBorelOf`, `borelSpace_glBorelOf` and `archHaarK` are in
the port at the pin's names, tier-0 green at the 200,000 cap and tier-1 green, with
the register carrying one new module and three `pin original` rows.

**Stage 2 — the proof silo (two subagent turns, in series).** The five modules of
§3, built in import order. The manager runs **two** subagent turns, not five: the
first carries the adèlic half, the second the generic engines and the façade. The
manager reviews the tree between the turns.

| turn | sets | modules | pin range | ≈ lines | state |
|---|---|---|---|---|---:|---|
| 1 | Q1, Q2 | `ArchApproxIdentity/{ArchInfra,EntryBall}` | 9–923 (Q1 9–517, Q2 520–923) | 1,150 | **landed** (556 + 453 lines, 84 declarations, tier-0 0 warnings, register current) |
| 2 | Q3, Q4, Q5a, Q5b | `RepTheory/{TypeReproducer,ConvolutionLimit}`, `ArchApproxIdentity/Instantiate`, `ArchApproxIdentity` (façade) | 926–3153 | 2,150 | **landed** (1,380 + 682 + 323 + 35 lines; checker +1, milestone build 9,519 jobs green) |

Q1 and Q2 may be split differently inside turn 1 if the ball layer's dependency on
`Kprod` is shallow; turn 2 writes Q3 and Q4 first and finishes with the façade Q5,
which is the only listed dispatch.

**Out of scope.** The four consumer silos (separate sets); the finite-place
twisted-orbital subject of `TwistedOrbital`; the 13 import-only `Definitions/`
modules; any `Definitions/` edit; the `p2m_*` scaffolding; the pin's file-wide
`attribute [-simp]` / `[-instance]` preludes.

## 8. Verification

* **Checker.** `timeout 300 python3 spec/check_flt_statements.py`, `0 mismatched /
  0 missing`; the `identical` delta equals the new listed surface (the façade's
  one headline, once wired). Pin-`private` matches verify through the dotted
  fallback and show as `promoted`.
* **Build.** tier-0 at the 200,000 cap with **0 warnings** on every module; tier-1
  `flock .lake/flt_build.lock timeout 300 lake build <module>` per finished module;
  no whole-tree build while a set is in flight.
* **Register.** `python3 tools/deps/unwired_register.py` regenerates cleanly and
  every new row carries a `pin original`.
* **Consumer.** `spec/AutomorphicFormConsumer.lean` gains a zone per set: the
  archimedean Haar measure and its Borel structure, the product Haar `muK`, the
  entry-ball bump, the type reproducer on a concrete finite-dimensional module,
  and finally the headline at a concrete `L`/`tys`. Deleting any imported module
  must break its zone.
* **Axioms.** `#print axioms` on the headline is
  `[propext, Classical.choice, Quot.sound]`.
* **Mutation test.** One-token mutation on the headline moves exactly one
  `mismatched`, reverted.
* **Sweep.** No `sorry`/`admit`/`axiom`/`native_decide`, no bare
  `import Mathlib`, no `set_option maxHeartbeats`.
* **Faithfulness.** Statements verbatim from the `Theorems/` wrapper, binder names
  included; a `def`/`abbrev` taking type arguments keeps the pin's
  `variable … in` form; header prose in `/- … -/` blocks.

## 9. Risks and open questions

1. **The definition-gate cut (§5) — resolved.** The three named declarations
   landed in `AutomorphicForm/Adelic/ArchHaar.lean`; the finite-place
   twisted-orbital subject of `TwistedOrbital` is deferred to its own whole-node
   wave. The alternative (port `TwistedOrbital` whole first) is correct under a
   strict whole-node reading but costs the 4,390-line closure for mathematics this
   silo never names; that closure is now a recorded future set, not a blocker.
2. **The two-body trap.** `contSubmodule` is copied in four pin files; the
   `isHaarMeasure_archHaarK`/`locallyCompactSpace_archGL` pair in four and five.
   Write one body per pin *name* in the shared home; the other spellings go
   `private` with their own names and are skipped by the checker.
3. **Instance inference (§6).** A low-cap failure that resists a clean fix is a
   stop-and-report with the declaration, pin line and trace — never a cap.
4. **Mathlib drift.** Adapt proofs, never statements; `def`-level drift is recorded
   in the module header (the `Ideal.inertiaDeg'` precedent).
5. **Namespace fidelity.** The `S_` file nests under
   `P2MW.S_AutomorphicForm_…`; strip the pin prefix and declare in the port's
   theory namespaces (`AutomorphicForm`, `RepTheory`), keeping each declaration's
   own binder shape. Two sub-namespaces with the same tail (`Q09AIarchC.Q09` vs
   `Q09AIarch.Q09`) must not be flattened together.
6. **Scope creep.** The silo's 154-helper closure is its own; do not pull the
   consumer silos' copies into the shared home — `port_advise` shows them to be
   binder variants that a later generalisation pass decides on.

## 10. Reproduce

```bash
cd tools/deps
# the silo, its family, and the plan
python3 frontier.py --target AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule --top 0
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --include-leaves --rank-by silo --top 0
python3 port_advise.py --nodes AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule --json build/arch_ident_advise.json
python3 port_plan.py --json build/arch_ident_advise.json
python3 port_advise.py --nodes AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule \
  --nodes AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule \
  --nodes AutomorphicForm.exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule \
  --nodes AutomorphicForm.exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre \
  --nodes AutomorphicForm.exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule \
  --json build/arch_family_advise.json
python3 port_plan.py --json build/arch_family_advise.json
# an edit price before any cascade
python3 build_ladder.py --edit FLTForHuman/AutomorphicForm/Adelic/TestFnNearIdentity.lean
# the definition gate, by hand
python3 explore.py AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule
cd ../lean
timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false FLTForHuman/AutomorphicForm/Adelic/ArchHaar.lean
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Adelic.ArchHaar
cd ..
python3 tools/deps/unwired_register.py
cd lean && timeout 300 python3 spec/check_flt_statements.py
```

The pin sources are public at
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean`
(the `solution` is at line 3142) and its
[wrapper](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean#L9).
