# TOPIC — `NumberField.TateGlobal.continuous_ideleNorm`: a thin-engine port plan

**Status (executed).** The port landed: `TateGlobal/FujisakiC3.lean` (121 lines, 6 public
declarations, tier 3) and the thin listed façade
`NumberField/TateGlobalContinuousIdeleNorm.lean` (42 lines, 2 headlines). The checker
reads **9542 identical / 0 mismatched / 0 missing** (was 9540 — the delta is exactly the
two headlines); both headlines have axioms `[propext, Classical.choice, Quot.sound]`; the
milestone build is green; no existing module was edited. The body below is the
reconnaissance that scoped it, kept as the record of the measurement; §10 records the
landing and the two build-time proof adaptations.

**Pin.** `anthropics/fermats-last-theorem` at `aa2d8b3`; the port's mathlib is
`v4.34.0`.

**Method.** The six-step loop of
[PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3 (read the frontier, cut by
mathematics, scope with the tools, the manager does the shared ground, dispatch, close
out), its §4 (definitions whole-node; `private` is a build tool; a hub edit is a wave),
and [porting-playbook.md](../../../porting-playbook.md) §2–§5.

**Companions.** [TOPIC-tateglobal-analytic-core.md](TOPIC-tateglobal-analytic-core.md)
— the T1 home this node imports — and its order
[WORKORDER-T1-tateglobal-core.md](WORKORDER-T1-tateglobal-core.md). The node is in the
Deligne–Serre target's closure (15 direct / 162 transitive dependents inside it), so
[PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §2 lists it under the
`NumberField` rows that are "reached by the target closure but are not `ModularCurve`
rows"; this note is that row's own plan.

## 0. The recommendation in one paragraph

The node is a 2,645-line silo, but **165 of its 171 private helpers are already in the
port** — the silo re-proves the T1 core — and its genuinely new mathematics is **six
declarations, 65 lines**. Those 65 lines are not the node's own: the same
`normQ`/`continuousOn_ideleNorm` block is re-proved in **nine** sibling `S_` files. So the
port is (a) one small **tier-3 shared engine** homing that block once, at its pin names,
imported by the node and by the eight siblings when their orders come, and (b) a **thin
tier-1 listed façade** that declares only the consumed headline. It **edits no existing
module**: no promotions, no hub edit, no wave. The only future cascade is the one the
thin façade is designed to bound.

## 1. The node

| | |
|---|---|
| pin statement | `Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm.lean` (9 lines) |
| pin proof | `P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm.lean` (2,645 lines, 173 declarations) |
| statement | `Continuous (NumberField.TateGlobal.ideleNorm F)` |
| proof imports | only `Definitions/Def_NumberField_TateGlobalZeta.lean`, `Definitions/Def_NumberField_Completion_Finite.lean` and `P2M.Util` |
| graph position | no pin premises: `frontier.py`'s target closure is 1 node / 2,645 `S_` lines |
| whole-project fan-in | 217 direct dependents (`continuous_ideleNorm`), 163 (`continuous_ideleNorm_det`) |
| Deligne–Serre fan-in | 15 direct / 162 transitive in the target closure |

The statement is a statement about the **definition** layer, and the definition is
already paid for: `NumberField.TateGlobal.ideleNorm` is `TateGlobal/Defs.lean:42` (the
T1 set homed `Def_NumberField_TateGlobalZeta.lean` whole). Nothing must be *stated*
before this node is ported — §4(a) of the Deligne–Serre workflow is already satisfied.

**The mathematics.** `ideleNorm F x` is the real-valued `distribHaarChar` of an idele.
The proof is Fujisaki's: the ideles split as `Q (F := F) S = (InfiniteAdeleRing F)ˣ ×
(SUnits S × DeepUnits S)` over a finite `S` (`asm`, `coord`, `TateGlobal/Coordinates.lean`),
`normQ` is the explicit product of the archimedean norms (weighted by `w.mult`) times the
finite norms, `ideleNorm (asm S q) = normQ S q` identifies the two, `continuousOn_coord`
transports continuity of `ideleNorm` from `normQ ∘ coord` to `unitsOutside S`, and
`continuous_ideleNorm` upgrades `ContinuousOn` to `Continuous` using that every idele lies
in some `unitsOutside S` and those are open.

The trivial corollary `NumberField.TateGlobal.continuous_ideleNorm_det`
(`Continuous fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (det g)`) is a 15-line pin `S_` file
that composes `continuous_ideleNorm` with mathlib's
`Matrix.GeneralLinearGroup.continuous_det`. It is in the same Deligne–Serre closure
(33 direct / 136 transitive dependents there) and is a natural +1 in the same order.

## 2. The measurement

```bash
cd tools/deps
python3 port_advise.py --target NumberField.TateGlobal.continuous_ideleNorm \
  --json build/ci_advise.json
python3 port_plan.py --json build/ci_advise.json
```

`port_advise` reads the pin including `private` (the docs-site graph carries only the
public surface):

| quantity | value |
|---|---:|
| target declarations (2 files) | 174 |
| identical statement already in the port | 159 |
| — importable (public in the port) | 148 |
| — **only** as a port-`private` declaration (in `TateGlobal/Ideles.lean`) | 11 |
| genuinely new declarations | **6** |

`port_plan`'s budget for the single node:

| quantity | value |
|---|---:|
| raw `S_` lines | 2,645 |
| declaration lines | 2,622 |
| duplicate copies | 0 |
| once-cost after dedup | 2,622 |
| already in the port (vetted, all tier 3) | 2,504 |
| substitutions | 155 trusted / 4 suspect |
| **net new math lines (upper bound)** | **118** |

The 118 is an upper bound: 65 lines are the six new declarations (§3), ≈39 lines are
seven glue rows the tool's adapter/name filter does not vet (`ord`, `asm`, `Q`,
`asm_apply`, `sAsm_apply`, `unitAtHom_embUnit_self`,
`coe_ne_zero_of_irreducible` — all present in the port under their names), and the
remainder is boilerplate. The 4 suspect rows are the parser's type-only `def` artifact
(`SUnits`, `archBox`, `box`, `DeepUnits` "matching" `Type`-shaped declarations); they are
the same false positives the T1 topic §2 recorded and are not needed here.

**The 148 importable substitutions are the port's T1 development, all tier 3** (unlisted,
registered in `spec/UNWIRED-PUBLIC.md`). Their homes:

| port module | substitutions |
|---|---:|
| `TateGlobal/Coordinates.lean` | 38 |
| `TateGlobal/FiniteSlab.lean` | 30 |
| `TateGlobal/ArchSlab.lean` | 27 |
| `TateGlobal/Ideles.lean` | 17 public (+11 private, below) |
| `TateGlobal/ArchMulHaar.lean` | 10 |
| `TateGlobal/ValuedOrdBridge.lean` | 6 |
| `TateGlobal/DistribHaarChar.lean` | 4 |
| `TateGlobal/ZetaIntegrand.lean` | 4 |
| `TateGlobal/LocalZetaUnramified.lean` | 3 |
| `TateGlobal/MulHaar.lean`, `TateGlobal/NormIntegrable.lean`, `TateGlobal/ReferenceMeasure.lean` | 2 each |
| `TateGlobal/IntLocalIntegrability.lean` | 1 |
| `Elliptic/Universal.lean` | 2 |

**No promotion is required.** The 11 port-`private` rows all live in
`TateGlobal/Ideles.lean` (the `M4aLocalCFT.ValuationOrd` block renamed
`NumberField.TateGlobal.ValuationOrd`: `ordA`, `ordZ`, `ordA_span`, `ordA_mul`,
`ordA_unique`, `ordZ_spec`, `coe_mk_ne_zero`, `exists_rep`, `exists_span_eq_pow`,
`pow_maximalIdeal_ne_of_lt`, `pow_maximalIdeal_injective`). They appear in the tool's
*same-file closure* of the pin silo because the silo's 165 reused helpers use them
internally — but those helpers are imported as already-proved public declarations, so no
new proof term reaches the private names. Promoting them would force a wave over the
whole T1 cone (below) for zero statement surface. They stay private, per playbook §4(b).

## 3. The shared block — the reason to plan this at all

The six new declarations are all in the pin's final `Fold_FujisakiC3d` section
(`namespace M4aLocalCFT.FujisakiC3`), lines 2568–2637:

| declaration | pin line | span |
|---|---:|---:|
| `exists_mem_unitsOutside` | 2578 | 21 |
| `normQ` (`def`) | 2599 | 4 |
| `continuous_normQ` | 2603 | 7 |
| `ideleNorm_asm_eq_normQ` | 2610 | 9 |
| `continuousOn_ideleNorm` | 2619 | 9 |
| `continuous_ideleNorm` | 2628 | 15 |
| **total** | | **65** |

**This block is not unique to this silo.** The same section is re-proved in eight sibling
`S_` files — the family slice is nine files:

```
S_NumberField_TateGlobal_continuous_ideleNorm
S_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
S_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
S_NumberField_TateGlobal_exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one
S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct
S_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one
S_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_of_exists_mem_normOneIdeles_ne_one
S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe
S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe_analyticAt_one_of_ne_one
```

`port_advise` over all nine (`--targets`, with the `Theorems/` wrappers):

```bash
cd tools/deps
grep -rl normQ ~/proj/fermats-last-theorem/P2M/Sol/S_NumberField_TateGlobal_*.lean > build/fujisaki_c3_files.txt
python3 port_advise.py --targets build/fujisaki_c3_files.txt --no-drags \
  --json build/fujisaki_advise.json
python3 port_plan.py --json build/fujisaki_advise.json
```

| quantity | value |
|---|---:|
| raw `S_` lines (nine files) | 60,093 |
| declaration lines | 59,714 |
| duplicate copies | 45,763 |
| once-cost after dedup | 13,951 |
| already in the port (vetted) | 3,513 |
| **net new math lines (whole slice)** | **10,438** |

The block shared by all nine files is `once 2,736 / inport 2,678 / 163 declarations` —
i.e. **the nine-file block is 2,678/2,736 lines already paid for**, and the
`normQ`–`continuous_ideleNorm` run is its new part. The remaining ≈10,400 net-new lines
are the siblings' *own* developments (a 5-file block of 4,314 once-lines, a 3-file block
of 2,885, and an 8-file block of 513), and are explicitly **not** this plan's scope.

The consequence is the same one the T1 topic drew for the trio: **home the shared block
once, at its pin names, and let the siblings import it.** Porting it privately inside this
node's module would set up eight later orders to re-prove it — the WeightOne failure mode
`port_advise` exists to prevent.

## 4. The port structure

**Engine — `FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiC3.lean`, tier 3,
unlisted.** The six declarations above, public under
`NumberField.TateGlobal.FujisakiC3` (the pin's `M4aLocalCFT.FujisakiC3`, chapter-prefix
renamed exactly as the T1 work order renamed every other `M4aLocalCFT.*` block), each
with a `-- pin: <name> (S_NumberField_TateGlobal_continuous_ideleNorm.lean:<line>)`
comment so `unwired_register.py` fills its provenance column. The name is deliberate:
the port already has a `NumberField.TateGlobal.FujisakiC3` namespace in
`TateGlobal/IntLocalIntegrability.lean` (`distribHaarChar_completion_eq_pow_mult`), so the
pin's block naming is already in the tree.

The six are **not** private in the port. Four siblings carry `private theorem
continuous_ideleNorm` and eight carry the `normQ` block; playbook §4(b) promotes what
another theory states or reuses, and this is the reuse in the family.

**Imports.** The engine imports the four T1 modules that carry the names its 65 lines
use — `TateGlobal/Coordinates.lean` (`Q`, `asm`, `coord`, `asm_coord`,
`continuousOn_coord`; and transitively `Ideles.lean` for `unitsOutside`,
`mem_unitsOutside_iff`, `isOpen_unitsOutside`), `TateGlobal/ZetaIntegrand.lean`
(`ideleNorm_asm`), `TateGlobal/IntLocalIntegrability.lean`
(`FujisakiC3.distribHaarChar_completion_eq_pow_mult`) and
`TateGlobal/NormIntegrable.lean` (`coe_distribHaarChar_adicCompletion_eq_norm`). Every
one is already public (tier 3).

**Hand-check the names.** `port_advise`'s substitution table is name-anchored and its
`port_name` column can pick a last-name fallback: it reports `coord` and
`distribHaarChar_completion_eq_pow_mult` bare, and
`isOpen_unitsOutside` as `NumberField.isOpen_unitsOutside`, while the port files declare
`NumberField.TateGlobal.coord` (`Coordinates.lean:477`),
`NumberField.TateGlobal.FujisakiC3.distribHaarChar_completion_eq_pow_mult`
(`IntLocalIntegrability.lean:109`) and `NumberField.TateGlobal.isOpen_unitsOutside`
(`Ideles.lean:114`). Read each name in its port module before writing the import — the
Deligne–Serre §3 "hand-check the import list" rule, applied to names rather than to
definitions.

**Façade — `FLTForHuman/NumberTheory/NumberField/TateGlobal.lean`, or a thin sibling.**
The consumed headline is one declaration:

```lean
theorem NumberField.TateGlobal.continuous_ideleNorm (F : Type) [Field F] [NumberField F] :
    Continuous (NumberField.TateGlobal.ideleNorm F) :=
  FujisakiC3.continuous_ideleNorm (F := F)
```

Two placements, and the choice is the point of this note:

* **thin (recommended): a new listed module** beside the directory — e.g.
  `FLTForHuman/NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean` — importing
  only the engine, holding the headline (and, if in scope,
  `continuous_ideleNorm_det`). A consumer of `continuous_ideleNorm` then elaborates the
  engine's 40-module / 11,149-line cone (§5) and is insulated from the T1 caps and from
  every future edit to the T1 façade.
* **reuse the existing T1 façade** `NumberField/TateGlobal.lean` (which already imports
  `EulerFactors`, `IntegrableZetaIntegrand`, `IndicatorEulerFactors`). One line, and it
  keeps the "one façade per topic" convention — at the price of putting this node's
  consumers inside the 52-module / 14,787-line cone and coupling them to every future T1
  façade edit.

Given the explicit worry about cascade rebuilds, the thin module is the recommendation;
the one-façade variant is recorded as the fallback if the project prefers a single wire.

**`continuous_ideleNorm_det` (optional +1).** Its pin proof is one composition; it needs
`AdelicGL2` (`FLTForHuman/AutomorphicForm/Adelic/Basic.lean:28`) and mathlib's
`Matrix.GeneralLinearGroup.continuous_det`. Putting it in the thin façade adds the
`AutomorphicForm/Adelic/Basic` cone to that module; a separate listed module would keep
the two cones apart. Either is a one-line proof once `continuous_ideleNorm` is stated.

**Naming and the checker.** The headline's statement authority is
`Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm.lean`; the pin's S_ file carries
the proof and `solution`. Wire (appended last, per the friction log):

* `SOURCES` += `Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm.lean`,
  `P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm.lean` (and the `_det` pair if in
  scope);
* `PORT_FILES` += the listed façade module;
* the engine module stays unlisted; its 6 public declarations appear in
  `spec/UNWIRED-PUBLIC.md` after `unwired_register.py --check` is regenerated, each with
  a pin counterpart.

The port does **not** reproduce the pin wrapper's `attribute [-instance]` prelude; the T1
façade does not carry it either, because the port's definition layer already states the
instances. The `_det` statement's `open NumberField AutomorphicForm` is a port-local
choice to be settled when the module is written.

## 5. The cascade budget

`build_ladder.py --edit` prices an edit to an existing module. The relevant hosts, all
measured on the tree this plan leaves (the engine does not exist yet, so the engine's own
future dependents are the eight siblings and the node's consumers):

| host | dependent cascade | ≈ wall |
|---|---:|---:|
| `TateGlobal/Defs.lean` | 25 modules / 8,900 lines | 108 s |
| `TateGlobal/Ideles.lean` | 24 modules / 8,137 lines | 107 s |
| `TateGlobal/Coordinates.lean` | 23 modules / 7,274 lines | 98 s |
| `TateGlobal/ZetaIntegrand.lean` | 13 modules / 3,680 lines | 49 s |
| `NumberField/TateGlobal.lean` (the T1 façade) | **0 modules today** | 1 s |

The façade's zero is the point: **no module imports it yet**, because the
`AutomorphicForm`/`LanglandsTunnell` consumers are unported. Today the landing is free;
the cascade appears the moment those 200-odd consumer nodes land.

Import-cone sizes (measured over `FLTForHuman` imports):

| module a consumer imports | modules | lines |
|---|---:|---:|
| engine only (thin façade) | 40 | 11,149 |
| existing T1 façade (+ 3 caps) | 52 | 14,787 |

The thin façade keeps a `continuous_ideleNorm` consumer outside the +12-module /
+3,638-line band that the three T1 headline caps (`EulerFactors`,
`IntegrableZetaIntegrand`, `IndicatorEulerFactors`) and their support modules
(`PureTensor`, `EulerBookkeeping`, `Shell*`, `PlaceSum`, `HMajorant`, `AdelicBox`,
`LsXi`) add. Concretely: an edit to any of those twelve does not rebuild the node's
consumers, and an edit to the T1 façade (which will happen when the next T1 headline
lands) does not either.

**Hub prohibition.** No subagent edits `Defs.lean`, `Ideles.lean`, `Coordinates.lean`,
`ZetaIntegrand.lean`, any other T1 development module, or the T1 façade. If one believes
a promotion is needed, it stops and reports with the declaration, the host and the
`build_ladder --edit` price. On the measurement above, no promotion is needed.

## 6. What is not in this set

* **The other eight `normQ` siblings and their ≈10,400 net-new lines.** They are later
  orders, and their own blocks (5-file, 3-file, 8-file) are priced in §3; they will import
  the engine, not copy it.
* **The other 84 `S_NumberField_TateGlobal_*` files** of the 96-file family (96 less T1's
  three and this slice's nine; T1 topic §6).
* **The 200-odd downstream consumers** (Deligne–Serre's automorphic gates, the
  `AutomorphicForm`/`LanglandsTunnell` layers). This plan ports the producer, not the
  consumers.
* **The pin's `P2M.Util` / `p2m_*` scaffolding** — transcription device, not mathematics.

## 7. Risks and open questions

1. **Two façades over one directory (novel).** The thin module is a second listed wire
   for `TateGlobal/`. If the project prefers one façade per topic, take the fallback in
   §4 and accept the larger cone; do not split the difference by listing the engine.
2. **Namespace of the promoted block.** The pin's block is `M4aLocalCFT.FujisakiC3`, the
   port's rename is `NumberField.TateGlobal.FujisakiC3`, and that namespace already exists
   in `IntLocalIntegrability.lean`. Keep one namespace across the two modules (Lean
   allows it); do not introduce `NumberField.TateGlobal.continuous_ideleNorm` as the
   engine's name — the façade owns that name.
3. **`_det` and `AutomorphicForm/Adelic/Basic.lean`.** Including it pulls a second cone
   into the façade. Decide whether `_det` shares the thin façade or gets its own.
4. **mathlib drift on the trivial proof.** `Matrix.GeneralLinearGroup.continuous_det` and
   the `AdelicGL2` topology are `v4.34.0` facts to be checked, not assumed; adapt the
   proof, never the statement.
5. **Heartbeats — never raise the limit.** The global cap stays; a module that exceeds it
   has an instance-inference defect (T1 topic risk §6). The engine is 65 lines; there is
   no reason for a long build and no licence for a `set_option maxHeartbeats`.
6. **The substitution table's `port_name` column.** Name-anchored; verify each name in
   its port module (§4) before trusting the table.
7. **The `_det` node's `SOURCES` pair.** The pin's `S_..._det.lean` imports
   `Theorems/Thm_..._continuous_ideleNorm.lean`; both must be in `SOURCES`, appended
   last, or the checker's last-name matching can flip.
8. **Open.** Whether the engine should also absorb `exists_mem_unitsOutside`'s natural
   home. It is a 21-line lemma about `unitsOutside` and is used by eleven family files,
   more than the nine with `normQ`; semantically it belongs beside `unitsOutside` in
   `Ideles.lean`, but that is a 24-module / 8,137-line hub edit and this plan avoids it.
   Home it in the engine; revisit if a consumer outside the `normQ` family appears.

## 8. Reproduce

```bash
cd tools/deps

# the node and its budget
python3 port_advise.py --target NumberField.TateGlobal.continuous_ideleNorm \
  --json build/ci_advise.json
python3 port_plan.py --json build/ci_advise.json

# the nine-file family slice and its budget
grep -rl normQ ~/proj/fermats-last-theorem/P2M/Sol/S_NumberField_TateGlobal_*.lean \
  > build/fujisaki_c3_files.txt
python3 port_advise.py --targets build/fujisaki_c3_files.txt --no-drags \
  --json build/fujisaki_advise.json
python3 port_plan.py --json build/fujisaki_advise.json

# candidate hosts, priced before any edit
python3 build_ladder.py --edit FLTForHuman/NumberTheory/NumberField/TateGlobal/Defs.lean
python3 build_ladder.py --edit FLTForHuman/NumberTheory/NumberField/TateGlobal/Ideles.lean
python3 build_ladder.py --edit FLTForHuman/NumberTheory/NumberField/TateGlobal/Coordinates.lean
python3 build_ladder.py --edit FLTForHuman/NumberTheory/NumberField/TateGlobal.lean

# the frontier view of the node (a leaf: 1 node / 2,645 S_ lines)
python3 frontier.py --target NumberField.TateGlobal.continuous_ideleNorm --rank-by silo --ready --top 0
```

The checker wiring convention (the `Theorems/` wrapper and the `S_` file to `SOURCES`;
the façade to `PORT_FILES`; both last) is in every work order and in the friction log.

## 9. Residuals

* The 11 port-`private` `ValuationOrd` helpers in `TateGlobal/Ideles.lean` stay private
  (§2). If a later family order needs one directly, it is a priced hub edit then.
* `continuous_ideleNorm_det` is planned as an optional +1 (§4). It is in the
  Deligne–Serre closure and its own `Theorems/` wrapper exists, so its absence is a
  deliberate scope choice, not an oversight.
* The eight siblings' engines: this plan homes the shared `normQ` block; the siblings'
  *other* blocks (4,314 / 2,885 / 513 once-lines) are untouched and unmeasured beyond
  §3.
* `port_advise`'s four suspect substitutions (`SUnits`, `archBox`, `box`, `DeepUnits`)
  are the known `Type`-shaped parser artifact; none is needed for the 65 lines.

## 10. Landing record

| | |
|---|---|
| engine | `FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiC3.lean` — 121 lines, 6 public declarations, tier 3, unlisted |
| façade | `FLTForHuman/NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean` — 42 lines, 2 headlines, listed |
| checker | **9542 identical / 0 mismatched / 0 missing** / 38 own-proof exempted (was 9540 / 0 / 0 / 38) |
| axioms | both headlines `[propext, Classical.choice, Quot.sound]` |
| build | engine and façade tier 1 green; milestone `lake build` green (9549 jobs) |
| mutation test | `_det` statement extended by `∧ True` compiles → 9541 / 1 mismatched, reverted |
| register | `spec/UNWIRED-PUBLIC.md` regenerated: 81 modules / 1987 public / 1699 with a pin counterpart; all 6 engine entries carry their pin line |
| existing modules edited | **none** — no promotion, no hub edit, no wave |

**Proof adaptations (pin → `v4.34.0`), statements verbatim.**

1. `continuous_normQ`: the pin's `Units.continuous_val.comp continuous_fst` loses the
   `TopologicalSpace` instance, because `InfiniteAdeleRing` is a non-reducible `def` and
   its `instTopologicalSpaceInfiniteAdeleRing` is keyed on the folded head, which the
   elaborator unfolds. Writing `Units.continuous_val (M := InfiniteAdeleRing F) |>.comp
   continuous_fst` pins the base monoid and restores it. Recorded above the declaration in
   the engine.
2. The façade imports `Mathlib.Topology.Algebra.Group.Matrix` for
   `Matrix.GeneralLinearGroup.continuous_det`, which `AutomorphicForm/Adelic/Basic.lean`
   does not transitively bring in.

Both are proof/import adaptations; the two checked statements are the pin wrappers'
verbatim. The 8 `normQ` siblings remain unported: they should import
`NumberField.TateGlobal.FujisakiC3`, not copy it.
