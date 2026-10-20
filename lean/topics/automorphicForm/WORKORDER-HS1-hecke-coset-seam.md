# WORKORDER-HS1 — the explicit Hecke coset system at a finite place (definition gate + leaf)

**Status (closed 2026-10-20): landed and reviewed green.** One gate, one set: **four modules, 94
statement-checked declarations** (45 definition-layer + 49 leaf), **one public headline**.
Measured: `spec/check_port.py --all` **1916 ok / 0 mismatch / 0 missing / 4 own / 0 kw over 51
modules** (583 exempt); tier-1 builds 1,795 + 2,164 + 2,247 jobs for the gate and 3,625 for the
leaf, 0 warnings throughout; axioms `[propext, Classical.choice, Quot.sound]`; the frontier reads
`needed 0` for the node. The pin files are transcribed **verbatim**, so the checker's verdict is on
every declaration of the gate, not only on the headline.

The row is the demand's head leaf
`HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen` — the 807-line `S_` file
(pinned `aa2d8b3`), `cites 0`, cited by **40** theorems. It is the explicit `q_v + 1`-coset
decomposition of the Hecke double coset at a finite place, in adelic form.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the per-module protocol — `spec-pin:` header, `spec/check_port.py`, no in-source
per-declaration marker.

## 1. Scope

For a number field `F` and `v ≠ 0` in `𝓞 F`, produce a uniformizer `ϖ` of the completion `F_v`
with `Valued.v ϖ = exp(-1)`, prove `finEmbed (localEmbed (diagPi ϖ)) = heckeGen v`, produce a
section `sec` of `𝓞 F → 𝓞 F ⧸ v.asIdeal`, and prove `IsHeckeCosetSystem` for the family
`i ↦ finEmbed (localEmbed (i.elim localRepInf (localRepSome (sec c))))` at the level group
`levelOne ⊓ finiteAdelicGL2Subgroup`.

| block | pin lines | the mathematics | port |
|---|---|---|---|
| `Def_LocalLanglands_LocalHeckeInstance` | 78 | the integral subgroup `LocalGL2.integralSubgroup R K`, the transpose `transposeGL`, `det_map_algebraMap` | **new module** (gate) |
| `Def_LocalLanglands_IntegralSubgroupOpen` | 106 | entrywise integrality and openness of `GL₂(ℤ_[p])` in `GL₂(ℚ_[p])` | **new module** (gate) |
| `Def_LocalLanglands_HeckeCosetLocal` | 400 | the local double coset: `unipotentR`/`weylR`/`diagPi`, the representatives `localRepSome`/`localRepInf`, the covering `exists_rep_of_mem_heckeMulSet`, finiteness `finite_image_mul_diagPi`, the operator `localHeckeOperator` | **new module** (gate) |
| `Aux4SevenTN` chapter of the `S_` file | 731 | the integral model of `F_v` (`piLoc`, `toLocInt`, `resMap`, `residueEquiv`), the local representatives `genHeckeRep`, the adelic section `adicToAdelic`, the membership bookkeeping that identifies `(productionPinsGeneral F).U` with the level-one group at finite places | **engine**, public |
| the last four lemmas + `solution` | 56 | the section `Quotient.out`, `family_eq`, `heckeGen_eq_adicToAdelic`, the headline | **headline** |

**Not this set:** the sibling silos of the same family (§6); the 40 consumers; any edit to an
existing module.

## 2. Measurement

`tools/deps/port_advise.py --target … --json build/heckeSeam_advise.json` on the leaf:
**50 declarations, 807 raw / 786 declaration lines, 25 boilerplate, 49 groups, 0 duplicates, 0
substitutions** — "none: every target declaration is new to the port". The definition gate:
**45 declarations, 584 pin lines, 0 real substitutions** — the tool's five "type-only `def`
matches" (`diagPi` ↔ `gl2Weyl`, `unipotentR` ↔ `unipotentGL2`, `localRepInf` ↔ `gl2Weyl`,
`integralSubgroup` ↔ `rowIsometrySubgroup`, `weylInt` ↔ `gl2Weyl`) are the parser's suspect tier
and **wrong**: those are different objects with similar-shaped types. They are recorded here so a
later `port_advise` run does not read them as duplicates.

The pin's imports were walked by hand (§4(a) of the column note): the leaf imports
`Def_LocalLanglands_{HeckeCosetSystem,HeckeCosetLocal}`, `Def_AdelicDock_LocalEmbedding`,
`Def_AutomorphicForm_{SmoothAutomorphicFnAt,ProductionPinsGeneral}`. The first, fourth and fifth are
homed (`RepTheory/LocalLanglands/HeckeCosetSystem.lean`, `AutomorphicForm/Adelic/ProductionPinsGeneral.lean`,
`AutomorphicForm/Adelic/SmoothAutomorphicFnAt.lean`), the second is the gate, and the third
(`localEmbed`, `finEmbed`, `localMat`, `splice`) is `NumberTheory/AdelicDock/LocalEmbedding.lean`.
The gate's own closure is `Def_AbstractHeckeOperator` (homed, `RepTheory/AbstractHeckeOperator.lean`)
and mathlib — nothing else is missing.

## 3. The definition gate (three modules, whole)

The gate is homed whole per playbook §2.3, at the local-Langlands theory home:

| module | pin source | declarations |
|---|---|---:|
| `RepTheory/LocalLanglands/IntegralSubgroup.lean` | `Def_LocalLanglands_LocalHeckeInstance` | 10 |
| `RepTheory/LocalLanglands/IntegralSubgroupOpen.lean` | `Def_LocalLanglands_IntegralSubgroupOpen` | 4 |
| `RepTheory/LocalLanglands/HeckeCosetLocal.lean` | `Def_LocalLanglands_HeckeCosetLocal` | 31 |

All three are **public** (they are `Definitions/` material: the math is the API), each carries its
own `spec-pin:` header, and all 45 declarations verify by **exact name and statement hash** —
transcription, not promotion. The pin namespaces `LocalGL2` and `FLT.SpectralSide` are kept.

Drift, all statement-preserving and all in the import/`rfl` layer:

* `import Mathlib` → specific mathlib modules; `Def_*` imports → the port's counterparts;
* `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (two sites), `zero_le'` → `zero_le` (one site);
* `Def_LocalLanglands_{HeckePair,CartanDecomposition}` are imported by the pin's
  `LocalHeckeInstance` but none of their declarations is used, so neither is imported;
* the pin's closing `example : Fintype.card (Option (Fin 2)) = 2 + 1` is not a declaration and is
  not transcribed.

## 4. The leaf: verbatim, engine public

The `S_` file's 48 declarations are `private` in the pin. The port makes them **public**, because
the `_principalLevel` sibling silo re-proves this whole engine (the two `S_` files differ by 171
diff lines out of ~800 shared) — the engine is written once and will be imported there (§6). That
is the same choice the Frobenius-subfield engine took (WORKORDER-SU1), and it is why the module's
checker surface is 49 rather than 1.

The transcription is mechanical: the pin's `namespace P2MW.S_…` wrapper is dropped, the chapter
namespace `Aux4SevenTN` is kept, and the pin's `solution` is renamed to the wrapper's name
`HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen` (its statement text is the
wrapper's, verbatim). Four proof-level adaptations were needed, all because mathlib `v4.34.0`'s
`adicCompletion` is a one-field structure whose `ext` now descends into `toCompletion`:

* the `hinj` step of `mem_integralSubgroup_of_entries_mem` (`Ext i j` goal is the
  `.toCompletion` image of the algebraMap equality): a `change` to the algebraMap form, then `rw`;
* the two `show`s in `adicToAdelic_diagPi` (same descent): the pattern carries `.toCompletion`;
* one file-level `set_option linter.style.haveILetI false`, as the pin's `S_` files set it
  file-wide and 192 port modules do — the `haveI` walls are the pin's instance plumbing;
* the pin's `attribute [-ext] adicCompletion.ext` is **not** copied: the transcription elaborates
  without it (the alternative — disabling the ext lemma to keep the old `ext` shape — would have
  hidden the change rather than adapted to it).

The headline's statement is the `Theorems/` wrapper verbatim, including the `∃ hϖ0` binder and the
`Option`-indexed family; the checker's `ok` on it is the statement contract.

## 5. Build discipline (verbatim)

```
tier 0  edit loop    timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>
tier 1  module done  flock .lake/flt_build.lock timeout 300 lake build <module>
tier 2  wave         none — no existing module was edited
tier 3  milestone    no whole-tree build without the user's permission
```

The three gate modules build in chain (each new module's `.olean` is needed by the next one's edit
loop), so the loop was run module by module: build, then elaborate the next.

## 6. Successors this landing unblocks

* **The twin, now cheap.** `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen_principalLevel`
  (908 pin lines) shares ~800 lines with this leaf and differs by 171 diff lines: the two level
  abbreviations `l1U`/`prinU`, a `weyl` block (`finComponent_glFin_weyl`, `finComponent_glFin_conj_weyl`
  and their consumers), and the `principalLevel` conjunct of its `solution`. With the engine public
  it is a ~170-line module; it has **one** project citer, so it is the cheap tail of the family.
* **The rest of the seam family** — `HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem` (39,
  ~178 citers as a co-input), `exists_isHeckeCosetSystem_integralSubgroup_diagPi` (35),
  `IsHeckeCosetSystem.exists_bijective_forall_exists_mul_eq_mul_of_mem` (72),
  `IsHeckeCosetSystem.sum_apply_mul_prod_ofFn_eq_of_mem` (111),
  `exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq` (137), and
  `exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd` (957).
* **Ready now**: `AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup`
  (229) — the first of the 40 consumers to reach the ready shelf.

## 7. Verification (measured on the tree this set leaves)

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/RepTheory/LocalLanglands/IntegralSubgroup.lean    # 10 ok
python3 spec/check_port.py --force FLTForHuman/RepTheory/LocalLanglands/IntegralSubgroupOpen.lean #  4 ok
python3 spec/check_port.py --force FLTForHuman/RepTheory/LocalLanglands/HeckeCosetLocal.lean      # 31 ok
python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/HeckeCosetSeam.lean         # 49 ok
python3 spec/check_port.py --all
#   1916 ok, 0 mismatch, 0 missing, 4 own, 0 kw — 51 module(s), 583 exempt (PORT_FILES)
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Adelic.HeckeCosetSeam
#   ✔ 3,625 jobs (5.9s)
python3 spec/unwired_register.py --check      # register is current
```

plus the `#print axioms` probe on the headline, the `grep` sweep over the four modules (no
`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/heartbeat override) and `git status`.

## 8. Report shape

The gate is transcribed whole, statement by statement (45 `ok`); the leaf's engine is public
because a sibling imports it (49 `ok`); the four proof adaptations are the `adicCompletion.toCompletion`
descent, recorded rather than suppressed; the headline is the wrapper verbatim; nothing is
registered, and no existing module was edited.

## 9. Addendum (2026-10-20): the 39-line coset-sum node, appended to the coset-system module

The last `HeckeIntegralSeam.` row in the D-S demand is
`HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem` — `frontier.py --ds --list` shows the
namespace at `1 / 39` lines, and `--ds --include-leaves` prices the node at silo 39, `used_by` 6 cone
/ 33 project, `cites 0`: a graph **leaf**, which is why `--ready` never showed it.

**It fits an existing module, and is housed there.** `RepTheory/LocalLanglands/HeckeCosetSystem.lean`
is the home of `IsHeckeCosetSystem` and its coset lemmas (disjoint union, `reps_injective`,
`canonical_isHeckeCosetSystem`, the measure computation); the coset-sum independence is that
structure's *well-definedness half* — the sum `∑ i, φ (g * reps i)` of a right-`U`-invariant `φ` is
a property of the double coset, not of the representatives. So the lemma is **appended** to that
module rather than given a module of its own.

**Priced first, as a hub edit.** `build_ladder.py --edit` on the host: **34 dependent modules /
16,230 lines, ≈197 s** (`SmoothRealization` and the new `HeckeCosetSeam` both import it). One wave
build of all 34, green.

**The append is also a handoff.** The module was in the frozen registry; it now carries
`spec-pin:` lines (its own `Def_` source for the 14 existing declarations, the coset-sum wrapper for
the new one) and its `PORT_FILES` entry is deleted — so the append *gains* 14 checked declarations
as well as the new one.

Transcription notes:

* the pin's two declarations (`P1RepIndep.heckeCosetSum_eq_of_isHeckeCosetSystem_impl` and its
  `solution` alias) are one public theorem, the helper inlined (`p2m` plumbing);
* the pin's binder text is `HeckeIntegralSeam.IsHeckeCosetSystem` (fully qualified). Inside
  `namespace HeckeIntegralSeam` the port first wrote the bare name and the checker reported a
  `MISMATCH` — `norm` erases `ModularCurve.`/`AlgebraicCurve.`/`kw_` prefixes, not this one. The
  fix is the pin's own text, which is what the statement contract asks for;
* imports added: `Mathlib.Basic.Complex.Basic` (`ℂ` in the statement) and
  `Mathlib.Algebra.BigOperators.Group.Finset.Basic` (`∑`, `Fintype.sum_bijective`).

## 10. Addendum (2026-10-20): the `_principalLevel` sibling, ported for the dedup

The near twin
`HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen_principalLevel` (908 pin lines, 56
declarations) is **not** in the D-S cone, but it re-proves the same 807-line engine, so it is
ported now rather than left to re-derive it. Landed as
`AutomorphicForm/Adelic/HeckeCosetSeamPrincipal.lean`, **295 lines, 11 statement-checked
declarations**.

**The substitution is explicit.** Of the twin's 56 declarations, **45 are imported from
`HeckeCosetSeam.lean`**: 42 byte-identical (the whole `Aux4SevenTN` engine, the generic coset-system
lemmas and the four `solution` glue lemmas), and the two `l1U`-spelled re-statements of
`mem_generalU_of_components` / `components_of_mem_generalU` — the parent's versions are stated for
`(productionPinsGeneral F).U N`, which is *by definition* `levelOne ⊓ finiteAdelicGL2Subgroup`
(`productionPinsGeneralOf_U`), so the sibling's `l1U` spelling is the same group and the `l1U`
abbreviation itself is not needed. **11 are restated** because their statements genuinely differ:
the `prinU` abbreviation, the five Weyl-conjugacy lemmas (`finComponent_glFin_weyl`,
`finComponent_glFin_conj_weyl`, `glArch_conj_weyl`, `mem_prinU_of_components`,
`components_of_mem_prinU`), four `prinU`-flavoured versions (`adicToAdelic_mem_generalU`,
`heckeGen_inv_mul_docked_mem_U`, `isHeckeCosetSystem_docked`,
`exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd_dev`) and the headline.

**Two homing decisions.**

* **The namespace.** The pin's chapter namespace `Aux4SevenTN` belongs to the parent module (the
  engine is public there), so the variants here live in `Aux4SevenTNPrincipal`; the checker matches
  on the last name and the statement hash, so nothing is lost.
* **The headline sits at the root.** The first draft put it inside `Aux4SevenTNPrincipal`, which
  made its full name `Aux4SevenTNPrincipal.HeckeIntegralSeam.…` — the checker still matched it, but
  a consumer would not find it. It is stated after `end Aux4SevenTNPrincipal`, at the wrapper's
  name, exactly as in the parent.

**Verification.** `spec/check_port.py --force` on the module: **11 ok / 0 mismatch / 0 missing**,
each against its own pin line. Tier-1 build 3,627 jobs, 4.9 s, no warnings; axioms
`[propext, Classical.choice, Quot.sound]`. The whole wired surface goes **1931 → 1942 ok** over
**53** modules. `frontier.py` on the twin now reads `needed 0`; because the row is outside the D-S
closure, the `--ds` readings do not move, but the port's `F` grows by the node (1,005 → 1,006).

## 11. Addendum (2026-10-20): `…_localRepSome_heckeGen_of_dvd` — scoped, then **deferred**

The family's last large sibling,
`HeckeIntegralSeam.exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd` (957 pin lines, 55
declarations), was scoped and a draft was generated; it is **deferred**, not landed.

**It does not drag in modules — that part is clean.** Its statement and the new block's proofs use
only identifiers already in `HeckeCosetSeam.lean`'s **105-module import closure** (`unipotentGL2` and
its `coe`/`add`/`zero` from `Adelic/ConstantTerm`, `AdelicLevel.idealBound{,_of_ne_bot}` from
`AdelicLevel/IdealBall`, `localLevelOne` from `AdelicLevel/Level`, `Valuation.map_one_add_of_lt`
from mathlib). The wrapper's five extra `Definitions/` imports (`WhittakerCoefficient`, `AdelicLsXi`,
`AdelicBox`, `StandardLocalConstantsAt`, `IdeleClassVocab`) are **inert** — zero occurrences in the
`S_` file — so no definition gate is owed. `port_advise` on the file: **39 substitutions (589 lines),
residual 13 declarations / ≈320 lines** (the level-bound trio, the unipotent quartet, the
`localLevelOne` bridging pair, `exists_localRepSome_inv_mul_mem` 153, `eq_of_localRepSome_inv_mul_mem`
8, `isHeckeCosetSystem_docked_dvd` 67, the headline 26). The three `'`-suffixed glue lemmas are
byte-identical to the parent's and would be imported.

**Why deferred: it is proof development, not transcription.**

* the 153-line covering lemma `exists_localRepSome_inv_mul_mem` carries
  `set_option maxHeartbeats 3200000 in` in the pin — the *only* heartbeat raise in the family. The
  column's discipline (playbook §3.5/§5) says such a declaration has an instance-inference defect to
  diagnose, never a cap to transcribe;
* its matrix-entry computations do not close under mathlib `v4.34.0`: in the draft, the
  `simp [...]; try ring` steps of the `hprod`/`hprod'` blocks leave unsolved goals and two
  `linear_combination`/application mismatches (`hbδ`, `hab` shapes), i.e. several of the ~40
  entrywise steps need reworking, not retyping.

That is a diagnose-and-fix task with a real risk of touching the engine's matrix conventions; it is
worth its own order rather than the tail of this one. The generated draft (379 lines, compiling up to
the covering lemma) is parked at `lean/tmp/HeckeCosetSeamDvd.draft.lean` (git-ignored) as the
starting point. Everything else landed here stands: the tree is unchanged at **1942 ok / 53 modules**.

**Successor order shape.** One module `AutomorphicForm/Adelic/HeckeCosetSeamDvd.lean`, namespace
`TorusStripC3a` (the pin's `P2M.TorusStripC3a` minus the `P2M.` plumbing prefix), headline at the
root, `import FLTForHuman.AutomorphicForm.Adelic.HeckeCosetSeam` only; 13 restated declarations, the
`'`-glue imported; the covering lemma's heartbeat defect to diagnose first (trace
`synthInstance`/`simp` on that declaration at the 200k cap), and the entrywise matrix steps to redo
with `ring_nf`/`field_simp`/`linear_combination` as the goals demand.
