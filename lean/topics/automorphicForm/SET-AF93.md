# SET-AF93 — the weight-one lift's adelic properties

**Status: LANDED (2026-11-20).** The cut is the four `weightOneLift` rows that SET-AF92's
landing readied, **4 rows / 4,494 silo**, into five new modules (one shared engine + four rows).
The fifth row of that family — the central scalar — is **deferred**: its statement needs
`DirichletCharacter.dirichletIdeleChar`, which the port declares only in a module that does not
build (FR-0244). No definition gate for the four cut rows (every `Definitions/` import is ported).

| # | order | rows | silo | module | decls (pub/priv) |
|---|---|---|---:|---|---|
| A | the adelic bookkeeping of the lift (engine) | — | 612 once-cost | `LanglandsTunnell/WeightOneLiftAdelic.lean` (new) | 52 (52/0) |
| B | the lift is cuspidal | 1 | 1,831 | `LanglandsTunnell/WeightOneLiftCuspidal.lean` (new) | 47 (1/46) |
| C | the lift is a Hecke-coset eigenfunction | 1 | 1,753 | `LanglandsTunnell/WeightOneLiftHeckeEigen.lean` (new) | 118 (1/117) |
| D | the lift is `K_f`-smooth; its equivariance | 2 | 438 + 472 | `LanglandsTunnell/WeightOneLiftKfSmooth.lean`, `LanglandsTunnell/WeightOneLiftGlobalPoints.lean` (new) | 1 + 1 |
| — | (deferred) the central character | 1 | 1,134 | — | the definition gate |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af93_read.json
```

| figure | before (AF92 landing) | after this set's scaffolds |
|---|---:|---:|
| `needed [F terminal]` | 456 / 222,580 | **452 / 218,086** |
| ready rows | 16 / 7,921 | **16 / 6,902** |
| leaves | 74 / 21,398 | 74 / 21,398 |
| withheld (FR-0044 guard) | 4 | 4 |

The delta is the four cut rows exactly (−4 nodes / −4,494 lines), and the landing read equals the
scaffold read (`452 / 218,086`, ready `16 / 6,902`, leaves `74 / 21,398`, withheld 4). **Four rows become ready,
3,475 silo** — the lift's Nebentypus and q-expansion consequences, which these four properties
unlock together:

| row readied | silo |
|---|---:|
| `DihedralWeightOne.qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq` | 1,260 |
| `DihedralWeightOne.sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_slash_apply_I_mul_det` | 927 |
| `DihedralWeightOne.exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul` | 853 |
| `DihedralWeightOne.weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero` | 435 |

`--selfcheck` still reports the fifteen `ModularCurve` phi-refactor false ported markers (MD-005);
they are not AF's and do not touch this cone's rows.

## 1. The cut, and what is not cut

The five rows are one story: the adelic weight-one lift `weightOneLift (span {n}) f` of a `Γ₁(n)`
weight-one form is an automorphic form. Each pin states one property and each pin carries the
**same private prelude** (48 declarations, 1,643 duplicated lines in the pin): the real component
`ratArch` of an idele-class representative, the finite-adèle integrality of level `Γ₁(N)`, the
archimedean slash factor, and the lift's independence of the chosen decomposition.

**Not cut, and why** (every row the read carried is named):

| row | silo | why not |
|---|---:|---|
| `LanglandsTunnell.weightOneLift_centralScalar_mul` | 1,134 | **definition gate**: its statement uses `DirichletCharacter.dirichletIdeleChar`, which only `LanglandsTunnell/TateLocal/DirichletIdele.lean` mentions, and that module does not build (FR-0244). The pin's `Def_DirichletCharacter_DirichletIdeleChar` (188 lines, the `RatIdele.unitPadicAt`/`unitResidue`/`dirichletIdeleChar` block) is unported — the manager's next definition-layer touch. |
| `AutomorphicForm.integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le` | 216 | AF-subject tail; its natural home is a hub edit (`AutomorphicForm/Adelic/WhittakerPositivity.lean`) and it is the manager's, not an order. |
| `NumberField.Idele.exists_setLIntegral_indicator_ideleNorm_sq_mul_mem_Icc_eq_const` | 108 | same: one headline whose home is the hub `NumberTheory/NumberField/IdeleProductMeasure.lean`. |
| `WeierstrassCurve.*`, `GaloisRep.*`, `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction`, `ModularCurve.*` | 1,905 | the MC / AC / hecke columns' rows, not the AF subject. |

## 2. The homes and the manager's layer

| module | direction | manager's work |
|---|---|---|
| `LanglandsTunnell/WeightOneLiftAdelic.lean` | above `DihedralWeightOneLift`, `AutomorphicForm/Adelic/Basic`, `ProductionPinsCompact`, `ArchType`, `NumberTheory/AdelicLevel/{Projections,Level,IdealBall}`, `AdelicDock/LocalEmbedding` | the statements + wires; **the eleven-declaration move** out of `WeightOneBound.lean` |
| `LanglandsTunnell/WeightOneLiftCuspidal.lean` | + `AutomorphicForm/Adelic/ConstantTerm`, `WindowedSiegel/Topology`, `BorelSubgroup` | row statement; the `_impl` fold |
| `LanglandsTunnell/WeightOneLiftHeckeEigen.lean` | + `HeckeCosetSystem`, `ModularForms/Defs/HeckeOperator`, `Cusp/SmoothRealization` | row statement |
| `LanglandsTunnell/WeightOneLiftKfSmooth.lean`, `…GlobalPoints.lean` | + `RepTheory/SmoothVectors`, `RightConvStructurePreservation`, `SmoothAutomorphicFn` | the two rows, proved by the manager |

**The engine is the manager's decision, and it is a port-once, not a copy.** `port_advise` priced
the set at 47 declarations in ≥2 target files, ≈1,804 removable lines. The port already held
eleven of them **privately** in `LanglandsTunnell/WeightOneBound.lean` (the boundedness row of an
earlier set had transcribed the same prelude at the same statements). So the engine module was
created by moving those eleven up — public, unchanged, proofs included — and transcribing the
other 41 once. `WeightOneBound` now imports the engine; its own gates are unchanged (1 ok, silent).
All 52 engine declarations are **statement-identical** to their pins (0 differences on
`statement_db` hashes).

**Scaffold facts worth carrying.** The pins are flat: each is `N private declarations + 1 public
`solution`. The port therefore transcribes the private engine at the pin's names, and
`scaffold_audit` reads 1 pin public declaration (`solution`, folded onto the row) so the audit is
`complete` at the scaffold; `check_port` reads 1 `ok` (the row) for orders B/C, and **0 ok** for the
engine — a public module whose declarations all match *private* pin declarations, so the checker
has nothing to diff (FR-0242). The engine's faithfulness test is the `statement_db` diff.

Three port-side statements of the pins needed a spelling:
`isCuspidalFn_weightOneLift` is the pin's public name, and the pin's *private* lemma of the same name
(its real proof) became `…_impl`; the pin's `ratArchHom`/`ratArch` stay their own private spelling of
`LanglandsTunnell.ratArchGL2` with the pin's `ratArchGL2_eq_ratArch` bridge (so the pin's `rfl`
keeps working); and the KfSmooth row states the open subgroup as
`(levelOne …).comap (finiteAdelicGL2Subgroup K).subtype`, the port's spelling of the pin's
`.subgroupOf` (the port's own precedent, `RightConvStructurePreservation:307`).

## 3. The orders

In `lean/tmp/af93/WO.md` (untracked): A engine, B cuspidal, C Hecke, D the two rows. A is the
dependency of B/C, so its `.olean` was built before they were dispatched; the four files are
disjoint.

## 4. The gates

As SET-AF89–AF92 §5: `check_port` 0 mismatch / 0 missing, `scaffold_audit` complete, the module
silent under `lake env lean -DmaxHeartbeats=200000`, one `flock`/`timeout 110 lake build` of the
module, `#print axioms` clean, `dedup --within` and `move_dead --dry-run` clean, a heartbeat probe
pair recorded and never installed, and a consumer zone in `spec/`.

## 5. Frictions

* **FR-0244** — `LanglandsTunnell/TateLocal/DirichletIdele.lean` imports a file that does not exist
  (`FLTForHuman.HeckeCharacter.Dirichlet`), so the module does not build and the only port copy of
  `dirichletIdeleChar` is unusable. This is what defers the central-scalar row.
* **a generation slip** (no FR): the scaffold generator first emitted the engine's declarations
  `private`, which would have blocked B/C/D from importing them; caught before dispatch, fixed by
  regenerating and rebuilding the engine's `.olean`.

## 6. The landing

**Five new modules, 2,953 lines, 229 declarations, 0 `sorry`, no linter option, no hub edited
except the one move out of `WeightOneBound`.** The set consumed **4 rows / 4,494 silo** and returned
**4 rows / 3,475 silo** (the lift's Nebentypus and q-expansion family), leaving `needed` at
**452 / 218,086** — the four cut rows exactly. Checker: **56 `ok`, 0 mismatch, 0 missing, 0 own**;
`scaffold_audit` complete on all five; every row and every probed engine on
`[propext, Classical.choice, Quot.sound]`; `dedup` 2 pin-own clusters (the engine's two spellings)
and 1 (the cuspidal pin's `solution`/engine pair), 0 otherwise; `move_dead` 0/0 on all five; the
consumer zone `spec/AutomorphicFormSetAF93Consumer.lean` green.

| order | module | lines | decls (pub/priv) | checker | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| A | `WeightOneLiftAdelic.lean` | **685** | 52 (52/0) | **52 ok / 0 / 0** | clean (7 probed) | 2 pin-own | 0 / 0 | 10,000 / 5,000 |
| D1 | `WeightOneLiftKfSmooth.lean` | **79** | 1 (1/0) | **1 ok / 0 / 0** | clean | 0 | 0 / 0 | 200,000 / 100,000 |
| D2 | `WeightOneLiftGlobalPoints.lean` | **79** | 1 (1/0) | **1 ok / 0 / 0** | clean | 0 | 0 / 0 | 400,000 / 200,000 |
| B | `WeightOneLiftCuspidal.lean` | **828** | 47 (1/46) | **1 ok / 0 / 0** | clean (47 swept) | 1 pin-own | 0 / 0 | 25,000 / 12,500 |
| C | `WeightOneLiftHeckeEigen.lean` | **1,282** | 128 (1/127) | **1 ok / 0 / 0** | clean | **0** | 0 / 0 | 8,000 / 4,000 |

**B's cut is the first place a scaffold count had to fall.** The pin's own file carries 40
private declarations that nothing in it reaches — the `LanglandsTunnell.P4.I2` delta-lift
construction, the `span_243` block, and arch-lift leaves — so `move_dead` first read `40 / 472`.
They were dropped (the playbook §1 exception, not the completeness exemption): their mathematics is
the port's `DeltaLift.lean`/`WeightOneBound.lean` content, there is no consumer, and the pin's own
unreachable set is 55 (9 of the rest are shared-prelude declarations other rows consume, 6 are dead
in the pin but live in the port module because its flat `LanglandsTunnell` namespace shadows
same-named imports). The 40 are registered in [../../CARRY-FORWARD.md](../../CARRY-FORWARD.md); the
module reads `0 / 0` and `check_port`/`scaffold_audit` are blind to the cut (they see private
declarations not at all).

**C's count and one linter decision.** The pin's prelude *for this file* is 34 declarations (not the
engine's 48), so 129 row-local − `solution` = **128**; the scaffold's 118 was my miscount from the
shared-set arithmetic. The agent had silenced `linter.style.haveILetI` at file scope for the pin's
nine `haveI`/one `letI` on propositions; the project's convention is the rewrite, not the silencing
(FR-0223/FR-0235), so the manager rewrote them to `have`/`let` and dropped the option — the module is
silent with no `set_option` of its own.

**A's two deltas that the next set inherits** (both in the module header): the module needs
`AutomorphicForm/Adelic/ProductionPinsTail` (for `exists_mem_productionPinsCompact_U_mul_eq_rat`,
the body of `hasWeightOneDecomp_of_ne_bot`), and three body-level substitutions at mathlib `v4.34` —
`AdelicBox.algebraMap_mem_adicCompletionIntegers` ->
`NumberField.AdelicLevel.…` (FR-0238's rename class), `if_pos`/`dif_pos` -> `ite_eq_left`/
`dite_eq_left`, and dropping the pin's `rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]`
(`SpecialLinearGroup` is a `def` in v4.34, so the rewrite is not type-correct under `implicit`
transparency; the `change` that follows it closes the goal). The last is a new instance of the
FR-0238 class, recorded for the next module that meets `SpecialLinearGroup`.

**The engine's `dedup --within` reading is 2 clusters / 18 lines and stays**: they are the pin's own
two spellings of one lemma (generic vs `𝓞 ℚ`-specialised), both on the wire, both with consumers;
the reason is in the header.

**A stale-olean recurrence worth noting** (FR-0033): after the engine's bodies landed, the two row
modules still reported `sorryAx` because their own `.olean`s predated it; rebuilding them cleared
it. The gate sequence has to be re-run *after* the dependency's olean is refreshed, not just the
dependency's build.

