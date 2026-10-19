# WORKORDER-SC2 — the weighted-Petersson pairing (landed)

Manager's round for the ready node
`AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain`
(node 6896) — the adelic weighted Petersson pairing: covariance under the right regular action,
non-degeneracy on `R'`, and packaging as a genuine sesquilinear form. This file records the
scoping and the defs+ ground, which is landed; **the proof-body wave is not yet ordered** (§5).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

## 1. The node and its silo

Not a leaf: cites 6, cited by 11, 12 theorems below. The pin `S_` file is 1,036 lines, **1 public
+ 70 private**; the headline's same-file closure is **74 helpers ≈ 933 lines**. There is no
sibling duplication — `port_advise` reads 0 duplicate copies, 0 substitutions, **1,004 net new
lines / 77 declaration groups**. The only multi-declaration block is 60 lines / 4 decls in the
same file (`exists_norm_eq`, `exists_norm_pow_mult_eq`, `mono`, `slab`).

## 2. Defs dependencies (§4(a))

| dependency | status before this round |
|---|---|
| `Definitions/Def_AutomorphicForm_PeterssonIntegral` | **absent** — 22 lines, one `def` (`peterssonIntegral`) |
| `Definitions/Def_AutomorphicForm_ProductionPinsGeneral` | homed at `AutomorphicForm/Adelic/ProductionPinsGeneral.lean` |
| `AutomorphicForm.ideleNorm_det_globalPoints` (premise, 170 pin citers) | **`private` only**, in the slab engine |
| `NumberField.TateGlobal.continuous_ideleNorm_det` | present |
| `NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc` | present |
| `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one` | present (`AdelicHaar/AdelicModulus.lean`) |
| `NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar` | present |
| `AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre` | present (WORKORDER-SC1) |

## 3. Readiness caveat

The frontier calls the node ready, but premise `ideleNorm_det_globalPoints` was importable
nowhere: the port held it only as the `private` prelude helper of `Siegel/SlabCovering.lean:701`,
and the frontier's name test counts that copy. This is the §9 last-name blindness in its worse
form (matching a `private` declaration), and it is why the node was not schedulable before this
round.

## 4. The manager's round (landed)

Two new leaf modules, plus one edit to the slab engine:

| module | what | pin |
|---|---|---|
| `AutomorphicForm/Adelic/PeterssonIntegral.lean` | `AutomorphicForm.peterssonIntegral`, homed whole | `Definitions/Def_AutomorphicForm_PeterssonIntegral.lean` (22 lines) |
| `AutomorphicForm/Adelic/IdeleNormDet.lean` | `AutomorphicForm.ideleNorm_det_globalPoints`, public node | `Theorems/Thm_AutomorphicForm_ideleNorm_det_globalPoints.lean` + its `S_` file (27 lines) |

Neither went into a hub: `AutomorphicForm/Adelic/Basic.lean` (which owns `globalPoints`) prices at
a **95-module / ~365 s** cascade, so each pin node got its own leaf instead (0 dependents).
`Siegel/SlabCovering.lean` dropped its 13-line `private` copy and now imports
`AutomorphicForm/Adelic/IdeleNormDet.lean`; its cascade is **1 module / 68 lines / ~14 s**
(`SlabCoveringTheorems.lean`), built green. The engine's one usesite
(`ideleNorm_det_globalPoints_mul_mul_centralScalar`) resolves to the imported public node
unchanged.

| check | result |
|---|---|
| tier-0 loops on both new modules | exit 0, **0 warnings** |
| tier-1 | new modules 3.2 s; engine + façade 2.9 s |
| checker | 9695 → **9697** identical — delta **+2**, exactly the def and the promoted node; 0 mismatched, 0 missing |
| `#print axioms` on both | `[propext, Classical.choice, Quot.sound]` |
| `unwired_register.py --check` | current after regen (`SlabCovering.lean` 1,130 → 1,119 lines; `TateGlobal/Defs.lean` importers 6 → 8) |
| forbidden-token sweep | none |

Wiring: `Definitions/Def_AutomorphicForm_PeterssonIntegral.lean`,
`Theorems/Thm_AutomorphicForm_ideleNorm_det_globalPoints.lean` and its `S_` file appended last to
`SOURCES`; the two new modules appended last to `PORT_FILES`.

## 5. The wave order (worker: the engine)

After this round the node is genuinely schedulable. The manager's half is landed (§4); this section
is the order for the proof body.

**Deliverable.** One new module, `FLTForHuman/AutomorphicForm/Adelic/PeterssonSlabPairing.lean`,
in the pin's namespace `AutomorphicForm.PeterssonSlabPairing`. Nothing else is created or edited; no
checker run, no register edit, no wiring (all the manager's).

The pin `S_` file splits into three pieces, and the module transcribes all of them:

| piece | pin lines | port treatment |
|---|---|---|
| `namespace FundamentalDomainSlab` (sections `FDAction`, `Group`, `Positivity`, `Pairing`, `Spans`, `Forms`) | 24–375 | the generic measure-theory prelude (`setLIntegral_fd_le_of_cover`, `setIntegral_mul_right_eq_of_isFundamentalDomain`, `trSpan`, `rt`, `exists_sesqForm_eq_on`, …) — write **once**, `private`, at the pin's names |
| `namespace AutomorphicForm` / `namespace PeterssonSlabPairing` | 377–974 | the adelic vocabulary (`dn`, `slab`, `μH`, `Γp`, `pairFn`, `CoveredBy`, `cc`, and their 40-odd lemmas) `private`, and the engine **`main` public** |
| `solution` | 980–1036 | the headline: state it verbatim from the pin `Theorems/` wrapper, proved by `main` with the SC1 covering supplied (below) |

`main` (pin line 844) is public and states the pin's `main` verbatim. It takes the SC1 covering as
its final argument
(`fun a b ha => AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre F c u d₁ d₂ T hd hcov a b ha`),
and the module states the headline from the pin `Theorems/` wrapper by supplying exactly that
covering — as the pin's `solution` does. This is why the module imports the SC1 façade
(`Siegel/SlabCoveringTheorems.lean`) and is **listed**: the checker then verifies both public
declarations, the headline against the wrapper and `main` against the pin's private `main` through
the dotted fallback. (The 92-line separate tier-1 façade this order first described was merged back
in on review; one module is the natural size here.)

**Sources.** Statements from
`https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain.lean`
(for the worker: only `main`'s statement is needed from it, but read it to confirm the extra
covering argument); proofs from
`https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain.lean`.
Local clone at `~/proj/fermats-last-theorem`.

**Transcription rules.**

* Rename the pin's mangled chapter (`P2MW.S_<stem>`, and the inner `FundamentalDomainSlab`) by
  `AutomorphicForm.PeterssonSlabPairing`; keep every declaration name verbatim. Proofs are
  transcribed and adapted, never restated; **stop and report** if a statement must change.
* Reuse, do not re-prove: `NumberField.TateGlobal.exists_norm_pow_mult_eq` (public in
  `NumberTheory/NumberField/TateGlobal/ArchNorm.lean`) — the pin's copy has `r` **implicit**, so
  `exists_norm_pow_mult_eq v hr` call sites become `exists_norm_pow_mult_eq v r hr`.
* `exists_norm_eq` is pin-`private` with no consumer: re-derive it `private` here, do not promote.
* The already-homed definitions are stated, not re-derived: `peterssonIntegral`
  (`AutomorphicForm/Adelic/PeterssonIntegral.lean`), `SmoothCuspRealizationAt`,
  `IsGenuineCuspRealizationAt`, `productionPinsOf`
  (`AutomorphicForm/Adelic/ProductionPinsGeneral.lean`), `ideleNorm_det_globalPoints`
  (`AutomorphicForm/Adelic/IdeleNormDet.lean`), `ideleNorm`, `globalPoints`, `centreCutSiegelSet`,
  `CoversModCentre`.
* Apply the `v4.34.0` drift checklist as it appears (`mem_setOf_eq` → `mem_ofPred_eq`,
  `ite_eq_left`/`ite_eq_right`, `Set.mem_iUnion`, …); drop the pin's `attribute [-instance]`/
  `attribute [-simp]` preludes if unused; never transcribe `set_option maxHeartbeats`.
* **Hub prohibition.** A helper stays `private` here and is reported; never promote, rename, or edit
  an existing module. If a promotion is genuinely required, **stop and report** the declaration, the
  intended host and the `build_ladder.py --edit` price.
* `-- pin: <name> (S_<stem>.lean:<line>)` on every **public** declaration (`main`); optional on the
  private prelude.

**Named risks and stop conditions.** The `FundamentalDomainSlab` generic prelude is the bulk of the
file (≈350 lines) and is stated over abstract `Group`/`MulAction`/measure hypotheses — the risk is
instance/`SMulInvariantMeasure` inference, diagnosed at the low cap. Then `main` (≈130 lines) and the
`exists_sesqForm_eq_on` span construction (≈50 lines). `exists_finset_shell_decomposition`-style
blow-ups did not occur in the sibling SC1 engine. **Stop and report** on: a statement change; an
import inversion; a required promotion; or a premise outside the `S_` file that is not one of the
homed items above.

**Build discipline (copy in, verbatim).**

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap
> is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the low
> cap is what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, only after the user agrees to it, and never on
> the agent's own initiative.

Concretely: tier-0 loop until `PeterssonSlabPairing.lean` is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Adelic.PeterssonSlabPairing`.
No bare `lake build`, no façade.

**Verification (the worker's, before stopping).**

| check | expected |
|---|---|
| tier-0 loop | exit 0, **0 warnings**, no forbidden token |
| tier-1 build | green; jobs and wall/user/sys time |
| `main` public at `AutomorphicForm.PeterssonSlabPairing.main` | statement equal to the pin `S_` file's `main` (extra covering argument included); byte-compare with the checker's own parser |
| `port_advise.py` + `port_plan.py` on the node | 77 declaration groups, 1,004 once-cost, 0 substitutions; the 74 same-file helpers present once each; none invented |
| `unwired_register.py --check` | report only (do **not** rewrite it) |

No checker run, no register edit, no wiring.

**Report shape.** Module and line counts; public vs `private`; tier-0 and tier-1 times; the `main`
byte-compare; the `ArchNorm` call-site adaptation; risks that bit; any statement change (there must
be none); any promotion stopped on; `git status` showing only the one new file.

**The manager's half (not this order; §4 already did the defs+).** The tier-1 façade stating the pin
`Theorems/` wrapper and supplying the SC1 covering; the checker wiring (wrapper + `S_` file appended
last to `SOURCES`, façade to `PORT_FILES`); the register refresh for the tier-3 engine; the
`identical` delta reconciled to +1.

## 6. Results as landed

Worker (§5 engine), then manager review and wire. Checker `9697 → 9699` (**delta +2**: the headline,
plus `main` itself once the module was listed; `promoted` 670 → 671), 0 mismatched / 0 missing.

| module | lines | public | private | tier-0 (wall/user/sys) | tier-1 |
|---|---:|---:|---:|---|---|
| `Adelic/PeterssonSlabPairing.lean` (listed, tier 1) | 1,066 | 2 (`main`, the headline) | 76 | exit 0, 0 warnings (8.0/11.0/2.1 s) | 7.6 s build |

The worker's `main` was re-checked byte-equal to the pin `S_` file's `main` (raw and normalized)
with the checker's own parser, the covering hypothesis included. The private `exists_norm_pow_mult_eq`
is dropped in favour of the public `ArchNorm` lemma; `exists_norm_eq` is re-derived `private`; every
other helper is present once. `port_advise`/`port_plan` parity: 77 groups, 1,004 once-cost, 0
substitutions.

**Adaptations (all proof-local; no statement changed, no promotion).** `MemLp` is no longer a
structure in mathlib `v4.34.0` (`def … := eLpNorm f p μ < ∞`), so `hf.2`/`hmem.1` became
`memLp_iff`/`hmem.aestronglyMeasurable` rewrites; the reusable premise is the port's
`distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one_impl`; `unpack` needed an explicit
`LsXiMemberAt … .Z` annotation because the port's `R.smoothCusp.1.1` elaborates to
`IsAutomorphicFnAt`; the pin's `haveI`s became `have` (the `linter.style.haveILetI` fix, not a
suppression); the pin's `attribute [-instance]`/`[-simp]` preludes are dropped.

**Review: the façade was merged back in.** The order's first cut put the headline in a separate
92-line tier-1 façade, which is disproportionate; on review it was appended to
`PeterssonSlabPairing.lean` and the façade file deleted. The module is now **listed**, so the checker
verifies both public declarations: the headline against the wrapper (+1) and `main` against the pin's
private `main` through the dotted fallback (+1, the `promoted` count moving 670 → 671). The module
leaves tier 3, so `spec/UNWIRED-PUBLIC.md` returns to 92 modules / 2,344 public / 2,056 with a pin
original. Wiring: the wrapper and its `S_` file appended last to `SOURCES`;
`FLTForHuman/AutomorphicForm/Adelic/PeterssonSlabPairing.lean` appended last to `PORT_FILES`.
`#print axioms` on the headline and on `main`: `[propext, Classical.choice, Quot.sound]`.

**Step-6 re-read (successors).** The node has left the ready shelf (it was the head at 1,036 silo
lines). The shelf still reads 91 candidates; the new head is
`EisensteinGeneral.LocalRam.integral_twisted_smooth_eq` (864), then
`AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule` (823)
and `AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction` (697).

Files changed: `FLTForHuman/AutomorphicForm/Adelic/PeterssonSlabPairing.lean`,
`spec/old_check_stmts.py`, `spec/UNWIRED-PUBLIC.md`.
