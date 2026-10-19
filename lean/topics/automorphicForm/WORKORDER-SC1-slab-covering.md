# WORKORDER-SC1 — the (central) slab-covering engine (tier 3)

Port the shared proof body behind the three `AutomorphicForm.exists_finset…slab_covering…` ready
nodes — the adelic Siegel-covering cluster of
[../../topics/PORTING-DeligneSerre.md](../../topics/PORTING-DeligneSerre.md) §2. The scoping this
order executes is `tools/deps/build/slab_covering_advise.json` (its `port_advise` output and its
`port_plan` budget); the worker re-runs both at the end for parity.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

**The manager's ground is landed** (do not re-open any of it):

* the definition layer `Def_AutomorphicForm_CentreCutSiegelSetAmple` (11 declarations) at
  `FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/CentreCutSiegelSetAmple.lean`;
* `Def_AutomorphicForm_SiegelCovering` at `…/Adelic/Siegel/Covering.lean` (owns `CoversModCentre`),
  `Def_AutomorphicForm_CentreCutSiegelSet` at `…/WindowedSiegel/CentreCutSet.lean` (owns
  `centreCutSiegelSet`), and the tier-3 `Def_NumberField_TateGlobalZeta` vocabulary at
  `FLTForHuman/NumberTheory/NumberField/TateGlobal/Defs.lean` (owns `ideleNorm`, `archUnitHom`);
* the three `Thm_NumberField_*` imports the `S_` files need;
* **two of the shared-block names are public already** at
  `FLTForHuman/NumberTheory/NumberField/TateGlobal/ArchNorm.lean`:
  `NumberField.TateGlobal.ideleNorm_archUnitHom` and
  `NumberField.TateGlobal.exists_norm_pow_mult_eq`. The first is a drop-in for the pin's slab copy
  (the two differ only in binder names); the second takes `r` **explicitly** where the pin's slab
  copy has it implicit, so its call sites need adapting (§3). Import them; do not re-prove either.

## 1. Scope

Port **once** the development the three self-contained pin `S_` files each carry in full — 6 target
files (3 `S_` + 3 `Theorems/`), 2,783 raw `S_` lines, 69 declaration groups, **1,213 net new math
lines** after dedup, **0 substitutions** (every remaining target declaration is new to the port).

| public kernel `AutomorphicForm.SiegelCovering.Engine.<name>` | pin stem `<stem>` |
|---|---|
| `exists_finset_central_slab_covering_of_coversModCentre` | `AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre` |
| `exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple` | `AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple` |
| `exists_finset_slab_covering_of_coversModCentre` | `AutomorphicForm_exists_finset_slab_covering_of_coversModCentre` |

Each node is taken whole (playbook §2.3): the whole `S_` file's proof, not only its headline.

The three files are one development written three times. The shared blocks are:

* **779 lines / 52 declarations, shared by all three files.** Write once:
  `archDetNorm_centralScalar`, `archDetNorm_centralScalar_mul'`, `archDetNorm_mul`, `archIdele`,
  `archIdele_fst`, `archIdele_inv_snd`, `archIdele_snd`, `archUnitHom_fst_of_ne`,
  `archUnitHom_fst_self`, `archUnitHom_snd`, `centralScalar_mul_comm`,
  `centralScalar_mul_mem_centreCutSiegelSet`, `det_centralScalar_sq`, `det_fst_apply`,
  `det_snd_apply`, `exists_bounds_ideleNorm_central`, `exists_bounds_ideleNorm_det`,
  `exists_centralScalar_mul_mem_archDetNorm_eq`, `exists_finset_normOne_decomposition`,
  `exists_finset_shell_decomposition`, `exists_mem_openShell`, `exists_net`, `exists_norm_eq`,
  `exists_norm_mul_self_eq`, `exists_norm_pow_mult_eq`, `exists_shell_ratio`,
  `glFin_centralScalar_mem_finiteIntegralGL2`, `glFin_centralScalar_of_snd_eq_one`,
  `globalPoints_scalar`, `ideleNorm_archUnitHom`, `ideleNorm_det_centralScalar`,
  `ideleNorm_det_eq_archDetNorm_rat`, `ideleNorm_det_eq_prod_archDetNorm_pow`,
  `ideleNorm_det_globalPoints`, `ideleNorm_det_globalPoints_mul_mul_centralScalar`,
  `ideleNorm_det_of_archDetNorm_eq`, `ideleNorm_inv`, `ideleNorm_one`, `ideleNorm_pow`,
  `isOpen_openShell`, `mem_openShell_iff`, `mul_archUnitHom_mem_shellIdeles`,
  `mul_centralScalar_mem_of_mem_shellIdeles`, `norm_eq_zpow_of_valued`,
  `norm_mul_self_mem_of_norm_pow_mult_mem`, `openShell`, `openShell_subset_shellIdeles`,
  `pointShape`, `prod_pow_mult_pos`, `shellIdeles`, `valued_det_finComponent_eq_one`,
  `valued_det_le_one`.
  Two of these (`ideleNorm_archUnitHom`, `exists_norm_pow_mult_eq`) are the landed `ArchNorm`
  lemmas: import them, leaving 50 names / ≈721 lines to write.
* **54 lines / 1 declaration, shared by the central and ample files:**
  `exists_finset_central_covering_of_point_of_stable_of_decomposition`.

The per-file tails are the three `solution` kernels and their few unique helpers. Two of them
generalise over the ample parameter and **must be one lemma each, not two copies** (playbook §5):
the ample file's `central_assembled` and
`exists_finset_central_covering_centreCut_of_point_of_stable_of_decomposition` differ from the
central file's only by the extra `κ : ℝ` binder (the slab file has its own
`e2a_assembled` / `…_of_stable_of_engine` variants and is not part of this pair).

**Explicitly not this order.** The tier-1 façade (the three `Theorems/` wrapper statements), the
checker wiring, `UNWIRED-PUBLIC.md`, the def layer above, any other ready-shelf node, and any
existing module. The manager does those after review.

## 2. Sources and deliverable

Statements come from the pin `Theorems/` wrappers; proofs from the `P2M/Sol/S_` engines:

* statements — `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_<stem>.lean`
* proofs — `https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_<stem>.lean`

for each `<stem>` of §1. The local clone at `~/proj/fermats-last-theorem` is the working copy;
`Theorems/Thm_<stem>.lean` is one `p2m_exact_reverting` line and is the authority for the
statement, never the `S_` file's `solution` spelling.

**Deliverable:** one tier-3 module

* `FLTForHuman/AutomorphicForm/Adelic/Siegel/SlabCovering.lean`

in namespace `AutomorphicForm.SiegelCovering` (the namespace of the sibling
`…/Siegel/Covering.lean`), with:

* the shared prelude of §1 written once, **`private`** at the pin's names (a private helper is not
  part of the verified surface; the checker skips it);
* the three kernels **public** at
  `AutomorphicForm.SiegelCovering.Engine.<name>` with the `Theorems/` wrapper statements, so the
  manager's façade can state the headlines and delegate;
* `-- pin: <name> (S_<stem>.lean:<line>)` above every **public** declaration (the tier-3 register
  reads it there); on the `private` prelude it is optional, for traceability only;
* a header stating the subject, the pin and the two landed reuse edges.

No other file is created or edited. The module is not wired (`PORT_FILES`) in this order.

## 3. Transcription rules, reuse, and the hub prohibition

* Replace the pin's mangled chapter (`P2MW.S_<stem>`) by `AutomorphicForm.SiegelCovering`; keep
  every declaration name verbatim. Proof bodies are transcribed and adapted, never restated.
* Reuse, do not re-prove: `NumberField.TateGlobal.ideleNorm_archUnitHom` and
  `NumberField.TateGlobal.exists_norm_pow_mult_eq` (`TateGlobal/ArchNorm.lean`). The pin's
  `exists_norm_pow_mult_eq v hr` call sites become `exists_norm_pow_mult_eq v r hr`; if a
  transcription reads better, keep a `private` adapter at the pin's `{r}` spelling delegating to
  the public lemma — an adapter stays `private` (playbook §5).
* The def layer is stated, not re-derived: `centreCutSiegelSet`, `centreCutSiegelSetAmple`,
  `CoversModCentre`, `centralScalar`, `globalPoints`, `ideleNorm`, `archUnitHom`.
* Apply the `v4.34.0` drift checklist (playbook §7) as it appears: `mem_setOf_eq` →
  `mem_ofPred_eq`, `ite_eq_left`/`ite_eq_right` for `if_pos`/`if_neg`. Do not transcribe the pin's
  `set_option maxHeartbeats`.
* **Hub prohibition.** A helper you need stays `private` here and is reported; you never promote,
  rename, or edit an existing module. If you believe a promotion is genuinely required, **stop and
  report** the declaration, the intended host and the `build_ladder.py --edit` price; the manager
  decides.

## 4. Named risks and stop conditions

Named risks, in the order they will bite: `exists_finset_shell_decomposition` (74 lines, the
largest shared helper), `exists_bounds_ideleNorm_central` (60),
`ideleNorm_det_globalPoints_mul_mul_centralScalar`, the κ-generalisation of the two central/ample
helpers, and the `AdelicGL2`/`AdelicRing` coercion seams. Diagnose at the low cap (playbook §3.5),
fix the inference, report — do not raise `maxHeartbeats`.

**Stop and report** if: a wrapper statement must change; a kernel cannot be stated without editing
an existing module or promoting a name; an import inversion appears between the three targets; or a
premise outside the three `S_` files is needed (`port_advise`/`port_plan` never walk imports).

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap
> is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the low
> cap is what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, only after the user agrees to it, and never
> on the agent's own initiative.

Concretely: tier-0 loop until `SlabCovering.lean` is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Adelic.Siegel.SlabCovering`.
No bare `lake build`, no dependent, no façade.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on `SlabCovering.lean` | exit 0, **0 warnings**, no forbidden token (`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/`maxHeartbeats`) |
| tier-1 build of the module | green; record jobs and wall/user/sys time |
| `port_advise.py` + `port_plan.py` on the three nodes | 69 declaration groups, 1,213 once-cost before the two `ArchNorm` imports, 0 substitutions; each of the 54 shared names present **once**; none invented |
| the three `Engine.*` kernels | present, public, byte-equal to their `Theorems/` wrappers under the checker's own parser |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

No checker run, no register edit, no wiring. (The checker's mutation sensitivity is its own
`--selftest`, run when the checker changes — not here.)

## 7. Report shape

Modules and line counts; public vs `private` declaration counts; tier-0 and tier-1 wall/user/sys
times; the parity table of §6; the named risks that bit and how; the exact `ArchNorm` call-site
adaptation; any statement that had to change (there must be none); any promotion you stopped on;
`git status` (only `SlabCovering.lean`).

## 8. The manager's half (not this order)

After review: the tier-1 façade stating the three `Theorems/` wrapper headlines and delegating to
the `Engine.*` kernels; the checker wiring (the three wrappers and `S_` files appended last to
`SOURCES`, the façade appended last to `PORT_FILES`); the `UNWIRED-PUBLIC.md` refresh for the
tier-3 engine; the `identical` delta reconciled to +3.

## 9. Results as landed

Worker report, then manager review and wire. Checker `9687 → 9690` (**delta +3**, exactly the three
headlines), 0 mismatched / 0 missing.

| module | lines | public | private | tier-0 (wall/user/sys) | tier-1 |
|---|---:|---:|---:|---|---|
| `Siegel/SlabCovering.lean` (worker, tier 3) | 1,129 | 3 | 59 | exit 0, 0 warnings (6.53/10.34/2.17 s) | 3,809 jobs, 6.3 s build (7.18 s wall) |
| `Siegel/SlabCoveringTheorems.lean` (manager, tier 1) | 78 | 3 | 0 | exit 0, 0 warnings (2.59 s) | 3,810 jobs, 3.1 s build |

**Parity.** All 54 shared names present **exactly once** (52 written once, 2 imported from
`ArchNorm`); no declaration name duplicated; 62 declarations in the engine. The three `Engine.*`
kernels were re-checked byte-equal to their `Theorems/` wrappers with the checker's own parser
before the façade was written (0 diff). The three headlines are stated verbatim from the wrappers
and delegate to the kernels.

**Deviation from the order (recorded).** §1 named **two** helpers that generalise over the ample
parameter; the pin actually carries **five** same-name / different-statement declarations
(`exists_centralScalar_mul_mem_archDetNorm_eq` 0.972, `mul_centralScalar_mem_of_mem_shellIdeles`
0.973, `pointShape` 0.980, `central_assembled` 0.981,
`exists_finset_central_covering_centreCut_of_point_of_stable_of_decomposition` 0.985). The worker
generalised each over the set `S` with two set-specific inputs (`hwin`, `hmul`) — and dropped the
now-unused `c u` binders of `central_assembled` — so each shared name occurs once; the `κ`-variants
are the two `…Ample` set inputs. This is visible to `port_advise` as "in the port under a different
statement" and is the intended §5 outcome, not a re-transcription. All other named risks
(`exists_finset_shell_decomposition`, `exists_bounds_ideleNorm_central`,
`ideleNorm_det_globalPoints_mul_mul_centralScalar`, the `AdelicGL2`/`AdelicRing` seams) did not
bite. Proof-only adaptations: `ite_eq_left`/`ite_eq_right`, `mem_ofPred_eq`, a deprecated
`mul_le_one₀` expanded, `globalPoints_scalar F a` → `globalPoints_scalar a`, three pin
`haveI`/`letI` spelled `have`/`let` (the `CentreCutSet` precedent), and the `ArchNorm`
call-site `r`. **No statement changed; no promotion; no existing module edited.**

**Manager's half.**

| check | result |
|---|---|
| `Siegel/SlabCoveringTheorems.lean` (tier 1) | 3 headlines, stated from the wrappers, tier-0 exit 0 / 0 warnings, tier-1 green |
| checker | **9690** identical, 0 mismatched, 0 missing, 38 own (9728 checked) |
| `#print axioms` on all three headlines | `[propext, Classical.choice, Quot.sound]` |
| forbidden-token sweep on both new files | none |
| `unwired_register.py --check` | current after regen |

Wiring: the three `Theorems/` wrappers and their three `S_` files appended last to `SOURCES`; the
façade appended last to `PORT_FILES`. The engine stays tier 3 and is registered:
`spec/UNWIRED-PUBLIC.md` 91 → 92 modules, 2,341 → 2,344 public declarations, 2,053 → 2,056 with a
pin original.

**Step-6 re-read (successors).** The three nodes have left the ready shelf. The shelf now reads
91 candidates (88 before: three left, six became ready as `F` grew); its new head is
`AutomorphicForm.exists_sesqForm_eq_peterssonIntegral_of_isGenuineCuspRealizationAt_of_isFundamentalDomain`
(1,036 silo lines, `used_by` 5 / 11), then `EisensteinGeneral.LocalRam.integral_twisted_smooth_eq`
(864) and `AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule`
(823). None is this column's own next cut by default.

Files changed by this order: `FLTForHuman/AutomorphicForm/Adelic/Siegel/SlabCovering.lean` (new),
`FLTForHuman/AutomorphicForm/Adelic/Siegel/SlabCoveringTheorems.lean` (new),
`spec/old_check_stmts.py`, `spec/UNWIRED-PUBLIC.md`.

