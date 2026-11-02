# WORKORDER-AF8 — the cusp-subrepresentation bridge (composition set)

**Issued 2026-11-02, dispatched after the manager's part landed.** Scope: [SET-AF8.md](SET-AF8.md)
§1 for why this set is a *composition*, not a transcription. **Read §0 first: it is the
manager's landed state and it supersedes SET-AF8's Appendix B count.**

**Audience.** A fresh coding session. Wire: the per-module protocol — the module carries its own
`spec-pin:` header, `spec/check_port.py` owns its statements, no in-source per-declaration marker.
Pin clone `/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`. Port mathlib `v4.34.0`.

**The row.** `AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep`, 3,833 silo, **757 net**
pin lines. Of its 224 declarations, **198 are byte-identical and public in the port**, 1 matches by
shape, 2 have no statement twin but exist under another name (`solution`, `exists_contDiff_dconvWith`),
and **23 are genuinely new**. SET-AF8's "50 declarations / 837 lines" counted the 25 `Def_`-side names
that the statement comparator cannot match (definitions, abbrevs) as new; they are not — see §0.1.

## 0. The manager's part, landed (do not redo it)

Everything below is on disk, green, and statement-checked. **Read it before writing anything**; if you
think one of these is wrong, report it, do not silently rewrite it.

1. **The definition gate is complete — no `Def_` node.** `spec/gate_scan.py` on the wrapper and on all
   four `Def_` modules of the file's import closure —
   `Definitions/Def_AutomorphicForm_{CuspidalConstituent,IsotypicCuspSpace,TwistedOrbital,FactorizableTestFn}.lean`
   — reports `uses 5/21, 29/123, 4/82, 4/10` with **0 missing from the port**. `IsCuspSubrep`,
   `ArchTypeFamily`, `ArchTypeFamily.IsContainedIn`, `archCutSubmodule`, `typeSubmodule`,
   `rowIsometryInclAt₀` and the row-isometry subgroup are all importable.
2. **The generic convolution-operator block is homed, public, in `RepTheory/ConvolutionLimit.lean`.**
   The pin's `ConvTransport` section (pin `:3155–3250`: `conv_integrand_eq`, `convDomain`,
   `mem_convDomain_iff`, `convOpOn`, `convOpOn_apply`, `comp_mul_mem_convDomain`, `convOpOn_comp_mul`,
   `convOpOn_mem_iSup_typeSubmodule`) is now that module's `section ConvTransport`, in
   `namespace ArchApproxIdentity` — the same subject as its neighbours `convOpR`/`convOpL`/`dconvWith`.
   `check_port --force` on it: **32 ok / 0 mismatch / 0 missing**; the module builds in 9.8 s, silent.
   That file now carries the AF8 `S_` file as a second `spec-pin:`.
3. **Two promotions in `AutomorphicForm/Adelic/TestFnTop.lean`.** `continuous_archEntries` and
   `continuous_of_isArchTestFactor` are **public** (they are public in the pin's own source; the port
   had made them `private`). While touching it the module was migrated off the frozen checker: it now
   has `spec-pin:` lines and is gone from `old_check_stmts.py`'s `PORT_FILES`. Its gate is
   **3 ok / 0 mismatch / 0 missing**, build 4.1 s, silent.
4. **The module exists.** `FLTForHuman/AutomorphicForm/Adelic/Cusp/RightConvSubrep.lean` — header with
   the two wires, the imports, the opens, and the pin's `JoinOfFamilies` section already ported
   (`archTypeFamilyJoin`, `isContainedIn_archTypeFamilyJoin_left`, `..._right`, `map_algebraMap_self`,
   all `private`, names with the pin's `aux_` dropped). `lake build` 3.1 s, silent; `check_port` on it
   `0 ok / 0 mismatch / 0 missing` (nothing public yet).
5. **The import surface is verified, not assumed.** `lean/tmp/af8-surface.lean` (untracked scratch)
   `#check`s ~90 names — every declaration the remaining proofs need — against exactly the module's
   imports and compiles **silently**. Keep it while you work; it is your first line of defence when a
   name will not resolve. The pin → port names it pins down:

   | pin | port |
   |---|---|
   | `KAvArch.Kprod` · `KAvArch.Kw` · `KAvArch.muK` · `KAvArch.inclArch` · `KAvArch.inclAdelic` · `KAvArch.isMulRightInvariant_muK` · `KAvArch.muK_univ` | `ArchInfra.Kprod` · `.Kw` · `.muK` · `.inclArch` · `.inclAdelic` · `.isMulRightInvariant_muK` · `.muK_univ` |
   | `KAvArchT.locallyCompactSpace_archGL` · `secondCountableTopology_archGL` · `secondCountableTopology_piRowIsometrySubgroup₀` · `sigmaFinite_archHaarK` | `ArchInfraTopology.*` (same last names) |
   | `Ent` | `ArchEntryBall.EntrySpace` |
   | `RowIsos.forall_rowIsometryInclAt₀_injective` | `ArchEntryBall.forall_rowIsometryInclAt₀_injective` |
   | `KAv.convDomain` · `KAv.convOpOn` · `KAv.mem_convDomain_iff` · `KAv.convOpOn_apply` · `KAv.convOpOn_mem_iSup_typeSubmodule` | `ArchApproxIdentity.*` (already open in the module) |
   | `KAvArch.exists_approxIdentity` · `tendsto_integral_mul_approxIdentity` | `ArchEntryBall.*` |
   | `archHaarK` | `AutomorphicForm.archHaarK` (`Adelic/ArchHaar.lean`, reached transitively) |
   | pin `continuous_of_mem_cuspKFiniteSubmodule` (pin `:3295`) | `CuspidalConstituent.TSMain.continuous_of_mem_cuspKFiniteSubmodule` — **import it, do not re-prove it** (20 pin lines saved) |
   | pin `exists_contDiff_dconvWith` (pin `:2967`, the ℝ-valued form) | `ArchApproxIdentity.exists_contDiff_dconvWith` (`ArchApproxIdentity/Instantiate.lean`, public; the "0.921 ratio" is `Kprod` spelled `ArchInfra.Kprod`) — **do not rewrite it**; its only pin consumer is `main`, which the port already has. Only the ℂ-valued `aux_exists_contDiff_dconvWith` (pin `:3373`) is yours. |
   | `RowIsos.archRowIsometryInclAt₀_injective` (**not in the table as issued**) | `ArchEntryBall.archRowIsometryInclAt₀_injective`, beside the `forall_` twin (`EntryBall.lean:389`) |
   | the pin's `p2m_reactivate "…KAvArch"` (**load-bearing, learned at the landing**) | **one line `open scoped ArchInfra`**: `compactSpace_Kw` and the `muK` probability/Haar facts are *scoped* instances there. The `#check` surface probe cannot reveal this — it resolves names, not instance synthesis (FR-0112). |

### 0.1 What is actually left: 11 declarations, ≈600 pin lines

| pin declaration | pin lines | where it goes | new name |
|---|---:|---|---|
| `aux_integral_mul_dconvWith` | 140 | **`RepTheory/ConvolutionLimit.lean`**, new `section ConvLimit` | `integral_mul_dconvWith` |
| `aux_exists_kernel` | 121 | the module | `exists_convKernel` |
| `solution` | 69 | the module, **public** | the wrapper's statement |
| `aux_dconvWith_tensor` | 57 | the module | `dconvWith_tensor` |
| `aux_rightConv_rightTranslate_eq` | 32 | the module | `rightConv_rightTranslate_eq` |
| `aux_exists_contDiff_dconvWith` | 29 | the module | `exists_contDiff_dconvWith` |
| `aux_rightConv_mem_archCutSubmodule` | 26 | the module | `rightConv_mem_archCutSubmodule` |
| `aux_exists_archTypeFamily_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule` | 22 | the module | `exists_archTypeFamily_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule` |
| `aux_isArchTestFactor_mul_right` | 13 | the module | `isArchTestFactor_mul_right` |
| `aux_exists_factors_mul_right` | 11 | the module | `exists_factors_mul_right` |
| `aux_isFinTestFactor_mul_right` | 6 | the module | `isFinTestFactor_mul_right` |

All but `solution` are `private` in the pin and stay `private` here. Names: drop the pin's `aux_`
prefix, keep the rest verbatim — the port's convention, and no invented tokens.

**Why `integral_mul_dconvWith` goes to the engine, not to the module.** Its statement names only
`Kc`, `H`, `a : Kc →* H`, two measures `μ` on `Kc` and `ν` on `H`, and `dconvWith` — no adèles, no
`GL₂`, exactly the abstraction level of `ConvolutionLimit.lean`, whose `Support`/`Limit` sections
already carry `integral_mul_shift`, `isCompact_image_mul_mul`, `mem_image_mul_mul_of_ne` and
`hasCompactSupport_dconvWith`, which this proof uses. Put it there as a new `section ConvLimit` in
`namespace ArchApproxIdentity`, with its own `variable` block (the `ZetaB` variables are closed by
then). That file already imports `Mathlib.MeasureTheory.Integral.Prod`, so
`integral_integral_swap_of_hasCompactSupport` is available. Its `spec-pin:` already covers the
statement. If the section needs anything `dconvWith`'s own hypotheses do not give, **report it** —
do not weaken the statement to make it fit the section.

## 1. What you write

1. **`ConvTransport`'s companion in `RepTheory/ConvolutionLimit.lean`** — the one 140-line theorem
   above, transcription-faithful, in the engine's public style (the engine is public there).
2. **In the new module**, in this dependency order: `isArchTestFactor_mul_right`,
   `isFinTestFactor_mul_right`, `exists_factors_mul_right`, `exists_archTypeFamily_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule`,
   `rightConv_mem_archCutSubmodule`, `rightConv_rightTranslate_eq`, `exists_contDiff_dconvWith`,
   `dconvWith_tensor`, `exists_convKernel`, then the headline.
3. **The headline, public, at the wrapper's statement, verbatim** (this exact binder list; it is what
   `check_port` diffs and what the consumer zone composes):

```lean
theorem rightConv_rightTranslate_mem_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (tys : ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F pins ξ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ V)
    (h : AdelicGL2 (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f) :
    rightConv F (rightTranslate F h φ) f ∈ V
```

## 2. The two files

**`FLTForHuman/AutomorphicForm/Adelic/Cusp/RightConvSubrep.lean`** — exists; add to it, do not
restructure it. Its header already states the subject and carries the two wires
(`Theorems/Thm_…` + `P2M/Sol/S_…`); `set_option linter.style.haveILetI false` is already at the top
(the pin's `letI := glBorel` walls), `open ArchApproxIdentity` is already there, and the
`JoinOfFamilies` section is already written. Home rationale: the subject is the cuspidal
subrepresentation; `Cusp/Constituent.lean` holds `IsCuspSubrep`, and the module sits above
`RightConvRegularity` (its premise) and above the engine.

**`FLTForHuman/RepTheory/ConvolutionLimit.lean`** — one new section, appended; do not touch the
existing declarations.

## 3. Traps

1. **The pin's names are not the port's.** 174 pin declarations are already in the port under other
   names, and 25 more are *definitions* whose statements the comparator cannot match (`piE`, `rt`,
   `Kw`, `Ent`, `muK`, `convDomain`, `rowIsometryInclAt₀`, `entryBall_mono`, `coeffFun_apply`,
   `piRep_apply`, …). §0's table is the map. Do not grep a pin name, conclude it is missing and
   write it again.
2. **`convOpOn` and `convDomain` are already written** (`ArchApproxIdentity.*`, ConvolutionLimit), and
   so are the two `archTypeFamilyJoin` monotonicity lemmas (the module). Do not re-derive them.
3. **Do not "repair" a pin name without checking the right one.** `Continuous.comp_continuous` does
   not exist in this mathlib, but the pin's `hff.1.comp_continuous (continuous_mul_const k)` is
   correct as written: `hff.1` is `IsLocallyConstant ff`, and `IsLocallyConstant.comp_continuous`
   (Mathlib/Topology/LocallyConstant/Basic.lean) is the lemma. Writing `(hff.1).comp …` fails.
   *As issued this trap said the opposite; corrected at the landing (FR-0113).*
4. **The `p2m_open` translation.** The pin's `p2m_open "A B~h C"` is `open A` / `open B (h)` /
   `open C`, each with `open scoped`. `p2m_reactivate` lines are dropped (they re-activate the file's
   own namespaces, which contain no scoped instances).
5. `set_option linter.style.haveILetI false in` locally where the pin keeps a `letI := glBorel` wall
   that a single declaration needs longer than the file-wide setting covers; the file-wide one is
   already there, so usually nothing to do.
6. No `set_option maxHeartbeats`; no `sorry`/`admit`/`axiom`/`native_decide`; no new `import` in the
   module beyond what is there (if one is needed, that is a manager decision — report it).
7. `check_port` treats every public declaration as an error unless the pin file has it. Keep the new
   declarations `private` (the pin does), so only the headline is diffed.

## 4. Gates

1. `lake env lean <file>` (with `-DautoImplicit=false -DmaxHeartbeats=200000` in the edit loop)
   silent, then `flock .lake/flt_build.lock timeout 280 lake build
   FLTForHuman.AutomorphicForm.Adelic.Cusp.RightConvSubrep` and the same for
   `FLTForHuman.RepTheory.ConvolutionLimit`; **no tree build**, no dependents.
2. `spec/check_port.py --force` on **both** files: the module **1 ok / 0 mismatch / 0 missing**, the
   engine **33 ok / 0 mismatch / 0 missing** (32 today + `integral_mul_dconvWith`).
3. `#print axioms` on the headline → `[propext, Classical.choice, Quot.sound]`.
4. `tools/deps/dedup.py --within` (expect ~0: the 3,000 ported lines were imported, not copied) and
   `--cross`; `tools/deps/move_dead.py` triaged by the rule — dead mathematics → `Reserve/`,
   duplicate or plumbing → delete. Report each disposition.
5. Zero warnings on both modules.
6. `spec/AutomorphicFormSetAF8Consumer.lean` — one zone, a real composition (no `#check`): compose the
   headline with SET-AF5's continuity, e.g. `Continuous (rightConv F (rightTranslate F h φ) f)` from
   `continuous_rightConv_and_contDiff_of_isFactorizableTestFn` together with the membership it implies.
7. Log build output under `lean/tmp/`; every tool call must finish inside 2 minutes and no loop may be
   used to dodge that. A compile that can plausibly run a minute is a background job with its own log.

## 5. Report

Module line counts (both files); the two checkers' numbers; the axioms line; build times and silence;
`dedup`'s clusters and `move_dead`'s report with each disposition; the consumer zone's error count;
**how many of §0's imports you used as-is and how many needed a re-statement, and why**; and every
deviation from the pin. **A blocker goes back immediately**, with the pin line and the error — do not
grind out a diagnosis, and never work around a hub defect locally.
