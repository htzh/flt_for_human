# WORKORDER-UF1 — the unit-factorizable definition gate (tier 3)

This is the **manager's ground wave** for the unit-factorizable trio of the `AutomorphicForm`
ready shelf — `exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule`
(823 silo lines, `tools/deps/build/uf_trio.json`), its `_finTestFactor_` sibling (854) and its
`_principalLevel_` sibling (971). Those three `S_` files are ready by premise (their one
premise, `exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`,
is already ported at `FLTForHuman/AutomorphicForm/Adelic/ArchApproxIdentity.lean`) but their
**statements name definitions the port does not have**. This order lands that definition layer
so the trio's proof port (`WORKORDER-UF2`) can be cut.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`. Checker baseline on this tree: **9790 identical (671 promoted, 83 renamed),
0 mismatched, 0 missing, 38 own (9828 checked)**. This order is tier 3 and **wires nothing**: the
checker delta is **0** (the modules are registered, not diffed) and the trio's `+3` comes later.

## 1. Scope — the exact gate, hand-checked

The trio names 20 declarations outside the port across three pin `Definitions/` modules. The wave
homes the part that is one development; the rest is deferred with a reason (§1.3). Every
declaration below was read in the pin, and its port status checked by hand (playbook §4(a)) —
`--ready`/`--with-defs` cannot see this gate.

### 1.1 M1 — the integrality / bi-invariance block (`Def_AutomorphicForm_LocalOrbitalBase`)

Pin lines 13–82, 131–140 and 298–315; **13 declarations**, ≈100 lines, all in the pin's namespace
`AutomorphicForm`:

`integralMatrixSet` (15), `integralMatrixSet_eq_pi` (17), `isCompact_integralMatrixSet` (22),
`isOpen_integralMatrixSet` (27), `integralUnitsSet` (33), `mem_integralUnitsSet` (37),
`one_mem_integralUnitsSet` (42), `isCompact_integralUnitsSet` (67), `isOpen_integralUnitsSet` (75),
`isLocallyConstant_indicator_one` (131), `IsBiInvariantUnder` (298), `IsBiInvariantUnder.mono` (303),
`isBiInvariantUnder_bot` (310).

`IsBiInvariantUnder` is the pin's only definition this trio names from that module (1 use); the
rest is its definitional/lemma support and the `semiLocalIntegralSet` support pulled in through
`SemiLocal`.

### 1.2 M2 — the semi-local layer + the unit-factorizable predicates (`Def_AutomorphicForm_TwistedOrbital`)

Pin lines 17–51 (Carrier), 67–74 (Embed), 76–192 (SemiLocal), 437–481 (AboveTier) and 483–522
(AboveTierRefined); **≈42 declarations**, ≈250 lines, in the pin's namespace `AutomorphicForm`:

* **Carrier** 17–51: `isTopologicalRing_tensor`, `t2Space_tensor`, `locallyCompactSpace_tensor`,
  `isTopologicalGroup_tensorGL`, `t2Space_tensorGL`, `locallyCompactSpace_tensorGL`;
* **Embed** 67–74: `toTensorGL`;
* **SemiLocal** 76–192: `semiLocalHomeomorph`, `piIntegers`, `isCompact_piIntegers`,
  `isOpen_piIntegers`, `semiLocalIntegers`, `semiLocalIntegers_eq_preimage`,
  `isCompact_semiLocalIntegers`, `isOpen_semiLocalIntegers`, `zero_mem_semiLocalIntegers`,
  `one_mem_semiLocalIntegers`, `IsSemiLocalTestFn`, `isSemiLocalTestFn_zero`,
  `semiLocalIntegralSet`, `one_mem_semiLocalIntegralSet`, `isCompact_semiLocalIntegralSet`,
  `isOpen_semiLocalIntegralSet`, `semiLocalIntegralCompacts`,
  `isSemiLocalTestFn_indicator_semiLocalIntegralSet`, `semiLocalHaar`,
  `isHaarMeasure_semiLocalHaar`, `semiLocalHaar_semiLocalIntegralSet`;
* **AboveTier** 437–481: `semiLocalEval`, `semiLocalComponent`, `IsSemiLocalFactorization`,
  `IsUnitFactorizableAbove`, `IsUnitFactorizableAbove.mono`, `isSemiLocalFactorization_zero`,
  `isUnitFactorizableAbove_zero`;
* **AboveTierRefined** 483–522: `IsUnitFactorizableAboveOfType`,
  `IsUnitFactorizableAboveOfType.isUnitFactorizableAbove`,
  `IsUnitFactorizableAboveOfType.isArchBiFinite`, `IsUnitFactorizableAboveOfType.mono`,
  `IsUnitFactorizableAboveOfType.mono_type`, `isUnitFactorizableAboveOfType_zero`.

This is the whole definitional chain of the trio's statement:
`IsUnitFactorizableAboveOfType φ := IsUnitFactorizableAbove K L U S φ ∧ IsArchBiFinite L tys φ`,
`IsUnitFactorizableAbove := IsBiInvariantUnder L U φ ∧ ∃ …, IsSemiLocalFactorization`, and
`IsSemiLocalFactorization` names `IsArchTestFactor`/`IsFinTestFactor` (ported),
`IsSemiLocalTestFn`, `semiLocalComponent`, `semiLocalIntegralSet`.

### 1.3 Deferred, with the reason (registered in [CARRY-FORWARD.md](../../CARRY-FORWARD.md))

* The **twisted-orbital orbital-integral subject** of `Def_AutomorphicForm_TwistedOrbital`:
  `Twist` 194–223, `TwistedBorel` 225–233, `Untwisted` 235–271, `Twisted` 273–352,
  `FinitePlaces` 354–394, `Archimedean` 396–435 (`archHaarL`, `archIdent`, `archIdentGL`,
  `AreMatchingArch`, …), `BelowTier` 524–574, and `centralizerBorel` (62). It has **no consumer
  here**, and its dependency is the unported tensor/base-change chain (`Def_DedekindDomain_Completion_BaseChange`,
  `Def_AutomorphicForm_SigmaCentralizer`, `Def_M4aHerbrand_ArchSemilocal`, `Def_NumberField_InfiniteAdeleRing_BaseChangeData`)
  — the cut [TOPIC-archTestFactor-family.md](TOPIC-archTestFactor-family.md) §5 already names as
  its own wave. Its consumers are the `coversModCentre` silo (3,038) and the
  `twistedConvOp_mem_isotypicCuspSubmodule…` silo (2,542).
* The **local-orbital subject** of `Def_AutomorphicForm_LocalOrbitalBase`: `localIntegralSet`,
  `localHaar`, the orbital-integral predicates, `IsUnitFactorizableAt`, `IsUnitFactorization`
  (lines 84–433 minus the blocks of §1.1). Same reason.
* **Explicitly not this order.** `glBorelOf`, `borelSpace_glBorelOf`, `archHaarK` are already
  public at `FLTForHuman/AutomorphicForm/Adelic/ArchHaar.lean` — **import, never re-prove**; no
  existing module is edited; no promotion; no checker wiring; the trio's proof port.

## 2. Sources and deliverable

Statements *and* proofs are the pin `Definitions/` modules (these are definition modules with no
`Theorems/` wrapper):

* `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean`
* `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_TwistedOrbital.lean`

The local clone `~/proj/fermats-last-theorem` is the working copy.

**Deliverable — three new tier-3 modules, in import order**, namespace `AutomorphicForm` (the
pin's own), every declaration **public at the pin's name**, with
`-- pin: <name> (Definitions/<module>.lean:<line>)` above each (the tier-3 register reads it
there), and a header stating the subject, the pin, the deferrals of §1.3 and the reuse edges:

| module | contents | ≈ lines |
|---|---|---:|
| `FLTForHuman/AutomorphicForm/Adelic/IntegralUnits.lean` | §1.1 (`integralMatrixSet` … `IsBiInvariantUnder`) | 100 |
| `FLTForHuman/AutomorphicForm/Adelic/SemiLocal.lean` | §1.2 Carrier + Embed + SemiLocal | 180 |
| `FLTForHuman/AutomorphicForm/Adelic/UnitFactorizable.lean` | §1.2 AboveTier + AboveTierRefined | 70 |

No other file is created or edited. The modules are **not** wired (`PORT_FILES`) in this order.

## 3. Transcription rules, reuse, and the hub prohibition

* Strip nothing from the pin's text but the chapter: the pin declares in `namespace AutomorphicForm`
  and so does the port. Keep every declaration name and the pin's `variable … in` forms for the
  `def`/`abbrev` that take section variables (the checker's contract for a transcribed `def`).
* **Reuse, do not re-prove** (all read and confirmed present):
  `AutomorphicForm.glBorelOf`, `AutomorphicForm.borelSpace_glBorelOf`, `AutomorphicForm.archHaarK`
  (`AutomorphicForm/Adelic/ArchHaar.lean`) — `semiLocalHaar`/`isHaarMeasure_semiLocalHaar` and the
  `glBorelOf`-typed definitions import them;
  `AutomorphicForm.IsArchTestFactor`, `AutomorphicForm.IsFinTestFactor`, `isArchTestFactor_zero`,
  `isFinTestFactor_zero` (`AutomorphicForm/Adelic/FactorizableTestFn.lean`) — named by
  `IsSemiLocalFactorization`/`isSemiLocalFactorization_zero`;
  `AutomorphicForm.IsArchBiFinite` (`AutomorphicForm/Adelic/IsotypicCuspSpace.lean`) — named by
  `IsUnitFactorizableAboveOfType`. M1's `integralUnitsSet` is imported by M2's
  `semiLocalIntegralSet`; M2's `IsSemiLocalTestFn`/`semiLocalComponent` by M3.
* The pin's `def`s over `L ⊗[K] v.adicCompletion K` use pin/mathlib `HeightOneSpectrum` API
  (`adicCompletion.baseChangeContinuousAlgEquiv`, `baseChangeAlgEquiv`, `tensorAdicCompletionIntegersTo`,
  `Extension`, `finAdeleEval`). If one is unported, **stop and report it verbatim with its pin
  line** — do not invent a shim, and do not edit the module that lacks it.
* Apply the `v4.34.0` drift checklist (playbook §7) as it appears (`mem_setOf_eq` → `mem_ofPred_eq`,
  `ite_eq_left`/`ite_eq_right`, deprecated shims). Do not transcribe a pin `set_option maxHeartbeats`
  (there is none here).
* **Hub prohibition.** A helper you need stays `private` here and is reported; you never promote,
  rename, or edit an existing module. If you believe a promotion is genuinely required, **stop and
  report** the declaration, the intended host and the `build_ladder.py --edit` price; the manager
  decides.

## 4. Named risks and stop conditions

Named risks, in the order they will bite: the `Carrier` topology instances over `L ⊗[K] A` (six
`inferInstance`-shaped proofs — the pin passes the tensor instances explicitly; reproduce that,
do not fight instance search); `semiLocalIntegers_eq_preimage` (13 lines, `Set.range`/`preimage`
rewriting); `isCompact_semiLocalIntegralSet`/`isOpen_semiLocalIntegralSet` (they `haveI` the
tensor ring/T2 instances locally, mirroring the pin); `semiLocalHaar`'s `letI`/`haveI` bracket
over `glBorelOf` + `isTopologicalGroup_tensorGL`; and the `AboveTier` `haveI`s. Diagnose at the
low cap (playbook §3.5), fix the inference, report — never raise `maxHeartbeats`.

**Stop and report** if: a pin `HeightOneSpectrum`/`Extension`/`finAdeleEval` prerequisite is
unported; a module cannot compile without editing an existing one; the `glBorelOf`-typed measure
needs a promotion; or the pin text cannot be matched without moving a statement. Do **not** open
the deferred `Twist`/`Twisted`/`FinitePlaces`/`BelowTier` sections, do not touch the trio's proof
siles, and do not wire anything.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the
> cap is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with `flock`
> and bounded with `timeout`. Per wave, build only the wave's affected targets — **never a bare
> whole-tree `lake build`**. A whole-tree build happens once, at the session's end, only after the
> user agrees to it, and never on the agent's own initiative.

Concretely: tier-0 loop until each of the three modules is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build <module>` in the order M1, M2, M3. No bare
`lake build`, no dependent, no trio.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on M1, then M2, then M3 | exit 0, **0 warnings**, no forbidden token (`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/`maxHeartbeats`) |
| tier-1 build of each module | green; record jobs and wall/user/sys time |
| coverage §1.1 + §1.2 | every listed declaration present **exactly once**, at the pin's name; the deferred §1.3 declarations **absent**; nothing invented |
| the five reuse edges | imported, not re-proved; `glBorelOf`-typed values reference `ArchHaar`'s |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

No checker run, no register edit, no wiring. (The checker's mutation sensitivity is its own
`--selftest`, run when the checker changes — not here.)

## 7. Report shape

Module paths and line counts; public vs `private` declaration counts; tier-0 and tier-1
wall/user/sys times; the coverage table of §6; every reuse edge as used; every pin prerequisite
that was unported (there must be none, or a stop); any statement that had to change (there must
be none); any promotion you stopped on with its `build_ladder.py --edit` price; `git status
--porcelain` showing only the three new modules.

## 8. The manager's half (not this order)

After review: register the three modules in `spec/UNWIRED-PUBLIC.md` (tier 3, no checker wiring);
then cut `WORKORDER-UF2` for the trio's proof port against the landed definitions — the trio is
one development written nearly three times (`port_plan`: 2,648 raw / **1,281 net new** / 88 groups,
a 582-line / 46-declaration block shared by all three and a 151-line / 7-declaration block shared
by two), with `IsUnitFactorizableAboveOfType` now statable.

## 9. Reproduce

```bash
cd tools/deps
python3 port_advise.py --target AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule \
  --target AutomorphicForm.exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule \
  --target AutomorphicForm.exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule \
  --json build/uf_trio.json
python3 port_plan.py --json build/uf_trio.json --section all    # 1,281 net new, the 582+151 blocks
cd ../lean
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/AutomorphicForm/Adelic/IntegralUnits.lean
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/AutomorphicForm/Adelic/SemiLocal.lean
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/AutomorphicForm/Adelic/UnitFactorizable.lean
```

The pin sources are public at
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean`
and
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_TwistedOrbital.lean`.

## 10. Results as landed (2026-10-14) — M1 landed, M2/M3 stopped, the wave deferred

**Outcome.** M1 landed green; M2/M3 hit the §4 stop condition on unported pin prerequisites and
were **not** written. The manager then priced the blocker and **deferred** the whole UF effort.

| module | lines | public | private | tier-0 | tier-1 |
|---|---:|---:|---:|---|---|
| `AutomorphicForm/Adelic/IntegralUnits.lean` (M1) | 168 | 13 | 1 | exit 0, 0 warnings (24.4 s wall) | 3,426 jobs, 2.9 s |
| `AutomorphicForm/Adelic/SemiLocal.lean` (M2) | — | — | — | **not written** (stop) | — |
| `AutomorphicForm/Adelic/UnitFactorizable.lean` (M3) | — | — | — | **not written** (stop) | — |

M1's coverage is §1.1 exactly (13/13 at the pin's names), plus the pin's `integralUnitsSet_eq_preimage`
kept `private` (the pin's proofs of the compact/open units lemmas use it). §1.2 coverage 0/42; the
whole §1.3 deferred surface is absent; no statement changed; no promotion; no existing module
edited. Registered tier 3: `UNWIRED-PUBLIC.md` 104 → **105 modules**, 2,998 → **3,011 public**,
2,710 → **2,723 with a pin original**; `--check` current.

**The stop, and the correction to §1.** §1.2 put the `SemiLocal` block **in scope** while §1.3
called the tensor/base-change chain the property of the *deferred* orbital-integral subject only.
That split is wrong: the trio's **statements** name `IsUnitFactorizableAboveOfType`, whose body
reaches `semiLocalIntegralSet` → `HeightOneSpectrum.tensorAdicCompletionIntegersTo` and
`semiLocalEval` → `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv`, and its proof reaches
`isCompact_semiLocalIntegralSet` → `piIntegers`/`HeightOneSpectrum.Extension`/`semiLocalHomeomorph`
and the `IsModuleTopology.*` instances. None of those are ported. This is the §4(a) trap the note
warns about, caught at the stop rather than mid-transcription.

**The price.** Minimal closure of the named seeds: **127 declarations / ≈1,966 pin lines across
nine modules**; whole-node, **3,740 pin lines / 341 declarations over eleven**. Both are larger
than the trio they unlock (`port_plan` 1,281 net new), and
`Def_DedekindDomain_Completion_BaseChange` carries `set_option maxHeartbeats 1200000` /
`synthInstance.maxHeartbeats 400000` — a discipline collision with no clean local fix yet.

**Decision — defer, do not port the chain.** `frontier --ds --top 0 --list` shows **zero** hits for
any chain name while the trio is `needed` at 823: no D-S theorem cites the chain, so deferring the
trio blocks nothing. It should be re-cut with its larger siblings
(`convOp_mem_isotypicCuspSubmodule…` 1,231, then the `coversModCentre` 3,038 and
`twistedConvOp_mem_…` 2,542 silos) so the chain is paid once. `WORKORDER-UF2` is **not** cut.
Record: [CARRY-FORWARD.md](../../CARRY-FORWARD.md) §Deferred API.

