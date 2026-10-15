# The twisted-orbital definition program — the base-change chain behind the unit-factorizable cluster

This note is the manager's plan for the **definitional** dependency the frontier cannot see: the
base-change chain under `Def_AutomorphicForm_TwistedOrbital`. It exists because
`AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule`
is `needed` for the Deligne–Serre target (823 silo lines, `build/ds_needed.txt:399`), its statement
names `IsUnitFactorizableAboveOfType`, and that definition reaches the chain. `frontier` shows
**zero** hits for the chain (it is a citation graph; defs are not edges), so this is the §9 blind
spot made concrete. [WORKORDER-UF1](WORKORDER-UF1-unit-factorizable-defs.md) §10 records the stop
that discovered it.

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Checker baseline on this
tree: **9790 identical / 0 mismatched / 0 missing / 38 own**.

## 1. The dependency, exactly

`IsUnitFactorizableAboveOfType` (`TwistedOrbital:489`) `= IsUnitFactorizableAbove ∧ IsArchBiFinite`;
`IsUnitFactorizableAbove` (`:463`) `= IsBiInvariantUnder ∧ ∃…, IsSemiLocalFactorization`;
`IsSemiLocalFactorization` (`:452`) names `semiLocalComponent` (`:446`) and `semiLocalIntegralSet`
(`:136`); `semiLocalIntegralSet = integralUnitsSet (semiLocalIntegers …)` and
`semiLocalIntegers` (`:98`) `= Set.range (HeightOneSpectrum.tensorAdicCompletionIntegersTo …)`;
`semiLocalEval` (`:441`) names `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv`. Those two are
`Def_DedekindDomain_Completion_BaseChange:649` and `:1058`. So the trio's **statement** requires
the chain, not merely its proof.

The full transitive `Definitions/` closure of the two def nodes is **54 modules / 13,974 pin
lines**; most of it is already landed (the `AdelicLevel`, `AdelicHaar`, `FactorizableTestFn`,
`IsotypicCuspSpace`, `ArchType`, `Siegel`, `WindowedSiegel` layers). The unported part is the
chain below.

### 1.1 Is the dependence essential? Yes — and it is specifically the semi-local apparatus

Checked against the two `S_` files that carry the shared development. The trio uses the chain
**materially**, not cosmetically: `semiLocalComponent` 18×, `semiLocalIntegers` 12×,
`semiLocalHomeomorph` 12×, `semiLocalEval` 8×, `semiLocalIntegralSet` 6×, `baseChangeAlgEquiv` 4×,
`piIntegers` 4×, `IsSemiLocalTestFn` 2×. The construction *is* an approximate identity factorized
across the places in `S` with integrality away from `S`; `IsSemiLocalFactorization` is that
content, and there is no route to the conclusion that skips the component map
`GL₂(A_L^fin) → GL₂(L ⊗_K K_v)` and its integral units.

It is not a mathematical artifact — but **mathlib v4.34 partly closed the gap the pin worked
around**. `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean:519–540` now proves
`Module.Finite Kv Lw` from a dense base-change map `Kv ⊗[K] L →ₗ[Kv] Lw`; that section was added
after the pin's `db584cd6`. The pin's specific declarations are still absent
(`tensorAdicCompletionIntegersTo`, `baseChangeAlgEquiv`, `locallyCompactSpaceOfFinite` all return
nothing in mathlib v4.34), so a port is owed — but W2 should *build on* the new mathlib lemma
rather than re-derive its foundation.

**The trio reaches none of the archimedean/twisted-orbital subject** (0 hits for `archIdent`,
`archIdentGL`, `AreMatchingArch`, `tensorPiAlgHom`, `InfinitePlaceData`, `IsTwistedOrbitalIntegral`,
`AreMatchingOn`, `twistedCentralizer`, `SigmaConjugate`, `toTensorGL`, `archHaarL`). So the *essential*
chain is six modules — `Def_Mathlib_IsModuleTopology` (511),
`Def_DedekindDomain_AdicValuation_InlineSpecific` (565),
`Def_DedekindDomain_Completion_BaseChange` (1,160), `Def_DedekindDomain_IntegralClosure` (301),
`Def_Mathlib_RightActionInstances` (179), `Def_Mathlib_Topology_Algebra_UniformRing` (40) ≈ **2,756
pin lines** — and the remaining ≈1,000 (`Def_NumberField_Extension`,
`Def_NumberField_InfiniteAdeleRing_BaseChangeData`, `Def_M4aHerbrand_ArchSemilocal`,
`Def_AutomorphicForm_SigmaCentralizer`, `Def_AutomorphicForm_UnitFactorizableOfType`) is for the
sections the trio never states. The plan keeps the **whole node** anyway, on the manager's call:
those sections are owed by the other D-S-`needed` consumers — `convOp_mem_isotypicCuspSubmodule…`
(1,231), the `coversModCentre` silo (3,038), `twistedConvOp_mem_…` (2,542) — so paying them once
here is cheaper than a third pass at `TwistedOrbital`.

## 2. The wave plan

Homes mirror the pin's subject, not its file names, and follow the established `Def_Mathlib_*`
convention (a mathlib-mirroring path under `FLTForHuman/`, with `import Mathlib` replaced by
explicit imports — see `Topology/Algebra/Valued/WithZeroMulInt.lean`).

### W1 — mathlib supplements and base algebra (≈1,150 pin lines; **no caps**)

| pin module | lines / decls | home |
|---|---:|---|
| `Def_Mathlib_IsModuleTopology` | 511 / 39 | `FLTForHuman/Topology/Algebra/ModuleTopology.lean` |
| `Def_Mathlib_Topology_Algebra_UniformRing` | 40 / 3 | `FLTForHuman/Topology/Algebra/UniformRing.lean` |
| `Def_Mathlib_RightActionInstances` | 179 / 14 | `FLTForHuman/Algebra/RightActionInstances.lean` |
| `Def_Mathlib_RingTheory_Localization_BaseChange` | 79 / 6 | `FLTForHuman/RingTheory/Localization/BaseChange.lean` |
| `Def_Mathlib_Algebra_Algebra_Hom` | 141 / 18 | `FLTForHuman/Algebra/Algebra/SemialgHom.lean` |
| `Def_NumberField_Extension` | 199 / 35 | `FLTForHuman/NumberTheory/NumberField/Extension.lean` |

`Def_Mathlib_IsModuleTopology` imports bare `Mathlib` and declares a `class IsTopologicalModule`
backport; before transcribing, check mathlib `v4.34.0` for each declaration and substitute where
it now exists (the UF1 stop found `Module.topologicalRing`, `t2Space`,
`locallyCompactSpaceOfFinite` absent).

### W2 — the Dedekind adic base-change core (≈2,030 pin lines; **caps risk**)

| pin module | lines / decls | home |
|---|---:|---|
| `Def_DedekindDomain_IntegralClosure` | 301 / 22 | `FLTForHuman/RingTheory/DedekindDomain/IntegralClosure.lean` |
| `Def_DedekindDomain_AdicValuation_InlineSpecific` | 565 / 32 | `FLTForHuman/RingTheory/DedekindDomain/AdicValuationInline.lean` |
| `Def_DedekindDomain_Completion_BaseChange` | 1,160 / 73 | `FLTForHuman/RingTheory/DedekindDomain/CompletionBaseChange.lean` |

**Manager decision required, and it is the one real risk.** Both the last two carry
`set_option maxHeartbeats 1200000` / `synthInstance.maxHeartbeats 400000`, and
`Completion_BaseChange` also `maxSynthPendingDepth 3` / `Elab.async false`. The port's discipline
forbids all of these.

**The method is fixed: keep the low cap, iterate fast, find the actual instance.** The low cap is
not an obstacle to work around, it is the instrument — a declaration that will not fit has an
instance-inference defect, and the job is to find the instance it is missing. The loop: isolate
the offending declaration in a scratch copy, run
`set_option diagnostics true in` / `set_option trace.Meta.synthInstance true in` on it alone at
the 200k cap, read which search fails or unfolds a coercion, then supply the instance
(`letI`/`haveI` with the elaborated type, `inferInstanceAs`, explicit `@`-application) or
restructure so the search is not needed — and re-run. Quick iteration is the point; a
declaration is not "long", it is under-determined. Only a genuine non-fit that survives that
diagnosis is a **stop-and-report to the user**, never a transcribed cap.

`Def_DedekindDomain_AdicValuation_InlineSpecific` should **not** be transcribed whole: it is an
inlining of mathlib's `AdicValuation` that the pin needed at `db584cd6`, its declarations are
mostly `private`, and `Completion_BaseChange` names only **three** of them —
`Valuation.IsRankOneDiscrete` (mathlib now has the class and the `FinitePlace` instance),
`denseRange_of_integerAlgebraMap` (mathlib has `denseRange_algebraMap`,
`AdicValuation.lean:886`) and `ValuationSubring.algebraMap_apply` (re-derivable). Treat it like
W1's supplements: check mathlib first, import the substitute, transcribe only what is genuinely
absent and actually reached — expected to cut 565 lines to tens, and to remove the 1200000-heartbeat
override entirely. `Completion_BaseChange` itself remains the 1,160-line / 73-declaration core; if
it alone will not fit the low cap, W2 splits into W2a (`IntegralClosure` + the InlineSpecific
substitutes) and W2b (`Completion_BaseChange`).

### W3 — the number-field and automorphic definition nodes (≈1,200 pin lines)

| pin module | lines / decls | home | note |
|---|---:|---|---|
| `Def_NumberField_InfiniteAdeleRing_BaseChangeData` | 361 / 36 | `FLTForHuman/NumberTheory/NumberField/InfiniteAdeleRing/BaseChangeData.lean` | |
| `Def_M4aHerbrand_ArchSemilocal` | 284 / 23 | `FLTForHuman/NumberTheory/M4aHerbrand/ArchSemilocal.lean` | `IdeleClassVocab.lean` already there |
| `Def_AutomorphicForm_SigmaCentralizer` | 62 / 6 | `FLTForHuman/AutomorphicForm/Adelic/SigmaCentralizer.lean` | |
| `Def_AutomorphicForm_UnitFactorizableOfType` | 78 / 9 | `FLTForHuman/AutomorphicForm/Adelic/UnitFactorizableOfType.lean` | |
| `Def_AutomorphicForm_LocalOrbitalBase` (rest) | 434 / 62 | `FLTForHuman/AutomorphicForm/Adelic/LocalOrbitalBase.lean` | 13 already in `IntegralUnits.lean` |
| `Def_AutomorphicForm_TwistedOrbital` | 575 / 83 | `FLTForHuman/AutomorphicForm/Adelic/TwistedOrbital.lean` | 3 already in `ArchHaar.lean` |

Whole node: `TwistedOrbital` and `LocalOrbitalBase` land **entire** here, so the orbital-integral
and archimedean sections deferred in [CARRY-FORWARD.md](../../CARRY-FORWARD.md) are no longer cut.

### W4–W5 — the consumer

* **W4** re-cuts [WORKORDER-UF1](WORKORDER-UF1-unit-factorizable-defs.md) §1.2 — `SemiLocal.lean`
  and `UnitFactorizable.lean` — now that the chain exists.
* **W5** is the trio's proof port (`WORKORDER-UF2`): 2,648 raw / **1,281 net new**, a 582-line /
  46-declaration block shared by all three and a 151-line / 7-declaration block shared by two; one
  general-`U` engine serving `levelOne` and `principalLevel` (`principalLevel ≤ levelOne`), plus
  the finTestFactor variant, plus three headlines.

## 3. Order and economy

W1 → W2 → W3 → W4 → W5, each a new-file wave with no existing-module edits (so no cascade; each
module is a tier-3 definition module registered in `spec/UNWIRED-PUBLIC.md`). W2 is the only wave
with a build-cost risk. The trio's `+3` checker delta still comes only in W5. No whole-tree build
until the session's end, with the user's agreement.
