# Topic — the X_H(M) Hecke/diamond inputs and the Along diamond lifts

**Status: SET-H-A LANDED (2026-10-08); SET-H-B/C dispatchable.** Planning record
for the next `ModularCurve` slice exposed by the ready frontier of the
Deligne–Serre target. It is the level-H sibling of the completed X₁ effort
([TOPIC-x1-hecke-diamond-inputs.md](TOPIC-x1-hecke-diamond-inputs.md)); like that
one it follows [porting-playbook.md](../../porting-playbook.md) (§2 planning,
§3.4 sets, §3.5 build discipline, §4 faithfulness). The **definition layer** (§5
SET-H-A) is ported: `ModularCurve/XH/{FunctionField,HeckeOperator,Operators}.lean`
(35 declarations, 385 raw / 155 content) plus 15 promotions in the X₁ prelude;
checker `6365 identical (312 promoted, 83 renamed), 0 mismatched, 0 missing,
36 own`, consumer `spec/XHConsumer.lean` 0 errors / delete-fail 3, whole-tree build
green (9,332 jobs). The measured record is
[logs/xh-hecke-set-a.md](../../logs/xh-hecke-set-a.md), including one deviation from
§2/§3 below: the `qC_*` group **cannot** be promoted (the pin states it over
a general `Γ`, the port's copies are `Γ₁(M)`-specialised), so SET-H-B must
generalise the engine rather than promote it. **No work order is written yet for
the two headline sets (B, C), and none of their proofs is ported.**

## 0. Where this set comes from

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready
```

leaves **93 ready candidates** — nodes whose whole citation demand is ported. By
silo they are `ModularCurve` **42 / 18,429 raw S_ lines**, `CuspForm` 10 / 2,843,
`WeierstrassCurve` 8 / 3,868, and singletons in `CohCarrier`, `AutomorphicForm`,
`AlgebraicCurve`, `PeriodPair`, `ModularForm`, `ModularPolynomialData`,
`CuspFormClass`. The `ModularCurve` silo is by far the largest and is the subject
of this topic.

Inside it the natural cluster is the **Hecke/diamond input layer**, because it is
one story, it is the only `ModularCurve` group the tooling shows sharing a large
prelude, and it carries the highest project leverage of the whole ready list:

| node | pin `S_` raw | project indeg | role |
|---|---:|---:|---|
| `ModularCurve.heckeDiamondInputsHAll` | 918 | **48** | the input bundle for `X_H(M)` |
| `ModularCurve.heckeInputsHAlong` | 326 | 12 | its Hecke half |
| `ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutHBar` | 1,178 | 1 | the H diamond lift |
| `ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutBar` | 1,188 | 3 | its X₁ sibling |

`heckeDiamondInputsHAll` is the largest-leverage ready node on the shelf and sits
on the shortest path to `FLT.fermatLastTheorem` (through
`ModularCurve.toricFrobeniusHecke_toricMonodromyPart_jZero` → the level-lowering
tower). The two `…intertwinesAlong_diamondAut…` nodes share a large engine (729 proof
lines / 75 declarations, `SequenceMatcher` 0.755 over substantive lines — a shared
engine, not the whole-file 0.977 duplicate the ds-head pair was); `heckeInputsHAlong`
is the Hecke half the bundle cites.

## 0.1 Targets and verdict

**Targets.** Four pinned statements, transcribed verbatim:

```lean
theorem ModularCurve.heckeInputsHAlong (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    ModularCurve.HeckeInputsHAlong L M H ℓ

theorem ModularCurve.heckeDiamondInputsHAll (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ModularCurve.HeckeDiamondInputsHAll M H

theorem ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutHBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (d : (ZMod M)ˣ) : ∃ τ, … IntertwinesAlong …

theorem ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutBar (M : ℕ) [NeZero M]
    (ℓ : ℕ) [NeZero ℓ] (d : ℕ) : ∃ τ, … IntertwinesAlong …
```

with predicates (pin `Definitions/`)

- `HeckeDiamondInputsHAll M H := (∀ ℓ prime, HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ)
  ∧ ∀ d : (ZMod M)ˣ, ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ`
  (`Def_ModularCurve_XHOperators.lean:113`);
- `HeckeInputsHAlong L M H ℓ` = the seven inputs on `xHTopFunctionFieldC ℚ M H (M*ℓ)`
  (`HeckeBetaHDefined`, `HeckeAlphaHBarIntegral`, `HeckeBetaHBarIntegral`, a
  `HasPrincipalDivisors`, `FiniteAlong heckeAlphaHBar`, `FundamentalIdentityAlong
  heckeBetaHBar`, `NormFormulaAlong heckeAlphaHBar`) (`Def_ModularCurve_XHHeckeOperator.lean:186`).

**Verdict. Port, but two things differ from a naive reading of `--ready`.**

1. **`--ready` hides the definitions.** The frontier counts theorem premises; all
   four nodes read as terminal (“needed 1 node / itself”), yet three *definition*
   modules they import are unported: `Def_ModularCurve_XH` (179 raw / 111
   content / 25 decls), `Def_ModularCurve_XHHeckeOperator` (249 / 154 / 27) and
   `Def_ModularCurve_XHOperators` (133 / 77 / 16). This is the playbook §2.1
   “a citation-leaf is not a leaf” bias; the XH vocabulary is a definitions-first
   set of its own (§5 SET-H-A). It is mostly thin, because
   `xHFunctionFieldC K M H := qExpFunctionFieldC K (CohCarrier.GammaH M H)` and
   both `qExpFunctionFieldC` and `CohCarrier.GammaH` are already ported.
2. **The `HeckeInputsAlong` already in the port is not this predicate.** The port
   has `ModularCurve.HeckeInputsAlong` (`ModularCurve/Defs/HeckeTotal.lean:27`),
   but it is stated on `modularFunctionFieldFull`/`heckeAlphaBar`; the pin's
   `HeckeInputsHAlong` is stated on `xHTopFunctionFieldC`/`heckeAlphaHBar`. They
   elaborate to the same *type* (`Prop`) but are different propositions; do not
   substitute one for the other. See §2.

Port, in three sets: definitions (A), the diamond-lift pair written once (B), the
Hecke inputs plus the manager's capstone (C). The two diamond nodes are the bulk
and must be written as one development.

## 1. The measured cone

### 1.1 The theorem slice

The four `S_` files are 3,610 raw lines. `port_advise.py` reads **375
declarations** across the four `S_` files and their four `Theorems/` wrappers, and
`port_plan.py` turns that into a correction ledger:

| row | lines |
|---|---:|
| raw `S_` lines | 3,610 |
| declaration lines | 3,511 |
| − duplicate copies (port once) | −1,087 |
| − boilerplate (`import`/`attribute`/`p2m_*`) | −99 |
| once-cost after dedup | 2,424 |
| − already in the port (vetted) | −105 |
| **net new math lines** | **2,319** |

The duplication is structured, and it is what makes this one cluster rather than
four topics (`port_plan.py --section blocks`):

| once | in-port | decls | files |
|---:|---:|---:|---|
| 697 | 89 | 65 | the two `…intertwinesAlong_diamondAut…` files |
| 237 | 0 | 22 | `heckeDiamondInputsHAll` + `heckeInputsHAlong` |
| 76 | 6 | 9 | the two diamond files + `heckeDiamondInputsHAll` (`slashForm`, `qC_*`) |
| 48 | 0 | 1 | `conj_mem_Gamma1` (the X₁ file alone) |

Sub-cluster prices, if the effort is ever split:

- the H package pair (`heckeInputsHAlong` + `heckeDiamondInputsHAll`): 1,244 raw
  → 932 once-cost → 14 in port → **918 net new**;
- the diamond-lift pair (`diamondAutBar` + `diamondAutHBar`): 2,366 raw → 1,498
  once-cost → 95 in port → **1,403 net new**.

### 1.2 The definition modules, measured separately

| pin module | raw | content | decls | this cone references |
|---|---:|---:|---:|---|
| `Definitions/Def_ModularCurve_XH.lean` | 179 | 111 | 25 | the Γ_H/function-field block (lines 20–127) — `translation_mem_GammaH`, `Gamma1_le_GammaH`, `xHFunctionField(C)`, `xHTopFunctionFieldC`, `xHFunctionFieldBar`; the `JH`/`torsionGaloisRep`/`tateGaloisRep` block (127–175) is **off-path**, 0 references |
| `Definitions/Def_ModularCurve_XHHeckeOperator.lean` | 249 | 154 | 27 | the `heckeAlphaHBar`/`heckeBetaHBar`/`HeckeInputsHAlong` block; the private `coeffMap_qExpandH`-style prelude dedups to `Defs/Laurent.lean`; `heckeDivHBar`/`heckePic0HBar`/`heckeOperatorHAlong` are off-path (0 refs) |
| `Definitions/Def_ModularCurve_XHOperators.lean` | 133 | 77 | 16 | `IsDiamondAutHBar`, `diamondAutHBar`, `isDiamondAutHBar_diamondAutHBar`, `HeckeDiamondInputsHAll`; `genOpH`/`tateGenOpH`/`diamondHBar` are off-path (0 refs) |
| `Definitions/Def_ModularCurve_XHDRModelAtP.lean` | 335 | 242 | 24 | **not imported by any of the four `S_` files** — out of scope |

So the definition prerequisite is ≈342 content lines, of which a large part is
transcription over already-ported objects:

- `xHFunctionFieldC K M H := qExpFunctionFieldC K (CohCarrier.GammaH M H)` — both
  `qExpFunctionFieldC` (`ModularCurve/JqIntegralRatios.lean`, `X1/Defs.lean`) and
  `CohCarrier.GammaH` (`ModularForms/Defs/GammaH.lean`) are ported;
- `xHFunctionField := xHFunctionFieldC ℚ M H` (1 line),
  `xHTopFunctionFieldC t := qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ Gamma0 t)`.

### 1.3 Reproduction

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0                     # the 93 ready nodes
python3 frontier.py --target ModularCurve.heckeDiamondInputsHAll --no-rank --list
#   needed 1 node / 918 (itself); cone 67 nodes / 32,799 with 66 already ported
python3 port_advise.py --targets build/hH_targets.txt --json build/hH_advise.json
python3 port_plan.py --json build/hH_advise.json      # budget / blocks / siblings / layers
```

`build/hH_targets.txt` is the four-`S_`-file list. The same numbers reproduce
against the pin `aa2d8b3`.

## 2. Route audit: what the port already has

| pin item | port home | disposition |
|---|---|---|
| `AlgebraicCurve.SemilinearAut.IntertwinesAlong` | `AlgebraicCurve/Defs/Correspondence.lean:383` (and `GaloisRamification.lean`) | **reuse** — the `Along` predicate of both diamond headlines |
| `AlgebraicCurve.SemilinearAut.ofAlgAut` | `AlgebraicCurve/Defs/SemilinearAut.lean` | **reuse** |
| `qExpFunctionFieldC` | `ModularCurve/JqIntegralRatios.lean`, `X1/Defs.lean` | **reuse** — the `xHFunctionFieldC` body |
| `CohCarrier.GammaH` | `ModularForms/Defs/GammaH.lean` | **reuse** — the Γ_H argument |
| `ModularCurve.laurentBaseChange` / `_mono` / `qExpand_mem_laurentBaseChange` | `ModularCurve/Defs/Laurent.lean:252,413,422` | **reuse** — the pin's `…H` private supply prelude dedups here |
| `x1FunctionField`, `x1x0FunctionFieldC`, `x1FunctionFieldBar` | `ModularCurve/X1/Defs.lean` | **reuse** — the `Bar` (X₁) headline |
| `IsDiamondAut`, `diamondAut`, `diamondAutBar`, `heckeAlphaOneBar`, `heckeBetaOneBar` | `ModularCurve/X1/Diamond.lean`, `X1/HeckeOperator.lean` | **reuse** — the X₁ diamond vocabulary |
| `JOneES.exists_transcendental_finiteDimensional_laurentBaseChange` | `ModularCurve/X1/FunctionFieldBaseChange.lean` | **reuse** (SET-X1-B) |
| `exists_algEquiv_laurentBaseChange_cover` | `ModularCurve/X1/BaseChangeCover.lean` | **reuse** (SET-X1-C) |
| `exists_isIntegralQExp_smul_slash_of_mem_Gamma0` | `ModularForms/WeightOne/Gamma0Integral.lean` | **reuse** (SET-10) |
| `AlgebraicCurve.{hasPrincipalDivisors,finiteDimensional_adjoin}_of_transcendental`, `fundamentalIdentityAlong`, `normFormulaAlong`, `separableAlong_of_charZero` | `AlgebraicCurve/…` | **reuse** — all on the ported AC frontier |
| `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul` | `ModularForms/…` | **reuse** |

**Port-private copies to promote** (`port_advise` §1: 32 of the 36 substitutions
are port-private). These are the X₁ diamond prelude, written `private` when the X₁
topic landed; the new nodes need them again, so promote in place rather than write
a second copy (playbook §2.4):

| port home | declarations | ≈ lines |
|---|---|---:|
| `ModularCurve/X1/QExpandStretch.lean` | `isCusp_heckeDiagMatrix_smul`, `intSeriesC_expandPS`, `heckeDiagMatrix_mul_eq`, `coeff_expandPS`, `expandInt`, `expandPS` | 57 |
| `ModularCurve/X1/DiamondAut.lean` | `ratioField`, `IsRatio`, `toC_algebraMap`, `toC_injective`, `qC_one`, `qC_zero`, `qC_mul`, `qC_add`, … | 44 |
| `ModularCurve/X1/FunctionField.lean` | `intSeriesC_neg'`, `intSeriesC_add'` | 10 |

**Recorded negatives** (searched, found nothing — do not repeat):

- **`ModularCurve.HeckeInputsAlong` (`Defs/HeckeTotal.lean`) ≠ `HeckeInputsHAlong`.**
  The ported predicate is on `modularFunctionFieldFull`/`heckeAlphaBar`; the pin's
  is on `xHTopFunctionFieldC`/`heckeAlphaHBar`. Same *type* (`Prop`), different
  proposition. The new predicate must be ported from `XHHeckeOperator`.
- **`ModularCurve.modularFunctionField`/`modularFunctionFieldFull`
  (`Defs/Fields.lean`) ≠ `xHFunctionField`/`xHTopFunctionFieldC`.** The port's are
  `IntermediateField.adjoin ℚ {jq, …}`/`adjoin ℚ (divisorExpansions N)` over ℚ;
  the pin's are `qExpFunctionFieldC K (GammaH …)` with a base field `K`.
- No ported declaration states `xHFunctionFieldC`, `xHFunctionFieldBar`,
  `heckeAlphaHBar`, `heckeBetaHBar`, `diamondAutHBar`, `IsDiamondAutHBar` or
  `HeckeDiamondInputsHAll` (`grep -c` over `FLTForHuman/`: 0 each) — the XH face is new.
- `Def_ModularCurve_XHDRModelAtP.lean` (the mod-p dictionary model, 242 content)
  is not on this cone; do not pull it in.
- The `JH`/`torsionGaloisRep`/`tateGaloisRep` block of `Def_ModularCurve_XH.lean`
  and the `genOpH`/`diamondHBar`/`heckeDivHBar` blocks of the other two XH modules
  have **0 references** inside the four `S_` files — deferred with the successor
  Jacobian targets, not this topic.
- `port_advise`'s substitutions `RationalSlash` / `SlashRational` →
  `PeriodPair.DiscriminantNeZero` and `expandInt` → `ModularCurve.expandPS` are
  the usual `def : Prop` / cross-name suspects; verify each body before trusting
  it (playbook §2.4). The one trusted importable row is `SField` →
  `ModularCurve.modularFunctionField`.

## 3. Deduplication before coding

Measured copies, largest first (`port_advise` §2 reports 98 names in ≥2 target
files, ≈1,003 removable lines):

1. **The diamond-lift pair is one development (697 lines / 65 decls).** The X₁
   file (`X1DiamondLift` namespace) and the H file (`XHDiamondLift`) differ only in
   whether the Hecke maps are `heckeAlphaOneBar`/`heckeBetaOneBar` on
   `x1x0FunctionFieldC` or `heckeAlphaHBar`/`heckeBetaHBar` on `xHTopFunctionFieldC`
   — i.e. exactly the ds-head `map_ne_zero_of_tame` / `two_mul_genus…` situation.
   Write the `qC`/`slashForm`/`exists_psi`/`exists_gammas`/`cocycle` engine **once**
   in a shared module and keep the two headlines as its two consumers.
2. **`heckeInputsHAlong` ⊂ `heckeDiamondInputsHAll` (237 lines / 22 decls).** The
   bundle's Hecke field is the `heckeInputsHAlong` proof; port the seven-input
   construction once and have the bundle call it.
3. **The `slashForm`/`qC` block is shared by all three H-side files (76 lines / 9
   decls).** It is generic in `Γ`; put it in the shared engine module of item 1,
   not per-file.
4. **The X₁/port-private prelude of §2 is the same mathematics already written
   `private`.** Promote those 12 declarations in place; do not re-derive them in
   the new modules. This is the `restrictForm` pattern the X₁ topic used.
5. **The pin's `coeffMap_qExpandH`-style supply prelude dedups to
   `ModularCurve/Defs/Laurent.lean`** (`coeffMap_qExpand`, `coeffEmb_qExpand`,
   `laurentBaseChange_mono`, `qExpand_mem_laurentBaseChange`). Import, do not
   restate.
6. **Three declarations prove the same diamond existence.** The bundle's in-file
   `A2HDIH.exists_isDiamondAutHBar` (pin `S_ModularCurve_heckeDiamondInputsHAll.lean:894`),
   the definition-module lemma `isDiamondAutHBar_diamondAutHBar`
   (`Def_ModularCurve_XHOperators.lean:42`) and the separate ready node
   `exists_algEquiv_intertwinesAlong_diamondAutHBar` all establish
   `IsDiamondAutHBar M H d (diamondAutHBar M H d)` (the last with the additional
   `IntertwinesAlong` conjuncts). Port the definition-module lemma once and have
   the bundle cite it; do not transcribe the bundle's private reproof. The
   `IntertwinesAlong` node is a strictly stronger statement and stays its own
   target (§5 SET-H-B).

## 4. Module layout

A new theory directory `FLTForHuman/ModularCurve/XH/` for the X_H vocabulary and
inputs (the X₁ sibling already has `ModularCurve/X1/`; `HeckeExchange/` holds the
shared exchange layer). Namespaces stay `ModularCurve` (the pin's), so the
checker's last-name match is unchanged.

| module | pin source | role |
|---|---|---|
| `ModularCurve/XH/FunctionField.lean` | `Def_ModularCurve_XH.lean:20–127` | `xHFunctionFieldC`/`xHFunctionField`/`xHTopFunctionFieldC`/`xHFunctionFieldBar` and the Γ_H/antitone lemmas; **not** the `JH` block |
| `ModularCurve/XH/HeckeOperator.lean` | `Def_ModularCurve_XHHeckeOperator.lean` | `heckeAlphaHBar`, `heckeBetaHBar`, `HeckeBetaHDefined`, the two integrality predicates, `HeckeInputsHAlong`; **not** `heckeDivHBar`/`heckeOperatorHAlong` |
| `ModularCurve/XH/Operators.lean` | `Def_ModularCurve_XHOperators.lean` | `IsDiamondAutHBar`, `diamondAutHBar`, `isDiamondAutHBar_diamondAutHBar`, `HeckeDiamondInputsHAll`; **not** `genOpH`/`diamondHBar` |
| `ModularCurve/XH/DiamondLiftPrelude.lean` | the shared block of the two diamond `S_` files | the `qC`/`slashForm`/`exists_psi*`/`exists_gammas`/`cocycle` engine, written once |
| `ModularCurve/XH/DiamondLift.lean` | `S_…_diamondAutHBar.lean` | the H headline `exists_algEquiv_intertwinesAlong_diamondAutHBar` |
| `ModularCurve/X1/DiamondLift.lean` | `S_…_diamondAutBar.lean` | the X₁ sibling headline over the shared engine |
| `ModularCurve/XH/HeckeInputs.lean` | `S_ModularCurve_heckeInputsHAlong.lean` | the seven-input theorem `heckeInputsHAlong` |
| `ModularCurve/XH/Inputs.lean` | `S_ModularCurve_heckeDiamondInputsHAll.lean` | the capstone `heckeDiamondInputsHAll` (manager-reserved) |
| edits | `X1/DiamondAut.lean`, `X1/QExpandStretch.lean`, `X1/FunctionField.lean` | **promote** the 12 port-private prelude declarations (§2) |

The mathematics is visible as three statements plus concretisation: the X_H
function field, the diamond-lift engine, and the input bundle; the shared `Along`
predicates are the generic AC adapter underneath.

## 5. Sets and work orders

Three sets, one agent per set, reviewed between sets (playbook §3.4); order is
definitions first (playbook §3.7). The manager writes each order against the
modules that actually exist and reserves the capstone (§3.4).

**Build discipline (shared, copy into each order).** `lake env lean
-DmaxHeartbeats=4000000 -DautoImplicit=false <file>` is the edit loop and must
carry the options; `timeout 90 lake build <module>` when a file is done; **one**
`timeout 300 lake build` per set at its boundary, serialized with
`flock .lake/flt_build.lock`; never a bare whole-tree build inside a set; never
raise `maxHeartbeats`; time builds with wall **and** user/sys. Price a hub edit
with `tools/deps/build_ladder.py --edit` before touching `Defs/Laurent.lean`,
`ModularForms/`, or any other shared home (the ds-head rider paid ~14 min of
cascade for one hub declaration).

**Dedup discipline (shared).** Before writing any helper, `grep` the port for its
pin name and near-names; §2/§3 are the measured copies. Promotion of a pin-public
helper out of a port-private copy is expected and verifies through the checker's
dotted fallback; an out-of-cone byte-identical duplicate is resolved by exposing
one copy, not rewriting; count before dropping (`grep -c`).

### SET-H-A — the X_H vocabulary (DONE, 2026-10-08)

**Landed.** The three modules and 15 of the promotions are ported and
checker-verified; see
[logs/xh-hecke-set-a.md](../../logs/xh-hecke-set-a.md). Stop-early risks (a) and
(b) did not bite; (c) was avoided by transcribing the pin's `∃`-body verbatim (the
`--prop-bodies` pass diffs it identical). The `qC_*` group of §2 is **not**
promotable — see the status note above and the log §3 — so SET-H-B's engine must be
generalised over `Γ` rather than promoted.

**Scope.** The three XH definition modules, scoped to the declarations the four
`S_` files reference plus their bodies' transitive needs, and the 12 promotions.
No headline proofs. Explicitly not: the `JH`/rep block, `genOpH`/`diamondHBar`,
`heckeDivHBar`, and `Def_ModularCurve_XHDRModelAtP`.

**Deliverable.** `XH/FunctionField.lean`, `XH/HeckeOperator.lean`,
`XH/Operators.lean`, plus the `private`-drop edits. Public surface: the pin's
names; keep pin-`private` helpers `private`.

**Route.** Transcribe the definition files with the §2 reuse table applied;
`xHFunctionFieldC`/`xHTopFunctionFieldC` are thin over the ported
`qExpFunctionFieldC` + `CohCarrier.GammaH`; the `…H` supply prelude imports the
`Laurent.lean` names.

**Stop-early risks.** (a) The pin's `GammaH`-instance/coercion shape at the
`⊓ Gamma0 t` in `xHTopFunctionFieldC` — scout in `Scratch.lean` before writing.
(b) `xHFunctionFieldBar` is an `abbrev` in the pin; keep it an `abbrev` so the
`rfl` bridges unfold. (c) If the `HeckeInputsHAlong` body's `∃`-binding order
fights the port's `HeckeInputsAlong` spelling, stop and report rather than
"generalise" one into the other (§2 negative).

### SET-H-B — the diamond-lift pair, written once

**Scope.** The shared `qC`/`slashForm`/`exists_psi`/`cocycle` engine and the two
headlines `exists_algEquiv_intertwinesAlong_diamondAutHBar` (H) and
`…diamondAutBar` (X₁). Explicitly not: the input bundle.

**Deliverable.** `XH/DiamondLiftPrelude.lean`, `XH/DiamondLift.lean`,
`X1/DiamondLift.lean`.

**Route.** Transcribe the H file as the engine, parameterising the two Hecke maps
and the two function fields; the X₁ headline is the specialisation. Reuse the
promoted X₁ prelude (`X1/DiamondAut.lean`, `X1/QExpandStretch.lean`,
`X1/FunctionField.lean`) and the ported `exists_algEquiv_laurentBaseChange_cover`.
The `exists_psi_generator_eq`/`exists_gammas`/`cocycle` blocks are the API-drift
surface (`ModularForm` slash conventions, `!![…]`–`SL(2,ℤ)` coercions — the X₁
topic needed `backward.isDefEq.respectTransparency.types false` on `cocycle`).

**Stop-early risks.** The two files share a 729-line engine (ratio 0.755) but
differ in the statement shape (`d : ℕ` for X₁ vs `d : (ZMod M)ˣ` for H, different
function fields); do not force one statement through the other — generalise only
the engine, keep the two pin statements verbatim (the checker diffs text).

### SET-H-C — the Hecke inputs and the capstone

**Scope.** `heckeInputsHAlong` (the seven inputs) and the manager's capstone
`heckeDiamondInputsHAll`. The capstone and its wire test are **reserved for the
manager** (playbook §3.4); the dispatched order covers only `HeckeInputs.lean`.

**Deliverable.** `XH/HeckeInputs.lean` and `XH/Inputs.lean`; the consumer zone.

**Route.** The seven inputs are the pin's `HeckeInputsHAll` namespace block over
the ported `JOneES` base-change, `hasPrincipalDivisors_of_transcendental`,
`fundamentalIdentityAlong`, `normFormulaAlong`, `separableAlong_of_charZero`,
`exists_isIntegralQExp_smul_slash_of_mem_Gamma0` and
`qCoeff_comp_heckeDiagMatrix_smul`. The bundle then supplies the Hecke field by
`A2HDIH.heckeInputsHAlong` and the diamond field by its own in-file
`A2HDIH.exists_isDiamondAutHBar` (pin `S_…:894`); it does **not** call
`XHOperators.isDiamondAutHBar_diamondAutHBar`, and the two should be reconciled at
port time (§3 item 6).

**Verification.** `#print axioms ModularCurve.heckeDiamondInputsHAll` and every
headline `[propext, Classical.choice, Quot.sound]`; the capstone compiles first
try (the review instrument); a consumer zone composing `heckeDiamondInputsHAll 1`
into a concrete `HeckeInputsHAlong (AlgebraicClosure ℚ) 1 ⊥ 2` and the diamond
branch at `(M, d) = (1, …)` producing a real `AlgEquiv` + `IsDiamondAutHBar`; no
`#check`, no `sorry`, every hypothesis discharged from ported material.

## 6. Budget and risk register

**Correction ledger, content lines.**

| row | content |
|---|---:|
| net new math lines (four-file `port_plan`) | 2,319 |
| + XH definitions (§1.2, minus reuse) | ≈340 |
| **estimate** | **≈2,660** |
| range (written ÷ content 1.0–1.2; AC/MC/X₁ calibration) | **2,400–3,100** |

The `--ready` reading alone (four nodes, 3,610 raw, no definitions) would have
under-budgeted by the ≈340 definition lines and over-budgeted the 1,087 duplicate
lines; the two corrections roughly cancel, which is why §1.1 and §1.2 must be
read together.

**Named shape risks, in the order they will bite.**

1. **The `--ready` definition gap.** The frontier calls the nodes terminal while
   the XH modules are unported. Mitigation: SET-H-A first; re-run
   `frontier.py --target ModularCurve.heckeDiamondInputsHAll --no-rank --list`
   after it lands and reconcile. *Open.*
2. **The `cocycle`/`!![…]`–`SL(2,ℤ)` coercion.** The X₁ capstone needed
   `backward.isDefEq.respectTransparency.types false`; the H engine will too.
   Mitigation: transcribe the pin's `set_option`, do not restructure. *Predicted
   medium.*
3. **`HeckeInputsHAlong` vs `HeckeInputsAlong`.** A careless reuse makes the
   statement elaborate while the checker reports `MISMATCH`. Mitigation: the §2
   negative; transcribe the pin's body. *Predicted low once the order is read.*
4. **Promotion collateral.** Dropping `private` on the X₁ prelude can change the
   checker's `promoted`/`renamed` counts and can shadow a private copy elsewhere.
   Mitigation: promote one at a time, re-run the checker, reconcile every delta
   against the promoted surface. *Predicted low.*
5. **Hub cascades.** Any edit to `Defs/Laurent.lean` or `ModularForms/` costs the
   ds-head-rider cascade. Mitigation: none should be needed (all reuse is import);
   if one is, price it first. *Predicted low.*
6. **Instance diamonds at `xHFunctionFieldBar`.** The X₁ bar hit these; the H bar
   is likely to as well (`instance-friction.md`). Mitigation: explicit local
   instances, no `synthInstance.maxHeartbeats` bumps. *Predicted low.*

**Predicted non-events** (do not budget again): the `Along` predicates, the
`SemilinearAut` API, the AC `transcendental`/`Along` lemmas, the X₁ diamond
vocabulary and the SET-10 slash inputs are all ported; `qExpFunctionFieldC` and
`CohCarrier.GammaH` are ported, so the XH function field is transcription.

## 7. Faithfulness and verification recipe (per set)

1. **Checker.** Append the set's `Theorems/Thm_<stem>.lean` wrappers to `SOURCES`
   last and the new modules to `PORT_FILES`; run
   `python3 spec/check_flt_statements.py`. Target `0 mismatched / 0 missing`.
   Baseline today: `6315 (312 promoted, 83 renamed), 0 mismatched, 0 missing,
   36 own (6351 checked)`. Verify the checker with a one-token mutation (expect
   exactly one more `mismatched`) and revert.
2. **Consumer.** Extend `spec/ModularCurveHeckeConsumer.lean` (or add
   `spec/XHConsumer.lean`); the error count is the deliverable; every zone must
   delete-fail.
3. **Axioms.** `#print axioms` on the four headlines; expect
   `[propext, Classical.choice, Quot.sound]`.
4. **Build ladder.** Per §5; one flocked wave build at the set boundary, whole-tree
   at the milestone.
5. **Coverage.** Re-run §1.3 and record the remaining figure moving per set;
   reconcile every drop against the ported surface.

## 8. What this topic is not

- Not the X₁ Hecke/diamond inputs (`ModularCurve.heckeDiamondInputsAll`); that is
  [TOPIC-x1-hecke-diamond-inputs.md](TOPIC-x1-hecke-diamond-inputs.md), COMPLETE,
  and disjoint — except for the one X₁ diamond-lift node
  `exists_algEquiv_intertwinesAlong_diamondAutBar` that this cluster's engine
  subsumes (§3 item 1).
- Not the X_H Jacobian/Tate-representation layer (`JH`, `torsionGaloisRep`,
  `tateGaloisRep`, `genOpH`, `diamondHBar`, `heckeDivHBar`,
  `Def_ModularCurve_XHDRModelAtP`); those are off this cone (0 references) and
  belong to the successor Jacobian topics.
- Not the `Pic0` action/torsion mini-set carried in
  [CARRY-FORWARD.md](../../CARRY-FORWARD.md) from the X₁ effort.
- Not the `CuspForm` nebentypus/Fricke, `WeierstrassCurve` char-2/3 or
  `CohCarrier` silos also exposed as ready by the same frontier command; each is a
  separate topic.
- Not the level-H Hecke *operator* layer (`heckeOperatorsCommuteBar`, m1–m13) or
  `HeckeInputsAlong`; those are ported and different objects (§2 negative).
