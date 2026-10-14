# WORKORDER-T3 — the Fujisaki compactness twins (tier 3)

**Status: landed 2026-10-13** — results in §9.

Read [TOPIC-compactness-twins.md](TOPIC-compactness-twins.md) first; §1 carries the
mathematics, §2 the twin measurement, §3 the landed definition gate, §4 the port structure
and §5 the recorded `ValuationOrd` negative. This order is the one engine module and nothing
else; the manager writes the façade.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

## 1. Scope

Write **one tier-3 engine module**:

`FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiCompact.lean` — transcribed from
**file A** (`P2M/Sol/S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean`,
3,683 lines / 285 declarations) **whole, except its final `theorem solution`**. File A is a
superset of file B (`…compactSpace_normOneIdeleClass.lean`, 3,615 / 284): file B carries no
declaration file A lacks, and its headline is a one-line call to the shared
`M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl` which is inside file A's text.
So there is no second source to read, and **no declaration is transcribed from file B**.

Budget: **1,023 net new lines** for the pair (949 + 1,017 separately — porting them apart is
the mistake this order avoids), of which 2,638 lines of the 3,664-line shared block are
already in the port.

**Explicitly not this order.** The tier-1 façade
(`FLTForHuman/NumberTheory/NumberField/TateGlobalCompactness.lean`), the `SOURCES`/`PORT_FILES`
wiring, `spec/UNWIRED-PUBLIC.md`, `spec/check_flt_statements.py`, the other rows listed in the
topic's §5.5, and every pin declaration the plan marks as already in the port. No promotion, no
edit to any existing module.

## 2. What is already in the port and must be imported, never re-transcribed

`port_advise` reports 364 substitutions / 2,638 lines over the pair, all **tier 3**
(importable, registered in `spec/UNWIRED-PUBLIC.md`, statement-unchecked), homed in the T1
development:

| port module | substitutions |
|---|---:|
| `NumberField/TateGlobal/Coordinates.lean` | 106 |
| `NumberField/TateGlobal/Ideles.lean` | 72 |
| `NumberField/TateGlobal/FiniteSlab.lean` | 60 |
| `NumberField/TateGlobal/ArchSlab.lean` | 54 |
| `NumberField/TateGlobal/ArchMulHaar.lean` | 20 |
| `NumberField/TateGlobal/ValuedOrdBridge.lean` | 12 |
| `NumberField/TateGlobal/ZetaIntegrand.lean` | 8 |
| `NumberField/TateGlobal/DistribHaarChar.lean` | 8 |
| `NumberField/TateGlobal/LocalZetaUnramified.lean` | 6 |
| `NumberField/TateGlobal/ReferenceMeasure.lean` | 4 |
| `NumberField/TateGlobal/{MulHaar, NormIntegrable, IntLocalIntegrability}.lean` | 2 each |
| others | the remainder |

Read the full table in `build/compactness_advise.json` (regenerate with §5 below) and import
the homes your module actually needs; the T1 modules are the natural import set.

**The 8 suspect substitutions are false positives — do not apply them.** `archBox` →
`TateGlobal.archSlab`, `box` → `TateGlobal.slab`, `SUnits`/`DeepUnits` →
`FLTForHuman.Elliptic.Univ.Poly`: the parser's type-only `def` artifact, the same rows the T1
topic recorded.

## 3. Do not transcribe `M4aLocalCFT.ValuationOrd`, and do not promote it

Both pin files re-carry the block at pin lines **85–284** (`namespace M4aLocalCFT` /
`namespace ValuationOrd` … `end ValuationOrd`). Its 11 declarations have statement-identical
copies in the port only as **`private`** declarations in
`NumberField/TateGlobal/Ideles.lean` (`NumberField.TateGlobal.ValuationOrd.*`), because the T1
round kept that block private. This is **not** a promotion case:

*Verified mechanically (the manager ran it, and it holds in both files):* every occurrence of
`ordA`, `ordZ`, `ordA_span`, `ordA_mul`, `ordA_unique`, `ordZ_spec`, `coe_mk_ne_zero`,
`exists_rep`, `exists_span_eq_pow`, `pow_maximalIdeal_ne_of_lt`,
`pow_maximalIdeal_injective` lies between lines **93 and 248**, i.e. inside the block itself,
and **nothing after line 284 names any of them**. No new proof term reaches a port-`private`
name, so the block is substituted by its existing home and **is not transcribed**.

```bash
# the check, if you want to re-run it
f=~/proj/fermats-last-theorem/P2M/Sol/S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean
for n in ordA ordZ ordA_span ordA_mul ordA_unique ordZ_spec coe_mk_ne_zero exists_rep \
         exists_span_eq_pow pow_maximalIdeal_ne_of_lt pow_maximalIdeal_injective; do
  printf '%-30s: ' "$n"; grep -n "\b$n\b" $f | cut -d: -f1 | tr '\n' ' '; echo; done
```

**If your build nevertheless needs one of those names** — i.e. a *new* declaration's proof
term reaches it — re-derive the pin's proof `private` in your module with the pin's statement
verbatim, and **report it**. Do not promote, and do not edit `Ideles.lean`. The manager has the
price of that wave on file (27 modules / 8,389 lines ≈ 110 s) and will decide.

## 4. Transcription rules

* Keep the pin's namespaces (`M4aLocalCFT`, `M4aLocalCFT.ValuationOrd` — not transcribed —
`M4aLocalCFT.FujisakiR1`, `M4aLocalCFT.FujisakiC2c`, `NumberField.TateGlobal`, …), declaration
names and statements **verbatim**. Drop the outer `P2MW.S_…` namespace and every `p2m_*` line;
keep `set_option autoImplicit false`, `noncomputable section` and the pin's `open` lines.
* Replace the pin's bare `import Mathlib` with the specific imports actually used, and
  `import Definitions.Def_NumberField_Completion_Finite` by
  `import FLTForHuman.NumberTheory.NumberField.Completion.Finite` (the manager wired that node:
  the pair uses `NumberField.isCompactAdicCompletionIntegers` at the pin's lines 595 and 638).
* `import Definitions.Def_M4aHerbrand_IdeleClassVocab` → the port's
  `FLTForHuman.NumberTheory.M4aHerbrand.IdeleClassVocab`, and
  `import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap` →
  `FLTForHuman.NumberTheory.AdelicModulus` (the landed façade).
* Every transcribed declaration carries, immediately above it (above any `@[...]`), a
  provenance comment `-- pin: <name> (<S_ basename>:<line>)`; `unwired_register.py` reads it.
* Do **not** transcribe the pin's final `theorem solution` — the façade owns both headlines.
* Replace the pin's `attribute [-instance]` / `p2m_export` preludes with specific imports; the
  port does not carry them.

## 5. Route, mathlib map, and stop conditions

* **Statements are the pin's**; a documented `v4.34.0` drift is the only permitted difference.
  Proofs are adapted freely. **If a proof needs a statement to change, stop and report.**
* Expected drift surface: `IsCompact`/`CompactSpace` on `adicCompletionIntegers` (wired from
  `Completion/Finite.lean`), `Valued`/`Valued.integer` API, `FractionalIdeal`/`Ideal` class-group
  arithmetic, `IsDedekindDomain.HeightOneSpectrum` support lemmas, `finprod`/`Finset` index
  manipulations on `principalIdeles`/`normOneIdeles`, and `Units`/`Subgroup.subgroupOf` quotient
  lemmas. The known deprecations in this tree: `mul_le_one₀`,
  `mul_lt_one_of_nonneg_of_lt_one_{left,right}`, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`,
  `zero_le'` → `zero_le`.
* **No new helpers beyond the pin's.** If a proof needs glue the pin does not have, re-derive
  it `private` in this module and report it. **No promotion and no edit to any existing
  module.** If you believe a promotion is genuinely required, **stop and report** the
  declaration, host and `python3 tools/deps/build_ladder.py --edit <host>` price — the manager
  decides.
* **Stop and report** if file A and file B turn out to differ in a declaration's *statement*
  (they should not: the normalized diff is namespace-stem and cap only), or if the block cannot
  be kept self-contained against the T1 modules + `Completion/Finite.lean` + mathlib.

## 6. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the
> low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with
> `flock` and bounded with `timeout`. Per wave, build only the wave's affected targets —
> **never a bare whole-tree `lake build`**. A whole-tree build happens once, at the session's
> end, and only with the user's permission.

Concretely: iterate at the low cap until the module is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.NumberTheory.NumberField.TateGlobal.FujisakiCompact`.
Build only this module and its dependencies.

**Build-time blow-up protocol.** The named risks are `count_fracIdealProd` and the ideal-class
count around it. If one exceeds the low cap, diagnose with `set_option diagnostics true` /
`trace.Meta.synthInstance true` in a scratch copy (never commit it), fix the inference, and
re-run. Report the declaration and the fix.

## 7. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on `FujisakiCompact.lean` | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock … lake build FLTForHuman.NumberTheory.NumberField.TateGlobal.FujisakiCompact` | green; record jobs and wall/user time |
| name parity against `port_advise` on file A | the transcribable names present once each; the 364 substituted names **absent**; `M4aLocalCFT.ValuationOrd`'s 11 names **absent**; nothing invented |
| both `_impl` kernels | `M4aLocalCFT.FujisakiR1.exists_isCompact_impl` and `M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl` public with the pin's statements |
| `#print axioms` on both kernels | `[propext, Classical.choice, Quot.sound]` |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

Do **not** run `spec/check_flt_statements.py` and do **not** edit the register. No wiring for
this order: the engine is tier 3.

## 8. Report shape

1. The module path, final line count, and the pin section → module map as built.
2. Declaration counts, public / `private`; confirm §3's block is absent and §7's two kernels
   are public.
3. Every pin declaration you substituted rather than transcribed, and every name you had to
   qualify.
4. Tier-0 and tier-1 results, with jobs and wall/user/sys times.
5. Every build-time blow-up, the declaration, the diagnosis, and the fix.
6. Any statement that could not be transcribed verbatim, and why (stop condition).
7. Any helper re-derived `private`, and any promotion you stopped on.

## 9. Results as landed (2026-10-13)

| | |
|---|---|
| engine | `FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiCompact.lean` — **966 lines, 95 declarations: 2 public, 93 `private`**, tier 3 |
| tier 0 | exit 0, **0 warnings**, no forbidden token |
| tier 1 | 3,789 jobs, wall 8.25 s / user 10.36 s / sys 3.41 s |
| façade | `FLTForHuman/NumberTheory/NumberField/TateGlobalCompactness.lean` — 2 headlines, tier 1 |
| checker | **9582 → 9584 identical (+2)**, 0 mismatched / 0 missing / 38 own (9,622 checked) |
| mutation | `principalIdeles` → `principalIdeals` on the class-group headline → exactly **1 mismatched** (9,583), reverted |
| axioms | both headlines `[propext, Classical.choice, Quot.sound]` |
| register | regenerated: 84 modules / 2,057 public / 1,769 with a pin original (`Completion/Finite.lean` de-listed −5, this engine +2) |
| existing modules edited | **none** — no promotion, no hub wave, no `Ideles.lean` edit |

**The landed headlines** (both stated from their wrappers verbatim, which is why the checker
took them on the first run):

* `NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul`
  ← `M4aLocalCFT.FujisakiR1.exists_isCompact_impl`;
* `NumberField.TateGlobal.compactSpace_normOneIdeleClass`
  ← `M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl`.

**The `ValuationOrd` decision held.** The engine contains no `M4aLocalCFT.ValuationOrd`
namespace; the only occurrence of the name in a proof is the port-public
`NumberField.TateGlobal.ValuationOrd.ord`, exactly as §3 predicted. The 11 block names are
absent, and no promotion was owed or stopped on.

**Tool artifact: a self-reference hazard in re-running `port_advise` after a module lands.**
The worker reported ten declarations (`fracIdealProd_add`, `fracIdealProdHom`,
`unitElem_mem_subgroupOf`, `image_mk_fiberCompact`, `compactSpace_fiberGroup_quot`, `inclHom`,
`continuous_inclHom`, `fiberMap`, `continuous_fiberMap`, `isCompact_range_fiberMap`) as
"`in_port: true` though absent from the port", and read it as a `find_stmt` type-only
false positive. It is not. Re-running `port_advise` on file A **after** the engine was written,
the tool reports each of them as a substitution whose `port` field is
`FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiCompact.lean` — that is, the worker's
own transcription of the pin declaration. File A alone goes from **178 to 272** reported
substitutions once its own engine exists.

Two consequences, both recorded rather than fixed here:

1. The worker's *transcription* was right: at the time it scoped, `build/compactness_advise.json`
   (generated before the module existed) correctly listed them as new, and the port had no
   declaration of any of those names — verified by `grep` over `FLTForHuman` excluding the new
   module. The engine is 95 declarations, not the 85 a naive reading of a post-hoc advise run
   would suggest.
2. **Name-parity checks must use the advise file generated *before* the module is written, or
   exclude the new module.** A worker that re-runs the tool after each edit loop iteration — as
   a literal reading of this order's §7 invites — will see its own output as pre-existing
   mathematics and may delete real declarations. Worth a line in the tool's own README or in
   the playbook's §3.5; the manager has added it to the topic's recorded negatives.

**Process note.** The two `solution`s were not transcribed; the façade owns them, as §4
required. The engine keeps the pin's `private` on 93 of its 95 declarations and promotes only
the two kernels the façade calls — the §4(b) promotion rule applied inside a new module, not a
hub edit.
