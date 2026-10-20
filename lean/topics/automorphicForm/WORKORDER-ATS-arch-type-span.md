# WORKORDER-ATS — the finite-dimensional `K`-span of right translates in finitely many archimedean types

**Status (closed 2026-10-20): landed and reviewed green.** One set, one module, **one public
headline**, and the pin's whole generic prelude **imported, not re-proved**. Measured:
`FLTForHuman/AutomorphicForm/Adelic/Cusp/ArchTypeSpan.lean`, **125 lines**, **1 statement-checked
declaration**; `spec/check_port.py` **1 ok / 0 mismatch / 0 missing / 0 own / 0 kw**; tier-1 build
3,838 jobs, 3.3 s, **0 warnings**; axioms `[propext, Classical.choice, Quot.sound]`; the frontier
reads `needed 0` for the node. The port's only new mathematics is the pin's 59-line adelic
instantiation `kspan_main` (kept `private`, as the pin keeps it) and the headline; **31 of the 39
pin declarations (696 of 786 declaration lines) are byte-identical to the port's shared `Q09`
engine** in `RepTheory/TypeReproducer.lean` (tier 3, registered) and are imported.

The row is
`AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`,
the 813-line leaf
`P2M/Sol/S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt.lean`
(pinned `aa2d8b3`). Under `frontier.py --ds --include-leaves --rank-by silo` it was the demand's
**rank #2 high-impact leaf** (813 silo lines; behind only `M4aTorus.completedRayL_fe`), with
`used_by` 3 in the cone / 9 in the project and **`cites 0`** — a graph leaf, so `--ready` and
`--hops` hide it and only `--include-leaves` (or a direct query) surfaces it.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the per-module protocol (§6 of the column note) — a `spec-pin:` header and
`spec/check_port.py`, no in-source per-declaration marker.

## 1. Scope

The node is one archimedean `K`-finiteness statement. At one infinite place `w`, a vector `φ` of
the supremum of finitely many archimedean type submodules `archTypeSubmoduleAt F w (ρs i)` spans,
under right translation by the row-isometry group `rowIsometrySubgroup₀ w.Completion`, a
**finite-dimensional** space `S` that is **stable** under those translations and still **inside**
the same supremum. Three conjuncts, one story: `K`-finiteness and the cut survive the passage to
the translate span.

The pin's `S_` file is two parts:

| block | pin lines | the mathematics | port |
|---|---|---|---|
| `R5bE` generic engine | 22–736 | the type-piece transport: coset coordinates, the product representation `piRep`, `typeSubmodule_piRep_le`, the finite-sum extraction `exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule`, the coefficient maps and the dual (`coeffFun`/`dualCoeffFun`/`transRep`, `dualCoeffFun_transRep_mem_iSup`), the right-translate span `spanTranslates` with `finiteDimensional_spanTranslates`, and the multi-place envelope `exists_finiteDimensional_stable` — 37 declarations, no adèles, no `GL₂` | **imported** from `Q09` (§2) |
| `R5bE.kspan_main` | 738–790 | the instantiation: `ι := rowIsometryInclAt₀ F w`, `ρ i := (ρs i).ρ`, the span `S` against `spanTranslates ι (span {φ})`, the three conjuncts | **transcribed** (59 lines) |
| `solution` | 792–813 | the headline | **transcribed** (the statement is the wrapper's verbatim) |

**Not this set:** the other eight consumers of the row (§7); any edit to an existing module; any
new definition module (§3); the pin's `p2m_export`/`#print axioms` plumbing and its
`attribute [local instance] glBorel` prelude.

## 2. Measurement — the pin is already in the port, 31 declarations of it

`tools/deps/port_advise.py --target … --json build/kspan_advise.json`,
`port_plan.py --json build/kspan_advise.json`, on the tree the previous landing left:

| quantity | value |
|---|---:|
| pin `S_` lines | 813 |
| declaration lines | 786 |
| boilerplate (imports/attrs/`p2m`) | 27 |
| distinct declaration groups | 39 (38 in the `S_` file + the wrapper's) |
| duplicate copies removable in-file | **0** |
| once-cost after dedup | 786 |
| already in the port (vetted) | **696** (31 declarations) |
| of those, tier 1 / tier 3 | 0 / **696** |
| substitutions | **31 trusted / 0 suspect** |
| **net new math lines** | **90** |

All 31 are **byte-identical**, not shape-tier: `0 identical up to binder spelling`, `0 suspect`.
The home is `FLTForHuman/RepTheory/TypeReproducer.lean`, namespace `Q09`, which was itself homed
from the **archTestFactor silo** — a *different* pin `S_` file
(`S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean`).
So this landing is not a within-silo dedup; it is a **cross-silo reuse**: one engine, two pin
silos, 1,380 port lines serving both. `port_advise`'s "one target copy and a duplicate elsewhere
in the pool" list is exactly that pair.

The six rows the substitution table does not list (`piRep_apply`, `coeffFun_apply`,
`dualCoeffFun_apply`, `rt`, `rt_apply`, `rtLinear_apply`) are the `:= rfl` one-liners; they are in
`Q09` too, at the same names, and are part of the 696 lines' home.

## 3. Pre-round — no definition gate is owed, and the reason is a hand-walk

The pin `S_` file imports two `Definitions/` modules; §4(a) of the column note requires each to be
walked declaration by declaration, not trusted through the import block.

* `Def_AutomorphicForm_FactorizableTestFn` — **ported**, `AutomorphicForm/Adelic/FactorizableTestFn.lean`
  (99 lines, legacy-listed).
* `Def_AutomorphicForm_CuspidalSpectrumCarrier` — **not ported** (288 lines / 31 declarations); it is
  still the gate of the deferred centre-cut slab bound, [CARRY-FORWARD.md](../../CARRY-FORWARD.md).

The walk: `fltdata.proof_defs` names both **modules** (`pd` is module-granular), so the graph cannot
settle it; a declaration-level `grep` over the `S_` file can and does. Not one of the 31
`CuspidalSpectrumCarrier` names occurs in it (`detNormSlab`, `IsSlabFundamentalDomain`, `fdPins`,
`Carrier`, `memberSubmodule`, `cuspMemberSubmodule`, `pairing`, `IsLift`, `flat`, …), and neither
does any `FactorizableTestFn`/`IsArchBiFinite`/`rightConv`/`IsSmoothCuspAutomorphicFnAt` name —
all zero. The leaf is stated and proved entirely over the type-piece API that
`AutomorphicForm/Adelic/IsotypicCuspSpace.lean` already homes (`IsRightEquivariant`,
`typeSubmodule`, `mem_typeSubmodule_of_isRightEquivariant`, `ArchRepAt`, `rowIsometryInclAt₀`,
`archTypeSubmoduleAt`) plus `rightTranslate`/`rightRegular` from
`AutomorphicForm/Adelic/Cusp/Constituent.lean`.

**Consequence:** `Def_AutomorphicForm_CuspidalSpectrumCarrier` is **not** homed by this set; it is
not on this leaf's path, and homing 288 lines of slab/carrier definitions for a leaf that never
mentions them would be the partial-port error §4(a) warns about in reverse. It stays recorded as
the centre-cut slab bound's gate.

## 4. Source and deliverable

Statements come from the pin `Theorems/` wrapper; the proof from the `P2M/Sol/S_` file:

* statement — `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt.lean`
* proof — `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt.lean`

The wrapper is one `p2m_exact_reverting` line and is the authority for the statement, never the
`S_` file's `solution` spelling. It is copied verbatim — binders, `let S`, the `↥S` coercion, the
`ρs` binder name — because the checker's contract is the statement text, not the name.

**Deliverable:** `FLTForHuman/AutomorphicForm/Adelic/Cusp/ArchTypeSpan.lean`, **125 lines**:

* `import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent` (right translation, `rightRegular`,
  and through it the definition layer) + `import FLTForHuman.RepTheory.TypeReproducer` (the `Q09`
  engine);
* `private theorem kspan_main` — the pin's 59-line instantiation, transcribed **byte-identically**
  (a `diff` of the pin's `R5bE.kspan_main` body against the port's shows no changed line; only the
  enclosing namespace and the `open Q09` differ);
* `theorem AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`
  — the headline, proved by `kspan_main F w m ρs φ hφ`.

Public: the headline. Private: `kspan_main`. No tier-3 module is added; nothing is registered.

## 5. Route, and the recorded negatives

* **`open Q09`** rather than re-qualifying every engine name. The pin's chapter opens
  `AutomorphicForm` and writes the engine names bare inside `R5bE`; the port's engine lives in
  `Q09` (the pin's own private-name mangling, kept by the archTestFactor landing), so the
  transcription only changes the resolution, not a single token of the proof.
* **`hcut : (⨆ i, archTypeSubmoduleAt F w (ρs i)) = ⨆ i, typeSubmodule ι (ρ i)` is `rfl`.** This is
  the one place the port must agree with the pin definitionally: `archTypeSubmoduleAt` is
  *defined* as `typeSubmodule (rowIsometryInclAt₀ F w) τ.ρ`, `ι` is a `let` for that homomorphism
  and `ρ i` is a `let` for `(ρs i).ρ`. The pin's `rfl` survives the port's `IsotypicCuspSpace` —
  recorded because a future re-homing of `archTypeSubmoduleAt` (e.g. through an unfolded wrapper)
  would break it and silently turn a definitional equality into a proof obligation.
* **`rightTranslate_rightTranslate` / `_add` / `_smul` / `_zero` and `rightRegular`** are the port's
  `Constituent.lean` copies at the pin's names; the last conjunct's `Submodule.map (rightRegular F
  (ι k))` argument shape is the pin's, and `rt_mem_typeSubmodule_self` consumes it directly.
* **No promotion is owed.** Every `Q09` declaration the proof reaches is already public and
  registered tier 3; the pin declares them `private` and the port promoted them whole when the
  archTestFactor silo landed. This is the one reuse shape in which *nothing* has to move.
* **`kspan_main` stays `private`.** It is an instantiation, not a theorem another theory will
  state; the pin keeps it `private` in `R5bE`, and the port's `Q09` engine is the reusable half.
  Making it public would add a second public surface with no consumer.
* **The wrapper's prelude is not copied.** The wrapper opens five namespaces and sets
  `attribute [local instance] NumberField.AdelicHaar.glBorel`; neither the statement nor the proof
  mentions a measure, so the module opens `IsDedekindDomain NumberField` only. `autoImplicit false`
  is set, as everywhere.
* **One narrow `set_option linter.style.haveILetI false in`**, on `kspan_main` only. Its two
  `haveI`s are load-bearing `FiniteDimensional` instance bindings (the singleton span, and
  `finiteDimensional_spanTranslates`'s conclusion); the linter reads them as proofs.
  `TypeReproducer.lean` carries the same narrow form at exactly its two analogous sites. No
  file-wide suppression, no other linter option.
* **No `maxHeartbeats` raise.** The transcription elaborates under the set's 200,000 cap; the pin
  sets none on this file.

## 6. Build discipline (verbatim)

```
tier 0  edit loop    timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>
tier 1  module done  flock .lake/flt_build.lock timeout 300 lake build <module>
tier 2  wave         only when a host module is edited — not this set
tier 3  milestone    no whole-tree build without the user's permission
```

One `lake build` at a time; the edit loop writes no `.olean`; a declaration over the 200k cap is an
instance-inference defect to fix, never a cap to raise.

## 7. Successors this landing unblocks

The row's nine project consumers; the one this landing makes **ready** is

`AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule` — the same principle one
step up, at the whole archimedean cut: the span of the archimedean translates of a cut vector is
finite-dimensional and stable. It was priced at 997 silo lines with 813 of them this leaf; after
the landing `frontier.py` reads its cone at **184 lines, all its own**, and it appears on the
`--ready` shelf (`used_by` 6 in the cone / 7 in the project). The other eight stay blocked on
their own premises:

* `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` — cone 1,182 /
  needed 3 nodes / 369 lines;
* `exists_eq_sum_su2String_highestWeight_of_mem_cut_of_isComplex`,
  `exists_forall_eq_sum_hasArchCharacterAtZero_mem_span_rightTranslate_of_mem_archCutSubmodule`,
  `exists_forall_eq_sum_hasCircleWeightAt_mem_span_rightTranslate_of_mem_archCutSubmodule_of_isArchSmoothAtComplex`,
  `convOp_principalLevel_invariant_and_mem_archCutSubmodule_and_isArchKFinite_of_isAutomorphicFnAt`,
  `isArchKFinite_rightConv_of_isInducedSection_of_comp_inv_mem_archCutSubmodule`,
  `exists_finiteDimensional_forall_rightConv_mul_mem_of_isInducedSection_of_comp_inv_mem_archCutSubmodule`,
  `integral_maximalCompact_mul_sum_integral_sum_inner_mul_axis_continuation_eq_self_of_levelTypeAverage_eq_self`.

## 8. Verification (measured on the tree this set leaves)

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/Cusp/ArchTypeSpan.lean
#   ArchTypeSpan.lean  [ok]  1 ok, 0 mismatch, 0 missing, 0 own, 0 kw
python3 spec/check_port.py --all
#   1816 ok, 0 mismatch, 0 missing, 4 own, 0 kw — 45 module(s), 584 exempt (PORT_FILES)
flock .lake/flt_build.lock timeout 300 lake build \
  FLTForHuman.AutomorphicForm.Adelic.Cusp.ArchTypeSpan
#   ✔ [3838/3838] Built …ArchTypeSpan (3.3s) — Build completed successfully (3838 jobs)
python3 spec/unwired_register.py --check            # register is current
```

plus the `#print axioms` probe (below), the `grep` sweep over the module
(`sorry|admit|^axiom|native_decide|import Mathlib|maxHeartbeats`: nothing) and `git status`
showing only the one new file.

`spec/old_check_stmts.py` is **not** run: it is the frozen registry of the grandfathered
`PORT_FILES`/`SOURCES` set, and `spec/check_port.py` is the checker. Nothing was appended to its
lists.

## 9. Report shape

What a review looked for, in order: the statement is the wrapper's text (checker `ok`, no marker);
the module adds no public declaration beyond the headline; the private helper is the pin's, with
the `rfl` definitional bridge intact; the Q09 imports are the 31 substituted declarations and
nothing is re-proved; the edit loop is silent; tier 1 is green with 0 warnings; the axioms are the
three; the register and the frontier agree that the node is ported.
