# WORKORDER-DC1 — the archimedean dual cut, and its right-convolution vanishing

**Status: definition layer landed 2026-10-25; proof bodies dispatched.** Pure addition of three
modules (plus one consumer zone); the rename of the two landed cut modules below is the
manager's, done with the definition layer. The definitions, the module boundaries, the names and
the `spec-pin:` wires are **fixed** — do not re-cut them. What remains is proof bodies: §2 lists
them with their pin lines.

## 0. The set

| node | pin `S_` lines | decls | `needed` |
|---|---:|---:|---:|
| `AutomorphicForm.exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq` | 1,376 | 93 | **3** |
| `AutomorphicForm.le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule` | 153 | 3 | 1 |
| `AutomorphicForm.le_iSup_typeSubmodule_dual_of_invariant_pairing` | 227 | 3 | 1 |

**What the headline says.** Fix a number field `F`, an archimedean type family `tys`, a continuous
`y` in the *cut* `archCutSubmodule F tys`, and a continuous compactly supported `f` whose right
translates under the archimedean compact group span a finite-dimensional space. Then some `f'` in
that span lies in the *dual* cut `archDualCutSubmodule F tys` and represents `y` the same way:
`rightConv F y f' = rightConv F y f`.

**The chain** (the pin's `PartC3`): the dual cut inside the carrier `cutDc` is
`ρc`-invariant, so it has a type-algebra module `cutDM`; the isotypic
components split into `goodComponentsD` (inside the dual cut) and its complement, with
`IsCompl` and `CAD ≤ cutDM`; the hard inclusion
`cutDM ≤ CAD` is the first premise node applied at
`rowIsometryInclAt₀ F w`; an irreducible component of the complement pairs to zero against `y`
(the second premise node plus a non-degenerate invariant pairing); and the split of `f`'s
class in the type algebra assembles the result.

## 1. Cone, readiness, budget — measured

* **Frontier.** 3 needed nodes / **1,756 raw `S_` lines**; the headline has six premises, four
  already in the port's frontier and two unported.
* **Reuse — `port_advise`:** 102 declarations; **47 / 671 lines are already in the port,
  byte-identically**. The five `def`s it also reports as substitutions (`cutDc`, `cutDM`,
  `goodComponentsD`, `CAD`, `CBD`) are false positives — the parser compares a `def`'s bare type
  and all five have type `Submodule …`; they are new mathematics and were read from the pin.
* **Budget — `port_plan`:** 1,756 raw → 1,700 declaration lines → −34 duplicate copies → −56
  boilerplate → 1,666 once-cost → −671 in the port = **995 net new**, **+14** for the five
  mis-priced defs = **≈1,009**. Written ÷ content 1.0–1.3 → **≈900–1,000 lines** of which **≈285
  are landed** (16 declarations of (c), 4 of (a)); the rest is proof body.
* **No definition gate**; the two premise nodes are layer 0 and the headline layer 1, so (b) is
  written before (c)'s inclusion can be proved.
* **Dedup:** the two premise files copy a 30-line private helper and a 4-line private abbreviation
  (`TW`) byte-identically — write each **once**, private, in (b).

## 2. What remains

### (a) `FLTForHuman/RepresentationTheory/SubrepresentationRestriction.lean` — 3 proofs

Landed: `restrictRep`, `restrictRep_apply_coe`, `restrictInvt`, `restrictInvt_apply_coe`
(checker `4 ok`). Add, at the pin's statements (`S_ …` below is the dual-cut `S_` file):

| declaration | pin line | note |
|---|---:|---|
| `coe_asAlgebraHom_restrictRep` | :839 | `MonoidAlgebra.induction_on`; the pin guards it with `set_option backward.isDefEq.respectTransparency false` |
| `exists_linearEquiv_asModule_mapSubmodule` | :851 | the `asModule` identity; also guarded in the pin |
| `isIrreducible_of_isSimpleModule` | :882 | `Representation.irreducible_iff_isSimpleModule_asModule` + `IsSimpleModule.congr`; also guarded |

**Do not carry `set_option backward.isDefEq.respectTransparency false`.** If a step only fires
with it, restructure (name the intermediate at its explicit term, or state the projection lemma
in element form); if it still does not, stop and report. Expected checker: `7 ok`.

### (b) `FLTForHuman/RepTheory/TypeInvariance.lean` — new module, 2 public + 2 private

Both premise nodes, whole, in `namespace AutomorphicForm`:

* `le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule` — verbatim from
  `Theorems/Thm_AutomorphicForm_le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule.lean`;
* `le_iSup_typeSubmodule_dual_of_invariant_pairing` — verbatim from
  `Theorems/Thm_AutomorphicForm_le_iSup_typeSubmodule_dual_of_invariant_pairing.lean`;
* `private TypeSummand` (the pin's `TW`: a `Σ` of a summand and a right-equivariant map out of it)
  and `private exists_finset_of_mem_iSup_span` — **one** copy of the two pin copies.

Imports: `FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace`,
`FLTForHuman.RepresentationTheory.SubrepresentationExtension`,
`Mathlib.RepresentationTheory.Subrepresentation`, `Mathlib.LinearAlgebra.Dual.Lemmas`,
`Mathlib.Tactic`. Wire: four `spec-pin:` lines (both wrappers, both `S_` files). Checker:
`2 ok`. Both proofs are `classical` + `Module.finBasis`; the second also uses
`LinearEquiv.ofInjective`, `Representation.dual`, `Submodule.dualRestrict_surjective`,
`LinearMap.dualMap`/`single`/`proj` and `Finset.univ_sum_single`.

### (c) `FLTForHuman/AutomorphicForm/Adelic/ArchDualCut.lean` — 6 proofs + the headline

Landed (16 declarations, checker `16 ok`, all at their pin statements): the dual cut
`cutDc`/`cutDM`, the split `goodComponentsD`/
`CAD`/`CBD` with its `IsCompl` and
`≤ cutDM`, the carrier API (`ρc_mem_underSub`,
`coe_ρc_mulSingle`, `rightTranslate_mem_map_subtype_of_forall`,
`comp_mul_rowIsometryInclAt₀_mem_archDualCutSubmodule`), and
`hasCompactSupport_of_mem_orbitSpan` / `rightConv_rightTranslate_rightTranslate'`.

Add, at the pin's statements:

| declaration | pin line | needs |
|---|---:|---|
| `cutDM_le_CAD` | :1089 | premise (b)-1 at `rowIsometryInclAt₀ F w` + `rowIsometryInclAt₀_injective` (imported from `EntryBall`, **do not re-declare**) |
| `rightConv_eq_zero_of_isIrreducible_of_le_CBD` | :1151 | premise (b)-2, `Representation.restrictRep`/`restrictInvt`, `Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero`, the six private helpers below |
| `hasCompactSupport_of_mem_mapSubmodule_orbitSpanc` | :1252 | `hasCompactSupport_of_mem_orbitSpan` + `map_orbitSpanc` |
| `rightConv_eq_zero_of_mem_inf_CBD` | :1261 | the previous + `sSup_simples_le` |
| `exists_mem_orbitSpanc_mem_archDualCut_rightConv_eq` | :1299 | `exists_add_eq_of_isCompl_biSup_isotypicComponents` + the split |
| `AutomorphicForm.exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq` | :1353 + wrapper | the previous + `mem_Ecf_of_mem_archCutSubmodule` + `orbitSpan_eq_span` |

`private` helpers, rectified from the pin's `c3_*` plumbing (keep them `private`,
`namespace AutomorphicForm.ArchDualCut`): `integrable_mul_rightConv` (`c3_integrable_mul`),
`rightConv_add_right`, `rightConv_smul_right`, `rightConv_smul_left` (the last two are the
pin's `c3_rightConv_*`), `exists_bilin_rightConv_fun` (`c3_exists_bilin_eval_fun`) and
`exists_bilin_rightConv_carrier` (`c3_exists_bilin_eval`). The Borel/Haar instances go in each
proof that needs them, as in `IsotypicCuspSpace.rightConv_add_left`; the file already carries
`set_option linter.style.haveILetI false` for that reason.

Add the one import the remaining proofs need: `import FLTForHuman.RepTheory.TypeInvariance`
(and `RepTheory/TypeSpan` only if something there is used). Expected checker: `22 ok`.

### (d) the consumer

One `-- Zone DC1` block in `spec/AutomorphicFormConsumer.lean`, imports of the three modules,
**executed** claims only (no `#check`; deleting any one module must break it):

1. a hypothesis-form instantiation of the headline: given `tys`, continuous
   `y ∈ archCutSubmodule F tys` and continuous compactly supported `f` with finite-dimensional
   orbit span, produce `f'` and compose its dual-cut membership with
   `mem_archDualCutSubmodule_iff`;
2. both premise theorems applied at one concrete small datum (trivial `K`, `G = ℂ` as a
   one-dimensional trivial representation, `S = S' = ⊤`, `θ = id`), plus one non-trivial use of
   `le_iSup_typeSubmodule_dual_of_invariant_pairing` in hypothesis form;
3. the dual-cut dictionary executed: `mem_cutDM_iff` composed with
   `isCompl_CAD_CBD` (`⊓ = ⊥`), and
   `Representation.restrictRep` + `Representation.isIrreducible_of_isSimpleModule` on one
   explicitly named one-dimensional representation.

## 3. Reuse map — call these, never restate

| pin declaration (`F4CutWords` spelling) | port home | verdict |
|---|---|---|
| `Ecf`, `ρc`, `orbitSpan`, `orbitSpanc`, `map_orbitSpanc`, `mem_orbitSpan_self`, `orbitSpanc_mem_invtSubmodule`, `archRep`, `ArchIsometryProd`, `archProdIncl*`, `exists_invt_compl`, `isSemisimpleModule_ρc` | `AutomorphicForm/Adelic/ArchCompactOrbit.lean` (the same names) | **import** |
| `ℂK`, `underSub`, `mem_underSub_iff`, `finiteDimensional_underSub_of_eq_span`, `mem_mapSubmodule_iff`, `rightTranslate_mem_of_mem_iSup_range'`, `isCompl_biSup_isotypicComponents`, `exists_linearEquiv_map_asModuleEquiv_of_linearEquiv`, `exists_add_eq_of_isCompl_biSup_isotypicComponents`, `exists_eq_span_singleton_of_isSimpleModule`, `le_biSup_isotypicComponents_of_forall_linearEquiv_le`, `mem_Ecf_of_mem_archCutSubmodule`, `mem_Ecf_of_finiteDimensional_span`, `orbitSpan_eq_span`, `archProdIncl_mulSingle` | `AutomorphicForm/Adelic/ArchCutProjector.lean` (the same names) | **import** |
| `rowIsometryInclAt₀_injective` | `EntryBall` (`Q09RowIso.rowIsometryInclAt₀_injective`) | **import, do not re-declare** |
| `exists_stable_compl` | the ported `Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous` (and `exists_invt_compl` is already ported) | **do not port** |
| `isCompact_rowIsometrySubgroup₀`, Haar/Borel vocabulary | `ArchInfra`, `NumberTheory/AdelicHaar/*`, `IsotypicCuspSpace` | **import** |
| `pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero` | `RepresentationTheory/InvariantPairing.lean` | **import** |
| `Representation.exists_extend_forall_apply_mul_of_injective` | `RepresentationTheory/SubrepresentationExtension.lean` | **import** |

Recorded negatives: `orbitSpan_le_Ecf` (:268) and `placeOrbitSpan_mono_of_mem` (:460) are declared
in this pin file and used nowhere in it or in any ported consumer; they are dropped as dead
prelude, matching the landed cut module.

## 4. Not this set

The cut-side sibling `AutomorphicForm.exists_mem_span_rightTranslate_mem_archCutSubmodule_and_rightConv_eq`
and the `rightConv_eq_of_archCutProjector` family are separate orders. No module outside the three
is edited; `ArchCompactOrbit`, `ArchCutProjector`, `RepTheory/BiIsotypic` and the
`RightConvComm/*` chain are imported, never touched — a needed promotion there is a stop-and-report.
**No existing module is renamed either**: `ArchCompactOrbit` and `ArchCutProjector` are
byte-identical to the 2026-10-22 landing, and the public name rectification is debt (§5).

## 5. Names and the wire — settled, do not change

**2026-10-25, after landing:** the generated *namespace* family of the modules this node imports
(`Q09`, `Q09AIarch`, `Q09AIarchC`, `Q09AIarchG`, `Q09RowIso`) was stripped in a separate sweep and
those modules were wired — see [logs/q09-rectification.md](../../logs/q09-rectification.md). It is
a different family from the engine tokens below, which stay the pin's.

**The rule for this wave: public names are the pin's, the parser is not touched.** The checker
diffs statement *text*, and every engine name here (`cutDc`, `cutDM`, `CAD`, `CBD`,
`goodComponentsD`, `Ecf`, `ρc`, `ℂK`, `underSub`) occurs *inside* statements. Renaming one
therefore turns every mentioner into `MISSING` unless the rename is registered in
`spec/lean_parser.py`'s `CANONICAL_NAMES`, which is a checker amendment. That amendment is **not**
made here: it buys legibility in the port at the cost of pin search, and it is only defensible
where a name is genuinely unreadable (a generated label, or a one- or two-letter token where
ambiguity is a real hazard). It is recorded as debt in `CARRY-FORWARD.md` instead. So:

* public declarations keep the pin's names — including the short ones (`cutDc`, `cutDM`, `CAD`,
  `CBD` beside `cutc`, `cutM`, `CA`, `CB`), and the pin's words (`ArchIsometryProd`,
  `archProdIncl`, `archRep`, `orbitSpan`, `TypeWitness`, `placeOrbitSpan`);
* **generated tokens are not carried**: the pin's `c3_*` private helpers (the `c3` is the
  `PartC3` section label) are named for what they do in (c), the premise helper `TW` becomes
  `TypeSummand` in (b), the pin's `PartB7`/`FarmC3G1G2`/`PartC3` section labels and its
  `solution`/`p2m_reactivate` staging disappear with the module structure. Private names are not
  diffed, so none of this touches the checker.

Public is the default; `private` is only for the six plumbing helpers in (c) and the two in (b).
A declaration added to a module the pin does not name in that module's `spec-pin:` files is
`MISSING` — do not add any.

## 6. Build discipline — read before the first compile

From `lean/`, through the lock:

```
flock .lake/flt_build.lock timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>
flock .lake/flt_build.lock timeout 300 lake build <Module>          # per finished file
```

* The **200,000 cap is a diagnostic**: a declaration that exceeds it has an instance-inference
  defect. Never raise it, never add a module `set_option maxHeartbeats`
  (or `synthInstance.maxHeartbeats`), never carry the pin's `backward.isDefEq.respectTransparency`
  switch.
* **Bound, do not measure**: no `time`, no durations, no second profiling run. Any compile that can
  plausibly run a minute is a background job with its own `timeout`, output redirected to
  `lean/tmp/…log`.
* Bound a module's floor before bisecting (a `lean/tmp/` copy with every proof `sorry`'d,
  statements and `def`s verbatim). If the floor is over the cap the cost is in the frozen types —
  stop and report.
* One probe, one edit, one bounded compile per turn. **No whole-tree build.**

## 7. Gates

```bash
cd lean
flock .lake/flt_build.lock timeout 120 python3 spec/check_port.py --force \
  FLTForHuman/RepresentationTheory/SubrepresentationRestriction.lean \
  FLTForHuman/RepTheory/TypeInvariance.lean \
  FLTForHuman/AutomorphicForm/Adelic/ArchDualCut.lean
# expected: 7 / 2 / 22 ok, 0 mismatch, 0 missing, 0 own, 0 kw
python3 spec/check_port.py --changed --strict-markers     # tree still green, no stale marker
```

plus: the three modules elaborate clean at 200k and `lake build` each green with **0 warnings**;
`#print axioms` on the headline and both premise theorems is
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`native_decide`/`import Mathlib`/
`set_option maxHeartbeats`; the consumer zone compiles with 0 errors; `git status` shows exactly
the four files of the wave once (a)–(d) are in — the three new modules and the consumer — with
`spec/lean_parser.py`, `CARRY-FORWARD.md` and every library module untouched.

## 8. Stop and report — do not improvise — if

a promotion or any edit to an existing module is needed (give the declaration, host and
`build_ladder.py --edit`'s price); a heartbeat raise looks necessary (give the statement-only
probe at 200k); a premise theorem's statement cannot be matched to its `Theorems/` wrapper; a
declaration reads `MISMATCH`/`MISSING`; a `spec/decl_markers.tsv` row seems needed; a `rw` needs
the pin's `backward.isDefEq.respectTransparency false`; or a definition's elaboration does not
close at 200k. Raise it at first belief, in one short message, and keep working on what is
independent.

## 9. Report shape

(i) per module: lines, declarations, the public/private split with the `shapes.py --module <file>
--port-only` reading behind every `private` decision; (ii) the three checker readings,
`--changed --strict-markers`, and the build's jobs/warnings; (iii) axioms; (iv) the reuse actually
taken against §3, each substitution confirmed by `exact`, and any row that did not hold; (v) the
consumer zone's error count; (vi) deviations with sites; (vii) what belongs in CARRY-FORWARD
(expected: the homing debt of `hasCompactSupport_of_mem_orbitSpan` and the two `rightConv` laws,
whose natural owners — `ArchCompactOrbit` and `rightConv`'s module — were left unedited; and the
two dropped dead prelude lemmas); (viii) `git status`.

## 10. Landed (2026-10-25)

| module | lines | decls | public | private | checker |
|---|---:|---:|---:|---:|---|
| `RepresentationTheory/SubrepresentationRestriction.lean` | 132 | 7 | 7 | 0 | `7 ok, 0 mismatch, 0 missing, 0 own` |
| `RepTheory/TypeInvariance.lean` | 366 | 4 | 2 | 2 | `2 ok, 0 mismatch, 0 missing, 0 own` |
| `AutomorphicForm/Adelic/ArchDualCut.lean` | 589 | 28 | 22 | 6 | `22 ok, 0 mismatch, 0 missing, 0 own` |
| `spec/AutomorphicFormConsumer.lean` (`Zone DC1`) | +150 | 5 executed claims | — | — | elaborates with 0 errors, 0 warnings |

Tree: `check_port --all` **5637 ok, 0 mismatch, 0 missing, 31 own, 0 kw over 254 modules**
(`--changed --strict-markers` the same, no stale marker; the 31 `own` are pre-existing). Builds:
each module and the consumer via `lake env lean` at 200k, then `lake build` per module — green,
**0 warnings**. Axioms on the headline and both premise theorems:
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`. No `sorry`/`admit`/`native_decide`/
`import Mathlib`/`set_option maxHeartbeats`; `git status` adds the three modules, the consumer and
this order — `spec/lean_parser.py`, `CARRY-FORWARD.md` and every library module untouched.

**Plan versus actual.** The budget was ≈1,009 net new content and ≈900–1,000 written; the landing
is 1,087 module lines (+150 consumer), i.e. ≈1.08× on the content ratio — inside the sibling set's
1.0–1.3 band. The split ran as planned: manager 20 declarations (the four `Representation`
unfoldings, the 16 dual-cut defs and short API), worker 6 `ArchDualCut` proofs plus the headline,
the whole `TypeInvariance` module and the consumer. All three premises of §0 landed whole; the
`port_advise` reuse table held row for row (§3), the two premise copies were deduplicated to one
30-line helper, and `RepTheory/TypeSpan` turned out to be unnecessary.

**Review notes, and what changed against the plan.**

* **The public names are the pin's; the parser was not amended.** The order as dispatched carried
  a rename of the compressed engine tokens (`Ecf` → `ContinuousFdOrbit`, `cutDc` →
  `archDualCutInFdOrbit`, …) with a `CANONICAL_NAMES` entry per name. That was reverted on review
  before the wave closed: a public name that occurs inside a statement can only move by amending
  the checker's normaliser, and that is not a change to make for legibility when it makes the pin
  harder to search. The landed public names are therefore the pin's — `cutDc`, `cutDM`,
  `goodComponentsD`, `CAD`, `CBD`, `Ecf`, `ρc`, `ℂK`, `underSub`, `ArchIsometryProd`, `archProdIncl`,
  `archRep` — and the rectification is open debt ([CARRY-FORWARD.md](../../CARRY-FORWARD.md), "the AC3
  engine carries the pin's engine tokens"). What *was* stripped is the part that costs the checker
  nothing: the pin's `c3_*` private helpers (the `c3` is its `PartC3` section label) are named for
  what they do, `TW` became `TypeSummand`, and the pin's `PartB7`/`FarmC3G1G2`/`PartC3` sections and
  its `solution` staging disappeared with the module structure.
* **Two module-boundary calls.** `Representation.restrictRep`/`restrictInvt` and the restriction
  API are generic `Representation` theory with no adèlic content → `RepresentationTheory/`
  (mathlib has no such restriction). The two premise nodes are statements about
  `AutomorphicForm.typeSubmodule` → `RepTheory/TypeInvariance.lean` beside `TypeSpan`, not in the
  adèlic module that consumes them.
* **Deviations.** `import Mathlib.RepresentationTheory.Irreducible` in the `Representation` module
  (`Representation.IsIrreducible` is not in the pin module's import closure);
  `import …RepresentationTheory.InvariantPairing` in `ArchDualCut` (the pairing lemma the vanishing
  theorem applies); two scoped linter switches — `linter.style.haveILetI false` on
  `isIrreducible_of_isSimpleModule` and file-wide in `ArchDualCut` (23 load-bearing `haveI`s), and
  `linter.unusedVariables false` on premise 1, whose `hS'` binder the pin leaves unused and which
  must stay named because the checker hashes binder names; `push Not` for the pin's deprecated
  `push_neg`, and its no-op `beta_reduce` lines dropped. No `set_option maxHeartbeats`, no
  `backward.isDefEq.respectTransparency`.
* **Degenerate diffs checked by hand.** The five `def`s have type-only statements
  (`Submodule …`), so the checker reports `cutDM`/`CAD`/`CBD` against the pin's `cutDM` by content
  hash; the bodies were read against pin :1030–:1057 (`cutDc` is the `comap` of the dual cut,
  `cutDM` its `mapSubmodule`, `CAD`/`CBD` the two `⨆ c ∈ …` sup-rema) and are the pin's.
