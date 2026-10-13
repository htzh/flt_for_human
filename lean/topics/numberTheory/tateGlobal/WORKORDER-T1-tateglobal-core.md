# WORKORDER T1 — the TateGlobal analytic core: one set, three nodes

**Status (2026-10-13): order written; dispatch 1 ready to run.** One dispatch = one
subagent = one or two natural modules, ≈1,300–1,600 ported lines. Dispatches run
**in series, one subagent at a time**; the manager reviews the tree between them and
re-issues the next dispatch against the tree that then exists.

**Audience.** A fresh subagent with no memory of the reconnaissance. Read §3 and §5
twice: §3 is the protocol and §5 is the recipe you execute. The method is
[porting-playbook.md](../../../porting-playbook.md) §2.3–§2.6, §3.1–§3.5, §4.
Companions: [TOPIC-tateglobal-analytic-core.md](TOPIC-tateglobal-analytic-core.md)
(why this set, the measurement, the module map), [CARRY-FORWARD.md](../../../CARRY-FORWARD.md),
[spec/UNWIRED-PUBLIC.md](../../../spec/UNWIRED-PUBLIC.md).

**Pin.** `anthropics/fermats-last-theorem` at `aa2d8b3`; the port's mathlib is
`v4.34.0`. The three silos are, in this order of the spine:

* **A** `P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean` (5,597 lines, 417 declarations) — the Euler-factor identity;
* **B** `P2M/Sol/S_NumberField_TateGlobal_integrable_zetaIntegrand.lean` (6,202 lines, 391 declarations) — integrability of the zeta integrand;
* **C** `P2M/Sol/S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean` (5,610 lines, 419 declarations) — the jointly-factorizable form.

Raw <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_integrable_zetaIntegrand.lean>
etc. stay correct for fetching; the `Theorems/Thm_*.lean` wrappers carry the
statements the checker diffs.

## 1. Scope

Port the three nodes as **one set**: a shared core of the declarations all three
files re-prove, spliced once into natural modules, then three cap modules carrying
each file's unique declarations and its headline, then a thin façade re-stating the
three consumed headlines at their pin names.

Measured: 17,409 raw lines, 17,318 declaration lines, 9,318 duplicate, **8,000
once-cost**. The core is 4,075–4,260 lines (330 declarations present in all three);
`A∩C` carries 911 more (the unfolding), `A∩B` one more; the caps are A 422, B 1,602,
C 448. The pin's `private` helpers are re-derived locally, not promoted.

**Not this set:** the other 93 `S_NumberField_TateGlobal_*` files; the ten Z1
consumers of `NumberField.exists_completedDedekindZeta_package`; the pin's `P2M.Util`
/ `p2m_*` scaffolding; any file-wide `set_option`.

## 2. What is already in the port (import it; never re-derive)

The definition layer is ported and green. The core modules import these; they must
not be duplicated:

* `FLTForHuman/NumberTheory/NumberField/TateGlobal/Defs.lean` — `ideleNorm`,
  `zetaIntegral`, `localChar`, `archLocalChar`, `IsUnramifiedCharAt`,
  `integralOutside`, `IsFactorizableStandardOutside` (`NumberField.TateGlobal`);
* `FLTForHuman/LanglandsTunnell/TateLocalZeta.lean` — `modulus`, `charExt`,
  `localZeta`, `tateFourier`, `localGammaAt` (`LanglandsTunnell.TateLocal`);
* `FLTForHuman/NumberTheory/AdelicFourier.lean` — `fourierIntegral`, `pureTensorSet`,
  `schwartzBruhat` (`NumberField.AdelicFourier`);
* `FLTForHuman/NumberTheory/AdelicBox.lean`, `…/AdelicLevel/*`, `…/AdelicHaar/*`,
  `…/AdelicVolume.lean` — `finIncl`, `localUnit`, `archCentralUnit`,
  `integralFiniteAdeles` and its openness/closedness/compactness;
* `FLTForHuman/NumberTheory/NumberField/Completion/Finite.lean` — the residue-field
  finiteness and the compact/open/locally-compact instances;
* `FLTForHuman/AlgebraicCurve/Place/{Completion,AdicCompletion}.lean` — the adic
  completion, uniformizers, `completionIdeal`, density and the residue-field
  identification;
* `FLTForHuman/AutomorphicForm/Adelic/LsXi.lean` etc. — `IsUnitaryChar`,
  `IsIdeleClassChar`.

If a pin declaration you are about to transcribe already has a statement-identical
copy in the port, import and use it; say so in the module header. The register
(`tools/deps/unwired_register.py`) will show the mapping.

## 3. The protocol

### 3.1 Natural module homes, natural names

* The development lives in `FLTForHuman/NumberTheory/NumberField/TateGlobal/`, with
  the prelude in namespace `NumberField.TateGlobal` (the pin's own namespace) and the
  three headlines at their pin names. The façade is
  `FLTForHuman/NumberTheory/NumberField/TateGlobal.lean`.
* **Home by mathematics, not by pin file.** A module is a mathematical role. Do not
  create a module per pin `S_` file, and do not split a module to keep files small —
  file size is not what makes a build slow (§3.4).
* **No pin prefixes.** These three files carry none, but strip any `p2m_open` /
  `p2m_reactivate` namespace nesting from the text you transcribe.
* **Rename the chapter prefix; keep the sub-namespace.** The pin's source wraps its
  prelude in a chapter namespace `M4aLocalCFT` and, inside it, mathematical
  sub-namespaces (`ValuationOrd`, `LocalHaarModulus`, `LocalZetaUnramified`,
  `ValuedOrdBridge`, `MulHaarFromAdditive`, …). Replace the chapter prefix
  `M4aLocalCFT.` with the port's theory namespace, so `M4aLocalCFT.X.foo` becomes
  `NumberField.TateGlobal.X.foo`. **Do not flatten two sub-namespaces into one.** A
  declares `measure_units_smul`, `mulMeasure_units_smul` and
  `image_val_subset_compl_zero` twice, in different sub-namespaces, with different
  statements; flattening them collides. Strip only `p2m_open`/`p2m_reactivate`
  nesting; the pin's `Fold_*` sections are comments, not namespaces.
* **Keep the pin's binder shape.** Section variables vs explicit binders is part of
  the statement; take each declaration's own text.
* Name a declaration for what it states if its tail is opaque (`hole_G2`,
  `t01`, `P`); otherwise keep the tail.

### 3.2 Provenance comments

Every transcribed declaration carries, on the line immediately above it (above any
`@[...]` attribute):

```lean
-- pin: apply_asm_of_isFactorizableStandardOutside (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4933)
```

Both name and `file:line` are required: `tools/deps/unwired_register.py` reads this
comment for its `pin original` column. A missing comment shows as `—` in the
register — treat that as a defect. For a declaration with no pin counterpart (a
port-only adapter) write `-- port-only: <reason>` instead. Anonymous instances get a
descriptive name and a `-- pin: <descriptive> (<file>:<line>)` comment.

### 3.3 Statements verbatim modulo the name; proofs adapted

* A **statement** is the pin's, character for character after the checker's
  normalisation — the name, the references to renamed siblings, and a documented
  `v4.34.0` drift being the only permitted differences. Recover the pin's own text
  with §10's extraction command; never retype it.
* A **proof** is adapted freely. If a proof needs a *statement* to change, that is a
  stop condition (§8).
* Where mathlib `v4.34.0` renamed or replaced an API the pin's statement mentions,
  restate with the new name and record the mapping in the module header (the
  definition layer already records `Ideal.inertiaDeg'` → `Ideal.inertiaDeg`,
  `Countable.of_module_finite` → `Finsupp.Countable.of_moduleFinite`).

### 3.4 Build-time discipline: solve instance inference, never raise the limit

**`maxHeartbeats` is not raised — not file-wide, not per declaration.** A slow
declaration is a defect in instance inference, and raising the cap hides it. The
recipe:

1. Compile with a **low** cap and a wall-clock timeout:
   `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>`.
   The first declaration to exceed the cap is the culprit.
2. Diagnose it with `set_option diagnostics true` / `set_option trace.Meta.synthInstance true`
   on that declaration (temporarily, in a scratch copy — do not commit it).
3. Fix the inference, e.g.: supply the instance explicitly (`letI h : … := …`), use
   `inferInstanceAs (T)` with the elaborated type, apply with `@`, avoid a `def` that
   blocks unification, or expose the instance the search cannot see through a
   coercion. Then re-run at the low cap; all declarations must fit.
4. Report the declaration and the fix in the hand-off.

If the whole file compiles at the port's global cap but not at a low cap, that is a
finding, not a licence: report the declaration and the trace.

### 3.5 What not to do

* Do not add a second copy of a declaration to make a proof easier.
* Do not add `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` anywhere.
* Do not add a file-wide option that the pin does not have. A **per-declaration**
  linter suppression with a one-line justification is allowed where the pin's
  verbatim statement or its load-bearing `letI`/`haveI` triggers a style linter —
  `set_option linter.style.haveILetI false in` and
  `set_option linter.overlappingInstances false in` (the latter where the pin keeps
  both `[μ.IsAddHaarMeasure]` and `[μ.Regular]`, which `v4.34.0` now sees as
  overlapping). Never `maxHeartbeats` / `synthInstance.maxHeartbeats`.
* Do not touch the definition-layer modules of §2, the other 93 `S_` files, the Z1
  modules, or the checker — except the façade wiring in the last dispatch.
* Do not transcribe a `p2m_*` line.
* Do not reorder across dependencies: the core's spine is A's declaration order
  (see §4), and every module must compile when appended after its predecessors.

## 4. The module map and the dispatch table

The spine is **A's declaration order**: every declaration shared by any two of the
three files occurs in A, and the pairwise intersection of all three is contained in
A. Merge B's and C's declarations into A's order after their dependencies; then cut
the merged list into the natural modules below, in order. **The pin's own sub-theory
namespaces are the natural module boundaries**: A is built from `M4aLocalCFT.X`
blocks (`ValuationOrd`, `LocalHaarModulus`, `LocalZetaUnramified`,
`MulHaarFromAdditive`, `ArchMulHaarReal/Complex/Completion`, `ValuedOrdBridge`,
`EulerBookkeeping`, `ShellBound`, `ShellTranslate`, …) interleaved with
`NumberField.TateGlobal` blocks, and one module per coherent cluster of them is the
right cut. The table below is indicative; re-cut a boundary if a cluster spans two
modules, but never move a declaration before a dependency, and never flatten two
sub-namespaces into one module namespace.

| module | pin range (A) | theme | ≈ lines |
|---|---|---|---:|
| `TateGlobal/Ideles.lean` | 28–660 + `ValuationOrd` | `integralOutside` lemmas, `unitsOutside`, the uniformizer/`ord`/`ordZ`/`ordA` prelude, `unitAtHom`/`embUnit`/`ordAt`/`Uniformizers`/`unifPow`/`unitPart`, `archUnits`, the shell decomposition, `hasSum_setIntegral_unitsOutside` | 620 |
| `TateGlobal/Coordinates.lean` | 666–1406 + `LocalHaarModulus` | `DeepUnits`/`SUnits`/`extendUnits`/`deepAsm`/`sAsm`/`asm`/`asmHomeo`/`coord`/`coordAt`/`deepCoordAt`/`archAsm`/`archCoord`; the local Haar-modulus cosets | 730 |
| `TateGlobal/DistribHaarChar.lean` | 1415–1517 (`LocalHaarModulus`) | `distribHaarChar_eq_one_of_mem_range`/`_mk0_irreducible`/`_adicCompletion`, `measure_smul_integers` | 175 |
| `TateGlobal/LocalZetaUnramified.lean` | 1556–1719 (`LocalZetaUnramified`) | local shells (`piUnit`, `shellSet`, `genShell`), measures, integrand | 257 |
| `TateGlobal/MulHaar.lean` | 1774–2105 (`MulHaarFromAdditive`) | the multiplicative Haar from the additive one | 430 |
| `TateGlobal/ArchMulHaar.lean` | 2142–2647 (`ArchMulHaarReal`/`Complex`/`Completion`) | the archimedean multiplicative Haar | 565 |
| `TateGlobal/ValuedOrdBridge.lean` | 2678–2882 (`ValuedOrdBridge`) | `valued_ne_zero_of_ne_zero`, `valued_le_one_of_mem`, `integers_adicCompletionIntegers`, `exists_irreducible_valued`, `valued_coe_units_eq_exp_neg_ord` | 208 |
| `TateGlobal/ReferenceMeasure.lean` | 2884–3220 | `deepRef`/`sRef`/`archRef`/`refMeasure`/`refConst`, `asmMeasure_eq_refConst_smul`, `localZeta_eq_integral_{comap,mulHaar,mulHaarCompletion}`, `integral_*Ref*` | 246 |
| `TateGlobal/FiniteSlab.lean` | 3222–3575 | `coordAt`/`finSingle`/`adeleSingle`, `slab`/`box`/`slabPush`, `embUnit`, `distribHaarChar_embUnit` | 355 |
| `TateGlobal/ArchSlab.lean` | 3577–3895 | `archCoord`/`archSingle`, `archSlab`/`archBox`/`archSlabPush`, `archCentralUnit`, `distribHaarChar_archCentralUnit`/`_archUnitHom` | 317 |
| `TateGlobal/ZetaIntegrand.lean` | 3897–4240 | `char_asm`, `apply_asm_of_isFactorizableStandardOutside`, `truncDeep`, `zetaIntegrand_asm`, the `*Integrand` definitions | 346 |
| `TateGlobal/UnifPowBridge.lean` | 4240–4362 | `ordAt_nonneg_of_mem`, `mem_integers_iff_ordAt_nonneg`, `unifPow_mul_*` | 117 |
| `TateGlobal/EulerBookkeeping.lean` | 4363–4733 (`EulerBookkeeping`) | `mono`/`monoN`, `sigmaT`, `sum_monoN_le_prod`, the Euler bookkeeping | 374 |
| `TateGlobal/PlaceSum.lean` | 4735–4853 | `underZ`, `absNorm_underZ_*`, `card_filter_underZ_le` | 118 |
| `TateGlobal/ShellBound.lean` | 4855–4998 (`ShellBound`) | `distribHaarChar_unifPow`, `baseFam`, `summable_absNorm_rpow_neg`, `summable_of_shell_bound` | 145 |
| `TateGlobal/ShellTranslate.lean` | 5000–5127 (`ShellTranslate`) | `setIntegral_shell_norm_le`, `norm_zetaIntegrand`, `integral_eq_tsum_shellCoef_mul` | 131 |
| `TateGlobal/EulerFactors.lean` | 5129–5597 (`G2Proof`) + A's headline | `unifOf`/`placeFactor`/`shellCoef`, the G2 unfolding, `zetaIntegral_mul_eulerFactors_eq_impl`, `solution` → the headline `NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq` | 464 |
| `TateGlobal/IntegrableZetaIntegrand.lean` | B's unique declarations | B's 60 unique declarations, `integrable_zetaIntegrand_impl`, `solution` → the headline `NumberField.TateGlobal.integrable_zetaIntegrand` | 1,600 |
| `TateGlobal/IndicatorEulerFactors.lean` | C's unique declarations | C's 19 unique declarations → the headline `NumberField.TateGlobal.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator` | 450 |
| `NumberField/TateGlobal.lean` | the three wrappers | façade: the three consumed headlines at the wrapper's names | 80 |

The ranges are the pin's measured cluster boundaries; one module per pin sub-namespace
cluster is the natural cut, and a dispatch may carry several such modules. The cap
modules hold each file's **headline** (`solution`) and its `_impl`; an A-only or
B-only declaration that sits inside a shared cluster stays in its thematic module
rather than being moved. One subagent runs one dispatch; a dispatch is 1,300–1,600
ported lines. Re-cut to hold that band and report the cut.

| dispatch | modules | pin source | ≈ lines |
|---|---|---|---:|
| 1 ✅ | `Ideles`, `Coordinates` | A 28–1414 | 1,350 |
| 2 ✅ | `DistribHaarChar`, `LocalZetaUnramified`, `MulHaar`, `ArchMulHaar` | A 1415–2676 | 1,427 |
| 3 | `ValuedOrdBridge`, `ReferenceMeasure`, `FiniteSlab`, `ArchSlab`, `ZetaIntegrand` | A 2678–4240 | 1,472 |
| 4 | `UnifPowBridge`, `EulerBookkeeping`, `PlaceSum`, `ShellBound`, `ShellTranslate`, `EulerFactors` | A 4240–5597 | 1,349 |
| 5 | `IntegrableZetaIntegrand` | B's 60 unique declarations + headline | 1,600 |
| 6 | `IndicatorEulerFactors`, `NumberField/TateGlobal.lean` | C's 19 unique + the three wrappers | 530 |

Dispatch 1 is §5; every later dispatch is §5 with the next range and module names,
re-issued by the manager against the tree that exists after review.

### 4.1 Block membership (how to tell shared from cap)

For a declaration in your range, it is **shared core** iff it occurs in ≥2 of A, B, C
with the same statement; otherwise it is a **cap** declaration of the file(s) that
have it. The measured blocks are: `A∩B∩C` 330 declarations (4,260 once-lines),
`A∩C` 70 (911), `A∩B` 1 (113); caps: A 16 (422), B 60 (1,602), C 19 (448). The two
private helpers (`intValuation_eq_coe_neg_multiplicity`, `ValuationSubring.subtype_inj`)
are re-derived locally where needed, not promoted. `tmp/tate_modules.txt` lists each
block's declarations by name and span; §5 step 1 regenerates the membership if the
scratch is gone.

## 5. The dispatch recipe (execute this)

1. **Extract the pin text.** For a pin range, list each declaration whose *start*
   line lies in it with its full source text (the command is §10). Read the whole
   declaration; the span is the declaration's, not the line's.
2. **Sort the shared from the cap.** For the shared core use the measured
   intersection (A∩B∩C = 330 declarations, plus A∩C = 70, A∩B = 1). The caps are the
   declarations in fewer than two of the three files; the module map in §4 names
   them.
3. **Write the module(s)** with the natural names, one `-- pin:` comment per
   declaration, statements verbatim, proofs adapted. Reuse §2's modules by import.
   Import the previous dispatch's module and build on it.
4. **Tier-0 loop.** `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>`
   until it exits 0 with **0 warnings**. Every failure is fixed by editing the proof
   or the instance argument, never by raising the cap (§3.4). When a declaration
   needs more than the low cap, find the inference and fix it.
5. **Tier-1.** `flock .lake/flt_build.lock timeout 300 lake build <module>` for each
   module just written. Never `lake build` with no argument.
6. **Regenerate the register.** `python3 tools/deps/unwired_register.py`; the new
   module's rows must show a `pin original`, not `—`.
7. **Report** per §9 and **stop**. The next dispatch is a separate subagent against
   the tree you leave behind.

## 6. Build discipline

* edit loop: `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>`;
* finished module: `flock .lake/flt_build.lock timeout 300 lake build <module>`;
* **no bare whole-tree `lake build`**; one `lake build <module>` per module, serialized;
* never raise the heartbeat cap, never add `set_option maxHeartbeats`;
* if you touch an existing module (only ever the façade in dispatch 6), build **only
  that module**, never the tree.

## 7. Verification (per dispatch)

* tier-0 `lake env lean` at the low cap: exit 0 and **0 warnings** — including no
  heartbeat override in the diff;
* tier-1 `flock … lake build <module>` green;
* `python3 tools/deps/unwired_register.py` regenerates cleanly and the new rows carry
  a `pin original`;
* `git status` shows only the dispatch's modules (plus the regenerated register);
* a `grep` sweep of the new files: no `sorry`/`admit`/`axiom`/`native_decide`, no bare
  `import Mathlib`, no `set_option maxHeartbeats`.

Final dispatch only (the façade):

* the façade listed in `PORT_FILES` (three entries / three headlines) and the three
  wrapper files plus the three silos in `SOURCES` (six entries), appended last;
* `timeout 300 python3 spec/check_flt_statements.py` — 0 mismatched / 0 missing, and
  the `identical` delta equal to the façade's public surface (the three headlines);
* a one-token mutation on one headline moves exactly one `mismatched`, then revert;
* `#print axioms` on the three headlines is `[propext, Classical.choice, Quot.sound]`;
* the sweep of §7 is clean.

## 8. Risks and stop conditions

1. **The merge order.** The largest structural cost: the core is a topological merge
   of three orders, not a prefix of one file. If a declaration cannot be placed
   without moving across a dependency, that is a stop-and-report.
2. **Mathlib drift.** Adapt proofs, never statements; a statement that will not
   typecheck as written after its documented drift is a stop.
3. **Instance inference.** A low-cap failure that resists a clean fix: report the
   declaration, its pin line, the trace, and the proposed fix; do not raise the cap.
4. **Binders.** Section-variable vs explicit-binder shape is part of the statement;
   take each declaration's own shape (Z1's risk §8.3).
5. **Local instances.** The pin's file-scoped `local instance`s (three in A and C,
   two in B) must be re-declared in each module a split crosses; they are invisible to
   the checker, deliberately not promoted, and are not a defect a reviewer should
   "fix".
6. **Scope creep.** Do not pull in the other 93 `S_` files, the Z1 consumers, or the
   pin's `P2M.Util`.
7. **Register drift.** A missing `-- pin:` comment loses provenance silently. The
   register check is not optional.
8. **`SFinite` on the product-measure API (`v4.34.0` drift) — resolved as a
   documented deferral.** `Integrable.mul_prod`/`smul_prod`/`op_fst_snd` gained
   `[SFinite ν]` (v4.33.0 omitted it through section variables), and the gap is not
   confined to them: `Measure.prod_restrict` needs `[SFinite μ] [SFinite ν]` on the
   unrestricted factors (`sum_sfiniteSeq`), and `Measure.prod_eq` needs
   `SigmaFinite`. So the pin's `integrable_refMeasure_mul` (B 5146) — stated over
   arbitrary measures — cannot be reached by the support-restriction repair either.
   What exists: the port-only mathlib supplement
   `FLTForHuman/MeasureTheory/Integral/Prod.lean` proves
   `MeasureTheory.sFinite_restrict_support_of_integrable` (the σ-finiteness of
   `μ.restrict (support f)`), which is the missing input a future SFinite-free
   product-measure development will need. The declaration itself is deferred, with
   a `CARRY-FORWARD.md` entry; its only consumer is ported by inlining under the
   Haar hypotheses. Any later declaration hitting this wall imports the supplement
   and does **not** change its statement.

## 9. Report shape

Per dispatch: the module paths and line counts; the count of declarations and the pin
range consumed, shared vs cap; provenance completeness (`N/N`); tier-0 result at the
low cap and tier-1 result; any instance-inference fix (declaration + what was wrong);
the register's diff (rows added); anything deferred, with the pin line; any stop
condition hit. Keep it short — the manager reads the tree.

## 10. Pin extraction

```bash
cd tools/deps
python3 - <<'EOF'
import importlib.util, sys
from pathlib import Path
sys.path.insert(0, ".")
import port_graph as pg
spec = importlib.util.spec_from_file_location("ck", "../../lean/spec/check_flt_statements.py")
ck = importlib.util.module_from_spec(spec); sys.modules["ck"] = ck; spec.loader.exec_module(ck)
PIN = Path.home() / "proj" / "fermats-last-theorem"
F = PIN / "P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean"  # A
lo, hi = 28, 1414   # dispatch 1: A's idèle/ord/unit-shell prelude and the S-units/coordinates
text = F.read_text(encoding="utf-8")
meta = {d["name"]: d for d in pg.scan_declarations(text)}
lines = text.split("\n")
for raw, kind, stmt in ck.raw_declarations(text):
    nm = raw.rsplit(".", 1)[-1]
    m = meta.get(nm)
    if m and lo <= (m["line"] or 0) <= hi:
        print(f"===== {m['line']}-{m['end_line']}  {kind}  {nm}")
        print("\n".join(lines[m["line"] - 1:(m["end_line"] or m["line"])]))
EOF
```

`tools/deps/extract_wave.py <lo> <hi>` prints the same for file A by default;
`tmp/tate_modules.txt` (this session's reconnaissance) lists the shared core and the
caps by name and span, and `tmp/A_order.txt` lists A's declarations in dependency
order. Both are untracked scratch; regenerate them with §5 step 1 if absent.

## 11. Dispatch log and final state (2026-10-13)

The order was executed to completion by six subagents, one at a time.

| dispatch | modules | pin | declarations |
|---|---|---|---|
| 1 | `Ideles`, `Coordinates` | A 28–1414 | 135 |
| 2 | `DistribHaarChar`, `LocalZetaUnramified`, `MulHaar`, `ArchMulHaar` | A 1415–2676 | 77 |
| 3 | `ValuedOrdBridge`, `ReferenceMeasure`, `FiniteSlab`, `ArchSlab`, `ZetaIntegrand` | A 2678–4240 | 114 |
| 4 | `UnifPowBridge`, `EulerBookkeeping`, `PlaceSum`, `ShellBound`, `ShellTranslate`, `EulerFactors` | A 4240–5597 | 91 |
| 5 | `IntLocalIntegrability`, `ShellSupport`, `NormIntegrable`, `HMajorant`, `PureTensor`, `IntegrableZetaIntegrand` | B's cap | 59 ported, 1 deferred |
| 6 | `IndicatorEulerFactors` + the façade | C's cap + the three wrappers | 19 |

24 development modules under `FLTForHuman/NumberTheory/NumberField/TateGlobal/` plus
the tier-1 façade `FLTForHuman/NumberTheory/NumberField/TateGlobal.lean`. Every module
is tier-0 `lake env lean` at the **200,000** heartbeat cap, exit 0 with 0 warnings, and
tier-1 `flock … lake build` green. No `maxHeartbeats` / `synthInstance.maxHeartbeats` /
`maxSynthPendingDepth` survives anywhere: the pin's preemptive overrides (A 1293–1360,
B 3113/4350/4493/4636/5377/5973/6063, A 4249/4841/4984/5113) were all dropped and every
declaration fits the low cap.

**Checker.** `python3 spec/check_flt_statements.py` → **9,237 identical** (648 promoted,
83 renamed), **0 mismatched, 0 missing**, 38 own-proof exempted, 9,275 checked. The
delta over the pre-port baseline (9,234 / 9,272) is +3, exactly the façade's three
headlines. A one-token mutation (`0 < c` → `0 ≤ c`) on the first headline moved exactly
one `mismatched` and was reverted. `#print axioms` on all three headlines is
`[propext, Classical.choice, Quot.sound]`. The register is current.

**Rulings that bind later work.**

* **Namespace rule.** The pin's chapter namespace `M4aLocalCFT` is renamed to
  `NumberField.TateGlobal`, the sub-namespace kept (`M4aLocalCFT.X.foo` →
  `NumberField.TateGlobal.X.foo`). Sub-namespaces are never merged: A really declares
  `measure_units_smul`, `mulMeasure_units_smul` and `image_val_subset_compl_zero`
  twice, in different sub-namespaces, with different statements.
* **C's cap is namespaced separately.** Fourteen of C's 19 unique names collide with
  A's on different statements, so they live under
  `NumberField.TateGlobal.IndicatorEulerFactors`.
* **Headline naming.** A development headline is named for what it states, in its
  sub-namespace (`G2Proof.zetaIntegral_mul_eulerFactors_eq`,
  `integrable_zetaIntegrand_holds`,
  `IndicatorEulerFactors.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator`);
  the façade re-states each at the pin wrapper's name, and only the façade is checked.
* **Heartbeats.** Never raised (topic §7.6). Every dispatch verified its range at the
  200,000 cap; the only instance-inference frictions were structural — `InfiniteAdeleRing`
  is a `def`, so `Function.update` rewrites need an `rfl`-ascribed Pi type, and the pin's
  `private mono` had to be promoted because public statements mention it.
* **`SFinite` drift.** `Integrable.mul_prod`/`smul_prod`/`op_fst_snd` gained
  `[SFinite ν]` and `Measure.prod_restrict` needs it on the unrestricted factors; the
  pin's `integrable_refMeasure_mul` (B 5146) is the set's one deferred declaration
  (§8.8, `CARRY-FORWARD.md`), with `FLTForHuman/MeasureTheory/Integral/Prod.lean` left
  as the partial step.

**Final register.** 57 modules, 1,250 public declarations, 962 with a pin original; the
TateGlobal development is tier-3 and unlisted, as designed. `git status` shows only the
development modules, the façade, the definition-layer modules (topic §5.1), the checker
wiring, the register, `CARRY-FORWARD.md` and the topic/order notes.
