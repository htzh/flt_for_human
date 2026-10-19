# WORKORDER-R — the Bruhat-transversal / Weyl-integrand trio: gate + two turns

**Status (2026-10-13): LANDED.** The gate and both subagent turns are complete; the tree
is green and the three headlines are checker-wired.

**Outcome.** Fourteen new modules, 4,116 written lines against the 2,780 measured net new
math lines: the gate `AutomorphicForm/Adelic/{BorelSubgroup 248, EtaFamily 139,
InducedSection 115, WeylIntertwining 73}.lean`; turn 1 `NumberTheory/AdelicLevel/Countability.lean`
(167), `NumberTheory/AdelicHaar/PlaceMeasure.lean` (622), `AutomorphicForm/Adelic/WeylIntegrable/{Coset 231,
Transfer 330, BoxBounds 260}.lean`; turn 2 `…/WeylIntegrable/{LatticeEstimates 850,
Assembly 320, UniformBound 357, Caps 154}.lean` and the façade
`AutomorphicForm/Adelic/WeylIntegrable.lean` (96, exactly three headlines). 324
declarations transcribed, every one carrying `-- pin:` provenance and statement-identical
to the pin. **Checker 9,238 → 9,241 identical (648 promoted, 83 renamed), 0 mismatched,
0 missing, 38 own** — the +3 is exactly the façade's three headlines; everything else
stays tier 3 in [spec/UNWIRED-PUBLIC.md](../../spec/UNWIRED-PUBLIC.md) (76 modules / 1,787
public declarations / 1,499 with a pin original). Tier-0 on all fourteen at the **200,000**
heartbeat cap, exit 0 with **0 warnings**; the milestone whole-tree build is green at
**9,533 jobs**. One-token mutations on each of the three headlines moved exactly one
`mismatched`, reverted; `#print axioms` on all three is
`[propext, Classical.choice, Quot.sound]`; `spec/AutomorphicFormConsumer.lean` runs the
R1–R4 zones. No promotion and **no existing Lean module edited**; the pin's
`set_option maxHeartbeats`/`synthInstance.maxHeartbeats` lines were dropped and every
declaration fits the low cap. The register tool's provenance window was fixed to
nearest-comment-first (it had mis-attributed `WeylIntegrable.toAdele_snd` to
`toAdele_fst`).

**Audience.** A fresh subagent with no memory of the reconnaissance. Read §3 twice: §3 is
the protocol and §4 is the recipe you execute. The method is
[porting-playbook.md](../../porting-playbook.md) §2.3–§2.6, §3.1–§3.5, §4. Companions:
[TOPIC-bruhat-transversal-trio.md](TOPIC-bruhat-transversal-trio.md) (the measurement,
the block structure, the homes), [spec/UNWIRED-PUBLIC.md](../../spec/UNWIRED-PUBLIC.md),
[CARRY-FORWARD.md](../../CARRY-FORWARD.md).

**Pin.** `anthropics/fermats-last-theorem` at `aa2d8b3`; the port's mathlib is `v4.34.0`.
The three silos, in spine order:

* **A** `P2M/Sol/S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`
  (2,763 lines) — summability;
* **B** `P2M/Sol/S_AutomorphicForm_continuous_bruhatTransversal_tsum_of_re_gt_half.lean`
  (2,792) — continuity;
* **C** `P2M/Sol/S_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean`
  (2,420) — integrability.

Raw URLs stay correct for fetching; the `Theorems/Thm_*.lean` wrappers carry the
statements the checker diffs.

## 1. Scope

Port the trio as **one set**: the four-module definition gate, then one shared home for
the ~2,400-line `WeylIntegrable` development, then three thin cap modules carrying the
headlines, then a façade that re-states the three at the wrappers' names.

Measured: 7,975 raw `S_` lines, **2,780 net new math lines**; the all-three block is
2,066 lines / 222 declarations, the pair-only (`LatticeSum`/`Uniform`) block 297 / 30, and
the three caps ≈377. The **third headline costs +13 lines** over the pair.

**Not this set:** the six descendant `S_AutomorphicForm_WeylIntegrable_*` silos; the
`weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` sibling; the
`LocalIntertwining_integral_*WeylIntegrand_adicCompletion` Tate pair; the consumers
(`exists_whittakerCoefficient_bruhatEisenstein_*`, the Rankin–Selberg and Maass–Selberg
rows); any `Definitions/` edit beyond the four gate modules; the pin's `P2M.Util` /
`p2m_*` scaffolding.

## 2. What is already in the port (import it; never re-derive)

* `FLTForHuman/AutomorphicForm/Adelic/Basic.lean` — `AdelicGL2`, `globalPoints`,
  `centralScalar`, `chiDet`.
* `FLTForHuman/AutomorphicForm/Adelic/LsXi.lean` — `IsIdeleClassChar`, `IsUnitaryChar`.
* `FLTForHuman/AutomorphicForm/Adelic/ConstantTerm.lean` — `unipotentGL2` and its
  `_coe`/`_zero`/`_add`.
* `FLTForHuman/NumberTheory/AdelicHaar/{Local,Adele,GeneralLinear}.lean` — `adeleBorel`,
  `adelicAddHaar`, `glBorel`, the adèlic topology.
* `FLTForHuman/NumberTheory/AdelicBox.lean`, `…/AdelicLevel/*` — `adelicBox`, `idealBall`,
  the level vocabulary.
* `FLTForHuman/LinearAlgebra/Countable.lean` — `of_module_finite` (the pin's
  `Def_Mathlib_LinearAlgebra_Countable` node, already transcribed, tier 3).
* The `AutomorphicForm/Adelic/ArchApproxIdentity/*` and `RightConvComm/*` layers — the
  house style for `attribute [local instance]` blocks and `scoped` instances.

`port_advise` reports **0 name clashes** and **0 substitutions** for the trio.

## 3. The protocol

### 3.1 Natural module homes, natural names

* The gate lands `AutomorphicForm/Adelic/{BorelSubgroup,EtaFamily,InducedSection,WeylIntertwining}.lean`,
  pin names, namespace `AutomorphicForm`.
* The proof lives under `NumberTheory/AdelicLevel/Countability.lean`,
  `NumberTheory/AdelicHaar/PlaceMeasure.lean`, `AutomorphicForm/Adelic/WeylIntegrable/*`,
  and the façade `AutomorphicForm/Adelic/WeylIntegrable.lean`. Keep the pin namespaces
  (`NumberField.AdelicCountability`, `M4aS4`, `NumberField.AdeleRing`,
  `AutomorphicForm.WeylIntegrable`) so statement text matches; the directories carry the
  organization.
* Strip the `P2MW.S_…` chapter prefix and every `p2m_open`/`p2m_reactivate`/`p2m_export`
  line. Do **not** flatten two sub-namespaces with the same tail.
* **Home by mathematics, not by pin file.** One module per role; file size is not what
  makes a build slow (§3.4).

### 3.2 Provenance comments

Every transcribed declaration carries, immediately above it (above any `@[...]`):

```lean
-- pin: bruhatTransversal_summand_norm_summable (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2665)
```

Both name and `file:line` are required: `tools/deps/unwired_register.py` reads the comment
for its `pin original` column. A missing comment shows as `—` — treat that as a defect.
For a port-only adapter write `-- port-only: <reason>`; anonymous instances get a
descriptive name and a `-- pin: <descriptive> (<file>:<line>)`.

### 3.3 Statements verbatim modulo the name; proofs adapted

* A **statement** is the pin's, character for character after the checker's
  normalisation; a documented `v4.34.0` drift is the only permitted difference.
* A **proof** is adapted freely. If a proof needs a *statement* to change, stop and
  report (§8).
* Keep each declaration's own binder shape; the pin writes the headline statements with a
  leading `let α := …;` — keep it exactly.

### 3.4 Build-time discipline: solve instance inference, never raise the limit

**`maxHeartbeats` is not raised — not file-wide, not per declaration.** A slow
declaration is a defect in instance inference, and raising the cap hides it:

1. compile with a low cap and a wall-clock timeout:
   `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>`; the
   first declaration to exceed the cap is the culprit;
2. diagnose it with `set_option diagnostics true` / `set_option trace.Meta.synthInstance true`
   on that declaration, temporarily, in a scratch copy — do not commit it;
3. fix the inference: supply the instance explicitly (`letI h : … := …`), use
   `inferInstanceAs (T)` with the elaborated type, apply with `@`, avoid a `def` that
   blocks unification, or expose the instance the search cannot see through a coercion;
   then re-run at the low cap — all declarations must fit;
4. report the declaration and the fix.

The pin's `set_option maxHeartbeats …` lines (e.g. above
`weylIntertwiningIntegrand_integrable_of_re_gt_half_impl`) are **dropped**; the
declaration must fit the low cap.

### 3.5 What not to do

* Do not add a second copy of a declaration to make a proof easier.
* Do not add `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` anywhere.
* A **per-declaration** linter suppression with a one-line justification is allowed where
  the pin's verbatim statement or a load-bearing `letI`/`haveI` trips a style linter.
  Never a heartbeat override, and never a file-wide `set_option` the pin does not have.
* Do not touch the definition-layer modules of §2, the descendants, the other `S_` files,
  or the checker — except the R-final façade wiring.
* Do not reorder across dependencies: the pin's declaration order is the spine, and every
  module must compile when appended after its predecessors.

## 4. The dispatch recipe (execute this)

1. **Extract the pin text.** For the pin range, list each declaration whose *start* line
   lies in it with its full source text. Read the whole declaration; the span is the
   declaration's, not the line's. (`tools/deps/extract_wave.py <lo> <hi>`, or the
   extraction snippet in the topic.)
2. **Classify** each declaration against §2: substitute (import), or new. There are no
   promotions and no pin-`private` helpers in the `S_` files.
3. **Write the module(s)** at the natural names, one `-- pin:` comment each, statements
   verbatim, proofs adapted. Import the previous dispatch's modules.
4. **Tier-0 loop.** `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>`
   until exit 0 with **0 warnings**. Every failure is fixed by editing the proof or the
   instance argument, never by raising the cap.
5. **Tier-1.** `flock .lake/flt_build.lock timeout 300 lake build <module>` per module.
   Never `lake build` with no argument.
6. **Regenerate the register.** `python3 tools/deps/unwired_register.py`; the new module's
   rows must show a `pin original`, not `—`.
7. **Report** per §9 and **stop**. The next turn is a separate subagent against the tree
   you leave behind.

## 5. The dispatch table

| turn | sets | modules | pin spine | ≈ lines | status |
|---|---|---|---|---|---:|---|
| — | **gate** | `AutomorphicForm/Adelic/{BorelSubgroup,EtaFamily,InducedSection,WeylIntertwining}.lean` | the 4 `Definitions/` nodes | 490 | **landed** |
| 1 | R1, R2 | `NumberTheory/AdelicLevel/Countability`, `NumberTheory/AdelicHaar/PlaceMeasure`, `AutomorphicForm/Adelic/WeylIntegrable/{Coset,Transfer,BoxBounds}` | `S4Base` → `AdelicBoxSec` | 1,090 | **landed** |
| 2 | R3, R4 | `…/WeylIntegrable/{LatticeEstimates,Assembly,UniformBound}`, `AutomorphicForm/Adelic/WeylIntegrable` (façade) | `PositiveChar` → the three caps | 1,390 | after turn 1 |

**Gate — the definition layer (manager, one wave; landed).** The four modules of topic
§4, whole nodes, at their homes, namespace `AutomorphicForm`, tier 3. Transcribed
mechanically from the pin (statements verbatim, `-- pin:` provenance on every
declaration); only `BorelSubgroup` needed a dependency build before `InducedSection`.
All four tier-0 green at the 200,000 cap with 0 warnings; tier-1 green; the register
gains 4 modules / 51 public declarations, all with `pin original` rows; the checker is
unchanged (9,238 / 0 / 0 / 38). No promotion, no cascade, no existing module edited.

**Turn 1 — the base and the transfer (landed 2026-10-13).** One subagent, five new
modules: `NumberTheory/AdelicLevel/Countability.lean` (167 lines / 12 declarations, pin
24–142), `NumberTheory/AdelicHaar/PlaceMeasure.lean` (622 / 59, pin 146–657, namespaces
`M4aS4` + `NumberField.AdeleRing`), `AutomorphicForm/Adelic/WeylIntegrable/{Coset 231/15,
Transfer 330/57, BoxBounds 260/26}`, 168 pin declarations with start lines in 14–1320
transcribed, 0 missing / 0 duplicated; all with `-- pin:` provenance. Tier-0 green at the
200,000 cap with 0 warnings on all five, tier-1 green; register +5 modules / +134
declarations, no `—` rows; the checker unchanged. The pin's
`synthInstance.maxHeartbeats 640000` on `regular_adelicMeasure` was dropped and the
declaration fits the low cap. Two scoping notes: `open scoped NumberField.AdelicCountability`
is needed where the pin's `p2m_open` activated those scoped instances, and the pin's
qualified `AdelicBox.integralFiniteAdeles` (the port homes the declaration under
`NumberField.AdelicLevel`) is reconciled by a one-line `-- port-only:`
`@[reducible] def NumberField.AdelicBox.integralFiniteAdeles` in `PlaceMeasure.lean`; no
turn-2 declaration names it, so no second copy arises.

**Turn 1 — the base and the transfer.** R1 is `S4Base`: `NumberField.AdelicCountability`
(generic countability) and `M4aS4` (place measures and the `distribHaarChar` product
formula), plus `NumberField.AdeleRing`. R2 is the `WeylIntegrable` front: `Coset`,
`ModFin` (the coset transversal and finite modulus), the `Generic`/`Adelic`/`Generic2`/
`Adelic2` transfer, and `EntryBox`/`NormBounds`/`AdelicBoxSec` (the entry-box and norm
bounds). `S4Base` is generic — home it under `NumberTheory/` and keep its pin namespaces.

**Turn 2 — the estimates, the assembly and the three caps.** R3 is
`PositiveChar`/`Pointwise`/`Lattices`/`R2`/`Fin`/`Place`/`Arch` (the lattice/place/
archimedean estimates), `Asm`/`Served` (the assembly, including the shared
`weylIntertwiningIntegrand_integrable_of_re_gt_half_impl`), and `LatticeSum`/`Uniform`
(the pair-only uniform M-bound). R4 is the façade
`AutomorphicForm/Adelic/WeylIntegrable.lean`, carrying **only** the three headlines at
the wrappers' names:

* `AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half` — one line on
  the shared `WeylIntegrable.bruhatTransversal_summand_norm_summable`;
* `AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half` — the 22-line
  `RhSContinuity.rhs_hole` (`continuousOn_tsum` under the shared uniform bound) plus the
  headline;
* `AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half` — one line on the
  shared `_impl`.

Only the façade is listed: add it to `PORT_FILES` and the three wrappers plus the three
`S_` files to `SOURCES` (both last), run the checker, and reconcile the `identical` delta
against the three headlines. The three cap declarations live in the tier-3 modules; the
façade re-states them, so nothing else appears in the delta.

The three statements are in the wrappers
`Theorems/Thm_AutomorphicForm_{bruhatTransversal_summand_norm_summable_of_re_gt_half,continuous_bruhatTransversal_tsum_of_re_gt_half,weylIntertwiningIntegrand_integrable_of_re_gt_half}.lean`
— recover them verbatim, including the leading `let α := …`.

## 6. Build discipline

* edit loop: `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>`;
* finished module: `flock .lake/flt_build.lock timeout 300 lake build <module>`;
* **no bare whole-tree `lake build`**; one `lake build <module>` per module, serialized;
* never raise the heartbeat cap, never add `set_option maxHeartbeats`;
* **new files only**; no existing Lean module is edited.

## 7. Verification (per turn)

* tier-0 `lake env lean` at the low cap: exit 0 and **0 warnings**;
* tier-1 `flock … lake build <module>` green;
* `python3 tools/deps/unwired_register.py` regenerates cleanly and the new rows carry a
  `pin original`;
* `git status` shows only the turn's modules (plus the regenerated register);
* a `grep` sweep: no `sorry`/`admit`/`axiom`/`native_decide`, no bare `import Mathlib`,
  no `set_option maxHeartbeats`.

Final turn only (the façade):

* the façade in `PORT_FILES`; the three wrappers and the three `S_` files in `SOURCES`,
  appended last;
* `timeout 300 python3 spec/old_check_stmts.py` — **9,238 → 9,241 identical**, 0
  mismatched / 0 missing, 38 own;
* a one-token mutation on each of the three headlines moves exactly one `mismatched`,
  then revert;
* `#print axioms` on the three headlines is `[propext, Classical.choice, Quot.sound]`;
* a `spec/AutomorphicFormConsumer.lean` zone per turn, executing the headline(s) at a
  concrete `F`/`μ`/`ν`/`φ`.

## 8. Stop and report

Stop and report, with the quotation and the pin line, if: a statement cannot be matched
without moving the pin's text (the leading `let α := …` spelling is the known trap); a
proof needs an unported `Definitions/` module beyond the four gate modules — report the
`import` verbatim; a helper is genuinely needed publicly and is `private` in a hub (**a
promotion is the manager's**); a low-cap failure resists a clean instance fix; or a build
exceeds its bound and bisecting does not settle it. Do **not** open the descendants, the
Tate pair, or the consumers.

## 9. Report shape

Per turn: module paths and line counts; declarations transcribed and the pin range
consumed; substitutions imported; provenance completeness (`N/N`); tier-0 result at the
low cap and tier-1 result; any instance-inference fix; the checker before → after with the
delta reconciled; the mutation tests caught and reverted; `#print axioms`; the consumer
zone; the register diff; anything deferred with its pin line; any stop condition hit. Keep
it short — the manager reads the tree.

## 10. Reproduce

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half \
  --nodes AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half \
  --nodes AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half \
  --json build/weyl_trio_advise.json
python3 port_plan.py --json build/weyl_trio_advise.json --section all
cd ..
python3 tools/deps/unwired_register.py
cd lean
timeout 300 python3 spec/old_check_stmts.py
```
