# WORKORDER-FTF1 — the factorizable test function is arch-smooth, and its archimedean derivative is a tensor (real place and complex mirror)

**Status: ready to dispatch (2026-10-22).** Pure addition: **two** new modules, no existing module edited.

## 0. The pair

| node | pin `S_` lines | decls |
|---|---:|---:|
| `AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor` | 721 | 85 |
| `AutomorphicForm.IsFactorizableTestFn.isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor` | 723 | 85 |

Both are **ready** (demand = themselves; every premise ported), both are **in the D-S demand** as
leaves, and they are **one development written twice**: after normalising the real↔complex vocabulary
(`archRealLiftAt`↔`archComplexLiftAt`, `ringEquivRealOfIsReal`↔`ringEquivComplexOfIsComplex`,
`archRealGLAt`↔`archComplexGLAt`, `archFlowAt`↔`archFlowAtComplex`, `archDerivAt`↔`archDerivAtComplex`,
`ArchDir`↔`ArchDirComplex`, `ℝ`↔`ℂ`), the two files differ by **10 lines** and their statements by
**3**. Their section skeletons are identical (`LiftAnalysis`, `AffineData`{`FieldOnly`,
`NumberFieldPart`}, `TestData`, `Conv`, …), and **78 of the 85 declaration names are identical**
(the 7 that differ are exactly the real/complex ones).

What the pair says: a factorizable test function `α = fa ⊗ ff` with `fa` an archimedean test factor is
arch-smooth at `w`, and for every archimedean direction `d` the derivative `archDerivAt hw d α` is
again a tensor with the *same* finite factor `ff` and a new archimedean factor `fa'`. The silo builds
the E8 test factor itself (`e8tc*`, `e8l5*`, `e8r5*`, 85 declarations: a determinant-open set, the
matrix inverse/adjugate chart, the lift `archMatrixUpdate`, the flow and its derivative, and the
tensor assembly).

**Demand.** Real node: 5 consumers in the demand (`archCasimirAt_rightConv_eq_smul_of_…`,
`archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt`,
`isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite{,_ofChar,_principal}`). Complex
node: 4 consumers (`…Complex…` twins of the first two and of the last two). Used_by project 5 and 4.

**Premises, all ported** — verified by name, since `Definitions/` modules are not graph nodes:
`IsFactorizableTestFn` / `IsArchTestFactor` / `IsFinTestFactor`
(`AutomorphicForm/Adelic/FactorizableTestFn.lean`), `glArch` / `glFin`
(`NumberTheory/AdelicLevel/Projections.lean`), `archMatrixUpdate` (`Adelic/ArchType.lean`),
`IsArchSmoothAt` / `archDerivAt` / `archFlowAt` / `archRealGLAt` / `archRealLiftAt`
(`Adelic/ArchDerivCasimir.lean`), and the complex twins `IsArchSmoothAtComplex` /
`archDerivAtComplex` / `archFlowAtComplex` / `archComplexGLAt` / `archComplexLiftAt` /
`ringEquivComplexOfIsComplex` / `ArchDir*` (`Adelic/ArchDerivCasimirComplex.lean` and
`…ComplexAPI.lean`). Nothing to home.

## 1. Deliverable — two modules, one order

**Real**, `FLTForHuman/AutomorphicForm/Adelic/FactorizableTestFnArchSmooth.lean`:
helper declarations under `namespace AutomorphicForm.IsFactorizableTestFn`, and the headline
`AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor` verbatim from the
wrapper.

**Complex mirror**, `FLTForHuman/AutomorphicForm/Adelic/FactorizableTestFnArchSmoothComplex.lean`:
helper declarations under **`namespace AutomorphicForm.IsFactorizableTestFn.Complex`** (a sub-namespace
of the same subject — the 78 shared last names forbid putting them beside the real helpers), and the
headline `AutomorphicForm.IsFactorizableTestFn.isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor`
verbatim from its wrapper.

Why two modules rather than one engine: the two developments are textually one, but their types are
not — a real place's derivative is the `GL(2, ℝ)`-direction `ArchDir` and the complex place's is
`ArchDirComplex` over `GL(2, ℂ)`, and the lifts, the GL maps and the flows are distinct ported
definitions. A single generic development would need an abstraction over the archimedean field built
first; that is a design job of its own, not this set. This is the same decision the port already made
for `ArchCasimir` / `ArchCasimirComplex` (the complex engine went to a separate namespace,
`AutomorphicForm.ArchCxGL`). Record the option in this order's landed section (or the set's log) —
`CARRY-FORWARD.md` is for open issues, not for design options or lessons learned.

* Imports: the ported definition/API modules the silo needs — at least
  `FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir` (real) /
  `…ArchDerivCasimirComplex` + `…ArchDerivCasimirComplexAPI` (complex),
  `FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn`,
  `FLTForHuman.NumberTheory.AdelicLevel.Projections` (for `glArch`/`glFin`), and the narrow
  `Mathlib.*` modules the pin's own import block names (no `import Mathlib`).
* Drop the pin's `P2MW.S_<stem>` wrapper namespaces, the `p2m_open`/`p2m_export`/`p2m_reactivate`
  staging, and any pin import the file never uses — check with `grep` and say which in the report.
* Keep the pin's phase **sections** (`LiftAnalysis`, `AffineData`, `FieldOnly`, `NumberFieldPart`,
  `TestData`, `Conv`, …) in both modules; they are what makes 720 lines navigable.
* Header docstring in the port's style: subject, pin source with pinned URLs (`aa2d8b3`), the two
  `spec-pin:` lines, the drift note, `set_option autoImplicit false`.
* Public/private: the pin's declarations public at the pin's last names, the pin's `solution` a
  **private** twin; the headline public. Expect `ok` = each module's public count (the pin's 85
  declarations are 84 helpers + `solution`, plus the separate headline).

Wiring: each module's own `spec-pin:` header — its `Theorems/Thm_…` wrapper first, then its
`P2M/Sol/S_…` comparable copy. No declaration-level marker is needed for a statement to be checked;
`spec/decl_markers.tsv` is for genuine exceptions only (report instead of adding rows).

## 2. Order of work — the mirror is written, not re-derived

1. **Real module first**, phase by phase, until it is green and frozen.
2. Then produce the **complex module from the real one by substitution** — this is legitimate and it
   is exactly what the pin did — but every line you touch must be re-elaborated and every statement
   must be the complex pin's text verbatim. Report every substitution that did **not** go through:
   the ported complex API may differ from the real one in more than the vocabulary (`ArchDirComplex`,
   `ringEquivComplexOfIsComplex`, the `IsComplex` hypotheses), and those are the interesting sites.
3. If a substituted declaration cannot be made to typecheck at all, that is a stop-and-report, not a
   reason to restate a statement.

## 3. Names

Keep the pin's last names (`e8tc_*`, `e8l5_*`, `e8r5_*`, `E8Ent`, …). They are pin tokens in the same
class as `Ecf` in AC3 — unreadable and unsearchable — but they are *statement* names in a tight DAG
(`e8l5_archEntries` appears in dozens of statements), so renaming them rewrites the statements that
mention them and is not this order's work. Do not privatise anything to gain a spelling.

## 4. Build discipline — read before the first compile

From `lean/`, always through the lock:

```bash
flock .lake/flt_build.lock timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/AutomorphicForm/Adelic/FactorizableTestFnArchSmooth.lean
```

A finished file: `flock .lake/flt_build.lock timeout 120 lake build FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmooth`
(and the `…Complex` twin).

* **The 200,000 cap is a diagnostic.** No `set_option maxHeartbeats`, no
  `synthInstance.maxHeartbeats`, ever; the pin's bumps are not inherited.
* **Bound the floor first** for the real module: a `lean/tmp/` copy with every proof `sorry` gives the
  floor in one run. If the floor aborts, the cost is in the frozen types; levers in order: an unused
  section variable becomes a `haveI`/term-`letI` in the proof that needs it, `private abbrev` aliases,
  then stop and report. The complex module inherits the real one's floor — probe it only if it
  differs.
* **Probes, not bisection** (`porting-playbook.md` §3.5): statement-vs-proof; isolate with earlier
  proofs stubbed; shrink the statement, not the file; one kept `diagnostics` trace;
  `trace.Meta.isDefEq` at `-DmaxHeartbeats=3000` only when the counters are the question. A probe over
  60 s is the probe's fault.
* **Bound, do not measure**: no `time`; anything that can plausibly run a minute is a **background
  job** with its own `timeout` and a log you read afterwards. One probe, one edit, one bounded compile
  per turn; every tool call under two minutes; no bare or whole-tree `lake build`.
* Expected risk: `ContinuousOn`/`HasFDerivAt` over `Matrix (Fin 2) (Fin 2) 𝕜` and the
  `archMatrixUpdate` chart — a slow declaration is an instance-inference or defeq problem; give the
  type one syntactic form, never a bump.

## 5. Gates

```bash
cd lean
flock .lake/flt_build.lock timeout 120 python3 spec/check_port.py --force \
  FLTForHuman/AutomorphicForm/Adelic/FactorizableTestFnArchSmooth.lean \
  FLTForHuman/AutomorphicForm/Adelic/FactorizableTestFnArchSmoothComplex.lean
# expected per module: 0 mismatch, 0 missing, 0 own, 0 kw, ok = that module's public count
python3 spec/check_port.py --changed --strict-markers
```

plus: 0 warnings in both; `#print axioms` on both headlines `[propext, Classical.choice, Quot.sound]`;
no `sorry`/`admit`/`native_decide`/`import Mathlib`; only `set_option autoImplicit false`; `git status`
adds exactly two files.

## 6. Stop and report — do not improvise — if

an existing module must change (declaration, host, `tools/deps/build_ladder.py --edit` price); the
proof needs a statement from another pin node (both silos cite none — a new citation is a real
finding); a heartbeat raise looks necessary (give the statement-only probe at 200k and the reading); a
headline reads `MISMATCH`; the complex substitution cannot be made to typecheck at some statement; or
a `spec/decl_markers.tsv` row looks needed.

## 7. Report shape

(i) per module: lines, declaration count, public/private split, public surface, and the namespace
used; (ii) the checker readings, `--changed --strict-markers`, the two builds' jobs/warnings;
(iii) axioms; (iv) every proof deviation from the pin with its site, and **the full list of
substitutions that did not go through mechanically** in the complex mirror; (v) names carried, the
wrapper/staging dropped, and the unused pin imports dropped; (vi) **open issues only** for
`CARRY-FORWARD.md` (a deferred declaration, a marker row, an API gap someone must act on) — the
shared-engine option of §1 and every other lesson go into this order's landed section or the set's
log, not into that file; (vii) `git status`; plus the floor probe and the pin ranges consumed.

Records: [TOPIC-mathlib-module-homing.md](../TOPIC-mathlib-module-homing.md),
[porting-playbook.md](../../porting-playbook.md) §3.1–§3.5, §4–§6,
[TOPIC-arch-casimir.md](TOPIC-arch-casimir.md) (the real/complex mirror precedent and its tiers),
[WORKORDER-DNR1](../algebraicCurve/WORKORDER-DNR1-deuring-norm-residue.md) (the previous cut and its
landed numbers).

## 9. Landed (2026-10-23)

Two new modules, no existing module edited.

`FLTForHuman/AutomorphicForm/Adelic/FactorizableTestFnArchSmooth.lean` — **781 lines, 86
declarations = 85 public + 1 private** (the pin's `solution` twin, private at :757). Namespace
`AutomorphicForm.IsFactorizableTestFn`; the pin's sections kept (`LiftAnalysis` :89, `AffineData`
:174 with `FieldOnly` :178 / `NumberFieldPart` :277, `TestData` :299, `Conv` :429,
`LeftDerivFactor` :484, `RightDerivFactor` :608); the headline
`AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor` at :769, verbatim
from its `Theorems/` wrapper (:15–24), proved by `solution K w hw α hα`. Public surface: the 84
helpers at the pin's last names (`E8Ent`, `e8DetSet`, `e8Inv`, `e8leftDeriv`, `e8tc_*` ×8,
`e8l5*` ×60, `e8r5*` ×12) plus the headline.

`FLTForHuman/AutomorphicForm/Adelic/FactorizableTestFnArchSmoothComplex.lean` — **776 lines, 86
declarations = 85 public + 1 private**. Helpers under
**`AutomorphicForm.IsFactorizableTestFn.Complex`** (engine in `noncomputable section E8Engine` :74,
`:72` opens the sub-namespace, `:750` closes it); the headline at :764 at the pin's full name
`…isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor`, in the outer namespace, verbatim from the
complex wrapper (:15–24). Same six sections (`LiftAnalysis` :84 … `RightDerivFactor` :604). 78 of the
85 pin last names are shared; the seven that are not are `e8l5_coe_archComplexGLAt`,
`e8l5_glFin_archComplexGLAt`, `e8l5_isFactorizableTestFn_archComplexGLAt_mul`,
`e8l5_archFlowAtComplex_inv`, `e8l5_archFlowAtComplex_eq_lift`, `e8l5_glFin_archFlowAtComplex`,
`e8r5_archDerivAtComplex_eq`.

| gate | real | complex |
|---|---|---|
| `check_port --force` | **85 ok**, 0 mismatch, 0 missing, 0 own, 0 kw | **85 ok**, 0 / 0 / 0 / 0 |
| `--changed --strict-markers` | 4343 ok, 0 mismatch, 0 missing, 12 own (pre-existing), 0 kw — 167 modules, 0 stale markers, exit 0 | (same run) |
| `lake build …ArchSmooth` | green, 3535 jobs, **0 warnings** | green, 3537 jobs, **0 warnings** |
| edit loop at 200k | exit 0, empty log | exit 0, empty log |
| `#print axioms` (headline) | `[propext, Classical.choice, Quot.sound]` | `[propext, Classical.choice, Quot.sound]` |
| hygiene | `set_option autoImplicit false` :71 only; no `sorry`/`admit`/`native_decide`/`import Mathlib` | `:63` only; same |

**Floor.** Statements are cheap: a `lean/tmp/FTF1RealFloor.lean` copy with all 62 theorem proofs
`sorry` — statements, the 21 `def`s, the 3 `abbrev`s and every section variable verbatim —
elaborates at 200k in one pass, 0 errors. The floor is in the proofs, and the unchanged module then
closes at the same cap in one pass: no abort, no bisection, no lever (`haveI`, `private abbrev` and
statement changes all unnecessary). The complex module inherits that floor and was not re-probed.
The `ContinuousOn`/`HasFDerivAt` over `Matrix (Fin 2) (Fin 2) 𝕜` and `archMatrixUpdate`-chart risk did
not materialise: the pin's own syntactic form was kept everywhere, the explicit
`ContinuousLinearMap.proj (R := ℝ) (φ := …)` spellings and `Matrix.GeneralLinearGroup.mkOfDetNeZero`
included, so no `isDefEq` was left to guess a type.

**Proof deviations.** Real, two sites, one kind: `continuousOn_iff_continuous_restrict` →
`continuousOn_iff_continuous_domRestrict` at :155 and :170 (the v4.34 deprecation; keeping the pin's
name costs two warnings). Complex: the same two sites, the pin's own non-substitution site (kept
verbatim, first below because it is the interesting one), and two deviations the two-namespace
split forces — all proof-side:

1. `e8tc_contDiffOn_tcInv` — the pin's complex copy itself is not the vocabulary map: the real proof
   is `.div e8tc_contDiff_det.contDiffOn fun _ he => he`, the complex one is
   `….contDiffOn.mul (….contDiffOn.inv …) |>.congr fun _ _ => div_eq_mul_inv _ _` (:111–112). This
   is the one line where "the same development written twice" is not literally a substitution.
2. `fun e _ => div_eq_mul_inv _ _` → `fun _ _ => …` (:112): the pin's binder is unused and the port's
   `linter.unusedVariables` is on; the pin's text would have warned.
3. `solution`/headline: the headline's proof is `Complex.e8r5_main hw α hα` (:762), qualified because
   the two-namespace split puts `solution` in the outer namespace and the engine in `.Complex`; the
   pin had one namespace, so its wrapper could name the twin unqualified.

**Substitutions that did not go through mechanically in the complex mirror** (the full list): the
site of (1) above; the two `continuousOn_iff_continuous_domRestrict` sites; the `fun _ _` binder;
and the two scaffolding moves the two-namespace decision forces — the qualified `Complex.e8r5_main`
and the *named* engine section (`noncomputable section E8Engine`, `end E8Engine` at :748). The last
one is a tooling artefact worth knowing: `spec/lean_parser.ENCLOSE_RE` reads `end` followed by
`\s+ [\w.']+`, and `\s` crosses blank lines, so a bare `end` followed by a line `end Name` is taken
as a *single* event whose endname is the word `end` of the second line — the second `end` is
consumed and the frame it closes stays open. Here that mis-named the private twin
`…Complex.AutomorphicForm.IsFactorizableTestFn.solution`, which would have mis-keyed the checker and
any consumer; naming the section makes both `end`s explicit and the scan exact. Everything
else — the vocabulary map of §1 plus `ℝ`→`ℂ` on `E8Ent`, the `Matrix (Fin 2) (Fin 2) 𝕜`, `GL₂`, the
chart maps `e8l5AddHom`/`e8l5Lin`/`e8l5LinMat` and the curve `e8l5Curve` — went through mechanically;
the flow's `(-1 : ℝ) •` stays real, as at the pin. No statement anywhere deviates: the checker
hashes all 85 public declarations per module as identical to the pin.

**Names, staging, imports.** The 84 engine names are carried verbatim (`e8tc_*`/`e8l5_*`/`e8r5_*`
included: they are statement tokens in a tight DAG). Dropped: the `P2MW.S_<stem>` wrapper namespace
and its `open`s; the `Theorems/` wrappers' `p2m_exact_reverting` glue (no such tactic here, so the
headline's proof is the `solution` body); `P2M.Util`; and the three pin imports the code never uses —
`Definitions.Def_AutomorphicForm_RightConvolution`,
`Definitions.Def_AutomorphicForm_CuspidalConstituent` (only its `open` appeared, and the body never
needs it) and, in the complex module, the same list. The pin's 17-module `Mathlib.*` block is cut to
the 8 the file's own lemmas name (`ContDiff.Operations`, `Deriv.Mul`, `Matrix.Adjugate`,
`Matrix.NonsingularInverse`, `Topology.Algebra.Constructions`, `Topology.Algebra.Module.FiniteDimension`,
`Topology.Instances.Matrix`, `Topology.Instances.RealVectorSpace`); the other nine are reached
transitively through the port's own modules, verified by the module compiling at the same cap
without them. The port modules are `ArchDerivCasimir` + `FactorizableTestFn` + `Projections` (real)
and `ArchDerivCasimirComplex` + `ArchDerivCasimirComplexAPI` + `FactorizableTestFn` + `Projections`
(complex).

**Pin ranges consumed.** Real: `S_…` 32–705 verbatim (declarations 34–704), 707–709 (the three
`open`s) replaced by the port's two, 711–721 (`solution`) with `private` added; 1–31 replaced by the
port's header/imports/namespace. `Theorems/Thm_…` 15–24 (statement; :24's `p2m_exact_reverting`
dropped). Complex: `S_…` 33–707 verbatim, 709–711 replaced, 713–723 (`solution`) with `private`
added; 1–32 replaced. `Theorems/Thm_…` 15–24 likewise.

**The shared engine (§1), recorded and declined.** The pair is one development twice — the two
`S_` files differ by 10 lines, and this port's two modules by 78 shared names and ~700 shared body
lines — so a single generic development over the archimedean place is tempting. It would cost an
abstraction over the place's field (a structure carrying `𝕜`, `ringEquiv…OfIs…`, `archLiftAt`,
`archGLAt`, `archFlowAt`, `ArchDir`, `archDerivAt`), and the price is the one thing this set is for:
a generic helper's *statement* is not the pin's, so the checker could diff none of the 84 helpers
and both modules would need `own:` rows for all of them. The pair verifies only because every helper
carries its pin statement text. That is the same conclusion `ArchCasimir`/`ArchCasimirComplex`
reached, where the complex engine went to its own namespace (`AutomorphicForm.ArchCxGL`) instead of
being generalised. A future refactor that wants the dedup should do it as a *third* generic engine
behind both mirrors, leaving the two mirrored surfaces as the diffs — not by rewriting the mirrors.
