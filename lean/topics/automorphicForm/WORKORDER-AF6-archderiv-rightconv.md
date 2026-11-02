# WORKORDER-AF6 — differentiating right convolution along an archimedean flow: two modules, two headlines

**Status (closed 2026-11-02): landed and reviewed green.** One worker dispatch, two new modules, **two
public headlines**, no blocker at any point:

| step | module (Δ lines) | checker | build | axioms |
|---|---|---:|---|---|
| R1 | `Adelic/ArchDerivRightConv.lean` (**new, 802**: 41 `private` + 1 public) | **1 ok** / 0 / 0 | silent, 7.0 s fresh | clean |
| R2 | `Adelic/ArchDerivRightConvComplex.lean` (**new, 808**) | **1 ok** / 0 / 0 | silent, 16 s fresh | clean |
| — | consumer probe `spec/AutomorphicFormSetAF6Consumer.lean` (**+144**, 4 zones, 9 examples) | — | 0 errors | — |

R2 compiled **first try** by the pin's vocabulary map. `dedup --within`: 0 clusters.
`move_dead` reported 6 declarations / 109 lines per module, all dead in the pin too (measured, one
occurrence each) — the pin's unreachable mathematics, which playbook §3.8 says to port rather than drop
at transcription time. The **review** then triaged and disposed of them (SET-AF6 §1.7): one deleted
(`l5_continuous_rightConv`, the first conjunct of SET-AF5's public headline — a duplicate, not dead
content) and five shelved into `Reserve/…ArchDerivRightConv{,Complex}Dead.lean`, so both live modules
now read **0 declarations / 0 lines dead** and the modules are 696 / 702 lines.
§1.6 of the brief records the five deviations (the one missing import `MulRightInvariant`, the two
v4.34 spellings, the `liftM`-vs-`root_.liftM` ambiguity, the pin's file-local names, the imported
`lift_leftDeriv_tensor`), the statement check of the 72 Appendix-A twins (**all imported, 0 restated**),
and Appendix B's five-name over-count. The original order follows unedited as the record of what was
asked.

**Status as issued (2026-11-02): the manager's layer is landed and frozen; the two proof bodies are
this order.** Scope: [SET-AF6.md](SET-AF6.md) — read §0.5, §1.5, §2, §3 and §5 before starting; §1.3
and its two appendices are your shopping list.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md) §3–§5;
wire: the per-module protocol — a `spec-pin:` header, `spec/check_port.py`, no in-source
per-declaration marker. Pin clone `/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`.

**Two new files, two public headlines, 2,494 raw pin lines, ≈1,450 lines to write** (the other 491 per
file is imported — §2). **R2 is R1 by substitution**, so write R1 completely first, then transcribe R2
by the vocabulary map. Log every build in `lean/tmp/`. Report a blocker as soon as one appears (§6);
never leave a `sorry` in the tree.

## 1. What the ground gives you (frozen — do not edit)

| declaration | module | what it is |
|---|---|---|
| `IsFactorizableTestFn.lift_*` / `chart_*` (72 declarations) | `AutomorphicForm/Adelic/FactorizableTestFnArchSmoothLeft.lean` (**new this set**, public) | the **left** half of the arch chart: the chart maps `liftCD`/`liftLD`/`liftPhi'`, the multipliers, the compact support, and the left derivative `leftDerivFactor` with `lift_leftDeriv_tensor` |
| the same names under `IsFactorizableTestFn.Complex` | `…FactorizableTestFnArchSmoothComplexLeft.lean` (**new**, public) | the complex mirror (5 declarations restored there beyond the real half's 4) |
| `IsFactorizableTestFn.flow_*`, `lift_*` (55 declarations) | `…/FactorizableTestFnArchSmooth{,Complex}.lean` | the **right** half — the `isArchSmoothAt_and_archDerivAt_eq_tensor` engine |
| `AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn` | `…/RightConvRegularity.lean` (SET-AF5) | `rightConv`'s continuity and its `C^∞` behaviour along the unipotent line |
| `AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` | `…/RightConvolution.lean` (SET-AF5) | the translation law |
| `AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn` | `…/TestFnTop.lean` | the decomposition's continuity + compact support |
| `archDerivAt`, `IsArchSmoothAt`, `ArchDir`, `archFlowAt`, `archRealGLAt`, `archFlowMatrix` | `…/ArchDerivCasimir.lean` | the real definition layer (`Def_`-wired, checked) |
| `archDerivAtComplex`, `IsArchSmoothAtComplex`, `ArchDirComplex`, `archFlowAtComplex` | `…/ArchDerivCasimirComplex.lean` | the complex one |
| `IsArchSmoothAtComplex.archDerivAtComplex` and the chart API | `…/ArchDerivCasimirComplexAPI.lean` | the derivative's defining properties — check here before re-deriving |

**Do not re-prove, restate or move any of those**, and do not add a `private` copy of an `lift_*`
declaration into your module: the two new left-half modules exist exactly so that you import them.

## 2. The two files

### R1 — `FLTForHuman/AutomorphicForm/Adelic/ArchDerivRightConv.lean`

Header: a `/- … -/` block (a `--` header line mis-aligns the checker's namespace tracker), the subject
sentence, and exactly two wires:

```
spec-pin: Theorems/Thm_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn.lean
spec-pin: P2M/Sol/S_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn.lean
```

Imports — the workorder fixes this list; add nothing else without a reason in your report:

```lean
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothLeft
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmooth
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplexAPI
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
```

**The headline** — the wrapper's statement verbatim, in `namespace AutomorphicForm`, public, at the
pin's name:

```lean
theorem AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) :
    (∀ φ α : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsFactorizableTestFn K α →
      IsArchSmoothAt hw (rightConv K φ α) ∧
        archDerivAt hw d (rightConv K φ α) =
          rightConv K φ (fun y => deriv (fun t : ℝ => α (archFlowAt hw d (-t) * y)) 0)) ∧
    (∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa →
        ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
          (fun y : AdelicGL2 (𝓞 K) K =>
              deriv (fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) *
                ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y))) 0) =
            fun y => fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
    (∀ φ γ ω : AdelicGL2 (𝓞 K) K → ℂ,
      Continuous φ → IsArchSmoothAt hw φ → Continuous (archDerivAt hw d φ) →
      Continuous γ → HasCompactSupport γ → IsArchSmoothAt hw γ → Continuous (archDerivAt hw d γ) →
      Continuous ω → (∀ (y : AdelicGL2 (𝓞 K) K) (t : ℝ), ω (y * archFlowAt hw d t) = ω y) →
        rightConv K φ (fun y => archDerivAt hw d γ y * ω y) =
          -rightConv K (archDerivAt hw d φ) fun y => γ y * ω y)
```

**Everything else stays `private`** (the pin's 113-declaration prelude minus the 66 you import, i.e. the
47 of Appendix B), and the pin's namespaces (`P2MW.S_…`, its sections) are dropped — the declarations
are `AutomorphicForm`'s, as their statements are.

### R2 — `FLTForHuman/AutomorphicForm/Adelic/ArchDerivRightConvComplex.lean`

The same, at `hw : w.IsComplex`, `d : ArchDirComplex`, `archDerivAtComplex`, `IsArchSmoothAtComplex`,
`archFlowAtComplex`, `archFlowMatrixComplex`, `archComplexGLAt`, chart `Fin 2 → Fin 2 → ℂ`, with
`FactorizableTestFnArchSmoothComplexLeft` + `FactorizableTestFnArchSmoothComplex` +
`ArchDerivCasimirComplex` in place of the real ones. Headline name
`AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn`, wires to its
own `Thm_`/`S_` pair. **It must be its own module**: the two engines share 52 last names, so one module
cannot import both.

## 3. The rename map (pin → port), for both files

| pin | port |
|---|---|
| `E8Ent` | `ArchEntry` |
| `e8DetSet` | `nonsingEntries` |
| `e8Inv` | `invEntries` |
| `e8tc_*` | `chart_*` |
| `e8l5*` | `lift*` (`e8l5Phi'` → `liftPhi'`, `e8l5MulR` → `liftMulR`, `e8l5cD` → `liftCD`, `e8l5M` → `liftM`, `e8l5LD` → `liftLD`, `e8l5Dir` → `liftDir`, …) |
| `e8r5*` | `flow*` |
| `e8leftDeriv` | `leftDerivFactor` |
| `l5*` / `tc_*` (the copies inside your two `S_` files) | the same map: `l5_*` → `lift_*`, `l5cD` → `liftCD`, `tc_*` → `chart_*` |

**Your first act (§0.5 of the brief): for each of the 66 names in SET-AF6 Appendix A, read the port
declaration's statement and only then decide it is the twin you need.** The list was produced by the
rename map, not by a statement diff — `port_advise` cannot see renamed copies, and a name match that is
*not* statement-identical must be reported, not papered over (a local `private` re-statement at the
pin's shape is then the right answer, and it goes in your report).

## 4. The traps (measured, all of them from the pin)

1. **`leftDerivFactor`, not `archDerivAt`, on the moving side.** The derivative of `y ↦ α (archFlowAt hw d (-t) * y)` at
   `t = 0` is the *left* derivative; the bridge to the chart is `lift_leftDeriv_eq` (imported). Using
   the right derivative produces a **false statement**, not a failed proof.
2. **The `ε`-estimate lives on the chart, not on `φ`.** `lift_exists_compact_support` (imported) is the
   domination that makes the `Conv` section work.
3. **`af_family` (57 lines) is the set's real new mathematics** — the closed form of the chart along the
   flow — and has no port twin. Same for `l5_archDerivAt_rightConv` (62), `l5_continuous_rightConv` (56)
   and `l5_rightConv_archDerivAt_mul` (44). Write them; do not hunt for a substitution.
4. **`IsArchSmoothAt` is a `def`**, so `archDerivAt`'s own properties come from
   `ArchDerivCasimirComplexAPI` (`IsArchSmoothAt*.archDerivAt*`). Check the API first.
5. **`set_option linter.style.haveILetI false in`** on a declaration whose proof keeps the pin's
   `letI := glBorel` / `haveI := borelSpace_…, isHaarMeasure_…` wall — otherwise four warnings and the
   build is not silent (the AF5 precedent).
6. **`ContDiff ℝ (⊤ : ℕ∞)`** still lands as `∞` in v4.34: no edit needed (AF5 measured it).
7. **`fun_prop` after `fin_cases … simp`** in the entry-wise continuity blocks.

## 5. Build and check discipline

- iterate with `lake env lean FLTForHuman/AutomorphicForm/Adelic/ArchDerivRightConv.lean`;
- write the olean with `flock .lake/flt_build.lock timeout 280 lake build <module>`; **no tree build**,
  no dependents (both modules have 0 importers);
- log builds in `lean/tmp/`;
- `python3 spec/check_port.py --force <module>` → **1 ok / 0 mismatch / 0 missing**;
- `#print axioms <headline>` → `[propext, Classical.choice, Quot.sound]`;
- `python3 ../tools/deps/dedup.py --within --module <module>` (report only);
  `move_dead.py --dry-run` (expect 0 real dead; a `local instance` report is FR-0104's false positive);
- **zero warnings**; no `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats`.

## 6. The consumer probe

New file `spec/AutomorphicFormSetAF6Consumer.lean`, **two zones**, one per row, each a real composition
(no `#check`):

* zone A composes R1's **first** conjunct with `RightConvRegularity`'s continuity
  (`Continuous (rightConv F φ α)` from both, so the zone dies if either module goes) and re-indexes the
  derivative identity through `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply`;
* zone B reads R1's **third** conjunct at `ω ≡ 1` (the adjointness) and composes it with the second
  conjunct's tensor form — i.e. an actual `rightConv` identity, not a `#check`.

Zone C/D for R2 mirror them at a complex place. A `mixedEmbedding.mixedSpace`-typed example needs
`open scoped Classical` (AF5's measured note). Error count is the metric: **0**.

## 7. Report

Report back: each module's line count; the checker's three numbers; the axioms line; the build time and
its silence; the dedup/move_dead verdicts; the consumer probe's error count; **how many of the 66
Appendix-A imports you actually used** and how many needed a local re-statement (and why); and every
deviation from the pin. A blocker goes back as soon as it is hit, with the pin line and the error.
