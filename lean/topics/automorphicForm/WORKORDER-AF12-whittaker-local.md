# WORKORDER-AF12 — the local Whittaker profile: the Casimir equation at a real and a complex place

**Issued 2026-11-02, one dispatch.** Scope: [SET-AF12.md](SET-AF12.md) — §1 the three rows, §2 the
price, §3 the definition gate, §4 the homes, §6 the traps, and **Appendix B, the per-declaration
worklist**. This order states the work, the manager's landed layer, the traps and the gates.

**Audience.** A fresh coding session. Wire: each target module carries its own `spec-pin:` header and
`spec/check_port.py` owns its statements. **No per-declaration markers**: the header is the tracking.
Pin clone `/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`. Port mathlib `v4.34.0`.

**The size.** 3 rows, 1,126 silo, **1,033 lines in 63 declarations to write** (1,070 net by
`port_plan`), in two orders over two files that do not import each other.

## 0. The manager's layer, landed (do not redo it)

1. **The new module exists and is wired.** `AutomorphicForm/Adelic/ArchWhittaker.lean` (skeleton:
   header, imports, opens, empty `namespace AutomorphicForm`) carries **four `spec-pin:` lines** — the
   two `Theorems/` wrappers and the two `S_` files — and `check_port --force` reads **0 ok / 0
   mismatch / 0 missing** (no declarations yet). Its imports are
   `ArchDerivCasimir`, `ArchDerivCasimirComplexAPI`, and the mathlib special-function modules the
   pin's `S_` files name (`Log.Basic`, `Log.Deriv`, `Pow.Deriv`, `Sqrt`, `Trigonometric.Deriv`,
   `Trigonometric.Arctan`, `ExpDeriv`); its opens are the pin's. **Add no import** — if a proof needs
   one that is not reachable, that is a blocker.
2. **The coefficient module gained its eleventh wire** (order B):
   `spec-pin: Theorems/Thm_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul.lean`,
   and `check_port --force` there reads **13 ok / 0 mismatch / 0 missing** — the landing target for
   order B is **14**.
3. **The statements are verified, not assumed.** `lean/tmp/probe-af12-statements.lean` states all
   **three** headlines verbatim from their `Theorems/` wrappers as `example … := by sorry` against
   exactly the two homes, and elaborates silently (three `declaration uses sorry` warnings, nothing
   else). Re-run it before you start; it has already settled that the two modules' opens cover all
   three, including the complex row's ten hypothesis families.
4. **No `Def_` node, no promotion, no migration.** `gate_scan` over the three `Def_` modules of the
   closure: `Def_AutomorphicForm_ArchDerivCasimir` 2/56, `Def_AutomorphicForm_ArchWeightChar` 9/19,
   `Def_AutomorphicForm_ArchDerivCasimirComplex` 3/32 — **0 missing** in all three. `ArchWeightChar`
   is legacy and is imported, never edited; if a proof needs one of its `private` helpers, raise it.
5. **The surface decision is this set's, not yours** (§4 of the set): the pin's two `S_` files are a
   flat **public** surface (70 public declarations, no `private` prelude), so the engine is
   **public at the pin's names**. Write it public; the checker's count should then be **~62 ok**, not
   2. A `MISSING` is a port-side helper the pin does not have (keep that one private); a `MISMATCH`
   on an engine declaration is a spelling to fix, never a reason to privatise.

## 1. What you write

**Order A — `AutomorphicForm/Adelic/ArchWhittaker.lean`** (append; the two rows, 965 lines in 62
declarations by Appendix B):

| row | pin `S_` file | work | shape |
|---|---|---:|---|
| 1 | `S_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight.lean` | **315** / 10 | the pin's `IwasawaAux` chart — `kIw` (the 2-line chart) with `splitTorusGL2_mul`, `splitTorusGL2_mul_unipotentGL2`, `kIw_coe`, `kIw_mem`, `det_kIw`, `archWeightCharℝ_kIw`, `lowerUnipotentGL2_iwasawa`, `inv_sqrt_mul_inv_sqrt`, `sq_sqrt_one_add_sq` — then the 235-line headline |
| 2 | `S_AutomorphicForm_gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype.lean` | **650** / 52 | the pin's `IwasawaC41` chart (`psiK`, `zeta`, `rotR`/`rotS`, `aT`, `xIw`/`uIw`, `flow*`, `cexp_neg_log_half`, `cos_arctan'`, `sin_arctan'`, the `hasDerivAt_*` block, `sum_M1`/`sum_M2`, `deriv*_torus`, `weight_derivH`/`weight_deriviH`, `covariant_deriv`, `deriviwasawa_sum`, …) then the 162-line headline |

Both headlines are **public** at `AutomorphicForm.gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight`
and `AutomorphicForm.gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype`
(the pin's `solution` is the headline's body, as usual). The helpers are public too, in two
**subject-named** sub-namespaces — the pin's `IwasawaAux` → `IwasawaChart` and `IwasawaC41` →
`IwasawaChartComplex` (the `41` is a pipeline label, dropped). Do not nest the headlines inside
those namespaces: the pin keeps `solution` at `AutomorphicForm` level for a reason and the checker
reads the headlines at that name.

**Order B — `AutomorphicForm/Adelic/WhittakerCoefficient.lean`** (append; 68 lines, 1 declaration):
`whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul`, public, under a new
`/-! ## The coefficient's API, VII: the unipotent average at a `diagOne` point -/` section. Its only
premise is AF11's `whittakerCoefficient_unipotentGL2_mul`, in the same module.

## 2. Traps

1. **The five "already in the port" substitution claims are all false (§2 of the set).** `rotR` and
   `rotS` do not map to `ArchCasimirComplex.rotGL` (`rotS s = !![cos s, I sin s; I sin s, cos s]` is a
   different matrix, and `rotGL` is `private` there); `zeta` is **not**
   `ModularCurve.RelIndex.expU` (`exp (t I)` vs `exp (2π i x)`); `sqrt_one_add_sq_pos` is `private` in
   `Iwasawa/Real/Continuation.lean`. Write all of them at the pin's statements.
2. **The complex chart is the whole risk.** 488 lines in 51 small lemmas: read the pin's `S_` file in
   dependency order (the `flow*` abbreviations and `psiK`, then `hasDerivAt_*`, then the
   `sum_M*`/`deriv*_torus` block, then `solution`). The `E₁`/`E₂` matrix families are part of the
   *statement*, not the proof — copy the wrapper.
3. **The port's flows are `archFlowMatrix`/`archFlowMatrixComplex`** (`archFlowAt hw d t =
   archRealGLAt hw (archFlowMatrix d t)`), so the pin's `flowH`/`flowE`/… one-liners become the port's
   `ArchDir`/`archDirMatrix` dictionary, and the pin's `rfl`-level coefficient lemmas may need the
   port's `archMatrixUpdate` spelling (AF11 hit this in rows 8/9).
4. **`linter.style.haveILetI` is live** (FR-0121): use `let`/`have` where the pin has `letI`/`haveI`.
   This set needs no `attribute [local instance]` block (it is archimedean, not adelic) — except order
   B, where the coefficient module already carries its own.
5. **v4.34 renames bite as warnings** (FR-0122): `Real.sqrt_pos`, `Real.log_sqrt`,
   `Complex.norm_exp_ofReal_mul_I`, the `Function.update` → `archMatrixUpdate` family. A warning fails
   the gate, so fix the spelling rather than suppressing.
6. **Binder shadowing for the checker** (FR-0123): the headlines must spell the wrappers' binders
   inline; the probe is the check, not the ok count.
7. **Row 2's conclusion is a long conjunction** (differentiability of each profile and of its
   derivative, then two equations at every `p`), and its hypotheses are six conjunct-wise families
   plus the two matrix identities and the two covariance laws. Destructure the hypotheses in the
   pin's order; an off-by-one in the `hΩ`/`hΩ'` parenthesisation reads as a type error far away.
8. **No name with a pipeline token or an id number.** The pin's `IwasawaAux` → `IwasawaChart` and
   `IwasawaC41` → `IwasawaChartComplex` (§1) are the only renames needed here, but the rule is general:
   never cite `FltWs24.…`, `M4aS4.…`, `P6B.…` or any `…C41`/`…17`-style name from new code (the
   manager removed the last two such citations from the coefficient module at this dispatch, FR-0125).
   If a proof needs a fact that only such a module holds, state the pin's own prelude locally or raise
   it — do not spread the label.
9. No `set_option maxHeartbeats`, no `native_decide`, no `sorry`/`admit`/`axiom`; zero warnings; no
   new module, no hub edit.

## 3. Gates

1. `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` silent on both,
   then each module's own `flock .lake/flt_build.lock timeout 280 lake build
   FLTForHuman.AutomorphicForm.Adelic.<Module>`; **no tree build**, no dependents.
2. `python3 spec/check_port.py --force` on both: `0 mismatch / 0 missing`; the coefficient module
   **14 ok** (13 before), the new module **~62 ok** (measure it). Then apply the recipe's surface
   gate: with `private` dropped on everything the pin has public, re-read the three numbers.
3. `#print axioms` on all three headlines → `[propext, Classical.choice, Quot.sound]`.
4. Zero warnings on both modules.
5. `dedup.py --within` and `move_dead.py --source <path> --target /dev/null --dry-run` per module:
   report every cluster and disposition. A wrapper-over-engine `shape` cluster is the pin's own
   pattern and stays with the reason recorded.
6. `spec/AutomorphicFormSetAF12Consumer.lean` — **one zone**, a real composition, no `#check`, no
   `sorry`: instantiate the real ODE (row 1) at the local component of the adelic coefficient,
   `F h := whittakerCoefficient K (productionPinsOf K D …) (stdAddChar K) φ 1 (g₀ * archRealGLAt hw h)`,
   reading `hD` from AF11's `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt`
   (row 8's first conjunct) and `hΩ` from its Casimir conjunct, and conclude that
   `y ↦ whittakerCoefficient … (g₀ * archRealGLAt hw (splitTorusGL2 (Real.log y / 2)))` satisfies the
   Whittaker equation. It imports the new module and the coefficient module; `lake env lean` it to
   zero errors. If the instantiation forces a hypothesis neither headline supplies, report it rather
   than weakening either headline.
7. `lean/tmp/probe-af12-statements.lean` still elaborates (three `sorry` warnings, nothing else).

## 4. Report

Per order and per row: lines written, declarations written and their public/`private` split, every
worklist entry you dropped and why (with the pin line), the pin line of every deviation, build times
and silence, the two checker counts (before 0 and 13; after whatever you measure), the three
`#print axioms` blocks, `dedup`'s clusters and `move_dead`'s dispositions, the consumer zone's error
count, and one paragraph on the complex chart: whether the pin's `exp (±t/2)`/`arctan` calculus
transcribed cleanly or needed restructuring, with the reason.

**A blocker goes back immediately** — "blocked on `<decl>` at pin `:NNN`; likely needs `<X>`", with
the pin line and the error. Do not grind out a diagnosis, never work around a hub defect locally, and
do not add an import, a module, or a `set_option`.
