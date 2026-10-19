# WORKORDER-AC2 — the real-place `CasCore` trio (set A)

**Set A of the arch-Casimir subject.** One shared engine, three public headlines. Its only premise
is [WORKORDER-AC1-defs.md](WORKORDER-AC1-defs.md), which has **landed**; the mathematics and the
measurements are [TOPIC-arch-casimir.md](TOPIC-arch-casimir.md) §1–§3.

**Status: landed**, with the "public surface" instruction superseded by the tier-3 exemption (§3).
The landed numbers are in §10.

## 1. Scope

Port the three real-place headlines, which the pin wrote three times over one 64-declaration engine:

| headline (public, exact pin name) | pin `S_` file | lines |
|---|---|---:|
| `AutomorphicForm.archCasimirAt_rightTranslate_archRealGLAt` | `S_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt.lean` | 569 |
| `AutomorphicForm.leftCasimir_eq_archCasimirAt_of_isArchSmoothAt` | `S_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt.lean` | 856 |
| `AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul` | `S_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul.lean` | 917 |

Raw 2,342 → **1,208 net new math lines** (`port_advise`/`port_plan` on the three targets: 1,068
duplicate copies removable, 66 boilerplate, 133 groups, 0 substitutions).

**Not this set, in any form:**

* the complex mirror (`archCasimirAtComplex_*`, 35 files) — it needs the Complex definition pair
  homed first, which is a separate manager wave;
* the two `…_rowIsometryInclAt_of_ne` siblings (133, 110) and the other 37 real-place proof files —
  set C, ordinary scheduling later;
* the definition layer — already landed, do not touch those two modules;
* `spec/old_check_stmts.py` and any other wiring: **the manager wires**. Do not edit it, do not
  run the checker for a delta, do not add yourself to `SOURCES`/`PORT_FILES`;
* any edit to an existing port module (the hub prohibition, §8).

## 2. The pin's duplication, exactly

The three `S_` files are one development written three times. Byte-normalised at the `private`
marker and the `namespace P2MW.S_…` line, the shared prefix is 552 lines; the instrument counts
**56 names / 538 declaration lines shared by all three**. The block map is:

**Block `CasCore17` — 64 declarations, written ONCE in the port.** Present in all three files at the
same line numbers, the same statements, differing only in the `private` marker (`private` throughout
in `iterate_raise…`; public elsewhere) and in the pin's `_root_.`-prefixed shadow copies in
`leftCasimir…`. In dependency order:

1. *lift algebra*: `archRealGLAt_eq_archRealLiftAt`, `archRealGLAt_mul_archRealLiftAt`, `conjArr`,
   `det_conjArr`, `archRealLiftAt_mul_archRealGLAt_eq`;
2. *the chart*: `chart`, `chart_rightTranslate`, `conjCLM`, `conjCLM_apply`, `coe_conjCLM`,
   `conjArr_one`, `U`, `one_mem_U`, `D1`, `contDiffAt_chart`, `hasFDerivAt_chart`,
   `archDerivAt_apply_mul_archRealLiftAt`, `archDerivAt_eq_D1`;
3. *right translation*: `isArchSmoothAt_rightTranslate`, `conjCLM_of_symm`,
   `archDerivAt_rightTranslate`, `D2`, `hasDerivAt_flow_entries`, `hasDerivAt_flow_mul_const`;
4. *mixed partials and commutation*: `archDerivAt_archDerivAt_eq`, `D2_symm`, `D1_sub`, `D1_add`,
   `D1_smul`, `archDerivAt_comm`;
5. *the adjoint action*: `AdM`, `trace_archDirMatrix`, `AdM_traceless`, `eq_smul_archDirMatrix`,
   `cf`, `Dconj`, `isArchSmoothAt_Dconj`, `Dconj_apply`, `D1_AdM`,
   `archDerivAt_rightTranslate_eq_Dconj`, `archDerivAt_Dconj`, `rightTranslate_combo`, `AdM_eq`;
6. *the nine structure coefficients* `cf_H_H … cf_Fm_Fm` and the three brackets
   `bracket_H_E` (`[H,E] = 2E`), `bracket_H_Fm` (`[H,F⁻] = -2F⁻`), `bracket_E_Fm` (`[E,F⁻] = H`);
7. *the relations*: `rel_E_H`, `rel_Fm_H`, `rel_Fm_E`;
8. *continuity*: `continuous_rightTranslate`, `continuous_Dconj`, `continuous_archDerivAt_Dconj`;
9. *the Casimir*: `casimir_identity`, `archCasimirAt_rightTranslate`, `package`.

**Tail of headline 1 (`archCasimirAt_rightTranslate_archRealGLAt`): none.** Its statement is
`CasCore17.archCasimirAt_rightTranslate` + `CasCore17.package` applied to `m : GL (Fin 2) ℝ`; the
`S_` file's only extra declaration is `solution`.

**Tail of headline 2 (`leftCasimir_eq_archCasimirAt_of_isArchSmoothAt`): 28 declarations**, in three
namespaces after `CasCore17`:

* `CommAway17` (8): `archRealLiftAt_mul_comm`, `archFlowAt_mul_comm`,
  `isArchSmoothAt_rightTranslate`, `archDerivAt_rightTranslate`, `archCasimirAt_rightTranslate`,
  `continuous_rightTranslate`, `package`, `archRealGLAt_mul_rowIsometryInclAt₀_comm`;
* `Elem17LR` (6): `glArch_ext`, `glArch_archRealGLAt`, `archComponent_glArch_archRealGLAt_self`,
  `archComponent_glArch_archRealGLAt_of_ne`, `glFin_archRealGLAt`,
  `archRealGLAt_mul_comm_of_archComponent_eq_one`;
* `CasLR17` (14): `Ld`, `hasDerivAt_negflow_mul_const`, `hasDerivAt_const_mul_negflow`,
  `negflow_mul_lift`, `Ld_apply_lift`, `Ld_one`, `Ld_Ld_one`, `leftCasimir_one`,
  `rightTranslate_mul`, `Ld_rightTranslate`, `exists_decomp`, `archCasimirAt_rightTranslate_any`,
  `isArchSmoothAt_rightTranslate_any`, `leftCasimir_eq`.

`Ld` is the pin's left Casimir `fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0`
— the statement's own `let L`; the headline is `CasLR17.leftCasimir_eq` unfolded.

**Tail of headline 3 (`iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul`): 38
declarations** in one namespace `OsAlg17`: `Dk`, `lower`, `raise`, `smooth_sub`,
`archDerivAt_sub'`, `smooth_Dk`, `smooth_lower`, `smooth_raise`, `archDerivAt_lower`,
`archDerivAt_raise`, `lower_apply`, `raise_apply`, `Dk_apply`, `weight_deriv`, `weight_apply`,
`Dk_lower`, `Dk_raise`, `relF_E_H`, `relF_Fm_H`, `relF_E_Fm`, `casimir_apply`,
`archDerivAt_casimir`, `casimir_comm_H`, `casimir_comm_E`, `casimir_comm_Fm`, `casimir_comm`,
`casimir_lower`, `casimir_raise`, `raise_lower`, `lower_raise`, `lower_smul`, `raise_smul`,
`raise_iter_smul`, `lower_iter_smul`, `lower_iter_props`, `raise_iter_props`,
`raise_iter_lower_iter`, `lower_iter_raise_iter`. `lower`/`raise` are the `let`-bound operators of
the statement; `lower_iter_props`/`raise_iter_props` are the `∀ j` conjuncts and
`raise_iter_lower_iter`/`lower_iter_raise_iter` the two `∀ M` product identities.

## 3. Deliverable

One module, `FLTForHuman/AutomorphicForm/Adelic/ArchCasimir.lean`, next to the landed
`ArchDerivCasimir.lean`:

* a docstring that states what the module is (the `𝔰𝔩₂` calculus at a real place: the chart
  derivative, the brackets, the Casimir commuting with the flows, the three headlines), says
  "transcribed from the three pin `S_` files" and names the dedup, and records the wiring;
* imports: `FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir`,
  `FLTForHuman.AutomorphicForm.Adelic.Cusp/Constituent` (for `continuous_rightTranslate`) and
  `Mathlib.Analysis.Calculus.FDeriv.Symmetric` (for `ContDiffAt.isSymmSndFDerivAt`, §10). Nothing
  wider; no `import Mathlib`;
* `namespace AutomorphicForm`;
* **public surface: the three headlines, at their exact pin names, are the wire; everything
  else is public *and* registered tier 3.** The checker exempts a public declaration whose
  `-- pin: <pin name> (<pin file>:<line>)` marker names a pin file `SOURCES` does not read — so the
  64-declaration engine and the three tails stay public (a later proof can import them),
  `SOURCES` lists only the three `Theorems/` wrappers, and the delta is exactly +3. Do **not** make
  the engine `private` and do **not** split it into an unlisted engine module plus a façade: both
  were the earlier plan and both are superseded. Do not leave a declaration without its marker — an
  unmarked public declaration with no `SOURCES` counterpart is a `MISSING` failure, and an unmarked
  one with a counterpart would be diffed. The pin's `private theorem _root_.CasCore17.…` /
  `_root_.CommAway17.…` shadows are dropped (the first two restate engine lemmas) or renamed (the
  `CommAway17` pair, whose statements differ by the `glArch = 1` hypothesis);
* the pin's `p2m_export`/`p2m_exact_reverting` glue does not exist in the port: re-state each
  headline's proof as the pin's `solution` body inlined (`intro`/`exact ⟨…⟩`).

**Statement authority is the `Theorems/` wrapper, not the `S_` file.** The three are
`Theorems/Thm_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt.lean`,
`…_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt.lean` and
`…_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul.lean`. Copy the statements verbatim
(binders `(K : Type) [Field K] [NumberField K]`, `(w : InfinitePlace K) (hw : w.IsReal)`); the
checker's delta must come out at exactly **+3** and any drift in a statement shows up there.

## 4. What is already in the port and must be reused

| name | where |
|---|---|
| the whole arch-derivative API (`archDerivAt`, `archCasimirAt`, `IsArchSmoothAt`, `ArchDir`, `archFlowAt`, `archFlowMatrix`, `archDirMatrix`, `archRealGLAt`, `archRealLiftAt`, `archRealProjAt`, `splitTorusGL2`, `lowerUnipotentGL2`, `IsArchSmoothAt.archCasimirAt`, the `_comp_mul_left`/`_comp_mul_right` forms) | `FLTForHuman/AutomorphicForm/Adelic/ArchDerivCasimir.lean` (landed) |
| `continuous_rightTranslate` — **substitution**, do not re-prove | `AutomorphicForm.CuspidalConstituent.continuous_rightTranslate`, `FLTForHuman/AutomorphicForm/Adelic/Cusp/Constituent.lean` |
| `rightTranslate` and its `_zero`/`_add`/`_mul` forms | `FLTForHuman/AutomorphicForm/Adelic/ProductionPinsGeneral.lean` / `RightConvolution.lean` |
| `unipotentGL2` (+`_coe`, `_zero`, `_add`) | `FLTForHuman/AutomorphicForm/Adelic/ConstantTerm.lean` |
| `glEquivOfRingEquiv`, `ringEquivRealOfIsReal`, `glEquivOfRingEquiv_apply_entry` | `FLTForHuman/AutomorphicForm/Adelic/ArchWeightCharTransport.lean` |
| `archGLIncl`, `adelicArchGLInclAt`, `glArch_adelicArchGLIncl`, `glFin_adelicArchGLIncl`, `archComponent_archGLIncl_self` | `FLTForHuman/AutomorphicForm/Adelic/ArchType.lean` |

`port_advise` reports **0 substitutions** against the port for these three files other than the
above, and **0 declarations already in the port** — the engine is genuinely new.

## 5. Route, with the recorded negatives

1. Write the engine from `S_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt.lean` (its
   copy is the one with no `private` markers, so it transcribes with the least friction).
2. Headline 1 is then `CasCore17.archCasimirAt_rightTranslate` + `package` — one `intro` and one
   `exact`.
3. Append headline 2's three namespaces (`CommAway17`, `Elem17LR`, `CasLR17`) from
   `S_…leftCasimir….lean`, dropping its `_root_.CasCore17.*` shadows (the port's engine already
   provides those lemmas under the same names in the engine namespace; rename references if the
   shadow was load-bearing — **report it if it was**, do not change a statement).
4. Append headline 3's `OsAlg17` from `S_…iterate_raise….lean`.
5. Build, then verify (§7).

**Recorded negatives — do not do these.**

* Do **not** generalise `IsArchSmoothAt` to a pointwise `ContDiffAt`: the pin's `∀ g` form is what
  every chart lemma is stated against and the checker diffs the public statements only, but a
  changed engine hypothesis changes the headlines' *proofs* into a different development.
* Do **not** "simplify" `archRealLiftAt` (`1` on `det e = 0`). Its `dif` is load-bearing for
  `archRealLiftAt_mul_archRealGLAt`.
* Do **not** replace `deriv ( … ) 0` by `fderiv`: `archDerivAt` is the scalar derivative at `0`.
* Do **not** re-prove `continuous_rightTranslate`; import it (§4).
* Do **not** make the engine `private` to shrink the wire; the tier-3 marker is the mechanism (§3).
* Do **not** port the complex twin because it "looks the same"; it is a different definition layer.

## 6. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap
> is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the low
> cap is what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, and only with the user's permission.

Concretely: iterate on `ArchCasimir.lean` at the low cap until exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Adelic.ArchCasimir`.
No dependent module, no façade, no checker run, no whole-tree build.

**Build-time blow-up protocol.** The named risks are `cf_*`/`AdM*` (nine `Matrix (Fin 2) (Fin 2) ℝ`
structure-coefficient goals, `ring`/`ext`/`fin_cases` chains), `archDerivAt_archDerivAt_eq` (27 lines,
the mixed-partial identity through the chart), `casimir_identity`/`casimir_comm_*`, and
`lower_iter_props`/`raise_iter_props` (the `ℕ`-induction with `Function.iterate_succ_apply`). If a
declaration hits the cap: reproduce it alone at the low cap with `set_option diagnostics true` in a
**scratch copy under `tmp/`** (never in the module), fix the inference (`convert`/`refine` with
explicit arguments, `Matrix.ext` before `simp`), re-run. If the wall clock, not the heartbeat, is the
limit, split the file compile by commenting the tail — but never commit that, and never raise the
cap.

## 7. Verification the worker runs before stopping

| check | expected |
|---|---|
| tier-0 loop on `ArchCasimir.lean` | exit 0, **0 warnings** |
| tier-1 build | green; record jobs and wall/user time |
| `grep -n "sorry\|admit\|^axiom\|native_decide\|import Mathlib\|maxHeartbeats\|set_option linter" ArchCasimir.lean` | no hits |
| public surface | the three headline names, plus a `-- pin:` marker above every other public declaration |
| statements | diffed against the three `Theorems/` wrappers, binder for binder |
| `#print axioms` on the three headlines | `[propext, Classical.choice, Quot.sound]` (scratch file under `tmp/`) |
| `git status` | only `ArchCasimir.lean` (+ anything under `tmp/`) |

## 8. Stop conditions (report, do not work around)

* A statement in the `Theorems/` wrapper will not elaborate against the landed definition layer →
  **stop**, report the declaration and the error, do not adjust the statement.
* A lemma needed from another module is `private` there → re-derive it locally and report it; do
  **not** promote it and do **not** edit the host (the hub prohibition: any edit to an existing
  module is the manager's, and is priced with `build_ladder.py --edit` first).
* A definition seems missing from the API → report it; the definition layer is landed and frozen.
* Two of the pin's three copies of a shared lemma differ in *statement* (not just `private`) → stop
  and report both; that is a faithfulness question, not a dedup one.

## 9. Report shape

1. The module's line count and the count of declarations per block (`engine`,
   `CommAway17`/`Elem17LR`/`CasLR17`, `OsAlg17`), against the pin's 64 / 28 / 38.
2. The three public statements, quoted, and the statement-authority file each was copied from.
3. Tier-0 and tier-1 results: exit codes, warnings (should be 0), jobs, wall and user CPU time.
4. The `#print axioms` output for the three headlines.
5. Anything the pin's `_root_.` shadows were load-bearing for, anything re-derived locally, and every
   place where the pin's three copies disagreed.
6. `git status`.

## 10. Landing record

Measured on the tree the set left (`ArchCasimir.lean`, 1,431 lines, 131 public declarations):

| check | result |
|---|---|
| tier-1 loop | exit 0, **0 warnings** |
| tier-2 build | green, 3,636 jobs, ~10 s |
| checker | **10,107 identical (676 promoted, 83 renamed), 0 mismatched, 0 missing**, 42 own-proof exempted, **128 registered-unwired exempted** (10,277 checked) — delta **+3** over the 10,104 baseline |
| `#print axioms` (3 headlines) | `[propext, Classical.choice, Quot.sound]` |
| `unwired_register.py --check` | current; the module is registered with its 128 declarations |
| forbidden tokens | none |
| `git status` | the module, the two definition modules, the checker wiring, the register, and the notes |

Statement diffs against the three `Theorems/` wrappers were also checked token by token: all three
identical (688 / 392 / 1,255 characters on both sides).

Four mathlib `v4.34.0` drifts had to be fixed relative to the pin: `dif_pos`/`dif_neg` →
`dite_eq_left`/`dite_eq_right`; `ContinuousLinearMap.neg_apply` → `_root_.neg_apply`; `D2_symm`
needs `Mathlib.Analysis.Calculus.FDeriv.Symmetric` imported explicitly (the pin reached
`ContDiffAt.isSymmSndFDerivAt` through its whole-library import); and the `bracket_*` three-goal
`simp` sets had to drop the now-unused `Matrix.mul_apply`/`Fin.sum_univ_two` arguments. Headline 1's
`hxc` binder is unused by its proof — the pin's `p2m_exact` hid that — and is referenced with the
`have _ := hxc` idiom rather than renamed, so the statement stays verbatim.

The register tool needed one addition to serve this design: `tools/deps/unwired_register.py` scanned
only *unlisted* modules, so a listed module's tier-3 declarations were registered nowhere. It now
covers them too, with a **text-only** predicate — no checker run: a public declaration of a listed
module is registered when it carries a `-- pin:` marker into a pin file `SOURCES` does not read *and*
no `SOURCES` declaration (public or pin-`private`) provides the same last name and normalised
statement. The marker alone is not enough, because the checker consults it only as a fallthrough.
Cost: the full scan is ~7 s for 712 port modules plus 1,482 `SOURCES` files parsed into the
"provided" index (~2.5 s of it); it reproduced the checker's own `UNWIRED` answer exactly
(124 modules / 3,815 declarations, of which this module is the only new one).
