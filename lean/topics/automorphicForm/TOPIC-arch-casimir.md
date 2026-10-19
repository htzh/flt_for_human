# The archimedean `𝔰𝔩₂` / Casimir calculus — mathematics, measurement and the port structure

The Deligne–Serre demand reaches the archimedean representation theory of `GL₂` through the
derivatives of right translation by the three one-parameter flows at a real place, and through the
Casimir operator built from them. Every one of those statements is phrased in the pin's
`Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean`, which the port did not have: the D-S
`--include-leaves` shelf shows the family's four real-place leaves at 569–917 silo lines each,
`AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul` (917) second on the
whole 463-leaf shelf behind only the ray-class hub `M4aTorus.completedRayL_fe`. This note is the
subject's home: §1 the mathematics, §2 the cone measurement, §3 the duplication and budget, §4 the
definition layer (the manager's ground), §5 the port structure and waves, §6 risks and recorded
negatives, §7 reproduce, §8 residuals.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

Companions: the column note [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2 (the ready
shelf and the leaf reading) and §7 (the two gates these statements stand behind); the playbook
[../porting-playbook.md](../porting-playbook.md) §2.1–§2.4 (measurement, route, whole nodes,
dedup), §3.2–§3.5 (layout, work orders, sets, build ladder), §4 (faithfulness), §5 (sharing); the
sibling archimedean subject [TOPIC-iwasawa-analytic-core.md](TOPIC-iwasawa-analytic-core.md) (the
compact factor and the Fourier decay, a different development at the same places); the
Bargmann/unitarity use of this calculus in
[../../math/028-iwasawa-decomposition-and-archimedean-estimates.md](../../math/028-iwasawa-decomposition-and-archimedean-estimates.md)'s
neighbourhood; the work orders [WORKORDER-AC1-defs.md](WORKORDER-AC1-defs.md) (the definition
layer) and [WORKORDER-AC2-cascore-trio.md](WORKORDER-AC2-cascore-trio.md) (the first proof set).

## 1. The mathematics

**The three flows.** At a real place `w` of a number field `F`, the pin transports `GL₂(ℝ)` into
`GL₂(𝔸_F)` by `archRealGLAt hw : GL (Fin 2) ℝ →* AdelicGL2 (𝓞 F) F`, the composite of the place
inclusion `adelicArchGLInclAt F w` with the ring equivalence `ringEquivRealOfIsReal hw`. A general
invertible real matrix does not lift through a monoid homomorphism (the map must respect
multiplication, and `mkOfDetNeZero` is a non-canonical choice), so the pin also carries
`archRealLiftAt hw e` — the lift of `e` when `det e ≠ 0`, `1` otherwise — which is what makes the
`smoothness` definition meaningful. Then:

* $`H`$, $`E`$, $`F^-`$ are three `ArchDir` directions realised as one-parameter subgroups of
  `GL₂(ℝ)`: $`H`$ by $`\mathrm{diag}(e^t, e^{-t})`$ (`splitTorusGL2`), $`E`$ by the upper
  unipotent $`t \mapsto [[1, t], [0, 1]]`$ (`unipotentGL2`, already in the port's
  `ConstantTerm.lean`), $`F^-`$ by the lower unipotent $`t \mapsto [[1, 0], [t, 1]]`$
  (`lowerUnipotentGL2`, new);
* `archFlowAt hw d t = archRealGLAt hw (archFlowMatrix d t)` is the flow in $`\mathrm{GL}_2(\mathbb{A}_F)`$,
  with `archFlowMatrix_zero` / `archFlowMatrix_add` making it a one-parameter subgroup, and
  `archDirMatrix` recording the three trace-zero direction matrices
  $`[[1, 0], [0, -1]]`$, $`[[0, 1], [0, 0]]`$, $`[[0, 0], [1, 0]]`$;
* the **derivative at the place** is
  $`D_d\varphi(g) = \frac{d}{dt}\big|_{t=0} \varphi(g \cdot \mathrm{archFlowAt}\, d(t))`$
  (`archDerivAt`), the classical right-invariant vector field, and the **Casimir operator** is
  $$\Omega\varphi = -\Bigl(\tfrac14 D_H D_H \varphi - \tfrac12 D_H \varphi + D_E D_{F^-}\varphi\Bigr),$$
  (`archCasimirAt`) — the pin's normalisation, so that $`\Omega`$ is the Laplace eigenvalue operator
  of the Maass form story. `IsArchSmoothAt hw φ` says every translate
  $`e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\, e)`$ is $`C^\infty`$ on $`\det e \neq 0`$,
  which is the hypothesis every derivative statement needs.

**The lemma ladder.** The definition module is not a bare set of `def`s: it carries the API the 47
proof files rest on, and the port must home all of it (playbook §2.3 — the whole node, not the
block one set reaches).

1. *transport*: `archRealGLAt`, `archRealLiftAt`, `archRealLiftAt_of_det_ne_zero`,
   `isOpen_setOf_det_ne_zero`, `IsArchSmoothAt`, `isArchSmoothAt_const`;
2. *flows*: `ArchDir`, `lowerUnipotentGL2` (+`_coe`, `_zero`, `_add`), `splitTorusGL2` (+`_coe`,
   `_zero`, `_add`), `archFlowMatrix`, `archFlowAt` (+`_zero`, `_add`), `archDirMatrix`;
3. *the derivative exists*: `hasDerivAt_archFlowMatrix_apply` (entrywise derivative of the flow is
   the direction matrix — six scalar cases), `archRealLiftAt_mul_archRealGLAt` (the lift intertwines
   right multiplication by `archRealGLAt`), `contDiff_of_symm_mul_const`,
   `hasDerivAt_of_symm_mul_archFlowMatrix`, `of_symm_mul_archFlowMatrix_zero`, and the chain rule
   `IsArchSmoothAt.archDerivAt`;
4. *linearity and smoothness algebra*: `archDerivAt_add`, `archDerivAt_smul`, `archCasimirAt_add`,
   `archCasimirAt_smul`, `IsArchSmoothAt.add`/`.smul`/`.neg`/`.sub`/`.archCasimirAt`,
   `archDerivAt_const`, `archCasimirAt_const`;
5. *invariance*: `eq_of_glArch_eq_of_glFin_eq` (an adelic point is its archimedean and finite
   components), `archRealGLAt_mul_comm_of_glArch_eq_one` and its `archRealLiftAt`/`archFlowAt`
   forms — the archimedean factor commutes with the finite part — and from them
   `IsArchSmoothAt.comp_mul_right`, `archDerivAt_comp_mul_right`, `archCasimirAt_comp_mul_right`,
   `IsArchSmoothAt.comp_mul_left`, `archDerivAt_comp_mul_left`, `archCasimirAt_comp_mul_left`;
6. *the projection*: `archRealProjAt`, `archRealProjAt_archRealGLAt`,
   `archRealGLAt_glEquivOfRingEquiv`.

**The first proof set** is the `𝔰𝔩₂` calculus itself, on three files that share one engine:

* `CasCore17` — the chart $`e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\, e)`$ and its
  derivatives (`chart`, `D1`, `D2`, `Dconj`, `AdM`, `cf`), the two identities
  `archDerivAt_archDerivAt_eq` (mixed partials commute) and `archDerivAt_comm`, the brackets
  $`[H,E] = 2E`$, $`[H,F^-] = -2F^-`$, $`[E,F^-] = H`$ (`bracket_*`), the commutation of
  $`\Omega`$ with the flows (`casimir_identity`, `casimir_comm_*`), and the package lemma;
* the three headlines: `archCasimirAt_rightTranslate_archRealGLAt` (the Casimir of a right
  translate), `leftCasimir_eq_archCasimirAt_of_isArchSmoothAt` (the pin's `leftCasimir`, the
  enveloping-algebra element acting on the left, agrees with `archCasimirAt`), and
  `iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul` — the Maass raising/lowering
  calculus: with $`E^{\mp} = D_H \mp i(D_E + D_{F^-})`$, from
  $`D_E\theta - D_{F^-}\theta = m\theta`$ and $`\Omega\theta = \lambda\theta`$ one gets
  $`(E^-)^j\theta`$ and $`(E^+)^j\theta`$ smooth with weight $`m \mp 2ij`$ and eigenvalue
  $`\lambda`$, and the iterated factorisation
  $$(E^+)^M (E^-)^M \theta = \prod_{j<M}\bigl(-4\lambda + (m-2ij)^2 - 2i(m-2ij)\bigr)\cdot\theta ,$$
  $$(E^-)^M (E^+)^M \theta = \prod_{j<M}\bigl(-4\lambda + (m+2ij)^2 + 2i(m+2ij)\bigr)\cdot\theta .$$
  That product is what forces the Bargmann inequalities on cuspidal constituents
  (`CuspidalConstituent.casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_*`) and the
  vanishing `whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero`.

References: D. Bump, *Automorphic Forms and Representations*, CUP 1997, §§2.2–2.5; S. Lang,
*SL₂(ℝ)*, GTM 105, ch. VI; V. Bargmann, *Irreducible unitary representations of the Lorentz group*,
Ann. of Math. 48 (1947), 568–640.

## 2. The cone measurement

The subject is invisible to the two frontier readings that are used to plan, and shows up only on
the leaf reading.

* `--ready` never lists it: every file of the family is a graph *leaf* (the pin's `S_` files cite
  no other theorem node), and a leaf never reaches `F`. `python3 frontier.py --ds --include-leaves
  --rank-by silo --top 0` is the reading that prices it — 463 leaves, the family's real-place rows
  at ranks 2, 4 and 6 (`iterate_raise…` 917, `archCasimirAtComplex_rightTranslate_archComplexGLAt`
  857, `leftCasimir_eq_archCasimirAt_of_isArchSmoothAt` 856, `archCasimirAt_rightTranslate_archRealGLAt`
  569, and the two 110/133-line `…_rowIsometryInclAt_of_ne` siblings).
* The *definition* module is invisible to readiness altogether (frontier.py does not model imports):
  `Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean` is not a node, and the port had no
  `archDerivAt`, `archCasimirAt`, `IsArchSmoothAt`, `ArchDir`, `archRealGLAt`, `archFlowAt`,
  `archRealProjAt`, `splitTorusGL2` or `lowerUnipotentGL2` at all. This is exactly the §4(a) trap
  the column records for `Def_ModularCurve_QExpansionDiff.lean`: readiness says "leaf, ready", the
  proof needs a definition layer nobody has priced.

**The demand, measured.** Intersecting the pin `P2M/Sol/*.lean` files that mention
`archDerivAt`/`archCasimirAt`/`IsArchSmoothAt` with the D-S `needed` list (`frontier.py --ds --list`):

| slice | files | raw `S_` lines |
|---|---:|---:|
| real place only | 43 | 17,361 |
| complex place (`archDerivAtComplex`, `archCasimirAtComplex`) | 35 | 16,365 |
| **the subject in the D-S demand** | **78** | **33,726** |

**The mapping matters, and getting it wrong undercounts by 40 %.** A node's `S_` file is its
qualified name with the dots replaced by underscores (`AutomorphicForm.CuspidalConstituent.foo` →
`S_AutomorphicForm_CuspidalConstituent_foo.lean`). Splitting the stem at the *first* underscore
instead silently drops every node whose namespace has two segments — which is all of
`AutomorphicForm.CuspidalConstituent.*`, the largest part of this subject. The corrected reading is
78 files; a stem split at the first underscore gives 47 / 22,607 and misses
`exists_iterate_lower_mem_cut_and_iterate_raise_mem_cut_of_hasArchCharacterAt` (1,416 lines) and
`iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar` (929) among others.

The seven shelf leaves are `iterate_raise…` (917), `leftCasimir…` (856),
`archCasimirAtComplex_rightTranslate_archComplexGLAt` (857),
`archCasimirAt_rightTranslate_archRealGLAt` (569) and the four `…_rowIsometryInclAt_of_ne`
siblings (133, 110 real; 133 and its complex twin). Both halves are gated by the same real-place
definition module, the complex half additionally by `Def_AutomorphicForm_ArchDerivCasimirComplex`
(196) and `…ComplexAPI` (381).

**Consumers of the leaf itself.** 6, of which 3 are in the D-S needed set — the two Bargmann
inequalities on cut vectors and `whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero`
(573 raw lines). The other three (`archOccursInClassOf_*`) are in the target cone but not in the
demand's unported slice.

## 3. Duplication and budget

`port_advise` + `port_plan` over the slices (all figures measured on the pin, `--no-drags`):

| slice | raw | duplicate copies | boilerplate | **net new math** | groups |
|---|---:|---:|---:|---:|---:|
| `iterate_raise…` alone | 917 | 0 | 22 | **895** | 103 |
| the three real-place headlines | 2,342 | 1,068 | 66 | **1,208** | 133 |
| 43 real-place files | 17,361 | 3,979 | 1,116 | **12,260** | 699 |
| 35 complex files | 16,365 | 3,565 | 930 | **11,851** | 752 |

The three real-place headlines share **56 names / ≈1,028 removable lines** — the pin wrote the
`CasCore17` prelude three times, in two spellings (`private` in `iterate_raise…`, public in the
other two). Normalised at the `private` marker and the `namespace` line, the longest common prefix
is 552 lines, and `port_plan`'s block view puts the shared development at one block of 56
declarations / 538 declaration lines shared by all three. So the trio is the WORKORDER-E / F1 shape:
one private engine, three public headlines, checker delta exactly +3.

The wider dedup is real but modest — 23 % of the real slice and 22 % of the complex slice is a
second or third copy — because outside the trio the fan is heterogeneous: each file adds its own
chart or Whittaker development on top of the shared prelude.

Substitutions found against the port: `continuous_rightTranslate` (the pin's `private` copy at
`S_…iterate_raise….lean:482`) is already public as
`AutomorphicForm.CuspidalConstituent.continuous_rightTranslate` in
`FLTForHuman/AutomorphicForm/Adelic/Cusp/Constituent.lean`, same statement up to binder names; the
engine imports it. Everything else in the trio is new. The tool's remaining "substitutions" in the
wider slices (`l5Ent`, `l5_continuous_ringEquiv`) are local helper names in an unrelated file
matching unrelated port declarations — recorded negatives, not substitutions. The complex slice also
carries **13 declarations already in the port at tier 3** (registered, not statement-diffed), which
is why its budget shows 19 vetted rows against the real slice's 6.

## 4. The definition layer — the manager's ground

Two pin modules, homed whole (playbook §2.3), at theory homes (not `Def_`-named files):

| pin module | lines | declarations | `private` | pin importers | port home |
|---|---:|---:|---:|---:|---|
| `Definitions/Def_LanglandsTunnell_ArchParam.lean` | 139 | 33 | 0 | 74 | `FLTForHuman/LanglandsTunnell/ArchParam.lean` |
| `Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean` | 445 | 58 | 0 | 339 | `FLTForHuman/AutomorphicForm/Adelic/ArchDerivCasimir.lean` |

Both are all-public, so **no promotion is owed** and the checker verifies every declaration by
dotted name directly. `ArchParam` is `LanglandsTunnell.{RealArchParam, ComplexArchParam}` — the
archimedean local parameters and their gamma factors, importing only
`Mathlib.Analysis.SpecialFunctions.Gamma.Deligne`; it is the pin's `import Mathlib`-free module, so
the port's no-`import Mathlib` rule costs nothing. `ArchDerivCasimir` imports the two already-ported
`Def_` modules (`ArchType`, `ArchWeightCharTransport`) plus `ConstantTerm` (for `unipotentGL2`) and
`ArchParam`.

Build shape: two new leaf modules, no edit to any existing module, so `build_ladder.py --edit` has
nothing to price — the cascade is the two `.olean`s and the two checker rows. The wave price is the
`SOURCES`/`PORT_FILES` append and one checker run.

The Complex pair (`…ArchDerivCasimirComplex` 196 lines / 32 declarations, `…ComplexAPI` 381 / 46;
both all-public, importing only each other and the layer above) is **not** homed in this wave: no
real-place file needs it. It is set B's prerequisite (§5).

`Def_LanglandsTunnell_ArchCasimirCompanion` (61 lines, 7 declarations) is a different subject and is
**not** homed here (§6).

## 5. The port structure and the waves

* **Wave 0 (manager, landed — see [WORKORDER-AC1-defs.md](WORKORDER-AC1-defs.md)).** The two
  definition modules above, checker wiring appended last to `SOURCES` / `PORT_FILES`, one checker
  run: `10,013 → 10,104` identical, **+91** (per module +33 `ArchParam`, +58 `ArchDerivCasimir`),
  0 mismatched / 0 missing, exemptions unchanged at 42. Both modules green at tier 1 with 0
  warnings, tier-2 builds green (2,847 and 3,533 jobs), `git status` clean but for them. One
  drift fixed: `dif_pos` → `dite_eq_left` in `archRealLiftAt_of_det_ne_zero` (proof term only).
* **Set A — the real-place `CasCore` trio (landed — see
  [WORKORDER-AC2-cascore-trio.md](WORKORDER-AC2-cascore-trio.md)).** The pin's three copies of the
  engine written once as **one module**, `AutomorphicForm/Adelic/ArchCasimir.lean` (1,431 lines):
  the three headlines are the statement-diffed wire, and **everything else is public and
  registered tier 3** — 128 declarations, each carrying a
  `-- pin: <pin name> (<S_ file>:<line>)` marker into one of the three `S_` files, which `SOURCES`
  deliberately does not read, so the checker exempts them (its `UNWIRED` fallthrough) and
  `spec/UNWIRED-PUBLIC.md` lists them. Checker `10,104 → 10,107` identical (**+3**), 0 mismatched /
  0 missing, 128 registered-unwired exempted. A future proof imports
  `AutomorphicForm.CasCore17.*`, `…CommAway17.*`, `…Elem17LR.*`, `…CasLR17.*`, `…OsAlg17.*`
  directly instead of re-deriving the chart or the brackets.

  The design point this set settles for the column: **do not make a shared engine `private` to keep
  the wire small.** A listed module may carry tier-3 public declarations — the checker reads their
  `-- pin:` markers as the exemption — so the engine is reusable *and* the delta is exactly the
  headlines. The earlier plan (a `private` engine, or an engine/façade split with an unlisted
  engine module) is superseded.
* **Set B — the complex mirror.** Needs `…Complex` + `…ComplexAPI` homed first (577 lines / 78
  declarations, the same whole-node shape as wave 0, no new subject), then its own engine + the
  headlines (16,365 → 11,851). Its shelf leaves are
  `archCasimirAtComplex_rightTranslate_archComplexGLAt` (857),
  `leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` (1,227) and the complex
  `…_rowIsometryInclAt_of_ne` (133).
* **Set C — the proof fan** (the remaining 40 real + 35 complex files, 24,111 net new lines across
  both halves) is left to the column's ordinary set-by-set scheduling once A and B are in; each of
  those files uses the definition API directly and needs no new ground.

## 6. Risks and recorded negatives

* **`IsArchSmoothAt` is an `∀ g` statement over the whole adele group**, so `archDerivAt` never has a
  local `DifferentiableAt` hypothesis of its own: the engine's lemmas take `IsArchSmoothAt hw φ` and
  discharge the derivative facts through `archFlowAt`/`archRealLiftAt`. A port that tries to replace
  it with a pointwise `ContDiffAt` will not match the pin's statements.
* **The chart is the whole difficulty.** `archRealLiftAt` is `1` on `det e = 0` by `dif_pos`, so the
  chain rule goes through `archRealLiftAt_mul_archRealGLAt` on `det e ≠ 0` and the derivative is
  taken along `Matrix.of.symm (Matrix.of e * archDirMatrix d)`. Do not "simplify" the chart.
* **`deriv` (the scalar one) at `0`**, not `fderiv`: `archDerivAt` is `deriv (… ) 0` on `ℝ → ℂ`.
  The `Real.hasDerivAt_exp`/`hasDerivAt_neg` case split in `hasDerivAt_archFlowMatrix_apply` is
  six scalar goals; it is where a mathlib drift between `v4.33.1` and `v4.34.0` would surface first.
* **No `import Mathlib`.** `ArchParam` needs exactly `…Gamma.Deligne`; `ArchDerivCasimir` needs the
  four port modules. The pin's `Def_AutomorphicForm_ConstantTerm` has `import Mathlib`, which the
  port has already replaced by five specific modules — do not re-widen it.
* **`ArchCasimirCompanion` is a different subject, and the boundary is sharp.** No file of this
  family imports it: 0 of the 78 demand rows carry it in their import block. But 130 pin `S_` files
  *do* — the `AutomorphicForm.CuspidalConstituent.*` cluster — and through
  `Def_LanglandsTunnell_JLConverse` (301 lines) it drags four unported modules (`JLData`,
  `ArchEpsilon`, `UnramifiedWhittaker_HeckeRecursion`, `StandardLocalConstantsAt`) plus the unported
  `ArchDatumR`. None of the 130 is a D-S `needed` row today, so neither the companion nor that chain
  is priced here. Recorded negative with its boundary, not a claim that the module is unused.
* **`--ready` cannot see this subject** (§2). Any re-read of the frontier that trusts `--ready`
  alone will report the family as absent.

## 7. Reproduce

```bash
cd tools/deps
# the shelf the family sits on (leaves only; --ready never lists them)
python3 frontier.py --ds --include-leaves --rank-by silo --top 0
# the subject's cone, by target
python3 frontier.py --target AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul --top 0
# advise / plan / twins
python3 port_advise.py --target S_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul \
  --target S_AutomorphicForm_archCasimirAt_rightTranslate_archRealGLAt \
  --target S_AutomorphicForm_leftCasimir_eq_archCasimirAt_of_isArchSmoothAt --json build/cascore3_advise.json
python3 port_plan.py --json build/cascore3_advise.json
python3 twin_scan.py --target AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
# the demand intersection (78 files / 33,726 raw lines): for each needed qual, stem = qual.replace('.','_')
python3 frontier.py --ds --list --top 0    # then grep the S_ stems against the list
```

The port side, per the column's §6:

```bash
cd lean
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/LanglandsTunnell/ArchParam.lean
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.LanglandsTunnell.ArchParam
timeout 300 python3 spec/check_flt_statements.py
python3 tools/deps/unwired_register.py --check
```

## 8. Residuals

* **Set A settled the engine/wire question: one listed module, public engine, registered tier 3.**
  No façade file and no `private` engine. The consequence to watch is that the module's public
  surface is now 131 declarations, 128 of them exempted by marker: a later edit that drops a
  `-- pin:` marker turns that declaration into a `MISSING`/`OWN` failure, and one that changes a
  marked statement silently changes a registered statement without a diff. The register is
  regenerated by `tools/deps/unwired_register.py`, which now also covers *listed* modules, deciding
  the tier-3 predicate from the tree's text alone (marker into a `SOURCES`-unread file, and no
  `SOURCES` counterpart by name and statement) rather than by running the checker.
* **The `…_rowIsometryInclAt_of_ne` siblings** (133, 110) are the smallest real-place leaves and are
  not in set A: they need the same definition layer but tell a different story (`archRealProjAt` on
  the row-isometry subgroup away from `w`). They are set C rows.
* **`laplaceEigenvalue`** (`ArchParam`'s `LanglandsTunnell.RealArchParam.laplaceEigenvalue` plus its
  two `rfl` lemmas) is homed with `ArchDerivCasimir` because that is where the pin puts it; it has
  no consumer in set A and is kept per the pin (whole-node rule).
* **The complex mirror's definition pair is measured but not scoped.** `…Complex` 196 lines / 32
  declarations and `…ComplexAPI` 381 / 46, both all-public and importing only the layer above, so
  set B's wave 0 is the same whole-node append as wave 0 here (expected checker **+78**). Its proof
  slice is 35 files / 16,365 raw → 11,851 net with 13 declarations already at tier 3; the dedup and
  the headline split have not been run through `port_advise` per file.
* **The 78-file count depends on a mapping that is easy to get wrong.** See §2: the `S_` stem is the
  qualified name with dots replaced by underscores. Any recomputation that splits at the first
  underscore reports 47 / 22,607 and drops the whole `CuspidalConstituent` part of the fan.
