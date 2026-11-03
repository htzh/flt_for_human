# WORKORDER-AF16 — the section's maximal-compact dictionary: regularity, height, span, and the two reductions

**Issued 2026-11-02, one dispatch, three modules, three orders.** Scope: [SET-AF16.md](SET-AF16.md) —
§1 the eight rows, §2 the price and the one false substitution, §3 the definition gate, §4 the homes,
§6 the risk register, and **Appendix B, the per-declaration worklist**. This order states the work, the
manager's landed layer, the traps and the gates.

**Audience.** A fresh coding session. Wire: each target module carries its own `spec-pin:` header and
`spec/check_port.py` owns its public statements. **No per-declaration markers.** Pin clone
`/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`. Port mathlib `v4.34.0`.

**The size.** 8 rows, 1,278 silo, **883 lines in 35 declarations to write** (877 net by `port_plan`;
**209 lines are already in the port** and 207 of those are genuinely importable — §2.1 of the brief).

## 0. The manager's layer, landed (do not redo it)

1. **The three skeletons exist, build, and are wired.**
   `FLTForHuman/AutomorphicForm/Adelic/InducedSectionKRegular.lean` (94 lines, ten `spec-pin:` lines,
   seventeen imports, empty `… LocalIntertwining namespace {SectionHeightBound, ContinuousOnMaximalCompact,
   ContinuousOnBorel}`), `…/Adelic/InducedSectionSpan.lean` (66 lines, two `spec-pin:` lines, eleven
   imports, empty `… LocalIntertwining namespace FlatFamilyDecomposition`) and
   `…/Adelic/MaximalCompactReductions.lean` (69 lines, four `spec-pin:` lines, twelve imports, empty
   `… LocalIntertwining namespace {DiagOneReduction, BorelHeightCompact}`). All three elaborate silent,
   all three build green (`flock .lake/flt_build.lock lake build <module>`, 3,901 jobs for the closure),
   and `spec/check_port.py --force` reads **0 ok / 0 mismatch / 0 missing** on each.
2. **The statements are verified.** `lean/tmp/probe-af16-statements.lean` states all **eight** headlines
   verbatim from their wrappers as `example … := by sorry` against the three built modules and elaborates
   with **exactly eight `declaration uses 'sorry'` warnings and nothing else**. Re-run it first. It settled
   that the probe needs `open scoped NNReal` at file level (four of the eight statements spell `ℝ≥0` in the
   `distribHaarChar`-to-`ℝˣ` monoid hom) — an `open scoped` does not touch a statement's text.
3. **The imports are the mathematics' and are final; needing another is a blocker report.** The one
   non-obvious edge is order B's: `FLTForHuman.RepTheory.TranslateSpan` carries the `EvalMatrix`/`UniformRank`
   engine at the pin's names, it imports **mathlib only** (checked), and the pin itself takes that engine
   from `Theorems/`. Do not re-prove it.
4. **§2.1's decision: write `KT`, import everything else.** (At the landing the six `atPlace`-kit
declarations below were promoted out of `private` in `MaximalCompactFactors.lean` and imported instead of
copied — the manager's act, on the rule that mathematics is promoted and only tactical helpers may be
duplicated; the copies in order C are gone.) The worklist calls 218 lines "imported"; 216 of
   them are genuine public port copies — `EvalMatrix`/`UniformRank` (83 lines, `RepTheory/TranslateSpan.lean`),
   `atPlace` and its kit plus `localEmbed_entries_integral`/`atPlace_mem` (54, `MaximalCompactFactors.lean`),
   `rowMaxNorm_mul_le_of_entries`/`finLocalHeight_mul_of_entries`/`finHeight_mul_of_mem` (78,
   `InducedSectionFlat.lean` and `NumberTheory/AdelicHeight.lean`) — **import those**. The one exception is
   the pin's `private abbrev KT : Type := {k : AdelicGL2 (𝓞 F) F // InK F k}` (2 lines), which the advise
   matches to `ZbarHomsConj.Qbar`: that is a shape-tier match on a *subtype of a `Type`*, the FR-0134
   class, and `Qbar` is a subtype of `ℂ`. **Write the pin's `KT`.**
5. **Visibility follows the pin's, and both readings matter here.** Rows 3 and 5 are flat public surfaces
   (13 and 4 public declarations), rows 1, 2, 4, 6 have small `private` preludes (13, 6, 5, 2), and rows 7,
   8 are one public declaration each. So the set has **23 public declarations in all** and ~26 `private`.
6. **No `Def_` node, no promotion, no migration, no legacy edit**: fifteen `Def_` modules in the closure,
   **0 missing** in every one (the heavy one is `Def_AdelicDock_LocalEmbedding`, 24 of its 62 declarations
   used by row 2, all ported).
7. **No `set_option`** beyond `autoImplicit false`; none of the eight statements carries a top-level `letI`.

## 1. What you write

Appended below each skeleton's empty namespaces. **Order A first** (five rows), then B (one), then C (two);
the three modules share no declaration and no row of one order cites another's, so the gates are per module
either way.

| order | row (`AutomorphicForm.` dropped) | namespace | work / decls | shape |
|---|---|---|---:|---|
| A | `IsInducedSection.eq_of_eqOn_maximalCompact` | (inside `IsInducedSection`, no helper) | **11** / 1 | the shortest: two induced sections agreeing on `K` are equal, by the Borel law |
| A | `continuousOn_of_isInducedSection_of_continuousOn_maximalCompact` | `ContinuousOnMaximalCompact` | **136** / 4 | continuity on `K` ⇒ continuity everywhere, through the decomposition |
| A | `continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn` | `ContinuousOnBorel` | **97** / 3 | the same from the pointwise Borel form |
| A | `exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection` | `SectionHeightBound` | **56** / 3 | the norm bound by the height's power (imports the height comparisons) |
| A | `exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family` | `FlatFamilyKInvariance` | **57** / 1 | a flat family's `k`-invariance on `maximalCompactAway S` |
| B | `exists_flat_isInducedSection_sum_eq_of_differentiable_family` | `FlatFamilyDecomposition` | **154** / 7 | the `EvalMatrix`/det argument, then the combination's five finiteness properties and the `K`-constancy |
| C | `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero` | `DiagOneReduction` | **171** / 2 | the `diagOne` reduction through `AdelicDock.LocalEmbedding`, place by place |
| C | `exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2` | `BorelHeightCompact` | **201** / 14 | bounded height + integrality ⇒ a compact Siegel set, from the decomposition |

Each headline is **public at its pin name** — that is, the *absolute* name `AutomorphicForm.<name>`
(`AutomorphicForm.IsInducedSection.eq_of_eqOn_maximalCompact` for row 8), **not** `<helper namespace>.<name>`.
A headline declared inside its helper namespace passes `check_port` and the frontier (they key on the
statement and the last name) and is still wrong: the repair is `theorem _root_.AutomorphicForm.<name>`,
which keeps the namespace's helpers in scope (found at this landing, FR-0135). The helpers' visibility is
the pin's (§0.5). The pin's `solution` body is the headline's body.

## 2. Traps

1. **Row 3 (order C) is the set's cost**: 14 declarations, 201 lines, a flat public surface, and its pin
   imports the height, the Haar character and the Tate-local zeta definition. Read it as Siegel-set
   compactness: write the point by the decomposition, bound the Borel factor by the height, and get
   compactness from boundedness in the windowed-Siegel set.
2. **Row 2 (order C) is one theorem of 171 lines** with a 24-declaration `LocalEmbedding` gate: the
   `diagOne` reduction goes place by place, and `maximalCompactAt F S` collects the local compact factors.
   Its hypothesis `hg₀` (trivial outside `S`) is what makes the reduction finite — keep it literal.
3. **Row 1 (order B) is linear algebra, not analysis**: import the `EvalMatrix` engine, and spend the work
   on transporting the three finiteness properties (`IsArchKFinite`, `IsKfSmooth`, continuity) and the
   holomorphy through the combination.
4. **The `K`-invariance predicates differ row by row**: rows 1 and 7 use `maximalCompactAway S` (trivial
   archimedean part); rows 1, 5, 6 use "`k` integral with every `glArch`-component a row isometry". A
   `K`-invariance stated for the wrong subgroup is a `MISMATCH`.
5. **Binder spelling is the statement** (FR-0123): eight headlines, several with section variables spelled
   inline and a `let α := …` preamble; row 8's declaration is `AutomorphicForm.IsInducedSection.eq_of_eqOn_maximalCompact`
   — inside the `IsInducedSection` namespace, not at `AutomorphicForm` level.
6. **`open scoped NNReal`** (four statements spell `ℝ≥0`) and, where the proof needs it,
   `open scoped ComplexConjugate`.
7. **No `sorry`/`admit`/`axiom`/`native_decide`, zero warnings, no `import Mathlib`**, no hub edit, no new
   module, no new import without a report.

## 3. Gates

Per module:

1. `timeout 200 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <module>` silent, then its own
   `flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.AutomorphicForm.Adelic.<Module>`; **no
   tree build**, no dependents.
2. `python3 spec/check_port.py --force <module>` → **0 mismatch / 0 missing**, with the ok count measured
   **at both readings**: at the pin's visibility the three modules should read **16 / 1 / 6** ok (23 in
   all), and the dropped-`private` reading ~49. A `MISMATCH` at either reading is a mis-transcription; a
   `MISSING` at the dropped reading is a port-side helper and stays `private`. Record both numbers and
   restore the pin's visibility.
3. `#print axioms` on all eight headlines → `[propext, Classical.choice, Quot.sound]`.
4. Zero warnings on all three modules.
5. `dedup.py --within` and `move_dead.py --source <path> --target /dev/null --dry-run` per module; the
   pin's own intra-file structures (row 1's engine, a headline against its `main`) stay, with the reason
   recorded.
6. `spec/AutomorphicFormSetAF16Consumer.lean` — **one zone per order**, real compositions, no `#check`, no
   `sorry`:
   - **A**: from `continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn` and
     `IsInducedSection.eq_of_eqOn_maximalCompact`, prove that two continuous induced sections agreeing on
     the maximal compact are equal;
   - **B**: take the decomposition at `n = 1` and read `φ s = c 0 s * ψ 0 s`, with `ψ 0` constant in its
     `K`-argument on the integral row-isometry subgroup;
   - **C**: use `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero` to produce
     `(t, k)` and `exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_…` to place `diagOne t * k`
     in the compact set, at a bounded height.
   Name whatever imports the zones need; error count is the deliverable metric.
7. `lean/tmp/probe-af16-statements.lean` still elaborates with exactly eight `sorry` warnings.

## 4. Report

Per row: lines written, declarations written and their namespace, every worklist entry dropped and why
(with the pin line), the pin line of every deviation, build time and silence, the checker counts at both
readings, the eight `#print axioms` blocks, `dedup`'s clusters and `move_dead`'s dispositions, the
consumer zone's error count, and one paragraph each on row 3 (the Siegel compactness: whether the fourteen
declarations came over cleanly) and row 1 (the span: whether the `EvalMatrix` import carried the argument).
Say whether `KT` was written as the brief says.

**A blocker goes back immediately** — "blocked on `<decl>` at pin `:NNN`; likely needs `<X>`", with the
pin line and the error. Do not grind out a diagnosis, never work around a hub defect locally, and do not
add an import, a module, or a `set_option`.
