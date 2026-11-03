# WORKORDER-AF14 — the local atom at a place (integrability, the two evaluations, the limit at `s = 1/2`)

**Issued 2026-11-02, one dispatch, two modules.** Scope: [SET-AF14.md](SET-AF14.md) — §1 the eight rows,
§2 the price and the substitutions, §2.2 the same-name decisions, §3 the definition gate, §4 the homes,
§6 the risk register, and **Appendix B, the per-declaration worklist**. This order states the work, the
manager's landed layer, the traps and the gates.

**Audience.** A fresh coding session. Wire: each target module carries its own `spec-pin:` header and
`spec/check_port.py` owns its public statements. **No per-declaration markers.** Pin clone
`/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`. Port mathlib `v4.34.0`.

**The size.** 8 rows, 1,578 silo, **1,403 lines in 78 declarations to write** (1,393 net by
`port_plan`), in **two modules**: 627 lines / 31 declarations in order A, 776 / 47 in order B.

## 0. The manager's layer, landed (do not redo it)

1. **Both modules exist, build, and are wired.**
   `FLTForHuman/AutomorphicForm/Adelic/LocalAtomIntegrable.lean` (67 lines: header with six `spec-pin:`
   lines, eight imports, opens, an empty `namespace AutomorphicForm namespace LocalIntertwining`) and
   `FLTForHuman/AutomorphicForm/Adelic/ArchAtomValues.lean` (74 lines: header with ten `spec-pin:`
   lines, seven imports, opens, the same empty namespaces). Each has been elaborated
   (`lake env lean -DautoImplicit=false`, silent) and built
   (`flock .lake/flt_build.lock lake build <module>`, green), and `spec/check_port.py --force` reads
   **0 ok / 0 mismatch / 0 missing** on each — no declarations yet, wire correct.
2. **The statements are verified, not assumed.** `lean/tmp/probe-af14-statements.lean` states all
   **eight** headlines verbatim from their `Theorems/` wrappers as `example … := by sorry` against the
   two built modules, one `namespace Probe…` block per row, and elaborates with **exactly eight
   `declaration uses 'sorry'` warnings and nothing else**. Re-run it first; it is the statement check
   for the whole set. Two findings it settled, both now in the probe and both load-bearing:
   - **row 8 needs `open scoped Classical in` on the declaration.** Without it the statement does not
     elaborate (`synthInstanceFailed` for `Fintype {w // w.IsReal}`, `MeasureSpace
     (mixedEmbedding.mixedSpace F)` and `Fintype {w // w.IsComplex}`). The wrapper has the same line
     directly above its `theorem`; put it directly above yours.
   - the eight statements need no `set_option` and no notation scope beyond `open scoped NNReal`
     (row 1's `ℝ≥0` in the `modulus` cast).
3. **The imports are complete; add none.** Order A: `EisensteinGeneral.LocalRam` (`integrable_twisted_smooth`),
   `NumberTheory/NumberField/TateGlobal/NormIntegrable` (`modulus_adicCompletion_eq_nnnorm`),
   `NumberTheory/NumberField/TateGlobal/LocalZetaUnramified` (`isCompact_integers`),
   `LanglandsTunnell/TateLocalZeta` (`modulus`), and the mathlib modules the three `S_` files need
   instead of their `import Mathlib` (`MeasureTheory.Integral.Bochner.Basic`,
   `MeasureTheory.Measure.Lebesgue.{Basic,Complex}`, `Analysis.SpecialFunctions.Pow.Complex`).
   Order B: `AutomorphicForm/Adelic/RightConvNeZeroArch` (`AutomorphicForm.TestFnArchProfile.sqSize`),
   `Analysis.SpecialFunctions.Gamma.Deligne` (`Complex.Gammaℝ`),
   `Analysis.SpecialFunctions.Gaussian.GaussianIntegral`, `Analysis.SpecialFunctions.Pow.Complex`,
   `MeasureTheory.Integral.Bochner.Basic`, `MeasureTheory.Measure.Lebesgue.Complex`,
   `NumberTheory.NumberField.CanonicalEmbedding.Basic` (`mixedEmbedding.mixedSpace`). Verified with
   `#check`: `integrable_rpow_neg_one_add_norm_sq` (the §2.1 short proof's engine) and
   `Complex.Gammaℝ` are already in scope, and **`Complex.Gammaℝ_two_mul` /
   `Complex.Gammaℝ_two_mul_add_one` do not exist** — they are the pin's own 7-line helpers and are to be
   written. If a proof needs another import, that is a blocker.
4. **The §2.1 decision on `integrable_one_add_sq_rpow_neg` (row 4's 51 pin lines): write it at the
   pin's name with the port's 8-line proof, do not transcribe the pin's 51 lines and do not promote.**
   The port's `private integrable_dom` (`FLTForHuman/AutomorphicForm/Iwasawa/Real/Continuation.lean:71`)
   is the same statement; its proof is
   ```lean
   have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * σ)
     (by rw [Module.finrank_self]; push_cast; linarith)
   refine h.congr (Filter.Eventually.of_forall fun x => ?_)
   simp only [Real.norm_eq_abs, sq_abs]
   congr 1
   ring
   ```
   at the pin's binder `{c : ℝ} (hc : 1 / 2 < c)` and with the pin's name. `one_add_sq_pos` (2 lines)
   and `rpow_le_max` (6) are **port-once**: write each **once**, publicly, at the pin's name, in order
   B's module, and use the one copy from both of its rows.
5. **The two binder-variant rows (7 lines each) are written at the pin's text**, not imported:
   `two_le_absNorm` (row 1; the port has a public copy at
   `NumberTheory/FrobeniusDensity/PrimeSumAsymptotic.lean:33` under a different binder spelling, but it
   is not imported by either module — restating at the pin's 7 lines avoids both an import and a
   `MISMATCH`), and `norm_sub_I` (row 3; the port's copy at `Iwasawa/Real/Continuation.lean:49` is
   `private` and cannot be imported).
6. **Three same-name pairs are namespace splits, in code and in the port**: `floor` and `entries_pos`
   (rows 2 and 3 — `ℂ` against `ℝ`) and `atom` (rows 6 and 7 — a `def`, `ℂ` against `ℝ`). Each pair is
   written **twice**, once in each row's sub-namespace. Do not rename, do not merge, do not widen a
   binder to make one copy serve: the statements are not the pin's if you do.
7. **Two port names differ from the pin's and must be used as the port spells them** (both confirmed by
   `#check`): the row-1 premise the pin calls
   `LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm` is
   `NumberField.TateGlobal.modulus_adicCompletion_eq_nnnorm` in the port; the substitution the pin calls
   `isCompact_integers` is `NumberField.TateGlobal.LocalZetaUnramified.isCompact_integers`. And the
   advise row's `maj` → `AutomorphicForm.TestFnArchProfile.sqSize` is a **shift**: the pin's
   `maj σ y = sqSize y ^ σ`.
8. **No `Def_` node, no promotion, no migration, no legacy edit.** `gate_scan` over the two `Def_`
   modules of the closure reports **0 missing** in both, and the only declaration used is
   `LanglandsTunnell.TateLocal.modulus` (ported).
9. **No `set_option` except the two `open scoped Classical in`/`autoImplicit false` already declared.**
   The pin's `letI`/`haveI` walls in proofs become `have`/`let` (FR-0126); a suppression is justified
   only for a term-mode `letI` inside a definition body.

## 1. What you write

Appended below each skeleton's empty namespace pair, in two orders. **Order A first** (it is smaller
and its rows are the ones the topic note's neighbours expect), then order B; the two files share no
declaration, so if you prefer to interleave, the gates are per module either way.

| order | row (`AutomorphicForm.LocalIntertwining.` dropped) | module | work / decls | shape |
|---|---|---|---:|---|
| A | `integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | `LocalAtomIntegrable` | **257** / 16 | the finite-place atom: uniformizer/uniform balls, `integrableOn_of_locallyConstantOn`, then `integrable_atom` and the Weyl shift |
| A | `integrable_complexAtom_and_integrable_moebiusShift` | `LocalAtomIntegrable` | **205** / 6 | `integrable_complexFactor`, the `floor`/`entries_pos` determinant block, `norm_complexFactor_le`, then the Möbius change of variables |
| A | `integrable_realAtom_and_integrable_moebiusShift` | `LocalAtomIntegrable` | **165** / 9 | the same over `ℝ`, with `norm_sub_I`/`norm_unit`/`norm_realFactor_eq` |
| B | `integral_one_add_sq_cpow_neg_eq_GammaReal_div` | `ArchAtomValues` | **298** / 11 | `scaledGammaIntegral`, `integrable_uncurry_kernel`, `integral_cpow_neg_one_add_sq` (the scaled-Γ/Fubini argument), then `Γ_ℝ(2s)/Γ_ℝ(2s+1)` |
| B | `integral_one_add_norm_sq_cpow_neg_eq_pi_div` | `ArchAtomValues` | **88** / 5 | `integral_value` over `ℂ` = `π/(2s)`, by the two real integrals in `re`/`im` |
| B | `tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` | `ArchAtomValues` | **157** / 13 | the `atom` def, the `norm_*` estimates, `tendsto_F`, then dominated convergence to `0` at `σ ↓ 1/2` |
| B | `tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` | `ArchAtomValues` | **134** / 11 | the same over `ℝ` |
| B | `exists_bound_norm_integral_mixedSpace_archAtom_prod` | `ArchAtomValues` | **99** / 7 | `real_bound`/`cx_bound` placewise, `integrable_maj`, then the product bound on the strip (`W4ARCH`) |

**Namespaces (one per pin file; the pin's labels are proof-search artefacts).** Order A:
`AutomorphicForm.LocalIntertwining.IntV` (row 1 — the pin's own label, subject-named, kept),
`…LocalIntertwining.ComplexAtom` (row 2, pin `IntArchC`), `…LocalIntertwining.RealAtom` (row 3, pin
`IntArchR`). Order B: `…LocalIntertwining.GammaReal` (row 4, pin `M4aP2DGK.ArchReal`),
`…LocalIntertwining.PiDiv` (row 5, pin `M4aP2DGK.ArchComplex`), `…LocalIntertwining.ComplexAtomLimit`
(row 6, pin `ARCHA4C`), `…LocalIntertwining.RealAtomLimit` (row 7, pin `ARCHA4R`),
`…LocalIntertwining.MixedSpaceBound` (row 8, pin `W4ARCH`). Each headline is **public at
`AutomorphicForm.LocalIntertwining.<pin name>`** (the pin's `solution` body is the headline's body) and
is declared **before** its namespace's helpers, or after them — your choice; the checker reads names,
not order.

**Visibility follows the pin's, and it is nearly everything here.** Five of the eight pin files are
flat public surfaces (rows 2–7): every helper there is a pin-public declaration, so it is public here
and `check_port` will diff it. Only rows 1 and 8 have a `private` prelude (15 helpers ≈133 lines; 6
helpers ≈61 lines) — those stay `private`, because a pin-private helper made public comes out
`MISMATCH` on the pin's `section`-variable spelling (FR-0123).

## 2. Traps

1. **Three statements carry a top-level `let`** — rows 1, 2, 3 (`let a := …` and `let atom := …`) — so
   `check_port`'s `top_level_cut` truncates their diff at the first `:=` and its `ok` is **degenerate**
   (FR-0056). Copy the wrapper's text verbatim and read those three by eye; the probe (§0.2) is the
   other check.
2. **Five pin `S_` files `import Mathlib`** (rows 2, 3, 6, 7, 8). Never import `Mathlib`; §0.3 names the
   modules. Expect to need one more at a blocker — report it, do not add it silently.
3. **The `Γ_ℝ` row is the set's cost** (298 lines, 11 declarations: `integral_cpow_neg_one_add_sq` 77,
   `scaledGammaIntegral` 64, `integrable_uncurry_kernel` 49). It is a scaled-Γ/Fubini computation with an
   `ℝ≥0`-valued intermediate (the pin's `scaledGammaIntegral`); read the pin's file in order, and do not
   try to unify it with row 5's `π/(2s)` radial argument before the last declaration.
4. **Rows 6 and 7 are limits from above**: the filter is `𝓝[>] (1/2 : ℝ)`, and the two `atom` defs
   differ by place. Do not "simplify" them into one (`floor`, `entries_pos`, `atom` are the three
   splits of §0.6).
5. **Row 8's statement needs `open scoped Classical in`** (§0.2), and its `∃ C` is uniform in `σ ∈
   (1/2, 1]` but **not** in the data `kdat`/`abm`: the bound depends on them, and only the hypothesis
   `(abm w).1 + (abm w).2.1 ≤ (abm w).2.2` is given. Its six private helpers stay private.
6. **Binder spelling is the statement** (FR-0123). Rows 2 and 3 spell their hypotheses `_hdet`, `_hσ`,
   `_habm`; row 1 spells `_hm`, `_hA`, `_hB` and carries the instance binders
   `[MeasurableSpace (v.adicCompletion F)] [BorelSpace …] [μ.IsAddHaarMeasure]`; rows 6 and 7 spell
   `_h`, `_habm`. Transcribe the wrapper's text, underscores included.
7. **`port_plan`/`af-worklist`'s "imported" figures overstate the reuse by 55 lines** (§2.1 of the
   brief): the 51 of row 4 and the 2+2 of rows 6/7 are `private` port copies. §0.4 and §0.5 are the
   decision; do not re-derive it.
8. **No `sorry`/`admit`/`axiom`, no `native_decide`, no `set_option maxHeartbeats`, zero warnings**, no
   hub edit, no new module, no new import without a report.

## 3. Gates

Per module, in this order:

1. `timeout 200 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <module>` silent, then its own
   `flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.AutomorphicForm.Adelic.<Module>`;
   **no tree build**, no dependents, no other module's build.
2. `python3 spec/check_port.py --force <module>`: **0 mismatch / 0 missing**, and the ok count
   **measured and reported**. Expect a large ok count (rows 2–7 alone are 55 public declarations); a
   `MISSING` is a port-side helper to keep `private`, a `MISMATCH` a spelling to fix. Then the recipe's
   surface gate: drop `private` on everything, read the three numbers again, record them, and restore
   the pin's visibility.
3. `#print axioms` on all eight headlines → `[propext, Classical.choice, Quot.sound]`.
4. Zero warnings on both modules.
5. `dedup.py --within` and `move_dead.py --source <path> --target /dev/null --dry-run` per module; the
   `rpow_le_max`/`one_add_sq_pos` port-once pair and the `floor`/`entries_pos`/`atom` splits are
   intended, and are kept with the reason recorded.
6. `spec/AutomorphicFormSetAF14Consumer.lean` — **two zones**, real compositions, no `#check`, no
   `sorry`, imported from the two new modules only:
   - at a real place, `(integrable_realAtom_and_integrable_moebiusShift 1 0 0 1 0 σ hσ).1` at `k = 0`
     together with `integral_one_add_sq_cpow_neg_eq_GammaReal_div σ hσ` to read
     `∫ x, atom σ x = Complex.Gammaℝ (2*σ) / Complex.Gammaℝ (2*σ+1)`;
   - at a complex place, the same with
     `(integrable_complexAtom_and_integrable_moebiusShift 1 0 0 1 0 0 0 σ hσ).1` and
     `integral_one_add_norm_sq_cpow_neg_eq_pi_div` to read `∫ z, atom σ z = π/(2σ)`.
   If an instantiation needs a hypothesis neither row supplies, state it on the consumer side and
   report it — never weaken a headline.
7. `lean/tmp/probe-af14-statements.lean` still elaborates with exactly eight `sorry` warnings.

## 4. Report

Per row: lines written, declarations written and their namespace, every worklist entry dropped and why
(with the pin line), the pin line of every deviation, build time and silence, the checker counts
(before 0/0/0, after measured, plus the dropped-`private` reading), the eight `#print axioms` blocks,
`dedup`'s clusters and `move_dead`'s dispositions, the consumer zone's error count, and one paragraph on
the `Γ_ℝ` row: whether the scaled-Γ/Fubini argument transcribed cleanly or needed restructuring, with
the reason. Also say whether `integrable_one_add_sq_rpow_neg` took the §0.4 short route.

**A blocker goes back immediately** — "blocked on `<decl>` at pin `:NNN`; likely needs `<X>`", with the
pin line and the error. Do not grind out a diagnosis, never work around a hub defect locally, and do not
add an import, a module, or a `set_option`.
