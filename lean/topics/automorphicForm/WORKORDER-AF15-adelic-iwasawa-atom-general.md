# WORKORDER-AF15 — the Borel decomposition of an adelic point, and the two general archimedean atom integrals

**Issued 2026-11-02, one dispatch, two modules, two orders.** Scope: [SET-AF15.md](SET-AF15.md) — §1 the
three rows, §2 the price and the (nil) substitutions, §3 the definition gate, §4 the homes, §6 the risk
register, and **Appendix B, the per-declaration worklist**. This order states the work, the manager's
landed layer, the traps and the gates.

**Audience.** A fresh coding session. Wire: each target module carries its own `spec-pin:` header and
`spec/check_port.py` owns its public statements. **No per-declaration markers.** Pin clone
`/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`. Port mathlib `v4.34.0`.

**The size.** 3 rows, 1,101 silo, **1,031 lines in 91 declarations to write** (`port_plan`'s once-cost;
the worklist says 996 because it counts 51 lines as imported, and §2.1 of the brief shows that not one of
them is — write them). All three pin files are **private preludes with one public headline each**.

## 0. The manager's layer, landed (do not redo it)

1. **Both modules exist, build and are wired.**
   `FLTForHuman/AutomorphicForm/Adelic/AdelicIwasawa.lean` (66 lines: header with two `spec-pin:` lines,
   ten imports, opens, empty `namespace AutomorphicForm namespace LocalIntertwining namespace
   IwasawaArch`) and `FLTForHuman/AutomorphicForm/Adelic/ArchAtomGeneral.lean` (71 lines: header with
   four `spec-pin:` lines, six imports, opens, empty `… LocalIntertwining namespace ArchRealWeight` and
   `namespace ArchComplexMoments`). Both elaborate silent, both build green
   (`flock .lake/flt_build.lock lake build <module>`, 3,549 jobs for the closure — the premise module
   `RepTheory/LocalLanglands/IwasawaDecomposition` had no `.olean` and now does), and
   `spec/check_port.py --force` reads **0 ok / 0 mismatch / 0 missing** on each.
2. **The statements are verified.** `lean/tmp/probe-af15-statements.lean` states all **three**
   headlines verbatim from their wrappers as `example … := by sorry` against the two built modules and
   elaborates with **exactly three `declaration uses 'sorry'` warnings and nothing else**. Re-run it
   first. One finding it settled: the probe needs `open AutomorphicForm` in its file-level opens because
   the port nests `AdelicGL2` under `AutomorphicForm` where the pin reaches it through
   `NumberField.AdelicLevel` — an `open` does not touch a statement's text, so this is a probe-side fix
   only.
3. **The imports are the ones the mathematics needs; add none without reporting a blocker.**
   Order A: `AutomorphicForm/Adelic/BorelSubgroup`, `…/Adelic/WindowedSiegel/RowIsometry`,
   `…/Adelic/ArchWeightCharTransport` (`glEquivOfRingEquiv`, `norm_ringEquivRealOfIsReal`,
   `ringEquivRealOfIsReal`, `ringEquivComplexOfIsComplex`), `…/NumberTheory/AdelicLevel/{Level,Projections}`
   (`AdelicGL2`, `glFin`, `glArch`, `archComponent`, `archEval`, `adeleArch`, `adeleFin`,
   `finiteIntegralGL2`, `finiteLevelZero`), `…/RepTheory/LocalLanglands/IwasawaDecomposition`
   (`LocalGL2.iwasawa_decomposition`, the row's one graph premise), plus `Mathlib.Analysis.RCLike.Basic`,
   `Mathlib.Analysis.SpecialFunctions.Sqrt`, `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`,
   `Mathlib.LinearAlgebra.Matrix.Notation` for the rotation-matrix block (`RCLike.conj`, `Real.sqrt`,
   `GeneralLinearGroup.mkOfDetNeZero`, `!![…]`). Order B: `AutomorphicForm/Adelic/ArchAtomValues` (the
   two special rows, which are this module's premises) plus `Analysis.SpecialFunctions.Gamma.Deligne`,
   `…Gaussian.GaussianIntegral`, `…Pow.Complex`, `MeasureTheory.Integral.Bochner.Basic`,
   `MeasureTheory.Measure.Lebesgue.Complex`.
4. **Write all 102 declarations the pin files contain; import none of the eleven.** §2.1 of the brief is
   the table. Concretely: `map_ringEquiv` (21 lines) and `norm_ringEquivComplexOfIsComplex` (4) are
   statement-identical to **`private`** declarations at
   `AutomorphicForm/Adelic/BigCellExpansion.lean:165` and `:192` — copy their text, keep them `private`;
   `projV` (3) is identical to the `private` `AutomorphicForm.evFin`
   (`InducedSectionMaximalCompact.lean:364`) — copy it; `projW` (3) is the *same function* as the
   `private` `projArch` (`BigCellExpansion.lean:775`) but defined by components, so write the pin's
   `(archEval F w).comp (adeleArch (𝓞 F) F)`; **`mkUnit` (8) has no port copy** — `AutomorphicForm.kOne`
   is a different element (`kOne` includes one archimedean component and is `1` elsewhere) and matches
   only by type, so write the pin's `assemble`-built element; and `rad`/`base`/`phase`/`Q` (2 each) and
   the complex row's `W`/`M` (2 each) are `def`s the advise matched by shape to unrelated port defs
   (`HARCHR.c00`, `RealIwasawa.botRow`/`logLine`, `HARCHR.q`, `PeriodPair.addCoreE`, `WLight.qN`) — write
   the pin's.
5. **Visibility is the pin's and it is uniform: 99 `private` helpers plus the three headlines.** The
   dropped-`private` reading (§3.2) is this set's real statement check.
6. **No `Def_` node, no promotion, no migration, no legacy edit**: the four `Def_` modules of the closure
   report **0 missing** (including `Def_AutomorphicForm_ArchWeightCharTransport`, which only the seed's
   `S_` file imports), and every used declaration is ported.
7. **No `set_option`** beyond `autoImplicit false`; none of the three statements carries a top-level
   `let` (unlike SET-AF14's rows 1–3), so the checker's diff is honest on all three.

## 1. What you write

Appended below each skeleton's empty namespace pair, **order A first**, then order B. The two files share
no declaration and neither order's rows cite the other's, so the gates are per module either way.

| order | row (`AutomorphicForm.` dropped) | namespace | work / decls | shape |
|---|---|---|---:|---|
| A | `exists_mem_adelicBorel_mul_eq` | `LocalIntertwining.IwasawaArch` | **353** / 31 | `rotMat`/`rotMatN` and `isRowIsometry_rotMatN` (rotation matrices), `exists_iwasawa_rclike`/`_of_ringEquiv`/`_infinitePlace` (the local decompositions), `assemble` with `projV`/`projW` and their `_assemble` lemmas, `entry_mem_of_mem_integralSubgroup`/`mul_entry_mem`/`eventually_entries_mem`, `mkUnit` and its two membership lemmas, `adelicGL2_ext`, `arch_mul`/`fin_mul`, then the headline |
| B | `LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` | `LocalIntertwining.ArchRealWeight` | **441** / 44 | `base`/`phase`/`Q`/`rad`/`RHS`/`J` (the defs), `phase_*` and `hasDerivAt_phase*` (the derivative calculus), `recursion_raw`/`recursion` (the recursion on `k`), `closed_form_nat`/`closed_form_zero`, `RHS_step`/`RHS_neg`, `J_neg`, then the headline |
| B | `LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` | `LocalIntertwining.ArchComplexMoments` | **241** / 16 | `W`/`M` (the defs), `continuous_W`/`norm_W`, `angular_eq_zero`, `integrable_moment`/`norm_moment`, `moment_zero`/`moment_succ_pointwise`/`moment_succ`, `integral_eq_zero_of_ne`, `closed_form`, then the headline |

Each headline is **public at its pin name** (`AutomorphicForm.exists_mem_adelicBorel_mul_eq`,
`AutomorphicForm.LocalIntertwining.…`); the pin's `solution` body is the headline's body. Every helper is
`private`, in the row's namespace (`IwasawaArch` is the pin's own label and is kept; the pin's
`M4aP2DGK.` prefix is dropped from the other two).

**The two order-B rows use SET-AF14's module.** Their proofs bottom the recursions out in
`integral_one_add_sq_cpow_neg_eq_GammaReal_div` (pin `:318`) and
`integral_one_add_norm_sq_cpow_neg_eq_pi_div` (pin `:171`) — do not try to derive those from the general
rows; the dependency is the other way and the inversion is circular (brief §1).

## 2. Traps

1. **The seed is an assembly argument, not one lemma.** Follow the pin's own order: `rotMat*` →
   `exists_iwasawa_rclike` → `exists_iwasawa_of_ringEquiv` → `exists_iwasawa_infinitePlace` →
   `assemble`/`projV`/`projW` → the integrality lemmas → `mkUnit` → `glFin_mkUnit_mem`/`mkUnit_mem_adelicBorel`
   → `adelicGL2_ext`/`arch_mul`/`fin_mul` → the headline. The `assemble` integrality hypothesis is a
   cofinite `∀ᶠ v in Filter.cofinite` statement; keep it as the pin states it.
2. **The 465 row is the set's cost** (44 declarations, 441 lines, a 74-line `RHS_step`): a recursion on
   `k` through the weight `((x-I)/√(1+x²))^k`, with `k = 0` the `ArchAtomValues` row. Read the pin's
   sections in order; do not short-circuit the recursion.
3. **`mkUnit` ≠ `kOne`, and `base`/`phase`/`Q` ≠ `botRow`/`logLine`/`HARCHR.q`** (§0.4). The advise
   file will suggest these imports; they are `def`s matched by type, and importing them makes the
   statements false.
4. **`RCLike` is the pin's working generality** for the rotation block (`variable {L} [RCLike L]`), and
   `IsRowIsometry` is a `WindowedSiegel` predicate on `GL (Fin 2) L`. Keep the pin's generality; a
   `ℝ`/`ℂ` split is a rewrite, not a transcription.
5. **Binder spelling is the statement** (FR-0123): the seed's headline is `(F) [Field F] [NumberField F]
   (g : AdelicGL2 (𝓞 F) F)` with a four-conjunct `∃`; the 465 row's `(-Complex.I) ^ k` and the 264 row's
   `if a = b then … else 0` are part of the statements. Transcribe the wrappers' text.
6. **The 264 row's side condition** is `((a : ℝ) + b) / 2 + 1 < t.re`, not `0 < t.re`; the 465 row's is
   `0 < s.re`, and its RHS carries `Γ_ℝ(2s+1+k)` and `Γ_ℝ(2s+1-k)` in the denominator.
7. **No `sorry`/`admit`/`axiom`/`native_decide`, zero warnings, no `import Mathlib`**, no hub edit, no
   new module.

## 3. Gates

Per module:

1. `timeout 200 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <module>` silent, then its own
   `flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.AutomorphicForm.Adelic.<Module>`;
   **no tree build**, no dependents.
2. `python3 spec/check_port.py --force <module>` → **0 mismatch / 0 missing**, and the ok count measured:
   **1 per row** at the pin's visibility (3 in all: one in order A, two in order B).
   **Then the surface gate, which is mandatory here**: strip `private` from every declaration, re-read
   the three numbers (expect ~102 ok in all), record them, and restore the pin's visibility. A `MISMATCH`
   there is a real defect in a helper — fix it; a `MISSING` is a port-side helper and stays private.
3. `#print axioms` on the three headlines → `[propext, Classical.choice, Quot.sound]`.
4. Zero warnings on both modules.
5. `dedup.py --within` and `move_dead.py --source <path> --target /dev/null --dry-run` per module; a
   `shape` cluster of a headline against its own helper is the pin's `solution`-calls-`main` structure and
   stays, with the reason recorded.
6. `spec/AutomorphicFormSetAF15Consumer.lean` — **two zones**, real compositions, no `#check`, no
   `sorry`:
   - **the decomposition meets the induced-section law.** From `exists_mem_adelicBorel_mul_eq g` take
     `b, k` with `b ∈ adelicBorel`, `glFin k ∈ finiteIntegralGL2`, the `IsRowIsometry` archimedean
     components and `g = b * k`; then apply `IsInducedSection`'s defining law
     (`InducedSection.lean:28`, imported through the new module) to prove
     `φ g = χ₁ (borelDiagFst ⟨b, hb⟩) * χ₂ (borelDiagSnd ⟨b, hb⟩) * φ k`. That is the statement the
     eight rows SET-AF15 readies build on, and it must be *proved*, not asserted.
   - **the general evaluations return the special ones.** At `k = 0` and at `a = b = 0, t = 2s+1`, prove
     the identity between the general row's value and SET-AF14's special row's value
     (`Γ_ℝ(2s)·Γ_ℝ(2s+1) / (Γ_ℝ(2s+1)·Γ_ℝ(2s+1)) = Γ_ℝ(2s)/Γ_ℝ(2s+1)` and
     `π·0!·Γ(2s+1-1)/Γ(2s+1) = π/(2s)`).
   It imports the two new modules **and `AutomorphicForm/Adelic/InducedSection.lean`** (found at the
   landing: `IsInducedSection` is not reachable through either new module, since neither imports it —
   corrected here, and the consumer is the only file that changed); `lake env lean` it to zero errors.
7. `lean/tmp/probe-af15-statements.lean` still elaborates with exactly three `sorry` warnings.

## 4. Report

Per row: lines written, declarations written and their namespace, every worklist entry dropped and why
(with the pin line), the pin line of every deviation, build time and silence, the checker counts before
(0/0/0) and after at both readings (pin visibility and dropped `private`), the three `#print axioms`
blocks, `dedup`'s clusters and `move_dead`'s dispositions, the consumer zone's error count, and one
paragraph on the 465 row: whether the `k`-recursion transcribed cleanly or needed restructuring, with the
reason. Say whether the seed's rotation block kept `RCLike` generality.

**A blocker goes back immediately** — "blocked on `<decl>` at pin `:NNN`; likely needs `<X>`", with the
pin line and the error. Do not grind out a diagnosis, never work around a hub defect locally, and do not
add an import, a module, or a `set_option`.
