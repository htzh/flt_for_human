# Frictions log

Append-only record of frictions, pitfalls and caveats met while porting: things that cost a
session time, looked like something else first, or will bite again. One entry per friction,
**newest at the bottom**; never rewrite an old entry, add a new one that supersedes it and say so.

This is the general log — the raw field reports. Two neighbours hold distilled or specialised
material: [../instance-friction.md](../instance-friction.md) is the typeclass-instance register
(with re-runnable harnesses), and [../porting-playbook.md](../porting-playbook.md) is where a
friction that generalizes becomes a rule (§3.6, §6–§7). Record here when it happens; the refactor
round promotes what generalizes.

## How to use it

- **Before** fighting something for more than a few minutes, grep this file:
  `grep -in '<keyword>' logs/frictions.md`.
- **After** you resolve it, append an entry at the bottom in the template below. Keep it factual:
  what you saw, what it actually was, what fixed it. Do not delete or rewrite earlier entries.
- **Tags** go in the heading, from this closed vocabulary (add to it in a new entry if needed):
  `build`, `checker`, `tooling`, `lean`, `docs`, `git`, `mathlib`, `pin`.
- List the entries: `grep -n '^## FR-' logs/frictions.md`.
- Filter by tag: `grep -n '\[build\]' logs/frictions.md`.

## Template

```text
## FR-NNNN [tag] — <one-line title>
- **where**: the module / tool / step it bites.
- **symptom**: what you see.
- **cause**: what it actually is.
- **fix**: what to do, and how to verify it.
- **seen**: <date>; <optional reproduction command or note>
```

---

## FR-0001 [build] — a "whole-tree build" is `lake build <lib>`, and it is the session's last act

- **where**: any `lake build` aimed at the library target (`lake build FLTForHuman`).
- **symptom**: thousands of jobs and tens of minutes of wall time; the last one measured over
  20 minutes and still growing as the port grows.
- **cause**: only building a dependent (or a library target) re-elaborates the cascade; `lake env
  lean <file>` compiles nothing and `lake build <module>` never builds dependents.
- **fix**: build the wave's affected targets, serialized under `flock`; make the whole-tree build
  the one agreed action at the session's end. See playbook §3.5.
- **seen**: 2026-10-13.

## FR-0002 [build] — comment and docstring edits invalidate `.olean`s too

- **where**: any module you touch while or after a build is running.
- **symptom**: a docstring-only fix triggers a full dependent cascade; a build that finished
  before the edit no longer matches the sources.
- **cause**: Lake hashes file *content*, not just the declarations, so a comment change is a
  change.
- **fix**: batch every edit — prose included — before starting the build, and check staleness by
  comparing the source's mtime with the `.olean`'s before claiming a tree is green.
- **seen**: 2026-10-13.

## FR-0003 [build] — a stale `.olean` reads as a missing declaration

- **where**: a consumer of a module whose `private` → public promotion, move or rename just landed.
- **symptom**: `Unknown constant …` in a consumer even though the declaration exists.
- **cause**: `lake env lean` reads the cached `.olean` of the defining module, whose statements
  still carry the old constant.
- **fix**: rebuild the defining module first, then the consumers **in dependency order**. In a
  rename this is two passes, not one.
- **seen**: 2026-10-13.

## FR-0004 [build] [lean] — `lake env lean` does not inherit the lakefile's `leanOptions`

- **where**: the edit loop.
- **symptom**: `autoImplicit`/`maxHeartbeats` behave differently from `lake build`, so a file can
  pass the edit loop and fail the build, or vice versa.
- **cause**: `lake env lean` runs Lean directly; only `lake build` applies the package options.
- **fix**: run the edit loop with `-DautoImplicit=false -DmaxHeartbeats=200000` and a wall timeout,
  and keep the cap low on purpose: a declaration that will not fit is an instance-inference defect
  to diagnose, not a bound to raise. See playbook §3.5, §6.
- **seen**: 2026-10-13.

## FR-0005 [checker] — the statement checker is text-only, and `--` comments shift its namespaces

- **where**: `spec/check_flt_statements.py`; any module whose header prose uses `--` comments.
- **symptom**: a wrong *dotted* name — which is what `OWN_PROOFS` and `--prop-bodies` key on — while
  the last-name lookup still looks fine.
- **cause**: block comments are stripped in one pass and line comments in a second, so each `--`
  comment shifts every later namespace event.
- **fix**: write header prose in `/- … -/` blocks. The checker never invokes Lean, so it also works
  on a module whose proofs do not elaborate — run it first on a module stuck in a failing edit
  loop.
- **seen**: 2026-10-13; playbook §4.

## FR-0006 [tooling] — `unwired_register.py --json` rewrites the tracked register

- **where**: `tools/deps/unwired_register.py`, `spec/UNWIRED-PUBLIC.md`.
- **symptom**: a read-only-looking invocation dirties a tracked file.
- **cause**: the tool writes the register unconditionally; only `--check` returns before writing.
- **fix**: use `--check` unless the register is meant to be regenerated, and check `git status`
  after any run of the tool.
- **seen**: 2026-10-13.

## FR-0007 [tooling] — `port_advise` reports a landed module's own output as pre-existing mathematics

- **where**: re-running `port_advise` on a pin file after its engine has been written.
- **symptom**: the substitution count jumps — every transcribed declaration matches itself, each
  extra row carrying `port: …/<the new module>` — which invites deleting real declarations.
- **cause**: the tool scans the whole port tree, so a module sees its own output.
- **fix**: use the advise file generated *before* the module was written, or exclude the new module
  from the scan.
- **seen**: 2026-10-13.

## FR-0008 [lean] — `end A.B` closes both nested scopes

- **where**: a file with `namespace A` / `namespace B`.
- **symptom**: names declared after the `end` are silently de-nested; the errors appear far
  downstream as unknown identifiers, so on a slow module it costs a whole re-elaboration round.
- **cause**: `end A.B` matches both open scopes, not just the inner one.
- **fix**: write two bare `end`s. See playbook §7.
- **seen**: 2026-10-13.

## FR-0009 [docs] — tracked Markdown is rendered by GitHub, with its own math rules

- **where**: any tracked note, work order or register.
- **symptom**: math shows as raw text (inline delimiters escape wrongly) or a `pmatrix` collapses
  to one row.
- **cause**: GitHub's math rendering needs the backtick-dollar inline form and doubled backslashes
  in display math (the DSH GUI uses plain KaTeX and does not).
- **fix**: run `python3 tools/check_math_delimiters.py <file>` after editing a tracked `.md`. See
  [../../notes/github-markdown-math.md](../../notes/github-markdown-math.md).
- **seen**: 2026-10-13.

## FR-0010 [git] — only the user commits

- **where**: the working tree.
- **symptom**: — (process caveat, not a failure).
- **cause**: the repository is published separately; staging and pushing are the user's call.
- **fix**: leave changes unstaged and report them; never `git add`/`commit`/`push` unprompted.
- **seen**: 2026-10-13; `AGENTS.md`.

## FR-0011 [tooling] — an abbreviated `-- pin:` filename yields a bogus provenance silently

- **where**: any module's `-- pin: <name> (<file>:<line>)` comment, read by
  `tools/deps/unwired_register.py`.
- **symptom**: `spec/UNWIRED-PUBLIC.md` renders the pin-file link with a literal `…` and a broken
  URL, yet still counts the declaration as having a pin original — so `unwired_register.py --check`
  passes and the staleness gate never fires.
- **cause**: the register takes the filename from the comment verbatim and does not validate it
  against the pin; a long pin filename is easy to shorten while writing the comment.
- **fix**: write the pin filename **in full** in every `-- pin:` comment (they are long — that is
  fine), then regenerate and check: `python3 tools/deps/unwired_register.py` followed by
  `grep -c '…' spec/UNWIRED-PUBLIC.md` (want 0).
- **seen**: 2026-10-13; `TateGlobal/WeylPrelude.lean`.

## FR-0012 [lean] — two `maximalIdeal`s: the namespace you define *in* beats the one you `open`

- **where**: porting the pin's `M4aP2DGK.FinGK.ValuationOrd` block (the generic DVR `ord` lemmas)
  into a port module, e.g. `TateGlobal/WeylShell.lean`.
- **symptom**: `(maximalIdeal A) ^ n` stops being an ideal power; `x ∈ maximalIdeal A` fails with
  `failed to synthesize instance Membership (↥A) (HeightOneSpectrum ↥A)`; and a goal printed as
  `Ideal.map ↑e (IsLocalRing.maximalIdeal A) ^ n = …` does not react to a rewrite by
  `map_maximalIdeal_ringEquiv`, which looks like a `rw`/`congr` problem and is not one.
- **cause**: mathlib v4.34 carries **both** `IsLocalRing.maximalIdeal : Ideal R`
  (`Mathlib/RingTheory/LocalRing/MaximalIdeal/Defs.lean:30`) and
  `IsDiscreteValuationRing.maximalIdeal : HeightOneSpectrum A`
  (`Mathlib/RingTheory/Valuation/Discrete/IsDiscreteValuationRing.lean:41`). Inside
  `namespace IsDiscreteValuationRing` the second shadows the first, `open IsLocalRing`
  notwithstanding; the pin's block sits in a namespace that does not shadow it, so the pin's text
  `maximalIdeal A` means the ideal. The same trap in the other direction: `open Ideal` inside
  `namespace NumberField` resolves to `NumberField.Ideal` (Lean emits an `Ambiguous namespace`
  warning) and silently opens nothing of mathlib's `Ideal` — write `open _root_.Ideal`.
- **fix**: home such a block **outside** the shadowing namespace (the port's `WeylShell.lean`
  keeps it in `NumberField.TateGlobal.WeylShell` with `open _root_.Ideal`), or qualify
  `IsLocalRing.maximalIdeal` at every occurrence. `#check @maximalIdeal` tells you which one is in
  scope before you start rewriting.
- **seen**: 2026-10-14; `TateGlobal/WeylShell.lean`.

## FR-0013 [lean] — a restricted `open Foo (n₁ … n_k)` is all-or-nothing

- **where**: a module header that opens an explicit name list, one of whose names is defined later
  in the same file.
- **symptom**: a single `unknown constant Foo.<later>` at the `open` line, followed by
  `unknown identifier` for *every other* name in the list at its use site; the cascade reads like
  a broken import and cost a full pass over the file before the one-line cause was found.
- **cause**: `open` with an explicit name list opens nothing at all if any listed name is missing.
- **fix**: list only names that already exist (the restricted open is exactly what keeps a
  shadowing namespace out — FR-0012 — so do not simply widen it), and read the **first** error at
  the `open` line rather than the downstream cascade. A name defined in the same file can be
  brought into scope after its definition instead.
- **seen**: 2026-10-14; `TateGlobal/WeylShell.lean` (`ordA_unit` was listed before it was defined).

## FR-0014 [checker] [pin] — a recorded rename *inside a statement* is invisible until the module is wired, then all its sites MISMATCH

- **where**: wiring `NumberTheory/NumberField/TateGlobal/WeylPrelude.lean` (Set 0) together with the
  `AutomorphicForm.LocalIntertwining` pin sources.
- **symptom**: the port's one recorded rename `ValuationOrd.ord` → `IsDiscreteValuationRing.ord`
  leaves 8 port statements differing from the pin by that single token; `norm()` in
  `spec/check_flt_statements.py` has no rule for it, so each is reported `MISMATCH` although the
  module is mathematically the pin's.
- **cause**: the checker normalises `ModularCurve.`, `AlgebraicCurve.` and the `kw_` prefix, i.e.
  namespace/promotion spelling it has seen before; the pin's per-file private-prelude namespaces
  (`ValuationOrd.*`) have no matching rule. Because the rename is in the *signature* (e.g.
  `modulus x = normQ v ^ (-(…ord…))`), it is diffed, and the module's own compile cannot see it.
- **fix**: manager's call — either add a symmetric normalisation (erase the pin side's
  `ValuationOrd.` and the port side's `IsDiscreteValuationRing.` in `norm`, exactly as `kw_` is
  erased on both sides), or provide a port `ValuationOrd.ord` alias and spell the pin's name in
  statements. Measured (`aa2d8b3` + the port at this date, shadow harness on the checker's own
  functions, `WeylPrelude.lean` + `WeylShell.lean` + `WeylUnramified.lean` in `PORT_FILES` and the
  node's `Theorems/` wrapper and `S_` file appended to `SOURCES`): 8 mismatches, all in
  `WeylPrelude.lean` — `modulus_coe_units_adicCompletion`,
  `modulus_of_ne_zero_adicCompletion`, `coe_mem_integers_iff_ord_nonneg`,
  `valued_eq_one_of_ord_eq_zero`, `ord_eq_one_of_valued`, `char_eq_one_of_ord_eq_zero`,
  `char_eq_zpow_of_ord`, `ord_of_mem_negShell` — and 0 in the two new modules, because no new
  statement mentions `ord` (only their proofs do).
- **seen**: 2026-10-14.

## FR-0015 [checker] [tooling] — "already in the port" by last name can be a *different* lemma

- **where**: deduplicating the `LocalIntertwining` shared prelude (`port_advise.py`, the work
  order's §3 table).
- **symptom**: `ofReal_pow_cpow` reads as already ported, so the pin's `cpow_qpow_bridge` looks like
  free reuse; the port's copy cannot prove it, and its statement is a different theorem.
- **cause**: the pre-port view is name-anchored, hence a lower bound (playbook §2.4): a same-last-name
  declaration with a different statement or binder order is invisible. Here the pin's
  `ofReal_pow_cpow` is `(((a ^ k : ℝ)) : ℂ) ^ s = (((a : ℝ) : ℂ) ^ s) ^ k`, while
  `FLTForHuman/NumberTheory/NumberField/CompletedDedekindZeta/Mellin.lean:115` is
  `((a : ℂ) ^ n) ^ z = (a : ℂ) ^ (n * z)` (different binders, different identity); both are
  tier 3, so no checker run surfaced the difference either.
- **fix**: diff the *statement*, not the name, before banking a reuse. The pin's 8-line version is
  re-proved `private` in `TateGlobal/WeylShell.lean` (its consumer there is `cpow_qpow_bridge`); the
  alternative is importing `…CompletedDedekindZeta.Mellin` for a lemma that does not fit.
- **seen**: 2026-10-14.

## FR-0016 [mathlib] [build] — pin-verbatim proofs collect v4.34 deprecation warnings; adapt, do not investigate

- **where**: any prelude proof transcribed unchanged from the pin, e.g.
  `TateGlobal/WeylShell.lean`.
- **symptom**: `deprecated` warnings (never errors) — `MeasureTheory.measure_diff`,
  `Set.diff_eq_empty`, `Set.diff_subset` — which read like API drift to chase.
- **cause**: v4.34 renamed the `diff` family to `sdiff`: `measure_sdiff`, `Set.sdiff_eq_empty`,
  `Set.sdiff_subset`.
- **fix**: rename at the proof site (proof text is not diffed; statements are untouched), and keep
  the `-- pin:` provenance comment. A warning-free tier-1 build is then the module's own output.
- **seen**: 2026-10-14; `TateGlobal/WeylShell.lean`.

## FR-0017 [tooling] [checker] — correction to FR-0015: the port carries `ofReal_pow_cpow` **twice**, and the copy you want is the one the checker cannot see from the name alone

- **where**: same dedup step as FR-0015 (`ofReal_pow_cpow` in the `LocalIntertwining` prelude).
- **symptom**: FR-0015's fix line named only `…CompletedDedekindZeta/Mellin.lean:115` as the port's
  copy. A later sweep shows a **second** port declaration of the same last name,
  `TateGlobal/EulerFactors.lean:80`, whose statement is the pin's identity with a different binder
  spelling: `{x : ℝ} (hx : 0 ≤ x) (m : ℕ) (s : ℂ)` versus the `LocalIntertwining` pin file's
  `{a : ℝ} (ha : 0 ≤ a) (s : ℂ) (k : ℕ)`.
- **cause**: the pin proves the same helper in two files under the same name with different binder
  order; the port transcribed both, each matching its own pin original. A name-only dedup cannot
  say which copy proves what, and a *public* port declaration must additionally reproduce the
  binder spelling of the source the checker will match (`Theorems/` wrapper or the first `SOURCES`
  entry carrying the name — here the T1 `S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`).
- **fix**: for a private, in-file use, keep the local 8-line proof (as `TateGlobal/WeylShell.lean`
  does); for reuse, import `TateGlobal/EulerFactors.lean` (same identity, different spelling), not
  Mellin. Supersedes only FR-0015's fix line; its diagnosis stands.
- **seen**: 2026-10-14.

## FR-0018 [checker] — resolution of FR-0014: a recorded rename *inside* a statement is a `norm()` rule

- **where**: `spec/check_flt_statements.py`, `norm()`.
- **symptom**: FR-0014 — wiring a module whose statements spell a deliberately renamed pin name
  (here the pin's `ValuationOrd.ord` against the port's `IsDiscreteValuationRing.ord`) reported one
  MISMATCH per site, eight of them for `TateGlobal/WeylPrelude.lean`.
- **cause**: `norm()` erased the declaration-name and in-statement noise of the namespaces it knew
  (`ModularCurve.`, `AlgebraicCurve.`, `kw_`) but had no rule for the pin's re-carried private-prelude
  namespaces.
- **fix**: `norm()` now erases `ValuationOrd.` and `IsDiscreteValuationRing.` on both sides when the
  qualifier is followed by one of the block's sixteen names — the same treatment, and the same
  monotone argument, as the existing `kw_` erasure. Restricted to those names so an unrelated
  `IsDiscreteValuationRing.*` (mathlib's `addVal`, `idealOrderIsoENat`) is untouched. The three
  `Weyl*` modules then wire clean: `9652 identical / 0 mismatched / 0 missing`.
- **consequence for the next rename**: a move that changes a name *inside* a signature needs either
  the port to keep the pin's spelling in statements or a `norm()` rule; it is not enough to record
  the rename in the topic and the register.
- **seen**: 2026-10-14.

## FR-0019 [pin] [checker] — a headline can be blocked by a pin `Definitions/` name the port never homed, not by mathematics

- **where**: set LI-2, `AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion`
  (`TateGlobal/WeylSmooth.lean`).
- **symptom**: every in-scope prelude declaration the set needs is present and green, yet the
  headline's hypothesis `hχ : ∃ c : ℕ, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1`
  cannot even be *stated*: `higherUnitsAt` (and its whole `LanglandsTunnell.TateLocal` constants
  module) has no port home. The set's plan counted a "definition layer" only for the definitions
  *inside* the two `S_` files; this one is imported from
  `Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean` and was never in scope for anybody.
- **cause**: the pre-port reuse audit (`port_advise.py`) is anchored on the `S_` files; an imported
  `Definitions/` declaration that no earlier ported module consumed is invisible to it, and the
  unramified twin of the node uses the *equivalent* zero-depth form
  (`∀ u, Valued.v u = 1 → χ u = 1`) instead of `higherUnitsAt`, so LI-1 neither needed nor noticed it.
- **fix**: transcribe the missing definition (3 lines) into the set's own module with its own
  `-- pin:` provenance, and flag it for promotion to a `LanglandsTunnell/TateLocalConstantsAt.lean`
  in the refactor round. Two traps in the transcription:
  (a) the pin declares `K` and `v` as **section variables**, so `declarations()` reads the signature
  as `(n : ℕ) : Set (v.adicCompletion K)ˣ`; writing them inline (`(K : Type) … (v …) (n : ℕ)`) gives
  a textually different signature and, once the `Definitions/` file is in `SOURCES`, a `MISMATCH`.
  Keep the pin's `variable (K …) (v …)` form.
  (b) The checker's last-name match is unaffected, so the set still wires clean on the headline.
- **seen**: 2026-10-14; `TateGlobal/WeylSmooth.lean`; measured with the checker's own
  `declarations()` (port `(n : ℕ)` vs pin `(n : ℕ)` → `IDENTICAL` after the fix).

## FR-0020 [lean] [build] — the pin's faithful instance context is no longer warning-free in `v4.34`, and three different linters fire

- **where**: `TateGlobal/WeylSmooth.lean` (`setIntegral_units_smul`, `setIntegral_tailShell`,
  `setIntegral_norm_tailShell`, `integral_smoothWeylIntegrand_impl`).
- **symptom**: three warning classes on pin-verbatim declarations: `linter.overlappingInstances`
  ("`[μ.IsAddHaarMeasure]` and `[μ.Regular]` each imply `[IsFiniteMeasureOnCompacts μ]`") on every
  declaration whose section context carries both instances, and `linter.style.haveILetI` on the
  pin's `haveI : μ.Regular := inferInstance` opening the implementation.
- **cause**: v4.34's `IsAddHaarMeasure` now implies `IsFiniteMeasureOnCompacts`, so the pin's
  deliberate `[μ.IsAddHaarMeasure] [μ.Regular]` pair (the pin's own `measure_smul_integers` comment
  says it keeps both) overlaps; and these linters post-date the pin (Lean `v4.33.1`).
- **fix**: suppress locally — `set_option linter.overlappingInstances false in` /
  `set_option linter.style.haveILetI false in` — exactly as `TateGlobal/WeylShell.lean` and
  `WeylUnramified.lean` already do; do not drop the instance, which would change the signature the
  pin states. Same pass, two proof-only v4.34 deprecations: `Set.mem_setOf_eq` →
  `Set.mem_ofPred_eq` (two sites; the `diff` → `sdiff` family of FR-0016 already covered the rest).
- **seen**: 2026-10-14.

## FR-0021 [checker] — one added `--` prose line flips a declaration's *tracked* namespace (FR-0005, minimal repro)

- **where**: `spec/check_flt_statements.py`, `raw_declarations()` / `namespace_events()`.
- **symptom**: `LanglandsTunnell.TateLocal.higherUnitsAt` was tracked correctly; adding a **single**
  two-line `--` prose comment above it made the same declaration report as
  `NumberField.higherUnitsAt` (the tracker popped both open namespaces early), without any change to
  the namespace or declaration.
- **cause**: `namespace_events()` scans `strip_line_comments(text)` (which **deletes** comment text,
  shortening the string) while `raw_declarations()` matches declarations on `strip_comments(text)`
  (block comments only). Every `--` comment therefore shifts all later `namespace`/`section`/`end`
  events left relative to the declarations, and enough drift re-nests the stack. This is FR-0005's
  mechanism, here reduced to a one-comment repro, and it bites a def whose *dotted* name feeds the
  promoted-from-pin-private lookup (the last-name lookup is unaffected, which is why the headline
  still diffed `IDENTICAL`).
- **fix**: keep prose in `/- … -/` blocks (as FR-0005 already says) — in `WeylSmooth.lean` every
  non-`-- pin:` comment is a block comment, and the tracked name is correct again. Note the
  `-- pin:` comments are exempt in practice only because direct last-name matches carry the diff.
- **seen**: 2026-10-14.

## FR-0022 [lean] [imports] — two pin `Mathlib.Data.*` import paths are deprecated in `v4.34.0` and warn on a verbatim def-layer transcription

- **where**: `AutomorphicForm/Iwasawa/Complex/Basic.lean` (the pin
  `Definitions/Def_AutomorphicForm_ComplexIwasawa.lean` transcribed whole).
- **symptom**: the pin's `import Mathlib.Data.Complex.Basic` and `import Mathlib.Data.Real.Sqrt`
  elaborate but emit `has been deprecated: please replace this import by …` warnings, so a verbatim
  transcription is not warning-free.
- **cause**: the module paths moved (`v4.33.1` → `v4.34.0`): `Mathlib.Data.Complex.Basic` →
  `Mathlib.Basic.Complex.Basic`, `Mathlib.Data.Real.Sqrt` → `Mathlib.Analysis.Real.Sqrt`.
- **fix**: use the new paths (a comment records the pin's spellings); the declarations are unchanged,
  so the checker is unaffected. `Mathlib.LinearAlgebra.Matrix.Notation` did not move.
- **seen**: 2026-10-14; `lean/FLTForHuman/AutomorphicForm/Iwasawa/Complex/Basic.lean`; tier-0 exit 0
  with 0 warnings after the swap.

## FR-0023 [lean] [imports] — a `scoped instance` on a restricted product only elaborates if the *mathlib* module supplying its pointwise instances is imported

- **where**: `NumberTheory/RatIdele/ClassCharNorm.lean`, the pin's
  `private scoped instance : TotallyDisconnectedSpace 𝔸ℚf` (and its `ᵐᵒᵖ`/`ˣ` companions).
- **symptom**: the instance body is pin-verbatim, yet elaboration stops with
  `failed to synthesize instance of type class TotallyDisconnectedSpace ((a : HeightOneSpectrum
  (𝓞 ℚ)) → HeightOneSpectrum.adicCompletion ℚ a)`. `TotallyDisconnectedSpace 𝔸ℚf` needs the Pi
  instance, and the Pi instance needs each place's completion to be totally disconnected; the
  per-place fact in `v4.34.0` comes from `NonarchimedeanAddGroup.instTotallySeparated`, a lemma of
  `Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected`.
- **cause**: the pin reached that mathlib module through `Def_NumberField_TateGlobalZeta`'s import
  cone. The port's homed premise modules (`AdelicHaar/PlaceMeasure`, `AdelicModulus`,
  `TateGlobalContinuousIdeleNorm`, `RatIdele/Normalizer`) are narrower and do not pull it, and the
  instance is *scoped*, so no downstream module was ever forced to import it either. Nothing about
  the statement or the proof is pin-specific here.
- **fix**: `import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected` (one line, no
  statement change; the instance stays pin-verbatim). Diagnose this class of failure with
  `#synth TotallyDisconnectedSpace (v.adicCompletion K)` in a scratch file: if it succeeds after the
  import and fails before it, the problem is the import cone, not the instance.
- **seen**: 2026-10-20; `NumberTheory/RatIdele/ClassCharNorm.lean`; 0 warnings after the import.

## FR-0024 [lean] — `(↑x).1` on an idèle is only type-correct at *default* transparency, so `Function.update_*` rewrites stop matching

- **where**: `NumberTheory/RatIdele/ClassCharNorm.lean`, the pin helper `coe_archCentralUnit_eq`.
- **symptom**: the pin proves it by `Prod.ext`/`funext`, then `rw [Function.update_self]` (resp.
  `Function.update_of_ne`) for the `w = Rat.infinitePlace` (resp. `≠`) branch. In `v4.34.0` both
  `rw`s fail with *"Did not find an occurrence of the pattern `Function.update ?f ?a ?v ?a`"*, and
  the reported goal is not even type-correct: `Application type mismatch: The argument
  ↑(AdelicVolume.archCentralUnit ℚ Rat.infinitePlace b) has type 𝔸ℚ but is expected to have type
  InfiniteAdeleRing ℚ × 𝔸ℚf`.
- **cause**: `AdeleRing R K` is a `def` (`InfiniteAdeleRing K × FiniteAdeleRing R K`), so the
  projection notation `(↑x).1` elaborates by unfolding it at default transparency, while `rw`'s
  matcher re-checks the goal at *implicit* transparency and sees the ill-typed spelling. Nothing is
  wrong with the mathematics; the same proof shape does work in files where the target is a bare
  `Prod`.
- **fix**: use the definitional fact instead of rewriting — the port's `archCentralUnit`'s `val`
  field *is* that `Function.update` pair, so `coe_archCentralUnit_eq` is closed by `rfl` (same
  statement, shorter proof). General prescription: if a pin proof rewrites inside `(↑x).1`/`.2`,
  state the pair equality and discharge it by `rfl`/`Prod.ext` *before* rewriting, rather than
  trying to rewrite the projected goal.
- **seen**: 2026-10-20; `NumberTheory/RatIdele/ClassCharNorm.lean`.

## FR-0025 [lean] [checker] — two `v4.34` linters fire on *pin-verbatim* proof text (`haveI` in a proposition goal, a dead `first` branch)

- **where**: `NumberTheory/RatAdele/DenseRange.lean` (`exists_generator`,
  `valued_algebraMap_adicCompletion`) and `NumberTheory/RatIdele/ClassCharNorm.lean`
  (`ideleNorm_principal`).
- **symptom**: `linter.style.haveILetI` on the pin's `haveI :=
  isPrincipalIdealRing_ringOfIntegers_rat` and on `ideleNorm_principal`'s load-bearing `letI
  MeasurableSpace`/`haveI BorelSpace`; `linter.unusedTactic` + `linter.unreachableTactic` on the
  second arm of the pin's `first | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' i _ |
  (rw [HeightOneSpectrum.algebraMap_adicCompletion]; exact …)`.
- **cause**: these linters post-date the pin (Lean `v4.33.1`). The `haveI`s *must* stay (they are
  the instance environment the pin's proof runs in — `have`/`let` would not register the local
  instance), and the `first`'s first arm already succeeds in `v4.34.0`, so its fallback is dead.
- **fix**: keep the `haveI`/`letI` and switch the style linter off at module level (as
  `NumberTheory/AdelicBox.lean` and `TateGlobal/WeylShell.lean` already do); **delete** the dead
  `first` arm rather than suppress the tactic linters, because here the fallback really is
  unreachable and no statement is involved. Neither choice touches a statement.
- **seen**: 2026-10-20; both modules build with 0 warnings.

## FR-0026 [checker] [pin] — a pin "declaration count" in a work order can exclude the `private scoped instance`s

- **where**: WORKORDER-RN1's `RatIdele.exists_norm_apply_eq_ideleNorm_rpow` line ("312 pin lines,
  45 declarations: 1 headline + private helpers + 4 private instances").
- **symptom**: the pin's `S_RatIdele_exists_norm_apply_eq_ideleNorm_rpow.lean` contributes **49**
  corpus rows (`statements.tsv` 639767–639815), not 45: 45 is the count of `def`/`theorem` rows
  and the four `private scoped instance`s are tallied separately in the same sentence. A verbatim
  port therefore has 49 declarations, and a "declaration count matches the work order" check
  would falsely report drift. (`S_RatAdele_…` is consistent: 309 lines / 21 = 1 + 20.)
- **cause**: the audit's declaration tally drops anonymous `instance`s (they have no last name to
  diff), so the two numbers in one sentence count different things.
- **fix**: when a work order's declaration count is used as a check, compare against
  `spec/statement_db.py`'s row count for the `spec-pin:` files, not against the prose. Recorded in
  `logs/rat-nodes.md` §1.
- **seen**: 2026-10-20.

## FR-0027 [pin] [tooling] — a pin `S_` file's `p2m_export`/`p2m_open` namespace scaffolding does not survive a verbatim copy

- **where**: the six set-B `S_` files (`S_Monoid_CoprodI_isTree_cosetGraph.lean:7,185`,
  `S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean:159,392,823,826,836`, …).
- **symptom**: the files declare their prelude in a *doubled* namespace and patch visibility with
  `p2m_open "Subgroup SimpleGraph P2MW.S_X.SimpleGraph"` / `p2m_export "SimpleGraph" "…"`
  (a `P2M.Util` alias command), so a text copy either fails on `open P2MW.S_X.SimpleGraph`
  (unknown namespace once the `P2MW.S_X` wrapper is stripped) or silently loses names that only
  the alias made visible.
- **cause**: `p2m_open`/`p2m_export` are metaprogramming: they register a namespace without
  checking it exists (`modifyScope`), and they add aliases the parser cannot see.
- **fix**: strip the `P2MW.S_X.` prefix from every `open` line, delete `p2m_export` lines
  (after the wrapper is stripped the exported names already live in the root namespace), and
  replace genuinely missing visibility with an explicit `open` of the real namespace.
- **seen**: 2026-10-20; all six modules then elaborated.

## FR-0028 [checker] [tooling] — the corpus's namespace tracker treats `end A.B` as closing one level, so its names carry a doubled namespace and `port_advise` misses 10 duplicates

- **where**: `tmp/flt-statements/statements.tsv`, rows for
  `S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean`: they read
  `…Kurosh.GroupTheory.GroupTheory.GraphTransversal.WalkConnected`, because the file writes
  `end GroupTheory.BassSerre` (which closes **two** namespaces in Lean).
- **symptom**: `port_advise` reported `WalkConnected`, `IsConnectedTransversal`,
  `walkConnected_singleton`, `insert_of_adj`, `walkConnected_sUnion`, `mem_orbit_symm'`,
  `eq_of_mem_orbit_sUnion`, `eq_of_mem_orbit_insert`, `exists_adj_of_walk`,
  `exists_isConnectedTransversal` only once, and the merged module said "already declared" for
  all ten — the doubles were in the target files but keyed by different (wrong) names.
- **cause**: the tracker pops one frame per `end` regardless of the dotted name; Lean pops one per
  dotted component. The same bug makes the tool's `ConjTrivial` vs `Kurosh.ConjTrivial` row look
  like a `generalise` pair when the file-local names are actually the same.
- **fix**: for dedup, do not trust the corpus's namespace for files containing `end A.B`;
  identify duplicates by statement hash (which is namespace-free) and delete by line span.
  10 declarations, 103 lines, removed by hand.
- **seen**: 2026-10-20; worth fixing in `statement_db.parse_file` (recorded here, not edited —
  `spec/old_check_stmts.py` is frozen for this work order).

## FR-0029 [tooling] — `statements.tsv`'s `end_line` is the statement's end, not the declaration's

- **where**: any `def`/`abbrev` row: `abbrev Vertex : Type _ :=` has `line = end_line`.
- **symptom**: deleting a duplicate declaration by its corpus `line..end_line` removes the header
  and leaves the body, producing "unexpected token `×`; expected command" and "unknown tactic"
  cascades far away from the seam.
- **cause**: `end_line = line + chunk[:cut].count("\n")`, and `cut` stops at the first top-level
  `:=`. For `theorem` rows this is the same line as the body's last line only by accident.
- **fix**: compute the declaration's extent lexically (from the keyword line to the first
  following non-blank line that starts at column 0), and delete exactly that plus the
  `@[…]` lines directly above.
- **seen**: 2026-10-20; the first merge attempt was silently mutilated this way.

## FR-0030 [lean] [mathlib] — v4.34 `open N` is what activates a `scoped instance`; the pin's `p2m_reactivate` has no port spelling

- **where**: `IrrationalPt`'s `scoped instance : CoeOut IrrationalPt ℝ` and the `MulAction SL(2,ℤ)`
  instance in `S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.lean` (pin
  `p2m_reactivate` at 43, 506, 509); the `BassSerre.Vertex` `SMul`/`MulAction` pair (kurosh pin
  207-226).
- **symptom**: `x` of type `IrrationalPt` is "expected to have type ℝ"; `h • v` on a `Vertex`
  fails `synthInstanceFailed` in the *consumer* module.
- **cause**: `scoped instance`s are only active where the namespace is open; `p2m_reactivate`
  re-activates them without a namespace, and nothing in `open scoped` does that (`open N` does —
  verified with a two-line harness).
- **fix**: `open IrrationalPt` right after `end IrrationalPt`; for cross-module consumers
  (`Vertex`) drop `scoped` on the two instances, since the pin's re-activation cannot cross a
  module boundary.
- **seen**: 2026-10-20.

## FR-0031 [mathlib] — four v4.34 module paths / lemma shapes that the `v4.33.1` pin used

- **where**: set B.
- **symptom / fix**:
  - `Mathlib.Combinatorics.SimpleGraph.Connectivity` does not exist: it is a directory now
    (`Connectivity/Connected.lean`); walks are `SimpleGraph/Walk/Basic.lean`.
  - `SpecialLinearGroup.SL2Z_generators` moved to `Mathlib/LinearAlgebra/Matrix/FixedDetMatrices.lean`.
  - `FreeGroup.toWord` / `toWord_eq_nil_iff` need `Mathlib/GroupTheory/FreeGroup/Reduce.lean`
    (not pulled in by `GroupTheory.CoprodI`).
  - `SemidirectProduct` needs `Mathlib/GroupTheory/SemidirectProduct.lean`.
- **cause**: ordinary version drift; the pin imported `Mathlib` wholesale so never named them.
- **seen**: 2026-10-20; each was a one-line import fix.

## FR-0032 [lean] — the pin's `rw [Subtype.mk.injEq, Sym2.eq_iff] at h` no longer rewrites a *dependent* `Subtype` in v4.34

- **where**: `S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean`, `treeRepEquivEdgeSet`
  (`rw [Subtype.mk.injEq, Sym2.eq_iff] at hgg'`).
- **symptom**: `motive is not type correct … g.property has type ↑g ∈ treeRep H hD but is expected
  to have type Vertex.mk 0 ↑g ∈ D ∧ …`; with `beta_reduce` first, the same failure with a
  different motive.
- **cause**: the edge-set elements are `Subtype` of `Sym2`, where the property mentions the
  value; `rw` abstracts the value and the motive stops typechecking. `v4.33`'s `simp`-backed
  `Subtype.mk.injEq` happened to work.
- **fix**: project first — `have hval := congrArg Subtype.val hgg'` then `rw [Sym2.eq_iff] at hval`
  — and keep the rest of the pin's proof (it only ever used `Subtype.val` of the components).
  Proof-only, statement untouched.
- **seen**: 2026-10-20.

## FR-0033 [tooling] [build] — the shared mathlib olean tree is partial: importing an existing mathlib module can fail on a missing `.olean`

- **where**: first compile of the merged engine: `…/SimpleGraph/Connectivity.olean does not exist`.
- **symptom**: `lake env lean file.lean` dies at the first import whose `.olean` is absent, even
  though the `.lean` exists.
- **cause**: the tree is built incrementally for what the port uses; `lake env lean` never builds
  dependencies.
- **fix**: check `.lake/packages/mathlib/.lake/build/lib/lean/<Module>.olean` before naming an
  import, or `lake build` the module (flock'd) and re-check. All eight final modules' imports are
  present and built.
- **seen**: 2026-10-20.
- **the port-side twin, seen 2026-10-27 (SET 4)**: a *port* module can be in the same state, and
  lake hides it — the build log says `Replayed FLTForHuman.…P1.PerfectResidue` while
  `.lake/build/lib/lean/FLTForHuman/…/PerfectResidue.olean` is **absent**, because the replay
  consults the log, not the file. Any `lake env lean` probe of an importing file then dies with
  `object file … does not exist`, which reads like a broken import rather than a missing build.
  Cure: `flock … lake build <that module>` explicitly, then re-probe. A `Replayed` line is not
  evidence that the olean exists.

## FR-0034 [lean] [tooling] — `alias` does not accept a `def`, so deduping a `generalise` definition needs a `private abbrev`

- **where**: deduping `ConjTrivial` (`GroupTheory.FreeDoubleCoset.ConjTrivial` vs the kurosh
  file's `Kurosh.ConjTrivial`, 2 lines each, same body, different binder names).
- **symptom**: `alias ConjT := A.Foo` for a `def` fails to parse ("unexpected identifier; expected
  command"); deleting the second copy and rewriting its references changes the *statement text* of
  five downstream lemmas (`Kurosh.ConjTrivial` → `GroupTheory.FreeDoubleCoset.ConjTrivial`), which
  the checker reports as 6 `MISMATCH` (the corpus hashes the statement text, not the elaborated
  type).
- **cause**: the checker compares statement *text*; a definition's alias is not text-neutral, but a
  `private` declaration is skipped by the checker (`if priv: continue`).
- **fix**: one definition in the home module, and a `private abbrev ConjTrivial … :=
  GroupTheory.FreeDoubleCoset.ConjTrivial A H` in the consumer, so the pin's statement text
  survives while the mathematics lives once. 0 mismatch, and `port_advise`'s
  `card_orbitRelQuotient_mul_card'` row is handled the same way (call the wrapper's headline).
- **seen**: 2026-10-20.

## FR-0035 [checker] [tooling] — the parser moved out of the frozen checker; the `end A.B` fix must count *namespace components*, not frames

- **where**: `spec/old_check_stmts.py` → new `spec/lean_parser.py` (2026-10-20, manager's set).
- **what**: FR-0028's `end A.B` bug is fixed at the root. `ENCLOSE_RE` captures the
  dotted name after `end`, `namespace_events` returns it, and `pop_frames` consumes
  namespace components from the frame stack. `old_check_stmts.py` now *imports* the
  parser (its frozen registry and check behaviour are otherwise unchanged);
  `spec/statement_db.py`, `spec/check_port.py` and `tools/deps/port_advise.py` import
  `lean_parser` directly, so the new toolchain no longer loads the legacy registry
  to parse text.
- **the trap**: the naive "pop one frame per dotted component" over-pops the other
  shape. `namespace I.R … end I.R` **pushes one** dotted frame (two components) and
  must pop one; the naive rule popped the enclosing namespace too, so
  `FLTForHuman/Patching/PatchingConstruction.lean`'s `IsPatchingSystem` lost its
  `PatchingConstruction.` prefix, its `OWN_PROOFS` dotted exemption stopped
  matching, and the legacy full run reported 1 mismatched. `pop_frames` now counts
  components per frame (a `None` section frame counts one), which is right for both
  shapes: `namespace A / namespace B / end A.B` pops two frames, `namespace I.R /
  end I.R` pops one.
- **verification**: `statement_db selftest` 16 assertions and `old_check_stmts
  --selftest` 56 pass; the corpus was rebuilt (parser digest changed) at 718,874
  declarations / 459 MB / 33 s; `check_port --all` reads **3496 ok, 0 mismatch, 0
  missing, 11 own over 129 modules** (identical to before the extraction); the
  legacy full run reads **8866 identical, 0 mismatched, 0 missing, 37 own-proof
  exemptions** (the 37th is the `IsPatchingSystem` exemption restored by the
  corrected pop); `port_advise` now prints the single `GroupTheory.` prefix for the
  Kurosh file and sees the ten graph-transversal duplicates it used to miss.
- **seen**: 2026-10-20.

## FR-0036 [lean] [method] — a drift guess copied into a work order was *inverted*: `push_neg` is the deprecated spelling in v4.34, so the pin's `push Not` transcribes unchanged

- **where**: `WORKORDER-BC1` trap 4 (`AlgebraicCurve/IsCurveOver/BaseChangeCorrespondence.lean`,
  `fibre_centred` and the headline).
- **symptom**: the order told the worker to spell the pin's `push Not at hcon` as
  `push_neg at hcon`. The worker kept the pin's text and reported that `push_neg` is the
  `@[deprecated]` alias in `v4.34.0` (it emits "Prefer using `push Not`"), so the pin's
  spelling is both the literal transcription and the warning-free one.
- **cause**: a drift row written from memory rather than from the tree. A deprecation has a
  *direction*, and a rename that went one way in `v4.31` can be reversed by `v4.34`; a work
  order is not the place to assert it.
- **fix**: the row now lives in the drift table (`topics/TOPIC-mathlib-drift.md`) with the
  direction stated, and the work-order text was corrected in the record. The general rule:
  **a work order states the pin's text and the *gate* (0 warnings), not a guessed
  modernization** — the worker has the mathlib tree and checks the deprecation there.
- **seen**: 2026-10-27.

## FR-0037 [method] [tooling] — a work order's *home* was below the pin declarations the proof needs, so three nodes stopped at the import graph

- **where**: `WORKORDER-BC5` (SET 3, the pointwise dictionary), three of ten nodes.
- **symptom**: the worker stopped and reported, correctly, instead of working around it:
  `Divisor.pushforward_div` needs `Divisor.pushforwardNormFormula` (public only *above*
  `Defs/PushPull.lean`); `Place.exists_integralClosureAt_of_ord_fiber_nonneg` needs the norm
  block and the fibre dictionary (above `Defs/PlacesOverDVR.lean`);
  `exists_poleDivisor_of_transcendental`'s pin proof opens with
  `isCurveOver_of_isAlgClosed_of_transcendental` (above `Defs/PoleDivisorPackage.lean`).
- **cause**: the order homed each node by *subject* ("`integralClosureAt` lives in
  `PlacesOverDVR`") without checking that the module sits above the pin declarations the proof
  consumes. `port_advise` reports the imports of a *node*, not the dependency direction of the
  *module* a home implies; nothing in the tool chain checks a proposed home against the graph.
- **fix**: two new modules above the norm block (`Place/IntegralClosureAtFiber.lean`,
  `PrincipalDivisors/PoleDivisor.lean`) and three lines beside the formula for the third; the
  manager stubs them at the pin's statement spelling and dispatches only the proofs. Check the
  home against `fltdata`'s edges (`d.cites(node)` vs the module's own imports) when writing the
  order — the cost of a wrong home is a full worker round.
- **seen**: 2026-10-27.

## FR-0038 [tooling] [method] — the premise→port-module mapping is statement-anchored, and that misses exactly the premises a *home* decision turns on

- **where**: SET 4's homing pass (`Lean/tmp/set4_homes*.py`), which tried to compute, for each
  ready node, the port modules above all of its pin premises.
- **symptom**: three failure modes, the first of which sent a node to a home that closed an import
  cycle (`Pic0.exists_mk_eq_forall_notMem_support` → `Defs/Divisor.lean`, caught by the worker):
  1. **binder spelling** — a pin wrapper that writes its binders inline has a different statement
     text from its own `S_` file (section variables), and the port transcribes the `S_` copy, so
     the hash lookup misses the premise and the node looks premise-free;
  2. **absent or private premises** — a premise the port does not have yet
     (`SemilinearAut.restrict_smul`) or holds as `private` maps to nothing;
  3. **a cached index** — `twin_scan.build_index` caches, so a run made before a wave landed maps
     against the previous tree and reports "no home above", which is what a *new module* looks
     like.
  Falling back to last-name matching over the wrapper and `S_` files over-corrects: common last
  names (`degree_eq_sum`) then match dozens of modules.
- **fix**: treat the machine table as a first cut and confirm each home against the pin proof's
  actual uses; when the worker's diagnosis and the table disagree, the diagnosis wins. Rebuild the
  index (`rebuild=True`) after every landed wave. The durable fix — a `port_advise` mode that
  answers "which port module may host node X" from the *pin edges* rather than from statement
  identity — is not built.
- **seen**: 2026-10-27.

## FR-0039 [build] [lean] — a wave's own declarations can each fit the low cap while one helper needs 1.6M: the pin's bump was *not* precautionary

- **where**: `IsCurveOver/ConstantFieldExtensionSpan.lean`, the `finrank_le_finrank` helper of the
  348-line `finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin` node (SET 4, BC7).
- **symptom**: the pin wraps the proof in `set_option maxHeartbeats 1600000 in`; dropping it as the
  rule requires (no `set_option maxHeartbeats` in a module) leaves a declaration that elaborates
  under the library's global 4M but not under the 200k edit-loop cap, while every other declaration
  in the wave checks clean at 200k.
- **cause**: not established — either a genuine instance-inference cost (the `Algebra ↥(Algebra.adjoin
  K' {x}) ↥(IntermediateField.adjoin K' {x})` shape that also forced the torsion node to clear
  denominators by hand) or a proof shape that a named intermediate would cheapen. The drift note's
  standing claim — "every pin bump met the low cap once the inference was found" — has this
  exception; record it rather than repeat it as a law.
- **fix**: accepted for now: the module build under the lakefile's 4M is the gate and it passes, and
  no cap is raised in source. The diagnosis is a build-cost pass of its own
  (`build_ladder.py --profile`, [../notes/lean-build-cost.md](../notes/lean-build-cost.md)), with the
  two probes that usually settle it: stub the module's proofs and see whether the floor is the
  *type*, then bisect the one declaration.
- **seen**: 2026-10-27.

## FR-0040 [tooling] [method] — a shelf *read* can carry the leaves block while the *brief* prices only the ready block

- **where**: SET 4's scoping read and its brief (`topics/algebraicCurve/SET-4.md` §0 against the read
  that produced it).
- **symptom**: the read was the canonical one — `frontier.py --ds --ready --include-leaves --rank-by
  silo --top 0` — and it reported `AlgebraicCurve` in two blocks: **14** rows / 4,410 silo in
  `ready_rank` and **24** rows / 2,491 silo in `leaves_rank`. The brief's shelf table says
  "`AlgebraicCurve` rows **14**, their silo lines **4,410**" and names only the fourteen. The
  twenty-four leaf rows were therefore neither cut nor recorded as deferred, and the next scoping
  pass (SET 5) opens on 29 AC rows, of which 24 are that unmentioned block and five are rows
  SET 4's own landing made ready.
- **cause**: the two blocks are separate keys of the same JSON (`ready_rank`, `leaves_rank`), and a
  brief written from the `ready_rank` table alone silently drops the other. TOPIC-scoping-a-ds-set
  §0 warns about the *read* (`--ready` without `--include-leaves`); this is the same loss one step
  later, after the flag is correct.
- **fix**: a brief's shelf table quotes **both** block counts and their silo sums, and every row it
  does not cut is either named or explicitly deferred with a reason. Verify by re-reading the JSON:
  `len(ready_rank.rows) + len(leaves_rank.rows)` for the namespace must equal the row count the
  brief claims.
- **seen**: 2026-10-27; found on the SET 5 read, which diffed the SET 4 shelf against the current
  one and saw 38 → 29 rows with 14 consumed and 5 new.

## FR-0041 [method] [tooling] — a row's engine can be a port theorem with a *more general* statement, and then `port_advise` prices the whole row as new

- **where**: SET 5's pricing of `AlgebraicCurve.Place.exists_ord_mul_eq_order_of_hasRamBound` (340
  silo, 23 declarations; `port_advise` reports 0 in-port lines, 318 net new).
- **symptom**: the row is priced as a from-scratch construction. It *is* one — but the port's
  `Place.exists_of_orderMap` (`Place/ValueDictionary.lean:1013`) already realises **any**
  `WithTop ℤ`-valued order map (multiplicative, nonarchimedean, trivial on constants, nontrivial)
  as `e` times a place's order. The pin's row is the `WithTop ℚ` + common-denominator `d` version
  (its `ramScale`/`HasRamBound`), i.e. `exists_of_orderMap` at `d = 1`.
- **cause**: `port_advise`'s substitution and drags tiers are statement-anchored (hash / shape
  after binder normalisation). A port theorem with *weaker hypotheses* than the pin's is not a
  shape match, so it is invisible — and it is exactly the theorem that decides whether a row is a
  transcription or a generalisation.
- **fix**: before accepting an order's "net new" figure, read the pin proof's first lines for a
  named engine and grep the port for the *idea*, not the name (`exists_of_orderMap`,
  `exists_forall_ord_eq`, `regularDiffs_eq_span` were all found this way in this pass). When the
  port's engine is the special case, decide the route explicitly — transcribe now, or generalise
  the engine and derive both — and record the call in the brief, because the two routes have
  different owners (worker vs manager).
- **seen**: 2026-10-27.

## FR-0042 [mathlib] [build] — a `Subfield` of `HahnSeries` does not elaborate without `HahnSeries/Summable`: the `Field` instance lives there, and the pin's `import Mathlib` hid it

- **where**: SET 5's `Defs/HahnSeriesRamificationBound.lean`, transcribing
  `Definitions/Def_HahnSeries_RamificationBound.lean` (which is `import Mathlib` only).
- **symptom**: with the obvious specific imports (`HahnSeries.Basic`, `HahnSeries.Multiplication`)
  the file fails with `failed to synthesize instance of type class DivisionRing K⟦ℚ⟧` at
  `RingHom.fieldRange`, and a knock-on `Application type mismatch` one line below, because
  `puiseuxRamSubfield : Subfield (HahnSeries ℚ K)` needs the codomain to be a division ring.
- **cause**: mathlib v4.34's `instance instField : Field R⟦Γ⟧` is in
  `Mathlib/RingTheory/HahnSeries/Summable.lean` (it is proved with `SummableFamily.powers`), not
  beside `order_mul` in `Multiplication.lean`. A pin file with `import Mathlib` never states this
  dependency, and grep for `HahnSeries.*Field` in `Multiplication.lean` finds nothing.
- **fix**: add `import Mathlib.RingTheory.HahnSeries.Summable` to any module that needs a ring
  structure on Hahn series (the `Field`/`DivisionRing`/`Subfield` family). Grep the *instance*
  name (`instField`, `instDivisionRing`) when a structure instance is missing rather than the
  structure's own name.
- **seen**: 2026-10-27.

## FR-0043 [tooling] — `move_dead.py --source` reports `0 declarations, 0 lines` on a module with 50

- **where**: SET 5's review of `AlgebraicCurve/RegularProlongationFinrank.lean` (51 declarations,
  1,586 lines after the wave); the docstring's invocation is
  `python3 move_dead.py --source lean/FLTForHuman/…/A.lean --target lean/Reserve/…/Dead.lean`.
- **symptom**: from the project root with `lean/`-prefixed paths, and from `lean/` with
  `FLTForHuman/`-prefixed paths, the same file gives `RegularProlongationFinrank.lean:
  0 declarations, 0 lines` and `live private helpers needed: 0` — a silent "nothing to move".
- **cause**: not diagnosed. Either the path resolution inside the tool wants a module name rather
  than a path, or its declaration scanner rejects this file's shape (the module opens with a
  `/- … -/` block whose `spec-pin:` lines are at column 0, then `namespace`s and `section`s).
  `dedup.py --module … --within` on the same module works and reports the expected single
  pre-existing cluster, so the module itself is fine.
- **fix**: do not read the `0 declarations` line as "clean". Cross-check with
  `dedup.py --module <module> --within` (it reports the clusters) and, until the scanner is fixed,
  treat `move_dead` as unavailable for modules of this shape.
- **seen**: 2026-10-27.

## FR-0044 [tooling] [method] — under `--ds`, `--ready` cannot see a premise that sits in the pruned set: a row reads ready while an unported, avoided premise is missing

- **where**: the SET 6 scoping read (`frontier.py --ds --ready --include-leaves --rank-by silo`,
  `needed` 1,040 / 410,470; 96 ready rows). Four of the 96 ready rows cite a direct premise that
  lies in the D–S prunable set and is **not** in the port: the two `AlgebraicCurve` rows
  `Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` (126 silo; its
  `Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice` 193 and
  `exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice` 871) and
  `Pic0.finite_torsion_of_isAlgClosed_of_charZero` (95; its
  `Pic0.natCard_torsion_prime_eq_pow_genus_complex` 61, which `ds_prunable.EXTRA` lists), plus
  `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` (327) and
  `ModularCurve.moduleFinite_padicInt_tateModule_jOne` (283). Together 4 rows / 831 silo. The
  leaves block is clean (0 of 296).
- **symptom**: each of those rows is printed with `premises_unported = 0` and `needed = 1`, i.e.
  as a row every premise of which is ported — the opposite of the truth. The recipe's §1 gloss,
  "`premises_unported` (zero by definition in a ready set)", is exactly the trap: zero by the
  definition the tool implements, not by the pin's demand.
- **cause**: `frontier.py` computes `need` with the avoided set removed
  (`needed(cites, target, ported=ported, avoided=avoided, …)`, `masks`/`counts` keyed by that
  `need`), and `premises_unported = premise_counts(cites, counts, exclude=ported)`
  (`frontier.py:842-845`) counts only premises that are *keys* of `counts`. An avoided premise is
  not a key, so it is silently dropped from both the readiness test and the premise count. The
  row is needed by the D–S target through a path that does not traverse R, so it stays on the
  shelf; its own proof, however, does traverse R.
- **fix**: audit the rows you intend to cut, not just the shelf. For each row take the pin `S_`
  file's `import Theorems.Thm_*` lines and test every premise for (i) membership of the frontier
  (the port) and (ii) membership of `ds_prunable`'s patterns/`EXTRA`; a premise that is in R and
  not in the port is a blocker the report cannot show. Two lines of `prune`/`frontier` API do it
  (`fr.frontier()`, `pay.cites(pay.pid(node))`). A row with such a premise is the prunable
  subject's work (the RR column's phase 3), not D–S work, however ready it looks; defer it and
  say so in the brief (recipe §0's rule for naming every row a set does not cut).
- **seen**: 2026-10-27; found on the SET 6 read, on the four rows above.
- **fixed (2026-10-27)**: `frontier.py --ready` now guards on a new
  `pruned_premise_counts` (`premises_pruned` per JSON row): a candidate whose own proof
  directly cites an unported premise in `R` is withheld from `ready_rank`, and the ready
  block carries a `withheld` list naming each row and the blocking premises; the text report
  prints them under the shelf. `--selftest` gained the synthetic case (3 avoided, `needed`
  cuts `1 -> 3`, both consumers read `needed == 1`; the guard empties the shelf). Re-read of
  the SET 6 tree: **90 -> 86 ready**, the four rows above now in `withheld` with exactly
  their recorded premises (`abelJacobiCard_genus` ×2, the two `abelJacobiDiv` engines,
  `natCard_torsion_prime_eq_pow_genus_complex`). The recipe and the tool README record the
  new reading. **Correction to this entry's symptom/cause**: `premises_unported` was *not*
  zero for those rows — the field counted the avoided direct premise (2 / 1 / 1 / 1 on the
  four), because `premise_counts`'s `universe` only selects the output keys and its
  `exclude` is the frontier, not `R`. The failure was that nothing used the column: the
  readiness test alone decided the shelf, and the text report does not print it. The fix
  therefore had to add the R-aware count rather than repair an existing one.

## FR-0045 [lean] [mathlib] — `Algebra K (HahnSeries Γ K)` has two instances, and which one an `F →ₐ[K] LaurentSeries K` elaborates with depends on the import order

- **where**: SET 6's TL2 order, the Laurent block appended to
  `AlgebraicCurve/Place/LaurentSeriesModel.lean` (the `exists_ord_mul_eq_order_of_algHom_laurentSeries`
  row); met again by the reviewer when writing `spec/AlgebraicCurveSet6Consumer.lean`.
- **symptom**: the `AlgHom` type of `ι : F →ₐ[K] LaurentSeries K` is printed with
  `HahnSeries.powerSeriesAlgebra ℤ K` in one file and with `HahnSeries.instAlgebra` in another, and
  a term of one does not typecheck against a theorem stating the other:
  `Application type mismatch: … has type @AlgHom K F (LaurentSeries K) … (HahnSeries.powerSeriesAlgebra ℤ K)
  but is expected to have type … HahnSeries.instAlgebra`. The `∃ x, (ι x).order ≠ 0` hypothesis
  then fails to elaborate against the theorem's `ι`, so the failure surfaces as a *metavariable*
  in the application (`… K ?m.48 ?m.49`), not as an instance error — easy to misread as a binder
  problem.
- **cause**: mathlib installs both `HahnSeries.instAlgebra` (through `HahnSeries.C`) and
  `HahnSeries.powerSeriesAlgebra` (through `HahnSeries.ofPowerSeries`, for `Γ = ℤ`) on
  `HahnSeries Γ K`; instance priority is equal, so the choice is the local instance set, which the
  import closure and the file's own `open`/`variable` order change. `Place/ValueDictionary.lean`
  (the `exists_ord_mul_eq_order_of_hasRamBound` hub) is stored with `HahnSeries.instAlgebra`.
- **fix**: pin the intended one locally in any file that composes with that hub —
  `attribute [local instance 2000] HahnSeries.instAlgebra` (the attribute is `local`, so it does
  not leak: verified with an importing probe) — and state the `C`-lemmas through
  `HahnSeries.C_eq_algebraMap` rather than the S_ file's `algebraMap_apply'` +
  `PowerSeries.algebraMap_apply`. If the two instances ever diverge in an unavoidable way, the
  honest cure is a port-level `abbrev`/`local notation` fixing the algebra structure, not a
  restatement of the theorem in the other instance.
- **seen**: 2026-10-27, SET 6 (TL2 and the review).

## FR-0046 [build] [method] — concurrent workers sharing one tree invalidate each other's oleans; `lake env lean` then fails with "object file … does not exist" in modules the worker did not edit

- **where**: SET 6's four-order wave (WR, TS, CR, TL2 dispatched in parallel on one tree).
- **symptom**: three of the four workers hit, at least twice each, `object file
  '…/.lake/build/lib/lean/FLTForHuman/…/X.olean' does not exist` (or a stale-olean elaboration
  error) for modules *they had not edited* — `Place/DegreeOne`, `P1/Dictionary`, `P1/DXCoeff`,
  `Tate/Agreement`, `LocalResidue/Instance`, `IsCovreOver/ConstantFieldExtensionSpan`,
  `ResidueTheorem/KFamily` — and one worker's `lake build` was killed by its own 110 s cap while
  rebuilding another order's dependency closure.
- **cause**: `lake build` rewrites the `.olean` files of the edited module *and of every module it
  rebuilds*, and `lake env lean <file>` elaborates against `oleans` without taking the build lock.
  So worker A's elaboration can read the tree while worker B's build is between removing and
  rewriting an olean, and the *edits* are file-disjoint only at the source level: the `.olean`
  layer is one shared, mutable interface.
- **fix**: (i) each worker elaborates its own file with `lake env lean` and only then takes the
  build lock; (ii) appends are made to compile *before* moving to the next file, so the tree is
  never left with a broken source that another worker's build would rebuild; (iii) a foreign
  "object file does not exist" is retried once after ~60 s, never treated as a failure of the
  order — and reported, because it is a scheduling signal; (iv) `flock -w 45` rather than a bare
  `flock` when several builds are queued, so the lock wait is visible as a wait and not as a
  module timeout. If a wave needs the dependency closure rebuilt first (as SET 6's manager lane
  did after editing `P1/Dictionary.lean`), run that one build before dispatch and say so.
- **seen**: 2026-10-27, SET 6.

## FR-0047 [method] [tooling] — a landed row whose last name another pin node shares makes that node read "ported", and the shelf under-reports (and mis-reports) what the set made ready

- **where**: SET 6's landing. Its ℙ¹ capstone is `AlgebraicCurve.RationalFunctionField.weilReciprocity`
  (`P1/Dictionary.lean`); the pin also has `AlgebraicCurve.weilReciprocity`
  (`Theorems/Thm_AlgebraicCurve_weilReciprocity.lean`), the **general function-field** reciprocity
  — a different statement, same last name.
- **symptom**: after the landing the re-read (`frontier.py --ds --ready --include-leaves`) reports
  `needed` falling by 14 nodes / 3,937 lines where the set consumed 12 rows / 3,779 lines; the
  shelf shows six new ready rows, one of which (`DivisorialWeilPairingData.toHom_injective_of_divisible`,
  496 silo) is built on the *general* `weilReciprocity` that is not ported; and
  `weilReciprocity_algebraMap` (58 silo), which has **no** unported premise, does not appear at
  all. `frontier.py`'s `ported` set is the set of **last-name components** of port declarations
  (`scan_port_decls`: `m.group("name").rsplit(".", 1)[-1]`), so the capstone's name satisfies the
  general node.
- **cause**: the same name-anchored reading that FR-0041 records in the *pricing* tools applies to
  the *readiness* test, which is what the recipe's §0/§7 numbers come from. It bites hardest after
  a landing, when the new declarations enter the port and start shadowing.
- **fix**: after a landing, do not take the three numbers from the instrument alone. Diff the shelf
  (rows that left, rows that entered) and, for every **vanished** row and every **entered** row,
  check the premise list against the frontier *and* against the pin's qualified name: a row that
  vanished because a same-last-name sibling landed is still needed; a row that entered on such a
  premise is spurious. Two lines of `pay.cites` per row. Report both the instrument's and the
  corrected figures (SET-6.md §8 does). A qualified-name-first tier in `Frontier.frontier` would
  fix it at the source, but it changes readiness everywhere and needs its own validation pass;
  until then, the correction is a scoping-time audit, not a tool change to be smuggled in.
- **seen**: 2026-10-27, SET 6's landing.

## FR-0048 [build] [method] — a pre-existing declaration in an edited module times out at the 200k edit-loop cap, so the cap cannot gate that module

- **where**: SET 7's manager lane, `AlgebraicCurve/IsCurveOver/ConstantFieldExtensionSpan.lean`.
  The edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` aborts
  at `private theorem finrank_le_finrank` (the `ConstantFieldAdjoin` block, unchanged by the
  set) with `(deterministic) timeout at whnf, maximum number of heartbeats (200000) has been
  reached`; a later `#print` in the same file then reports a kernel `unknown constant` for the
  aborted declaration.  The module builds at the project's lakefile cap (`maxHeartbeats`
  4,000,000) in ~21 s.
- **not a regression**: the same abort reproduces on the file as it stands at `HEAD` (checked
  by typechecking `git show HEAD:…` from a `tmp/` copy): the declaration was already over 200k
  before SET 7, and the set's edits are all earlier in the file.
- **cause**: not diagnosed.  The declaration is the instance-heavy `finrank_le_finrank` of the
  `ConstantFieldAdjoin` engine, which the port's later `finrankAlong` rows use; it is not one
  of SET 7's rows.  The low cap is the instance-inference detector, and here it has found a
  pre-existing instance cost that the project cap has been hiding.
- **fix (for the set)**: use the module build at the lakefile cap as the gate for this module,
  and record that its 200k silence is not a claim the set can make; the edit loop still gates
  every declaration *before* the offender (SET 7's additions are all before it and pass).  The
  real fix is the §3.5 probe ladder on `finrank_le_finrank` (statement/proof stub, then
  `trace.Meta.synthInstance` at a tiny cap); do not raise the cap and do not attribute the cost
  to the set's edits.
- **seen**: 2026-10-27, SET 7's landing gate.

## FR-0049 [tooling] [method] — readiness is premise-based, so a row whose *statement* needs an unported structure reads ready

- **where**: SET 8's scoping read, the row
  `AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible` (496).  It is the
  FR-0047 shadow's consumer: after the general `weilReciprocity` (100) lands it becomes a graph
  premise-complete row.  Adding the set's four rows and the 100 to `ported` in an API read
  (`frontier.analyze` on the corrected baseline) puts the 496 on the ready shelf with
  `needed = 1`, `premises_unported = 0`, while the port declares **no**
  `DivisorialWeilPairingData` structure at all — only that `Def_` module's support block, homed
  in `AlgebraicCurve/Defs/WeilDatum.lean`.  The row's statement is
  `(e : DivisorialWeilPairingData K F n) : Function.Injective e.toHom`, so it cannot be written.
- **symptom**: `frontier.py --ready` will carry a row that is not portable; `--selfcheck` is
  silent, `twin_scan --node` says `new` (it hashes the statement, which mentions the missing
  structure but does not resolve it), and `port_advise` prices it as new lines (496) as if the
  vocabulary existed.
- **cause**: readiness is computed over the **graph premises** of the row's `S_` file only.  A
  statement's own type dependencies come from the `Definitions/Def_*.lean` modules the
  *wrapper* imports, which are module-level and not graph nodes (`fltdata.py`'s graph is the
  theorem graph; the README's "Definition dependencies are module-level" note).  `needed` never
  reads the statement.  This is the statement-side analogue of FR-0041's pricing blind spot and
  of FR-0047's name shadow, and the third mechanism producing a *false ready* (FR-0044 was the
  prune-set one).
- **fix (scoping time)**: before believing `needed = 1` on a row whose statement names a
  structure or class, read the wrapper's `import Definitions.…` lines and check each against the
  port's wired `Def_` modules; `spec/statement_db.py show <name>` gives the statement text.
  For the 496 the gate is the carrier block of
  `Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial`: the structure, `toChar`, `toHom`,
  `toHom_apply_apply` and the two pairing laws those consume (`pair_zero_right`,
  `pair_add_right`) — ≈250 lines, the definition gate of SET 9, not SET 8.
- **fix (tool, next ask)**: a statement-vocabulary check in `--ready` (resolve each candidate
  wrapper's `Definitions/` imports through the port's `defs` wire) would close it; it needs its
  own validation pass like FR-0047's qualified-name tier, so it is recorded, not smuggled in.
  What *was* implemented while preparing SET 8 is the marker correction: `frontier.py
  --unport NAME` (repeatable, SET 7's call 7) removes a false ported marker from `F`, so the
  corrected shelf of a brief is now a command instead of an API script; the default read is
  untouched and the selftest covers the subtraction.
- **seen**: 2026-10-27, SET 8's scoping read (computed after-read; the row is not on the current
  shelf, it is one row behind the 100).

## FR-0050 [checker] [method] — a pin hypothesis unused in its proof cannot be renamed to `_h`, because the statement hash keeps binder names

- **where**: SET 8's SPAN row,
  `AlgebraicCurve.lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed`
  (`IsCurveOver/ConstantFieldExtensionSpan.lean`).  The pin wrapper carries `hlift_new` (the
  "new places" hypothesis), and the pin's own proof never uses it — it is there for the row's
  consumer, the `ell_mapDomain_eq_…` (151) node.
- **symptom**: at the project cap the module is green but warns
  `Variable name hlift_new is not explicitly referenced`, so the set's zero-warning gate fails.
  The obvious fix — rename the binder to `_hlift_new` — makes `check_port` report a **MISMATCH**
  on the row, with the two signatures textually identical except for the underscore.
- **cause**: `check_port`'s `norm` (`spec/lean_parser.py`) strips namespace qualifiers and
  `kw*` labels but **not binder names**, so a declaration is matched to the pin by its statement
  text, and a renamed hypothesis is a different statement.  (The exact-last-name tier does not
  save it: the name tier is hash-gated and falls through to a mismatch.)
- **fix**: keep the pin's binder name and reference it with the tree's idiom for carried
  hypotheses — `have _ := hlift_new` at the top of the proof (used elsewhere in
  `ConstantReductionCorrespondence`, `RadicalRegion/Engine/Reparam`), with a one-line comment
  saying it is carried for the consumer.  Do **not** rename binders to silence the linter unless
  the pin's own name is free to change; `own:` markers are for whole declarations, not binders.
- **seen**: 2026-10-27, SET 8's landing.

## FR-0051 [instrument] [read] — the shelf's *corrected* `needed` figure does not reproduce, and the delta is the shadow node itself

- **where**: `lean/topics/modularCurve/TOPIC-ready-shelf.md` §0/§7, the corrected read's
  `needed [F terminal]` = 1,020 / 404,926.  Reproduced 2026-10-27 for SET MC-7.
- **symptom**: the documented three-`--unport` command
  (`…_exists_sum_smul_eq_of_isIntegralQExp_gamma1`, `…_exists_basis_gamma1_qCoeff_mem_range_ratCast`,
  `AlgebraicCurve.weilReciprocity`) on the same tree gives **1,021 / 405,187**, and so does the
  two-`--unport` form once MD-001's wire is closed.  Restoring the MD-001 wire and rerunning
  reproduces the same 1,021 / 405,187, so the tree is not the cause.
- **cause**: the 261-line `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` node is in
  `F` through the `CuspForm` twin's last name, so `--unport` on it adds 261 lines to `needed`.
  The shelf's figure counts that addition as already made; it was not.
- **fix**: quote the read produced by the command actually run, and say which markers it used.
  SET MC-7 §0.1 records both readings; every other shelf line (ready 86, leaves 296 / 72,205,
  MC 25 / 8,668, MC demand 185 / 81,780, frontier 1,387 / 721,245) reproduces exactly, so only
  the `needed` line was mis-quoted.  A corrected read's delta must be measured on the same
  marker set (the recipe's own warning, now with a case).
- **seen**: 2026-10-27, SET MC-7's scoping read.

## FR-0052 [audit] [definitions] — a priced definition gate can be already landed under an H2 name, and the audit cannot see it

- **where**: `TOPIC-ready-shelf.md` §0.2 prices `CuspForm_Gamma1HeckeOperators` as
  "4 missing declarations / 32 lines" and SET MC-7's gate as 295 + 32 = 327.
- **symptom**: all four are present and public in the port —
  `ModularForm.HeckeGamma1.mdifferentiable_heckeU` (`ModularForms/HeckeAnalytic.lean`),
  `ModularForm.HeckeRepresentatives.mapGL_apply`, `ModularForm.Level.isUnit_wt`,
  `ModularForm.Level.det_mod` — the H2 reconciliation
  (`Gamma1HeckeOperators.lean`'s header names the phase).  `isUnit_wt` is *weaker* than the pin's
  (drops `hp : p.Prime`), which is also why the statement-anchored audit cannot recover it.
- **cause**: the audit compares the pin `Def_` module's declarations against the port *module*
  (`ModularForms/Defs/Gamma1HeckeOperators.lean`), not against the port tree; a declaration
  reconciled into another namespace/module reads as missing.
- **fix**: before pricing a definition gate, `grep -rn "theorem <last name>"` over the tree and
  `twin_scan --node` the pin declaration — as SET MC-7 did for the four.  A gate that is already
  landed under an H2 name is not a gate; the four are recorded in the brief's §0.2 table.
- **seen**: 2026-10-27, SET MC-7's definition audit.

## FR-0053 [surface] [engine] — a private engine written for one file's own use is not promotable: its binders are the *port's*, not the pin's

- **where**: `ModularCurve/X1/QExpRegularProlongation.lean` (47 `private` declarations — the
  `Lam`/`homSpan`/`IsFrac`/`resF` engine), whose pin block is byte-identical to the 953 row's
  `S_` lines 131–786 (`diff` = 0).
- **symptom**: the recipe's surface gate (drop `private`, `check_port --force`) gives
  **13 ok / 37 mismatch**.  Every one of the 37 is `gaussRing A Γ` (port) against
  `gaussRing A hT` (pin): `hT : ModularGroup.T ∈ Γ` is an *unused explicit parameter of the
  definition* in the pin, so the term differs while the mathematics does not.
- **cause**: the block was ported for the module's own proofs (stated for an arbitrary `Γ`, per
  the `QExpDeuring` engine it reuses), not as a public transcription of the pin's text.
- **fix**: keep it private, and let the consumer module that *needs the pin's shape* carry a thin
  facade at the pin's binders over the public `Γ`-shaped engine (`def gaussRing (hT) :=
  QExpDeuring.gaussRing A Γ`, …).  That is SET MC-7's MC-7a order; the facade turns a 953-line
  row into ≈150 lines of new proof plus delegations.  Do not "promote" by rewriting the engine's
  binders in a landed hub.
- **seen**: 2026-10-27, SET MC-7's engine audit.

## FR-0054 [style] [linter] — the three suppressions a worker reaches for are all fixable, and one of them hid a redundant case

- **where**: SET MC-7's three row modules and the definition wave (`X1/DiamondCorrespondence.lean`,
  `X1/HeckeCorrespondence.lean`, `X1/GaussResidue.lean`, `ConstantReductionQExp.lean`,
  `AlgebraicCurve/Differential/AutTrace.lean`, `Defs/QExpReductionModL.lean`).
- **symptom**: every module came back "silent" with a `set_option linter.style.haveILetI false` (or
  `linter.deprecated`) in it, plus the port's habitual `unusedSectionVars`/`unusedVariables`
  suppressions.  Removing them exposes **3 + 10 + 1 = 14** warnings, not hundreds.
- **the fixes** (all mechanical, no statement touched):
  * `haveI := h` → `have := h` when the binding's class is `Prop`-valued: Lean 4 *does* use a local
    hypothesis of class type for instance search, so the ten `haveI := finiteDimensional_beta …`,
    `haveI : Algebra.IsSeparable …`, `haveI : NeZero …` in `HeckeCorrespondence` become `have` and
    the file is warning-free (same for three in `DiamondCorrespondence`, one in
    `ConstantReductionQExp`).
  * `TensorProduct.induction_on` (deprecated) → `inductionOn`: the deprecated eliminator's `zero`
    case is **redundant**, because `inductionOn` derives `motive 0` from `tmul 0 0` (its own
    proof does `simpa using! tmul 0 0`).  So the pin's `| zero => …` branch can go and the module
    needs no `set_option linter.deprecated`.
  * an `unusedSectionVars` warning on a single `private` theorem (GaussResidue's
    `exists_primitive_of_mem_homSpan`, unused `[Algebra ℚ L]`) → the linter's own `omit [… ] in`,
    safe because the declaration is private and called only in its own file.  **Never** `omit` on a
    public declaration to silence this: `omit` changes the auto-bound signature, so it is only
    consumer-safe when it removes a requirement nobody supplies *or* when the declaration is
    private (the rule used here); on a public declaration, prefer keeping the variable and
    referencing it (FR-0050's idiom).
- **seen**: 2026-10-27, SET MC-7's review.  Net effect: none of the set's six modules carries a
  linter or heartbeat option except the port-wide `linter.unusedVariables`-free state — i.e. zero.

## FR-0055 [tree] [promotion] — a stale `private` copy of a promoted lemma breaks the build the moment its olean is invalidated

- **where**: `FLTForHuman/WeierstrassCurve/Velu/RestrictAlong.lean` (committed, untouched by SET
  MC-1) carried `private theorem count_normalizedFactors_span_singleton` and
  `private theorem ord_norm_eq_sum_fiberOver`; the public promoted copies live in
  `AlgebraicCurve/PrincipalDivisors/Transcendence.lean:200/323` (SET 3/4's promotions), which is in
  `RestrictAlong`'s import closure.
- **symptom**: on this toolchain a **private** declaration whose name collides with an imported
  non-private one is rejected (`a non-private declaration … has already been declared`), so the
  module fails to elaborate — but only once its `.olean` is rebuilt.  The stale olean hid the
  defect until a concurrent wave's rebuild cascade deleted it, and then every consumer of
  `RestrictAlong.olean` (MC-1a's module among them) died at import time with
  `object file … does not exist`.  Two gates looked like worker failures and were not.
- **the fix applied and resolved as is** (2026-10-27): the two local copies are renamed
  `…_restrict` with their two call sites, and the module header records the *decision*.  Deleting
  them was tried first and is **not** the end state: the file then fails at the
  `Place.ord_norm_eq_sum_fiberOver v hf` call site, because the public promoted form is stated
  under `omit [CharZero F]` and the local one is not — the two are *not* interchangeable as drop-in
  replacements, so the deletion needs the call sites adapted (an instance-synthesis fix), not a
  mechanical one.  So the copies stay under the suffix — a decided exception, not an open issue.
- **rule for the next wave**: when a set promotes a lemma, **the promoting set decides the private
  copies in the same touch** — delete-and-adapt if the statements are interchangeable, rename-and-
  record if they are not (as here).  Either way the decision is made at promotion time: a
  `spec-pin`-wired module carrying an un-decided private duplicate is a time bomb keyed on olean
  invalidation, and it goes off in whichever later wave rebuilds it.
- **seen**: 2026-10-27, SET MC-1a's gates (blocked for ~20 minutes; unblocked by the rename).

## FR-0056 [checker] — a statement whose *type* carries an instance binding is diffed only up to that `:=`

- **where**: `spec/statement_db.py`'s statement parse (via `lean_parser.top_level_cut`), met on
  `CuspForm.coe_heckeTLinH_apply` / `coe_heckeTLinH_eq` in `ModularForms/Defs/GammaH.lean`, whose
  types state `haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩` before the conclusion.
- **symptom**: both come back `ok`, and would have come back `ok` even if the rest of the statement
  had drifted: the normaliser cuts the statement at the first top-level `:=`, and for these two
  declarations that `:=` is inside the *type* (it is the `haveI`'s value), not the proof's start.
  So only the binder prefix is hashed, and the `gammaLift`/`heckeDiagMatrix` part of the type is
  outside the comparison.
- **cause**: `top_level_cut` is a text heuristic for "where the statement ends and the proof
  begins"; a `haveI … := …` in the type is a `:=` at column 0's nesting level, so it wins.
- **fix**: none applied — the declarations are transcribed from the pin and the *left* part is
  checked. The rule for the reviewer: a row whose statement carries a `haveI`/`letI` binding in its
  type is **under-checked**, so read it against the pin by eye (MC-4's D1 declarations were read
  that way). Teaching the checker to skip `haveI`/`letI`/`let` binders before the cut changes the
  global checked surface, so it is its own pass with `--selftest`, not a rider on a set.
- **seen**: 2026-10-27, the MC definition wave (D1).

## FR-0057 [checker] — an `inductive` declaration is invisible to the statement parser

- **where**: `spec/lean_parser.py`'s `DECL_RE`, met on `CohCarrier.Gen`
  (`ModularForms/CohCarrier/Inst.lean`), the generator type of the `X_H`/`X₁` Hecke operators.
- **symptom**: the module reports 5 checked declarations for 6 public ones, and `Gen` never appears
  in a `check_port` row — neither the pin corpus nor the port parse indexes it, so a transpcription
  error in its constructors (`T`/`U`/`dia`, their binders and hypotheses) would not be caught.
- **cause**: `DECL_RE` admits `def|theorem|lemma|abbrev|structure|class|instance` only. The same
  gap is recorded in `../CARRY-FORWARD.md` for `scoped instance`; `inductive` is the second
  declaration kind it hides, and it is not a corner: `CohCarrier.Gen` is the *type* of
  `genOpH`/`opFamily`, i.e. part of two rows' statements.
- **fix**: none applied. Widen the regex and rebuild the corpus is a checker pass of its own (every
  corpus hash changes); record the gap and read the inductive by eye against the pin (here: the
  three constructors and their binder shapes are the pin's, verified line by line).
- **seen**: 2026-10-27, the MC definition wave (D4).

## FR-0058 [checker] — a verbatim pin statement reads as `MISMATCH` when the port homes its names in another namespace

- **where**: `ModularForms/Defs/GammaH.lean`, the `CuspForm` operators block (D1 of the MC
  definition wave). The pin writes `gammaLift M d` in `coe_diamondLinH_apply`'s type; this port
  homes `gammaLift` (with `unitOfPrimeNotDvd`, `StableD`/`StableU`/`StableT` and the
  `slash_mapGL_eq_of_gamma0Units_eq` prelude) in `CohCarrier`, for the good reason that the pin
  spreads the same prelude across four `Def_` modules and re-inlines it into every consumer.
- **symptom**: writing the faithful statement `⇑f ∣[k] (mapGL ℝ (CohCarrier.gammaLift M d) …)` gets
  `MISMATCH (direct name)`, and the diff is exactly the qualifier — the mathematics is identical.
- **cause**: the checker compares statement *text* after normalisation. It resolves nothing, so a
  namespace qualification is a spelling difference, and the only sanctioned spellings are the
  marker table's (`own:`), which would stop diffing a declaration that *is* the pin's.
- **fix applied**: a section-scoped `open CohCarrier` in the operators section, so the statement is
  written with the pin's unqualified text and diffed normally (`42 ok / 0 mismatch`). The rule:
  when the port's home for a pin name differs from the pin's namespace, `open` the home in the
  section that transcribes the pin's statements — do not qualify, and do not spend an `own:` row on
  a namespace. (An `own:` row stays right for a genuinely different home *object*, e.g. a restated
  `Inputs` bundle.)
- **seen**: 2026-10-27, the MC definition wave (D1); found by the worker's first `check_port` run.

## FR-0059 [homes] [import] — a pin `Def_` module holding both an engine and its consumer becomes a cycle when the port splits it

- **where**: MC-4d, the 27-line `ModularCurve.heckeOperatorHAlong_diamondHBar_comm`
  (`topics/modularCurve/SET-MC4.md` §2.1). The pin keeps `diamondHBar`/`genOpH` **and**
  `exists_algEquiv_intertwinesAlong_diamondAutHBar` in one `Definitions/Def_ModularCurve_XH.lean`, so
  the pin never faces the question of which is below which. The port split them into
  `XH/Operators.lean` (the operator vocabulary, the def wave's D3) and `XH/DiamondLift.lean` (the
  lift, SET-H-B) — and `XH/DiamondLift.lean` **imports** `XH/Operators.lean`.
- **symptom**: the row's proof needs `exists_algEquiv_intertwinesAlong_diamondAutHBar` (only in
  `XH/DiamondLift`, nowhere else in the port) *and* `diamondHBar`/`diamondHBar_apply` (only in
  `XH/Operators`). The brief had picked `XH/Operators` as the home by subject; that is the cycle
  `Operators → DiamondLift → Operators`. The worker caught it before writing a line; the shelf's
  acyclicity table (a first cut, recipe §4) had the edge backwards.
- **cause**: "the home is the module of the subject" is necessary but not sufficient. Where the pin
  had one module and the port has two, the home of a row that consumes *both* is the one that
  imports the other — the subject does not decide it, the import graph does.
- **fix applied**: the row lands in `XH/DiamondLift.lean` (which imports `Operators`), the analogue
  of MC-4e's X₁ row in `X1/DiamondLift.lean`; that module was migrated off `PORT_FILES` by the
  manager in the same wave (16 ok / 0 / 0 before the row, 17 after). The no-facade rule forbids the
  other route (re-declaring pin-shaped `diamondHBar` in the lift module).
- **rule for the next brief**: when the pin's `Def_` module is split, the row's home is the
  *highest* of the split modules, not the one whose name matches the subject; check the edge
  direction with `grep '^import'` on both candidates before writing the order.
- **seen**: 2026-10-27, SET MC-4d (caught in the worker's first pass, before any Lean was written).

## FR-0060 [tooling] [build] — `lake build` under `flock` is killed by the executor's cap while merely queueing

- **where**: every worker order of the MC-4 wave that builds one module under
  `flock /tmp/lean-build.lock lake build …`; hit by MC-4d (and MC-4a/4c report the same shape).
- **symptom**: a foreground `flock … lake build <module>` dies with no Lean output — no error, no
  `Replayed`, just a kill — when another wave's build holds the lock: the command spends its whole
  executor budget (60 s in the workers' harness) *waiting for the lock*, and the build itself never
  starts.
- **cause**: `flock` blocks before `lake` runs, so the wall time is queueing + build; with four
  waves building concurrently the queue alone can exceed the per-call cap.
- **fix applied**: run the build as a background job (`run_in_background: true`) and collect it, or
  keep the `flock` but give the call a longer `timeoutMs`. Both were used; the same command that was
  killed at 60 s finished in 27.5 s once it got the lock.
- **rule for the next wave**: on a busy tree, a module build belongs in the background channel; a
  foreground `flock`+`lake build` is only safe when the lock is known free. The `lake env lean`
  probe (no olean write) is the cheap foreground gate.
- **seen**: 2026-10-27, SET MC-4's worker orders.

## FR-0061 [lean] [linter] — `haveI`/`letI` in a `Prop` goal: `have`/`let` register the instance, so no suppression is needed

- **where**: every MC-5/MC-6 order (MC-5b's `NeZero`/`Fact`, MC-5c's 7 sites, MC-6b's
  `finiteDimensional_alpha`, MC-6a's `haveI := hKfin`); met as `linter.style.haveILetI`, which is
  default-on in v4.34 and fires whenever `haveI`/`letI` binds a *proposition* (every typeclass that
  is `Prop`-valued, e.g. `Module.Finite`, `FiniteIndex`, `NeZero`, `Fact`).
- **symptom**: the pin's literal `haveI : NeZero N := …` warns, and a worker may not add the
  linter option (the wave's gate forbids suppressions).
- **cause / fact**: in Lean 4 `have x : T := v` and `let x : T := v` **do** register a local
  instance when `T` is a class, exactly as `haveI`/`letI` do — the difference is only the linter's
  opinion. So the unsuppressed spelling is `have`/`let`, or, where a term is wanted, the term-mode
  `exact haveI : T := v` (MC-4c used that; it does not trip the linter because it is not the tactic).
- **consequence for the port**: where an older module carries `set_option linter.style.haveILetI
  false` (`X1/DiamondLift.lean`, `XH/DiamondLift.lean`, the three MC-7-era modules), that option is
  now **redundant** for new code — do not extend it to new declarations, and delete it when the
  module is next touched for another reason. The three older modules are left as they are
  (grandfathered) so their checked surface does not move in a wave that is not theirs.
- **seen**: 2026-10-27, SET MC-5 and MC-6.

## FR-0062 [mathlib] [build] — `Mathlib.Tactic.Omega` does not exist in v4.34.0, and an unbuilt mathlib module fails the edit loop outright

- **where**: MC-5c's imports; and generally any new module whose proof uses `omega`.
- **symptom**: `import Mathlib.Tactic.Omega` fails — there is no such module in mathlib v4.34.0.
  `omega` now rides on `Mathlib.Tactic.Order` (`public meta import Lean.Elab.Tactic.Omega` inside
  it). Separately, because the port's mathlib is only *partially* built (164 oleans under
  `Mathlib/Tactic/` at the time of writing), importing an unbuilt mathlib module fails the edit loop
  with `object file … does not exist` instead of rebuilding it.
- **fix**: import `Mathlib.Tactic.Order` (or the umbrella `Mathlib`); and when the "object file"
  error names a mathlib module, build that module explicitly under `flock`
  (`lake build Mathlib.<path>`) before re-running the edit loop — the same cure as FR-0033 for port
  modules, one level down.
- **seen**: 2026-10-27, SET MC-5c; the same "partially built mathlib" cost MC-6a two dependency
  rebuilds (`HeckeFrickeTrace`, `QExpansionCoeff`).

## FR-0063 [lean] [definitions] — projecting `opAlgHom`/`toMLₒ` off a `hdata`-built `HeckeData` exceeds 200k heartbeats, while the construction is cheap

- **where**: `spec/ModularCurveLeavesDefConsumer.lean`'s first draft (the leaves' definition wave,
  SET-LEAVESDEF), on `CohCarrier.HeckeData` (`ModularForms/CohCarrier/HeckeData.lean`, the pin's
  `Def_CohCarrier_HeckeData.lean`) applied to `V = CohCarrier.H1 M H 𝒪`.
- **symptom**: `example (θbar) : CohCarrier.HeckeData 𝒪 (CohCarrier.H1 M H 𝒪) k :=
  CohCarrier.hdata M H S 𝒪 k hcomm θbar` elaborates in a few seconds, but the moment a statement
  *projects* a field off a `hdata`-defined datum —
  `(D hcomm θbar).opAlgHom (MvPolynomial.X g) = (D hcomm θbar).op g`, even with `D` a `noncomputable
  def` rather than an inline literal — elaboration spins in `whnf`/`isDefEq` past 200k heartbeats
  (the spec file ran >4 minutes at the 4M cap before being killed; the culprit is the `FreeAlg`
  field: `MvPolynomial D.Gen 𝒪` has to be unfolded through the structure literal *and* the `Gen`/`opFamily`
  arguments).
- **cause**: `D.Gen`/`D.FreeAlg` are structure *fields*, so any statement mentioning `D.FreeAlg`
  reduces `D` to its construction; `hdata`'s construction mentions `opFamily M H S 𝒪`, whose
  `Module.End 𝒪 (H1 M H 𝒪)` type is a large function type, and the definitional unfolding is not
  cached across the two sides of the equation.
- **fix applied**: the consumer states the `HeckeData` API over an **abstract** datum
  (`variable (D : CohCarrier.HeckeData 𝒪 (H1 M H 𝒪) k)`) — projections on a variable are cheap — and
  keeps the `hdata` construction as its own `example`. The same rule applies to the leaves' `pair_*`
  rows: bind the datum once and work with its lemmas, or pass the fields (`D.op`, `D.Gen`) as
  explicit arguments; do not write `(hdata …).<field>` inside a statement.
- **seen**: 2026-10-27, the leaves' definition wave (the consumer zone cost ~5 minutes before the
  restructure; 7 s after).

## FR-0064 [mathlib] [lean] — `if_pos`/`if_neg` are deprecated in v4.34; the replacements are `ite_eq_left`/`ite_eq_right`

- **where**: the leaves' row wave (SET-LEAVES), LV-2's `StarBank.deltaNorm`/`closure` and LV-3's
  `StarBank.starK`/`count`; six proof sites in total.
- **symptom**: `rw [if_pos h]` is a deprecation warning, which fails the zero-warning gate.
- **fix**: `ite_eq_left`/`ite_eq_right` (same statement, the `dite`/`ite` lemma family's v4.34
  spelling). Proof-neutral.
- **seen**: 2026-10-27, SET-LEAVES wave A.

## FR-0065 [lean] [build] — `linter.style.haveILetI` fires on `haveI : NeZero M` / `letI : TopologicalSpace K := ⊥` in proofs of `Prop`s

- **where**: LV-1's `BernoulliWeight.lean` (three sites) and LV-2's `etaNorm_powerSeries` (one site).
- **symptom**: the style linter reports "the `haveI`/`letI` binding is used only for its instance"
  and the zero-warning gate fails. The bindings are *load-bearing* (`NeZero`/`Fact` instances the
  goal needs, `DiscreteTopology` for a `tprod`).
- **fix**: write them as `have`/`let` instead — Lean 4 registers the instance from a `have`/`let`
  of an instance type exactly as it does from `haveI`/`letI`, so the proof is unchanged and the
  linter is silent. Do not add a suppression.
- **seen**: 2026-10-27, SET-LEAVES wave A.

## FR-0066 [mathlib] [lean] — `LinearMap.restrict_apply`, `convert … using 1`, `Nat.choose_symm` and `HahnSeries.algebraMap_apply'` all drifted under the pin

- **where**: four independent sites in SET-LEAVES wave A: LV-1's `TE_surjective`/`mem_span_iff_even`
  and `hasSum_cos_wt`; LV-3's `count` and `starK`.
- **symptom** (each its own): (i) `LinearMap.restrict_apply` is restated at the subtype
  (`(f.restrict hf) x = ⟨f ↑x, ⋯⟩`), so the pin's `simp only [TE, LinearMap.restrict_apply]` is an
  *unused simp argument*; (ii) `convert h using 1` now discharges the function side and leaves one
  goal, so the pin's following `· rfl` bullet hits "no goals"; (iii) `Nat.choose_symm` is
  `n.choose (n - k) = n.choose k` in v4.34, the opposite orientation to the pin's use — the port
  needed `Nat.choose_symm_of_eq_add` for `p.choose (p - 1) = p`; (iv)
  `HahnSeries.algebraMap_apply'` carries an explicit `Γ` binder, so it must be applied as
  `… ℤ` rather than positionally.
- **fix**: (i) a defeq `congrArg Subtype.val`; (ii) hoist the arithmetic `have` above the
  `convert`; (iii)–(iv) the v4.34 spellings above. All four are proof-neutral.
- **seen**: 2026-10-27, SET-LEAVES wave A.

## FR-0067 [mathlib] [lean] [build] — four more v4.34 drift sites, and a pin cap of 3.2M heartbeats that the port does not need

- **where**: SET-LEAVES LV-4 (`ModularPolynomialCoset.lean`, `JqCoefficients.lean`).
- **symptom/fix** (each proof-only, statements verbatim): (i) `Finset.prod_le_prod` no longer
  discharges the nonneg side itself — v4.34 has `Finset.prod_le_prod₀` which takes the nonneg
  hypothesis at ℝ; (ii) `AdjoinRoot.Minpoly.toAdjoin` / `coe_toAdjoin_mk_X` moved under the
  `AdjoinRoot` namespace; (iii) `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right` (the same
  spelling change FR-0064 records for `ite`); (iv) `Polynomial.natDegree_prod_of_monic` keeps its
  three explicit arguments, so the pin's implicit application fails.
- **cap**: the pin's `S_ModularCurve_hasSum_coeff_etaProd_pow` carries
  `set_option maxHeartbeats 3200000` around the domination/convergence engine; the whole
  `EtaQSeries` engine (`tendsto_tsum_of_dominated_convergence`, the `Maj` majorant, the `Cong`
  congruence layer) elaborates at the port's **200,000** edit-loop cap. Do not copy such a cap
  before measuring: this is the third pin cap (with 504's 800,000 and `c4_tateLaurent`'s
  `synthInstance` 400,000) that the port has not needed.
- **seen**: 2026-10-27, SET-LEAVES wave B.

## FR-0068 [mathlib] [lean] — on `LaurentSeries`, `SMul` now resolves to the pointwise `HahnSeries` instance, so `Algebra.toSMul` proofs fail on byte-identical goals

- **where**: SET-LEAVES LV-5 (`X1/CoeffMap.lean`, rows 314/468) and LV-6 (the `Pic0` transport).
- **symptom**: goals that print identically (`c • ↑y = c • ↑y`) fail `rw`/`rfl`; every
  `IntermediateField` coercion lemma and `Algebra.smul_def` speaks `Algebra.toSMul`, while the
  default search picks `HahnSeries.instSMul`.
- **fix**: transcribe the pin's own `attribute [local instance 2000] Algebra.toSMul Algebra.toModule`
  at the top of the module section. It is a *local* attribute, not a `set_option` and not one of the
  forbidden `attribute [-simp]` lines; the pin carried it for exactly this reason. A second, related
  one: `Module.rank_lt_aleph0_iff` now demands a `Module.Free` instance that is not synthesized at
  the 20,000 default — supply `Module.Free.of_divisionRing` explicitly instead of the pin's
  `synthInstance.maxHeartbeats 1600000`.
- **seen**: 2026-10-27, SET-LEAVES wave B.

## FR-0069 [checker] [tooling] — a shape-tier "already in the port" match across carriers is not an import

- **where**: SET-LEAVES LV-6's pricing: `port_advise` credited 345 in-port lines to the rows of
  `ModularCurve.diamondOneBar_comm` (468) and `pic0Congr_jOne_jH_bot_compat` (536), matching pin
  declarations to `X1/DiamondCorrespondence.lean`/`AtkinLehnerExchange.lean` lemmas.
- **symptom**: the worker found only ~6 of the 468 engine's 22 declarations and ~1/3 of 536's
  `ES1Sol` engine in the port; the rest were new (~700 lines). The shape tier had matched, e.g.,
  the pin's `mem_intFormRatiosC_of_mem` (over `intFormRatiosC`) to the port's `mem_Sb_of_mem` (a
  different carrier's spelling).
- **rule**: read the two statements before accepting a shape-tier row on a *large* declaration, and
  do not price a leaf row's engine as a free prelude when the engine is a *sibling node*'s — a leaf
  that re-proves its sibling's engine is new work. The aggregate budget (dedup + boilerplate
  allowances) can absorb the gap, so the miss is invisible in the total and visible only per order.
- **seen**: 2026-10-27, SET-LEAVES LV-6.

## FR-0070 [tooling] — `move_dead.py` reads only proof bodies, so an `abbrev` used in a *type* and a token used by an `example` both look dead

- **where**: SET-LEAVES' close: `Pic0Correspondence.lean` reported 2 dead declarations (`Γ1`,
  `coeffEmb_algebraMap`) and `StarBank/Hasse.lean` 1 (`Kbar2`).
- **symptom**: `Γ1` is an `abbrev` used in the *types* of a dozen declarations (`ModularForm (Γ1 M) k`,
  `γ ∈ Gamma0 M` side conditions) and by `slashForm`'s signature; `Kbar2` is used by the module's two
  `example` probes, which are not declarations. The dry-run's shelf contains them, so `--apply`
  would have broken both modules.
- **rule**: never `--apply` move_dead on a report you have not read; grep the flagged names for
  *type-level* uses (a `def`/`abbrev`'s name in a binder type) and for `example` bodies before
  cutting. `grep -c <name>` over the module is the cheap test — the tool counts only bodies.
- **seen**: 2026-10-27, SET-LEAVES close; no declaration was cut.

## FR-0071 [tooling] — the name tier counts a *private* transcription as ported, so a public pin node can hide behind its own private twin

- **where**: `ModularCurve.qExpansion_E6_eq_map_mk` (`X1/IntegralityJqNModC.lean:97`, `private`,
  inside `namespace EisensteinCube`) and `AlgebraicCurve.Divisor.pushforwardNormFormula_of_finiteDimensional`
  (`AlgebraicCurve/PrincipalDivisors/Transcendence.lean:359`, `private`, with a `spec-pin:` of its own
  at line 43).
- **symptom**: both nodes are public in the pin (each has a `Thm_`/`S_` pair) and both are read
  *ported* by `frontier.py`'s name tier, which scans private port declarations by design
  (`Frontier.tiers()`'s documented limit). Neither is importable, so a shelf row citing one can be
  read ready and cannot be transcribed. `--port-public-only` shows the second exactly: the 650-line
  `AlgebraicCurve` row appears on the ready shelf, where the instrument had it ported.
  In the MC family the cost is two rows / 541 silo of the successor shelf; in `AlgebraicCurve` it is
  650 silo of hidden demand.
- **rule**: treat `twin_scan --node <premise>` → `twin-private` as a **manager item**, not as a
  ported premise: promote the statement (public, at the pin's name, out of any inner namespace, its
  own wire) or, if it is genuinely a local spelling, keep it private and stop claiming it. `--unport
  <name>` is the local instrument that prices the gap (the shelf drops the rows that lean on it);
  `--port-public-only` is the global one and is *not* a drop-in corrected read (it also changes the
  frontier tier, so its `needed`/`frontier` deltas are not comparable with the instrument's).
- **seen**: 2026-10-28, the `ModularCurve` successor-shelf scoping
  ([../topics/modularCurve/TOPIC-ready-shelf-1.md](../topics/modularCurve/TOPIC-ready-shelf-1.md) §0.2);
  the promotion and the 650-line instance are both open.

## FR-0072 [tooling] [build] — the playbook's `/tmp` build lock is a no-op under the harness, and a foreground `timeout 90` never fires

- **where**: the four concurrent worker agents of the `ModularCurve` wave 1 (MS-1, MS-2, MS-3, the
  manager-lane MSDEF), each following the playbook's build discipline
  (`flock /tmp/lean-build.lock timeout 90 lake build <module>`).
- **symptom**: `/tmp` is **not** shared between tool calls — every `bash` call runs in its own
  namespace with a fresh `--tmpfs /tmp` (verified: write a file in one call, it is absent in the
  next). Three consequences: (i) the lock file is recreated per call, so `flock
  /tmp/lean-build.lock` *serializes nothing* between agents and the tree has no build lock at all;
  (ii) a background build's log in `/tmp` is gone by the time it is read, so the log must live in
  the (persistent, git-ignored) repo `tmp/`; (iii) the harness kills a foreground call at 60 s, so
  a `timeout 90` never fires — the effective cap is the harness's, and any build that can plausibly
  exceed it must be a background job.
- **effect measured**: MS-2's first build replayed and rebuilt its whole 4,505-job dependency
  closure (`X1/HeckeCommute` and others read as stale) because two other agents were writing and
  building in the same tree at the same moment. Nothing was corrupted, but the wave paid a full
  cascade it had budgeted as a per-module build (`Build completed successfully (4505 jobs)`,
  the module's own compile 7.6 s).
- **rule**: put the lock where the *workspace* is, not in `/tmp` — `flock tmp/lean-build.lock
  timeout 90 lake build <module>` (or `--timeout`-less: launch it as a background job and read
  `tmp/<order>/build.log`); treat 60 s, not the `timeout` value, as the foreground budget; and when
  several agents share a tree, serialize the *first* build of each (the cold closure), not only the
  module's own.
- **seen**: 2026-10-28, the `ModularCurve` ready shelf 1 wave 1
  ([../topics/modularCurve/TOPIC-ready-shelf-1.md](../topics/modularCurve/TOPIC-ready-shelf-1.md) §1.1).

## FR-0073 [tooling] — `move_dead.py`'s tokeniser drops non-ASCII identifiers, so `Δ_smul` reads dead

- **where**: `ModularCurve/TateSlots/Invariants.lean` (MS-3's U9 insertion), the declaration
  `ModularCurve.JMultiplicity.Δ_smul`.
- **symptom**: `move_dead.py --select dead --dry-run` reports
  `Invariants.lean: 1 declarations, 6 lines` naming `Δ_smul`, which is in fact cited twice (at the
  module's lines 980 and 1244). The tokeniser's identifier class does not cover `Δ` (and by the
  same mechanism `Γ`, `ζ`, `μ`, `Φ`-named declarations), so every token of a `Δ`-named declaration
  reads as absent from the bodies that use it.
- **rule**: never `--apply` a `move_dead` report on a module whose declarations use non-ASCII names
  without grepping each flagged name (`grep -c 'Δ_smul'` is the cheap test); the tool reports
  *token* occurrences, and a name outside `[A-Za-z0-9_']` is invisible to it. This is the second
  class of false positive in the same tool (FR-0070 is the `abbrev`-in-a-type one).
- **seen**: 2026-10-28, MS-3 of the `ModularCurve` ready shelf 1 wave 1.

## FR-0074 [lean] [build] — a pin `maxHeartbeats` cap localised to one 20-line transport; the fix is a `RingEquiv` detour, not a bigger cap

- **where**: `ModularCurve/X1/FunctionFieldIndex.lean` (MS-6 of ready shelf 1), declaration
  `transfer_finrank`; the pin's `P2M/Sol/S_…_qExpFunctionFieldC_le_index.lean` carries
  `maxHeartbeats 6400000` + `synthInstance.maxHeartbeats 1600000` on exactly this declaration.
- **symptom**: the module is correct and builds (checker 3 ok, axioms clean, zero warnings at 250k),
  but the port's 200k **edit-loop** discipline is not met: ≈240k are needed (0 errors at 240k/250k,
  fails at 230k/200k). `sorry`-cut probes put the whole overrun in the final ~20 lines —
  `let e₂ : N₁ ≃+* Fk := RingEquiv.refl Fk`, the `hcomm` coherence, and
  `Module.Finite.of_equiv_equiv` / `Algebra.finrank_eq_of_equiv_equiv` — not in the 250-line body
  (which fits 200k in 9 s).
- **diagnosis**: the instance trace (taken in a `tmp/` probe, never in the module) shows recurring
  base-change searches over `IntermediateField` subtypes: `Module ↥K₁ ↥S` ≈3,300 lines ×5,
  `Module ↥K₁ ↥(N₁.toSubalgebra)` ≈3,700, `Algebra k ↥K₀` ≈1,100 ×3, and a *failing*
  `Nonempty (Fin n)` search ≈2,900. Local `haveI` bricks give a real 2.5× speed-up but change the
  instance *identity*, and the kernel's defeq check then rejects `Module.Finite.span_of_finite` and
  `hcomm`'s `change`.
- **rule**: when a pin cap localises to a short transport block, the cure is to remove the transport
  (`RingEquiv.refl` + `of_equiv_equiv` where the two carriers are definitionally the same
  `IntermediateField`), not to add instances and not to copy the cap. Next move for this one:
  prove `FiniteDimensional K₀ Fk ∧ finrank K₀ Fk ≤ n` from `hrankN` by `IntermediateField`-level
  rewriting (`N₁` and `Fk` share their carrier; `K₀.map val = K₁`).
- **seen**: 2026-10-28, MS-6 of ready shelf 1; recorded as the order's one unmet gate in
  [../topics/modularCurve/SET-MS6.md](../topics/modularCurve/SET-MS6.md) §2.

## FR-0075 [tooling] — `port_advise`'s shape tier skips *instance* binders, so a 103-line theorem prices as "already in the port"

- **where**: `tools/deps/port_advise.py`, `shape_of` (the `[` case at `port_advise.py:543`);
  met scoping `AlgebraicCurve.Place.isRational_of_isAlgClosed`
  ([../topics/algebraicCurve/SET-9.md](../topics/algebraicCurve/SET-9.md) §0.3).
- **symptom**: `port_plan` reports `already in the port (vetted) 103 → NET NEW 644` for a four-row
  set whose row is a 119-line pin file with one 103-line `solution`. The claimed substitute is
  `AlgebraicCurve.Place.isRational_of_isCurveOver` (`Place/OrdCalculus.lean:110`, 5 lines), whose
  hypothesis is `[IsCurveOver K F]`; the pin node has no such hypothesis (it has
  `[Algebra (RatFunc K) F] [IsScalarTower] [FiniteDimensional]` and no characteristic bound), so it
  is neither a substitute nor a rebuild base.
- **cause**: `shape_of` builds the key from the *explicit* hypothesis list and **drops every `[...]`
  binder**, so two theorems that differ only in their instance hypotheses have the same shape. This
  is the exact inverse of FR-0041: there a port theorem with *weaker* hypotheses was invisible to
  the shape tier; here a port theorem with *stronger* ones masks the pin node.
- **fix**: do not believe `port_plan`'s `already in the port` column for a row whose hypotheses are
  instance binders — read the pin statement against the claimed port copy (`port_advise` prints the
  claim's `-> module`, so it is one `grep`). A row priced at 0 net with a `prem` count and a
  `twin_scan` `relative` verdict is the tell: both mean "read the two statements".
- **seen**: 2026-10-31, scoping SET 9 of the `AlgebraicCurve` column
  (`python3 port_advise.py --nodes AlgebraicCurve.Place.isRational_of_isAlgClosed`, then
  `port_plan.py --json`). The same row is also the second live FR-0047 name shadow
  (`AlgebraicCurve.RationalFunctionField.isRational_of_isAlgClosed`, ported, ℙ¹-only): the graph's
  last-name tier reads the general node ported, `--selfcheck` cannot see it, and the row was on no
  shelf and in no brief until this pass.

## FR-0076 [checker] — a pin declaration with an explicit universe suffix (`…divisible.{u, v}`) is unindexable, so the row needs a marker

- **where**: `spec/lean_parser.py`'s `DECL_RE` (name class `[\w.'ₐ]+`), consumed by
  `spec/statement_db.py`'s `parse_file`; met porting
  `AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible` in SET 9
  ([../topics/algebraicCurve/SET-9.md](../topics/algebraicCurve/SET-9.md) §1.1).
- **symptom**: `check_port` reports the row `MISSING` with the hint "identical statement at
  `S_…_toHom_injective_of_divisible.lean:484`" — the text *is* in the wire, but no tier finds it.
- **cause**: the pin's wrapper spells the declaration `…toHom_injective_of_divisible.{u, v}`. The
  name regex eats the `.` before `{` and stops, so the parsed name is `…divisible.` and its *last
  name* (everything after the final dot) is the empty string. `Wire` skips rows with an empty last
  name, so the pin's own `Thm_`/`S_` rows are invisible to the name tiers, to the stage/part-label
  tiers and to `by_hash`. Any pin declaration with an explicit universe suffix behaves this way.
- **workaround**: a marker row. The marker's **key must be the port declaration's parsed name,
  trailing dot included** — `AlgebraicCurve.…toHom_injective_of_divisible.` — otherwise it is
  reported as a *stale marker* and the row stays `MISSING` (the first attempt keyed it without the
  dot; that is the tell).
- **fix** (not done: it invalidates the 472 MB statement corpus, which is keyed by these names):
  strip a trailing `.` from the written name in `parse_file` and rebuild the corpus; then such rows
  index normally and the marker disappears.
- **seen**: 2026-10-31, SET 9's PAIR row; `git grep -n '\.\{u, v\}' P2M/Sol` shows the family is
  small but not empty.

## FR-0077 [checker] — the `.{u, v}` row: the `pin:` marker and the frontier disagree, so the port drops the suffix and takes an `own:`

- **where**: `FLTForHuman/AlgebraicCurve/Pic0/DivisorialPairing.lean`, the headline
  `DivisorialWeilPairingData.toHom_injective_of_divisible`; supersedes FR-0076's *workaround* (its
  diagnosis stands).  Met reviewing SET 9
  ([../topics/algebraicCurve/SET-9.md](../topics/algebraicCurve/SET-9.md) §1.2).
- **symptom**: two green instruments do not compose.  With the pin's spelling
  `…toHom_injective_of_divisible.{u, v}` on the port declaration, `check_port` is `1 ok` through a
  `pin:` marker, but `frontier.py --selfcheck` **FAILS** (`source node not covered by the name
  scan`) — the frontier's own name scan reads `…divisible.`, so the node is in `F` only through its
  `Thm_` source row.  Dropping the suffix (universes from `universe u v`) makes `--selfcheck` PASS
  and the name tier see it, but then `check_port` reports `MISSING`, and a `pin:` marker gives
  `MISMATCH`: the pin's stored *statement text* begins `theorem …divisible.{u, v}`, so a clean
  statement cannot hash to it.
- **rule**: prefer the reading the *shelf* depends on — drop the explicit universe suffix and take
  one `own:` row whose reason says the statement was hand-diffed and why no tier can see it.  A
  `--selfcheck` FAIL is worse than one undiffed statement: it is a standing lie about `F`, and every
  later `needed` figure is quoted next to it.  Re-run **both** instruments after a landing that
  touches a declaration's name.
- **fix** for the tool (not done; it invalidates the statement corpus): strip the trailing `.` (and
  the `{...}` suffix) from a parsed name and from the statement text, then rebuild the corpus.
- **seen**: 2026-10-31, SET 9's PAIR row, the review after the worker's order.

## FR-0078 [tooling] — `port_advise`'s shape tier does not lift the *pin* side's section variables, so a port copy with explicit binders is invisible

- **where**: `tools/deps/port_advise.py`, `shape_of` (the `SECTION_DECL` drop at `:545`); met scoping
  ready shelf 2 of the `ModularCurve` column
  ([../topics/modularCurve/TOPIC-ready-shelf-2.md](../topics/modularCurve/TOPIC-ready-shelf-2.md) §3.1).
- **symptom**: for the pin row
  `ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC`
  (171 lines), `port_advise` reports *none — every target declaration is new to the port* and
  `port_plan` prices it at **148 net (0 already in the port)**, although the port holds the row's
  own engine `ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq` (`X1/CoeffMap.lean:250`) at the
  same statement, plus `BCEqProof.image_intFormRatiosC` (`:219`), `BCEqProof.coeffEmb_mem_adjoin`
  (`:235`), `coeffEmb_injective` (`Defs/Laurent.lean:367`) and the three `coeffEmb_*` variants. The
  row is an assembly of ≈60–80 net, not 148.
- **cause**: the pin declaration states its binders as file-level `variable`s
  (`variable (K : Type*) [Field K] [Algebra ℚ K]`, `variable (Γ)`), so
  `statement_db.parse_file`'s statement text begins at the colon —
  `: laurentBaseChange K (qExpFunctionFieldC ℚ Γ) = qExpFunctionFieldC K Γ` — and `K`/`Γ` occur
  **free**. `shape_of` builds its hypothesis list from the parsed binder block only; a free
  section variable is never bound, so the pin's shape has hypotheses `[]` and its conclusion
  mentions `K`, where the port's inline-binder copy has hypotheses `["Γ : Subgroup SL(2,ℤ)"]` and
  mentions `L`. The docstring's normalisation covers "a section variable written *into* the binder
  block" (the port side); it does not lift the pin side's free variables into one. The byte tier
  fails the same way: it compares the raw statement texts, and the pin's has no binder block.
- **rule**: for a row whose pin `S_` file writes its binders under `variable`, do not accept the
  substitute section, the dedup count or the net figure unread — open the pin proof's first lines,
  find the named engine, and look for it in the port by *name* (the port's copies usually carry the
  same name in a different namespace). Here the hand read is what prices the set (§3.1).
- **fix** (not done): in `shape_of`, bind every free variable of the statement after the
  alpha-renaming, on both sides, and compare; the same lift makes the byte tier comparable. The cost
  is a rebuild of the pin shape cache (`build/pin-shapes.tsv.gz`); the port side needs no corpus
  change.
- **seen**: 2026-10-31, scoping ready shelf 2 of the `ModularCurve` column.

## FR-0079 [lean] [port] — the `LaurentSeries` algebra diamond makes two port premises incomposable; the fix is a ring-hom statement, not an `AlgHom` transport

- **where**: `FLTForHuman/ModularCurve/LevelN/FieldGalois.lean`'s `exists_algHom_laurentSeries_qExpansion`
  (producer) versus `FLTForHuman/AlgebraicCurve/Place/LaurentSeriesModel.lean`'s
  `Place.exists_ord_mul_eq_order_of_algHom_laurentSeries` (consumer); met porting the
  `ModularCurve` row `LevelN.exists_place_ord_jGen_le_two_three_level`
  ([../topics/modularCurve/TOPIC-ready-shelf-2.md](../topics/modularCurve/TOPIC-ready-shelf-2.md) §5.7,
  [../topics/modularCurve/WORKORDER-RS2-ready-shelf2.md](../topics/modularCurve/WORKORDER-RS2-ready-shelf2.md) §2).
- **symptom**: the producer's `E : K →ₐ[ℂ] LaurentSeries ℂ` is elaborated at
  `HahnSeries.powerSeriesAlgebra`; the consumer's `ι` is at `HahnSeries.instAlgebra`
  (`LaurentSeriesModel` pins it with `attribute [local instance 2000]`). `E` therefore cannot be
  passed: every spelling of the transport (`AlgHom.mk`, `{toRingHom := … with …}`, an explicit
  `@AlgHom … instAlgebra` ascription, a `local instance` pin) dies on *synthesized type class
  instance is not definitionally equal to expression inferred by typing rules*.
- **cause**: `Algebra K (HahnSeries Γ K)` is a Mathlib diamond — both `HahnSeries.instAlgebra`
  (constants via `C`) and `HahnSeries.powerSeriesAlgebra` (through `PowerSeries`) apply, and
  resolution picks by import order / local priority. The port now has three spellings in
  circulation (`X1/CoeffMap.lean`'s `Algebra.toSMul`/`toModule` pin, FR-0068;
  `LaurentSeriesModel`'s `instAlgebra` pin; the `FieldGalois`/`QExpBridge` default), so an `AlgHom`
  crossing two modules is only well typed when the two chose the same one. Pinning a spelling
  file-wide does not fix a composition, it moves the breakage: `FieldGalois` with the
  `instAlgebra` pin flips `QExpBridge`'s mixed spellings, and a consumer's pin breaks its uses of
  `E` (both were tried and reverted).
- **rule**: do not transport an `AlgHom` across the two spellings, and do not pin either one
  file-wide to make a composition typecheck. State the consumer for a **ring hom**
  `f : F →+* LaurentSeries K` plus the constants identity `∀ c, f (algebraMap K F c) =
  HahnSeries.C c` — that statement mentions no `LaurentSeries`-side algebra instance — and pin the
  `HahnSeries ℚ`-side instance (`instAlgebra`, which the ram-bound dictionary uses) inside that
  glue module. Landed as
  `FLTForHuman/AlgebraicCurve/Place/LaurentSeriesRingHom.lean`,
  `AlgebraicCurve.Place.exists_ord_mul_eq_order_of_ringHom` (`own:`, 1 own / 0 / 0, build green in
  2.1 s, silent).
- **seen**: 2026-10-31, RS2 order D: the worker's first attempt (the whole prelude compiled, only
  the cusp dictionary step failed, nine transports tried) and the manager's bridge.

## FR-0080 [lean] — four v4.34 deprecation renames in the pin's `main` block: `if_neg`/`if_pos`/`tendsto_finset_prod`

- **where**: `FLTForHuman/ModularCurve/SiegelUnit/Integrality.lean`'s appended `SExpPi` block,
  transcribed from `P2M/Sol/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow.lean`
  (`main`, the pin's ≈200 lines); met porting the MC row
  `SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow`
  ([../topics/modularCurve/TOPIC-ready-shelf-2.md](../topics/modularCurve/TOPIC-ready-shelf-2.md) §12,
  [../topics/modularCurve/WORKORDER-RS2-ready-shelf2.md](../topics/modularCurve/WORKORDER-RS2-ready-shelf2.md) §3).
- **symptom**: the pin's proof rewrites with four names that are deprecated in the port's mathlib
  (`v4.34.0`): `if_neg` → `ite_eq_right`, `if_pos` → `ite_eq_left`, `tendsto_finset_prod` →
  `tendsto_finsetProd` (twice). Each is a deprecation **warning**, so the zero-warning gate fails
  even though the proof elaborates.
- **rule**: replace on transcription — `if_neg h` ⇒ `ite_eq_right (h := h)` (and the `if_pos`
  dual), `tendsto_finset_prod` ⇒ `tendsto_finsetProd`; the semantics are unchanged and the
  statements are unaffected. The pin files' `attribute`/`p2m_*` walls are still not transcribed.
- **seen**: 2026-10-31, RS2 order A (the four renames were the order's only statement-preserving
  deviation; the block then compiles silently at a 20k heartbeat cap).

## FR-0081 [lean] [port] — the A4 helper table's *namespaces* and *binders* both drift: `T_mem_Gamma1`/`Gamma_le_Gamma1` are `ModularForm.Level`, `qParam_one_eq_pow` is `X1DiamondRational` (and ℂ-valued vs ℍ-valued)

- **where**: `FLTForHuman/ModularCurve/SiegelUnit/ProductForm.lean`, order A's `IntZero` block,
  transcribed from `P2M/Sol/S_…_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean`
  (`Group`/`Forms`/`Delta` sections), and the same in the 457 `INTINF` block; met porting orders A
  of [../topics/modularCurve/WORKORDER-RS3-ready-shelf3.md](../topics/modularCurve/WORKORDER-RS3-ready-shelf3.md)
  §A4.
- **symptom**: the order's A4 table gives the pin's spellings (`CongruenceSubgroup.T_mem_Gamma1`,
  `CongruenceSubgroup.Gamma_le_Gamma1`, `ModularCurve.qParam_one_eq_pow`, `ModularCurve.natCast_pos`)
  with the *file* they live in. In the port the first two are `ModularForm.Level.T_mem_Gamma1`
  (`ModularForms/Level/Gamma1Slash.lean:65`) and `ModularForm.Level.Gamma_le_Gamma1` (`:77`); the
  other two are `X1DiamondRational.qParam_one_eq_pow` / `X1DiamondRational.natCast_pos`
  (`ModularForms/WeightOne/Defs/RatAt.lean:113,115`). `#check @CongruenceSubgroup.T_mem_Gamma1`
  and the three siblings are `unknownIdentifier`.
- **second drift, the one that costs lines**: the port's `qParam_one_eq_pow` is
  `(N : ℕ) [NeZero N] (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N`, while the pin's
  469-layer copy is `(N : ℕ) (hN : 0 < N) (z : ℂ) : Periodic.qParam 1 z = Periodic.qParam N z ^ N`.
  They are not interchangeable at a call site whose `N` only has `0 < N` (the `Delta` section) and
  whose argument is a `ℂ`, so the ℂ-valued form is re-spelled in the module (6 lines) and the
  457 layer's `INTINF.qParam_one_eq_pow` is a one-line alias of the port's.
- **rule**: read the A4 table's *file* column, not its *name* column, for a helper it marks
  "import"; and when the pin has two copies of one fact at different binders (ℂ-valued and
  ℍ-valued), the port's single public copy serves whichever call site matches its binder and the
  other one is re-spelled privately. `natCast_pos` is the same story with a one-line body, so it was
  written in-module to keep the pin's implicit-`N` binder.
- **seen**: 2026-11-01, RS3 order A (all three headlines green, module silent at the 200k loop).

## FR-0082 [lean] [port] — `coeff_jqModC_of_lt` is *not* in `Defs/JqCoeff.lean`: the port's public copy sits in the `X0` cone, so order C re-spells it in one line

- **where**: order C's `IgusaSepAux` block in
  `FLTForHuman/ModularCurve/ModularPolynomialCoset.lean`, transcribed from
  `P2M/Sol/S_…_separable_map_ratFunc_of_natCast_ne_zero.lean`; met porting order C of
  [../topics/modularCurve/WORKORDER-RS3-ready-shelf3.md](../topics/modularCurve/WORKORDER-RS3-ready-shelf3.md) §3.
- **symptom**: the order's "use, do not restate" list names `coeff_jqModC_neg_one` **and**
  `coeff_jqModC_of_lt` as public in `Defs/JqCoeff.lean:196`. That line is `coeff_jqModC_neg_one`;
  `Defs/JqCoeff.lean` carries `coeff_jqModC_pow_self` and `coeff_jqModC_pow_of_lt` but **no**
  `coeff_jqModC_of_lt`. The port's only public `coeff_jqModC_of_lt` is
  `FLTForHuman/ModularCurve/X0/FunctionFieldFull.lean:96` — a module the 0-importer host does not
  have and whose cone is the `X0`/function-field tower.
- **rule**: for a one-line consequence of a declaration the host already imports, re-spell it
  privately rather than pull the cone: `simpa using coeff_jqModC_pow_of_lt R (b := 1) (m := m)
  (by simpa using hm)`. This is the same call the A4 table makes for `T_pow_mem_Gamma` (write the
  5 lines, do not import 38 modules), and it is worth applying to the *premise audit* rows too —
  a row that names a declaration's `file:line` should be re-resolved, not trusted, when the line is
  the neighbouring declaration.
- **seen**: 2026-11-01, RS3 order C (checker 35 ok / 0 / 0, module silent).

## FR-0083 [lean] [port] — five v4.34 deprecation renames in the 457 block (`if_pos`/`if_neg`/`if_false`/`ModularForm.coe_sub`)

- **where**: `FLTForHuman/ModularCurve/SiegelUnit/ProductForm.lean`'s `DeltaQExpInt`/`INTINF`/`solution`
  blocks, transcribed from `P2M/Sol/S_…_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean`.
- **symptom**: the zero-warning gate fails on deprecations alone: `if_pos` → `ite_eq_left` (4
  occurrences), `if_neg` → `ite_eq_right` (2), `if_false` → `ite_false` (1),
  `ModularForm.coe_sub` → `FunLike.coe_sub` (2). Same family as FR-0080 (`if_neg`/`if_pos`/
  `tendsto_finset_prod` in `SiegelUnit/Integrality.lean`), now with the `if_false` and the
  `FunLike.coe_*` renames added.
- **rule**: transcribe the renames mechanically — the argument shapes are compatible
  (`ite_eq_left (h := …)`, `ite_eq_right (h := …)`), and `FunLike.coe_sub` replaces the
  `ModularForm.coe_sub` spelling everywhere (the `Pi`/`DFunLike` coercion lemmas have moved to
  `FunLike`). The 249 layer needed none of these; the 457 layer needed all five.
- **seen**: 2026-11-01, RS3 order A (the 457 block then compiles silently at the 200k loop).

## FR-0084 [lean] [gate] — `linter.style.haveILetI` vs the pin's `haveI`/`letI` idiom: `have`/`let` do register the instance, and the defeq check still succeeds

- **where**: order C's `solution` in `FLTForHuman/ModularCurve/ModularPolynomialCoset.lean`: the pin
  writes `letI : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra` and
  `haveI : NeZero ((N : ℕ) : K) := ⟨hNK⟩`; the port may not (a `haveI`/`letI` in a proof of a
  proposition is a `linter.style.haveILetI` warning, and the gate is zero warnings).
- **symptom**: the `letI` is *load-bearing*: without it `algebraMap K E` elaborates at
  `HahnSeries.powerSeriesAlgebra` and is not definitionally the composite
  `(algebraMap L E).comp (algebraMap K L)`, so the pin's last step
  (`convert hp using 2 <;> first | with_reducible_and_instances rfl | rfl`) fails with "Tactic `rfl`
  failed: The left-hand side … is not definitionally equal to the right-hand side `algebraMap K E`".
  This is the same seam as FR-0079's `HahnSeries` algebra diamond.
- **fix that works**: write the pin's `letI` as a plain `let` (`let : Algebra K E := …`) and its
  `haveI` as a plain `have`. Lean 4's `have`/`let` register local instances themselves, and a
  `let`-bound instance is zeta-reducible for both typeclass search and `isDefEq`, so the composite
  *is* defeq to `algebraMap K E` and the pin's `convert hp using 2` then closes the goal with no
  residual `rfl` goals at all (the trailing `<;> first | … | rfl` became dead and was removed once
  — before the `let` was in place it was still needed, which is how the two states are told apart:
  the `let` version emits `linter.unusedTactic`/`linter.unreachableTactic` on that tail).
- **also in this pass, same cause (a pin idiom that a port linter refuses)**: the pin's
  `variable {N} [NeZero N]` block with an unused instance makes `linter.unusedSectionVars` fire on
  `Forms`' `coe_Thetaform` (fixed: give the two declarations explicit `{N} [NeZero N]` binders); the
  pin's `convert … <;> try …` makes `linter.unnecessarySeqFocus` fire (fixed: `(convert …; try …)`);
  and the pin's `simpa [h] using (hasSum_zero …)` makes `linter.unnecessarySimpa` fire (fixed:
  `simp [h]`).
- **seen**: 2026-11-01, RS3 orders A and C. The `have`/`let` half is instance-shaped: see
  [../instance-friction.md](../instance-friction.md)'s `IF` note on this row.

## FR-0085 [lean] [port] — order C needs two mathlib imports the order did not list (`RatFunc.Basic`, `RootsOfUnity.AlgebraicallyClosed`)

- **where**: `FLTForHuman/ModularCurve/ModularPolynomialCoset.lean`'s new import block, order C of
  [../topics/modularCurve/WORKORDER-RS3-ready-shelf3.md](../topics/modularCurve/WORKORDER-RS3-ready-shelf3.md) §3
  ("New import: `FLTForHuman.ModularCurve.Degree.PhiDegree` only").
- **symptom**: the pin imports `Mathlib`, so its 128 lines use `RatFunc`, `IsFractionRing.lift`,
  `algebraMap (Polynomial F) (RatFunc F)` and `HasEnoughRootsOfUnity.prim (M := AlgebraicClosure K)`
  without naming a module. `PhiDegree`'s cone supplies `RatFunc`'s *type* through
  `IntermediateField`/`AlgebraicClosure` imports but not `Mathlib.FieldTheory.RatFunc.Basic`'s
  API or the `HasEnoughRootsOfUnity` instance at `AlgebraicClosure`; `#check @RatFunc` resolves,
  `#check @HasEnoughRootsOfUnity.prim` does not.
- **rule**: for an order whose pin file is `import Mathlib`-only, price *two* import lines, not one:
  the subject module plus whichever mathlib module carries the `IsFractionRing`/`RatFunc` API
  (`Mathlib.FieldTheory.RatFunc.Basic`) and whichever carries the roots-of-unity existence instance
  (`Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`). Both are acyclic and the resulting
  module is still a 0-importer host.
- **seen**: 2026-11-01, RS3 order C (checker 35 ok / 0 / 0; consumer zone green).

## FR-0086 [tool] — `move_dead.py` reads a `private`-heavy module as 3 declarations, so "0 dead" is not evidence

- **where**: `tools/deps/move_dead.py` run on the two touched modules of RS3 orders A and C.
- **symptom**: `--source lean/FLTForHuman/ModularCurve/SiegelUnit/ProductForm.lean` reports
  "3 declarations, 11 lines" for a 1,216-line module with 3 public headlines and 96 `private`
  declarations, and `ModularPolynomialCoset.lean` (992 lines) as "0 declarations, 0 lines". The
  parser does not see `private def`/`private theorem` at column 0, so it cannot compute liveness
  for them and reports nothing to move. `dedup.py` on the same two modules reads 99 and 40
  declarations and reports **0 duplicate clusters** at `name,shape,body` tiers (also at
  `--min-cost 0`), which is the number to quote.
- **rule**: quote `dedup.py`'s cluster count as the dedup evidence on a `private`-heavy module and
  read `move_dead.py`'s output as "no *public* declaration is dead" rather than "nothing is dead".
  The two declarations this pass knows to be pin-fidelity-only and unreferenced are
  `coe_restrictMF` (required by the order's errata, 3 lines) and
  `exists_int_discriminant_qExpansion_coeff` (one of the pin `S_` file's 45 declarations, kept so
  the transcription is the file); both stay.
- **seen**: 2026-11-01, RS3 orders A and C.

## FR-0087 [lean] [port] — order B's *statement* needs `Mathlib.GroupTheory.DoubleCoset`, which the module's closure does not have

- **where**: `FLTForHuman/ModularCurve/LevelN/GenusFF.lean`'s new import block, order B of
  [../topics/modularCurve/WORKORDER-RS3-ready-shelf3.md](../topics/modularCurve/WORKORDER-RS3-ready-shelf3.md) §2
  ("Imports to add: `LevelN.QExpBridge`, `LevelN.SpecialRamification`,
  `IsCurveOver.ConstantFieldExtensionSpan`, `Degree.PhiDegree`").
- **symptom**: the wrapper's statement is built from
  `Nat.card (DoubleCoset.Quotient (Γ : Set SL(2,ℤ)) (Subgroup.zpowers … : Set SL(2,ℤ)))`, and
  `DoubleCoset` is unknown in the four-import closure (`unknown identifier 'DoubleCoset.Quotient'`
  on all nine occurrences). `Mathlib.GroupTheory.DoubleCoset` is a leaf mathlib module
  (`Coset.Basic` + `Subgroup.Pointwise`), acyclic and cheap; it was added as a fifth import line.
- **rule**: a pin `import Mathlib` file may use a mathlib module the *premises'* closure does not
  reach. The order's import list is priced from the premises; a name in the **statement** is a
  separate line. Read the wrapper first and `#check` every non-prelude identifier in it.
- **seen**: 2026-11-01, RS3 order B (checker 3 ok / 0 / 0; module build green).

## FR-0088 [lean] [instance] — the pin's `synthInstance.maxHeartbeats 1600000` wall is one `Module.Free` search at the concrete `ℚ̄⟮y⟯`, and it is *not* fixable by supplying the instance by hand

- **where**: `LevelN/GenusFF.lean`'s `main_K`, the pin's line 26 option and its line 895
  `maxHeartbeats 6400000` (work order §B0.1), at `FiniteDimensional ℚ̄⟮y⟯ FF`.
- **symptom**: `apply Module.finite_of_finrank_pos` at the concrete
  `((AlgebraicClosure ℚ)⟮y⟯)` dies with "failed to synthesize `Module.Free ↥(adjoin …) FF` /
  (deterministic) timeout at typeclass, maximum 20000 heartbeats" — the `-DmaxHeartbeats=200000`
  edit loop does **not** raise `synthInstance.maxHeartbeats`, which is the 20000 in the message.
  Two separate causes, measured:
  1. `Module.Free` over a division ring is `Module.Free.of_divisionRing`
     (`Mathlib/LinearAlgebra/Basis/VectorSpace.lean`), which is **not in this module's closure**;
     without it the search *fails* (after exhausting every other `Module.Free` instance), with it
     the search merely runs past 20000. So the import is the first half of the fix (see FR-0089's
     sibling note in this file: mathlib imports of a `import Mathlib` pin).
  2. supplying it by hand does not work: `Module.Free.of_divisionRing _ _` is rejected with a
     `Semiring`-path mismatch — the goal's `Module.Free` is keyed on
     `(SubsemiringClass.toCommSemiring …).toSemiring` while the constructor's is
     `DivisionRing.toRing.toSemiring`. Same failure for a hand-written
     `StrongRankCondition`/`DivisionRing` chain: instance *paths* are data, not propositions.
- **fix that works**: state the fact at a **variable** intermediate field —
  `finiteDimensional_of_finrank_pos_intermediate (E : IntermediateField L M) (h : 0 < finrank E M)`
  — where the search is instant (measured: silent at the default 20000), then apply it at
  `E := ℚ̄⟮y⟯`. With that, `main_K` elaborates whole inside the 200k edit loop: **no split and no
  cap is needed**, and the pin's 6.4M on `main_K` disappears with the 1.6M on the module.
- **seen**: 2026-11-01, RS3 order B. Instance-shaped detail + the diagnosis recipe:
  [../instance-friction.md](../instance-friction.md) `IF-005`.

## FR-0089 [lean] [port] — mathlib v4.34 arity/API drift across 1,123 transcribed lines: six shapes, all mechanical

- **where**: the order-B transcription of
  `P2M/Sol/S_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index.lean` into
  `LevelN/GenusFF.lean`. Each of these compiled in the pin and does not here (or vice versa):
  | pin text | v4.34 |
  |---|---|
  | `IntermediateField.adjoin_algHom_ext ℂ hgen` | unchanged — `F` is still **explicit** (`#check` it; guessing it implicit costs a run) |
  | `(IntermediateField.mem_map).mp he` | `(IntermediateField.mem_map (S := A) (f := f)).mp he` — `S` became explicit |
  | `DoubleCoset.out_eq' Γ Kst r` | `DoubleCoset.out_eq' (H := Γ) (K := Kst) r` — `H K` became implicit |
  | `rw [CongruenceSubgroup.Gamma1_mem]` | works, but its signature is `(N) (A)` explicit (rewrite still unifies) |
  | `have hcard : 0 < Nat.card H := Nat.card_pos` | `Nat.card_pos` now needs `[Finite α]`; use `rw [← h1]; exact Module.finrank_pos` from `finrank (fixedField H) K = Nat.card H` |
  | `rw [h, σK_ker]` where `h : liftHom … γ = 1` and the goal is `σ' M K γ = 1` | `σ'` is a `def`, so it does not `rw`-unfold *under application*; open with `show (liftHom …) γ = 1 ↔ …` |
- **two more, not arity**: the pin's `@[scoped simp]` on `liftE_apply`/`liftHom_apply`/`σ'_apply`
  is dropped (the two `_apply` aliases are unused here; `σ'_apply` is used by name in `hσE`), and
  `Subgroup.index_map` is `(H ⊔ f.ker).index * f.range.index` — the pin's `finrank_fixedField_map`
  chain (`… σ'_ker, index_top, mul_one`, then `congr 1` + `le_antisymm` on `Γ ⊔ (Γ(N) ⊔ ±1)`) works
  as written, which is worth knowing before rewriting it.
- **rule**: `#check @` every identifier whose call shape you are about to transcribe from a
  1,000-line pin proof, not just the ones the order named; on this row the arity drift was six
  lines, but each cost an edit-loop cycle when it surfaced as a downstream error.
- **seen**: 2026-11-01, RS3 order B (all fixed mechanically; module silent, checker 3 ok / 0 / 0).

## FR-0090 [lean] [port] — FR-0085's "price two import lines for an `import Mathlib` pin" is an upper bound, not a rule: the 252-line peaked-auxiliary row needed **no** mathlib import

- **where**: `FLTForHuman/ModularCurve/SiegelUnit/PeakedAuxiliary.lean` (new), transcribed from
  `P2M/Sol/S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd.lean` (252
  lines, `import Mathlib` plus three `Theorems/` wrappers), after the RS3 wave
  ([../topics/modularCurve/TOPIC-ready-shelf-3.md](../topics/modularCurve/TOPIC-ready-shelf-3.md) §12).
- **symptom**: none — which is the datum. Order C's pin (FR-0085) was `import Mathlib`-only too and
  needed two mathlib modules (`RatFunc.Basic`, `RootsOfUnity.AlgebraicallyClosed`) that its host's
  closure lacked; this row's pin is `import Mathlib`-only and needed **zero** mathlib imports beyond
  the three FLT modules it names. Everything it uses — `Asymptotics.IsBigO.of_bound`,
  `Real.abs_exp`/`exp_le_exp`, `ZMod.addOrderOf_coe`, `Nat.card_zmultiples`,
  `QuotientAddGroup.eq`, `Finset.sum_fiberwise`, `Int.emod_add_mul_ediv`,
  `AddSubgroup.mem_zmultiples_iff` — is already in `SiegelUnit/ProductForm`'s closure, because that
  module's own 469/457 layers rest on the same analysis of `q`-expansions.
- **rule**: the two-import estimate is what an `import Mathlib` pin costs *when the target's closure
  is a thin algebraic corner*; it is not a property of `import Mathlib`. Decide by the APIs the pin
  actually uses and the closure of the module the row will sit above. Corollary for sizing: a row
  whose premises are all in one already-landed module's closure is a transcription, not a route
  problem — this one went in with no `#check`-driven substitutions, no v4.34 renames, and no
  declaration over the 200k edit loop, in one pass.
- **seen**: 2026-11-01, RS3 §12 (manager's own port, not a dispatch).

## FR-0091 [lean] [port] — `omit … in` **does** parse in this toolchain, so the pin's section-variable spelling is reproducible

- **where**: promotion of the shared `S`-conjugate prelude of
  `FLTForHuman/ModularCurve/SiegelUnit/ProductForm.lean` (`Thetaform`/`coe_Thetaform`), met while
  porting the 249 row of [../topics/modularCurve/TOPIC-ready-shelf-3.md](../topics/modularCurve/TOPIC-ready-shelf-3.md)
  §13.
- **symptom**: promoting `coe_Thetaform` at the pin's own binder spelling (section variables
  `{N} [NeZero N] {w : ℤ}`) makes `linter.unusedSectionVars` fire, because the instance is unused in
  that statement. The pin answers with `omit [NeZero N] in`, and shelf 2's order D recorded
  (`TOPIC-ready-shelf-2.md`, order D's deviation) that **`omit … in theorem` does not parse** in this
  toolchain — so the temptation is to split the section or to re-spell the binders explicitly.
- **measured**: `omit [NeZero N] in theorem coe_Thetaform …` parses and elaborates **silently** at
  v4.34, and the declaration's statement is then byte-identical to the pin's (checker `ok`, and the
  module's checked surface grows from 3 to 18 `ok`).
- **rule**: prefer the pin's `omit … in` over splitting a section; it is statement-preserving by
  construction, whereas re-spelling the binders explicitly changes the declaration text the checker
  diffs. Shelf 2's note is now stale for `omit … in theorem` (it may still hold for other
  `omit … in` positions — re-test rather than assume).
- **seen**: 2026-11-01, RS3 §13.

## FR-0092 [tooling] [method] — a *pre-existing* same-last-name node at a weaker statement hides an unported premise: `twin_scan --node` per premise is the audit, `--unport` prices it

- **where**: the scoping read of SET-AF1
  ([topics/automorphicForm/SET-AF1.md](topics/automorphicForm/SET-AF1.md) §0.2). The shelf row
  `AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous` (89 silo)
  cites `NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow` (236 silo).
- **symptom**: `frontier.py --ds --ready` prints the row with `premises = 1`,
  `premises_unported = 0` — i.e. ready — and `--selfcheck` PASSes; but the port has only
  `RatIdele.exists_norm_apply_eq_ideleNorm_rpow`, the statement over `ℚ`
  (`NumberTheory/RatIdele/ClassCharNorm.lean:366`), in a different namespace with a different
  normalizer (`RatIdele.ρ`). The general number-field node is not ported, so the row cannot be
  written.
- **cause**: the same name-anchored reading FR-0047 records, but from the *other* direction. FR-0047
  is a **landing** shadowing an older general node; here the port has long held a **specialisation**
  whose last name equals the general pin node's, and neither `--ready` nor `--selfcheck` compares
  statements against names (the source-tier check is `Thm_` stem → name tier, not statement → name).
  `twin_scan --node` names the situation precisely: **`relative`** — "same last name, different
  statement", the verdict it also gives for a genuine binder variant, so it is a *flag to read*, not
  a verdict to trust.
- **fix**: in a scoping read, run `twin_scan --node` on **every premise of every row you intend to
  cut** (0.6 s each; `TWIN-public` = ported at that statement, `new`/`relative` = not) and put the
  verdict column in the brief. Then price the correction with the recipe's own one-command corrected
  read — `--unport <the shadowed node>` on the same `frontier.py` invocation. Here it moved
  `needed` 924 / 375,331 → **925 / 375,567**, dropped the AF row off the ready shelf and put the
  236-line general node on it (leverage 7 / 42), and the corrected read is what the set is cut from.
  `--unport` is now doing the work FR-0047's post-landing diff was invented for, before any landing.
- **seen**: 2026-11-02, SET-AF1 §0.2–§0.3.

## FR-0093 [tooling] — a pin-`private` helper whose statement the port holds publicly is invisible to the prelude count, so the pricing over-counts new lines

- **where**: SET-AF1's B1 module (`NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow`,
  [topics/automorphicForm/SET-AF1.md](topics/automorphicForm/SET-AF1.md) §1.5). `twin_scan` priced it
  `prelude 0/24`, i.e. all 24 declarations of the pin `S_` file as new.
- **symptom**: the worker (correctly) did not re-prove three of them. Two are pin-`private` helpers
  whose statements the port already holds **public** — `continuous_archUnitHom`
  (`NumberField.TateGlobal.continuous_archUnitHom`, `TateGlobal/NormSection.lean:83`) and
  `ideleNorm_archUnitHom` (`NumberField.TateGlobal.ideleNorm_archUnitHom`,
  `TateGlobal/ArchNorm.lean:57`) — and the third, `coe_archCentralUnit_eq`, exists only to serve those
  two proofs. The module landed at 246 lines / **21** declarations.
- **cause**: the pin keeps both helpers `private`, so they are not graph nodes and `twin_scan --node`
  cannot be asked about them (`not a theorem node`); the prelude counter compares the pin file's
  declarations against the port's statements, but the port's copies live under the `TateGlobal`
  namespace (a rename), and the pin side's section variable is `K` where the port's is `F` — the same
  pair of obstacles FR-0078 records for the *shape* tier, here on the *statement* tier.
- **rule**: `prelude n/m` is a lower bound on reuse, and a **pin-`private`** helper is where it is
  weakest. Price a node with 20+ declarations by reading its `port_advise` *substitute* block against
  the file (the block that lists what the port already has), not by the prelude ratio; and when a
  landed module comes out short of its priced declaration count, check first for exactly this (reuse
  the pricing did not see) before assuming a transcription was dropped. Here the miss was in the safe
  direction (fewer lines written than priced).
- **seen**: 2026-11-02, SET-AF1 B1.

## FR-0094 [lean] [port] — the `if`/`dif` deprecation family is a fifth v4.34 rename set, and a `TopologicalSpace (Matrix …)` instance does not synthesise inside a term

- **where**: SET-AF2's M2 (`Adelic/InducedSectionMaximalCompact.lean`,
  [topics/automorphicForm/SET-AF2.md](topics/automorphicForm/SET-AF2.md) §1.6).
- **symptom (a)**: the pin's `dif_pos` / `dif_neg` / `if_pos` / `if_neg` are deprecated at `v4.34`;
  thirteen occurrences in the 478-line Weyl/unipotent proof. The `v4.34` names are `dite_eq_left` /
  `dite_eq_right` / `ite_eq_left` / `ite_eq_right` (the port already uses them in
  `Analysis/Complex/CircleIntegralResidue.lean` and `Analysis/PowerSeries/EisensteinAlgSeries.lean`).
  This is a **fifth** deprecation family after FR-0080/FR-0083's `if_pos`/`if_neg` (which were the
  same names in a different position — check both the `_of_` and the plain forms), `push_neg` (FR-0036)
  and the `Set` family (`Set.setOf_forall`/`setOf_and`/`mem_setOf_eq` →
  `Set.ofPred_forall`/`ofPred_and`/`mem_ofPred_eq`, which SET-AF2's gate hit).
- **symptom (b)**: the pin's `continuous_finComponent_glFin` proof goes through
  `Units.continuous_val.matrix_elem` entry by entry. In the port that term does not elaborate: the
  `TopologicalSpace (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))` instance is not synthesised *inside
  the term*, although `#synth` finds it interactively. Proved instead as
  `(continuous_finComponent v).comp (continuous_glFin)` — one line, no new import, and it also removes
  the need for the pin's `attribute [local instance] glBorel` line in that module.
- **rule**: for (a), grep the pin proof for `if_pos|if_neg|dif_pos|dif_neg` when it has `dite`/`ite`
  branches and translate to the `…_eq_left`/`…_eq_right` names; for (b), when a pin proof's *term*
  names a matrix-entry continuity, prefer the port's structural continuities
  (`continuous_finComponent`, `continuous_glFin`, `continuous_archComponent`, `continuous_glArch`)
  and only fall back to the entry route with the instance supplied explicitly (`letI := …`).
- **seen**: 2026-11-02, SET-AF2 M2.

## FR-0095 [tooling] [method] — a large landing *manufactures* last-name shadows: a `private` helper named after an unported pin node moves `needed` and the ready shelf in the wrong direction

- **where**: the post-landing re-read of SET-AF2. The new M2 module proves
  `private theorem continuous_unipotentGL2`, and the pin has the node
  `AutomorphicForm.continuous_unipotentGL2` (28 silo, a leaf).
- **symptom**: the raw re-read reports `needed` **909 / 373,333**, i.e. 1 node / 28 lines *better* than
  the true figure, and puts **two** rows on the ready shelf
  (`continuous_rightConv_and_contDiff_of_isFactorizableTestFn`,
  `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset`)
  whose only missing premise is that node — so the shelf over-reports by two and the set looks better
  than it is. `frontier.py`'s ported set is a set of last-name components **including `private`
  declarations** (`scan_port_decls(include_private=True)`), so any helper that happens to carry an
  unported node's last name silently "ports" it. FR-0047 recorded the same mechanism after
  *renaming*; this is the accidental version, and it is a function of landing size: 45 private
  declarations in one module is 45 chances to collide.
- **fix**: after **every** landing, run the read twice — the instrument's and the `--unport` one — and
  diff the new modules' `private` declaration names against the unported last names
  (`grep -o 'private theorem [A-Za-z0-9_]*' <new modules>` versus the `needed` last names). Here the
  correction is one node (`--unport AutomorphicForm.continuous_unipotentGL2`) and it restores both
  figures: `needed` 910 / 373,361 and the shelf to 27 rows / 6,669 silo, which is what SET-AF2 §8
  quotes. The *renamed-copy* variant of FR-0047 and this *collision* variant are one rule: the
  corrected read is part of the landing, not of the next scoping.
- **seen**: 2026-11-02, SET-AF2 §8.

## FR-0096 [tooling] [method] — a module-level gate census over-reports because ported `Def_` modules are wired by `-- pin:` markers, not `spec-pin:` lines; and `gate_scan.py`'s port root is relative to the CWD

- **where**: the SET-AF3 scoping read (§0.3), building the `AutomorphicForm` gate census from the
  wrappers' `import Definitions.Def_*.lean` lines, then confirming each candidate with
  `spec/gate_scan.py`.
- **symptom (a)**: the census reported **ten** pin `Def_` modules as unported —
  `BorelSubgroup`, `EtaFamily`, `InducedSection`, `WeylIntertwining`, `LocalOrbitalBase`,
  `TwistedOrbital`, `AdelicFourier`, `TateGlobalZeta`, `TateLocalZeta`,
  `Mathlib_LinearAlgebra_Countable` — and hence ten rows as "gated". Every one of them is ported:
  `gate_scan` says **0 missing** for all of them (e.g. `BorelSubgroup` 3/19 used, `TwistedOrbital`
  10/82 used). The cause is that a ported `Def_` transcription may be wired by `-- pin:` markers in
  an engine module (the `ArchCasimir`/`ArchInfra` pattern) instead of a `spec-pin:` line, and a
  ported-set test built from `spec-pin:` + `old_check_stmts.py` alone reads such a module as absent.
  The error is expensive in the scoping direction: it prices a definition wave that does not exist.
- **symptom (b)**: run from the repository root instead of `lean/`, `gate_scan.py` reports **every**
  declaration `MISS` — its `--port-root` default is `FLTForHuman`, a path relative to the CWD, and a
  missing root silently yields an empty port index. The first run of the census did exactly this and
  "found" forty missing declarations in the four rows this set cuts.
- **fix**: use `gate_scan` as the *census*, not just as a confirmation — run it once per imported
  `Def_` module with the rows that name it, from `lean/`, and treat the module list as a first cut
  only. A row is gated when `gate_scan` reports missing *declarations*, and the count to quote is the
  pin lines of those declarations: on this shelf the whole remaining gate is ≤ 44 pin lines per row
  (`FnTwist.det_centralScalar` 4, `RationalTorusUnipotentQuotient` 15, `IwasawaShellIndex` 44,
  `UnramifiedWhittaker_HeckeRecursion.placeEmbed` 8, …) — five small definition items, not five
  modules.
- **fix (landed, 2026-11-02)**: the whole class was swept, not just the ten rows. **Thirty-two** port
  modules that transcribed a pin `Def_` module with per-declaration `-- pin:` markers now carry a
  `spec-pin:` header instead — **684 markers removed, 32 wires added**, the six of them that were
  still in `PORT_FILES` retired there (`SOURCES` rows kept), and the register fell 139 modules /
  4,024 declarations → **113 / 3,478**. The checker reads **686 ok, 0 mismatch, 0 missing, 6 own** over
  the 32; the six `own:` rows are the statements the wire cannot reach (three written through the
  deprecated `Ideal.inertiaDeg'`, `AlgEquiv.extendScalars` through `AlgHom.restrictDomain` →
  `AlgHom.domRestrict`, and one port-own `IsBiscalar` instance), each with its reason in
  `spec/decl_markers.tsv`. The sweep moved no shelf figure (the frontier's ported set is by
  declaration name) — it moved the *checked surface*, which is what the next set's imports rely on.
- **seen**: 2026-11-02, SET-AF3 §0.3 and §4.5.

## FR-0097 [port] [method] — a port engine that *merged* two pin lemmas under the stronger one's hypothesis cannot serve the row stated at the weaker one; and a workorder's engine list must be grepped, not inferred

- **where**: SET-AF3's span module
  ([topics/automorphicForm/SET-AF3.md](topics/automorphicForm/SET-AF3.md) §1.5), rows
  `finiteDimensional_span_rightTranslate_of_mem_{archCut,archDualCut}Submodule` (459, 222).
- **symptom (a)**: the pin proves `finiteDimensional_orbitSpan_of_mem_archCutSubmodule` with no
  continuity hypothesis. The port had *merged* that lemma into
  `ArchCutProjector.mem_Ecf_of_mem_archCutSubmodule`, whose statement additionally demands
  `Continuous φ` (the carrier `Ecf` is a submodule of continuous functions). The FD-only statement
  exists nowhere in the port, so the two rows — which the wrapper states without `Continuous` — could
  not use the engine, and the workorder's "use the port's per-place lemma" was only half true.
- **symptom (b)**: the same order listed `ArchCutProjector.placeOrbitSpan_mono_of_mem` among the port
  engines. It is a **pin declaration of the 459 `S_` file**; the port never had it. The worker caught
  it by grep and inlined the one-line argument.
- **cause**: an engine module written for one consumer is shaped by that consumer's hypotheses. A
  later row stated at the pin's weaker form cannot see the difference: the merged lemma's *last name*
  is new, so `port_advise`'s name tier does not flag it, and `gate_scan` only reads `Def_` modules.
- **fix**: when a port engine merges two pin lemmas, check whether the weaker one is a statement any
  shelf row carries (grep the `S_` files for the missing hypothesis); if it is, keep the weaker form
  public beside the stronger, or say in the set's brief which route the rows take. And **grep every
  lemma a workorder lists as available** before issuing it (`grep -rn 'theorem <name>' FLTForHuman`)
  — the order's engine table is a reading, and a name that occurs in the pin's `S_` file is not a name
  in the port. Here the miss cost nothing (the worker's shared-envelope route came out shorter than
  the pin's two inductions), but it could have cost a round.
- **seen**: 2026-11-02, SET-AF3 §1.5.

## FR-0098 [method] — the post-landing gate is a *checklist*, and `move_dead` is the step easiest to substitute with a proxy: "every helper is used" is not its verdict

- **where**: SET-AF3's landing record (§1.5/§4.6), where the gate list says `dedup.py` / `move_dead.py`
  and the first pass ran `dedup --within` on the new modules but replaced `move_dead` with a manual
  reference count of the private helpers (`grep -c` of each name).
- **symptom**: the manual count answers a *different* question. `move_dead` computes reachability from
  the module's public API over the whole declaration graph — a private block can reference nothing and
  still be reported only by the tool; and a block can be referenced by another *dead* block, which the
  per-name count shows as "used". The proxy also cannot see the closure question the tool exists for
  (what a dead tail still needs from the live core).
- **cause (tooling)**: `move_dead.py` has no report-only mode without `--target` (`--source` and
  `--target` are both required, even with `--dry-run`), so an attempt without a shelf path errors out
  and is easy to abandon. Pick a scratch target (`lean/Reserve/<set>/<Module>.lean`) — a dry run
  writes nothing.
- **fix**: run the three commands and quote their lines: `dedup.py --within --module <m>` (per module),
  `dedup.py --cross` over the set's modules plus the engines they import (the cross sweep is what
  catches a repeated engine across the module boundary), and
  `move_dead.py --source <m> --target lean/Reserve/<set>/<name>.lean --select dead --dry-run` per
  module — expect `0 declarations, 0 lines`. Record the verdicts in the brief, not a paraphrase. A
  pre-existing dead block in a touched *engine* module is reported and left (the `instructions.md`
  exemption for completeness content), but it must be named.
- **seen**: 2026-11-02, SET-AF3 §4.6/§1.5.

## FR-0099 [tooling] [method] — the declaration-level gate scan reads the *direct* `Def_` imports, and a definition can reach a row's statement through a `Def_` module's own imports

- **where**: SET-AF4's 49-line row
  `NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles`
  ([topics/automorphicForm/SET-AF4.md](topics/automorphicForm/SET-AF4.md) §0.4). Its statement is
  `finitePartUnits … ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles`.
- **symptom**: `spec/gate_scan.py --pin Definitions/Def_NumberField_IdeleBox.lean` reports the gate as
  the single declaration `finitePartUnits` (2 pin lines) and **0 missing** for anything else, and
  `port_advise --with-defs` lists four `Def_` modules — `HeckeEigenfunction`, `AdelicHeight`,
  `IdeleBox`, `TateGlobalZeta` — none of which contains `unitIdeles`. Yet `unitIdeles` and
  `mem_unitIdeles_iff` are **unported** (grepped in the port tree and in mathlib: absent), and the row
  cannot be written without them. They live in `Def_IsDedekindDomain_FiniteUnitIdeles`, which the row
  reaches only because `Def_NumberField_IdeleBox` imports it. The real gate is ≈27 pin lines in three
  modules, not ≈8 in two.
- **cause**: both tools close over the *wrapper's own* `Definitions/` imports — `gate_scan` over the
  one `--pin` module's declaration list, `--with-defs` over the wrappers' direct import lines. The
  pin's `Def_` modules import each other (`IdeleBox` → `FiniteUnitIdelesOutside` →
  `FiniteUnitIdeles`), so the vocabulary can be two edges away and invisible. This is FR-0049's
  lesson one level down: the readiness test is premise-based, and the *statement's* vocabulary needs
  its own read.
- **fix**: treat `gate_scan` + `--with-defs` as the first cut and hand-read the wrapper's statement for
  every `Def_`-sounding identifier, grepping each against the port
  (`grep -rn "def <name>\|theorem <name>\|abbrev <name>" FLTForHuman`); a negative is a gate, and it
  goes in the manager's def order at the *declaration* level. Here the order is `finitePartUnits`,
  `unitIdeles`, `mem_unitIdeles_iff`, `uniformizerIdele` — four declarations, three pin modules — and
  the mis-priced version would have stalled the worker on an unwritable statement.
- **seen**: 2026-11-02, SET-AF4 §0.4/§4.1.

## FR-0100 [method] [tooling] — the gate of a set's *consumers* needs `gate_scan` too: a `Def_` module can be 29/39 used with **nothing** missing, and a module-level census over-prices the rest

- **where**: SET-AF4's §0.5 consumer table and its §8 re-read
  ([topics/automorphicForm/SET-AF4.md](topics/automorphicForm/SET-AF4.md)). Four rows the set
  readies — `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043),
  `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` (624),
  `exists_flat_isInducedSection_family_eq_of_isInducedSection` (325),
  `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` (179) — were priced
  "remaining gate" from the *module-level* import census (the pin `Def_` modules their wrappers import
  and the port seems to lack).
- **symptom**: at landing, `gate_scan` showed the table wrong in both directions. `WeylSelectors`
  (`Def_AutomorphicForm_WeylSelectors`, 39 public declarations) is **29/39 used and 0 missing**, so
  624 was never gated and lands ready. The two real gates are *larger* than the census's pin-line
  counts: 325 needs `FnTwist.isSmoothVector_rightTranslationFn_mul` (22 pin lines), 179 needs the three
  `RationalCentreUnipotentQuotient` declarations (13), not the 4 and 5 claimed.
- **cause**: exactly FR-0096's over-report, one layer out — here applied to the rows a set *unblocks*
  rather than to the rows it cuts. A `Def_` module import is module-granular; a row can import it and
  use nothing (623's case), or use a declaration that was never in the module's census.
- **rule**: run `gate_scan` for every row whose *writability* the brief asserts, cut rows and consumers
  alike, and quote two different columns in §8 — **on the ready shelf** (the frontier's premise test,
  which is blind to definition gates, FR-0049) and **writable** (gate-free). Here the shelf lists all
  thirteen new rows; only ten are writable. A brief that merges the two columns mis-states what the
  next dispatch can pick up.
- **seen**: 2026-11-02, SET-AF4 §0.5/§8.

## FR-0101 [port] [method] — a row whose whole proof block already exists `private` in another module: promote it to a public home and delete the copy in the same touch

- **where**: SET-AF4's N3, `NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult`
  ([topics/automorphicForm/SET-AF4.md](topics/automorphicForm/SET-AF4.md) §1.5). Its six-declaration
  glue block was transcribed **private** in `AutomorphicForm/Adelic/Siegel/SlabCovering.lean` (from
  another pin `S_` file that copies the same block), and the pin's `_pow` helper is
  statement-identical to its `_pow_mult` headline.
- **symptom**: `port_advise` prices the row at **0 net new lines** ("already in the port"), which is
  true only in the hash sense — the statements exist as `private` declarations, so the row cannot be
  *imported*; a naive transcription writes 93 lines that duplicate a block `dedup` structurally cannot
  see (it reads public declarations), and the pin's two identical statements would leave a shape
  cluster inside the new module.
- **fix**: promote the block to a public home and delete the private copy in the same touch. Here the
  block's hypothesis names `AdelicGL2`, whose home is `AutomorphicForm/Adelic/Basic`, so the home is on
  the `AutomorphicForm` side (`AutomorphicForm/Adelic/IdeleNormDetGlue.lean`); `SlabCovering` imports
  it, loses its `private` copies (−91 lines) and its ℚ specialisation calls the public headline. Keep
  the block's **headline** at the wrapper's name and drop the pin's identical `_pow` helper. Rebuild
  the old module's dependents (`SlabCoveringTheorems`) — the direction `AutomorphicForm → NumberTheory`
  is what decides which side hosts the home.
- **outcome, and the shelf rule**: `SlabCovering` was brought to standards in the same touch (60
  markers → six `spec-pin:` wires, checker 3 ok, register 113 → 112 modules). It carried **two**
  pre-existing dead private declarations — the ℚ specialisation `ideleNorm_det_eq_archDetNorm_rat`
  (one line from the public general theorem) and the one-line inclusion
  `openShell_subset_shellIdeles` — and both were **deleted**, not shelved: `move_dead`'s `Reserve/`
  shelf is for dead declarations that *are* mathematics, and a statement derivable in a line is not.
  `move_dead --select dead` reads 0 / 0 afterwards. The module's one remaining dedup cluster is the
  pin's `stable`/`stable + centreCut` two-statement pattern and stays.
- **seen**: 2026-11-02, SET-AF4 §1.5.

## FR-0102 [tooling] [metadata] — a promoted declaration in a `Def_` module needs the **`Thm_`** wire, and the checker's normaliser does not add binders or strip namespaces

- **where**: SET-AF5's G1/G2, the manager's two promotions into the legacy `Def_` modules
  `AutomorphicForm/Adelic/ConstantTerm.lean` and `AutomorphicForm/Adelic/RightConvolution.lean`
  ([topics/automorphicForm/SET-AF5.md](topics/automorphicForm/SET-AF5.md) §1.5).
- **symptom (a)**: the module was wired with three `spec-pin:` lines — its `Definitions/Def_…` source,
  the promoted theorem's `P2M/Sol/S_…` copy, and nothing else — and `check_port` reported the new
  theorem **`MISSING (no match)`**, not a mismatch. An `S_` source's declaration is the `solution`
  of `P2MW.S_<stem>`, and the checker keys a promoted headline to the **`Theorems/Thm_…`** wrapper
  (the recipe's migration table writes such modules with a `Thm_` + `S_` pair for exactly this reason).
  Adding the `Thm_` line turned `MISSING` into `MISMATCH`, i.e. it started diffing.
- **symptom (b)**: two `MISMATCH`es then, both purely textual:
  (i) the port wrote `Continuous fun x : R => (unipotentGL2 x : GL (Fin 2) R)` where the wrapper writes
  `Continuous fun x : R => AutomorphicForm.unipotentGL2 x` — the type ascription *and* the namespace
  prefix are part of the diff, and the normaliser strips neither;
  (ii) the port transcribed the lemma with the module's section variables
  (`variable (K : Type) [Field K] [NumberField K]` in scope, as `rightConv_comp_mul_left` does) where
  the `S_` file's statement writes them **inline** (`(K : Type) [Field K] [NumberField K] …`). The
  section-variable form is *not* normalised into the inline one on a `Thm_`/`S_` wire — it is `ok`
  against a `Def_` source only because the pin's `Def_` file also uses a section variable.
- **fix**: for a promotion into a `Def_` module, wire **`Definitions/Def_…` + `Theorems/Thm_…` +
  `P2M/Sol/S_…`**, and write the statement with the *wrapper's* exact text: explicit binder block when
  the wrapper has one (shadowing the section variable is legal and is what the checker wants), the
  fully qualified name when the wrapper spells it out, and no type ascription the wrapper does not have.
- **rule**: the checker is text-first, so a promotion's statement is a *quotation of the wrapper*, not a
  paraphrase in the module's local style; and `MISSING (no match)` on a declaration you just wrote is a
  **wire** symptom, not a statement symptom — read the wire before editing the statement.
- **seen**: 2026-11-02, SET-AF5 §1.5 (three checker runs to get from `MISSING` to `ok`).

## FR-0103 [port] [method] — a "cheap" 28-line leaf can be the pin node of a development the port already wrote **k times**: port the general statement once and delete the copies

- **where**: SET-AF5's G1, `AutomorphicForm.continuous_unipotentGL2`
  ([topics/automorphicForm/SET-AF5.md](topics/automorphicForm/SET-AF5.md) §1.5). `port_advise` prices
  the row at **17 net** with **0 substitutions** and **0 already in the port**.
- **symptom**: both zeroes are true and both are misleading. The pin states the node at a general
  `CommRing R`; the port held its `R := AdeleRing (𝓞 F) F` instance **three times** —
  `continuous_unipotentGL2_adele` (`Cusp/SpectrumCarrier.lean`, public, 15 lines),
  `continuous_unipotentGL2'` (`WeylIntegrable/Assembly.lean`, public, 14, registered in
  `UNWIRED-PUBLIC`) and `private continuous_unipotentGL2` (`InducedSectionMaximalCompact.lean`, 13).
  `port_advise` is name-anchored and statement-anchored, so three *specialisations* under two other
  names and one shadowing name are invisible to it; and the third copy is why the pin node had been
  reading as **ported** since SET-AF2 (FR-0095's shadow), which is why the row looked free.
- **fix**: write the general statement in the module that defines the object it is about (here
  `Adelic/ConstantTerm.lean`, next to `unipotentGL2`), then delete every specialised copy and rewrite
  its call sites as `(continuous_unipotentGL2 (R := …))` — one term each. 17 lines written, 36 deleted,
  and the FR-0095 shadow disappears at the root: the pin node is ported by a declaration the checker
  diffs against its `Thm_` wrapper and reports `ok`, so the `--unport` correction every read since
  SET-AF2 needed is retired.
- **rule**: before accepting "0 already in the port" for a leaf, `grep -rn 'theorem <last name>'` and
  `grep -rn '<last name>'` over the port tree and read what the hits *state*; a hit at a specialised
  type is a duplicate to delete, not a supply to use. And when the same last name is `private` in one
  module, that module is the shadow — the cure is a public general statement, never a permanent
  `--unport`.
- **seen**: 2026-11-02, SET-AF5 §0.2/§1.5/§8.2.

## FR-0104 [tooling] — `move_dead` reads liveness by dotted-name reference, so a `private abbrev …` used only by `attribute [local instance]` reports as dead

- **where**: SET-AF5's W1, `AutomorphicForm/Adelic/RightConvRegularity.lean`
  ([topics/automorphicForm/SET-AF5.md](topics/automorphicForm/SET-AF5.md) §1.6). The module keeps the
  pin's wall verbatim: `private abbrev instNG : NormedAddCommGroup (mixedEmbedding.mixedSpace K) :=
  inferInstance`, the same for `instNS : NormedSpace ℝ …`, and then
  `attribute [local instance] instNG` / `instNS`.
- **symptom**: `move_dead.py --dry-run` reports **2 declarations / 5 lines** dead. Both are
  load-bearing: the attribute lines are the only *reference*, they name the abbrevs and the proof does
  not mention either again, so a reference scan finds no use. Acting on the report deletes the local
  instances and the module stops elaborating (`hasFDerivAt_integral_of_dominated_of_fderiv_le` cannot
  find the normed structure on the mixed space).
- **fix**: read the report's declarations before moving them, and treat `attribute`/`local instance` as
  a use. Here nothing was moved: real dead = 0.
- **rule**: on a module carrying a pin `local instance`/`attribute` wall (the `instNG`/`instNS`,
  `letI`/`haveI` class of FR-0036-adjacent transparencies), `move_dead`'s dead list is **advisory**;
  the gate is "does the module still build after the move", so apply it on a copy (`--copy`) or not at
  all. A tool that cannot see `attribute` references must not be the last word on dead code.
- **seen**: 2026-11-02, SET-AF5 §1.6.

## FR-0105 [proof] [drift] — `AdeleRing` is a semireducible `def`, not an `abbrev`, so `rw` cannot key a lemma about it at implicit transparency

- **where**: SET-AF5's W1, the private helpers `glArch_unipotent`/`glFin_unipotent`
  ([topics/automorphicForm/SET-AF5.md](topics/automorphicForm/SET-AF5.md) §1.6). The pin writes
  `AdelicLevel.glArch (𝓞 K) K (unipotentGL2 ((a, b) : AdeleRing (𝓞 K) K))` and closes with
  `rw [AdelicLevel.glArch_apply, unipotentGL2_coe, unipotentGL2_coe]`.
- **symptom**: the `unipotentGL2_coe` rewrite fails with
  `Application type mismatch: the argument (a, b) has type InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K
  but is expected to have type AdeleRing (𝓞 K) K`. Cause: mathlib declares
  `AdeleRing R K := InfiniteAdeleRing K × FiniteAdeleRing R K` as a **`def`** in mathlib's
  `NumberTheory/NumberField/AdeleRing.lean:50` (semireducible), while `rw`'s keyed matching runs at
  *implicit* transparency. So `unipotentGL2 ((a, b) : AdeleRing …)` does
  not key against the `R := `-polymorphic `unipotentGL2_coe`, and `(a, b)` is not accepted where the
  elaborated type is the `def`'s.
- **fix**: state the argument with the instance explicit —
  `unipotentGL2 (R := AdeleRing (𝓞 K) K) (a, b)` — and close by
  `ext i j; rw [AdelicLevel.gl{Arch,Fin}_apply]; fin_cases i <;> fin_cases j <;> rfl`, i.e. **without**
  the `_coe` rewrite. Content and statement are unchanged; the downstream rewrites in
  `archEntries_slice` still key on the two lemmas by name.
- **rule**: when an upstream `def` stands where the pin's `abbrev` did (a `Type`-level unfolding a
  proof is expected to rewrite through), either `abbrev` it in the port or give the transcribing proof
  an explicit-`R` statement that never asks `rw` to see through the `def` — the second is cheaper, safe
  for a private helper, and is what this landing did. The same class produced the `local instance` transparencies of FR-0104.
- **seen**: 2026-11-02, SET-AF5 §1.6.

## FR-0106 [method] [tooling] — a set's forecast is its **closure** return, not the sum of its rows' `return`: the set's own consumer is invisible to a per-row scan

- **where**: SET-AF6's §8 forecast ([topics/automorphicForm/SET-AF6.md](topics/automorphicForm/SET-AF6.md)),
  written before its one worker order was dispatched, and the re-read after it landed.
- **symptom**: every figure the cut controls came out exact — `needed` **896 / 367,956**, `literal`
  909 / 371,431, frontier **1,519 / 759,410** — but the ready block missed by **one row / 779 silo**:
  41 / 22,039 forecast, 42 / 22,818 measured. The set readied **two** rows, not one:
  `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar` (214, visible to both
  rows' returns) **and** `archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt`
  (**779**), whose unported premise set was *both* of the set's rows. A row that needs the whole set is
  the set's **consumer**, and it appears in **no** single row's `return`.
- **cause**: the brief's arithmetic summed `return(R1) + return(R2)`, which by definition only sees rows
  whose missing set is a singleton. SET-AF4 §8 hit the identical blindness *after* its landing ("a
  thirteenth row… had no single unported premise, it had several, all inside the set"); SET-AF6 is the
  same failure **before** it, i.e. the instrument was known to be blind and the forecast still used it.
- **fix / rule**: forecast with
  `return(set) = Σ silo of the unported cone rows whose unported premise set ⊆ set`,
  computed over the set (the same graph query, one predicate changed), and quote the per-row `return`
  only as the *ranking* aid it is. Two corollaries: a set with a *single* row is the same computation
  (which is why SET-AF4's earlier forecasts held), and a set whose consumer chain is two deep (A → B → C
  inside the set) needs the ⊆ form or it undercounts twice.
- **seen**: 2026-11-02, SET-AF6 §8 (the re-read), with SET-AF4 §8 as the precedent.

## FR-0107 [port] [drift] — a promoted helper's content name can collide with a Mathlib name; and two more v4.34 spellings the arch-derivative rows hit

- **where**: SET-AF6's R1/R2 ([topics/automorphicForm/SET-AF6.md](topics/automorphicForm/SET-AF6.md)
  §1.6), transcribing pin `aa2d8b3`'s two `S_` files against mathlib `v4.34.0`.
- **symptom (a), the naming one**: `IsFactorizableTestFn.liftM` (the port's content name for the pin's
  `e8l5M`) is **ambiguous with `_root_.liftM`** inside a `simp only` list — `simp only` resolves a bare
  name against the opened namespaces *and* the root, and both exist. The declaration must be written
  `simp only [IsFactorizableTestFn.liftM, …]`. Nothing is wrong with the promotion; the collision is the
  price of a content name that is also a common monadic one, and it will hit the next consumer of the
  engine (SET-AF7).
- **symptom (b)**: two spellings the pin uses are gone in v4.34 —
  `by_cases h : p <;> rw [if_pos h]` / `[if_neg h]` are now `ite_eq_left` / `ite_eq_right` (the
  `if_pos`/`if_neg` aliases are deprecated, so the rewrite fails the `-DwarningAsError`-clean build);
  and `hasFDerivAt_integral_of_dominated_of_fderiv_le`'s `(x₀ := e₀)` no longer names a binder, so the
  call takes `(𝕜 := ℝ)` and passes the point positionally (AF5's use of the same lemma already did).
- **rule**: a *promotion* inherits its own naming risk — before promoting a `private` helper at a
  content name, grep the root namespace for the same name (`liftM`, `lift`, `map`, `id`); and when a
  transcribed proof rewrites a *deprecated alias* (`if_pos`, `push_neg`, `Set.mem_setOf_eq`), expect the
  build to be silent but the rewrite to fail, and check FR-0036's list first.
- **seen**: 2026-11-02, SET-AF6 §1.6 (deviations 2 and 3).

## FR-0108 [tooling] [method] — cutting a dead declaration by hand from one declaration to the next swallows the sections and variables in between; cut to the end of the **body**

- **where**: SET-AF6's §1.7 triage, the deletion of the pin's dead `l5_continuous_rightConv` (56 lines)
  from `AutomorphicForm/Adelic/ArchDerivRightConv{,Complex}.lean`
  ([topics/automorphicForm/SET-AF6.md](topics/automorphicForm/SET-AF6.md) §1.7).
- **symptom**: the cut was computed as "from the declaration's start line to the *next declaration's*
  start line", which is correct only when nothing but the body sits between them. Here the next
  declaration was `private structure TcFamily` **five blocks later**, so the cut also removed
  `end TestData`, `section EngineBridge`, `open MeasureTheory Metric Set`, `section Engine` and the two
  `variable` lines (`{X} [MeasurableSpace X] (ν : Measure X)`, `{Y} [NormedAddCommGroup Y] …`). The
  module then failed 60 lines further down with `Unknown identifier X / Y / ν` (three errors, none of
  them near the cut), and the repair cost a re-derivation of the section skeleton from the pin.
- **cause**: exactly the failure `move_dead.py`'s own docstring warns about — *"span ≠ text: `end_line`
  runs to the next declaration; a section's `end`, `open`, or attribute between them is inside that
  span. Cut by `body_end`, and never let a moved block contain a column-0
  `namespace`/`section`/`end`"*; it is the reason the tool computes `body_end` at all.
- **rule**: hand-cut a dead declaration to the **last line of its body** (the first following column-0
  line that is a structural keyword — `end`/`section`/`namespace`/`open`/`variable`/`attribute`/a new
  declaration — and stop *before* it), or, better, let `move_dead` do it: `--select names --names <n>`
  moves exactly one declaration with its premises. And when a `set_option linter.… false in` line sits
  immediately above a cut declaration, it belongs to it and goes too — but the same line above the
  *next* declaration must be re-checked afterwards, since the cut's neighbours shift.
- **seen**: 2026-11-02, SET-AF6 §1.7 (one repair cycle, both modules).


## FR-0109 [method] — mechanical whole-node transcription or composition? Decide it by the port-overlap ratio, in one `port_advise` run

- **where**: two consecutive sets on the cone's two largest ready rows, scoped within an hour of each
  other: SET-AF7's `bigCell_eq_sum_pureTensor_of_flat_family` (5,407 silo) and SET-AF8's
  `rightConv_rightTranslate_mem_of_isCuspSubrep` (3,833 silo)
  ([topics/automorphicForm/SET-AF7.md](topics/automorphicForm/SET-AF7.md),
  [topics/automorphicForm/SET-AF8.md](topics/automorphicForm/SET-AF8.md)).
- **symptom**: the two rows look alike (3–5k silo, one headline, a long `private` prelude) and want
  opposite treatment. bigCell: **612 of 5,365 declaration lines (11%) already in the port**, 0
  within-file duplicates → a mechanical transcription is right, the prelude is the node's own. The
  cusp-subrep row: **3,015 of 3,811 (78%) already in the port**, 174 declarations, 183 of the 185
  matched copies public → a mechanical transcription would *manufacture* ~3,000 lines of duplicates,
  and the dedup that is supposed to clean them up would miss almost all of them, because the pin's
  names (`main`, `aux_*`, `tendsto_integral_mul_dconvWith`) have no port twin (FR-0103's name-anchor at
  six times the scale). The measured nets are 4,753 vs **757**.
- **cause**: the port has been built in waves whose engines were written for *other* rows and homed
  where the engine's subject lives (`RepTheory/TypeReproducer`, `RepTheory/ConvolutionLimit`,
  `Adelic/ArchApproxIdentity/{ArchInfra,EntryBall,Instantiate}`), so a later row can be 78% *supplied*
  under names that share nothing with its pin text. `port_advise`'s substitution block is the only
  instrument that sees this, and it must be run **before** choosing a strategy, not after.
- **rule**: one `port_advise` run decides the strategy for any large row —
  **overlap ≤ ~20% of declaration lines → mechanical whole-node port** (transcribe the text at the
  pin's names, keep it `private`, dedup after; SET-AF7);
  **overlap ≥ ~50% → composition** (import the engine, write only the new declarations, and expect the
  new part to be a small `aux_*` cluster; SET-AF8);
  in between, read the substitution list case by case. Either way the *price* is the net, never the
  silo — 5,407 lines cost 4,753 and 3,833 cost 757.
- **see also**: FR-0106 (the forecast is the set's closure return, not the sum of row returns) — the
  same two rows show why the instrument has to be picked for the question.
- **seen**: 2026-11-02, SET-AF7 §1 and SET-AF8 §1.

### FR-0110 — `move_dead.py`'s reference scanner dropped **capital** Greek letters, so `Φ_snd` read as unreferenced — **fixed 2026-11-02**

- **where**: SET-AF7's `move_dead --apply` on the 5,445-line mechanical transcription of the big-cell
  node ([topics/automorphicForm/SET-AF7.md](topics/automorphicForm/SET-AF7.md) §5).
- **symptom**: `move_dead --select dead` reported 18 declarations as unreferenced; four of them
  (`Φ_snd`, `Φ_snd_sigmaC`, `Φ_snd_apply`, and the bridge `mC_apply` they need) are **used**. Applying
  the cut broke the module and the four had to be restored by hand — a repair cycle on a green module.
- **cause, exactly**: the scanner's token regex was
  `[A-Za-z_\u03b1-\u03c9][\w'.!?\u2080-\u209c]*`. The **tail** is Unicode-aware (`\w`), but the
  **first character** admitted only ASCII plus *lowercase* Greek (α–ω, U+03B1–U+03C9), so a
  declaration whose name starts with a **capital** Greek letter — `Φ` is U+03A6 — never tokenised in
  a reference position: its users were not counted and it was reported dead. Lowercase Greek was fine
  (`ρR_pos` was *correctly* reported: it is genuinely dead), which is why the failure looks arbitrary.
  A name referenced only from an `attribute [local instance]` line read dead for the separate reason
  FR-0104 records (attributes are not declaration bodies).
- **fix** (this session): the first-character class is now `[^\W\d]` (every Unicode word character
  except a digit) with an explicit `_\w*` alternative, so capitals and subscripts tokenise. Verified
  three ways: the same `move_dead --dry-run` on the module now reports **0 declarations / 0 lines**
  (the 12 real ones were shelved); a synthetic probe with `Φ_used`/`Φ_unused` reports exactly the
  unused one; and the shelf's 118 copied premises still resolve.
- **rule that outlives the fix**: `move_dead`'s dead set is a **proposal**, never a fact — and the same
  standing as `dedup`'s clusters. Before `--apply` on a transcribed module, `grep -c` the reported
  names against the source (one line, the whole set), and never hand-cut spans (FR-0108). Two tool
  bugs have now been found this way (FR-0104, this one), both in the *liveness* direction — the
  direction whose failure mode is a broken module rather than a missed shelf.
- **see also**: FR-0104 (attribute-only references), FR-0108 (span cutting), playbook §3.8 (the shelf
  rule).
- **seen**: 2026-11-02, SET-AF7 §5.


## FR-0111 [method] [tooling] — `dedup`'s `shape` tier paired 31 declarations on a 5,000-line transcription and **6 of them did not substitute**: factor the real duplicates out, but test each one at its call site

- **where**: the sharing pass after SET-AF7's landing
  ([topics/automorphicForm/SET-AF7.md](topics/automorphicForm/SET-AF7.md) §5.1), the big-cell module
  against the whole `AutomorphicForm/Adelic` tree.
- **symptom**: `dedup --cross --tier name,shape,body` reported **31 clusters / 414 removable lines**
  against five port modules. Twenty-five were true duplicates: 13 `ArchKFiniteFamily.LevelInvariance`
  declarations held `private` (promoted in place, and the checker *verifies* them through its
  pin-private fallback — that module went 1 ok → 14 ok) and 12 `InducedSectionFlat` ones already
  public (their copies deleted, the namespace opened). **Six were not**, and each one failed at the
  call site, not at the name: the port's twin took `(h₁) (h₂)` where the pin's use rewrote with one
  argument; the pin's `continuous_adelicArchGLInclAt` binds `(F) (w)` *explicitly* while the port's
  binds `(w)`; the port's `norm_symm_ringEquivRealOfIsReal` takes an `x : ℝ` where the pin feeds a
  point-free form to `IsRowIsometry.map_ringEquiv`; the port's `adelicWeyl_inv'` lives in
  `WeylIntegrable` while the pin rewrites bare; and `rTrans` is a three-line spelling of a public def
  that takes `F` explicitly.
- **cause**: the `shape` tier normalises binder *spelling* and the conclusion, not the argument
  *demands* of the call sites (playbook §5's recorded caveat: "`dedup.py --tier shape` ignores
  instance arguments … verify at the call sites before deleting one"). On a 400-declaration module the
  caveat is not a footnote: it is a ~20% false-positive rate.
- **rule**: run the sharing pass **top-down by cluster size** and make each cluster an experiment —
  substitute, compile, keep it only if the module is still green. Promote what is shared *in the home
  the mathematics names* (here the engine module, at the pin's names, which also earns checker rows),
  delete only the copy, and keep trivial helpers private even when a twin exists: a five-line
  coercion law or a three-line `fun y => ψ (y * g)` does not deserve a public name, and forcing one
  re-qualifies call sites for nothing.
- **seen**: 2026-11-02, SET-AF7 §5.1 (5,445 → 5,176 lines; 31 → 6 clusters).


## FR-0112 [method] [tooling] — a `#check` surface probe proves that *names* resolve, not that the **instances** the proofs need are synthesizable

- **where**: SET-AF8's manager layer
  ([topics/automorphicForm/SET-AF8.md](topics/automorphicForm/SET-AF8.md) §0.5), the "verified import
  surface" probe `tmp/af8-surface.lean` (~90 `#check` lines) handed to the worker as the set's
  first-line defence.
- **symptom**: the probe compiles silently, and the module still does not elaborate: the pin's
  `p2m_reactivate "…KAvArch"` is load-bearing because `compactSpace_Kw` and the `muK`
  probability/Haar facts are **`open scoped`** instances of `ArchInfra`. The worker found it, added one
  `open scoped ArchInfra`, and no declaration moved. Every name the probe listed was present.
- **cause**: `#check` elaborates a term; instance synthesis happens inside a *proof* (or inside a
  statement whose types carry instances). A probe over `@name` checks the constant, never the
  resolution of `CompactSpace (Kprod F)` or `IsFiniteMeasure (muK F)`, and a `scoped` instance is
  invisible unless activated.
- **rule**: a surface probe carries, in addition to its `#check`s, **one `example` per instance the
  proofs will need** (`example (F) [Field F] [NumberField F] : CompactSpace (ArchInfra.Kprod F) :=
  inferInstance`), with the same `opens` the module will use, and at least one `example` whose
  *statement* is the set's headline. `#check` says "the name exists"; only an `example` says "the
  module will elaborate".
- **seen**: 2026-11-02, SET-AF8 (worker report, deviation 1).


## FR-0113 [method] — when a name is missing, `#check` the *candidate replacement* too; "the obvious repair" of a pin call is how an order hands a worker a wrong trap

- **where**: WORKORDER-AF8 §3.3, written by the manager from a single failed `#check`, and corrected by
  the worker at the landing.
- **symptom**: the order said "`Continuous.comp_continuous` does not exist in this mathlib;
  `hff.1.comp_continuous (continuous_mul_const k)` is `(hff.1).comp (continuous_mul_const k)`". The
  first half is true; the second is false, and the pin's spelling was already right — `hff.1` is
  `IsLocallyConstant ff`, and `IsLocallyConstant.comp_continuous` is the continuity lemma. The
  suggested repair does not elaborate.
- **cause**: the manager checked the *absent* name and inferred the replacement from the shape of the
  call instead of checking it — one `#check @IsLocallyConstant.comp_continuous` (~2 s) would have
  settled it. An order that states a trap with confidence spends the worker's time twice: once to hit
  it, once to disprove it.
- **rule**: a trap is written in one of two forms only — *"`X` is not in the port/mathlib; the port's
  name is `Y`, `#check` it"* or *"`X` fails here; `Y` elaborates (checked)"*. Never a syntactic
  repair inferred from a missing name. And a worker may treat a trap as a *claim to verify*, exactly
  as it treats a pin statement.
- **seen**: 2026-11-02, SET-AF8 (worker report, deviation 3).


## FR-0114 [tooling] — a `spec-pin:` wire marks the whole pin **file** ported, so a module skeleton wired at creation moves `needed` by the in-flight row

- **where**: the AF9 scoping read, taken while SET-AF8 was in flight; the manager had wired the new
  module's header (its own practice: the worker must be able to run `check_port` from its first file).
- **symptom**: the read returned `needed 894 / 358,716` and `frontier 1,521 / 768,650` — SET-AF8's
  *post-landing* arithmetic — while only 8 of the row's 25 declarations existed. `--unport
  AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep` restored `895 / 362,549` and
  `1,520 / 764,817`, i.e. SET-AF7's post-landing table to the line. `--selfcheck` printed PASS: it
  checks the opposite direction (a `Thm_` source claiming nodes nothing covers).
- **cause**: `frontier.py`'s `sources` tier reads `spec-pin:` headers (`wired_sources()`), so one wire
  ports every node of that pin file at once. That is intentional — it is what makes the checker
  handoff (`spec-pin:` in, `PORT_FILES` out) keep a module on the diffed frontier — but it means the
  read is **ahead of the tree** during any dispatch whose module is wired before it is finished.
- **rule**: a scoping read taken during a dispatch passes `--unport <every in-flight row>` and says so
  in the brief; a read taken after the landing is the instrument's. Quote which of the two produced a
  figure. Do **not** "fix" this by stripping the wires from a skeleton — the worker needs them to run
  the checker while it works.
- **seen**: 2026-11-02, the AF9 scoping read
  ([topics/automorphicForm/SET-AF9.md](topics/automorphicForm/SET-AF9.md) §0).


## FR-0115 [method] — a worklist's "already in the port" column is an *existence* claim, not an *importability* claim: the copy can sit **downstream** of the home

- **where**: SET-AF9's two orders
  ([topics/automorphicForm/SET-AF9.md](topics/automorphicForm/SET-AF9.md) §5.1), the per-declaration
  worklist of `build/af9-worklist.py` that priced the set at ≈1,380 lines.
- **symptom**: eight of the 911 "already in the port" declaration lines could not be imported. Row 2's
  rotation prelude (`rotMat`, `det_rotMat`, `rotGL`, `rotGL_coe`, `rotGL_mem`, `rotSO`,
  `archWeightOneℝ_rotSO`) *is* the port's — under `TSRot.*` in `Cusp/CutWeightDecomposition.lean`,
  which imports `IsotypicCuspSpace` and sits **downstream** of `ArchCasimir.lean`, the home the row
  belongs to; row 6's `norm_ringEquivComplexOfIsComplex_symm` lives in
  `WeylIntegrable/LatticeEstimates.lean`, outside the row's closure. Both were re-stated `private`
  (8 declarations) rather than pulling an import upward into a zero-importer hub.
- **cause**: the worklist maps a pin declaration to *some* port declaration with the same statement
  (`port_advise`'s substitution tier is module-blind). Import direction — the rule that has now cost
  three sets (FR-0037, FR-0038 and this one) — is a property of the **pair** (home, copy), not of the
  declaration, and no single-declaration instrument can see it.
- **rule**: for every row of a set's worklist, read the "already in the port" line together with the
  copy's **module**, and drop the row from the import column when that module is at or below the home
  in the import graph. The order should say so explicitly ("imported as-is" vs "re-stated, because the
  port's copy is downstream") so the worker is not blamed for a worklist artefact, and the brief's net
  figure should count those lines as work.
- **seen**: 2026-11-02, SET-AF9 (worker report §6.1–6.2 and deviation 4–5).


## FR-0116 [method] [tooling] — "delete the copy, import the home" fails when the home is a **transcription namespace**: `dedup --cross` flags the pin's own per-file prelude copies, and the import does not even make the name resolve

- **where**: the AF10 landing ([topics/automorphicForm/SET-AF10.md](topics/automorphicForm/SET-AF10.md)),
  `ArchCasimirComplex.lean` against `ArchCasimir.lean`: `dedup --cross` reported 6 clusters, of which
  4 are the ℝ/ℂ twins (`U`, `D1`, `D2`, `conjCLM` — type-distinct, not removable) and 2 are `glArch_ext`
  and `rightTranslate_mul`, byte-identical `private` re-statements of declarations the port holds in
  `ArchCasimir.lean`.
- **symptom**: the rule "duplicate → delete the copy and import the home" was applied and **reverted**.
  The port's copies do not live at `AutomorphicForm.glArch_ext`; they live at
  `AutomorphicForm.Elem17LR.glArch_ext` and `…OsAlg17.rightTranslate_mul` — inside the *transcription
  namespaces* of the real engine (`Elem17LR`, `OsAlg17`, `CasCore17`, `CommAway17`, …), which exist only
  because the pin's generated files wrapped each prelude in its own namespace. Adding
  `import …ArchCasimir` pulls a 1,640-line engine into the complex module and **still** leaves the
  unqualified references (`glArch_ext` inside `namespace ElemC`) unresolved: six errors, and the cure is
  requalifying every call site. Two 5-line `private` re-statements are the cheaper, clearer shape.
- **cause**: the dedup instrument is name- and statement-anchored, so it cannot see that a "home" is a
  *transcription artefact* rather than a subject-level API. The port's `-- pin:`/`spec-pin:` discipline
  keeps the pin's names, and the pin namespaces are part of that: a helper that the pin copies into
  every file of a family stays a per-file copy in the port unless someone promotes it *out* of the
  transcription namespace into a subject module (which is what SET-AF6 did for the chart halves, and
  what would be needed here).
- **rule**: a `dedup --cross` cluster whose two sides sit in *different pin-derived namespaces* of the
  same development is the pin's own prelude duplication, not a port defect: keep it, record the
  namespace pair and the pin line, and treat "promote the helper out of the transcription namespace"
  as a separate refactor (it needs its own home, its own wire and a cascade budget). Never apply the
  delete rule to it without measuring the call sites: the import alone does not resolve the name.
- **seen**: 2026-11-02, SET-AF10 (worker report §4, manager's reverted experiment).


## FR-0117 [tooling] [method] — a `Def_` gate can be **free by the module-level scan and expensive by the row-level one**: `port_advise --with-defs`'s closure is premise-shaped, and a definition spelled only in a row's *statement* still gates it

- **where**: SET-AF11's scoping ([topics/automorphicForm/SET-AF11.md](topics/automorphicForm/SET-AF11.md)
  §3: "the definition gate: complete, no `Def_` node"), rows 6 and 7, at dispatch.
- **symptom**: `spec/gate_scan.py --pin Definitions/Def_UnramifiedWhittaker_HeckeRecursion.lean` against
  the two `SmoothCuspRealizationAt.` wrappers reports **4 missing from the port** (`placeEmbed`,
  `repSome`, `repInf`, `scalarPi`) — and those names are *in the rows' statements*, so the rows could
  not be stated at all. The scoping had run the gate over "the five `Def_` modules of the nine
  wrappers' closure" and found 0 missing.
- **cause**: the closure that produced the five modules is the *premise* closure of the rows, and
  `UnramifiedWhittaker` entered by a different route — the rows' `S_` files import it, and the
  statement names come from there. A `Def_` node pulled in by an `S_` file's import rather than by a
  premise of the headline is invisible to a premise-shaped closure, while being maximal for the work:
  the statement does not elaborate.
- **rule**: before declaring a set's definition gate free, run `gate_scan` **per row** over *every*
  `Definitions/` module any of the set's `S_` files imports (union of the `import` lines, not only the
  premises), and treat "0 missing" as a claim about that union, not about the shelf's reading. The
  cheap check is the statements probe: state all headlines against the intended home before the
  order is written — it catches this class in one compile.
- **seen**: 2026-11-02, SET-AF11 dispatch (manager's layer, `RepTheory/LocalLanglands/UnramifiedWhittaker.lean`).


## FR-0118 [tooling] [method] — the **import cycle** of a hub: a `Definitions/` module's faithful `import` can put the *coefficient* above the *character*, and then the coefficient's API module cannot import the trace

- **where**: SET-AF11, `AutomorphicForm/Adelic/WhittakerCoefficient.lean` gaining
  `import NumberTheory/NumberField/AdelicTraceFin`; the cycle is
  `WhittakerCoefficient → AdelicTraceFin → AdelicTraceProducer → StandardGlobalAddChar →
  StandardGlobalAddCharRat → WhittakerCoefficient`.
- **symptom**: `lake env lean` on the module aborts with `import … failed, environment already
  contains 'AutomorphicForm.IsPrincipalInvariantAddChar'` (or, before the split, `has already been
  declared` on all eight of the module's own declarations) — Lean names the *root* module, which
  reads like a duplicate-declaration bug in your own file. A stale `.olean` of the edited hub makes
  it persist after the fix: `lake env lean` writes no `.olean`, so the *old* import edge survives in
  the hub's olean until `lake build <hub>`.
- **cause**: the pin's `Def_NumberField_StandardGlobalAddCharRat.lean` imports
  `Def_AutomorphicForm_WhittakerCoefficient.lean` — verbatim transcribed — for **two predicates**
  (`IsPrincipalInvariantAddChar`, `IsGlobalAddChar`) that the coefficient file also happens to hold.
  A `Definitions/` file with two subjects becomes, on the port's side, two modules; until they are
  split, whichever subject is *upstream in the pin* drags the other one's whole import closure with
  it, and the closure now reaches back.
- **rule**: when a module must gain an import from the `NumberTheory/NumberField/` character side,
  read the *port's* import DAG for the pin file the module transcribes and split it by subject before
  adding the import: the predicates about a character belong below both the coefficient and the
  standard-character development, not inside either. And after rewiring a hub's import, `lake build`
  the **hub** (not just `lake env lean`) — the `.olean` is the thing every other module reads.
- **seen**: 2026-11-02, SET-AF11 dispatch; the split is `NumberTheory/NumberField/GlobalAddChar.lean`
  (4 declarations, wired, 4 ok), the hub handed over at 44 ok / 0 mismatch / 0 missing.


## FR-0119 [tooling] [method] — "the port already has it" is a claim about the **import closure**, not the file tree: an in-file pin prelude can be unreachable from the module being written

- **where**: SET-AF11, `AutomorphicForm/Adelic/WhittakerCoefficient.lean`, all nine rows.
- **symptom**: four names the order lists as *already in the port* — `countable_principalSubgroup`,
  `distribHaarChar_algebraMap`, `isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox`, and (in a
  different module) the pin's row-5 `gl_ext` — are `unknownIdentifier` under `lake env lean` on the
  module. `FltWs24.AdelicModulusOne.countable_principalSubgroup` lives in
  `NumberTheory/AdelicHaar/ProductFormula.lean`; `NumberTheory/AdelicModulus.lean` (which holds the
  other two) and `AutomorphicForm/Adelic/MaximalCompactFactors.lean` are *not* in the module's
  transitive `import` closure (53 `FLTForHuman` modules), although they are in the tree.
- **cause**: "the port has it" was measured with a grep over the tree; the compiler only sees the
  closure. `MaximalCompactFactors` shows the trap in its sharpest form: it *imports*
  `AdelicMaximalCompact`, so `gl_ext` is upstream-side of the module and cannot be imported without
  adding the arrow the wrong way.
- **rule**: before writing a row, compute the module's transitive `import` closure (a 20-line walk
  over `^import FLTForHuman`), and check every "already in the port" name against *that* list, not
  against `grep -r FLTForHuman/`. For a helper that exists only outside the closure, prefer the
  closure-internal substitute when there is one (row 5 used `ArchDerivCasimir.eq_of_glArch_eq_of_glFin_eq`,
  which is imported, instead of the pin's 15-line `gl_ext`); otherwise it is a blocker, not a
  transcription.
- **seen**: 2026-11-02, SET-AF11 (rows 1, 4, 5); the row-4 half was reported as a blocker and fixed
  by the manager adding `import FLTForHuman.NumberTheory.AdelicModulus` (the amended order §0.5).


## FR-0120 [tooling] — `lake env lean file.lean` writes **no** `.olean`, so a probe that does `import <module>` reads the *last built* environment, not the file you just edited

- **where**: SET-AF11, all name- and statement-probes over
  `FLTForHuman/AutomorphicForm/Adelic/WhittakerCoefficient.lean` after the module gained
  `import …AdelicModulus`.
- **symptom**: `tmp/probe-names.lean` (`import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient`)
  reports `unknownIdentifier` for a name that a fresh `lake env lean` on the module itself accepts,
  and the statements probe keeps accepting the module's *old* set of declarations. The module's
  `.olean` in `.lake` predates the edit; every `import`-ing probe loads it.
- **cause**: `lean` on a file elaborates it but does not write its `.olean`; only `lake build` does.
  So the edit loop (`lake env lean <module>`) validates the source while probes validate the stale
  artifact — the two disagree exactly when the edit *adds* something (a name, an import edge).
- **rule**: reachability of a name from module `M` is answered by `lake env lean M` (the compile) or
  by `lake build M` (which also refreshes what the probes see) — never by a probe whose import is
  `M`. When a probe must see the current environment, `lake build` the module first (serialized with
  the usual `flock`), or have the probe import the *source* module that declares the name directly.
- **seen**: 2026-11-02, SET-AF11 (this cost one false "the manager's import did not work" round).


## FR-0121 [style] [method] — `linter.style.haveILetI` is live here: the pin's `letI := adeleBorel` / `haveI : μ.Regular := …` proof preludes must become one file-local `attribute [local instance]` block

- **where**: SET-AF11, every `S_` file's preamble: `attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar`,
  plus per-proof `letI := adeleBorel (𝓞 F) F`, `haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F`,
  `haveI : (adelicAddHaar (𝓞 F) F).Regular := Measure.regular_addHaarMeasure`.
- **symptom**: transcribed verbatim, each `letI`/`haveI` in a *proof* emits
  ``warning: The goal is a proposition, so `have` is preferred over `haveI` `` — fatal under the
  "zero warnings, no `set_option`" rule, and `set_option linter.style.haveILetI false` is forbidden.
  The port's module has no such block to inherit (the pin's is in the wrapper files).
- **cause**: the linter is on by default in this toolchain, and the pin's measure-theory prelude is
  *instance* setup, which the port registers with `attribute [local instance]` (a command, not a
  proof step) — the port's `NumberField.AdelicHaar.adeleBorel` &c. are `def`s, not instances, so
  something must register them.
- **rule**: put **one** `attribute [local instance]` block at the top of the appended region, listing
  `adeleBorel`, `borelSpace_adeleBorel`, `isAddHaarMeasure_adelicAddHaar` (and, when a row reaches
  `distribHaarChar_mul`, `FltWs24.regular_adelicAddHaar`); then delete every `letI`/`haveI` from the
  transcribed proofs. Where an instance is needed only for a `def`'s `letI` (`whittakerCoefficient`
  itself), nothing is needed — the definition carries it. A `private instance` re-export
  (`Countable ↥(principalSubgroup)`) is the other shape that stays silent.
- **seen**: 2026-11-02, SET-AF11 (rows 1–9; the subagent porting rows 6/7 hit it first, on the pin's
  `letI := adeleBorel (𝓞 F) F` at `S_…sum_whittakerCoefficient…:102`).


## FR-0122 [api drift] — mathlib `v4.34.0` renames that the pinned `S_` proofs spell the old way: each is a *warning*, and a warning fails the gate

- **where**: SET-AF11 transcription, `AutomorphicForm/Adelic/WhittakerCoefficient.lean`.
- **symptom** (four, all silent-blocking under "zero warnings"):
  * `Measure.regular_addHaarMeasure` (pin row 4 `haveI : (adelicAddHaar …).Regular := …`) **does not
    exist** in `v4.34.0`; the port's copy is `FltWs24.regular_adelicAddHaar F`, and `Regular` is an
    instance argument of `distribHaarChar_mul`, so the transcribed `rw [← distribHaarChar_mul …]`
    fails without it.
  * `integral_finset_sum` is deprecated in favour of `integral_finsetSum` (pin row 2).
  * `if_pos` is deprecated in favour of `ite_eq_left` (pin row 5, the `_hμbox` rewrite).
  * `add_left_injective` / `add_right_injective` are the *other* side from what the pin's
    `Set.preimage_image_eq (adelicBox F) (add_left_injective x)` needs for `fun u => u + x`: the
    rewrite silently targets `fun u => x + u` and fails with a pattern-not-found on the set integral.
- **cause**: the pin is on Lean 4.33.1 / mathlib v4.33.0; the port is `v4.34.0`. Deprecation warnings
  are warnings in both, but the pin's build does not run with "zero warnings" as a gate.
- **rule**: when transcribing, treat every deprecation hint as a rename *and* grep the port for a
  same-subject copy before inventing one (`FltWs24.regular_adelicAddHaar` was already there, in the
  closure, one import away). For the injectivity pair, state the intended function explicitly
  (`add_right_injective` for `· + x` in this version) and re-check the `conv_lhs` target.
- **seen**: 2026-11-02, SET-AF11 (rows 1, 2, 4, 5).


## FR-0123 [method] — the checker hashes the **signature text**, so a headline appended to a module with a section `variable (F : Type)` must still spell `(F : Type) [Field F] [NumberField F]` out, and must copy the wrapper's *qualified* names

- **where**: SET-AF11, appending the nine headlines to `WhittakerCoefficient.lean`, whose
  `namespace AutomorphicForm` opens with `variable (F : Type) [Field F] [NumberField F]` at line 108.
- **symptom**: two traps, both silent at compile time and only visible in `check_port`'s hash tier:
  (1) relying on the section variable makes `F` an *auto-bound* parameter — the statement elaborates
  and proves, but its `nhash` differs from the wrapper's, so the row is `missing`; (2) the wrappers
  are not uniform in spelling — row 3/4 say `IsDedekindDomain.HeightOneSpectrum`, rows 1/2 say
  `HeightOneSpectrum`; row 4 says `AdelicBox.adelicBox F`, the others `adelicBox F`.
- **cause**: `statement_db.nhash` is `sha1` of the signature with comments stripped and whitespace
  collapsed — tokens, not terms. A section variable and an explicit binder are different tokens; a
  qualified and an unqualified name are different tokens. (`check_port` therefore diffs *text*, and
  `private` is what keeps helpers out of the diff.)
- **rule**: transcribe each headline's binders **from the wrapper** (or from the verified statements
  probe), not from the pin's `S_` file and not from the module's context; when the module has a
  section variable with the same name, shadow it with an explicit `(F : Type) [Field F] [NumberField F]`
  (Lean accepts the shadowing; verified here). Then re-run `check_port --force` — it is the only
  gate that reads the hash.
- **seen**: 2026-11-02, SET-AF11 (rows 1–9; the probe file already carried the right spellings,
  which is what made the check a diff rather than an investigation).


## FR-0124 [tooling] — the gate's own command line: `dedup.py --module` and `move_dead.py --source` do **not** take a module name the same way

- **where**: SET-AF11 gate 5, run verbatim from the order §3.5:
  `python3 ../tools/deps/dedup.py --within --module <module>` and
  `python3 ../tools/deps/move_dead.py --source <module> --target /dev/null --dry-run`.
- **symptom**: `dedup.py --module FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient` works
  (dotted module name), but the same dotted name in `move_dead.py --source` crashes with
  `FileNotFoundError: 'FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient'` — it treats
  `--source` as a *path*, so it needs `--source FLTForHuman/AutomorphicForm/Adelic/WhittakerCoefficient.lean`.
  Both flags are documented as "module" in their `--help`.
- **cause**: the two tools resolve their argument differently (`dedup` joins the module path from the
  dotted name; `move_dead` opens `--source` directly). A dotted name is only a valid path when the
  module sits at the root of the tree.
- **rule**: quote the gate with the *file path* for `move_dead` and the *dotted name* for `dedup`, or
  just pass the path to both (`dedup --module` accepts it too) — and when a gate tool tracebacks with
  `FileNotFoundError` on its own subject, try the other spelling before suspecting the module.
- **seen**: 2026-11-02, SET-AF11 (0 clusters / 0 dead either way; the crash is argument-only).


## FR-0125 [method] [style] — a port name carrying a **pipeline token** is not a dependency new code may take: the façade fact is wrapped or re-proved at a token-free name, never cited

- **where**: SET-AF11's landed `AutomorphicForm/Adelic/WhittakerCoefficient.lean` (caught at AF12's
  dispatch): the module's local-instance block cited `FltWs24.regular_adelicAddHaar` and
  `FltWs24.AdelicModulusOne.countable_principalSubgroup` — two names of the pin-chapter namespace
  `FltWs24` in `NumberTheory/AdelicHaar/ProductFormula.lean`, one of the four "pin-chapter
  namespaces still in use" recorded in [../CARRY-FORWARD.md](../CARRY-FORWARD.md) (`Cleanup families`).
- **symptom**: the module compiles and checks 13/0/0 — nothing mechanical objects. The defect is in the
  *surface*: a new module has taken a name whose namespace is a pipeline chapter label, so the label
  now has a consumer that the cleanup wave would have to chase, and the port's naming rule ("generated
  name tokens are rectified, not carried") is broken by the newest code rather than the oldest.
- **cause**: `Measure.regular_addHaarMeasure` is gone in mathlib `v4.34.0`, so the port's copy of the
  regularity fact lives in the façade (`FltWs24.regular_adelicAddHaar`, three lines), and the
  countability of the principal subgroup likewise (`FltWs24.AdelicModulusOne.countable_principalSubgroup`).
  Both read as "already in the port, just import it" — the same shape as a legitimate substitution, but
  the *name* is part of the cost.
- **rule**: before citing a port declaration from new code, read its **namespace**, not only its
  statement. If the namespace is a pin chapter label (`FltWs24`, `M4aS4`, `P6B`, `M4aLocalCFT`, or any
  `…C41`/`…17`-style id), do not cite it: either state the pin's own prelude locally (it is the pin's
  text, and a shim for a removed mathlib lemma is a shim either way — `regular_adelicAddHaar` is three
  lines, `countable_principalSubgroup` six), or make the token-free wrapper in the façade's own
  token-free module (`NumberTheory/AdelicModulus.lean`) the thing you import, and let the
  rectification wave move the label. A cleanup family is a reason to *avoid* the name, never to
  spread it.
- **seen**: 2026-11-02, SET-AF11 → SET-AF12 (manager's fix: the two references replaced by two local
  `private instance`s proved in the module; the module was re-checked at 13 ok, the statements probe
  re-run, and the facade's remaining reference sites are again only its own).


## FR-0126 [checker] [style] — wiring a module that still carries `-- pin:` markers reports **every** marked declaration as `MISSING … (marker)`; and a "load-bearing" `haveI` is fixed with `have`, not with a suppression

- **where**: the `FltWs24` naming sweep (CARRY-FORWARD, `Cleanup families`), on
  `NumberTheory/AdelicHaar/ProductFormula.lean` and `NumberTheory/AdelicModulus.lean`.
- **symptom (a)**: with `spec-pin:` lines added but the grandfathered `-- pin: name (file:line)`
  comments left in place, `check_port --force` reports **8 of 9** declarations `MISSING … (marker)`
  in the engine and **3 of 6** in the façade, on a module whose statements are byte-faithful and
  whose wire names the right files. Stripping the markers in the same edit turns the same wire into
  **9 ok / 0 mismatch / 0 missing** and **6 ok / 0 / 0**.
- **cause**: the marker tier resolves a declaration by the marker's *pin name*, looked up in the
  wire — not by the port's statement — so a marker naming a pin helper the port states elsewhere
  (or under a different last-name path) can never resolve, and the policy since 2026-11-02 is that
  the header is the tracking and markers are stripped when the module is touched. A marker's
  `(file:line)` is informational; it does not widen the wire.
- **symptom (b)**: `linter.style.haveILetI` fires on every `haveI`/`letI` in a *tactic* proof whose
  goal is a proposition, and the tempting reply is `set_option linter.style.haveILetI false`. That is
  the wrong reply: mathlib's own linter docstring states that in Lean 4 **`have` and `let` register
  local instances themselves**, so `have`/`let` is a drop-in replacement and the suppression hides
  nothing but a style difference. (A suppression *is* justified for a **term-mode** `letI` inside a
  definition body — `letI := pins.nS` before `∫ … ∂pins.ν` — where `let` changes the elaborated term.)
- **rule**: when a module is wired (for any reason), strip the `-- pin:` markers and put every file
  they named in the header in the same edit, then read `MISSING` as a real gap. When the `haveILetI`
  linter fires in a proof, write `have`/`let`; keep a file-wide or narrowly-scoped `set_option` only
  where the binding is in a term, with the reason in the header.
- **seen**: 2026-11-02, the `FltWs24` sweep (engine 9 ok, façade 6 ok, both silent with no
  suppression; CARRY-FORWARD's table now has two live labels, `M4aS4` and `M4aLocalCFT`).


## FR-0127 [style] [api drift] — the pinned `S_` proofs transcribe, but "zero warnings" forces five mechanical repair classes (and one of the linters' own hints is unsound)

- **where**: SET-AF12 order A, `AutomorphicForm/Adelic/ArchWhittaker.lean` (both `S_` files transcribed
  verbatim: the pin's real row at `S_…gl2Real…:114–347`, the complex row at `S_…gl2Complex…:19–695`).
  Under the port's gates the two rows compile at once but emit **14 + 49 warnings**, all style/API,
  none mathematical.
- **symptom** (each fails the "zero warnings" gate; fixes are proof-shape only):
  * `linter.unusedTactic` on `all_goals first | rfl | skip` (pin real `:221`, `:227`; complex `:563`,
    `:568`, `:580`, `:585`, `:713`, `:718`, `:759`, `:763`, `:984`, `:989`). Where the linter fires,
    no goal was closed by `rfl` and the whole line is a no-op: deleting it leaves the following
    bullets on the same goals. Do **not** delete the unflagged occurrences (e.g. the `hpow` block,
    pin real `:294`/complex `:967`), where `rfl` does close a goal and the bullets then refer to the
    rest.
  * `linter.unnecessarySeqFocus` on `convert … using 1 <;> first | rfl | simp` (pin real `:191`,
    `:325`, `:330`, `:355`; complex `:520`, `:686`, `:692`). The hint "use `(tac1; tac2)`" is
    **unsound**: with `;`, `first | rfl | simp` picks one branch against the whole goal list and
    commits it to every goal, so the goal that needed `simp` is left unsolved (measured: `;` broke
    `hasDerivAt_xIw` and the `hl` block). The shape that both silences the linter and keeps the
    per-goal choice is `convert … using 1` on its own line followed by `all_goals first | rfl | simp`.
  * `linter.unusedSimpArgs` on `simp [hre]` (pin complex `:569`, `:586`, `:719`): `simp` alone closes
    the goal; drop the argument (the `hre` hypothesis stays used in the sibling bullet, so the
    `linter.unusedVariables` gate stays quiet).
  * `linter.unusedVariables` on `aT_mul_flowH`'s `(hy : 0 < y) (hs : 0 < s)` (pin complex `:134`). The
    binders are part of the **hashed signature** (FR-0123), so `_hy`/`_hs` is not an option; reference
    them in the proof (`have _ : 0 < y := hy`) and keep the pin's names.
  * deprecations `if_pos`/`if_neg`/`dif_pos`/`dif_neg` → `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/
    `dite_eq_right` (pin complex `:835`, `:838`, `:843`, `:845`, `:872–:875`, `:895–:898`, `:968`;
    16+ sites). FR-0122 recorded `if_pos` once from AF11; the whole family bites in this set. Note
    the replacements take the hypothesis as an argument (`ite_eq_left h1`) in `rw` chains, and
    **`rw [ite_eq_left]` with no argument still works**, leaving `⊢ p` as a side goal exactly as
    `rw [if_pos]` did — which is why the pin's `rw [if_neg]` / `intro h` pairs port unchanged.
- **cause**: the pin is built without `mathlib`'s full linter set and on mathlib v4.33.0; the port's
  modules run with `linter.style.*`, `linter.unusedTactic`, `linter.unnecessarySeqFocus`,
  `linter.unusedSimpArgs`, `linter.unusedVariables` and deprecation warnings live, and any one of
  them fails the module. The repairs are all local rewrites of the proof script; none changes a
  statement (checked: `check_port` 69 ok / 0 mismatch / 0 missing after the repairs).
- **rule**: transcribe the statement verbatim and the proof *shaped* — run the edit loop
  (`lake env lean -DautoImplicit=false -DmaxHeartbeats=200000`) and treat every warning as a defect
  to repair, not to suppress (no `set_option linter.…` in a module). When a linter suggests a
  tactic rewrite, test it: `unnecessarySeqFocus`'s `;` hint is wrong for goal-list-sensitive
  second tactics (`first`, `all_goals`, `try`).
- **also (scoping gotcha, Lean core)**: `open Foo in` binds to the *next declaration*; a
  section doc-comment `/-! … -/` placed between them swallows the scope, and the declaration then
  fails with `Unknown identifier` on every unqualified name of `Foo` (measured on the real row:
  `splitTorusGL2_mul`, `lowerUnipotentGL2_iwasawa`). Either drop the comment between them or use a
  plain `open Foo` before the comment.
- **seen**: 2026-11-02, SET-AF12 order A (real row 14 warnings, complex row 49; both silent after).


## FR-0128 [method] [tooling] — a substitution row can point at the **`private` twin**: read its `port` *module*, not only its `port_name`; and a pin `S_` file that reads "flat public" still has `private` preludes

- **where**: SET-AF13's pricing (`port_advise`/`port_plan` on the four flat-Eisenstein rows) and its
  first dispatch.
- **symptom**: three advise rows flagged as "not importable" — `norm_finComponent_le_one_of_mem`,
  `finLocalHeight_one'`, `hpow` — of which only one was genuinely private: the tool's row for
  `norm_finComponent_le_one_of_mem` named `AutomorphicForm.BigCellExpansion.Height.norm_finComponent_le_one_of_mem`
  (a `private` copy), while `NumberField/AdelicHeight.lean:442` holds a **public** copy of the same
  statement (`AdelicHeight.norm_finComponent_le_one_of_mem`). Importing the public one saves the 13-line
  restatement and a dedup cluster, and the advise file cannot see it because the two copies share a
  last name and the name tier resolves one of them.
- **cause**: `port_advise` is name-anchored and picks one module per last name; when the port holds
  two copies — one private, one public — the row's `port` field is whichever the index hits first. The
  `port_name`/`port` pair is the only place the choice is visible, and it is easy to read past.
- **second half**: the set's design claim "these `S_` files are a flat public surface" is a claim about
  a *sweep*, not about every declaration: the same files carry `private theorem`s (in this set:
  `exists_bound_on_unitBox_family_j1`, `hpow`, `finLocalHeight_one'`, `norm_finComponent_le_one_of_mem`).
  Making one of those public in the port produces a checker `MISMATCH` that no re-spelling fixes, because
  the pin's statement is spelled with the file's `section` variables (`variable {A : Type*} [CommRing A]`)
  and inlining them changes the text (FR-0123). The faithful and cheap answer is `private`.
- **rule**: for each advise substitution, read `port` (the module) and `port_private` together; if the
  named copy is private, look for a public copy of the same last name before pricing a restatement.
  And when a set orders "helpers public", qualify it: **public where the pin is public, private where
  the pin is private** — the checker's text diff decides, not the set's aesthetics.
- **seen**: 2026-11-02, SET-AF13 (worker's two questions at its first row; the manager added the
  fourth mathlib import `Mathlib.Analysis.Complex.LocallyUniformLimit`, which the pin's `import Mathlib`
  had been hiding).


## FR-0129 [pin-gap] [definition-gate] — a pin `S_` proof may rest on a `Def_` module the set's gate never listed: `Def_AutomorphicForm_FnTwist`

- **where**: SET-AF13's dictionary row, proof of `isKfSmooth_mul_hpow` (pin
  `P2M/Sol/S_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection.lean:194`),
  which calls `isSmoothVector_rightTranslationFn_mul` — defined only in
  `Definitions/Def_AutomorphicForm_FnTwist.lean:67` (pin line 7 of that `S_` file's imports).
- **symptom**: the four wrappers' closure lists eight `Def_` modules and `gate_scan` reports 0 missing
  in each, but the *proof* imports a ninth (`FnTwist`) that the port has not ported. The port's
  `RepTheory/SmoothVectors.lean` has no product-smoothness lemma (it has `.add`, `.smul`,
  `.const_smul`, `isOpen_coe_inf_stabilizer`, but not `mul`), so `IsKfSmooth (fun g => φ₀ g * hpow t g)`
  cannot be closed by import.
- **cause**: the set's definition gate scans the *statements'* closure (the wrappers), while a
  ported proof carries its own closure — the `S_` files' import lists. `--rows` over the wrappers
  cannot see a proof-only `Def_` node.
- **rule**: when pricing a set, run the gate over the wrappers **and** over the four `S_` files'
  import lists; a `Def_` node that appears only in the latter is an unported prerequisite. Locally,
  a 10-line `IsSmoothVector` product argument (product stabilizer ⊇ intersection of stabilizers, which
  is open) can be inlined into the declaration that needs it without adding a public declaration the
  wire does not own — which is what was done here (no `MISMATCH`, no extra surface).
- **seen**: 2026-11-02, SET-AF13 dictionary row.

## FR-0130 [mathlib-API] — the height row's three mathlib v4.34 shifts: `prod_le_prod₀`, `coe_toFinset` as a simp argument, and `unusedSectionVars` on pin-shaped declarations

- **where**: SET-AF13's height row (`Ws37EisMaj`), transcriptions of pin
  `S_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet.lean`
  `:281`–`:285` (`hSa`/`hSb`/`hSd`), `:289`, `:299`, `:327` (the three `Finset.prod_le_prod` calls),
  `:132`, `:135`, `:141` (the three instance-unused theorems) and `:60`, `:77`
  (`Eventually.of_forall`).
- **symptom**: (1) the two-argument `Finset.prod_le_prod` (nonnegativity + pointwise) is
  `Finset.prod_le_prod₀` in v4.34, in `Algebra/Order/BigOperators/GroupWithZero/Finset.lean:39`;
  the un-subscripted name is now the `[MulLeftMono N]` version, which ℝ does not satisfy, and
  using it makes the second argument apply to the *conclusion* ("function expected"). (2)
  `simp only [hS, Finset.coe_union, Set.Finite.coe_toFinset]` no longer rewrites the goal
  (`v ∈ ↑(ha.toFinset)`), so the pin's `Or.inl (Or.inl hv)` fails; an explicit
  `rw [Set.Finite.coe_toFinset (hs := ha)]` works and keeps `hv` usable. (3) `maxEntry_nonneg`,
  `le_maxEntry`, `fdistort_nonneg` have an `[IsUltrametricDist K]` binder auto-included from the
  pin's `section Ultra` although they never use it; the port's `linter.unusedSectionVars` fails the
  module on exactly that, and it cannot be silenced without `set_option`. Moving the three (and the
  defs `maxEntry`/`fdistort`) into a `section UltraBase` with only `[NormedField K]` keeps their
  source text — and therefore their hashes — byte-identical. (4) `Eventually.of_forall` is now
  `Filter.Eventually.of_forall`, and the row-4 file's `ℝ≥0∞`/`∞` need `open scoped ENNReal`.
- **cause**: the pin is on mathlib v4.33 with its own linter set; the port is on v4.34 with the full
  linter set live. Product/measure API names and section-variable bookkeeping both moved.
- **rule**: on a height row, check `prod_le_prod` first (subscript `₀`), prefer an explicit `rw` of
  `Set.Finite.coe_toFinset` over a `simp only` argument, and split a pin `section` whose instance
  variable is unused by some of its theorems — the text is unchanged, so the checker still matches,
  while the linter goes quiet.
- **seen**: 2026-11-02, SET-AF13 height row (0 warnings after the repairs; `check_port` 33 ok /
  0 mismatch / 0 missing at that point).

## FR-0131 [checker] [instance] — `statement_db` does not index `instance` declarations, but a pin `def` may need the instance it declares

- **where**: SET-AF13's constant-term row, pin
  `S_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.lean:34`
  (`scoped instance instNontrivialAdeleRing : Nontrivial 𝔸`) and `:39` (`def principalEquiv`).
- **symptom**: the worklist for the row counts 8 declarations and none of them is an instance, yet
  `principalEquiv`'s statement `F ≃ AdeleRing.principalSubgroup (𝓞 F) F` fails with
  `synthInstanceFailed: Nontrivial 𝔸` unless the pin's instance is re-stated (the equiv's forward
  map builds a subtype element from `algebraMap F 𝔸`). With the instance in place the file
  elaborates; the checker's 41-ok surface does not list it, but the "drop `private`" surface gate
  does (64 ok), so it *is* matched by hash and costs nothing. Its `Countable` twin is not needed:
  the port's `NumberField.AdelicHaar.countable_principalSubgroup` can be registered by
  `attribute [local instance]`, as the port's `WhittakerCoefficient.lean:149` already does.
- **cause**: instances carry statements, but the worklist's "declaration lines" pass skips them, and
  the pin hides an instance dependency inside the *type* of an ordinary `def`.
- **rule**: when a pin `def`'s type mentions a structure that needs a `Nontrivial`/`Countable`
  instance the pin declares locally, re-state the pin's instance rather than discovering the gap at
  elaboration; and check the "drop `private`" number, not only the ok count, to confirm it is matched.
- **seen**: 2026-11-02, SET-AF13 constant-term row.

## FR-0132 [tooling] [instrument] — no reading answers "what does this landing ready"; a scoping pass must simulate the landing

- **where**: SET-AF14's scoping read, `tools/deps/build/af14-forecast.py` (69 lines: two `analyze`
  calls over the same frontier), used to price four candidate blocks on one shelf.
- **symptom**: the recipe's §7 asks a scoping pass to report "which rows **became ready because of the
  set**", and nothing in `frontier.py`, `port_advise.py` or `port_plan.py` can be asked that question
  before the work exists: `--ready` reads one frontier, and two shelves taken a set apart are the only
  comparison the column has had (AF13 §5.1: "the re-read ... readied nothing again"). A scoping brief
  therefore cannot say *why* one ready block is a better cut than another beyond silo and leverage —
  and on this shelf both of those mislead: the largest ready block (the Weyl pair, 2,640) and the
  largest single row (the indicator, 1,043) each ready **zero** rows, while a 372-line row readies
  **nine** (2,168 silo) and this set's 1,578 readies two (729).
- **cause**: readiness is a pure function of the ported set (`needed_masks`), so it *is* computable
  ahead of the work; the tool offers only the present-tense reading of it.
- **rule**: before cutting a set, run the landing as a simulation — `ported ∪ set` through the same
  `analyze(...)` the shelf read uses — and quote the delta (needed / frontier / ready / leaves) and the
  readied rows with their silos. `build/af14-forecast.py` is the working instance (4.9 s for two
  analyses); a `--pretend-ported NAME` (the inverse of `--unport`) on `frontier.py` would make it one
  command.
- **seen**: 2026-11-02, SET-AF14 scoping (§0.3); the numbers it produced moved the cut off the block
  the previous brief had named.

## FR-0133 [tooling] — the worklist's "imported" column counts statement-identical **private** port copies, so it overstates a set's reuse

- **where**: SET-AF14's price, `build/af-worklist.py` over the eight `LocalIntertwining` layer-0 rows:
  "62 imported" of 1,465 declaration lines. `port_plan.py` on the same slice: "already in the port
  (vetted) 58" → net 1,393.
- **symptom**: 55 of those 62 lines are statement-identical copies the port holds `private` —
  `integrable_one_add_sq_rpow_neg` (51 lines, pin text) is `Iwasawa/Real/Continuation.lean:71`'s
  `private integrable_dom`, and `one_add_sq_pos` (2+2) is `private` in the same pair of modules. A
  `private` declaration is not importable, so neither figure is reuse; the honest one is **7**. Only
  `port_advise`'s substitution block says so ("only as a port-private declaration: 3 — promote or move
  to a home"), and the worklist and the plan both read as if the lines were free.
- **cause**: the worklist's statement index is built over every declaration in the port tree, `private`
  ones included (which is right for `dedup`-style redundancy, wrong for importability), and
  `port_plan`'s "in port" set is that index's.
- **rule**: when a slice's in-port figure is a large fraction of its raw lines, check the *three*
  substitution classes separately — byte-identical public, binder-spelled public, private-only — and
  price the third as work (or as a promotion decision) rather than as reuse. FR-0128 is the same trap
  from the other side (`port_advise` pointing at a `private` twin as if it were the port copy).
- **seen**: 2026-11-02, SET-AF14 price (§2.1).

## FR-0134 [tooling] — a `def` in `port_advise`'s substitution table is matched by its *type*, so a `def` with a different body reads as reusable

- **where**: SET-AF14's price, `port_advise`'s substitute block: pin
  `S_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod.lean:61`
  (`private def maj`) against port `AutomorphicForm.TestFnArchProfile.sqSize`
  (`AutomorphicForm/Adelic/RightConvNeZeroArch.lean:276`), reported as "identical up to binder spelling".
- **symptom**: both are `(F : Type) [Field F] [NumberField F] → mixedEmbedding.mixedSpace F → ℝ`, so the
  shape tier matches; the bodies are different functions — the pin's
  `maj y = (∏_real (1+‖y.1 i‖²)^(-1)) * ∏_cplx (1+‖y.2 w‖²)^(-2)` is a *product* of inverse
  Japanese-bracket factors, the port's `sqSize x = (∑ v, (x.1 v)^2) + ∑ v, ‖x.2 v‖²` a *sum of squares*.
  Importing `sqSize` for `maj` would have made the row's `integrable_maj` **false as stated** (the
  measure is the product measure, and `sqSize` is integrable only after a Gaussian argument the pin does
  not make). The 4-line `def` was written at the pin's text instead, and `check_port` matches it at the
  pin's line, so nothing was lost but the price was wrong by 4 lines and one import.
- **cause**: a declaration's "statement" is its type, and for a `def` the type is not its content;
  `port_advise` inherits the statement-based matching that is right for theorems. The `maj`/`sqSize` pair
  also survived the binder-spelling and shape tiers because the *type* is literally the same.
- **rule**: never import on a `def` row of the substitution table — read the port `def`'s body against
  the pin's (the table gives both line numbers for exactly this). A `def` row is a *hint* that a home
  exists, not a substitution; if the bodies differ, write the pin's `def` at the pin's name and drop the
  import the row claimed.
- **seen**: 2026-11-02, SET-AF14 row 8 (`maj`, written private at the pin's text; the import it justified,
  `RightConvNeZeroArch`, removed, and order B's closure dropped from 3,561 to 3,128 jobs).

## FR-0135 [checker] [tooling] — neither `check_port` nor the frontier sees a headline declared under the wrong *name*: the statement hash and the last name both pass

- **where**: SET-AF16's landing: seven of its eight headlines were declared *inside* their helper
  namespaces (`AutomorphicForm.LocalIntertwining.ContinuousOnBorel.continuousOn_of_…`) instead of at the
  pin's names (`AutomorphicForm.continuousOn_of_…`).
- **symptom**: `spec/check_port.py --force` read **8 / 1 / 15 ok, 0 mismatch / 0 missing**, and the
  frontier counted all eight as ported — both correct on their own terms, and both blind to the defect:
  the checker keys on the statement's *text*, and the frontier maps a graph node to a port declaration by
  its **last** name, which is unchanged. The only instrument that caught it was `#print axioms` on the
  pin's full names, where seven came back `unknownIdentifier`. A reader following a brief ("the headline
  is at `AutomorphicForm.<name>`") or a consumer citing the pin's name finds nothing.
- **cause**: the port's convention — a headline sits at the pin's name, helpers in subject namespaces —
  is a *naming* rule, and no tool in `spec/` or `tools/deps` checks names against the pin; `check_port`
  was built to verify statements, and deliberately accepts a port copy under another name (that is the
  documented false negative of the name-anchored instruments, FR-0128/FR-0133's mirror image).
- **rule**: after a dispatch, run `#print axioms` on every headline at its **pin-qualified** name; a name
  that does not resolve is a naming defect, not a missing proof. (`lake` will not report it either: a
  declaration under another name still builds, and the module is silent.) A `theorem _root_.<absolute name>`
  declared inside a helper namespace is the cheap repair — the proof keeps its helpers and the
  declaration gets the pin's name; the consumer's references then need the absolute spelling too.
- **seen**: 2026-11-02, SET-AF16 (seven headlines; repaired by the manager, then rebuild + checker +
  axioms + probe + consumer re-run green).

## FR-0136 [tooling] [surface] — the surface gate's `sed` misses `private noncomputable def` (and `private instance`), so the reading under-counts

- **where**: SET-AF17's landing, order C (`RightConvStructurePreservation.lean`, 18 declarations of which 17
  are `private`): `sed 's/^private theorem /theorem /; s/^private def /def /; s/^private lemma /lemma /'`
  followed by `check_port --force` read **16 ok**; with `private noncomputable def` also stripped it reads
  **18 ok**. The two declarations the first pass left private were `sliceFn` and `slice`, both
  `private noncomputable def`.
- **symptom**: the set's dropped-`private` reading came out 101 instead of 103, and the two "missing"
  declarations looked like a checker blind spot (FR-0131's class) until the `sed` was fixed — they were
  never missing, the gate had simply not made them public for the experiment.
- **cause**: the recipe's surface gate is written as "drop `private` from the module's declarations" and
  every set's brief carries the same four-substitution `sed`; Lean's declaration forms include
  `private noncomputable def`, `private instance`, `private protected theorem`, `private abbrev` and
  `private opaque`, and a `sed` keyed on `private (theorem|def|lemma)` silently keeps the rest private.
- **rule**: strip `private` with a pattern that drops the *modifier*, not the keyword after it —
  e.g. `sed 's/^private //'` on every line that starts with it — and then re-read; or compare the ok count
  against the declaration count that `dedup.py --within` reports for the module (18 here), which is the
  cheap cross-check that catches a short reading immediately.
- **seen**: 2026-11-02, SET-AF17 order C (manager's own first pass; corrected on the second).

## FR-0137 [instrument] [setup] — a fresh session's `check_port` reads every pin file as `UNKNOWN PIN FILE` and every declaration as `MISSING`

- **where**: SET-AF18's ground prep, 2026-11-07. `spec/check_port.py --force` on a wired module reported
  `0 ok, 0 mismatch, 2 missing` with the line `UNKNOWN PIN FILE S_AutomorphicForm_bruhatTransversal_…`, and the
  two "missing" declarations were plainly present in the pin file. The checker was fine; the **corpus was absent**.
- **cause**: `check_port` resolves a module's `spec-pin:` files through the statement corpus
  (`tmp/flt-statements/statements.{tsv,idx}`), which is a *build artifact*, not a tracked file. `tmp/` is
  git-ignored and does not survive a clean checkout, so a session that starts after one has no corpus; `Wire`
  then sees no declarations for any source, `db.has_file` is false, and every declaration falls to `MISSING`
  with the misleading `UNKNOWN PIN FILE` header. Nothing in the module's own text is at fault, and the
  per-module verdict cache (`tmp/check-port/state.json`) is gone with it, so this looks like a regression in
  the tree.
- **rule**: before believing any checker verdict, check `ls $REPO/tmp/flt-statements/statements.idx`. If it is
  absent, run `python3 spec/statement_db.py build` (measured 2026-11-07: 35 s, 60,478 pin files, 718,874
  declarations, 459 MB — the same count the playbook quotes). Note the path: the corpus lands in the **repo**
  root's `tmp/`, not `lean/tmp/`.
- **seen**: 2026-11-07, SET-AF18 (one wasted checker run).

## FR-0138 [instrument] [shelf] — a third false ported marker: `NumberField.AdeleRing.secondCountableTopology` is read ported because of a last-name shadow, and `--selfcheck` cannot see it

- **where**: SET-AF18's scoping read. The D–S shelf carried
  `NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo` (32) and three
  `NumberField.AdelicHaar` rows (215 / 128 / 119) as **ready**, and three `AutomorphicForm` rows
  (`isCuspidalFn_rightConv`, `isKfSmooth_rightConv`, `rightConv_rightConv_eq_rightConv_rightConv_comp_inv`) were
  read as one edge from ready — all of them through the premise
  `NumberField.AdeleRing.secondCountableTopology` (62), which the port does **not** declare at that name.
- **symptom**: `frontier.py --selfcheck` **PASSes**. The names tier marks the node ported because the port
  declares `lemma RestrictedProduct.secondCountableTopology`
  (`Topology/Algebra/RestrictedProduct/TopologicalSpace.lean`), a different statement with the same last name
  (FR-0047's mechanism, met a third time). The corrected read, `--unport NumberField.AdeleRing.secondCountableTopology`,
  moves `needed` 838/344,897 → 839/344,959 and takes the four rows above off the shelf (494 silo).
- **cause**: the readiness test is last-name membership (`port_decl_nodes`), and `--selfcheck` validates only
  that `Thm_` *source* claims are covered by the name tier — it never asks whether the name tier's match is the
  statement. The port *did* have the mathematics, as `scoped instance instSecondCountableAdeleRing` (a name the
  pin's wrapper does not carry), so no re-proof was needed; the missing thing was a declaration the checker
  could diff.
- **rule**: for any shelf row whose premises are few, `twin_scan.py --node <premise>` the premises of the rows
  you mean to cut; a `relative` verdict means the premise's *statement* is absent and the row is not ready.
  Then either port the premise at the pin's name (cheap when the instance exists: a two-line theorem) or
  `--unport` it and re-read. Do not trust a bare `needed = 1` whose premise you have not seen declared.
- **seen**: 2026-11-07, SET-AF18 (§0.2 of its brief; repaired in §3.1).

## FR-0139 [tooling] [linter] — no linter suppression is needed for `haveI`/`letI`: `have`/`let` register local instances

- **where**: SET-AF18's ground prep, promoting `continuous_rightConv` to the pin's public
  `continuous_rightConv_of_continuous_of_hasCompactSupport`. Its proof is a proposition goal with three
  instance walls, and the landed module carried
  `set_option linter.style.haveILetI false in` above it (a pattern several port modules carry, transcribed
  from the pin's own file-wide suppressions).
- **symptom**: `haveI`/`letI` in a `Prop` goal makes mathlib's `linter.style.haveILetI` fire
  ("The goal is a proposition, so `have` is preferred over `haveI`"). Deleting the suppression therefore
  looked like it required either warnings or a proof rewrite.
- **cause**: the linter's own docstring states the fact — "in Lean 4, `have` and `let` register local
  instances themselves, so inlining is the only remaining difference" — so the rewrite is mechanical:
  `haveI h : <class>` → `have h : <class>`, `letI : T` → `let name : T`. Measured on the promotion: the
  three walls became `let mSpace` / `have hBorel` / `have hHaar` and the module elaborates silent, no
  `set_option`. The same conversion was used for the two new countability theorems in
  `AdelicLevel/Countability.lean`.
- **rule**: never silence `linter.style.haveILetI`; convert. (And never add `set_option maxHeartbeats` — that
  is a defect marker.) One parser detail that costs a round: a docstring cannot be followed by a `--` comment
  and then a `set_option … in` line — Lean reports `unexpected token 'set_option'; expected 'lemma'` at the
  docstring. Put the comment above the `set_option`, or the docstring inside it.
- **seen**: 2026-11-07, SET-AF18 ground prep (`RightConvRegularity.lean`, `AdelicLevel/Countability.lean`).

## FR-0140 [workorder] [tools] — an order's copy-pasteable tool commands did not resolve: `tools/deps` sits at the repo root, and `dedup.py --within` takes a module pattern

- **where**: SET-AF18's orders A and C, 2026-11-07. Both carried the recipe's (and SET-AF17's) form of
  the two post-flight commands: `python3 tools/deps/dedup.py --within FLTForHuman/…/X.lean` and
  `python3 tools/deps/move_dead.py --source FLTForHuman/…/X.lean …`, to be run from `lean/`. Neither
  resolves in this checkout.
- **symptom**: `No such file or directory` for `tools/deps/dedup.py` (the tools live at the **repo**
  root, i.e. one level above `lean/`), and, once found, `dedup.py --within` rejects a file path — it
  takes a **module pattern** (`FLTForHuman.AutomorphicForm.Adelic.RightConvAdjoint`), not
  `…/RightConvAdjoint.lean`. Order A's worker reported both; order B's worker ran the tools from `lean/`
  with a relative `../tools/deps/` path and got there by trial.
- **cause**: the work orders were written by copying SET-AF17's §6 gate block, which predates the
  working-directory convention being stated anywhere in the order; and `dedup.py`'s `--within` argument
  is documented in its `--help` but not in the playbook's §8 line for the tool.
- **rule**: in a work order, give the two commands **verbatim with their working directory**, e.g.
  ```
  (from the repo root) python3 tools/deps/dedup.py --within FLTForHuman.<Area>.<Module>
  (from the repo root) python3 tools/deps/move_dead.py --source lean/FLTForHuman/<Area>/<Module>.lean --target /dev/null --dry-run
  ```
  The checker, by contrast, is run from `lean/` with a path (`python3 spec/check_port.py --force
  FLTForHuman/…/X.lean`) and the graph tools from `tools/deps/` with `build/…` output — three different
  working directories in one set of gates, which is exactly why they get copied wrong.
- **seen**: 2026-11-07, SET-AF18 (two of three workers; no proof work lost).

## FR-0141 [build] [dispatch] — three concurrent workers on one tree: transient `object file … does not exist`, and the 60 s tool cap while queueing on the build lock

- **where**: SET-AF18's dispatch (three orders, four modules, one tree), 2026-11-07. Both the carrier
  and the operator-algebra workers report the same two symptoms; neither cost proof work (retries
  cleared them), but both burn turns.
- **symptom 1**: the edit loop (`lake env lean <file>`) fails with `object file
  '.lake/build/lib/lean/FLTForHuman/…/X.olean' of module … does not exist` for a *dependency* another
  worker is rebuilding at that moment — the other job has removed/replaced the `.olean` between this
  job's import resolution and its read. It is transient by construction, and the module's own
  `lake build` re-establishes it.
- **symptom 2**: `flock .lake/flt_build.lock timeout 280 lake build <module>` — a *correctly bounded*
  build — can exceed the agent's own 60 s per-tool-call cap while it waits on the lock, and is then
  killed by the harness, not by its own `timeout`. The retry usually finishes in seconds (measured:
  a 3.5 s build killed once while queued).
- **rule**: with more than one worker in the tree, (a) retry an `object file … does not exist` once
  before diagnosing it, and mention it in the report as *transient* rather than as a blocker; (b) run
  every `lake build` under `flock`/`timeout` in the **background** and read its log
  (`run_in_background` + `job_output`), so a lock wait cannot eat the foreground turn; (c) never
  attribute a proof failure to either symptom — both are I/O-level and self-healing.
- **seen**: 2026-11-07, SET-AF18 orders A, B and C (each hit at least one; no rework).

## FR-0142 [drift] [faithfulness] — a mathlib change can make a *pin statement* false, not merely unprovable

- **where**: SET-AF19 order A, 2026-11-07. The pin's prelude lemma `eLpNorm_two_pow_two`
  (`S_…CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact.lean:76`)
  states `eLpNorm (φ ^ 2) 1 ν`-style identities with **no measurability hypothesis**.
- **symptom**: at mathlib v4.34 the identity is *false*, and a faithful transcription does not fail to
  prove — it fails to typecheck in a way that looks like a missing lemma. v4.34 defines
  `MemLp f p μ := eLpNorm f p μ < ∞` (`LpSeminorm/Defs.lean:152`) with `AEStronglyMeasurable` no
  longer a conjunct, and `eLpNorm = ⊤` off the a.e. strongly measurable functions (`Defs.lean:96–101`),
  so for a non-a.e.-strongly-measurable `φ` the two sides cannot be equal.
- **cause**: the port's rule "adapt proofs, never statements" presupposes the pin's statements *hold*
  on the port's mathlib. A drift that changes a definition's *meaning* (here `MemLp`'s) can invert a
  statement, and no amount of proof search recovers it.
- **rule**: when a "the pin's statement" resists proof at a shape that suggests a missing hypothesis,
  ask whether a v4.34 def change has moved under it before concluding the transcription is wrong —
  the `MemLp`/`eLpNorm` case is now a row in [TOPIC-mathlib-drift.md](../topics/TOPIC-mathlib-drift.md).
  The cure is the hypothesis that every pin use discharges, plus an `own:` marker row with the reason;
  never an `axiom`, and never a silent weakening of a *headline* (a prelude helper is the case this can
  legitimately happen to).
- **seen**: 2026-11-07, SET-AF19 order A (one declaration; the two headlines it feeds are unaffected).

## FR-0143 [scoping] [imports] — a pin proof's route can be unavailable on the port's side of the import boundary

- **where**: SET-AF19 order C, 2026-11-07. The pin proves
  `NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` through
  `ideleNorm_det_eq_prod_archDetNorm_pow_mult` applied to `diagOne a`. In the port that lemma lives in
  `AutomorphicForm/Adelic/IdeleNormDetGlue.lean`, and `NumberField/TateGlobal/Defs.lean`'s header fixes
  the rule that the `NumberField` tree does **not** import `AutomorphicForm`.
- **symptom**: none at scoping time — the row was ready (its single premise was ported), its statement
  elaborated, and the checker read it `ok`. The wall appears only when the worker opens the pin proof
  and finds its main ingredient on the wrong side of the boundary.
- **cause**: readiness is computed on the *graph* (the pin's `S_` import edges), and the pin's own
  boundary between `NumberField` and `AutomorphicForm` is not the port's.
- **rule**: when scoping a row in a low-level area (`NumberField`, `Topology`, the `Defs` tier), check
  that the pin proof's *named engine* has a home on the same side of the boundary before pricing the
  row as a transcription. If it does not, the row is still portable — the statement is — but by a
  different route, and the brief should say so rather than promise a transcription. Here the
  finite-`finprod` collapse (`distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm` +
  `finprod_eq_one_of_forall_eq_one`) proves the same statement in 12 lines.
- **seen**: 2026-11-07, SET-AF19 order C (route changed, statement and gates unaffected).

## FR-0144 [scoping] — a set's "next subject" named on silo is not a measurement of what it opens

- **where**: SET-AF20's scoping, 2026-11-07. SET-AF19 §8 closed with "AF's ready shelf is now 32
  rows / 13,111 silo, of which AF20's subject is the `diagOne` family, 3,248" — a *silo* ranking of
  the four `diagOne` rows (`…whittakerCoefficient_diagOne…` 913, `…isArchTestFactor_nonneg…` 905, the
  two `CuspidalConstituent…diagOne…` 716 / 714).
- **symptom**: none — the four rows are ready, their premises are ported, and the recommendation
  reads as a decision. It is not: the recipe (§1, §7) chooses on *what the landing buys*, and that
  number is not in the shelf row.
- **measurement**: the return of a row — the silo of the in-cone rows whose every unported premise is
  that row — is 0, 0, 0, 0 for the four `diagOne` rows. Their consumers are four 400–1,400-line rows
  that each still need two to six further premises. On the same shelf, `123 silo` of
  `NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact` returns **2,113**, and
  `70 silo` of `exists_isRightEquivariant_comp_subtype_eq_of_injective` returns **1,445**.
- **cause**: `frontier.py` ranks by `silo` (the row's own size) and reports `leverage` (fan-in), but
  neither is readiness *return*: a row with fan-in 1 whose single consumer is one premise short is
  worth everything, a row with fan-in 4 whose consumers each need six more rows is worth nothing.
  The tool does not compute the second-order readiness.
- **rule**: before a brief names a set, compute the return of its rows (the one-liner is
  `tools/deps/build/af20-return3.py`; it walks `cited_by ∩ cone \\ F` and checks each consumer's
  remaining unported premises) and quote it beside the silo. A "next subject" paragraph inherited
  from the previous set is a hypothesis, not a measurement — re-measure it, and expect it to be
  wrong about half the time when it was chosen on size.
- **seen**: 2026-11-07, SET-AF20 scoping (the cut changed from the inherited `diagOne` family to the
  leaf this note takes).

## FR-0145 [tooling] [faithfulness] — two statement-fidelity traps a scoping session hits before any proof

- **where**: SET-AF21's scaffolding, 2026-11-07. Writing the eight frozen statements of the set into
  four skeletons.
- **symptom 1 — a docstring can close its own block comment.** A header line reading
  `the rational (centre-/torus-)unipotent subgroups` contains `-/`, which **terminates** the
  `/- … -/` comment: the rest of the header is parsed as Lean, and the error points at line 2
  column 42 (`unexpected identifier; expected command`) with an `import` complaint at the end of the
  header. Nothing in the message mentions the comment.
- **symptom 2 — a qualified name in a statement is part of the hash.** The pin's two
  `HaarQuotient.*` wrappers state their conclusions outside the namespace, so they write
  `∂(HaarQuotient.measure μ H μH)`; writing `measure μ H μH` inside the same namespace elaborates to
  the same term but the checker reads `MISMATCH` (the diff is text-anchored after normalisation of
  binders, not of *qualified names*). The fix is to transcribe the wrapper's spelling, not the
  namespace-local one.
- **cause**: the checker's statement hash is a *text* function, and the port's convention is "the
  wrapper's text"; the docstring case is pure Lean lexing.
- **rule**: when scaffolding, (a) never write a hyphen immediately before a slash in a `/- … -/`
  header (`centre-/torus-`, `and-/or-`, `pre-/post-` are the natural ways to do it by accident), and
  (b) when a statement mentions a declaration from its own namespace, write it **qualified exactly
  as the wrapper does** — a `MISMATCH` whose port and pin texts look identical on the printed
  prefix is usually this, so print the full row rather than the head.
- **symptom 3 — an explicit binder name is not normalised, unlike its *kind*.** The pin's
  `hle : Γ₂ ≤ Γ₁` is unused in one headline (at the pin too), so the port wanted Lean's `_hle`
  idiom to keep the module warning-free without `set_option`. `check_port` reports **MISMATCH**:
  the checker normalises section variables vs inline binders, but not the *name* of an explicit
  binder. So an unused hypothesis must be **referenced** in the proof (one proof-neutral `have`
  line) rather than renamed — and that is what the landed module does, with the reason in a
  comment.
- **seen**: 2026-11-07, SET-AF21 scaffolding (two headers, two statements; both caught by
  `lake env lean` / `check_port --force` before dispatch), and its order A (the `_hle` attempt,
  measured on the landed module and reverted).

## FR-0146 [drift] — a mathlib deprecation can name a replacement that is not in the library

- **where**: SET-AF22's three orders and SET-AF21's orders A/C/D, 2026-11-07. The pin uses
  `Measurable.ennreal_tsum` / `AEMeasurable.ennreal_tsum` at four sites
  (`S_…isIdeleClassChar…:40-76`, `S_HaarQuotient_…lint…:143`, `S_…isFundamentalDomain_iUnion_inv_smul…:86`,
  `S_…boxSheet…`).
- **symptom**: at mathlib `v4.34.0` both names are *deprecated* (`since := "2026-04-30"`) and the
  message points at `Measurable.tsum` / `AEMeasurable.tsum` in
  `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean` — **which does not exist in this checkout**
  (`rg "theorem Measurable\.tsum|lemma Measurable\.tsum|theorem AEMeasurable\.tsum"` over both files
  returns nothing, and there is no deprecation alias either). So the warning steers to a dead end,
  and `set_option linter.deprecated false` is not available to the port.
- **cause**: a `to_additive`-generated lemma (`AEMeasurable.tprod`'s additive image) was named in
  the deprecation before it was added/kept, or was removed afterwards — either way the port cannot
  take the suggested route and cannot silence the warning.
- **rule**: when a pin lemma is deprecated, check that its named replacement *exists* before
  planning around it; if it does not, re-derive the deprecated lemma's own short proof inline
  (`ENNReal.tsum_eq_iSup_sum` + `Measurable.iSup` + `Finset.measurable_fun_sum`, or `ae_lt_top'`)
  with a comment naming the missing lemma. Three orders did this independently in one dispatch, which
  is the sign that the workaround belongs in a shared supplement rather than in each module — the
  candidate home is the next `MeasureTheory/` supplement this column writes.
- **seen**: 2026-11-07, SET-AF21 orders A/C/D and SET-AF22 (same lemma, four sites).

## FR-0147 [tooling] — `gate_scan`'s `--port-root` is relative to the *invocation directory*, so from the pin root every declaration reads `MISS`

- **where**: `spec/gate_scan.py`, the definition-gate first cut of a set's scoping read.
- **symptom**: run as `cd ~/proj/fermats-last-theorem && python3 <port>/lean/spec/gate_scan.py --pin Definitions/Def_X.lean --rows Theorems/Thm_….lean`
  it reports `uses 9/32 — 9 missing from the port` for declarations the port has had for weeks
  (`archDerivAtComplex`, `archFlowAtComplex`, `archComplexLiftAt`, `IsArchSmoothAtComplex`), i.e. the
  whole gate looks unpaid.
- **cause**: `--pin-root` defaults to the pin clone but `--port-root` defaults to the *relative* path
  `FLTForHuman`, resolved against the CWD. From the pin root that directory does not exist, so the
  port index is empty and every name is `MISS`. The tool's own usage block says "from `lean/`"; the
  invocation in the set notes drops the `cd`.
- **fix**: run it from `lean/` (`cd lean && python3 spec/gate_scan.py --pin Definitions/…`), where the
  default port root is right; or pass `--port-root <repo>/lean/FLTForHuman` explicitly. Verify by the
  count: a gate that reads "0 missing" on a module this column landed in an earlier wave is the
  signal, and a `MISS` on a declaration `rg` finds in `FLTForHuman/` is the contradiction.
- **seen**: 2026-11-07, SET-AF24's scoping read (the first run said 6–13 missing on all four rows;
  the same command from `lean/` said 0 missing everywhere).

## FR-0148 [tooling] — a `def` whose type is a function type "substitutes" to any same-typed `def`

- **where**: `port_plan`'s `substitutions:` block, on a pin file that writes a derivative as a bare
  `def D0 (y : G → ℂ) : G → ℂ := archDerivAtComplex hw .iH y`.
- **symptom**: three of SET-AF24's six substitution rows read `2 D0 -> AutomorphicForm.OsAlg.Dk`,
  `2 D1 -> …`, `2 D2 -> …` — three different derivatives "already in the port" as one unrelated
  `def`, which would price 6 lines as reused and, worse, invite a worker to delete them.
- **cause**: the checker's type view of `def D0 (y : G → ℂ) : G → ℂ := …` is the function *type*
  `(G → ℂ) → G → ℂ`; every definition of that shape has the same type text, so the substitution tier
  matches them all. It is the `def … : Prop` false positive of playbook §2.4 in its function-type
  form.
- **rule**: read every `substitutions:` row whose pin side is a `def` (not a theorem) and check the
  body by eye before accepting it; `port_plan` already marks these as "suspect". A `def` row is only
  a real substitute when the *body* is the same mathematics.
- **seen**: 2026-11-07, SET-AF24 (`port_advise --nodes` over the four rows).

## FR-0149 [lean] — `!![…]` inserts a second `Matrix.of` at v4.34, so `Matrix.of_apply` will not fire in a `simp`/`rw` script

- **where**: any pin proof that writes a matrix as `!![(cos s : ℂ), -(sin s : ℂ); (sin s : ℂ), (cos s : ℂ)]`
  and then simplifies its *entries* — on this column `archComplexLiftAt hw !![…]` (SET-AF24B's
  headline proof, pin `:158-175`).
- **symptom**: the pin's `ext i j` / `fin_cases` / `simp` script for
  `archComplexLiftAt hw !![1, 0; 0, 1] = 1` leaves goals of the shape
  `Matrix.of !![1,0;0,1] 0 0 = 1` unsolved; `rw [Matrix.of_apply]` and `norm_num` both fail to make
  progress, and the failure looks like a missing lemma rather than a term-shape difference.
- **cause**: `Matrix m n α` is *syntactically* `m → n → α`, so `!![…]` (i.e. `Matrix.of ![![…]]`)
  already has the matrix type, and `archComplexLiftAt`'s own `(Matrix.of e)` then wraps it a **second**
  time: `Matrix.of (Matrix.of ![![…]])`. `simp`/`rw` elaborate at implicit transparency, where
  `Matrix` does not unfold, so the two `of`s do not cancel and the entry lemma cannot apply.
- **fix**: route the literal through the function form once — `fun i j => (!![…]) i j` — which is
  definitionally the same term (eta) and leaves the entries `simp`-reachable; keep the `have` at the
  frozen spelling so the downstream `hk0`/`hspan` arguments still see the pin's shape. Cost ~3 lines.
  Verify with the zero-warning edit loop, then `check_port --force` (the *statement* is untouched, so
  the checker must stay `ok`).
- **seen**: 2026-11-07, SET-AF24B (`Adelic/ArchRotCoordinate.lean`); the same pin idiom appears in
  the `su2Derivs`/`su2Strings` statements, where it survives because no proof simp's the entries.

## FR-0150 [tooling] — a row named in another set's prose is not a row *on the shelf*: the blocks omit `needed ≥ 2`

- **where**: cutting a set from the D–S shelf; SET-AF24's brief, whose row table took the block label
  from SET-AF23 §5's prose instead of from the shelf JSON.
- **symptom**: two of the four rows (`exists_su2Strings_of_finiteDimensional_…` 908,
  `hasArchCharacterAtZero_one_of_…` 169) were written up as "ready" rows of the −1,077 silo that the
  set would remove from the ready block. After landing, the ready block was **unchanged** at
  72 / 24,200: those rows had never been in it.
- **cause**: the shelf's two blocks are not exhaustive. `ready_rank` holds `needed == 1`, `leaves_rank`
  holds graph leaves, and a row that is **neither** — one unported premise and at least one consumer,
  i.e. `needed == 2` — appears in **neither** block. SET-AF23 §5 named the pair as the successors of
  its own leaf, which is true and says nothing about block membership. `af-return.py` priced them
  correctly (755 readies 908 + 169 = 1,077), and that is the instrument that finds them.
- **rule**: a brief's row table takes each row's block from the JSON (`r in ready_rank.rows` /
  `r in leaves_rank.rows` / **else "off-shelf"**), never from the prose of an earlier set nor from the
  return column; the block accounting in the brief must then sum only what the blocks actually hold.
  A row that is off-shelf is a *good* find (it is one edge above a leaf and cheap), but it must be
  named as such — it does not reduce a block's figure and the forecast must not subtract it there.
- **seen**: 2026-11-07, SET-AF24 (`build/shelf-af24.json` vs `shelf-af24-post.json`: the ready block
  identical, the leaves −2 / −939, `needed` −4 nodes / −2,016 lines).

## FR-0151 [pin] — two ways a pin *statement* cannot be transcribed verbatim in this port

- **where**: scaffolding SET-AF27's first candidate, the Weyl intertwining pair
  (`weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` 1,349 and
  `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` 1,291).
- **symptom 1 — a qualified name the port re-homed.** The 1,291 wrapper writes
  `NumberField.AdelicBox.integralFiniteAdeles`. The port homes that definition in
  `NumberField.AdelicLevel` (`NumberTheory/AdelicLevel/IdealBall.lean:159`); the `AdelicBox` namespace
  does not carry the name, so the pin's text fails to elaborate with `Unknown constant
  NumberField.AdelicBox.integralFiniteAdeles`. Respelling it is a *statement* change (the checker's text
  hash sees the qualifier), so it cannot be a worker's silent adaptation.
- **symptom 2 — an auto-bound binder, and only partly diagnosed.** The 1,349 wrapper's hypothesis is
  `(hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))`: `x` is untyped, its type meant to come from `α`'s domain. In the
  port the same text reports `failed to synthesize LE Type` / `OfNat Type 0` (Lean has bound `x` as a
  *type* variable), and the failure survives `set_option autoImplicit true` **and** an explicit binder
  annotation — so the cause is not `autoImplicit` alone. What *does* work is the same hypothesis with
  `α` a section variable instead of a `let`-bound term, which points at the `let α : … := …` block
  (its value is a `distribHaarChar`-composed hom that needs instances the port's context may not
  synthesize, leaving `α`'s type unforced when the binder is elaborated). Treat it as **unresolved**:
  the next pass should elaborate the wrapper text in a scratch file with the pin's own imports first
  (`Mathlib.MeasureTheory.Measure.Haar.DistribChar` included) before deciding between a port-side
  spelling and an `own:` row.
- **cause**: the pin's own `set_option autoImplicit false` sits in each `S_` file and does **not** govern
  the `Theorems/` wrapper's generated statement (the wrapper has its own, later, and the statement was
  machine-generated from the solution's binders), and the pin's namespace layout (`AdelicBox` owning
  `integralFiniteAdeles`) is not the port's.
- **CORRECTION (same session, superseded by FR-0154).** **Neither symptom was a port obstruction.** Both
  were scaffolding gaps in my own module skeletons: (1) `NumberField.AdelicBox.integralFiniteAdeles`
  *does* exist in the port — it is declared in `NumberTheory/NumberField/TateGlobal/IdeleNormValues.lean`,
  which my scaffold did not import (`#check @NumberField.AdelicBox.integralFiniteAdeles` succeeds once it
  is), so the pin's qualified text needed an import, not an alias; (2) the `∀ x` binder was never the
  problem — `open scoped NNReal` was missing, so `ℝ≥0` in the `let α` block parsed as an inequality
  instead of the type, the `let` collapsed into type-valued metavariables, and the untyped binder then
  reported `LE Type`. With `open scoped NNReal` the statement elaborates **verbatim**. The pair was
  scaffolded the same session (SET-AF33, both scaffolds checker-green) and is being ported.
- **rule**: scaffold a set's statements *before* pricing the order, and when a statement will not
  elaborate, **classify the failure before acting on it**: an *environment* failure (a missing `import`,
  a missing `open`/`open scoped`, a missing instance) is fixed in the scaffold and says nothing about the
  pin or the port; a *conflict* (the port states the declaration differently, or does not have it at all)
  is the manager's `own:`/alias decision. Never record a row as "blocked" without that distinction — this
  entry cost the shelf its largest subject for one round on two false positives.
- **seen**: 2026-11-07, SET-AF27's scoping (the pair was dropped from the set and the `L²`-continuity
  trio taken instead; this entry is what a future pass needs to pick it up).

## FR-0152 [checker] — a worker's `private` default can cost a whole set's checked surface, and a sibling module's precedent is not the pin's text

- **where**: SET-AF30's landing (`Adelic/Siegel/CentreCutCover.lean`, four headlines over 905 + 520 + 432
  + 346 pin lines), reviewed after the worker reported "all gates green".
- **symptom**: the checker read **5 ok / 0 mismatch / 0 missing** and looked perfect: the four headlines
  plus the one helper the worker had left public. The module actually holds ~140 pin declarations, and
  the pin's own `S_` files state them **publicly** (measured: 103 public / 0 private in the 905 file, 20/0
  in the 520 file, 17/0 in the 432 file, 1 public + 19 private in the 346 file). So 137 pin-faithful
  statements were invisible to the checker and unavailable to any future consumer.
- **cause**: the worker applied the column's *private-prelude* habit with a real precedent
  (`Siegel/SlabCovering.lean`'s header: "the shared prelude is transcribed once, `private`"), which is
  right for a prelude the pin itself keeps private and wrong for a node whose `S_` file is a public
  development. `check_port` cannot see the difference — it only diffs what is public, so a `private`
  module is always "0 mismatch / 0 missing".
- **fix**: run the recipe's surface gate at review, as one experiment: strip `private` from the module's
  declaration keywords, elaborate (it cost nothing here — no names clashed), and re-run `check_port`.
  Read three numbers: every **`ok`** is a pin-faithful statement that belongs public (here 137 of them),
  every **`MISMATCH`** is either a local re-spelling (keep *that one* private — here a single qualifier,
  `integralFiniteAdeles` vs `AdelicLevel.integralFiniteAdeles`) or a genuine mis-transcription, and every
  **`MISSING`** is a port-side helper (keep it private). Side effects worth knowing: the promotion also
  emptied `move_dead`'s "4 declarations / 18 lines dead" finding, because those declarations were dead
  only in the private world, and the module's build went 29 s → 44 s.
- **rule**: an order's gate section must say *which* visibility the pin's file has (quote the `private`
  count), and the reviewer must run the promotion experiment before accepting a "5 ok" module with a
  three-figure pin line count. A landed module whose `ok` count is a small fraction of its pin's public
  declarations is not "green", it is unchecked.
- **seen**: 2026-11-07, SET-AF30 (5 ok → 142 ok in one pass; the only casualty was the qualifier
  re-spelling, which stayed private).

## FR-0153 [checker] — a surface-gate `MISMATCH` is usually fixed by the *open*, not by re-privatising the declaration

- **where**: SET-AF30's surface gate, second pass (a follow-up to FR-0152).
- **symptom**: after stripping `private` the checker read 142 ok / **1 mismatch**: the pin writes the
  bare `integralFiniteAdeles`, the port had it as `AdelicLevel.integralFiniteAdeles`. My first call was
  to keep that one declaration `private` (the recipe allows it: "the pin's own prelude copy re-spelled").
- **cause**: the re-spelling was not the pin's text but the *module header's* doing. Three namespaces were
  opened (`NumberField`, `NumberField.AdelicLevel`, `NumberField.AdelicBox`, and `AdelicHaar` further
  down), and `integralFiniteAdeles` exists in two of them (`AdelicLevel/IdealBall.lean:159`,
  `AdelicHaar/PlaceMeasure.lean:48`), so the bare name was ambiguous and the worker had qualified it.
  Nothing in the module used `NumberField.AdelicBox` at all.
- **fix**: drop the unneeded `open` and restore the pin's text — one line, and the declaration goes from
  `MISMATCH` + `private` (invisible to the checker) to `ok` + public. Measured: **142 ok / 1 mismatch**
  → **143 ok / 0 mismatch / 0 missing / 0 own**, `grep -c private` = 0, `move_dead` still 0/0, build
  35 s, consumer 0 errors.
- **rule**: when a promoted declaration mismatches on a *qualifier*, first ask whether an `open` in the
  module's own header is what forced the qualifier; if it is unused elsewhere, remove the `open` and take
  the pin's spelling. Keep `private` only for a genuine local re-spelling (a stated-at-a-different-type
  `show`, a port-side helper) — and say which in the module header. A header that opens one namespace
  more than it needs silently costs the checker the declarations it touches.
- **seen**: 2026-11-07, SET-AF30 (`AdelicBox` open dropped; 143 ok, nothing private).

## FR-0154 [tooling] — classify a statement that will not elaborate: *environment* first, *conflict* second

- **where**: scaffolding a set's statements (recipe §0/§3: "the scaffolding is the statement gate").
- **symptom**: the pin's wrapper text reports an error that looks like the port cannot state the theorem
  — `LE Type` / `OfNat Type 0` for an untyped binder, `unknown constant NumberField.AdelicBox.integralFiniteAdeles`
  for a qualified name — and the temptation is to write the row down as "blocked on a statement-spelling
  conflict" (FR-0151 did exactly that for the Weyl intertwining pair, the largest open subject on the
  column's shelf, and one round was spent on smaller sets because of it).
- **cause**: both errors were *environment*, not conflict. `ℝ≥0` needs `open scoped NNReal`; without it the
  `let α : (AdeleRing …)ˣ →* ℝˣ` block does not mean what it looks like, the `let` leaves type-valued
  metavariables behind, and the *untyped* binder downstream reports a `Type`-shaped failure that has
  nothing to do with binders. And a qualified pin name (`NumberField.AdelicBox.integralFiniteAdeles`) can
  simply live in a module the scaffold did not import — the port had it all along.
- **fix / rule**: before concluding anything about the pin or the port, run the two cheap checks:
  `#check @<qualified name>` after importing the pin's own `import` list (the port usually has a home for
  it), and re-elaborate with the pin's **`open scoped`** line copied verbatim. Only if both fail is it a
  conflict, and then it is the manager's `own:`/alias decision. A "blocked" note must name which of the
  two classes it is, and a scaffolding failure should be retried with the pin's header — imports *and*
  scoped opens — before it is recorded.
- **seen**: 2026-11-07, SET-AF33 (the Weyl intertwining pair): both scaffolds green at **1 ok** each after
  copying the pin's imports and `open scoped NNReal`, where FR-0151 had recorded two obstructions.

## FR-0155 [build] — the edit loop (`lake env lean`) takes no lock, so a sibling's `lake build` can pull the oleans out from under it

- **where**: two orders dispatched in parallel on one tree (SET-AF33A/AF33B, and the same shape in
  AF30/AF31/AF32): the `lake build` half is serialized by `flock .lake/flt_build.lock`, the `lake env lean`
  edit loop is not.
- **symptom**: a `lake env lean <file>` that had been silent for many passes suddenly fails with
  `object file '…/.lake/build/lib/lean/FLTForHuman/…/X.olean' of module … does not exist`, for a module
  nobody edited. Re-running the same command minutes later succeeds unchanged.
- **cause**: `lake build <sibling>` re-elaborates its dependency chain and rewrites the shared `.lake`
  directory; if it is mid-flight (or a build directory was pruned), the oleans the edit loop imports are
  transiently absent. The lock only orders *builds* against each other, not a build against a read.
- **fix**: treat that message as *not* a code error: check whether another `lake build` is in flight
  (the `flock` holder), wait for it, and re-run — never start editing the apparently-missing module. For a
  parallel dispatch, either give each agent a disjoint *import* closure (preferred) or have the edit loop
  take the same lock in shared mode (`flock -s`), which `lake` does not do itself.
- **seen**: 2026-11-07, SET-AF33B (transient, self-resolving; the agent re-ran after the sibling's build
  finished and every gate line in its report is post-hoc clean).

## FR-0156 [tooling] — the *last-name* shadow is not only a port-side hazard: `RatAdele.denseRange_…` covers `NumberField.denseRange_…`

- **where**: scoping a set off the D–S shelf (`frontier.py --ds --ready`, recipe §0: "run `--unport` and
  read the shelf twice").
- **symptom**: a ready row with `premises_unported = 0` whose pin proof cites a theorem the port does not
  hold. SET-AF34's general obstruction row
  (`…not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt`, 527) cites
  `NumberField.denseRange_algebraMap_add_adeleSingleAt` at pin `:525`; the port holds only
  `RatAdele.denseRange_algebraMap_add_adeleSingleAt` — the `K = ℚ` case, **same last name**. The name
  tier reads the general node as ported, so the row looks ready and both `--selfcheck` and
  `check_port` are silent (the former checks the source tier's coverage, the latter statement-diffs the
  modules that exist).
- **cause**: readiness is a *name* test over the port index, and the pin's general theorem and its
  rational specialisation share a last name exactly when the port has migrated the special one first.
  The recipe's FR-0047 shadows were the reverse direction (a port declaration at a *specialised*
  statement covering the general node); this is the same collision with the pin's own two names.
- **fix / rule**: the instrument is `--unport <the general name>` on the same read. If the row leaves
  `ready_rank` and that name enters `leaves_rank`, the row was a false ready and its premise is the
  set's first order. Quote the corrected `needed` (here 763 / 319,019 → **764 / 319,352**) next to the
  instrument's, and re-take the read after the premise lands — the shadow then resolves itself.
- **seen**: 2026-11-08, SET-AF34 §0.2.

## FR-0157 [tooling] — a `sorry`-bodied scaffold at the wrapper's name makes the frontier price the set as landed

- **where**: the manager's scaffolding step (new modules, statements with `sorry` bodies, wires) taken
  *before* dispatch, then a mid-wave shelf read.
- **symptom**: right after scaffolding four modules and landing only one of them, `frontier.py --ds
  --ready` reports `needed` **759 / 317,413** — all five of the set's nodes gone — and the ready block
  drops the four rows and promotes the two rows that *depend* on them (113 and 1,187 silo). Nothing had
  been proved yet.
- **cause**: the ported test is the name tier. A scaffold that declares `Theorems/Thm_…`'s headline at
  the wrapper's name *is* the node; `frontier.py` reads declarations, not proofs, and `check_port`
  compares statements, so neither instrument can see a `sorry`.
- **fix / rule**: the baseline read must be taken **before** the scaffolds exist (it is the pre-scaffold
  read plus arithmetic that the landing record quotes), and the post-landing re-read only after every
  scaffold is sorry-free. The gate that certifies a scaffold has become a proof is
  `#print axioms` without `sorryAx` — not `check_port`, which is green at both ends. A scaffold's
  `1 ok` is a *statement* certificate and must never be quoted as a landing figure.
- **seen**: 2026-11-08, SET-AF34 §0.3 (the mid-wave read is recorded there as the counter-example).

## FR-0158 [verification] — `#print axioms` reads the *olean*, so the axiom gate is only meaningful after the module's own build

- **where**: the per-order axiom gate on a module that was scaffolded with `sorry` bodies and then filled
  (SET-AF34, the `ℚ` row of `Cusp/LevelOneObstruction.lean`).
- **symptom**: the module is `sorry`-free and `check_port` reads `3 ok / 0 mismatch / 0 missing`, the edit
  loop (`lake env lean <file>`) is silent, and yet `#print axioms` on the headline reports `sorryAx`.
- **cause**: `#print axioms` is a `lean` run on a *probe file* that **imports** the module, so it reads
  `.lake/build/lib/lean/.../<Module>.olean` — which still holds the scaffold's `sorry` bodies. The edit
  loop does not write oleans, and `check_port` never elaborates the proofs. FR-0033 is the general case
  ("a `Replayed` line is not evidence that its `.olean` exists"); this is the same file/olean split with
  the direction reversed: the *source* is newer than the olean and nothing says so.
- **fix / rule**: run `flock .lake/flt_build.lock timeout 110 lake build <Module>` **before** the axiom
  gate, and re-run the gate if the module was edited after its last build. A `sorryAx` in a module whose
  source has no `sorry` is a stale-olean report, not a proof bug: check the build log's timestamp before
  hunting for a hidden `sorry`. The gate order is build → axioms, never the reverse.
- **seen**: 2026-11-08, SET-AF34 order C (the module landed green and the axiom line was clean once the
  module build had run).

## FR-0160 [process] — the surface gate's default is *promote*, and an order that says "keep private" caps the checked surface

- **where**: the per-order surface gate (recipe §5) in a wave of four sets; SET-AF38A.
- **symptom**: three modules of the same wave read `check_port` at **2 ok** (two headlines) after landing,
  one at **45 ok**, one at **5 ok** — the same instruction ("run the surface gate, promote what the
  checker accepts") produced three different checked surfaces, because two orders added "the pin states
  these helpers `private`, so keep them private" and one did not.
- **cause**: the surface gate's `ok` count is the *only* instrument that measures how much of the pin's
  mathematics the port has actually transcribed, and it can only see public declarations. A helper the pin
  states publicly but the port keeps `private` is invisible to it; a helper the pin states `private` is
  invisible either way. So "match the pin's visibility" is the right rule *only* for pin-`private`
  helpers — for pin-public ones it silently shrinks the checked surface, and a later reader cannot tell a
  2-ok module from a 34-ok module.
- **fix / rule**: the default is **pin-public ⇒ public** (promote; that is what the gate is for) and
  **pin-`private` ⇒ `private` unless a landed consumer needs it**. Measured on SET-AF38A: stripping
  `private` from the 32 pin-public helpers moved the module from `2 ok` to **`34 ok, 0 mismatch,
  0 missing, 0 own`**, no proof changed, zero warnings — the checked surface of that module went up by a
  factor of 17 for one edit. Two declarations stay outside the tier and both are legitimate: a restated
  helper the checker still matches (`exists_cocycle` — it lands `ok`), and a port-side extraction the pin
  does not have (`slash_eq_smul_changeLevel`, `missing` if public, so `private`).
- **seen**: 2026-11-08, SET-AF38A (the other three modules of the wave: 35A and 35B are pin-`private` and
  stay private, 37A is 81/82-public and was promoted).

## FR-0161 [tooling] — `--with-defs` closes over *statement* vocabulary, so an unported `Def_` module can still block a proof

- **where**: the definition-gate check of the scoping recipe (§0: "`--with-defs` adds the pin
  `Definitions/Def_*.lean` closure … worth running once per set").
- **symptom**: the check returns a short list of `Def_` modules, all ported, and the set reads gate-free —
  then the proof needs a lemma that lives in a `Def_` module **not** on that list. SET-AF38's degeneracy
  lift needed `diagMatInt` and `diagMatInt_map_eq`, both stated in
  `Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean`, which the pin's `S_` file imports and the port
  does **not** have (no `FreyPackage.ModMCarrier` anywhere). Two declarations of it had to be carried into
  the module and marked `own:`; the advise closure never mentioned the module.
- **cause**: `--with-defs` walks the definitions that appear in the targets' **statements**. A `Def_`
  module imported by the pin file for its *lemmas* — the `exists_cocycle_rescale`/`diagMatInt*` family here
  — is not in that closure, and the readiness test cannot see it either (a `Definitions/` module is not a
  graph node). The gate is therefore a *statement* gate, exactly as `needed = 1` is a premise claim.
- **fix / rule**: run the statement-closure check **and** the raw import check: for every
  `import Definitions.Def_*` line of the target `S_` files, ask whether the port has the module (the
  `port_advise` header prints the target files; a two-line grep of the pin file's imports against the port
  tree catches it). Treat a missing module as a deferral candidate, not as a gap to improvise around: the
  two carried declarations are recorded `own:` this time, but a larger one is a definition-layer set.
- **seen**: 2026-11-08, SET-AF38 (the degeneracy lift); the same class as the `idelicHaar` deferral of
  SET-AF39 §1, where the missing module *was* vocabulary.

## FR-0162 [tooling] — `dedup.py --within` is a *boolean flag*, not a pattern selector; the recorded invocation form fails

- **where**: gate 5 of the two orders of SET-AF41 (`dedup`/`move_dead` on the new modules).
- **symptom**: `python3 dedup.py --within ../FLTForHuman/LanglandsTunnell/WhittakerODENearZero.lean`
  answers `no module matches ['../FLTForHuman/…']`, and the "corrected" form the manager sent next,
  `--within LanglandsTunnell.WhittakerODENearZero`, fails the same way. Both orders lost a tool call to it.
- **cause**: `--within` and `--cross` are mutually exclusive **flags** selecting the comparison scope
  (inside one module / across modules); the module selection is `--module PATTERN` (repeatable) or a
  positional pattern. The briefs of earlier waves wrote `dedup.py --within <module>`, which reads as if
  `--within` took the module.
- **fix / rule**: the working forms are
  `python3 dedup.py --within --module <ModuleName> [--min-cost N]` and
  `python3 dedup.py --cross --module A --module B`. `move_dead.py` is different and does take a file
  path (`--source <path>`, relative to `tools/deps` unless absolute), and its leading number is the count
  of *dead* declarations, so `0 declarations, 0 lines` is the clean answer rather than a parse failure.
- **seen**: 2026-11-12, SET-AF41 (both orders; the AF41A agent found it, the manager had mis-corrected it
  once).

## FR-0163 [mathlib] — v4.34 fires `linter.unnecessarySeqFocus`/`unusedTactic` on the pin's `convert … <;> try … rfl` idiom

- **where**: four sites of the Bessel file, SET-AF41B: `odeC`'s `hGd` (pin `:46`), `gapC`'s `hGd`
  (pin `:158`) and `hBd` (pin `:195`), `twoTermAp`'s `hud` (pin `:274`), all of the shape
  `convert h using 1 <;> try with_reducible_and_instances rfl` followed by `all_goals try rfl`.
- **symptom**: the transcription compiles but gate 1 (zero warnings) fails with `unnecessarySeqFocus` /
  `unusedTactic` on tactics that were silent at the pin's toolchain.
- **cause**: the pin's idiom deliberately runs a *focusing* combinator over zero-or-more goals, which the
  newer linters read as an unused sequence point; and its `convert` orientation leaves the goal's
  orientation opposite to what `HasDerivAt.congr_deriv` produces.
- **fix / rule**: write the intent directly — `refine h.congr_deriv ?_` then the coefficient identity
  (`simp only`/`linear_combination`/`ring`) — and check the **sign** of the coefficient, because the
  `congr_deriv` orientation is the reverse of the pin's `convert` one (measured twice here). Never
  silence the linter: the four rewrites were statement-preserving and cost one line each.
- **seen**: 2026-11-12, SET-AF41B.

## FR-0164 [checker] — a pin hypothesis the pin never uses: `linter.unusedVariables` vs statement fidelity

- **where**: the Bessel headline `norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori`
  (pin wrapper `:11`), which carries `(hν : 0 ≤ ν.re)` and never uses it; SET-AF41B.
- **symptom**: the port's proof is complete and silent except for one `linter.unusedVariables` warning on
  `hν`; both bounds hold with no sign condition on `Re ν`.
- **cause**: a redundant hypothesis in the pin's statement. The two obvious cures are both forbidden here:
  renaming the binder to `_hν` is a **statement** change (the checker compares binder text — AF36's
  recorded `_hν` rejection), and `set_option linter.unusedVariables false` silences a linter.
- **fix / rule**: keep the hypothesis and *reference* it once — `have hν₀ : 0 ≤ ν.re := hν` immediately
  after the proof's first `set` — so the linter sees a use and no mathematics changes. Record it in the
  set's brief as a deviation with the reason, and never as a `set_option`.
- **seen**: 2026-11-12, SET-AF41B.

## FR-0165 [tooling] — a `shape` cluster whose statements are *identical* is a merge, not a keep

- **where**: `dedup.py --within --module ODENearZeroBounds` on the landed SET-AF41B module.
- **symptom**: the worker reported `1 duplicate cluster, 106 lines removable` between
  `OdeCAux.main` (euler pin file `:19`) and `Gap41.odeC` (bessel pin file `:16`) as `tier shape`, and
  kept it with the reason "different namespaces, non-interchangeable statements". Normalising the two
  statements modulo their names shows they are **the same theorem**, binder for binder and conclusion for
  conclusion: the pin wrote its first-order argument `y f' = b f + h` twice, in two files.
- **cause**: the `shape` tier is evidence, not a verdict, and "different namespaces" is never a
  mathematical difference. The keep/merge decision is the manager's (`instructions.md`: `dedup` after the
  order) and it turns on the **statement** comparison, which `dedup` does not make for you.
- **fix / rule**: for every `shape` cluster, normalise the two statements and compare before accepting a
  keep. Identical → prove once and keep the pin's second name as a one-line application; the module keeps
  its checked surface (10 → 10 `ok` here) and the duplicated body disappears (106 → 8 removable lines,
  the residual being the pin's own duplicated *statement*, which the port keeps on purpose). Different →
  the keep stands and the reason goes in the brief.
- **seen**: 2026-11-12, SET-AF41B (the manager merged it; the module went 795 → 694 lines).

## FR-0166 [tooling] — a scaffold carries the *statement's* import closure, not the proof's

- **where**: the four scaffolds of the AF42/AF43 wave, generated programmatically from the pin's `S_` files
  (statements + `sorry` bodies), then handed to three workers.
- **symptom**: two of the three workers hit a proof that needed a theorem sitting in a port module the
  scaffold did not import — four times in all: `CongruenceSubgroup.Gamma_div_le_gamma1_inf_Gamma_sup_zpowers`
  (`NumberTheory/ModularForms/CongruenceSubgroupLattice`), `CuspForm.IsEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul`
  (`ModularForms/Level/DegeneracyString`), `EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow`
  (`ModularForms/Eisenstein/ResidueSumQExpansion`) and `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`
  + `ModularForm.finiteDimensional_of_isArithmetic` (`ModularForms/WeightOne/Gamma1IntegralBasis`). Each was
  a report and a manager ruling, not a silent import.
- **cause**: the scaffolder maps the pin's `Definitions/Def_*` imports to port homes and checks the
  statements against them, and `check_port` verifies **statements** only — so a module can read
  `55 ok / 0 mismatch / 0 missing` while lacking every premise its 54 bodies need. The pin's `Theorems/`
  imports are the *proof's* premise list, and they are invisible to the statement gate (the same split as
  FR-0049's and FR-0161's, seen from the scaffolder's side instead of the shelf's).
- **fix / rule**: when generating a scaffold from a pin file, also emit the mapping from its
  `Theorems/Thm_*` imports to their port homes, and put those imports in the header before handing the
  module out (if the mapping is not immediate, state in the order which premises are still unresolved).
  The recipe's §4 import-direction rule is about the *proofs*; a statement-clean scaffold is not yet an
  import-clean one. The workers' four reports cost one ruling each and no rework, because the rule they
  followed — report, do not silently add — is what kept the header honest.
- **seen**: 2026-11-12, AF43A (2 imports), AF43BC (2 imports). AF42 needed none: its four pin files cite
  exactly the five `S_` files the previous set landed, which the scaffold had already imported.

## FR-0167 [process] — a premise whose port home sits above the home: import the closure, or re-prove privately?

- **where**: `CuspForm.StableU`, needed by `CuspForm.heckeULinH_comm` (AF43BC order B). Its port is
  `CuspForm.stableU` in `ModularCurve/Period/HeckeStability.lean:94`, whose own premise
  (`ModularForm.heckeU_slash_eq_self_of_mem_GammaH`) is a further ModularForms module, and whose 16-module
  closure imports `EichlerShimura/PeriodOf`.
- **symptom**: a one-hypothesis need, satisfiable three ways — import a `ModularCurve` module into a
  `ModularForms` module; re-prove `StableU` in-module; or duplicate the ported proof.
- **cause**: the port's directory layering (`ModularForms` below `ModularCurve`) is not the import graph;
  the recipe's rule is that the *home* must be able to import its premises, which a `ModularForms` module
  can do for a `ModularCurve` premise without a cycle (nothing imports the new module). The real cost is
  the closure, not the direction.
- **fix / rule**: decide on **measured closure size**, and record the side taken with three facts (the pin
  line of the use, the port declaration that would have been imported, and the line count of the
  alternative). Concretely, this wave's rule: *import* when the module is the port home of a consumed pin
  premise and its closure is in the same weight class as the module's own (here 3 and 53 modules against
  existing 52–56); *re-prove privately* when the closure drags an analytic layer for one hypothesis and
  the re-proof is about one screen from in-closure facts. AF43BC took the second route: a **62-line
  `have`** inlined inside the consumer, so no declaration and no checker surface change.
- **seen**: 2026-11-12, AF43BC order B; the same test ruled the four imports of FR-0166 in.

## FR-0168 [tooling] — measure heartbeat headroom by *lowering* the gate, not by asserting it

- **where**: the heartbeat gate ("the module fits the default 200,000; the pin's override is not carried"),
  applied to `NebentypusSeparation.lean` (AF43A), whose pin file asked for `maxHeartbeats 3200000`.
- **symptom**: "it fits 200,000" is satisfied by a module whose worst proof needs 190,000, and that fact is
  invisible in a green gate — the next edit to that proof then breaks the build for a reason nobody sees
  coming.
- **cause**: the gate measures a *pass*, not a margin.
- **fix / rule**: run the same elaboration with `-DmaxHeartbeats=40000`, `20000`, `10000`, `5000`, `1000`
  and record the first value at which a declaration fails; the margin is then a number. Measured on
  AF43A: silent at 40,000 / 20,000 / 10,000, three declarations failing at 5,000 (`slashV_E`, `induct`,
  `main`) and 101 at 1,000 (the sanity check that the option bites) — so the worst proof is in [5k, 10k],
  a 20×–40× margin, and the pin's 3,200,000 override is genuinely unnecessary rather than merely dropped.
- **seen**: 2026-11-12, AF43A. The same wave's other two modules were silent at the gate with no override
  to remove.

## FR-0169 [mathlib] — a v4.34 `whnf` divergence: the pin's `Summable.mul_left` one-liner does not elaborate at any budget

- **where**: `DiamondDivisorSum`'s `FracLemma` summability step (AF43BC order C), the pin's
  `(summable_pow_mul_geometric_of_norm_lt_one 4 (by rwa [norm_norm])).mul_left 2`.
- **symptom**: a deterministic timeout in elaboration — reproduced **at 2,000,000 heartbeats**, so it is
  not a budget problem — while the pin's toolchain accepted the same text.
- **cause**: with the bound's ring still undetermined, v4.34's `whnf` diverges on the `.mul_left`
  projection before typeclass search has fixed the codomain; the pin's toolchain resolved the same term
  eagerly.
- **fix / rule**: fix the ring explicitly by *naming the intermediate summable function* —
  `have h0 : Summable (fun m : ℕ => (m : ℝ) ^ 4 * ‖exp‖ ^ m) := summable_pow_mul_geometric_of_norm_lt_one 4 (by …)`
  then `h0.mul_left 2` — and expand the following `gcongr` into a `calc`. Same mathematics, same constants;
  a timeout that survives a 10× heartbeat raise is an elaboration divergence and must be reported as one,
  not silenced by an override (which is what the wave's heartbeat gate forbids anyway).
- **seen**: 2026-11-12, AF43BC order C.

## FR-0170 [lean] — inside `namespace ValuationSubring`, mathlib's own `add_mem`/`neg_mem`/`mul_mem` shadow `Subring`'s

- **where**: the AF44 wave, both orders. Seven sites in `ValuationSubringPolynomial.lean`, three in
  `ValuationSubringPartialFraction.lean`.
- **symptom**: a proof transcribed verbatim from the pin fails at `add_mem (hp j) (hq j)` with a type
  mismatch, although the same text compiles at the pin.
- **cause**: mathlib v4.34 declares `ValuationSubring.add_mem`/`neg_mem`/`mul_mem` (`Mathlib/RingTheory/
  Valuation/ValuationSubring.lean:70,72,74`) with explicit `(x y : K)` — they are the *structure's* closure
  lemmas, not `Subring`'s `AddMemClass` instances. The pin states its declarations inside
  `namespace P2MW.S_…`, where the bare name resolves to `Subring.add_mem`; the port nests them inside
  `namespace ValuationSubring` (the pin's mathematical namespace), so the bare name resolves to the
  projected one, which wants its two points.
- **fix / rule**: pass the points (`A.add_mem _ _`) or spell the class form
  (`AddMemClass.add_mem`/`NegMemClass.neg_mem`/`MulMemClass.mul_mem`). More generally: **when a port nests
  a pin's task-label namespace under a mathlib namespace, re-check every unqualified lemma name the pin's
  proofs use** — the nesting can change resolution. A probe (`#check`) inside the real namespace settles it
  in one line.
- **seen**: 2026-11-12, AF44A (7 sites) and AF44B (3).

## FR-0171 [process] — an order's consumer suggestion must be checked against the *hypotheses*, not only against the statement

- **where**: the consumer zones of AF44A and AF44B (a suggested `t = X` and a suggested `t = 1 + X`).
- **symptom**: both suggestions are untypeable, and not because of a name or a shape: they are *instances
  that cannot exist*. The constancy criterion needs `A.valuation (t.coeff 0) = 1`, and `X.coeff 0 = 0`, so
  no valuation subring admits `t = X`; the partial-fraction criterion needs a unit at `0` with all higher
  coefficients *small* (`valuation < 1`), and `(1 + X).coeff 1 = 1` has valuation `1`, which no valuation
  subring of a field can make small. Both orders' workers replaced them with the pin's own good shape
  `t = 1 - C c * X` (`A.valuation c < 1`), recorded in the consumer files.
- **cause**: an order's suggested composition is a *mathematical* claim about the theorem's hypotheses, and
  the manager writes it from the statement's shape; the AF36 §6.2 lesson covered a different failure (a
  name that does not exist in the port yet) and this one is its sibling.
- **fix / rule**: when suggesting a consumer instance, check the instantiation against each hypothesis's
  own side condition (`valuation (coeff 0) = 1`, `< 1`, a positivity, a support condition) before writing
  it into an order — or state it as "read the theorem at the pin's own `IsGood`/base shape" and let the
  worker pick the instance. A substitution is legitimate and cheap (two in this wave, both one line of
  documentation), but the order should not spend a worker's judgment on an impossible instance.
- **seen**: 2026-11-12, AF44A and AF44B (the wave's third and fourth such substitutions: AF41A's arithmetic
  slip and AF42's `S = {2}` were the first two).

## FR-0172 [lean] — the pin closes its label namespaces with a *qualified* `end`, which cannot resolve inside the port's nested namespace

- **where**: both orders of AF45; every pin file that nests its label namespace under a mathematical one
  (`end AlgebraicCurve.RegularProlongation.W7XK3FI`, `end ValuationSubring.CompleteSplitting`).
- **symptom**: a scaffold generated by copying the pin's text fails to elaborate at its last line with
  `Unexpected name 'RegularProlongation' after 'end': The current section is unnamed`, and an earlier line
  `Unknown identifier 'RegularProlongation'` — while `check_port` still reads the module green, because it
  matches statements and never elaborates.
- **cause**: Lean resolves the head of a qualified `end` name against the **current** namespace. The pin's
  declaration sits at the outermost level, where `end A.B.C` closes `A.B.C`; the port nests the same block
  inside `namespace A / namespace B`, where the qualified form means `A.B.A.B.C`.
- **fix / rule**: the port closes the *bare* name (`end W7XK3FI`), and it is a pure scoping change with no
  effect on any declaration's name. When a scaffolder copies a pin file's text, it must rewrite
  `end <dotted>` to `end <last component>` for every namespace the scaffold re-nests — and then
  **elaborate**, because the statement checker will not catch it (the same blind spot as FR-0166).
- **seen**: 2026-11-12, AF45A and AF45B (both scaffolds, caught by the manager's first elaboration).

## FR-0173 [lean] — v4.34 ships `linter.style.haveILetI` **on by default**, so the pin's `haveI`/`letI` walls must be respelled

- **where**: AF45B, order B2's `core` (11 sites: pin `:18, :19, :31, :37, :38, :213, :214, :239, :245,
  :247, :249`); the same device as AF41B's `haveI : <class> :=` note in SET-AF40's brief.
- **symptom**: the transcribed proof is correct but emits `linter.style.haveILetI` warnings, and the gate is
  zero warnings.
- **cause**: v4.34 enables that style linter by default; its own documentation says the point is that Lean 4's
  `have`/`let` **already** register local instances for a proposition goal, so `haveI`/`letI` is redundant.
- **fix / rule**: rewrite `haveI : C := …` → `have : C := …` (and `letI` → `let`) at the site; the
  instance still enters the local context and every downstream typeclass goal still fires. This is a
  *rewrite*, not a silencing: no `set_option`, no `omit`. Measured here: 11 sites, the module elaborates and
  is silent at `-DmaxHeartbeats=30000`.
- **seen**: 2026-11-12, AF45B (and AF40B, where the same rewrite was recorded in passing).

## FR-0174 [lean] — the `ValuationSubring` namespace shadows more than the closure lemmas (supersedes FR-0170)

- **where**: AF45B, inside `namespace ValuationSubring`; three distinct shadowings in one module.
- **symptom / cause**: v4.34 declares, in `namespace ValuationSubring` itself, names that also exist at the
  root of mathlib with a different meaning or binder order:
  1. `ValuationSubring.add_mem`/`neg_mem`/`mul_mem` (explicit `(x y : K)`), so the pin's bare
     `add_mem (hp j) (hq j)` must pass the points or use `AddMemClass.add_mem` / `NegMemClass.neg_mem`
     (`_root_.neg_mem` does not exist);
  2. `ValuationSubring.eq_top_iff` (`O = ⊤ ↔ ¬ O.valuation.IsNontrivial`), so the pin's bare `eq_top_iff`
     must be `_root_.eq_top_iff` — a silent *meaning* change, not a type error, if both sides happen to
     elaborate;
  3. `IsLocalHom` is now a class whose single field is `map_nonunit`, so the pin's `h.1` on an `IsLocalHom`
     hypothesis must be `.map_nonunit`.
- **fix / rule**: for any port declaration that nests inside `ValuationSubring` (or any mathlib namespace
  with same-named lemmas), re-check every *unqualified* lemma name the pin's proof uses against the
  namespace — a one-line `#check` inside the real namespace settles each. Prefer the fully qualified root
  name or the class form; never rely on the bare name resolving as it did at the pin.
- **seen**: 2026-11-12, AF45B (10 sites across the three shadowings); FR-0170 recorded the first of them
  for AF44.

## FR-0175 [port] — the same fully-qualified name declared in two port modules, and the import that exposes it

- **where**: `FLTForHuman/AlgebraicCurve/RegularProlongation.lean:160` and
  `FLTForHuman/AlgebraicCurve/GaussProlongation.lean:67`, both declaring
  `AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers`; AF46B is the first module that
  needed to import *both*.
- **symptom**: `import FLTForHuman.AlgebraicCurve.GaussProlongation` fails with
  `environment already contains 'AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers'
  from FLTForHuman.AlgebraicCurve.RegularProlongation` — while each module *on its own* is green
  (`check_port` clean, silent build) and nothing else in the tree notices.
- **cause**: two early port modules were assigned the same pin node (`Thm_..._coeff_mem_of_aeval_mem_integers`)
  and both transcribed it, one under the namespace block and one fully qualified. The statement checker
  matches per module, so it reports `ok` in both; the duplication is only visible to the *elaborator*, and
  only when a consumer imports both. This is the import-level twin of the `shape`-cluster problem FR-0165
  records.
- **fix / rule**: keep the declaration in the module that owns its namespace (here `RegularProlongation.lean`,
  which had already wired the node) and delete the fully qualified copy from the sibling; its own proofs
  then use the imported copy, since the sibling already imports the owner. Remove the loser's two
  `spec-pin:` lines for that node and expect its `ok` count to drop by exactly one (measured: 10 → 9) —
  that is the intended accounting (one pin declaration, one port copy), not a regression. Detection rule:
  when a *new* module needs two AlgebraicCurve modules at once, run the import before writing proofs; a
  clash is a one-line probe, and it is cheaper than a scaffold that cannot elaborate.
- **seen**: 2026-11-12, AF46B (the worker reported it at first belief; the manager made the dedup).

## FR-0176 [checker] — the statement checker compares **text**, so a name-resolution change reads `ok` while the meaning drifts

- **where**: AF46B, `psi_residue` (pin `S_…_exists_gaussBasis_…:327`); the sharpest instance the column has
  met of a general hazard.
- **symptom**: the pin's statement writes the bare token `residue`, which means `IsLocalRing.residue`. The
  port nests the same block inside `namespace AlgebraicCurve.RegularProlongation`, where a declaration also
  has a **field** called `residue` — so the bare token resolved to `RegularProlongation.residue` and the
  statement *printed identically* while meaning something else. `check_port` read it `ok` (it hashes
  normalised **source text**), and the "obvious" repair — qualifying the term as
  `IsLocalRing.residue` — turned the checker **red**, because qualification changes the text.
- **cause**: the statement hash is syntactic by design (it is what makes the checker cheap and stable), so
  any change of *resolution* under the same text is invisible to it. Nested namespaces are exactly where
  such a change happens: the pin's file sits in `P2MW.S_…`, the port nests under
  `AlgebraicCurve.RegularProlongation`, and the two shadow differently.
- **fix / rule**: restore the pin's *meaning* while keeping the pin's *text* — a file-local
  `local notation "residue" => IsLocalRing.residue` does it, and the checker stays green. More generally, on
  any module whose pin text uses a bare identifier that the port's namespace also declares (structure
  fields, `ValuationSubring.eq_top_iff`-style names, `add_mem`-style projections — FR-0170/FR-0174), check
  *what the token resolves to*, not only that the statement hashes. A `#check` on the elaborated statement,
  or reading the `#print axioms`/`#print` output, is the instrument; the checker is not.
- **seen**: 2026-11-12, AF46B (`psi_residue`, seven terms across the module).

## FR-0177 [mathlib] — `ResidueField` went from `abbrev` to `def`, so instance search no longer unfolds it

- **where**: AF46B, the `:407` instance-synthesis failure.
- **symptom**: `failed to synthesize instance` where v4.33 found one; the pin's file needs the instance
  `Module (R ⧸ I) (M ⧸ I • ⊤)` to fire *through* `ResidueField A = A ⧸ maximalIdeal A`.
- **cause**: v4.33's `ResidueField` was an `abbrev`, which typeclass search unfolds; v4.34's is a `def`, so
  the quotient-module instance no longer applies at `ResidueField`-typed goals.
- **fix / rule**: activate the instances the module itself declares — here `open scoped FinGeSol.Generic`
  (the port's scoped `Module`/`SMul` instances for `gaussRing`-modules) — rather than importing the pin's
  `attribute [-instance]` shim, which names pin instances the port does not have. The mechanical pass
  dropped that shim, and this is the correct replacement, not a workaround.
- **seen**: 2026-11-12, AF46B.

## FR-0178 [tool] — `--selfcheck`'s source tier is a *ported* tier, so a deliberate future-promote `SOURCES` row reads as ported

- **where**: the D–S shelf's scoping read (SET-AF47 §0), ten `ModularCurve` rows.
- **symptom**: `frontier.py --selfcheck` fails "source tier covered by the name tier" with ten
  `PhiGen`/`ModularPolynomialData` nodes that no port declaration carries; the shelf's frontier is
  1,704 / 827,574 instead of 1,694 / 823,223, and `needed [literal]` 724 / 303,267 instead of
  733 / 306,724 (`needed [F terminal]` is unchanged — none of the ten reaches the terminal mask).
- **cause**: `spec/old_check_stmts.py` lists those `Thm_` rows on purpose — the comments say the `S_`
  files are there so a later topic *would* verify the block's promoted declarations — but the source
  tier is used as evidence of porting, so a pin side that is not ported reads as ported. `twin_scan
  --node` reports `new` for each: the mathematics is not in the port under another name either.
- **fix / rule**: read the shelf with `--unport NAME` for each (the documented correction), quote both
  columns and say which marker set produced the corrected one. Register the inventory in
  `spec/METADATA-ISSUES.md` (MD-005) rather than deleting the rows in another column's wave — the
  correction is either a promotion or a wire close, and both are the phi workstream's call.
- **seen**: 2026-11-12, SET-AF47 §0 (ten rows; the first five were recorded in SET-AF41 §0 without an
  MD entry).

## FR-0179 [lean] — the pin's task-label namespaces (`W9OComposite`, `IndepMember`, `CompleteSplittingE`) are rectified in a new module, and the checker does not care

- **where**: SET-AF47's four scaffolds, all generated from the pin's text.
- **symptom**: copying the pin's `namespace W9OComposite` / `IndepMember` / `CompleteSplittingE` into a
  new module would put machine tokens in the public API (`ValuationSubring.W9OComposite.composite`), and
  `end ValuationSubring.IndepMember` does not even resolve once the block is re-nested (FR-0172).
- **cause**: the pin nests its proof-search labels *under* the mathematical namespace; the port's
  earlier valuation-subring modules kept them (AF44 §3.2), which is legal but carries the token.
- **fix / rule**: rename the label to a descriptive one (`Composite`, `Independent`,
  `CompleteSplitting`), close it with the **bare** `end <Label>`, and leave every declaration's last
  name unchanged — the checker matches last names, so no `spec/decl_markers.tsv` row is needed and the
  surface counts are unaffected (measured: 8 / 2 / 8 / 23 `ok`, 0 mismatch, 0 missing before a proof was
  written). This is a *scaffold-generation* rule: apply it when the module is first written, not as a
  later rename (a rename moves the checker key and costs a cascade).
- **seen**: 2026-11-12, SET-AF47 §2.

## FR-0180 [lean] — the pinned *def bodies* carry v4.34 deprecations the statements do not, and a mechanical scaffold inherits them

- **where**: SET-AF47's `locAt` (pin `S_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top.lean:347–424`)
  and two more sites in the same block.
- **symptom**: the generated module elaborated with `Set.mem_setOf_eq has been deprecated: Use
  Set.mem_ofPred_eq` and `zero_le' has been deprecated: Use zero_le`, inside a `def` the manager
  transcribed verbatim; a `def` cannot be left `sorry`-closed, so the deprecation is the manager's to
  fix, not a worker's.
- **cause**: only *proof bodies* are stubbed in a scaffold, so any deprecation inside a transcribed
  `def` survives; the AF46 drift orders never saw this because their defs were already in the tree.
- **fix / rule**: keep a small `DRIFT` table in the generation script and apply it to every generated
  body (`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `zero_le'` → `zero_le`, …), then elaborate the
  scaffold before it is dispatched — a scaffold that warns is not landed, and the worker's gate is
  silence.
- **seen**: 2026-11-12, SET-AF47 §2.

## FR-0181 [process] — a scaffold's imports must be closed over the *port* modules, not only over the pin's import lines

- **where**: SET-AF47's module `FieldTheory/ValuationSubringCompleteSplitting.lean`; the worker added
  the missing edge and reported it, the manager kept it.
- **symptom**: `bar_sup_bar_eq_top` (pin `S_…finrank_le_card.lean:583`, call at `:586`) applies
  `ValuationSubring.exists_le_forall_mem_iff_apply_mem`, whose home is `ValuationSubringComposite.lean`;
  the scaffold imported `Independent`, `Finrank` and `Approximation` but not `Composite`, so the proof
  could not be written — the lemma is a *sibling's*, not reachable through the three frozen imports.
- **cause**: the scaffold's import block was derived from the pinned file's own `import` lines, which
  point at `Theorems/Thm_*.lean` wrappers and `P2M.Util`, not at the port's modules. The pin's premise is
  therefore visible in the *inventory* (the order named A1's home) but absent from the *header*.
- **fix / rule**: when generating a scaffold, translate every pin-side premise into its port home and
  close the import block over those modules — the pin's `Theorems/` imports are the list to translate,
  not to drop. Cheap check before dispatch: for each declaration in the module, `#check` its premises
  from the scaffold's imports only.
- **seen**: 2026-11-12, SET-AF47 (one edge, 47C); SET-AF49 (`Mathlib.FieldTheory.KummerExtension` and
  `ValuationSubringCompleteSplitting`); and — the worst instance so far — SET-AF50A, where **two** port
  modules were missing (`AlgebraicCurve/Genus/DegreeIdentity` for the divisor-degree identity,
  `AlgebraicCurve/ResidueTheorem/RRAssembly` for `constantsAreBase_of_deg_eq_one`), blocking a whole
  dependency chain (`zsum_sub_algebraMap` → `zsum_phi_le` → `zsum_eq_zsum_residue` → the headline) while 42
  independent `sorry`s were unblocked. The worker computed the import closure of all 14 frozen project
  imports (32 modules) to prove the lemma was unreachable and asked; the manager granted the imports.
  **The rule, stated sharply**: translate *every* pin `Theorems/Thm_*` import a file cites into the port
  module that declares it — the audit's premise list gives the names, `tools/deps/build/af47-audit.py`-style
  scripts or a name→module index give the homes — and check *that* closure, not the pin's own import list.
  When the closure is uncertain, the order should say "add the specific project import you need and record
  it", instead of freezing a list the manager is not sure of.

## FR-0182 [lean] — a `local instance` does not travel through `import`: the consumer must re-install it

- **where**: `lean/spec/FieldTheorySetAF47CConsumer.lean`, consuming
  `ValuationSubring.CompleteSplitting.card_add_card_le_finrank`.
- **symptom**: the theorem's hypothesis carries `Module (ResidueField ↥(R.comap …)) (ResidueField ↥R)`;
  in a consumer that imports the module, that instance is not synthesizable and the hypothesis cannot be
  stated — although inside the module it is, because the module writes
  `attribute [local instance] residueAlgebra` twice.
- **cause**: `attribute [local instance]` scopes to the file (the section) it is written in; an importing
  file does not inherit it. With `ResidueField` a `def` in v4.34 (FR-0177) instance search does not
  unfold it either, so there is no fallback.
- **fix / rule**: the consumer repeats `attribute [local instance] <Module>.residueAlgebra` (the
  module's existing definition — do not invent a new named instance, and do not make it global). This is
  the consumer-side face of FR-0177 and belongs in the order's consumer instructions whenever a headline's
  *hypotheses* are stated over `ResidueField`.
- **seen**: 2026-11-12, SET-AF47 (47C consumer).

## FR-0183 [process] — a consumer instance must also be checked against the *lattice*, not only against the hypotheses (FR-0171, fifth instance)

- **where**: SET-AF47's 47A consumer zone (the composite criterion at `W = ⊥`).
- **symptom**: the suggested instance `W = ⊥` — and its reading `O' = ⊥` — is untypeable:
  `ValuationSubring` has `OrderTop` (`Mathlib/RingTheory/Valuation/ValuationSubring.lean:118`) but **no
  `OrderBot`**, and the bottom candidate `{0}` is not a valuation subring of a nontrivial field
  (`mem_or_inv_mem'` fails at `x = 1`).
- **cause**: the order's suggestion was written from the statement's shape (an order-theoretic
  "cut down"), and the hypothesis side was checked but not the *object* side: whether the lattice has the
  element at all.
- **fix / rule**: before writing an instantiation into an order, `#check` the *element* it names (here
  `(⊥ : ValuationSubring ℚ)`) as well as the hypotheses; when the lattice is one-sided, read the theorem
  at the side that exists. The substitution is legitimate and cheap (two readings: `W = ⊤` giving
  `O' = O`, and `O = ⊤` with `W = ℤ_(2)` giving the cut-down), but it should not be a worker's discovery.
- **seen**: 2026-11-12, SET-AF47 (47A consumer); FR-0171 recorded the hypothesis side of the same class.

## FR-0184 [tool] — `port_plan`/`port_advise` price against the *tree*, so a scaffold already in it reads as "already in the port"

- **where**: SET-AF48 and SET-AF49 (2026-11-12), both scaffolded before their briefs' price line was written.
- **symptom**: for AF48's two rows, `port_plan` on the scaffolded tree reads
  `already in the port (vetted) 2100` / **net new math lines 13** — for a set whose pin files are 2,173
  lines — and for AF49 it reads **20**. The briefs' real figures are ≈2,105 and ≈740.
- **cause**: `port_advise`'s substitute test is name/shape-anchored against **the port tree** (its own
  `PortIndex`), so the manager's freshly written scaffold statements *are* the substitute: the tool answers
  "how much of this is not yet declared anywhere", which after scaffolding is very little, and that is not
  the porting budget. (This is the pre-port tool meeting the post-scaffold tree — the mirror image of
  FR-0114, where a skeleton wire makes the *shelf* read the node as ported.)
- **fix / rule**: **price before you scaffold, or price a scratch tree.** Concretely: run
  `port_advise`/`port_plan` on the target nodes first, keep the JSON, and write the brief's budget table
  from it; a later re-run is meaningful only for a different node set. If a price must be taken after the
  scaffold exists, say so and label the number a lower bound.
- **seen**: 2026-11-12, SET-AF48 §1 and SET-AF49 §1.

## FR-0185 [tooling] — a declaration-inventory regex without Unicode subscripts truncates pin names, and the work order then states a wrong name

- **where**: SET-AF48's order for `RegularProlongationReducedPlace` (the manager's own inventory table).
- **symptom**: the table listed `coe_eval :173`, `residue_eval :181`, `residue_eval :188` — and, since two
  `residue_eval`s cannot coexist, the order told the worker they were "the pin's two copies in different
  namespaces". The pin's actual declarations are `coe_eval₂_constHom` (:173), `residue_eval₂_constHom`
  (:181), `residue_eval₂_ne_zero` (:188): the inventory's regex
  `[A-Za-z0-9_'.]+` stopped at the subscript `₂`, so three distinct names came out as two, one truncated
  and one duplicated.
- **cause**: the pin's auto-generated identifiers use Unicode subscripts (`₂`, `₀`, `₁`) — normal in this
  pin's `eval₂`-family names — and an ASCII-only name class silently truncates rather than failing.
- **fix / rule**: a name regex for pin inventories must accept the whole identifier alphabet
  (`[^\s(:]+` up to the declaration's binder, or explicitly `₂₀₁` etc.). Verify a generated inventory against
  the pin's own file once (`grep -c` of declarations) before pasting it into an order: the count must match,
  and a repeated name is the signal.
- **seen**: 2026-11-12, SET-AF48A's order; the worker followed the pin and reported the discrepancy (correct
  behaviour — the pin's text wins over a manager's table).

## FR-0186 [checker] — a headline that lands inside the pin's file-level `P2MW.S_…` namespace reads `1 ok`, because the checker matches *content*, not the name a consumer uses

- **where**: SET-AF51's `NumberTheory/NumberField/CompletedDedekindZeta/RegularizedZeta.lean` (found by the
  manager at the landing, after the worker's gates were green).
- **symptom**: the module's single headline was declared at
  `P2MW.S_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero.NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero`
  instead of `NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero`
  (the wrapper's name). `check_port --force` read **1 ok, 0 mismatch, 0 missing** in both cases, the module
  elaborated silently, `#print axioms` on the *mangled* name was clean, and the consumer zone compiled —
  because the worker had qualified the call with the mangled name.
- **cause**: the scaffold's slice for that pin file started at its `namespace P2MW.S_…` line (the other
  scaffolds start at the label namespace below it), so the wrapper's fully-qualified `theorem NumberField.…`
  was appended *inside* the pin's file-level namespace. The checker hashes normalised statement text and
  matches by name *tier*, so a declaration one namespace too deep is still "the same statement"; and the
  consumer zone, written against the same (wrong) name, cannot see the defect either.
- **fix / rule**: **assert the headline's name, not only its statement.** In the generation script, drop the
  pin's file-level `namespace P2MW.S_…` (it is tooling, like `p2m_*`); in the landing check, `#check` each
  wrapper's qualified name in a scratch probe **after the module's `lake build`** (`#check` reads the olean,
  so an unbuilt edit hides the defect — this cost one round trip here), and require the consumer zone to
  call the wrapper's name with no namespace prefix beyond it. A consumer that needs a `P2MW.`-prefixed name
  is the signal.
- **seen**: 2026-11-12, SET-AF51 (one module, one headline, fixed by deleting one line and one consumer
  qualification).

## FR-0187 [lean] — a `P.ord` argument that mixes a subtype coercion with a raw term costs ≥2,000,000 heartbeats; the pin's one-line `exact` does not fit in the port

- **where**: SET-AF50A, `AlgebraicCurve/RegularProlongationSumOrdResidue.lean`, the proof of
  `ord_add_algebraMap_eq_zero` (pin `S_…sum_ord_eq_sum_ord_residue…:101`).
- **symptom**: the pin's proof — `have := ord_eq_zero_of_isUnit P (isUnit_nonunit_add_algebraMap P hm hc); exact this`
  — times out at the 200,000-heartbeat gate (`whnf` timeout), and the worker measured that it needs
  **≥ 2,000,000** (probes `lean/tmp/af50/probe{7,9,11}.lean`). The statement is untouched and the module's
  other 459 lines fit at 100,000.
- **cause**: the `P.ord` argument is `↑(⟨m, _⟩ + ⟨algebraMap …, _⟩)` on one side and the raw
  `m + algebraMap K F c` on the other; `isDefEq` will not take the syntactic path and unfolds the
  `Subtype`/`Submonoid` coercion and the `ord` definition to compare them.
- **fix / rule**: never ask for that defeq — rewrite *through* the coercion instead of unifying under it.
  The replacement used: `obtain ⟨w, hw⟩ := …; have hwF := congrArg Subtype.val hw; rw [← hwF]; exact
  P.ord_coe_unit w`. This is the §6 "spell the terms / name the bridge" family (the zeta and `Subtype.val`
  rows), with the specific tell that the *pin* proof is one line: a one-line pin proof that needs a
  seven-figure budget is always a defeq trap, never a long proof.
- **seen**: 2026-11-12, SET-AF50A (one declaration; measured with a probe ladder, no cap raised).

## FR-0188 [tooling] — four ways a mechanical scaffold generator fails silently, and the checks that catch each

- **where**: the SET-AF47→AF53 generator (`tmp/af4*/gen.py`, one script evolved across seven sets).
- **symptom / cause / check**, in the order they bit:
  1. **Name regex without Unicode subscripts** truncates pin names and manufactures a duplicate
     (`coe_eval₂_constHom` → `coe_eval`, two `residue_eval₂_*` → one repeated `residue_eval`). Check: the
     declaration count and the name list against the pin file (`grep -c '^theorem\|^def'`), and a repeated
     name is the signal. (FR-0185.)
  2. **A slice that starts at the pin's file-level `namespace P2MW.S_…`** leaves the wrapper's
     fully-qualified headline *inside* it; the checker reads `1 ok` and the consumer compiles against the
     mangled name. Check: the slice starts at the first *label* namespace, and `#check` each wrapper's
     qualified name after `lake build`. (FR-0186.)
  3. **`stub_theorem` cutting at the first `:=`** breaks any statement that contains a `letI := …` term
     (the adelic Haar `main`: `(letI := glBorel … , … = c • μa.prod μf) := by`), producing a parse error
     deep in the statement. Check: cut at `:= by`, fall back to the first `:=` only when the declaration's
     body is a term.
  4. **A slice that stops before the label namespace's `end`** (or carries the pin's `open <Label>` after
     it) leaves the headline nested one namespace too deep, or an `unknown namespace` error. Check: every
     slice boundary is a line of the pin's own `end`-list, and the generated file's `namespace`/`end`
     balance is asserted.
  Two more that are not the generator's fault but the *order's*: a frozen import block derived from the
  pin's `Theorems/` lines rather than from the port's homes (FR-0181), and a `lake build` that replays
  dependency warnings into the gate's log (grep for the module's own filename before reporting silence).
- **rule**: **elaborate the scaffold before dispatching it, and run `check_port` plus a `#check` of every
  headline.** All four generator failures above are caught by those two commands; none is caught by the
  statement checker alone.
- **seen**: 2026-11-12, SET-AF47→AF53 (each failure cost at most one iteration because the scaffold was
  always elaborated before dispatch).

## FR-0189 [instance] — `NormedAddCommGroup (NumberField.mixedEmbedding.mixedSpace K)` needs `open scoped Classical`

- **where**: `AutomorphicForm/Adelic/TestFactorIntegral.lean` (SET-AF55, the pin's `ARCHCONV` prelude
  rectified to `ArchConvIntegral`).
- **symptom**: with `open scoped Topology Pointwise ContDiff` — the pin's line minus one word —
  `scoped instance : NormedAddCommGroup (PP F) := Prod.normedAddCommGroup` fails with
  `failed to synthesize instance of type class NormedAddCommGroup (Xm F)`, then a cascade
  (`NormedSpace ℝ (PP F)`, `ContDiff ℝ ∞` on `Xm F × PP F`). The statement is fine; the *instances* are
  what is missing.
- **cause**: `mixedSpace K` is a mathlib `abbrev` for
  `({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)`. The `Pi`
  normed-group instance needs `Fintype` of each index, and `Fintype` of a *subtype* needs
  `DecidablePred` — which is `Classical.propDecidable`, hence only in scope under `open scoped Classical`.
  `mathlib`'s own `NumberField.InfinitePlace.fintype` is declared `open scoped Classical in … protected
  noncomputable instance`, so the `Fintype (InfinitePlace K)` half is there either way; the subtype half
  is not.
- **fix / rule**: keep the pin's `open scoped` line verbatim — in particular the `Classical`, which reads
  as boilerplate and is load-bearing. The tell is that an *instance* search fails on a type the file's
  statements use verbatim; the cure is to compare the file's `open scoped` line with the pin's, not to
  start a `show`/`change` round.
- **corroboration**: `AutomorphicForm/Adelic/RightConvRegularity.lean:224` does the same
  `inferInstance` successfully because that file opens `Classical` elsewhere — a probe copied from it
  fails unless the `open scoped Classical` travels with it.
- **seen**: 2026-11-13, SET-AF55's scaffold pass (one elaboration round, no proof effort spent).

## FR-0190 [homing] — the subject home is a *legacy* module: home one import above it, and record the debt

- **where**: SET-AF55's A8 (`AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot`,
  56 silo). Its only premise and its whole subject are `Cusp/CutWeightDecomposition.lean`.
- **symptom / cost**: appending it there requires migrating that module *in this wave* — the module is
  still wired through the frozen `spec/old_check_stmts.py` (`PORT_FILES`), so "touch it and bring it up to
  standards" means a `spec-pin:` wire over a 906-line pin source, deletion of the `PORT_FILES` row, and a
  public-surface diff of ~76 declarations (most of them the pin's private prelude, transcribed private and
  therefore `MISSING` in the checker's reading) — a set-sized piece of work for a 56-line row.
- **rule** (a refinement of the scoping recipe's §4 "if the subject demands that module, put the
  declaration there and migrate in the same touch"): the rule presumes the migration is *proportionate*.
  When the row is small and the legacy module's public surface is large, home the row **one import above**
  the legacy module, state in the module header that the subject home is the legacy module, and register
  the move as a debt to be paid when that module is next opened. Do **not** silently duplicate the
  subject into a new module as if the legacy module did not exist, and do not stretch the wave to pay a
  migration the row does not need.
- **seen**: 2026-11-13, SET-AF55 A8; the debt is recorded in that set's brief §3.3.

## FR-0191 [homing] — a home is "above its premises" only if it is above their **modules**; the three-line check that decides it

- **where**: SET-AF55's first cut. A1/A2 were appended to `ArchDerivRightConv.lean` /
  `ArchDerivRightConvComplex.lean` beside their `_ofChar` twins, and A6 to `ArchCutProjector.lean`
  beside the projector engine it extends.
- **symptom**: all three rows are *unwritable* in those modules. `ArchDerivRightConv` is **below**
  `LeftCasimirTestFn`, which is where the general `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite`
  (`:552`) and its complex twin (`:1022`) live — so A1/A2's key premise is unreachable and the
  `_ofChar` twin's proof cannot be replayed. `ArchCutProjector` is below `ArchApproximation`, which
  holds `exists_rightConv_eq_of_archCutProjector` and the `lamData` helpers its proof needs.
- **cause**: the scoping audit asked two questions — "is the premise *ported*?" (yes) and "is the
  home's *subject* right?" (yes) — and not the third: **"is the home above the premise's module?"**
  The recipe's §4 step 3 asks for it; the plan checked it for order B's new modules and took it for
  granted for the appends, because the twin's *statement* sits in the same file as the home and the
  premise's *name* appears in the same module's source. Both are the false positives §4 already lists.
- **check** (run it before scaffolding, not after): build `module -> imports` over `FLTForHuman` and
  require `premise_module ∈ closure(home)` for **every** premise of **every** row. Three lines of
  Python over `grep '^import FLTForHuman'`; it is the whole test. Watch the direction — `closure(home)`
  must *contain* the premise's module, not the other way round (the first version of this check here
  printed the verdict inverted, and the worker's report is what caught it).
- **fix taken**: re-home, do not refactor. A1/A2 → `LeftCasimirTestFn` (which holds the general
  engines and A7), A6 → `ArchApproximation` (which holds the reformulation its statement uses). No
  statement changed; the three first homes are restored to their pre-set state.
- **the same failure in miniature, and the ruling it forced**: four of A3's prelude rows *are* ported
  (`comp_mem_typeSubmodule_of_map`, `comp_mem_iSup_of_forall`, `commute_of_glArch_eq_one_of_glFin_eq_one`
  in `RightConvIntegral`; `eq_of_glArch_eq_of_glFin_eq` in `Cusp/SpectrumLift`) but those modules are
  above `TestFnInvariance`, so importing is the same cycle. The four generic proofs are transcribed
  in `TestFnInvariance` — what the pin itself does — and their `shape` clusters in `dedup.py` are the
  recorded ruling (their real home is a `RepTheory` module below both; registered in
  [../CARRY-FORWARD.md](../CARRY-FORWARD.md)). Do not delete either side.
- **second half, the build-side tell**: restoring a source file without rebuilding it leaves a **stale
  `.olean` that exports the removed declarations**, and the next elaboration of an importer fails with
  `` `X` has already been declared `` — the mirror of the playbook's "a stale `.olean` reads as a
  missing declaration". After any re-home, build the vacated modules **before** elaborating the new
  homes: `lake build <vacated> <vacated>` then `lake env lean <new home>`.
- **seen**: 2026-11-13, SET-AF55 (worker report at first pass; no proof effort spent on the three rows
  before the fix).

## FR-0192 [defeq] — a `have` stated over `a ∈ memberSubmodule` cannot be rewritten into a goal over its subtype

- **where**: SET-AF55 order B, the orthogonality row
  (`AutomorphicForm.CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant`),
  the pin's `inner_toCarrier` (`S_…:108`).
- **symptom**: the pin states `inner_toCarrier` over `(a b : GL₂(𝔸) → ℂ)` with
  `(ha : a ∈ memberSubmodule Φ₀ ξ)` and rewrites it into a goal whose `toCarrier` arguments are the
  *subtypes* `⟨↑ψ, ⋯⟩`. At v4.34 the rewrite fails at **application elaboration** — not at `rw`'s
  matching: `Application type mismatch: The argument ξ …`. The pattern unfolds the carrier to
  `IsAutomorphicFnAt F (fdPins F Φ₀) ξ ?a` and then demands `↥⊤ ≡ ↥(fdPins F Φ₀).Z`, which is false.
- **cause**: FR-0187's family — a `Subtype` coercion over `pins.Z` against a raw `⊤` — but here the
  unfold happens while *elaborating the lemma's type at its use site*, so no `congrArg Subtype.val`
  rewrite is available (there is no `h : … = …` to rewrite; the terms are being unified).
- **fix / rule**: restate the *local* `have` over the subtype, `∀ (A B : ↥(memberSubmodule F Φ₀ ξ)),
  ⟪toCarrier … A, toCarrier … B⟫ = pairing F Φ₀ σ (B : _) (A : _)`, and use the identical proof body
  (`rintro ⟨a, ha⟩ ⟨b, hb⟩`). The headline's statement is untouched — this is a `have`, not a
  declaration. The general rule: **when a pin `have` is used with subtype arguments, state it over the
  subtype from the start**; do not try to make the `∈`-form match.
- **seen**: 2026-11-13, SET-AF55 order B (one round; the proof body was unchanged after the restatement).
- **corroboration**: the same session's B5 heartbeat profile (~46–50k for the 259-line declaration,
  cumulative) is *not* this trap — it fails at a different line each time, which is the tell that a
  cost is cumulative rather than one pathological unification.

## FR-0193 [instance/scope] — a `scoped instance` is not active in a wrapper statement unless its namespace is opened there, and `omit` is not available until the body is real

- **where**: SET-AF55's A5 (`AutomorphicForm.isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport`)
  in `AutomorphicForm/Adelic/TestFactorIntegral.lean`.
- **symptom 1**: with the prelude's `scoped instance : NormedAddCommGroup (PP F)` in
  `namespace ArchConvIntegral` and the headline written at top level, the headline's own statement
  fails to elaborate: `NormedAddCommGroup (Xm F × PP F)` does not synthesize. `Xm F` alone is fine —
  a three-level product loses the instance search that the two-level one wins.
- **cause**: `scoped instance` is only active where its namespace is **opened**; the pin writes
  `open ARCHCONV in` immediately above the same headline for exactly this reason, and the manager's
  scaffold dropped the prefix as boilerplate.
- **fix / rule**: keep the pin's `open <Label> in` prefix on any headline whose statement mentions a
  type whose instances are `scoped` in the prelude's namespace. The tell: an instance-search failure
  in the *statement* of a headline whose prelude defines the type — not in its proof.
- **symptom 2**: once A4/A5's bodies stopped being `sorry`, Lean 4.34's `linter.unusedSectionVars`
  fired on auto-bound instance binders (`[NumberField F]`, `[TopologicalSpace Y]`, …) that the
  statements do not mention. `sorry` bodies hide the linter, so this class of problem appears only at
  the very end of a wave.
- **fix / rule**: `omit [binder] in` is the linter's prescription and is **not** a silencer — it drops
  a binder the statement does not carry, and `check_port` cannot see the difference. Forbidden is
  `set_option linter.…`; `omit` is the intended tool. Expect the omit set to change the moment the last
  `sorry` goes, and check the statement text against the pin afterwards.
- **seen**: 2026-11-13, SET-AF55 order A (two deviations, both statement-preserving; the second is the
  general "the gates can only be run once the bodies are real" point).

## FR-0194 [definition-gate] — a pin prelude that derives `private scoped instance`s has no v4.34 counterpart, and the port pins those instances per module

- **where**: SET-AF56's planned second order, the cuspidal unfolding
  (`AutomorphicForm.integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn`, 635;
  see `SET-AF56.md` §1.1). Cut at the scaffold, so no proof effort was spent.
- **symptom**: the pin's prelude (`S_…:35–68`) opens with five `private scoped instance`s —
  `Countable K`, `Countable (𝓞 K)`, `SecondCountableTopology (FiniteAdeleRing …)`,
  `SecondCountableTopology (InfiniteAdeleRing K)`, `SecondCountableTopology (AdeleRing …)` and
  `SecondCountableTopology (GL (Fin 2) (AdeleRing …))`. Transcribed as they stand, the module fails
  at the *statements*: `RestrictedProduct.secondCountableTopology` no longer exists at v4.34
  (`unknown constant`), and `MeasurableSpace (AdeleRing (𝓞 K) K)` does not synthesize even with the
  port's `AdelicHaar/PlaceMeasure` and `AdelicHaar/ProductMeasure` imported.
- **cause**: the port does not carry the adele ring's measurability as a global instance. It is pinned
  per module as a `local instance` — `attribute [local instance] NumberField.AdelicHaar.adeleBorel`
  (and `borelSpace_adeleBorel`) — which is why `NumberTheory/AdelicBox.lean:350` and
  `NumberTheory/AdelicModulus.lean:107` each carry that line, and why every `AutomorphicForm` wrapper
  that touches the adele ring carries it too. The pin instead *derives* the instances privately inside
  the proof file, so the file is self-contained in a way a v4.34 transcription is not.
- **fix / rule**: before scaffolding an `AutomorphicForm` row whose statement mentions
  `AdeleRing (𝓞 K) K` (or a `GL`/`Matrix` over it), check three things in the *statement* round trip:
  (a) `attribute [local instance] NumberField.AdelicHaar.adeleBorel` present, (b) the port's
  second-countability is `NumberField.AdelicHaar.ProductMeasure.L1.secondCountableTopology_finiteAdeleRing`
  (a theorem, not the old `RestrictedProduct` lemma), (c) the pin's `private scoped instance` block
  dropped in favour of the port's. If those do not close the statement, the row is a
  **definition-layer** item: register it and cut it, do not spend a proof wave on it.
- **seen**: 2026-11-13, SET-AF56 (one scaffold round, ~10 minutes; the row is deferred with its price
  in the set note).

## FR-0195 [tactic/elaboration] — `Finset.map_noncommProd` cannot be used inside `rw` at v4.34 (implicit transparency)

- **where**: SET-AF56's row A, `RightConvProduct.iota_mulSingle`
  (`AutomorphicForm/Adelic/RightConvProductIntegral.lean`), from the pin
  `S_…exists_pos_forall_rightConv_integral_prod_mul_indicator_…:73`.
- **symptom**: `rw [← Finset.noncommProd_mulSingle κ, Finset.map_noncommProd]` fails with
  "target expression is not type-correct under the `implicit` transparency level". The pin's line
  reads as a two-step rewrite.
- **cause**: `Finset.map_noncommProd`'s right-hand side is
  `fun _ hx _ hy _ => (comm.forall₂ hx hy).map g`. Elaborating that pattern needs `Set.Pairwise`/
  `Function.onFun` unfolded, which `rw`'s **implicit** transparency will not do. It is not about the
  `let`-bound subgroup or the `noncommProd` index that the pin's line appears to touch; a minimal
  repro outside this project reproduces it, and the same lemma is fine as a term-mode `have`.
- **fix / rule**: state the map step as a **closed `have`**, which elaborates at default transparency,
  and `rw` with it:
  `have h2 : ι (univ.noncommProd f comm) = univ.noncommProd (fun i => ι (f i)) (fun i _ j _ _ => (comm_ij).map ι) := Finset.map_noncommProd _ _ _ _`
  then `rw [← h1, h2]`. No `set_option`, no cap: the general rule is the playbook's "spell the terms /
  name the bridge" family — when `rw`'s pattern needs a transparency the tactic does not use, give the
  instance as a `have` and rewrite with the name.
- **seen**: 2026-11-13, SET-AF56 row A (one round). Carried into
  [../CARRY-FORWARD.md](../CARRY-FORWARD.md) for the next port that touches `noncommProd`.

## FR-0196 [instance/scope] — the cure for the adele ring's instance layer: pin `adeleBorel`/`glBorel` **inside** the section, and open `ProbabilityTheory`

- **where**: SET-AF57's row U (`AutomorphicForm/Adelic/CuspidalUnfolding.lean`), the row FR-0194
  diagnosed and cut at SET-AF56.
- **the three steps, in the order they matter**:
  1. `attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel`
     **after** `variable (K : Type) [Field K] [NumberField K]`, not at the top of the file: the attribute
     names an instance whose `K` is implicit, and before the `variable` there is no `K` to pin, so the
     line is accepted and does nothing. This is the whole difference between the two attempts.
  2. `attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel`
     for `MeasurableSpace (GL (Fin 2) (AdeleRing …))`.
  3. `open scoped ProbabilityTheory` for the `μ[|s]` notation — it is a
     `scoped[ProbabilityTheory] macro` in `Mathlib/Probability/ConditionalProbability.lean`, not a
     `MeasureTheory` notation, so a file that writes `adelicAddHaar[|adelicBox K]` and does not open it
     fails at the *statement* with `unexpected token ']'`.
  Plus `open scoped NumberField.AdelicHaar` if the port's scoped second-countability instances are wanted.
- **what is *not* needed**: none of the pin's eight `private scoped instance`s. Drop the block. Two of
  them cannot even be transcribed (`RestrictedProduct.secondCountableTopology` is gone at v4.34), and
  `Countable K`/`Countable (𝓞 K)` come from mathlib for a `NumberField`. Verified: the 635-line
  statement elaborates with only the three fixes above, in one probe.
- **rule**: the port's convention is that the adele ring's measurable space is a **per-module local
  instance** (`NumberTheory/AdelicBox.lean:350`, `NumberTheory/AdelicModulus.lean:107`). Any
  `AutomorphicForm` row that mentions `AdeleRing (𝓞 K) K`, `GL (Fin 2) (AdeleRing …)` or `μ[|s]` opens
  with those lines; its pin prelude's derived-instance block is dropped, and the drop is recorded in
  the module header as a prelude substitution (not a statement change).
- **seen**: 2026-11-13, SET-AF57 (the deferral of SET-AF56 was resolved in one scaffold round).

## FR-0197 [tooling/defeq] — a `where`-bodied declaration is stubbed at its `where`, not at its first `:=`; and `IsFundamentalDomain`'s field set at v4.34

- **where**: SET-AF58's scaffold of C (`Adelic/GlobalPointsDomain.lean`), the pin's
  `private theorem isFundamentalDomain_inter_restrict` and `…_iUnion_of_restrict`
  (`S_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range.lean:31`, `:54`).
- **symptom**: after a mechanical stub, the module fails with `Fields missing: ae_covers, aedisjoint`
  at the `IsFundamentalDomain` structure literal, then a cascade of "unsolved goals" in the same
  declaration. It reads like a statement drift between the pin's mathlib (`v4.33.1`) and the port's
  (`v4.34.0`).
- **cause**: the pin writes the literal as
  `IsFundamentalDomain G (⋃ k, S k) μ where` / `  nullMeasurableSet := …` / `  ae_covers := …` /
  `  aedisjoint := …`. A stubber that cuts at the **first `:=`** cuts *inside* the literal: the first
  field survives as `nullMeasurableSet := by sorry` and the remaining two are silently dropped, which
  the elaborator reports as missing fields. The fields themselves are the same at both versions.
- **fix / rule**: cut at the ` where` that ends the statement line (`re.search(r"[ \t]+where[ \t]*\n", …)`
  and replace it by ` := by\n  sorry`), so the whole structure literal becomes one `sorry` body — the
  same rule as FR-0188's "cut at `:= by`, fall back to the first `:=` only when the body is a term",
  with the missing case now named. A `where`-bodied declaration is *never* a term body.
- **also recorded here**: the same scaffold needed `open NumberField.TateGlobal` for `ideleNorm` in
  `PeterssonSelfPairing` (the pin opens it at file level, and nothing in the port's
  `AutomorphicForm.Adelic` modules had made it reachable), and the pin's two `haveI`s in
  `scoped instance instCountableΓ` are `have`s at v4.34 (FR-0173's family).
- **seen**: 2026-11-13, SET-AF58 (one generator round; the fix is in `tmp/af5{6,7,8}/gen.py`).

## FR-0198 [statement/gate] — a pin row with two overlapping instance parameters has no legal exit under (statement frozen, no silencer, zero warnings)

- **where**: SET-AF61's first attempt, `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion`
  (305 silo, lev 1/7). Scaffolded, elaborated, **withdrawn at the scaffold**; no proof effort spent.
- **symptom**: the module elaborates, `check_port` is clean, and the only diagnostic is
  `linter.overlappingInstances` on a **prelude** row:
  `integral_comp_inv` inherits the section binders `variable (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]`,
  and `[μ.Regular]` implies `[IsFiniteMeasureOnCompacts μ]`, which `[μ.IsAddHaarMeasure]` already implies.
  Lean's suggestion is "may be removed".
- **why the obvious fixes are all illegal here**:
  (a) *remove* `[μ.Regular]` — changes the declaration's type, so `check_port` reads a MISMATCH against
  the pin, and the row is no longer a faithful transcription;
  (b) `omit [μ.Regular] in` — same thing, it drops the binder from the declaration;
  (c) `set_option linter.overlappingInstances false in` (or any linter `set_option`) — the port forbids
  silencing, and this is exactly the silencer the rule names;
  (d) leave the warning — the per-module gate is zero warnings.
  The triple (statement frozen by the checker) + (never silence a linter) + (zero warnings) has no exit
  when the pin's *own* statement is the redundant shape.
- **rule / what a set should do**: such a row is a **reviewer's** decision, not a wave's — either an
  accepted-warning class is declared for statements the pin spells redundantly (with the gate text
  amended in the same touch), or the checker gets a marker for it, or the row is ported with its type
  repaired and a `decl_markers.tsv` `own:` row recording the one-binder repair. Until one of those is
  chosen, cut the row and register it here; do not quietly silence, and do not weaken the statement.
- **corroboration**: the sibling row of the same pair (`TateLocal.measureReal_setOf_valued_le_exp`, 100)
  is separately blocked by a pin `set_option maxHeartbeats 4000000`, which is the other half of the same
  phenomenon — the pin's local Tate module is where its instance friction lives.
- **seen**: 2026-11-13, SET-AF61 (scaffold round only).

## FR-0199 [instance] — the pin's `Nat.card`-vs-`Fintype` route leans on a `Finite → Fintype` instance this port does not register

- **where**: SET-AF61's headline tail
  (`AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup`,
  pin `S_…:223`–`:228`).
- **symptom**: the pin closes with `haveI : Finite (𝓞 F ⧸ v.asIdeal)` and then
  `rw [Nat.card_eq_fintype_card, Fintype.card_fin, hcard]`. Transcribed, the `rw` finds neither lemma:
  `Nat.card_eq_fintype_card` needs a `Fintype` instance, and `inferInstance : Fintype (𝓞 F ⧸ v.asIdeal)`
  fails (`synthInstanceFailed`) even with `Finite` in scope — the port does not register the
  `Finite → Fintype` bridge that the pin's environment (or its `P2M.Util`) carries. Separately, `haveI`
  on a `Prop`-class fires `linter.style.haveILetI`, and a silencer is forbidden.
- **fix / rule**: do the cardinal comparison on `Nat.card` and pass the instance *explicitly*:
  `have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)`, then
  `have hle : Nat.card (Fin (absNorm + 1)) ≤ Nat.card (𝓞 F ⧸ v.asIdeal) :=
  @Nat.card_le_card_of_injective _ _ hfin f hfinj`, then `rw [Nat.card_fin, hcard] at hle; omega`. Same
  conclusion, no `haveI`, no `Fintype`, no `set_option`.
- **rule, generalized** (this is the second case this session, after FR-0194/FR-0196's adele-ring
  instance layer): when a pin tail's `rw` "cannot find the lemma" but the lemma exists, suspect a
  **`Finite`/`Fintype`/`Nonempty` bridge** or a scoped instance the port pins per module. The tells are
  a `synthInstanceFailed` for a class the statement does not mention, and a *proof-local* `haveI` in the
  pin — which is the pin carrying an instance the port declares elsewhere.
- **seen**: 2026-11-13, SET-AF61 (three lines; no statement change).

## FR-0200 [checker] — a prelude written **once** against two differently-spelled pin copies still checks `ok`: the tiers are name-first, *hash-second*

- **where**: SET-AF63's two scaffolds. The pin copies its per-file prelude into every `S_` file that
  needs it, and the copies drift in spelling: `S_CuspForm_exists_qCoeff_eq_sum_primeFactors_…:382–495`
  re-states 25 of `S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime`'s declarations in the `Γ₁(N)`
  notation while the first file writes `CuspForm (Gamma1 N) k`. The same happens between the two
  Petersson files (12 declarations, byte-identical there) and between row F's file and
  `WeightOne/PrimitiveQCoeffNorm.lean` (19 declarations).
- **the question the manager had to answer before scaffolding**: does writing the block once make the
  other copy report `MISMATCH` (its text is not in the module) or `missing`?
- **answer, measured**: neither. `check_port.py` indexes the wire by last name and then *picks, among
  those candidates, the one whose statement hash equals the port declaration's* (`Wire.by_last` +
  `pick`). A port declaration matches the copy it transcribes, and a `MISMATCH` needs the statement to
  match **no** copy. Measured on both AF63 scaffolds: 84 ok / 0 / 0 and 58 ok / 0 / 0, with every
  deduped declaration `ok` against the copy whose spelling the port kept.
- **rule**: a pin block copied into several `S_` files of one module is written **once**, in the
  spelling of one copy (state which in the header, and `open` it from the other namespaces). The
  checker resolves the rest; a local `local notation` inside the reusing namespace is free. This is
  what `port_advise`'s *port once* block is reporting when it lists the same name twice from two pin
  files.
- **caveat**: the resolution is by *last name* first, so this is only safe when the copies carry the
  **same** last name. A renamed copy needs a `pin:` row in `spec/decl_markers.tsv`.
- **seen**: 2026-11-14, SET-AF63.

## FR-0201 [tooling] — writing the scaffold *is* a port as far as the frontier is concerned: −1,985 silo before a proof is written

- **where**: SET-AF63's §0 read, taken twice on the same tree: once before the two scaffolds were
  written (`needed [F terminal]` **662 / 285,984**) and once after (`656 / 283,999`).
- **the move is exactly the six cut rows' silo** (339 + 118 + 868 + 249 + 142 + 269 = 1,985 lines, six
  nodes), because `frontier.py`'s name tier scans the port tree for *declarations* and a `sorry`-bodied
  declaration is a declaration. Nothing about readiness changed: the six rows' proofs do not exist.
- **rule (the FR-0114 rule, with the price attached)**: take the *opening* read of a set **before** its
  scaffold is written, quote that figure in the brief, and never compare a post-landing read against a
  read taken with the scaffolds in flight. If a read must be taken mid-wave, `--unport` the in-flight
  rows — here six `--unport`s would have been needed, and it is cheaper to take the read first.
- **corollary for the plan**: the scaffold also *inflates* the `--selfcheck` frontier figure by its
  prelude declarations' last names, so a mid-wave `--selfcheck` is not comparable with the pre-wave one.
- **seen**: 2026-11-14, SET-AF63.

## FR-0202 [scaffolding/tooling] — dropping a declaration that carries a `omit … in` / `open … in` prefix leaves the prefix on the **next** survivor, and `check_port` cannot see it

- **where**: SET-AF63's ORDER-B scaffold, `ModularForms/Analytic/HeckeEigenvalueConj.lean`. The pin's
  `S_CuspForm_peterssonOn_add_smul_conj.lean` opens its prelude with `omit [Γ.FiniteIndex] in`
  (pin `:76`) directly before `petersson_continuous'`; that declaration is one of the twelve the
  manager deduped out of the second namespace. The scaffold's chunker splits on non-indented lines, so
  `omit [Γ.FiniteIndex] in` became a chunk of its own — with no declaration name, so the
  drop-by-name list did not remove it — and it landed immediately before the next surviving
  declaration, `peterssonOn_add_right`.
- **symptom**: the module elaborates, `check_port` reads **58 ok / 0 / 0**, and the affected row is
  **unprovable**: `omit [Γ.FiniteIndex] in` removes the instance from the proof context, so
  `integrand_eq`/`integrable_cosum` (whose signatures need `[Γ.FiniteIndex]`) cannot apply, and
  additivity of the Bochner integral needs integrability. A worker reported it at the *first belief*
  and fixed it by deleting the orphan line — which restores exactly the pin's public binder set.
- **why the gate missed it**: `check_port`'s declaration regex starts at `theorem`/`def`/…, so a
  non-indented prefix line is **not part of the compared signature**. The port can therefore carry a
  *different binder set* from the pin and still read `ok`. The same is true of a misplaced
  `variable … in`, `include … in` or `open … in` — a silent, checking-invisible statement change.
- **rule for a scaffolder**: attach a non-indented prefix line (`omit`/`include`/`variable`/`open`/
  `attribute` … ending in `in`) to the **chunk it modifies**, so that dropping the declaration drops
  the prefix with it. `lean/tmp/af63/gen.py` now does this. And on the reading side: a scaffold is
  not verified by `check_port` alone — the public binder set of every declaration must be diffed
  against the pin's, which is what the worker's skeleton diff did here.
- **seen**: 2026-11-14, SET-AF63 order B (found and fixed by the worker within the dispatch, not a
  blocker).

## FR-0203 [defeq/expose] — v4.34's `@[expose]` on `SpecialLinearGroup` makes an anonymous constructor elaborate at the **unfolded** subtype, and the pin's `mapGL`/`Gamma1_mem` steps then do not unify

- **where**: SET-AF63 order A, `ModularForms/AtkinLehnerLowering.lean`, the two cocycle lemmas
  `Depletion.exists_cocycle_trans` (pin `S_…ite_coprime.lean:48`) and
  `AtkinLehnerMain.exists_cocycle_wGL` (pin `…_sum_primeFactors.lean:199`).
- **symptom**: the pin's literal text
  `let δ : SL(2, ℤ) := ⟨!![a, b; c, d], hdet⟩` / `exact ⟨⟨!![…], hdet⟩, …⟩` fails at v4.34 with
  "Application type mismatch: … has type `{A // A.det = 1}` but expected `SL(2, ℤ)`" when the term is
  then fed to `Matrix.SpecialLinearGroup.mapGL ℝ` or to `Gamma1_mem` — at `.implicit` transparency the
  two are not identified. `SpecialLinearGroup` is `@[expose]` in this mathlib, so the anonymous
  constructor is *seen through* to the subtype.
- **fix / rule**: bind the element first and record its `Matrix` value as a `rfl` at the `SL(2, ℤ)`
  type, then rewrite with that equation:
  ```lean
  let δ : SL(2, ℤ) := ⟨!![a, b; c, d], hdet⟩
  have hδcoe : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := rfl
  ```
  This is the "state the intermediate at the named type" rule of the playbook's §6 brick recipe, in its
  `@[expose]`-induced form; a `show`/`change` at the unfolded type does **not** fix the downstream
  application, because the failure is on the argument's type, not on the goal.
- **cost when missed**: this is the only proof-level adaptation the order needed (two sites); both
  proofs are otherwise verbatim.
- **seen**: 2026-11-14, SET-AF63 order A.

## FR-0204 [namespace/shadow] — opening `OnePoint` shadows `map_smul`, and the port's own `OnePoint.map_smul` then wins the elaboration

- **where**: SET-AF64 order A's scaffold, `ModularForms/NebentypusEigenbasis.lean` — the pin's `open
  CongruenceSubgroup ModularForm UpperHalfPlane Filter Function` (plus `OnePoint` from its `p2m_open`
  line) is carried into the module.
- **symptom**: four sites (`ker_sq`, `qCoeff_heckeFun` twice, `mem_eigenSet_of_eigen`) report
  "ambiguous" for a bare `map_smul` rewrite; the goal's `SMul` is the function/module one, but
  `OnePoint.map_smul` (the `OnePoint` API's own) is in scope with equal priority.
- **fix / rule**: write `_root_.map_smul` at those sites. The general rule: when the pin's `p2m_open`
  list is hoisted to a module-level `open`, a name as generic as `map_smul`/`coe_*`/`mul_*` can be
  shadowed by a namespace the pin happened to open; qualify with `_root_.` rather than dropping the
  `open` (dropping it breaks the other nine sites that need it).
- **seen**: 2026-11-14, SET-AF64 order A.

## FR-0205 [instance] — the Dirichlet orthogonality sum needs `NeZero ((Monoid.exponent (ZMod N)ˣ : ℕ) : ℂ)`, not `NeZero (Monoid.exponent …)`

- **where**: SET-AF64 order A, `SSbasis.sum_proj` (pin `S_…eigen.lean:329–393`), the
  `∑ ε : DirichletCharacter ℂ N, proj ε g = g` decomposition.
- **symptom**: the pin's `haveI : NeZero (Monoid.exponent (ZMod N)ˣ)` does not satisfy
  `DirichletCharacter.sum_char_inv_mul_char_eq`, and `Fintype (DirichletCharacter ℂ N)` alone is not
  enough either: the lemma's `HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod N)ˣ)` instance is what
  carries the sum, and mathlib builds it from the **ℂ-valued** `NeZero ((Monoid.exponent (ZMod N)ˣ : ℕ) : ℂ)`
  (`NeZero` of a cast into the ring), not from the `ℕ`-valued one.
- **fix / rule**: install the ℂ-valued one — the port already builds it at
  `ModularForms/WeightOne/IntegralWeightOneForm.lean:86`, which is the copy to imitate. A `NeZero` whose
  statement mentions the exponent is ambiguous between the two casts; read the instance's own statement in
  mathlib before installing it.
- **corroboration**: the same wave found the `Γ₀`/`Γ₁` twin problem in the premise audit — a second
  instance-level near-miss in one order, both caught by the worker before the gate rather than after.
- **seen**: 2026-11-14, SET-AF64 order A.

## FR-0206 [scaffolding/gate] — `check_port` is not an elaboration gate, and counting `warning|error` lines is not reading them

- **where**: SET-AF65's third scaffold, `ModularForms/GammaHDictionary.lean`. I reported all three scaffolds
  "elaborating at the low cap with `sorry` warnings only, all checker-green before dispatch". The third one
  **did not elaborate**: three defects (two real errors and one bogus `end`), repaired by the worker inside
  its dispatch.
- **what the defects were** (all scaffold-side, none a statement change): (a) the pin's persistent
  `open scoped MatrixGroups ModularForm` sat *after* the two `open … in` chains, so the chain consumed it and
  the final headline's `∣[k]` notation failed to parse; (b) a statement needing `Decidable (ε₀ = ε)` needs
  `open Classical in` on that declaration (`Classical.propDecidable` is scoped; mathlib has no
  `DecidableEq (DirichletCharacter ℂ M)`, so no import supplies it); (c) one `end` too many.
- **how the gate missed it, twice**: `check_port.py` is a *textual* statement checker — it parses the module
  and diffs signatures, and it reads `4 ok / 0 / 0` on a module that does not elaborate. Then my `lake env
  lean | grep -v "declaration uses" | grep -c "warning\|error"` returned `6` — four warnings and two errors in
  one number, which I read as "six warnings".
- **rule for a scaffolder**: the scaffold gate is two commands, and the first is
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <module> 2>&1 | grep -E "error"` — **grep for
  `error`, print it, and require it empty**; the second is `check_port --force`. Never summarise the compiler's
  output as a count, and never take `check_port ok` as evidence that a module compiles. (The `sorry` warnings
  are the only diagnostics a scaffold may carry.)
- **corroboration**: the same wave's other two scaffolds were verified the same way and *were* clean, which is
  exactly why the practice must be a command and not a judgement — the failure was invisible in every
  aggregate number.
- **seen**: 2026-11-14, SET-AF65 order B (found and repaired by the worker at the start of its dispatch).

## FR-0207 [namespace/collision] — two namespaces declaring `T_mem_Gamma1`, one module opening both: a **latent** build break that only a re-elaboration exposes

- **where**: `FLTForHuman/ModularForms/HeckeNebentypusExistence.lean:122`, found by SET-AF66's order B at the
  start of its dispatch (it could build nothing: the module's olean had just been deleted by `lake`).
- **symptom**: `error: Ambiguous term T_mem_Gamma1` — `X1DiamondRational.T_mem_Gamma1`
  (`ModularForms/WeightOne/Defs/GammaRational.lean:262`, `N` a section variable) and
  `CuspForm.HeckeEigenNebentypus.T_mem_Gamma1` (`HeckeEigenNebentypus.lean:125`, `N` an explicit argument) are
  both in scope through the file's own `open CuspForm.HeckeEigenNebentypus` and `open X1DiamondRational`.
- **why it was invisible for weeks**: the module is unmodified at HEAD and its `.olean` was a **prebuilt
  cache**. Nothing forces a re-elaboration until a *dependency* is rebuilt; SET-AF64's order A rebuilt 20
  stale upstream modules, one of them `HeckeEigenNebentypus`, which made this module stale — and the rebuild
  then failed and lake deleted the olean, so every importer became unbuildable at once. A cached `.olean` is
  not evidence that a module compiles; the tree at HEAD could not build this module from scratch.
- **fix / rule**: qualify the one site (`CuspForm.HeckeEigenNebentypus.T_mem_Gamma1 M`) — the same statement,
  and the minimal edit; dropping one of the two `open`s would re-resolve every bare name in the module and a
  `private` copy would duplicate mathematics. **The general rule**: a port module must not `open` two
  namespaces that both declare a generic name like `T_mem_Gamma1`/`mapGL_apply`/`dd`; prefer the qualified
  call at the site, or keep the copy `private` under a distinct name. The other two modules that open
  `X1DiamondRational` and use a bare `T_mem_Gamma1` (`WeightOne/Gamma0Rationality.lean`,
  `ModularCurve/X1/IsIntegralAtkinLehner.lean`) do **not** open the second namespace, so this is the only
  site.
- **also the reason a wave must not trust `lake build <module>` alone**: a green build over cached oleans says
  nothing about the modules it did not re-elaborate. (Compare FR-0033's missing-olean rule.)
- **seen**: 2026-11-14, SET-AF66 order B (repaired by the worker, reviewed and adopted by the manager).

## FR-0208 [linter/statement] — `unusedSectionVars` on a frozen statement's dead `[NeZero M]`: spend the witness, do not `omit`

- **where**: SET-AF66 order A, `OldFormCosetSum.qCoeff_sub` (pin `S_…comp_heckeDiagMatrix_apply_eq_of_not_dvd.lean:94`).
- **symptom**: the pin's declaration carries `[NeZero M]` among its section variables and its proof never
  uses the instance; v4.34's `linter.unusedSectionVars` fires, and the per-module gate is zero warnings.
- **why the usual exits are illegal here**: `omit [NeZero M] in` (or `include`) travels with the declaration
  and changes its binder set — for a wired module that is a statement change the checker would see as a
  MISMATCH on the *next* declaration of the block; a `set_option linter.*` is the forbidden silencer; and
  renaming/removing the variable is not available because it is the pin's own section structure.
- **fix / rule**: make the proof *spend* the hypothesis that is already in the context — here a reference to
  `NeZero.ne M` (and to `periodic f`, which the same proof also had in hand). The statement stays
  byte-identical, the warning goes. This is FR-0198's family in a third linter (after
  `linter.style.haveILetI` and `linter.overlappingInstances`), and the general answer is the same: the pin's
  unused hypothesis is often spendable, and spending it is always cheaper than a silencer or a statement
  change.
- **corroboration**: the same wave's other dead-binder case was resolved the same way by a different worker
  (`slashV_lowU_avgV`'s `hp`, AF63), so the class now has two independent instances and one rule.
- **seen**: 2026-11-14, SET-AF66 order A.

## FR-0209 [instrument] — "ported" is not "imported": the frontier's name scan sees the whole tree, so a ready row's premise may be unreachable from the row's home

- **where**: SET-AF67 order A. Row A's premise
  `CuspForm.norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd` is ported in
  `ModularForms/WeightOne/PrimitiveQCoeffNorm.lean`, which is **not** in the new module's import list; the
  worker had to add `import FLTForHuman.ModularForms.WeightOne.PrimitiveQCoeffNorm` for the proof to reach
  its premise at all.
- **why the tools say nothing**: `frontier.py`'s name tier runs `scan_port_decls(port_roots)` over the whole
  port tree, so a declaration counts as ported wherever it lives and however far its module is from the
  row's home. `needed = 1` therefore means "the statements exist in the tree", **not** "they are usable from
  the module this row belongs to". The recipe's §4 import-direction rule is the statement-level version of
  this (`a module below the proof's premises cannot host it`); this is the *module-graph* version: the row's
  home must be **above** its premises' homes, which the frontier does not measure.
- **cost when missed**: one added import, and — the part that can hurt — the import may drag a large cone
  into the row's build (here a 9 s target, benign; with `EichlerShimura`-bearing closures it is FR-0167's
  trade).
- **rule**: when a work order lists a premise as "ported per the graph", a worker must check the *import*
  reachability too, and the manager's premise audit should name the module a premise lives in (not just the
  fact that it exists). Both are now in the AF67 order: `twin_scan` for the statement, and the module path
  for the import.
- **corroboration**: the same dispatch also found `PrimitiveQCoeffNorm`'s olean **stale** (Oct 25 against
  newer `HeckeQCoeff`/`AtkinLehnerSlash` oleans) and built that one target before the module — the same
  tree-state class as FR-0207, and the reason a work order says "build the single target, report it, never a
  tree build".
- **seen**: 2026-11-14, SET-AF67 order A (found at first belief, one import, no rework).

## FR-0210 [scaffolding] — the statement itself may contain a depth-0 `:=`, and the scaffold generator cut it in half

- **where**: `lean/tmp/af63/gen.py`'s `stub_theorem`/`top_level_assign`, on two statements of SET-AF68
  row B (pin `S_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_…_apply.lean:339` and `:90`).
- **symptom**: the generated scaffold fails to elaborate with a pair of errors that name the *next*
  declaration — `unexpected token 'theorem'; expected ':=', 'where' or '|'` plus `unsolved goals` — at
  the two sites, and nothing else in the file is wrong.
- **cause**: the recipe stubs a theorem by cutting at the **first `:=` at bracket depth 0**, which is the
  declaration's own `:=` for every pin statement of the first sixty-seven sets. A statement may carry a
  `haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩` binder in *type* position (the `T_ℓ`/`U_q` action lemmas do), and
  that `:=` is also at depth 0: the stub then replaces the rest of the *statement* by `sorry` and the
  next declaration lands in a malformed chunk.
- **fix**: `top_level_assign` now skips a depth-0 `:=` whose line begins with `haveI`/`have`/`letI`/
  `let`/`show`/`obtain` (those introduce a witness, not the body). Verify with the FR-0206 gate on the
  freshly generated module — the two errors are absent and the checker is unchanged (`check_port`
  cannot see this class: the statement is right in the *pin*, wrong in the scaffold).
- **seen**: 2026-11-14, SET-AF68 scaffold (`lean/tmp/af68/gen68.py`, first run).

## FR-0211 [instrument] — `--also` is not a "what if this were ported" probe: it withholds the consumer under the FR-0044 guard

- **where**: `tools/deps/frontier.py` when scoping a *chain* (SET-AF68: the 277 readies the 492, which
  readies the 176 and the 539).
- **symptom**: `--ready --also <the three chain rows>` returns the shelf with **no** new row, and the
  consumer (here the 539) shows up in the `withheld` block instead: the tool reads the chain rows as
  *pruned* (R), and a candidate whose own proof directly cites an unpruned-but-absent R premise is
  withheld by FR-0044's guard. The reading looks like "porting the chain readies nothing".
- **cause**: `--also` populates `avoided` (the prune set R), not `ported` (the frontier F). For
  readiness the two are not interchangeable even though both make the premise uncounted.
- **fix / rule**: to price a chain, add the rows to `ported` through the API and call `analyze` on that
  set (the SET-AF68 §0 probe: `ported = fr.frontier("union") | {ids}`, then `analyze(..., ready=True)`),
  and read the `withheld` block as the readiness return. **Resolved in the same set**: `frontier.py` now
  has the `--port NAME` dual of `--unport`, so pricing a chain (and reproducing the forecast after the
  landing) is one command.
- **corroboration**: the same run also showed that once a module declares the headline (even with
  `sorry`), the **name tier** marks the node ported, so a scaffold on disk changes the next shelf read
  — the read must be taken before the scaffold (FR-0201), and a post-scaffold read is not comparable
  with a pre-scaffold one.
- **seen**: 2026-11-14, SET-AF68 §0/§4.

## FR-0212 [mathlib] — v4.34's `Module.Basis` is `repr`-based: the pin's `simp [basis, vec]` on a `Basis.mk` is dead

- **where**: SET-AF68 order B, `WeightTwoEigenformSpace.basis_apply` (pin
  `S_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one.lean:82`), and any proof that
  unfolds a `Module.Basis.mk`.
- **symptom**: `simp [basis, vec]` no longer closes the goal; after the unfold, `Basis.mk_apply` /
  `coe_mk` cannot infer the basis vector `v` from the goal (the expected `v` is not syntactically the one
  in the goal), and `simp` reports `vec` as an unused argument.
- **cause**: `Module.Basis` is now `repr`-based — `Basis.mk` is `.ofRepr …`, so the coercion of a `Basis`
  goes through `repr` and the `mk_apply` rewrite is no longer a syntactic match. (This is a different
  class from the rename table: no name changed, the *shape* did.)
- **fix**: state the lemma as the term the old `simp` was reaching for —
  `Module.Basis.mk_apply 𝒟.hli _ x`, where the `_` is the `⊤ ≤ span` proof, discharged by proof
  irrelevance (the statement's `hspan` is `= ⊤`, `mk_apply` wants `≤`). Statement untouched, checker
  green.
- **sibling in the same wave**: five `change (⇑(…) : UpperHalfPlane → ℂ) = …` lines at the head of the
  `heckeT_GH`/`diamond_GH`/`heckeU_GH` branches are **no-ops** at v4.34 (the goal already has that shape
  after `apply DFunLike.ext'`), so `linter.unusedTactic` fires and the line must be *deleted* — the
  drift table's `beta_reduce` row. Deleting a no-op `change` is statement-neutral; do not replace it
  with `show`.
- **seen**: 2026-11-14, SET-AF68 orders B and A.

## FR-0213 [linter/gate] — the scaffold's silence gate is blind to every linter item that a `sorry` body hides

- **where**: any scaffold produced by the `af63/gen.py` recipe with theorem bodies stubbed to `sorry`;
  SET-AF69 module B is the worked case.
- **symptom**: the scaffold's "zero warnings apart from `declaration uses sorry`" gate passes, yet once
  the proofs are filled the same file reports `linter.unusedSectionVars` on **seven** declarations, not
  the two the scaffold showed (`AverageConvolution.continuous_integrand`'s six dead instances and one
  more, then five more in the `AverageOperator` block, each different).
- **cause**: most linters run on the *elaborated declaration*, and a `sorry` body makes the linter bail or
  stay quiet — `unusedSectionVars` in particular cannot see which section variables the proof body would
  have used, so it reports only the declarations whose *type* alone is enough to judge. The manager's
  scaffold gate (FR-0206's `error`-only grep, and even an `error|warning` grep) therefore prices the
  linter surface of a module at a strict lower bound.
- **fix / rule**: a work order must say "spend the witnesses, and expect *more* of these than the scaffold
  shows", not quote the scaffold's count as the list; and the manager's scaffold figure for FR-0208-class
  work is a floor. Spending is still the answer (`have _ := …`), never `omit` for a variable the pin does
  not omit, never a `set_option linter.*`.
- **corroboration**: the same wave's module A had exactly one such item at scaffold time (the dead `hν`
  binder) and it survived filling — so the undercount is invisible, not systematic.
- **seen**: 2026-11-14, SET-AF69 order B (7 declarations, all spent, module silent).

## FR-0214 [checker] — the statement hash includes binder *names*: a dead binder in a frozen statement cannot be renamed

- **where**: SET-AF70 order B, `WeightTwoCohomology.lean` — the three `linter.unusedVariables` warnings on
  the pin's `(hqM : q ∣ M)` binders (nested inside a `∀` in the statement, so no proof can spend them).
- **symptom**: the linter's own suggested fix (`_hqM`) silences the warning but takes `check_port` from
  **2 ok / 0 mismatch** to **1 ok / 1 mismatch**.
- **cause**: `check_port`'s `nhash` is a hash of the checker-**normalised source text** of the statement,
  and that normalisation does not alpha-convert binder names. So a binder name is part of the wire, and
  the checker's "the comparison is on the statement, not on the name" means the *declaration* name, not
  the bound-variable names inside the statement.
- **fix / rule** (amended by the project's current instruction, "no silencing linters **without good
  reason**"): for a dead binder **inside the statement** there are four exits. (i) Spend it — impossible
  when the binder is a `∀`-bound hypothesis the type does not use. (ii) Rename it `_x` — a checker
  mismatch, so **not available**. (iii) `omit` — available only for a *section variable*, not for a
  `∀`-bound binder; a section variable dead in both type and proof is `omit`-able without moving the hash
  (`NeZero M` in `Ψ_apply_E`/`Ψ_injective`). (iv) **A scoped, documented silencer** for the frozen API:
  `set_option linter.unusedVariables false` with a header paragraph stating why (the public statement is
  preserved byte-for-byte, the rename is a mismatch, the witness is unspendable) — this is the good reason
  the instruction allows, and it is what `WeightTwoCohomology` now does. The pin's own file silences the
  sibling linter for the same reason. Blanket silencers, or one without a reason in the module, remain
  forbidden.
- **corroboration**: the same experiment *worked* for the `hν` binder of SET-AF69's
  `le_norm_sub_of_mem_eigenspace` — not because renaming is legal but because that binder *was* spendable
  (a `mul_self_le_mul_self` chain), so no rename was needed.
- **seen**: 2026-11-14, SET-AF70 order B (applied, measured 1 mismatch, reverted).

## FR-0215 [instrument] — an abandoned scaffold contaminates the shelf read: delete it in the same touch

- **where**: SET-AF71/AF72 scoping. Two candidate sets were scaffolded and then dropped before dispatch
  (the `EisensteinGeneral.Piece` pair — blocked on a missing `AutomorphicForm/Adelic/WeilIntertwining`
  module and the `mixedEmbedding` API — and a `WeierstrassCurve/Automorphism/Stabilizer` five-row set —
  blocked on unported `IsCharTwoJNeZeroNF`/`IsCharThreeJNeZeroNF` classes), and an orphan
  `EisensteinGeneral/Factorization/Datum.lean` was left behind.
- **symptom**: the post-landing read came out **605 / 267,705 with ready 21 / 3,900**, five nodes and
  ~3,050 lines away from the accounting figure (610 / 270,200, ready 22 / 4,790), and it "readied" rows
  the wave had not cut. `--unport` on the names that looked suspicious did not move it, because the
  culprits were not the rows but the *engines*.
- **cause**: `frontier.py`'s name tier marks a graph node ported when **any declaration** of the port
  carries its last name. A scaffold of a pin `S_` file declares the pin's whole engine, and generic or
  distinctive engine names coincide with graph nodes (`add`, `inv`, `mul`,
  `linearIndependent_coeffMap`, `hasseInvariant`, …); the pin's proof engines are large, so one abandoned
  scaffold can hide five nodes. The same mechanism is what makes a *live* scaffold's probe read
  optimistic (SET-AF71 §4).
- **fix / rule**: (i) delete an abandoned scaffold in the same touch — never leave it "for the next
  wave"; (ii) take the shelf read on the cleaned tree, and if a scaffold is still on disk, price its
  rows by accounting and say so; (iii) an orphan `Def_` module is the same hazard (its definition names
  shadow graph nodes), so a `Def_` layer lands only with the set that needs it.
- **seen**: 2026-11-14, SET-AF71/AF72 landing (read corrected 605 → 610 with the four deletions).

## FR-0216 [tooling] — `move_dead` orphans an `omit … in` prefix, and an `omit` is load-bearing for callers

- **where**: SET-AF73's `move_dead --copy` sweep of `MeasureTheory/HaarQuotientFubini.lean`.
- **symptom**: after the sweep the trimmed source failed with `cannot omit referenced section variable
  inst✝¹` at an `omit … in` block whose declaration had moved to the shelf; deleting the block then gave
  a *new* `failed to synthesize LocallyCompactSpace G` at a **call site** in a neighbouring declaration.
- **cause**: (i) `move_dead.py`'s docstring names `@[...]`, docstrings and `open … in` as prefixes that
  must travel with a declaration, but **`omit … in` is a declaration prefix too**, and the cut can leave
  one behind — it then attaches to whatever follows (here to a declaration whose type references the very
  instance the prefix omits). (ii) An `omit` on a *callee* is what lets a caller that omits the same
  instance call it at all: once the instance is dropped from both sides' telescopes, a caller whose
  section context has the variable in hand still cannot synthesize it, so the callee's `omit` must be
  restored, not removed.
- **fix / rule**: after any `move_dead` cut, (a) check every `omit … in` block at the cut boundary —
  a prefix whose declaration left must be deleted; (b) then re-run the edit loop and let
  `linter.unusedSectionVars` name the instances that are *now* unused, adding one `omit` at a time from
  the linter's own message (this converges in one or two rounds; guessing the union of instances does
  not — that was the `inst✝¹` error); (c) never remove an `omit` from a declaration that another
  `omit`-bearing declaration calls.
- **also**: the `--header-file` of a `Reserve/` shelf must not carry a `spec-pin:` line, or the shelf is
  wired into `check_port` and its partial declaration set reads as a diff of the whole pin file.
- **seen**: 2026-11-14, SET-AF73 landing (source 672 → 425 lines, shelf 649 lines, both silent, checker
  and consumer unchanged, `move_dead` then 0).

## FR-0217 [instance] — a delayed coercion metavariable inside a *spelled* induction motive is an instance-term `isDefEq`

- **where**: SET-AF75 order A, `NumberTheory/AdelicFourier/Space.lean`,
  `comp_mul_mem_schwartzBruhat` (the row the scaffold had omitted and the manager restored from the pin
  with the pin's own proof, `P2M/Sol/S_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat.lean:77`).
- **symptom**: a ten-line proof aborts at the project's 200 k edit-loop cap with
  `(deterministic) timeout at whnf` on the `refine schwartzBruhat_induction …` line, although the rest
  of the module is far under the cap — and the pin file carries `set_option maxHeartbeats 1600000`, so
  the defect predates the port.
- **cause**: the motive spells `fun x ↦ f (↑y * x)` with `y : (AdeleRing (𝓞 F) F)ˣ`. `· * x` only
  constrains the *target type* of the coercion `↑`, so the elaborator postpones it as a `Coe`
  metavariable over the motive's telescope; assigning that metavariable when the eliminator
  instantiates the motive is a defeq that unfolds `AdeleRing = InfiniteAdeleRing × FiniteAdeleRing`,
  `InfiniteAdeleRing = (v) → v.Completion`, `v.Completion = SeparationQuotient (UniformSpace.Completion)`
  and the `Mul` instance term. The counters are the tell: `Units.val ↦ 870774`, `Prod.fst ↦ 360312`,
  `InfiniteAdeleRing ↦ 90097`, `Quotient`/`SeparationQuotient`/`UniformSpace.Completion ↦ 30025`,
  `Set ↦ 28813` — all in *reduction* of instance/coercion terms, with **no `synthInstance` goal
  anywhere**, i.e. the playbook's §3.5 class "instance terms compared by an argument check", but its
  trigger is not a big instance term in the *statement*: it is a *delayed* coercion in the *proof*.
- **fix / rule**: ascribe the coercion where it is written — `(↑y : AdeleRing (𝓞 F) F) * x` in the
  motive. Statement unchanged (`check_port` 33 ok), edit loop silent at 200 k, no `set_option`.
  Two probes worth carrying: (i) the **floor probe** (every proof `sorry`) is silent, so the cost is in
  the proof and no statement deviation is needed; (ii) spelling the same *dependent* motive at the span
  spelling (`∈ Submodule.span ℂ (pureTensorSet F)`, no `schwartzBruhat` anywhere) still aborts, so the
  `whnf` of the `def` is *not* the cost — and rewriting the induction as `Submodule.span_induction`
  (whose motive stays *inferred* from the goal and is never re-elaborated as a term, so the delayed
  metavariable never exists) is a cure but **not** a diagnosis: it leaves the trap armed for the next
  spelled motive. Prefer the ascription.
- **seen**: 2026-11-14, SET-AF75 order A (diagnosed by a build-fix subagent under §3.5, fix verified at
  the 200 k cap, 32 → 33 checked declarations on the module).

## FR-0218 [port] — a scaffold's `variable {F}` re-spells every *call site*, and the symptom is a `simp` that does not fire

- **where**: SET-AF76 order C, `AutomorphicForm/Adelic/BesselInequality.lean`. The manager's scaffold had to
  make the pin's section variable implicit (`variable {F}`) because v4.34 puts an explicit `F` into `ech`'s
  telescope where the pin's Lean left it implicit, so the pin's own text `ech ψ α` in the neighbouring
  statements elaborates only with the implicit annotation (FR-0217's file has the mirror case, `variable (F)`
  … `variable {F}` mid-file, which the scaffold had to reproduce).
- **symptom**: the *call sites* of the pin's proofs silently lose the argument — the pin writes
  `setIntegral_adelicBox_comp_add_right F G hG x`, the port needs `setIntegral_adelicBox_comp_add_right G hG x`
  — and the failure does not point at the call: a `simp only` list whose rewrite never fires leaves a goal
  that reads like an unfinished arithmetic step.
- **cause**: the binder annotation of a section variable is part of *every* declaration's signature that
  uses it, so changing it changes the arity of every same-file declaration at once.
- **fix / rule**: a scaffold that copies the pin's statement text must also copy the pin's `variable`
  annotations (and the port must add the annotations v4.34 needs); the worker's first move is then to diff
  the pin's *call sites of same-file theorems* against the scaffold's binder lines, not to debug the goal.
- **also** (v4.34, same order): `@norm_sq_eq_re_inner ℂ` is now the class projection
  `InnerProductSpace.norm_sq_eq_re_inner`, which needs `𝕜` pinned and a `conv_lhs` — a bare `rw` also
  rewrites the `‖f u‖^2` on the other side of the target.
- **seen**: 2026-11-14, SET-AF76 order C (5 mechanical call-site/binder fixes; checker and all gates green).

## FR-0219 [pin-vs-port] — `AdeleRing` is a `def`, so the pin's `subst`-then-measure steps are rejected in v4.34

- **where**: SET-AF76 order B, `NumberTheory/AdelicBox/Normalization.lean`, the headline
  `inv_measure_adelicBox_mul_integral_pureTensor_eq` (pin `:125–220`).
- **symptom**: after the pin's `subst hmA` (which identifies the `MeasurableSpace` of `𝔸_F` with the product
  one), `μ (adelicBox F)` reports `Function expected at μ`, and `rw [hμ, integral_smul_nnreal_measure]` fails
  with "pattern not found".
- **cause**: in v4.34 mathlib `AdeleRing` is a `def` (not an `abbrev`); the elaborated term `μ` still carries
  the old `A`-typed instance in instance-argument position, so a `subst` of the `MeasurableSpace` does not
  re-type it and the product instance is rejected where it is *applied*.
- **fix / rule**: never re-type `μ` by `subst`; give the product-typed copy a name and move the goal once —
  `let μP : Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := μ`, then one `change` restating the
  frozen goal at the product type, `let πP := πX.prod ν`, `have hμP : μP = c • πP := hμ`, and
  `hset : adelicBox F = infiniteBox F ×ˢ integralFiniteAdeles (𝓞 F) F := rfl` for the product-measure step.
  The pin's lemma sequence is then transcribable verbatim. (The same trap sits in order D's file, which copies
  the same prelude; it is harmless there only because no measure is applied to a set after the `subst`.)
- **seen**: 2026-11-14, SET-AF76 order B (fixed, all gates green; flagged forward to order D at the time).

## FR-0220 [orchestration] — a scaffold shared between two parallel orders blocks the dependent's *build* gate

- **where**: SET-AF76 orders B and D. D's module imports B's `Normalization` (the seven transport/countability
  lemmas the pin proves twice — the set's one real dedup). The manager dispatched B and D together, which is
  sound for the *statements* (a scaffold's `sorry` bodies elaborate).
- **symptom**: D's edit loop and checker were green while `lake build` of D failed, and the errors were all
  **inside B's file** — `True`-valued statements, "function expected at `μ`", a rewrite that did not fire.
  B was simply mid-flight; D could not produce its `.olean`, so its axioms/dedup/consumer gates could not run
  either.
- **cause**: a `sorry` body is not an error, but a half-edited file is; and `lake build D` builds the *whole*
  import closure, so a dependency being edited by another order is on D's critical path.
- **fix / rule**: when an order's module is a *dependency* of another order, either sequence them (the
  dependency's order first — its statements are frozen, so nothing is lost by waiting), or tell the dependent
  worker that its build/axioms/consumer gates close **after** the dependency lands and that it must not
  hand-make `.olean`s or edit the dependency. Both happened here: the dependent stopped at the blocker, wrote
  its consumer zone, and closed the four remaining gates itself once B landed, with no change to its file.
- **seen**: 2026-11-14, SET-AF76 orders B/D (D's gates 2/4/5/6 closed ~25 min after its gates 1/3).

## FR-0221 [instrument] — a row whose pin `solution` is a *specialization* must be ported at the row's name, or the shelf never credits it

- **where**: SET-AF78 order A, `LanglandsTunnell/TateLocal/HaarInvariance.lean`. The pin's file proves the
  general statement `integral_comp_inv` (pin `:110`, over any locally compact nonarchimedean field `K`
  with `hmod`/`h0` as hypotheses) and then a `solution` (`:269–304`) that specializes it to
  `v.adicCompletion F` with both hypotheses discharged. The row's node is the specialization.
- **symptom**: the worker ported the general form (checker `8 ok / 0 / 0`, axioms clean, consumer green —
  the mathematics is in), but the post-landing shelf read came out **588 / 265,599 against a forecast of
  587 / 265,294**: the node still counted as unported, 305 silo of accounting, and the wave's
  readiness forecast was off by a row.
- **cause**: `frontier.py`'s name tier credits a graph node when a port declaration carries its **last
  name**. The port's `integral_comp_inv` is not `integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion`,
  so the node stayed open — the same mechanism as FR-0215, in its benign direction.
- **fix / rule**: when a row's pin `S_` file ends in a `solution` that *specializes* a general theorem in
  the same file, the port declares **both**: the general one (the engine) and the row's statement at the
  row's name, proved by applying it. The scaffold must carry the row's statement — a scaffold that
  transcribes only the engine's `_impl`/general form silently loses the row, which is the inverse of
  SET-AF75's A3 omission (a scaffold that lost the headline itself, FR-0217's file).
- **also**: the same asymmetry explains why a `--port` forecast can be off by a row in either direction;
  the post-landing read is the only authority, and a one-row delta should be traced to the name tier
  before it is called a graph change.
- **seen**: 2026-11-14, SET-AF78 order A (the manager added the row statement and had the module's worker
  fill its proof; the read then credited the row).

## FR-0222 [instrument] — `check_port` cannot see a missing row, and `scaffold_audit.py` can

- **where**: the four sets of 2026-11-14 (AF75–AF80). Two of the wave's three real defects were *missing
  declarations* that every gate declared green: SET-AF75's A3 headline (the scaffold dropped it; the
  checker read `32 ok`, FR-0217's file) and SET-AF78-A's row statement (the port had the pin's general
  theorem but not the row's specialized form, so the shelf stayed red, FR-0221). `check_port` diffs the
  declarations a module *has* against the wire; it has no notion of a declaration the wire has and the
  module lacks.
- **instrument**: `tools/deps/scaffold_audit.py <module>` reads the module's own `spec-pin:` wire, takes
  every pin declaration the statement corpus indexes (public, non-`scoped`), and classifies it as
  *declared here* / *satisfied by the port import closure* (recursion over `import FLTForHuman.…`) /
  *FOLDED* (the pin's `solution` glue) / *RENAMED?* (same statement hash, different last name) / **MISSING**.
- **sweep of the twenty modules this session landed**: one real gap — the 20 unported tail declarations of
  `Definitions/Def_NumberField_PrimeNormSums` behind `NumberTheory/PrimeNormSums.lean` (recorded in
  [../CARRY-FORWARD.md](../CARRY-FORWARD.md)); one class of *benign* miss that a reader must be told about —
  `Transform`'s `countable_numberField`/`countable_ringOfIntegers`/`countable_ringOfIntegers'`, replaced by
  an inlined pin body and by the port's `instCountableRingOfIntegers` scoped instance; and two
  `main`-folded rows (`BesselInequality`, `ShiftConvergence`), where the pin's `main` is shape-equal to the
  row's headline but text-different, so neither hash nor name catches it. Everything else — including
  SET-AF79's nine-of-nine and SET-AF80's 70-of-70 — reads complete.
- **fix / rule**: run the audit on every module whose `spec-pin:` wire is an `S_` or `Definitions/` file,
  and state the classification (declared / imported / folded / missing) in the set's brief. A `MISSING`
  row is a manager decision: transcribe it (FR-0221), record it as a deferral, or name the substitution
  that replaced it. Do not read a green checker line as completeness.
- **seen**: 2026-11-14, sweep over SET-AF75–AF80 (20 modules); instrument written and debugged in the same
  pass (the import regex and the `FLTForHuman/` path join were both wrong on the first cut — the sweep
  silently reported "0 satisfied by the import closure", which is why the rule says to run it on a module
  whose answer is known before trusting a clean run).

## FR-0223 [port] — `have`/`let` *do* provide instances: the `haveI`→`have` substitution is always safe, and two diagnoses got it backwards

- **where**: five sets of 2026-11-14. `linter.style.haveILetI` is default-on in this mathlib and fires on
  every `haveI`/`letI`; the standing substitution is `haveI` → `have`, `letI` → `let` (FR-0198's family).
  Three workers (`AF76D`, `AF80A`, `AF79B`) did it unhesitatingly; two (`AF82B`, and a near-miss in
  `AF81A`) concluded instead that "the value must be an *instance*, so `have` does not compile", and one of
  those then claimed a sibling module carried the same warnings — it did not.
- **fact (probed, not argued)**: Lean 4's instance resolution consults **class-typed local hypotheses**
  regardless of binder info, so `have h : μ.Regular := …` followed by `inferInstanceAs (μ.Regular)`
  accepts. `haveI`/`letI` are therefore *syntactic sugar for a case Lean already handles*; the linter is
  telling the truth when it prints a `Try this:` block, and that block is a compiler-checked replacement.
  (`tmp/af82/probe-have-vs-havei.lean` is the probe.)
- **the two wrong turns, both worth recognising**: (i) "delete the `haveI` line → `synthInstanceFailed`"
  is a test of *deletion*, not of the substitution — the instance was never introduced another way in that
  experiment; (ii) "the sibling module has the same warnings" — check it, don't assume it: AF81A's loop was
  warning-free, and a sibling's silence or noise is not evidence about your file.
- **fix / rule**: for every `linter.style.haveILetI` warning, apply the linter's own suggestion first; a
  class-typed `have`/`let` keeps the instance. Escalate to a scoped, documented silencer only when a
  *specific* suggestion fails to compile, and say which site and why. Never "fix" a warning by widening a
  hypothesis or by leaving `haveI` in place.
- **seen**: 2026-11-14, SET-AF82 order B (5 sites, all `have`, module silent, checker and dedup unchanged).

## FR-0224 [spec] — a scaffold's statement must keep the pin's *own qualification* and its `open scoped`; the checker hashes text

- **where**: SET-AF83's manager scaffolding (2026-11-14), four modules written from the pin's `S_` files with
  `sorry` bodies before dispatch. Two statement-level traps, both invisible to `lake env lean`.
- **trap 1 — qualification**: `check_port` matches by `nhash`, the sha1 of the **checker-normalised statement
  text**; `spec/lean_parser.py:norm` erases only `ModularCurve.` and `AlgebraicCurve.` prefixes. Writing the
  row as `Nonempty (EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S)` while the pin writes
  `Nonempty (FactorizationDatum F ψv nψ χ ϖ Ψ g S)` produces a *byte-identical modulo one namespace* statement
  that reports `MISSING (no match)` — no mismatch, no hint. The fix is `open EisensteinGeneral.Piece in` before
  the theorem (the pin's own line) and the bare name in the statement.
- **trap 2 — the scope that the statement needs**: the same scaffold's `∏ i : {w : InfinitePlace F // w.IsReal}`
  failed with `synthInstanceFailed … Fintype {w // w.IsReal}` until `open scoped Classical` was added (the
  pin's `open scoped Classical in` lines are what make its own statements elaborate; `Subtype.fintype` needs the
  `DecidablePred` that scope provides).
- **diagnosis recipe**: when a scaffold reports `MISSING`, do not read it as "the checker is broken" and do not
  re-prove anything — run `statement_db.parse_file` on the pin file and on the module and diff the two
  normalised `stmt` strings. The diff is always a name or a scope.
- **rule**: scaffold from the pin's text, not from the wrapper's qualified spelling; keep the pin's `open … in`
  lines; a green `lake env lean` is not a green statement check. Both gates (`lake env lean`, `check_port
  --force`) before dispatch, and again as the first step of the order.
- **trap 3 — local notation is part of the statement text too**: the pin's `SlabFDFinite` block states its
  two engine lemmas as `μH ((· * x) '' centreCutSiegelSet K c u d₁ d₂) < ⊤` over `local notation "G"` /
  `"μH"` (which expand to `AdelicGL2 (𝓞 K) K` / `adelicGLHaar (Fin 2) (𝓞 K) K`). Scaffolding them with the
  expansions spelled out reports **2 mismatch** — the checker's `norm` does not expand local notation. The
  fix is to carry the pin's two `local notation` lines into the module and write the lemmas with `G`/`μH`.
- **seen**: 2026-11-14, `EisensteinGeneral/PieceFactorizationDatum.lean` (trap 1) and
  `EisensteinGeneral/PieceLatticeMajorant.lean` (trap 2), both green after the two fixes; again on
  SET-AF85's scaffolding — `AutomorphicForm/Adelic/Siegel/FiniteCover.lean` (trap 1: the row read `MISSING`
  with the qualified `AutomorphicForm.SiegelCovering.CoversModCentre` against the pin's bare
  `CoversModCentre`) and `AutomorphicForm/Adelic/Siegel/SlabVolume.lean` (trap 3: `2 mismatch` on the two
  measure lemmas). Both green after the fix; the lesson is cheaper to apply than to rediscover.

## FR-0225 [spec] — gate 6 asked for an in-file `maxHeartbeats` floor; the playbook forbids one, and the gate's own wording cannot hold

- **where**: SET-AF83 (2026-11-14), all four orders. The work order's gate 6 read "a heartbeat floor: `set_option
  maxHeartbeats n` at the top with `n` ≈ 4–8× the natural cost, and record the probe that bounded it (silent at
  `n`, fails at `n/2`)". Playbook §3.5 says the opposite twice: "**no module carries a `set_option
  maxHeartbeats`** — including one transcribed from the pin", and "never add a module `set_option
  maxHeartbeats`".
- **the arithmetic that should have caught it**: "4–8×" and "fails at `n/2`" are incompatible for any margin
  above 2× — at 4× the natural cost, `n/2` = 2× is still *above* the natural cost and therefore silent. Two
  workers (AF83C, AF83A) said so explicitly rather than quietly picking one half. Four of the seven modules
  arrived carrying a floor (12 k, 60 k, 80 k, 100 k, 800 k across four files).
- **fix (manager, on landing)**: remove every in-file floor, keep the probe as a header comment, and re-elaborate
  each module at the playbook's own cap — `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000`. All seven
  silent, no proof changed, and the measured numbers are the deliverable: A ≈20 k, B ≈62 k, C1 ≈7 k, C2 ≈45 k,
  D1 <25 k, **D2 ≈190 k** (within 5 % of the edit loop's cap; `lake build`'s project cap is 4,000,000, so it is
  an edit-loop risk, not a build risk — watch it in any set that reopens `PieceLatticeMajorant`).
- **rule**: a heartbeat *probe* is a measurement reported in the module header ("silent at N, fails at N/2");
  a heartbeat *floor* is a defect marker. Record the first, never install the second. Gate text that conflates
  them will be obeyed literally by a careful worker, which is exactly what happened here.
- **seen**: 2026-11-14, five `set_option maxHeartbeats` sites removed from four modules of SET-AF83; the two
  workers' objections are quoted in [../topics/automorphicForm/SET-AF83.md](../topics/automorphicForm/SET-AF83.md) §5.

## FR-0226 [spec] — count a module's public surface with the corpus parser, never with a `private`-prefix regex

- **where**: SET-AF84's scoping (2026-11-14). The manager sized four orders from a throwaway counter that decided
  "private" by `line.startswith("private ")`. It therefore read **`@[scoped simp] private theorem …` as public**,
  and order C was dispatched with a target of "26 public declarations" when the wire carries **23** and the
  module's structural maximum is **11**. The worker reproduced the true arithmetic from the corpus before writing a
  line of proof: C1 has 1 public declaration (not 4 — the extra 3 are `@[scoped simp] private`), C2 and C3 have 11
  each, and `diff` of `:12-198` in the two files is empty, so 10 of the 23 are the pin's own duplicated engine block
  that the port declares **once**.
- **the two arithmetic facts the inflated number hid**: (i) a pin file may carry the *same* engine block twice (the
  *port once* rule of `port_advise`), so the port's declaration count is strictly smaller than the wire's public
  count; (ii) a pin's `solution` is wrapper glue whose statement is the row's, so it folds rather than adding.
- **the instrument**: `spec/statement_db.py`'s parser is the authority — `parse_file` returns
  `(line, end, name, key, last, kind, priv, anon, stmt, raw, hash)` per declaration, with `priv` and `anon` as the
  parser computes them (it reads attributes and `@[scoped simp]` prefixes). Any count in a brief, a work order or a
  report comes from it — `tools/deps/pubcount.py` is a *regex* and is now retired for this purpose.
- **a target `N ok` is one per *port* declaration, not one per wire public** (added on SET-AF84's landing, from
  the A order): `check_port` emits one verdict per declaration **of the module**, so when one port declaration
  covers two pin publics — a row and the pin's statement-identical `_impl` general form, or a row and its own
  `solution` — the line is *shorter* than the wire's public count and the audit says so (`RENAMED?` / `FOLDED`).
  SET-AF84A's order asked for "3 ok" for a two-row module whose pin carries three publics, and the worker
  correctly delivered `2 ok` + `complete`; the two halves of that same order contradicted each other.
- **and the count was never the gate anyway**: `check_port` iterates the *module's* declarations, so it reports a
  missing declaration as nothing at all (`N ok` looks the same whether one declaration or ten are absent).
  `scaffold_audit` is the direction-reversed check and is what proves a step-1 transcription complete. A target of
  "`N ok` for a given N" is therefore a *sizing* statement, and `scaffold_audit: complete` is the *acceptance* one.
  Both are gates; only the audit can fail on an omission.
- **seen**: 2026-11-14, SET-AF84 order C at step 1 (`11 ok / 0 / 0` + `complete`, 23 pin publics on the wire);
  SET-AF83's §1 table also carried the same inflation (15 publics / 217 engines for a true 17 / 196) and was
  corrected on the second pass.

## FR-0227 [lean] — a dropped type ascription becomes an `isDefEq` timeout, and the 4 M project cap hides it

- **where**: `ModularForms/HeckeFiniteAlgebra.lean:257`, in `span_heckeAlgebra_eq_fullC` (the weight-2
  `ℂ`-span = `fullC` bridge). The shape recurs at any `have h : A ≤ B` closed by `refine Algebra.adjoin_le ?_`
  where `B` is a `Subalgebra.restrictScalars` coming from a subalgebra over another scalar ring.
- **symptom**: at the playbook's edit-loop cap the *whole declaration* aborts —
  `error: (deterministic) timeout at isDefEq, maximum number of heartbeats (200000)` on the last `exact`, plus two
  cascading `«tactic execution»` timeouts on the enclosing tactic and its statement. Meanwhile
  `lake build FLTForHuman.ModularForms.HeckeFiniteAlgebra` is **green in 7.8 s**, so the tree never showed it and
  the stale `.olean` (built by `lake build`) made the module look fine to every consumer.
- **cause**: the pin writes `exact (Algebra.subset_adjoin hx : x ∈ fullC N)`; the port had transcribed it as
  `exact Algebra.subset_adjoin hx`. Without the ascription the expected membership is
  `x ∈ ↥((fullC N).restrictScalars ℤ)` and the scalar ring of `Algebra.subset_adjoin` stays a **metavariable**, so
  `isDefEq` must unfold `Subalgebra.restrictScalars`, `fullC`, both `Algebra.adjoin`s *and their instance
  arguments* to decide that the two `Subalgebra` carriers agree. No search goal runs, so
  `trace.Meta.synthInstance` reports nothing — this is the `isDefEq`/`whnf` branch of the §6 classification, not
  the search branch.
- **fix**: restore the pin's ascription. Elaboration is then directed — `R := ℂ` is fixed by `fullC`, the set by
  `hx`, and the only remaining check is `↥(Algebra.adjoin ℂ s)` against `↥(fullC N)`, one delta. Alternative when
  the ascription reads badly: state the element form once (`SetLike.le_def.mp`) and apply that at the site.
  Verified silent at 200 000 and still silent at **60 000** (~3× margin), no `set_option maxHeartbeats`; the
  statement check is unchanged because the edit is proof-only (`7 ok / 0 mismatch / 0 missing`).
- **the instrument failure it exposes**: the lakefile sets `maxHeartbeats := 4 000 000` project-wide, and
  `lake build` inherits `leanOptions` while `lake env lean` does not. So a declaration over the *edit-loop* cap is
  green at tier 1, green at tier 2 and green in a whole-tree build, and stays invisible until someone runs
  `lake env lean` — a module that **builds** is not a module that **fits**. Read "green build" as evidence about
  the 4 M cap only, and run the 200 k edit loop on any module you touch.
- **seen**: 2026-11-14; `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularForms/HeckeFiniteAlgebra.lean`. The pin carries `set_option maxHeartbeats 6400000` in
  `S_CuspForm_finrank_span_heckeAlgebra_eq_finrank.lean`, consistent with it paying this same defeq (unverified on
  the pin's own line).

## FR-0228 [spec] — a pin declaration written by *equation clauses* has its whole proof stored as its `stmt`

- **where**: SET-AF85 order B (2026-11-14), `UnramifiedWhittaker.exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero`'s
  second pin, `P2M/Sol/S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.lean:185`
  (`finComponent_prod_localEmbed`), declared as
  `theorem foo (…) : ∀ l, l.Nodup → … = if w ∈ l then c w else 1 | [], _ => by simp | (a :: l), hl => by …`.
- **symptom**: `check_port` reports `MISMATCH` for any port declaration whose body is not the pin's **verbatim**,
  and a `sorry` body cannot match at all. `84 ok / 1 MISMATCH` was the step-1 reading of an otherwise complete
  transcription.
- **cause**: `spec/lean_parser.top_level_cut` finds a declaration's statement by cutting at the first top-level
  `:=`/`where`. An equation-clause theorem has neither before its bodies, so the cut returns `len(chunk)` and the
  corpus stores the **whole proof** — plus whatever follows (`section W` / `variable …`) — as that declaration's
  `stmt`. Measured on the pin: `stmt` begins with the signature and continues through `| [], _ => by simp | (a ::
  l), hl => by rw […] … if_neg hwl …` into the next `theorem`. The hash therefore depends on the proof text.
- **two forces that cannot both win**: transcribing the body verbatim keeps `ok` but freezes the pin's
  deprecated `if_pos`/`if_neg` (v4.34 warns unconditionally), so the module is not silent; renaming them to
  `ite_eq_left`/`ite_eq_right` (the port's recorded practice) is silent but changes the hash, so `1 mismatch`.
  There is no transcription that satisfies both gates.
- **fix taken**: an `own:` row in `spec/decl_markers.tsv` (tier 2, not diffed) with the reason spelled out, so
  the declaration is verified neither by hash nor by name but by hand, and the module stays silent. The row key
  is the **full** name the checker parses (`UnramifiedWhittaker.DiagOne.finComponent_prod_localEmbed`): the
  module-relative `DiagOne.…` reads as `STALE MARKER`, and a `pin:` row would not help — tier-1 name matching
  still hash-gates the statement.
- **rule**: a pin declaration stated with pattern-matching clauses gets an `own:` row from the start, with the
  reason "the pin's equation-clause form defeats the statement cut"; do not spend a round hunting for a body that
  matches, and never let a deprecation warning through to keep a hash.
- **the instrument fix this record does not make**: `top_level_cut` should stop at a top-level `|` that begins a
  new equation **after** a complete signature (or use the declaration's own syntax tree). Changing it re-hashes
  every equation-clause declaration in the corpus, so it is a parser-version change — run
  `python3 spec/statement_db.py selftest` and diff the corpus hashes before and after, not a wave-time edit.
- **seen**: 2026-11-14, SET-AF85B step 1; `84 ok / 0 mismatch / 0 missing / 1 own / 0 kw` after the marker.

## FR-0229 [orchestration] — "the premise is in the import closure" is a measurement, not a recollection

- **where**: SET-AF85 order C, C1 (`AutomorphicForm/Adelic/Cusp/IrreducibleSpine.lean`), 2026-11-14. The
  manager's brief asserted that both premises of
  `AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul` were
  already in the module's import closure.
- **symptom**: the first premise was. The second,
  `Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq`
  (`Analysis/Normed/Operator/CompactFiniteDimensional.lean`), was in the *port* but imported by nothing in
  `IrreducibleSpine`'s **354-module** closure, so the worker hit `unknownIdentifier` at the point of use —
  a proof-side failure several declarations into the order. The scaffold's green gates could not have caught
  it: the statement does not mention the premise, `check_port` diffs statements, and `lake env lean` on a
  `sorry` body never calls the premise.
- **second half of the defect**: that module's `.olean` was *absent* from `.lake/build/lib/lean/…` (only
  `.olean.hash` / `.trace`), so even the correct `import` line would not have sufficed — the worker built the
  one dependency (2.8 s) before adding the line. This is FR-0033's "a `Replayed` line is not evidence that the
  `.olean` exists", met from the other side: a module in the *dependency* position whose olean was never
  produced because nothing had imported it yet.
- **cause**: the brief's closure claim came from sampling a few likely layers (a `grep` over the home's
  neighbours), not from the graph. The rule in the scoping recipe (§4) says the home must sit above the
  proof's premises and calls the check "a first cut only" — it does not say the *manager* may skip it.
- **recipe** (10 lines, run before dispatch for every row whose premise is a port declaration):
  1. BFS over `^import FLTForHuman\.` from the home module, mapping dotted names to paths;
  2. check each premise's own module is in that closure — the premise's module is `grep -l "^theorem <last
     name>"` over `FLTForHuman/`, or the `spec-pin:`/`SOURCES` map for a pinned declaration;
  3. check the `.olean` exists under `lean/.lake/build/lib/lean/FLTForHuman/…` for every module on the
     path that the order will need, and build the missing ones (bounded, `flock` + `timeout`) rather than
     leaving it to the worker.
- **rule**: a work order that says "its premises are imported" states a measurement; when the order instead
  says "add the `import` line if the closure lacks it", it costs the worker one `import` edit and one build,
  not a stall — and the brief should say which premises it *verified*.
- **instrument (added the same day)**: `tools/deps/premise_imports.py --nodes … [--missing-from <module>]
  [--olean]` prints one `import` line per *declaring module* of a row's graph premises, with the premises
  it serves, filtering out the ones already in the target module's import closure (BFS) and flagging a
  missing `.olean`. `--nodes A --nodes B …` takes the rows; `--missing-from` takes the home. It reproduces
  AF87A's hand BFS line for line.
- **its scope, stated so it is not over-trusted**: only the *graph* premises. A proof may need a module that
  is not a premise at all — AF86C's `AutomorphicForm.adelicArchGLIncl` (`AutomorphicForm/Adelic/ArchType.lean`)
  is the recorded case — so a scaffold's import list is this report **plus** whatever the elaboration asks
  for. The compile loop still has the last word.
- **seen**: 2026-11-14, SET-AF85C (the worker reported at first belief, built the dependency, added the
  line; `IrreducibleSpine` closed at `21 ok / 0 / 0` plus the rest of its six gates). The same order also
  needed `open scoped Pointwise` and a countable-instance chain that the scaffold's `open` list had dropped —
  both supplied proof-side, so the module kept `0 own`.
- **count of the recurrence before the instrument existed**: **eleven** premise modules across four orders in
  two sets — AF85C (1: `CompactFiniteDimensional`), AF86B (3: `MulRightInvariant`, `ArchCasimir`,
  `ArchCasimirComplex`), AF86C (2: `MulRightInvariant`, `ArchType`), AF87A (5: `MaximalCompactFactors`,
  `TestFnTop`, `RightConvProductIntegral`, `ArchCutReproducer`, `ArchPeterssonPairing`). Every one was one
  `import` edit; every one cost a worker the same measurement. That is what the tool is for.

## FR-0230 [orchestration] — a bounded `lake build` killed mid-cascade leaves the *dependency's* olean missing

- **where**: SET-AF87A (2026-11-14). `ProductMeasure.olean` was present at 13:46 and gone at 13:48 (only
  `.olean.hash` and `.trace` left), while the worker's own `flock`'d `timeout 110 lake build` of
  `LevelSphericalLimit` was running. The module imports `ProductMeasure`, so the worker's next edit loop could
  not import it.
- **mechanism**: `lake build` on a module whose dependency is stale *removes* the stale olean, then rebuilds
  it; if the wall bound kills the build in between, the dependency's olean is simply absent. Nothing in the
  output says "removed": the failure the next command gives is `unknown identifier` at the *first use* of a
  declaration from that module — which reads like a missing premise (FR-0229's symptom) but is not one.
- **diagnosis, one command**: `ls lean/.lake/build/lib/lean/FLTForHuman/<Dir>/<Module>.olean` (FR-0033's check,
  from the other side — there a `Replayed` line hid a missing olean, here a killed build removed one).
- **fix**: rebuild the dependency **alone**, under the lock, with its own bounded call
  (`flock /tmp/flt-build.lock timeout 110 lake build FLTForHuman.NumberTree.<Dep>` — a single module's build
  is seconds; the cascade is what was expensive), then resume. Never hand-make an olean and never edit the
  dependency to make the import resolve. The worker did exactly this.
- **the preemptive rule for a long first-time cascade**: build the *dependency* first, in its own call, before
  building the dependent — then the dependent's `timeout 110` covers one module, not a cascade. A one-shot
  `timeout 900` on the dependent is out of policy (AGENTS.md: every tool call within two minutes) even when it
  finishes faster; the two-call version respects the bound and gives a better failure message.
- **seen**: 2026-11-14, SET-AF87A; the rebuild was `3701 jobs`, exit 0, and the dependency was untouched.

## FR-0231 [mathlib-drift] — `continuous_mul_right` is `continuous_mul_const` in v4.34

- **where**: SET-AF88A, the archimedean bi-finiteness pin (pin 3 `:194`). The pin writes
  `continuous_mul_right` for `Continuous (fun g => g * a)`; v4.34 has it as `continuous_mul_const`
  (`continuous_mul_right` is gone).
- **why it matters beyond one line**: the `Continuous (· * g)` idiom is everywhere in the adelic continuity
  layer (right-translation continuity, `placeEmbed`-covariance, the Hecke-gen action), so this rename will be
  met again in every ported continuity proof that predates it. The substitution is mechanical and
  statement-neutral.
- **seen**: 2026-11-14, SET-AF88A; one occurrence, fixed in place, `check_port` unchanged at 81 ok.

## FR-0232 [port] — "statements only, `sorry` bodies" is wrong for `def`s, and a whole-declaration splice must stop at the next *prelude*

Two instructions from SET-AF88A's step 1 that every later work order should carry verbatim.

- **`def` bodies are not statements.** A `sorry`-bodied `def` loses the section variables only its *body*
  mentions, so the elaborated arity changes and the pin's `solution` no longer applies (`W`, `Stable`,
  `trSpan` in the tensor-split pin were exactly this). The rule is: **theorems get `sorry` bodies, `def`s are
  transcribed verbatim** — a step-1 pass that stubs every `def` produces a module that is checker-green and
  cannot be proved.
- **A whole-declaration splice stops at the next declaration's *prelude*, not at its keyword.** Cutting a
  body at `theorem`/`def` swallows the `variable` / `include` / `section` lines that sit between a body and
  the next declaration; the symptom is a fake *statement* error (or a stray `end`) several declarations later,
  which reads as a mis-transcribed statement. The worker's `lean/tmp/af88/splice.py` had this bug and it cost
  one round; the fix is to cut at the first *declaration keyword or section/variable/include line* after the
  body.
- **and a `def` can carry equations**: `iterMulVec`'s hashed statement is signature **plus** equations
  (pin 1 `:275`), so FR-0228's `|`-clause case is live outside the Whittaker module — a `:= sorry` reads as
  `MISMATCH` and the equations must be transcribed.
- **seen**: 2026-11-14, SET-AF88A (81 declarations, step 1 in one pass after the two rules were applied).

## FR-0233 [lean] — a bare `end` no longer closes a `namespace` at v4.34, and the error is 400 lines away

- **where**: SET-AF88C, `AutomorphicForm/Adelic/KfSmoothTensor.lean`. Three subject namespaces
  (`KfLevel`, `CuspidalConstituent.Conj`, `LevelSplit`, `SliceTensor`) were closed with a bare `end` as the
  pin does; at v4.34 the parse fails — but the reported position is the **file's last `end`**, several hundred
  lines after the offending one.
- **probe** (`tmp/af88/probe-bare-end.lean`): `namespace Foo / theorem bar : True := trivial / end` →
  `error: Missing name after `end`: Expected the current scope name `Foo`` with the hint `end Foo`.
  The same file with `section … end` inside the namespace is fine: **a bare `end` still closes a `section`,
  only a `namespace` needs its name.**
- **why it is worth an entry**: the pin (and every port module written before this bit) closes namespaces
  with a bare `end` in places, so a whole-file transcription can carry the defect silently; and the distant
  error position makes it look like a missing `end` at the *bottom* of the file. The cure is local (`end Foo`)
  and statement-neutral.
- **seen**: 2026-11-14, SET-AF88C; four namespaces, four `end`s named, `check_port` unchanged.

## FR-0234 [tooling] — `scaffold_audit.py` and `premise_imports.py` are CWD-relative

- **where**: SET-AF88's work orders. The gate lines were written as
  `python3 tools/deps/scaffold_audit.py <module>` from the repository root, which fails with
  `ModuleNotFoundError: No module named 'statement_db'` — `scaffold_audit.py` inserts `../../lean/spec` on
  `sys.path` relative to the **caller's** directory, and `premise_imports.py`'s `--port-root` defaults to
  `../../lean/FLTForHuman`, likewise relative.
- **fix**: both are run from `tools/deps/` (`cd tools/deps && python3 scaffold_audit.py ../../lean/FLTForHuman/…`),
  which is how `check_port.py` (`spec/`, run from `lean/`) differs — two tools, two working directories.
- **rule for a work order**: quote the tool commands with their working directory, not just their paths.
  A command that fails for a path reason costs a worker a detour and looks like a broken tree.
- **seen**: 2026-11-14, SET-AF88C (reported by the worker; both tools work as documented from `tools/deps/`).

## FR-0235 [port] — `haveI`/`letI` → `have`/`let` is not always safe: a `letI`-bound instance **in the goal type** needs the inlining

- **where**: SET-AF89D1, `AutomorphicForm/Adelic/Cusp/BoundedGenuineRealization.lean` (the
  `memLp_two_restrict_of_bound` statement and the 69 row's instance context).
- **what FR-0223 said**: replacing `haveI`/`letI` by `have`/`let` is a statement-neutral v4.34
  substitution (the `haveILetI` linter). It is, *when the instance is only used by the proof*.
- **the failure**: at three sites the frozen goal **type** itself carries a `letI`-bound
  `MeasurableSpace` (the `MemLp … ((adelicGLHaar …).restrict D)` conclusion). That instance is
  opaque to synthesis in the goal, and `have`/`let` fails with `synthesized type class instance is
  not definitionally equal … synth glBorel / pins.mS`. Only `letI`'s *inlining* of the value into
  the goal type makes the statement elaborate.
- **the fix (no silencer, no statement change)**: write the definition/theorem in **term
  position** with `letI …` (`letI : MeasurableSpace … := …; body`), which keeps the inlining; no
  linter fires and no `set_option` is needed. Do not "fix" the goal by restating it.
- **rule**: FR-0223's substitution is safe only when no `letI`-bound instance appears in the goal
  type; otherwise keep `letI` in term position.
- **seen**: 2026-11-19, SET-AF89D1 (three sites).

## FR-0236 [instrument] — a `sorry` body hides `linter.unusedVariables`

- **where**: SET-AF89D1, the 69 row `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre`.
  Its frozen `hd : d₁ < d₂` and `hcov : CoversModCentre …` are dead in the pin's proof.
- **symptom**: the manager's scaffold was silent because a `sorry` body counts as using every
  binder; the same theorem with `trivial` warns. So a scaffold's "silent + built" is not evidence
  that its frozen binders will be spent, and a worker's first proof attempt meets a linter the
  scaffold hid.
- **fix**: spend the hypothesis once (`have hd' … := hd`) rather than renaming it (the binder name
  is part of the wire) or silencing the linter (FR-0164).
- **rule**: when a worker removes a `sorry`, expect `linter.unusedVariables` on binders the pin's
  proof ignores; budget one line per dead binder and keep its name.
- **seen**: 2026-11-19, SET-AF89D1 (two binders, one row).

## FR-0237 [instrument] — `scaffold_audit.py` matches by **last name**, so an unrelated declaration can read a pin public as "satisfied"

- **where**: SET-AF89 B and C. The audit's `imported` bucket is a last-name test over the module's
  port-import closure, not a statement test (`scaffold_audit.py`'s `closure_names`).
- **the instances**: the pin's `Kw` (a `Subgroup`) was credited to `AutomorphicForm.ArchInfra.Kw`
  (a `Type`-valued abbrev) in B, and the pins' public `main` (C4 `:119`, C5 `:110`) to unrelated
  `main`s in `ProductMeasure`/`ArchFiniteFactorization` in C. In both cases the audit read `complete`
  while a pin public was not declared.
- **effect**: `complete` is a **last-name coverage** test; it can be green on a collision. It is
  still the only instrument that sees an *omitted* declaration (`check_port` iterates the module's
  declarations and cannot), so the two must be read together with the wire's public count:
  `declared + imported + folded = wire`, and every `imported` row should be checked for a same-name
  collision when the declaration is mathematical, not glue.
- **the resolution in this set**: B declared `Kw`/`W` at the pin's statements (collision removed);
  C left the two `main`s folded into their rows (`solution`'s statement *is* `main`'s), so the
  audit's `complete` there leans on a collision and the report says so.
- **rule for a work order**: state the audit's three buckets (`declared / imported / folded`) and
  require the worker to name any `imported` match that is not statement-identical.
- **seen**: 2026-11-19, SET-AF89B/C.

## FR-0238 [mathlib-drift] — `AdeleRing` and `InfiniteAdeleRing` are `def`s, so the pin's `rw`-into-the-character scripts fail at implicit transparency

- **where**: SET-AF90B, `NumberField/AdelicLevel/ArchLevelLattice.lean`, the
  `stdAddChar_single_half` conjunct of the `diagOne` row (pin `:171`).
- **the pin**: `rw [psiK_apply, adelicTrace_apply, psiQ_apply]` and `rw [traceInfHom_apply]`
  compute the standard character by unfolding the projection; at v4.34 `AdeleRing` is a `def` of a
  product (not an `abbrev`; `InfiniteAdeleRing` too), and `rw` matches at `implicit` transparency,
  so the unfolded goal is ill-typed and the script does not replay.
- **fix (statement-neutral)**: name the components first — `set x : InfiniteAdeleRing F`,
  `set u : AdeleRing (𝓞 F) F`, `set z : AdeleRing (𝓞 ℚ) ℚ` — and close with
  `rw [psiK_apply, htr, hzpsi]`. This is FR-0219's def-transparency class, now on the two adele
  ring abbreviations; every later `psiQ`/`traceInfHom` computation will pay the same one
  substitution.
- **seen**: 2026-11-20, SET-AF90B (one row, two sites).

## FR-0239 [port] — a scaffolded row cannot always stay at the top of its module

- **where**: SET-AF91A, `AutomorphicForm/Adelic/WhittakerSum.lean`. The scaffold declared the row
  at the top (the manager's convention: headline first, engines to be transcribed below it by the
  worker). The pin's flattened file has the opposite order: its engine `innerSolution` at `:1060`,
  its `solution` at `:1140`.
- **the constraint**: Lean has no forward references, so a row at the top can only be a `sorry`;
  once the proof is the pin's, it has to follow the engine. The worker moved the row to the end of
  the module (`:1143`) with the name, visibility and statement byte-identical.
- **why it is harmless**: `check_port` and `scaffold_audit` are declaration-position-blind; the
  wire, the axioms, `dedup` and `move_dead` do not move. The only cost is that a reader comparing
  the scaffold with the landed file sees the row at the bottom.
- **rule for a work order**: a scaffolded row may be moved within its module once its proof is
  transcribed; never re-spell it, and say in the report where it moved.
- **seen**: 2026-11-20, SET-AF91A (one row, 1,161-line module).

## FR-0240 [instrument] — the frontier's name tier rejects short generic last names, so a ported `add`/`smul` row never leaves the shelf

- **where**: SET-AF92, `AutomorphicForm/Adelic/ProductionPinsTail.lean` ports
  `AutomorphicForm.IsCuspidalFn.add` and `.smul` (check_port 5 ok, audit complete), yet both stay in
  the `--ready` block after the landing read.
- **cause**: `frontier.py`'s name tier filters the port's declared last names through
  `_distinctive`, which drops short generic method names (`add`, `mul`, `pow`, `smul`, …) to avoid
  crediting a node through an unrelated namesake. `IsCuspidalFn.add`/`.smul` are exactly such names,
  so no port declaration can ever credit them — even the real one under their own namespace.
- **effect**: the plain landing read under-counts by the rows with such names (here 2 nodes / 25
  silo: 456 / 222,580 plain against 454 / 222,555 corrected). The corrected read is
  `frontier.py … --port <node> --port <node>` (the dual of `--unport`); the two figures must be
  quoted together, as for the FR-0047/MD-005 marker corrections.
- **rule**: a landing read that moves by less than the cut is checked against the cut's *long-named*
  rows first; for a row whose last name is generic, quote the `--port`-corrected figure and say so.
- **seen**: 2026-11-20, SET-AF92 (2 rows, 25 silo).

## FR-0241 [instrument] — `namespace_events` computes offsets on the line-comment-stripped text, so any `--` comment shifts every later `namespace`/`end` early

- **where**: `spec/lean_parser.py:80` and `spec/statement_db.py:204`. `parse_file` passes
  `code = flat_code(text)` (block comments blanked, newlines kept, **line comments kept**) and then
  calls `P.namespace_events(code)`, which scans `strip_line_comments(text)` — a *shortened* copy.
  The event offsets are therefore smaller than the corresponding offsets in `code`.
- **repro**: `namespace Foo / -- a comment line / theorem a : True := trivial / end Foo` reports the
  `end` at offset 43 while it starts at 60 in `code`; every event after a `--` line fires 17 bytes
  early.
- **symptom**: a declaration after a `--` comment is attributed to the **previous** namespace (or a
  `--`-comment-heavy prelude makes an `end` fire inside the previous declaration's body). SET-AF92D
  met it: a three-line `--` prelude note put `end WhittakerUnfolding` inside the previous body and
  parsed `addChar_neg_eq_conj` as `AutomorphicForm.…` rather than `…WhittakerUnfolding.…` (no gate
  moved: `check_port` matches by last name + statement hash, and `scaffold_audit` by last name).
- **workaround used**: a `/- … -/` block comment for the prelude note (block comments are blanked
  by `flat_code` with their offsets preserved).
- **fix (to be made after the wave)**: make `strip_line_comments` length-preserving — replace each
  `--[^\n]*` by spaces of the same length — so `namespace_events` offsets are offsets in the text it
  is given; the parser's own callers (which strip first and then scan) are unaffected. Re-run
  `python3 statement_db.py` selftest and `check_port --all` after the change, and expect the corpus's
  full names (not the statement hashes) to move for `--`-commented files.
- **seen**: 2026-11-20, SET-AF92D.

## FR-0242 [instrument] — `check_port` skips private port declarations, so a private engine is unchecked

- **where**: `spec/check_port.py:474` (`if priv: continue`). SET-AF92A/B/C are the extreme case:
  modules of 134 / 134 / 101 declarations, of which one row is public and the rest are the pin's
  private engine. `check_port --force` reads **1 ok** on all three however complete or incomplete
  the engine.
- **what this corrects**: SET-AF92's work order (and the standing phrasing) said the checker's
  "dotted fallback reads" a private port declaration against the pin's private copy. It does not:
  the fallback matches a *public* port declaration to a pin-private row; a `private` port
  declaration is skipped outright. A private engine's only gates are the elaboration, the proof it
  feeds, `#print axioms`, and a manual `statement_db.parse_file` diff.
- **the measurement to use instead**: parse both sides and diff names + statement hashes, e.g.
  `python3 - <<'PY'` with `statement_db.parse_file` over the pin and the module — AF92B did exactly
  this (134/134 names, 133/133 private names, 0 statement-text differences) and so did AF92A (0
  diffs). Record that diff in the report whenever a module's surface is mostly private.
- **rule for a work order**: for a private-engine pin, state that `check_port`'s `N ok` counts only
  the public surface, require the `parse_file` name/statement diff, and keep the elaboration +
  proof + axioms as the substantive gates.
- **seen**: 2026-11-20, SET-AF92A/B (both reported it; the brief had it wrong).

## FR-0243 [instrument] — `move_dead` cannot see instance consumption, so a pin's `def` + `attribute [local instance]` has to become a `private instance`

- **where**: SET-AF92E, `AutomorphicForm/Adelic/AdelicTraceTail.lean`. The pin declares
  `algQK`/`algQL`/`finiteDimensional_QK`/`finiteDimensional_QL`/`isScalarTower_QKL` as
  `def`/`theorem` plus `attribute [local instance]`; the port transcribed them verbatim and
  `move_dead` read **6 declarations, 42 lines** — it sees declarations, not instance search, so the
  local instances look dead.
- **the accommodation**: declare them `private instance` with byte-identical bodies and statements
  (`@[reducible]` kept); instance consumption then counts as a use and `move_dead` reads `0/0`. The
  module stays silent and `linter.dangerousInstance` does not fire (the instances are private).
- **why it is safe**: the declarations are `private`, so the checker skips them (FR-0242) and the
  pin's own visibility is unchanged; only the keyword differs. A literal transcription cannot
  satisfy gates 5–6 as written.
- **also worth carrying**: a `private scoped instance` is invisible to `lean_parser.DECL_RE`, so the
  corpus parser (and hence the checker and the audit) never sees it; `dedup.py` has its own scanner
  and counts it. A module whose surface includes scoped instances will report different counts from
  the two tools (here 23 vs 26), and the difference is expected.
- **seen**: 2026-11-20, SET-AF92E.

## FR-0244 [tree] — a module in the package imports a file that does not exist, so `lake build` of it fails

- **where**: `FLTForHuman/LanglandsTunnell/TateLocal/DirichletIdele.lean:6` imports
  `FLTForHuman.HeckeCharacter.Dirichlet`, and there is no such file (the directory
  `FLTForHuman/HeckeCharacter/` exists, `Dirichlet.lean` does not). `lake build
  FLTForHuman.LanglandsTunnell.TateLocal.DirichletIdele` fails with
  `bad import 'FLTForHuman.HeckeCharacter.Dirichlet'`; the module has no `.olean`, so anything
  importing it fails with "object file … does not exist".
- **how it surfaced**: SET-AF93's central-scalar row needs `DirichletCharacter.dirichletIdeleChar`,
  which the port declares *only* in that module, so the row's statement could not elaborate.
- **the cure** (next touch of that module): either restore the missing import to the module that now
  holds the Dirichlet-character development, or delete `DirichletIdele.lean` and let
  `definitions/Def_DirichletCharacter_DirichletIdeleChar` be ported into `NumberTheory/RatIdele/`
  (which is where its `RatIdele.unitPadicAt`/`unitResidue` block belongs) together with
  `DirichletCharacter.dirichletIdeleChar`.
- **rule**: a `--selfcheck`/`--ready` read does not see a broken *module*; only a build does. When a
  row's statement names a definition, check that its home module actually builds (FR-0049's
  vocabulary gate, one level down).
- **seen**: 2026-11-20, SET-AF93 scoping.

## FR-0245 [mathlib-drift] — `Matrix.SpecialLinearGroup` is a `def`, so the pin's `mapGL_coe_matrix` rewrite does not replay

- **where**: SET-AF93A, `LanglandsTunnell/WeightOneLiftAdelic.lean`, the body of
  `DetIntegral.exists_mapGL_eq_of_mem_finiteIntegralGL2` (pin 1 `:64`).
- **the pin**: `rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]` to turn a `SL(2, ℤ)`-value into its
  matrix of entries. At mathlib `v4.34` `Matrix.SpecialLinearGroup` is a `def` of
  `{A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1}` (not an `abbrev`), so the rewrite is rejected with
  "not type-correct under the implicit transparency level" — the same class as FR-0238, on the
  special-linear group.
- **fix (statement-neutral, body only)**: drop the `rw` and keep the `change (algebraMap ℤ ℚ) (A i j)
  = _` that the pin writes immediately after it; it closes the goal on its own.
- **rule**: any pin body that `rw`s a `…_coe_matrix`/`…_coe` lemma through `SpecialLinearGroup` or
  `GLPos` needs the same treatment; the `change` form is what to write.
- **seen**: 2026-11-20, SET-AF93A.

## FR-0246 [instrument] — flattening a pin's search-stage namespaces can change a *statement*, so a scaffold's `check_port` pass is the gate, not the transcription

- **where**: SET-AF94A, `LanglandsTunnell/WeightOneLiftLevel.lean`, `repZ_eq_map` (pins
  `S_…qCoeff_hecke_eq_…:192` and `S_…sum_weightOneLift_…:67`).
- **the pin**: the declaration is
  `HeckeCosets.repZ p i = (repMat p i).map (Int.castRingHom ℤ_[p])` — it qualifies `repZ` through
  the search-stage namespace (`HeckeCosets`) because in the pin the definition lives there while
  `repMat` lives in `DescentEngine`.
- **what went wrong**: the port flattens those namespaces to `DihedralWeightOne` (the row's own
  namespace), so the scaffold wrote `repZ p i = …` and `check_port` read **1 mismatch** out of 84.
  The bodies compounded it: the pin's proofs say `unfold HeckeCosets.repZ`.
- **the fix**: keep the pin's statement text verbatim (qualifier included) and add a `private`
  `abbrev HeckeCosets.repZ := DihedralWeightOne.repZ` so the qualified name resolves; the alias is
  `private`, so the checker and `scaffold_audit` skip it (FR-0242), and the statement hashes to the
  pin's, which is the stronger property — no `decl_markers.tsv` row is needed.
- **rule for a work order**: "the statements are the pin's byte-for-byte" is a claim the *checker*
  has to make, not the generator. State in the order that a `check_port` mismatch on a *statement*
  (not a body) is a scaffold defect to report, and that the cure is the pin's own text plus a
  private alias for any qualifier the flattening dropped.
- **seen**: 2026-11-20, SET-AF94A.

## FR-0247 [instrument] — `scaffold_audit` and `check_port` read `spec-pin:` out of prose, so a header that mentions the token corrupts the wire

- **where**: SET-AF94B, the `## Deferred pin surface` section of
  `LanglandsTunnell/WeightOneLiftNebentypus.lean`.
- **symptom**: `scaffold_audit` printed `(pin file not found: `)` — the scanner is
  `spec-pin:\s*(\S+)` over the whole file, so prose of the form "the deferred pin's
  spec-pin: `S_….lean` is …" (with a backtick or a full stop after the token) registers a bogus pin
  source whose name is the punctuation.
- **the cure**: write the deferral without the token — name the pin file and say it is deferred —
  or quote it as `` `spec-pin` `` (no colon). Both tools share the scanner, so the same prose breaks
  both.
- **also worth carrying**: a module's wire must not name a pin source the module does **not**
  transpose, even when the omission is deliberate; that is MD-001's false-ported-marker mechanism
  (a wired-but-absent source hides a node from every planning read). Cutting a pin source's rows
  means cutting its `spec-pin:` line in the same touch, and registering the deferral in prose.
- **seen**: 2026-11-20, SET-AF94B.

## FR-0248 [process] — a scaffold generator re-run after a landing rewrote three finished modules; `git checkout --` is the cure, disarming the generator is the prevention

- **where**: SET-AF95, 11:45: `lean/tmp/af93/gen3.py` (the AF94 scaffold generator) re-run to pick up an
  `open`, which rewrote `LanglandsTunnell/WeightOneLiftLevel.lean` (1,164 → 622 lines),
  `…WeightOneLiftNebentypus.lean` (506 → 439) and `…WeightOneLiftQCoeff.lean` (320 → 439) from their
  *scaffold* templates, discarding the agents' proof bodies and header prose. The user had committed
  them at `e55b790`, so `git checkout -- <three paths>` restored everything exactly.
- **why it was not caught earlier**: the generators live in `lean/tmp/af93/` and write by
  path (`OUT + 'LanglandsTunnell/…'`), so a run for a *new* set regenerates every module that
  generator was ever pointed at, not only the new one. Nothing in the script says "these outputs are
  landed".
- **the cure used**: restore from the commit, rebuild the oleans from the restored sources under the
  lock, and re-verify one row's `#print axioms` (a stale `sorry`-based olean is otherwise invisible —
  the AF93/FR-0033 lesson).
- **the prevention, now in force**: every generator in `lean/tmp/af93/` is renamed `gen*.py.used` the
  moment its output is landed or handed to an agent, so a later `python3 gen…py` cannot run; and a
  re-run for a new set must be a *new* script whose `OUT` paths are only the new modules.
- **rule for the next manager**: a scaffold generator is a one-shot tool. Freeze it before dispatch
  (SET-AF94's lesson) **and** disarm it after landing (this one). `git status` before and after any
  generation is the cheap check: a tracked file listed as modified is a clobber.
- **seen**: 2026-11-20, SET-AF95 (found by order AF95E, which noticed HEAD 1,164 lines vs a 622-line
  working tree).

## FR-0249 [mathlib-drift] — `Nat.Primes` is a `def`, so `rw [natGenerator_primesEquiv_symm]` does not replay (FR-0238/FR-0245 class, third instance)

- **where**: SET-AF95B, `NumberTheory/RatIdele/UnitResidue.lean`, the two `rw [natGenerator_primesEquiv_symm]`
  sites (pin `:90`, `:106`).
- **symptom**: "not type-correct under the `implicit` transparency level" — at mathlib `v4.34`
  `Nat.Primes` is a `def` of `{p // p.Prime}`, so the goal's `⟨↑p, ·⟩` argument is not syntactically
  the subtype the lemma expects.
- **fix (body only)**: name the place first — `set q : Nat.Primes := ⟨(p : ℕ), …⟩` — then the pin's
  `rw` replays against `q`.
- **the class, now three sets running**: FR-0238 (`AdeleRing`, `InfiniteAdeleRing`), FR-0245
  (`Matrix.SpecialLinearGroup`), this one (`Nat.Primes`). The pattern is always the same: a pin body
  that `rw`s a `…_def`/`…_coe` lemma through a `def`-abbreviation fails at `implicit` transparency;
  the cure is to name the intermediate object with `set`/`have` and then rewrite.
- **seen**: 2026-11-20, SET-AF95B.

## FR-0250 [mathlib-drift] — three deprecation/ambiguity traps met in one row (deprecated lemma, `Matrix`-shadowed `mul_inv_rev`, a changed q-expansion extensionality)

- **where**: SET-AF95E, `LanglandsTunnell/WeightOneLiftQCoeffConverse.lean`, the `exists_repZ_eq` and
  `cusp_ext_of_qCoeff` proofs.
- **(a) a deprecated lemma with no replacement**: `mul_lt_one_of_nonneg_of_lt_one_right` is deprecated
  since 2026-07-28 and *aborts* the elaboration (not merely a warning), so it breaks the silence
  gate. Inline it: `(mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one a)).trans_lt hjt`.
- **(b) an open-namespace shadow**: `simp only [mul_inv_rev, inv_inv]` becomes ambiguous once `Matrix`
  is open (`Matrix.mul_inv_rev` shadows the root lemma); write `_root_.mul_inv_rev`.
- **(c) a changed extensionality**: v4.34's `UpperHalfPlane.eq_of_forall_qCoeff_eq` no longer takes
  the pin's seven periodic/holomorphic/bounded arguments (`HasQCoeff` now carries them); the port's
  `ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods M) h` is the form to use.
- **rule**: for a pin body, a *deprecated* name is not a warning to live with — it aborts. Prefer the
  mathlib replacement, else inline the deprecated lemma's statement-neighbour form, and record it.
- **seen**: 2026-11-20, SET-AF95E.

## FR-0251 [instrument] — a module whose pin-wire line is missing is invisible to every planning read, and the loss can be silent

- **where**: SET-AF95F, the first `write` of `AutomorphicForm/Adelic/WhittakerUnipotent.lean`: the
  header's `spec-pin:` line did not persist (a second `edit` re-adding the identical line did), so
  `check_port` read the file as **tier 3 / "not wired"** and the audit reported nothing to check.
- **why it matters**: the frontier reads "ported" from the wire (`spec-pin:` lines and the checker's
  `SOURCES`), so a module that builds and is correct but unwired does **not** reduce `needed`, does
  not count as a consumer for its dependencies, and can put its own rows back on the ready shelf.
  That is the mirror of MD-001 (a wire naming content the module lacks): here the content is there
  and the wire is missing.
- **the check**: after writing a new module, `grep -c 'spec-pin:'` on it and one `check_port` run —
  a `0 ok, 0 mismatch, 0 missing` summary with a header that visibly carries the line means the
  scanner did not see it.
- **seen**: 2026-11-20, SET-AF95F.

## FR-0252 [instrument] — a row's statement must be emitted from the pin `S_` file's `solution`, not from the `Theorems/` wrapper

- **where**: SET-AF96's scaffold generator (`lean/tmp/af96/gen.py`), first run over the eight row pins.
- **what happened**: the row theorem was emitted from the wrapper `Theorems/Thm_<node>.lean`, which is
  the statement the *reader* wants — but the wrapper unqualifies names (`CuspForm (Gamma1 N) 1` for
  the pin's `CuspForm (CongruenceSubgroup.Gamma1 N) 1`, `𝓞 ℚ` where the pin writes
  `NumberField.RingOfIntegers ℚ`). `check_port` keys a renamed row by *content* (the module's last
  name has no counterpart in the wire, so the name tiers miss) and the unqualified text does not
  hash to the pin's `solution`, so the row read **`MISSING`** — the checker reporting a port
  declaration the wire does not have, which is exactly the shape of a real defect.
- **the cure**: emit the row from the pin's own `solution` text (renaming `solution` to the published
  name) and keep the wrapper only as the source of that name. The statement then hashes to the pin's
  and reads `ok  [pin name …solution]`, which is also the stronger property: the statement is the
  pin's byte-for-byte (FR-0246).
- **rule for the next manager**: the wrapper is the *name* source; the `S_` file's `solution` is the
  *statement* source. A scaffold generator must be run over the eight row pins and must read
  `check_port` before the order is written — `0 ok` on a module whose wire is not empty means the
  scanner is not seeing the wire (FR-0251), and `MISSING` on a row means the statement is not the
  pin's.
- **seen**: 2026-11-20, SET-AF96.

## FR-0253 [instrument] — an attribute written inline at column 0 (`@[simp] theorem …`) is not a declaration start, so a chunk-based scaffold drops the declaration and swallows it into its predecessor

- **where**: SET-AF96's scaffold generator over `Definitions/Def_LanglandsTunnell_ArchPlace.lean`
  (three `@[simp] theorem`s) and `Definitions/Def_RepTheory_GL2CongruenceSubgroup.lean`.
- **symptom**: `pin_split.decl_starts` starts a declaration at a line matching
  `privates/noncomputable? theorem…`, so `@[simp] theorem norm_anglePhase …` is passed over and the
  *previous* chunk extends to the next recognised start — carrying the attribute, the theorem and its
  body inside the previous declaration. The generated module then either drops the declaration (if
  the chunk is trimmed at the attribute) or emits the body un-sorried (an "unsolved goals" error at
  the attribute's line, not at the declaration's).
- **the cure used**: derive the declaration list from `spec/statement_db.py`'s `parse_file` (whose
  offsets already include the attribute lines), and trim a chunk at the first attribute line that is
  *not* its own first line. `statement_db` also gets the `private` flag, the kind and the pin
  statement text, so it is the better source for a generator on all three counts.
- **rule**: a scaffold generator should read `statement_db.parse_file`, not a hand-rolled declaration
  regex; and a chunk must be cut at an attribute line only when the attribute is not the chunk's own.
- **seen**: 2026-11-20, SET-AF96.

## FR-0254 [build] — a bare `import Mathlib` in a new module makes every elaboration cost ~100 s on this box, and poisons everything downstream of it

- **where**: SET-AF96's ten scaffolds, all generated with `import Mathlib` as their first import
  (the pin wrappers `Theorems/Thm_*.lean` all start that way, so the generator copied the habit).
- **the measurement** (order AF96B): the `Mathlib` olean closure is **6.1 GB** against **7 GB** of
  RAM, so it is never page-cached; a file containing only `import Mathlib` takes **101 s / 99 s**
  wall on two back-to-back `lake env lean` runs with **~1 s** of user CPU — pure I/O thrash.
  `import Mathlib.Tactic` alone is 67 s, `Mathlib.Data.Nat.Basic` 15 s. The gate `timeout 100 lake env
  lean` then fails for a reason that has nothing to do with the mathematics, and because the cost is
  transitive, every module that imports the affected scaffold pays it again.
- **the cure**: replace it with the specific modules the file needs — the port's established practice,
  documented in the header of `RepTheory/LocalLanglands/IntegralSubgroup.lean`. Worked measurement:
  `RepTheory/LocalLanglands/IntegralSubgroupCompact.lean` went from >115 s (timeout) to **42 s**
  silent on five narrow imports (`Mathlib.Topology.Algebra.Group.Units`,
  `…Topology.Algebra.Monoid`, `…Topology.Compactness.Compact`, `…Topology.Instances.Matrix`,
  `Mathlib.NumberTheory.Padics.ProperSpace`). Narrowing is statement-neutral, so it is a one-line
  `## Port deltas` entry, not a discussion.
- **rule for a scaffold generator**: emit the pin's *narrow* imports (the `Definitions/Def_*.lean`
  files list them), never `import Mathlib`; and a work order must name this, because otherwise every
  order in the wave meets the same 100 s wall and reports it as a blocker.
- **seen**: 2026-11-20, SET-AF96B.

## FR-0255 [mathlib-drift] — narrowing a scaffold's `import Mathlib` surfaces the deprecations the 100 s wall was hiding

- **where**: SET-AF96D, `LanglandsTunnell/WeightOneLiftFactorizationBound.lean`, after the umbrella
  import was replaced by seven leaf modules (FR-0254).
- **what surfaced**, all in pin body text that the pin replays verbatim:
  `zero_le'` -> `zero_le` (core deprecation 2026-07-21, six sites), `if_pos`/`if_neg` ->
  `ite_eq_left`/`ite_eq_right`, and five `haveI : … := …` -> `have : … := …`
  (`linter.style.haveILetI`; `have` still serves as the instance at every site, verified).
  SET-AF96B separately found `Mathlib.Data.Complex.Basic` itself deprecated at v4.34 — the live path
  is `Mathlib.Basic.Complex.Basic` — so even an *import* can fail the silence gate.
- **why it was invisible**: with `import Mathlib` no run ever finished inside the two-minute cap, so
  the warnings were never printed; the module "looked" silent because nothing was seen. That is the
  general hazard: a wall-clock failure can masquerade as a clean gate.
- **rule**: after narrowing imports, re-run the silence gate *before* believing a pin body replays;
  budget for a deprecation sweep of the pin's body text (`zero_le'`, `if_pos`, `if_neg`, `haveI`), and
  treat a deprecation inside an `import Mathlib.X` line as a statement-neutral import delta.
- **seen**: 2026-11-20, SET-AF96D (and 96B for the import-level one).

## FR-0256 [build] — `flock /tmp/flt-build.lock` serializes nothing in this harness, and a `timeout`-killed `lake build` leaves the target's oleans deleted

- **where**: SET-AF96, all seven orders. Each shell call gets its own sandbox namespace with a per-call
  tmpfs `/tmp`, so `/tmp/flt-build.lock` is a *fresh* file in every call: the `flock` wrapper the build
  discipline prescribes is inert. What actually serializes builds is lake's in-project
  `.lake/build.lock`; what actually caused the wave's races was that.
- **the damage**: two orders lost rounds to it. A `timeout 100 lake build` killed *inside* lake's
  rebuild leaves the tree **worse than before** — lake deletes the target's `.olean`/`.ilean` before
  writing them, so a cancelled build removes an olean that existed, and every module importing it then
  fails with "object file … does not exist" until something rebuilds it. On this wave that stripped
  `GL2CongruenceSubgroup.olean` (and once `ConductorDatum.olean`) repeatedly, blocking two consumer
  orders that were otherwise finished. The mirror image of FR-0033 (a stale olean that hides a
  `sorry`): here an *absent* olean blocks elaboration outright.
- **the cures**: (a) narrow a module's imports (FR-0254) *before* running its first build, so the build
  fits the timeout; (b) run a build of a big target as a background job rather than under a foreground
  `timeout`; (c) if a `lake build` is cancelled, rebuild that one module alone before touching anything
  downstream; (d) do not rely on `flock /tmp/...` for mutual exclusion — use the project's own
  `.lake/build.lock` (lake does), or a lock inside the workspace (e.g. `lean/tmp/.build.lock`), which
  does persist across calls.
- **seen**: 2026-11-20, SET-AF96 (reported independently by orders B, C and G).

## FR-0257 [mathlib-drift] — `AdeleRing` and `InfiniteAdeleRing` are `def`s at v4.34, so a pin `rw` *into* a `Prod.mk`/`Pi.single` fails at `implicit` transparency

- **where**: SET-AF97C, `NumberTheory/StandardAddChar/GlobalAndInfinite.lean`, four sites in
  `psiLocal_rat_eq_psiV` and the two infinite-place rows (pins' `AdelicTraceData.adelicTrace_apply`,
  `psiQ_apply`, `traceInfHom_apply`, `FiniteAdeleRing.algebraMap_apply`, `adeleSingleAt_apply`).
- **the pin**: writes `rw [adelicTrace_apply]` where the goal's argument is a literal `(a, b)` / `Pi.single`
  tuple; at `v4.34` `AdeleRing R K` is a plain `def` (a product) and `InfiniteAdeleRing K` a `Pi` type,
  so the tuple is not *syntactically* of type `AdeleRing …` and the rewrite is rejected with "the
  target expression is not type-correct under the `implicit` transparency level".
- **the cure (body only)**: a term-mode `have h : … := rfl` (or a `show` of the unfolded form), which
  elaborates at the default transparency and does see through the `def`. Do **not** try more `rw`.
- **the class, now four sets running** (FR-0238 `AdeleRing`/`InfiniteAdeleRing`, FR-0245
  `SpecialLinearGroup`, FR-0249 `Nat.Primes`, this one on the same two types at the term level). The
  general rule stands: a pin step that *rewrites through* a `def`-abbreviation needs `set`/`have`/`show`
  rather than `rw`.
- **seen**: 2026-11-20, SET-AF97C (AF97D was warned forward, being the same block).

## FR-0258 [instrument] — `scaffold_audit` credited a pin engine as "satisfied by the import closure" when the imported copy was `private`

- **where**: `tools/deps/scaffold_audit.py`, `closure_names`: it collected the last name of **every**
  declaration in the module's import closure, `private` ones included. SET-AF97G's scaffold read
  "12 pin public declarations, 1 port declaration, **3 satisfied by the import closure**" while those
  three (`coef`, `weight_eq`, `measurable_weight`) exist in `MeasureTheory/HaarQuotient.lean` only as
  `private` — i.e. not importable, so the audit was crediting a copy nothing can see.
- **why it matters**: this is FR-0242's blind spot one level up. FR-0242 says a `private` declaration
  is skipped by the checker, so a module that quietly keeps an engine `private` can look complete by
  having it elsewhere — and the audit, whose whole job is to catch a missing row, agreed.
- **the fix (landed)**: `closure_names` skips declarations with the private/anonymous flag, so a
  "satisfied by the import closure" line now names a *public* declaration. Re-running the fix over
  the already-landed SET-AF96 modules leaves them all `complete`, so nothing that was declared
  complete on the old reading was false — but a future wave could have been.
- **rule**: when a gate reports a *count* (here "N satisfied by the import closure"), read the names
  it credits, not the number; and a tool that answers "is this row on the wire" must ask "is it
  importable", which for Lean means public.
- **seen**: 2026-11-20, SET-AF97G (reported), fix landed the same session.

## FR-0259 [port-structure] — two modules must never declare the same *public* full name, and neither `check_port` nor `dedup --within` can see it

- **where**: SET-AF97. Two cases in one set, both found by a consumer zone rather than by a gate:
  (a) `AutomorphicForm.IsCuspidalFn.add`/`.smul` were declared in `Adelic/ProductionPinsTail.lean`
  (its wire lines 4–5) *and* in the new `Adelic/CuspidalSpace.lean` (same two pins);
  (b) `DihedralWeightOne.slash_eq` was declared in `LanglandsTunnell/WeightOneLiftNebentypus.lean`
  (AF95C) *and* in the new `WeightOneLiftCuspidalRealization.lean` (AF97A), from two different pins
  that both state it publicly.
- **symptom**: importing both fails at *import* time — `environment already contains 'X' from Y` — so
  the two modules can never be used together, and every consumer that wants both is blocked. Each
  module is green on its own wire, and `dedup --within` is within-module by construction, so no gate
  reports anything.
- **the cure used**: (a) the two rows moved to `CuspidalSpace.lean`, `ProductionPinsTail` lost the
  block and its two wires (and the old `spec/AutomorphicFormSetAF92EConsumer` now imports both, which
  is legal once the duplicate is gone); (b) A's copy kept the **pin's own stage namespace**
  (`namespace Ws1.L1`), so the full name is `DihedralWeightOne.Ws1.L1.slash_eq` and the pin's last
  name — which is all the checker and the shelf read — still matches. Keeping the pin's stage
  nesting where the flattening would collide is cheaper than a rename and stays pin-faithful.
- **rule**: before a set lands, `grep` the new public declarations' full names against the tree
  (`grep -rn "^theorem <last>\|^def <last>" FLTForHuman/`); and when a consumer zone will not compile
  on an import, suspect this class before suspecting the consumer.
- **seen**: 2026-11-20, SET-AF97 (E's and A's reports, confirmed by the set's consumer zone).

## FR-0260 [build] — a `rw` list whose last entry instantiates a big term can burn the whole heartbeat budget; split it into `rw` + `exact`

- **where**: SET-AF97D, `LanglandsTunnell/TateLocal/AddCharLevel.lean`, the first row.
- **symptom**: `rw [hz, psiFin_eq_one_of_forall_mem _ (fun w => (traceInt K z w).2)]` took
  **> 4,000,000 heartbeats** (> 100 s wall, no output, "deterministic timeout at whnf/isDefEq" on the
  `rw` line). Replacing it by `rw [hz]` followed by
  `exact psiFin_eq_one_of_forall_mem _ (fun w => …)` elaborated the **whole module in 5.7 s**
  (< 8,000 heartbeats). Same proof, same statement.
- **why**: the rewrite tactic re-elaborates its pattern under the accumulated instance state; a
  combined list with a term argument that elaborates slowly is re-traversed per occurrence, and the
  cost is not additive.
- **rule**: end a proof with `exact`/`refine` rather than appending the closing lemma to a `rw` list,
  and when a pin body stalls at a `rw` with a `(fun …)` argument, split it before touching
  `maxHeartbeats` (which is forbidden by the no-linter/no-option rule anyway).
- **seen**: 2026-11-20, SET-AF97D.

## FR-0261 [port-structure] — a port module's flat namespace can shadow an opened prelude name, and the body then silently proves the wrong thing

- **where**: SET-AF97A, `LanglandsTunnell/WeightOneLiftCuspidalRealization.lean` (and the same class in
  SET-AF95/96 modules that `open LanglandsTunnell.RatArch` from inside `namespace DihedralWeightOne`).
- **the hazard**: `LanglandsTunnell/WeightOneLiftLevel.lean` declares, *inside* `DihedralWeightOne`,
  nine names that are also on the AF93 prelude — `ratArch_mul`, `ratArch_inv`, `ratArchHom_apply`,
  `ratArch_eq_one_of_glArch_eq_one`, `ratArch_globalPoints`, `archPart`, `glFin_archPart`,
  `ratArch_archPart`, `slash_eq_smul_of_hasNebentypus` — and all nine are about
  `LanglandsTunnell.ratArchGL2` (the *delta* lift), not about the pin's `ratArch`. The pin's flat
  search-stage namespaces never meet them; in the port the local name wins over the opened prelude,
  so a body reading `ratArch_mul` silently gets the `ratArchGL2` law.
- **symptom when it bites**: not a type error at the shadowed name, but a `rewrite` failure or a
  mysteriously unprovable goal a few lines later (AF97A spent a build round on it, then cured it with
  full qualification at two sites).
- **rule**: when a module in `DihedralWeightOne` opens a `LanglandsTunnell` prelude namespace, qualify
  every prelude name the module itself also declares; and when a *new* module re-declares a prelude
  engine, check that name against `WeightOneLiftLevel.lean` first. Also relevant to FR-0259: the
  collision that produced this list is why adding an import to A's module changed a proof.
- **seen**: 2026-11-20, SET-AF97A.

## FR-0262 [instrument] — `linter.style.haveILetI`'s cure is wrong for an *inlined* instance: `letI := (productionPinsCompact ℚ).mS` cannot become `let`/`have`

- **where**: SET-AF97A, the two rows of `WeightOneLiftCuspidalRealization.lean`.
- **what happened**: the pin installs the measurable-space instance as
  `letI := (productionPinsCompact ℚ).mS`. The linter asks for `have`/`let`, but neither elaborates:
  the goal's instance is the *inlined* `mS`, so `have : MeasurableSpace (AdeleRing …)` is not
  definitionally equal to it ("synthesized type class instance is not definitionally equal…").
  AF97A kept `letI` with `set_option linter.style.haveILetI false in`, **scoped to exactly those two
  declarations**, with the precedent of `AutomorphicForm/Adelic/Cusp/BoundedGenuineRealization.lean`.
- **rule**: FR-0255's blanket `haveI`/`letI` → `have`/`let` cure holds for a *pin-fresh* instance; it
  does not hold when the instance is an inlined term from another module. Then a **declaration-scoped**
  `set_option` is the honest cure, and the header must say why (house style for narrowed
  suppressions). Do not lift that `set_option` to the file.
- **seen**: 2026-11-20, SET-AF97A.

## FR-0263 [instrument] — `port_advise` reports the wrong home namespace past an `open … in` reset

- **where**: SET-AF97A, the substitute block for the two 1,000-line lift pins.
- **symptom**: it printed `LanglandsTunnell.ArchLift.DetIntegral.*`, `ArchLift.ArchLift.*`,
  `ArchLift.RatArch.*` for declarations whose true homes are `LanglandsTunnell.{weightOneLift_eq,
  _mul_of_mem_U, _globalPoints_mul, _mul_eq, det_coe_SL}`, `LanglandsTunnell.DetIntegral.{mem_U_iff,
  archDetNorm_default_eq}`, and only `weightOneArchLift_*` inside `ArchLift` — because the source's
  `open ArchLift` at `:392` resets the nesting for everything after it, while the tool reads the
  declared namespace of each declaration. It also placed `archDetNorm` under the prelude when it is
  `NumberField.AdelicVolume.archDetNorm`. Cost: three `open`s and two probe rounds.
- **rule**: treat a `port_advise` *namespace* as a hint, not a fact (the same way its substitution
  tier is a hint); when a substitute does not resolve, `#check` the last name rather than trusting the
  printed qualification.
- **seen**: 2026-11-20, SET-AF97A.

## FR-0264 [instrument] — the shelf could not credit a row whose last name is generic *and* whose only wire is an `S_` source, so ported rows came back as `needed`

- **where**: `tools/deps/frontier.py`, the two ported-frontier readings. `AutomorphicForm.IsCuspidalFn.add`
  and `.smul` read `needed` on every DSH read from SET-AF95 through SET-AF97 although the port declared
  both (AF95's `Adelic/ProductionPinsTail.lean`, then `Adelic/CuspidalSpace.lean`), with the pin wired
  and `check_port` reading each `ok`.
- **the mechanism, two halves that must both be present**: (a) the name scan
  (`port_decl_nodes` over `scan_port_decls`) drops a last name shorter than six characters with no
  underscore and no upper-case letter or digit — `add`, `smul`, `mul`, … — because otherwise
  `HahnSeries.HasRamBound.add` would read as ported; (b) the sources reading was built from the
  checker's `SOURCES` list with `include_s=False`, so a *module header's* `spec-pin: P2M/Sol/S_….lean`
  contributed nothing to it. A wired `S_` row with a generic last name therefore fell between the two
  tiers, though the docs of `wired_sources` state that the sources tier exists exactly for the
  hand-over direction. (The three documented exceptions relied on the row also being on a `Thm_`
  `SOURCES` row, which a fresh wire is not.)
- **the fix (landed, then narrowed the same day)**: `Frontier.wired_source_nodes` credits the graph
  nodes of the pin sources a tracked port module's header wires. The first version required the module
  to declare the node and, for a generic last name, a statement-hash match with the pin's `solution`;
  that was withdrawn in favour of the **file-level** rule (FR-0265) — the frontier counts node files,
  never statements, so a refactor that moves, renames or drops declarations cannot put a node back on
  the shelf. The over-broad wires this admits are reported by `--selfcheck` and registered in
  `spec/METADATA-ISSUES.md`.
- **the measurement**: the file-level credit lifts `AutomorphicForm.IsCuspidalFn.add/.smul` off the
  shelf and nothing else that the demand contains (the five extra nodes it admits lie outside the
  D–S cone, FR-0265), so `needed [F terminal]` 419 / 20,846 → **417 / 206,821** and ready rows
  28 / 12,637 → **27 / 12,612**. The ported-node set grows by 7 (2 in the demand, 5 outside it).
- **the rule**: when a `needed = 1` looks suspicious, test *both* tiers — a non-distinctive last name
  is invisible to the name scan, and an `S_`-only wire is invisible to the `Thm_` sources tier; and
  when a landing's row does not leave the shelf, diff the ported-node set with and without the fix
  (two lines of Python) rather than adding the row's lines to `needed` by hand.
- **seen**: 2026-11-20, SET-AF97 (reported at landing; fixed the same session).

## FR-0265 [instrument] — the frontier counts node *files*, not statements: that is the rule, and the `--selfcheck` list is where an over-broad wire is registered

- **where**: `tools/deps/frontier.py` (after FR-0264). Settled with the user on 2026-11-20.
- **the rule, confirmed by reading the code**: `frontier.py` reads (a) `spec/old_check_stmts.py`'s
  `SOURCES`/`PORT_FILES` string lists, (b) each port module's header for `spec-pin:` lines, and
  (c) each port module's *declaration names* (`DECL_RE`) for the last-name scan. It reads **no
  statement** — `grep statement_db frontier.py` is empty. Statement fidelity is `spec/check_port.py`'s
  job and completeness is `tools/deps/scaffold_audit.py`'s; the shelf only counts node files.
- **consequence (the point of the rule)**: a node is ported once a *tracked* module's header wires its
  pin source, whatever that member currently declares. Moving a declaration to another module,
  renaming a helper, splitting a module or deleting a statement therefore cannot put a node back on
  the shelf. Verified directly: a header-only module with **zero** declarations and one `spec-pin:`
  line credits its node.
- **the price, measured**: a wire credits *all* of a pin `S_` file's nodes, including the file's row
  when the module only took that file's engines. Five such over-broad wires exist today
  (`WeierstrassCurve.Affine.ncard_fibSet` from `FibSetFinite.lean`;
  `ModularCurve.isInftySide_cuspInftyBar` from `LaurentGlue.lean`;
  `ModularCurve.JOne.degeneracyPullbackInputs` from `Inputs.lean`;
  `ModularCurve.FullLevel.laurentBaseChange_gamma0_le_fieldBar` from `Laurent.lean`;
  `AlgebraicCurve.Annulus.abv_evalAt_le_max_of_isAttached_both_ends` from `PlaceEvaluation.lean`), and
  **all five lie outside the D–S demand**, so they move no `needed` figure (417 / 206,821 either way).
  `--selfcheck` prints them as "source node not covered by the name scan" — that list, plus
  `spec/METADATA-ISSUES.md` for the registered ones (MD-005), *is* the register for this class.
- **do not** re-introduce a statement read in `frontier.py` to narrow this. If a wire is genuinely
  too broad, the cure is the wire (a module should name the pin sources it transposes — FR-0247), and
  the checker is what proves it.
- **seen**: 2026-11-20, SET-AF97 (FR-0264's hash gate removed the same day it was added).

## FR-0266 [instrument] — `port_advise`'s substitution tier matches a `def` on its *type*, so "already in the port, import it" can be a false positive

- **where**: SET-AF98A, `AutomorphicForm/Adelic/WhittakerSystem.lean`. `port_advise` reported three of
  the pin's `casWords`/`casCoeff`/`casBarCoeff` (`S_…su2String_gl2Complex_whittaker_system_…:174`,
  `:181`, `:184`) as `byte-identical` to port declarations — `LeftCasimirComplex.W10` and
  `LocalIntertwining.ComplexCasimirComm.sgn` — and `port_plan` counted them among 45 *trusted*
  substitutions. The work order then instructed "the whole `casWords`/`casCoeff`/`casBarCoeff`
  dictionary is already there … import those; do not re-declare".
- **why it is false**: `statement_db` stores a `def`'s `stmt` as its **type** (`casCoeff`'s is
  `def casCoeff : Fin 10 → ℂ`), so the hash tier matches *any* port `def` of the same type.
  `LeftCasimirComplex.W10`/`c10`/`c10b` are the **left** Casimir dictionary (`Ld`-based) and `sgn` is
  `![1,1,1,1,-1,-1,1,1,1,1]`; none of them is the pin's right-Casimir `Fin 10` dictionary, and no
  port declaration has those last names at all. `port_plan` itself flags the class ("3 suspect (the
  parser's type-only `def` matches)").
- **cost**: the three deletions would have been `scaffold_audit` `MISSING` rows and a headline that
  does not elaborate (its two Casimir steps are `← archCasimirAtComplex_eq_sum …` and a
  `linear_combination` over `casCoeff`).
- **rule**: for a `def`, the substitution tier is a *type* match, not a statement match — check the
  body before believing it, and never let a work order's "already ported" list decide for a `def`.
  A `def`'s pin-faithfulness is its body, which no checker hashes.
- **seen**: 2026-11-21, SET-AF98A.

## FR-0267 [mathlib-drift] — `Matrix.of` is no longer `fun f => f`, so a pin's `Matrix.of !![…]` needs a `show`, and the `!![…]` literal is already a `Matrix`

- **where**: SET-AF98A, the two `archComplexGLAt_eq_lift_rot`/`…_irot` rows
  (`S_…su2String_gl2Complex_whittaker_system_…:368`, `:384`). The pin's
  `have hmat : (Matrix.of !![…] : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix …) := by rw [hk]; ext i j;
  fin_cases i <;> fin_cases j <;> simp [Complex.ofReal_cos, Complex.ofReal_sin]` leaves
  `of !![…] 0 0 = Complex.cos ↑s` unsolved at v4.34.
- **why**: `Matrix.of_apply` is `∀ (f : m → n → α) (i j), of f i j = f i j`, and the pin passes it a
  term whose type is `Matrix (Fin 2) (Fin 2) ℂ` — a `def`, so `f` will not unify at `implicit`
  transparency and the simp lemma reads *unused*. `unfold Matrix.of` shows this mathlib's `of` is
  `Equiv.refl (Fin 2 → Fin 2 → ℂ)` applied, not the identity, so `rfl` does not close it either. In
  the pin's mathlib `!![a,b;c,d]` was a plain `Fin 2 → Fin 2 → ℂ` and the `of` was needed; here it is
  already a `Matrix` and the `of` is the defect.
- **cure used**: `rw [hk]` then `show (!![…]) = !![…]` at the literal (the `of` is definitionally the
  identity, so the `show` is accepted), then the pin's `ext`/`fin_cases`/`simp` — and the four
  `Matrix.cons_val_*`/`Matrix.head_cons`/`Fin.isValue` arguments the pin lists in `simp only` are then
  unused (`linter.unusedSimpArgs`), while `Matrix.cons_val_zero`/`_succ` are still load-bearing for the
  `linear_combination` two declarations later.
- **rule**: when a pin's matrix literal is `!![…]` under a `Matrix.of` and the goal survives `simp`,
  `show` at the literal; and never trust the pin's `simp only` list to be *all* necessary or *all*
  used after such a change — re-read `linter.unusedSimpArgs` per site.
- **seen**: 2026-11-21, SET-AF98A.

## FR-0268 [port] — `AdeleRing`-as-`def` breaks `rw`/`simp` *globally*, not locally: "not type-correct under the implicit transparency level" is the tell

- **where**: SET-AF98A, the two unipotent-character steps of the real-place rows
  (`S_…diagOne_satisfies_whittaker_ode…:243`, `S_…detOneTorus_eq_zero…:264`), both of the form
  `have this : (((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w * e.symm (ε * x) = …`.
- **symptom**: the pin's `rw [map_one, one_mul]` (or `simp only [one_mul]`) reports *either* "did not
  find an occurrence of the pattern `1 * ?a`" in a goal that visibly contains `1 * (Pi.single …)`,
  *or* "`simp` made no progress" with the note **"the target expression is not type-correct under the
  `implicit` transparency level, which may have triggered the failure"**. That note is the whole
  diagnosis: `((↑1 : AdeleRing …)).1` is a `Prod.fst` on the *unfolded* product, so the goal is
  ill-typed at every transparency below `default` and **every** subsequent `simp`/`rw` on it fails,
  at a site unrelated to the `rw` that introduced it.
- **cure used**: do not rewrite the pin's identity into the goal at all — restate it. Prove
  `ha : ((… : AdeleRing …) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K).1 w = 1` (by
  `rw [Units.val_one]; rfl`) and then `hU : archRealGLAt hw (unipotentGL2 (ε * x)) = unipotentGL2
  (show (AdeleRing …) from ((Pi.single w (e.symm (ε * x)), 0) : … × …))` by `rw [hE, ha, one_mul]`,
  and rewrite with `hU` instead of the pin's `hE`. The rest of the pin's proof then replays verbatim,
  and its `this` step disappears.
- **rule**: when a pin step's argument contains `.1`/`.2` on a type the port spells as a `def`
  (`AdeleRing`, `InfiniteAdeleRing`), do not insert it into the goal — restate it at the unfolded
  type first. `set_option linter.tacticCheckInstances true` is what names the offender.
- **seen**: 2026-11-21, SET-AF98A.

## FR-0269 [instrument] — `scaffold_audit` keys the import-closure credit on the **last name**, so a pin law the port already has under another last name must be restated

- **where**: SET-AF98C, `RankinSelbergShellIndicator.lean`. The pin states two laws twice, once in
  its `RS24` block and once in its `Ws50CH1`/`T2` block: `units_inv_snd_apply` /
  `T2_units_inv_snd_apply` (same statement, same proof) and `centralScalar_comm`-shaped
  `T2_centralScalar_comm` (the port has `AutomorphicForm.centralScalar_mul_comm`, the same law in
  the opposite orientation).
- **what the audit does**: `scaffold_audit.py` compares `promoted_key(name).split('.')[-1]` on both
  sides, and the import-closure credit (`inport`, FR-0258's fix) is a set of last names. So
  `units_inv_snd_apply` is credited by `AutomorphicForm.UnipotentDepth.units_inv_snd_apply` while
  `T2_units_inv_snd_apply` is **not** — the law is public and imported and the row still reads
  `MISSING`. Same for `T2_centralScalar_comm` against `centralScalar_mul_comm`.
- **what it costs, and the decision**: both are one-liners by reuse
  (`T2_centralScalar_comm K z h := (centralScalar_mul_comm z h).symm`, and the `units_inv` one the
  pin's three-line proof). That is cheaper than a `spec/decl_markers.tsv` row and it keeps the
  auditor's `complete` honest, so AF98C transcribed both at the pin's names and said so in the
  report. `port_advise` *does* report the pair — its per-name `how: binder spelling` line — so the
  signal exists; the trap is reading the advise's totals ("33 declarations already in the port")
  instead of its per-name rows.
- **rule for a work order**: "import, do not re-prove" is a statement-level rule; when the *same*
  law is on the wire under two last names, the audit's completeness gate needs both. Budget one
  line per duplicate and name the duplicate in the report rather than treating the advise's
  substitution count as the module's target surface.
- **seen**: 2026-11-21, SET-AF98C.

## FR-0270 [instrument] — a pin `set_option maxHeartbeats` is the generator's budget, not the port's cost; and a one-qualifier statement diff is cured with `open … in`

- **where**: SET-AF98C, `RankinSelbergShellIndicator.lean`, `torus_at_S` — the pin's only
  heartbeated declaration (`S_…:572`, `set_option maxHeartbeats 1600000 in`) and its only
  qualifier-sensitive statement (`finEmbed` bare, because the pin opens `AdelicDock` at the section
  head `:526`).
- **the measurement**: transcribed verbatim with **no** option and no split, `torus_at_S` costs the
  whole module under `100000`; the probe pair is silent at `70000` / fails at `65000`
  (deterministic timeout at `isDefEq`/`whnf` inside it), against the default `200000` and the
  project's own `4000000`. The pin's `1 600 000` is ≈24× the port's real cost — it is what the
  search stage needed, not what the proof needs. Two corollaries worth carrying: (a) do not
  pre-emptively split a 300-line pin proof because its declaration carries a budget — transcribe,
  then probe; (b) `lake env lean` does **not** read the lakefile's `leanOptions`
  (`#eval Lean.getMaxHeartbeats` → `200000000`, i.e. 200000, from `tmp/af98/probe.lean`), while
  `lake build` uses `4000000` — so the edit loop is the *stricter* gate and a green build is not
  evidence that the loop will be green.
- **the qualifier diff**: the port's proof wants the qualified `AdelicDock.finEmbed` (the port's
  `finEmbed` is not unambiguously in scope in this file), and writing it in the statement turns the
  row into `MISMATCH — port: … (AdelicDock.finEmbed …)` vs `pin: … (finEmbed …)`, a one-token
  difference that `alpha_stmt` cannot absorb (it renames binders, not constants). The cure is
  FR-0246's shape with a cheaper instrument: put the pin's own `open AdelicDock in` back in front
  of the declaration, spell the statement bare and keep the proof qualified — no private `abbrev`,
  no `decl_markers.tsv` row, and the statement hashes to the pin's.
- **rule**: a statement `MISMATCH` whose diff is a namespace qualifier is a *scope* defect, not a
  mathematical one; restore the pin's `open … in` on that declaration. And treat a pin
  `set_option maxHeartbeats` as documentation of difficulty, never as a floor to install (the work
  order forbids installing it, and here it was not needed).
- **seen**: 2026-11-21, SET-AF98C.

## FR-0271 [mathlib-drift] — a `set`-abbreviation inside an `ae_eq_refl`/`inter` result is already delta-reduced, so the pin's `rwa [hcap] at h` no longer matches

- **where**: SET-AF98D, `AutomorphicForm/Adelic/BorelFundamentalDomain.lean`, the row's
  `have hScap : (S ∩ Sd) =ᵐ[μG] 𝓕` (pin `S_…bruhatEisenstein.lean:429-431`).
- **the pin**:
  ```
  set Sd := slab F d₁ d₂ with hSd'             -- a local definition
  have hS₀cap : (𝓕 ∪ (D \ Sd)) ∩ Sd = 𝓕 := …
  have h := hSeq.inter (ae_eq_refl Sd)         -- hSeq : S =ᵐ 𝓕 ∪ (D \ slab F d₁ d₂)
  rwa [hS₀cap] at h
  ```
- **what happened at v4.34**: the goal state of the `rwa` shows
  `(S ∩ fun x => Set.Icc d₁ d₂ (ideleNorm F (det x))) =ᵐ … (𝓕 ∪ D \ <slab>) ∩ fun x => …` — the `Sd`
  of `h`'s type has been zeta/delta-reduced to `slab`'s `setOf` body (and, asymmetrically, the
  `𝓕 ∪ D \ ·` half still prints `slab`), while `hS₀cap`'s pattern still carries the `fvar Sd`.
  `rw`'s matcher does not close that gap, so the rewrite reports "Did not find an occurrence of the
  pattern", and re-stating the pattern in the unfolded `setOf` form fails too (the two halves are not
  reduced alike).
- **the cure (body only)**: do not rewrite. State the identity you need as its own `have` and
  compose: `have h2 : ((𝓕 ∪ (D \ Sd)) ∩ Sd : Set _) =ᵐ[μG] 𝓕 := by rw [hS₀cap]` then
  `exact h.trans h2`. The type ascription is checked up to `isDefEq`, which *does* unfold local
  definitions, so `h2` is accepted where the rewrite pattern is not.
- **rule**: a pin step that both `set`-abbreviates a term *and* rewrites with an identity whose two
  sides are the abbreviation and its value is the FR-0238/0245/0249/0257 class at the
  `EventuallyEq` level: replace the rewrite by a composition. Any `… =ᵐ …`/`=ᵐ` goal built by a
  `Filter.EventuallyEq` combinator is a candidate, because those combinators run `isDefEq` and store
  the unfolded form.
- **seen**: 2026-11-21, SET-AF98D.

## FR-0272 [instrument] — a premise declared with a dotted qualified name after `end <engine namespace>` is invisible to a `^theorem <name>` grep, so the "is it ported?" check gives a false negative

- **where**: SET-AF98D, `AutomorphicForm/Adelic/BorelFundamentalDomain.lean`. The pin's
  `obtain ⟨D, hD⟩ := AutomorphicForm.exists_isFundamentalDomain_globalPoints_range F` looked unported:
  `grep -rn 'exists_isFundamentalDomain' FLTForHuman/` returns only the `…_restrict_ideleNorm_det_Icc`
  variant, so the natural conclusion is "prerequisite missing, needs a port".
- **the fact**: the row *is* in the port, at `AutomorphicForm/Adelic/GlobalPointsDomain.lean:193`,
  declared as `theorem AutomorphicForm.exists_isFundamentalDomain_globalPoints_range (F : Type) …`
  — outside the file's `namespace GlobalPointsDomain`, with the namespace spelled into the *name*.
  Every declaration-shaped grep (`^theorem exists…`, `^def exists…`) misses it, and so does
  `grep -n 'theorem <last name>'`.
- **why it matters**: the work order's FR-0259 advice is "grep the new public names against the tree";
  the same grep, read the other way, is how one decides a premise is missing. Both directions fail on
  a dotted declaration, and the failure mode of the second is expensive (a needless port of a 165-line
  pin) — or worse, a second public copy of a name that already exists.
- **the instrument**: `grep -rn '\b<last name>\b' FLTForHuman/ | grep -v '^\S*:.*--'` (any position,
  not declaration-anchored), or ask the dependency graph
  (`port_advise`/`port_plan`'s premise block) rather than the source text. `statement_db.parse_file`
  also sees the full dotted name.
- **rule**: when checking whether a premise is ported, search the *name anywhere*, not the
  declaration line; and when transcribing a pin whose `p2m_open`/`p2m_export` machinery re-homes a
  declaration, expect the port to have kept a dotted name.
- **seen**: 2026-11-21, SET-AF98D.

## FR-0273 [build] — `open scoped` inside a `namespace` ends at `end`, and `linter.style.haveILetI` fires on *every* `letI`/`haveI` in a Prop goal (`MulAction` and `MeasurableSpace` included), so FR-0255's blanket `have` cure does not reach it

- **where**: SET-AF98D, `AutomorphicForm/Adelic/BorelFundamentalDomain.lean`. Two symptoms, one cause
  ("the row is not where the pin put it").
- **(a) the notation loss.** The pin states its row at the root and its engines inside `RS11C9A`, so
  its `open scoped Pointwise ENNReal` at `:37` lapses at `end RS11C9A` and the pin re-issues
  `open scoped Pointwise ENNReal` at `:345`, just before the row. The port keeps the pin's stage
  namespace (FR-0259) and writes the row outside it, but transcribed only the *body* lines — so
  `→ ℝ≥0∞` in the row's proof died with `error: expected token` at the `0`, and the pin's
  `‖·‖ₑ`/`γ • s` were silently unavailable. The tell is an `expected token` whose token is the second
  character of a notation (`ℝ≥` parses because `NNReal` is open, `∞` does not).
- **(b) the linter.** The pin's proof opens with
  `haveI := isHaarMeasure_adelicGLHaar …`, `letI := ratAction F`, `letI := mGL F`,
  `haveI := measurableSMul_rat F`. `linter.style.haveILetI` fires on all four — its rule is "the goal
  is a proposition, so `have`/`let` is preferred", independent of the bound value's type, so even the
  `MulAction` and `MeasurableSpace` binds are flagged. And the suggested cure does not work: `have :=
  mGL F` gives "synthesized type class instance is not definitionally equal to expression inferred by
  typing rules" (FR-0262's class, and the goal *is* stated with the inlined `mGL F`).
- **the cures**: (a) re-issue the pin's `open scoped …` at **module** level whenever the row sits
  outside the pin's engine namespace; (b) `set_option linter.style.haveILetI false in` scoped to the
  one declaration (precedent `RepTheory/TypeReproducer.lean:656`). The option line does not disturb
  the statement: `check_port` still reads the row `ok` and `scaffold_audit` `complete`.
- **rule**: when a port moves a pin's row out of the pin's engine namespace (which FR-0259 often
  forces), it must also move everything the *scope* was providing — the `open scoped` notations and
  the `scoped instance`s. A missing `scoped instance` shows up as `failed to synthesize Countable ↥⊤`
  deep in the proof, not as a scope error; a missing scoped notation shows up as `expected token`.
- **seen**: 2026-11-21, SET-AF98D.

## FR-0274 [port-structure] — two orders pinning the same private prelude declare the same public full names, and no gate reports it

- **where**: SET-AF98, orders A and B. AF98A's `AutomorphicForm/Adelic/WhittakerSystem.lean` and
  AF98B's `AutomorphicForm/Adelic/WhittakerDiagOneBound.lean` both transcribed the pin's `E40DCFN`
  Casimir dictionary and its `E37K` `K`-type block, 15 public full names in all:
  `DCFN.{hasDerivAt_W_string, archDelAt_apply', archDelBarAt_apply', archDerivAtComplex_sub'',
  archDerivAtComplex_archDelAt', archDerivAtComplex_archDelBarAt', casWords, casCoeff, casBarCoeff,
  archCasimirAtComplex_eq_sum, archCasimirBarAtComplex_eq_sum}` and
  `KType.{archComplexGLAt_eq_lift_rot, archComplexGLAt_eq_lift_irot, hK_of_string, final_bound}`.
- **why it happened**: the pins are different files, but each `S_` file copies the whole su(2)-string
  prelude into itself (the pin's own generation habit), so *both* pins legitimately state these 15,
  and each order's brief says "transcribe the pin". Neither order can tell from its own gates that a
  sibling is writing the same names: `check_port` is per module, `scaffold_audit` is a name set,
  `dedup --within` is within-module, and `port_advise` only sees what was in the port *when it ran*.
- **the symptom, if it lands**: `environment already contains 'AutomorphicForm.DCFN.casWords' from
  …` at *import* time, i.e. any consumer that wants both rows (and the set's consumer zone does).
- **the measurement**: 14 of the 15 were byte-identical (`statement_db` `nhash`), the 15th
  (`KType.final_bound`) alpha-equivalent only — one module had renamed the unused binder `hδ → _hδ`
  to silence `linter.unusedVariables`. So the duplication is total, not accidental near-duplication.
- **the cure used** (and the rule): write the prelude **once** in the module that owns it first, and
  import it from the other. B was temporarily made self-contained by moving its copies to
  `AutomorphicForm.DiagOneCasimir` / `…Su2KType`; when A landed green (no `sorry`, olean on disk,
  `lake build` exit 0) B switched to `import …WhittakerSystem` and deleted its 14 copies, keeping only
  the one name A does not have (`Su2KType.whittakerCoefficient_mul_right`, whose statement differs —
  it takes `pins`/`ψ`). Statements do not move either way.
- **the check to run before a set lands** (30 lines, and it should be a gate — `dedup --cross` or a
  `name_collisions.py`): after a module compiles, take its `statement_db.parse_file` **full** names and
  intersect with every other `FLTForHuman/**.lean`'s public full names; report any intersection. B
  ran it and got 0 after the cure.
- **also worth carrying**: an order cannot *verify* a cross-order import while the set is in flight.
  The first `import …WhittakerSystem` failed with `object file … does not exist` because A's rebuild
  had deleted the olean (FR-0256, second sighting). Sequence a set's shared-prelude module first, or
  expect the import to be un-checkable until it lands.
- **seen**: 2026-11-21, SET-AF98 (orders A and B).

## FR-0275 [instrument] — `statement_db.parse_file` rows are 11-tuples, not the 9 the docstring documents, and the "is my pin already ported?" diff is a hash of `r[10]` against `r[4]`

- **where**: SET-AF98B, the first cross-reference pass of its 87-declaration pin against the tree.
- **symptom**: a pass keyed on the documented layout (`(line, end_line, name, last, kind, private,
  stmt, raw, nhash)`) read **0 of 87** declarations as already ported — the opposite of
  `port_advise`'s "854 lines already in the port" claim — and would have caused a full re-derivation
  of 45 declarations that are in the tree byte-for-byte.
- **the actual layout** (11 fields, as `check_port.check_module` unpacks it):
  `(line, end_line, name, last_with_stage_label, short_name, kind, private, anonymous, stmt, raw,
  nhash)`. So `r[4]` is the short name that `scaffold_audit` credits, `r[5]` is the kind, `r[6]` the
  `private` flag, `r[10]` the normalised hash. `r[3]` is *not* the short name (it keeps the pin's
  search-stage namespace: `E40DCFN.eC`).
- **the check worth keeping**: for each pin public row, look for a port public declaration with the
  same `r[4]` whose `r[10]` equals the pin's `r[10]`; `HASH` = byte-identical, `NAMEONLY` = a
  same-named copy with a different statement (a real decision), `NEW` = transcribe. AF98B's pin read
  49 `HASH` / 6 `NAMEONLY` / 32 `NEW`, which is what made the 20-declaration module possible.
- **rule**: read `statement_db.parse_file`'s tuple off `check_port.check_module`, not off its
  docstring; and prefer a hash+short-name join over a bare name grep for "is it already ported".
- **seen**: 2026-11-21, SET-AF98B.

## FR-0276 [process] — `lean/tmp/<set>/` is shared by every order of the set, so an un-suffixed scratch filename silently reads another order's file

- **where**: SET-AF98, `lean/tmp/af98/`. Order B wrote `tmp/af98/axioms.lean` (a `#print axioms`
  probe over its own module) and `tmp/af98/build.log`; another order overwrote both between the write
  and the read.
- **symptom**: the probe printed 16 declarations that are not in B's module (A's
  `whittakerCoefficient_su2String_…`, `TorusOdeAux.*`) and 14 "failures" that were really *missing*
  axioms lines — a plausible-looking gate failure with no defect behind it. Same for `build.log`,
  which showed two interleaved "Build completed successfully" lines from two lake runs.
- **the cure**: suffix every scratch artifact with the order letter (`axioms-AF98B.lean`,
  `build-AF98B.log`, `out-AF98B.txt`). The work order says "write your build logs to
  `lean/tmp/<set>/`", which is right for *discoverability* and wrong for *uniqueness*.
- **rule for a work order**: name the per-order prefix in the same sentence that names the directory.
- **seen**: 2026-11-21, SET-AF98B.

## FR-0277 [instrument] — a pin whose surface is nearly all `private` makes *both* completeness gates vacuous: `scaffold_audit` reads `complete` on the bare `sorry` scaffold

- **where**: SET-AF98E, `LanglandsTunnell/IsotypicCuspSubmodule.lean`, pin
  `S_LanglandsTunnell_exists_mem_finset_inf_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot_of_mem_sup`
  (836 lines). `statement_db.parse_file` over that pin: **47 declarations, 46 of them `private`**, and
  the one public declaration is the pin's `solution` — the very row the scaffold already carries.
- **the measurement**: on the scaffold as dispatched (header prose + one `sorry` headline),
  `check_port --force` reads `1 ok, 0 mismatch, 0 missing` and `scaffold_audit` reads
  `1 pin public declarations on the wire, … complete: every pin public declaration is declared here`
  (`solution` lands in the `FOLDED` branch). Both are *green on a module whose entire content is a
  `sorry`*. After the full transcription they read exactly the same two lines —
  `1 ok` and `complete` — with 46 more declarations of engine in between, i.e. **neither gate moved**
  between "nothing ported" and "everything ported".
- **why**: `check_port` skips a `private` port declaration (FR-0242) and `scaffold_audit` skips a
  `private` pin declaration, and this pin puts the whole engine on the private side. The two tools
  are consistent; what fails is the *reading* — "the audit says `complete`" is being used in the
  set's orders as a completeness gate, and for such a pin it is vacuous.
- **the countermeasure used here**: FR-0242's prescribed substitute — parse both sides with
  `statement_db.parse_file` and diff names, kind, private flag and statement text (and `nhash`).
  Measured for this row: 47/47 names (one rename, `solution` → the row's name), 46/46 private on both
  sides, **0** statement-text differences, 0 `nhash` differences. That diff is the gate; the two
  tools' readings are recorded beside it, not instead of it.
- **rule for a work order**: do not assert the private/public split of a set's pins from one row —
  run `statement_db.parse_file` per pin and state the private count, because the completeness gates'
  *meaning* depends on it. When the pin's public surface is the row itself, the required deliverable
  is the `parse_file` diff plus the substantive gates (elaboration, the proof, `#print axioms`), and
  the report must say so, or a later reader will take `1 ok / complete` as evidence of a transcription
  that never happened.
- **seen**: 2026-11-21, SET-AF98E.

## FR-0278 [build] — two *concurrent* `lake build`s in one tree race on each other's oleans: the second build's rebuild deletes the first's dependency mid-elaboration

- **where**: SET-AF98F, `lean/`: `lake build FLTForHuman.LanglandsTunnell.WeightOneLiftFactorizationBound`
  (job 1) and `lake build FLTForHuman.MeasureTheory.HaarQuotient` (job 2) started a minute apart in
  two background shells.
- **symptom**: job 1 died with three *unrelated* modules failing at their `import` line —
  `WeightOneLiftNebentypus.lean:119`, `WeightOneLiftQCoeff.lean:66`,
  `WeightOneLiftCuspidalRealization.lean:110`, all with
  `failed to open file '.lake/build/lib/lean/FLTForHuman/MeasureTheory/HaarQuotient.olean': No such
  file or directory` — while job 2 reported `Build completed successfully` and the olean existed
  again by the time job 1's log was read. Nothing was wrong with either module.
- **why**: this is FR-0256's mechanism, but the trigger is not a `timeout` kill — lake deletes a
  target's `.olean` *before* rewriting it, and a second lake process reading that target in the
  window sees an absent file. Lake's `.lake/build.lock` serializes *writers*, not readers, so
  `lake build A` and `lake build B` where `B` is in `A`'s import closure still corrupt each other,
  and the failure is attributed to whichever module happened to be elaborating.
- **the cure**: build one module at a time even across *orders*, and when a build reports an import
  whose olean obviously exists, do not debug the sources — re-run that one build alone. The re-run
  here was `4832 jobs` in 10 s with no failures.
- **rule for a work order**: "run big builds as background jobs, one module at a time" must say
  *globally* one at a time — a background job is not serialized by being one order's only job. When
  several agents share a tree, a failed build whose errors are all `failed to open file …olean` is a
  race, not a defect: re-run before reporting.
- **seen**: 2026-11-21, SET-AF98F.

## FR-0279 [instrument] — a work order's "these helpers are public in the pin" can be exactly backwards, and the checker makes the wrong choice fail

- **where**: SET-AF98F, `LanglandsTunnell/TateLocal/AddCharLevel.lean`, the
  `S_LanglandsTunnell_TateLocal_psiLocal_ne_one` pin (74 lines). The order says the pin's three
  helpers (`trace_surjective`, `main_of_dock_of_base`, `main_of_docks`) "are public in the pin", and
  the preamble of the same work order says `statement_db.parse_file` reads **0 private declarations**
  across the set's twelve rows.
- **the measurement**: `S_…psiLocal_ne_one.lean` is the counterexample — parse_file reads
  `priv = 1` on all three helpers and `priv = 0` on the sole `solution` row (4 declarations, 3
  private). Transcribing them *public* would have been a gate failure, not a fidelity gain: the wire
  does not carry them, so `check_port` would have written them into the `own` column (the gate is
  `0 own`), and `scaffold_audit` would still have skipped them on the pin side. `private` gives
  `4 ok, 0 own` and `complete`.
- **why the order got it backwards**: the pin's `-- pin:`-free helpers are written
  `private theorem` inside a search-stage namespace (`SolED33`), which is exactly the shape that the
  set's other pins use for their *public* engines; the prose generalised from those.
- **the cure used**: keep the pin's `private` markers (the order's own rule "keep the pin's
  `private` markers as the pin has them" governs over its per-row description), drop the
  generation-label namespace, and record the deviation in the module header and the report.
- **rule**: a per-row claim about a pin's visibility is a *measurement*; run
  `statement_db.parse_file` on that row's pin before writing the declarations, and prefer the pin's
  own markers when the order's prose and the pin disagree — the gates agree with the pin.
- **seen**: 2026-11-21, SET-AF98F.

## FR-0280 [port-structure] — a pin's two premises can live in modules that import the module the row is ordered into, so "import, do not re-prove" is impossible and the cure is the home module's own `private` engine

- **where**: SET-AF98F, `MeasureTheory/HaarQuotient.lean`, the
  `S_HaarQuotient_lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer` pin.
- **the trap**: the pin's three premises are `HaarQuotient.measurable_density`,
  `HaarQuotient.lintegral_density_mul_eq_one` and
  `HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out`. The first is already in the ordered
  module; the other two *are in the port*, but in `MeasureTheory/HaarQuotientDensity.lean` and
  `MeasureTheory/HaarQuotientFubini.lean`, **both of which `import FLTForHuman.MeasureTheory.HaarQuotient`**.
  Adding either as an import of the row's home is a cycle; a work order that says "its premises are
  already in the port, import them" is unsatisfiable as written, and a `grep` for the names says
  "ported" without saying "upstream of me".
- **the cure**: the row's home module already carries the *same mathematics* on its private side —
  `orb_density H hH μH g` is exactly `∫⁻ x : H, density H μH (↑x * g) ∂μH = 1` and
  `lintegral_eq_lintegral_measure` is the Fubini row with the orbit integral still folded into
  `orb H μH f q.out`. The pin's proof then replays verbatim against those two, with one `show` per
  site to cross the folded/unfolded gap (`orb` is a `def`, so `show` is enough; no new helper and no
  `dedup --within` cluster). Gates: `6 ok / 0 mismatch / 0 missing / 0 own`, `complete`, no new
  import at all.
- **rule**: before ordering a row into module `M`, check each pin premise's `module ≤ M` in the
  import DAG — not merely that its name exists — and when a premise is downstream, look for the same
  law on `M`'s private side before concluding the row needs a new module. Also worth carrying: the
  sibling modules that *do* hold the public copies are the right home for a row whose proof needs
  them, so "the module this row goes into" and "the module its premises are in" can be different and
  the work order should name the upstream one.
- **seen**: 2026-11-21, SET-AF98F.

## FR-0281 [build] — `nohup lake build … &` inside a tool call is silently killed; builds must be `run_in_background` jobs

- **where**: SET-AF99C, two build attempts. `nohup lake build FLTForHuman/... > log 2>&1 &` inside a
  bash tool call returned immediately, and the next call found **no process, no log file and no
  error**: the sandbox runs the command under `bwrap --die-with-parent`, so the backgrounded child is
  killed with its parent at the end of the call.
- **why it matters**: the failure is silent in both directions — no build, no log to read, and nothing
  in the exit status of the call that started it. A worker that then reads `lean/tmp/…/build.log`
  concludes the build passed (or that it never started, and starts another).
- **rule**: a build is a harness **background job** (`run_in_background`), never `nohup`/`setsid`/`&`
  inside a call. The job's own log is the artifact; and builds are serialized **globally**, not per
  order (FR-0278: lake deletes a target's `.olean` before rewriting it, so two concurrent builds
  corrupt each other's imports).
- **related**: FR-0256 (a `timeout`-killed build deletes the target's olean and blocks every importer),
  FR-0278 (concurrent builds), and the workspace rule that `/tmp` is `tmpfs` and does not persist
  across calls — a log written to `/tmp` is gone too.
- **seen**: 2026-11-21, SET-AF99C.

## FR-0282 [instrument] — `scaffold_audit`'s closure credit is a **last-name** match, so on a pin with short overloaded names `complete` is vacuous and points at a *different* declaration

- **where**: SET-AF99A, `AutomorphicForm/Adelic/PeterssonUnfolding.lean`, pin
  `S_AutomorphicForm_peterssonIntegral_mul_bruhatEisenstein_eq_integral_whittakerCoefficient_mul_conj_rationalCentreUnipotentQuotient`
  (671 lines, 20 public declarations). On the **bare scaffold** (header prose + one `sorry` headline)
  `scaffold_audit.py` printed "20 pin public declarations on the wire, 1 port declarations, **4
  satisfied by the import closure**" and — with the 15 `MISSING` rows — that `4` was the only reason
  the module needed any engine at all.
- **the measurement** (the manager's `tmp/af99/credit_probe.py`, which emits `#check @<full name>` for
  every pin public declaration the module does not declare, reading the *type*): two of those four
  credits were false. The pin's `slab` (:70) was credited to **`NumberField.TateGlobal.slab`** — a
  different object, `(v : HeightOneSpectrum (𝓞 F)) → Set (InfiniteAdeleRing F) → Set (AdeleRing (𝓞 F) F)`,
  the finite-place slab of `TateGlobal/FiniteSlab.lean`, which is in scope only because the module
  `open NumberField.TateGlobal`. The pin's `measurableSet_slab` (:73) likewise had no root-level copy.
  The other two (`globalPoints_unipotentGL2`, `continuous_unipotentGL2`) are genuine.
- **the tell, and it is cheap**: the scaffold's *next* helper statement did not elaborate —
  `unipotentGL2_mul_mem_slab_iff` failed with "The argument `F` has type `Type` … but is expected to
  have type `HeightOneSpectrum (𝓞 ?m)`", i.e. `slab` resolved to the finite-place slab. So the
  false credit and the real defect announce themselves in the same elaboration error, one declaration
  after the audit says `complete`.
- **why**: `closure_names(path, depth=4)` collects `r[3].split('.')[-1]` for every public declaration
  in the depth-4 import closure (SET-AF97G's fix stopped it crediting `private` copies — FR-0258 —
  but the *name* match stayed). Short, mathematically overloaded last names (`slab`, `dn`, `μH`, `Γp`,
  `W`, `coef`, `weight`) are exactly the ones a pin's engine is built from, and exactly the ones a
  large tree has several of.
- **rule**: `complete` is a *surface* claim only when the credit is resolved by full name, not by last
  name. Before a module's `complete` is quoted as "the row is ported", run
  `#check @<namespace>.<pin last name>` for every row the audit did not find declared in the module,
  and require it to resolve (and, for a `def`, to be the pin's object — FR-0266). The two readings
  belong side by side: this module's final gates are `18 ok / complete` **plus** "2 not declared, both
  `#check`-resolve".
- **seen**: 2026-11-21, SET-AF99A.

## FR-0283 [port] — a 28-premise unfolding row: `port_advise`'s substitution block pointed at a *sub-namespace* copy, so a faithful statement did not elaborate; the row itself then replayed verbatim

- **where**: SET-AF99A, the Petersson/Rankin–Selberg unfolding row (600 declaration lines, 460-line
  `solution` body, 28 graph premises).
- **what the instruments said**: `port_advise` reported "13 declarations already have this statement in
  the port (≈592 lines not to re-prove)" and `port_plan` "NET NEW MATH LINES 71". Both were right about
  the *mathematics* and wrong about the *surface*: the replacement homes printed for the pin's `RS11C9`
  engine (`-> FLTForHuman/AutomorphicForm/Adelic/BorelFundamentalDomain.lean
  AutomorphicForm.BorelUnfolding.slab`) are subject **sub-namespaces**, so `AutomorphicForm.slab`,
  `AutomorphicForm.indicator_comp_globalPoints_mul`, … did not exist, and the pin's own helper
  statements — which mention `slab` bare — could not be written at all. See FR-0282 for the audit side.
- **what the row actually cost**: 17 helper declarations transcribed (9 of them the `RS11C9` slab
  algebra, 8 the `det`/Borel-membership/`sqrt` lemmas), 2 genuine closure credits, and **the 460-line
  proof transcribed verbatim** — the only body change is the identifier renaming
  (`RS11C9.<name>` → `<name>`, plus two premises the port publishes under subject namespaces:
  `AutomorphicForm.WhittakerUnipotent.integral_mul_conj_unipotent_…`,
  `AutomorphicForm.norm_apply_eq_one_of_isGlobalAddChar`). Zero proof steps were open; a 28-premise
  row is not *a priori* a stall.
- **what made it cheap, in order of value**: (a) `BorelFundamentalDomain` (AF98) supplies the row's
  only heavy premise `exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein`
  *and* is upstream, so one import closes the Borel/Petersson side; (b) the pin's `hSd : {g | …} = slab F d₁ d₂
  := rfl` still closes because `slab` is a `def` with the pin's body — a `def`, not an `abbrev`,
  is what makes the pin's later `simp only [slab, …]`/`rw [hindG]` steps work unchanged; (c) three of
  the pin's premises are published by the port under a *different name shape*
  (`NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar` →
  `AutomorphicForm.norm_apply_eq_one_of_isGlobalAddChar`, `RS11C9.continuous_unipotentGL2` →
  `AutomorphicForm.continuous_unipotentGL2` whose instance is `[ContinuousNeg R]` not
  `[IsTopologicalRing R]`), and each is a one-token edit — the pin's `continuous_unipotentGL2 _`
  passes the type explicitly, so the port's implicit-binder copy needs the `_` dropped.
- **rule**: for a wide row, read the substitution block as a list of *mathematics* already present,
  then `#check` each at the pin's full name before deciding to import; and expect the pin's
  body to be reusable as text if the pin's engine names are declared at the pin's names (which is
  cheaper than adapting 460 lines to sub-namespace qualification).
- **seen**: 2026-11-21, SET-AF99A.

## FR-0284 [build] — FR-0262 is one-directional: `haveI` → `have` *does* work for an inlined instance when the row consumes it only as a class hypothesis

- **where**: SET-AF99A, the row's first eight proof lines; `haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F`
  (no type ascription, the shape FR-0262 says must stay `haveI`), plus seven typed
  `haveI : SecondCountableTopology …`/`SigmaCompactSpace …`/`SigmaFinite …`/`SFinite …`/
  `Countable …`/`IsProbabilityMeasure …` installs.
- **the measurement**: all eight convert to `have`, and `linter.style.haveILetI` goes silent with no
  other change and no scoped `set_option`. The elaboration succeeds because the row never needs the
  instance *definitionally* — it needs `IsHaarMeasure μG`, `SecondCountableTopology …` etc. as
  hypotheses for `Measure.IsHaarMeasure.sigmaFinite`, `sigmaCompactSpace_of_locallyCompact_secondCountable`,
  `MeasureTheory.Measure.restrict` lemmas — and Lean's instance search does use a local `have` binding
  of class type.
- **why FR-0262 does not apply**: FR-0262's failure mode is a goal whose *instance argument* must be
  definitionally equal to the inlined term (`MeasurableSpace`, `MulAction` — FR-0273's list). An
  `IsHaarMeasure`-style property is consumed as a proposition, so proof irrelevance makes the
  inlining irrelevant (the linter says exactly this: "the goal is a proposition").
- **rule**: try `have` first even for an inline `haveI := <term>`; if it elaborates, no scoped
  suppression is needed. Keep the suppression for the `MeasurableSpace`/`MulAction`/`MeasurableConstSMul`
  class of installs, which is the class FR-0262 and FR-0273 actually measured.
- **seen**: 2026-11-21, SET-AF99A.

## FR-0285 [instrument] — a legacy module's bare-basename `-- pin:` markers fight a `spec-pin:` wire, and the frozen row then hides the live verdict

- **where**: SET-AF99E, `EisensteinGeneral/LocalUnr.lean`. The module is in `spec/old_check_stmts.py`'s
  `PORT_FILES`, and its 19 legacy markers name pin files by **bare basename**
  (`-- pin: foo (S_X.lean:12)`). Adding the module's `spec-pin:` wire made `check_port` actually wire
  the module — and it then read `0 ok / 0 mismatch / 19 missing`, because a bare basename is not a
  pin-relative path (`UNKNOWN PIN FILE` × 6): every pre-existing declaration reads MISSING.
- **cure**: give the markers the full pin rel path (`P2M/Sol/S_….lean`, `Theorems/Thm_….lean`) — 19
  comment-line edits, wire only, zero statement change — and then **retire the `PORT_FILES` row**
  (SOURCES untouched): the module now has a live wire that checks all 19 public declarations, so the
  frozen row is redundant and is what prints the `MISSING IN FLT` line for a wrapper it was never told
  about (`pin_markers` keys by the written name, and the frozen loop looks up by last name, so a
  fully qualified marker is unreachable from it).
- **rule**: migrating a legacy module is the same three-step in this column — wire with full pin paths
  (never bare basenames), retire the `PORT_FILES` row, keep the markers as wire-only comments — and the
  tell that it is needed is a frozen-only line that names a wrapper the live checker already proves.
  Do not add an entry to `SOURCES` to placate the frozen checker; it is being retired.
- **seen**: 2026-11-21, SET-AF99E.

## FR-0286 [instrument] — `lean_parser.ENCLOSE_RE` lets `\s` cross newlines, so a bare `end` swallows the next opener

- **where**: `spec/lean_parser.py`, `ENCLOSE_RE`: an `end`'s optional name is spelled `\s+[\w.']+`, and
  `\s` matches a newline. So `end`⏎⏎`end Foo` reads the second `end Foo` as the first one's *name* —
  one pop instead of two, `Foo` stays open — and `end`⏎⏎`namespace Foo` reads `endname = "namespace"`,
  eats the opener, and never pushes `Foo`: every later declaration in that file gets the wrong namespace.
- **found by**: SET-AF99F, whose first draft produced `ModularForm.LevelOneBasis.exists_polynomial_aeval_…`
  — a name that does not exist — while `check_port` stayed green (it is hash-driven, so the drift is
  invisible to it).
- **blast radius (measured, `lean/FLTForHuman`)**: **780 bare-`end` sites in 141 files**, **285** of them
  swallowing a `namespace`/`section`/`mutual` opener. So `statement_db`'s full names are unreliable
  after such a site, and any check that keys on full names — FR-0274's collision intersection, the
  corpus's `name` column, `scaffold_audit`'s promoted key — inherits the error. Statement **hashes** are
  unaffected (they are parsed from the signature, not the name), which is why the fidelity gate held.
- **cure (one character)**: `[ \t]+` instead of `\s+` in `ENCLOSE_RE`, then bump the corpus stamp
  (`spec/statement_db.py build`) and re-check (`check_port --all`) — a checker round, not a set's.
- **workaround until then**: a collision check must use an independent namespace-aware scanner that
  honours `end X` (SET-AF99F ran one: 43 last names × the whole tree → 0 collisions, the only
  `ModularForm.` hit being `ModularForm.HeckeFricke.main`, a different full name).
- **seen**: 2026-11-21, SET-AF99F.

## FR-0287 [build] — narrowing a pin written against `import Mathlib`: at v4.34 the *re-export chain* decides the list, so the minimum is far below the declaring-module set (3 modules from 19 pin-free imports)

- **where**: SET-AF99G, the three new `MeasureTheory` modules. The nine `S_` pins list `import Mathlib`
  and nothing else (FR-0254), so the whole list had to be measured, not recalled.
- **what was measured** (a greedy single-pass minimizer over `lake env lean -DautoImplicit=false`, one
  run per candidate import, ~6 s each — `lean/tmp/af99/narrow-AF99G.py`): the first-draft lists
  (10 / 19 / 7 imports, each entry the `rg`-found *declaring* module of one name the statement uses)
  minimized to **2 / 3 / 4**. Dropped as redundant: `MeasureTheory.Integral.Lebesgue.Add`,
  `Topology.Instances.ENNReal.Lemmas`, `Integral.MeanInequalities`, `Measure.Prod`,
  `Integral.Bochner.Basic`, `Order.LiminfLimsup`, `Basic.ENNReal.Inv` (11 pin imports for one module),
  `Measure.Haar.Basic`, `Group.Measure`, `Group.Integral`, `Measure.GiryMonad`, `Measure.Regular`,
  `Measure.Typeclasses.Probability`, `PiSystem`, `Integral.Lebesgue.Basic`, `Integral.Bochner.Set`,
  `Topology.Algebra.OpenSubgroup`, `Topology.Algebra.Group.Quotient`, and both
  `Topology.Algebra.Group.{Basic,Neighborhood}`.
- **why**: mathlib at v4.34 carries `module` + `public import` headers, and a re-export chain is
  transitive through `public import` only. Two measurements pin it down. `Mathlib.Analysis.Complex.Liouville`
  alone gives `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (a lemma declared in a module Liouville
  never names) because Liouville `public import`s `CauchyIntegral` → `ParametricIntervalIntegral` →
  `ParametricIntegral`; and `Mathlib.MeasureTheory.Measure.Haar.Unique` alone gives
  `Measure.haarMeasure`/`haarMeasure_self`, declared in `Haar/Basic`, for the same reason. Conversely a
  *dropped* import's absence is only visible as a cascade (`unknown identifier DifferentiableOn` when
  both `Liouville` and `ParametricIntegral` were gone, although either one alone suffices).
- **rule for a narrowing order**: (a) the draft list should be declaring modules, one `rg` per name —
  that is what a reader needs; (b) the *gate* list is the measured minimum; (c) when the two differ,
  keep the declaring module and say so, because "it compiles without it" is not "it is not needed"
  under a re-export chain; (d) `rg -n "^public import|^import" <candidate>` is the five-second way to
  see whether a candidate is a re-export hub. Do **not** infer from one failed trial that a module lacks
  a lemma — drop the candidates one at a time (the greedy pass does) or the cascade misleads.
- **seen**: 2026-11-21, SET-AF99G.

## FR-0288 [instrument] — `scaffold_audit` credits a folded pin `main` and `port_omissions` calls it MISSING: two completeness gates disagree on the `main`/`solution` shape

- **where**: SET-AF99G, `MeasureTheory/MoebiusIntegral.lean`. Each of the two pins states the row twice:
  `ARCHA3C.main` (the proof) and `solution` (`exact ARCHA3C.main …`), and the two statements differ in
  **one unused binder name** — `main`'s `(hdet : a * d - b * c ≠ 0)` against `solution`'s `(_hdet : …)`.
- **the measurement**: with the row's proof written directly at the row (the fold), `scaffold_audit`
  read `complete` — but only because it has a *statement-equality* tier: when the two statements are
  byte-identical it prints `RENAMED? main (same statement, different last name)`, which is what
  `ParametricIntegral`'s `RS11IC.main` gets. Where the binder is spelled `_hdet` vs `hdet` the tier does
  not fire and the same fold reads **`MISSING main`, `incomplete`**. `port_omissions.py` has no such
  tier at all: it read `1 MISSING` for `ParametricIntegral` and `2 MISSING` for `MoebiusIntegral` on the
  same folded modules that `check_port` and `scaffold_audit` both passed.
- **cure used**: keep the pin's two declarations — `Engine.main` (the pin's `hdet`, holding the proof)
  plus the row (the pin's `_hdet`) as `exact Engine.main a b c d _hdet G`, in the subject namespaces
  `MeasureTheory.MoebiusComplex` / `MeasureTheory.MoebiusReal` / `MeasureTheory.ParametricIntegral`.
  Both gates then read green (`8 ok`, `complete`, `0 MISSING`), and `dedup --within` reports exactly the
  pin's own pairs (one per row: `main` and the row, same statement), which the work order allows with
  the reason.
- **rule**: an order whose pin has the `main` + `solution` shape must keep both declarations public; a
  fold is invisible to `port_omissions` and *sometimes* invisible to `scaffold_audit`, so "complete"
  alone is not evidence. And an unused binder spelled `_hdet` in one copy of a statement and `hdet` in
  the other is enough to drop a whole credit tier — read `scaffold_audit`'s `RENAMED?` lines, they are
  the ones that say *which* statement was matched.
- **seen**: 2026-11-21, SET-AF99G.

## FR-0289 [mathlib-drift] — a dot-notation error names the *elaborated head* of the receiver, not the lemma you wrote

- **where**: SET-AF99G, both Möbius rows: the pin's `h1.div h2 hz` on `HasDerivAt` proofs.
- **symptom**: `error(lean.invalidField): Invalid field `div`: The environment does not contain
  `HasFDerivAtFilter.div`, so it is not possible to project the field `div` from an expression h1 of
  type HasFDerivAtFilter (fun y => b + y * d) (ContinuousLinearMap.toSpanSingleton ℂ d) (nhds z ×ˢ pure z)`.
  There is no lemma named `HasFDerivAtFilter.div` in mathlib at any version, and `rg` for it finds
  nothing — the missing declaration is `HasDerivAt.div` (`Analysis/Calculus/Deriv/Inv.lean:173`), and
  the error prints the receiver's *unfolded* type head because dot notation resolves the field name
  against that type once `HasDerivAt.div` is absent from the environment.
- **cure**: `rg -n "^(theorem|lemma) <Receiver>\.<field>" Mathlib` on the spelling you wrote (here
  `HasDerivAt.div`), then `import` its module (`Mathlib.Analysis.Calculus.Deriv.Inv`). The same session
  lost a round to the mirror case in FR-0287's cascade, both being "the error names something that is
  not the missing lemma".
- **seen**: 2026-11-21, SET-AF99G.
