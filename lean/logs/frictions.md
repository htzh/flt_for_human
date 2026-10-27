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
