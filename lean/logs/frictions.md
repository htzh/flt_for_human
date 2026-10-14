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
