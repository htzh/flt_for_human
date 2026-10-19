# `lean/play/` — the playback bench

**Status:** open. Ground rules fixed 2026-10-14; the workflow below is v0 and
grows as we use it. The sheets are tracked and also rendered by the browser
reader under [`play/`](../../play/) — serve it statically and open
`play/index.html`.

The porting push is over for a large segment of FLT. This directory is where we
read it back. The mode is different from everything else under `lean/`: it is
**interactive and question-driven**, the unit of work is a **subject you name**,
and the artifact is a **worksheet you open in the editor** — not a library
module, not a note for publication.

```
you:  "the card n-torsion theorem"
me:   writes lean/play/CardNTorsion.lean, checks it, hands it over
you:  open it in VS Code, ask questions about what you see
me:   answers by editing the file (prose, `#check`s, live `example`s)
```

## 1. Ground rules

**R1 — Responsiveness is the first principle.** Everything else gives way to it.
A worksheet that takes a minute to open is a worksheet nobody asks questions
about. Concretely, in `play/`:

- **Never `import Mathlib`**, and never open an umbrella namespace. Import the
  *narrowest* port module that contains the subject — no more. Measured on this
  machine with `lake env lean` and oleans already built:

  | import | cost |
  |---|---|
  | `FLTForHuman.Elliptic.TorsionCard` | ~3 s warm, ~18 s first touch |
  | `FLTForHuman.Elliptic.Omega` (the EDS cone) | ~2.7 s warm |
  | `FLTForHuman.Elliptic.TorsionZMod` | ~5.5 s warm |
  | `Mathlib` (the umbrella, bare) | ~75 s |

  The last row is why the rule exists: the umbrella costs over a minute of olean
  loading before a single line elaborates, where a narrow port module costs
  seconds. Auditing a port module's import list is therefore part of making a
  subject playable.
- **We do not do tree rebuilds.** Nothing here recompiles mathlib or the port.
  The first touch of a module — and the first touch after any source change —
  pays its elaboration once; every later open is warm. Report both numbers, but
  treat warm as the loop's real cost, and read a slow first touch as a signal
  that a dependency's import list moved.
- One import per worksheet, as a rule. A second import is a cost to justify.
- If a subject genuinely needs a heavy cone, say so *before* writing the file.

**R2 — One subject, one file.** You name a subject in any wording; I pick a
Lean-legal slug and write `play/<Slug>.lean`. The subject→file mapping is the
index in §4; it is the only registry.

**R3 — A worksheet must compile.** Hand-off is only after
`lake env lean play/<Slug>.lean` reports **0 errors**. If a zone cannot be made
to compile today, it ships commented out *with the reason*, or not at all. A
worksheet that lies is worse than no worksheet.

**R4 — Written to be opened, not read.** Zones with headings, `#check` for every
name it talks about, live `example`s for every claim it makes, and the questions
answered in place. Your editor's infoview is the medium.

**R5 — Playback, not new mathematics.** A worksheet restates, unfolds and
explains what is already ported. It does not prove new theorems and is not a
verification artifact; anything genuinely new goes into `FLTForHuman/` through
[the porting playbook](../porting-playbook.md).

**R6 — Provenance in the header.** Every worksheet names its subject, the port
module it reads, and the pinned FLT source (`aa2d8b3`, per AGENTS.md), so a later
reader can trace a claim without opening anything else.

**R7 — Tracked, and pointing the right way.** Worksheets are tracked and
published. Nothing globs `lean/play/` — it is not a library and `lake build`
never touches it — but the files themselves are part of the repository, so
they must obey the repository's citation rules: cite public URLs (the pin,
mathlib, or a tracked file), never an untracked local path. The generated
browser view lives in `play/` and is part of the tracked app; the generator is a
local-only tool. A tracked worksheet may point at `play/`, not at the generator.
To publish distilled prose, still promote it
into a tracked note (`math/`, `topics/`, `logs/`) and re-cite it with public
URLs; the worksheet remains the working artifact.

**R8 — Math rendering depends on the reader.** Worksheets are read in the
editor, so plain Unicode (`#E[n] = n²`, `→`, `ℤ`) is fine and preferred. Text
that gets promoted into tracked Markdown must then obey the AGENTS.md
GitHub-math rules.

## 2. Workflow

v0, to be revised as we go. The loop is: **name → write → open → ask → edit.**

1. **Name.** You give a subject, usually a theorem or a definition from the
   port. No format required.
2. **Write.** I create `play/<Slug>.lean` in the shape of §3, run the check, and
   report the cost and the status.
3. **Open.** You open it in the editor. This is where the actual work happens.
4. **Ask.** You ask anything about what you see: "why is `(n : K) ≠ 0` there?",
   "what does `ΨSq` have to do with torsion?".
5. **Edit.** I answer by *editing the file*, not by writing an essay in chat:
   a new `example`, an extra `#check`, a paragraph in the right zone, a `-- ⇐`
   marker next to the line you asked about. The question and a one-line answer
   land in the worksheet's question log (Zone Q).
6. **Promote or retire.** When a subject is understood, the distilled prose is
   promoted to a tracked note (usually a `math/` note) with public URLs, the
   worksheet's status becomes `promoted`, and the index (§4) records where it
   went.

Practicalities:

- Open the **`lean/`** directory as the editor workspace, so Lake resolves the
  toolchain and mathlib; then open the worksheet. The `#check`s report in the
  infoview. A worksheet lives outside every `lean_lib` glob, so `lake build`
  never touches it — only the editor or the explicit `lake env lean` command
  does.
- The check in step 2 is the only build cost in the loop, and it is small by
  construction (R1): the current worksheet re-checks in ~3 s.

Conventions that keep the loop cheap:

- The file's header carries `status: open | answered | promoted` and the exact
  check command; see §3.
- Questions are logged oldest-first with the date, so the file itself is a
  record of the session.
- Prefer editing the existing zone over appending a new one; when a subject
  outgrows its file, that is the signal to split it into two subjects.
- Chat answers stay short: they point at the file.

## 3. The shape of a worksheet

```
header comment   subject · intro · source module · pinned FLT URL · check
                 command · status · date · zone list
imports          one narrow port module (R1)
Zone A           the statement, unpacked
Zone B           the mechanism — why the proof works, not what it calls
Zone C           the assembly — how the pieces combine
Zone D           the engine — the parts worth reading line by line
Zone E           things to poke at — concrete edits to try, with what to expect
Question log     oldest-first: date, question, one-line answer
```

The `Intro` label is the public summary: it is shown at the top of the worksheet
page and on the index. `Check`, `Status` and `Date` are build metadata and stay
inside the page's collapsed “source & build” details, not at the headline. Prose
outside `Intro` is editor-facing context (workflow, import timing, provenance)
and is not promoted to the public headline.

Zones A–E are a default, not a law: a definitional subject may need only two.
What matters is that every `#check` in the file names something real and every
`example` compiles.

## 4. Index

| subject | worksheet | reads | status |
|---|---|---|---|
| the card `n`-torsion theorem (`#E[n] = n²`) | [`CardNTorsion.lean`](CardNTorsion.lean) | `FLTForHuman/Elliptic/TorsionCard.lean` | open |
| the division polynomials (`ψ`, `Ψ`, `ΨSq`, `Φ`, `φ`) and the EDS layer | [`DivisionPolynomials.lean`](DivisionPolynomials.lean) | `FLTForHuman/Elliptic/Omega.lean` | open |

## 5. Open questions

Things not settled yet; they get settled by using the bench, not by guessing.

- Is one file per subject enough, or do subjects want a companion `.md` here as
  well? (Default: no — prose goes in the worksheet until it is promoted.)
- Do answers get mirrored into a tracked note immediately, or only on
  promotion? (Default: only on promotion, to keep R1 honest.)
- Do we pre-check on every edit, or only on hand-off? (Default: every hand-off,
  which is the expensive moment; mid-session edits are checked when they change
  a proof term.)
- Does `lean/README.md` want a line about this bench? It can now point at
  `lean/play/` (the sheets are tracked); a short line is enough.
