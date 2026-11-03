# Semi-formal presentations of Lean proofs

**Status.** v0, initial model. One instance is worked out end to end: the
function-field generation capstone. The format is expected to move as the next
subjects are presented.

## 1. Why

The port is correct, but a Lean proof body is a poor *document*. A reader who
wants the mathematics has to reconstruct it from tactics, instance arguments and
`Eq.mpr` chains, and much of what the compiler needs — `NeZero`, `letI`,
`aeval` versus `eval₂`, private helper lemmas — carries no mathematical content
at all. The opposite failure is just as bad: a prose note that says "one checks"
is not checkable and cannot be turned back into a proof.

A *presentation* is the middle. Every definition and every statement stays in
Lean, so its type can still be inspected with `#check` and `#print`. Only the
**proof body** is replaced by a semi-formal argument in mathematical vocabulary:

1. restate, mathematically, what is to be proved;
2. unpack each hypothesis: what it gives us;
3. state each intermediate goal as a claim, and say **how each premise is met**,
   citing either an earlier goal or a proven theorem;
4. finish with the conclusion and, where useful, hints for regenerating the Lean
   proof.

The document is encoded in **JSON**, not written directly as a Lean worksheet.
The JSON is the source of truth; a Lean sheet is generated from it. That buys
three things: the narrative can be diffed and reviewed without opening Lean; the
same document can be rendered for the editor, for a browser, or fed to an LLM;
and the Lean statements are pinned by name, so the compiler keeps us honest
about them even though it never sees the proof.

## 2. A presentation is JSON

The machine-readable contract is [`schema.json`](schema.json). A presentation
has four content layers.

| layer | what it holds |
|---|---|
| `definitions` | the objects of the theory: Lean name, source, and a mathematical gloss |
| `premises` | every statement cited by a proof, with its Lean type and a gloss |
| `declarations` | the theorems of the module: statement, restatement, hypotheses, and a semi-formal proof |
| `sections` | the document order: zones, prose, and the members shown in each |

`conventions` is a shared glossary (`F_N`, `F_N^full`, `ψ(N)`, integrality, …) so
that the same notation means the same thing in every proof.

A declaration's `lean` field is the statement verbatim, with the proof body
removed. A definition's `lean` field is the source for reading: long sections of
binder variables may be inlined and the body kept short. In both cases the
compiler output in the generated sheet (`#check`, `#print`) is the authority;
the JSON never replaces it.

A proof is a list of steps. Each step has a `claim`, and optionally:

```json
{
  "id": "s2",
  "kind": "claim",
  "claim": "Gen N: F_N = F_N^full.",
  "math": "The two-generator field is already the full divisor field at level N.",
  "why": "Specialize Hall N at d = N and take the second component.",
  "cites": [
    {"kind": "step", "ref": "s1"}
  ],
  "requires": [
    {"what": "N ∣ N", "met_by": {"kind": "trivial", "ref": "dvd_rfl"}}
  ]
}
```

`cites` says what the claim rests on; `requires` says how each condition of the
cited statement is met. The `kind` vocabulary is deliberately small and
mathematical:

| kind | meaning |
|---|---|
| `claim` | an intermediate goal |
| `reduce` | a reduction: it is enough to prove something else |
| `construct` | introduce an object with its defining property |
| `calculate` | a computation |
| `unpack` | translate a hypothesis into mathematics |
| `close` | the step that finishes the proof |
| `goal` | a restatement of the goal, when it is useful early |

A citation (`cites` / `met_by`) is one of:

| `kind` | `ref` points at |
|---|---|
| `hypothesis` | a hypothesis of the theorem (an id from `declaration.hypotheses`) |
| `premise` | a proven theorem or mathlib lemma (an id in `premises`) |
| `step` | an earlier step of the same proof |
| `definition` | a definition of the presentation |
| `declaration` | another declaration of the same presentation |
| `trivial` / `computation` | a definitional or arithmetic fact (free-text `ref`) |
| `goal` | the goal itself |

Every reference is resolved by the renderer. A typo is an error, not a silently
inert label.

## 3. From JSON to a Lean worksheet

```bash
python3 presentation/render.py presentation/function-field-generation/capstone.json
```

This validates the JSON (against the schema when `jsonschema` is installed, and
against the cross-reference rules in all cases) and writes the sheet named by
`worksheet.output`. For the capstone:

```bash
cd lean && lake env lean presentation/FunctionFieldGenerationCapstone.lean
```

The generated sheet is a Lean file whose only executable content is `import`,
the `open`s, and one `#print` or `#check` per definition and statement. The
narrative lives in comments. Concretely:

- a **definition** is exhibited with `#print`, so the editor shows its type and
  body;
- a **theorem** is exhibited with `#print` when the presentation asks for the
  proof term (the one-liners are worth seeing) and with `#check` otherwise;
- a **private** declaration cannot be named from another module, so its
  statement is exhibited as a closed Lean proposition,
  `#check (fun … => (… : Prop))`;
- every **cited premise** is `#check`ed in the reference zone, so the sheet is
  self-contained even though it does not repeat the proof;
- every **site of citation to a proven theorem or to a definition** carries the
  full Lean name as a code span, so the Play reader resolves it to a card and
  opens that card in the side panel: the statement is one click away where it
  is used, without leaving the sheet. Hypotheses and earlier steps are not
  cards and stay plain. The reference zone at the end remains the full index.

Because the sheet contains no proofs, it cannot be `sorry`-ridden, and it
compiles against the module in seconds once the module's oleans are warm. It is
not library code: no Lake glob includes `lean/presentation/`. The renderer emits
prose at column 0 (only the header metadata is indented by two) so the Play
reader's Markdown parser sees paragraphs, bullets and code spans rather than an
indented code block; that is what makes the citation links live.

The generated header and zones are already in the shape the `lean/play/` reader
uses. The local Play build (see [`lean/play/README.md`](../lean/play/README.md))
reads both `lean/play/*.lean` (hand-written, tracked) and
`lean/presentation/*.lean` (generated, ignored), so
the same JSON drives the browser reader without copying the sheet into
`lean/play/`. Generated worksheets are **not** git-tracked; the JSON is. The
default output stays under `lean/presentation/` to keep generated and
hand-written sheets apart.

## 4. What the sheet does *not* do

It does not certify the proof narrative. Lean checks the statements and the
names; the mathematics is the presentation's claim. That is the intended split:
the narrative is the thing to read and to regenerate from, and the compiler
checks the objects it talks about, not the argument.

It also does not replace the port. A change to the mathematics goes into
`lean/FLTForHuman/` first; the presentation follows. The JSON is not a second
source of truth for the statements — `#check` is.

## 5. Regeneration contract (for a human or an LLM)

A declaration carries everything needed to write the proof again:

1. the exact Lean statement, verbatim from the module (`lean`), and the
   compiler's own view of it (`#check` in the sheet);
2. the hypotheses, with what each one means mathematically;
3. the list of proven theorems the argument uses, each with its Lean name, its
   type, and a gloss;
4. the steps, in order, with the claim and the reason;
5. `regeneration`: hints for the Lean-specific choices (which rewrite goes in
   which direction, which packaged lemma the source calls);
6. `formal_notes`: the detours that must be reproduced but carry no
   mathematics.

A regenerating reader should be able to write the proof by following the steps
and applying the cited theorems in order. The one thing the presentation does
*not* state is the tactic script, deliberately: the same steps may be realized
by different Lean proofs.

## 6. The initial instance

[`function-field-generation/capstone.json`](function-field-generation/capstone.json)
presents `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean`,
the unconditional capstone of the function-field-generation segment:

- `hall_all` is the private strong induction over the divisor lattice; it calls
  the seven significant statements of T15–T19 directly, with no `Inputs` bundle;
- `functionFieldGeneration` is the target statement, and the three corollaries
  are the field equality, the degree of the modular equation, and the relative
  degree of the full field.

The interface tail (`exists_monic_evalAtJ_jqN_eq_zero`,
`exists_phiIrreducible_of_finrank_eq`, `exists_phiIrreducible`,
`nonempty_modularPolynomialData`) is not part of this sheet: it lives in
`ModularPolynomialExistence.lean` and is checked there.

The mathematics is written up at length in
[`math/010-function-field-generation.md`](../../math/010-function-field-generation.md);
the JSON is the proof-shaped projection of it, with every statement anchored to
the port's Lean names. The FLT provenance is pinned at
`anthropics/fermats-last-theorem@aa2d8b3`; for example the theorem wrapper is
[`Theorems/Thm_ModularCurve_functionFieldGeneration.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_functionFieldGeneration.lean)
and the strong induction is
[`P2M/Sol/S_ModularCurve_functionFieldGeneration.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_functionFieldGeneration.lean#L614-L700).

What the instance taught, and is now part of the format:

- **Private helpers need a second representation.** Three of the capstone's
  lemmas are `private`; their names cannot cross a module boundary. They are
  presented with `private: true` and a `lean_goal`, a closed proposition that
  the sheet can `#check`. This is a general pattern for any `private` step.
- **`#print` is worth choosing, not defaulting.** A structure with seven large
  fields is unreadable as a `#print`; its field statements are better exhibited
  one by one through the theorems that discharge them. Conversely, a one-line
  proof term is worth `#print`ing.
- **Orientation is a real proof obligation.** Several equalities are used in
  both directions (`Gen` is $`F_N = F_N^{\text{full}}`$, the collapse is
  $`F_N^{\text{full}} = F_N`$). The presentation records the direction of each
  rewrite in `regeneration`, because that is where a regenerated proof fails.
- **`NeZero` is plumbing, not mathematics.** It is stated once in the
  conventions and then treated as an instance in the proofs. Presentations
  should not spend a step on it unless it changes a statement.

## 7. Validation

`render.py` enforces:

- the JSON validates against `schema.json`;
- ids are unique in each layer;
- every `cites` and every `met_by` resolves (hypothesis, premise, step,
  definition, or declaration, as appropriate);
- a `cites` to a step points at an *earlier* step; a `requires` may point at a
  later one, since a case split is stated before its cases are discharged;
- every premise is cited by at least one proof (a dead reference is an error);
- every definition and declaration is reachable from a section;
- a `private` declaration has a `lean_goal`;
- no narrative contains a Lean comment delimiter (`/-` or `-/`), which would
  break the generated file.

Provenance follows the repository rules: port files are cited by tracked path,
FLT statements by the pinned commit sha (`aa2d8b3`), and mathlib lemmas by a
public URL at the pinned mathlib revision (`5ed2965`). No citation points at a
file under `lean/.lake/` or another untracked location.

The generated sheet itself must compile; that is the final check and the only
one that touches Lean:

```bash
cd lean && lake env lean presentation/FunctionFieldGenerationCapstone.lean
```

## 8. Files and commands

```
presentation/
  README.md                                  this file
  schema.json                                the JSON Schema
  render.py                                  validator + renderer
  function-field-generation/
    capstone.json                            the initial instance
lean/presentation/                           generated, git-ignored
  FunctionFieldGenerationCapstone.lean       generated sheet
```

```bash
python3 presentation/render.py <presentation.json>          # validate + write
python3 presentation/render.py --check-only <presentation.json>
python3 presentation/render.py --stdout <presentation.json> # inspect
cd lean && lake env lean presentation/<Sheet>.lean          # compile
```

The generated sheet is a build artifact of the JSON and is git-ignored. Edit the
JSON, then regenerate; an edit to the sheet will be overwritten.

## 9. Open questions

- Does a presentation want a companion rendered view for the browser reader
  (`play/`), or is the editor's infoview enough? The local Play build already
  consumes `lean/presentation/*.lean`, so the sheet appears at
  `play/worksheets/<Slug>.html`; what is still open is whether generated sheets
  should be listed next to the hand-written ones in `lean/play/README.md`.
- Should intermediate steps be exhibited as Lean propositions (`#check (… :
  Prop)`), not only for `private` helpers? The format allows a `lean` field on a
  step; it is currently used only where a private name forces it.
- How much of a cited theorem's *proof* should a presentation repeat? v0 cites
  the name and glosses the statement. The capstone is a good test: its seven
  inputs are deep theorems of the segment, and repeating any of them would
  double the document.
- A second instance should be a definitional subject (the two function fields,
  say) to see whether the four-layer split still fits when there are no
  proof-bearing declarations.
