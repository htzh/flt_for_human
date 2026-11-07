# Assembler interfaces, proof scripts, and module boundaries: how a ported proof becomes readable

**Status: methods note, written from the FFG T15 case (2026-11-04); §7–§8 added the same day from
the T16 dispatcher case; §5's fan-in/fan-out rule added 2026-11-06 from the T15 re-cut.** §1–§4 are the diagnosis, §5 the remedy menu, §6 the measured cost of
each mechanism, §7 the proof-script tests, §8 the certificate and module-graph tests, §9 the
naming/namespace policy, §10 the audit recipe, §11 where else in the tree to look. The two worked
instances — the exact edits, the module splits, the gates — are
[functionFieldGeneration/TOPIC-ffg-refactor.md](functionFieldGeneration/TOPIC-ffg-refactor.md) §13.
Companions: [TOPIC-dedup-refactoring.md](TOPIC-dedup-refactoring.md) (what to do with content the
port already has) and [TOPIC-mathlib-module-homing.md](TOPIC-mathlib-module-homing.md) (where a
declaration belongs). Authority for statement fidelity is
[porting-playbook.md](../porting-playbook.md) §4, for what to export §5.

**The worked instances, end to end: [CASE-hall-all.md](CASE-hall-all.md).** That is the note to
point at when you say "refactor this like `hall_all`": symptoms, the seven-step treatment, the
before/after arc with numbers, the things the first attempts got wrong, and the gates — twice, the
second time one node down on the prime-power degree dispatcher, where the last step turned out to
be a module boundary rather than a statement. This note is the method; the case note is what it
looks like on real nodes.

**The claim, stated once.** An *assembler* — the theorem that closes a node by applying three or
four ported theorems — is the declaration most likely to be unreadable, and the cause is
structural, not stylistic. It is transcribed from the pin's `Theorems/` wrapper, and a wrapper is
itself a transcript of a proof script. What survives the transcription is the pin's **local proof
context**: the binders the script happened to have in scope, the auxiliary datum it happened to
`obtain`, the `rcases` it happened to perform. That context is not an interface. A reader of the
port cannot see the mathematics through it, and a caller cannot use the theorem without
reconstructing the script.

This note is the generalisation of two worked cases; each is worth reading first because every
claim below is a number measured there.

**Readability has three surfaces, and a fix on one does not reach the others.**

| surface | the defect | the tests | the gates |
|---|---|---|---|
| the **statement** | it records the pin's proof script (§2) | decode into one sentence, count copies, find the `rcases` (§4) | the checker's diff against the wrapper |
| the **proof script** | it performs arithmetic and setup instead of mathematics (§7) | the five-lines test, the closure test, the orientation test (§7) | none — only a reader |
| the **module graph** | a certificate is homed by the file its proof came from, so the caller pays for it (§8) | producer-versus-consumer order, subject-versus-dependency (§8) | the wire, the register, the import cone |

The last two have no mechanical gate: a body can be fully checkable and unreadable, and a tree can
be fully green while every module is homed by an accident of its proof's import list. That is why
they are in a methods note and not in a script.

## 1. The worked case, measured

`ModularCurve.jqN_div_mem_modularFunctionField`
([`FunctionFieldGeneration/Descent.lean`](../FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean))
— this note was written when the statement was the one below; it has since been replaced by
the `Hall` form, and case note §4 corrects this section's conclusion — stated:

> For a prime `p` and a level `M`, `j(q ^ M) ∈ ℚ(j(q), j(q ^ (M * p)))`.

Counted on the tree as it then stood:

| quantity | count |
|---|---|
| statement lines (75–90) | 16 |
| lines of mathematics in the conclusion | 1 |
| binders | 10 |
| binders that do not occur in the conclusion (`K`, `ζ`, `hζ`, `htw`, `hsp`) | 5 |
| copies of the pushed-minimal-polynomial term in the signature | 2 |
| the same root-predicate hypothesis across the FFG directory | 6 (in 2 files) |
| glue the caller writes to speak this interface (`Capstone.lean:141–215`) | 75 lines |
| the caller's call site | 7 lines |

The pattern is not local to T15. In `ModularCurve/` the composite
`` $`(\text{coeffEmb}\ K) \circ (\text{qExpand}\ \mathbb{Q}\ N)`$ `` occurs 78 times, and the pushed
minimal polynomial 29 times out of 81 `minpoly` mentions — always inline. `Descent.lean` writes its
function field as
`(IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))` four times; the same type is written
`ℚ⟮jq⟯` 81 times elsewhere in the directory. So there are two problems here, and — the correction case note §4 records —
**they are not independent**: the unnamed vocabulary is a symptom of the certificate the
signature carries, and naming it (§3) makes the certificate readable without removing it. The
statement that "records a proof script" (§2) is the disease; the vocabulary was the wrong
remedy, and the four names it produced are `private` now.

## 2. What a transcribed signature records

Six symptoms. Each is a *proof artifact* that reached the statement; the right-hand column is the
question to ask of any assembler you are reading.

| # | symptom | why it is there | the question |
|---|---|---|---|
| 1 | a **hypothesis used inside exactly one `rcases`** of the proof | the pin's proof case-split the mathematical input before stating it | is this hypothesis one branch of something I can name without the split? |
| 2 | a **binder that the conclusion never mentions** | the proof passed to a splitting field / an algebraic closure and stayed there | is this statement really two theorems joined at a base-change? |
| 3 | a term of **two or more lines appearing twice** | no `def` existed at the pin's level of abstraction | what is this object called in prose? |
| 4 | `∀ x, f x = 0 → …` where `f` is a predicate | the script wrote `eval` where the library has `IsRoot` | what is the set being quantified over? |
| 5 | the theorem **manufactures its own auxiliary datum** (`obtain ⟨data, -, -⟩ := …` in the body) | the pin's node proved the datum's existence elsewhere | can the caller name that datum, or is every hypothesis about it forced to be asymmetric? |
| 6 | arithmetic in **unmatched association** (`M * p * M` in the statement, `p * (M * p * M)` in the proof) | the statement and the proof were written at different times | does the statement's spelling make the proof re-associate? |

The instance, for each: (1) `htw`/`hsp` are branches 2 and 1 of the `rcases` at line 189; (2) `K`,
`ζ`, `hζ` are the splitting field `CyclotomicField (M * p) ℚ`, and the tail of the proof
(lines 207–215) is the base-change back; (3) the pushed minimal polynomial; (4)
`Polynomial.eval y P = 0` for `P.IsRoot y`; (5) the level-`p` modular datum is `obtain`ed inside
the theorem, so neither `htw` nor `hsp` can mention it — which is exactly why the caller must
re-derive the datum's root shape himself (the 75 lines of §1); (6) three `TS_congr (by ring)`
blocks, ≈20 lines.

**Symptom 5 is the one that is invisible to a reader** and it is the reason the interface cannot
simply be tidied: a theorem that selects its own witness has no interface in terms of that witness.
Any hypothesis about the witness must be stated about something else, so the statement ends up
asymmetric — here, both hypotheses constrain the minimal polynomial and neither can constrain the
modular equation.

## 3. Unnamed vocabulary is a separate defect

An assembler with a good statement can still be unreadable if its terms are spelled out. The test is
mechanical and does not need judgement:

* count the term's occurrences in the directory — 78 for the nome-reading composite, 29 for the
  pushed minimal polynomial;
* count the characters in the shortest correct spelling of the *object* — `pushedMinpoly K M (M*p)`;
* if the object has a name in the module's own prose (here: "the pushed minimal polynomial", used in
  three headers), the `def` is a transcription omission, not a design choice.

A `def` introduced this way must be **definitionally** the old spelling, and that must be proved in
the tree (`:= rfl`), not asserted in prose. Otherwise every downstream proof rewrites, and the cost
lands on the next wave instead of this one.

## 4. Decoding a signature (a five-minute procedure)

Do this before designing anything; it is also the fastest way to review someone else's assembler.

1. **Write the sentence.** One English sentence: "if …, then …". If it needs more than two clauses,
   the signature has a symptom.
2. **Mark the conclusion's vocabulary.** Every binder/term not in the conclusion is either a
   *certificate* (it carries the proof) or an accident (it carries the script). Sort them.
3. **Count copies.** Any term twice in one signature is a `def` (§3).
4. **Find the `rcases`.** Grep the proof body for `rcases`/`obtain` and check whether each hypothesis
   is consumed whole or in pieces. A hypothesis consumed in one branch is a split, not an interface.
5. **Look for the base change.** A field variable in a ℚ-statement is a base-change certificate; the
   tail of the proof will be the descent back, and it is a lemma.
6. **Record the ratio.** statement lines : conclusion clauses. T15 is 16 : 1. Ratios above about 4
   are worth a second pass; the number is the one thing that can be tracked across a wave.

## 5. The remedy, in the order it should be applied

Each step is independent and each is a strict improvement; do them in this order because the later
ones are easier once the earlier ones have names to work with.

1. **Name the objects** (§3): a `def` per repeated term, with a `rfl` bridge.
2. **Replace formulas by predicates**: `P.IsRoot y`, or a named root-set relation. Instantiate the
   `∀` yourself in the hypothesis; the caller never wants the general form. *Which* spelling is not
   free — pick the one the declaration that finally consumes the hypothesis already takes, or you
   buy an adapter (see "Fan-in and fan-out" below).
3. **Name the case-free hypothesis.** The engine's hypothesis — here "the pushed minimal polynomial
   and the level-`p` equation have the unique common root `x₀`" — is a `def` or a named hypothesis
   of the *core* theorem, and the case split becomes a separate lemma that *derives* it, so the core
   and the pinned statement share one proof body. Extracting the core is the deeper fix and it does
   restructure the pin's script, so it needs a reason; but note that **rewriting only the statement
   is not a restructure at all**. A hypothesis that is one branch of a case split is *applied* at
   one place in the proof; changing its shape changes that application and nothing else. If the plan
   for an assembler says "keep the old statement and add a readable one on top", suspect it: it
   usually means the mathematics stays under the unreadable statement (see §6).
4. **Name the seam** for a hidden base change: a generic reflection lemma ("membership in a subfield
   of `ℚ((q))` reflects along an injective ring map") plus a splitting-field theorem. The ℚ-level
   statement then reads as the theorem, and the `K`-level one as its certificate, with the reason
   for `K` visible in the name.
5. **Seal the seam in the caller's direction.** If the certificate is now derivable from a named
   invariant (`Hall M`) that the caller already has, give the *caller* that interface. This is the
   step that lands the value: the 75 lines of glue and the 7-line call site collapse to one line,
   and the glue moves into a module whose subject it is.
6. **Normalise the arithmetic.** Either state in one association, or introduce the level names once
   (`N := M * p`, then `N * M`, `N * (N * p)`). Three `by ring` blocks disappear.

**Where a helper that two modules need goes.** A `private` helper in the module where it
was first noticed is the right *first* step (§6), but if a second module re-derives the
same bound, a second private copy is the wrong second step: the fact needs an upstream
home both already import, and that home's own standard has to be discharged in the same
change. Measured on the FFG level bounds — once the second module needed them, the cost
stopped being two lines of Lean and became a regularisation pass on the home (7 `spec-pin`
wires, 5 `own:` rows, retirement from the frozen checker, `dedup`, silent-build check).
Budget for the home, not the helper; and pick the home by subject *and* by its
verification tier, because a subject-correct home in a legacy module costs the pass.

### Fan-in and fan-out are not symmetric

Steps 1–6 say what to *name*. They do not say whether a name should be a producer or a consumer,
and the two directions are not the same kind of thing:

* the **fan-out** of a declaration is what one application of it delivers;
* the **fan-in** is what the reader has to bring.

**High fan-out is a producer, and it is the good kind.** `exists_phiAtSeed_roots`
(`Descent.lean`) takes two instance arguments and delivers a polynomial plus three facts about it,
all three used by the one caller. A consumer reads the statement and stops: nothing behind the name
can change what the call site means, so there is no reason to open the file. Producers are also
where a case split belongs — "the root is the conjugate or one of the `p` twists" is one conjunct
once the set has a name (`IsPhiRoot`), and naming it is what kept the certificate's statement from
taking the companion polynomial as a parameter.

**High fan-in is a funnel, and it is the bad kind whenever the declaration could have been a
producer's statement instead.** The measured case (2026-11-06, the T15 re-cut): the engine takes
`Polynomial.aeval y A = 0`, the certificate's readable spelling was
`(A.map (nomeAlgebra N)).IsRoot y`, and the two are the same fact. The tempting repair is one
private adapter —

    private theorem mem_range_of_unique_common_root' (hB hBs hBnd hxA hxB huniq) : x ∈ …

— whose statement is the generic lemma's statement modulo spelling and whose proof is six lines of
`IsRoot`/`Algebra`-instance shuffling. It is a *cost* disguised as a name. A reader who meets it in
a proof cannot see that its content is `Polynomial.mem_range_of_unique_common_root`'s, nor what its
six hypotheses have to do with the goal, and the only way to learn either is to open the file —
exactly the click-through this note exists to remove. Six in, one out, no new mathematics.

**The boundary.** Fan-in is not wrong in itself: the engine has seven hypotheses and one
conclusion, and it is the best declaration in the segment. The test is whether a declaration
*forwards* or *is* the mathematics — specifically, whether its statement duplicates another
declaration's statement modulo notation:

| declaration | in | out | verdict |
|---|---|---|---|
| `Polynomial.mem_range_of_unique_common_root` | 7 | 1 | fine — the fan-in **is** the content; there is no upstream declaration it could forward to |
| `exists_transported_minpoly` | 1 | 5 | fine — a producer; read at its statement |
| `mem_of_mem_range_nome` | 1 | 1 | fine — one hypothesis, and its twelve lines of `q`-expansion injectivity exist nowhere else |
| `mem_range_of_unique_common_root'` | 6 | 1 | **not fine** — an adapter over a declaration with the same content; the content lives behind the name |

So: **push the work into high-fan-out producers, and give a consumer a reason to exist besides
notation.** When you want a low-fan-out consumer whose statement is another theorem's statement in
a different spelling, one of three things is true.

1. **The producers are speaking the wrong notation** and should be respelled to speak the final
   consumer's language directly. Here that is the whole fix: state the root conditions as
   `P.eval₂ (nomeAlgebra N) y = 0`, which is the engine's own spelling, and the adapter has nothing
   left to do — the descent's body becomes four lines with no conversion at all. The prettier
   spelling was the thing paying for the adapter.
2. **The consumer is not a re-spelling** but new reasoning, in which case it is a declaration and
   the fan-in is the interface to mathematics that lives nowhere else (`mem_of_mem_range_nome`).
3. **The conversion belongs at the call site** — and if the call site is the one theorem the
   segment exists for, that is the right place: the reader is already standing there.

**The one lawful funnel is a seam**, where the statement is deliberately unlike the content because
the content is a base change the caller must not see (§8's seam test). Keep those to one per seam,
and say so in the docstring.

### What not to do

* **Do not respell a pinned statement to make it readable.** The checker's diff is textual;
  measured: rewriting `IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))` as the notation
  `ℚ⟮jq⟯` inside `jqN_div_mem_modularFunctionField` reports **MISMATCH** (1 ok, 1 mismatch) and
  fails the module. The pinned text stays; the readable spelling goes in a *new* declaration (step
  1–5 above) whose statement is the port's own.
* **Do not make real mathematics `private` to dodge the diff** (playbook §4). The mechanism exists
  (§6); using it to hide a transcription is the failure it was built to prevent.
* **Do not delete the wire** to make an unreadable statement "not our problem". A module with no
  `spec-pin:` line is not diffed at all, so the module silently leaves statement verification.

## 6. What each mechanism costs (measured on `Descent.lean`, 2026-11-04)

The port has four kinds of public surface (see `spec/unwired_register.py`'s docstring for the
canonical statement of the three tiers). Mechanisms, for a declaration in an already-wired module,
with the counts measured on a copy of `Descent.lean` when it still had two diffable statements
(`2 ok` is therefore the starting point):

| mechanism | `check_port.py` result | bookkeeping | when |
|---|---|---|---|
| do nothing, declaration is public | `2 ok, 1 missing` — **FAIL** | none | never |
| `private` | `2 ok` — unchanged | none | the only consumers are in this module |
| public + `own:` row in `spec/decl_markers.tsv` | `2 ok, 1 own` — pass | one TSV row with a reason | ≥2 modules need the name |
| **retire a pinned statement**: pin's name kept, statement rewritten, `own:` row | that declaration reads `own`, not `missing` — pass | one TSV row, whose reason names the wrapper | the signature is the defect (§6) |
| new module with no `spec-pin:` line (tier 3) | not diffed at all | header must justify it; register it with `unwired_register.py` | a whole module's worth of port-own content |

Three facts that are easy to get wrong, all verified:

* **Where a marker goes (policy, 2026-11-04).** Only `spec/decl_markers.tsv`. The in-source
  `-- pin:` / `-- own:` comments the checker still reads are the obsolete spelling and are not to
  be reintroduced. A **promotion** whose statement is unchanged (a pin-`private` declaration made
  public) needs no row at all: the checker matches it by name — nine of the ten promotions in the
  dispatcher case did. A port-own *new* statement that must be public is the case a row exists for.
* **`own:` is tier 2, not an exemption from review.** `spec/decl_markers.tsv` takes
  `<module path>`, `<full declaration name as the checker parses it>`, and `own: <reason>`. The name
  must be the one the parser produced: read it out of `spec/check_port.py --json` rather than
  typing it from the Lean file. A name the parser did not produce yields `STALE MARKER` **and** the
  declaration stays `missing`, so the module still fails — the marker silently does nothing.
* **A tier-3 module is a real cost.** It is built and elaborated but its statements are never
  diffed, and the register is how anyone finds out what is in it. Prefer `own:` on a small number of
  declarations to a new unwired module unless the module is wholly the port's own (the `SlotValues`
  case: the pin has no counterpart because its content is the named sub-goals of a monolithic
  proof).
* **The wire is per module, the marker is per declaration.** Adding a wire never invalidates an
  `own:` row, and a `pin:` row can name a file the header does not list.

**When a pinned statement is the thing to retire.** Once an assembler's signature is judged
unreadable, the wrong repair is to add a readable declaration beside the pinned one. That keeps two
statements of one theorem and — because the proof stays with the pinned statement — leaves the
mathematics under the unreadable text, where the reader who arrives from the pin's name will land.
It also makes the readable declaration an adapter over the bad one, so the bad one can never be
removed later without redoing the work.

The repair is to **retire the text and keep the name**:

> the pin's declaration *name* keeps its role (it is what a reader arriving from the pin types, what
> consumers `#check`, what the presentation labels); its *statement* is replaced by the readable one;
> the retirement is recorded as an `own:` row whose reason names the wrapper file; the verbatim text
> is preserved in the topic note and in git history; **no `spec-pin:` line is removed.**

What this costs, stated honestly: the wire no longer diffs that statement, so nothing mechanical
checks that the port still states the pin's theorem — the port's statement becomes the spec, and the
`own:` reason plus the quoted text in the notes carry the record. That is a real loss of automation
and it is the right trade when the statement's readability is the deliverable, which for this port
it is. A module-level wire is the wrong granularity for the same reason: the *other* declarations in
the module still mirror their wrappers and must keep being diffed. What is measured is the verdict
(`own:` turns a `missing` into a passing `own`); the count that a particular module ends up with is
arithmetic on how many of its statements it still mirrors — `Descent.lean` lands on `1 ok + 1 own`,
recorded as a prediction in the FFG order §13.7.

**What still keeps a pinned statement verbatim.** Two cases, and only two: (a) the readable
declaration is a *different* statement, not a respelling — e.g. `Hall M` in place of two slot
hypotheses is genuinely new, so it is a second theorem, not a replacement; (b) the statement is not
yet understood well enough to respell it, in which case leaving it alone is honest and adding a gloss
in prose is cheaper than a second declaration.

**And when does the module's wire go?** When *no* public declaration in it mirrors the pin any more.
That happened in the FFG wave: after the descent was respelled, `Descent.lean`'s other statement
was still the pin's, so the wire stayed; once that one was respelled too
([functionFieldGeneration/TOPIC-ffg-refactor.md](functionFieldGeneration/TOPIC-ffg-refactor.md) §14),
the wire diffed nothing and was removed, and the module became tier 3 with its provenance in the
header (`no spec-pin: directive — not wired (tier 3)`, one measured line of output). The distinction
is per declaration for the retirement and per module for the wire, and keeping them apart is what
stops a module-level edit from unverifying a statement that still matches.

## 7. The proof script: does it read as mathematics?

Fixing the statement is necessary and not sufficient: the same case that produced §1 also produced a
body of eighty lines in which the mathematics was three of them. Six tests, in the order a reader
hits them. Each is a question you ask of a line, and each has a mechanical or near-mechanical
answer.

**The five-lines test.** Open the proof and read every line. Each must be one of: *the case
split*, *the induction hypothesis*, *a named lemma's application*, *the comparison*, *the
conclusion*. Anything else — a `set`, an `obtain` that manufactures the theorem's own datum, a
three-line bound, a rewrite that exists only to orient an equation — is a missing name. In the T15
descent nine lines of setup became one `obtain`; in the dispatcher a two-line certificate argument
disappeared altogether, derived inside from the condition the caller holds.

**The closure test.** A group of local facts consumed only by each other and by one or two
downstream lemmas is one helper. Ask of every `have`: does anything outside this block use it? If
no, and the block is longer than three lines, it is a `private` theorem — in the consumer if the
statement is about this proof's own data (the decomposition `d = M * p ^ (a + 1)`, the bound below
it), upstream if it is standard mathematics (a `ψ` recurrence, a power shape, a tower lemma).

**The arithmetic test.** Does a line look like it belongs in a number-theory module? Then it
does, and it needs a name. The tell is `omega`, `ring`, `Nat.minFac`, a `calc` chain over `ℕ`, or an
`⟨p, by rw [pow_succ, mul_assoc]⟩` witness. This is the test that produced the upstream level
bounds and, in the dispatcher case, the generic tower lemma `IntermediateField.adjoin_eq_adjoin_Iio`
— a statement that names no `jq`, no `ℚ` and no prime, and therefore belonged in
`FieldTheory/`.

**The orientation test.** Keep the constants; eliminate the variables. In Lean `subst h` for
`h : x = y` substitutes the *right-hand* side away when both are variables, so `h : d = N`
eliminates the level `N` and leaves the divisor `d` — the opposite of what a reader wants in an
induction over `N`. State the equation in the direction of the variable you want to disappear
(`have hNd : N = d`, then `subst hNd`). If no orientation gives the right elimination, the proof
has introduced a variable it does not need. (Measured: one line, and the whole `Tight` half went
from `d` to `N`.)

**The commentary test.** A comment inside a term is a claim no gate checks: it answers one
reader's question at every reader's cost, and it is not compiled. If a line needs a comment it needs
a *name* — a `def`, a lemma, a helper, or a different statement — and the explanation belongs in
the module header, the topic note, or a test the build runs (`fail_if_success`). Corollary: do not
add a comment to record why a step is there; add the step's name.

**The arithmetic and commentary tests meet on one line.** A comment that explains arithmetic — "the
conjugate sits at level `p * N * N`, so `a = N`, which does not divide `M`" — fails both at once, and
the repair is one declaration: **the sentence becomes the helper's statement, and its subject becomes
the name.** Measured on the T15 re-cut's comparison (2026-11-06): three comments in the mainline
became three `private theorem`s —

| the comment | what it became |
|---|---|
| "the conjugate sits at level `p * N * N`, so `a = N`, which does not divide `M`" | `conjLevel M p ≠ slotLevel p a`, given `a ∣ M` |
| "its level forces `a = M`, and then the twist index `b'` is `0`" | `twistLevel M p = slotLevel p a → b < M / a → ζ ^ (p * (b * a)) = 1` |
| "`b < p` keeps the exponent below the order, so `ζ ^ (b * M) = ζ ^ 0`" | `ζ ^ (b * M) = 1 → b < p → b = 0` |

— and the descent's body went from 45 lines to 19 with no `omega`, no `ring`, no `Nat.*` rewrite and
no comment in it. The count that matters is *where the noise went*: it did not disappear, it moved
into proof bodies whose statements now say what they prove, and the mainline became
`obtain` / `rcases` / one helper per branch. Note also what the third row buys: the mainline keeps
the case split and the confrontation of the two descriptions — that is the proof — while every step
of *index arithmetic* is a name.

**Name the magnitudes the comments name, as `abbrev`.** The statements above cannot read without the
three levels, and they must be `abbrev`s, not `def`s: instance search unfolds `abbrev` at `reducible`
transparency, so `NeZero (conjLevel M p)` is synthesized for `TS`'s level argument, while the same
`slotLevel` as a `def` fails to elaborate at every `TS` that mentions it (verified: `def` gives
`failed to synthesize NeZero (conjLevel M p)` at three sites). `abbrev` has a second payoff —
`TS_injective` then returns `conjLevel M p = slotLevel p a` in exactly the terms the helper takes,
so no unfolding happens at the call site.

**The call-site test.** A continued line that exists only to hold a certificate, a
`(by rw [...])` inside an argument, or a nested application of a theorem that produces another
theorem's hypothesis: these are §8's symptom, not a style matter. The caller should be able to
write one line whose arguments are conditions it holds.

Two habits that make these tests cheap to run. **Read the caller**: a body that looks fine on its
own can be paying for itself at every use, and the use site is where the duplication shows
(two lambdas with the same header, the same two-line term twice). **Measure the ratio**: statement
lines to lines of mathematics, and proof lines to named applications. The numbers in §1 and §6 were
taken that way, and the ratio is the only quantity that can be tracked across a wave.

## 8. Certificates, seams, and the module graph

The statement-level symptom (2) of §2 — *a binder the conclusion never mentions* — is usually a
**certificate**: a hypothesis whose content is another node's conclusion, written out so that this
node can consume it. The test and the repair:

**The certificate test.** For every hypothesis, ask *which theorem produces it, and can I derive
it from what the caller has?*

* If the producing theorem lives **upstream**, put the derivation inside this theorem and take
  the condition the caller actually holds. Measured on the T16 dispatcher, three times over:
  `hup` (T18's generation) became `p ∤ M`; the `hall` projection (T17's prime non-membership)
  became a line inside; `hnm` (T17's tower read at the full field) became two lines inside. The
  caller's line went from three arguments to `relfinrank_full_eq_mul M p a hpM hallM`.
* If the producing theorem lives **downstream**, the derivation cannot go inside, and the
  interface is not the thing to change: the **tree** is. Split along the dependency (see below) or
  accept the edge, but say which and why in the header.

**Is it a condition or a certificate?** A condition is a statement about the objects in the
conclusion ("the new generator is not in the lower field"); a certificate is a proof-shaped object
(a field equality, a `Hall` bundle) that only matters because some proof needs it. The stopping
point is the most general condition the *caller can produce in one line*, not the most general
statement: the two ends of that trade are `hnm` (any proof of it) and `Hall M` (the induction's own
state), and the dispatcher chose `Hall M` because the theorem *is* the induction's step.

**The import-order test.** The module that states a theorem must sit downstream of everything its
*proof* uses, and upstream of nothing its *caller* pays for. When a fact both (a) is consumed by a
node and (b) consumes that node's statement, no ordering is free: **split the node along the
dependency**, one module holding the facts the induction consumes and another the statement that
consumes the degree step. Measured: one 891-line non-membership module became `Nonmembership`
(988 lines, the two facts the induction uses) and `TwoPrimeSeparation` (300, the public `Theorems/`
statement that needs T16).

**The homing test.** Home by *subject*, not by the file the proof came from. The T19 helper
`jqN_prime_not_mem_full` sat in `SlotProduct` because its proof uses the slot machinery; by subject
it is non-membership, and that mis-homing is exactly what produced the `T16 ⇒ T19` import edge that
reads (correctly) as a symptom. When a node's statement is the thing a module is *named for*, the
module imports the machinery it needs; it does not host the machinery's other clients.

**The tier test.** A port-own declaration — one the pin has only as a `private`, or not at all —
has exactly two lawful homes: `private` in its consumer, or a **tier-3** module (no `spec-pin:`,
registered with `spec/unwired_register.py`). A *promotion* whose statement is unchanged needs
neither: the checker matches a promoted pin-`private` declaration by name (nine of ten promotions in
the dispatcher case matched and cost nothing). `spec/decl_markers.tsv` is the residue mechanism, for
a port-own statement that must be public: one row, with the reason. The in-source `-- pin:` /
`-- own:` comments are the obsolete spelling and should not be reintroduced.

**The seam test.** When the conclusion is over `ℚ` and the signature mentions a field `K`, the
proof is base-changing and the certificate is the proof's, not the caller's. The statement then
loses `K`, `ζ` and the root predicates, and the certificate-taking form becomes `private` in the
same module (the port's first answer — a second public statement in a seam module, with the
`K`-level theorem kept public beside it — is the detour the case note's §4 records; it was
withdrawn on 2026-11-05). A seam module is the right answer only when the certificate's
dependencies and the caller's would otherwise force one module to serve two import directions.

A last, unglamorous note. **No gate checks any of this.** The build, the checker, the register and
`dedup` verify that the statement matches the pin, that nothing is unreachable, that the imports
resolve and that the axioms are the three expected ones. They cannot tell whether the statement
reads as a sentence, whether the body reads as mathematics, or whether a module is homed by subject.
Those three are why the case notes exist.

## 9. Naming and namespace for port-invented vocabulary

The question that comes up immediately: should a new `def` be `private`, or live in a sub-namespace
to avoid colliding with a future pin declaration?

The two questions are orthogonal, and it helps to say which one is being answered:

* **`private` vs public** answers *"does another module need to name it, and does the checker see
  it?"* — the table in §6.
* **namespace** answers *"can a future pin file collide with this name?"* — and the checker is
  **blind to it**: matching keys on the last name component and the statement's content hash, so a
  namespace neither creates nor removes a `missing`/`mismatch`. Measured: `check_port` reports the
  same counts before and after a namespace move.

Policy, in the port's terms:

1. **Default to `private`** for a helper whose consumers are all in one module. It is free on both
   axes (`lean_parser.py`: "a `private` port helper is never diffed").
2. **Export it, in a sub-namespace, when a second module needs it.** The port's `ModularCurve`
   namespace is otherwise *exactly the pin's*, so a bare port-invented name there is an
   undetectable collision waiting for a re-pin. Six sub-namespaces already exist
   (`ModularCurve.Period`, `.LevelP`, `.TateCurve`, `.X1HeckeCorrespondence`, `.SiegelUnit`,
   `.LevelN`), so this is house style, and it costs a consumer one `open`.
3. **Audit the candidate name against the pin before exporting it**, not after:
   `cd lean && python3 spec/statement_db.py grep <name> --limit 3`. Zero hits today is not a
   guarantee for the next pin, but the corpus is rebuilt on every pin move and the command is one
   line — re-run it at the re-pin, not per wave.
4. **Name the object, not the construction.** `nomeMap` and `x₀`, not
   `minpoly_map_comp_coeffEmb_qExpand`. If the module's prose already names the thing ("the pushed
   minimal polynomial"), that phrase is the name — but the name is earned by the writing it saves,
   and the writing that counts is inside a proof, not across statements. The pushed minimal
   polynomial was named while four *statements* spelled it out and lost the name once one proof
   was the only place it appeared (see §5's fan-in/fan-out rule).
5. **Group, do not scatter.** One sub-namespace per family of port-invented vocabulary (here: the
   two nome/slot readers), not one namespace per `def` and not one per module.

## 10. Audit recipe

```bash
cd lean

# 1. the statement's size and its duplicated terms (the ratio from §4.6).
#    measured on the pre-2026-11-05 statement, since replaced by the `Hall` form
awk 'NR>=75 && NR<=90' FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean

# 2. is the vocabulary already named somewhere? (zero is the answer that means "add a def" —
#    and §4 of the case note and §17 of the log are the record of what naming it cost)
python3 spec/statement_db.py grep pushedMinpoly --limit 3      # the pin
grep -rn "minpoly ℚ⟮jq⟯" --include=*.lean FLTForHuman | wc -l  # the port

# 3. does a port-invented name collide with the pin's?
python3 spec/statement_db.py grep <candidate> --limit 3

# 4. the wire and the marker table, after an edit
python3 spec/check_port.py <module> --force --json | head -40   # the parsed names, for `own:` rows
python3 spec/check_port.py <module> --force                     # 0 mismatch / 0 missing

# 5. nothing new is unreachable or duplicated
python3 spec/unwired_register.py --check
cd ../tools/deps && python3 dedup.py --module <...> --no-json
```

The `--json` run in (4) is not optional: it is the only way to learn the declaration name the marker
table must use (§6), and the only way to see the `own:` rows that have gone stale.

## 11. Where else to look, and what is not settled

Candidates of the same shape, in the FFG directory first because that is where the case was measured:

* `SlotProduct.minpoly_jqN_map_eq_prod_slots` — a ~15-line statement whose subject is the slot list.
  Its spelling cannot change (a pinned statement), but a readable restatement is blocked one level
  earlier: the slot vocabulary `sv` that would state it is `private` to its own module, so the
  readable form has to be invented in a public home first.
* `SlotProduct.jqN_prime_not_mem_full` and `Nonmembership` — check for symptom 1: the hypotheses
  may be branches of one case split.
* `PrimePowerStepAnyField` (the C-layer twin) — **done** (2026-11-04, same wave): four
  inline blocks replaced by the two shared bounds once they moved to
  `NumberTheory/DedekindPsi.lean`. This is the case that shows why a private helper is
  only the first step: the twin re-derived exactly the same three lines twice.
* `modularFunctionField_eq_full_of` — **done** (2026-11-04, same wave): it was not the T15
  pathology at all. No seam, no case split, no certificate; the defects were a hypothesis stating the
  module's own `abbrev` (`Gen`) unfolded, a five-binder prefix written twice, and two facts consumed
  together but passed apart — *and the duplication had migrated to the call site*, where two lambdas
  repeated the same header. Five lines became three, the caller's twelve became eight. Recorded in
  [functionFieldGeneration/TOPIC-ffg-refactor.md](functionFieldGeneration/TOPIC-ffg-refactor.md) §14.
  **The lesson to carry: read the caller.** A two-hypothesis statement can look fine on its own and
  still be paying for itself twice at every use.
* `DegreeStep`, `Generation`, `Collapse` — 1–3 public declarations each; cheap to read end to end.
* The `C`-layer twins (`SlotProductAnyField`) carry the same signatures, so a fix lands twice or
  not at all; decide which before editing either.

**Settled (2026-11-04).** Whether to retire a pinned but unreadable statement: **yes, retire the
text and keep the name**; keep the wire while some declaration in the module still mirrors the pin,
and retire the wire with the last of them (§6). Not a policy question any more — it is what the FFG
wave 7 did, and the module is now tier 3 with its provenance in the header.

**Not settled here.** (a) Whether to thread the auxiliary datum (symptom 5) through the signature
as an explicit argument: it is the deeper fix, it *does* change the shape of the statement beyond
respelling, and it has no consumer yet. (b) Whether the same retirement should be applied to the
other assemblers in §11's list — each is a separate judgement, and the FFG case was chosen because it
had a measured caller. (c) The threshold in §4 (4 : 1) is a review heuristic measured on one case,
not a rule. (d) A port-own helper that two modules need has no single lawful home yet: the
dispatcher case promoted it and paid one `.tsv` row, the alternative is to move the vocabulary it
depends on into a tier-3 module — both were argued on the day and neither is settled.
