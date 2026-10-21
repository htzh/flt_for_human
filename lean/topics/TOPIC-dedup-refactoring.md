# Refactoring a landed port during the dedup phase of a new cut

**Status: methods note, written from the FR1 set (2026-10-20).** §1–§6 are the standard; §7 is the
worked example with its measurements; §8 is what the FR1 refactor deliberately left undone. The
companion note for the *homing* question — where a ported declaration's path and namespace belong —
is [TOPIC-mathlib-module-homing.md](TOPIC-mathlib-module-homing.md); its §10 covers the composite
pin silo and the `private` phantom landings. This note is the third member of that family: what to
do with the port's **existing** content when a new node's dedup report says "you already have this".

**The question, stated once.** A new pin node is scoped; the tooling reports that some of its
statements are already in the port. The decision is not "how many copies are there" and not "how
many lines does the budget save". It is: *for each declaration the new module needs, where does
that content belong, and does the import graph the new module is forced to have put it there?* The
answer is allowed to be "write it locally" — and is allowed to be "promote it here" — but the
reason has to be about content and context, never about a count.

## 1. What the tools answer, and what they do not

Three instruments produce the dedup table for a pin node, and each answers a narrower question than
it looks:

| instrument | answers | blind to |
|---|---|---|
| `port_advise --target` | which pin declarations have their **statement** in the port, byte-identical or up to binder spelling; which have it only `private`; which share a name with a *different* statement | a match that differs by a file-level `variable` (the binder skeleton); that a matching host is out of context |
| `port_plan` | the budget: raw lines, once-only dedup, net new lines, declaration groups | the same, and it prices a **single** target file, so it cannot see cross-silo duplication at all |
| `shapes.py` | for every declaration of one module, whether a same-**shape** twin exists in the pin (split into its own `spec-pin:` sources and the rest) or in another port module | intra-file repetition of the pin file itself; anything whose shape differs by a dropped-binder rename; `def`s, which it does not key |

None of them answers the two questions that matter. *Is the declaration's host module a place where
this subject lives?* — that is a reading of the host's header and its consumers. *Is this a piece of
mathematics or a spelling of one?* — that is a reading of the two texts. The tools give the
inventory; the tests in §3 make the decision.

A practical note on the shape index: it takes a path **inside** `lean/`, so asking it about a pin
file means parking a copy of that pin file under `lean/tmp/` (untracked) and querying that. Query it
with `--port-only` — a pin file has no `spec-pin:` lines, so every one of its own declarations would
otherwise be reported as "another pin file", which is the noise the tool's docstring warns about.
The reverse query — a **port** module against the whole pin — is the receipt that a landing added no
twin (§5.6).

## 2. The failure mode: the pin file is a silo, and the import block inherits it

The homing note's §10 establishes that a pin `S_` file is not a unit of mathematics: it concatenates
other modules. The dedup phase meets a second, milder form of the same thing, and it is the one that
damages a *new* cut: even a single-subject `S_` file carries other modules' **prelude**, because the
pin's author wrote the same openers into every file that needed them.

The FR1 pin file is 1,307 lines and four subjects:

| pin section | lines | subject | port home at scoping time |
|---|---:|---|---|
| `Matrices` 23–174 | 152 | the Fricke matrix and its diagonal/level-scaling companions | partly public in `ModularForms/HeckeFrickeTrace.lean`, partly nowhere |
| `Fourier` 176–298 | 123 | `t • –` transport of periodicity / holomorphy / boundedness, and the resulting width change of `qExpansion` | public and general in `NumberTheory/ModularForms/QExpansionCoeff.lean` |
| `Level` 300–560 | 261 | `Γ₁` bookkeeping, restriction and level-change constructors, slash invariance | scattered `private` across six modules |
| `Rational`+`Even`+`Odd` 562–1281 | 720 | the reciprocity proper | `IsRat` block public in `WeightOne/Gamma0Integral.lean`; the parity assembly nowhere |

A port that transcribes "one `S_` file, one module" and imports what the pin's `import` block names
therefore does two bad things at once. It **imports out of context** — the pin's `import` block is
not a claim about subject, it is the author's convenience, and the port module it names may be an
unrelated silo. And it **re-derives real mathematics locally**, because the block's owner lives
somewhere the importer did not think to look.

Both directions are structural damage, and both are cheap to avoid *at scoping time* and expensive
later, which is what makes this a methods note rather than a cleanup note.

## 3. The four tests

Apply them in this order, to each declaration in the dedup table.

### 3.1 Content: mathematics or spelling?

The test is the promotion rule of [PORTING-DeligneSerre.md](PORTING-DeligneSerre.md) §4(b) turned
around: *would a second theory state this?*

* **Mathematics** — one home, called, never re-proved. `qExpansion_coeff_mul_width` is mathematics:
  the reindexing of `q`-expansion coefficients under a width change, which the port already states
  more generally. `IsRat` is mathematics (a predicate with an API). `frickeConj` is mathematics (the
  conjugation, named in statements). `Gamma1_le_of_dvd` is mathematics.
* **Spelling** — local, `private`, no guilt, no home. `natCast_pos'` is `Nat.cast_pos.mpr
  (NeZero.pos L)`. `mapGL_eq_coe` is `rfl`. `coe_mulPt`/`im_mulPt`/`diagGL_smul` are one-line
  restatements of the `•` action that `UpperHalfPlane.coe_smul_of_det_pos` already gives.
  `mulPt t ht τ` **is** `diagGL t ht • τ`.

The grey zone is a definition that is a *parameterisation* of an existing hub definition. The pin's
`diagGL (t : ℝ) (ht : 0 < t)` is `!![t,0;0,1]`; the port's `ModularForm.heckeDiagMatrix` is the same
matrix for a natural `p`, with an `if p = 0` guard. That is one definition in two parameter types.
The rule: keep the pin's real-parameter copy local, and generalise the hub only when a **second**
consumer needs the real form. Do not generalise a hub for one call site; do not write a second
near-copy after a hub has been generalised.

### 3.2 Context: is the thing at home where it lives?

A matching declaration is only reusable if its host's subject is the consumer's subject. When it is
not, the correct move is not to import the wrong host — it is to put the content where it belongs,
or to keep a local spelling. Three real instances from this cone:

* `CuspForm.LiNormSq.one_mem_strictPeriods` lives in `ModularForms/Analytic/NormSqPow.lean`, whose
  subject is the `L²` norm-square engine. It is the only *public* copy of `(1 : ℝ) ∈ Γ.strictPeriods`
  for `Γ₁`, so every consumer that wants the fact imports an analytic module. That is a home
  accident, not a home.
* `ModularCurve.JqIntegralRatios.restrictForm` is a public six-line `ModularForm` constructor inside
  a module about `J`/`q` ratios — and it sits **above** `WeightOne/Gamma0Integral`, so a
  `ModularForms/WeightOne` node that wants it imports a `ModularCurve` node for six lines.
* `ModularCurve.surjective_specialLinearGroup_map_zmod` (group theory: `SL₂(ℤ) → SL₂(ℤ/N)`
  is surjective) is homed in `WeightOne/LevelOneHauptmodul.lean`. It is a **premise** of the FR1
  node, not a helper, so it is imported and the misplacement is recorded rather than fixed in this
  cut — moving a premise is a different order's job.

### 3.3 Cluster: if you already import the host, promote there

This is the user's rule and it is the one that decides most cases: *if the cut already imports (or
must import) a module and that module has the content you need, promoting it there beats both
importing a third module and writing a local copy.* The import edge is already paid and the content
is already in context, so promotion adds no new structure — it exposes what the structure already
holds.

Two FR1 instances:

* `WeightOne/Gamma0Integral.lean` is imported for the `IsRat` block regardless — the headline's own
  hypothesis is `IsRat (qExpansion 1 f)`. So the Γ₁ facts and the restriction/slash constructors
  that `Gamma0Integral` carries `private` are *candidates* for promotion. They lose this test on
  §3.2, not on the cluster test: a `Γ₁` slash toolkit does not live inside a `Γ₀`-integrality module,
  and promoting it there would create precisely the placement we are trying to stop. The test is
  conjunctive: already-imported **and** on-subject.
* `ModularForms/HeckeFrickeTrace.lean` is the port's Fricke module, already public (`frickeGL`,
  `val_frickeGL`, `det_frickeGL_pos`, `coe_frickeGL_smul`), and the cut needs `frickeConj` — the same
  `F`, one conjugation away. Both conditions hold, so `frickeConj` was appended **there**, public,
  at the pin's signature, with a `pin:` row (§4.4). The two legacy `private` copies were left
  alone: they are other namespaces, and unifying them is not this cut's business.

### 3.4 Silo: a pin section that is one subject with no home gets a home

When a contiguous block of the pin is one subject, and the port has no module that owns it, the
answer is a module, stated at the **general** shape — the `CongruenceSubgroupOrder` pattern: a
supplement that states the lemma once, generally, in the namespace consumers already `open`, and
lets a consumer that must keep the pin's binder spelling wrap it in one line. Not a copy of the
pin's block under a new name, and not a section inside the consumer.

FR1's `Level` section is that block, and it landed as
`ModularForms/Level/Gamma1Slash.lean` (§7).

## 4. The checker's orientation — and why the cost is not counted

The dedup decision is a **writing** decision, and the reason is the checker's structure.

1. `spec/check_port.py` parses **the port module** (`statement_db.parse_file(rel, …)` with `rel` the
   port module) and looks each of its declarations up in the wire built from the module's
   `spec-pin:` files. Port `private` declarations are skipped outright ("a private helper is
   invisible").
2. Therefore: **imported pin material is invisible** — it is not a port declaration, so it costs no
   delta and needs no marker. **The delta is the number of public declarations written.** A module
   whose whole engine is `private` and whose only public declaration is its headline reports
   `1 ok`; the same module listed whole reports one row per public declaration. That is a choice
   about API surface, not about the checker.
3. It follows that "import rather than restate" and "write a two-line local helper rather than
   import" are **equally free** at the checker. Neither is priced. So the choice between them is
   made entirely by §3 — which is the point: the checker cannot be used to justify a structural
   decision, and it must not be.
4. **A declaration added to a wired host must be the pin's, byte-exact after `norm`.** The matcher's
   `pick` requires `nhash` equality: a promoted or appended declaration whose signature differs —
   an instance binder `[NeZero L]` where the pin has one, a section variable where the pin has an
   explicit binder, a different `k` — reads `mismatch`, not `ok`. Names are matched by last name, by
   the promoted key, by prefix stripping, then by content hash; the statement hash is the gate.
5. **A host that gains a declaration from a file outside its header needs a `pin:` row** in
   `spec/decl_markers.tsv`. `pin: <name> (<file>:<line>)` adds that file to the module's wire for
   that declaration, which is how `ALTraceIdentity.frickeConj` is verified against the FR1 pin file
   from inside the Fricke module. `own:` is tier 2 and is not diffed — use it for a statement of
   ours, never to silence a promotion.

The corollary, and the column's working rule since 2026-10-20: **the dependent-cascade price is not
an input to a dedup decision.** The port does not run tree builds; the checker is byte-exact, which
is where integrity comes from, and a stale unused `.olean` does not weaken a statement diff. The
build ladder still governs how a module is elaborated and built
([porting-playbook.md](../porting-playbook.md) §3.5) — but "this promotion
would cost 50 modules" is not a reason to duplicate mathematics, and "this promotion is nearly free"
is not a reason to make it. Both FR1 decisions here (append `frickeConj`; do *not* consolidate the
`Γ₁` copies) were made on content and context, and the free one was the append only because the
module was already the Fricke home.

### 4.1 Why build time is not an input — because refactoring has to stay affordable

That corollary is safe only because the port treats **elaboration cost as a defect, not as a
budget**. A module that takes minutes to elaborate is a bug in that module — an instance-inference
or defeq defect — and it is found and fixed in the cut that ports it. It is not a fact about the
tree to be traded against structural cleanliness. Establish that invariant and the cascade price of
a refactor collapses to *the number of modules in the wave times a few seconds*; the wave's size
stops being an argument. Fifty modules at 5 s each is a coffee break. Fifty modules at four minutes
each is a column that never refactors.

Which is the point, and it is the reason the rule exists: **we do not tolerate excessive build times
because we want refactoring to stay affordable.** Structural debt is only cheap to carry if paying
it off later is cheap. Every slow module raises the price of every subsequent structural
improvement — every promotion, every move to a proper home, every dedup wave — and so biases the
whole port toward leaving the silo exactly where it is. The two rules are one rule: *we do not price
refactors because we do not tolerate slow builds.*

The column's own record ([PORTING-DeligneSerre.md](PORTING-DeligneSerre.md) §1, §5 and the logs they
cite):

* the `ZLattice` pair was drafted, priced at **429 s**, and deferred — and the diagnosis then found
  that the cost was not in the proofs at all: three `PeriodizeLift` declarations each blew the
  diagnostic in their *statements*, all of it the argument check of a hypothesis mentioning the norm
  on a restricted `ContinuousMap`, so `isDefEq` unfolded `dist x 0`, `sInf` and `Finset.sum`. Naming
  that hypothesis type once (`LocSum`) took the 614-line module to **5.5 s** and the pair landed as
  the column's first registered deviation set. Nothing was traded away; a bug was fixed.
* five of the pin's large `maxHeartbeats` bumps turned out to be precaution and were dropped whole
  in the phase-2 wave (no module in that set carries a `set_option maxHeartbeats`), the two real
  ones being instance-inference shape problems;
* the one genuinely expensive proof (`sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow`,
  pin bump 4,000,000) is arithmetic defeq, exceeds the 200k *diagnostic* by design, and lands in
  **31 s** at tier 1 with no `set_option` — the cap is a diagnostic, the library setting is the
  build budget ([../logs/build-time-issues.md](../logs/build-time-issues.md) is the open register).

The *method* for paying this debt cheaply is
[porting-playbook.md](../porting-playbook.md) **§3.5, "the build ladder"** — do not improvise it:

* the **probe ladder**, five `lake env lean` turns of seconds each: *statement or proof?* (stub the
  proof with `sorry`; if the timeout survives, the cost is in the type and no tactic change can move
  it); *isolate* the declaration in a scratch file from the module's imports with the prelude's
  proofs stubbed, one `-- PROBE <label>` per candidate; *shrink the statement, not the file*; *read
  the counters* (`diagnostics true` for the reduction table, `trace.Meta.isDefEq` at a 3,000-heart
  cap to name the subterm that will not unify); *classify, then fix*;
* the two fix recipes are in playbook **§6**: an instance *search* blow-up gets the instance-brick
  treatment, and instance *terms* compared by an argument check get one syntactic form — the type
  named once, exactly the `LocSum` move — which deviates the statement and is therefore a registered
  `own:` row, not a bump;
* the **tier table** (edit loop / module / wave / session end) and the five rules: never `lake build`
  in the edit loop, one edit per module per wave, serialize with `flock`, and a whole-tree build only
  at the session's end with the user's agreement. Anything that resists all of that goes to a
  subagent briefed on the build-cost note (playbook §0.4).

**Operational form for the order.** If a dedup decision touches a module that is slow, its slowness
is **in scope**: that cut is the cheapest moment to bisect it, because the file is already open, the
wave is already being paid, and the diagnosis is the same read that the dedup needed anyway. The one
thing not to do is to use the slowness as the reason not to touch it — that converts a fixable
defect into permanent structural debt, which is the failure mode §2 describes, arrived at from the
other side.

## 5. The procedure

The round the manager runs before dispatching a set:

1. **Read the pin file's section boundaries** and name each subject. That table is the set's plan;
   it is not "one `S_` file, one module". If a section is one subject with no port home, it is a
   module (§3.4).
2. **Build the three inventories** for the block: statement-identical (import), name-relative and
   port-`private` (a decision each), absent (write). `port_advise --target` produces the first and
   the third directly. Point the shape index at a copy of the pin file (§1) to confirm the third at
   shape level, and — before believing any "this is a twin pair" story — to check the block for
   **internal** repetition: a parity split or a twin pair shows up as repeated shapes inside the
   file, and a block with none is as many developments as it has declarations.
3. **Attribute each reusable declaration to its host** and run §3.1–§3.4 on that host. Write down,
   in the order, the host, the verdict, and the one-line reason. A verdict of "import" that cannot
   name why the host is the subject is a verdict to revisit.
4. **Decide the block homes**, then write the home module(s) **first**, at the pin's signatures, wired
   by their own `spec-pin:` header. They are the ground the body stands on; they must be green and
   frozen before the body is dispatched.
5. **Promote/append only in hosts that passed §3.3**, at the pin's signature, with the `pin:` row.
   Then freeze those too.
6. **Hand the body to a subagent** with the work order: the frozen ground, the reuse map, the list of
   what to write `private`, the drifts already found, the gates. Do not let the body re-open a host.
7. **After the body lands, take the receipt.** Run the shape index on the new module against the
   whole pin: it should show the module's declarations as matched (they are the pin's) and add no
   twin in another port module. A landing that adds a twin has undone the dedup in the act of
   completing it, and a landing that adds minutes has undone the affordability of the next one
   (§4.1).

## 6. What a dedup-phase refactor must not do

* **Do not restate what you import** — not even "to keep the module self-contained". The checker
   costs it, the reader pays for it, and `port_advise` will report it as a substitution on the next
   cut.
* **Do not import a host for a helper.** If the only reason for the edge is the helper, write the
   helper (§3.1/§3.2). A `one_mem_strictPeriods` import of an `L²` module is the canonical error.
* **Do not promote into a host whose subject is different**, even when the cut imports it. That is
  how a silo is born: `restrictForm` public inside a `J`/`q`-ratio module is exactly this.
* **Do not consolidate a many-copy prelude inside a new cut.** "The wave is the same price for one
  move and five" ([PORTING-DeligneSerre.md](PORTING-DeligneSerre.md) §4(c)) is true of a file you are
  already editing; it is not a licence to
  open six modules a new node does not touch. Count the copies, record them, move on — the count is
  a *receipt* of past damage, not an instruction.
* **Do not add a public declaration to a wired host without the pin's exact signature and a
  `pin:` row** (§4.4–4.5).
* **Do not let the new module become the fourth copy.** If the block has a home, import it even at
  the cost of a local wrapper for a binder spelling; a private re-derivation of a block that has a
  home is the silo problem in its purest form.
* **Do not leave a slow module alone because touching it is expensive.** That is the same error one
  level up: it is how a tree becomes one that cannot afford the refactor (§4.1). The cut that touches
  a slow module owns the bisection.

## 7. The FR1 worked example, measured

The node: `ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0`, 1,307 pin
lines, 94 declarations, one headline. The dedup report:

* 17 declarations already have their **statement** in the port (9 byte-identical, 8 up to binder
  spelling): 12 importable public, 5 only `private`.
* 9 further names the port defines with a different binder skeleton, and 11 generalise rows where
  the pin block shares a name but not the binders — `frickeGL_mul_mul_inv` in 3 pin files as 3
  statements, `periodic_slash` in 6 as 4, `IsRat` in 7 as 4. The pin re-writes its own prelude with
  a different binder order in almost every file that needs it.
* Of the 81 theorem/lemma shapes, 12 have a same-shape twin in a port module and **none repeats
  inside the pin file**: the `Even`/`Odd` parity split is two developments, not a twin pair, so the
  610-line assembly is genuinely new.

The decisions, by §3 test:

| pin block | verdict | where |
|---|---|---|
| `Level` generic (18 declarations) | §3.4 new home, general shape | `ModularForms/Level/Gamma1Slash.lean`, **18 ok** |
| `frickeConj` | §3.3 append to the Fricke module | `HeckeFrickeTrace.lean`, **11 ok** (+1), `pin:` row |
| `frickeGL`, `val_`, `det_pos`, `coe_smul` | §3.1 import | `ALTraceIdentity.*` |
| `IsRat` block, `Eaux`, `exists_weights` | §3.2/§3.3 import (the headline's own hypothesis type) | `WeightOne/Gamma0Integral.lean` |
| `qExpansion_coeff_unique'` | §3.1 import | `ModularForms/QExpansionCoeff.lean` |
| `qExpansion_coeff_mul_width` | §3.1 import, one-line wrapper | `NumberTheory/ModularForms/QExpansionCoeff.lean` (more general) |
| `Gamma1_le_of_dvd` | §3.1 import (its declared subject) | `NumberTheory/ModularForms/CongruenceSubgroupOrder.lean` |
| `exists_of_mul_eq`, `exists_zeta_lift` | §3.2 import, restate at the pin's shape | `WeightOne/RationalityDvd.lean` |
| `diagGL`, `mulPt`, `liftDiag`×5, `frickeGL_eq_*`, `eq_frickeGL`, `mul_inv_mem_Gamma1`, `slash_of_neg_mem`, the `Fourier` transports | §3.1 spelling — `private` in the body | the new module |
| the `Even`/`Odd` assembly | new mathematics | the new module |

The split the tools did not produce, and the reading did: the pin's `Fourier` section is a
123-line re-derivation of a width change the port states publicly and generally. It is not
"already ported" by statement (the pin's extra `h' = N * h` hypothesis defeats the shape tier) and
it is not new mathematics. It is one call and a wrapper — the single largest structural saving of
the set, invisible to every instrument because the statement shapes differ by a hypothesis.

**Outcome (2026-10-20).** Three pieces: the toolkit (18 declarations, checker **18 ok**), the host
append (11 ok, +1, one `pin:` row), the body (1,202 lines, 62 `private` declarations and one public
headline — checker **1 ok / 0 mismatch / 0 missing**, `lake build` 4,136 jobs in 10 s, zero warnings,
axioms `[propext, Classical.choice, Quot.sound]`). Wired delta **+20**; the tree reads 3,805 ok over
148 modules; `frontier.py --ds --target` reads `needed 0 / 0 lines`, *"target is ported"*. The
receipt of §5.7 found **one** twin: a two-line `coe_Eaux`, re-derived because the host's copy is
`private` — exactly the residue §8's rule predicts, and the only place the body had to restate
something the port already had. Nothing else was opened, moved or promoted.

## 8. What the refactor left undone, and why that is the right residue

The `Γ₁` slash toolkit now has a home, and the copies it *could* replace are still in place:
`restrictF`-under-another-name in three modules, `T_mem_Gamma1` in seven, `one_mem_strictPeriods` in
fifteen, `Gamma_le_Gamma1` in four, the `γ 0 0`/`γ 1 1` variants of `mul_inv_mem_Gamma1`, and three
spellings of `frickeConj`. The list, with line numbers, is in [CARRY-FORWARD.md](../CARRY-FORWARD.md).

That is not an oversight, it is §6's fourth rule. Each copy sits inside a module the port
transcribed whole, and each of those modules is somebody's silo: folding them in means opening six
modules for a new node that touches none of them. The home exists now, so the *next* consumer that
has to open one of those modules for its own reasons can move the block in the wave it is already
paying — which is when the move is free in the only sense that matters, the sense that it comes with
a read of the file's content.

The same file's two `IsRat`s are the class's cleanest warning: the public one is the pin's
`∀ n, ∃ r, coeff n = r`, the private one is `∃ p : PowerSeries ℚ, p.map = φ`. Equivalent, not defeq,
same name, forty lines apart in one file. A consumer that opens the wrong namespace proves the
right theorem about the wrong predicate.

Records: [deligneSerre/WORKORDER-FR1-fricke-reciprocity.md](deligneSerre/WORKORDER-FR1-fricke-reciprocity.md)
(the order, the frozen ground, the reuse map), [PORTING-DeligneSerre.md](PORTING-DeligneSerre.md) §1
(the landing), [porting-playbook.md](../porting-playbook.md) §3.3–§3.4 (the order and the sets),
§3.5 (the build ladder and the probe ladder, §4.1), §4, §5 (the workflow this round sits in).
