# Case study: "refactor like `hall_all`"

**Status: case note, written 2026-11-04 from the end of the FFG wave-7 arc; §7 is a second
application, the same day, one node down.** This is the
worked instance of the method in [TOPIC-assembler-interfaces.md](TOPIC-assembler-interfaces.md),
kept as a template: when a node's assembler or its proof shows the symptoms in §1, apply the
treatment in §2 and check the gates in §5. The Lean-level traps that cost build rounds are
[functionFieldGeneration/TOPIC-refactor-friction.md](functionFieldGeneration/TOPIC-refactor-friction.md);
the decisions taken during the wave, with their reasoning and reversals, are
[functionFieldGeneration/TOPIC-ffg-refactor.md](functionFieldGeneration/TOPIC-ffg-refactor.md)
§13–§15. Measured on `ModularCurve.FunctionFieldGeneration`.

The short version, to be quoted at a future node: **decode the statement, name its
vocabulary, retire the text and keep the name, seal the seam behind the caller's vocabulary,
turn the proof's arithmetic into named lemmas — upstream if it is standard number theory —
and leave the proof reading as mathematics.**

## 1. The trigger

Two symptoms, from two different directions. Either one alone is enough to start; both
together is this case.

**In the statement.** The assembler `jqN_div_mem_modularFunctionField` stated
`jqN M ∈ modularFunctionField (M * p)` in sixteen lines: ten binders, five of which the
conclusion never mentions, the pushed minimal polynomial spelled out twice, and two
hypotheses that were the branches of one `rcases` in its own proof. The caller then wrote
seventy-five lines of glue to speak it. Ratios that flag this: statement lines to lines of
mathematics (16 : 1), and a term of two lines appearing twice in one signature.

**In the proof.** The capstone `hall_all` opened its `Tight` half with nine lines of setup
(`set p := d.minFac`, `Nat.minFac_prime`, `Nat.exists_eq_pow_mul_and_not_dvd`, a nonzero
derivation, a prime-power successor split, a re-oriented equation, a strict bound, a
divisibility witness) and closed with an eleven-line case split over `a = 0`. None of it was
about function fields.

The questions that decide whether to start:

- Does the conclusion's vocabulary appear in the signature, or only the proof's?
- Is a binder never mentioned by the conclusion? (It carries a certificate, usually a base
  change.)
- Is a hypothesis consumed in exactly one branch of one `rcases`? (It is half of something
  nameable.)
- Is a group of local facts consumed only by each other and by one or two downstream
  lemmas? (It is a helper's body — the *closure test*, the single most useful test here.)
- Does the proof contain a line that would be equally at home in a number-theory module?

## 2. The treatment

Seven steps, in this order. Each names the failure it prevents.

1. **Decode the statement into one sentence.** "If … then …". If it needs a third clause,
   the signature is recording the proof script rather than the theorem, and everything else
   below will be guesswork. Here: *under two root conditions on the pushed minimal
   polynomial, `j(q ^ M)` lies in `ℚ(j(q), j(q ^ (M p)))`.*
   **Prevents:** redesigning a statement you have not understood.

2. **Name the vocabulary.** One `def` per repeated term, with a `rfl` bridge so nothing
   downstream rewrites (`Nome.nomeMap`, `Nome.pushedMinpoly`, `pushedMinpoly_def`). Port-
   invented names go in a sub-namespace, because the port's namespace is otherwise exactly
   the pin's.
   **Prevents:** the reader decoding a five-line term at every occurrence, and a future pin
   colliding with your name.

3. **Retire the text, keep the name.** The pin's declaration *name* is the pin linkage (what
   a reader arriving from the pin types, what consumers `#check`); its *text* is the
   unreadable part. Rewrite the statement in place under the same name, adapt the proof's
   hypothesis applications, and record the retirement: an `own:` row naming the wrapper, or
   — once no declaration in the module mirrors the pin any more — remove the module's
   `spec-pin:` wire and say so in the header.
   **Prevents:** the worst of both worlds — two statements of one theorem with the
   mathematics left under the unreadable one.

4. **Seal the seam behind the caller's vocabulary.** If the conclusion is over `ℚ` and the
   signature mentions a field `K`, the proof is base-changing; give the certificate its own
   module and the caller a statement in its own terms (`DescentFromSlots`:
   `jqN_mem_modularFunctionField_of_hall`, no `K`, no `ζ`, no root predicate). The `K`-level
   theorem stays public — it is the mathematical statement with its certificate — but it is
   no longer what the next node calls.
   **Prevents:** every consumer paying for a splitting field it never wanted (seventy-five
   lines of glue and a seven-line call site, here one line).

5. **Turn the proof's arithmetic into named lemmas.** Apply the closure test: a group of
   facts consumed only by each other and by one or two lemmas is one helper. Then split by
   *subject*, not by consumer count — a statement about this proof's own data (the
   decomposition `d = M * p ^ (a + 1)`, the bound below it) stays `private` in the consumer;
   standard arithmetic on objects an upstream module owns (`ψ`'s prime-power recurrence, the
   prime-power shape) goes upstream, even with one consumer, because that is where the next
   module will look.
   **Prevents:** an induction that is 40% arithmetic, and cheap number theory buried in a
   proof where nobody will find it.

6. **Re-read the proof as mathematics.** Every line should be one of: the case split, the
   induction hypothesis, a named lemma's application, the comparison, the conclusion. If a
   line is arithmetic, it is missing a name.
   **Prevents:** the situation where the *statement* was fixed and the proof still cannot be
   read, which is what "refactor the assembler" alone achieves.

7. **Bring every touched module to standard.** Per
   [instructions.md](instructions.md) §"Legacy Modules": `spec-pin` wire, out of the frozen
   checker, silent build, no build-time blow-up, `dedup.py`, `move_dead.py`; and no doc
   cross-references left in headers or comments.
   **Prevents:** a clean refactor that leaves two modules unverified.

## 3. The arc, in the order it happened

| step | what changed | numbers |
|---|---|---|
| 0 | decode; measure. The descent's statement is 16 lines for one membership; `hall_all` is 80 lines | 16 : 1 |
| 1 | `Defs/PhiAtSlot.lean` gains `Nome.nomeMap`, `Nome.pushedMinpoly`, `pushedMinpoly_def`, `nomeMap_qExpand` | +43 lines, one 5-line `hcomp` becomes `simpa only [nomeMap] using nomeMap_qExpand` |
| 2 | the descent's statement rewritten in place under the pin's name; `hBev` retyped, two hypothesis applications changed, `hseed`/`hdist`/`hspread`/the engine untouched | statement 16 → 6 lines |
| 3 | `DescentFromSlots.lean` created: the 75 lines of glue move out of `Capstone`, behind `jqN_mem_modularFunctionField_of_hall` | new module 156 lines |
| 4 | `Capstone.lean` loses `Shapes` and its two-lambda call site; `Cyclotomic`/`TS` imports go | 337 → 240 lines; `hall_all` 80 → 57 |
| 5 | the second assembler: `Gen` used instead of its unfolding, two hypotheses merged into one conjoined induction step (the caller's two lambdas become one) | statement 5 → 3 lines; caller 12 → 8 |
| 6 | `hall_all`'s arithmetic: two `private` helpers in the consumer, the `ψ` recurrence and the power shape upstream; the `hprop` wrapper dissolved | `hall_all` 57 → 40 lines |
| 7 | `NumberTheory/DedekindPsi.lean` and `Defs/PhiAtSlot.lean` regularised (both were legacy modules) | 12 ok + 7 own; 18 ok + 4 own |

Two things did *not* change, deliberately: the **conclusions** (the same memberships and
field equalities, same hypotheses once decoded) and the **proof scripts' spines** (the pin's
`rcases`, its engine application, its injectivity strip). Only hypothesis *types* at two
application sites changed. That is what makes this a refactor and not a re-development: if a
step would change what is proved, it belongs in the node's own plan, not here.

## 4. What I got wrong first

The most reusable part of the record. Each of these was argued for, attempted, and reversed.

1. **"Keep the pinned statement and add a readable adapter beside it."** Wrong: the proof
   stays under the unreadable statement, so the reader arriving from the pin's name lands
   there; and the adapter makes the bad statement impossible to remove later. The fix is
   step 3: retire the *text*.
2. **"Keep the `spec-pin:` wire — it is the only guard against drift."** Right while some
   declaration in the module still mirrors its wrapper; wrong the moment the second one was
   respelled, because then the wire diffs nothing and left in place it reports the module as
   `MISMATCH` — a red flag saying "the port drifted" when the port chose. Retire the wire
   with the last mirroring declaration.
3. **"Explain the odd line with a comment in the proof."** Wrong direction: a comment costs
   every reader to answer one reader's question, and no build checks it. It became a shelf
   example with `fail_if_success` guards plus a friction note — a claim the build verifies.
4. **"`hprop`'s divisibility hypothesis is dead, its body pattern ignores it."** Wrong:
   `omega` was using it (`0 ∣ d` gives `d = 0`, contradicting `m < d`; `m < d` alone admits
   `m = 0, d = 1`). The refusal was the useful signal, and the fix was better than the
   original: apply `ih` directly at both sites and delete the wrapper.
5. **"The user named two clauses, so factor two clauses."** Wrong: the whole setup block was
   a closed set feeding them. Nine lines became one `obtain`.
6. **"A worked example can import all of `Mathlib`."** Wrong for a default-target library:
   that shelf file cost 97 s / 8924 jobs. Two imports do the job in 1.7 s / 689 jobs.

And three that belong to the friction note rather than here, because they are mechanical:
`rw` refusing an equation `exact` accepts (instance arguments inside an `if`);
`rw [h]` rewriting the variable inside `d.minFac` as well; and
`Nat.exists_eq_pow_mul_and_not_dvd` returning `d = p ^ k * M`, prime power first.

## 5. Gates

```bash
cd lean
# per edited module, in dependency order; silent output is the pass condition
timeout 110 lake build FLTForHuman.NumberTheory.DedekindPsi          # 3 s
timeout 110 lake build FLTForHuman.ModularCurve.Defs.PhiAtSlot      # 4 s
timeout 110 lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.Descent
timeout 110 lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.DescentFromSlots
timeout 110 lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
# statements: 0 mismatch / 0 missing on every wired module in reach
python3 spec/check_port.py <module> --force
# the register, when a module changes tier; the duplicates, for the edited modules
python3 spec/unwired_register.py --rebuild
cd ../tools/deps && python3 dedup.py --module <module> --no-json
# the headlines, by name
#print axioms ModularCurve.functionFieldGeneration
```

No tree build, ever, during the refactor (AGENTS); the cascade from a `Defs/` edit is a
reason to sequence modules, not a reason to build the tree.

## 6. What the case cost and bought

| file | before | after |
|---|---|---|
| `FunctionFieldGeneration/Descent.lean` | 256 | 293 (both statements shorter; the growth is the docstrings that now explain `K`, `htw`, `hsp` and the retirements) |
| `FunctionFieldGeneration/DescentFromSlots.lean` | — | 156 (75 of them the glue moved out of `Capstone`) |
| `FunctionFieldGeneration/Capstone.lean` | 337 | 240 |
| `FunctionFieldGeneration/PrimePowerStepAnyField.lean` | 1564 | 1555 (four inline blocks became one-line calls) |
| `ModularCurve/Defs/PhiAtSlot.lean` | 243 | 289 (the vocabulary, and the wire in the header) |
| `NumberTheory/DedekindPsi.lean` | 234 | 290 (three level bounds, the `ψ` recurrence, the power shape, the wire in the header) |

Statement lines: the descent 16 → 6, the one-prime reduction 5 → 3. `hall_all`: 80 → 40.
`#print axioms` on the four headlines: `[propext, Classical.choice, Quot.sound]` before and
after — this refactor changes no mathematics.

## 7. Second application, same day, one node down: the prime-power degree dispatcher

The theorem `hall_all` calls in its `Tight` half is `DegreeStep.relfinrank_full_eq_mul` —
"the relative degree of one full prime-power step is `p + 1` when `a = 0` and `p` otherwise".
It is worth recording separately because here **the treatment's last step was a module
boundary, not a statement**, and because most of the seven steps were first done the obvious
way and then undone.

### 7.1 The statement, decoded

The pin's `Theorems/` wrapper takes three things the conclusion never mentions:

* `hup` — `F^full_{M p ^ (a + 1)} = ℚ(F^full_{M p ^ a}, j(q ^ (p ^ (a + 1))))`, which is T18's
  `full_eq_adjoin_full_div_prime` handed in as a certificate;
* the `hall M` projection, i.e. `j(q ^ p) ∉ F_M^full`, which is T17's
  `jqN_prime_not_mem_full`;
* `hnm` — `j(q ^ (p ^ (a + 1))) ∉ F^full_{M p ^ a}`, which is T17's prime-power tower read at
  the full field.

Every one of them is *another node's theorem*, and each is what made the caller write a
two-line adapter in front of the call. Decoded, the statement is one sentence: *at a level
where the strong induction's invariants hold, and for `p ∤ M`, the step has that degree.*

### 7.2 The arc, measured

| step | what changed | numbers |
|---|---|---|
| 0 | decode; count the certificate binders | 3 certificates, 2 of them a two-line term |
| 1 | `hup` → `p ∤ M`, derived inside from T18 | statement 6 → 5 lines; caller's two-line adapter → one line |
| 2 | the chain bound extracted as a generic lemma (`IntermediateField.adjoin_eq_adjoin_Iio`, `FieldTheory/AdjoinTower.lean`, tier 3) | 22 lines of private induction → a 57-line generic module + a 10-line specialisation |
| 3 | `jqN_pow_not_mem_full`'s `hall M` → the prime-level fact it actually consumes | the helper stopped mentioning `Hall` |
| 4 | that helper made public next to the tower — **rejected**, see 7.3 | — |
| 5 | instead: the degree step derives `hnm` itself, and finally takes `Hall M` | hypotheses `hup`, `hnm` → `hpM`, `hnm` → `hpM`, `hallM`; no certificate term at the call site |
| 6 | the non-membership node split along its dependency: the tower and the prime non-membership upstream (`Nonmembership.lean`), the public two-prime separation downstream (`TwoPrimeSeparation.lean`) | one module (891) → 988 + 300 lines |
| 7 | `SlotProduct` loses the non-membership (homed there by its *proof's* dependency) | 1606 → 1228 lines; subject narrowed to the slot product |
| 8 | `Defs/Fields.lean` edited, so brought to standard: four `spec-pin:` wires and the port-own content extracted | 24 ok / 0 missing / 0 own; `Defs/Invariants.lean` created (tier 3) |

The final shape is a chain rather than a fan:

```
Defs/Fields        (wired)  the pinned field API and the Tight/Gen/Hall vocabulary
  ↓
SlotProduct        (wired)  the slot product
  ↓
Nonmembership      (wired)  jqN_prime_not_mem_full, jqN_pow_not_mem_adjoin_full
  ↓
DegreeStep         (wired)  relfinrank_full_eq_mul  (hpM) (hallM)  — all three certificates derived
  ↓
TwoPrimeSeparation (wired)  the public Finset separation, downstream because it consumes T16
Capstone           (wired)  hall_all and the four headlines
tier 3: Defs/Invariants (gen_prime and the two Tight packagings), FieldTheory/AdjoinTower
```

and the caller is one line, `relfinrank_full_eq_mul M p a hpM hallM`, with `hpM` and `hallM`
the only things it knows.

### 7.3 What I got wrong, in the order I got it wrong — seven, all reusable

1. **"Move the adapter to the neighbouring module."** Wrong: a certificate that only one
   consumer needs is not API. The repair is to change the *consumer's* interface until no
   adapter exists anywhere; the intermediate `hnotmem : jq ^ p ∉ F_M^full` survives only as a
   line *inside* the degree step's proof.
2. **"`Hall` is not a statement about fields, so the degree step must not take it."** Wrong in
   the other direction: reasoning about what the *proof* needs (one node's certificate) is the
   same mistake as reasoning about what the *caller* happens to have. `Hall M` is the
   induction's hypothesis and the step is the induction's step; taking it is honest, and it is
   what makes the three certificates disappear.
3. **Homing by proof dependency.** `jqN_prime_not_mem_full` sat in `SlotProduct` because its
   proof consumes `rval_aux`; by *subject* it is non-membership. That mis-homing is exactly what
   produced the `T16 ⇒ T19` import edge — the "upstream issue" that reads as a symptom, and is
   one. Home by subject; let the proof import upward.
4. **"A port-own helper can simply be promoted where it is used."** Only if the pin has it: the
   checker matches promoted pin-`private` declarations by name (nine of ten did), so a
   promotion whose statement is unchanged needs nothing. A *port-own* public declaration in a
   wired module is a structural error, not a bookkeeping one. Its two lawful homes are: private
   in the consumer, or tier 3. `spec/decl_markers.tsv` is for the residue — a port-own statement
   that must be public — one row, with the reason; the in-source `-- pin:` / `-- own:` comments
   are the obsolete spelling and must not be reintroduced.
5. **Silencing the linter.** `set_option linter.style.haveILetI false` on the two new
   `Tight`-packagings was the wrong fix; `have hfd : FiniteDimensional ℚ⟮jq⟯ …` elaborates and is
   used by instance search. Fix the source, do not mute the check.
6. **Inlining a shared helper to dodge the wire.** Copying `sv_inj_slot`'s bound argument into
   the second consumer duplicated *mathematics*, not an adaptation. The lawful answers were
   the two in point 4; the promotion plus one `.tsv` row was chosen.
7. **Re-serialising generated JSON by hand.** Regenerating the presentation source with the
   wrong indent rewrote all 1050 lines and hid the 27 that mattered. Round-trip a generated
   file with its own formatting.

### 7.4 One module up: the same inversion again, in `modularFunctionField_eq_full_of`

The `Gen` half of `hall_all` calls `Descent.modularFunctionField_eq_full_of`, and it was the
same defect one level up. Its hypothesis conjoined two facts per factorization `N = M * p` —
`Gen M` and `jqN M ∈ F_N` — and the caller had to build both: `Gen M` by projecting `Hall M`,
and `jqN M ∈ F_N` by applying the `Hall`-level descent and transporting it along `N = M * p`
with a private `mff_congr`. Six of the eight lines of the caller's lambda were that assembly.

The repair is the same shape as the dispatcher's, and it moved the statement: the module that
declares `modularFunctionField_eq_full_of` must sit downstream of the `Hall`-level descent, so
the reduction moved into the seam module beside it. Its first new text still indexed the
hypothesis by a factorization (`∀ M p, p prime → M * p = N → Hall M`) — better, but still the
wrong *shape*: the caller had to introduce `M`, `p`, the factorization and the bound before it
could hand over the induction hypothesis. The form that removes the whole lambda is the shape
the induction actually gives the hypothesis:

```lean
theorem modularFunctionField_eq_full_of (N : ℕ) [NeZero N]
    (h : ∀ m : ℕ, m < N → m ≠ 0 → Hall m) :
    modularFunctionField N = modularFunctionFieldFull N
```

so the capstone's `Gen` half is

```lean
  have hgen : Gen N := by
    unfold Gen
    exact modularFunctionField_eq_full_of N ih
```

— `ih` unchanged. Everything the reduction consumes (the factorization `N = (d m′) · p`, its
bound, `Gen (d m′)` and `jqN (d m′) ∈ F_N`) is derived inside. The theorem does need *some*
hypothesis: `F_N = F_N^full` is not provable at `N` alone — its proof reduces `j(q ^ d)`,
`d ∣ N`, `d ≠ N`, to the level `N / p` — but the only thing it consumes from below is
`Hall m`, which is exactly what the descent interface `jqN_mem_modularFunctionField_of_hall`
takes. Two by-products: the transport lemma `mff_congr`
(and its twin `full_congr`, which had a second private copy in `Degree/Roof.lean`) had to become
a shared declaration in a tier-3 module rather than a third private copy; and the `Gen`
reduction's pin node is now fully in the port's hands, its text retired to the `Hall` form.

The proof then took its own pass — the case's §2 steps, applied one level below the statement:

1. **The case split substituted the wrong side.** `rcases eq_or_ne d N with rfl | …` *is* a
   `subst`, and `subst` eliminates the right-hand side, so at `d = N` it eliminated `N` — the
   theorem's subject, its `NeZero`, the level every `modularFunctionField` in the goal is
   applied to. The branch's goal silently became `(qExpand ℚ d) jq ∈ modularFunctionField d`:
   provable, and read backwards. Naming the equation and writing `subst d` keeps the goal at
   `N`.
2. **The arithmetic became one `obtain`.** Fifteen lines of `minFac` bookkeeping — the
   decomposition `N = (d · m′) · p`, `m′ ≠ 0`, its `NeZero`, the bound `d · m′ < N` — are now
   the private `exists_mul_prime_lt_of_dvd_of_ne`, in the consumer: they are about the level
   `m` the induction hypothesis is taken at and the prime `p` its step is taken by, which is
   the `hall_all` precedent of §2 step 5 (`private` for this proof's own data, upstream only
   for standard number theory). The second private helper,
   `full_le_of_gen_of_mem`, carries the other non-arithmetic step — `Gen m` and
   `jqN m ∈ F_N`, hence `F_m^full ≤ F_N` — so the body is the case split, the level, the
   induction hypothesis, the descent transported along `N = m · p`, the inclusion, the
   conclusion.

The body went from 34 lines to 14; the two private helpers are 22 lines of statement and proof
between them, and all the arithmetic in the node is inside the first. The measurement that
matters is the same one as `hall_all`'s: what remains in the body is only the mathematics of the
induction step.

The moral is the one §8 of the method note states and this case re-states: **the inversion is
recognisable from the call site, not from the statement.** A lambda that projects, applies and
transports before it can call is the signature of an interface that should have taken the
invariant and derived the projection itself.

### 7.5 The rule this arc produced

**A certificate belongs to the module whose subject it is, not to the node that happens to
state it; and its statement belongs to the consumer, not to the API.** When a caller has to
pass another theorem's proof as an argument, the interface is wrong — and the fix may be a
module boundary (a split, a move, a tier-3 home), because the dependency order *is* the
interface. The gates in
§5 apply unchanged; the one this arc added to them is the checker on every touched module:

| module | verdict |
|---|---|
| `Defs/Fields` | 24 ok, 0 missing, 0 own (wired here) |
| `SlotProduct` | 9 ok, 0 missing, 2 own |
| `Nonmembership` | 2 ok |
| `DegreeStep` | 2 ok, 1 own (the retired text) |
| `TwoPrimeSeparation` | 1 ok |
| `Capstone` | 4 ok |

## 8. Pointers

- The method, port-wide: [TOPIC-assembler-interfaces.md](TOPIC-assembler-interfaces.md) —
  symptoms, decoding procedure, the mechanism table (`private` / `own:` / tier 3 / wire).
- The Lean traps: [functionFieldGeneration/TOPIC-refactor-friction.md](functionFieldGeneration/TOPIC-refactor-friction.md)
  — instances, decomposition orientation, `rw` versus `exact`, cascades, checker names.
- The decisions and reversals with dates: [functionFieldGeneration/TOPIC-ffg-refactor.md](functionFieldGeneration/TOPIC-ffg-refactor.md)
  §13 (the interface), §14 (the second assembler and the wire), §15 (the level bounds and the
  two regularisations).
- The re-runnable check on the instance question: [`Reserve/Example/FactPrimeNeZero.lean`](../Reserve/Example/FactPrimeNeZero.lean).
