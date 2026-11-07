# Case study: "refactor like `hall_all`"

**Status: case note, revised 2026-11-05.** It records the node's state against its state
before the refactor (§1–§2), the gates that certify that state (§3), and the detour of
2026-11-04 as a lesson (§4). The method it instantiates is
[TOPIC-assembler-interfaces.md](TOPIC-assembler-interfaces.md); the Lean-level traps that cost
build rounds are
[functionFieldGeneration/TOPIC-refactor-friction.md](functionFieldGeneration/TOPIC-refactor-friction.md);
the decisions with their dates are
[functionFieldGeneration/TOPIC-ffg-refactor.md](functionFieldGeneration/TOPIC-ffg-refactor.md)
§13–§17. Measured on `ModularCurve.FunctionFieldGeneration`.

The short version, to be quoted at a future node: **decode the statement, ask of every binder
whether the conclusion mentions it, and where it does not, put the certificate inside the proof
rather than a better name on the binder — then leave the proof reading as mathematics.**

## 1. The node, before and after

The node is T15's descent and the one-prime reduction of `Gen`, in
`FunctionFieldGeneration/Descent.lean`. Decoded, the descent is one sentence: *under
`Hall M`, `j(q ^ M)` lies in `ℚ(j(q), j(q ^ (M p)))`*; the reduction is another: *if the
invariants hold at every level below `N`, then `modularFunctionField N` is the full divisor
field*.

| aspect | before the refactor (`bb68c72`, 2026-09-22) | now |
|---|---|---|
| the descent's statement | 16 lines: `K`, `ζ`, `hζ` and two root predicates whose types spell the pushed minimal polynomial out in full, twice | 3 lines: `(M) [NeZero M] (p) [Fact p.Prime] (hallM : Hall M)` → `jqN M ∈ modularFunctionField (M * p)` |
| what a caller supplies | a splitting field, a primitive `(M * p)`-th root of unity, and two facts about the roots of the pushed minimal polynomial | `Hall M` |
| the descent's engine | the same argument, as that statement's proof | two `private` producers stating facts about one polynomial each, and a 12-line `huniq` in the theorem's body where the two descriptions face each other |
| the slot facts that feed it (`root_shape`, `htw_of`, `hsp_of`) | private in the spine module (later `Capstone.lean`), with 75 lines of glue around them | `private` in `Descent.lean`: `slotLevel_ne_conjLevel` and `slotUnit_eq_one_of_twistLevel`, one claim per branch of the comparison |
| vocabulary for the certificate | written inline in the statement | `private`: `Lc`, `nomeAlgebra`, `x₀`, the three levels, `slotUnit` — the pushed minimal polynomial itself is gone |
| the reduction's hypothesis | two facts per factorization (`Gen M` and `jqN M ∈ F_N`), `Gen` unfolded | the induction hypothesis as the induction gives it: `∀ m < N, m ≠ 0 → Hall m` |
| the reduction's caller | an 8-line lambda, 6 of them assembling those two facts | `exact modularFunctionField_eq_full_of N ih` |
| `hall_all` | 80 lines: its `Tight` half opened with 9 lines of setup and closed with an 11-line case split over `a = 0` | 37 lines: the setup is one `obtain` from a private helper |
| modules | `Descent.lean` (252) plus the spine holding the slot machinery | one `Descent.lean`: the two producers with the certificate's root theory, the comparison, and the reduction |
| `FunctionFieldGeneration/Capstone.lean` | 337 lines | 192 lines |
| `Defs/PhiAtSlot.lean` | 243 lines, `check_port` 18 ok + 0 own | 247 lines, `check_port` 18 ok + 0 own |
| public statements of the descent | 1, carrying the certificate | 1, carrying only `Hall` |
| conclusions, hypotheses once decoded | — | unchanged |
| `#print axioms` on the capstone's four headlines | `[propext, Classical.choice, Quot.sound]` | unchanged |

Two things are deliberately the same: **the mathematics** — the same memberships, the same
field equalities, the same strong induction, the same unique-common-root argument — and **the
pin linkage** — the declarations keep the pin's names, so `jqN_div_mem_modularFunctionField` is
still what a reader arriving from
`Theorems/Thm_ModularCurve_jqN_div_mem_modularFunctionField.lean` types. What the refactor
changed is what those statements *carry*.

## 2. The current state, and why each piece sits where it does

1. **The statement takes `Hall M`, and nothing else.** `Hall M` is what the induction has at a
   divisor; the splitting field, the root of unity and the two root conditions are what the
   descent's proof *needs*. One is an argument; the rest are the proof's privates. The
   conclusion stays over `ℚ`, so the statement is readable by a reader who does not know what a
   nome is.

2. **The engine is the body.** The two producers state what each polynomial's roots are —
   `exists_phiAtSeed_roots` for the level-`p` equation, `exists_transported_minpoly` for the
   certificate — and the theorem's `huniq` makes those two descriptions face each other.
   `Polynomial.mem_range_of_unique_common_root` is then applied literally to what the producers
   deliver, so nothing sits between them and the comparison, which happens in one place and is
   visible there. The certificate's root theory — the slot product, its splitting and the
   distinctness `slot_inj` gives — is inside that producer's proof, which is its only reader;
   reading a member of the slot multiset back as an index is
   `exists_slotValue_of_mem_slotValues`, a fact about slots that names no polynomial.

3. **The arithmetic of the comparison is three named claims.** `slotLevel_ne_conjLevel` (no
   divisor of `M` is the conjugate's slot index), `slotUnit_eq_one_of_twistLevel` (the twist's
   level is the slot `(M, 0)`, so its unit is `1`) and `eq_zero_of_pow_eq_one` (`ζ`'s order kills
   a twist index below `p`). The levels they compare are the descent's own, so nothing outside
   reads them — but they must sit downstream of T19, which is why they are here and not in the
   spine where the slot machinery started.

4. **The vocabulary is private.** `Lc` (the field), `nomeAlgebra`/`nomeMap` (the two readings),
   `x₀` (the element the theorem is about), the three levels and `slotUnit`. Each is worth a
   name because the pin writes the same five-line term at each use, and none is API because the
   public statement mentions no nome.

5. **One module, named for the node, downstream of T19.** The `Hall` statement's proof needs
   the slot product, so the module that states it is downstream of both T15 and T19 — and the
   dependency order is the interface. The name is the pin's node name, and the pin's own file
   has the descent and the reduction together anyway
   (`S_ModularCurve_modularFunctionField_eq_full_of.lean`: descent 553–690, reduction 694–727).
   The engine, which needs no T19, could move upstream again if a second consumer appeared.

6. **The reduction takes the induction hypothesis as given.** `modularFunctionField_eq_full_of`
   is `∀ m < N, m ≠ 0 → Hall m → modularFunctionField N = modularFunctionFieldFull N`: the
   capstone passes `ih` unchanged, and the reduction derives a level `m < N` with `d ∣ m` and
   `N = m * p` (`exists_mul_prime_lt_of_dvd_of_ne`, private — the arithmetic of this
   reduction's own data), then `Hall m`, `jqN m ∈ F_N` from the descent, and `Gen m` from
   `Hall m`.
   The pin instead passes both facts per factorization.

7. **The caller is one line, and the capstone's other half reads as mathematics.** The `Gen`
   half of `hall_all` is `exact modularFunctionField_eq_full_of N ih`; its `Tight` half keeps
   two private helpers — the decomposition `d = M * p ^ (a + 1)` and the bound below it — while
   the `ψ` recurrence at a prime power went upstream to `NumberTheory/DedekindPsi.lean`, because
   that is standard number theory on an object the module already owns.

8. **Two by-products are shared declarations, not copies.** `mff_congr` and `full_congr`
   (transport of the two fields along a level equality) live at tier 3 in
   `Defs/Invariants.lean` — they had three private copies — and `gen_prime` (T19's substitution
   for the pin's squarefree-generation detour) sits beside the invariants it is about.

## 3. Gates

```bash
cd lean
# per edited module, in dependency order; silent output is the pass condition
timeout 110 lake build FLTForHuman.ModularCurve.Defs.PhiAtSlot                        # 4 s
timeout 110 lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.Descent
timeout 110 lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
# statements: 0 mismatch / 0 missing on every wired module in reach
python3 spec/check_port.py FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean --force   # 18 ok, 0 own
python3 spec/check_port.py FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean --force
# the register and the duplicates, for the edited modules
python3 spec/unwired_register.py --rebuild
cd ../tools/deps && python3 dedup.py --module <module> --no-json
# the four headlines, by name: functionFieldGeneration, modularFunctionField_eq_full,
# finrank_adjoin_jqN_eq_dedekindPsi, relfinrank_full_eq_dedekindPsi
#print axioms ModularCurve.functionFieldGeneration
```

`Descent.lean` is tier 3 (no `spec-pin:` wire, because its public statements are the port's own
spelling), so the register's two rows and the capstone build are its whole guarantee;
`Defs/PhiAtSlot.lean` is wired and clean. No tree build is run during a refactor (AGENTS); the
cascade from a `Defs/` edit is a reason to sequence modules, not a reason to build the tree.

## 4. Lesson learned: the detour treated a signature as a vocabulary problem

### 4.1 The symptom was a signature, not a missing word

The descent's statement before the refactor, in its first four lines:

```lean
theorem jqN_div_mem_modularFunctionField (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [Algebra ℚ K] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (htw : ∀ y : LaurentSeries K, Polynomial.eval y ((minpoly ℚ⟮jq⟯ (jqN M)).map …) = 0 → …)
```

Ten binders, five of which the conclusion never mentions, and the minimal-polynomial term
written out in full inside two of them. The diagnosis is in that last clause: **the conclusion
mentions none of the five**. A binder the conclusion never mentions carries a certificate, and
a certificate in a signature is a proof's private business on display. The statement did not
need better names for its certificate; it needed to stop taking it.

### 4.2 What was done instead

Five steps, each defensible on its own, and together the wrong answer:

| step | shape | what it bought |
|---|---|---|
| name the vocabulary | `Nome.nomeMap`, `Nome.pushedMinpoly`, `pushedMinpoly_def`, `nomeMap_qExpand` public in `Defs/PhiAtSlot.lean` | the certificate's terms became readable, and the root predicates fit on one line |
| retire the text in place | the pin's statement rewritten to use them, under the pin's name | a reader arriving from the pin finds a shorter signature |
| seal the seam | a new module `DescentFromSlots.lean` with the slot facts and a `Hall`-only wrapper `jqN_mem_modularFunctionField_of_hall` | the capstone no longer builds a splitting field |
| move the reduction to the seam module | `modularFunctionField_eq_full_of` takes the `Hall`-level descent | the caller's lambda shrank |
| record the residue | four `own:` rows in `spec/decl_markers.tsv` for the port-own public names | the checker stayed green |

Two of those steps were right in themselves — the wrapper's *interface* (`Hall M`, no `K`, no
root predicate) is exactly the final statement, and the reduction's move fixed the caller. What
was wrong was the *direction*: the certificate was made presentable instead of internal.

### 4.3 What it cost

| item | cost |
|---|---|
| public vocabulary | 43 lines in a wired module, four `own:` rows, and `check_port` at 18 ok + 4 own for a module whose other 18 statements are the pin's |
| two statements of one theorem | the `Hall`-only wrapper and the certificate-taking descent, in two modules, the wrapper's proof all certificate plumbing |
| a second module | 156 lines, created in the same commit as the second statement (`2d3fa8c`, 2026-11-04) — the duplicate statement and the extra module were one mistake |
| the caller's work | reduced only by a second wave; the wrapper itself was never what the capstone called |

None of this changed the mathematics, which is why it survived review: every gate was green
throughout. A refactor can be locally right and directionally wrong, and the gates cannot see
direction.

### 4.4 The correction

One public statement, `jqN_div_mem_modularFunctionField (hallM : Hall M)`; the certificate and
the level-`p` equation as two private producers; the comparison between their two root
descriptions in the theorem's body; the arithmetic of that comparison as three private claims
beside it; the vocabulary private too; and the seam module's content back in the node's own
module, which carries the pin's name.
The checker went **18 ok + 4 own → 18 ok + 0 own**, the register lost a module, and the
statements were untouched.

### 4.5 Rules, and the tell

1. **A binder the conclusion never mentions is a certificate, and certificates move inside.**
   Do not name it, do not wrap it: change the signature so the caller supplies the invariant
   the induction actually has.
2. **Naming a term only repairs a statement the term stays in.** The pushed minimal polynomial
   earned its definition while the engine's statement was public; once the engine went private,
   every consumer of the definition was private too, so it went private with them — and once the
   remaining consumers numbered one, the definition went as well and the term is written where it
   is used. A port-own definition needs a reason that survives the refactor it is introduced for,
   and "it appears in four statements" is not one: it is a measure of how often it would have to
   be written, not of whether a reader is served by the name.
3. **Do not state one theorem twice.** When the friendly form is what every consumer wants, it
   *is* the statement; the certificate-taking form becomes `private`, or disappears. A wrapper
   whose proof is all certificate is a second interface, not a refactor.

The tell, asked of any signature you are about to refactor:

- Does the conclusion's vocabulary appear in the signature, or only the proof's?
- Is a binder never mentioned by the conclusion? (It carries a certificate, usually a base
  change.)
- Is a hypothesis consumed in exactly one branch of one `rcases`? (It is half of something
  nameable.)
- Is a group of local facts consumed only by each other and by one or two downstream lemmas?
  (It is a helper's body — the *closure test*, the single most useful test here.)
- Does the proof contain a line that would be equally at home in a number-theory module? (It
  belongs there, with a name.)

And the treatment, in the order that works: decode the statement into one sentence; move every
certificate into the proof; then turn the proof's arithmetic into named lemmas — `private` in
the consumer when the statement is about this proof's own data, upstream when it is standard
arithmetic on an object another module owns; then re-read the proof: every line should be the
case split, the induction hypothesis, a named lemma's application, the comparison, or the
conclusion.

## 5. The same lesson one node down: the prime-power degree dispatcher

`DegreeStep.relfinrank_full_eq_mul` — "one full prime-power step has relative degree `p + 1`
when `a = 0` and `p` otherwise" — took three certificates as hypotheses (`hup`, `hall M`,
`hnm`), each of them another node's theorem, which is why its caller wrote a two-line adapter.
The final statement takes `hpM` and `hallM` only: the generation is derived from T18's
`full_eq_adjoin_full_div_prime` inside, the non-membership from T17's tower, and the caller is
one line. Two structural decisions came out of it, both worth remembering:

- **Home by subject, not by proof dependency.** `jqN_prime_not_mem_full` sat in the
  slot-product module because its proof consumed `rval_aux`; by subject it is non-membership.
  That mis-homing produced a spurious `T16 ⇒ T19` import edge — "an upstream issue" that was a
  symptom. The split that fixed it (`Nonmembership.lean` upstream, `TwoPrimeSeparation.lean`
  downstream because it consumes T16) is the same rule as §2.5: the dependency order is the
  interface.
- **A port-own public helper has exactly two lawful homes** — `private` in the consumer, or
  tier 3. Its third, "public where it is used", needs a `spec/decl_markers.tsv` row, and that
  row is for the residue, not for a convenience.

## 6. Pointers

- The method, port-wide: [TOPIC-assembler-interfaces.md](TOPIC-assembler-interfaces.md).
- The Lean traps:
  [functionFieldGeneration/TOPIC-refactor-friction.md](functionFieldGeneration/TOPIC-refactor-friction.md).
- The decisions and reversals with dates:
  [functionFieldGeneration/TOPIC-ffg-refactor.md](functionFieldGeneration/TOPIC-ffg-refactor.md)
  §13–§17 — §16 is the pass that created the wrapper and the vocabulary, §17 the correction.
- The re-runnable check on the instance question:
  [`Reserve/Example/FactPrimeNeZero.lean`](../Reserve/Example/FactPrimeNeZero.lean).
