# Scoping the next ready set in the D–S cone

**Status: a recipe, not a plan (2026-10-27).** Read this before cutting the next set out of the
Deligne–Serre ready shelf. It records only what the last three scoping passes actually did — SET 3
([algebraicCurve/SET-3.md](../algebraicCurve/SET-3.md)), SET 4
([algebraicCurve/SET-4.md](../algebraicCurve/SET-4.md)) and SET 5
([algebraicCurve/SET-5.md](../algebraicCurve/SET-5.md)) — with the figures each step produced, the
instrument failures found on the way, and the rules that the failures forced. The column plan is
[../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2; the worked instance this note
generalises is [TOPIC-weierstrass-ready-shelf.md](TOPIC-weierstrass-ready-shelf.md). What it does
**not** decide: which namespace to cut next, and whether a given block of mathematics should be
ported at all — those are the reviewer's.

## 0. The read — `--ds` means without the prunable modules

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf.json
```

The things about this command, each learned the hard way.

- **`--ds` is a subtraction, not a target.** It targets
  `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` and *avoids* the complex-analytic
  Jacobian / path-integral / Abel–Jacobi / CellDissection set (`ds_prunable.py`: the substring
  patterns `CellDissection`, `pathIntegral`, `abelJacobi`, `pathPeriodLattice`, plus four exact
  names). On this cone that is **140 nodes / 74,620 lines** avoided. The report's *port cone
  (target closure)* line is the **literal** closure — 2,103 nodes / 982,173 lines — and is not the
  work figure. The work figure is `needed [F terminal]`.
- **`--include-leaves` is part of the read.** The plain `--ready` view drops graph leaves; on this
  shelf that hid **five `AlgebraicCurve` rows, ≈1,100 silo lines**, including a 925-line node
  (`Divisor.mapDomain_placeReduction_correspondence`). SET 3 cut the shelf on `--ready` alone and
  missed them; SET 4 found them. The tool's own help says to pair the two flags.
- **…and the leaves are a second block of the *report*, not just of the read.** The flag fixes the
  read; it does not fix the table. SET 4's read returned 38 `AlgebraicCurve` rows — 14 in
  `ready_rank`, 24 in `leaves_rank`, 6,901 silo — and its brief priced 14 / 4,410, silently leaving
  2,491 silo of leaf rows neither cut nor deferred. SET 5 then opened on 29 AC rows, 24 of which
  were that block. So a brief's shelf table quotes **both** block counts and their silo sums, and
  names or defers every row it does not cut (FR-0040).
- **`--ready` used to be blind to a premise inside the pruned set; it now withholds such
  rows.** The readiness test is computed on the *non-avoided* demand (the masks are keyed by
  `need`, which `--ds` has already stripped of R), so before FR-0044's fix a row that cites an
  unported R node was printed as `needed = 1` and looked ready, while its own proof had to
  traverse the pruned subject. SET 6's read had **four such rows out of 96, 831 silo** (two
  `AlgebraicCurve` rows — the `_complex` prescribed-divisor engine and the `Pic0` torsion
  finiteness — and two `ModularCurve` Tate-module rows); the leaves block had none.
  `frontier.py` now applies that audit itself: a candidate whose own proof directly cites an
  unported R premise is withheld from `ready_rank` and printed in its `withheld` block with the
  blocking premises (JSON `ready_rank.withheld`, per-row `premises_pruned`), so the shelf no
  longer shows them and the count is the one to quote. A row with such a premise is the
  prunable subject's work, not this column's; name it in the brief and defer it (FR-0044).
  Quote the withheld block next to the shelf — those are rows the shelf would otherwise have
  carried.
- **Run `--selfcheck` with the read.** It prints the nodes a `Thm_` source claims and no
  port declaration covers — **false ported markers**. They are not visible in `--ready`
  (each one hides a row from the demand) and `check_port` does not flag them (it checks the
  module's declarations against the wire, not the wire against the module). The live ones
  are registered in [spec/METADATA-ISSUES.md](../../spec/METADATA-ISSUES.md); SET 7's read
  had three, plus the `weilReciprocity` name shadow the check cannot see.
- **Read the delta, not the absolute.** The port grows between two reads: after SET 3 landed,
  `needed [F terminal]` moved **1,103 nodes / 421,670 lines → 1,090 / 419,020**, and twelve rows
  left the ready list while five entered (see §7 on new arrivals). A shelf figure quoted in a
  brief must say which read produced it.

The prunable set is a **rewiring assumption**, not a deletion: the subject is a second, redundant
supply to a step the D–S route reaches through the differentials ↔ cusp-forms transport, and the
released nodes' own premises are the subject anyway. Its rationale and its port plan are
[PRUNABLE-complex-analytic.md](PRUNABLE-complex-analytic.md) and the CellDissection topic; do not
re-derive them per set, and do not silently port something from inside `R` because it looks ready.

## 1. Reading the rows

Each `ready_rank` row carries `silo_lines` (the pin's `S_` lines for the node's whole demand — the
rank key), `premises` (pin citations; a proxy for glue risk), `premises_unported` (the direct
premises not yet ported — zero on a plain ready row, since the readiness guard leaves none),
`premises_pruned` (of those, how many lie in the pruned set R; a positive value keeps a candidate
off the plain ready shelf, §0), `leverage` / `leverage_project` (outbound demand inside the cone
and across the project), and `leaf`.

- **Rank by silo, but never drop the leaves.** Demand is inverted relative to size on this shelf:
  a 60-line leaf carried 8 project consumers and a 26-line leaf 33, while 500-line nodes carried
  1–3. The leaves are also the cheapest declarations in the set. SET 3's ten-node tail was ~430 net
  lines and unblocked the most nodes per line of anything in the wave.
- **Silo is not content.** `port_plan`'s raw → net gap was 18% in SET 3 (4,972 silo → **4,087 net
  new math lines**, after 198 dedup lines and 230 already-in-port lines) and larger where a set
  reuses a promoted engine (BC6's new module came out at 619 lines against 925 pin lines).
- **`premises` is a risk column, not a size column.** A 15-premise node is where a set stalls
  (SET 4's `genusFF_sub_one_eq_…`); give it its own order and its own wall time.

## 2. Group into stories, not namespaces

A *story* is one mathematical subject with 3–5 nodes; a set is one story. Two signals pick them
out, both mechanical:

- **The pin's own duplication is the story.** `port_advise`'s *port once* block reports names
  proved in ≥2 target files: the three `exists_constantFieldDescent*` files share a **105-line**
  prelude (`descent_abstract` 45, `isAlgebraic_of_rational_relation` 34,
  `nonempty_ringHom_complex` 26) and the same development ends in three headlines. That is one
  engine and three statements, written once.
- **A same-last-name pair with two statements is a namespace split, never a rename.** The pin
  proves `descent_abstract` (and `core`) twice; both have consumers, so both are written, in two
  sub-namespaces — the checker matches statements by hash, and the pin's own precedent for such a
  pair is a split.
- **Binder variants are not duplication.** Nine names in SET 3's set had 2–3 statements differing
  only in binders (`mem_of_ord_nonneg` in 37 pin files, `ord_nonneg_of_mem` in 36,
  `evalAt_algebraMap` in 7): take the `Theorems/` wrapper's binders, which is what the port's
  promotion already has.

## 3. Price the set before writing a sentence of the order

```bash
python3 port_advise.py --nodes <node> [--nodes <node> …] --json build/set_advise.json
python3 port_plan.py --json build/set_advise.json
```

Four sections, four decisions:

| section | what it answers | what to do with it |
|---|---|---|
| *substitute* | these statements are already in the port | import them; SET 3 had 21 (≈249 lines), BC6 imported 16 (≈400 lines) and the new module came out at 619 lines against 925 pin lines |
| *port once* | these names are proved in ≥2 target files | write once, publicly, at the pin's names |
| *generalise* | same conclusion, different binders; or same name, different statement | wrapper's binders; for the same-name pair, a namespace split |
| *drags* | what each public declaration's proof needs | a `0 helpers` row means the pin file is a flat public surface — expect no private prelude |

Three false negatives to carry: `port_advise` is **name-anchored**, so a port copy under another name
reads as "new" (the pin's `nonempty_ringHom_complex` sat in the port as
`Field.nonempty_ringHom_complex_of_countable`, and the tool said `prelude 0/23`); it does not read
mathlib at all; and it is **statement**-anchored, so a port theorem whose hypotheses are *weaker*
than the pin node's is invisible — which is precisely the theorem that decides whether a row is a
transcription or a generalisation of something the port has (SET 5's 340-line ramification-bound row
against `Place.exists_of_orderMap`: `port_advise` priced all 318 net lines as new, FR-0041). Read the
pin proof's first lines for a named engine before accepting an order's net-new figure. `--with-defs` adds the pin `Definitions/Def_*.lean` closure — worth running
once per set: in SET 3 all twelve of those modules were already ported (2,555 lines of surface
matched), which is the answer that lets a set skip the definition layer entirely. Four recorded
omissions in them (`Place.fiber_eq_fiberOver`, `Place.finite_setOf_forall_mem_and_ord_pos`,
`Divisor.mapRestrict`/`mapRestrict_single`, `AbelJacobiCard`) are in
[../../CARRY-FORWARD.md](../../CARRY-FORWARD.md).

## 4. Home by subject — but the module must sit **above** the proof's premises

This is the one rule that has cost a worker round twice (FR-0037, FR-0038). A node's home is a
mathematical decision; it is also constrained by the import graph: **every port module that holds
a declaration the pin proof consumes must be at or below the home.** Two of SET 3's three
"blocked" nodes and one of SET 4's were cycles of exactly this kind — a node whose proof opens with
weak approximation cannot live in `Defs/Divisor.lean`, which is below every approximation module.

The check is a three-step script, and **it is a first cut only**:

1. read the node's pin `S_` file `import Theorems.Thm_*` lines — its premise nodes;
2. map each premise to its port module(s) — statement-identical lookup through the checker's own
   normaliser over the port index (`twin_scan`'s `PortIndex`);
3. keep the modules above all of them in the port's import closure (a module counts as above
   *itself*), or propose a new module that imports them.

It fails in three recorded ways: a premise whose **wrapper writes its binders inline** while the
port transcribes the `S_` copy's section variables (the hash lookup misses it and the node reads
as premise-free — this is how `Defs/Divisor.lean` got ordered); a premise the port **lacks or holds
`private`** (it maps to nothing); and a **cached index** (`rebuild=True`, or map the previous
wave's tree). Falling back to last-name matching over wrapper + `S_` over-corrects — common last
names match dozens of modules. So: build the table, then **confirm each home by hand against the
pin proof's first lines**, and when a worker's diagnosis disagrees with the table, the diagnosis
is the authority.

**Legacy homes — be neutral about them.** A home in `spec/old_check_stmts.py`'s `PORT_FILES` is
*not* a reason to move the mathematics elsewhere: **if the subject demands that module, put the
declaration there and migrate the module in the same touch.** Every legacy module is going to be
migrated eventually, so the cost is paid either way — better paid at the moment a set needs the
module, when the reader and the wire are in hand. The migration is mechanical: its own `spec-pin:`
wire (one line per pin source it transcribes), deletion of the `PORT_FILES` row (its `SOURCES` rows
stay — removing a pin side can un-match other listed modules), a silent build,
`dedup.py`/`move_dead.py`, and any machine-token rectification. The one thing that *does* veto a
home is the import direction (§ above): a module below the proof's premises cannot host it, whatever
its subject — that is a cycle, not a cost.

The measured migrations of SET 3–4 (all landed this way, none of them avoided on cost grounds):

| module | its wire | checker after |
|---|---|---|
| `Defs/PlaceEvaluation.lean` | 7 sources (its pin `Def_` plus six `S_` files) | 21 ok |
| `Defs/PushPull.lean` | 6 (pin `Def_` plus the five `S_` files the promoted ord helpers come from) | 63 ok |
| `Defs/PlacesOverDVR.lean` | 1 (its pin `Def_`) | 36 ok |
| `Defs/PoleDivisorPackage.lean` | 1 | 10 ok |
| `PrincipalDivisors/Transcendence.lean` | 5 | 8 ok |
| `WeilExchange/GaloisRamification.lean` | 7 wrappers | 9 ok |
| `IsCurveOver/ConstantFieldExtension.lean` | 5 sources (two wrappers, two `S_` copies, and the separable-adjoin node) | 26 ok |

The separable-adjoin node is the worked case for the rule: it was first inserted into
`IsCurveOver/Transcendental.lean` (non-legacy) to dodge the migration, and that was the wrong
reason — its subject *is* the constant field extension, so it was moved to the legacy
`IsCurveOver/ConstantFieldExtension.lean` and that module migrated. Choose the home the
mathematics names, then pay.

**Promotions are the manager's, and they change the shelf.** When the pin states a result publicly
but the port holds it `private` — or when a later node needs it without the hypotheses the public
wrapper carries — promote it (public, at the pin's name, its own wire) instead of letting the next
node copy 150 lines: `Place.ord_norm_eq_sum_fiberOver` (45-line engine), `Place.count_normalizedFactors_span_singleton`
and `RegularProlongation.coeff_mem_of_aeval_mem_integers` (a pin node with nine consumers, carried
privately under an invented `_aux` suffix) were rescued this way. A promotion is also an
*unblocking* act: three of SET 4's fourteen ready rows became ready only because SET 3 promoted the
norm block.

## 5. The cut

- **One story per order, ~1,300–1,600 silo lines** (≈1,100–1,400 net) per dispatch. SET 4's four
  orders were 1,006 / 1,488 / 1,284 / 632; SET 3's were 950 / 1,240 / 430.
- **New module vs insertion is a price, not a preference.** A new module is cascade-free; an
  insertion edits a hub and its dependents re-elaborate. But build time is *not* a homing
  consideration: the home is chosen by subject and the import direction, then priced.
- **Check for disjoint files before dispatching in parallel.** SET 4's four orders touch disjoint
  files, so all four were safe concurrently; only the build lock is shared. Two orders editing one
  module must be serialized, and a worker must never edit a hub another order is building against.
- **Give the manager the definition layer, the promotions and the migrations**; give the worker
  the proof bodies and the transcription, with the pin file, the wrapper, the home and the gates.
- **State each order's build gate in the order**: no tree build, no dependents, the module's own
  `lake build` under `flock` and `timeout`, the checker at `0 mismatch / 0 missing`, axioms clean,
  zero warnings, no `sorry`, no marker rows.

**The surface gate — run it before believing a set is done.** A worker scoped to one headline will
often keep the node's engine `private` (a legitimate local default, and the precedent of an earlier
module may even bless it), while the pin states those declarations **public**. The cheap test is one
experiment: drop `private` from the module's declarations, run `check_port`, and read three numbers —

- every `ok` was a pin-faithful statement that belongs public: promote it (SET 4's
  `Place/EvalAtNorm` went from **2** checked declarations to **27** in one run this way, and
  `Place/ComplexDictionary` from 1 to 12);
- every `MISMATCH` is either the pin's *own* prelude copy re-spelled in the module (keep it private —
  it is a local spelling, not a duplicate) or a genuine mis-transcription (fix it);
- every `MISSING` is a port-side helper the pin does not have (keep it private).

Nothing about the proofs changes; only `private` and, where the checker objects, the statement's
spelling. Doing this at review is what keeps a set's *checked surface* equal to the mathematics it
claims to have ported.

## 6. The gates, per order

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, every added
   declaration `ok` (or an `own:`/`pin:` row in `spec/decl_markers.tsv`, which the manager writes).
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake build` under `flock`/`timeout`, and the module silent. A `Replayed` line
   is **not** evidence that its `.olean` exists — a missing one breaks any probe of an importing
   file, and the cure is to build that module explicitly (FR-0033).
4. `dedup.py` / `move_dead.py` on the module; wrapper-over-engine `shape` clusters are the pin's
   own pattern and stay, with the reason recorded.
5. A `spec/` consumer zone with a real cross-module composition (no `#check`s), whose error count
   is the deliverable metric.

## 7. After the landing — re-read the shelf

Re-run §0 and report **three** numbers: what the set consumed, what the new `needed [F terminal]`
is, and which rows **became ready because of the set** (promotions and wirings create readiness).
SET 3's landing moved the figure by 13 nodes and produced three new ready rows
(`Place.evalAt_norm_eq_prod_fiber` 672, `Place.ordDifferential_D_eq_zero_…` 517,
`genusFF_sub_one_…` 263) — which is why a shelf re-read, not a shelf memory, opens the next
scoping. Record the set's own numbers in its brief, and append the frictions to
[../../logs/frictions.md](../../logs/frictions.md) as they are hit.
