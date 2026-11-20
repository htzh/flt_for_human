# SET-AF95 — the two definition gates of the weight-one lift, and the three rows behind them

**Status: IN FLIGHT (2026-11-20).** Two waves. Wave 1 is the **definition layer** that has blocked this
family for three sets — the `AdelicSpan` carrier and the Dirichlet character on idèle classes. Wave 2
is the three rows those gates unblock. Cut: **3 rows / 2,584 silo**, plus the adelic Whittaker tail
(216) as an insertion into an existing module.

| # | order | kind | rows | silo | module |
|---|---|---|---:|---|---|
| A | the `AdelicSpan` carrier | definition layer | — | gate | `NumberTheory/LocalNewvector/AdelicSpan.lean` (new) |
| B | the Dirichlet character on idèle classes | definition layer | — | gate | `NumberTheory/RatIdele/UnitResidue.lean` (new); fixes the broken `TateLocal/DirichletIdele.lean` |
| C | the Nebentypus exists | row | 1 | 853 | `LanglandsTunnell/WeightOneLiftNebentypusExists.lean` (new) |
| D | the central character | row | 1 | 1,134 | `LanglandsTunnell/WeightOneLiftCentralScalar.lean` (new) |
| E | the converse q-expansion row | row | 1 | 597 | `LanglandsTunnell/WeightOneLiftQCoeffConverse.lean` (new) |
| F | the adelic Whittaker tail | row | 1 | 216 | `AutomorphicForm/Adelic/WhittakerUnipotent.lean` (new; **changed from an insertion** into `WhittakerPositivity.lean`, which would have been a hub edit for seven declarations) |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af95_read.json
```

| figure | before (AF94 landing) | after this set's scaffolds |
|---|---:|---:|
| `needed [F terminal]` | 449 / 215,464 | **445 / 212,664** |
| ready rows | 14 / 4,877 | **12 / 3,072** |
| leaves | 74 / 21,398 | 74 / 21,398 |
| withheld (FR-0044 guard) | 4 | 4 |

The delta is the four cut rows exactly (−4 nodes / −2,800 lines). **Two rows become ready, 995
silo**: `DihedralWeightOne.factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1`
(**921** — the conductor-`p`-adic-`K₁` row, which the new `AdelicSpan` carrier is exactly what
unlocks) and `LanglandsTunnell.weightOneLift_centralScalar_det_gen_mul` (**74**, the determinant
companion of the central-character row).

The AF subject's remaining ready block is exactly these three rows plus the two tails; the rest of
the shelf is the other columns (`WeierstrassCurve` 1,296, `GaloisRep` 495, `ModularCurve`,
`AlgebraicCurve`).

## 1. Why this set is definition work first

Three sets have deferred rows with the same reason, and the reason is now written down twice in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md):

* `Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean` (179 lines / 33 declarations) declares the
  carrier of the lift's right translates and the span they generate — the type the Nebentypus-EXISTS
  row reads the lift on. **Not one declaration of it was ported.**
* `Definitions/Def_DirichletCharacter_DirichletIdeleChar.lean` (188 lines / 25 declarations) declares
  `RatIdele.unitPadicAt`/`unitResidue` and `DirichletCharacter.dirichletIdeleChar` — the character
  the central-character row is stated with. The port's only reference to it is a module that
  **does not build** (FR-0244), which is also why that module has been dead on the tree.

So this set builds them, and the two rows behind them. Both are manager-scaffolded from their
`Definitions/` pins (statements and namespaces the pin's, `def`s and `instance`s transcribed body and
all per FR-0232) and handed to agents for the variable/import scaffolding and the proof bodies.

## 2. The homes

| module | direction | note |
|---|---|---|
| `NumberTheory/LocalNewvector/AdelicSpan.lean` | above `AutomorphicForm/Adelic/Basic`, `ArchType`, `AdelicHaar/GeneralLinear` | the *subject* is a local-newvector carrier, so it lives in the directory of that subject, not in `LanglandsTunnell` |
| `NumberTheory/RatIdele/UnitResidue.lean` | above `RatIdele/Normalizer`, `AdelicLevel/IdealBall` | next to the idèle-class machinery it belongs to |
| `LanglandsTunnell/WeightOneLiftNebentypusExists.lean`, `…CentralScalar.lean`, `…QCoeffConverse.lean` | above the AF93/AF94 preludes and the two new definition layers | one row each, the family's naming |

The three row modules are the AF94 prelude's own consumers: their `check_port` reads one `ok` per
row, and the prelude supplies the declarations the pins keep private.

## 3. The instruments

Two hard rules carried in from AF94 and written into the orders: a `check_port` **mismatch on a
statement** is a scaffold defect, to be fixed with the pin's own text (FR-0246); and the token
`spec-pin` followed by a colon must never appear in header prose, because both checkers read it as a
wire entry (FR-0247). The `move_dead` escape clause also carries AF94C's lesson: a declaration that is
dead only because the port resolved a reference differently is **reported, not deleted** — the port
must not end up holding the special case instead of the general one.

## 4. The gates

As SET-AF89–AF94 §5, unchanged, plus the note that `scaffold_audit` cannot read `complete` on a
prelude module wired to whole multi-public pins (the AF94A finding); the definition-layer modules are
the opposite case and must read `complete`, since their wire is exactly their own surface.

## 4b. The generator incident (FR-0248)

Mid-wave the AF94 scaffold generator was re-run to pick up an `open`, and it rewrote the three
**landed** AF94 modules from their scaffold templates (`WeightOneLiftLevel` 1,164 → 622 lines,
`WeightOneLiftNebentypus` 506 → 439, `WeightOneLiftQCoeff` 320 → 439), discarding their proof bodies
and header prose. Order AF95E caught it by comparing the working tree against `HEAD` (the user's
commit `e55b790`); `git checkout --` on the three paths restored them exactly, the oleans were
rebuilt from the restored sources under the lock, and the two `QCoeff` rows re-probed clean on
`[propext, Classical.choice, Quot.sound]`. Every generator in `lean/tmp/af93/` is now disarmed
(`gen*.py.used`); the rule is recorded as FR-0248: a scaffold generator is a one-shot tool, frozen
before dispatch and disarmed after landing, with `git status` as the cheap clobber check.

## 5. The landing

| order | module | lines | decls | checker | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| A | `NumberTheory/LocalNewvector/AdelicSpan.lean` | **294** | 27 named + 16 anon instances | **27 ok / 0 / 0** | clean (27 swept) | 1 pin-own | 0 / 0 | 2,000 / 1,000 |
| B | `NumberTheory/RatIdele/UnitResidue.lean` | **250** | 25 (25/0) | **25 ok / 0 / 0** | clean (25 swept) | **0** | 0 / 0 | 4,000 / 2,000 |
| B | `TateLocal/DirichletIdele.lean` (repaired) | **156** | 8 (1/7) | **1 ok / 0 / 0** | clean | — | 0 / 0 | — |
| C | `WeightOneLiftNebentypusExists.lean` | **577** | 37 (2/35) | **2 ok / 0 / 0** | clean (37 swept) | **0** | **2 decls / 7 lines — kept** (see below) | 6,000 / 3,000 |
| D | `WeightOneLiftCentralScalar.lean` | **623** | 55 (1/54) | **1 ok / 0 / 0** | clean (55 swept) | 1 pin-own | 0 / 0 | 8,000 / 7,000 |
| E | `WeightOneLiftQCoeffConverse.lean` | **635** | 31 (12/19) | **12 ok / 0 / 0** | clean (7 probed) | **0** | 0 / 0 | 25,000 / 12,500 |
| F | `AutomorphicForm/Adelic/WhittakerUnipotent.lean` | **262** | 5 (5/0) | **5 ok / 0 / 0** | clean (6 probed) | 1 pin-own | 44 ok / 0 / 0 | 8,000 / 7,000 |

**The two gates are open.** `AdelicSpan` and `DirichletCharacter.dirichletIdeleChar` are now public,
wired modules in the tree, and the two rows that waited on them are scaffolded and running.

**B did more than its brief asked, correctly.** `TateLocal/DirichletIdele.lean` was not merely
import-broken: its row body was `sorry` in a tree that is sorry-free, so silence + axioms forced the
transcription of the pin's `solution` and its seven private engines (two extra imports,
`AdelicModulus` and `ProductionPinsCompact`, and the pin's prelude opens). That module — the port of
`S_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen`, dead on the tree since before this
session — now builds, is silent and its row is `[propext, Classical.choice, Quot.sound]`.

**A's finding is a gate of its own**: the carrier's last two statements are stated over
`fixedSubmodule`/`HasNewvectorConductor` from `Def_LocalNewvector_ConductorDatum.lean`, which is
unported; A transcribed that vocabulary `private`, keeping the public surface exactly its pin's.
Registered in [CARRY-FORWARD.md](../../CARRY-FORWARD.md).

**The set's numbers**: five new modules (two definition layers, three rows), a sixth for the
Whittaker tail, and one repaired module — **2,797 lines, 0 `sorry`, no linter option**, the four cut rows consumed (**2,800 silo**) and two
rows readied (**995 silo**), leaving `needed` at **445 / 212,664**.

**C's `move_dead` is 2 declarations / 7 lines and it is correct.** `isReal_rat_infinitePlace` and
`ratArchHom` are live in the pin (their users are ported in `WeightOneLiftLevel` and in
`WeightOneAdelic`'s `RatArch` block), so they are dead in this module only because the port resolved
the reference through the prelude. That is the AF94C rule applied the other way — a *kept*
declaration with the reason in the header — and it is the first time the escape clause has been
used as written rather than discovered afterwards. Deleting them to reach 0/0 would delete pin-live
mathematics.

**F's `dedup` is 1 cluster / 38 lines and it is the pin's own.** The pin states the proposition
twice — `main` (`:67`) and `solution` (`:182`) — and both are public, so folding `main` into the row
would drop a declaration the `scaffold_audit` wire counts (it reads `complete` only because `main` is
on the surface). Kept, with the reason in the header; the same pattern as the AF93 `_impl` pair.

**E is the set's counter-example to AF94C's mistake.** Its pin carries eight engines
(`repZ_of_lt`, `repZ_last`, `coe_finComponent`, `glEq_of_forall_finComponent_eq`,
`commute_of_finComponent_eq_one`, `mapMatrix_injective`, `exists_glMap_eq`,
`exists_finComponent_eq_padicGL_map`) that AF94C had cut as dead — dead on *its* four pins, live on
this one — so E transcribed them. That is exactly the distinction the `move_dead` escape clause is
for, and it is why the clause is written into every order since.

**Two brief errors worth carrying**, both reported by the agents: the `UnitResidue` scaffolding gap
was three defects (lost `[NeZero N]`, dropped `attribute [local instance] fact_prime_of_mem_primeFactors`,
dropped `namespace DirichletCharacter` — the last had flattened nine `χ` declarations into
`RatIdele`), and the `AdelicSpan` pin declares 43 declarations, not the 33 my scaffold counted (the
16 anonymous instances are invisible to a name-keyed scan).
