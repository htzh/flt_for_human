# SET-AF80 — the Weyl shift, and the adelic-height Weyl mass

**Status: SCAFFOLDED, DISPATCHED (2026-11-14).** The two rows SET-AF78 readied — the largest pair on the
shelf (793 + 472 silo) and the two heaviest orders the column has dispatched.

**2 rows / 1,265 silo** in **two new modules**, two orders.

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `AutomorphicForm.exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow` | 793 | 1/1 | new `AutomorphicForm/Adelic/HeightWeylMass` |
| **B** | `AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion` | 472 | 2/2 | new `AutomorphicForm/Adelic/WeylIntegrable/ShiftConvergence` |

## 0–1. The read, the rows

`needed` **587 / 265,294**, ready **21 / 5,522** (SET-AF78 §5).

- **A** is the pin's `P2mMass`/`P2mMassZeta` development — **70 public declarations**: the Weyl-transform
  mass `wn`, its height identities (`localHeight_wn`, `finLocalHeight_wn`, `adelicHeight_wn`,
  `adelicHeight_wn_rpow`), the archimedean and finite factors `archF`/`finF` with their positivity and
  comparison lemmas, the Euler-product estimates (`PW`, `logTerm`, `eulerR`, `eulerR_bounds_*`), the
  measure construction (`μv`, `μA`, `cyl`, `archConst`, `mass_identity`), the two monotonicity lemmas
  `lower_aux`/`upper_aux` and the bound `1/2` in the headline.
- **B** is 25 declarations of which two are public: boundedness of the Weyl shift and its convergence to
  the unshifted integral as the shift leaves compact sets, against a smooth atom.

## 2. The homes and the scaffolds

| module | row | scaffold | `sorry` | `check_port` |
|---|---|---:|---:|---|
| `AutomorphicForm/Adelic/HeightWeylMass.lean` (new) | A | **20** lines | 1 | **1 ok / 0 / 0** |
| `AutomorphicForm/Adelic/WeylIntegrable/ShiftConvergence.lean` (new) | B | **20** | 1 | **1 ok / 0 / 0** |

Both modules are scaffolded with the headline only — every engine declaration of these two rows is the
pin's `private` engine, and **transcribing it is the order's work** (70 and 23 declarations, ≈700 and
≈450 lines). That is deliberate: these two orders are the column's first with a load above ~400 lines of
proof per worker, and the scaffolding decision is that the statements of a fully-private engine are the
worker's transcription, not the manager's.

The manager's ground work is the vocabulary: A's header imports the adelic height (`NumberField.AdelicHeight`),
the adelic Haar (`NumberField.AdelicHaar.Adele`), the box normalization, the Weyl-integrand family; B's
imports the Weyl-integrand family, the Haar layer and SET-AF78-A's `HaarInvariance` (its premise).

## 3–4. The orders and the forecast

| order | row | content | scaffold `sorry`s |
|---|---|---|---:|
| `WORKORDER-AF80A` | A | ≈700 + 70 decls | 1 |
| `WORKORDER-AF80B` | B | ≈450 + 25 decls | 1 |

Disjoint files, two orders in parallel. Gates: the same six as SET-AF75 §3, with the load note that a
70-declaration transcription is expected to take several edit-loop rounds — the low cap is the detector,
the probe ladder is the diagnosis (FR-0217/FR-0219 are the two shapes to expect), and no `set_option`.

Forecast (joint with SET-AF79, one `--port` read, in §5 on landing): `needed` −1,265 silo, ready
**19 / 5,522**, leaves **141 / 36,643**.

## 4. The shelf effect (measured with `--port`, jointly with SET-AF79)

| figure | §0 | forecast (AF79 + AF80) |
|---|---:|---:|
| `needed [F terminal]` | 587 / 265,294 | **582 / 262,734** |
| ready rows | 21 / 5,522 | **21 / 4,877** |
| leaves | 143 / 37,308 | **140 / 36,013** |

| row readied | silo | lev |
|---|---:|---:|
| `AutomorphicForm.exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family` | 421 | 1/1 |
| `LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow` | 199 | 2/4 |

The five rows cost 2,560 silo and return 620: the pair nets −645 lines, the ready count is unchanged
(five cut, two readied), and the two readied rows are the next cut's head.

## 5. The landing

Both rows in, **71 + 17 engine declarations** and no `sorry`, two new modules plus one prerequisite.

| file | row | lines | checker |
|---|---|---:|---|
| `AutomorphicForm/Adelic/HeightWeylMass.lean` | A | 20 → **835** | **70 ok / 0 / 0** |
| `AutomorphicForm/Adelic/WeylIntegrable/ShiftConvergence.lean` | B | 20 → **455 → 427** | **1 ok / 0 / 0** |
| `NumberTheory/PrimeNormSums.lean` (new, prerequisite) | — | **≈120** | **12 ok / 0 / 0** |

**Row A is the column's heaviest order and it landed in one pass**: the pin's 71 declarations (70 engine +
the headline), transcribed in the pin's order with its two `attribute [local instance]` walls and its
statement spellings, axioms `[propext, Classical.choice, Quot.sound]` on the headline and on `main`,
`dedup` 0 clusters, `move_dead` 0. Heartbeat floors: every declaration ≤ 15 000 except
`archF_ringEquiv` (≤25 000) and `main` (≤90 000, its closing `positivity`); file-wide clean at 90 000,
83 % headroom. **Count**: the checker reports **70**, not the 71 the order asked for, and 70 is the
structural maximum — the pin's `isAddHaarMeasure_μv` is a `scoped instance`, which
`spec/lean_parser.py`'s `DECL_RE` does not index, so it is in the module but invisible to the wire.

**The brief was wrong about the definition layer, and the worker was right.** SET-AF80 §2 said "no `Def_`
work"; every `P2mMassZeta` statement is written in `NumberField.PrimeNormSum.pw`, and `pw` was not in the
port at all. The worker homed the pin's `Definitions/Def_NumberField_PrimeNormSums` prefix (12
declarations) as `NumberTheory/PrimeNormSums.lean`, kept the pin's namespace so the statement text stays
verbatim, gave it its own `spec-pin:` wire, and left every existing module untouched. That is the
definition-gate audit the recipe's §0 asks for and the manager skipped; recorded here rather than in
`CARRY-FORWARD` because it is closed.

**The dedup decision (row B).** The pin's engine carried six private declarations its own `main` never
uses, and they are the prelude the sibling row already ported **publicly** as `IntV` in
`AutomorphicForm/Adelic/LocalAtomIntegrable.lean`. Those are not "the pin's own dead lemmas" (the AF77A
case, kept) but duplicated mathematics with a live public home, so the manager dropped them
(`move_dead --select dead --apply --target /dev/null`, 6 declarations / 27 lines) and re-ran the gates:
455 → **427 lines**, edit loop silent, build silent (7.0 s), checker `1 ok / 0 / 0`, `move_dead` 0.

### The set's numbers

| figure | before | **after** | forecast (joint with AF79) |
|---|---:|---:|---:|
| `needed [F terminal]` | 587 / 265,294 | **582 / 262,734** | 582 / 262,734 ✓ exact |
| ready rows | 21 / 5,522 | **21 / 4,877** | 21 / 4,877 ✓ exact |
| leaves | 143 / 37,308 | **140 / 36,013** | 140 / 36,013 ✓ exact |

The two readied rows are the pair the forecast named
(`AutomorphicForm.exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family`,
421, and `LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow`,
199), and the pair of sets traded five rows (2,560 silo) for two (620 silo) with the read landing exactly
on the forecast.
