# SET-AF62 — the adelic box's periodic integral, and the arch × finite factorization

**Status: LANDED (2026-11-13).** Read off the D–S shelf after SET-AF61. The
sixty-second set of the column, and its first **`NumberField` measure-theory** set: the adelic-box
pair that SET-AF53 cut at its scoping ("its statement layer needs a further import investigation") is
now on the shelf, and the arch × finite factorization of the adelic integral goes with it.

**3 rows / 452 silo / ≈430 net** in **two new modules**, two orders.

| # | row (`NumberField.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic` | 129 | 1/2 | new `AdelicBoxPeriodicIntegral` |
| **B** | `AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap` | 122 | 1/11 | same module |
| **C** | `AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral` | 201 | 1/6 | new `AdelicHaar/ArchFiniteFactorization` |

## 0. The read

| figure | value |
|---|---:|
| `needed [F terminal]` | **665 / 286,436** |
| ready rows, all namespaces | **25 / 4,887** |
| leaves, all namespaces | **183** |

## 1. What the set says

- **A** — a function periodic along the rational adeles has the same `lintegral` over the adelic box as
  over the whole adele ring: the box is a fundamental domain for `K`'s translation action.
- **B** — the conditional integral against the box of a function pulled back along `algebraMap K 𝔸`: it
  is the conditional integral over the box, by measure preservation under the rational translation and
  the fundamental-domain property of the box's preimage.
- **C** — a function on `GL₂(𝔸)` that splits as an archimedean factor composed with `glArch` times a
  finite one composed with `glFin` integrates to the product of the two integrals, the measure being a
  scalar times the product measure (SET-AF53's `exists_map_adelicGLHaar_eq_smul_prod`).

A and B are the pin's box pair; C is the same measure-theoretic layer one level up. Together they are
the adelic integral calculus the automorphic rows consume.

### 1.1 What the set does not cut

The content/height row (333), `rationalCentreUnipotent` (179), the character-matching row (113), the
Siegel-centre covering (30), the two withdrawn Tate-local rows (FR-0198 and its cap-override sibling),
`CuspForm.IsEigenformWith.fg_adjoin_qCoeff` (291, lev 1/8), `CohCarrier` (252), the `GaloisRep` and
`ModularCurve` heads, and everything else as SET-AF58 §1.1 lists it.

## 2. The price and the homes

| module | rows | lines | decls | `sorry` | `check_port` |
|---|---|---:|---:|---:|---|
| `NumberTheory/AdelicBoxPeriodicIntegral.lean` (new) | A, B | **193** | 13 | 11 | **13 ok / 0 / 0** |
| `NumberTheory/AdelicHaar/ArchFiniteFactorization.lean` (new) | C | **156** | 19 | 14 | **19 ok / 0 / 0** |

Both elaborate at the low cap, both build (3,691 / 3,698 jobs, silent), both checker-green before
dispatch. The pin's label tokens are rectified to word namespaces (`C7B17` → `PeriodicBoxIntegral`,
`FltWs24` → `CondBoxIntegral`, `Ws1`/`Ts` → `ArchFiniteFactorization`); all prelude rows are public in
the pin and stay public here, so the modules are checker-visible beyond the three headlines.

**Two scaffold findings**: the box module needs the adele ring's measurable space pinned **per module**
(`attribute [local instance] NumberField.AdelicHaar.adeleBorel` inside the section — FR-0194/FR-0196's
rule, applied again); and a module whose header carries no `spec-pin:` line reads as *unwired*
(`0 ok`), which is the checker's way of saying the wire was forgotten rather than the declarations.

## 3. The orders and the gates

Two dispatches, disjoint files: `tmp/af62/WORKORDER-AF62A-box-pair.md` and
`tmp/af62/WORKORDER-AF62B-arch-finite.md`. Gates per module: no tree build; edit loop at
`-DmaxHeartbeats=200000`; `lake build <module>` under `flock`/`timeout`; `check_port` unchanged
(**13 ok**, **19 ok**); `#print axioms` on the three headlines; zero warnings; no `sorry`; no `set_option`
beyond `autoImplicit false`; no silencer; `dedup`/`move_dead` clean; one consumer zone per order.

## 4. The shelf effect, measured (statements in)

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 665 / 286,436 | **662 / 285,984** | 662 / 285,984 ✓ |
| frontier F | 1,752 / 841,116 | **1,755 / 841,568** | +452 ✓ |
| ready rows | 25 / 4,887 | **23 / 4,539** | — |

**One row readied**: `AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup` —
the constant term's invariance under the global points (the row the box pair's periodic integral feeds).

## 5. The landing record

### 5.1 Order B — the arch × finite factorization (landed 2026-11-13)

One row, one module, **70 written proof lines** (156 → 226), 14 `sorry`s → **0**, no imports and no
`set_option` added, header byte-identical to the issued file.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `NumberTheory/AdelicHaar/ArchFiniteFactorization.lean` | 156 → **226** | 19 | 14 → **0** | 3,698 jobs, 5.2 s, silent | **19 ok / 0 / 0** | clean |

Silent at 200,000 and still at 40,000 heartbeats. `move_dead --dry-run`: 0 declarations, 0 lines.
Consumer zone `spec/NumberFieldSetAF62BConsumer.lean` (56 lines, two executed compositions: at
`∫ Φ = 0` the adelic integral vanishes; at `K = ℚ` the constant test function reads the positive scalar
off the factorization): **0 errors**.

**`dedup --within` reports one cluster, and it stays**: 12 lines, `main` (`:184`) against its wrapper
headline (`:216`) — the pin's own wrapper-over-engine pair (pin `:157`/`:191`), both frozen public API.
Recorded here as the ruling; nothing removed.

Four deviations, all proof-level: `Topology.IsEmbedding` qualified (the module's frozen `open` list has
no `Topology`, the pin's has); the eight second-countability/split proofs follow the **already-ported
SET-AF53 copy** in `ProductMeasure.L1` where it differs from the pin, because that is the form that
compiles on v4.34 — a substitute found *inside the port* rather than re-derived, which is the whole point
of porting the engine once; and `haveI`/`letI` → `have`/`let` in `main` (1 + 8), where the worker verified
by build-and-revert that the nine-instance wall is **load-bearing** (dropping the four `GL`-level
`SecondCountableTopology`/`LocallyCompactSpace` binders fails on `SFinite μa`, `SFinite μf`,
`SecondCountableTopologyEither …` — FR-0194/FR-0196's class again).

### 5.2 Order A — the box pair (landed 2026-11-13)

Two rows, one module, **99 written proof lines** (193 → 281; 88 net), 11 `sorry`s → **0**, no imports and
no `set_option` added, statements untouched.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `NumberTheory/AdelicBoxPeriodicIntegral.lean` | 193 → **281** | 15 | 11 → **0** | 3,691 jobs, 5.3 s, silent | **13 ok / 0 / 0** | **2/2 clean** |

`move_dead --dry-run`: 0 declarations, 0 lines. `dedup --within` reports one cluster (17 lines, shape
tier): headline A against `PeriodicBoxIntegral.main` — the pin's own wrapper-over-engine pair (pin
`:67`/`:122`), both public API, recorded as the ruling. Consumer zone
`spec/NumberFieldSetAF62AConsumer.lean` (4 executed compositions, two per headline): **0 errors**.

**The finding worth keeping (a new resolution of the FR-0198 class).** The pin's `main` carries
`hh : Measurable h`, and the pin's own route (`setLIntegral_comp_emb`) never spends it — so under the
port's zero-warning gate `linter.unusedVariables` fires on a *public-API* binder that may not be renamed
(that breaks the checker's statement hash) and may not be silenced. The worker did not weaken, rename or
silence: it changed the **proof** to spend `hh`, replacing the pin's measurability-free
`setLIntegral_comp_emb` step by its `Measurable`-taking sibling
(`MeasurePreserving.setLIntegral_comp_preimage` with
`T.measurableEmbedding.measurableSet_image' (measurableSet_adelicBox F)` and `hh`, after
`nth_rewrite 1 [← Set.preimage_image_eq (adelicBox F) T.injective]`). Same mathematics, statement
untouched, warning gone. That is the general answer to this class where FR-0198 had none: **look for a
sibling lemma that takes the unused hypothesis** — the pin's unused binder is often a hypothesis a
stronger sibling wants.

Further deviations, all proof-level: `regular_adelicAddHaar` routed through the port's existing lemma
rather than the pin's `unfold`; seven `haveI` → `have` on `Prop`-valued classes; one long binder line
wrapped and one unused `rintro` binder anonymised.

## 6. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf18.json
python3 ../tmp/af62/gen.py
cd .. && python3 spec/check_port.py --force FLTForHuman/NumberTheory/AdelicBoxPeriodicIntegral.lean
python3 spec/check_port.py --force FLTForHuman/NumberTheory/AdelicHaar/ArchFiniteFactorization.lean
```
