# SET-AF106 — the reduction inputs, the Fricke equivalence, divisor reduction, the constituent's intersection, and the modular polynomial

**Status: LANDED (2026-11-27).** Five orders, ten rows, 4,882 silo, six new modules, **127 checked
declarations, none `sorry`-bearing, and no edit-loop gap** (§6.1); the shelf re-read (§7) shows the set
consumed exactly its cut and made **8 new rows ready** (3,711 silo). What follows is the brief as it was
cut. The next set of the AF column in the D–S cone, scoped per
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. **Five orders, ten rows, 4,882 silo**, six new modules, **no definition layer** (every
row's `Definitions` closure is already ported — checked). It is the shelf head after SET-AF105: **seven
of its ten rows are that set's own payoff**, and the other three are the modular-polynomial cluster the
last three sets deferred.

| # | order | rows | silo | module(s) |
|---|---|---|---:|---|
| A | the reduction inputs of the `q`-expansion modulo `ℓ` | 1 | 1,236 | `ModularCurve/Reduction/QExpModL.lean` (new) |
| B | the Fricke involution as an algebra equivalence on `X_H` | 1 | 1,105 | `ModularCurve/XH/FrickeAlgEquiv.lean` (new) |
| C | divisor reduction and the valuation-subring section | 3 | 859 | `AlgebraicCurve/DivisorPlaceReduction.lean` (new) |
| D | the cuspidal constituent's intersection with the level `archCut` piece | 2 | 882 | `AutomorphicForm/Adelic/Cusp/ConstituentIntersection.lean` (new) |
| E | the modular polynomial's Hasse descent, and the `Γ₀` index bound | 3 | 800 | `ModularCurve/ModularPolynomialHasseDescent.lean` (new), `ModularCurve/Gamma0DedekindPsi.lean` (new) |
| **total** | | **10** | **4,882** | 6 new modules |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' <the 21 selfcheck names>) > build/shelf_af106_read.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **302 / 166,004** |
| ready rows | 20 / 6,395 |
| leaves | 16 / 15,007 |
| withheld (FR-0044 guard) | 4 / 831 |

SET-AF105's landing read, reproduced exactly. The shelf's head is now almost entirely SET-AF105's
payoff: **A, B, C's 629-row and D's two rows are all rows that set made ready** (its §7 lists them), and
E's three are the deferred modular-polynomial cluster. The two biggest ready rows (1,236 and 1,105) have
never been touched by a set; the rest of the ready block (the `TateCurve` tail, `ValuationSubring`'s two
rows, `ModularCurve.exists_sum_smul_eq_…`, `rep_tateModule_jOne_comm`) stays on the shelf (§5).

## 1. The stories

### A — the reduction inputs of the `q`-expansion modulo `ℓ`

`ModularCurve.reductionInputsQExpModL_of_finrank_le_of_genusFF_eq` (**1,236** silo, 8 premises, def
layer `ModularCurve_QExpReductionModL` 338 pin lines — **ported** as
`ModularCurve/Defs/QExpReductionModL.lean`). The row packages the reduction dictionary of the
`q`-expansion: `qExpModL` on the `q`-expansion ring, its compatibility with the function field's residue
dictionary, and the integrality of the coefficients under a `finrank ≤ genusFF` hypothesis. It is the
hypothesis package the modular-representation arguments consume — the reduction of `ρ` mod `ℓ` and its
semisimplicity (SET-AF105D's criterion) take their inputs from here.

Home `ModularCurve/Reduction/QExpModL.lean`, beside `Reduction/EquivariantTorsion.lean` (AF103A), above
`ConstantReductionQExp.lean`, `Defs/QExpReductionModL.lean`, the degree glue, the `jq`-integrality and
AF105C's `RegularProlongationRetraction.lean`.

### B — the Fricke involution as an algebra equivalence on `X_H`

`ModularCurve.exists_frickeAlgEquiv_xHFunctionFieldBar` (**1,105** silo, 5 premises, def layer
`ModularCurve_XHOperators` 133 pin lines — **ported** as `ModularCurve/XH/Operators.lean`). The Fricke
(Atkin–Lehner) involution `w_N` on `X_H`'s function field: the algebra equivalence whose `q`-expansion
effect is the Fricke slash, and which therefore implements the Atkin–Lehner symmetry of the Hecke algebra
on the function field rather than only on the analytic model.

Home `ModularCurve/XH/FrickeAlgEquiv.lean`, in the `XH` family (`XH/{Inputs,FrickeGalois,Operators}.lean`).

### C — divisor reduction and the valuation-subring section

Three rows, **859** silo: `Divisor.mapDomain_placeReduction_eq_ord_of_retraction` (629, **15
premises**), `RegularProlongation.exists_eq_integers_of_forall_mem_adjoin_iff_of_sum_finrank_eq_of_isAlgClosed`
(196), `exists_valuationSubring_section_of_constantField_valuationSubring` (34). One subject: *places and
divisors over a constant field extension, and how they compute* — the retraction of the regular
prolongation makes `mapDomain` commute with place reduction, the prolongation with prescribed `integers`
is obtained from the adjoin criterion plus a finrank count, and every valuation of the constant field
extends.

Home `AlgebraicCurve/DivisorPlaceReduction.lean`, above the `RegularProlongation*` family (AF105C's
`RegularProlongationRetraction.lean` is a premise) and the constant-field-extension calculus.

### D — the cuspidal constituent's intersection

Two rows, **882** silo: `exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent`
(650) — a cusp constituent is topologically generated by the right convolutions of one level-spherical
eigenvector, which is SET-AF105B's real-eigenvalue row applied to the constituent; and
`map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed` (232) — an irreducible closed cuspidal
subrepresentation maps its own intersection.

Home `AutomorphicForm/Adelic/Cusp/ConstituentIntersection.lean`, beside `Constituent.lean`,
`ConstituentModulus.lean`, `SpectrumConstituentClosure.lean` and AF105B's
`LevelSphericalEigenvector.lean`.

### E — the modular polynomial's Hasse descent, and the `Γ₀` index bound

Three rows, **800** silo: `StarBank.hassePolyDescent` (407) — the modular polynomial's coefficients from
level one's `E₄³/Δ` `q`-expansion and its Hasse derivatives; `ModularPolynomialData.eq_all` (75) — the
data bundle is determined by its `q`-expansion and finrank; `card_quotient_gamma0_le_dedekindPsi` (318) —
`Nat.card (Γ₀(N) \\ SL₂(ℤ)) ≤ dedekindPsi N`.

This is the cluster SET-AF104/105 §5 deferred as "splits by subject"; the split is made here by module
(the Hasse descent and the uniqueness in one, the index bound in the other) while keeping it one order,
because each half alone is a ~400-line dispatch.

## 2. The scaffolds

Six modules exist before any order starts, each with its header prose, its `spec-pin:` wires, a narrow
import list, the headline declarations at the wrapper's statements, and body `sorry`. All six elaborate
at the 200 k cap, silent but for their `sorry`s, and are built:

| order | module | scaffold `check_port` |
|---|---|---:|
| A | `ModularCurve/Reduction/QExpModL.lean` | **1 ok** |
| B | `ModularCurve/XH/FrickeAlgEquiv.lean` | **1 ok** |
| C | `AlgebraicCurve/DivisorPlaceReduction.lean` | **3 ok** |
| D | `AutomorphicForm/Adelic/Cusp/ConstituentIntersection.lean` | **2 ok** |
| E | `ModularCurve/ModularPolynomialHasseDescent.lean` | **2 ok** |
| E | `ModularCurve/Gamma0DedekindPsi.lean` | **1 ok** |
| **total** | | **10 ok / 0 / 0 / 0** |

Wave build of the six: `Build completed successfully (5093 jobs)`, no non-`sorry` warning from any of
them; the set-level collision probe (`lean/tmp/af106/collision-probe.lean`) is **silent** — run before
dispatch, as SET-AF105 taught (a `Definitions` port can collide with an already-public declaration, and
no per-module gate sees it).

## 3. The pricing

`port_plan` on the ten rows:

| figure | value |
|---|---:|
| raw `S_` lines | 4,882 |
| declaration lines | 4,608 |
| duplicate copies | 22 |
| boilerplate | 274 |
| distinct declaration groups | 324 |
| **already in the port (vetted)** | **2,000** |
| **net new math lines** | **2,586** |
| substitutions | 144 trusted / 5 suspect |

**This is the cheapest set in the column per silo** — 2,000 of its 4,608 declaration lines are already
public in the port, because these rows are the *consumers* of SET-AF103/104/105 and their engines were
ported as part of those sets. The concentration is the pricing's real content: **order B has 70 rows /
635 lines in the port** (the whole `XH` operator engine), **order A 42 / 447**, order D 13 / 369, order
E 7 / 381, order C 5 / 224. So every order's first task is a substitution pass, and the brief's expected
`check_port` sizes are deliberately not given — they are a measurement (§6), not a prediction.

The **five suspects** are the parser's type-only `def` matches, all of the SET-AF105 `G`/`H` shape
(`ratioField → modularFunctionField`, `frickeGL → AtkinLehnerDatum.alGL`, `appendFamily →
archTypeFamilyJoin`, `delta → JOneES.A12`, `gensF → QExpDeuring.gensZ`) — read each body, one name at a
time (FR-0311).

## 4. The gates

Per order, as [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
§6: `check_port` **0 mismatch / 0 missing / 0 own** with every declaration `ok`; the engine diff; `#print
axioms`; the silent edit loop and one locked `lake build`; `dedup.py --within`; `move_dead.py --dry-run`;
a heartbeat probe pair recorded and **not installed**. The two house policies of SET-AF104/105 carry
unchanged (the low-cap probe ladder for any heartbeat site; the surface gate at review), and the
frictions list in the work order's preamble now has six entries (FR-0266, FR-0306–FR-0311) that this
set's pins can hit.

## 5. Not cut — named and deferred (FR-0040)

* **`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary` (951)** — still the one single-row
  `ModularForm` story; it wants an order of its own and a `ModularForms` home, and it is not a consumer
  of anything this set lands.
* The **`TateCurve` tail** (`sOne_eq_tsum_xfun` 101, `pointX/pointY_zpow_mul` 22 + 22, `defectCoeff_zero`
  13) and the two points-law leaves (471 + 247) — one subject with its deferred definition layer.
* **`ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one` (75)**,
  **`exists_polynomial_map_residue_ne_zero_eval_mul_mem` (42)**,
  **`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36)**,
  **`ModularCurve.rep_tateModule_jOne_comm` (24)**,
  **`ModularCurve.exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials`
  (227)** — each is small and belongs with a subject that another order of this set is not.
* The `NumberField.*` leaves (~1,600), `WeierstrassCurve.{stepCurve_stepSubgroup_two_eq}` (231) and
  `…veluQuotient…` (194), `MeasureTheory.Lp` (148), `M4aTorus.completedRayL_fe` (12,126) — unchanged
  from SET-AF105 §5.
* Withheld by the FR-0044 guard: the same four rows.

## 6. The landing

**C landed (2026-11-27).** `AlgebraicCurve/DivisorPlaceReduction.lean`, **890 lines**, 0 `sorry`,
**26 ok / 0 / 0 / 0**; engine diff 33 pin rows → 26 declarations, **26 by hash, 0 unaccounted**; axioms
clean on 26/26; silent with **10× headroom** (first failure at 10,000); locked build 18 s, 0 warnings;
`move_dead` 0/0; one `dedup` cluster (the pin's own 3-line `ratAlg` prelude in three declarations). The
order's sequencing paid exactly as written: the 34-row is a **six-line** proof because AF105C's retraction
matches the pin component-for-component, and the 15-premise 629-row's premise set **was usable as
stated** — the set's named risk did not bite.

Two decisions, both recorded in the module header: the 12-line local `have hformula` **stays for now**
and the promotion it points at is registered (below); and **`GST.Rebase` stays at the pin's namespace** —
it is the pin's own namespace (one pin file, four declarations), not a pipeline label, so the naming
policy keeps it as it keeps `CasCore`, and the checker is namespace-blind either way.

**D landed (2026-11-27).** `AutomorphicForm/Adelic/Cusp/ConstituentIntersection.lean`, **949 lines**
(2 public + 36 `private`), 0 `sorry`, **2 ok / 0 / 0 / 0**; engine diff 42 pin rows → 38 declarations,
**35 by hash, 0 hash-mismatched, 3 documented restatements**; axioms clean; silent with ~47 k of 200 k
used (first failure at 45,000); locked build 35 s, 0 warnings; `dedup` 0; `move_dead` 0/0.

D's substitute pass is the set's most instructive negative: of 11 helper rows, **2 were imported and 9
transcribed because the port holds them `private`** — a `private` port declaration is not a substitute,
which is the preamble's rule paying off as a measurement. The surface probe reads 36 ok, and the
**promotion was declined on principle**: eight of the 36 already exist `private` in
`Cusp/ArchTypeSubmodule.lean`, so promoting this module's copies would publish a second copy of the same
mathematics at root level. The clean move — promote them in the arch-type module and import — is a hub
edit, registered in CARRY-FORWARD (§7's shelf is not the only thing a set moves).

D also carries the pin's `backward.isDefEq.respectTransparency false` on seven declarations. **Kept**,
because it is the pin's option, the port has precedent (`RepTheory/BiIsotypic.lean`, five scoped uses),
and it is elaboration semantics rather than a budget — without it `map_mem_typeSubmodule`'s
`rw [LinearEquiv.apply_symm_apply]` is not type-correct at implicit transparency, which is **FR-0309**'s
class. The proper cure (state the term in the shape `rw` needs) is a refactor-round option; the option
stays scoped, never file-wide.

**E landed (2026-11-27).** `ModularCurve/Gamma0DedekindPsi.lean` (**110 lines**, **1 ok**) and
`ModularCurve/ModularPolynomialHasseDescent.lean` (**462 lines**, 10 declarations, **10 ok**); both
`sorry`-free, silent, clean locked builds, axioms clean on 11/11, `dedup` 0, `move_dead` 0/0. The
`dedekindPsi` row is the two-step bridge it was priced as (`Gamma0_index` + the imported `dedekindPsi`,
never restated), and its private bridge `card_quotient_gamma0_eq_index` stays `private` — the pin-faithful
size is **1**, not the 2 the surface probe shows. The Hasse-descent module found **5 real substitutions**
(so `eq_all` is the pin's eleven lines and `hassePolyDescent` is its own 300-line proof text).

E's three deferred findings are in CARRY-FORWARD: an **unclaimed node**
(`ModularCurve.qExpansion_div_mem_laurentBaseChange`, 65 silo, whose 240-line `AHBridge` engine sits
inside the psi pin's `S_` file and is ported nowhere — a real gap the frontier cannot show), a **homing
move** (`eq_all`'s subject is the uniqueness module, which already wires that node), and a **one-word
duplicate** (`W1.algebraMap_laurent_eq_single` is the `Defs/Laurent.lean` lemma in weaker generality, so
widening the `Defs/` copy retires it).

**A landed (2026-11-27).** `ModularCurve/Reduction/QExpModL.lean`, **736 lines**, 54 declarations,
0 `sorry`, **54 ok / 0 / 0 / 0**; engine diff wire 97 → 54 declarations, **54 by hash, 0 unaccounted**;
axioms clean on 54/54; silent at 200 k with ~2× headroom (red at 100,000, three of the red sites
statement-only at 50,000); locked build 32 s, 0 warnings; `dedup` 0; `move_dead` 0/0. Its substitution
pass reproduced the priced figure **exactly**: 42 rows / 447 pin lines imported. Two findings:
`gensF → QExpDeuring.gensZ` is **not** substitutable (the pin's set is integral-*Laurent* and really has
negative exponents; `gensZ` is integral-`q`-expansion) — transcribed; and the pin threads
`hT : ModularGroup.T ∈ Γ` through its *definitions*, which makes ~35 assembly names both unmatched and
unimportable (**FR-0313**, cured by two `abbrev` aliases that forget `hT`). The headline's `Module.Free`
site is red at the default 20 k and green at 40 k, and the module **supplies the instance by hand**
(`Module.Free.of_divisionRing`) instead of raising a cap — the pin's `synthInstance.maxHeartbeats 1600000`
is that site and only that site.

**B landed (2026-11-27).** `ModularCurve/XH/FrickeAlgEquiv.lean`, **673 lines**, **34 ok / 0 / 0 / 0**;
engine diff 108 pin rows → 37 declarations, **35 by hash, 0 by name, 2 unaccounted** (two `private`
adapters); axioms clean; silent at 200 k but the set's **tightest module** (floor between 100,000 and
200,000); locked build 29 s, 0 warnings; `dedup` 0; `move_dead` 0/0. Its substitution is the set's
deepest: **63 of 71 matched rows imported**, 4 re-declared because the port's copy is `private` or only a
binder-shape match, plus 6 more the matcher missed. **Both advise suspects were rejected after reading
the bodies** (FR-0311): `ratioField → modularFunctionField` is type-only and `frickeGL →
AtkinLehnerDatum.alGL` is the same matrix at a different hypothesis. The floor's cause is a port-vs-pin
**shape** difference, not a defect: the port's `abbrev xHFunctionField` over `def xHFunctionFieldC`
where the pin has one `def`, so the two spellings are only default-transparency defeq — **FR-0312**,
recorded with both cures (instantiate the rewrites, which landed; or align the spelling in the hub,
which is registered as optional in CARRY-FORWARD).

## 6.1 The landing table

| order | module(s) | lines | checker | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---:|---|---|
| A | `ModularCurve/Reduction/QExpModL.lean` | **736** | **54 ok / 0 / 0** | 54 clean | 0 | 0 / 0 | 150,000 / 100,000 |
| B | `ModularCurve/XH/FrickeAlgEquiv.lean` | **673** | **34 ok / 0 / 0** | 34 clean | 0 | 0 / 0 | **200,000 / 100,000 (floor 100–200 k, FR-0312)** |
| C | `AlgebraicCurve/DivisorPlaceReduction.lean` | **890** | **26 ok / 0 / 0** | 26 clean | 1 (the pin's own `ratAlg` prelude) | 0 / 0 | 20,000 / 10,000 |
| D | `AutomorphicForm/Adelic/Cusp/ConstituentIntersection.lean` | **949** | **2 ok / 0 / 0** (36 on the surface, **not** promoted) | 2 clean | 0 | 0 / 0 | 50,000 / 45,000 |
| E | `ModularCurve/ModularPolynomialHasseDescent.lean` | **462** | **10 ok / 0 / 0** | 10 clean | 0 | 0 / 0 | 20,000 / 15,000 |
| E | `ModularCurve/Gamma0DedekindPsi.lean` | **110** | **1 ok / 0 / 0** (2 on the surface) | 1 clean | 0 | 0 / 0 | 1,000 / 500 |
| **set** | **6 new modules** | **3,820** | **127 ok / 0 / 0 / 0** | 127 clean, no `sorryAx` | 1, recorded | 0 / 0 | **0 edit-loop gaps** |

The set-level gates, run by me on the landed tree: **wave build** `Build completed successfully (5165
jobs)` with no non-`sorry` warning from any of the six; the **collision probe** over all six silent; and
`spec/SetAF106Consumer.lean` with three zones (the modular polynomial's datum is a `Subsingleton`; the
`Γ₀` index bound at level one; and a consumer-shaped elimination of the datum via the two composed).
Unlike SET-AF105, this set's consumer cannot exercise A/B/C/D's headlines at all: they are 10–20 binder
telescopes over the whole reduction/Fricke/place machinery, so a consumer zone would restate the
statement — the same judgement SET-AF105 §6.1 made for its C and D2, and the reason the zones here are
E's three.

**No edit-loop gap**, for the second set running: every module is silent at the 200 k detector. B is
the tight one (floor 100–200 k) and its cause is diagnosed and registered; nothing is installed in any
module — no `maxHeartbeats`, no `synthInstance.*`, no `attribute [-]` wall, no `sorry`.

One process note worth carrying: **D's module was broken by my own header edit and the checker did not
see it.** Appending the review decisions by replacing the first `set_option autoImplicit false` put the
prose *after* the header comment, and `check_port` still read 2 ok because it is a text instrument — the
wave build caught it (`unexpected token '#'`) and it was repaired in one edit (**FR-0315**: after a
header-prose edit, run the edit loop, not just the checker).

## 6.2 Plan vs actual

| figure | plan (§3) | actual |
|---|---:|---:|
| rows / orders | 10 / 5 | 10 / 5 |
| silo | 4,882 | 4,882 |
| written lines | net-new 2,586 | **3,820** (+48% over the net-new, **−22% under the silo**) |
| modules | 6 | 6 |
| checked declarations | not predicted (deliberately) | **127** |
| recorded edit-loop gaps | 0 predicted | **0** |

This is the first set whose **written lines came out *below* its silo** — 3,820 against 4,882 — which is
what a genuinely cheap set looks like: 2,000 lines were already in the port and 127 declarations are the
whole surface (the pins' engines are largely imported, so the written text is the *statements* plus the
gaps). And it is the third set running where the `port_plan` **net-new** figure under-predicted the
writing (2,586 against 3,820): the substitutions are real, but a substitution still costs the module a
*statement* (B's 4 re-declared rows, A's `gaussRing`, C's 26 declarations), and the net-new figure
counts proof text only. The lesson is now stable enough to state as a rule: **price a port by its silo
and its statement count, not by its `port_plan` net-new** — the net-new answers "how much proof is
left", which is not the same question as "how much module must be written".

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' <the 20 selfcheck names>) > build/shelf_af106_final.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` (corrected read) | 302 / 166,004 | **292 / 161,122** |
| ready rows | 20 / 6,395 | **18 / 5,224** |
| leaves | 16 / 15,007 | 16 / 15,007 |
| withheld (FR-0044 guard) | 4 / 831 | 4 / 831 |

The delta is **−10 nodes / −4,882 lines**, *exactly* the cut. **Eight rows became ready (3,711 silo)**:
C's two biggest payoff rows
(`RegularProlongation.exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq` **1,116**,
`Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le` **687**), the
`Pic0.freeAlgebra_lift_correspondence_eq_zero_of_baseChange` (**532**), the
`Divisor.finrank_riemannRochSpace_le_…mapDomain_placeReduction` (**510**), `ModularCurve.StarBank.starBank`
(**453**, E's consumer), `RegularProlongation.forall_exists_residue_eq_algebraMap_…` (**276**),
`CuspidalSpectrum.map_inf_orthogonal_eq_bot_or_le_of_isIrreducibleCuspSubrep` (**107**, D's consumer) and
`exists_constantReduction_of_constantFieldExtension` (**30**). C is the productive order by this measure:
four of the eight are its consumers.

**The correction list is now 20 names, not 21, and the set is what changed it.** `--selfcheck` reports
20 false ported markers after this set instead of 21: **`ModularCurve.ModularPolynomialData.eq_all` is no
longer one of them**, because E's module genuinely declares it (`check_port` reads it `ok` against
`Theorems/Thm_ModularCurve_ModularPolynomialData_eq_all.lean`). Quoting the *stale* 21-name list
understates the landing by exactly that row — the read on the old list is 293 / 161,197 with `eq_all`
still sitting in the ready block, i.e. the correction forces a genuinely ported row back onto the shelf.
**The list is the `--selfcheck` output of the current tree, never a stored copy**: it shrank once here and
will shrink again as the MD-005 phi-refactor block lands. The 20-name list used above is saved at
`lean/tmp/af106/unport20.txt` — and this is the point the scoping recipe makes about quoting *which*
marker set produced a figure.

## 8. What the set leaves behind

Six modules and no definition layer, which is what "the consumers of the last three sets" look like: the
reduction inputs (`ModularCurve/Reduction/QExpModL.lean`), the Fricke equivalence (`XH/FrickeAlgEquiv.lean`),
the divisor/place reduction (`AlgebraicCurve/DivisorPlaceReduction.lean`), the constituent's intersection
(`Cusp/ConstituentIntersection.lean`), and the modular polynomial's descent plus the `Γ₀` index
(`ModularPolynomialHasseDescent.lean`, `Gamma0DedekindPsi.lean`).

Five things carried beyond the files:

* **the port's engine is now mostly the consumers' own:** 2,000 of 4,608 declaration lines substituted, and
  **127 checked declarations** for 4,882 silo. This is what the column looks like once three sets of
  engines are in place, and it is the argument for reading a shelf by *statements* rather than by silo
  (§6.2's rule).
* **four new frictions, all about the machinery rather than the mathematics**: **FR-0312** (a port-side
  `abbrev` where the pin has a `def` doubles statement costs and blocks `rw`), **FR-0313** (a pin that
  threads an unused section variable through its definitions makes its assembly surface unimportable),
  **FR-0314** (`port_advise`'s generic-last-name filter makes its substitution count a lower bound) and
  **FR-0315** (`check_port` is a text instrument: a header-prose edit that lands outside the comment is
  invisible to it — which cost one wave build here).
* **three deferred items in CARRY-FORWARD**: D's eight arch-type helpers (promote in the arch-type
  module, not here), C's hypothesis-free norm formula (**MD-008** in the metadata register — a wired node
  held `private`, so it reads as ported and cannot be imported), E's unclaimed `qExpansion_div_mem_…`
  node with its 240-line engine inside another pin's `S_` file, and B's optional `XH/FunctionField.lean`
  spelling alignment.
* **the surface gate declined twice and accepted once, deliberately**: declined for D (its eight
  duplicates have a private home) and for E's bridge (a port-side adaptation, not pin mathematics);
  accepted implicitly everywhere else by keeping the pin's visibility.
* **the consumer zones are E's three, and that is a statement about the set**: A/B/C/D's headlines are
  10–20 binder telescopes, so a zone would restate the theorem. The honest form of the gate for such a
  set is the per-order engine diff (§6.1), which is 127/127 by hash with 0 unaccounted.
