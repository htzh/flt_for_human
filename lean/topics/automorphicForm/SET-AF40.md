# SET-AF40 — the idèle product-measure layer, and the Borel Haar disintegration it unblocks

**Status: LANDED 2026-11-08** — §1 the def layer, §2 the row, §3 the forecast, §4 the landing record. This set exists because SET-AF39 §1 **deferred** the Borel Haar
disintegration row: its conclusion mentions `NumberField.Idele.idelicHaar`, and the port had no idèle
product-measure layer at all.

## 1. The definition layer (the manager's, as the instructions require)

`Def_NumberField_IdeleProductMeasure` turned out to be the *bottom* of a three-module chain, because its own
imports were unported too. All three are now in the port, wired by their own `spec-pin:` headers:

| module | pin source | declarations | `check_port` |
|---|---|---:|---|
| `NumberTheory/NumberField/UnitIdelesOutside.lean` | `Def_IsDedekindDomain_FiniteUnitIdelesOutside` | 7 | **7 ok** |
| `RepTheory/LocalLanglands/UnramifiedWhittakerZetaIntegrand.lean` | `Def_UnramifiedWhittaker_ZetaIntegrand` | 2 (`zetaIntegrand`, `ProductMeasureData`) | **2 ok** |
| `NumberTheory/NumberField/IdeleProductMeasure.lean` | `Def_NumberField_IdeleProductMeasure` | **64** | **42 ok + 1 own** (the 21 pin-`private` declarations are invisible to the checker) |

Plus two declarations added to the existing `NumberTheory/NumberField/FiniteIdeles.lean`
(`finiteUnitsComponent`, `val_finiteUnitsComponent`, the pin's `Def_NumberField_IdeleBox:106/116`), which
brings that module to **7 ok**.

**Landed** (order AF40A, 2026-11-08): `IdeleProductMeasure.lean` is **694 lines, 0 `sorry`, `check_port`
42 ok + 1 own**, **`#print axioms` clean on all 43 public declarations**, module build silent, `dedup`
0 clusters, `move_dead` 0. The manager wrote the twelve *definitions*; the order wrote the 53 bodies in
**525 lines** (block sizes: `ord`/`unitComponent` 36, projections 54, `S`-part/unfold lemmas 131,
factorization & `diagOne` 61, measure layer 54, disjoint union 57, the Tonelli identity **117**,
`productMeasureData` 15 — the last one verbatim).

**Adaptations: exactly one real one.** `ord_eq_zero_iff` (pin `:143`) cites
`FiniteAdeleRing.integer_and_inv_integer_iff_valuation_eq_one`, a pin-local lemma of
`Def_NumberField_IdeleBox.lean:29` that the port does not hold (IdealBall is the level-`N` lattice section
only); its own pin proof is inlined as a local `have key` and the pin's remaining 12 lines are verbatim.
Two mechanical v4.34 renames account for the other 13 textually-different bodies (`if_pos`/`if_neg` →
`ite_eq_left`/`ite_eq_right` in 12, `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` twice inside the Tonelli
body, which is otherwise verbatim). Nothing else moved.

**One consumer-side note**: `productMeasureData`'s *type* mentions `ideleBorel F`, and the module's
`attribute [local instance]` is local, so any consumer must re-install `ideleBorel`/`borelSpace_ideleBorel`
before using it (the set's consumer does). Registering the instance globally would make the Borel structure
the default `MeasurableSpace` on `(𝔸_K)ˣ` for the whole downstream tree — the pin keeps it local, and so
does the port.

**The one `own:` row**: `truncFin_eq_mapAlong`, whose statement carries an inline proof term that the pin
writes with the now-deprecated `if_pos`/`if_neg` (the port writes `split_ifs`); only that
proof-irrelevant term differs. Registered in `spec/decl_markers.tsv`.

## 2. The row it unblocks

`AutomorphicForm.exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant` — the Haar
measure of the adèlic Borel, disintegrated:

`∫⁻ b, F b ∂μB = c · ∫⁻ x ∫⁻ u ∫⁻ t, F (n(x) · z(u) · diag(t)) · ‖t‖⁻¹`

for every locally finite, open-positive, left-invariant `μB` (429 pin lines / 36 declarations). This is the
measure-theoretic Iwasawa decomposition of `B(𝔸_K)` — the standard first step of every unfolding argument.
Its scaffold is **created and checker-green** (`AutomorphicForm/Adelic/BorelHaarDisintegration.lean`,
**1 ok**), which is the check that the def layer did what it was for: before §1 the row could not even be
*stated*. The proof is order **AF40B**, dispatched once AF40A is sorry-free (the proof consumes
`idelicHaar`'s Haar property, which is one of AF40A's bodies).

## 3. Forecast

The def layer moves no graph node (a `Def_*` module is not a node), so `needed` is unchanged by §1. The row
is 429 silo:

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 743 / 310,075 | **742 / 309,646** |
| frontier F | 1,673 / 817,301 | **1,674 / 817,730** |
| ready rows | 51 / 9,600 | **50 / 9,171** |
| leaves | 200 / 50,557 | 200 / 50,557 |
| `AutomorphicForm` demand | 261 / 114,219 | **260 / 113,790** |

## 4. The landing (2026-11-08)

| order | module | lines | declarations | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| **40A** | `NumberTheory/NumberField/IdeleProductMeasure.lean` | 694 | 64 (43 public, 21 pin-`private`) | **42 ok + 1 own** | 3,663 jobs, silent | 43/43 clean |
| **40B** | `AutomorphicForm/Adelic/BorelHaarDisintegration.lean` | 532 | 49 (33 transcribed helpers + 12 `scoped instance`s + the headline) | **1 ok** | 3,724 jobs, silent | clean |

Consumers `spec/NumberFieldSetAF40AConsumer.lean` and `spec/AutomorphicFormSetAF40BConsumer.lean` — 0
errors each, real compositions (the trivial `L = []` decomposition of `productMeasureData`; the Borel
identity read at `F = 1_U`, at `U = univ`, and as a vanishing criterion). No promotion, no migration, no
legacy touch, no tree build.

**40B's accounting**: 466 of its 533 lines are declaration bodies; of the pin's 36 declarations one is
**reused** (the port's `continuous_unipotentGL2` is the general `{R} [CommRing R] …` form), and the 13 named
`scoped instance`s keep the pin's exact form — the shared parser ignores them on both sides, which is why
`move_dead` reports 15 declarations as "dead" (they are reached only from those instance terms). Twelve
`haveI : <class> :=` became named `have`s (the v4.34 `haveILetI` linter) and one mathlib drift
(`Measure.map_smul` now takes its `AEMeasurable` argument) is the only proof-level change outside that.

**What the two orders consumed**: the def layer 810 pin lines in ~810 written lines (plus the two small
modules), the row 429 silo in 532 lines. Three new imports in 40B, each the port home of one of the pin's
own `Theorems/` imports, all reported.

### 4.1 The re-read, and one operational note

| figure | before | forecast | **actual** |
|---|---:|---:|---:|
| `needed [F terminal]` | 743 / 310,075 | 742 / 309,646 | **742 / 309,646** ✓ |
| `needed [literal]` | 755 / 313,540 | 754 / 313,111 | **754 / 313,111** ✓ |
| frontier F | 1,673 / 817,301 | 1,674 / 817,730 | **1,674 / 817,730** ✓ |
| ready rows | 51 / 9,600 | 50 / 9,171 | **50 / 9,171** ✓ |
| leaves | 200 / 50,557 | 200 / 50,557 | **200 / 50,557** ✓ |
| `AutomorphicForm` demand | 261 / 114,219 | 260 / 113,790 | **260 / 113,790** ✓ |

Every cell exact. The shelf diff is the single deferred row leaving `ready_rank` and nothing entering.

**Operational**: while 40B ran, a concurrent order's rebuild deleted `AutomorphicForm/Adelic/Basic.olean`
mid-run ("object file does not exist"), and one `flock` build of the module restored the closure — the
FR-0155 friction (a build and a read sharing the tree), now seen from the other side.

## 5. What this set does not do

- The **rest of the idèle/Tate layer** the def module touches through `ProductMeasureData`: the
  zeta-integral consumer chain (`UnramifiedWhittaker`'s `zetaIntegrand` is ported, its integrals are not).
- The **cuspidal unfolding** row (635) and the `U_p`/level-one coset obstruction (229), still ready.
"""
