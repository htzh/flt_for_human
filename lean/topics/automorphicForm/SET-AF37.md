# SET-AF37 — the Weyl translate of an induced section, evaluated

**Status: scoped 2026-11-08, two orders in parallel** — §4 is the forecast, §6 the landing record (to be
appended). Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the read that
follows SET-AF34/36. It is the **thirty-seventh** set of the column, and it closes the subject AF33
opened (the Weyl intertwining integrand) on its value side.

**3 rows / 1,620 silo / 1,037 net priced** — the composition-heaviest set of the column: `port_advise`
finds **464 of the 1,501 declaration lines already in the port** (429 tier 1 + 35 tier 3), because the
first ~440 lines of the 1,043-line row are the height/`flatOne` prelude the port already has in
`AutomorphicForm/Adelic/InducedSectionFlat.lean`.

| # | row | silo | lev | prem | what it says |
|---|---|---:|---:|---:|---|
| **A** | `AutomorphicForm.isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1,043 | 1/3 | 3 | the bottom-row indicator times the height power is an induced section — continuous, `K`-finite, `K_f`-smooth, with its four invariance laws and `φ₀ 1 = 1` |
| **B** | `AutomorphicForm.apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1/1 | 1 | at one infinite place `w`: `φ (w⁻¹ n(x) k) = ‖det k_w‖^(s+1/2) ‖k_w00 + x_w k_w10‖^(-(2s+1)) · φ (w⁻¹ n(x'))` |
| **C** | `AutomorphicForm.apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 1/1 | 2 | at one finite place `v`: `φ (w⁻¹ n(x) finEmbed (localEmbed v gl2Weyl)) = modulus(x_v)^(-(2s+1)) · φ (w⁻¹ n(x'))` |

**One story.** A is the *section* the Weyl integrand is evaluated on; B and C are its two *evaluations* —
the archimedean and the finite-place Weyl translates, each a product of `‖·‖`-powers times the value at a
corrected point. AF33's set proved that translating an induced section is integrable over the finite
adèles; these are the pointwise computations that turn the resulting integral into local factors. The set
is cut as A | B+C because the two halves are different modules and different proofs, and they do not cite
each other.

## 0. The read

The read SET-AF34/36 left (`needed` **753 / 313,678**, `--selfcheck` PASS; the six scaffolds of the
in-flight AF35/AF36 wave are in the tree, so the shelf already prices those rows as landed — FR-0157):

| figure | value |
|---|---:|
| `needed [F terminal]` | 753 / 313,678 |
| frontier F | 1,663 / 813,698 |
| ready rows | 59 / 12,916 |
| leaves | 200 / 50,557 |
| `AutomorphicForm` ready | 29 / 6,087 |

**Premise audit** (name *and* statement; the FR-0156 lesson): A's three premises are
`NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm`,
`AutomorphicForm.isInducedSection_adelicHeight_cpow` (the headline of `InducedSectionFlat.lean`) and
`NumberField.AdelicHeight.continuous_adelicHeight`; B's is `distribHaarChar_eq_…`; C's are `distribHaarChar_eq_…`
and `LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`. Each last name occurs exactly once in
the port. No shadow.

**Definition gate: none that bites.** `--with-defs` closes over eleven pin `Def_` modules
(`AdelicDock_LocalEmbedding`, `AdelicMaximalCompact`, `ArchKFinite`, `EtaFamily`, `InducedSection`,
`RowIsometryInvariance`, `SmoothAutomorphicFnAt`, `WeylIntertwining`, `TateLocalZeta`, `AdelicHaar`,
`AdelicHeight`); all are ported — `AdelicMaximalCompact` 38/38, `ArchKFinite` 9/9, `InducedSection` 10/10,
`RowIsometryInvariance` 12/12, `SmoothAutomorphicFnAt` 16/16, `WeylIntertwining` 7/7, `AdelicHaar` 25/25,
`AdelicHeight` 26/28, `EtaFamily` 12/15, `TateLocalZeta` 20/23, `LocalEmbedding` 50/62 — and the residual
counts are declarations the port states under its own names or holds `private`; the scaffolds (and the
wires) are the operative test, and both elaborate.

**Ten suspect substitutions to refuse.** `port_advise` reports `scalarPi → UnramifiedWhittaker.repInf`
(12) and `finiteLevelOne → NumberField.AdelicLevel.finiteLevelZero` (10): both are type-only `def` matches.
The pin's `scalarPi`/`finiteLevelOne` are *its own* objects; write them, do not substitute the port's
lookalikes.

## 1. The cut

| order | module | rows | silo | why this module |
|---|---|---|---:|---|
| **37A** | `AutomorphicForm/Adelic/InducedSectionBorelIndicator.lean` | A | 1,043 | the explicit test section; above `InducedSectionFlat` (which holds its prelude) |
| **37B** | `AutomorphicForm/Adelic/WeylTranslateValues.lean` | B + C | 577 | the two evaluations; above `IwasawaWeylUnipotent` (which holds the shared `coe_weylInv_mul_unipotent`) |

`IwasawaWeylUnipotent.lean` has **no in-tree importers**, so both modules are cascade-free. A is not
inserted into `InducedSectionFlat.lean` on purpose: that module is a legacy `PORT_FILES` entry, and
touching it would trigger the legacy-module migration (instructions §"Legacy Modules") for no
mathematical reason.

## 2. The price

| figure | value |
|---|---:|
| raw `S_` lines | 1,620 |
| declaration lines | 1,531 |
| — duplicate copies | 30 |
| — boilerplate | 89 |
| distinct declaration groups | 144 |
| already in the port (vetted) | **464** (429 tier 1, 35 tier 3) |
| **net new math lines** | **1,037** |

364 trusted substitutions, 10 suspect (above). Per row: A 82 declarations (81 public in the pin!), B 43,
C 22.

## 3. Orders and gates

`lean/tmp/WORKORDER-AF37A-induced-section-indicator.md`, `…-AF37B-weyl-translate-values.md`. The standard
gates, plus the **surface gate** with a twist for A: its pin file's helper block is almost entirely
*already ported* (`InducedSectionFlat.lean`), so the surface gate's `ok`s will include declarations that
belong to the imported module — check the checker's mapping per declaration, and do not re-declare what the
import provides.

## 4. Forecast

With SET-AF35/36 in flight, quote the delta from the read above.

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 753 / 313,678 | **750 / 312,058** |
| `needed [literal]` | 765 / 317,143 | **762 / 315,523** |
| frontier F | 1,663 / 813,698 | **1,666 / 815,318** |
| ready rows | 59 / 12,916 | **57 / 11,919** (A 1,043 and B 360 out; C 217 also out → 56 / 11,702) |
| leaves | 200 / 50,557 | 200 / 50,557 |
| `AutomorphicForm` demand | 267 / 116,664 | **264 / 115,044** |

## 5. What this set does not do


- The **Euler-product consumer** `exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul`
  (995) still needs the meromorphic continuation.
- The **`isInducedSection`-family tail**: `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway`
  (209), `exists_finset_forall_exists_mem_valued_eq_max_contentHomFin_mul_sq_eq` (333) and
  `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` (229) are ready
  but not this story.
- The **CuspForm Γ₁ Hecke layer** (`exists_degeneracy_gamma1_hasNebentypus` 218 with leverage 9/12, the
  `U_ℓ` pair 241 + 348, the vanishing criterion 351) — cut as SET-AF38 in the same wave.
- No definition layer, no promotion, no migration, no legacy touch, no tree build.

## 6. The landing (2026-11-08)

Two orders, two modules, all gates green.

| order | module | lines | declarations | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| **37A** | `AutomorphicForm/Adelic/InducedSectionBorelIndicator.lean` | 724 | 46 transcribed (the pin's other 36 are imported prelude) | **45 ok + 1 own** | 3,863 jobs, silent | clean |
| **37B** | `AutomorphicForm/Adelic/WeylTranslateValues.lean` | 583 | 62 (2 headlines, 34 pin-public, 23 pin-`private`, 5 new `private`) | **34 ok / 0 / 0** | 3,728 jobs, silent | clean, both |

**What the set consumed**: 3 rows / 1,620 silo in **1,307 written lines**, and 464 declaration lines
imported rather than written — the composition-heavy set the price predicted. Consumers
`spec/AutomorphicFormSetAF37AConsumer.lean` (116 lines) and `…AF37BConsumer.lean` (119) — 0 errors, real
compositions (the `S = ∅` degeneration of the indicator into the imported `flatOne`; the local and
archimedean evaluations composed on one section). One new import in 37B
(`TateGlobal/NormIntegrable`, for `modulus_adicCompletion_eq_nnnorm`), reported. No promotion, no
migration, no definition layer, no tree build.

### 6.1 The composition measurement

37A is the cleanest instance of the recipe's "silo is not content" rule so far: the pin's 1,043-line file
carries **82 declarations**, and the port writes **46** of them because

* 31 are hash-identical to declarations of the imported `InducedSectionFlat.lean`
  (`AutomorphicForm.FlatInducedSection.*`, the height/`flatOne` prelude),
* 1 is the prelude's `private coe_mul`,
* 4 are hash-identical to the homed `PlaceModulus.*` in `NumberTheory/AdelicHaar/AdelicModulus.lean`.

Zero prelude declarations were re-declared, and no pin declaration of the file is unaccounted for. That is
the accounting *by name and statement hash*, not by last name.

### 6.2 Deviations held for review

1. **37A's one `own:` row** — `phi0_of_cond` concludes `phi0 S n s g = FlatInducedSection.flatOne K s g`
  where the pin writes `P6B.JE2aFlat.flatOne K s g` (a task label the port deliberately does not carry).
  The exception is registered in `spec/decl_markers.tsv` (the house rule: not in the Lean source) and
  validated with `--strict-markers`; a plain provenance comment remains above the declaration.
2. **37B corrects one of this set's own scoping claims.** The scoping priced `gl_ext` as ported
  (`InducedSectionMaximalCompact.lean`, binder-spelling). The *public* `AutomorphicForm.gl_ext`
  (`MaximalCompactFactors.lean:271`) takes its finite hypothesis as `glFin g = glFin h`, **not** the pin's
  placewise `∀ u, finComponent … = finComponent …`; the pointwise copy is `private`. So the pin's
  `gl_ext`/`glArch_ext` are stated locally with the pin's binders and its 8-/6-line proofs. A `private`
  port copy does not satisfy the checker's public-surface tier — the same distinction AF34-B's surface-gate
  note drew.
3. **37B's `toCompletion` drift**: the port's `InfinitePlace.Completion` is a one-field structure, so the
  pin's `field_simp; ring` leaves `toCompletion` atoms; three private helpers (`toCompletion_inv`,
  `toCompletion_neg`, `toCompletion_ne_zero`) push inverse/negation/zero through. Also the pin's inline
  dependent function inside `Matrix.of` does not reduce (an `Equiv` in the port) — named
  `atPlaceMat`/`atPlaceMatInv`; and `simp [moeb]` does not fire `Function.update_self` at
  `InfiniteAdeleRing`, replaced by `unfold`+`exact`.

### 6.3 The re-read

Taken with SET-AF38 in the same wave, with the *next* wave's scaffolds un-ported (FR-0157): the full table
is [SET-AF38.md](SET-AF38.md) §7. This set's own delta from the shelf diff:

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 753 / 313,678 | **750 / 312,058** (the wave lands at 746 / 310,900) |
| frontier F | 1,663 / 813,698 | **1,666 / 815,318** |
| ready rows | 59 / 12,916 | **56 / 11,296** |
| `AutomorphicForm` demand | 267 / 116,664 | **264 / 115,044** |

**Rows this set readied: none.** The three rows leave the shelf and nothing cites them yet — the
Euler-product consumer (995) needs the meromorphic continuation beside them, not just the evaluations.
