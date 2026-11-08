# SET-AF39 — the right-convolution engine at a level coset

**Status: scoped 2026-11-08, two orders in parallel** — §4 is the forecast, §5 the landing record (to be
appended). Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). It is the
**thirty-ninth** set of the column.

**3 rows / 825 silo / 693 net priced.**

| # | row | silo | lev | prem | what it says |
|---|---|---:|---:|---:|---|
| **A** | `AutomorphicForm.exists_integral_rightConv_eq_rightConv` | 514 | 2/3 | 3 | the average of `rightConv y f` over a compact `U = O ⊓ K_f` with a probability Haar measure is `rightConv y f'` for a `U`-bi-invariant factorizable, arch-`bi`-finite `f'` |
| **B** | `AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 2/5 | 1 | a finite combination of right convolutions by `v`-central elements is `v`-invariant, a Hecke coset-eigenfunction with the same eigenvalue, and `U`-bi-invariant |
| **C** | `AutomorphicForm.cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 2/2 | 1 | for level-spherical `f` and a double-coset transversal `reps` of `g` mod `U`: `∑ i rightConv φ f (· * reps i) = rightConv (∑ i φ (· * reps i)) f` |

**One story.** `rightConv` is the right action of `GL₂(𝔸)`, and these are the three moves the column's
Hecke/eigenfunction arguments make with it: average it over a compact level subgroup (A — the average is
again a right convolution, of an invariant test function), push it through a coset sum (C — the linearity
that makes a coset sum of translates a convolution), and read a coset sum of convolutions as an
eigen-relation (B). AF34 used the third move implicitly in its capstone; this set states the engine.

## 0. The read

The read after SET-AF35/36 (`needed` **753 / 313,678**, `--selfcheck` PASS; the AF37/AF38 wave's scaffolds
are priced as landed unless `--unport`ed — FR-0157). The three rows are on the ready block at 514 / 173 /
138.

**Premise audit** (name *and* statement): A's premises are
`NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo`,
`NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar` and
`AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn`; B's and C's premises are
`NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo` (B) and the ported
`exists_sesqForm_…`-family statements. Each last name occurs once in the port (checked; the two rows of
`secondCountableTopology` are a subgroup lemma and the general one at
`NumberTheory/AdelicLevel/Countability.lean:170`).

**The definition gate is clean**: `--with-defs` closes over `ArchSpherical` (7/7), `RightConvolution`
(5/5), `SmoothCuspRealization` (25/25), `AdelicHaar` (25/25), `UnramifiedWhittaker_HeckeRecursion` (8/8)
and `CuspidalConstituent` (18/21 — the three residual names are spellings the port states differently, and
the statement does not need them).

## 1. One row deferred — the Borel Haar disintegration

`AutomorphicForm.exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant` (429) is on the
ready shelf and was the natural third row, but it is **not statable in the port**: its conclusion is

`∫⁻ b, F b ∂μB = c * ∫⁻ x, ∫⁻ u, ∫⁻ t, F (unipotentGL2 x * centralScalar u * diagOne t) * ‖t‖⁻¹ ∂idelicHaar ∂idelicHaar ∂adelicAddHaar`

and the port has **no `NumberField.Idele.idelicHaar`** (nor `ideleBorel`, nor the `ord`/`unitComponent`/
`partAt` family): `Def_NumberField_IdeleProductMeasure` is 64 declarations, **none** of them ported. This
is the FR-0049 class of the recipe §0 — *`needed = 1` is a premise claim, not a statement claim* — and it
is invisible to the shelf because a missing `Definitions/Def_*` module is not a graph node. The row is
**deferred** until that definition layer is ported (a separate definition-layer set: 64 declarations of
idèle product measure, which the Fourier/Tate layer will want anyway).

This is the second time in two waves that a "ready" row failed on its *vocabulary* rather than its
premises (SET-AF34's `fnTwist`, this one's `idelicHaar`). The check the recipe prescribes (§0, "read the
wrapper's `import Definitions.…` lines and run `twin_scan --node`") was run for the two rows kept here and
they are clean.

## 2. The cut

| order | module | rows | silo |
|---|---|---|---:|
| **39A** | `AutomorphicForm/Adelic/RightConvIntegral.lean` | A | 514 |
| **39B** | `AutomorphicForm/Adelic/RightConvCosetSum.lean` | B + C | 311 |

Both new modules, above `RightConvolution`/`Constituent`/`SmoothRealization`/`ArchSpherical` and below
nothing (0 importers at creation).

## 3. The price

| figure | value |
|---|---:|
| raw `S_` lines | 825 |
| declaration lines | 758 |
| — duplicate copies | 10 |
| — boilerplate | 66 |
| distinct declaration groups | **39** (the lowest of the column: the declarations are large) |
| already in the port (vetted) | 135 |
| **net new math lines** | **693** |

96 trusted substitutions, 3 suspect (`clamp01`-style type-only `def` matches; do not substitute).

## 4. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 753 / 313,678 | **750 / 312,853** |
| `needed [literal]` | 765 / 317,143 | **762 / 316,318** |
| frontier F | 1,663 / 813,698 | **1,666 / 814,523** |
| ready rows | 59 / 12,916 | **56 / 12,091** |
| leaves | 200 / 50,557 | 200 / 50,557 |
| `AutomorphicForm` demand | 267 / 116,664 | **264 / 115,839** |

## 5. The landing (2026-11-08)

Two orders, two modules, all gates green.

| order | module | lines | declarations | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| **39A** | `AutomorphicForm/Adelic/RightConvIntegral.lean` | 428 | 14 (all public) | **14 ok** | 4,867 jobs, silent | clean, all 14 |
| **39B** | `AutomorphicForm/Adelic/RightConvCosetSum.lean` | 363 | 6 (3 public, 3 pin-`private`) | **3 ok** | 3,633 jobs, silent | clean, both |

**What the set consumed**: 3 rows / 825 silo in **791 written lines**, with 6 of A's 19 pin declarations
**reused** rather than re-declared (`eq_of_glArch_eq_of_glFin_eq` and `continuous_finEmbed` from
`LevelCompactness`, `glFin_eq_one_of_mem_iSup_range`/`sandwich`/`archEntries_mul_mul`/
`isFactorizableTestFn_sum_mul_translate_of_mem_iSup_range` from `TestFnInvariance`) — re-declaring them
would put a second public `AutomorphicForm.sandwich` in the library and break any module importing both.
One new import in A (five, reported: `TestFnInvariance`, `LevelCompactness`, `TestFnTop`, `Countability`,
`MulRightInvariant`) and one in B (`TestFnTop`). Consumers
`spec/AutomorphicFormSetAF39AConsumer.lean` (131 lines, 12 declarations) and `…AF39BConsumer.lean` — 0
errors, and A's consumer **constructs** its `U` and its probability Haar measure rather than assuming them.

### 5.1 Deviations held for review

1. **B's instance wall** (pin `:89-91`): `letI`/`haveI` at the head of a Prop-valued proof trips
   `linter.style.haveILetI`, so the three instances are set with a file-local
   `attribute [local instance]` (the port idiom of `SpectrumLift.lean:65-67`). Same instances, same scope.
2. **B's final `calc`** (pin `:166-173`): the pin's single `rw […, mul_assoc]` cannot close the goal as
   written (it rewrites the wrong side); the port spells the five-step `calc` with `← mul_assoc` then
   `mul_assoc`. The agent's judgement, recorded.
3. **B's `hdec`** (pin `:140-150`) is the port form of `SpectrumLift.lean:531-540`, decomposing straight
   from `glFin y ∈ glFin '' U`; the pin's `AdelicDock.finEmbed` route is the same conclusion.
4. **`isHeckeCosetSystem_mul_right`** (pin-public) is transcribed in the pin's `variable` form: the
   explicit-binder spelling was a checker mismatch, because the checker compares against the pin's
   variable-shaped statement.

### 5.2 The one duplicate, and the generalized copy the scoping missed

B's three private helpers (`eq_of_glArch_eq_of_glFin_eq`, `mul_comm_of_glFin_eq_one_of_glArch_eq_one`,
`sum_apply_mul_mul_reps_eq`) already exist **public** at `Cusp/SpectrumLift.lean:472/476/482`, ported from
the same pin earlier — but that module is downstream of B's import cone, so the names are unreachable and
the triad was re-brought privately (46 lines). `dedup --within` is clean; a **cross-module** dedup would
flag it. The honest fix is a shared home, and the recipe's FR-0041 check is the lesson: the port also
already holds `SpectrumLift.cosetSum_rightConv_eq` (line 509), which is row C **generalized** over an
arbitrary `U ≤ K_f` with an explicit `IsFactorizableTestFn` hypothesis. Row C is not an immediate corollary
(the pin derives factorizability from its level-spherical condition internally, and that derivation is
exactly what row C's 100-line proof supplies), but a scoping pass that greps for a *generalized* copy — not
only for a statement twin — would have known before dispatch that 100 of the set's 825 silo were already in
the tree in stronger form.

### 5.3 The re-read

Taken after the wave, with the Borel row (deferred in §1) still un-ported:

| figure | before | forecast | **actual** |
|---|---:|---:|---:|
| `needed [F terminal]` | 753 / 313,678 | 750 / 312,853 | **743 / 310,075** (the three sets of the wave: −10 / −3,603) |
| frontier F | 1,663 / 813,698 | 1,666 / 814,523 | **1,673 / 817,301** (the wave) |
| ready rows | 59 / 12,916 | 56 / 12,091 | **51 / 9,600** (the wave) |
| leaves | 200 / 50,557 | 200 / 50,557 | **200 / 50,557** ✓ |
| `AutomorphicForm` demand | 267 / 116,664 | 264 / 115,839 | **261 / 114,219** (the wave) |

This set's own delta, from the shelf diff: three rows left the ready block (−825) and **none entered** —
the right-convolution engine readies nothing on its own, which is the expected shape for a set whose rows
are *tools*: what it does is make the coset/eigenfunction arguments (AF34's capstone, the Hecke layer)
shorter to write, not new rows ready.

**Rows this set readied: none.**

## 6. What this set does not do

- **The Borel Haar disintegration** (429): deferred on the missing idèle product-measure layer (§1).
- **The cuspidal unfolding** `integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn` (635)
  and the level-one coset obstruction `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_…` (229):
  ready, in this subject area, not cut.
- **The `isKfSmooth`/maximal-compact-away family** (209, 333) and the arch-cut lattice tail (68, 66, 56,
  52, 37, 59, 48, 29).
- No definition layer, no promotion, no migration, no tree build.
