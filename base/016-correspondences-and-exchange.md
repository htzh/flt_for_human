# Correspondences, the exchange lemma, and the norm formula

**Status: OUTLINE — for review. The prose is not yet written; this file fixes the
scope, the section plan and the declaration inventory so the coverage can be
checked first.** Planned as `base/016`, the second of the three notes carrying the
mathlib-level mathematics of the `AlgebraicCurve` port
([../lean/PORTING-AC.md](../lean/PORTING-AC.md), topics **T4–T7**).

## Why this note

[008](008-divisors-and-pic0.md) §5 states the classical calculus — `e`, `f`, the
fundamental identity, pushforward, pullback, "a correspondence is pushforward
along one leg and pullback along the other" — and math/009 §4 states the exchange
identity the Hecke commutativity proof turns on. What neither covers is the layer
the port actually writes:

1. the **`...Along` encoding** (`algebraAlong`, `FiniteAlong`, `SeparableAlong`,
   `finrankAlong`, `pullbackAlong`, `pushforwardAlong`) that replaces the older
   `pullback`/`pushforward`/`pullbackHom` API of 008 §8;
2. the **linearly-disjoint (fibre-product) square** and the identity
   `b^* a_* = b'_* a'^*`, together with the local identity it reduces to;
3. the **bifibre count** and the Galois orbit argument that proves it;
4. the **norm formula**, `ord(N_{F'/F} f) = Σ_{w|v} e(w) f(w) ord_w(f)`, which 017
   uses to discharge `HasPrincipalDivisors`.

This note is where the mathematics of `T_ℓ T_{ℓ'} = T_{ℓ'} T_ℓ` sits at the
mathlib level; [math/009](../math/009-hecke-jacobian-commute.md) is the FLT-step
narrative that consumes it.

## Planned sections

### 0. Scope and placement
- What a correspondence is (008 §5); why the Hecke operator is one; the two faces
  of the theorem — the generic exchange and the Hecke instance.
- Reading order: [015](015-places-and-extensions.md) → this note →
  [017](017-rational-function-field-and-principal-divisors.md); the Hecke
  instance itself is math/009.

### 1. The `...Along` encoding (T4)
- Why an `AlgHom φ : F →ₐ[K] F'` is not enough: `PushforwardNormFormula`,
  `FundamentalIdentity` etc. are stated for a *field extension*, while the
  exchange square is built from maps. `algebraAlong φ` turns `φ` into the
  `Algebra F F'` structure; `isScalarTower_along`, `isIntegral_along` are the two
  side conditions.
- The four bundled predicates and what each buys:
  `FiniteAlong` (finiteness, for pushforward),
  `SeparableAlong` (separability, so the tensor square is étale),
  `FundamentalIdentityAlong` (`Σ e·f = [F':F]`, degree preservation on pullback),
  `NormFormulaAlong` (principal preservation on pushforward),
  and `finrankAlong`.
- The leaf lemmas the cone uses: `finiteAlong_comp`,
  `finiteAlong_of_surjective`, `separableAlong_of_charZero` (characteristic zero
  makes separable automatic), `restrictAlong_congr`.

### 2. Pushforward and pullback along a map (T4)
- `Divisor.pullbackAlong`, `Divisor.pushforwardAlong`, their defining equations on
  singles (`pullbackAlong_single`, `pushforwardAlong_single`), and the point-level
  formulas via `Place.restrictAlong`, `Place.ramificationIndexAlong`,
  `Place.inertiaDegAlong`, `Place.fiberAlong`, `Place.mem_fiberAlong`,
  `Place.ord_restrictAlong`.
- Degree and principality: `degree_pullbackAlong`, `pullbackAlong_mem_degZero`,
  `isPrincipal_pullbackAlong`, `degree_pushforwardAlong`,
  `pushforwardAlong_mem_degZero`, `isPrincipal_pushforwardAlong`; the composite
  `Divisor.correspondence`, `correspondence_correspondence`,
  `pullbackAlong_pullbackAlong`, `pushforwardAlong_pushforwardAlong`.
- Descent to `Pic0`: `Pic0.correspondence`, `Pic0.correspondence_correspondence_comm`,
  `Pic0.mk_eq_zero_iff`, `Pic0.zsmul_mk`, `Pic0.zsmul_mk_eq_zero_of_isPrincipal`,
  `Pic0.nsmul_mk_eq_zero_of_isPrincipal`,
  `Pic0.addOrderOf_mk_dvd_of_isPrincipal`; why the quotient is handled by choosing
  a representative (`Pic0.mk_surjective`).

### 3. The linearly-disjoint square and the exchange identity (T7)
- The square `F → A → E`, `F → B → E`; the five hypotheses in words:
  commutativity `hsq`, finiteness, separability, generation
  `Algebra.adjoin K (range a' ∪ range b') = ⊤`, and the degree match
  `finrankAlong (a'.comp a) = finrankAlong a * finrankAlong b`.
- Why `hgen` + `hLD` are "the square is a fibre product / the two legs are
  linearly disjoint" over an algebraically closed base.
- The statement
  `Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`, and
  its reading: pull-then-push down the left legs equals push-then-pull across the
  roof.
- **Layer 1 (the reduction).** Additivity reduces to a single place `w_A`;
  `Finsupp.addHom_ext`, `ext w_B`, `Finset.sum_apply'`, the two cases
  (`w_B` restricting to the same place as `w_A` or not), and the `rfl` bridges
  `eA`/`fB`/`fF`/`eF` that convert `...Along` invariants to `Place` invariants.
- **Layer 2 (the local identity).** The coefficient identity becomes
  `Place.sum_ramificationIndex_mul_inertiaDeg_exchange`, stated with an arbitrary
  finset `T` and the membership hypothesis
  `∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂`.

### 4. The local identity, taken apart (T5–T6)
- The two-layer structure: the **Galois case** `exchange_of_isGalois`, then the
  **separable reduction** through the normal closure.
- **The bifibre count** `sum_ramificationIndex_mul_inertiaDeg_bifiber`: for a
  compositum `E` of `F₁, F₂` inside a finite Galois `M/F`,
  $`\sum_{W} e_F(W) f_F(W) = (e_F(w_1) f_F(w_1)) (e_F(w_2) f_F(w_2))`$.
- **Tower multiplicativity** (from [015](015-places-and-extensions.md) §5):
  `e_F(W) = e_{F_1}(W) e_F(w_1)`, `f_F(W) = f_{F_2}(W) f_F(w_2)`, and the
  cancellation of the positive factor `e_F(w_1) f_F(w_2)`; positivity of
  `w_2.inertiaDeg F` via `card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`
  and `Module.finrank_pos`.
- **The orbit argument** and its two generic lemmas. The Galois group acts on the
  places over `v`; with `resHom : Gal(M/F) → Gal(M/F_i)` (restriction),
  `card_range_resHom`, `index_range_resHom`,
  `orbit_range_resHom_eq`, `orbit_gal_eq`,
  `forall_apply_algebraMap_eq_of_adjoin_eq_top`. The count
  $`|H_1 x_1 \cap H_2 x_2| \cdot |X| = |H_1 x_1| \cdot |H_2 x_2|`$ is the
  generic lemma `MulAction.ncard_orbit_inter_orbit_mul_card` (165 `S_` lines, not
  in mathlib), and the index hypothesis is turned into `H_1 H_2 = Gal` by
  `Subgroup.exists_eq_mul_of_index_inf_eq` (48 lines, not in mathlib). mathlib
  provides `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`,
  `Subgroup.index_inf_le`, `Subgroup.relIndex_mul_index` but not these statements.
- **The normal-closure reduction:** `Env F E :=
  IntermediateField.normalClosure F E (AlgebraicClosure E)`, `isGalois_env`,
  `algebraEnv` and the six local `IsScalarTower` instances, then
  `sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable` and the final
  `exchange_of_isGalois`/`solution` at `M = Env F E`.

### 5. The norm formula (T4/T9 boundary)
- `PushforwardNormFormula K F F'`, `pushforward_eq_of_normFormula`,
  `isPrincipal_pushforward_of_normFormula`: a finite map pushes principal divisors
  to principal divisors because `φ_* div(g) = div(Norm_{F'/F} g)`.
- Its local form `ord_norm_eq_sum_fiberOver`:
  $`\mathrm{ord}_v(N_{F'/F} f) = \sum_{w \mid v} \mathrm{inertiaDeg}(w)\cdot \mathrm{ord}_w(f)`$,
  proved from the fibre-centre dictionary of [015](015-places-and-extensions.md)
  §3 and `Ideal.relNorm`. This is the lemma 017 consumes; the note states it and
  records the boundary, leaving the `relNorm` computation itself to 017.

### 6. How the code says this
- Encoding choices: `algebraAlong` and the `letI`/`haveI` walls; why the exchange's
  `rfl` bridges depend on the definitional unfolding of `algebraAlong`;
  `HasPrincipalDivisors` needed on `B` and `E` for the final statement but not for
  the class-free `fiberOver` computation.
- Key-point → declaration map.
- Traps: instance diamonds in the normal-closure block; `DecidableEq (Place K E)`
  for the `Finset.filter`; the deprecated `Ideal` alias set; the `p2m_*` namespace
  machinery that is dropped; the duplicated `BifibreDev`/`BifibreW2`/`BifibreWEX`
  preludes that the port writes once.

### 7. Links
- FLT sources at `aa2d8b3`: `Def_AlgebraicCurve_Correspondence`,
  `Def_AlgebraicCurve_DivisorPushPull`, `Def_AlgebraicCurve_DegeneracyTower` (the
  Hecke instance), the `S_` files of T4–T7, the two generic `S_MulAction_*` /
  `S_Subgroup_*` files, and the `Theorems/` wrappers.
- mathlib at `v4.33.0`: `AlgebraicGeometry/FunctionField` (the scheme seam, cited
  only to say it is *not* used), `FieldTheory/Galois/Basic`,
  `FieldTheory/Normal/Closure`, `FieldTheory/SeparableClosure`,
  `GroupTheory/Index`, `LinearAlgebra/Dimension/Finrank`.
- Companion notes: [008](008-divisors-and-pic0.md) §5,
  [015](015-places-and-extensions.md), [math/009](../math/009-hecke-jacobian-commute.md) §3–§4.

## Planned key-point → declaration map

| Mathematics | Lean declaration | AC topic |
|---|---|---|
| a map as an algebra structure | `algebraAlong`, `isScalarTower_along` | T4 |
| bundled finiteness / separability | `FiniteAlong`, `SeparableAlong` | T4 |
| relative degree of a map | `finrankAlong` | T4 |
| pushforward / pullback along a map | `pullbackAlong`, `pushforwardAlong` | T4 |
| the correspondence on divisors and `Pic0` | `Divisor.correspondence`, `Pic0.correspondence` | T4 |
| correspondence composition | `correspondence_correspondence`, `Pic0.correspondence_correspondence_comm` | T4 |
| fibre along a map | `Place.fiberAlong`, `Place.mem_fiberAlong` | T4 |
| linearly disjoint square | `hgen`, `hLD` of the exchange | T7 |
| the exchange identity | `Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong` | T7 |
| the local identity | `Place.sum_ramificationIndex_mul_inertiaDeg_exchange` | T6 |
| reduction to a place | `Finsupp.addHom_ext`, `pullbackAlong_single`, `pushforwardAlong_single` | T7 |
| bifibre count | `sum_ramificationIndex_mul_inertiaDeg_bifiber` | T5 |
| orbit-intersection count | `MulAction.ncard_orbit_inter_orbit_mul_card` | T5 |
| index product | `Subgroup.exists_eq_mul_of_index_inf_eq` | T5 |
| normal closure reduction | `Env`, `isGalois_env`, `exchange_of_isGalois` | T6 |
| norm pushes principal to principal | `PushforwardNormFormula`, `isPrincipal_pushforward_of_normFormula` | T4 |
| local norm formula | `ord_norm_eq_sum_fiberOver` | T4/T9 |

## Open questions for the review

- Should the Hecke instance (`heckeSquareBar_commutes`, `towerInclBar`,
  `towerSubstBar`, `heckeRoof_adjoin_range_union_eq_top`,
  `finrankAlong_towerSubstBar_comp_heckeAlphaBar`) be *stated* here as the worked
  example, or left entirely to math/009? Plan: a short pointer in §0 plus the
  generic statement, with math/009 owning the instance.
- Should `ord_norm_eq_sum_fiberOver` be proved here or in 017? It is used only by
  017, but its proof is the dictionary of 015 §3. Plan: state it here, prove it in
  017 (or cross-reference whichever is written first) — decide at writing time.
- Length target: ~500–650 lines.
