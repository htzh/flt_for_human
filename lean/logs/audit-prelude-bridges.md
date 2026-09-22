# Audit — mathlib reuse and line savings in the FFG prelude and bridges

Read-only audit. Sources:

- FLT clone `/home/haitao/proj/fermats-last-theorem`, git HEAD `aa2d8b34`
  (`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`, "Lean 4.33.1, Mathlib v4.33.0").
- Pinned mathlib `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean/.lake/packages/mathlib`,
  tag `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`.
  All `path:line` mathlib citations below are against **this** checkout.
- Port `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean/FLTForHuman/`.

Reference copy of the prelude: `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean`
lines 35–404 (370 lines; 321 of them are declaration lines counted with their
blank separators, 267 body-only).

## Headline

1. **The duplication is much larger than "~12 files".** 41 files declare the
   `jq`-prelude `TS`; **38 of them carry all 41 declarations verbatim**
   (2 carry 34, 1 carries 23). A further **11 files** carry a parallel
   `jqModC` prelude (`TS` over `jqModC K`, a second, structurally identical set).
   A shared module therefore removes **≈270–320 lines per full copy**, i.e.
   **≈10,000–12,000 lines** for the `jq` family alone. The port has already
   started this (`Defs/TS.lean`, `Defs/Twist.lean`, `Defs/Cyclotomic.lean`,
   `SlotRoots.lean`).
2. **Only two genuine mathlib collisions exist in the listed prelude**, both
   about primitive roots of unity:
   `exists_isPrimitiveRoot_cyclotomicField`/`cycUnit`/`cycUnit_spec`/`cycUnit_pow`
   vs `IsCyclotomicExtension.zeta`/`zeta_spec`/`zeta_pow`, and
   `isPrimitiveRoot_pow_div` vs `IsPrimitiveRoot.pow`.
   Together ≈18 lines of the 41-declaration prelude.
3. **Everything else in the prelude is FLT-specific glue**, and its proofs
   already call exactly the mathlib lemmas named in the brief
   (`Polynomial.roots_mul`, `roots_X_sub_C`, `roots_multiset_prod_X_sub_C`,
   `mem_roots`, `IsPrimitiveRoot.pow_inj`, `Polynomial.eval₂_finsetProd`,
   `RingEquiv.ofBijective`, `HahnSeries` API). There is no further collision.
4. **Bridges:** the only true mathlib win beyond the prelude is `coeffMapEquiv`
   (`RingEquiv.ofBijective`) and `exists_pow_eq_of_coprime`
   (`exists_pow_eq_self_of_coprime`). `rUnit`/`range_map_eq_rUnit`,
   `eq_of_isRoot_of_isLevel` and `w1_relfinrank_insert` are **not** mathlib
   collisions — the last already uses the mathlib tower law. The dominant win in
   the bridges is de-duplication, not replacement.

---

## (a) Table — prelude candidates

Reference spans are in
`P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean`; "copies" counts files that
declare the same name (over the whole `P2M/Sol/S_ModularCurve_*` family).

### a.1 Genuine collisions (replace or drop)

| pin name | ref line | lines | copies | mathlib replacement (pinned path:line) | mathlib statement | est. saving/copy |
|---|---|---|---|---|---|---|
| `exists_isPrimitiveRoot_cyclotomicField` | L195–200 | 6 | 40 | `IsCyclotomicExtension.zeta` `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean:87`; `…zeta_spec` `:93` | `noncomputable def zeta : B` / `IsPrimitiveRoot (zeta n A B) n` | 6 → 0 (drop; use `⟨zeta N ℚ _, zeta_spec N ℚ _⟩`) |
| `cycUnit` | L201–203 | 3 | 40 | `IsPrimitiveRoot.isUnit` `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean:126` | `IsPrimitiveRoot ζ k → k ≠ 0 → IsUnit ζ` | 3 → 2 |
| `cycUnit_spec` | L204–208 | 5 | 40 | `IsPrimitiveRoot.isUnit_unit` `…/PrimitiveRoots.lean:173` (with `coe_units_iff` `:170`) | `IsPrimitiveRoot (hζ.isUnit hn).unit n` | 5 → 2 |
| `cycUnit_pow` | L209–211 | 3 | 40 | `IsCyclotomicExtension.zeta_pow` `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean:106` | `zeta n A B ^ n = 1` | 3 → 2 |
| `isPrimitiveRoot_pow_div` | L225–236 | 12 | 39 | `IsPrimitiveRoot.pow` `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean:263` (+ `Nat.div_mul_cancel`) | `0 < n → IsPrimitiveRoot ζ n → n = a * b → IsPrimitiveRoot (ζ ^ a) b` | 12 → 3 |
| `qTwistEquiv` | L130–141 | 12 | 40 | `RingEquiv.ofBijective` `Mathlib/Algebra/Ring/Equiv.lean:446` | bijective ring hom → ring equiv | 12 → 9 (port already does this at `Defs/Twist.lean:164`) |
| `roots_phiProd_conj_nodup` (inner step) | L189–193 | — | 40 | `IsPrimitiveRoot.injOn_pow` `…/PrimitiveRoots.lean:270` | `Set.InjOn (ζ ^ ·) (range n)` | 14 → 13 |
| `roots_prime_at_slot_nodup` (inner step) | L299–311 | — | 39 | `IsPrimitiveRoot.injOn_pow` `…/PrimitiveRoots.lean:270` | same | 32 → 31 |

The `IsPrimitiveRoot.pow` route in full (replaces the 12-line pin proof):

```lean
have h : IsPrimitiveRoot ((ζ : K) ^ (N / p)) p :=
  hζ.pow (NeZero.pos N) (Nat.div_mul_cancel hpN).symm
rwa [Units.val_pow_eq_pow_val] at h
```

The `zeta` route replaces `cycUnit`'s `Exists.choose`, and
`IsPrimitiveRoot.isUnit_unit` is *literally* the pin's `cycUnit_spec` shape.

### a.2 Non-collisions — already minimal, FLT-specific

Every other listed declaration has no mathlib counterpart. The composite
statements (`TS*`, `qTwist_TS`, `iota_*`, `conj_*`, `phiProd_conj_eq`,
`roots_phiProd_conj`, `roots_prime_at_slot*`, `isRoot_prime_at_slot_iff`,
`phiAtSeed*`) are FLT's own; their proofs already consume mathlib where
available:

| mathlib lemma used | pinned path:line | used at (ref) |
|---|---|---|
| `Polynomial.roots_mul` | `Mathlib/Algebra/Polynomial/Roots.lean:181` | L174, L269 |
| `Polynomial.roots_X_sub_C` | `…/Roots.lean:198` | L174, L269 |
| `Polynomial.roots_multiset_prod_X_sub_C` | `…/Roots.lean:318` | L179, L279 |
| `Polynomial.mem_roots` | `…/Roots.lean:110` | L332 |
| `Polynomial.card_roots'` | `…/Roots.lean:80` | `CommonRoot.lean` engines |
| `IsPrimitiveRoot.pow_inj` | `…/RootsOfUnity/PrimitiveRoots.lean:138` | L193, L311 |
| `Polynomial.eval₂_finsetProd` | `Mathlib/Algebra/Polynomial/Eval/Defs.lean:657` | port `FunctionFieldGeneration/Spine.lean:292,294` |
| `RingHom.mem_range` | `Mathlib/Algebra/Ring/Subring/Basic.lean:249` | port `Defs/TS.lean:145` (`qExpand_qTwist_notMem_range_qExpand`) |
| `Polynomial.Monic.map`, `Monic.natDegree_map` | `Mathlib/Algebra/Polynomial/Monic.lean:397` | `phiAtSeed_monic`, `phiAtSeed_natDegree` |
| `HahnSeries.map` | `Mathlib/RingTheory/HahnSeries/Basic.lean:143` | port `Defs/Laurent.lean:156` (`coeffMap`) |

So: **no replacement** for the ~35 remaining prelude declarations; only the
micro-shortenings in a.1.

---

## (b) Table — bridge candidates

### b.1 `coeffMapEquiv`, `coeffMap_TS`, `rUnit`, `range_map_eq_rUnit`
File: `P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_pow_succ_of_not_mem.lean`
(near-verbatim duplicate in `S_ModularCurve_finrank_adjoin_jqN_sq_of_not_mem.lean`).

| pin name | line | lines | copies | mathlib route | verdict | est. saving |
|---|---|---|---|---|---|---|
| `coeffMapEquiv` | L446–462 | 18 | 2 | `RingEquiv.ofBijective` `Mathlib/Algebra/Ring/Equiv.lean:446`, fed by `coeffMap_coeffMap`/`coeffMap_id`/`coeffMap_congr` (port `Defs/Laurent.lean:189,195,199`) | **real win (shortening)**, same route the port already uses for `qTwistEquiv` | ~8/copy → **16** |
| `coeffMap_qTwist` | L422–428 | 7 | 41 | none — FLT transfer for `coeffMap` vs `qTwist`; needs `coeffMap_coeff`/`qTwist_coeff` | dedup only | ~7 × 40 = **280** |
| `coeffMap_coeffEmb_algHom` | L430–433 | 4 | 3 | none | dedup | **8** |
| `coeffMap_TS` | L435–437 | 4 | 14 | none (composes the two above) | dedup | ~4 × 13 = **52** |
| `coeffEmb_injective'` / `iota_injective` | L403–408 / L410–412 | 6 / 3 | 4 / 12 | none; the port already has `coeffEmb_injective` (`Defs/Laurent.lean:326`) | dedup into `Defs/Laurent` | **~100** |
| `jqN_congr` | L467–468 | 2 | 20 | none | dedup | **~40** |
| `rUnit` | L470–472 | 3 | 2 | none | **needs route test**; see below | 0 |
| `range_map_eq_rUnit` | L474–542 | 70 | 2 | none | **needs route test** | 0–70/copy (dedup ⇒ **70**) |

**On `RingHom.mem_range` / `Ideal.Quotient` / `IsLocalRing`.** This is a
category error for `rUnit`/`range_map_eq_rUnit`. `rUnit e ζ g i` is the
`LaurentSeries K`-valued function `TS K e (ζ ^ (((g^i : (ZMod p)ˣ) : ZMod p).val))`,
and `range_map_eq_rUnit` is the **multiset identity**

```
(Multiset.range p).map (fun b => TS K e (ζ ^ b))
  = TS K e 1 ::ₘ (Multiset.range (p - 1)).map (rUnit e ζ g)
```

for a generator `g` of `(ZMod p)ˣ`. Its content is the cyclicity of the unit
group and the reindexing `{1,…,p-1} ↔ (ZMod p)ˣ` via `ZMod.val`; the proof
already uses mathlib's `IsCyclic.exists_generator`, `orderOf_eq_card_of_forall_mem_zpowers`,
`pow_injOn_Iio_orderOf`, `ZMod.unitOfCoprime`, `ZMod.val_cast_of_lt`. There is
no mathlib lemma stating this multiset identity, and no `RingEquiv`/quotient
formulation of it. It exists to reindex the roots so that the port's
`Polynomial.irreducible_of_transitive_ringAut` engine applies with `n = p - 1`;
removing it means either changing that engine's indexing or indexing roots by
`(ZMod p)ˣ` throughout. **Route test required; no citeable replacement.**

### b.2 `toAdjoin_eq_minpoly`
File: `P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_eq_of_squarefree.lean`
L668–678 (11 lines; 3 copies).

| item | mathlib pieces (pinned path:line) | verdict |
|---|---|---|
| `toAdjoin_eq_minpoly` | `IntermediateField.adjoin.finrank` `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:489`; `minpoly.dvd` `Mathlib/FieldTheory/Minpoly/Field.lean:69`; `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` `Mathlib/Algebra/Polynomial/Div.lean:95`; `minpoly.monic` `Mathlib/FieldTheory/Minpoly/Basic.lean:54` | **already minimal / not a collision.** It is the standard "monic + annihilating + minimal degree ⟹ `minpoly`" package, and every step is a named mathlib lemma. The port has already ported it at `ModularCurve/ModularPolynomialUniqueness.lean:97–107` (and `ModularPolynomialData.minpoly_jqN_eq`, `ModularPolynomialIrreducible.lean:452`). Only saving is dedup: ~11 × 2 = **22**. |

### b.3 `IsLevel` family
File: `S_ModularCurve_finrank_adjoin_jqN_eq_of_squarefree.lean` L406–647
(242 lines, 1 copy — not duplicated).

| pin name | line | lines | mathlib / port engine | verdict |
|---|---|---|---|---|
| `IsLevel` | L406–408 | 4 | — | FLT-specific predicate; no collision |
| `isLevel_iota`, `isLevel_one` | L410–415 | 6 | — | FLT-specific witnesses |
| `exists_pow_eq_of_coprime` | L417–424 | 9 | `exists_pow_eq_self_of_coprime` `Mathlib/GroupTheory/OrderOfElement.lean:332` + `orderOf_dvd_of_pow_eq_one` `…:273` (+ `Nat.Coprime.coprime_dvd_right`) | **real win (shortening):** 9 → ~4. The statement `∃ u, u^q = w` from `Coprime q M`, `w^M = 1` is mathlib's coprime-power surjectivity on the cyclic subgroup `⟨w⟩`, just oriented as `(w^q)^m = w`. |
| `prime_step_facts` | L426–431 | 7 | `Nat.squarefree_mul_iff`, `Nat.Prime.coprime_iff_not_dvd` | FLT-specific packaging |
| `level_exponent_eq` | L433–439 | 8 | `TS_injective` | FLT-specific |
| `isLevel_mul_of_isRoot` | L441–482 | 43 | `isRoot_prime_at_slot_iff`, `pow_mul`, `Nat.div_mul_cancel` | FLT-specific |
| `eq_of_isRoot_of_isLevel` | L484–637 | 155 | **none applies verbatim** | **needs route test** (see below) |

**`eq_of_isRoot_of_isLevel` is not an instance of the named engines.**
Its conclusion is `z = z'` for two elements both satisfying the arithmetic
predicate `IsLevel K N M`; the candidate engines conclude something else:

- `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`
  (`Mathlib/Algebra/Polynomial/Roots.lean:767`) concludes `p = 0`;
- port `Polynomial.mem_range_of_eval_eq_const`
  (`FLTForHuman/FieldTheory/CommonRoot.lean:111`) concludes
  `x ∈ (algebraMap F L).range`;
- port `Polynomial.mem_range_of_unique_common_root` (`CommonRoot.lean:60`) also
  concludes range membership.

The pin proves it by root-slot case analysis (`isRoot_prime_at_slot_iff` +
`IsPrimitiveRoot.pow_inj` + `pow_eq_pow_iff_modEq` + coprimality `M` vs `q`),
155 lines, and it is used at L830 inside `hinj` to identify two `E`-algebra homs.
A shorter route would have to recast "unique root in a level-set" as a statement
about a gcd/minpoly over a base field; plausible but unproven. **Route test;
plausible saving 0–60 lines, but no citeable reduction.**

### b.4 `w1_relfinrank_insert`
File: `S_ModularCurve_relfinrank_full_of_squarefree.lean` L424–461 (38 lines;
4–5 copies, ~137 total).

| item | mathlib pieces (pinned path:line) | verdict |
|---|---|---|
| `w1_relfinrank_insert` | `IntermediateField.relfinrank_eq_finrank_of_le` `Mathlib/FieldTheory/Relrank.lean:313`; `IntermediateField.extendScalars_adjoin` `Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:449`; `IntermediateField.relfinrank_mul_relfinrank` `Mathlib/FieldTheory/Relrank.lean:465` | **already minimal — not a collision.** The pin uses exactly the mathlib relative-degree/tower API; the remaining 38 lines are FLT-specific rewriting of the adjoin generating set (`adjoin ℚ (insert jq {jqN q : q ∈ insert p S})` collapses to `adjoin A {jqN p}`), then `finrank_adjoin_jqN_prime_of_not_mem`. The port already uses the same API (`FunctionFieldGeneration/Spine.lean:414` calls `IntermediateField.relfinrank_mul_relfinrank`) and `relfinrank_modularFunctionField` (`Defs/Fields.lean:73`). Only saving is dedup: ~38 × 3 = **114**. |

---

## (c) Overall estimated savings

| bucket | estimate | notes |
|---|---|---|
| **Prelude dedup** (`jq` family) | **≈10,000–12,000 lines** | 38 full copies × ≈270 (body-only) … ≈320 (with separators) lines; plus 3 partial copies. Dominant by far. |
| Prelude mathlib reuse (a.1) | **≈18 lines once** (~700–800 if left duplicated ×40) | `zeta`/`isUnit`/`isUnit_unit`/`zeta_pow` ≈ 14, `pow` ≈ 9, `injOn_pow` ≈ 2 |
| `coeffMapEquiv` (`RingEquiv.ofBijective`) | **≈16** | 2 copies × ~8 |
| `coeffMap_qTwist` dedup | **≈280** | 41 copies × ~7 |
| `coeffMap_TS` + `coeffMap_coeffEmb_algHom` dedup | **≈60** | 14 + 3 copies |
| `coeffEmb_injective'` + `iota_injective` + `jqN_congr` dedup | **≈180** | 4 + 12 + 20 copies |
| `rUnit` + `range_map_eq_rUnit` | **0–140** | no mathlib replacement; dedup gives 70, elimination could give 140 |
| `toAdjoin_eq_minpoly` | **≈22** (dedup) | mathlib route already used; port done |
| `exists_pow_eq_of_coprime` | **≈5** | mathlib `exists_pow_eq_self_of_coprime` |
| `eq_of_isRoot_of_isLevel` | **0–60** | needs route test |
| `w1_relfinrank_insert` | **≈114** (dedup) | already uses mathlib tower law |
| Out-of-scope but adjacent: parallel `jqModC` prelude | **≈2,000–3,000** | 11 files carry a second `TS`/`jqModC` prelude; same shared-module treatment applies |

**Bottom line.** The prelude is the whole story: a single shared module removes
~10–12k lines, and only ~18 lines of it are genuinely replaceable by mathlib
(the `zeta` quartet and `IsPrimitiveRoot.pow`). In the bridges, mathlib reuse
buys only ~20 lines (`coeffMapEquiv`, `exists_pow_eq_of_coprime`); the rest is
de-duplication of transfer lemmas (`coeffMap_qTwist`, `coeffMap_TS`,
`jqN_congr`, `iota_injective`) and of the `w1_relfinrank_insert` family.

## Open route tests

1. `isPrimitiveRoot_pow_div` → `IsPrimitiveRoot.pow`: mechanical, high
   confidence (both in `RingTheory/RootsOfUnity/PrimitiveRoots.lean`).
2. `cycUnit*` → `IsCyclotomicExtension.zeta`/`zeta_spec`/`zeta_pow` +
   `IsPrimitiveRoot.isUnit`/`isUnit_unit`: mechanical; needs one
   `haveI : NeZero ((N:ℕ):ℚ)` for the `CyclotomicField` instance
   (`Mathlib/NumberTheory/Cyclotomic/Basic.lean:674,768`).
3. `exists_pow_eq_of_coprime` → `exists_pow_eq_self_of_coprime`: mechanical.
4. `rUnit`/`range_map_eq_rUnit`: no mathlib replacement; decide between dedup
   (1 line copy) and re-indexing the irreducibility engine by `(ZMod p)ˣ`.
5. `eq_of_isRoot_of_isLevel`: check whether the "unique level-`M` root" can be
   routed through `CommonRoot.lean`'s engines; no citeable reduction yet.
