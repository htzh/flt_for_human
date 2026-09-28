# The Eichler–Shimura package — port scout

**Status (2026-09-27).** A living port scout for the **full Eichler–Shimura
isomorphism**. §1 fixes the driver, §2 is the pin's inventory and consumer map,
§3 the baseline effort, §4 what the port has already landed, §5 the gap, §6 the
port order. Everything is measured against the FLT pin `aa2d8b3` with
`tools/deps` (docs-site graph closure) plus source greps of the pin's `S_`/`Thm_`
files; the port's mathlib is `v4.34.0`.

**Route B is no longer on the path.** Its blob proves the weight-2 slice of the
same map plus a finiteness statement C′ already gives; it adds no coverage, and
it is recorded as a `lean/Reserve/` candidate (§1.3).

Companions: [flt-non-frey-segments.md](flt-non-frey-segments.md) §8–§8.1,
[route-c-prime-scout.md](route-c-prime-scout.md),
[../math/017-eichler-shimura-isomorphism.md](../math/017-eichler-shimura-isomorphism.md)
(the mathematics — the classical isomorphism and its ingredients),
[../math/015-weight-two-hecke-periods.md](../math/015-weight-two-hecke-periods.md)
(route B, now Reserve),
[../math/016-mod-p-weight-filtration.md](../math/016-mod-p-weight-filtration.md)
(the mod-$`p`$ weight filtration, retained as background).

## 0. Terminology

The words "Eichler–Shimura", "E-S" and "route A" have been used for three
different objects; the measurements are in §8 of the old scout, reproduced here.

| object | what it is | size |
|---|---|---|
| **route A** | the *integral-structure* route: the pin's proof of `CuspForm.hasIntegralStructure_of_two_le` (and `moduleFinite_heckeAlgebra` above it) | 657 nodes / 263,720 lines, ~528 of them modular-curve / elliptic geometry |
| **the E-S isomorphism** | the period map $`S_k \to H^1_{par}(\Gamma_0, \mathrm{Sym}^{k-2})`$ and its two-piece decomposition; the mathematical content below | the driver (§1) |
| **the E-S cohomology packaging** | the `HeckeEis` nodes bundling that content: `eichlerShimuraMap`, `coeffH1par`, the conjugate half, the integral basis, the dimension bound | 33 nodes / 10,789 `S_` lines (§2.1) |

Route A is not an E-S cone, and the E-S isomorphism is not the cohomological
packaging; separating them changes the payoff accounting. C′ replaces route A's
*proof* for **4 nodes / 800 lines**
([route-c-prime-scout.md](route-c-prime-scout.md) §4 addendum).

**On the name `HeckeEis`.** It is a Lean namespace in the pin; its "Eis" is the
pin's shorthand for *Eichler–Shimura* (the definition module is titled "Eichler
integrals and the Eichler–Shimura map to parabolic cohomology"). It is ambiguous
with *Eisenstein* and mixes kept and removed material, so it is used here only as
a literal Lean identifier.

## 1. The driver

### 1.1 The statement

The driver is the classical **Eichler–Shimura isomorphism** in the form the
endgame needs. The pin's packaged form is
`HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime (N) [NeZero N] (n)`:

```lean
∃ (ES    : CuspForm (Γ₀ N) ((n:ℤ)+2) →ₗ[ℂ] coeffH1par (binaryFormRepSL ℂ n ∘ Γ₀.subtype))
  (ESbar : CuspForm (Γ₀ N) ((n:ℤ)+2) →ₛₗ[starRingEnd ℂ] coeffH1par (binaryFormRepSL ℂ n ∘ Γ₀.subtype)),
  Function.Injective ES ∧ Function.Injective ESbar ∧
  IsCompl (LinearMap.range ES) (LinearMap.range ESbar) ∧
  (∀ ℓ prime, ℓ ∤ N, ∀ T Hecke on coeffH1par, (∀ f, T (ES f) = ES (heckeTLin f)) ∧
                                             (∀ f, T (ESbar f) = ESbar (heckeTLin f))) ∧
  (∀ ℓ prime, ℓ ∣ N, ∀ T Hecke on coeffH1par, (∀ f, T (ES f) = ES (heckeULin f)) ∧
                                             (∀ f, T (ESbar f) = ESbar (heckeULin f)))
```

i.e., in the mathematics of
[017](../math/017-eichler-shimura-isomorphism.md),

$$H^1_{par}(\Gamma_0(N), \mathrm{Sym}^{k-2}) \;\cong\; S_k(\Gamma_0(N)) \oplus \overline{S_k(\Gamma_0(N))}$$

as Hecke modules, the isomorphism being the period map and its complex conjugate.
A port-facing statement would name it once (`eichlerShimura_isomorphism`) rather
than bundle it in an existential, and would define the period map separately.

### 1.2 Why this driver

* **It is the classical statement, with math content.** Eichler (1957) and
  Shimura (1959); the pin's generated titles call it "Eichler–Shimura
  decomposition of parabolic cohomology". It is a landmark of the theory even
  though it is not one of the pin's 49 route landmarks
  (`PROOF-PATH.md` names no E-S step).
* **It is uniform in the weight.** No form-side weight descent is needed, which
  is what makes it a single driver rather than a family.
* **It is exactly the source of the endgame's two E-S consumers.** Interfaces 1
  (level raising, the mod-$`p`$ eigenclass) and 4 (char-3 weight $`\le 4`$, the
  classification of `H¹` eigensystems) are the only interfaces whose closure
  meets the packaging at all (§2.2). Interface 1 needs the period map, the
  integral lattice and the eigenclass; interface 4 needs the surjectivity /
  Eisenstein half.
* **It strictly contains route B.** Route B is the $`n = 0`$ slice, where the
  quotient and the anti-holomorphic half both vanish.

### 1.3 Route B is retired to `lean/Reserve/`

Route B's 4,308-line blob (`S_CuspForm_moduleFinite_heckeAlgebra_two.lean`) is
self-contained (graph closure 1) and pleasant, but it proves:

* the weight-2 period map and its injectivity — the $`n = 0`$ slice of the
  driver, so no coverage the driver does not give; and
* a finiteness statement (`moduleFinite_heckeAlgebra_two`) that C′'s integral
  structure already implies in every weight
  ([../math/015-weight-two-hecke-periods.md](../math/015-weight-two-hecke-periods.md)
  role-correction).

So it contributes nothing to the critical path. Its value is pedagogical: a
self-contained worked instance of the period construction. That is precisely the
`lean/Reserve/` convention (a verified alternative route kept out of the
critical-path library), and it is recorded there in
[../lean/Reserve/README.md](../lean/Reserve/README.md).

## 2. The pin's package: inventory and consumers

### 2.1 The 33 packaging nodes

`R` is the set matched by the patterns `eichlerShimuraMap` and `coeffH1par`:
**33 nodes / 10,789 `S_` lines** in the `HeckeEis` namespace. By role, over
$`\Gamma_0(N)`$, $`V_n =`$ `BinaryForm ℂ n`, representation `binaryFormRepSL`,
Hecke `binaryFormAlphaAdj`, weight $`k = n+2`$:

| group | nodes | lines | content |
|---|---:|---:|---|
| 1. the period map | 4 | 394 | `eichlerShimuraMap` additive, ℂ-homogeneous, injective |
| 2. the two halves | 5 | 2,000 | conjugate-linear involution, complementarity, packaged isomorphism |
| 3. Hecke equivariance | 4 | 1,742 | existence of the cohomological $`T_\ell`$, $`U_\ell`$, and the square |
| 4. coefficient change / functoriality | 3 | 1,142 | base change, equivariant retractions, Shapiro/projLine |
| 5. integral structure | 9 | 3,521 | torsion-freeness, integral basis, base change, denominators |
| 6. dimension theory | 4 | 1,180 | Euler-characteristic / genus bounds |
| 7. mod-$`p`$ eigenclass and boundary | 4 | 810 | integral eigenclass mod $`p`$; the Eisenstein boundary |

The full list with the pin's English titles is Appendix A. Three nodes are
**interface-facing** — the only members of `R` whose consumers outside `R` are an
endgame interface (all three feed interface 1) rather than another member of `R`,
route A / `finite_int_heckeAlgebra`, an analytic node, or the retained re-proved
node `HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1`:

* `exists_coeffH1par_projLineRepSL_equiv_parabolicHoms` (710) → interface 1;
* `exists_coeffH1par_map_of_equivariant_retraction` (174) → interface 1;
* `exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two`
  (61) → interface 1.

### 2.2 The consumer map: only two interfaces touch `R`

Of the ten maximal interfaces (old scout §6), only two have any of `R` in their
closure. The other eight are either **C′-dissolved** (interfaces 5 and 6 fall
from 25 `R`-nodes to **0** once `hasIntegralStructure_of_two_le` is supplied by
C′) or never touch `R` (2, 3, 7, 8, 9, 10).

| interface | `R`-closure | endgame role | needs the full isomorphism? |
|---|---:|---|---|
| 1. `WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_…` | 20 / 6,369 | level raising: a nonzero mod-$`p`$ eigenclass | **no** |
| 4. `WeierstrassCurve.exists_ideal_heckeAlgebra_three_weight_le_four_…` | 25 / 8,648 | char-3, weight $`\le 4`$: classify `H¹` eigensystems | **yes**, on its current branch |

**Interface 1 wants existence, not surjectivity.** Its `R`-closure is the period
map (group 1), the $`T_\ell`$-equivariance (part of group 3), the integral
structure (part of group 5), the mod-$`p`$ eigenclass (group 7), and the
Shapiro/projLine and retraction carrier maps (group 4). Injection plus an
integral lattice is enough to produce the eigenclass.

**Interface 4 wants the full isomorphism.** Its path reaches the packaged
isomorphism through `HeckeEis.exists_modularForm_heckeTLin_eq_smul_of_isEigensystemH1`
("eigensystems in `H¹(Γ₀(N), Symⁿ)` arise from weight `n+2` forms") and the
boundary node. That is the surjectivity / Eisenstein half: every `H¹` eigensystem
comes from a form, which needs $`H^1_{par}`$ to be exactly the cuspidal part —
complementarity and, through it, the dimension theory. But the same input lemma
also cites the **intrinsic** mod-$`p`$ core
`ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen`, which sits on
the kept analytic core and not on `R`; so interface 4 has a routing choice, and
the full isomorphism is on only one of the two branches.

### 2.3 The 12-node analytic core

The driver's period map rests on the 12-node analytic set of the old scout §2.3:
the Eichler-integral existence input, the transport/slash and difference-by-a-
constant lemmas, the iterated-$`\partial_1`$ identity, the boundedness-at-cusp
lemma, the Hecke-correspondence transport, the two algebraic bridge lemmas, and
the period Hecke-equivariance and injectivity statements. The full list with line
counts is Appendix B. Of the twelve, **ten** are in the driver's closure; the two
not needed are `coeffH1Mk_cocycle_heckeTLin_modularForm` and
`modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero`, which belong to the
target-lemma form of the statement rather than to the isomorphism.

## 3. Baseline effort: the full isomorphism

### 3.1 The closure

The closure of `exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime` in
the pin is **645 nodes / 260,938 lines**. That headline is mostly geometry: the
dimension theory of group 6 reaches `ModularCurve.genusFormula`, `nuTwo`,
`nuThree`, `cuspCount`, the Riemann–Roch / `AlgebraicCurve` cone and the
`JZero`/`Tate` arithmetic. By namespace:

| namespace | nodes | lines | relation to the driver |
|---|---:|---:|---|
| `WeierstrassCurve` | 100 | 91,063 | shared endgame geometry (needed regardless) |
| `AlgebraicCurve` | 162 | 69,010 | shared geometry |
| `ModularCurve` | 266 | 67,287 | shared geometry |
| `HeckeEis` | 49 | 12,003 | **E-S-specific** |
| `PeriodPair` | 9 | 9,836 | shared uniformisation |
| others | ~59 | ~11,739 | mathlib gaps, `CuspForm`/`ModularForm` |

So the port surface that is *E-S-specific* is the `HeckeEis` 49, not the 645.

### 3.2 The E-S-specific surface

| piece | pin `S_` lines | note |
|---|---:|---|
| packaging, groups 1, 2, 3, 4, 6 (23 nodes) | 8,127 | the isomorphism proper |
| analytic core, 10 of 12 nodes | 1,388 | the period map's analysis |
| E-S dimension / representation helpers (16 nodes) | 2,488 | `exists_induced_binaryFormRepSL_top`, `le_finrank_fixed_*`, `exists_pairing_binaryForm_linePow`, `existsEichlerShimuraMapLinear`, … |
| definition modules (5) | 858 | `BinaryFormRep` 140, `Gamma0CoeffCohomology` 153, `Gamma0CoeffCohomologyEigen` 112, `HeckeEis_EichlerIntegral` 149, `Gamma0HeckeOperatorHom` 304 |
| external mathlib-absent lemmas (3) | 365 | star-convex antiderivative 150, boundedness-at-cusp 175, iterated `pderiv` 40 |
| `Thm_` statement files | ~250 | wrappers; a port states directly |

**Total: roughly 13,200 `S_` lines of E-S-specific Lean**, essentially none of it
already in the port. For comparison, route B's self-contained blob is 4,308
lines; the driver is the same order (about $`3\times`$) and strictly contains it.

The `R`-minus-driver remainder is the ten nodes the isomorphism does not use
(the eigenclass, the boundary, the projLine equivalence, the retraction, the
denominators); they are the optional door-2 layer of §6.

### 3.3 The external mathlib-absent lemmas

Three theorem dependencies are outside the 12 and absent from mathlib `v4.34.0`:

| lemma | `S_` lines | content |
|---|---:|---|
| `Complex.exists_hasDerivAt_of_starConvex` | 150 | radial path integral differentiated under the integral sign |
| `UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic` | 175 | $`v' = u`$, $`u`$ bounded and periodic, $`v`$ periodic $`\Rightarrow`$ $`v`$ bounded at the cusp |
| `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` | 40 | pure `MvPolynomial` algebra |

They are the analysis/analysis-adjacent gap and the first things a port must
write (§6).

## 4. What has already landed

The port (`lean/FLTForHuman`, 137 files / ~68,900 lines) already carries a large
part of the *shared* layer the driver needs, and none of the E-S-specific layer.

| landed | file | relevance to the driver |
|---|---|---|
| Hecke operators on forms `heckeTLin`/`heckeULin` | `ModularForms/HeckeOperatorForms.lean` (184) | the target of the Hecke-equivariance square |
| Hecke representatives on $`\mathbb{P}^1(\mathbb{F}_p)`$ | `ModularForms/Defs/HeckeRepresentatives.lean` | the coset/reindexing machinery |
| $`\Gamma_0(N)`$ index, $`\mathbb{P}^1(\mathbb{Z}/N)`$ count, Dedekind $`\psi`$ | `ModularCurve/Gamma0Index.lean` (773) | the dimension theory's index and cusp counts |
| Sturm bound, `finiteDimensional_Gamma0` | `ModularForms/SturmBound.lean` (451) | finite-dimensionality of cusp forms |
| C′ integral structure | `ModularForms/WeightOne/IntegralStructure.lean` | door 1 (not needed by the driver) |
| modular-curve geometry | `ModularCurve/*` (19,043), `AlgebraicCurve/*` | the shared geometry cone |

What is **not** landed, and is the E-S-specific gap:

* `BinaryForm`, `binarySubst`, `binaryFormRepSL`, `binaryFormAlphaAdj`;
* `coeffCocycles`, `coeffCoboundaries`, `coeffH1`, `coeffParabolicCocycles`,
  `coeffH1par`, `coeffHeckeFun`;
* `heckeUpper`, `heckeConj`, `transferAux`, `heckeOperatorHom` (the group
  correspondence underlying `coeffHeckeFun`);
* `IsEquivariantPrimitiveWith`, `IsEichlerIntegral`, `eichlerShimuraMap`;
* the ten analytic-core nodes and the three external lemmas;
* the dimension theory (`finrank_coeffH1par_*`, `ModularCurve.genusFormula`,
  `nuTwo`, `nuThree`, `cuspCount`);
* the conjugate-linear involution and the complementarity proof;
* the integral basis of $`H^1_{par}`$ and the eigenclass layer.

## 5. The effort relative to what landed

The honest split is:

* **Shared layer.** ~248k lines of the closure (modular-curve geometry,
  Riemann–Roch, $`J_0(N)`$/Tate arithmetic, cusp-form finite-dimensionality). The
  port already carries ~19k lines of it and needs the rest for the endgame
  regardless of the driver; the driver does not add to it except through the
  dimension theory's genus/cusp counts.
* **E-S-specific layer.** ~13,200 lines, ~0 landed. This is the marginal cost of
  the driver.

So the baseline is: **write the E-S-specific layer (~13k lines) on top of the
already-landed Hecke/geometry infrastructure.** That is a self-contained,
well-understood body of classical mathematics (one-variable complex analysis,
group cohomology in degree one, and a dimension count), not new theory. The three
mathlib-absent lemmas are the only places where the port is not assembling
existing pieces.

## 6. What to port next

The order below is dependency-driven; each tier is checkable on its own. The
first three tiers are the driver; tier 4 is the optional door-2 layer.

1. **Definitions.** `BinaryForm` + `binaryFormRepSL` + `binaryFormAlphaAdj`;
   `coeffCocycles`/`coeffCoboundaries`/`coeffH1`/`coeffParabolicCocycles`/
   `coeffH1par`/`coeffHeckeFun`; `heckeUpper`/`heckeConj`/`transferAux`; the
   Eichler-integral predicate. Small (~1,700 lines), self-contained, and the
   first thing that can be checked against the pin.
2. **The analysis.** The three mathlib-absent lemmas (the star-convex
   antiderivative, the boundedness-at-cusp implication, the iterated `pderiv`
   identity), then the ten analytic-core nodes: existence of the Eichler
   integral, its transport and difference-by-a-constant, the ladder and
   boundedness lemmas, the Hecke-correspondence transport.
3. **The period map and the isomorphism.** `eichlerShimuraMap` (`ES`) with its
   linearity, injectivity, and Hecke equivariance; the conjugate-linear
   involution; the integral basis; the dimension bound; and the complementarity
   that assembles the named driver `eichlerShimura_isomorphism`.
4. **Door 2 (optional, decides itself by interface 4).** The mod-$`p`$
   eigenclass, the Eisenstein boundary and the projLine/retraction carrier maps.
   Port these only if interface 4 keeps its packaging branch; otherwise the
   intrinsic mod-$`p`$ core covers interface 4 and interface 1 is the only
   consumer (§2.2).

Stop condition: if tier 3's dimension bound turns out to need a large unported
slice of the `ModularCurve` genus/cusp cone, decide explicitly whether to port
that geometry now or to state the driver for a level where the bound is already
available.

## 7. Reproduction

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from fltdata import FltData
from prune import FltPayoff, build_removed, DEFAULT_ROOT, INTERFACES, ANALYTIC_12
d = FltData(); pay = FltPayoff(data=d)
port = pay.closure(pay.pid(DEFAULT_ROOT))
full = d.index['HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime']
R = set(build_removed(pay, "packaging", port)[0])
A12 = {d.index[q] for q in ANALYTIC_12}
C = pay.closure(full)
print('iso closure:', len(C), pay.total_lines(C))
print('  R:', len(C & R), pay.total_lines(C & R))
print('  core:', len(C & A12), pay.total_lines(C & A12))
print('  HeckeEis:', len([i for i in C if d.qual(i).startswith('HeckeEis.')]),
      pay.total_lines([i for i in C if d.qual(i).startswith('HeckeEis.')]))
for n, q in INTERFACES:
    print('interface', n, 'R-closure', len(pay.closure(d.index[q]) & R))
PY
```

## Appendix A — the 33 packaging nodes of `R`

Line counts are the pin's `S_`-file lines; titles are the pin's generated English
titles. Statement files are `Theorems/Thm_<stem>.lean` with `<stem>` the
qualified name with dots replaced by underscores (pin `aa2d8b3`).

### 1. The period map (4 / 394)

| node (`HeckeEis.`) | lines | content |
|---|---:|---|
| `eichlerShimuraMap_eq_coeffH1parMk` | 48 | computed by any admissible Eichler integral |
| `eichlerShimuraMap_add` | 81 | additivity |
| `eichlerShimuraMap_smul` | 79 | ℂ-homogeneity |
| `eichlerShimuraMap_injective` | 186 | injectivity via the negative-weight form |

### 2. The two halves (5 / 2,000)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_semilinearMap_starRingEnd` | 332 | conjugate-linear involution on $`H^1_{par}`$ |
| `isCompl_range_eichlerShimuraMap_range_conj` | 185 | the two images are complementary |
| `range_eichlerShimuraMap_inf_range_conj_eq_bot` | 1,325 | they meet only in 0 (the hard half) |
| `exists_eichlerShimura_coeffH1par_binaryFormRepSL` | 48 | the packaged isomorphism |
| `exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime` | 110 | the same with all Hecke operators |

### 3. Hecke equivariance (4 / 1,742)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_linearMap_coeffHeckeFun` | 80 | the cohomological $`T_\ell`$ exists |
| `coeffH1par_map_heckeT_comm` | 113 | coefficient change commutes with $`T_\ell`$ |
| `eichlerShimuraMap_heckeTLin` | 907 | $`ES`$ intertwines $`T_\ell`$ (good $`\ell`$) |
| `eichlerShimuraMap_heckeULin` | 642 | $`ES`$ intertwines $`U_\ell`$ (bad $`\ell`$) |

### 4. Coefficient change and functoriality (3 / 1,142)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_map_ringHom` | 258 | coefficient extension on $`H^1_{par}`$ |
| `exists_coeffH1par_map_of_equivariant_retraction` | 174 | equivariant retractions (interface 1) |
| `exists_coeffH1par_projLineRepSL_equiv_parabolicHoms` | 710 | Shapiro/projLine bridge |

### 5. Integral structure (9 / 3,521)

| node | lines | content |
|---|---:|---|
| `coeffH1par_binaryFormRepSL_int_eq_zero_of_smul_eq_zero` | 138 | torsion-freeness |
| `coeffH1par_binaryFormRepSL_eq_zero_of_odd` | 71 | odd $`n`$ vanishes |
| `coeffH1par_map_int_rat_injective` | 426 | $`\mathbb{Z}\to\mathbb{Q}`$ injective |
| `linearIndependent_coeffH1par_map_rat_complex` | 470 | independence persists over ℂ |
| `mem_span_range_coeffH1par_map_rat_complex` | 471 | rational classes span over ℂ |
| `exists_basis_coeffH1par_int_complex` | 316 | integral basis maps to a ℂ-basis |
| `span_range_coeffH1par_map_int_complex_eq_top` | 54 | integral classes span |
| `exists_ne_zero_smul_eq_coeffH1par_map_int_rat` | 789 | nonzero integral multiples |
| `exists_eq_prime_smul_of_coeffH1par_map_eq_zero` | 786 | mod-$`p`$ kernel is $`p`$-divisible |

### 6. Dimension theory (4 / 1,180)

| node | lines | content |
|---|---:|---|
| `finrank_coeffH1par_top_add_le` | 393 | Euler-characteristic bound for $`\mathrm{SL}_2(\mathbb{Z})`$ |
| `finrank_coeffH1par_gamma0_le_finrank_coeffH1par_top_induced` | 500 | Shapiro monotonicity |
| `finrank_coeffH1par_le_two_mul_dimFormula` | 120 | $`\dim H^1_{par} \le 2\dim S_{n+2}`$ |
| `finrank_coeffH1par_zero_le_two_mul_genusFormula` | 167 | weight-2 bound $`2g`$ |

### 7. Mod-$`p`$ eigenclass and boundary (4 / 810)

| node | lines | content |
|---|---:|---|
| `exists_coeffH1par_int_modp_eigenclass_of_eigenform` | 205 | integral eigenclass mod $`p`$ |
| `exists_coeffH1par_int_modp_eigenclass_of_ideal_heckeAlgebra` | 71 | from a maximal Hecke ideal |
| `exists_coeffH1par_binaryFormRepSL_eigenclass_of_ideal_heckeAlgebra_of_ne_two` | 61 | char-$`p`$ eigensystem (interface 1) |
| `exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1` | 473 | the Eisenstein boundary is form-theoretic |

## Appendix B — the 12-node analytic core

`S_` lines, old scout §2.3 order (the first ten are in the driver's closure).

| # | node (`HeckeEis.`) | `S_` lines | content |
|---|---|---:|---|
| 1 | `exists_isEichlerIntegral` | 102 | existence of the Eichler integral |
| 2 | `isEquivariantPrimitiveWith_of_isEichlerIntegral` | 46 | EI + slash-invariance $`\Rightarrow`$ primitive |
| 3 | `IsEichlerIntegral.slash` | 191 | EI transported by $`\delta`$ |
| 4 | `IsEichlerIntegral.exists_sub_eq_const` | 172 | two EI differ by a constant |
| 5 | `IsEichlerIntegral.eq_zero_of_eval_eq_const` | 92 | constant eval of an EI forces $`g = 0`$ |
| 6 | `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` | 305 | iterated $`\partial_1`$ identity |
| 7 | `IsEichlerIntegral.isBoundedAtImInfty_eval` | 178 | growth at the cusp |
| 8 | `IsEichlerIntegral.binarySubst_adjugate_comp_smul` | 184 | EI transported along the Hecke correspondence |
| 9 | `IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` | 44 | primitives differing by a constant give coboundary differences |
| 10 | `jFactor_pow_mul_eval_binaryFormRepSL` | 74 | automorphy-factor identity |
| 11 | `coeffH1Mk_cocycle_heckeTLin_modularForm` | 633 | Hecke equivariance of the period class (target lemma only) |
| 12 | `modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` | 280 | period injectivity (target lemma only) |
