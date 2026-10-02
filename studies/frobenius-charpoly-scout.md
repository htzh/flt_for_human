# Which Frobenius characteristic polynomial is the most basic?

**Status: scouting note, measured 2026-10-02** against the pin `aa2d8b3` with
`tools/deps` (the FLT dependency graph and the pin's `S_` files). It answers:
*among the many statements that pin the characteristic polynomial of a Frobenius
element, which one sits **under** the others — i.e. which is the primitive form
the rest are versions of?*

Prior coverage. [../base/010-finite-fields-frobenius-and-point-counts.md](../base/010-finite-fields-frobenius-and-point-counts.md)
is the mathematics of the **elliptic-curve** version: it defines
`FrobCharEqOnPoints`, derives
$`\varphi_q^2 - a_q\varphi_q + q = 0`$, and names
`ResidualGaloisRep.IsAttachedTo` as the modularity bridge. [../math/011-tate-module.md](../math/011-tate-module.md)
§5.3 documents the **$`J_0`$ / divisorial** version's packaging
(`EichlerShimuraData`, `FrobeniusQuadratic`, `CuspForm.HeckeGaloisRepDatum`,
`IsAttachedTo`). Neither asks the dependency question — *which of these is the
bottom?* — and the answer is not what either note's framing suggests: there are
**three** independent bottoms, and the Deligne–Serre cone uses only one of them
(§6).

## 0. Verdict

**There is no single bottom. The family is a three-root DAG.** The primitive
form is the *quadratic relation*

$$\sigma^2 x - T_\ell\\,\sigma x + \ell\\,x = 0,$$

because in rank $`2`$ the characteristic-polynomial identity
$`\mathrm{charpoly}(f) = X^2 - aX + b`$ is *equivalent* to (the quadratic relation
with trace $`a`$) together with $`\det f = b`$. Every "Frobenius charpoly" in the
pin is obtained by proving that relation and then converting. The relation is
proved **three times**, from pairwise unrelated inputs:

* the **E-root**, `FrobeniusEndo.frobCharEqOnPoints_of_frobenius` — the pointwise
  relation on the points of an elliptic curve over a finite field, from kernel
  counts (the subject of [base/010](../base/010-finite-fields-frobenius-and-point-counts.md));
* the **$`J_0`$-root**, `ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero`
  — the Eichler–Shimura congruence on the divisorial model
  $`\mathrm{Pic}^0`$ of the $`\mathbb{Q}`$-modular function field in characteristic
  $`\ell`$;
* the **q-expansion root**, `ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental`
  — the same congruence $`\mathrm{Fr}^\ast\mathrm{Fr}_\ast = \ell`$ on the
  $`q`$-expansion function field of $`X_1(M)`$ / $`X_H(M)`$, which is a **disjoint**
  route: neither of the two $`J`$ roots is in the other's cone, and both are
  disjoint from the E-root.

| reading of "most basic Frobenius charpoly" | answer | evidence |
|---|---|---|
| fewest hypotheses, most upstream, *about Frobenius* | the quadratic relation (three roots) | charpoly $`\iff`$ relation $`+`$ determinant in rank 2 |
| literally a characteristic-polynomial statement | `LinearMap.charpoly_of_finrank_eq_two` | 0 premises, 13 `S_` lines, 11 consumers; E-side only (the $`J`$ sides re-prove the conversion, §4) |
| the single node carrying the most *other* versions | `ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero` (tied with the q-expansion root) | 8 of the 35 curated family nodes rest on each — but the $`J_0`$ branch is the one the Deligne–Serre cone does **not** use (§6) |

## 1. What counts as a "version"

Two layers have to be separated, because the pin's *definitions* are not
statements about a charpoly and its *statements* are not definitions.

**Definitions that encode the charpoly.** Three shapes occur:

| definition | where | what it says |
|---|---|---|
| `ModularCurve.FrobeniusQuadratic` | [Def_HeckeGalois_EichlerShimura.lean:130](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L130-L135) | the *quadratic relation* on $`p`$-power torsion of a Hecke module $`J`$ |
| `ModularCurve.SpecializationExists` / `IsSpecialization` / `SpecialFibreRelation` | [:197, :208, :219](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L197-L225) | the special-fibre datum from which the relation is transported |
| `CuspForm.HeckeGaloisRepDatum.charpoly_frob` | [Def_CuspForm_HeckeGaloisRepDatum.lean:31](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean#L31-L34) | a *charpoly equality* field, $`\mathrm{charpoly}(\rho(\sigma)) = X^2 - \pi(T_\ell)X + \ell`$ |
| `ResidualGaloisRep.IsAttachedTo` | [Def_GaloisRep_Residual.lean:48](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean#L48-L55) | the same equality in the curve direction, $`X^2 - \varphi(a)X + \ell`$ |
| `FrobCharEqOnPoints` | [Def_EllipticCurve_FrobeniusEndo.lean:50](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusEndo.lean#L50) | the E-side pointwise relation of [base/010](../base/010-finite-fields-frobenius-and-point-counts.md) |

Note the split: the E-side and the two Jacobian sides encode the **relation**;
the Hecke-datum and residual-attachment predicates encode the **charpoly
equality**. The conversion between the two shapes is where the work is (§4).

**Statements that prove a version.** The family used below is the 34 nodes
reached by `charpoly`/`frobeniusQuadratic` in the qualified name, grouped by
role, and measured in §7.

## 2. The E-side cone

Everything rests on the pointwise relation, and the chain is short
(the mathematics is [base/010](../base/010-finite-fields-frobenius-and-point-counts.md)):

```
FrobeniusEndo.frobCharEqOnPoints_of_frobenius        (23 lines, 4 premises)
   |  σ²P − a·σP + q·P = 0 on (W/k).Point
   v
WeierstrassCurve.frobenius_cayleyHamilton_on_torsion (274 lines, 1 premise)
   |  the same on prime-to-ℓ torsion of W/ℚ̄
   v
WeierstrassCurve.tateModuleRep_charpoly_frobenius     (98 lines, 4 premises)
      charpoly(ρ(σ)) = X² − C(a_ℓ)·X + C(ℓ) on T_pE
```

`tateModuleRep_charpoly_frobenius` is the only place the *charpoly* shape is
produced on this side, and its four premises are exactly the decomposition
"relation + determinant + rank-two dictionary":

1. `frobenius_cayleyHamilton_on_torsion` — the relation;
2. `WeierstrassCurve.tateModuleRep_det_frobenius` — the determinant $`\ell`$;
3. `LinearMap.trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq` — trace from
   relation + determinant (37 lines, 2 consumers);
4. `LinearMap.charpoly_eq_iff_of_finrank_eq_two` — the coefficient criterion
   (21 lines, 3 consumers).

The proof is literally
`LinearMap.charpoly_eq_iff_of_finrank_eq_two hrank f ⟨trace_eq_…, hdet⟩`
([S file:96](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_tateModuleRep_charpoly_frobenius.lean#L96-L98)).
So on the E-side the *bottom of the charpoly family is the relation*, and the
conversion is done through **shared** Mathlib-shaped nodes.

**The E-root is used by nobody in the modular-form direction.** Its two consumers
are `WeierstrassCurve.frobenius_cayleyHamilton_on_torsion` and
`FrobeniusEndo.galoisTrace_frob_eq_of_line_of_charEqOnPoints`; the whole E-cone
serves the **elliptic-curve** side (the Frey curve's Tate module), not the
modular form side.

## 3. The Jacobian side is two disjoint routes

The two $`J`$ roots both state the same quadratic relation, and neither is a
premise of the other (verified transitively: the $`J_0`$-root's cone is 111 nodes
and does not contain the q-expansion root; the q-expansion root's cone is 42
nodes and does not contain the $`J_0`$-root).

### 3.1 The $`J_0`$ / divisorial route

```
ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero
   |  Fr*(Fr* y) − T̄_ℓ(Fr* y) + ℓ·y = 0 on J₀C in char ℓ     (918 lines, 2 premises)
   +-------------------------------+
   v                               v
frobeniusQuadratic_JZero      frobeniusQuadratic_tateModule_jZero
 (79 lines, 994 below)          (105 lines, 993 below)
                               |
                     exists_galoisRepAdic_charpoly_frobenius_of_heckeChar (J₀, 736)
                               |
                     CuspForm.exists_galoisRep_of_point          (Γ₀ consumer)
```

The root's two premises are pure geometry — `nonempty_modularPolynomialData`
and `AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable` — so it is a
genuine source. The abstract `ModularCurve.FrobeniusQuadratic` plus
`of_specializationExists` is a *parallel* packaging of this route:
`W54.jZeroPPowTorsion_frobeniusQuadratic` reaches the relation through
`specializationExists_JZero` and `of_specializationExists` rather than through
the root directly.

### 3.2 The q-expansion / $`\Gamma_1`$–$`\Gamma_H`$ route

```
ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
   |  Fr*Fr_* = ℓ on Pic⁰ of the q-expansion function field, char ℓ   (568 lines, 2 premises)
   +-------------------+--------------------+
   v                   v                    v
reductionQExpModL_  reductionQExpModL_    (both γ_H and γ₁ instances:
gammaH_hecke…       gamma1_hecke…         470 / 566 lines)
   +-------------------+--------------------+
   v                                        v
frobeniusQuadratic_tateModule_jH     frobeniusQuadratic_tateModule_jOne
   (145 lines)                          (240 lines)
                                        |
              exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar (J₁, 727)
                                        |
              CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt (319)
```

This route is **not** a reduction of §3.1: it works on the $`q`$-expansion
function field (a different model of the same Jacobians) and its special-fibre
relation is proved from `ModularCurve.reductionQExpModL_gamma*_*` and the
perfect-field/transcendental generator input, not from the divisorial root. The
$`J_1`$ node is the one the **Deligne–Serre** cone consumes (§6).

### 3.3 The charpoly payloads

Both $`J`$ routes end in an `exists_galoisRepAdic_charpoly_frobenius_of_…`
statement that produces the charpoly *equality*:
`…_of_heckeChar` (Γ₀, cites `frobeniusQuadratic_tateModule_jZero` plus the
rank-two/cyclotomic determinant `rationalRankTwoCyclotomic_family`) and
`…_of_heckeDiamondChar` (Γ₁, cites `frobeniusQuadratic_tateModule_jOne` plus
`rationalRankTwoNebentypus_family`). For $`J_1`$ the determinant is the
nebentypus $`d`$ and the charpoly is $`X^2 - daX + d\ell`$.

## 4. The shared floor, and the conversion that is re-proved eight times

The statement under the E-cone that is *literally* about a characteristic
polynomial — and the only rank-two dictionary in the graph — has no Frobenius
content at all:

```lean
theorem LinearMap.charpoly_of_finrank_eq_two … (h : Module.finrank R M = 2) (f : M →ₗ[R] M) :
    f.charpoly = X ^ 2 - C (LinearMap.trace R M f) * X + C (LinearMap.det f)
```

([Thm:9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_LinearMap_charpoly_of_finrank_eq_two.lean#L9),
13 `S_` lines, **0 premises**, 11 consumers). Its thinnest Galois wrapper is
`ResidualGaloisRep.charpoly_eq` (9 lines, cites only this), which is the
"charpoly = trace/det" normal form for residual representations.

**The E-side uses this floor; neither $`J`$ route does.** The $`J`$-side payload
proofs each carry a *private* `charpoly_eq_of_quadratic_of_det` that re-derives
charpoly from (relation, determinant) by hand — Cayley–Hamilton for the
$`X`$-coefficient, then comparison — because the shared
`LinearMap.trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq` is an operator-algebra
statement and the $`J`$-side argument is a polynomial-coefficient one. That
private helper occurs in **8 files**:

```
S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeChar.lean:593
S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar.lean:580
S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeChar_tateModule_quotient.lean
S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar_tateModule_quotient.lean
S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_and_inertia_mul_eq_zero_….lean
S_CuspForm_IsNormalizedEigenform_exists_residualGaloisRep_isAttachedTo.lean
S_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_charpoly_frobenius_eq_and_isRoot_charpoly_one_….lean
S_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_linearIndependent_inertia_apply_eq_smul_….lean
```

Its statement (from the $`J_1`$ payload) is

```lean
theorem charpoly_eq_of_quadratic_of_det (hV : Module.finrank O V = 2)
    (f : Module.End O V) (hf : IsUnit f) (t d : O)
    (hq : f * f - t • f + algebraMap O (Module.End O V) d = 0) (hdet : LinearMap.det f = d) :
    f.charpoly = X ^ 2 - C t * X + C d
```

This is the actionable finding: **the conversion "relation + determinant
$`\Rightarrow`$ charpoly" has no shared home.** It is a Mathlib-shaped lemma,
it is the exact step every charpoly production needs, and the pin proves it
eight times privately. Compare `LinearMap.charpoly_of_finrank_eq_two` (E-side,
shared) — the $`J`$ sides are missing its analogue.

## 5. Where the routes meet: the determination lemmas

The three routes never share a Frobenius *production*; they are joined by
Chebotarev, which extends agreement at Frobenii to the whole group:

| node | `S_` lines | cited by | role |
|---|---:|---:|---|
| `GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq` | 199 | **38** | adic comparison |
| `ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq` | 104 | **20** | residual comparison |
| `GaloisRepAdic.isEquiv_of_charpoly_frobenius_eq` | 39 | 6 | charpolys $`+`$ absolute irreducibility $`\Rightarrow`$ equivalence |
| `GaloisRepAdic.localType_congr_of_charpoly_frobenius_eq` | 30 | 8 | transport of local types |

These carry the many `…_of_charpoly_frobenius_eq` consumers (the `heckeLocal`,
`heckeAlgebra` and `TWLevel` families), which is why they top a naive
"cited-by" ranking. They are *determination*, not *production*: they take the
Frobenius charpoly agreement as a hypothesis. They are the reason the family
looks like one object when it is three.

## 6. Which route the Deligne–Serre cone actually uses

The D–S forward cone is the closure of
`DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` (2,308 nodes;
[deligne-serre-weight-one-scout.md](deligne-serre-weight-one-scout.md) §2).
Membership of the three routes in that cone:

| route | root in the D–S cone? | downstream nodes in the cone |
|---|---|---|
| E (point counts) | **no** | none — `frobCharEqOnPoints_of_frobenius`, `frobenius_cayleyHamilton_on_torsion`, `tateModuleRep_charpoly_frobenius` all absent |
| $`J_0`$ / divisorial | **no** | none — `frobenius_frobenius_sub_…`, `frobeniusQuadratic_JZero`, `_tateModule_jZero`, `of_specializationExists`, the `W54.*` forms all absent |
| q-expansion / $`\Gamma_1`$ | **yes** | `qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental`, `reductionQExpModL_gamma1_heckeOperatorOneBar`, `frobeniusQuadratic_tateModule_jOne` |

The cone contains exactly **13** nodes with `charpoly` / `frobeniusQuadratic` in
the name, all on the $`q`$-expansion route:

```
ModularCurve.frobeniusQuadratic_tateModule_jOne
ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar
CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt
DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightTwo_hecke_eigen
DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen
GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel
GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range
DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range
DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le
Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top
Representation.exists_conj_eq_of_charpoly_eq_of_finite_range
Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard
```

Note what is **absent** even though it is the shared floor: neither
`LinearMap.charpoly_of_finrank_eq_two` nor
`LinearMap.charpoly_eq_iff_of_finrank_eq_two` is in the cone. The D–S charpoly
work goes through the *private* `charpoly_eq_of_quadratic_of_det` of §4, exactly
as the route analysis predicted — the dependency graph does not even record the
conversion, because the pin re-proves it privately. So the "most basic" node by
citation is not reachable here, and the branch that *is* used is the one neither
[base/010](../base/010-finite-fields-frobenius-and-point-counts.md) (E-side) nor
[math/011 §5.3](../math/011-tate-module.md) ($`J_0`$ packaging) describes.

**Consequence for the $`J_0`$ route.** `frobenius_frobenius_sub_…` is the family
node with the most versions above it (§0), yet the whole $`J_0`$ route is dead
weight for the Deligne–Serre cone. The route that matters there is the
$`q`$-expansion one, and it is a *different proof of the same relation*, so any
porting effort split between the two is duplicated arithmetic. The porting topic
for the q-expansion root is
[`lean/topics/charLFrobenius/TOPIC-qexp-frobenius-modl.md`](../lean/topics/charLFrobenius/TOPIC-qexp-frobenius-modl.md)
(11 needed nodes / 1,669 raw `S_` lines, plus the unported `qExpFrobenius*`
definition layer).

## 7. The family, measured

`dep` is distance from `fermat_last_theorem`; `below` is the import closure;
`cb` is cited-by; `S_` is the pin's proof-file line count. Branch labels:
**E** = point counts, **J₀** = divisorial, **Jq** = $`q`$-expansion.

| node | branch | dep | below | cb | `S_` |
|---|---|---:|---:|---:|---:|
| `LinearMap.charpoly_of_finrank_eq_two` | — | 8 | 0 | 11 | 13 |
| `LinearMap.charpoly_eq_iff_of_finrank_eq_two` | — | 9 | 1 | 3 | 21 |
| `LinearMap.trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq` | — | 9 | 1 | 2 | 37 |
| `ResidualGaloisRep.charpoly_eq` | — | 10 | 1 | 2 | 9 |
| **E:** `FrobeniusEndo.frobCharEqOnPoints_of_frobenius` | E | 7 | 23 | 2 | 23 |
| **E:** `WeierstrassCurve.frobenius_cayleyHamilton_on_torsion` | E | 6 | 24 | 3 | 274 |
| **E:** `WeierstrassCurve.tateModuleRep_charpoly_frobenius` | E | 8 | 70 | 4 | 98 |
| `ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero` | J₀ | 9 | 111 | 8 | 918 |
| `ModularCurve.FrobeniusQuadratic.of_specializationExists` | J₀ | 9 | 0 | 5 | 28 |
| `ModularCurve.frobeniusQuadratic_JZero` | J₀ | 8 | 994 | 11 | 79 |
| `ModularCurve.frobeniusQuadratic_tateModule_jZero` | J₀ | 10 | 993 | 9 | 105 |
| `W54.jZeroPPowTorsion_frobeniusQuadratic` | J₀ | 10 | 1034 | 6 | 35 |
| `W54.tateModule_frobeniusQuadratic` | J₀ | 11 | 0 | 5 | 22 |
| `ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental` | Jq | 19 | 42 | 5 | 568 |
| `ModularCurve.reductionQExpModL_gamma1_heckeOperatorOneBar` | Jq | 19 | 984 | 4 | 470 |
| `ModularCurve.frobeniusQuadratic_tateModule_jOne` | Jq | 18 | 1002 | 3 | 240 |
| `ModularCurve.frobeniusQuadratic_tateModule_jH` | Jq | 18 | 1005 | 5 | 145 |
| `ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeChar` | J₀ | 9 | 1238 | 2 | 736 |
| `ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar` | Jq | 17 | 1377 | 1 | 727 |
| `CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt` | Jq | 16 | 1478 | 11 | 319 |
| `CuspForm.IsNormalizedEigenform.exists_galoisRepAdic_charpoly_frobenius_eq_of_isMaximal` | Jq | 19 | 1335 | 1 | 322 |
| `GaloisRepAdic.charpoly_baseChangeAlong` | — | 8 | 0 | 50 | 9 |
| `GaloisRepAdic.charpoly_eq_of_isEquiv` | — | 8 | 0 | 6 | 13 |
| `GaloisRepAdic.charpoly_residual` | — | 8 | 0 | 34 | 7 |
| `GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq` | — | 9 | 21 | 38 | 199 |
| `ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq` | — | 8 | 4 | 20 | 104 |

## 8. Consequences

**For the notes.** [base/010](../base/010-finite-fields-frobenius-and-point-counts.md)
answers the E-side question completely and is the right place to read
$`\varphi_q^2 - a_q\varphi_q + q = 0`$. What it does not state — and what a
reader arriving from it will expect — is that the pin's *other* Frobenius
charpoles are **not** derived from `FrobCharEqOnPoints`; they are derived from
the char-$`\ell`$ Eichler–Shimura congruence, and there are two independent
proofs of that congruence ($`J_0`$ divisorial and $`q`$-expansion).
[math/011 §5.3](../math/011-tate-module.md) documents the first; the Deligne–
Serre cone uses the second. A note on the modular-form attachment should say
which model it is on, and should present the *relation + determinant* normal
form (with the determinant as the cyclotomic character of
[base/007](../base/007-weil-pairing.md)) rather than starting from the charpoly
equality.

**For the port.** Of the family, only two *Galois-side* nodes are ported —
`GaloisRepAdic.charpoly_baseChangeAlong` and `charpoly_eq_of_isEquiv`, both in
`lean/FLTForHuman/GaloisRep/AdicCharpoly.lean`; the `LinearMap.*` nodes are
Mathlib's and are already available. The Deligne–Serre port should take the
$`q`$-expansion route (§6), not the $`J_0`$ one, and should add the shared
conversion lemma the pin lacks: a
`LinearMap.charpoly_eq_iff_of_finrank_eq_two`-shaped statement taking the
quadratic relation and the determinant directly (the private
`charpoly_eq_of_quadratic_of_det` of §4). That single promotion replaces eight
private copies.

**Landed (2026-10-02).** The promotion is written, as recommended:
`LinearMap.charpoly_eq_of_quadratic_of_det` in
[`../lean/FLTForHuman/Algebra/CharpolyOfQuadratic.lean`](../lean/FLTForHuman/Algebra/CharpolyOfQuadratic.lean),
statement-identical to the pin's eight copies, with the companion
`eq_zero_of_smul_id_eq_zero` private. It verifies through the statement checker
against the pin's own declaration (the `S_` carrier is registered in `SOURCES`),
so no exemption was needed; axioms are `[propext, Classical.choice, Quot.sound]`,
and `spec/DeligneSerreConsumer.lean` zone S9 is the executed wire test.

## Method

* Graph readings (depth, closure, citation direction, induced family order,
  cone membership) are from the pin's docs-site data via `tools/deps/fltdata.py`;
  the per-node dossiers from `tools/deps/explore.py`.
* `S_` line counts are `wc -l` on the pin's `P2M/Sol/S_<stem>.lean`.
* The three-root claim is the induced-subgraph result: over the 35 curated
  family nodes, the E-root has 3 family members above it, the $`J_0`$-root has
  8, and the $`q`$-expansion root has 8; the $`J_0`$-root's 111-node cone and the
  $`q`$-expansion root's 42-node cone are disjoint, and both are disjoint from
  the E-cone.
* The Deligne–Serre membership result is
  `closure(DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen)`,
  2,308 nodes, filtered by the three roots and their chains.
* Line-number links are pinned to `aa2d8b3`, as required for `blob/` anchors.
