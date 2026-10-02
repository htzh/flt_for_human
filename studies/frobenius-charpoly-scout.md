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
§5.3 documents the **Jacobian** version's packaging (`EichlerShimuraData`,
`FrobeniusQuadratic`, `CuspForm.HeckeGaloisRepDatum`, `IsAttachedTo`). Neither
asks the dependency question — *which of these is the bottom?* — which is the
question here, and whose answer is not the one either note's framing suggests.

## 0. Verdict

**There is no single bottom. The family is a two-root DAG.** The primitive form
is the *quadratic relation*

$$\sigma^2 x - T_\ell\\,\sigma x + \ell\\,x = 0,$$

because in rank $`2`$ the characteristic-polynomial identity
$`\mathrm{charpoly}(f) = X^2 - aX + b`$ is *equivalent* to (the quadratic relation
with trace $`a`$) together with $`\det f = b`$. Every "Frobenius charpoly" in the
pin is obtained by proving that relation and then converting. The relation is
proved **twice**, from two unrelated inputs:

* the **E-side root**, `FrobeniusEndo.frobCharEqOnPoints_of_frobenius` — the
  pointwise relation on the points of an elliptic curve over a finite field,
  from kernel counts (the subject of [base/010](../base/010-finite-fields-frobenius-and-point-counts.md));
* the **J-side root**, `ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero`
  — the Eichler–Shimura congruence $`\mathrm{Fr}^\ast\mathrm{Fr}_\ast = \ell`$ in
  characteristic $`\ell`$ on $`J_0(N)`$.

No node in the pin has both cones below it. They meet only at the Chebotarev
*determination* lemmas (§5), which is a comparison, not a proof of either.

| reading of "most basic Frobenius charpoly" | answer | evidence |
|---|---|---|
| fewest hypotheses, most upstream, *about Frobenius* | the quadratic relation (two roots) | charpoly $`\iff`$ relation $`+`$ determinant in rank 2 |
| literally a characteristic-polynomial statement | `LinearMap.charpoly_of_finrank_eq_two` | 0 premises, 13 `S_` lines, 11 consumers; E-side only (the J-side re-proves the conversion, §4) |
| the single node carrying the most *other* versions | `ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero` | 8 of the 34 curated family nodes rest on it |

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

Note the split: the E-side and the Jacobian side encode the **relation**; the
Hecke-datum and residual-attachment predicates encode the **charpoly equality**.
The conversion between the two shapes is where the work is (§4).

**Statements that prove a version.** The family used below is the 34 nodes
reached by `charpoly`/`frobeniusQuadratic` in the qualified name, grouped by
role, and measured in §6.

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

## 3. The J-side cone

The Jacobian side has its own root, a geometric statement about the special
fibre of the modular curve — not a point count:

```
ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero
   |  Fr*(Fr* y) − T̄_ℓ(Fr* y) + ℓ·y = 0 on J₀(N) in char ℓ     (918 lines, 2 premises)
   +-----------------------------+-------------------------------+
   v                             v                               v
frobeniusQuadratic_JZero   frobeniusQuadratic_tateModule_    FrobeniusQuadratic.of_specializationExists
 (79 lines, 994 below)       jZero/jOne/jH (105/240/145)        (28 lines, generic lift)
                              |                               W54.jZeroPPowTorsion_frobeniusQuadratic (35)
                              v                               W54.tateModule_frobeniusQuadratic (22)
   exists_galoisRepAdic_charpoly_frobenius_of_heckeChar (J₀, 736)
   exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar (J₁, 727)
                              v
   CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt (319)
```

The root's two premises are pure geometry — `nonempty_modularPolynomialData`
and `AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable` — so it is a
genuine source, not a reduction. The abstract
`ModularCurve.FrobeniusQuadratic` and its `of_specializationExists` lift are a
*parallel* packaging: the Tate-module instances
(`frobeniusQuadratic_tateModule_jZero/jOne/jH`) cite the root **directly**, not
through `FrobeniusQuadratic`, which is why `frobeniusQuadratic_JZero` and
`W54.jZeroPPowTorsion_frobeniusQuadratic` are siblings of the Tate forms rather
than ancestors of them (the instance list is also
[flt-non-frey-segments.md](flt-non-frey-segments.md) §"what FLT already has").

The payload `exists_galoisRepAdic_charpoly_frobenius_of_heckeChar` then produces
the charpoly *equality*: it cites `frobeniusQuadratic_tateModule_jZero`
alongside the rank-two/cyclotomic determinant input
`rationalRankTwoCyclotomic_family`, and converts. For $`J_1`$ the determinant is
the nebentypus $`d`$ and the charpoly is $`X^2 - daX + d\ell`$.

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

**The E-side uses this floor; the J-side does not.** The J-side payload proofs
each carry a *private* `charpoly_eq_of_quadratic_of_det` that re-derives
charpoly from (relation, determinant) by hand — Cayley–Hamilton for the
$`X`$-coefficient, then comparison — because the shared
`LinearMap.trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq` is an operator-algebra
statement and the J-side argument is a polynomial-coefficient one. That private
helper occurs in **8 files**:

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

Its statement (from the J₁ payload) is

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
shared) — the J-side is missing its analogue.

## 5. Where the cones meet: the determination lemmas

The E-cone and J-cone never share a Frobenius *production*; they are joined by
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
looks like one object when it is two.

## 6. The family, measured

`dep` is distance from `fermat_last_theorem`; `below` is the import closure;
`cb` is cited-by; `S_` is the pin's proof-file line count.

| node | dep | below | cb | `S_` |
|---|---:|---:|---:|---:|
| `LinearMap.charpoly_of_finrank_eq_two` | 8 | 0 | 11 | 13 |
| `LinearMap.charpoly_eq_iff_of_finrank_eq_two` | 9 | 1 | 3 | 21 |
| `LinearMap.trace_eq_of_sq_sub_smul_add_eq_zero_of_det_eq` | 9 | 1 | 2 | 37 |
| `ResidualGaloisRep.charpoly_eq` | 10 | 1 | 2 | 9 |
| **E:** `FrobeniusEndo.frobCharEqOnPoints_of_frobenius` | 7 | 23 | 2 | 23 |
| **E:** `WeierstrassCurve.frobenius_cayleyHamilton_on_torsion` | 6 | 24 | 3 | 274 |
| **E:** `WeierstrassCurve.tateModuleRep_charpoly_frobenius` | 8 | 70 | 4 | 98 |
| **J:** `ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero` | 9 | 111 | 8 | 918 |
| **J:** `ModularCurve.FrobeniusQuadratic.of_specializationExists` | 9 | 0 | 5 | 28 |
| **J:** `ModularCurve.frobeniusQuadratic_JZero` | 8 | 994 | 11 | 79 |
| **J:** `W54.jZeroPPowTorsion_frobeniusQuadratic` | 10 | 1034 | 6 | 35 |
| **J:** `ModularCurve.frobeniusQuadratic_tateModule_jZero` | 10 | 993 | 9 | 105 |
| **J:** `ModularCurve.frobeniusQuadratic_tateModule_jOne` | 18 | 1002 | 3 | 240 |
| **J:** `ModularCurve.frobeniusQuadratic_tateModule_jH` | 18 | 1005 | 5 | 145 |
| **J:** `W54.tateModule_frobeniusQuadratic` | 11 | 0 | 5 | 22 |
| `ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeChar` | 9 | 1238 | 2 | 736 |
| `ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar` | 17 | 1377 | 1 | 727 |
| `CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt` | 16 | 1478 | 11 | 319 |
| `CuspForm.IsNormalizedEigenform.exists_galoisRepAdic_charpoly_frobenius_eq_of_isMaximal` | 19 | 1335 | 1 | 322 |
| `GaloisRepAdic.charpoly_baseChangeAlong` | 8 | 0 | 50 | 9 |
| `GaloisRepAdic.charpoly_eq_of_isEquiv` | 8 | 0 | 6 | 13 |
| `GaloisRepAdic.charpoly_residual` | 8 | 0 | 34 | 7 |
| `GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq` | 9 | 21 | 38 | 199 |
| `ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq` | 8 | 4 | 20 | 104 |

## 7. Consequences

**For the notes.** [base/010](../base/010-finite-fields-frobenius-and-point-counts.md)
answers the E-side question completely and is the right place to read
$`\varphi_q^2 - a_q\varphi_q + q = 0`$. What it does not state — and what a
reader arriving from it will expect — is that the pin's *other* Frobenius
charpoly, the one attached to modular forms, is **not** derived from
`FrobCharEqOnPoints`. It is derived from the char-$`\ell`$ Eichler–Shimura
congruence of [math/011 §5.3](../math/011-tate-module.md). A note on the
modular-form attachment should say so explicitly, and should present the
*relation + determinant* normal form (with the determinant as the cyclotomic
character of [base/007](../base/007-weil-pairing.md)) rather than starting from
the charpoly equality.

**For the port.** Of the family, only two *Galois-side* nodes are ported —
`GaloisRepAdic.charpoly_baseChangeAlong` and `charpoly_eq_of_isEquiv`, both in
`lean/FLTForHuman/GaloisRep/AdicCharpoly.lean`; the `LinearMap.*` nodes are
Mathlib's and are already available. If the E-side or J-side
charpoly production is ported, the shared lemma to add first is the one the pin
lacks: a Mathlib-level
`LinearMap.charpoly_eq_iff_of_finrank_eq_two`-shaped statement taking the
quadratic relation and the determinant directly (the private
`charpoly_eq_of_quadratic_of_det` of §4). That single promotion replaces eight
private copies.

## Method

* Graph readings (depth, closure, citation direction, induced family order) are
  from the pin's docs-site data via `tools/deps/fltdata.py`; the per-node
  dossiers from `tools/deps/explore.py`.
* `S_` line counts are `wc -l` on the pin's `P2M/Sol/S_<stem>.lean`.
* The two-root claim is the induced-subgraph result: over the 34 curated
  family nodes, the E-root has 3 family members above it, the J-root has 8, and
  no node has both cones below it.
* Line-number links are pinned to `aa2d8b3`, as required for `blob/` anchors.
