# Deligne–Serre weight one — port scout and subject plan

**Status (snapshot, 2026-09-30).** Umbrella overview for the weight-one
Deligne–Serre cone, measured against pin `aa2d8b3` with `tools/deps` (the docs-site
graph closure and the `S_`-line metric); the port's mathlib is `v4.34.0`. One
measurement per subject — the tables below are not a history.

* **Frontier** $`F`$ — the union of the checker's `Theorems/Thm_*` sources and the
  declaration names in `lean/FLTForHuman/`: **650 nodes / 268,456 raw `S_` lines**.
* **Forward target** `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen`:
  cone 2,308 nodes, **430 already ported**, **1,867 needed / 901,998 raw `S_` lines**.
* **Landed** — the §3 first batch (weight-one Eisenstein series, relèvement, the
  weight-one $`\to`$ weight-two lifting, the Galois assembly) and the K-route
  residue-theorem / Riemann–Roch block of
  [PORTING-RR](../lean/topics/PORTING-RR.md) (rows 3.3/3.4/3.6/3.7: the Tate
  agreement, trace-completion commutation, K ending and RR assembly).
* **Open in RR** — row 3.5, the perfect-field producer
  `residueTheorem_of_perfectField`; it is off this cone's path, which the
  algebraically-closed K route already serves.
* **Deferred** — the complex-analytic Jacobian / path-integral / Abel–Jacobi block
  (204 nodes / 103,815 lines avoided).

Each subject is getting its own scout as it is attacked; RR is the first
([PORTING-RR](../lean/topics/PORTING-RR.md), options in
[riemann-roch-strategy.md](riemann-roch-strategy.md)), and §6 lists the rest. This
file stays the umbrella measurement and ordering note: §1 fixes the target set, §2
the effort against the frontier, §3 the cheapest mathematics, §4 the finer structure
and port order, §5 the redundancy discipline, §6 the subject scouts, §7 how to
reproduce.

This note is the **living home** for the umbrella measurement and the subject plan.
The measurement paragraph that used to sit in
[flt-non-frey-segments.md](flt-non-frey-segments.md) §3.4 now lives here, because
it changes every time a module lands; §3.4 keeps the landmark description and
points here.

Companions: [../math/019-deligne-serre-weight-one.md](../math/019-deligne-serre-weight-one.md)
(the mathematics — the theorem, its two directions, its place among the modularity
theorems), [flt-non-frey-segments.md](flt-non-frey-segments.md) §3.4 (the segment),
[route-c-prime-scout.md](route-c-prime-scout.md) (the C′ Γ₁-basis, which is in this
cone), [eichler-shimura-scout.md](eichler-shimura-scout.md) (the analytic
Eichler–Shimura package this cone's mod-$`p`$ layer shares),
[../math/020-frobenius-density-and-artin.md](../math/020-frobenius-density-and-artin.md)
(the mathematics of the Galois / Frobenius / Artin cluster),
[riemann-roch-strategy.md](riemann-roch-strategy.md) (the Riemann–Roch foundational
question split out of §4), and [t-side-driver.md](t-side-driver.md) (the $`R = T`$
side that consumes the weight-two output).

## 0. Scope

The port target is the `DeligneSerre.*` weight-one family, in the three shapes FLT
uses it:

* **forward** — a normalized weight-one cuspidal newform $`f`$ of level $`N`$ and
  odd nebentypus $`\varepsilon`$ produces an odd finite-image
  $`\rho_f : G_{\mathbb{Q}} \to \mathrm{GL}_2(\mathbb{C})`$ with
  $`\mathrm{charpoly}(\rho_f(\mathrm{Frob}_p)) = X^2 - a_p X + \varepsilon(p)`$ at
  every good $`p \nmid N`$;
* **lifting** — the reduction of a weight-one mod-$`\ell`$ eigenform is a weight-two
  mod-$`\ell`$ eigenform (multiplication by a weight-one Eisenstein series), which
  is how the weight-one world feeds weight two;
* **converse / conductor** — an odd two-dimensional representation is realized by a
  weight-one form at the correct (Artin-conductor) tame level.

It is on the endgame path: the Frey curve's mod-$`3`$ representation is solvable,
Langlands–Tunnell realizes it by a weight-one form, the lifting moves it to weight
two, and that residual modularity feeds $`R = T`$. The premise chain and the three
faces are in [../math/019-deligne-serre-weight-one.md](../math/019-deligne-serre-weight-one.md)
§5.

Two conventions. The **frontier** $`F`$ is the union of the checker's
`Theorems/Thm_*` sources and the declaration names found in `lean/FLTForHuman/`
(**650 nodes / 268,456 raw `S_` lines**). "New nodes" is `frontier.py`'s
`needed(t) = closure(t) \ F` with a frontier node terminal; "lines" is the sum of
the `S_` files of the needed nodes. The frontier is an upper bound read off the
port's declaration names, so a node counts as landed as soon as the port declares
its statement.

## 1. Target set and internal structure

The public surface is small — 24 declarations in the `DeligneSerre` namespace, plus
the Langlands–Tunnell and `No2BridgeWiring` consumers. Its internal shape is what
matters for ordering.

| internal target | new nodes | `S_` file | status |
|---|---:|---:|---|
| `DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr` | 0 | 676 | landed (`DeligneSerre/Relevement.lean`) |
| `DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen` | 0 | 491 | landed (`DeligneSerre/CoefficientRing.lean`) |
| `DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen` | 0 | 1,242 | landed (`DeligneSerre/Lifting.lean`) |
| `DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd` | 11 | 478 | 11 nodes / 17,470 lines, through the ray-class input |
| `DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le` | 14 | 283 | 14 nodes / 18,942 lines, same shared input |
| `DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual` | 0 | 463 | landed (`DeligneSerre/Assembly.lean`) |
| `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen` | 765 | 271 | **gate 1**: the Rankin-type second-moment bound |
| `DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen` | 766 | 248 | **gate 2**: coefficient-ring finiteness via upper density |
| `DeligneSerre.eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace` | 380 | 709 | local factors and Artin-conductor level (converse side) |
| `DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace` | 413 | 145 | the converse: rep $`\to`$ weight-one form |
| `DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen` | 1,102 | 271 | the workhorse: residual charpolys from a weight-one form |
| `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` | 1,867 | 291 | the forward capstone (characteristic zero, irreducible) |

The dependency shape:

```text
forward:   weight-one eigenform f
           ├─ gate 1  exists_tsum_norm            (Rankin second moment)
           ├─ gate 2  exists_finset_qCoeff_mem    (coefficient ring, upper density)
           └─ exists_subalgebra_qCoeff_mem ─┐
           exists_weightTwo_hecke_eigen_reduction (lifting mod ℓ)
                └→ exists_residual_galoisRep_charpoly
                     └→ exists_galoisRep_complex_trace
                          └→ isIrreducible_…_of_odd
                               └→ exists_galoisRep_of_weightOne
lifting:   exists_weightOne_eisenstein (E₁(1,χ) mod ℓ)
             └→ exists_hecke_eigen_reduction (relèvement)
                  └→ exists_weightTwo_hecke_eigen_reduction
converse:  eulerFactor_eq_and_tameLevel ─→ exists_weightOne_cuspForm_tameConductor
```

The two gates are the only expensive single statements: each is a short `S_` file
(248–271 lines) that nevertheless drags the automorphic block (§4). Everything else
in the forward direction is assembly of cost 5–31. The two unported density lemmas
(`isIrreducible`, `exists_natCard_range_le`) are the only members of the §3 batch
still open; their union is 15 nodes / 19,420 lines, and removing the shared
`M4aTorus.completedRayL_fe` (12,126) leaves 14 nodes / 7,294 (§3.1).

## 2. Effort against the frontier

| target | cone | ported (in cone) | **new nodes / raw `S_` lines** | hops |
|---|---:|---:|---:|---:|
| `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` | 2,308 | 430 | **1,867 / 901,998** | 1 |
| `DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen` | 1,528 | 415 | **1,102 / 531,825** | 1 |
| `DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace` | 439 | 26 | **413 / 194,995** | 1 |
| `FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd` (consumer) | 7,222 | 453 | 6,592 / 4,232,594 | — |
| `LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift` (the mod-3 input) | 6,805 | 432 | 6,362 / 4,125,930 | — |

The forward cone's 430 ported nodes are the §3 first batch, the K-route residue/RR
block, and most of the modular-curve / function-field substrate (`ModularCurve` 151,
`AlgebraicCurve` 141, `ModularForm` 23, `FrobeniusDensity` 18, `CuspForm` 17,
`WLight` 17). Its 1,867 needed nodes compose by subject — this is the single
subject table for the note (namespace-based grouping):

| subject cluster | needed nodes | raw `S_` lines | status | home / scout |
|---|---:|---:|---|---|
| automorphic / adelic $`\mathrm{GL}_2`$ | 533 | 249,591 | not started; the forward gate | `AutomorphicForm/` |
| modular curves / Hecke geometry | 427 | 208,372 | partly ported; finest units §4.1 | `ModularCurve/` |
| function-field / curve layer | 324 | 128,923 | partly ported; RR block landed | `AlgebraicCurve/` ([PORTING-RR](../lean/topics/PORTING-RR.md)) |
| number fields / adelic infrastructure | 164 | 89,780 | not started; shared with Kummer/LT | `NumberTheory/Adelic/` |
| elliptic / Weierstrass / Tate | 128 | 123,724 | partly ported; finest units §4.1 | `WeierstrassCurve/`, `Elliptic/`, `TateCurve/` |
| weight-one forms / Eisenstein | 117 | 48,463 | lifting group landed; Eisenstein partial | `ModularForms/WeightOne/` |
| Langlands–Tunnell (in-cone) | 38 | 17,344 | not started; the mod-3 input | `LanglandsTunnell/` |
| Galois reps / Frobenius / Artin (in-cone) | 8 | 3,791 | subject landed except eight nodes, §4.3 | `GaloisRep/`, `NumberTheory/FrobeniusDensity/` |
| `DeligneSerre` (our own) | 7 | 2,297 | assembly landed; the capstone remains | `DeligneSerre/` |
| everything else | 121 | 29,713 | — | — |
| **total** | **1,867** | **901,998** | | |

The **definition layer** is the other half of the substrate: the cone touches
**281 definition modules**, and the most widely used are
`AlgebraicCurve_DivisorClassGroup` (231 cone theorems), `AlgebraicCurve_IsCurveOver`
(226), `ModularCurve_X0` (162), `AutomorphicForm_ProductionPinsGeneral` (130),
`NumberField_AdelicBox` (127), `AutomorphicForm_FactorizableTestFn` (127),
`ModularCurve_JqCoeff` (119), `AutomorphicForm_WhittakerCoefficient` (105),
`ModularForm_HeckeOperator` (98), `FLTPrelim_Modularity` (77). These are the
candidates for `Defs/` homes: ported once, imported everywhere.

> **Measurement caveat (important).** `frontier.py` counts *theorem-to-theorem*
> citation edges only. A declaration whose proof is self-contained against Mathlib
> and the definition modules shows **cost 1** however large its proof is — e.g.
> `AutomorphicForm.RankinSelberg.*`, `AutomorphicForm.LocalIntertwining.*` and the
> Iwasawa lemmas are all cost 1. Node cost therefore *under-prices* the automorphic
> layer; read the `S_`-line column beside it, and expect the true cost of the
> automorphic subject to be its 250k lines, ported module by module, not a closure
> of 533 nodes. The converse cone has the same property.

## 3. Cheapest mathematics — the §3 batch

These are the cheapest new nodes that are *mathematics*, not adapters: each is a
statement with content, small in both new nodes and `S_` lines, and inside this
cone.

| task | new nodes | `S_` file | status | what it is |
|---|---:|---:|---|---|
| `ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd` | 0 | 703 | landed | the weight-one Eisenstein series $`E_1(1,\chi)`$ for a primitive odd $`\chi`$, with the divisor-sum $`q`$-expansion — the engine of the lifting |
| `DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr` | 0 | 676 | landed | the relèvement: a residual eigenform of any weight is the reduction of a genuine eigenform |
| `DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen` | 0 | 1,242 | landed | weight-one mod $`\ell`$ $`\to`$ weight two — the FLT lifting |
| `ModularForm.exists_rankinCohen_one_qExpansion_eq` | 2 | 301 | open | the first Rankin–Cohen bracket of modular forms |
| `CuspForm.finiteDimensional_Gamma1` | 1 | 16 | open | finite-dimensionality of $`S_k(\Gamma_1(M))`$ |
| `DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range` | 0 | 675 | landed (as `GaloisRep.…`) | a semisimple 2-dimensional representation from two characters |
| `DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen` | 0 | 491 | landed | the finite coefficient ring |
| `DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd` | 11 | 478 | open | irreducibility from the second-moment bound plus oddness |
| `DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le` | 14 | 283 | open | image-order bound from a Frobenius-charpoly density condition |
| `DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual` | 0 | 463 | landed | promote a compatible residual family to a complex representation |
| `CuspForm.HasNebentypus.diamondLinOne_apply_eq_smul` | 0 | 29 | landed | diamond operators act by $`\varepsilon(d)`$ on forms with nebentypus |
| `ModularForm.exists_gamma0_qExpansion_eq_of_levelOne` | 1 | 36 | open | a level-one form is a form for $`\Gamma_0(N)`$ |
| `FrobeniusDensity.ncard_conj_gen_ne_zero_iff` | 0 | 17 | landed | the Chebotarev-style conjugating-count criterion |
| `NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` | 1 | 32 | open | compactness of the adele class group $`\mathbb{A}_F/F`$ |
| `LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers` | 1 | 45 | open | the standard local additive character is trivial on $`\mathcal{O}`$ |

**The recommended first batch is landed.** The lifting group
(`exists_weightOne_eisenstein`, `exists_hecke_eigen_reduction`,
`exists_weightTwo_hecke_eigen_reduction`) and the Galois-assembly group
(`exists_isSemisimpleRepresentation`, `exists_subalgebra_qCoeff_mem`,
`isIrreducible_…_of_odd`, `exists_natCard_range_le`,
`exists_galoisRep_complex_trace`) were a union of 70 new nodes; six of the eight
targets are landed, leaving the two density lemmas (union 15 nodes / 19,420 lines)
plus the five small open tasks above. Landing the two density lemmas gives the whole
DS statement skeleton with the two gates as explicit hypotheses, so the expensive
automorphic work can then be attacked against a fixed interface.

**Do not mistake the gates for small tasks.** `exists_tsum_norm` and
`exists_finset_qCoeff_mem` are single short statements (271 and 248 lines) but each
drags ~765 nodes of the automorphic block; they are the subject of §4, not of this
list.

### 3.1 The shared ray-class input

The open density lemmas split at `M4aTorus.completedRayL_fe`, the 12,126-line proof
of the analytic continuation and functional equation of the completed
narrow-ray-class $`L`$-function.

| piece | nodes | raw `S_` lines | depends on `completedRayL_fe`? |
|---|---:|---:|---|
| lifting group + `exists_isSemisimpleRepresentation` + `exists_subalgebra_qCoeff_mem` + `exists_galoisRep_complex_trace` | 54 | 13,226 | no — landed |
| `isIrreducible_…_of_odd` + `exists_natCard_range_le` | 15 | 19,420 | yes |
| the same two, with `completedRayL_fe` deferred | 14 | 7,294 | one interface |

So the remaining batch is 15 nodes / 19,420 lines, and deferring the one statement
takes it to 14 / 7,294: 12,126 lines (62%) removed for one interface.

The interface is narrower than the file. `completedRayL_fe` is a single theorem
(the 12,126-line file is its proof, 595 helper lemmas), and the batch reaches it by
exactly one route, `NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one`
(102 lines), whose proof destructures it as

```text
obtain ⟨F, G, -, -, hFeq, -, -, hent⟩ := M4aTorus.completedRayL_fe K 𝔣 χ S hpar
```

keeping only the agreement on $`\mathrm{Re}\,s \gt 1`$ (`hFeq`) and the
$`\chi \ne 1 \Rightarrow`$ differentiability conjunct (`hent`), and **discarding the
functional equation** (the `-` slots). The functional-equation extraction
`NumberField.exists_completedRayL_functionalEquation_of_primitive` (1,055 lines) is
not in the forward batch cone at all; it is consumed by
`ArtinL.Abelian.exists_completedLSeries_functionalEquation_u0` and appears only in
the **converse** cone. So the batch needs only

> for a nontrivial narrow ray-class character $`\chi`$, the completed ray-class
> $`L`$-function has an entire continuation agreeing with its Dirichlet series on
> $`\mathrm{Re}\,s \gt 1`$,

the classical Hecke analytic continuation of the ray-class $`L`$-function, without
the functional equation or root number — strictly weaker than `completedRayL_fe`,
and the natural seam. The residual 7,294 lines are themselves mostly a
Chebotarev/density block (`NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt`,
`GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective`, the
`FrobeniusDensity.*` lemmas; 2,669 lines); treating that block as a second interface
leaves **11 nodes / 4,625 lines**.

## 4. Finer structure and port order

Every count in this section is of **FLT pin nodes**; the *ported* columns are the
current frontier. The target set is the forward cone of
`DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` in the pin's citation
graph, and the units inside it are selected from each node's namespace and
identifier tokens by the §7 script.

### 4.1 The two large substrate clusters

**Elliptic / Weierstrass / Tate.** 129 pin nodes / 125,059 `S_` lines
(`WeierstrassCurve.*` 106, `TateCurve.*` 23); 1 ported.

| unit | nodes | `S_` lines | ported |
|---|---:|---:|---:|
| Vélu isogeny / cyclic quotient / modular polynomial | 50 | 91,966 | 0 |
| Weierstrass function field / coordinate ring / places | 19 | 15,027 | 0 |
| models, group law, variable change, $`j`$ | 18 | 4,946 | 0 |
| torsion / division polynomials / Drinfeld | 11 | 4,585 | 1 |
| other (genus-one/closure) | 4 | 4,215 | 0 |
| Tate curve: analytic parametrization | 23 | 2,749 | 0 |
| reduction / semistability / modularity data | 3 | 1,356 | 0 |
| formal group / EDS / special invariants | 1 | 215 | 0 |
| **total** | **129** | **125,059** | **1** |

The actionable fact is the concentration inside the 50-node Vélu block: its 24
cyclic-kernel/place-classification nodes (83,224 lines) are 67% of the row's lines
in 19% of its nodes (six 4,000–12,000-line statements), and they are Mazur-type
cyclic-isogeny classification through the `Affine.FunctionField`/place gate and the
`IsogenyEndDatum`/`IsogenyHomDatum` endomorphism data, not "elliptic curves". The
rest of the block is the explicit Vélu formulas, the modular polynomial /
`cyclicQuotientJ` bijection, and the odd-order summing-set special cases (char 2 and
3). Several of the biggest statements occur in near-duplicate pin file variants
(`velu_map_equation_of_oddOrderSummingSet` and `…_of_isAlgClosed`;
`exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq` and `…_of_isAlgClosed`),
so the raw line total overstates the block too; the pooled `port_advise` method of
§7 is how to quantify that. Port order: models/group law → function field and places
(which need `AlgebraicCurve` places) → explicit Vélu → the classification block. The
Tate curve depends on `AlgebraicCurve`'s annulus and residue material, not on the
Weierstrass classification.

**Function-field / curve layer.** The `AlgebraicCurve.*` cone is 465 pin nodes /
219,684 lines; 141 ported. Split by the §7 predicates:

| unit | nodes | `S_` lines | ported |
|---|---:|---:|---:|
| complex-analytic Jacobian / path integrals / Tate trace | 67 | 84,610 | 9 |
| places / valuations / local fields / completions | 161 | 35,677 | 72 |
| divisors / class group / $`\mathrm{Pic}^0`$ / Jacobian | 69 | 22,494 | 19 |
| Riemann–Roch / repartitions / genus / index | 41 | 25,650 | 20 |
| differentials / residues / Serre duality | 46 | 18,190 | 3 |
| curves, models, correspondences, function fields | 52 | 16,681 | 11 |
| other (genericity/closure) | 29 | 16,382 | 7 |
| **total** | **465** | **219,684** | **141** |

The three subjects that the sharing shows to be one dependency mass — places (161)
+ divisors (69) + Riemann–Roch (41) = **271 pin nodes / 83,821 lines** (111 ported,
**160 needed**), the residual pool for the curve layer. Their finer sub-units:

| places sub-unit | nodes | `S_` lines | ported |
|---|---:|---:|---:|
| A. rational function field / $`\mathbb{P}^1`$ places | 21 | 8,816 | 18 |
| B. ord / valuation ring / local residue | 76 | 14,692 | 26 |
| C. place extension / ramification calculus | 19 | 2,140 | 8 |
| D. local expansion / completion / evaluation | 10 | 2,202 | 6 |
| E. place existence / basic vocabulary | 29 | 7,678 | 12 |
| Z. `SemilinearAut` action on places | 6 | 149 | 2 |
| **places total** | **161** | **35,677** | **72** |

| divisors sub-unit | nodes | `S_` lines | ported |
|---|---:|---:|---:|
| A. class group / degree / principal | 30 | 10,924 | 7 |
| C. pushforward / pullback / norm formula | 11 | 3,437 | 4 |
| D. $`\mathrm{Pic}^0`$ / Jacobian | 22 | 3,347 | 6 |
| E. pole / universal divisor | 6 | 4,786 | 2 |
| **divisors total** | **69** | **22,494** | **19** |

(Canonical divisor is not in this table: the predicate sends `canonicalDivisor` to
the differentials unit. Its 5 nodes / 3,254 lines belong with divisors A.)

Running `port_advise` on the 160 needed nodes of the pool (raw 41,281 lines) reads
320 `S_`+`Thm_` files / 2,049 declarations, with **218 substitutions** (115 unique
names, 4,334 lines already in the port), **221 names proved in two or more target
files** (5,616 removable lines; 3,470 excluding the substituted names), a
**3,135-line unique shared prelude**, and **≈33,500 projected new lines**. The
remaining pool is now much less dedup-able per raw line than the Riemann–Roch/adelic
engine the port already absorbed.

The boundaries of this layer are **layers, not subjects**: one shared
Riemann–Roch / adelic prelude (`ell`, `lSpace`, `poleDivisor`, `indexOfSpecialty`,
`RiemannGenusReachedAt`, `TranscendenceTower`, `stichtenothGenusExists`, `adeleBddQuot*`,
`residuePairing`, `reciprocity_linear`, under `finrank_quotient_chain*`,
`nestedComapMapMkQEquiv`, `doubleResiduePairing_injective`,
`linearIndependent_pow_of_transcendental`) is one module; the already-ported
place/valuation vocabulary is an **import boundary**, not work. The port's
`AlgebraicCurve/` tree is now **73 files / 2,124 declarations / 37,023 lines** and
holds **141** of the cone's pin nodes (first measurement: 17 files / 372 declarations
/ 77 nodes), across `Defs/*`, `PrincipalDivisors/*`, `Genus/*`, `RiemannRoch/*`,
`Canonical/*`, the `P1/` residue core, the `Tate/` agreement and commutation, and the
`ResidueTheorem/` K family and RR assembly. Two blocks are deliberately deferred:
`Defs/Divisor.lean` excludes the `Pic`/torsion/`AbelJacobiCard` block ("API for the
modular Hecke/Galois-representation layer, not for the exchange cone"), and
`Defs/SemilinearAut.lean` excludes the `Divisor`/`Pic0` action-and-torsion section of
`BaseChangeGalois`.

### 4.2 The Riemann–Roch subject

RR now has its own scout: [PORTING-RR](../lean/topics/PORTING-RR.md) carries the
work order and [riemann-roch-strategy.md](riemann-roch-strategy.md) the options. In
this cone, the RR family is 72 pin nodes / 62,710 lines, **30 ported / 42 needed**;
the full-RR *statements* are only 4 nodes / 210 lines and almost every other node
cites nothing within the family, so the shared prelude needs one home.

What is in the port: the phase-1 genus / index engine and the phase-2 canonical
divisor; the K-route residue block (Tate agreement, trace-completion commutation, K
ending) and the RR assembly, giving `FunctionFieldRiemannRoch` / `WeilDualityAdelic`
/ `genus_eq_genusFF`; and `residueTheorem_of_isAlgClosed`, the general
$`ResidueTheorem`$ over algebraically closed fields. The cone's unported
`residueTheorem|tateAgreement|residueTrace` nodes are **0**, and its only remaining
RR gap is the pin's three thin wrappers `functionFieldRiemannRoch_of_isAlgClosed`,
`…_of_isCurveOver` and `…_of_transcendental` — 3 nodes / 155 lines.

What is deferred is **not RR**: the complex-analytic Jacobian / path-integral /
Abel–Jacobi / `CellDissection` subject. Avoiding its needed nodes is prunable = 205
nodes / 107,257 lines, taking the forward target to 1,666 / 798,338 — a saving of
201 nodes / 103,660 lines; with the two differential-residue applications and the
three RR wrappers deferred too, prunable = 209 / 113,669 and the target is
1,663 / 798,183 (204 nodes / 103,815 lines saved), at a 13-node rewiring frontier.
The cone consumes RR through the differentials ↔ cusp-forms transport
`ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm`
(6 cone dependents) and the chain below it; that transport is the bottleneck, not RR
itself. The **arithmetic** dimension route is independent:
`CuspForm.finiteDimensional_Gamma1`, the $`\Gamma_1`$-integral basis and the
coefficient-ring gate have zero RR ancestors.

### 4.3 The Galois / Frobenius / Artin cluster

The forward cone's 23 strict nodes of this subject — `FrobeniusDensity.*` (18 nodes,
2,505 `S_` lines), `GaloisRep.*` (3 nodes: `exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel`
171, `exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range`
495, `sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective` 945) and the two
bridges `NumberField.exists_isFrobenius_lift_arithFrobAt` (240) and
`Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen` (28) — total 23 nodes /
4,384 raw `S_` lines. **21 of the 23 are landed**; the 2 still needed are the
density-lemma helpers `sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective`
(945) and `exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range`
(495), which the §3.1 interfaces remove from the batch.

Counting in the generic `Representation.*` conjugacy/lifting group the cluster also
reaches, the subject's in-cone total is 29 nodes / 7,332 lines, 21 ported and **8
needed**: the six `Representation.*`
(`exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top`
1,692, `exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue` 291,
`span_range_eq_top_of_isIrreducible` 151,
`exists_isCompl_forall_mem_of_compactSpace_of_continuous` 112,
`exists_extend_forall_apply_mul_of_injective` 69,
`pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero` 36) plus the two
`GaloisRep.*` above. Two nodes are one algebraic subject:
`GaloisRep.exists_isSemisimpleRepresentation_…` is a 495-line `S_` file delegating to
the private `DSRt.main`, whose true content is the two-character descent the
`DeligneSerre.*` sibling (`add_mem_range`/`mul_mem_range`, 675 lines) states; port
them as one `GaloisRep/` subject. The mathematics of the cluster is
[../math/020-frobenius-density-and-artin.md](../math/020-frobenius-density-and-artin.md).

The cluster's new definition modules are the D layer:
`Def_TaylorWiles_Primes`, `Def_FrobeniusDensity_{DegOneAsymptotic,PrimeSums,BadPrimes}`
and `Def_GaloisRep_FrobeniusPowerDense`; `GaloisFactorsThroughFiniteLevel`
(`Def_GaloisRep_Residual`) and the place vocabulary of `Def_FLTPrelim_Ramification` /
`Def_EllipticCurve_FrobeniusTrace` are already ported.

**The analytic block is the un-priced risk.** `primeSum_toReal_add_log_isBigO` (474),
`degOneSum_add_log_isBigO` (292) and `tailSum_le` (158) are `tsum`/`IsBigO` analysis
of the ideal sum. They are self-contained against Mathlib and therefore each show
cost 1 in `frontier.py` — the §2 measurement caveat in its purest form. Dedup is
concrete: the Möbius/fixed-coset prelude (`mem_zpowers_pow_div_iff`,
`sum_moebius_mem_zpowers`, `exists_pow_coprime_eq_of_orderOf_eq`,
`orderOf_pow_orderOf_div`, `ncard_conj_mem_eq_card_mul_ncard`, `ncard_eq_sum_indicator`)
and `card_le_of_forall_pow_eq` are repeated; one
`NumberTheory/FrobeniusDensity/Basic.lean` covers them.

### 4.4 Port order

The subjects are coherent theories, ported one at a time: **number fields / adelic
infrastructure** before the **automorphic gate** (the gates are one subject, not two
— both cones are `AutomorphicForm` 473, `NumberField` 123, `LanglandsTunnell` 38);
**Langlands–Tunnell / octahedral / Artin** is independent of the automorphic gate for
the converse but shares the number-field layer and the Kummer files' Artin
$`L`$-function vocabulary; **modular curves** and **elliptic / Weierstrass / Tate**
interleave at any point and are the best coverage per node, subject to §4.1 (the
`AlgebraicCurve` places/divisor vocabulary is a prerequisite of the curve layer, and
the Vélu cyclic-kernel classification is a separate, concentrated effort). The
converse cone is different: 413 needed, resting on `NumberField` 82, `ArtinL` 36,
`M4aHerbrand` 34, `groupCohomology` 30, `IsDiscreteValuationRing` 31.

## 5. Redundancy discipline

The port's cautionary tale is the **WeightOne rectification**
([../lean/topics/hecke/TOPIC-weightone-rectify.md](../lean/topics/hecke/TOPIC-weightone-rectify.md)):
transcribing FLT package-by-package re-proved every private prelude per consumer,
7,242 removable lines in 12 modules. This cone overlaps that material
(`CuspForm`, `ModularForm`, `EisensteinSeries`, `PeriodPair`), so the same failure
mode is available. The rules for this port:

* **Run `port_advise.py` before transcribing any slice.** On the 18-file
  `S_WLight_*` slice its first reading was 931 declarations with a byte-identical
  statement already in the port (≈13,467 lines) and 180 names proved in ≥2 target
  files (≈4,369 target-removable lines). A slice of this cone should get the same
  treatment first: `python3 port_advise.py --target 'P2M/Sol/S_DeligneSerre_*'`.
* **One home per subject.** Shared real mathematics (weight-one Eisenstein series,
  q-expansion uniqueness, the adelic vocabulary, the modular-curve polynomial
  package) goes in `Defs/`/`Basic`, never `private` in each consumer; adapters stay
  `private` in the consumer.
* **Check the definition layer first.** The 281 definition modules of §2 are the
  most likely place where two subjects would otherwise duplicate a definition; port
  the shared `Def_*` module once.
* **Keep the interfaces stable.** Land the §3 batch with the gates as hypotheses, so
  the automorphic subject can be ported behind a fixed interface without reworking
  the DS lemmas.

## 6. Subject scouts

This file is the umbrella; the detailed measurement for a subject moves to its own
scout when that subject is attacked.

| subject | scout / home |
|---|---|
| Riemann–Roch / curve layer | [PORTING-RR](../lean/topics/PORTING-RR.md) + [riemann-roch-strategy.md](riemann-roch-strategy.md); code in `AlgebraicCurve/` |
| modular curves / Hecke geometry | to be written; code in `ModularCurve/` |
| automorphic / adelic $`\mathrm{GL}_2`$ | to be written; code in `AutomorphicForm/` |
| number fields / adelic infrastructure | to be written; code in `NumberTheory/Adelic/` |
| elliptic / Weierstrass / Tate | to be written; code in `WeierstrassCurve/`, `Elliptic/`, `TateCurve/` |
| Langlands–Tunnell / octahedral / Artin | to be written; code in `LanglandsTunnell/` |
| weight-one forms / lifting | this note (§3) + `ModularForms/WeightOne/` |
| Galois reps / Frobenius / Artin | this note (§4.3) + `GaloisRep/`, `NumberTheory/FrobeniusDensity/` |

Update §2 and §4.1 in this file when a subject lands; the per-subject scout carries
the finer record.

## 7. Reproduce

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --top 40
python3 frontier.py --selfcheck
python3 port_advise.py --target 'P2M/Sol/S_DeligneSerre_*'

# --- §4.1 target-node finder --------------------------------------------------
# The target sets are pin-only: the forward cone of the Deligne-Serre target in
# the pin's citation graph.  The frontier `front` is consulted only to fill the
# ported/needed columns; the file written for port_advise is the needed subset.
python3 - <<'PY'
import frontier, re
from collections import defaultdict
fr = frontier.Frontier()
root = fr.pay.pid('DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen')
cone = fr.closure(root)                 # pin-only, frontier-independent
front = fr.frontier('union')            # the port's current frontier
def ac_bucket(q):                       # AlgebraicCurve.* predicates of §4.1
    s = q[len('AlgebraicCurve.'):]
    if 'functionFieldRiemannRoch' in s: return 'Riemann-Roch'   # the RR theorem, even when proved from the residue theorem
    if re.search(r'abelJacobi|pathIntegral|pathPeriodLattice|CellDissection|cell|Cell|RadialRegion|grid|residueTheorem|residueTheoremK|Tate|tate|residueTrace|residue_norm|complex|Complex|chartedSpace|isCoveringMapOn|Analytic|analytic|period|Period|Chordal|ComplexLineIntegral|StandardAnnulus|ResidueDiscs|eventually_abel', s): return 'complex-analytic'
    if re.search(r'[Dd]ifferential|Diffs|diffs|dCoord|omegaSpace|Serre|WeilDatum|weil|Kaehler|canonicalDivisor|CanonicalDivisor|ordDiff|localUnitDerivative', s): return 'differentials/duality'
    if re.search(r'[Dd]ivisor|Pic0|pic0|Jacobian|classGroup|ClassGroup|Cartier|UniversalDivisor|GluedPic0|NodalPic0|divisorClass|abel|hasPrincipalDivisors|degree_eq|degree_canonical', s): return 'divisors/Pic0'
    if re.search(r'[Rr]iemannRoch|repartition|Repartition|indexOfSpecialty|genus|Genus|ell_|ell\b|lSpace|two_mul_genus|RiemannGenus|omegaSpace|stichtenoth', s): return 'Riemann-Roch'
    if re.search(r'[Pp]lace|ord_|ord\b|valuation|Valuation|completion|Completion|[Ll]ocalResidue|TaylorCoeff|depth|Depth|PlaceEvaluation|normFormulaAlong|relNorm|semilinear|SemilinearAut', s): return 'places/local'
    if re.search(r'[Cc]urve|Curve|functionField|FunctionField|ratFunc|RatFunc|[Cc]orrespondence|correspondence|constantField|ConstantField|Semistable|semistable|model|Model|[Cc]overing|covering|TranscendenceTower|transcendental|Transcendental|finiteDimensional|isAlgClosed|adjoin|KummerCover|FibreResidue|baseChange|BaseChange|traceAlong|pullbackAlong', s): return 'curves/models'
    return 'other'
def wt_bucket(q):                       # WeierstrassCurve.* / TateCurve.* predicates of §4.1
    if q.startswith('TateCurve.'): return 'Tate curve: analytic parametrization'
    s = q.split('.', 1)[1]
    if re.search(r'[Vv]elu|cyclicQuotient|cyclicKernels|isAddCyclic|IsogenyEnd|IsogenyHom|pointMapOfPushforward|pointHom|dualEndData|stepCurve|OddOrderSummingSet|isOddVeluSet|ker_pointMap|veluFunctionFieldHom|veluPointHom|veluQuotient|velu_map_equation|veluGx|velu2|zmultiples_eq_of_veluQuotient|Delta_eq_veluGx', s): return 'Vélu isogeny / cyclic quotient / modular polynomial'
    if re.search(r'torsion|Torsion|DivPoly|divPoly|evalEval_psi|KernelPolynomial|KernelIdeal|FullKernel|Drinfeld', s): return 'torsion / division polynomials / Drinfeld'
    if re.search(r'ProjModel|AddFormula|Third|PointChart|SectionAtOrigin|MapPoint|PointAddEquiv|VariableChange|variableChange|Legendre|Deuring|j_eq|j_perturb|jInvariant|vcInvFun|zsmul_some|smul_some|some_add|some_zero|Point\.|exists_addMonoidHom_i_tau|exists_addMonoidHom_vcInvFun', s): return 'models / group law / variable change / j'
    if re.search(r'FunctionField|functionField|placeOfPoint|PlaceGate|hasPrincipalDivisors|valuationSubring|CoordinateRing|XYIdeal|adjoin_yCoord|finiteDimensional_ratFunc|isDedekindDomain|GenusOnePlace', s): return 'Weierstrass function field / coordinate ring / places'
    if re.search(r'reduceHom|ReduceHom|[Rr]eduction|goodModel|inertia|Semistab|semistab|Conductor|PeuRamifiee|Modularity|ThreeFive|Mlc1|FrobeniusCard|isGalois', s): return 'reduction / semistability / modularity data'
    if re.search(r'FormalGroup|EDSEngine|Hasse|RatPoint|RationalEnd|delta|Delta|exists_isUnit_mul_pow_eight|exists_valuationSubring_with_transcendental', s): return 'formal group / EDS / special invariants'
    return 'other / genus-one closure'
def report(qs, bucket, label):
    g = defaultdict(lambda: [0, 0, 0, 0])
    for i in qs:
        b = bucket(fr.pay.qual(i)); g[b][0] += 1; g[b][1] += fr.lines(i)
        g[b][2 if i in front else 3] += 1
    print(label, f'({sum(v[0] for v in g.values())} nodes /'
                 f' {sum(v[1] for v in g.values())} lines)')
    for b, (n, L, p, nd) in sorted(g.items(), key=lambda kv: -kv[1][1]):
        print(f'  {b:52} total={n:4} lines={L:7} ported={p:3} needed={nd:3}')
report([i for i in cone if fr.pay.qual(i).startswith('AlgebraicCurve.')], ac_bucket, 'AlgebraicCurve cone')
report([i for i in cone if fr.pay.qual(i).startswith(('WeierstrassCurve.', 'TateCurve.'))], wt_bucket, 'Weierstrass+Tate cone')

def plc_theme(q):
    s = q[len('AlgebraicCurve.'):]
    if re.search(r'RationalFunctionField|placeInfty|ratFunc|constantsAreBase|isRational', s): return 'A RatFunc/P1'
    if re.search(r'PlaceEvaluation|PlaceTaylorCoeff|PlaceDepth|PlaceCompletion|PlaceDictionary|evalAt|localParam|analyticOrderAt|TaylorCoeff', s): return 'D local expansion'
    if re.search(r'restrictAlong|inertiaDegAlong|ramificationIndexAlong|finrankAlong|separableAlong|finiteAlong|normFormulaAlong|relNorm|Restrict|restrict_eq|restrict_ofAlgAut|Along', s): return 'C extension/ramification'
    if re.search(r'(?<![A-Za-z])ord(?![A-Za-z])|adicValuation|[Vv]aluationSubring|toValuation|maximalIdeal|LocalResidue|residue_norm', s): return 'B ord/valuation'
    if re.search(r'(?<![A-Za-z])[Pp]lace', s): return 'E place basic'
    return 'Z other places'
def div_theme(q):
    s = q[len('AlgebraicCurve.'):]
    if re.search(r'Pic0|pic0|Jacobian|jacobian', s): return 'D Pic0/Jacobian'
    if re.search(r'PushPull|pushforward|pullback|pushForward|pushforwardAlong|pullbackAlong|normFormula', s): return 'C push/pull/norm'
    if re.search(r'UniversalDivisor|PoleDivisor|poleDivisor', s): return 'E pole/universal'
    if re.search(r'ClassGroup|classGroup|divisorClass|hasPrincipalDivisors|principal|degree|support|Divisor|divisor', s): return 'A class group/degree'
    return 'Z other'
def report_fine(unit, theme, label):
    g = defaultdict(lambda: [0, 0, 0, 0])
    for i in cone:
        q = fr.pay.qual(i)
        if not q.startswith('AlgebraicCurve.') or ac_bucket(q) != unit: continue
        b = theme(q); g[b][0] += 1; g[b][1] += fr.lines(i)
        g[b][2 if i in front else 3] += 1
    print(label, f'({sum(v[0] for v in g.values())} nodes /'
                 f' {sum(v[1] for v in g.values())} lines)')
    for b, (n, L, p, nd) in sorted(g.items()):
        print(f'  {b:34} total={n:4} lines={L:6} ported={p:3} needed={nd:3}')
report_fine('places/local', plc_theme, 'places sub-units of §4.1')
report_fine('divisors/Pic0', div_theme, 'divisors sub-units of §4.1')
pool = [fr.pay.qual(i) for i in cone
        if i not in front and fr.pay.qual(i).startswith('AlgebraicCurve.')
        and ac_bucket(fr.pay.qual(i)) in ('places/local', 'divisors/Pic0', 'Riemann-Roch')]
open('build/pool_pdr_nodes.txt', 'w').write(','.join(pool))
print('pool for port_advise (needed places+divisors+RR):', len(pool), 'nodes')
PY
python3 port_advise.py --nodes "$(cat build/pool_pdr_nodes.txt)" --json build/pool_pdr_advise.json
python3 build/pa_summary.py build/pool_pdr_advise.json \
  "$(python3 -c "import frontier;fr=frontier.Frontier();print(sum(fr.lines(fr.pay.pid(q)) for q in open('build/pool_pdr_nodes.txt').read().split(',')))")"
```

The §2 target counts are `frontier.py` reads of the named targets against the live
frontier; the §2 subject table and the §4.1 units are the §7 classifier with the
namespace map of the note as the grouping. The §4.2 payout is `prune.py`'s
reachability together with `frontier.py`'s `needed` avoiding $`R`$ (the residue/Tate
set is fully ported in-cone, so the measurement that moves is the complex-analytic
block):

```bash
cd tools/deps
python3 - <<'PY'
import re, frontier
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
root = pay.pid('DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen')
cone = fr.closure(root)
def has(*pats):
    return {i for i in cone if any(re.search(p, pay.qual(i)) for p in pats)}
base = frontier.needed(pay.cites, root, ported=front)
COMPLEX = has(r'CellDissection', r'pathIntegral', r'abelJacobi',
              r'pathPeriodLattice', r'Pic0\..*complex') - front
DIFFRES = has(r'exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero',
              r'sum_fibre_evalAt_eq_zero_of_smul_D_mem_regularDifferentials') - front
WRAPPERS = has(r'functionFieldRiemannRoch_of_isAlgClosed') - front
for label, R in [('complex-only', COMPLEX),
                 ('complex + diff-residue apps + RR wrappers', COMPLEX | DIFFRES | WRAPPERS)]:
    keep = frontier.needed(pay.cites, root, ported=front, avoided=R, cutters=None)
    print(label, 'R', len(R), pay.total_lines(R),
          'prunable', len(pay.prunable(root, R)), pay.total_lines(pay.prunable(root, R)),
          'needed after', len(keep), pay.total_lines(keep),
          'saving', len(base) - len(keep), pay.total_lines(base) - pay.total_lines(keep))
PY
```

The same $`R`$ on `FLT.fermatLastTheorem` reproduces
[riemann-roch-strategy.md](riemann-roch-strategy.md) §5.1 (27 / 64,873; prunable
35 / 95,884; rewiring frontier 14).
