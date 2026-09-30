# Deligne–Serre weight one — port scout and subject plan

**Status: SCOPED, port not started (2026-09-29).** A living port scout for the
weight-one Deligne–Serre cone. §1 fixes the target set and its internal structure,
§2 is the effort against the current frontier, §3 the minimum-effort
mathematically significant tasks, §4 the foundational modules and their clusters,
§5 the redundancy discipline, §6 the living subject map, §7 how to reproduce.
Everything is measured against the pin `aa2d8b3` with `tools/deps` (docs-site graph
closure and the `S_`-line metric); the port's mathlib is `v4.34.0`.

This note is the **living home** for the effort measurement and the subject plan.
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
(the mathematics of the §6.1 Galois / Frobenius / Artin cluster), and
[t-side-driver.md](t-side-driver.md) (the $`R = T`$ side that consumes the
weight-two output).

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

Two conventions matter for the numbers below. The **frontier** $`F`$ is the union
of the checker's `Theorems/Thm_*` sources and the declaration names found in
`lean/FLTForHuman/` (492 nodes / 120,774 raw `S_` lines as of this measurement).
"New nodes" is `frontier.py`'s `needed(t) = closure(t) \ F` with a frontier node
terminal; "lines" is the sum of the `S_` files of the needed nodes.

## 1. Target set and internal structure

The public surface is small — 24 declarations in the `DeligneSerre` namespace, plus
the Langlands–Tunnell and `No2BridgeWiring` consumers. Its internal shape is what
matters for ordering.

| internal target | new nodes | `S_` lines | role |
|---|---:|---:|---|
| `DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr` | 5 | 676 | the *relèvement*: a residual eigenform is the reduction of a genuine eigenform |
| `DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen` | 13 | 491 | coefficient-ring finiteness ($`58/71`$ of its cone already ported) |
| `DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen` | 17 | 1,242 | weight-one mod $`\ell`$ $`\to`$ weight two |
| `DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd` | 18 | 478 | irreducibility from the second-moment bound + oddness |
| `DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le` | 21 | 283 | bound on the order of the Frobenius image |
| `DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual` | 31 | 463 | assemble the complex representation from residual characteristic polynomials |
| `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen` | 775 | 271 | **gate 1**: the Rankin-type second-moment bound |
| `DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen` | 783 | 248 | **gate 2**: coefficient-ring finiteness via upper density |
| `DeligneSerre.eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace` | 386 (cone) | 709 | local factors and Artin-conductor level (converse side) |
| `DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace` | 439 (cone) | 145 | the converse: rep $`\to`$ weight-one form |
| `DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen` | 1,210 | 271 | the workhorse: residual charpolys from a weight-one form |
| `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` | 1,988 | 291 | the forward capstone (characteristic zero, irreducible) |

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
(248–271 lines) that nevertheless drags the automorphic block (§2). Everything else
in the forward direction is assembly of cost 5–31.

## 2. Effort against the current frontier

| target | cone | already in the port (in cone) | **new nodes / raw `S_` lines** | hops |
|---|---:|---:|---:|---:|
| `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` | 2,308 | 309 | **1,988 / 995,359** | 2 |
| `DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen` | 1,528 | 307 | **1,210 / 622,105** | 3 |
| `DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace` | 439 | 18 | **421 / 196,678** | 2 |
| `FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd` (consumer) | 7,222 | 331 | 6,713 / 4,325,955 | — |
| `LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift` (the mod-3 input) | 6,805 | 311 | 6,483 / 4,219,291 | — |

The port already owns about 309 of the forward cone's nodes, and they are almost
all on the modular-curve/function-field side (`ModularCurve` 151, `AlgebraicCurve`
77, `ModularForm` 21, `WLight` 17, `CuspForm` 10). The rest is unported.

**Composition of the forward cone's 1,988 needed nodes**, by the natural subjects of
§4 — the table also gives each subject's average and maximum coverage over the pin's
49 landmark cones, the "judged by all projects" measure of §4:

| subject cluster | needed nodes | raw `S_` lines | avg landmark share | max |
|---|---:|---:|---:|---:|
| automorphic / adelic $`\mathrm{GL}_2`$ | 534 | 242,409 | 10.7 | 22 |
| modular curves / Hecke geometry | 443 | 219,577 | 15.9 | 22 |
| function-field / curve layer | 425 | 217,578 | 21.2 | 24 |
| weight-one forms / Eisenstein | 134 | 52,352 | 12.4 | 22 |
| number fields / adelic infrastructure | 133 | 69,962 | 11.2 | 20 |
| elliptic / Weierstrass / Tate | 129 | 123,876 | 21.4 | 31 |
| Langlands–Tunnell (in-cone part) | 38 | 17,344 | 9.3 | 12 |
| Galois reps / Frobenius / Artin (in-cone part) | 23 | 4,620 | 17.5 | 20 |
| `DeligneSerre` (our own) | 13 | 5,988 | 9.2 | 11 |
| everything else | 116 | 41,653 | — | — |
| **total** | **1,988** | **995,359** | | |

The two gates have almost the same cone — `AutomorphicForm` 473 nodes,
`NumberField` 123, `LanglandsTunnell` 38 — so they are one
subject, not two: the analytic automorphic layer. The converse is a *different*
421-node cone, resting on `NumberField` 81, `ArtinL` 36, `M4aHerbrand` 34,
`groupCohomology` 30, `IsDiscreteValuationRing` 31.

> **Measurement caveat (important).** `frontier.py` counts *theorem-to-theorem*
> citation edges only. A declaration whose proof is self-contained against Mathlib
> and the definition modules shows **cost 1** however large its proof is — e.g.
> `AutomorphicForm.RankinSelberg.*`, `AutomorphicForm.LocalIntertwining.*` and the
> Iwasawa lemmas are all cost 1. Node cost therefore *under-prices* the automorphic
> layer; read the `S_`-line column beside it, and expect the true cost of the
> automorphic subject to be its 242k lines, ported module by module, not a closure
> of 534 nodes. The converse cone has the same property.

## 3. Scout Q1 — minimum-effort tasks with mathematical content

These are the cheapest new nodes that are *mathematics*, not adapters: each is a
statement with content, small in both new nodes and `S_` lines, and inside this
cone. Costs are from the forward target.

| task | new nodes | `S_` lines | what it is |
|---|---:|---:|---|
| `ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd` | 5 | 703 | the weight-one Eisenstein series $`E_1(1,\chi)`$ for a primitive odd $`\chi`$, with the divisor-sum $`q`$-expansion — the engine of the lifting |
| `DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr` | 5 | 676 | the relèvement: a residual eigenform of any weight is the reduction of a genuine eigenform |
| `DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen` | 17 | 1,242 | weight-one mod $`\ell`$ $`\to`$ weight two — the FLT lifting |
| `ModularForm.exists_rankinCohen_one_qExpansion_eq` | 2 | 301 | the first Rankin–Cohen bracket of modular forms |
| `CuspForm.finiteDimensional_Gamma1` | 1 | 16 | finite-dimensionality of $`S_k(\Gamma_1(M))`$ |
| `DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range` | 1 | 675 | a semisimple 2-dimensional representation from two characters |
| `DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen` | 13 | 491 | the finite coefficient ring ($`58/71`$ of its cone already ported) |
| `DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd` | 18 | 478 | irreducibility from the second-moment bound plus oddness |
| `DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le` | 21 | 283 | image-order bound from a Frobenius-charpoly density condition |
| `DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual` | 31 | 463 | promote a compatible residual family to a complex representation |
| `CuspForm.HasNebentypus.diamondLinOne_apply_eq_smul` | 1 | 29 | diamond operators act by $`\varepsilon(d)`$ on forms with nebentypus |
| `ModularForm.exists_gamma0_qExpansion_eq_of_levelOne` | 1 | 36 | a level-one form is a form for $`\Gamma_0(N)`$ |
| `FrobeniusDensity.ncard_conj_gen_ne_zero_iff` | 1 | 17 | the Chebotarev-style conjugating-count criterion |
| `NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` | 1 | 32 | compactness of the adele class group $`\mathbb{A}_F/F`$ |
| `LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers` | 1 | 45 | the standard local additive character is trivial on $`\mathcal{O}`$ |

**Recommended first batch.** The lifting group
(`exists_weightOne_eisenstein`, `exists_hecke_eigen_reduction`,
`exists_weightTwo_hecke_eigen_reduction`) and the Galois-assembly group
(`exists_isSemisimpleRepresentation`, `exists_subalgebra_qCoeff_mem`,
`isIrreducible_…_of_odd`, `exists_natCard_range_le`,
`exists_galoisRep_complex_trace`) have a **union of 70 new nodes**. They are the
parts of the theorem FLT proves itself rather than imports from analysis, and
landing them gives the whole DS statement skeleton with the two gates as explicit
hypotheses, so the expensive automorphic work can then be attacked against a fixed
interface.

But that union is **32,804 raw `S_` lines**, not the sum of the eight targets'
short files: the assembly lemmas reach the Frobenius-density / Chebotarev step,
and that pulls the shared ray-class $`L`$-function node
`M4aTorus.completedRayL_fe` — **12,126 lines**, shared with the Kummer segment.
So even the cheap batch is not free of the foundational arithmetic layer. That is
the single clearest argument for porting that layer as its own subject rather than
discovering it through this cone (§4).

**Do not mistake the gates for small tasks.** `exists_tsum_norm` and
`exists_finset_qCoeff_mem` are single short statements (271 and 248 lines) but each
drags ~775–783 nodes of the automorphic block; they are the subject of §4, not of
this list.

### 3.1 Deferring the shared ray-class input

The batch's 32,804 lines are not all its own. It splits at
`M4aTorus.completedRayL_fe`, the 12,126-line proof of the analytic continuation and
functional equation of the completed narrow-ray-class $`L`$-function.

| piece | nodes | raw `S_` lines | depends on `M4aTorus.completedRayL_fe`? |
|---|---:|---:|---|
| lifting group + `exists_isSemisimpleRepresentation` + `exists_subalgebra_qCoeff_mem` + `exists_galoisRep_complex_trace` | 54 | 13,226 | no — **unconditional** |
| `isIrreducible_…_of_odd` + `exists_natCard_range_le` | 22 | 20,391 | yes |
| the same two, with `M4aTorus.completedRayL_fe` deferred | 21 | 8,265 | one interface |

So deferring one statement takes the batch from **70 nodes / 32,804 lines** to
**69 nodes / 20,678 lines**: 12,126 lines (37%) removed for one interface.

**The interface is narrower than the file.** `M4aTorus.completedRayL_fe` is a single
theorem (the 12,126-line file is its proof, 595 helper lemmas), and the batch reaches
it by exactly one route,
`NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one` (102 lines), whose
proof destructures it as

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
the functional equation or root number. That is strictly weaker than
`completedRayL_fe` and is the natural seam.

The residual 8,265 lines are themselves mostly a Chebotarev/density block
(`NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt`,
`GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective`, the four
`FrobeniusDensity.*` lemmas). Treating that block as a second interface — the
density input as a classical theorem to be proved once — leaves only
**5 nodes / 2,428 lines** for the two DS lemmas and the image-bound linear algebra
(`Matrix.GeneralLinearGroup.exists_natCard_le_…`,
`ModularCurve.SerreImage.contains_SL2`). The whole batch with both interfaces is
**59 nodes / 15,654 lines**, against 70 / 32,804 undeferred.

**Verdict.** Do the 54-node unconditional group now; land the two density-dependent
lemmas behind the ray-class-continuation interface (21 / 8,265) or, if the density
block is also to be proved once as its own subject, behind both interfaces
(5 / 2,428). The full ray-class file is not wasted either way — the converse cone
needs its functional equation for the Artin $`L`$-function step, so it is ported
once there and this batch reuses only the continuation.

## 4. Scout Q2 — the foundational modules and how they cluster

The measure of "foundational, judged by all FLT projects" used here: for each node
in the cone, how many of the pin's **49 landmark cones** contain it. A node in 20+
landmarks is vocabulary the whole development rests on. The DS cone's clusters,
with the landmark share that measures how foundational each one is:

| cluster | needed nodes | `S_` lines | avg share | why it is foundational |
|---|---:|---:|---:|---|
| function-field / curve layer | 425 | 217,578 | 21.2 | places, divisors, differentials, Riemann–Roch — beneath nearly every landmark |
| elliptic / Weierstrass / Tate | 129 | 123,876 | 21.4 | curve arithmetic, reduction, Tate curve — the Frey/Mazur/Ribet side |
| Galois reps / Frobenius / Artin (in-cone) | 23 | 4,620 | 17.5 | the representation vocabulary $`R = T`$ and level lowering both speak |
| modular curves / Hecke geometry | 443 | 219,577 | 15.9 | $`X_0/X_1`$, modular polynomials, period pairs, Hecke carriers |
| weight-one forms / Eisenstein | 134 | 52,352 | 12.4 | the form side of this cone; partly ported already |
| number fields / adelic infrastructure | 133 | 69,962 | 11.2 | adeles, Haar measure, adelic Fourier, class group — shared with Kummer/LT |
| automorphic / adelic $`\mathrm{GL}_2`$ | 534 | 242,409 | 10.7 | Iwasawa, Whittaker, Rankin–Selberg — the forward gate |
| Langlands–Tunnell (in-cone) | 38 | 17,344 | 9.3 | the octahedral/Artin input to the mod-3 step |
| `DeligneSerre` (our own) | 13 | 5,988 | 9.2 | the theorem itself |

The **definition layer** is the other half of "foundational": the cone touches
**281 definition modules**, and the most widely used are the shared vocabulary —
`AlgebraicCurve_DivisorClassGroup` (231 cone theorems), `AlgebraicCurve_IsCurveOver`
(226), `ModularCurve_X0` (162), `AutomorphicForm_ProductionPinsGeneral` (130),
`NumberField_AdelicBox` (127), `AutomorphicForm_FactorizableTestFn` (127),
`ModularCurve_JqCoeff` (119), `AutomorphicForm_WhittakerCoefficient` (105),
`ModularForm_HeckeOperator` (98), `FLTPrelim_Modularity` (77). These are the
candidates for `Defs/` homes: ported once, imported everywhere.

**Natural clusters and the order to port them.** The subjects are the rows above,
and each is a coherent theory that can be ported as a unit:

1. **Weight-one forms + the lifting** (134 nodes, 52k lines; partly ported).
   Entry: the lifting tasks of §3. This is our own subject and the cheapest.
2. **Galois reps / Frobenius / Artin vocabulary** (23 in-cone nodes, 4.6k lines;
   the full cluster is much larger). Entry: the assembly tasks of §3. Shared with
   $`R = T`$, so the homes should be generic, not `DeligneSerre`-private.
3. **Number fields / adelic infrastructure** (133 nodes, 70k lines). Foundational
   for the gates *and* for Langlands–Tunnell and the Kummer segment; the adele ring,
   Haar, adelic Fourier and class-group compactness belong in one subject directory.
4. **Automorphic / adelic $`\mathrm{GL}_2`$** (534 nodes, 242k lines). The forward
   gate. Because it is self-contained against the definition layer (§2 caveat), port
   it module by module — Iwasawa, then Whittaker/cuspidal constituents, then
   Rankin–Selberg — not as a closure.
5. **Langlands–Tunnell / octahedral / Artin** (38 in-cone nodes; the LT landmark's
   own cone is 6,805). The converse gate and the mod-3 endgame input; port together
   with the Artin $`L`$-function and class-field-theory vocabulary it shares with
   the Kummer files.
6. **Modular curves / Hecke geometry remaining** (443 nodes, 220k lines, but many at
   cost 1–5 because the port already owns the substrate). Interleave: it is shared
   with every landmark and is the cheapest place to gain coverage.
7. **Elliptic / Weierstrass / Tate** (129 nodes, 124k lines). Shared with the
   modularity-lifting and level-lowering efforts; port for those, and this cone
   inherits it.

Dependency order is 3 before 4, and 3/4 before the forward gates close; 5 is
independent of 4 for the converse but shares the number-field layer. 6 and 7 can be
interleaved at any point and are the best "coverage per node" because the frontier
is already adjacent.

### 4.1 Finer divisions of the two large substrate clusters

Rows 6 and 7 are named at namespace scale, and both contain more than one subject.
The partition below is name/module based (a node's namespace, its pin `S_`/`Def_`
family, and its identifier tokens), so the sub-counts are approximate; the row
totals are the exact namespace counts. It is a survey, not a work order.

**Row 7 — elliptic / Weierstrass / Tate.** The clean core is
`WeierstrassCurve.*` 105 nodes / 120,975 lines plus `TateCurve.*` 23 / 2,749 (the
doc's 129 is one node more than this namespace count). The nodes are not one
theory; they split into:

| unit | nodes | `S_` lines | home |
|---|---:|---:|---|
| **cyclic-kernel / place classification** | 24 | 83,224 | `WeierstrassCurve/IsogenyClassification.lean` |
| **explicit Vélu quotients and formulas** | 18 | 4,768 | `WeierstrassCurve/Velu.lean` |
| **Weierstrass function field, coordinate ring, places** | 19 | 15,027 | `WeierstrassCurve/FunctionField.lean` |
| **models, group law, variable change, $`j`$** | 18 | 4,946 | `WeierstrassCurve/Model.lean` |
| **torsion / division polynomials / Drinfeld** | 10 | 3,250 | `WeierstrassCurve/Torsion.lean` |
| **modular polynomial / `cyclicQuotientJ`** | 4 | 1,897 | `WeierstrassCurve/ModularPolynomial.lean` |
| **odd-order summing sets / char 2 and 3** | 4 | 2,077 | with Vélu/classification |
| **reduction / semistability / modularity data** | 3 | 1,356 | `WeierstrassCurve/Reduction.lean` |
| **formal group / EDS / special invariants** | 1 | 215 | `WeierstrassCurve/FormalGroup.lean` |
| **Tate curve: analytic parametrization** | 23 | 2,749 | `TateCurve/Parametrization.lean` |
| other (genus-one/closure) | 4 | 4,215 | — |
| **total** | **128** | **123,724** | |

The first thing the split shows is that **row 7 is two efforts under one name**.
The classical substrate — models and group law, the function field and its places,
torsion, the explicit Vélu construction, reduction — is roughly 70 nodes / 30k
lines. The cyclic-kernel/place classification is **24 nodes / 83k lines**, i.e. 67%
of the row's lines in 19% of its nodes, and it is dominated by six 4,000–12,000-line
statements (`exists_dualEndData_dual_mem_and_norm_eq_finrankAlong`,
`exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq(_of_isAlgClosed)`,
`isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom`,
`velu_map_equation_of_oddOrderSummingSet(_of_isAlgClosed)`,
`exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward`). This is
Mazur-type cyclic-isogeny classification, via the `Affine.FunctionField`/place gate
and the `IsogenyEndDatum`/`IsogenyHomDatum` endomorphism data — the engine of the
modularity-lifting step, and a different subject from "elliptic curves". Port order:
models/group law → function field and places (which need `AlgebraicCurve` places) →
explicit Vélu → the classification block.

The **Tate curve** is separate again (23 nodes / 2.7k lines: `pointX/Y_*` and the
`xfun`/`yfun` series, the `defect`/nodal-equation bookkeeping, the group law and
torsion parametrization, and the annulus/`zpow` geometry); it depends on
`AlgebraicCurve`'s annulus and residue material, not on the Weierstrass
classification.

**Function-field / curve layer.** The clean core is `AlgebraicCurve.*`: 387 nodes /
208,750 lines (the row's 425 includes about 38 function-field-flavoured nodes
outside the namespace — `ModularCurve`'s `qExpFunctionField`/`genusFF`/
`regularDifferentials` block and `PeriodPair`'s lattice lemmas). Its inner split:

| unit | nodes | `S_` lines | home |
|---|---:|---:|---|
| **places / valuations / local fields / completions** | 109 | 30,951 | `AlgebraicCurve/Places/` |
| **complex-analytic Jacobian / path integrals / Tate trace** | 68 | 90,867 | `AlgebraicCurve/Analytic/` |
| **divisors / class group / $`\mathrm{Pic}^0`$ / Jacobian** | 55 | 19,844 | `AlgebraicCurve/Divisors/` |
| **differentials / residues / Serre duality** | 47 | 18,245 | `AlgebraicCurve/Differentials/` |
| **Riemann–Roch / repartitions / genus / index** | 39 | 19,338 | `AlgebraicCurve/RiemannRoch/` |
| **curves, models, correspondences, function fields** | 45 | 16,055 | `AlgebraicCurve/Models/` |
| other (genericity/closure) | 24 | 13,450 | — |
| **total** | **387** | **208,750** | |

Two things stand out. First, the layer is **not one subject**: the algebraic core
(places + divisors + differentials + Riemann–Roch + models = 295 nodes / 104k lines)
and a **complex-analytic block** (Abel–Jacobi, path period lattices, cell
dissections, contour integrals, Tate's trace/agreement = 68 nodes / 91k lines) carry
comparable line weight. The analytic block is analysis on Riemann surfaces
(`residueTheoremK`, `tateAgreement`, `tateTraceCompat`, `tateChainRule`,
`abelJacobiDiv_*`, `span_real_pathPeriodLattice_eq_top`, the `CellDissection`/
`RadialRegion` grids), not function-field algebra, and is a separate porting effort
that happens to be grouped here. Second, the **`RationalFunctionField` place
package** inside the places unit (`RatFuncPlaces`, `RatFuncPlaceInfty`,
`RatFuncPlaceClassification`, ~16 nodes / 16k lines) is a self-contained classical
unit — places of $`\mathbb{P}^1`$ — that much else rests on, so it is the natural
first landing of the layer.

**Overlap with row 6.** 67 `ModularCurve` nodes import `Def_AlgebraicCurve_*`
(the `qExpFunctionField`, `genusFF`, `regularDifferentials`, `place` and Tate-module
blocks), so the `AlgebraicCurve` core is a prerequisite of the modular-curve cluster
as well, and row 6 cannot be interleaved freely before it. The definition-layer
fan-in says the same: `AlgebraicCurve_DivisorClassGroup` is imported by 231 cone
theorems and `AlgebraicCurve_IsCurveOver` by 226, the two most shared definitions of
the whole cone. Port the divisor/class-group and places/`IsCurveOver` vocabulary
once, at the bottom.

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
  treatment first:
  `python3 port_advise.py --target 'P2M/Sol/S_DeligneSerre_*'`.
* **One home per subject.** Shared real mathematics (weight-one Eisenstein series,
  q-expansion uniqueness, the adelic vocabulary, the modular-curve polynomial
  package) goes in `Defs/`/`Basic`, never `private` in each consumer; adapters stay
  `private` in the consumer.
* **Check the definition layer first.** The 281 definition modules of §4 are the
  most likely place where two subjects would otherwise duplicate a definition; port
  the shared `Def_*` module once.
* **Keep the interfaces stable.** Land the §3 batch with the gates as hypotheses, so
  the automorphic subject can be ported behind a fixed interface without reworking
  the DS lemmas.

## 6. Subject map and progress (living)

| # | subject | needed nodes | status | home |
|---|---|---:|---|---|
| 1 | weight-one forms + lifting | 134 | not started | `ModularForms/WeightOne/` (partly exists) |
| 2 | Galois reps / Frobenius / Artin (in-cone) | 23 | scoped, see §6.1 | `GaloisRep/`, `NumberTheory/FrobeniusDensity/` |
| 3 | number fields / adelic infrastructure | 133 | not started | `NumberTheory/Adelic/` |
| 4 | automorphic / adelic $`\mathrm{GL}_2`$ | 534 | not started | `AutomorphicForm/` |
| 5 | Langlands–Tunnell / octahedral / Artin | 38 (+LT cone) | not started | `LanglandsTunnell/` |
| 6 | modular curves / Hecke geometry remaining | 443 | partly ported | `ModularCurve/` (finer units: §4.1) |
| 7 | elliptic / Weierstrass / Tate | 129 | partly ported | `WeierstrassCurve/`, `Elliptic/`, `TateCurve/` (finer units: §4.1) |

Update this table and the §2 numbers when a subject lands; the §1 internal-target
table is the finer-grained progress record.

### 6.1 The Galois / Frobenius / Artin cluster (row 2)

The forward cone's 23 nodes of this subject are exactly

* `FrobeniusDensity.*` — 18 nodes, 2,505 raw `S_` lines;
* `GaloisRep.*` — 3 nodes, 1,611 lines
  (`exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel` 171,
  `exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range` 495,
  `sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective` 945);
* two bridges — `NumberField.exists_isFrobenius_lift_arithFrobAt` (240) and
  `Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen` (28).

That is **23 nodes / 4,384 raw `S_` lines**: the node count of §2/§4 row 2, with
a line total 236 below the 4,620 recorded there. The difference is that the row's
grouping included some of the `ValuationSubring` place/Frobenius vocabulary
(`isFrobeniusAt_of_forall_smul_sub_pow_mem` 149,
`IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` 83, and the `liesOverPrime` existence
family), which this strict reading counts under the number-field subject of row 3.
The mathematics of the strict 23 is
[../math/020-frobenius-density-and-artin.md](../math/020-frobenius-density-and-artin.md).

**It is not a porting unit; it is cut across the work order.** Mapping the 23 to
the 54-node slice of §3:

| cluster part | set | note |
|---|---|---|
| `GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_…` | S6 | with the two generic `Representation.*` conjugacy/lifting nodes |
| `GaloisRep.exists_isSemisimpleRepresentation_…` | S5 | distinct from the batch's `DeligneSerre.exists_isSemisimpleRepresentation_…add_mem_range_of_mul_mem_range` (675 lines), which is its larger sibling, not the same node |
| `FrobeniusDensity.*` (17 of the 18) + the two bridges | S7 | the S7 work order is 27 nodes; the other 8 (`ArithmeticFunction.sum_moebius_filter_dvd`, `CommRing.infinite_…`, `IsOpen.…`, `NumberField.exists_valuationSubring_eq_localization`, the four `ValuationSubring` lemmas) belong to other §4 subjects |
| `FrobeniusDensity.tailSum_le` | S7 | exposed in the cone but absent from S7's 27-node list; it is a helper of `degOneSum_add_log_isBigO` |
| `GaloisRep.sub_mul_log_le_tsum_rpow_neg_…` | deferred density block | one of the two lemmas the §3.1 second interface removes |

So S7's 27 nodes are this cluster's largest piece plus 8 place/number-field
vocabulary nodes, and the cluster's third `GaloisRep` node lives in the deferred
density interface rather than in the batch.

**The analytic block is the un-priced risk.** `primeSum_toReal_add_log_isBigO`
(474), `degOneSum_add_log_isBigO` (292) and `tailSum_le` (158) are `tsum`/`IsBigO`
analysis of the ideal sum. They are self-contained against Mathlib and therefore
each show cost 1 in `frontier.py` — the §2 measurement caveat in its purest form:
the largest files in the cluster contribute the fewest nodes. The group theory
above them (`weight_eq`, the degree-one fixed-point counts,
`statement_of_degOneAsymptotic`) is cheap.

**Dedup is concrete and named.** The Möbius/fixed-coset prelude
(`mem_zpowers_pow_div_iff` 30, `sum_moebius_mem_zpowers` 39,
`exists_pow_coprime_eq_of_orderOf_eq` 19, `orderOf_pow_orderOf_div` 8,
`ncard_conj_mem_eq_card_mul_ncard` 16, `ncard_eq_sum_indicator` 14) is repeated
verbatim and `private` in both `sum_moebius_mul_pos` and `weight_eq`;
`card_le_of_forall_pow_eq` occurs in both `stabilizer_eq_zpowers_arithFrobAt` and
`ncard_degreeOne_primesOver_under`. One `NumberTheory/FrobeniusDensity/Basic.lean`
(the H1 home of the definitions work order) covers them, together with
`tsum_normFiber` (22 × 2) and `isBigO_sum_of_tendsto_div` (20 × 2).

**Two nodes are one algebraic subject.** `GaloisRep.exists_isSemisimpleRepresentation_…`
is a 495-line `S_` file whose proof is delegated to the private `DSRt.main`; its
true content is the two-character descent that the `DeligneSerre.*` sibling (S5,
675 lines) states in the `add_mem_range`/`mul_mem_range` form. Port them as one
`GaloisRep/` (or `Algebra/`) subject, not as two independent nodes.

**Definitions.** The cluster's new definition modules are those of the D layer:
`Def_TaylorWiles_Primes`, `Def_FrobeniusDensity_{DegOneAsymptotic,PrimeSums,BadPrimes}`
and `Def_GaloisRep_FrobeniusPowerDense`. `GaloisFactorsThroughFiniteLevel`
(`Def_GaloisRep_Residual`) and the place vocabulary of
`Def_FLTPrelim_Ramification` / `Def_EllipticCurve_FrobeniusTrace` are already
ported.

## 7. Reproduce

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --top 40
python3 frontier.py --target DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen --json
python3 frontier.py --target DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace
python3 frontier.py --selfcheck
python3 port_advise.py --target 'P2M/Sol/S_DeligneSerre_*'
```

The per-cluster and landmark-share tables were computed with `fltdata.FltData` and
`frontier.needed` over the pin's landmark set (`meta['lm']`); the reproduction is
the three-command pattern of
[flt-non-frey-segments.md](flt-non-frey-segments.md) §1 with the cluster sets of §4
as the grouping.
