# Deligne–Serre weight one — port scout and subject plan

**Status: FIRST BATCH AND THE K-ROUTE RESIDUE/RR BLOCK LANDED, remeasured
(2026-09-30).** A living port scout for the
weight-one Deligne–Serre cone. §1 fixes the target set and its internal structure,
§2 is the effort against the current frontier, §3 the minimum-effort
mathematically significant tasks, §4 the foundational modules and their clusters,
§5 the redundancy discipline, §6 the living subject map, §7 how to reproduce.
Everything is measured against the pin `aa2d8b3` with `tools/deps` (docs-site graph
closure and the `S_`-line metric); the port's mathlib is `v4.34.0`.

**Remeasurement (2026-09-30).** The §3 recommended first batch has largely landed
(`lean/FLTForHuman/DeligneSerre/` 4 modules + `GaloisRep/` 6 modules + the
`FrobeniusDensity/` subject), and the K-route residue-theorem / Riemann–Roch block of
[PORTING-RR](../lean/topics/PORTING-RR.md) §3 has landed since the previous
remeasurement — rows 3.3/3.4 (the Tate agreement and trace-completion commutation),
row 3.6 (the K ending) and row 3.7 (the RR assembly) — so the frontier has moved from
541 to **650 nodes / 268,456 raw `S_` lines** (the previous reading was 608 /
183,832); the forward target is now **1,867 needed nodes / 901,998 lines** (from
1,897 / 949,701 at the previous remeasurement, and 1,988 / 995,359 before the first
batch), and four of the twelve §1 internal targets are closed. Because the K ending and
the RR assembly are in the port, the pin's analytic route to Riemann–Roch — the residue
theorem and the bridge — is **no longer deferred** for this cone: all seven nodes of
the RR family's analytic group are in the frontier, and the forward cone's unported
`residueTheorem|tateAgreement|residueTrace` nodes are **0**. The one PORTING-RR row
still open is row 3.5, the general perfect-field producer
`residueTheorem_of_perfectField`, which this cone does not consume (it is served by the
algebraically-closed K route). §4.2 records the measured effect, the bridge that
landed, and what is still deferred (the complex-analytic Jacobian block, not RR). The
pre-landing numbers are kept where they are the definition of the target; every
*needed* count below is the new measurement.

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
(the mathematics of the §6.1 Galois / Frobenius / Artin cluster),
[riemann-roch-strategy.md](riemann-roch-strategy.md) (the Riemann–Roch foundational
question split out of §4.1), and
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
`lean/FLTForHuman/` (**650 nodes / 268,456 raw `S_` lines** at the 2026-09-30
remeasurement, up from 608 / 183,832 at the previous one; it was 541 nodes when this
note was first remeasured, and 492 / 120,774 when it was written). "New nodes" is
`frontier.py`'s `needed(t) = closure(t) \ F`
with a frontier node terminal; "lines" is the sum of the `S_` files of the needed
nodes. The frontier is an upper bound read off the port's declaration names, so a
node counts as landed as soon as the port declares its statement.

## 1. Target set and internal structure

The public surface is small — 24 declarations in the `DeligneSerre` namespace, plus
the Langlands–Tunnell and `No2BridgeWiring` consumers. Its internal shape is what
matters for ordering.

| internal target | new nodes (was) | `S_` file | status |
|---|---:|---:|---|
| `DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr` | **0** (5) | 676 | **landed** (`DeligneSerre/Relevement.lean`) |
| `DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen` | **0** (13) | 491 | **landed** (`DeligneSerre/CoefficientRing.lean`) |
| `DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen` | **0** (17) | 1,242 | **landed** (`DeligneSerre/Lifting.lean`) |
| `DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd` | **11** (18) | 478 | 11 nodes / 17,470 lines, all through the ray-class input |
| `DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le` | **14** (21) | 283 | 14 nodes / 18,942 lines, same shared input |
| `DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual` | **0** (31) | 463 | **landed** (`DeligneSerre/Assembly.lean`) |
| `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen` | **765** (775) | 271 | **gate 1**: the Rankin-type second-moment bound |
| `DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen` | **766** (783) | 248 | **gate 2**: coefficient-ring finiteness via upper density |
| `DeligneSerre.eulerFactor_eq_and_tameLevel_of_weightOne_newform_qCoeff_eq_trace` | **380** (386 cone) | 709 | local factors and Artin-conductor level (converse side) |
| `DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace` | **413** (439) | 145 | the converse: rep $`\to`$ weight-one form |
| `DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen` | **1,102** (1,210) | 271 | the workhorse: residual charpolys from a weight-one form |
| `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` | **1,867** (1,988) | 291 | the forward capstone (characteristic zero, irreducible) |

The internal shape is otherwise unchanged, and the two density-dependent lemmas
(`isIrreducible`, `exists_natCard_range_le`) are now the only unported members of the
§3 batch: their **union** is 15 nodes / 19,420 lines, and removing the shared
`M4aTorus.completedRayL_fe` (12,126) leaves 14 nodes / 7,294.

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
| `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` | 2,308 | 430 | **1,867 / 901,998** | 1 |
| `DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen` | 1,528 | 415 | **1,102 / 531,825** | 1 |
| `DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace` | 439 | 26 | **413 / 194,995** | 1 |
| `FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd` (consumer) | 7,222 | 453 | 6,592 / 4,232,594 | — |
| `LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift` (the mod-3 input) | 6,805 | 432 | 6,362 / 4,125,930 | — |

The port already owns 430 of the forward cone's nodes, up from 400: the whole §3
first batch, the K-route residue/RR block, and almost all of the modular-curve /
function-field side (`ModularCurve` 151, `AlgebraicCurve` 141, `ModularForm` 23,
`FrobeniusDensity` 18, `CuspForm` 17, `WLight` 17). The rest is unported.

**Composition of the forward cone's 1,867 needed nodes** (2026-09-30), by the
natural subjects of §4. The clustering here is namespace-based (the previous
predicate-based grouping folded most of the generic-named tail into the named
clusters, so the two differ mainly in the tail); the landmark columns are the
doc-era pin-only measure of §4 and do not move with the port.

| subject cluster | needed nodes | raw `S_` lines | avg landmark share | max |
|---|---:|---:|---:|---:|
| automorphic / adelic $`\mathrm{GL}_2`$ | 533 | 249,591 | 10.7 | 22 |
| modular curves / Hecke geometry | 427 | 208,372 | 15.9 | 22 |
| function-field / curve layer | 324 | 128,923 | 21.2 | 24 |
| number fields / adelic infrastructure | 164 | 89,780 | 11.2 | 20 |
| elliptic / Weierstrass / Tate | 128 | 123,724 | 21.4 | 31 |
| weight-one forms / Eisenstein | 117 | 48,463 | 12.4 | 22 |
| Langlands–Tunnell (in-cone part) | 38 | 17,344 | 9.3 | 12 |
| Galois reps / Frobenius / Artin (in-cone part) | 8 | 3,791 | 17.5 | 20 |
| `DeligneSerre` (our own) | 7 | 2,297 | 9.2 | 11 |
| everything else | 121 | 29,713 | — | — |
| **total** | **1,867** | **901,998** | | |

The two gates have almost the same cone — `AutomorphicForm` 473 nodes,
`NumberField` 123, `LanglandsTunnell` 38 — so they are one
subject, not two: the analytic automorphic layer. The converse is a *different*
413-node cone, resting on `NumberField` 81, `ArtinL` 36, `M4aHerbrand` 34,
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

| task | new nodes (was) | `S_` file | status | what it is |
|---|---:|---:|---|---|
| `ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd` | **0** (5) | 703 | **landed** | the weight-one Eisenstein series $`E_1(1,\chi)`$ for a primitive odd $`\chi`$, with the divisor-sum $`q`$-expansion — the engine of the lifting |
| `DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr` | **0** (5) | 676 | **landed** | the relèvement: a residual eigenform of any weight is the reduction of a genuine eigenform |
| `DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen` | **0** (17) | 1,242 | **landed** | weight-one mod $`\ell`$ $`\to`$ weight two — the FLT lifting |
| `ModularForm.exists_rankinCohen_one_qExpansion_eq` | **2** (2) | 301 | | the first Rankin–Cohen bracket of modular forms |
| `CuspForm.finiteDimensional_Gamma1` | **1** (1) | 16 | | finite-dimensionality of $`S_k(\Gamma_1(M))`$ |
| `DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range` | **0** (1) | 675 | **landed** (as `GaloisRep.…`) | a semisimple 2-dimensional representation from two characters |
| `DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen` | **0** (13) | 491 | **landed** | the finite coefficient ring |
| `DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd` | **11** (18) | 478 | | irreducibility from the second-moment bound plus oddness |
| `DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le` | **14** (21) | 283 | | image-order bound from a Frobenius-charpoly density condition |
| `DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual` | **0** (31) | 463 | **landed** | promote a compatible residual family to a complex representation |
| `CuspForm.HasNebentypus.diamondLinOne_apply_eq_smul` | **0** (1) | 29 | **landed** | diamond operators act by $`\varepsilon(d)`$ on forms with nebentypus |
| `ModularForm.exists_gamma0_qExpansion_eq_of_levelOne` | **1** (1) | 36 | | a level-one form is a form for $`\Gamma_0(N)`$ |
| `FrobeniusDensity.ncard_conj_gen_ne_zero_iff` | **0** (1) | 17 | **landed** | the Chebotarev-style conjugating-count criterion |
| `NumberField.AdeleRing.compactSpace_quotient_principalSubgroup` | **1** (1) | 32 | | compactness of the adele class group $`\mathbb{A}_F/F`$ |
| `LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers` | **1** (1) | 45 | | the standard local additive character is trivial on $`\mathcal{O}`$ |

**Recommended first batch (landed).** The lifting group
(`exists_weightOne_eisenstein`, `exists_hecke_eigen_reduction`,
`exists_weightTwo_hecke_eigen_reduction`) and the Galois-assembly group
(`exists_isSemisimpleRepresentation`, `exists_subalgebra_qCoeff_mem`,
`isIrreducible_…_of_odd`, `exists_natCard_range_le`,
`exists_galoisRep_complex_trace`) were a **union of 70 new nodes**. Six of the eight
recommended-batch targets are landed (the lifting group and the Galois-assembly
group, except the two density lemmas) — eight of the fifteen §3 tasks in all. The two
density-dependent lemmas
(`isIrreducible_…_of_odd` 11 nodes / 17,470 lines and
`exists_natCard_range_le` 14 / 18,942) are what remains of the batch, with **union
15 nodes / 19,420 lines**. They are the parts of the theorem FLT proves itself
rather than imports from analysis, and landing them gives the whole DS statement
skeleton with the two gates as explicit hypotheses, so the expensive automorphic
work can then be attacked against a fixed interface.

The residual union is not free of the foundational arithmetic layer: the assembly
lemmas reach the Frobenius-density / Chebotarev step, and that pulls the shared
ray-class $`L`$-function node `M4aTorus.completedRayL_fe` — **12,126 lines**,
shared with the Kummer segment. Deferring that one interface leaves
14 nodes / 7,294. That is the single clearest argument for porting that layer as
its own subject rather than discovering it through this cone (§4).

**Do not mistake the gates for small tasks.** `exists_tsum_norm` and
`exists_finset_qCoeff_mem` are single short statements (271 and 248 lines) but each
drags ~775–783 nodes of the automorphic block; they are the subject of §4, not of
this list.

### 3.1 Deferring the shared ray-class input

The unconditional 54-node group of the batch **is landed**, so what remains is the
two density-dependent lemmas, and they split at `M4aTorus.completedRayL_fe`, the
12,126-line proof of the analytic continuation and functional equation of the
completed narrow-ray-class $`L`$-function.

| piece | nodes | raw `S_` lines | depends on `M4aTorus.completedRayL_fe`? |
|---|---:|---:|---|
| lifting group + `exists_isSemisimpleRepresentation` + `exists_subalgebra_qCoeff_mem` + `exists_galoisRep_complex_trace` | 54 | 13,226 | no — **landed** |
| `isIrreducible_…_of_odd` + `exists_natCard_range_le` | 15 | 19,420 | yes |
| the same two, with `M4aTorus.completedRayL_fe` deferred | 14 | 7,294 | one interface |

So the remaining batch is **15 nodes / 19,420 lines**, and deferring the one
statement takes it to **14 nodes / 7,294 lines**: 12,126 lines (62%) removed for
one interface.

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

The residual 7,294 lines are themselves mostly a Chebotarev/density block
(`NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt`,
`GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective`, the
`FrobeniusDensity.*` lemmas; 2,669 lines). Treating that block as a second
interface — the density input as a classical theorem to be proved once — leaves
**11 nodes / 4,625 lines**: the two DS lemmas themselves, the image-bound linear
algebra (`Matrix.GeneralLinearGroup.exists_natCard_le_…`,
`ModularCurve.SerreImage.contains_SL2`) and three ray-class-adjacent number-field
lemmas.

**Verdict.** The 54-node unconditional group is landed. Land the two
density-dependent lemmas behind the ray-class-continuation interface
(14 / 7,294) or, if the density block is also to be proved once as its own
subject, behind both interfaces (11 / 4,625). The full ray-class file is not
wasted either way — the converse cone needs its functional equation for the
Artin $`L`$-function step, so it is ported once there and this batch reuses only
the continuation.

## 4. Scout Q2 — the foundational modules and how they cluster

The measure of "foundational, judged by all FLT projects" used here: for each node
in the cone, how many of the pin's **49 landmark cones** contain it. A node in 20+
landmarks is vocabulary the whole development rests on. The DS cone's clusters,
with the landmark share that measures how foundational each one is:

| cluster | needed nodes | `S_` lines | avg share | why it is foundational |
|---|---:|---:|---:|---|
| function-field / curve layer | 354 | 176,626 | 21.2 | places, divisors, differentials, Riemann–Roch — beneath nearly every landmark |
| elliptic / Weierstrass / Tate | 128 | 123,724 | 21.4 | curve arithmetic, reduction, Tate curve — the Frey/Mazur/Ribet side |
| Galois reps / Frobenius / Artin (in-cone) | 8 | 3,791 | 17.5 | the representation vocabulary $`R = T`$ and level lowering both speak |
| modular curves / Hecke geometry | 427 | 208,372 | 15.9 | $`X_0/X_1`$, modular polynomials, period pairs, Hecke carriers |
| weight-one forms / Eisenstein | 117 | 48,463 | 12.4 | the form side of this cone; partly ported already |
| number fields / adelic infrastructure | 164 | 89,780 | 11.2 | adeles, Haar measure, adelic Fourier, class group — shared with Kummer/LT |
| automorphic / adelic $`\mathrm{GL}_2`$ | 533 | 249,591 | 10.7 | Iwasawa, Whittaker, Rankin–Selberg — the forward gate |
| Langlands–Tunnell (in-cone) | 38 | 17,344 | 9.3 | the octahedral/Artin input to the mod-3 step |
| `DeligneSerre` (our own) | 7 | 2,297 | 9.2 | the theorem itself |

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
is already adjacent — subject to the finer structure of §4.1: the `AlgebraicCurve`
places/divisor vocabulary is a prerequisite of row 6, so it is ported before the
modular-curve cluster is interleaved, and row 7's cyclic-kernel classification is a
separate, concentrated effort.

### 4.1 Finer divisions of the two large substrate clusters

**How the target nodes are found.** Every count in this section is of **FLT pin
nodes** and is independent of the port. The target set is the *forward cone* of
`DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` in the pin's
citation graph (`frontier.closure`) — a pin-only object — and the units inside it
are selected from each node's namespace and identifier tokens by the predicates of
the §7 script. The port's frontier enters only through the columns headed *ported*
and through one block marked **provisional frontier measurement**; those carry the
frontier size at measurement and move, while the target tables do not. The §2 and §4
tables above are doc-era *needed* counts and are therefore frontier-dependent: treat
them as the measurement of that date, not as the definition of the target.

**Row 7 — elliptic / Weierstrass / Tate.** 129 pin nodes / 125,059 `S_` lines
(`WeierstrassCurve.*` 106, `TateCurve.*` 23); 1 ported (unchanged at frontier 650).

| unit | nodes | `S_` lines | ported |
|---|---:|---:|---:|
| **Vélu isogeny / cyclic quotient / modular polynomial** | 50 | 91,966 | 0 |
| **Weierstrass function field / coordinate ring / places** | 19 | 15,027 | 0 |
| **models, group law, variable change, $`j`$** | 18 | 4,946 | 0 |
| **torsion / division polynomials / Drinfeld** | 11 | 4,585 | 1 |
| **other (genus-one/closure)** | 4 | 4,215 | 0 |
| **Tate curve: analytic parametrization** | 23 | 2,749 | 0 |
| **reduction / semistability / modularity data** | 3 | 1,356 | 0 |
| **formal group / EDS / special invariants** | 1 | 215 | 0 |
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
so the raw line total overstates the block too; the pooled `port_advise` method
below is how to quantify that. Port order: models/group law → function field and
places (which need `AlgebraicCurve` places) → explicit Vélu → the classification
block. The Tate curve depends on `AlgebraicCurve`'s annulus and residue material,
not on the Weierstrass classification.

**Function-field / curve layer.** The `AlgebraicCurve.*` cone is 465 pin nodes /
219,684 lines (the §4 row's 425 is a doc-era needed count and also includes about
38 function-field-flavoured nodes outside the namespace). Split by the §7
predicates:

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
**160 needed** at the current frontier; it was 94 / 177 at the previous remeasurement,
and 65 / 206 at frontier 541). Their finer sub-units, again pin-only:

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

> **Provisional frontier measurement (frontier 650).** Running `port_advise` on the
> 160 needed nodes of the 271-node pool (raw 41,281 lines) reads 320 `S_`+`Thm_`
> files / 2,049 declarations: **218 substitutions** (115 unique names, 4,334 lines
> already in the port), **221 names proved in ≥2 target files** (5,616 removable
> lines; 3,470 excluding the substituted names), a **3,135-line unique shared
> prelude**, and **≈33,500 projected new lines** (41,281 − 4,334 − 3,470, with the
> substitution span summed over all pin occurrences as in the earlier columns; the §7
> `pa_summary.py` reads the same components and prints its projection with the
> unique-name span instead, 35,370). The duplication ratio has kept falling — the previous run at
> frontier 608 read 177 needed nodes / 51,422 raw lines with 344 substitutions
> (177 unique names, 6,646 lines), 293 shared names (8,727 removable; 5,299 excluding
> substituted) and ≈39,500 projected lines, and at frontier 541 the pool was 206
> needed nodes / 76,463 raw lines with 230 substitutions (4,396 lines), 444 shared
> names (31,876 removable; 28,737 excluding substituted) and ≈43,000 projected lines.
> The port has already absorbed the duplication-heavy Riemann–Roch/adelic engine, so
> the **remaining** pool is much less dedup-able per raw line (81% of raw projects to
> new lines, against 77% at frontier 608 and 57% at frontier 541). These are the
> numbers that move with the frontier; the tables above do not.

The boundaries are **layers, not subjects**:

* **One shared Riemann–Roch / adelic prelude** (~4,700 unique lines), used by files
  of all three subjects: `ell`, `lSpace`, `poleDivisor`, `indexOfSpecialty`,
  `RiemannGenusReachedAt`, `TranscendenceTower`, `stichtenothGenusExists`,
  `adeleBddQuot*`, `residuePairing`, `reciprocity_linear`, under the generic algebra
  they run on (`finrank_quotient_chain*`, `nestedComapMapMkQEquiv`,
  `doubleResiduePairing_injective`, `linearIndependent_pow_of_transcendental`). This
  is **one module**, not a subject.
* **The already-ported place/valuation vocabulary** — `ord_nonneg_of_mem` (35
  files), `mem_iff_ord_nonneg` (26), `mk_mem_maximalIdeal_iff`, `residueOfCenter`,
  `inertiaDeg`, `toValuationSubring…`. The port's `AlgebraicCurve/` tree is now **73
  files / 2,124 declarations / 37,023 lines** and holds **141** of the cone's pin nodes
  (it has grown the `Genus/`, `RiemannRoch/`, `Canonical/`, `P1/`, `Tate/`,
  `ResidueTheorem/` and `Defs/` homes since the first measurement, when it was 17 files
  / 372 declarations / 77 nodes):
  `Defs/{Place,PlacesOverDVR,PlaceDictionary,RatFuncPlaces,Divisor,PushPull,Correspondence,SemilinearAut,KaehlerTranscendental,RiemannRochRows,PlaceEvaluation,PlaceEvaluationAlgebra,PlaceCompletion,LocalResidue,TateResidueCurrency}.lean`,
  `PrincipalDivisors/{RatFuncDegree,Transcendence}.lean`, `Genus/{Stichtenoth,Index}.lean`,
  `RiemannRoch/Assembly.lean`, `Canonical/WeilDifferential.lean`, the `P1/` residue core,
  the `Tate/` agreement and trace-completion commutation, and the `ResidueTheorem/` K
  family and RR assembly. Two blocks are
  deliberately deferred: `Defs/Divisor.lean` excludes the
  `Pic`/torsion/`AbelJacobiCard` block ("API for the modular Hecke/Galois-representation
  layer, not for the exchange cone"), and `Defs/SemilinearAut.lean` excludes the
  `Divisor`/`Pic0` action-and-torsion section of `BaseChangeGalois`. This layer is
  an **import boundary**, not work.
* **Per-file unique content** — ≈35,000 lines per the provisional
  measurement: 177 mostly-independent statements whose places/divisors/Riemann–Roch
  file names are cosmetic. The pin totals overstate even these: the
  `RationalFunctionField` files come in near-duplicate pairs (`ord_X_sub_C` ↔
  `ord_placeOfPoint_algebraMap` share 57 of 70 declarations;
  `ord_X_nonneg_of_ne_placeInfty` ↔ `ord_placeInfty_X` share 153 of 157), and the
  `ord_X_sub_C` pair alone is 1,017 removable lines. Duplication-light, genuinely
  separate families: `Pic0` (14 nodes / 3,103 lines / 762 shared), `SemilinearAut`
  (9 / 295 / 0), `normFormulaAlong` (2 / 45 / 0).

**The RR question is its own subject.** The Riemann–Roch foundational material — what
form of RR the cone needs, whether the sibling statements should be derived from it,
the two proof routes, and the siloing — is studied in
[riemann-roch-strategy.md](riemann-roch-strategy.md); the numbers live there. Three
facts matter to this scout:

* The cone reaches the RR family through the differentials ↔ cusp-forms transport:
  `ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm`
  (6 cone dependents) → `exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm`
  (5) → `CuspForm.IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq` (4) →
  `…exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt` (3) → the
  Deligne–Serre residual representation. The bottleneck is the transport above RR,
  not RR itself.
* The RR family is **siloed**: 72 cone nodes / 62,710 lines (**30 ported** at the
  current frontier, up from 22 at the previous remeasurement and 1 before the first
  batch); the full-RR statements are 4 nodes / 210 lines and
  almost every other node cites nothing within the family. `port_advise` on its
  42 still-needed nodes finds the family's duplication, so the shared prelude needs
  one home — §4.2 measures what can be pruned instead of ported.
* The **arithmetic** dimension route is independent: `CuspForm.finiteDimensional_Gamma1`,
  the $`\Gamma_1`$-integral basis and the coefficient-ring gate
  `DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen`
  have **zero RR ancestors**, so Sturm/q-expansion and integral-Hecke dimension theory
  bypass this layer.

**Status (2026-09-30).** Phase 1 (the genus / index engine) and phase 2 (the canonical
divisor) of [PORTING-RR](../lean/topics/PORTING-RR.md) are landed, and phase 3 has since
landed all of its rows except row 3.5, so the **algebraic Riemann–Roch and its analytic
K-route input are in the port**: `exists_weilCanonical_riemannRoch` gives
$`\exists W, \forall D, \ell D - \ell(W-D) = \deg D + 1 - g_{\mathrm{FF}}`$, with the
index formula, $`\Omega`$-finiteness and rank-one behind it; the K ending
(`residueTheoremK_of_isAlgClosed`, `residueTheoremK_ratFunc_of_isAlgClosed`), the Tate
agreement, the trace-completion commutation and the RR assembly
(`functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`) supply the
canonical-genus / duality API (`FunctionFieldRiemannRoch`, `WeilDualityAdelic`,
`genus_eq_genusFF`), and `residueTheorem_of_isAlgClosed` gives the general
`ResidueTheorem` over algebraically closed fields. What the one open row (3.5, the
perfect-field producer `residueTheorem_of_perfectField`) would add is a hypothesis the
cone does not need. Consequence for this scout: the function-field layer below (the
per-file `RationalFunctionField` / divisor / differential applications) can be ported
now, with only the three RR wrapper statements (155 lines) and the differentials ↔
cusp-forms transport still to land. §4.2 turns this into the measured payout and records
the landed bridge.

**Overlap with row 6.** 67 `ModularCurve` nodes import `Def_AlgebraicCurve_*` (the
`qExpFunctionField`, `genusFF`, `regularDifferentials`, `place` and Tate-module
blocks), so the `AlgebraicCurve` vocabulary is a prerequisite of the modular-curve
cluster too. The definition-layer fan-in says the same:
`AlgebraicCurve_DivisorClassGroup` (231 cone theorems) and
`AlgebraicCurve_IsCurveOver` (226) are the two most shared definitions of the whole
cone. Port the vocabulary once, at the bottom.

**Consequence for the plan.** For this cone, the curve vocabulary is **imported**
once — the port already owns 141 in-cone nodes of the `AlgebraicCurve` tree across
`Defs/{Place,PlacesOverDVR,PlaceDictionary,RatFuncPlaces,Divisor,PushPull,Correspondence,SemilinearAut}.lean`
and `PrincipalDivisors/{RatFuncDegree,Transcendence}.lean` — then the per-file
statements are grouped by *application*: `RationalFunctionField` ord computations,
divisor class group / principal divisors, `Pic0`/Jacobian, `RegularProlongation`
residue calculus, with the duplication-light
`Pic0`/`SemilinearAut`/`normFormulaAlong` tail kept separate. The order in which the
Riemann–Roch layer itself is ported, and which of its forms to derive rather than
re-prove, is the subject of
[riemann-roch-strategy.md](riemann-roch-strategy.md).

### 4.2 The RR prune for this cone (2026-09-30)

The prunes below were measured with `prune.py`'s
reachability semantics — `prunable(R) = closure(root) \ closure(root with R deleted)`
— and `frontier.py`'s `needed(t) =` reachable from $`t`$ avoiding $`R`$, minus the
ported frontier $`F`$.

**The analytic residue / RR block is landed, not deferred (changed 2026-09-30).**
The pin's analytic route to RR is
`functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` (6,257) fed by
`residueTheoremK_of_isAlgClosed` (8,121), `residueTheoremK_ratFunc_of_isAlgClosed`
(13,170), `tateAgreement` (4,816) and `residueTraceCompletionCommute` (1,109). The
K-route half of that block — the residue K ending, the Tate agreement, the
trace-completion commutation and the RR assembly — has now landed in the port
([PORTING-RR](../lean/topics/PORTING-RR.md) §3 rows 3.3/3.4/3.6/3.7), so this is a
**port, not a prune**: the RR family's analytic group is 7 nodes / 33,534 lines and all
7 are in the frontier, and the D-S cone's unported
`residueTheorem|tateAgreement|residueTrace` nodes are **0**. The measured effect is the
drop in the forward target from the previous remeasurement's 1,897 / 949,701 to
**1,867 / 901,998** — 30 nodes / 47,703 lines, essentially all of it the
function-field cluster (354 → 324 nodes, 176,626 → 128,923 lines).

The port reached RR on the **K route**, so the one row of
[PORTING-RR](../lean/topics/PORTING-RR.md) §3 still open — row 3.5, the general
perfect-field producer `residueTheorem_of_perfectField` — is **off this cone's path**:
the cone cites `residueTheorem_of_isAlgClosed` (40) and
`residueTheorem_of_residueTheoremK` (21), both ported and in the cone, and the RR
assembly `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`. Both of the
pin's analytic routes still exist in the graph; the route choice the earlier version of
this section deferred is settled by the port for this cone.

**The bridge (landed).** The pin's *statement* `functionFieldRiemannRoch_of_isAlgClosed`
is what the cone cites, and the port supplies the mathematics from the algebraic engine
plus the K ending: the pin's `MirrorAssembly` block (≈300 measured lines) was
transcribed as `ResidueTheorem/RRAssembly.lean` (694 ln) against the ported phase-1
engine, giving `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`, while
`ResidueTheorem/GeneralFromK.lean` (66 ln) gives `residueTheorem_of_residueTheoremK` and
`residueTheorem_of_isAlgClosed`. What remains unported for this cone is only the pin's
three thin wrappers `functionFieldRiemannRoch_of_isAlgClosed` (39),
`…_of_isCurveOver` (39) and `…_of_transcendental` (77) — **3 nodes / 155 lines** — whose
statements port unchanged over the assembled headline.

**Still deferred: the complex-analytic Jacobian block, not RR.** What remains deferred
on this cone is the separate complex-analytic Jacobian / path-integral / Abel–Jacobi /
`CellDissection` subject. Avoiding its still-needed nodes is `prunable = 205 nodes /
107,257 lines`, taking the forward target from 1,867 / 901,998 to 1,666 / 798,338 — a
saving of **201 nodes / 103,660 lines**; if the two differential-residue applications
and the three RR wrappers are deferred with it, `prunable = 209 / 113,669`, the target
falls to 1,663 / 798,183 (a saving of 204 nodes / 103,815 lines), and the rewiring
frontier is 13 kept nodes:
`exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf`
(817), `two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le` (812),
`moduleFinite_and_free_padicInt_tateModule_jH` (327),
`moduleFinite_padicInt_tateModule_jOne` (283), and the differentials layer
(`exists_isUnit_det_evalAt_differentialCoeff` 507,
`finite_and_finrank_regularDifferentials_eq_genus` 220). On the whole
`FLT.fermatLastTheorem` root the same analytic $`R`$ is 27 nodes / 64,873 lines with
`prunable = 35 / 95,884` and a 14-node rewiring frontier, reproducing
[riemann-roch-strategy.md](riemann-roch-strategy.md) §5.1.

**Prune the weaker RR versions (derive them).** With the assembly landed, the
siblings that are pure consequences of the full formula do not need the pin's
siloed proofs. Inside the D-S cone these are only
`degree_canonicalDivisor_eq_of_riemannRoch` (16),
`ell_canonicalDivisor_eq_genus_of_riemannRoch` (13) and `genus_eq_genusFF` (30) —
3 nodes / 59 lines, all short derivations that cite `FunctionFieldRiemannRoch`
(the first two already take it as a hypothesis in the pin). The *larger* candidates
the strategy flagged are **not** prunable here:
`two_mul_genus_sub_two_eq_of_degree_canonical` (1,229) takes the canonical-degree
facts `hK`/`hK'` as hypotheses (it is a ramification computation),
`instHasCanonicalDivisorRatFuncPerfectField` (1,461) is a construction, and the
16-node genus / `genusFF` comparison group is independent (Hurwitz line bound,
constant-field extension, splitting fields). The alternative *forms* of RR are
outside this cone: `ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable`
(128), `cechRiemannRoch_of_genusReached` (49),
`weilDualityAdelic_of_isAlgClosed` (54) and the pin's own Stichtenoth assemblies
`riemannGenusReached_of_stichtenothGenusExists` (2,728) /
`riemannIndexFormula_of_genusReached` (2,726), which the port's
`exists_genus_riemannIndex_of_stichtenothGenusExists` replaces. The whole-port
prune of that set is 10 nodes / 6,410 lines with `prunable = 11 / 6,461`, at a
102-node rewiring frontier; so for **this** cone the weaker-RR prune is 59 lines
plus the wrappers' 155, and the 6,461-line whole-port prune is a decision for the
broader plan rather than a D-S saving. Supplying the two predicate-form assemblies
that the frontier cites (`riemannIndexFormula_of_genusReached`,
`riemannGenusReached_of_stichtenothGenusExists`) is short from the ported
`RiemannGenusReachedAt.eq_of_ge` + `indexOfSpecialty_eq_of_genusReached` API, so
that 102-node frontier is rewire-to-the-engine, not re-prove. (The strategy's "derive the `ell` /
Riemann-inequality group" candidate is largely moot in the other direction: the six
`ell_le_*` / inequality nodes are already the engine's own ported prelude — the
Riemann inequality itself is `ell_le_degree_add_ellZero` — and the six still-unported
`ell` nodes are constant-field-extension computations, not the inequality.)

**Net effect on the scout.** The forward cone's 1,867 needed nodes already exclude
the landed §3 batch, the algebraic engine and the K-route residue/RR block. What is
left to prune is the complex-analytic Jacobian subject (204 nodes / 103,815 lines);
the function-field per-file applications can then proceed with only the
differentials ↔ cusp-forms transport held back.

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

The needed counts are the 2026-09-30 measurement, so they already net out the landed
first batch and the K-route residue/RR block.

| # | subject | needed nodes | status | home |
|---|---|---:|---|---|
| 1 | weight-one forms + lifting | 117 | **lifting group landed**; Eisenstein/`Rankin–Cohen` partial | `ModularForms/WeightOne/` |
| 2 | Galois reps / Frobenius / Artin (in-cone) | 8 | **subject landed** except six generic `Representation.*` and two density helpers, see §6.1 | `GaloisRep/`, `NumberTheory/FrobeniusDensity/` |
| 3 | number fields / adelic infrastructure | 164 | not started | `NumberTheory/Adelic/` |
| 4 | automorphic / adelic $`\mathrm{GL}_2`$ | 533 | not started | `AutomorphicForm/` |
| 5 | Langlands–Tunnell / octahedral / Artin | 38 (+LT cone) | not started | `LanglandsTunnell/` |
| 6 | modular curves / Hecke geometry remaining | 427 | partly ported | `ModularCurve/` (finer units: §4.1) |
| 7 | elliptic / Weierstrass / Tate | 128 | partly ported | `WeierstrassCurve/`, `Elliptic/`, `TateCurve/` (finer units: §4.1) |

Update this table and the §2 numbers when a subject lands; the §1 internal-target
table is the finer-grained progress record.

### 6.1 The Galois / Frobenius / Artin cluster (row 2)

The forward cone's 23 strict nodes of this subject — the ones this note grouped as row
2, and excluding the generic `Representation.*` group the status paragraph below
adds — are exactly

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

**Status (2026-09-30).** 21 of the 23 are landed (the whole `FrobeniusDensity/`
subject, `GaloisRep/{Prelude,RepConj,RepLift,SemisimpleDescent,ConjFromFrobenius}.lean`,
and both bridges `NumberField.exists_isFrobenius_lift_arithFrobAt` and
`Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen`). The **2 still needed**
among the strict 23 are the density-lemma helpers
`GaloisRep.sub_mul_log_le_tsum_rpow_neg_of_frobenius_mem_of_surjective` (945) and
`GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range`
(495), both of which the §3.1 interfaces remove from the batch. The cone's
subject cluster also reaches the generic `Representation.*` conjugacy/lifting nodes,
six of which are still needed — `exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top`
1,692, `exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue` 291,
`span_range_eq_top_of_isIrreducible` 151,
`exists_isCompl_forall_mem_of_compactSpace_of_continuous` 112,
`exists_extend_forall_apply_mul_of_injective` 69,
`pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero` 36. Counting those in,
the subject's in-cone total is 29 nodes / 7,332 lines, 21 ported and **8 needed** —
exactly the §2 row-2 count.

**It is not a porting unit; it is cut across the work order.** Mapping the 23 to
the §3 slice (whose 54-node unconditional group is now landed):

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
front = fr.frontier('union')            # provisional, moves with the port
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

The per-cluster and landmark-share tables were computed with `fltdata.FltData` and
`frontier.needed` over the pin's landmark set (`meta['lm']`); the reproduction is
the three-command pattern of
[flt-non-frey-segments.md](flt-non-frey-segments.md) §1 with the cluster sets of §4
as the grouping.

### Remeasurement and the §4.2 prune

The §1/§2/§3 tables are `frontier.py` reads of the named targets against the live
frontier; the §2 composition replaces the §7 classifier with the namespace map of
the note, and the §4.1 sub-unit tables and the pool are the §7 script above with
the current frontier.

```bash
cd tools/deps

python3 frontier.py --selfcheck | tail -1          # live frontier size

python3 - <<'PY'                                   # §1/§2/§3 needed counts
import frontier
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
for q in ['DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen',
          'DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen',
          'DeligneSerre.exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace',
          'FLT.No2BridgeWiring.weightOneNewformExists_not_cube_dvd',
          'LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift']:
    i = pay.pid(q); cone = fr.closure(i)
    need = frontier.needed(pay.cites, i, ported=front)
    print(len(need), pay.total_lines(need), len(cone), len(cone & front), q)
PY

python3 port_advise.py --nodes "$(cat build/pool_pdr_nodes.txt)" --json build/pool_pdr_advise.json
python3 build/pa_summary.py build/pool_pdr_advise.json \
  "$(python3 -c "import frontier;fr=frontier.Frontier();print(sum(fr.lines(fr.pay.pid(q)) for q in open('build/pool_pdr_nodes.txt').read().split(',')))")"
```

The §4.2 payout is `prune.py`'s reachability together with `frontier.py`'s
`needed` avoiding $`R`$. The residue/Tate set is now fully ported in-cone, so the
measurement that moves is the still-deferred complex-analytic block:

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
RESIDUE = has(r'residueTheorem', r'tateAgreement', r'residueTrace') - front
print('unported residue nodes in cone:', len(RESIDUE), pay.total_lines(RESIDUE))
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
for i in sorted(pay.frontier(root, COMPLEX), key=lambda i: -pay.lines(i)):
    print('  rewire', pay.lines(i), pay.qual(i))
PY
```

The same $`R`$ on `FLT.fermatLastTheorem` reproduces
[riemann-roch-strategy.md](riemann-roch-strategy.md) §5.1 (27 / 64,873; prunable
35 / 95,884; rewiring frontier 14).
