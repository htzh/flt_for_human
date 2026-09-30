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
(`WeierstrassCurve.*` 106, `TateCurve.*` 23); 1 ported at frontier 541.

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
| complex-analytic Jacobian / path integrals / Tate trace | 67 | 84,610 | 0 |
| places / valuations / local fields / completions | 161 | 35,677 | 51 |
| divisors / class group / $`\mathrm{Pic}^0`$ / Jacobian | 69 | 22,494 | 14 |
| Riemann–Roch / repartitions / genus / index | 41 | 25,650 | 0 |
| differentials / residues / Serre duality | 46 | 18,190 | 0 |
| curves, models, correspondences, function fields | 52 | 16,681 | 7 |
| other (genericity/closure) | 29 | 16,382 | 5 |
| **total** | **465** | **219,684** | **77** |

The three subjects that the sharing shows to be one dependency mass — places (161)
+ divisors (69) + Riemann–Roch (41) = **271 pin nodes / 83,821 lines** (65 ported,
206 needed at frontier 541). Their finer sub-units, again pin-only:

| places sub-unit | nodes | `S_` lines | ported |
|---|---:|---:|---:|
| A. rational function field / $`\mathbb{P}^1`$ places | 21 | 8,816 | 7 |
| B. ord / valuation ring / local residue | 76 | 14,692 | 25 |
| C. place extension / ramification calculus | 19 | 2,140 | 8 |
| D. local expansion / completion / evaluation | 10 | 2,202 | 0 |
| E. place existence / basic vocabulary | 29 | 7,678 | 9 |
| Z. `SemilinearAut` action on places | 6 | 149 | 2 |
| **places total** | **161** | **35,677** | **51** |

| divisors sub-unit | nodes | `S_` lines | ported |
|---|---:|---:|---:|
| A. class group / degree / principal | 30 | 10,924 | 4 |
| C. pushforward / pullback / norm formula | 11 | 3,437 | 4 |
| D. $`\mathrm{Pic}^0`$ / Jacobian | 22 | 3,347 | 6 |
| E. pole / universal divisor | 6 | 4,786 | 0 |
| **divisors total** | **69** | **22,494** | **14** |

(Canonical divisor is not in this table: the predicate sends `canonicalDivisor` to
the differentials unit. Its 5 nodes / 3,254 lines belong with divisors A.)

> **Provisional frontier measurement (frontier 541).** Running `port_advise` on the
> 206 needed nodes of the 271-node pool reads 412 `S_`+`Thm_` files / 3,946
> declarations: **230 substitutions** (75 unique names, 4,396 lines already in the
> port), **459 names proved in ≥2 target files** (31,876 removable lines; 28,737
> excluding the substituted names), **6,394 lines of unique shared prelude**
> (2,447 Riemann–Roch/adelic + 2,266 generic algebra + 1,542 place/valuation + 139
> divisor), and **≈43,000 projected new lines** (76,463 − 4,396 − 28,737), ≈43%
> less than the needed subset's raw 76,463. These are the numbers that move with
> the frontier; the tables above do not.

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
  `inertiaDeg`, `toValuationSubring…`. The port's `AlgebraicCurve/` tree is 17 files
  / 372 declarations and verifies 77 in-cone pin nodes:
  `Defs/{Place,PlacesOverDVR,PlaceDictionary,RatFuncPlaces,Divisor,PushPull,Correspondence,SemilinearAut}.lean`
  and `PrincipalDivisors/{RatFuncDegree,Transcendence}.lean`. Two blocks are
  deliberately deferred: `Defs/Divisor.lean` excludes the
  `Pic`/torsion/`AbelJacobiCard` block ("API for the modular Hecke/Galois-representation
  layer, not for the exchange cone"), and `Defs/SemilinearAut.lean` excludes the
  `Divisor`/`Pic0` action-and-torsion section of `BaseChangeGalois`. This layer is
  an **import boundary**, not work.
* **Per-file unique content** — ≈37,000 lines per the provisional
  measurement: 206 mostly-independent statements whose places/divisors/Riemann–Roch
  file names are cosmetic. The pin totals overstate even these: the
  `RationalFunctionField` files come in near-duplicate pairs (`ord_X_sub_C` ↔
  `ord_placeOfPoint_algebraMap` share 57 of 70 declarations;
  `ord_X_nonneg_of_ne_placeInfty` ↔ `ord_placeInfty_X` share 153 of 157), and the
  `ord_X_sub_C` pair alone is 1,017 removable lines. Duplication-light, genuinely
  separate families: `Pic0` (14 nodes / 3,103 lines / 762 shared), `SemilinearAut`
  (9 / 295 / 0), `normFormulaAlong` (2 / 45 / 0).

**What the RR layer ultimately feeds (a dependency fact, not a size fact).** The RR
statements are the geometric dimension engine, and they feed dimension arguments
all the way up. The direct consumers of `finiteDimensional_lSpace` (110 forward-cone
dependents) are dimension counts —
`Divisor.exists_finset_finrank_riemannRochSpace_mapDomain_placeReduction_le`,
`finite_and_finrank_regularDifferentials_eq_genus` ($`\dim\Omega = g`$), the genus
comparisons `genusFF_le_of_constantFieldExtension_of_isAlgClosed` and
`sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one`; `indexOfSpecialty_eq_finrank_H1`
(91 dependents) is $`\dim H^1`$; and
`ell_canonicalDivisor_eq_genus_of_riemannRoch` /
`degree_canonicalDivisor_eq_of_riemannRoch` give $`\deg K = 2g - 2`$. They reach the
forward target by one narrow chain:
`ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm`
(6 cone dependents) →
`exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm` (5) →
`CuspForm.IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq` (4) →
`…exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt` (3) → the
Deligne–Serre residual representation. So the *bottleneck* is not the RR prelude
itself but the differentials ↔ cusp-forms transport above it.

**The arithmetic dimension route is independent.** `CuspForm.finiteDimensional_Gamma1`,
`CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`,
`ModularForm.exists_gamma0_qExpansion_eq_of_levelOne`, and the coefficient-ring gate
`DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen`
have **zero RR ancestors**: the Sturm/q-expansion and integral-structure dimension
results live on the arithmetic (Hecke/q-expansion) side and bypass the
function-field layer entirely.

**The complex-analytic block is upstream, not a side effort.** The two
most-depended-on nodes of the group are not RR but complex-analytic:
`tateAgreement` (4,816 lines, 104 cone dependents) and
`residueTheoremK_of_isAlgClosed` (8,121 lines, 102), and the RR theorem's
`functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` (6,257, 97) is proved
from them. The RR bucket (41 nodes) is in 22 of the 49 landmark cones, including
`fermat_last_theorem`, all three level-lowering landmarks,
`FreyPackage.{Mazur_Frey, frey_isModular}`, and
`LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift`. The
complex-analytic block (67 nodes / 84,610 lines) is therefore a separate *subject*
but sits on the critical path to the geometric dimension theory.

**Overlap with row 6.** 67 `ModularCurve` nodes import `Def_AlgebraicCurve_*` (the
`qExpFunctionField`, `genusFF`, `regularDifferentials`, `place` and Tate-module
blocks), so the `AlgebraicCurve` vocabulary is a prerequisite of the modular-curve
cluster too. The definition-layer fan-in says the same:
`AlgebraicCurve_DivisorClassGroup` (231 cone theorems) and
`AlgebraicCurve_IsCurveOver` (226) are the two most shared definitions of the whole
cone. Port the vocabulary once, at the bottom.

**Consequence for the plan.** For the function-field layer, drop
places/divisors/Riemann–Roch as porting units and port (i) the one RR/adelic
prelude, (ii) **import** the ported place/valuation vocabulary, and (iii) the
per-file statements grouped by *application* — `RationalFunctionField` ord
computations, divisor class group / principal divisors, `Pic0`/Jacobian,
`RegularProlongation` residue calculus — keeping the duplication-light
`Pic0`/`SemilinearAut`/`normFormulaAlong` tail separate.

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
```

The per-cluster and landmark-share tables were computed with `fltdata.FltData` and
`frontier.needed` over the pin's landmark set (`meta['lm']`); the reproduction is
the three-command pattern of
[flt-non-frey-segments.md](flt-non-frey-segments.md) §1 with the cluster sets of §4
as the grouping.
