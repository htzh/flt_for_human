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
Eichler–Shimura package this cone's mod-$`p`$ layer shares), and
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
| 2 | Galois reps / Frobenius / Artin (in-cone) | 23 | not started | `GaloisRep/` |
| 3 | number fields / adelic infrastructure | 133 | not started | `NumberTheory/Adelic/` |
| 4 | automorphic / adelic $`\mathrm{GL}_2`$ | 534 | not started | `AutomorphicForm/` |
| 5 | Langlands–Tunnell / octahedral / Artin | 38 (+LT cone) | not started | `LanglandsTunnell/` |
| 6 | modular curves / Hecke geometry remaining | 443 | partly ported | `ModularCurve/` |
| 7 | elliptic / Weierstrass / Tate | 129 | partly ported | `WeierstrassCurve/`, `Elliptic/` |

Update this table and the §2 numbers when a subject lands; the §1 internal-target
table is the finer-grained progress record.

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
