# Topic: porting the relaxed option's 12-node analytic core

**Status: scouting report (2026-09-26), pinned to `aa2d8b3`. Purely
reconnaissance — no Lean build and no Lean work order.** The *relaxed* option of
[../../../studies/eichler-shimura-bypass-scout.md](../../../studies/eichler-shimura-bypass-scout.md)
§4.5/§6 keeps **both** route B (the weight-2 period map) **and** the 12-node
general-weight primitive, plus C′ (integrality), and drops only the
parabolic/bundled packaging (`coeffH1par` / `eichlerShimuraMap`). The 12 nodes
therefore stay in the port and their cost is a real line item. This file scopes
that line item: which nodes they are, what they *actually* depend on, where the
nominal count over- or under-states, and what a port would have to write.

Companion: the interface-3 rewiring plan
[TOPIC-interface-3-rewiring.md](TOPIC-interface-3-rewiring.md), the measured
scout [../../../studies/eichler-shimura-bypass-scout.md](../../../studies/eichler-shimura-bypass-scout.md)
(§2.3 for the node table, §4.5 for the variant), and the mathematics of the
weight-2 period argument
[../../../math/015-weight-two-hecke-periods.md](../../../math/015-weight-two-hecke-periods.md).
FLT is read at the pin `aa2d8b3`; the port's mathlib is `v4.34.0`. Line counts
are raw `S_`/`Thm_`/`Def_` file lines of the pin.

## 0. Verdict in one paragraph

At the **theorem layer** the relaxed core is small and self-contained: the
closure of the 12 is **15 nodes / 2,666 `S_` lines**, and the only non-`HeckeEis`
members are three short mathlib-absent lemmas. But the nominal figure
**"12 nodes / 2,301 lines" is a proof-body count, not a port footprint.** The
actual port surface is **2,666 `S_` lines + 250 `Thm_` statement lines + 1,449
`Def_` lines = 4,365 lines**, of which **191 lines are byte-identical duplicate
helper blocks** inside the 12 themselves (so no re-derivation is needed for
them). The analysis is one-variable complex analysis on $`\mathbb{H}`$ and
polynomial/matrix algebra; there is no scheme, sheaf or higher cohomology on the
path. Feasible with the usual shape-risk budget; the main cost drivers are the
633-line Hecke-correspondence node and the 305-line `pderiv`/`descFactorial`
computation, neither of which is a mathlib-gap problem. The definition layer is
9 modules / 214 declarations, of which 7 modules / 1,174 lines are actually
needed by the 12. Its only cohomology is a **hand-rolled degree-1 group
cohomology** (`coeffCocycles`/`coeffCoboundaries`/`coeffH1`) that is formally
disjoint from Mathlib's `groupCohomology` — which the pin's Galois side already
imports in 2,033 files — but is mathematically the same object; §5.4–§5.6 trace
the correspondence and the porting choice it forces.

## 1. The 12 nodes, identified

Key: **A** = genuine complex analysis; **ES** = E-S period-class packaging (no
analysis). Category is the scout §2.3 one (the scout's 12 analytic nodes are its
9 A nodes plus these 3 ES nodes).

| # | node (`HeckeEis.`) | `S_` lines | cat | what it is |
|---|---|---:|---|---|
| 1 | `exists_isEichlerIntegral` | 102 | A | the one existence input: a holomorphic $`f`$ has an Eichler integral $`F`$ |
| 2 | `isEquivariantPrimitiveWith_of_isEichlerIntegral` | 46 | ES | EI + slash-invariance $`\Rightarrow`$ equivariant primitive (hence a cocycle class) |
| 3 | `IsEichlerIntegral.slash` | 191 | A | EI transported by $`\delta`$: $`f \mid_k \delta`$ has EI $`\rho(\delta^{-1}) F(\delta\,\cdot)`$ |
| 4 | `IsEichlerIntegral.exists_sub_eq_const` | 172 | A | two EI of the same $`f`$ differ by a constant binary form |
| 5 | `IsEichlerIntegral.eq_zero_of_eval_eq_const` | 92 | A | ladder argument: constant $`\mathrm{eval}[(1,-\tau)]`$ of an EI forces $`g=0`$ |
| 6 | `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` | 305 | A | iterated $`\partial_1`$ derivative identity for the eval of an EI |
| 7 | `IsEichlerIntegral.isBoundedAtImInfty_eval` | 178 | A | growth at the cusp from boundedness + periodicity of $`f`$ |
| 8 | `IsEichlerIntegral.binarySubst_adjugate_comp_smul` | 184 | A | EI transported along the Hecke correspondence $`\alpha_\ell^{\mathrm{adj}}`$ |
| 9 | `IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` | 44 | ES | primitives differing by a constant give cocycles differing by a coboundary |
| 10 | `jFactor_pow_mul_eval_binaryFormRepSL` | 74 | ES | automorphy-factor identity $`j^n \cdot \mathrm{eval}(\rho(g) P) = \mathrm{eval}(P)`$ (pure matrix algebra) |
| 11 | `coeffH1Mk_cocycle_heckeTLin_modularForm` | 633 | A | Hecke equivariance of the period class: $`T_\ell`$ on the EI cocycle of $`f`$ is the EI cocycle of $`T_\ell f`$ |
| 12 | `modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` | 280 | A | period injectivity / nonvanishing: the EI class of $`f`$ is 0 only if $`f=0`$ |
| | **total** | **2,301** | | **9 A / 3 ES**; the honest "analytic" subset is the 9 A nodes / 2,137 lines |

The three ES nodes are *not* analysis. `jFactor_pow_mul_eval_binaryFormRepSL`
(#10) is linear algebra over $`\mathbb{C}`$; #2 and #9 are the two algebraic
bridge lemmas that turn an Eichler integral into a `coeffCocycles` class. So the
label "12 analytic" is a reachability label for interface 3, not a measurement
of analytic content; the analytic work is 9 nodes.

## 2. What "actual" means, and where nominal and actual differ

The docs-site graph (`tools/deps`) records `cites(A,B)` when
`P2M/Sol/S_A.lean` imports `Theorems.Thm_B.lean`, and the per-edge `cu` is the
count of uses of `B` in `A`'s proof. Measured on the 12:

- **theorem-module level: nominal = actual.** All 15 nodes reachable from the 12
  along `cu > 0` edges; the nominal closure contains **zero** `cu = 0` edges.
  There is no import-only ballast inside this core. (Contrast the whole graph,
  which has 2,890 `cu = 0` edges.)
- **the layers the import graph omits are the actual port surface.** The graph
  has theorem nodes only. The port must also carry (a) the `Definitions/Def_*`
  modules named in a node's statement (`sd`) and proof (`pd`), (b) the public
  `Theorems/Thm_*` statement files, and (c) the mathlib facts. Counting the 12
  theorem nodes alone hides 2 of those 3 layers.
- **declaration level: the pin already carries its own dependency list.**
  Each `S_` file's `p2m_export "HeckeEis" "…"` line names the exact `HeckeEis`
  declarations the proof uses; these confirm the module-level edges and show,
  for example, that #3 `slash` uses `binarySubst`, `binaryFormRepSL`,
  `binaryFormRepSL_apply_coe`, `linePow`, `jFactor`, `jFactor_eq_denom`,
  `jFactor_ne_zero`, `binaryFormRepSL_linePow`, `IsEichlerIntegral` from the two
  E-S definition modules.
- **redundancy is real and is invisible in the node graph.** Four of the twelve
  `S_` files re-embed a byte-identical helper block that already exists in
  another of the 12 (§6); 191 lines are such a second copy, including a 132-line
  block copied whole between two files.

The source check for §3–§6 was: resolve the 12 to node ids, read each `cites`
with its `cu`, read each node's `sd`/`pd` from the docs data, then diff the
twelve `S_` bodies with `difflib` (`SequenceMatcher`, blocks `>= 8` lines). No
Lean build was run.

## 3. Actual theorem-layer dependencies

### 3.1 Direct edges (all `cu > 0`)

| node | direct actual theorem deps (`cu`) |
|---|---|
| `exists_isEichlerIntegral` | `Complex.exists_hasDerivAt_of_starConvex` (1) |
| `isEquivariantPrimitiveWith_of_isEichlerIntegral` | `IsEichlerIntegral.slash` (2), `IsEichlerIntegral.exists_sub_eq_const` (2) |
| `IsEichlerIntegral.slash` | — |
| `IsEichlerIntegral.exists_sub_eq_const` | — |
| `IsEichlerIntegral.eq_zero_of_eval_eq_const` | `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` (2), `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` (1) |
| `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` | — |
| `IsEichlerIntegral.isBoundedAtImInfty_eval` | `hasDerivAt_eval_iterate_pderiv` (1), `MvPolynomial…iterate_pderiv…` (1), `UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic` (1), `jFactor_pow_mul_eval_binaryFormRepSL` (2) |
| `IsEichlerIntegral.binarySubst_adjugate_comp_smul` | — |
| `IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` | — |
| `jFactor_pow_mul_eval_binaryFormRepSL` | — |
| `coeffH1Mk_cocycle_heckeTLin_modularForm` | `binarySubst_adjugate_comp_smul` (1), `exists_sub_eq_const` (1), `cocycle_sub_cocycle_mem_coeffCoboundaries` (1) |
| `modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` | `IsEichlerIntegral.slash` (2), `isBoundedAtImInfty_eval` (1), `eq_zero_of_eval_eq_const` (1) |

Seven nodes are **sources** (no intra-12 dependency): #1, #3, #4, #6, #8, #9,
#10. Five are **internal**: #2, #5, #7, #11, #12. The DAG has three levels:
level 0 = the seven sources; level 1 = `eq_zero_of_eval_eq_const`,
`isBoundedAtImInfty_eval`, `isEquivariantPrimitiveWith_of_isEichlerIntegral`,
`coeffH1Mk_cocycle_heckeTLin_modularForm`; level 2 =
`modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero`. **The 12 are not 12
independent units: five of them are consumed only by another member of the 12**,
and two — `hasDerivAt_eval_iterate_pderiv` and `slash` — are each shared by two
members.

### 3.2 The target lemma cites only four of the twelve

`HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul` cites, with
`cu = 1` each: `exists_isEichlerIntegral` (#1),
`isEquivariantPrimitiveWith_of_isEichlerIntegral` (#2),
`coeffH1Mk_cocycle_heckeTLin_modularForm` (#11), and
`modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` (#12). The other eight are
reachable through those four. This is the analytic call-site structure the
scout §2.4 records (lines 370–390 of the 523-line lemma).

### 3.3 Actual theorem closure: 15 nodes / 2,666 lines

| `S_` lines | node | in the 12? |
|---:|---|---|
| 633 | `HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm` | yes |
| 305 | `HeckeEis.IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` | yes |
| 280 | `HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` | yes |
| 191 | `HeckeEis.IsEichlerIntegral.slash` | yes |
| 184 | `HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul` | yes |
| 178 | `HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval` | yes |
| 175 | `UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic` | **external** |
| 172 | `HeckeEis.IsEichlerIntegral.exists_sub_eq_const` | yes |
| 150 | `Complex.exists_hasDerivAt_of_starConvex` | **external** |
| 102 | `HeckeEis.exists_isEichlerIntegral` | yes |
| 92 | `HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const` | yes |
| 74 | `HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL` | yes |
| 46 | `HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral` | yes |
| 44 | `HeckeEis.IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` | yes |
| 40 | `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` | **external** |
| **2,666** | | **12 + 3** |

The public `Theorems/Thm_*` statement files for these 15 add **250 lines**
(218 for the 12, 32 for the three external nodes).

## 4. The three external nodes, and the mathlib gaps

These are the *only* theorem dependencies outside the 12. Each was checked
against the port's mathlib `v4.34.0` checkout under
`lean/.lake/packages/mathlib`.

| node | `S_` lines | not in mathlib `v4.34`? | consumers | content |
|---|---:|---|---|---|
| `Complex.exists_hasDerivAt_of_starConvex` | 150 | **yes** — no `exists_hasDerivAt_of_starConvex`; mathlib has the dominated-convergence machinery but not the packaged statement | this core **+ 2 `AlgebraicCurve.CellDissection` nodes** | radial path integral $`g(w)=\int_0^1 (w-q) f(q+t(w-q))\,dt`$ differentiated under the integral sign (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`), with compactness bounds |
| `UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic` | 175 | **yes** — mathlib has `isBoundedAtImInfty` and `cuspFunction`, but not this implication | this core only | $`v'=u`$, $`u`$ bounded + periodic, $`v`$ periodic $`\Rightarrow`$ $`v`$ bounded at the cusp; uses `cuspFunction`, `dslope`, `isExactOn_ball`, `Periodic.qParam` |
| `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` | 40 | **yes** — `iterate_pderiv` does not occur in mathlib | this core only | $`\varphi`$ homogeneous of degree $`n`$, $`n \lt i`$ $`\Rightarrow`$ $`(\partial_k)^i\varphi=0`$; pure `MvPolynomial` algebra |

Two of the three (215 of 365 lines) are private to this core; the star-convex
node is shared with route-A geometry and would be ported for that route anyway
if it is on the endgame path. The analysis profile is exactly the scout §2.6
one: one-variable complex analysis on $`\mathbb{H}`$, a Liouville-type
boundedness input, and polynomial algebra. **No Dolbeault, no Hodge theory, no
several-variable analysis.** The ported tree already uses `isBoundedAtImInfty`
in the `ModularForms/` q-expansion layer, but contains none of these three
statements (`grep` for `StarConvex`, `iterate_pderiv`, and the
`of_hasDerivAt_of_periodic` name is empty in `FLTForHuman/`).

## 5. The definition layer: 9 modules / 1,449 lines, 214 declarations

The `sd`/`pd` def-module sets of the 12, resolved transitively through
`Definitions/Def_*.lean` imports. Declaration counts are from the pin's `ddecl`
index (defs, theorems, abbrevs and instances).

### 5.1 The nine modules

| `Def_` lines | decls | module | role | in the 12's actual need? |
|---:|---:|---|---|---|
| 304 | 44 | `Gamma0HeckeOperatorHom` | Hecke correspondence: `alphaMat`, `heckeUpper(SL)`, `heckeConj(SL)`, `gammaZeroRed`, `transferAux`, `resHom`, `coresHom`, `pullbackHom`, `heckeOperatorHom` | yes |
| 204 | 50 | `ModularForm_HeckeOperator` | `heckeMatrix`, `heckeDiagMatrix`, `heckeT`/`heckeU` on functions | yes — already ported (`FLTForHuman/ModularForms/Defs/HeckeOperator.lean`) |
| 182 | 26 | `ProjectiveLineMatrixAction` | `ProjectiveLine` matrix action, `projLineRepSL`, `projLineAlphaAdj`, `ProjLineCusps` | **no** — imported only for the `Eval` section |
| 153 | 21 | `Gamma0CoeffCohomology` | hand-rolled degree-1 group cohomology, the parabolic layer, `coeffHeckeFun` | yes |
| 149 | 19 | `HeckeEis_EichlerIntegral` | `linePow`, `jFactor`, `IsEquivariantPrimitiveWith`, `IsEichlerIntegral`, `eichlerShimuraMap` | yes (minus the last) |
| 140 | 16 | `HeckeEis_BinaryFormRep` | `BinaryForm`, `binarySubst`, `binaryFormRepSL`, `binaryFormAlphaAdj`, + `Eval` section | yes (minus `Eval`) |
| 112 | 14 | `Gamma0CoeffCohomologyEigen` | `coeffH1`, `coeffH1Mk`, `coeffH1parToH1`, `IsCoeffHeckeOnH1`, `IsEigensystemH1`, `binaryFormRep` | yes |
| 112 | 12 | `ModularForm_HeckeOperatorForms` | `heckeTLin`/`heckeULin` on `ModularForm`/`CuspForm` | yes — already ported, the port file says "verbatim" |
| 93 | 12 | `ModularCurve_ProjectiveLine` | `IsUnimodularRow`, `UnimodularRow`, `ProjectiveLine`, `borel` | **no** — imported only for the `Eval` section |
| **1,449** | **214** | | | **7 modules / 1,174 lines actually needed by the 12** |

### 5.2 The declaration-level trace

```
Mathlib primitives
├─ MvPolynomial + homogeneousSubmodule ─► Def_HeckeEis_BinaryFormRep
│     BinaryForm, binarySubst,
│     binaryFormRepSL : Representation K SL(2,ℤ) (BinaryForm K n)   [the representation]
│     binaryFormAlphaAdj                                            [the Hecke α_ℓ operator]
│     └─ Eval section: evalRow, binaryFormEval ─ needs ModularCurve_ProjectiveLine
│                                              ─ NOT used by the 12
├─ ModularForm / SlashAction ─► Def_ModularForm_HeckeOperator (heckeMatrix, heckeT, heckeU)
│     └─► Def_ModularForm_HeckeOperatorForms (heckeTLin, heckeULin)   [already ported]
├─ Submodule / LinearMap / Quotient ─► Def_Gamma0CoeffCohomology
│     coeffCocycles, coeffCoboundaryMap, coeffCoboundaries,
│     IsParabolicCocycle, coeffParabolicCocycles, coeffH1par, coeffHeckeFun
└─ Subgroup / Matrix / SL(2,ℤ) ─► Def_Gamma0HeckeOperatorHom
      heckeUpper, heckeConj, transferAux, coresHom, resHom, heckeOperatorHom
                                          └─► coeffHeckeFun (coset sum)

Def_HeckeEis_EichlerIntegral
    linePow, jFactor, IsEquivariantPrimitiveWith, IsEichlerIntegral
    IsEquivariantPrimitiveWith.cocycle_mem_coeffCocycles ── lands in Def_Gamma0CoeffCohomology
    [eichlerShimuraMap: dropped packaging]

Def_Gamma0CoeffCohomologyEigen
    coeffH1 := coeffCocycles ⧸ coeffCoboundaries, coeffH1Mk, coeffH1parToH1,
    IsCoeffHeckeOnH1, IsEigensystemH1                     [the contract]
    binaryFormRep
```

The 12 touch only the top and bottom blocks: `binaryFormRepSL` /
`binaryFormAlphaAdj` (from `HeckeEis_BinaryFormRep`), `coeffCocycles` /
`coeffCoboundaries` / `coeffH1` / `coeffH1Mk` (from the two cohomology modules),
`IsEquivariantPrimitiveWith` / `IsEichlerIntegral` (from
`HeckeEis_EichlerIntegral`), and `ModularForm.heckeTLin` /
`Gamma0HeckeOperatorHom`'s coset data (through the 633-line node).

### 5.3 Nominal vs actual at this layer

Ten of the twelve `S_` files carry the *same* three
`import Definitions.Def_…` lines (`HeckeEis_BinaryFormRep`,
`Gamma0CoeffCohomology`, `HeckeEis_EichlerIntegral`) regardless of use; only
`coeffH1Mk…` (7 def imports) and `modularForm_eq_zero…` (4) add more. The shard
`sd`/`pd` sets confirm that this nominal list is also the *directly used* list.

At the **transitive** level, however, the closure is not tight: the two
projective-line modules enter only because `Def_HeckeEis_BinaryFormRep` imports
them for its `Eval` section (`evalRow`, `binaryFormEval`). Measured directly,
**none of the 12 uses `ProjectiveLine`, `UnimodularRow`, `projLine*`,
`binaryFormEval`, `evalRow`, or `Additive`** (0 of 12 files each). So the 12's
actual definition need is **7 modules / 1,174 lines**, and the extra
`ProjectiveLineMatrixAction` + `ModularCurve_ProjectiveLine` (275 lines) is
shared ballast: `binaryFormEval` is retained endgame API (cited by
`CuspForm.heckeLocal.*` and interface 5) and `projLineRepSL` belongs to the
dropped packaging. A port that splits FLT's `Def_HeckeEis_BinaryFormRep` into a
"binary forms / representation" module and a separate "projective-line
evaluation" module gets the tighter figure.

The port would also reorganise by role (playbook §7.1): FLT's
`Def_HeckeEis_BinaryFormRep` (representation) and `Def_HeckeEis_EichlerIntegral`
(analysis) are separate concerns, and the port should adopt mathlib's
`MvPolynomial`/`UpperHalfPlane`/`ModularForm` types directly, as the existing
`FLTForHuman/ModularForms/*` already does for the Hecke operators (316 of the
1,449 lines are already ported).

### 5.4 The two cohomologies in the pin

The pin contains **two unrelated cohomology developments**:

1. **The hand-rolled one on this path.** `HeckeEis.coeffCocycles` /
   `coeffCoboundaries` / `coeffH1` (and the parabolic `coeffH1par`) are defined in
   `Def_Gamma0CoeffCohomology` / `Def_Gamma0CoeffCohomologyEigen` from
   `Submodule`, `LinearMap` and `Submodule.Quotient` alone: 1-cocycles
   $`z(gh) = z(g) + \rho(g)z(h)`$ as a submodule of $`G \to V`$, 1-coboundaries
   as the range of $`v \mapsto (\rho(g)v - v)_g`$, and their quotient. It shares
   Mathlib's **representation** layer (`Representation`, from
   `Mathlib.RepresentationTheory.Basic`, and `Module.End`) but imports nothing
   from the **cohomology** layer (`Mathlib.RepresentationTheory.Homological`).
2. **Mathlib's group cohomology, used heavily elsewhere.** The Galois/Selmer
   side has **49** `Definitions/Def_GroupCohomology_*.lean` modules (`Kummer`,
   `Selmer`, `TateShiftMaps`, `ContinuousH1`/`H2`, `PoitouTate`, …) and
   **2,033** `P2M`/`Theorems` files reference mathlib's `groupCohomology`,
   `cocycles₁`, `H1π` or `H1Iso`. The port's endgame will import
   `Mathlib.RepresentationTheory.Homological.GroupCohomology.*` regardless.

The two never meet: the 9 def modules and the twelve `S_` files contain **zero**
occurrences of `groupCohomology`, `cocycles₁`, `coboundaries₁`, `H1π`,
`Rep.of`, or `inhomogeneousCochains`. So there is no *formal* interaction today —
but there is an exact *mathematical* correspondence, which is the porting
decision.

### 5.5 The hand-rolled cohomology against Mathlib's

Mathlib `v4.34` has degree-1 group cohomology for $`A : \mathrm{Rep}\ k\ G`$ in
`Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree`. The
correspondence (with `A := Rep.of ρ`):

| pin (`HeckeEis.`, on `ρ : Representation K G V`) | Mathlib (on `A : Rep k G`) | relationship |
|---|---|---|
| `coeffCocycles ρ` | `groupCohomology.cocycles₁ A` | same submodule of `G → A`; the identities differ only by `add_comm` |
| `mem_coeffCocycles_iff` | `mem_cocycles₁_iff` | same statement |
| `coeffCoboundaryMap ρ` ($`v \mapsto (\rho g v - v)_g`$) | `d₀₁ A` | same linear map |
| `coeffCoboundaries ρ` (`LinearMap.range`) | `coboundaries₁ A` (`LinearMap.range (d₀₁ A).hom`) | identical definition |
| `coeffCoboundaries_le_coeffCocycles` | `coboundaries₁_le_cocycles₁` | same |
| `coeffH1 ρ` (cocycles modulo coboundaries) | `H1 A`; `H1Iso : H1 A ≅ cocycles₁ A ⧸ coboundaries₁ A` | isomorphic, **not** definitionally equal |
| `coeffH1Mk ρ` | `H1π A` | the quotient map |
| `coeffH1Mk_eq_zero_iff` | `H1π_eq_zero_iff` | same |
| trivial coefficients: `coeffCoboundaries 1 = ⊥`, `coeffH1 1 ≅ Additive Γ₀ →+ K` | `coboundaries₁_eq_bot_of_isTrivial`, `cocycles₁IsoOfIsTrivial`, `H1IsoOfIsTrivial : H1 A ≅ (Additive G →+ A)` | the scout §1.2 carrier bridge is **already in mathlib** |
| `IsParabolicCocycle`, `coeffParabolicCocycles`, `coeffH1par`, `coeffH1parMk`, `coeffH1parToH1` | none | parabolic sub-quotient, pin-specific |
| `coeffHeckeFun`, `IsCoeffHeckeOnH1`, `heckeOperatorHom`, `transferAux`, `coresHom`, `resHom`, `pullbackHom` | none | Hecke action, pin-specific |
| `IsEigensystemH1` | none | the contract |

The bridge is thin: `coeffCocycles ρ = cocycles₁ (Rep.of ρ)` should go through
by `Submodule.ext` and `add_comm` on the carrier, and `coeffH1 ρ ≃ₗ[K] H1
(Rep.of ρ)` through `H1Iso`. The trivial-coefficient specialization is where
mathlib pays for itself: `H1IsoOfIsTrivial` lands in exactly the tame
`Additive G →+ A` type that route B and the CohCarrier bridge use,
and `coboundaries₁_eq_bot_of_isTrivial` is the "quotient disappears" fact.

### 5.6 Port implication

- **Option (a) — port the definitions verbatim.** Carry the 7 modules / 1,174
  lines (214 declarations, minus the projective-line and packaging sections) as
  written. Self-contained, no mathlib cohomology dependency, and every one of the
  12's and the target contract's statements is unchanged. This is the low-risk
  choice and is what the faithfulness discipline (playbook §7.4) favours.
- **Option (b) — re-found on Mathlib's group cohomology.** Set
  $`A := \mathrm{Rep.of}\ (\rho_{\mathrm{bin}} \circ \Gamma_0)`$ (the
  `Γ₀.subtype` composite) and use `cocycles₁ A` / `coboundaries₁ A` / `H1 A` / `H1π A` in place of
  `coeffCocycles` / `coeffCoboundaries` / `coeffH1` / `coeffH1Mk`. Gains: the
  ~13 cohomology declarations (the `Cocycles` section and the `H1` section,
  ~83 lines) and the trivial-coefficient bridge come free from mathlib, and no
  new library dependency is added because the Galois side already imports
  `Mathlib.RepresentationTheory.Homological.GroupCohomology`. Costs: a `Rep.of`
  bridge; a Hecke-action transport across `H1Iso`; and statement churn in the
  eight E-S-free algebra nodes (2,281 lines of the 21-node cone) whose statements
  are written over `coeffH1`/`coeffCocycles`. The Hecke action and the parabolic
  quotient are pin-specific under either option.

A middle path is available and is probably right: port option (a) as the core,
and add a **separate compatibility module** proving `coeffCocycles ρ =
cocycles₁ (Rep.of ρ)`, `coeffCoboundaries ρ = coboundaries₁ (Rep.of ρ)` and
`coeffH1 ρ ≃ₗ H1 (Rep.of ρ)`. That gives the relaxed core its self-contained
proofs, lets the trivial-coefficient interfaces use mathlib's `H1IsoOfIsTrivial`
directly, and keeps the door open to replacing the carrier later without
touching the algebraic nodes' statements.

Two further scoping notes, both measured from the pin:

- `Def_HeckeEis_EichlerIntegral` also defines `eichlerShimuraMap` (lines
  112–143, ~32 lines) and `Def_Gamma0CoeffCohomology` the whole `Parabolic`
  section (`IsParabolicCocycle`, `coeffParabolicCocycles`, `coeffH1par`,
  `coeffH1parMk`, `coeffH1parToH1`, lines 67–122, ~56 lines). None of the 12
  cites these; they are the dropped packaging's vocabulary. They are omitted from
  the core port (but the `Parabolic` section has no mathlib counterpart, so it is
  new work if the packaging is ever restored).
- `Def_HeckeEis_BinaryFormRep`'s `Eval` section (`evalRow`, `binaryFormEval`,
  lines 93–138, ~46 lines) is *not* used by the 12, but *is* used by retained
  endgame nodes (e.g. `CuspForm.heckeLocal.*`, interface 5) via
  `attribute [-simp] HeckeEis.binaryFormEval_mk`. It must stay.

## 6. Redundancy inside the twelve

### 6.1 Byte-identical duplicate blocks: 191 avoidable lines

Using `difflib` on the twelve `S_` bodies with a `>= 8`-line block filter, and
attributing a repeated block to the later file (keep one copy):

| later file | avoidable lines | duplicated from |
|---|---:|---|
| `IsEichlerIntegral.exists_sub_eq_const` | 132 | `IsEichlerIntegral.slash` |
| `IsEichlerIntegral.isBoundedAtImInfty_eval` | 32 | `IsEichlerIntegral.eq_zero_of_eval_eq_const` |
| `IsEichlerIntegral.binarySubst_adjugate_comp_smul` | 17 | `exists_isEichlerIntegral`, `slash` |
| `IsEichlerIntegral.slash` | 10 | `exists_isEichlerIntegral` |
| **total** | **191** | |

The largest block is exact: `slash` lines 14–145 and `exists_sub_eq_const`
lines 14–145 are the **same 132 lines** — the whole `EichlerIntegralAux`
namespace (`degExps`, `mem_degExps_iff`, `eq_sum_degExps`,
`coeff_binaryFormRepSL_eq_sum`, `apply_eq_apply_of_hasDerivAt_zero`,
`hasDerivAt_smul_ofComplex`, `hasDerivAt_comp_smul`,
`hasDerivAt_coeff_binaryFormRepSL`). The `zero`/`bdd` pair shares the 32-line
`LadderAux.rung` block. There are further `< 8`-line echoes
(`degExps`/`mem_degExps_iff` text appears in four files); the 191 is a lower
bound on the deduplication saving.

**Consequence for the budget:** the 2,301-line figure overstates the unique
proof content by 8.3%. A port that factors these helpers once writes **~2,110
analytic/proof lines**, not 2,301, and the playbook's "diff before porting a
second similar lemma" rule applies immediately to the `slash`/`exists_sub_eq_const`
pair.

### 6.2 Shared dependencies are not redundancy

`hasDerivAt_eval_iterate_pderiv` is used by two members and `slash` by two; that
is sharing, not duplicate content, and both must be ported once. The genuinely
redundant mass is the 191 lines above.

### 6.3 The node-count itself

Seven sources + five internal nodes means the port order is not the listing
order. A faithful top-down port of the target lemma would meet the four direct
cites (#1, #2, #11, #12) first and only then discover the other eight; a
bottom-up port writes the seven sources first. The latter is the order in §8.

## 7. Who actually needs the 12 under the relaxed route

The relaxed removed set `R` is the 33 `coeffH1par`/`eichlerShimuraMap` nodes.
After that pruning, the retained nodes that *directly* cite any of the 12 are:

- the 12 themselves (intra-12 edges);
- `HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul` (523 lines) —
  interface 3's target lemma, kept;
- `ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen` (932 lines)
  — the intrinsic mod-p core, kept.

Every *other* direct consumer of the 12 in the pin is a packaging node that the
relaxed route drops — ten of them, all in the relaxed pruned set:
`eichlerShimuraMap_eq_coeffH1parMk`, `eichlerShimuraMap_injective`,
`eichlerShimuraMap_heckeTLin`, `eichlerShimuraMap_heckeULin`,
`exists_isEichlerIntegral_isParabolicCocycle`,
`isParabolicCocycle_cocycle_of_isEichlerIntegral`,
`exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles`,
`exists_modularForm_heckeTLin_eq_smul_of_notMem_range_coeffH1parToH1`,
`IsEichlerIntegral.coeff_binaryFormRepSL_inv_apply_eq_intervalIntegral_slash`,
and `range_eichlerShimuraMap_inf_range_conj_eq_bot`. So under relaxed the 12 are
load-bearing for exactly **two retained entry points** (plus the retained tail
above them), which is the smallest consumer surface the core can have.

This is the porting consequence of §4.5: the analytic core cannot be dropped,
but the number of *places that must agree with its interface* collapses to two.

## 8. Porting effort

### 8.1 Line accounting

| layer | nodes/modules | lines | note |
|---|---:|---:|---|
| theorem layer, the 12 (`S_` proofs) | 12 | 2,301 | 191 lines are duplicates → ~2,110 unique |
| theorem layer, the 12 (`Thm_` statements) | 12 | 218 | public wrappers; the port states directly, so these mostly fold into the proofs |
| external theorem nodes (`S_` proofs) | 3 | 365 | 150 shared with route-A geometry; 215 private |
| external theorem nodes (`Thm_` statements) | 3 | 32 | |
| definition layer (transitive `Def_` closure) | 9 | 1,449 | 7 modules / 1,174 lines are the 12's actual need; the other 2 modules / 275 (projective line) are shared with retained `binaryFormEval`; 316 lines already ported |
| **nominal total** | | **4,365** | **~4,174 after the 191-line dedup** |
| `P2M/Util.lean` (all twelve import it) | 1 | 127 | shared macros (`p2m_exact_reverting` etc.); a mathlib-style port states the theorem directly and drops it |

The **marginal** core (content that exists only for this core) is the 12
theorems + the two private external lemmas = 2,301 + 218 + 40 + 175 + 32 = 2,766
nominal lines; the star-convex node (150), the defs (1,449 nominal, 1,174
actually needed by the 12) and `Util` (127) are shared with the rest of the port
or with route-A geometry.

### 8.2 Port order (bottom-up, dependencies satisfied)

1. `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` (305) — needs the
   `MvPolynomial` iterated-`pderiv` lemma (external, write first).
2. `IsEichlerIntegral.slash` (191) — needs the star-convex antiderivative only
   indirectly (via the shared `hasDerivAt_comp_smul` block).
3. `IsEichlerIntegral.binarySubst_adjugate_comp_smul` (184).
4. `IsEichlerIntegral.exists_sub_eq_const` (172) — reuse `slash`'s
   `EichlerIntegralAux` block, do **not** copy it.
5. `exists_isEichlerIntegral` (102) — the star-convex node (external) supplies
   the antiderivative.
6. `jFactor_pow_mul_eval_binaryFormRepSL` (74).
7. `IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` (44).
8. `coeffH1Mk_cocycle_heckeTLin_modularForm` (633) — needs 3, 4, 7 and the
   `Gamma0HeckeOperatorHom` / `Gamma0CoeffCohomologyEigen` defs.
9. `IsEichlerIntegral.isBoundedAtImInfty_eval` (178) — needs 1, 6 and the
   `UpperHalfPlane…of_periodic` lemma (external).
10. `IsEichlerIntegral.eq_zero_of_eval_eq_const` (92) — needs 1.
11. `isEquivariantPrimitiveWith_of_isEichlerIntegral` (46) — needs 2, 4.
12. `modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` (280) — needs 2, 9, 10.

The external `Complex…starConvex` (150) is needed at step 5,
`MvPolynomial…iterate_pderiv` (40) at step 1, and
`UpperHalfPlane…of_periodic` (175) at step 9.

### 8.3 Difficulty, by node (source-read, not build-tested)

| node | lines | character | risk |
|---|---:|---|---|
| `coeffH1Mk_cocycle_heckeTLin_modularForm` | 633 | double-coset Hecke correspondence: `alphaMat`/`betaGL`/`transferAux`, Bézout and coset transversals, slash bookkeeping, one analytic input (`isEichlerIntegral_heckeTransform`) | **highest**; long but elementary; the risk is bookkeeping volume, not mathlib gaps |
| `hasDerivAt_eval_iterate_pderiv` | 305 | `descFactorial`/`choose`/alternating-sum identities, `eval_one_eq_sum`, derivative of a finite sum | high; the pin uses `Int.alternating_sum_range_choose`; expect `Nat.descFactorial_*` name drift |
| `modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` | 280 | builds a weight-`(–n)` `ModularForm` `perForm`, cusp/periodicity, `eq_const_of_weight_zero` / `isZero_of_neg_weight` | high; the shape risk is the `ModularForm` structure fields at negative weight |
| `IsEichlerIntegral.slash` | 191 | chain rule under the slash action, `hasStrictDerivAt_smul`, `denom`/`zpow` bookkeeping | medium-high |
| `binarySubst_adjugate_comp_smul` | 184 | adjugate identities + chain rule with determinant | medium-high |
| `isBoundedAtImInfty_eval` | 178 | ladder induction (`rung`), periodicity, Liouville | medium; depends on the 175-line external fact |
| `exists_sub_eq_const` | 172 | differ-by-constant via `is_const_of_fderiv_eq_zero`; ~132 lines are the shared block | low-medium once the block is factored |
| `exists_isEichlerIntegral` | 102 | radial path integral; thin wrapper over the external star-convex node | medium |
| `eq_zero_of_eval_eq_const` | 92 | ladder induction | medium |
| `jFactor_pow_mul_eval_binaryFormRepSL` | 74 | matrix `linear_combination` | low |
| `isEquivariantPrimitiveWith_of_isEichlerIntegral` | 46 | algebra | low |
| `cocycle_sub_cocycle_mem_coeffCoboundaries` | 44 | algebra | low |

The playbook's calibration applies: **expense is the route's distance from
mathlib, and here that distance is the three external lemmas** (365 lines) and
the API archaeology beneath them — not the 2,301-line
theorem body, which is mostly algebra and bookkeeping against mathlib's existing
`MvPolynomial`, `UpperHalfPlane`, `ModularForm`, `GL(2,ℝ)` and
`intervalIntegral` APIs. Adopting mathlib's types as the port interface from the
first declaration (playbook §3.8) is what keeps the 633-line correspondence node
from growing.

## 9. Stop conditions and open questions

- **Stop if route B is meant to replace the 12.** The relaxed option explicitly
  keeps both; treating route B as a substitute is the *strict* variant, where
  the cost is the form-side `[2, p+1] → 2` descent of scout §4.5, not this core.
- **Stop if a candidate must build a genuine $`H^1(\Gamma_0, \mathrm{Sym}^n)`$**
  (Kuga–Sato, de Rham comparison). This core needs only degree-1 group
  cohomology on `coeffCocycles`/`coeffCoboundaries`, and only two of the 12 ever
  mention the quotient. That is the carrier constraint of the rewiring topic §3.
- **Open:** whether the 191-line dedup should be a single `EichlerIntegralAux`
  module in the port (playbook "one theory per directory" suggests a
  `ModularForms/EichlerIntegral/` directory with `Aux.lean` + one module per
  node). Not decided here.
- **Open:** whether `Complex.exists_hasDerivAt_of_starConvex` should be ported as
  part of this core or as part of the route-A geometry layer, since two
  `AlgebraicCurve.CellDissection` nodes also consume it. Either way the port
  must carry it; only the accounting differs.

## 10. Reproduction

The figures come from the FLT docs-site graph plus the pin's source, via the
local (untracked) `tools/deps` helpers `fltdata.py` / `prune.py`; the same
convention as the scout §7. The dedup measurement reads only the public pin
source. All commands assume the pin checkout at `~/proj/fermats-last-theorem`
(`aa2d8b3`).

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from fltdata import FltData
from prune import ANALYTIC_12, FltPayoff, TARGET_LEMMA
d = FltData(); pay = FltPayoff(data=d)
A12 = set(ANALYTIC_12)

# 1. per-node actual direct theorem deps (cu > 0) and def-module use
for n in ANALYTIC_12:
    i, sh = d.index[n], d.shards[n]
    direct = [(d.qual(j), sh['cu'][k]) for k, j in enumerate(d.cites(i))]
    sd = sorted({d.defs[x] for x in sh.get('sd') or []})
    print(f"{pay.lines(i):>4}  {n}\n      {direct}\n      sd={sd}")

# 2. actual theorem closure of the 12 (all edges have cu > 0)
cl = set()
for n in ANALYTIC_12:
    cl |= pay.closure(d.index[n])
print('closure:', len(cl), 'nodes /', pay.total_lines(cl), 'S_ lines')
print('non-12:', sorted(d.qual(i) for i in cl if d.qual(i) not in A12))

# 3. which of the 12 the target lemma cites directly
t, shT = d.index[TARGET_LEMMA], d.shards[TARGET_LEMMA]
print('target direct:', [(d.qual(j), shT['cu'][k]) for k, j in enumerate(d.cites(t))
                         if d.qual(j) in A12])
PY
```

```bash
# 4. duplicated blocks inside the twelve (public pin source only)
cd ~/proj/fermats-last-theorem/P2M/Sol && python3 - <<'PY'
import difflib
names = ['exists_isEichlerIntegral','isEquivariantPrimitiveWith_of_isEichlerIntegral',
 'IsEichlerIntegral_slash','IsEichlerIntegral_exists_sub_eq_const',
 'IsEichlerIntegral_eq_zero_of_eval_eq_const','IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv',
 'IsEichlerIntegral_isBoundedAtImInfty_eval','IsEichlerIntegral_binarySubst_adjugate_comp_smul',
 'IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries',
 'jFactor_pow_mul_eval_binaryFormRepSL','coeffH1Mk_cocycle_heckeTLin_modularForm',
 'modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero']
F = {n: open(f'S_HeckeEis_{n}.lean').read().splitlines() for n in names}
avoid = {n: set() for n in names}
for i, n in enumerate(names):
    for prev in names[:i]:
        sm = difflib.SequenceMatcher(None, F[prev], F[n], autojunk=False)
        for b in sm.get_matching_blocks():
            if b.size >= 8:
                avoid[n].update(range(b.b, b.b + b.size))
for n in names:
    if avoid[n]: print(f"{len(avoid[n]):>4}  {n}")
print('avoidable total:', sum(len(v) for v in avoid.values()))
PY
```

```bash
# 5. the definition trace: the nine modules, and the mathlib-cohomology seam
cd ~/proj/fermats-last-theorem && python3 - <<'PY'
from pathlib import Path
mods = ['Gamma0HeckeOperatorHom','ModularForm_HeckeOperator','ProjectiveLineMatrixAction',
        'Gamma0CoeffCohomology','HeckeEis_EichlerIntegral','HeckeEis_BinaryFormRep',
        'Gamma0CoeffCohomologyEigen','ModularForm_HeckeOperatorForms','ModularCurve_ProjectiveLine']
print('total', sum(sum(1 for _ in open(Path('Definitions') / f'Def_{m}.lean')) for m in mods), 'lines')
for pat in ['groupCohomology', 'cocycles\u2081', 'coboundaries\u2081', 'H1\u03c0', 'Rep.of',
            'inhomogeneousCochains']:
    on = sum(pat in (Path('Definitions') / f'Def_{m}.lean').read_text(errors="replace")
             for m in mods)
    print(f'{pat:>22}  on the nine def modules: {on}/9')
print('Def_GroupCohomology_* modules:',
      len(list(Path('Definitions').glob('Def_GroupCohomology_*.lean'))))
PY
```

## Appendix — the twelve, in the order they were identified

Scout §2.3 order, with the actual `S_` path in the pin
(`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_<stem>.lean`):

1. `HeckeEis.exists_isEichlerIntegral` — 102
2. `HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral` — 46
3. `HeckeEis.IsEichlerIntegral.slash` — 191
4. `HeckeEis.IsEichlerIntegral.exists_sub_eq_const` — 172
5. `HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const` — 92
6. `HeckeEis.IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` — 305
7. `HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval` — 178
8. `HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul` — 184
9. `HeckeEis.IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` — 44
10. `HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL` — 74
11. `HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm` — 633
12. `HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` — 280
