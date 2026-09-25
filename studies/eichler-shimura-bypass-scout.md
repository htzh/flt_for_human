# The Eichler–Shimura bypass — scout

**Status (2026-09-25).** A living results document: measurements and findings
accumulate here as the study progresses. The operational plan and its phase gates
live in
[../lean/topics/eichlerShimuraBypass/TOPIC-interface-3-rewiring.md](../lean/topics/eichlerShimuraBypass/TOPIC-interface-3-rewiring.md);
this note records what is true about the pin. Everything below is measured
against the FLT pin `aa2d8b3` with `tools/deps` (docs-site graph closure) plus
source greps of the pin's `S_`/`Thm_` files. The port's mathlib is `v4.34.0`.
Companion provenance: [flt-non-frey-segments.md](flt-non-frey-segments.md)
§8–§8.1, [route-c-prime-scout.md](route-c-prime-scout.md) §4 addendum,
[../math/015-weight-two-hecke-periods.md](../math/015-weight-two-hecke-periods.md),
and [../math/016-mod-p-weight-filtration.md](../math/016-mod-p-weight-filtration.md)
(the mathematics of the gap in §4.5).

**Established.**

1. The contract and the carrier constraint (§1).
2. Interface 3's analytic-Eichler–Shimura footprint is 12 nodes / 2,301 lines,
   all reachable only through the target lemma (§2).
3. The degree-0 contract is reachable E-S-free by composing route B's weight-2
   period (`ModularCurve.Period.exists_parabolicRealization`) with the CohCarrier
   bridge (`CohCarrier.isEigensystemH1_one_of_heckeT_eq_smul`) (§3).
4. The Katz/mod-p weight reduction is E-S-free **modulo C′** except for one
   intrinsic core, and a weight-$`(p+1)`$ → 2 descent already exists (§4).

**Open.** A form-side $`[2, p+1] \to 2`$ descent, or a weight reduction landing at
$`p+1`$ (§4.5). This is the one brick between the degree-0 composition and
interface 3 at weight $`k \ge 3`$, and it gates the higher-weight interfaces and
the full ten-interface payout (§6).

**Thesis.** Strip the interface bookkeeping away and the question is: do Route C′
(integrality of the Hecke algebra, all weights) and the $`k = 2`$ period map
(Route B) supply all the analytic-Eichler–Shimura content the Wiles–Taylor
endgame consumes? The endgame takes analytic E-S through exactly **two doors**:
Hecke-algebra finiteness/integrality, and the mod-$`p`$ Hecke eigenvector /
Galois attachment. C′ covers the first; Route B plus the geometric E-S congruence
and $`S_2 \cong \Omega^1`$ (both already in the pin) covers the second. "All
analytic content" means all *period-map* content, not all complex analysis: the
$`\mathbb{H}`$ / q-expansion layer that C′ itself rests on stays, and so does
the residual `JZero`/Riemann–Roch geometry (§6). The open condition is the
form-side weight reduction for the higher-weight interfaces.

**All-weight integrality is still needed.** The two doors are not
interchangeable. Interfaces 4, 5 and 6 consume
`CuspForm.hasIntegralStructure_of_two_le` (all weights $`\ge 2`$) directly, and
13 endgame nodes cite it — Katz weight-raising
(`WeierstrassCurve.exists_ideal_heckeAlgebra_two_or_succ_…_of_katz_…`,
`…_three_weight_le_four_…`, `…_weight_le_succ_…`), level-raising ideals, and the
`CuspForm.heckeLocal.*` patching datums. Its downstream
`CuspForm.moduleFinite_heckeAlgebra` (all weights) is consumed by six more
endgame nodes, including interface 3's own consumer
`GaloisRep.exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal`.
Separately, interfaces 1, 2, 3 and 8 consume the **$`k = 2`$** finiteness
`CuspForm.moduleFinite_heckeAlgebra_two` (Route B). So the endgame needs both:
all-weight integrality (door 1, supplied by C′) and the $`k = 2`$ period (door
2, supplied by Route B). The $`k = 2`$ finiteness does not replace C′.

## 1. The contract and the carrier constraint

### 1.1 The types

The exact types the replacement must produce or be compatible with. All are in
the pin; the citation is by file and line.

| name | file | shape |
|---|---|---|
| `HeckeEis.coeffCocycles` | `Definitions/Def_Gamma0CoeffCohomology.lean:13` | `Submodule K (G → V)`, carrier $`z`$ with $`z(gh) = z(g) + \rho(g) z(h)`$ |
| `HeckeEis.coeffH1` | `Definitions/Def_Gamma0CoeffCohomologyEigen.lean:16` | `↥(coeffCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype` |
| `HeckeEis.IsCoeffHeckeOnH1` | `Definitions/Def_Gamma0CoeffCohomologyEigen.lean:61` | `∀ z, ∃ w, w = coeffHeckeFun N ℓ ρ a z ∧ T (coeffH1Mk ρ z) = coeffH1Mk ρ w` |
| `HeckeEis.IsEigensystemH1` | `Definitions/Def_Gamma0CoeffCohomologyEigen.lean:72` | `∃ x ≠ 0, ∀ ℓ prime, ℓ ∤ N → ℓ ∉ S₀ → ∃ T, IsCoeffHeckeOnH1 N ℓ ρ (a ℓ) T ∧ T x = lam ℓ • x` |
| `HeckeEis.binaryFormRepSL` | `Definitions/Def_HeckeEis_BinaryFormRep.lean:61` | `Representation K SL(2, ℤ) (BinaryForm K n)`, `g ↦ binarySubst K ↑g` |
| `HeckeEis.binaryFormAlphaAdj` | `Definitions/Def_HeckeEis_BinaryFormRep.lean:82` | `BinaryForm K n →ₗ[K] BinaryForm K n`, `binarySubst K !![ℓ,0;0,1]` |
| `HeckeEis.IsEichlerIntegral` | `Definitions/Def_HeckeEis_EichlerIntegral.lean:105` | `∀ d τ, HasDerivAt (coeff d ∘ F ∘ ofComplex) (f τ * coeff d (linePow n τ)) τ` |
| `HeckeEis.IsEquivariantPrimitiveWith` | `Definitions/Def_HeckeEis_EichlerIntegral.lean:68` | `∀ γ, ∃ c, ∀ τ, F (γ • τ) - ρ γ (F τ) = c` |

Two rows are the seam. `coeffH1` is the *only* quotient in the contract — the sole
cohomology argument anywhere in this study — while `IsEichlerIntegral` /
`IsEquivariantPrimitiveWith` are the analytic carrier. Route B's blob has that
same primitive with no quotient at all: `coeffCoboundaries ρ` is the range of
$`v \mapsto (\rho g v - v)_g`$ (`Definitions/Def_Gamma0CoeffCohomology.lean`), so
at trivial coefficients `coeffCoboundaries 1 = ⊥` and `coeffH1 1` is already
route B's `addChars κ Γ₀ κ`.

### 1.2 The carrier constraint (route B's tame type)

Route B's blob never formalizes cohomology, and a replacement must not either. Its
period side is `addChars R G M` — literally the submodule of additive characters
$`G \to M`$ cut out by $`\varphi(\gamma\delta) = \varphi\gamma + \varphi\delta`$
([`S_CuspForm_moduleFinite_heckeAlgebra_two.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean#L1695-L1697)
L1695; see [../math/015-weight-two-hecke-periods.md](../math/015-weight-two-hecke-periods.md)
§3). At trivial coefficients every 1-coboundary vanishes
($`g \cdot m - m = 0`$), so `addChars` is just `Hom(G, M)`: no quotient, no
$`H^1`$, no resolution. Interface 3's analytic step instead lands in
`HeckeEis.coeffH1 = coeffCocycles ⧸ coeffCoboundaries` on `Sym^n` — a genuine
cohomology quotient, and the only one in the contract.

The rule that follows: **produce the $`n = 0`$ eigensystem on route B's tame
carrier** (`addChars κ Γ₀ κ`, or the `IsEquivariantPrimitive`/`period` primitive
that generates it) **and reach `coeffH1 1` only through the thin bridge where
`coeffCoboundaries 1 = ⊥`**; obtain $`n > 0`$ by a *form-side* weight reduction,
never by building $`H^1(\Gamma_0, \mathrm{Sym}^n)`$ (Kuga–Sato, de Rham
comparison, `coeffH1`-carrier identifications). This is what makes the geometric
candidates of §3.3 suspect and route B / CohCarrier leading.

### 1.3 The target

The target lemma's conclusion (the contract the replacement must match) is

```lean
HeckeEis.IsEigensystemH1 N
  ((HeckeEis.binaryFormRepSL κ n).comp (CongruenceSubgroup.Gamma0 N).subtype)
  (fun ℓ => HeckeEis.binaryFormAlphaAdj κ n ℓ) S (fun ℓ => φ (a ℓ))
```

i.e. a nonzero Hecke eigenvector in `coeffH1` of the **binary-form coefficient
system** `Sym^n`, with Hecke action `binaryFormAlphaAdj` — precisely the shape
`HeckeEis.IsEigensystemH1` quantifies over. Note this is a *carrier* statement:
nothing in the conclusion names the Eichler integral, the period map, or `ℂ`.

## 2. What interface 3 consumes

### 2.1 The 36-node partition

Interface 3's cone is 1,390 nodes, 36 of them `HeckeEis.`, together 13,293 raw
`S_` lines. Of those 36, only 21 lie in the target lemma's cone (its cone is 25
nodes total; the 4 non-`HeckeEis.` members are
`Complex.exists_hasDerivAt_of_starConvex`,
`Module.exists_ne_zero_forall_baseChange_eq_smul_of_algHom`,
`MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt`,
`UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic`).

Split by whether a node is reachable from interface 3 *without* passing through
the target lemma (a graph fact, not a statement about analyticity):

| class | `HeckeEis.` nodes | lines | note |
|---|---:|---:|---|
| reachable **only through** the lemma | 14 | 3,082 | 12 analytic + 2 E-S-free algebra (§2.2) |
| reachable **without** the lemma ("tail") | 22 | 10,211 | 7 also in the lemma's cone, 15 not |
| total | 36 | 13,293 | |

The 15 tail-only nodes carry 8,188 lines and are the weight-reduction /
level-raising machinery of the tail:
`exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL`,
`exists_isEigensystemH1_gamma0NebenRep_of_…`,
`exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep`,
`exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom`,
`isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1`,
`isEigensystemH1_one_natCast_add_one`, `…_natCast_mul_…`,
`exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd`,
`isEigensystemH1_of_isEigensystemH1_of_surjective`,
`isEigensystemH1_or_of_isEigensystemH1_of_injective`, the
`existsUnique_coeffCocycles_sl2z_apply_S_ST_eq` /
`exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq` pair, and
the three small transfer/`postcomp` bookkeeping lemmas. The per-node line counts
are in the Appendix.

### 2.2 The 14 "only through the lemma" nodes

Twelve are analytic (9 analytic + 3 E-S packaging, §2.3). The other two are
E-S-free *algebra* that happens to be consumed only via the lemma inside
interface 3 and must be counted in any replacement budget:

| node | lines | role |
|---|---:|---|
| `HeckeEis.span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top` | 423 | integral cocycles $`\mathbb{C}`$-span `coeffCocycles` |
| `HeckeEis.exists_injective_baseChange_coeffH1_binaryFormRepSL` | 358 | injectivity of $`F \otimes_{\mathbb{Z}} \mathrm{coeffH1}_{\mathbb{Z}} \to \mathrm{coeffH1}_F`$ at $`\mathrm{char}\,F = p`$ |

Neither is analytic, and both are general cohomology-algebra facts a replacement
would reuse unchanged. The honest label for this class is "graph-reachable only
through the lemma", not "analytic". A replacement that keeps the carrier but
swaps the analytic step still needs them (or an equivalent), so the marginal
saving is the analytic set, not all 14.

### 2.3 The 21-node cone and the analytic fact table

Category key: **A** = genuine complex analysis (derivatives, antiderivatives,
boundedness/growth, periodicity); **ES** = E-S period-class packaging (no
analysis itself, but specific to the Eichler integral); **alg** = E-S-free
cohomology algebra.

| node (`HeckeEis.`) | lines | cat | fact used / role |
|---|---:|---|---|
| `exists_isEichlerIntegral` | 102 | A | **the one existence input**: holomorphic $`f`$ on $`\mathbb{H}`$ has $`F`$ with $`\partial_d F = f\cdot \mathrm{coeff}_d(\mathrm{linePow})`$; proof = star-convex antiderivative (`Complex.exists_hasDerivAt_of_starConvex`) |
| `IsEichlerIntegral.slash` | 191 | A | EI transported by $`\delta`$: $`f \mid_k \delta`$ has EI $`\rho(\delta^{-1}) F(\delta\,\cdot)`$ |
| `IsEichlerIntegral.exists_sub_eq_const` | 172 | A | two EI of the same $`f`$ differ by a constant binary form |
| `IsEichlerIntegral.eq_zero_of_eval_eq_const` | 92 | A | ladder/$`\partial_1`$ argument: EI with constant $`\mathrm{eval}[(1,-\tau)]`$ forces $`g=0`$ |
| `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` | 305 | A | iterated $`\partial_1`$ derivative identity for the eval of an EI |
| `IsEichlerIntegral.isBoundedAtImInfty_eval` | 178 | A | growth at the cusp from boundedness + periodicity of $`f`$ (`UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic`) |
| `IsEichlerIntegral.binarySubst_adjugate_comp_smul` | 184 | A | EI transported along the Hecke correspondence $`\alpha_\ell^{\mathrm{adj}}`$ |
| `coeffH1Mk_cocycle_heckeTLin_modularForm` | 633 | A | **Hecke equivariance of the period class**: $`T_\ell`$ on the EI cocycle of $`f`$ = EI cocycle of $`T_\ell f`$ |
| `modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` | 280 | A | **period injectivity / nonvanishing**: the EI class of $`f`$ is 0 only if $`f=0`$ |
| `isEquivariantPrimitiveWith_of_isEichlerIntegral` | 46 | ES | **the E-S construction step**: EI + slash-invariance $`\Rightarrow`$ equivariant primitive, hence a `coeffCocycles` class |
| `IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` | 44 | ES | primitives differing by a constant $`\Rightarrow`$ cocycles differ by a coboundary (identifies EI class with the period class) |
| `jFactor_pow_mul_eval_binaryFormRepSL` | 74 | ES | automorphy-factor identity $`j^n \cdot \mathrm{eval}(\rho(g) P) = \mathrm{eval}(P)`$; pure matrix algebra, feeds the slash transport |
| `coeffHeckeFun_mem_coeffCocycles` | 158 | alg | `coeffHeckeFun` preserves cocycles |
| `coeffHeckeFun_mem_coeffCoboundaries` | 158 | alg | `coeffHeckeFun` preserves coboundaries |
| `coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries` | 534 | alg | commutator of two Hecke operators is a coboundary (double-coset algebra) |
| `sum_repr_sub_coeffHeckeFun_mem_coeffCoboundaries` | 166 | alg | coset-sum form of the same |
| `binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj` | 44 | alg | Hecke-compatibility of $`\alpha_\ell`$ (`IsCompat` hypothesis) |
| `exists_coeffH1_map_ringHom_binaryFormRepSL` | 440 | alg | coefficient base change $`R \to R'`$ on `coeffH1`, compatible with `TH` |
| `exists_injective_baseChange_coeffH1_binaryFormRepSL` | 358 | alg | injectivity of $`F \otimes_{\mathbb{Z}} \mathrm{coeffH1}_{\mathbb{Z}} \to \mathrm{coeffH1}_F`$ |
| `span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top` | 423 | alg | integral cocycles $`\mathbb{C}`$-span `coeffCocycles` |
| `isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul` | 523 | — | the lemma itself: E-S-free bookkeeping + one analytic construction |

Category totals inside the 21: **A** 9 nodes / 2,137 lines, **ES** 3 nodes /
164 lines, **alg** 8 nodes / 2,281 lines, lemma 523 lines; total 5,105.

The **analytic** set proper is therefore
`{exists_isEichlerIntegral, IsEichlerIntegral.* (6), isEquivariantPrimitiveWith_of_isEichlerIntegral, IsEquivariantPrimitiveWith.cocycle_sub…, jFactor_pow_mul_eval_binaryFormRepSL, coeffH1Mk_cocycle_heckeTLin_modularForm, modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero}`
— 12 nodes, 2,301 lines — all only reachable through the lemma.

**No tail node depends on it.** For each of the 22 tail-reachable nodes, its
closure intersects the analytic set only at the lemma itself, and no tail node
cites the lemma. So the analytic cone is a *leaf gadget*: interface 3 consumes it
solely through the one lemma.

### 2.4 Where the analysis sits in the 523-line lemma

| lines | section | content | E-S? |
|---|---|---|---|
| 31–108 | `Induced` | abstract Hecke operator `coeffHeckeFun` on `coeffH1`, uniqueness of `IsCoeffHeckeOnH1`, Hecke commutativity | no |
| 110–152 | `Sym` | specialisation to `binaryFormRepSL` / `binaryFormAlphaAdj`, `TH` | no |
| 154–203 | `FiniteGen` | `moduleFinite_coeffH1` via `Group.FG SL(2,ℤ)` | no |
| 205–244 | `Words` | free-algebra/eigenvector bookkeeping `ev`, `map_ev_apply`, `ev_apply_eigenvector` | no |
| 246–299 | `Coeff` | `IsCoeffMap` (coefficient base change), integral-span vanishing criterion | no |
| 301–331 | `Eichler` | only `isEichlerIntegral_smul`, `isEquivariantPrimitiveWith_smul`, `cocycle_smul` — trivial `•`-compatibilities | thin |
| 333–488 | `Main` | **`exists_eigenclass_of_eigenform` (the analytic core)**; `ev_eq_zero_of_eigenform`; `exists_algHom_adjoin`; `exists_eigenclass_of_baseChange` | core |
| 496–523 | `solution` | assembly: analytic eigenclass $`\to`$ $`\mathbb{Z}`$-integrality $`\to`$ mod-$`p`$ base change | mix |

The analytic call sites are lines 370–390 (`exists_eigenclass_of_eigenform`):
`exists_isEichlerIntegral` (370), `isEquivariantPrimitiveWith_of_isEichlerIntegral`
(378), `modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` (380),
`coeffH1Mk_cocycle_heckeTLin_modularForm` (385). Everything else in the file is
E-S-free. All four call-site facts build the period class and its two properties
(existence, nonvanishing, Hecke eigenvector); no analytic fact is needed for the
*carrier* or for the base-change/Hecke-bookkeeping half of the lemma.

### 2.5 Cross-checks against the topic

| topic claim | measured |
|---|---|
| lemma cone 25 nodes / 21 `HeckeEis` | 25 / 21 |
| interface 3 `HeckeEis` footprint 36 nodes | 36 |
| that footprint's raw `S_` lines 13,293 | 13,293 |
| lemma's only direct citer is interface 3 | yes (only citer) |
| interface 3's only citer is `…trace_eq_heckeT_mod_of_isMaximal` | yes (only citer) |
| the tail (weight reduction `n → 0`, `ModP` construction) is E-S-free | yes |
| route B blob `S_CuspForm_moduleFinite_heckeAlgebra_two.lean` = 4,308 lines | 4,308 |
| `Def_ModularCurve_PeriodMap.lean` has `IsEquivariantPrimitive`, `period`, `periodHom`, `parabolicHoms` | yes |
| route B ingredients present (`exists_equivariantPrimitive_gamma0`, `periodHom_injective`, `periodHom_hecke`, `span_range_ofIntChars`) | yes |
| all provenance files exist | yes |

## 3. The candidate constructions

Measured against the pin (`tools/deps` cones). "analytic" is the intersection with
the 12-node analytic set of §2.3. The question for each candidate is whether it
can produce the contract's eigensystem **without** the Eichler integral, and
whether its carrier matches `coeffH1` of the binary-form system.

| # | candidate | key declaration(s) | carrier produced | cone (nodes / lines) | `HeckeEis` | analytic | degree |
|---|---|---|---:|---:|---:|---|
| 0 | Route B / Period (leading) | `ModularCurve.Period.exists_parabolicRealization` | `ModularCurve.Period.parabolicHoms k Γ₀ k` | 31 / 7,166 | 0 | **0** | 0 |
| 1 | CohCarrier | `CohCarrier.isEigensystemH1_one_of_heckeT_eq_smul` | `CohCarrier.H1 N ⊤ k = Additive Γ₀ →+ k` | 3 / 307 | 1 | **0** | 0 |
| 2 | JZero / Frobenius | `CuspForm.IsNewform.exists_eigenPlane_tateModule_jZero` | Tate module of `JZero N` / regular differentials | 882–1,291 / 383k–551k | 0–1 | **0** | 0 |
| 3 | Katz / mod-p form side | `ModPForms.exists_weight_le_succ_…_of_isModPEigen_algebraicClosure` | Katz / mod-p forms of weight k | 43–1,311 / 8.9k–521k | 20–73 | **10–12** | all k |
| 4 | Abstract E-S data | `ModularCurve.EichlerShimuraData`; `FrobeniusQuadratic.of_specializationExists` | abstract datum / `FrobeniusQuadratic` | 1 / 28 | 0 | **0** | n/a |

**The headline: 0 and 1 compose, and the composition produces the exact degree-0
contract, E-S-free.** It is the only E-S-free route to the contract, and it is
weight-2 only.

### 3.1 Route B / Period (candidate 0)

`ModularCurve.Period.exists_parabolicRealization`:

```lean
(f : CuspForm (Γ₀ N) 2) (hf : f.IsNormalizedEigenform) (hint : f.PrimeCoeffsIntegral)
    (k : Type) [Field k] (red : integralClosure ℤ ℂ →+* k) :
  ∃ f₀ : parabolicHoms k (Γ₀ N) k, f₀ ≠ 0 ∧
    ∀ (ℓ) [NeZero ℓ] (hℓp : ℓ.Prime),
      heckeOperatorHom N ℓ k (f₀ : Additive (Γ₀ N) →+ k) =
        (red (eigenLift hint ⟨ℓ, hℓp⟩)) • (f₀ : Additive (Γ₀ N) →+ k)
```

Supporting lemmas, each E-S-free: `exists_equivariantPrimitive_gamma0` (1 / 289),
`periodHom_ne_zero_of_ne_zero` (3 / 503), `periodMap_heckeTLin` (4 / 1,307),
`periodHomPair_injective` (7 / 1,839), `periodHomPair_range_eq_parabolicHoms`
(range = `parabolicHoms ℂ Γ₀ ℂ`). Carrier: `parabolicHoms k Γ₀ k` is a submodule
of `Additive Γ₀ →+ k` — route B's tame `Hom` type with the parabolic condition.

**Carrier bridge (already in the pin, in a harder form).** At $`n = 0`$,
`binaryFormRepSL k 0` is the trivial representation on the constants, so
`coeffCocycles 1 = Additive Γ₀ →+ k`, `coeffCoboundaries 1 = ⊥`, and
`coeffH1 (1 : Representation k Γ₀ k) ≃ₗ[k] Additive Γ₀ →+ k`. The Hecke action
matches because `binaryFormAlphaAdj k 0 ℓ = id` and
`coeffHeckeFun N ℓ 1 id = heckeOperatorHom N ℓ k` on functions
(`Definitions/Def_Gamma0CoeffCohomology.lean:129` vs
`Definitions/Def_Gamma0HeckeOperatorHom.lean:285`). The pin already formalizes this
bridge for the **non-trivial** projective-line representation:
`HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms` gives
`coeffH1par (projLineRepSL p k) ≃ₗ[k] parabolicHoms k (Γ₀ (Np)) k`
(cone 10 / 2,945, 7 `HeckeEis`, **0 analytic**), and
`HeckeEis.coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom`
(5 / 1,121, 3 / 0) matches the Hecke actions. The $`n = 0`$ bridge is the
lower-dimensional analogue of that, but no `binaryFormRepSL 0` instance of it
exists yet.

### 3.2 CohCarrier (candidate 1) and the 0 ∘ 1 composition

`CohCarrier.H1 M H A := Additive ↥(Γ_H(M,H)) →+ A`
(`Definitions/Def_CohCarrier_Level.lean:162`) — again the tame `Hom` type, no
quotient, and `Γ_H(M, ⊤) = Γ₀(M)`. The decisive lemma is

```lean
theorem CohCarrier.isEigensystemH1_one_of_heckeT_eq_smul
    (N : ℕ) {K : Type} [Field K] (S₀ : Set ℕ) (lam : ℕ → K)
    (v : CohCarrier.H1 N ⊤ K) (hv : v ≠ 0)
    (heig : ∀ (ℓ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N ⊤ ℓ K v) = lam ℓ • v) :
    HeckeEis.IsEigensystemH1 N (1 : Representation K (Γ₀ N) K)
      (fun _ => LinearMap.id) S₀ lam
```

cone 3 / 307, 1 `HeckeEis` (`CohCarrier`→`HeckeEis.coresHom_eq_transfer`, a
transfer bookkeeping lemma), **0 analytic**. This is the *exact* trivial-coefficient
`IsEigensystemH1` that interface 3's weight reduction produces and its Galois step
consumes. The bridge to `HeckeEis.heckeOperatorHom` is
`CohCarrier.heckeT_top_apply_eq_heckeOperatorHom` (2 / 141, 1 / 0); the supporting
package is `exists_complex_heckeT_eigen_reduction_eq_of_mem_span_int`
(6 / 2,018, 0 / 0), `mem_span_int_of_forall_isOfFinOrder_apply_eq_zero`
(2 / 1,155, 0 / 0), and
`exists_ringHom_heckeAlgebra_apply_smul_eq_heckeT_of_mem_parabolicHoms`
(594 / 245,864, 2 / 0).

**The composition.** Route B's `exists_parabolicRealization` produces a nonzero
`f₀ ∈ parabolicHoms k Γ₀ k ⊂ CohCarrier.H1 N ⊤ k` with
`heckeOperatorHom N ℓ k f₀ = red(eigenLift hint ℓ) • f₀`; candidate 1 turns it
into the exact degree-0 `IsEigensystemH1` with eigenvalues
`lam ℓ = red (eigenLift hint ℓ)`. Both halves are in the pin, E-S-free, and the
carrier/Hecke-operator match is already formalized for the projLine analogue. So
**the degree-0 contract is E-S-free reachable today** — for a weight-2 input.

### 3.3 JZero / Frobenius (candidate 2)

`CuspForm.IsNewform.exists_eigenPlane_tateModule_jZero` (1,291 / 551,238, 1
`HeckeEis`, 0 analytic) builds an eigenplane in the Tate module of `JZero N`;
`ModularCurve.frobeniusQuadratic_JZero` (995 / 430,110, 1 / 0) and
`W54.jZeroPPowTorsion_frobeniusQuadratic` (1,035 / 433,950, 1 / 0) supply the
geometric E-S congruence; `exists_linearEquiv_tensor_intLattice_regularDifferentials_qExpansionDiffAlong_eq`
(882 / 382,850, 0 / 0) supplies $`k \otimes intLattice(N,2) \cong \mathrm{regularDifferentials}`$.
Carrier: Tate module / regular differentials — **not** `coeffH1`. All 31 nodes
concluding `IsEigensystemH1` are disjoint from the cones of the Frobenius
congruence nodes, and no glue theorem connects them. So this route is E-S-free
but its carrier is the wrong side of the de Rham comparison; using it would need
new comparison theory.

### 3.4 Katz / mod-p form side (candidate 3)

`KatzModularForm R k` (`Definitions/Def_ModularForm_KatzLevelOne.lean:10`) is the
mod-p/Katz modular-form type; every `KatzModularForm.*` node's cone is small and
0-analytic. But the general-weight reduction statements are not E-S-free:
`ModPForms.exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure`
reduces a weight-k mod-p eigenform to weight $`k'`$ with $`2 \le k' \le p+1`$
(cone 1,311 / 520,774, **10** analytic nodes in cone), and
`ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen` (43 / 8,855,
**12/12** analytic — it directly cites `exists_isEichlerIntegral`,
`isEquivariantPrimitiveWith_of_isEichlerIntegral`,
`coeffH1Mk_cocycle_heckeTLin_modularForm`,
`modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero`). Taken at face value this is
circular as a replacement. §4 shows the dependence is almost entirely C′-dissolved
and only the second of these is intrinsic.

### 3.5 Abstract E-S data (candidate 4)

`ModularCurve.EichlerShimuraData`
(`Definitions/Def_ModularCurve_EichlerShimuraData.lean:100`) has **zero consumers**
anywhere in the pin; `EichlerShimuraDataReduced`, `EichlerShimuraRelationOn` and
`FreyPackage.MazurEichlerShimuraFamily` are equally unused. The live clause is
`FrobeniusQuadratic` / `SpecialFibreRelation`, instantiated E-S-free on `JZero`
by `frobeniusQuadratic_JZero`, but its consumers live entirely in the
Tate-module / `heckeTorsion` / Mazur level-lowering branch (e.g.
`ModularCurve.exists_torsionEmbedding_of_congruences`, 122 / 0 / 0), which is
disjoint from every `IsEigensystemH1` node. The only consumer that turns the
analytic map into an eigensystem-like object,
`HeckeEis.existsEichlerShimuraMapLinear` (20 / 1,709, 17 `HeckeEis`, **5**
analytic), is itself the analytic period map. Verdict: the abstract datum cannot
be substituted for the analytic lemma, and no glue exists.

### 3.6 What the candidates leave

Route B and CohCarrier give the exact degree-0 contract, E-S-free, but only at
weight 2. The geometric route (JZero/Frobenius) is E-S-free but on the wrong
carrier. The Katz/mod-p route is the only general-weight one, and its analytic
dependence is the subject of §4.

## 4. The weight-reduction blocker

### 4.1 The first measurement

The general mod-p reduction
`ModPForms.exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure`
takes a mod-p weight-k eigenform to weight $`k'`$ with $`2 \le k' \le p+1`$,
eigenvalues twisted by $`\ell^j`$. As measured, its cone has 10 of the 12
analytic nodes, and the related weight-$`\le 4`$ reduction
(`ModPForms.exists_three_weight_le_four_…`) has 12. That looks like a circular
blocker.

### 4.2 The analytic dependence is C′-dissolved

Tracing the reduction to its minimal analytic entry points shows the count is
almost entirely an artefact of using **route A's proof of
`CuspForm.hasIntegralStructure_of_two_le`**, the statement C′ replaces. Treating
that statement as supplied by C′:

| node | cone | analytic now | analytic with C′ |
|---|---:|---:|---:|
| `ModPForms.nonempty_ssDatum_algebraicClosure` | 1,310 | 10 | **0** |
| `ModularCurve.SSHeckeV2.ssHeckeFun_window` | 1,280 | 10 | **0** |
| `ModPForms.dimFormulaCusp_le_finrank_modPCusp` | 663 | 10 | **0** |
| `ModPForms.exists_weight_le_succ_…` (k → k′ ≤ p+1) | 1,311 | 10 | **0** |
| interface 5 (`exists_isMaximal_two_ringHom_of_succ_…`) | 1,254 | 10 | **0** |
| interface 6 (`thetaCycle_exists_ringHom_mul_two_…`) | 1,208 | 10 | **0** |
| `ModPForms.exists_three_weight_le_four_…` (k → ≤ 4) | 791 | 12 | 12 |
| `ModPForms.exists_isEigensystemH1_…_of_isModPEigen` | 43 | 12 | 12 |
| `HeckeEis.exists_eichlerShimura_coeffH1par_…_forall_prime` | 645 | 10 | 10 |
| interface 1 (`…ideal_heckeAlgebra_mul_two_…`) | 662 | 10 | 10 |
| interface 3 (target) | 1,390 | 12 | 12 |
| interface 4 (`…three_weight_le_four_…`) | 885 | 12 | 12 |

The mod-p weight reduction is form-theoretic. `SSDatum`
(`Definitions/Def_ModPForms_SSDatum.lean`) is exactly the Katz weight filtration:
mod-p modules `S k`, Hecke operators `T k ℓ`, a residue map with
`res_ker : res φ = 0 → φ ∈ modPMod(k-(p-1))`, and weight periodicity
`bIso : S k ≃ S (k+(p+1))`. The `SSHeckeV2` construction (`resQFun`,
`ssHeckeFun`, `liftFun`, `Definitions/Def_ModularCurve_SSHeckeV2.lean`) is built
from `modularFunctionFieldC`, Kähler differentials and `weightDivisor` — no
periods. The single analytic entry is `dimFormulaCusp_le_finrank_modPCusp` citing
`hasIntegralStructure_of_two_le`. So the general reduction
`exists_weight_le_succ_…` is E-S-free modulo C′.

### 4.3 The intrinsic core

One core survives every substitution found so far.
`ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen` (43 nodes, all
12 analytic) directly cites `exists_isEichlerIntegral`,
`isEquivariantPrimitiveWith_of_isEichlerIntegral`,
`coeffH1Mk_cocycle_heckeTLin_modularForm` and
`modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero`: it *is* the
$`\mathrm{Sym}^{k-2}`$ Eichler–Shimura map from a mod-p weight-k eigenform to
the degree-$`(k-2)`$ eigensystem. Nothing C′ or route B supplies substitutes for
it, and it is the analytic content of interfaces 1, 3 and 4. Route A's
`HeckeEis.exists_eichlerShimura_coeffH1par_…_forall_prime` (645 / 10) is the
parallel `coeffH1par` map; C′ bypasses it as a statement rather than dissolving
it.

### 4.4 The weight-$`(p+1)`$ → 2 lever

A genuine descent to weight 2 already exists, and it is C′-dissolved. Interface 6
takes a Hecke character $`\theta : heckeAlgebra\ N\ (p+1)\ S \to F`$ and
produces $`\theta_2 : heckeAlgebra\ (Np)\ 2\ (S \cup \mathrm{bad}) \to F`$ with
matching $`T_\ell`$ (and $`U_p = \theta(T_p)`$): a descent from weight
$`p+1`$ to weight 2. Interface 5 is the maximal-ideal version
(weight-$`(p+1)`$ ideal → weight-2 ideal). Both are C′-dissolved. So the
"reach weight 2" step is available *at weight* $`p+1`$.

### 4.5 The remaining gap

The full mathematical account of this section, with the motivation and the routes
past it, is [../math/016-mod-p-weight-filtration.md](../math/016-mod-p-weight-filtration.md);
what follows is the summary.

**What it is mathematically.** The reduction of §4.1 produces an eigenform of
weight $`k'`$ with $`2 \le k' \le p+1`$ and $`(p-1) \mid (k - k')`$. Since
$`p-1`$ is even and nonzero classical forms have even weight
(`CuspForm.eq_zero_of_odd_gamma0`, `ModPForms.modPMod_eq_bot_of_odd`), the
canonical weights are $`\{2, 4, \dots, p-1, p+1\}`$. Weights differing by
$`p-1`$ have identical Hecke action — `heckePS k ℓ` multiplies the old part by
$`\ell^{k-1}`$, and $`\ell^{p-1} = 1`$ — so $`k' = p+1`$ is Hecke-equivalent to
$`k' = 2`$. That is exactly the existing $`p+1 \to 2`$ lever, which carries a
level–weight exchange with it
(`ModPForms.modPCusp_add_one_le_modPCusp_mul_two_…`: weight $`p+1`$ at level $`N`$
embeds in weight 2 at level $`Np`$). The interior even weights $`4 \le k' \le p-1`$
are **not** Hecke-equivalent to weight 2 — the actions differ by the nontrivial
character $`\ell^{k'-2}`$ — so the form itself must move through the mod-p weight
filtration. The devices are the Hasse invariant (weight $`p-1`$, a unit on the
ordinary locus) and the Serre derivative
($`12\,\theta\varphi - k E_2\varphi \in \mathrm{modPMod}(k+2)`$); for
$`2 \le k' \le p-1`$ the Hasse step is empty ($`k' - (p-1) \le 0`$), so the
filtration predicts a $`\theta`$-descent to weight 2, iterated. Formally that is a
*membership* statement —
$`\mathrm{modPMod}(k') \subseteq \theta^m(\mathrm{modPMod}(2))`$, or the descent
$`\varphi \in \mathrm{modPMod}(k') \Rightarrow \exists \psi \in \mathrm{modPMod}(k'-2),\ \theta\psi = \varphi`$
— with level bookkeeping.

**What the pin has, and what is absent.** The $`\theta`$/Hasse toolkit is present
and E-S-free: $`\theta = q\,d/dq`$ (`ModPForms.thetaPS`), its product rules
(`thetaPS_add_smul_mul_mem_modPMod_add_two`,
`smul_mul_thetaPS_sub_smul_thetaPS_mul_mem_modPMod_add_add_two`), the
Serre-derivative identity, the Hasse inclusion
(`modPMod_le_modPMod_add_sub_one`:
$`\mathrm{modPMod}(k) \subseteq \mathrm{modPMod}(k+(p-1))`$), the non-membership
criterion (`thetaPS_not_mem_modPMod_add_two_of_not_mem_sub_of_not_dvd`), a
conditional drop by $`p-1`$ (`mem_modPMod_sub_of_qP_mul_mem`), and two descents to
weight 2: weight $`p+1`$ when the $`p`$-multiples of the q-expansion vanish
(`mem_modPMod_two_of_mem_modPMod_of_forall_coeff_mul_eq_zero`, which is what feeds
interface 6) and the char-3 weight-4 case
(`mem_modPMod_two_of_mem_modPMod_four_of_…`). What is **absent** is the general
interior descent: no node anywhere in the pin takes $`3 \le k' \le p-1`$ to
weight 2.

**Does the slice supply it? No.** Measured over the E-S-ish namespaces, the slice
is 213 nodes, but only **43** are analytic-dependent — the 12 core analytic nodes
of §2.3 plus 31 downstream of them — while **170** are E-S-free (`ModPForms`
56/65, `HeckeEis` 96/130, `PeriodPair` 18/18). The $`\theta`$/Hasse toolkit just
listed is in the E-S-free part. The analytic nodes do not descend weight at all;
they *bypass* the gap by producing the degree-$`(k-2)`$ eigensystem directly from
a weight-k mod-p eigenform
(`ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen`, §4.3). So the
gap is not supplied by any piece of the slice — it is the alternative to the
slice — and building it needs only E-S-free material. The worst case (gap
unfillable) therefore costs the 12-node / 2,301-line analytic core, not the whole
213 / 71,865 package.

**Ways forward.**

1. sharpen the reduction so it lands at $`p+1`$ (then interface 6 + route B +
   CohCarrier close interface 3);
2. build the form-side $`\theta`$-descent $`[2, p+1] \to 2`$;
3. build the general-weight $`\mathrm{Sym}^n`$ eigenclass geometrically
   (architecture A; the `intLattice ≅ regularDifferentials` and `KatzLevelPForm`
   clusters are the candidates to host it).

That one statement is what stands between the degree-0 composition and interface 3
at weight $`k \ge 3`$.

## 5. Compatibility and circularity

### 5.1 The refactor of interface 3

The target lemma concludes the **degree-`n`** eigensystem. Its consumer chain in
interface 3 (`P2M/Sol/S_GaloisRep_exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le.lean`
L104–L120) is:

1. `eig χ ℓ := χ(T_ℓ)`; `heig` converts `hχ` into the `heckeTLin` eigenvalue form;
2. the analytic lemma → degree-`n` eigensystem;
3. `GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_binaryFormRepSL_of_ringHom`
   (degree-`n` wrapper), which internally is the weight reduction
   (`HeckeEis.exists_isEigensystemH1_one_dvd_mul_sq_…`, degree-`n` → degree-0,
   level `M \mid Np^2`, eigenvalues twisted by $`\ell^{n/2}`$) followed by
   `GaloisRep.exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom`
   (degree-0 → $`\rho`$, $`\det = \ell`$) and a cyclotomic twist to
   $`\det = \ell^{n+1}`$.

The weight reduction and the Galois step are **E-S-free** (cones 18 / 9,854 and
1,350 / 566,832, **0** analytic nodes), so only step 2 needs replacing. But
candidates 0 + 1 deliver degree 0, not degree `n`. So the swap is *not* one token
at the lemma; the minimal refactor is:

- **drop the analytic lemma and the degree-`n` weight reduction**;
- insert [form-side weight reduction $`k \to 2`$] then route B
  (`exists_parabolicRealization`) then `CohCarrier.isEigensystemH1_one_of_heckeT_eq_smul`,
  yielding the degree-0 `IsEigensystemH1` at level `N`;
- keep `exists_galoisRep_trace_eq_of_isEigensystemH1_one_of_ringHom` and the
  existing cyclotomic twist (the twist lemmas live in the degree-`n` wrapper and
  are reusable).

The refactor is local to interface 3's proof (its own 120-line file), and the
downstream consumers are untouched.

### 5.2 Hypothesis derivability

Interface 3's inputs are: a cusp eigenform `f` of weight $`k \ge 3`$,
$`f \neq 0`$, and $`\chi : heckeAlgebra\ N\ k\ S \to integralClosure\ \mathbb{Z}\ \mathbb{C}`$.
Route B's `exists_parabolicRealization` needs a **weight-2** `IsNormalizedEigenform`
with `PrimeCoeffsIntegral`. So:

- for $`k = 2`$ (outside interface 3's stated range) the hypotheses are the
  weight-2 specialization and the refactor is immediate;
- for $`k \ge 3`$ the hypotheses are **not** derivable without the form-side
  reduction. That reduction is the missing brick of §4.5: the general
  $`k \to k' \le p+1`$ step is C′-dissolved and the $`p+1 \to 2`$ step exists,
  but the $`[2, p+1] \to 2`$ descent is absent.

### 5.3 Circularity

The candidates must not cite the analytic set they are meant to replace. Measured
on the 12-node analytic set of §2.3:

| candidate | analytic nodes in cone | circular? |
|---|---:|---|
| 0 (route B / Period) | 0 | no |
| 1 (CohCarrier, incl. `isEigensystemH1_one_…`) | 0 | no |
| 2 (JZero / Frobenius) | 0 | no |
| 3 (Katz / mod-p reduction, general `exists_weight_le_succ_…`) | 10 now, **0 modulo C′** | no modulo C′ (§4.2) |
| 3′ (`exists_isEigensystemH1_…_of_isModPEigen` core) | 12 | **yes, as written** |
| 4 (abstract E-S data) | 0 (but no path; `existsEichlerShimuraMapLinear` has 5) | n/a |

The E-S-free candidates are non-circular. Candidate 3 splits: the general
reduction is circular only through route A's `hasIntegralStructure_of_two_le`,
which C′ supplies, so modulo C′ it is clean; the intrinsic
`exists_isEigensystemH1_…_of_isModPEigen` core is genuinely circular and is the
one statement a replacement must re-prove without `exists_isEichlerIntegral` and
the other eleven nodes.

## 6. The payout

Interface 3 is the cheapest probe, not the prize. If route B's tame period type
(candidate 0) can be wired into *every* interface, the endgame loses its entire
analytic-Eichler–Shimura layer. Measured over the closure of `FLT.fermatLastTheorem`
(the FLT proof cone):

| quantity | nodes | raw `S_` lines | share of endgame |
|---|---:|---:|---:|
| FLT proof cone | 29,488 | 11,926,355 | 100% |
| E-S-ish package in it: `HeckeEis` 130 / 44,516 + `ModPForms` 65 / 15,084 + `PeriodPair` 18 / 12,265 | 213 | 71,865 | 0.72% / 0.60% |
| ... reachable under the ten maximal interfaces (union of their E-S-ish cones) | 207 | 70,558 | |
| ... residual `ModPForms` nodes with their own entries | 6 | 1,307 | |

**The payout: the E-S layer goes to zero.** Those 213 nodes / 71,865 lines are
the whole formal price of the analytic period map in the endgame; a de-E-S-ified
architecture carries none of them. In port terms this is the
de-`HeckeEis`-ification of the endgame: the E-S spine that §8 of
[flt-non-frey-segments.md](flt-non-frey-segments.md) shows is shared between the
modularity and patching segments disappears from the dependency graph.

**The replacement is already inside the endgame.** Every ingredient of the
replacement is in the FLT proof cone today, so the marginal *new* mathematics is
the wiring, not the theory:

| ingredient | node | role |
|---|---|---|
| route B blob | `CuspForm.moduleFinite_heckeAlgebra_two` | weight-2 period carrier (4,308-line `S_` file, closure 1) |
| C′ lattice | `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` | integral structure |
| geometric E-S congruence | `ModularCurve.frobeniusQuadratic_JZero`, `W54.jZeroPPowTorsion_frobeniusQuadratic` | $`\mathrm{Frob}^2 - T_\ell\,\mathrm{Frob} + \ell = 0`$, zero analytic-E-S nodes |
| $`S_2 \cong \Omega^1`$ | `ModularCurve.exists_linearEquiv_tensor_intLattice_regularDifferentials_qExpansionDiffAlong_eq` | weight-2 identification, no period map |
| eigenplane | `CuspForm.IsNewform.exists_eigenPlane_tateModule_jZero` | E-S-free on the `JZero` Tate module |

All five are already in the endgame closure, so the prize is not offset by a
comparable new cone.

**Why this is not route A's 657-node cone.** Route A's cone is 657 nodes /
263,720 lines, but ~528 of those are modular-curve / elliptic geometry the
endgame needs regardless (Riemann–Roch, `JZero`, patching). The analytic-E-S part
of it is the 213 / 71,865 sliver — which is why C′ alone removes only 4 nodes /
800 lines ([route-c-prime-scout.md](route-c-prime-scout.md) §4 addendum). The
payout is the sliver, and it is the only lever of this size in the interface
family.

**Three targets, one package.** If route B reaches only interface 3, that removes
46 nodes / 23,363 lines. De-E-S-ifying the other nine while retaining interface 3
removes 161 nodes / 47,195 lines. All ten removes the full 213 / 71,865. The first
two are disjoint and partition the ten-interface union (46 + 161 = 207); the
residual six complete the package.

**Two conditions, and one refinement.**

1. *Higher weight is the real condition.* Route B as written is weight 2.
   Interfaces 4, 5 and 6 involve weight $`> 2`$ and the `KatzModularForm.*`
   cluster, so "workable for all interfaces" means the form-side weight reduction
   is E-S-free at general weight — the missing brick of §4.5.
2. *The surface is not literally ten nodes.* The ten maximal interfaces cover 207
   of the 213 E-S-ish nodes, but 12 further non-E-S-ish endgame nodes outside
   their cones (mostly `ModularCurve.SSHeckeV2.*`) directly cite E-S-ish nodes,
   and the 6 residual `ModPForms` nodes have their own entries. A complete
   de-E-S-ification must rewire those too. The prize (213 / 71,865) is unchanged;
   the wiring inventory is the ten interfaces plus a further twelve direct citers
   and the entry points of the residual six.
3. *The residual geometry is paid regardless.* The `JZero`/Tate/Riemann–Roch
   geometry the interfaces consume stays; only the E-S layer leaves.

## 7. Reproduction

### 7.1 Interface 3's partition and analytic cone

```bash
cd tools/deps && python3 - <<'PY'
import sys, os; sys.path.insert(0, '.')
from fltdata import FltData
d = FltData(); I = d.index
root = os.path.expanduser('~/proj/fermats-last-theorem')
def cl(i, skip=frozenset()):
    seen, st = set(), [i]
    while st:
        j = st.pop()
        if j in seen: continue
        seen.add(j)
        if j in skip: continue
        st.extend(d.cites(j))
    return seen
def path_of(i):
    stem = d.stem_of.get(i, '')
    for sub in ('P2M/Sol', 'Theorems'):
        for pre in ('S_', 'Thm_'):
            p = os.path.join(root, sub, f'{pre}{stem}.lean')
            if os.path.exists(p): return p
def lines(i):
    p = path_of(i)
    return sum(1 for _ in open(p, encoding='utf-8', errors='replace')) if p else 0
lem = I['HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul']
i3  = I['GaloisRep.exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le']
CL, C3, C3nl = cl(lem), cl(i3), cl(i3, skip={lem})
he = lambda C: {i for i in C if d.qual(i).startswith('HeckeEis.')}
H3, HCL = he(C3), he(CL); only = H3 - C3nl
ANALYTIC = {I[q] for q in [
 'HeckeEis.exists_isEichlerIntegral',
 'HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral',
 'HeckeEis.IsEichlerIntegral.slash',
 'HeckeEis.IsEichlerIntegral.exists_sub_eq_const',
 'HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const',
 'HeckeEis.IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv',
 'HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval',
 'HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul',
 'HeckeEis.IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries',
 'HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL',
 'HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm',
 'HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero']}
assert ANALYTIC <= CL and ANALYTIC <= C3 and ANALYTIC <= only
assert not [i for i in (H3 - only) if cl(i) & ANALYTIC and i != lem]
print('lemma cone:', len(CL), 'HeckeEis', len(HCL))
print('i3 cone:', len(C3), 'HeckeEis', len(H3), 'lines', sum(lines(i) for i in H3))
print('only-through:', len(only), 'lines', sum(lines(i) for i in only))
print('tail-reachable:', len(H3 - only), 'lines', sum(lines(i) for i in H3 - only))
print('analytic:', len(ANALYTIC), 'lines', sum(lines(i) for i in ANALYTIC))
PY
```

### 7.2 The payout

```bash
cd tools/deps && python3 - <<'PY'
import sys, os; sys.path.insert(0, '.')
from fltdata import FltData
d = FltData(); I = d.index
root = os.path.expanduser('~/proj/fermats-last-theorem')
def lines(i):
    stem = d.stem_of.get(i, '')
    for sub in ('P2M/Sol', 'Theorems'):
        for pre in ('S_', 'Thm_'):
            p = os.path.join(root, sub, f'{pre}{stem}.lean')
            if os.path.exists(p):
                return sum(1 for _ in open(p, encoding='utf-8', errors='replace'))
    return 0
def cl(i):
    seen, st = set(), [i]
    while st:
        j = st.pop()
        if j in seen: continue
        seen.add(j); st.extend(d.cites(j))
    return seen
ES = ('HeckeEis.', 'ModPForms.', 'PeriodPair.')
ifaces = [
 'WeierstrassCurve.exists_ideal_heckeAlgebra_mul_two_of_ideal_heckeAlgebra_two_or_succ',
 'WeierstrassCurve.exists_H1_parabolic_not_dvd_diamondRaw_heckeT_congr_apOfModel_level_div_of_forall_linearMap_psCarrier_eq_zero',
 'GaloisRep.exists_galoisRep_trace_eq_eigenchar_and_det_eq_pow_of_three_le',
 'WeierstrassCurve.exists_ideal_heckeAlgebra_three_weight_le_four_pow_mul_apOfModel_of_exists_prime_dvd_mod_three_eq_two',
 'CuspForm.heckeAlgebra.exists_isMaximal_two_ringHom_of_succ_of_map_T_eq_zero_of_five_le_or_exists_prime_dvd',
 'CuspForm.heckeAlgebra.thetaCycle_exists_ringHom_mul_two_apply_eq_of_ringHom_succ_of_eq_three_imp_exists_prime_dvd_mod_three_eq_two',
 'CuspForm.exists_mem_heckeAlgebra_singleton_heckeTLin_eq_add_smul_of_ne_two',
 'LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime',
 'ModularCurve.exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero',
 'WeierstrassCurve.exists_ne_zero_mem_rationalHomSet_of_comp_self_add_smul_eq_smul']
end = cl(I['FLT.fermatLastTheorem'])
Eend = {i for i in end if d.qual(i).startswith(ES)}
U = set()
for q in ifaces:
    U |= {i for i in cl(I[q]) if d.qual(i).startswith(ES)}
print('endgame', len(end), 'nodes /', sum(lines(i) for i in end), 'lines')
print('E-S-ish', len(Eend), '/', sum(lines(i) for i in Eend))
print('ten-interface union', len(U), '/', sum(lines(i) for i in U))
print('residual', len(Eend - U), '/', sum(lines(i) for i in (Eend - U)))
PY
```

### 7.3 The C′-dissolution of the weight reduction

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from fltdata import FltData
d = FltData(); I = d.index
AN = {I[q] for q in [
 'HeckeEis.exists_isEichlerIntegral',
 'HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral',
 'HeckeEis.IsEichlerIntegral.slash',
 'HeckeEis.IsEichlerIntegral.exists_sub_eq_const',
 'HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const',
 'HeckeEis.IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv',
 'HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval',
 'HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul',
 'HeckeEis.IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries',
 'HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL',
 'HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm',
 'HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero']}
def cl(i, skip=frozenset()):
    seen, st = set(), [i]
    while st:
        j = st.pop()
        if j in seen: continue
        seen.add(j)
        if j in skip: continue
        st.extend(d.cites(j))
    return seen
H = I['CuspForm.hasIntegralStructure_of_two_le']
for q in [
 'ModPForms.nonempty_ssDatum_algebraicClosure',
 'ModularCurve.SSHeckeV2.ssHeckeFun_window',
 'ModPForms.exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure',
 'ModPForms.exists_three_weight_le_four_mem_modPMod_isModPEigen_pow_mul_of_exists_prime_dvd_mod_three_eq_two',
 'ModPForms.exists_isEigensystemH1_binaryFormRepSL_of_isModPEigen']:
    C, Cx = cl(I[q]), cl(I[q], skip={H})
    print(f'{q}: analytic {len(C & AN)} -> {len(Cx & AN)} with C-prime')
PY
```

### 7.4 How much of the slice is actually analytic

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from fltdata import FltData
d = FltData(); I = d.index
AN = {I[q] for q in [
 'HeckeEis.exists_isEichlerIntegral',
 'HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral',
 'HeckeEis.IsEichlerIntegral.slash',
 'HeckeEis.IsEichlerIntegral.exists_sub_eq_const',
 'HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const',
 'HeckeEis.IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv',
 'HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval',
 'HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul',
 'HeckeEis.IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries',
 'HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL',
 'HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm',
 'HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero']}
def cl(i):
    seen, st = set(), [i]
    while st:
        j = st.pop()
        if j in seen: continue
        seen.add(j); st.extend(d.cites(j))
    return seen
for ns in ('HeckeEis.', 'ModPForms.', 'PeriodPair.'):
    nodes = [q for q in I if q.startswith(ns)]
    free = [q for q in nodes if not (cl(I[q]) & AN)]
    print(f'{ns:12s} {len(nodes):4d} nodes: {len(free):4d} E-S-free, {len(nodes)-len(free):3d} analytic-dependent')
PY
```

## Appendix — the 15 tail-only `HeckeEis` nodes (8,188 lines)

In interface 3's cone, outside the target lemma's cone, hence E-S-free by §2.3.
These are the weight-reduction / level-raising / transfer nodes of the tail.

| node (`HeckeEis.`) | lines |
|---|---:|
| `exists_isEigensystemH1_gamma0NebenRep_of_isEigensystemH1_binaryFormRepSL_of_dvd` | 1,178 |
| `exists_isEigensystemH1_one_of_isEigensystemH1_gamma0NebenRep` | 1,129 |
| `exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd` | 1,113 |
| `isEigensystemH1_one_natCast_add_one` | 835 |
| `exists_isEigensystemH1_binaryFormRepSL_empty_of_isEigensystemH1_of_ringHom` | 649 |
| `isEigensystemH1_of_isEigensystemH1_of_surjective` | 631 |
| `exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd` | 594 |
| `isEigensystemH1_binaryFormRepSL_mul_of_isEigensystemH1` | 482 |
| `existsUnique_coeffCocycles_sl2z_apply_S_ST_eq` | 452 |
| `isEigensystemH1_or_of_isEigensystemH1_of_injective` | 405 |
| `exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq` | 395 |
| `exists_isEigensystemH1_one_dvd_mul_sq_of_isEigensystemH1_binaryFormRepSL` | 236 |
| `coresHom_eq_transfer` | 59 |
| `heckeOperatorHom_smul` | 17 |
| `postcomp_heckeOperatorHom` | 13 |
| **total** | **8,188** |
