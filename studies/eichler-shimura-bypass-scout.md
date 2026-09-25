# The Eichler–Shimura bypass — scout

**Status: Phase 0 complete (2026-09-25). Phases 1–6 not started.** Phase 0 froze
the contract and produced the E-S partition, and it fixed the one constraint that
decides Phase 1: the replacement must stay inside route B's **tame carrier**
(`addChars`, i.e. `Hom`, with no cohomology quotient) and must not introduce a
general `Sym^n` `H¹` (§0, §7). The plan in
[../lean/topics/eichlerShimuraBypass/TOPIC-interface-3-rewiring.md](../lean/topics/eichlerShimuraBypass/TOPIC-interface-3-rewiring.md)
is coherent as written: every number it states reproduced against the pin, and its
Phase 0 gate passes (§0). This note is the artifact Phase 0 was supposed to
deposit; the parent topic remains the plan of record.

Measured 2026-09-25 against the FLT pin `aa2d8b3` with `tools/deps` (docs-site
graph closure) plus source greps of the pin's `S_`/`Thm_` files. The port's
mathlib is `v4.34.0`. Companion provenance:
[flt-non-frey-segments.md](flt-non-frey-segments.md) §8–§8.1,
[route-c-prime-scout.md](route-c-prime-scout.md) §4 addendum,
[../math/015-weight-two-hecke-periods.md](../math/015-weight-two-hecke-periods.md).

## 0. Verdict and Phase 0 gate

**The gate passes.** Interface 3's analytic-Eichler–Shimura footprint is
concentrated in the cone of the single target lemma

`HeckeEis.isEigensystemH1_binaryFormRepSL_of_heckeTLin_eq_smul`,

and every bit of it is analytic *Eichler-integral / period-map* content of one
kind. No node of interface 3's E-S-free tail reaches it (§2.3). The analytic cone
is not "one declaration" — it is 9 genuinely analytic nodes plus 3 E-S-packaging
nodes, all of them in the target lemma's proof cone and nowhere else in interface
3 (Table 2). This is exactly the shape the plan's §3 "one analytic lemma"
assumption needs: replacing that one construction removes the whole analytic
footprint, and nothing downstream inherits an analytic obligation.

**The constraint that governs the replacement (route B's tame type).** Route B's
blob never formalizes cohomology, and the replacement must not either. Its period
side is `addChars R G M` — literally the submodule of additive characters
$`G \to M`$ cut out by $`\varphi(\gamma\delta) = \varphi\gamma + \varphi\delta`$
([`S_CuspForm_moduleFinite_heckeAlgebra_two.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean#L1695-L1697)
L1695; see [../math/015-weight-two-hecke-periods.md](../math/015-weight-two-hecke-periods.md)
§3). At trivial coefficients every 1-coboundary vanishes
($`g \cdot m - m = 0`$), so `addChars` is just `Hom(G, M)`: no quotient, no
$`H^1`$, no resolution. Interface 3's analytic step instead lands in
`HeckeEis.coeffH1 = coeffCocycles ⧸ coeffCoboundaries` on `Sym^n` — a genuine
cohomology quotient, and the only one in the contract.

So the Phase 1 rule is: **produce the $`n = 0`$ eigensystem on route B's tame
carrier** (`addChars κ Γ₀ κ`, or the `IsEquivariantPrimitive`/`period` primitive
that generates it) **and reach `coeffH1 1` only through the thin bridge where
`coeffCoboundaries 1 = ⊥`**; obtain $`n > 0`$ by a *form-side* weight reduction,
never by building $`H^1(\Gamma_0, \mathrm{Sym}^n)`$ (Kuga–Sato, de Rham
comparison, `coeffH1`-carrier identifications). This is what makes the plan's
Architecture A candidates suspect and Architecture B / Candidate 0 the leading
one, and it is carried into §7 as the Phase 1 gate.

Coherence checks against the plan all pass (§5).

## 1. The contract (Phase 0 task 2)

These are the exact types the replacement must produce or be compatible with. All
are in the pin; the `S_`/`Thm_` citation is by module stem.

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
cohomology argument anywhere in this topic — while `IsEichlerIntegral` /
`IsEquivariantPrimitiveWith` are the analytic carrier. Route B's blob has that same
primitive with no quotient at all: `coeffCoboundaries ρ` is the range of
$`v \mapsto (\rho g v - v)_g`$ (`Definitions/Def_Gamma0CoeffCohomology.lean`), so
at trivial coefficients `coeffCoboundaries 1 = ⊥` and `coeffH1 1` is already
route B's `addChars κ Γ₀ κ`.

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

## 2. The 36-node E-S partition (Phase 0 task 3)

Interface 3's cone is 1,390 nodes, 36 of them `HeckeEis.`, together 13,293 raw
`S_` lines — the plan's §1 figure. Of those 36, only 21 lie in the target
lemma's cone (its cone is 25 nodes total; the 4 non-`HeckeEis.` members are
`Complex.exists_hasDerivAt_of_starConvex`,
`Module.exists_ne_zero_forall_baseChange_eq_smul_of_algHom`,
`MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt`,
`UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic`).

### 2.1 The two-way partition (the requested table)

Split by whether a node is reachable from interface 3 *without* passing through
the target lemma (a graph fact, not a statement about analyticity):

| class | `HeckeEis.` nodes | lines | note |
|---|---:|---:|---|
| reachable **only through** the lemma | 14 | 3,082 | 12 analytic + 2 E-S-free algebra (§2.2) |
| reachable **without** the lemma ("tail") | 22 | 10,211 | 7 also in the lemma's cone, 15 not |
| total | 36 | 13,293 | |

The 15 tail-only nodes carry 8,188 lines and include the weight-reduction /
level-raising machinery the plan calls E-S-free:
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
the three small transfer/`postcomp` bookkeeping lemmas.

### 2.2 The 14 "only through the lemma" nodes

Twelve are analytic (9 analytic + 3 E-S packaging, Table 2). The other two are
E-S-free *algebra* that happens to be consumed only via the lemma inside
interface 3 and must be counted in any replacement budget:

| node | lines | role |
|---|---:|---|
| `HeckeEis.span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top` | 423 | integral cocycles $`\mathbb{C}`$-span `coeffCocycles` |
| `HeckeEis.exists_injective_baseChange_coeffH1_binaryFormRepSL` | 358 | injectivity of $`F \otimes_{\mathbb{Z}} \mathrm{coeffH1}_{\mathbb{Z}} \to \mathrm{coeffH1}_F`$ at $`\mathrm{char}\,F = p`$ |

Neither is analytic, and both are general cohomology-algebra facts a
replacement would reuse unchanged. The honest label for this class is
"graph-reachable only through the lemma", not "analytic".

### 2.3 No tail node depends on the analytic cone

Direct check: for each of the 22 tail-reachable nodes, compute its closure and
intersect with the analytic set. The only hit is the lemma itself. No tail node
cites the lemma (`d.cites` is empty of it). So the analytic cone is a *leaf
gadget*: interface 3 consumes it solely through the one lemma. This is the
measurement the plan's Phase 0 gate and its §2 claim needed.

## 3. The 21-node lemma cone and the analytic fact table

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

## 4. Where the analysis sits inside the 523-line lemma

The lemma file splits cleanly, and the split is the plan's §2 claim made
concrete:

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

The analytic call sites are lines 370–390
(`exists_eigenclass_of_eigenform`): `exists_isEichlerIntegral` (370),
`isEquivariantPrimitiveWith_of_isEichlerIntegral` (378),
`modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero` (380),
`coeffH1Mk_cocycle_heckeTLin_modularForm` (385). Everything else in the file is
E-S-free.

**Marking, as Phase 0 asked, "which are only needed to build the period class":**
all four call-site facts build the period class and its two properties
(existence, nonvanishing, Hecke eigenvector). They are needed for the ℂ
eigensystem that the `ℤ`-integrality and base-change steps consume. No analytic
fact is needed for the *carrier* or for the base-change/Hecke-bookkeeping half of
the lemma.

## 5. Coherence of the plan (what reproduced)

| plan claim | measured |
|---|---|
| lemma cone 25 nodes / 21 `HeckeEis` | 25 / 21 |
| interface 3 `HeckeEis` footprint 36 nodes | 36 |
| that footprint's raw `S_` lines 13,293 | 13,293 |
| lemma's only direct citer is interface 3 | yes (only citer) |
| interface 3's only citer is `…trace_eq_heckeT_mod_of_isMaximal` | yes (only citer) |
| the tail (weight reduction `n → 0`, `ModP` construction) is E-S-free | yes (§2.3) |
| route B blob `S_CuspForm_moduleFinite_heckeAlgebra_two.lean` = 4,308 lines | 4,308 |
| `Def_ModularCurve_PeriodMap.lean` has `IsEquivariantPrimitive`, `period`, `periodHom`, `parabolicHoms` | yes |
| route B ingredients present (`exists_equivariantPrimitive_gamma0`, `periodHom_injective`, `periodHom_hecke`, `span_range_ofIntChars`) | yes |
| all provenance files exist | yes |

Two refinements the plan should carry into Phase 1:

1. **"Only through the lemma" ≠ "analytic".** Two E-S-free algebra nodes
   (`span_coeffCocycles_…`, `exists_injective_baseChange_…`, 781 lines) are in
   the 14-node only-through class. A replacement that keeps the carrier but
   swaps the analytic step still needs them (or an equivalent), so the marginal
   saving is the analytic set, not all 14.
2. **The plan's date is off by one** — the topic header says 2026-09-26; this
   Phase 0 ran 2026-09-25. Cosmetic.

The plan's §3 leading hypothesis (Architecture B / Candidate 0, route B weight-2
E-S plus a form-side weight reduction) is untouched by Phase 0 and remains the
thing Phase 1 must test. Phase 0 adds one precise target: the replacement need
only reproduce $`\mathrm{coeffH1}(\mathrm{binaryFormRepSL}\,\kappa\,n)`$'s
eigensystem, and the analytic machinery it must avoid is exactly the 12-node set
of §3.

## 6. Reproduction

Graph closure, the 36/21 partition, the only-through split, and the line totals
(the `tools/deps` metric: sum of `S_`-file lines over a closure, `P2M/Sol`
preferred over `Theorems`):

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

## 7. What Phase 1 inherits

- **The carrier constraint (§0).** The replacement must stay inside route B's
  tame type: build the $`n = 0`$ eigensystem on `addChars κ Γ₀ κ` (or the
  `IsEquivariantPrimitive`/`period` primitive), bridge to `coeffH1 1` only where
  `coeffCoboundaries 1 = ⊥`, and reach $`n > 0`$ by a form-side weight
  reduction. Any candidate whose cone contains a genuine $`H^1`$ over
  $`\mathrm{Sym}^n`$ (Kuga–Sato, de Rham comparison, `CohCarrier.H1`
  identification) is outside this constraint and needs a separate justification.
- A frozen contract (§1) with the exact `IsEigensystemH1` target.
- The knowledge that the replacement's marginal cost is the 12-node / 2,301-line
  analytic set, and that the carrier/base-change/Hecke-bookkeeping half is
  reusable as is.
- The only-through split, so Phase 2's circularity check has the exact 12-node
  set to test candidate cones against (the plan's §5 stop condition).
- Untouched: Phase 1's five candidates, Phase 2 compatibility, Phase 3 measured
  gain, Phase 4 novelty, Phase 5 spike.

## Appendix — the 15 tail-only `HeckeEis` nodes (8,188 lines)

In interface 3's cone, outside the target lemma's cone, hence E-S-free by §2.3.
These are the weight-reduction / level-raising / transfer nodes the plan's §1
calls the E-S-free tail.

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
