# Topic: the general-weight Eichler–Shimura period map and its injectivity

**Status: scoped, not started (2026-09-27).** A port plan for the **minimum cone
that logically contains Route B generalised to all weights**: the period map
$`S_k(\Gamma_0(N)) \to H^1_{par}(\Gamma_0(N), \mathrm{Sym}^{k-2})`$ and its
injectivity, for every $`k = n+2 \ge 2`$. This is the first milestone of
[../../../studies/eichler-shimura-scout.md](../../../studies/eichler-shimura-scout.md)
§3.4 and §6 (tiers 1–2); it is **not** the full isomorphism (no Hecke
equivariance, no conjugate half, no integral basis, no dimension theory, no
eigenclass).

Measured against the FLT pin `aa2d8b3`; the port's mathlib is `v4.34.0`. The
mathematics is [../../../math/017-eichler-shimura-isomorphism.md](../../../math/017-eichler-shimura-isomorphism.md)
§1; the analytic-core scoping that this plan narrows is
[TOPIC-relaxed-analytic-core.md](TOPIC-relaxed-analytic-core.md); route B (the
$`n = 0`$ case this target subsumes) is retired to `lean/Reserve/`.

## 0. Target and verdict

**Target.** For all $`N \ge 1`$ and $`n \ge 0`$, a ℂ-linear map

```lean
periodMap (n N) : CuspForm (Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ]
    coeffH1par ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype)
```

with `periodMap n N f` the class of the period cocycle of an Eichler integral of
$`f`$, and a proof

```lean
theorem periodMap_injective (n N) : Function.Injective (periodMap n N)
```

**Verdict.** Feasible and self-contained. The cone is **27 nodes / 2,759 `S_`
lines** plus **3 definition modules / 442 lines** and **~200 statement lines** —
about **3,400 lines**, of which roughly none is in the port today. It is
*smaller* than Route B's 4,308-line blob and strictly stronger. The only genuine
mathematical gap is the analysis: the star-convex antiderivative, the
boundedness-at-the-cusp implication, the trace classification and the iterated
$`\partial_1`$ identity.

## 1. The cone, measured

Closure of `HeckeEis.eichlerShimuraMap_injective` in the pin, restricted to the
nodes this target needs:

| piece | nodes | `S_` lines |
|---|---:|---:|
| `HeckeEis` theorem nodes | 22 | 2,149 |
| definition modules | 3 | 442 |
| external theorem nodes | 5 | 610 |
| `Thm_` statement wrappers | — | ~200 |
| **total** | **27 + 3 defs** | **~3,400** |

The full node list with direct dependencies is the Appendix. It splits into:

* **leaves** (no intra-cone dependency): `IsEichlerIntegral.add` (42),
  `IsEichlerIntegral.smul` (38), `IsEichlerIntegral.slash` (191),
  `IsEichlerIntegral.exists_sub_eq_const` (172),
  `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` (305),
  `jFactor_pow_mul_eval_binaryFormRepSL` (74),
  `binaryFormRepSL_neg_one_apply` (34),
  `coeff_single_one_eq_eval_of_mem_binaryForm` (36),
  `mem_range_binaryFormRepSL_T_zpow_sub_one` (113),
  `IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` (44);
* **the ladder/boundedness branch**:
  `eq_zero_of_eval_eq_const` (92) and `isBoundedAtImInfty_eval` (178);
* **the parabolic branch**: `exists_isEichlerIntegral` (102),
  `isEquivariantPrimitiveWith_of_isEichlerIntegral` (46),
  `vadd_sub_T_zpow_apply_mem_range` (85),
  `isParabolicCocycle_cocycle_of_isEichlerIntegral` (137),
  `exists_isEichlerIntegral_isParabolicCocycle` (27);
* **the map and assembly**: `eichlerShimuraMap_eq_coeffH1parMk` (48),
  `eichlerShimuraMap_add` (81), `eichlerShimuraMap_smul` (79),
  `existsEichlerShimuraMapLinear` (39), `eichlerShimuraMap_injective` (186).

Nothing here uses `coeffH1` (the non-parabolic quotient), `coeffHeckeFun`, the
Hecke correspondence (`heckeUpper`/`heckeConj`/`transferAux`), the dimension
theory, or the `ModularCurve` genus/cusp cone.

## 2. Module plan

Directory `FLTForHuman/ModularForms/EichlerShimura/` (one theory per directory,
playbook §8), with the shared vocabulary in the parent `Defs/` if it is reused
later:

| module | contents |
|---|---|
| `EichlerShimura/BinaryForm.lean` | `BinaryForm`, `binarySubst` (+ `_X`, `_C`, `_one`, `_mul`, `_mem`), `binaryFormRepSL` (+ `_apply_coe`), `binaryFormAlphaAdj`; the helpers `coeff_single_one_eq_eval_of_mem_binaryForm`, `binaryFormRepSL_neg_one_apply`, `mem_range_binaryFormRepSL_T_zpow_sub_one` |
| `EichlerShimura/CoeffCohomology.lean` | `coeffCocycles`, `coeffCoboundaryMap`, `coeffCoboundaries`, `IsParabolicCocycle`, `coeffParabolicCocycles`, `coeffH1par`, `coeffH1parMk`, `coeffH1parMk_eq_zero_iff`, and the inclusion lemmas |
| `EichlerShimura/EichlerIntegral.lean` | `linePow`, `jFactor` (+ `_eq_denom`, `_ne_zero`), `binaryFormRepSL_linePow`, `IsEquivariantPrimitiveWith` (+ `cocycle`, `sub_eq_cocycle`, `apply_smul`, `cocycle_mem_coeffCocycles`), `IsEichlerIntegral`, `jFactor_pow_mul_eval_binaryFormRepSL` |
| `EichlerShimura/PeriodMap.lean` | `periodMap` (the linear map), `periodMap_eq_coeffH1parMk`, `periodMap_injective` |
| `EichlerShimura/Externals.lean` (or split into the areas below) | the five mathlib-absent nodes of §3 |

The five externals do not belong to the E-S theory; place them where the port
already keeps their neighbours: the antiderivative near `ModularCurve/Analytic/`,
the two `UpperHalfPlane` facts near the q-expansion layer, the trace
classification near the congruence-subgroup/`SL₂(ℤ)` material, the `pderiv`
identity in a small `MvPolynomial` module. A single `Externals.lean` is
acceptable for the first pass; promote on the second consumer (playbook §9).

## 3. Tier order

Each tier builds and is checkable on its own. The order is bottom-up by the
dependency edges in the Appendix.

### Tier 0 — the five externals (610 lines)

| node | `S_` lines | content | note |
|---|---:|---|---|
| `MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` | 40 | homogeneous $`\varphi`$ of degree $`n`$, $`n \lt i`$ $`\Rightarrow`$ $`(\partial_k)^i\varphi = 0`$ | pure algebra, no analysis |
| `Complex.exists_hasDerivAt_of_starConvex` | 150 | radial path integral differentiated under the integral sign | **the one new analytic lemma**; mathlib has the dominated-convergence machinery but not the package |
| `UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic` | 175 | $`v' = u`$, $`u`$ bounded and periodic, $`v`$ periodic $`\Rightarrow`$ $`v`$ bounded at the cusp | Liouville-type; uses `cuspFunction`, `dslope`, `isExactOn_ball`, `Periodic.qParam` |
| `UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty` | 110 | the mean-value/periodic-integral identity behind the above | |
| `ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four` | 135 | a $`\gamma \in \mathrm{SL}_2(\mathbb{Z})`$ with $`\mathrm{tr}^2 = 4`$ is conjugate to $`\pm T^h`$ | the parabolic classification |

### Tier 1 — the definitions (442 lines)

Bottom-up: `BinaryForm.lean` → `CoeffCohomology.lean` → `EichlerIntegral.lean`.
Adopt mathlib types as the interface from the first declaration (playbook §3.8):
`MvPolynomial.homogeneousSubmodule`, `Representation`, `Submodule.Quotient`,
`UpperHalfPlane`, `ModularForm`/`CuspForm`, `Matrix.SpecialLinearGroup`.

**One deliberate divergence.** The pin defines `eichlerShimuraMap` on
$`f : \mathbb{H} \to \mathbb{C}`$ by a `dif` on the existence of an Eichler
integral with a parabolic cocycle, falling back to `0`. The port should not
mirror that: define the period class on cusp forms from a chosen Eichler
integral (`Classical.choose` of `exists_isEichlerIntegral`), prove it independent
of the choice through `exists_sub_eq_const` and
`cocycle_sub_cocycle_mem_coeffCoboundaries`, and expose the linear map
`periodMap`. This removes the `dif`, makes linearity structural rather than a
case split, and leaves the pin's `eichlerShimuraMap_def` /
`eichlerShimuraMap_of_not_exists` wrappers behind. Record the divergence in the
module header (playbook §7.4).

### Tier 2 — the leaves (about 1,100 lines)

`IsEichlerIntegral.add` (42), `.smul` (38), `.slash` (191),
`.exists_sub_eq_const` (172), `binaryFormRepSL_neg_one_apply` (34),
`coeff_single_one_eq_eval_of_mem_binaryForm` (36),
`mem_range_binaryFormRepSL_T_zpow_sub_one` (113),
`IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` (44),
`jFactor_pow_mul_eval_binaryFormRepSL` (74).

Two notes. `exists_sub_eq_const` and `slash` share a 132-line byte-identical
helper block in the pin (`EichlerIntegralAux`); factor it once, do not copy
(playbook §7 checklist item 7). `slash` and `binarySubst_adjugate_comp_smul` are
**not** both needed here — the latter is Hecke-transport, outside this cone.

### Tier 3 — the analytic chain and the target (about 1,050 lines)

In dependency order:

1. `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` (305) — the iterated
   $`\partial_1`$ identity; the largest node.
2. `IsEichlerIntegral.eq_zero_of_eval_eq_const` (92).
3. `IsEichlerIntegral.isBoundedAtImInfty_eval` (178).
4. `exists_isEichlerIntegral` (102) — the star-convex antiderivative wrapper.
5. `isEquivariantPrimitiveWith_of_isEichlerIntegral` (46).
6. `IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range` (85).
7. `isParabolicCocycle_cocycle_of_isEichlerIntegral` (137).
8. `exists_isEichlerIntegral_isParabolicCocycle` (27).
9. `eichlerShimuraMap_eq_coeffH1parMk` (48) / `periodMap_eq_coeffH1parMk`.
10. `periodMap_add` (81), `periodMap_smul` (79) — structural in the port's
    restatement.
11. `existsEichlerShimuraMapLinear` (39) — or folded into the `periodMap` def.
12. **`periodMap_injective`** (186) — the target.

## 4. Difficulty and risk

| node | lines | character | risk |
|---|---:|---|---|
| `hasDerivAt_eval_iterate_pderiv` | 305 | `descFactorial`/`choose`/alternating sums, `eval_one_eq_sum` | high; expect `Nat.descFactorial_*` name drift |
| `isBoundedAtImInfty_of_hasDerivAt_of_periodic` (external) | 175 | Liouville-type boundedness | medium-high; the `cuspFunction`/`dslope` API |
| `exists_hasDerivAt_of_starConvex` (external) | 150 | interval integral differentiated under the sign | medium-high; the only genuinely new analysis |
| `IsEichlerIntegral.slash` | 191 | chain rule under slash, `denom`/`zpow` | medium-high |
| `exists_sub_eq_const` | 172 | `is_const_of_fderiv_eq_zero`; 132 shared lines | low-medium once factored |
| `mem_range_binaryFormRepSL_T_zpow_sub_one` | 113 | unipotent fixed-vector algebra | medium |
| `periodMap_injective` | 186 | negative-weight form trick | medium; mostly assembly |
| the rest | ~700 | transport/bookkeeping | low |

The port's expense is its distance from mathlib (playbook §7.3). Here that
distance is the five externals (610 lines) and the API archaeology beneath them;
the 1,100-line theorem body is mostly algebra and bookkeeping against mathlib's
existing `MvPolynomial`, `UpperHalfPlane`, `ModularForm` and `intervalIntegral`
APIs.

## 5. Faithfulness and consumers

* Diff every public statement against the pin's `Theorems/Thm_HeckeEis_*.lean`,
  spelling binders as the pin does, with the two recorded divergences
  (`periodMap` replaces the `dif`ed `eichlerShimuraMap`; injectivity is stated
  for the linear map).
* Add a consumer module under `lean/spec/` in the style of the existing
  `*Consumer.lean` files: import the period-map module and compose it into a
  `#check`/`example` that reproduces the pin's `eichlerShimuraMap_injective`
  statement through the port's API.
* `#print axioms` clean; no `sorry` (playbook §5.11).

## 6. Stop conditions

* **The star-convex antiderivative resists.** If `Complex.exists_hasDerivAt_of_starConvex`
  cannot be closed against mathlib `v4.34.0` after a bounded attempt, stop and
  report: it is the whole analytic base, and the rest of the cone is contingent
  on it.
* **The iterated-`pderiv` node blows up the build.** Bound every build
  (`timeout 180 lake build`); a heartbeat jump means a defeq blow-up, not a slow
  proof (playbook §3.11). Quarantine and revisit.
* **The def-layer port pulls in the projective-line / eval block.** The pin's
  `Def_HeckeEis_BinaryFormRep` also contains `evalRow`/`binaryFormEval` for the
  projectiveline; they are *not* needed here. If the port's `BinaryForm.lean`
  needs `ProjectiveLine`/`UnimodularRow`, something has been included that
  belongs to the full driver.

## 7. Budget

**3–5 build rounds** for tiers 0–3, plus 1 round for the consumer and the
statement diff. Tier 0 is the schedule risk; tiers 1–2 are mechanical.

## 8. What this unlocks

* The general-weight period map and its injectivity — strictly containing Route B
  (its $`n = 0`$ case), so the Route B reserve candidate never needs to be
  ported for coverage.
* The foundation for the rest of the driver
  ([../../../studies/eichler-shimura-scout.md](../../../studies/eichler-shimura-scout.md)
  §6): tier 3 of the scout (Hecke equivariance, conjugate half, integral basis,
  dimension bound, complementarity) sits directly on this, and the door-2 layer
  after it.
* A checkable answer to "is the E-S analysis portable against mathlib `v4.34.0`"
  before any of the cohomological packaging is attempted.

## 9. Reproduction

```bash
cd tools/deps && python3 - <<'PY'
import sys, os, re, collections; sys.path.insert(0, '.')
from fltdata import FltData
from prune import FltPayoff
d = FltData(); pay = FltPayoff(data=d)
root = os.path.expanduser('~/proj/fermats-last-theorem')
C = pay.closure(d.index['HeckeEis.eichlerShimuraMap_injective'])
he = [i for i in C if d.qual(i).startswith('HeckeEis.')]
ext = [i for i in C if not d.qual(i).startswith('HeckeEis.')]
print('closure', len(C), pay.total_lines(C))
print('HeckeEis', len(he), pay.total_lines(he))
print('external', len(ext), pay.total_lines(ext))
defs = collections.Counter()
for i in he:
    stem = d.stem_of.get(i, d.qual(i).split('.')[-1])
    p = os.path.join(root, 'P2M/Sol', f'S_{stem}.lean')
    if os.path.exists(p):
        for line in open(p, encoding='utf-8', errors='replace'):
            m = re.match(r'import Definitions\.(Def_\w+)', line.strip())
            if m: defs[m.group(1)] += 1
for m, c in defs.most_common():
    print('def', m, sum(1 for _ in open(os.path.join(root, 'Definitions', m + '.lean'))))
PY
```

## Appendix — the 22 nodes, with in-cone dependencies

| `S_` lines | node (`HeckeEis.`) | in-cone deps |
|---:|---|---|
| 42 | `IsEichlerIntegral.add` | — |
| 38 | `IsEichlerIntegral.smul` | — |
| 191 | `IsEichlerIntegral.slash` | — |
| 172 | `IsEichlerIntegral.exists_sub_eq_const` | — |
| 305 | `IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv` | — |
| 92 | `IsEichlerIntegral.eq_zero_of_eval_eq_const` | `hasDerivAt_eval_iterate_pderiv`, `iterate_pderiv_eq_zero_of_lt` |
| 178 | `IsEichlerIntegral.isBoundedAtImInfty_eval` | `hasDerivAt_eval_iterate_pderiv`, `iterate_pderiv_eq_zero_of_lt`, `isBoundedAtImInfty_of_hasDerivAt_of_periodic`, `jFactor_pow_mul_eval_binaryFormRepSL` |
| 74 | `jFactor_pow_mul_eval_binaryFormRepSL` | — |
| 34 | `binaryFormRepSL_neg_one_apply` | — |
| 36 | `coeff_single_one_eq_eval_of_mem_binaryForm` | — |
| 113 | `mem_range_binaryFormRepSL_T_zpow_sub_one` | — |
| 44 | `IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries` | — |
| 102 | `exists_isEichlerIntegral` | `Complex.exists_hasDerivAt_of_starConvex` |
| 46 | `isEquivariantPrimitiveWith_of_isEichlerIntegral` | `slash`, `exists_sub_eq_const` |
| 85 | `IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range` | `coeff_single_one_eq_eval_of_mem_binaryForm`, `apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty`, `mem_range_binaryFormRepSL_T_zpow_sub_one` |
| 137 | `isParabolicCocycle_cocycle_of_isEichlerIntegral` | `exists_eq_conj_T_zpow_of_trace_sq_eq_four`, `vadd_sub_T_zpow_apply_mem_range`, `binaryFormRepSL_neg_one_apply`, `slash` |
| 27 | `exists_isEichlerIntegral_isParabolicCocycle` | `exists_isEichlerIntegral`, `isEquivariantPrimitiveWith_of_isEichlerIntegral`, `isParabolicCocycle_cocycle_of_isEichlerIntegral` |
| 48 | `eichlerShimuraMap_eq_coeffH1parMk` | `exists_sub_eq_const`, `cocycle_sub_cocycle_mem_coeffCoboundaries` |
| 81 | `eichlerShimuraMap_add` | `exists_isEichlerIntegral_isParabolicCocycle`, `eichlerShimuraMap_eq_coeffH1parMk`, `IsEichlerIntegral.add` |
| 79 | `eichlerShimuraMap_smul` | `exists_isEichlerIntegral_isParabolicCocycle`, `eichlerShimuraMap_eq_coeffH1parMk`, `IsEichlerIntegral.smul` |
| 39 | `existsEichlerShimuraMapLinear` | `eichlerShimuraMap_add`, `eichlerShimuraMap_smul` |
| 186 | `eichlerShimuraMap_injective` | `hasDerivAt_eval_iterate_pderiv`, `isBoundedAtImInfty_eval`, `eq_zero_of_eval_eq_const`, `jFactor_pow_mul_eval_binaryFormRepSL`, `exists_isEichlerIntegral_isParabolicCocycle`, `eichlerShimuraMap_eq_coeffH1parMk`, `slash`, `existsEichlerShimuraMapLinear` |

**Definition modules:** `Def_HeckeEis_BinaryFormRep` (140),
`Def_Gamma0CoeffCohomology` (153), `Def_HeckeEis_EichlerIntegral` (149).

**External nodes:** `UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic`
(175), `Complex.exists_hasDerivAt_of_starConvex` (150),
`ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four` (135),
`UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty` (110),
`MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt` (40).
