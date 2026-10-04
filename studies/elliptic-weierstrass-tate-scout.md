# Elliptic / Weierstrass / Tate — port scout and subject plan

**Status (snapshot, 2026-09-30).** Subject scout for the elliptic-curve theory the
FLT/Frey cone needs, split out of the Deligne–Serre scout §4.1 (which now points
here). Everything is measured against pin `aa2d8b3` with `tools/deps`; the port's
mathlib is `v4.34.0`.

* **Frontier** $`F`$ — the union of the checker's `Theorems/Thm_*` sources and the
  declarations in `lean/FLTForHuman/`: **650 nodes / 268,456 raw `S_` lines**.
* **The EC-theory cluster in the Deligne–Serre forward cone**: **129 pin nodes /
  125,059 raw `S_` lines, 1 ported** — the set this scout's tables use.
* **The base theory is mathlib's, not the pin's.** The pin's `S_` files import
  `Mathlib.AlgebraicGeometry.EllipticCurve.*` directly; mathlib's elliptic-curve
  library is ~9,831 lines. The cluster is FLT's extension of it.
* **The rest of the `WeierstrassCurve.*` namespace is not this subject.** In the FLT
  root cone the namespace is 999 nodes / 371,410 lines (2 ported); the 893 nodes
  outside the D-S cone are dominated by the modularity-lifting / Tate-module /
  rational-endomorphism / Drinfeld material (`rationalHomSet`, `tateModule`,
  `galoisRep`, `fullKernelHom`, Hecke, newform; `DrinfeldGlobal` alone is 155 nodes).
  That is a different subject, not elliptic-curve theory.

Companions: [deligne-serre-weight-one-scout.md](deligne-serre-weight-one-scout.md) §4.2
(where the cluster surfaced), [flt-function-field-theory-and-mathlib.md](flt-function-field-theory-and-mathlib.md)
(the curve-layer survey), [../lean/logs/card-torsion-port.md](../lean/logs/card-torsion-port.md)
(the worked example of the mathlib-first method), [../math/005-card-torsion-p-squared.md](../math/005-card-torsion-p-squared.md)
and [../math/002-frey-curve-model-and-discriminant.md](../math/002-frey-curve-model-and-discriminant.md)
(the mathematics), [t-side-driver.md](t-side-driver.md) (the modularity-lifting
consumer), [basic-objects-ec-modular.md](basic-objects-ec-modular.md) (the object-form
taxonomy shared with modular curves and modular forms),
[velu-cluster-structure.md](velu-cluster-structure.md) (the Vélu block's two proof
spines and the redundancy-first planning method).

## 0. Scope

The cluster is the elliptic-curve theory proper: Weierstrass models and variable
changes, $`j`$ and the normal forms, the affine / projective / Jacobian point groups,
the function field / coordinate ring / places, torsion and division polynomials, the
Vélu isogeny and cyclic-quotient machinery, the Tate curve, and reduction /
semistability.

Two scopes are in play and must not be conflated:

* the **D-S forward-cone restriction** — 129 nodes / 125,059 lines, the elliptic row
  the D-S scout used to carry, and what §2 uses;
* the **full `WeierstrassCurve.*` / `TateCurve.*` namespace in the FLT root cone** —
  999 + 55 nodes / 400,440 lines, which is *not* one subject, because it also carries
  the modularity-lifting stack.

Conventions as in the D-S scout: "new nodes" is `frontier.py`'s
`needed(t) = closure(t) \ F` with a frontier node terminal, and "lines" is the sum of
the `S_` files of the needed nodes.

## 1. mathlib supplies the base; the cluster is the extension

This is the central fact for the port, and it is already recorded concretely in the
worked example [../lean/logs/card-torsion-port.md](../lean/logs/card-torsion-port.md).

mathlib v4.34.0's elliptic-curve library (~9,831 lines / 19 files) covers the general
theory:

| ingredient | mathlib module |
|---|---|
| `WeierstrassCurve`, coefficients, `b`/`c`/`Δ`/`j`, `IsElliptic` | `EllipticCurve/Weierstrass.lean` |
| `VariableChange` (a group) and its action, `variableChange_Δ`, `variableChange_j` | `…/VariableChange.lean` |
| normal forms `IsCharNeTwoNF`, `IsShortNF`, `IsCharThreeJNeZeroNF`, `IsCharTwoJNeZeroNF`, `IsCharTwoJEqZeroNF` + `exists_variableChange_is…NF` | `…/NormalForms.lean` |
| equal $`j`$ ⇒ isomorphic | `…/IsomOfJ.lean` |
| models realizing a given $`j`$ | `…/ModelsWithJ.lean` |
| affine / projective / Jacobian points and the group law | `…/Affine/Point.lean`, `…/Projective`, `…/Jacobian` |
| division polynomials `ψ`, `Ψ`, `ΨSq`, `Φ`, `φ` with degree/coeff facts | `…/DivisionPolynomial/{Basic,Degree}.lean` |
| elliptic divisibility sequences (`IsEllipticNet`, `atom`, `rel`, `normEDS`, `complEDS`) | `NumberTheory/EllipticDivisibilitySequence.lean` |
| reduction: `IsIntegral`, `IsMinimal`, `HasGoodReduction`, mult/add/split | `…/Reduction.lean` |

The pin builds on exactly this: `S_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div.lean`
imports `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`, `…Jacobian.Point`,
`…DivisionPolynomial.Basic`, `…DivisionPolynomial.Degree` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence`. So the port should **import
mathlib's EC stack** and transcribe only the extensions.

What mathlib v4.34.0 does **not** have, and the cluster adds:

| gap | example pin nodes |
|---|---|
| Legendre and Deuring normal forms | `exists_variableChange_eq_legendreCurve_of_isUnit_two`, `exists_variableChange_eq_deuring_of_isUnit_three` |
| the `VariableChange` stabiliser and the automorphism-group counts | `finite_stabilizer_variableChange`, `natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728` |
| the char-2 / char-3 automorphism groups | `exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two`, `exists_addMonoidHom_i_tau_vcInvFun_of_char_three` |
| variable change as a map on points (`vcInvFun`) | `Affine.Point.vcInvFun_add` |
| the division-polynomial **point** formulas | `Affine.Point.zsmul_some_eq_some_div` ($`x(nP)=Φ_n/Ψ_n^2`$), `Affine.Point.smul_some_eq_zero_iff` ($`nP=O ⇔ ψ_n(P)=0`$) |
| divisibility of $`E(K)`$ for algebraically closed $`K`$ | `Affine.Point.exists_zsmul_eq_of_isAlgClosed` |
| an alg-equiv of function fields from a variable change | `nonempty_functionField_algEquiv_of_variableChange` |
| inertia-equivariant good reduction | `exists_inertia_equivariant_reduction_of_variableChange_eq_map` |
| Vélu isogenies / cyclic quotients / modular polynomial | the 49-node Vélu block |
| the Tate curve (analytic parametrisation) | the 23-node `TateCurve.*` block |

**The card-torsion port is the template.** For
`WeierstrassCurve.card_torsion_of_isAlgClosed` it kept mathlib's `Submodule.torsionBy`,
the division polynomials and `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`;
it re-derived FLT's EDS core from mathlib's `atom`/`atomRel`/`rel`/`normEDS`/`complEDS`
rather than copying the pin's ~950-line engine; and it ported only the genuine gap —
the multiplication bridge plus the `ω` polynomial / reduced invariants mathlib dropped
after v4.30 — for 13 modules / 3,362 lines, dropping the pin's
`Def_Compat_Mathlib430.lean` (340 lines, 197 importers) outright. The result is in
`FLTForHuman/Elliptic/`.

**Version gap.** The pin is Lean `v4.33.1` / mathlib `db584cd6…`; the port is Lean
`v4.34.0` / mathlib `v4.34.0`. The base API is present, but pin proofs written against
the older release need adaptation (`Def_Compat_Mathlib430.lean` is exactly such a
shim, and the port drops it).

## 2. The cluster in the D-S cone

129 pin nodes / 125,059 `S_` lines, 1 ported. Unit split (namespace/token classifier,
§6; reduction is tested before the other units, so an inertia statement named
`…variableChange…` counts as reduction):

| unit | nodes | `S_` lines | ported |
|---|---:|---:|---:|
| Vélu isogeny / cyclic quotient / modular polynomial | 49 | 91,772 | 0 |
| Weierstrass function field / coordinate ring / places | 20 | 15,771 | 0 |
| torsion / division polynomials / Drinfeld | 13 | 4,247 | 1 |
| other (genus-one closure) | 4 | 4,215 | 0 |
| models / group law / variable change / $`j`$ | 13 | 3,097 | 0 |
| reduction / semistability / modularity data | 6 | 2,993 | 0 |
| Tate curve: analytic parametrization | 23 | 2,749 | 0 |
| formal group / EDS / special invariants | 1 | 215 | 0 |
| **total** | **129** | **125,059** | **1** |

The one ported node is `WeierstrassCurve.card_torsion_of_isAlgClosed` (1,335 lines),
in the torsion unit — the card-torsion port of §1, living in `Elliptic/`.

**The Vélu block is the cluster.** 49 nodes / 91,772 lines — 73% of the cluster's
lines in 38% of its nodes. Its six largest statements
(`velu_map_equation_of_oddOrderSummingSet` and `…_of_isAlgClosed`,
`IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong`,
`exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq` and `…_of_isAlgClosed`,
`IsogenyEndDatum.exists_restrictAlong_placeOfPoint_eq_add`) are 60,586 lines — 66% of
the block — and the top ten are 86%. They are Mazur-type cyclic-isogeny classification
through the `Affine.FunctionField`/place gate and the `IsogenyEndDatum`/
`IsogenyHomDatum` endomorphism data, not the explicit Vélu formulas. Several of the
biggest occur in near-duplicate pin variants (`velu_map_equation_of_oddOrderSummingSet`
and `…_of_isAlgClosed`; `exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq` and
`…_of_isAlgClosed`), so the pooled `port_advise` method of §6 is how to price the block.

**The models / group law / variable change / $`j`$ unit.** 13 nodes / 3,097 lines, in
four sub-themes:

* normal forms and $`j`$ — Legendre (274), Deuring (213), $`j`$-transcendence (156);
* the variable-change stabiliser — `finite_stabilizer_variableChange` (285) and the two
  `natCard_stabilizer…` counts (256, 187);
* the char-2 / char-3 automorphism groups — 988 + 424;
* the point-map and group-law facts — `Affine.Point.vcInvFun_add` (188), the
  collinear-triple and flex nodes (40, 34), the two scaling stabilisers (26, 26).

Not one of them is a mathlib restatement (§1); they are the Frey-side extension.

## 3. Consumers and dependency shape

The cluster has **401 out-of-D-S-cone consumers** in the FLT root cone, through the
modularity-lifting tower and the modular-curve side:
`CuspForm.heckeLocal.exists_patchingDatum_of_isResiduallyModular_…`,
`WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add`,
`ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ`, the `TateCurve.ks17_*`
exports, and `CerednikDrinfeld`. None of the 129 nodes lies in any of the pin's 49
landmark cones — the cluster is deep substrate, a prerequisite mass rather than a
landmark-shared one, so no landmark-share column is useful here.

The definition layer is large and only partly new: the pin's 72
`Def_WeierstrassCurve_*` / `Def_EllipticCurve_*` modules total 20,740 lines, but only
the extension vocabulary (Vélu, `ProjModel`, EDS/`ω`, cyclic quotients, `ReductionMap`,
`Semistability`, `FrobeniusTrace`, …) is genuinely new; the base curve,
variable-change, point and division-polynomial definitions are mathlib's.

## 4. Port order and homes

1. **Models / group law / variable change / $`j`$** (13 nodes / 3,097 lines). Import
   mathlib's `WeierstrassCurve`/`VariableChange`; the normal forms, stabiliser counts
   and char-2/3 automorphisms are the extension. Home `WeierstrassCurve/` for the
   model / variable-change / normal-form material, alongside the existing
   `WeierstrassCurve/{Defs/FreyPackage,Defs/Modularity,ModularityLifting}.lean`.
2. **Function field / coordinate ring / places** (20 / 15,771). Needs the ported
   `AlgebraicCurve` place vocabulary; the `Affine.FunctionField`/`placeOfPoint` gate.
3. **Tate curve** (23 / 2,749). Depends on `AlgebraicCurve`'s annulus and residue
   material, not on the Weierstrass classification. Home `TateCurve/` (not yet created).
4. **Explicit Vélu formulas** — the computable part of the 49-node block
   (`velu_map_equation_*`, `veluQuotient_*`, the `OddOrderSummingSet` special cases).
5. **The cyclic-kernel / place classification block** — the concentrated, expensive
   part; pool it with `port_advise` before transcribing. The measured factoring,
   the general/plain sibling rule and the phased order are in
   [../lean/topics/velu/TOPIC-port-plan.md](../lean/topics/velu/TOPIC-port-plan.md)
   (91,442 raw → **39,986 net new** lines; `tools/deps/port_plan.py` turns the
   ~105 kB `port_advise` report into a plan).

## 5. Redundancy discipline

* **Check mathlib first** (playbook §2.4). The template is
  [../lean/logs/card-torsion-port.md](../lean/logs/card-torsion-port.md): name what
  mathlib already has, re-derive the EDS layer from mathlib's `atom`/`rel`/`normEDS`,
  and port only the genuine gap. Expect the same shape in the other units.
* **Run `port_advise.py` on a slice before transcribing** — in particular the Vélu
  block, where the pin repeats near-duplicate file variants.
* **Watch the v4.34.0 API drift.** The pin targets `v4.33.1`; the port drops the
  340-line `Def_Compat_Mathlib430.lean` shim and adapts proofs at the seam.
* **One home per piece.** `Elliptic/` for EDS / division-polynomial / torsion,
  `WeierstrassCurve/` for models / variable-change / normal forms, `TateCurve/` for the
  Tate curve.

## 6. Reproduce

```bash
cd tools/deps
python3 frontier.py --selfcheck | tail -1

# the cluster in the D-S forward cone, by unit
python3 - <<'PY'
import frontier, re
from collections import defaultdict
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
ds = fr.closure(pay.pid('DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen'))
def bucket(q):
    if q.startswith('TateCurve.'): return 'Tate curve'
    s = q.split('.', 1)[1]
    if re.search(r'reduceHom|ReduceHom|[Rr]eduction|goodModel|inertia|Semistab|semistab|Conductor|PeuRamifiee|Modularity|ThreeFive|Mlc1|FrobeniusCard|isGalois', s): return 'reduction'
    if re.search(r'[Vv]elu|cyclicQuotient|cyclicKernels|isAddCyclic|IsogenyEnd|IsogenyHom|pointMapOfPushforward|pointHom|dualEndData|stepCurve|OddOrderSummingSet|isOddVeluSet|ker_pointMap|veluFunctionFieldHom|veluPointHom|veluQuotient|velu_map_equation|veluGx|velu2|zmultiples_eq_of_veluQuotient|Delta_eq_veluGx', s): return 'velu'
    if re.search(r'torsion|Torsion|DivPoly|divPoly|evalEval_psi|KernelPolynomial|KernelIdeal|FullKernel|Drinfeld|zsmul_some|smul_some_eq_zero|exists_zsmul_eq', s): return 'torsion'
    if re.search(r'FunctionField|functionField|placeOfPoint|PlaceGate|hasPrincipalDivisors|valuationSubring|CoordinateRing|XYIdeal|adjoin_yCoord|finiteDimensional_ratFunc|isDedekindDomain|GenusOnePlace', s): return 'function field'
    if re.search(r'FormalGroup|EDSEngine|Hasse|RatPoint|RationalEnd|exists_isUnit_mul_pow_eight|exists_valuationSubring_with_transcendental', s): return 'formal'
    if re.search(r'ProjModel|AddFormula|Third|PointChart|SectionAtOrigin|MapPoint|PointAddEquiv|VariableChange|variableChange|Legendre|Deuring|j_eq|j_perturb|jInvariant|vcInvFun|Point\.|exists_addMonoidHom_i_tau|exists_addMonoidHom_vcInvFun', s): return 'models'
    return 'other'
g = defaultdict(lambda: [0, 0, 0])
for i in ds:
    q = pay.qual(i)
    if not q.startswith(('WeierstrassCurve.', 'TateCurve.')): continue
    b = bucket(q); g[b][0] += 1; g[b][1] += pay.lines(i); g[b][2] += 1 if i in front else 0
for b, (n, L, p) in sorted(g.items(), key=lambda kv: -kv[1][1]):
    print(f'{b:16} {n:4} {L:8} ported={p}')
PY

# the full namespace scope
python3 - <<'PY'
import frontier
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
flt = fr.closure(pay.pid('FLT.fermatLastTheorem'))
for pref in ('WeierstrassCurve.', 'TateCurve.'):
    ns = [i for i in flt if pay.qual(i).startswith(pref)]
    print(pref, len(ns), pay.total_lines(ns), 'ported', sum(1 for i in ns if i in front))
PY

# price a slice before transcribing
python3 - <<'PY' > build/velu_nodes.txt
import frontier, re
fr = frontier.Frontier(); pay = fr.pay; front = fr.frontier('union')
ds = fr.closure(pay.pid('DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen'))
rx = re.compile(r'[Vv]elu|cyclicQuotient|cyclicKernels|isAddCyclic|IsogenyEnd|IsogenyHom|OddOrderSummingSet|ker_pointMap|veluFunctionFieldHom|veluQuotient|velu_map_equation')
print(','.join(pay.qual(i) for i in ds
               if i not in front and pay.qual(i).startswith('WeierstrassCurve.')
               and rx.search(pay.qual(i).split('.', 1)[1])))
PY
python3 port_advise.py --nodes "$(cat build/velu_nodes.txt)" --json build/velu_advise.json
```
