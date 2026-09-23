# Coverage: how much of `ModularCurve.heckeOperatorsCommuteBar` is ported

Measured report, 2026-09-23, after the `AlgebraicCurve` port closed. Companion to
[hecke-commute-bar-survey.md](hecke-commute-bar-survey.md) (the mathematical survey
of the same theorem) and to the two process records
[ac-retrospective.md](../lean/topics/ac-retrospective.md) and
[ffg-retrospective.md](../lean/topics/ffg-retrospective.md). It answers one
question with numbers: **what fraction of `math/009`'s theorem is now ported, and
what exactly is left.**

Everything is read from the local clone `~/proj/fermats-last-theorem` pinned at
`aa2d8b3`; all citations are public URLs at that sha. Conventions are those of
[../AGENTS.md](../AGENTS.md).

## 0. What is measured, and how

The target is one Lean theorem
([`Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean`, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean#L9)),
but the mathematics is its **transitive citation cone**: every `S_` node the proof
reaches. The report partitions that cone into three parts:

- **ported** — a node whose `Theorems/Thm_<name>.lean` wrapper is listed in the
  port's statement checker (`lean/spec/check_flt_statements.py`, `SOURCES`) and
  therefore diffed against the pin; or whose declaration name appears in the port
  tree `FLTForHuman/`;
- **the `AlgebraicCurve` slice** — the 65 nodes of the third port
  ([../lean/topics/PORTING-AC.md](../lean/topics/PORTING-AC.md)), reported
  separately because it is the newest and because it is the *generic* half;
- **remaining** — everything else.

`raw` is the whole `S_` file; `content` excludes imports, `attribute` lines,
namespace/`section`/`variable` lines, `p2m_*` lines, comments and blanks. The
reproduction recipe is in §7.

**The measurement is an upper bound on what is left, and the reason is honest:** it
is name-based. A node counts as ported if its wrapper is checked or its last name
occurs anywhere in the port. It therefore will *not* notice a remaining node that
is implied by a differently-named ported theorem (and, symmetrically, could miss a
port that renamed a declaration). Two of the remaining slices have exactly that
shape (§5), so read the 82-node figure as "at most 82".

## 1. The headline

The full cone of `ModularCurve.heckeOperatorsCommuteBar`:

| | nodes | raw lines | content lines |
|---|---|---|---|
| full closure | 225 | 42,099 | 30,559 |
| **ported** | **143 (64%)** | **31,530 (75%)** | **22,980 (75%)** |
| — of which the `AlgebraicCurve` slice | 65 | 5,423 | 3,535 |
| — of which earlier ports and shared vocabulary | 78 | 26,107 | 19,445 |
| **remaining** | **82 (36%)** | **10,569 (25%)** | **7,579 (25%)** |

Two readings of the same fact, and they matter differently:

- **By nodes, 36% is left**, which sounds like a third of the theorem.
- **By content, only 25% is left**, and it is concentrated in one analytic cluster
  (§4). The earlier ports took the deep but reusable half of the stack
  (`functionFieldGeneration`, the Φ_p existence/degree theory, the R1 q-expansion
  analysis); the `AlgebraicCurve` port took the generic algebra.

What is *not* in this table is the fourth `math/009` slice named in
[PORTING-AC §0](../lean/topics/PORTING-AC.md): the **`ModularCurve` Hecke layer**,
which is part of the remaining 82 — it is the theorem's own construction, not a
generic input.

## 2. What is ported, and where

| pin cone | port modules | record |
|---|---|---|
| the function field of `X₀(N)` inside `ℚ((q))`: `qExpand`, `coeffMap`, `jq`, `qTwist`, `modularFunctionField(Full)`, `TS`, `qExpandAlgC` | `lean/FLTForHuman/ModularCurve/Defs/*` | [logs/ffg-port.md](../lean/logs/ffg-port.md) §0–§1 |
| `functionFieldGeneration` — every `j(q^d)`, `d ∣ N`, lies in `ℚ(j, j(q^N))`, unconditional | `ModularCurve/FunctionFieldGeneration/*` (+ `FieldTheory/CommonRoot.lean`) | [ffg-retrospective.md](../lean/topics/ffg-retrospective.md) |
| the Φ_p cone: `exists_phiIrreducible`, `splits_prime_at_slot`, `modularPolynomialFamily`, `ModularPolynomialData`, `eq_of_prime`, the degree `finrank_adjoin_jqN_eq_of_prime` | `ModularCurve/PhiGen*`, `ModularPolynomial*`, `JqCoefficients`, `JqCoeffPositivity` | [logs/phiGen-port.md](../lean/logs/phiGen-port.md) |
| the R1 / analytic q-expansion input: `QExpansionPrinciple`, `JqAnalyticModel`, `Hauptmodul`, `PhiGenDescends`, `HeckeQExpansion` | `ModularForms/*` | [logs/phiGen-port.md](../lean/logs/phiGen-port.md) |
| **the generic curve layer**: `Place`, `Divisor`, `Pic0`, push/pull, the correspondence API, the Weil exchange, `HasPrincipalDivisors` by norms | `AlgebraicCurve/Defs/*`, `WeilExchange/*`, `PrincipalDivisors/*`, `FieldTheory/FiniteGroupAction.lean` | [ac-retrospective.md](../lean/topics/ac-retrospective.md), [logs/ac-port.md](../lean/logs/ac-port.md) |

## 3. The four moves of `math/009`, mapped

`math/009` §1–§5 describes the construction stack in four moves. Their status is:

| note | Lean move | status |
|---|---|---|
| §1 | `X₀(N)` as a field in `ℚ((q))`; `modularFunctionFieldFull`, and the collapse `functionFieldGeneration` | **ported** (unconditional) |
| §2 | the Jacobian as a divisor class group: `Divisor`, `Pic0`, `HasPrincipalDivisors` | **ported** |
| §3–§4 | degeneracy maps, `T_ℓ = α_ast ∘ β^ast`, the roof square, `heckeOperatorsCommuteBar_of_heckeExchangeAt` | **remaining** (the Hecke layer) |
| §4 step 3 | the general exchange lemma `Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong` | **ported** (T7) |
| §4 step 4 | roof generation `heckeRoof_adjoin_range_union_eq_top`; degree `finrankAlong_towerSubstBar_comp_heckeAlphaBar` | **remaining**, but both inputs are ported |
| §5 | `hasPrincipalDivisors_modularFunctionFieldBar` | **remaining, nearly free** (§5) |
| §5 | `modularPolynomialFamily` / `ModularPolynomialData` | **partly ported** (existence, splitting, degree at a prime); the squarefree/analytic tail remains |

## 4. The remaining 82 nodes, by slice

The classification below is by declaration vocabulary, from the measured remaining
set.

| slice | nodes | raw | content | representative remaining nodes |
|---|---|---|---|---|
| **analytic q-expansion / R1 / Fricke** | 26 | 4,967 | 3,731 | `coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant` (1,155), `mem_modularFunctionField_of_hasSum_of_gamma0_invariant` (870), `isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant` (870), the `hasSum_modularUnitSeries_{,inv_}qParam` cluster (258–325 each), `qParam_coeff_unique` (158), `eq_cuspInftyBar_or_eq_cuspZeroBar` (236) |
| **Hecke layer / tower / operators** | 23 | 2,007 | 1,386 | `DegeneracyTower`, `heckeAlphaBar`/`heckeBetaBar`/`towerInclBar`/`towerSubstBar`, `heckeSquareBar_commutes`, `HeckeExchangeAt`, `heckeExchangeAt_of_WEX`, `heckeInputsAll`, `heckeOperatorsCommuteBar_of_heckeExchangeAt`, `HeckeOperatorsCommuteBar`, the leg integrality/finiteness lemmas |
| **roof generation + degree** | 5 | 1,643 | 1,226 | `finrankAlong_towerSubstBar_comp_heckeAlphaBar` (610), `heckeRoof_adjoin_range_union_eq_top` (571), `relfinrank_qExpand_full` (794), `relfinrank_laurentBaseChange` (342), `finrank_adjoin_jqNModC_eq_of_prime` (275) |
| **Φ squarefree / degree tail** | 11 | 1,534 | 1,012 | `nonempty_modularPolynomialData_of_squarefree` (513), `finrank_adjoin_jqN_eq_of_squarefree`-style API, `exists_isFrickeAut_of_modularPolynomialData` (299), `exists_perm_gamma0_cosetReps` (134) |
| **principal divisors** | 2 | 82 | 38 | `hasPrincipalDivisors_modularFunctionFieldBar`, `hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull` |
| **glue** | 15 | 336 | 186 | `laurentBaseChange_modularFunctionField(Full)`, `coeffEmb_jq`/`coeffEmb_jqN`, `order_qExpand`, cusp bookkeeping |

Read as two theories plus corollaries:

1. **The `ModularCurve` Hecke layer** (Hecke + roof + glue ≈ 43 nodes, ≈ 2.6k
   content). Construction and bookkeeping on top of the already-ported FFG
   vocabulary, plus the ported exchange lemma. The named risks of the *generic*
   half are gone; what remains is modular-specific instance work.
2. **The analytic input** (analytic + Φ tail ≈ 37 nodes, ≈ 4.7k content). The
   modular-form q-expansion / Fricke / cusp cluster that supplies
   `modularPolynomialFamily` and the roof's generation and degree facts. This is
   the part mathlib has nothing for.

## 5. What the `AlgebraicCurve` port bought for the remainder

Three concrete reductions, all because the AC layer is generic and unconditional:

- **`HeckeExchangeAt` is discharged by the capstone.** The pin's glue
  `heckeExchangeAt_of_WEX`
  ([`S_ModularCurve_heckeOperatorsCommuteBar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorsCommuteBar.lean))
  applies `AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`
  to the roof square; the Hecke layer's job is therefore the roof *statement* and
  its two field-theoretic hypotheses, not the exchange. The same AC lemma is
  applied at high indegree from ModularCurve files outside this theorem's cone
  (`JH_pullbackAlongHom_heckeOperatorHAlong…`, `JOne_degeneracyPullbackPair…`,
  `correspondence_heckeAlphaC_heckeBetaC…`), which is the library dividend the
  blueprint predicted.
- **`hasPrincipalDivisors_modularFunctionFieldBar` is nearly a corollary.** Its
  wrapper
  ([`Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean))
  is `(hΦ : ModularPolynomialFamily) (N) : HasPrincipalDivisors (AlgebraicClosure ℚ)
  (modularFunctionFieldBar N)` — i.e. it takes the modular-equation data as a
  hypothesis and asks only for the principal-divisors property. With the ported
  `hasPrincipalDivisors_of_transcendental`
  ([`PrincipalDivisors/Transcendence.lean`](../lean/FLTForHuman/AlgebraicCurve/PrincipalDivisors/Transcendence.lean)),
  `transcendental_jq`
  ([`Defs/Jq.lean`](../lean/FLTForHuman/ModularCurve/Defs/Jq.lean#L189)), and
  finite-dimensionality over `K(jq)`, its 38 content lines should collapse to a
  short application. The blueprint's risk 10 — *keep the statement generic in `K`,
  do not specialise to `AlgebraicClosure ℚ`* — is exactly what makes this possible.
- **The roof facts have ported inputs.** Generation needs
  `Φ_ℓ(j, j_ℓ) = 0` and integrality of `j(q^{ℓ'})` over the intermediate field;
  the degree needs `[ℚ(j, j(q^n)) : ℚ(j)] = ψ(n)`. The first is the Φ_p port's
  `splits_prime_at_slot`/`irreducible`, the second its
  `finrank_adjoin_jqN_eq_of_prime` and the Φ-squarefree API. So the two `math/009`
  §4-step-four nodes are now *assembly* over ported inputs, not new mathematics.

## 6. Where the remaining risk is, and a rough price

- **Cheapest first milestone:** the principal-divisors slice (§5). It is one
  corollary, and it closes one of `math/009` §5's two named inputs.
- **The Hecke layer proper** (≈43 nodes, ≈2.6k content) is construction against an
  already-ported vocabulary: `DegeneracyTower`'s four embeddings, the
  `heckeAlphaBar`/`heckeBetaBar` correspondences, `heckeSquareBar_commutes` (a
  `rfl`-level square, per `math/009` §4), the predicate `HeckeExchangeAt`, and the
  reduction `heckeOperatorsCommuteBar_of_heckeExchangeAt`. This is the same *kind*
  of work SET 1 did, and its one-time shape decisions (the `Algebra`/`IsScalarTower`
  instances on the tower) are already fixed by AC0's `algebraAlong` design.
- **The expensive cluster is the analytic input** (≈37 nodes, ≈4.7k content): the
  Fricke/cusp and `hasSum_modularUnitSeries` analysis. mathlib has no modular-form
  q-expansion theory, so this is genuine analysis, and it is where a fourth port
  would spend most of its shape-risk budget. The Φ_p effort has already done the
  analogous work once, so the *route* is known; only the statements are unported.

At the `AlgebraicCurve` effort's measured adaptation ratios (module lines ÷ content
lines ≈ 1.0–1.3), the ≈7.6k remaining content lines price at roughly **8k–10k
written lines** — about 1.5–2× the `AlgebraicCurve` effort — with the standing
caveat that line count is not effort and the analytic cluster is the least
predictable piece. If the effort were stopped early, the natural stopping point is
after the Hecke layer, with the analytic input bundled as `hΦ` — exactly the shape
the pin's `hasPrincipalDivisors_modularFunctionFieldBar` already has.

## 7. Reproduction

The graph reader is the one the other studies use (`tools/deps`; the notes'
convention, e.g. [flt-ffg-field-theory.md](flt-ffg-field-theory.md) §reproduction).

```bash
cd tools/deps && python3 - <<'PY'
import sys, re
from pathlib import Path
sys.path.insert(0, '.')
from fltdata import FltData
d = FltData(); FLT = Path.home() / 'proj' / 'fermats-last-theorem'
LEAN = Path('../../lean')   # the port tree, relative to tools/deps

def closure(i):
    seen, stack = set(), [i]
    while stack:
        j = stack.pop()
        if j in seen: continue
        seen.add(j); stack.extend(d.cites(j))
    return seen

cl = closure(d.index['ModularCurve.heckeOperatorsCommuteBar'])
sc = re.compile(r'^\s*(import |attribute |namespace |end\b|open |p2m_open|p2m_export|p2m_alias|p2m_reactivate|section\b|variable\b|#|/-|--|\s*$)')
def raw(i):  return sum(1 for _ in open(FLT / f"P2M/Sol/S_{d.stem_of[i]}.lean", encoding='utf-8'))
def cont(i): return sum(1 for l in open(FLT / f"P2M/Sol/S_{d.stem_of[i]}.lean", encoding='utf-8') if not sc.match(l))

port = "\n".join(p.read_text(encoding='utf-8') for p in (LEAN / 'FLTForHuman').rglob('*.lean'))
src = re.search(r'SOURCES = \[(.*?)\n\]', (LEAN / 'spec/check_flt_statements.py').read_text(), re.S).group(1)
srcs = set(re.findall(r'"([^"]+)"', src))
def ported(q):
    if any(s.endswith('Thm_' + q.replace('.', '_') + '.lean') for s in srcs): return True
    return re.search(r'(?<![\w.])' + re.escape(q.rsplit('.', 1)[-1]) + r'(?![\w])', port) is not None

rem = [n for n in cl
       if not d.qual(n).startswith(('AlgebraicCurve.', 'Polynomial.'))
       and d.qual(n) not in ('MulAction.ncard_orbit_inter_orbit_mul_card', 'Subgroup.exists_eq_mul_of_index_inf_eq')
       and not ported(d.qual(n))]
print(f"closure {len(cl)} nodes, {sum(raw(n) for n in cl)} raw, {sum(cont(n) for n in cl)} content")
print(f"remaining {len(rem)} nodes, {sum(raw(n) for n in rem)} raw, {sum(cont(n) for n in rem)} content")
for n in sorted(rem, key=lambda n: -raw(n))[:30]:
    print(f"  {raw(n):5d} raw {cont(n):5d} c  {d.qual(n)}")
PY
```

Line numbers and paths above are against `anthropics/fermats-last-theorem@aa2d8b3`;
mathlib is the project's pinned `v4.34.0`.

## 8. Pointers

- [hecke-commute-bar-survey.md](hecke-commute-bar-survey.md) — the mathematical
  survey of the same theorem (the reduction chain, the two degeneracy maps, the
  local bifibre identity, and §9's list of what the note must not claim).
- [../math/009-hecke-jacobian-commute.md](../math/009-hecke-jacobian-commute.md) —
  the note this report measures the distance to.
- [../lean/topics/PORTING-AC.md](../lean/topics/PORTING-AC.md) — the retired
  `AlgebraicCurve` blueprint, including §0's slice table.
- [../lean/topics/ac-retrospective.md](../lean/topics/ac-retrospective.md) and
  [ffg-retrospective.md](../lean/topics/ffg-retrospective.md) — the two closed
  efforts' reviews.
- [../lean/spec/AlgebraicCurveConsumer.lean](../lean/spec/AlgebraicCurveConsumer.lean)
  — the consumer that fixes the AC interface (Zones A–J).
