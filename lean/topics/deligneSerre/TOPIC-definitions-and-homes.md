# Work order — phase D (definitions) and phase H (home blocks)

**Status: work order, not started (2026-09-29).** The definition layer and the
factor-out blocks for the 54-node unconditional slice. Read
[TOPIC-port-order.md](TOPIC-port-order.md) first; the theorem modules are in
[TOPIC-theorem-order.md](TOPIC-theorem-order.md).

Pinned at `aa2d8b3`; the port's mathlib is `v4.34.0`. Line counts are pin lines.

## 1. Phase D — the definition layer

The 54 theorem nodes touch **20 definition modules / 2,752 pin lines**, and the
import DAG among them has **four levels** (computed from their `Definitions/`
import edges). Port one level per dispatch, in this order.

| level | module | lines | status | home |
|---|---|---:|---|---|
| D0 | `Def_ModularForm_HeckeOperator` | 204 | **ported** (PORTING-Hecke) | `ModularForms/Defs/HeckeOperator.lean` |
| D0 | `Def_FLTPrelim_Ramification` | 52 | **ported** | `GaloisRep/Defs/Ramification.lean` |
| D0 | `Def_FLTPrelim_Modularity` | 106 | **half ported** — reuse `ModularFormClass.qCoeff`/`IsNormalizedEigenform`; port any missing block | `ModularForms/` |
| D0 | `Def_Deformations_MatrixRepresentation` | 23 | new | `GaloisRep/Defs/MatrixRepresentation.lean` |
| D0 | `Def_EisensteinSeries_WeierstrassZeta` | 14 | new | `ModularForms/Eisenstein/WeierstrassZeta.lean` |
| D0 | `Def_FieldTheory_RatAlgClosureGalois` | 7 | new | `FieldTheory/RatAlgClosureGalois.lean` |
| D0 | `Def_Gamma0Away` | 147 | new | `ModularCurve/Defs/Gamma0Away.lean` |
| D0 | `Def_IharaIota` | 188 | new | `ModularCurve/Defs/IharaIota.lean` |
| D0 | `Def_RepTheory_BrauerNesbitt_TraceCharZero` | 453 | new | `Algebra/BrauerNesbitt.lean` |
| D0 | `Def_TaylorWiles_Primes` | 106 | new | `NumberTheory/FrobeniusDensity/TaylorWilesPrimes.lean` |
| D1 | `Def_ModularForm_HeckeOperator` → `Def_CuspForm_Gamma1HeckeOperators` | 680 | **half ported** — the Γ₁/diamond layer is `ModularForms/Level/Diamond.lean` (PORTING-Level SET-2); port only the remainder | `ModularForms/` |
| D1 | `Def_FLTPrelim_Modularity` → `Def_CuspForm_PrimitiveFormGamma1` | 72 | new | `ModularForms/Defs/PrimitiveFormGamma1.lean` |
| D1 | `Def_FLTPrelim_Ramification` → `Def_EllipticCurve_FrobeniusTrace` | 66 | **ported** | `GaloisRep/Defs/FrobeniusTrace.lean` |
| D1 | `Def_TaylorWiles_Primes` → `Def_FrobeniusDensity_DegOneAsymptotic` | 44 | new | `NumberTheory/FrobeniusDensity/DegOneAsymptotic.lean` |
| D1 | `Def_IharaIota` → `Def_IharaAmalgam` | 98 | new | `ModularCurve/Defs/IharaAmalgam.lean` |
| D2 | `Def_FrobeniusDensity_DegOneAsymptotic` → `Def_FrobeniusDensity_BadPrimes` | 126 | new | `NumberTheory/FrobeniusDensity/BadPrimes.lean` |
| D2 | `Def_EllipticCurve_FrobeniusTrace` + `Def_FLTPrelim_Ramification` → `Def_GaloisRep_FrobeniusPowerDense` | 13 | new | `GaloisRep/Defs/FrobeniusPowerDense.lean` |
| D2 | `Def_EllipticCurve_FrobeniusTrace` + `Def_FLTPrelim_Modularity` → `Def_GaloisRep_Residual` | 105 | **ported** | `GaloisRep/Defs/Residual.lean` |
| D2 | `Def_Gamma0Away` + `Def_IharaAmalgam` → `Def_IharaAmalgamMap` | 153 | new | `ModularCurve/Defs/IharaAmalgamMap.lean` |
| D3 | `Def_FrobeniusDensity_BadPrimes` → `Def_FrobeniusDensity_PrimeSums` | 95 | new | `NumberTheory/FrobeniusDensity/PrimeSums.lean` |

**Reuse first.** Before writing any D0 module, confirm what is already on disk
(`ModularForm_HeckeOperator`, `FLTPrelim_Modularity`'s `qCoeff` half,
`FLTPrelim_Ramification`, `EllipticCurve_FrobeniusTrace`, `GaloisRep_Residual`, and
the Γ₁/diamond half of `CuspForm_Gamma1HeckeOperators`). The new definition lines
are **~1,600–2,000**; the rest is reuse.

**Discipline.** Definitions are transcribed with their statements verbatim from the
pin's `Definitions/`; run the statement checker after each level. A definition file
is closed once green.

## 2. Phase H1 — factor-out blocks into new homes

The 54 targets repeat their private preludes; `port_advise` reports **78 shared
blocks / 585 removable lines** inside the slice. Give each block **one home in a
new file** (new files touch no existing module, so no cascade). The four homes,
with the largest blocks:

| home (new file) | shared blocks (removable lines) |
|---|---|
| `ModularForms/Eisenstein/Cotangent.lean` | `norm_pi_cot_add_le` (44), `pi_cot_add_eq` (24), `norm_pi_cot_sub_le` (18), `norm_cexp_two_pi_I` (10), `add_intCast_mul` (9) |
| `NumberTheory/FrobeniusDensity/Basic.lean` | `sum_moebius_mem_zpowers` (39), `mem_zpowers_pow_div_iff` (30), `tsum_normFiber` (22), `isBigO_sum_of_tendsto_div` (20), `exists_pow_coprime_eq_of_orderOf_eq` (19), `ncard_conj_mem_eq_card_mul_ncard` (16), `tendsto_sum_idealCount_div` (15), `card_le_of_forall_pow_eq` (14), `ncard_eq_sum_indicator` (14), `primeSum_le_idealSum` (14), `toReal_term` (10), `term_eq_ofReal_zetaTerm` (9) |
| `GaloisRep/Prelude.lean` | `finite_range_of_factorsThroughFiniteLevel` (28) |
| `ModularForms/HeckePrelude.lean` | `periodic_of_slash_T` (22), `mdifferentiable_heckeU` (16×5), `heckeDiagMatrix_mul_T` (12), `periodic_smul` (9×7), `isBoundedAtImInfty_heckeU` (9×4) |

The rest of the 78 are small (≤ 8 lines) and are handled by the adapter rule: an
adapter used by one consumer stays `private` in that consumer (playbook §9); only a
block used by ≥ 2 consumers is promoted. Re-read the advice before each home:

```bash
cd tools/deps
python3 port_advise.py --nodes "$(paste -sd, build/groupA_nodes.txt)" --json build/groupA_advise.json
```

## 3. Phase H2 — promotions and reconciliations in existing files

This is the cascade phase. Do it in one pass, after H1, with a full `lake build`.

| action | count | files |
|---|---:|---|
| promote a port-**private** copy so it can be imported | 7 | `ModularForms/WeightOne/Gamma0Rationality.lean`, `ModularForms/Defs/HeckeRepresentatives.lean` |
| reconcile a name the port already defines, with a different statement | 22 (5 binder-only) | `ModularForms/Level/Diamond.lean`, `ModularForms/Defs/HeckeRepresentatives.lean`, `ModularForms/WeightOne/{Gamma0Rationality,Gamma0Integral,Gamma1IntegralBasis}.lean`, `ModularForms/WeightOne/Defs/{GammaRational,RatAt}.lean`, `ModularForms/HeckeAnalytic.lean`, `ModularCurve/Analytic/Gamma0Cosets.lean`, `Reserve/ModularCurve/Analytic/LevelTauBridge.lean` |
| extend an existing home that must grow | as needed | `NumberTheory/FrobeniusAtPlace.lean` (already ports the `ValuationSubring.exists_isFrobeniusAt_*` family; the `_algebraicClosure_rat` variants are new) |

A **binder-only** clash takes the pin wrapper's binders (playbook §7.4); a genuine
clash is generalised, not copied twice. The 7 promotions are the port-private
statements `locKer`, `heckeDiagMatrix_mul_of_eq`/`_of_eq'`,
`heckeMatrix_mul_of_eq`/`_of_eq'`, `heckeU_eq_sum_zmod`, `redMatrix` (re-read the
exact list from the JSON before acting).

After this phase those files are **closed** — later work must not edit them.

## 4. Closing a step

- `timeout 120 lake build <module>` green, no `sorry`/`admit`;
- statement checker 0 mismatched / 0 missing for the step's files;
- `#print axioms` clean on the headlines;
- friction entries appended for anything resolved locally.
