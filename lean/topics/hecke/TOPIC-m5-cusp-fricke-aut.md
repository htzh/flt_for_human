# Topic m5 — the cusp dichotomy, the Fricke automorphisms, and the cusp bookkeeping (M9)

**Status: work order drafted (pending the SET-M1 review).** Third topic of
[SET-M2](SET-M2.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** Three modules:

- `FLTForHuman/ModularCurve/Analytic/CuspBookkeeping.lean` — the 11 short
  `ord_*`/`isCusp_*`/`cuspZeroBar_ne_cuspInftyBar`/`frickeInvolutionBar_coeffEmb_qExpand`
  nodes and `ord_qInftyPlaceBar`.
- `FLTForHuman/ModularCurve/Analytic/FrickeAut.lean` — `exists_isFrickeAut_of_modularPolynomialData`,
  `exists_isFrickeAut`, `exists_isFrickeAutFull`,
  `isFrickeAutFull_frickeInvolutionFull_prime`.
- `FLTForHuman/ModularCurve/Analytic/CuspDichotomy.lean` — `eq_cuspInftyBar_or_eq_cuspZeroBar`
  and `modularFunctionFieldBar_eq_restrictScalars`.

**Why this topic.** It is the bridge between the analytic core (m4) and the
degree theory (m6/m7/m8): the dichotomy identifies the cusps of `ℚ̄(X₀(ℓ))`, the
restrict-scalars identity is the field-theoretic form `finrank_adjoin_jqNModC_eq_of_prime`
(m8) needs, and the Fricke automorphisms are what make the `q ↦ q^ℓ` transport
(the `fricke_transport` of m4) available at every prime.

## 1. The short nodes (assembly)

| node | content | route |
|---|---|---|
| `ModularCurve.ord_qInftyPlaceBar` | 27 | from the `qInftyPlaceBar` definition and `qSeriesBar` coercion (m2's `Defs/QAdicPlace.lean`); `(qInftyPlaceBar L F h).ord f = (qSeriesBar L F f).order` |
| `ModularCurve.ord_cuspInftyBar` | 3 | `ord_qInftyPlaceBar` + `cuspInftyBar`'s definition |
| `ModularCurve.ord_cuspInftyBar_coeffEmb_jq` | 4 | `order_coeffEmb_jq` (m2) + the `= -1` computation |
| `ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand` | 5 | `ord_cuspInftyBar` + `order_qExpand` (m4's glue) |
| `ModularCurve.ord_cuspZeroBar_coeffEmb_jq` | 7 | `IsFrickeAutFull` + `Place.ord_smul` |
| `ModularCurve.ord_cuspZeroBar_coeffEmb_qExpand` | 4 | `frickeInvolutionBar`'s action on `qExpand ℚ a jq` |
| `ModularCurve.cuspZeroBar_ne_cuspInftyBar` | 7 | the two `ord` values at `1 < N` |
| `ModularCurve.isCusp_iff_ord_neg` | 5 | `IsCusp` + `Place.ord` (AC's `mem_iff_ord_nonneg`) |
| `ModularCurve.isCusp_cuspInftyBar` | 4 | `isCusp_iff_ord_neg` + `ord_cuspInftyBar_coeffEmb_jq` |
| `ModularCurve.isCusp_cuspZeroBar` | 4 | same for `cuspZeroBar` |
| `ModularCurve.frickeInvolutionBar_coeffEmb_qExpand` | 8 | `IsFrickeAutFull`'s defining property + `frickeInvolutionBar_def` |

These are transcriptions against m2's vocabulary; **`ord_qInftyPlaceBar` is the
only one with a real (short) proof** — scout it first.

## 2. The Fricke automorphisms

- `ModularCurve.exists_isFrickeAut_of_modularPolynomialData` (197 content):
  wrapper `{N} [NeZero N] (data : ModularPolynomialData N) (hsymm : EvalSymm data.Φ)
  (hirr : PhiIrreducible data) : ∃ σ : modularFunctionField N ≃ₐ[ℚ]
  modularFunctionField N, IsFrickeAut N σ`. The pin's block: `algHom_ext_of_eq_on_gens`,
  `exists_isFrickeAut_of_endo`, `eval_swap_eq_zero`, `aeval_jqN_toAdjoin`,
  `minpoly_jqN_eq`, `frickeBaseHom`/`frickeRelativeHom`/`frickeAbsoluteHom`,
  `modularFunctionField_eq_restrictScalars`, `relativeRingEquiv`,
  `mem_of_apply_gens_mem`, `frickeAbsoluteHom_mem`, `frickeEndoRingHom`,
  `frickeEndoAlgHom` + the two `_jInF`/`_jNInF` lemmas. Seam: mathlib's
  `IntermediateField.AdjoinRoot`/`Polynomial.aeval`/`minpoly` and the ported
  `Defs/Fields.lean` `toAdjoin`/`adjoinJq`/`evalAtJGen`.
- `exists_isFrickeAut` (5) and `exists_isFrickeAutFull` (33): from the ported
  `exists_phiIrreducible_evalSymm` (`∃ data, PhiIrreducible data ∧ EvalSymm data.Φ`)
  and the previous theorem; `exists_isFrickeAutFull` transports along
  `FunctionFieldGeneration`/`Gen` (m6's `full_eq_of_prime`).
- `isFrickeAutFull_frickeInvolutionFull_prime` (5): `frickeInvolutionFull`'s
  `dif_pos` + `IsFrickeAutFull`, from `exists_isFrickeAutFull`.

## 3. The cusp dichotomy

`ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar` (163 content):

```lean
theorem ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar (ℓ : ℕ) [Fact ℓ.Prime]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ))
    (hc : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, …⟩ : modularFunctionFieldBar ℓ) w) :
    w = cuspInftyBar ℓ ∨ w = cuspZeroBar ℓ
```

The pin's route: build `φ : RatFunc 𝕂 →+* modularFunctionFieldBar ℓ` with
`φ X = jb = coeffEmb jq`, the tower/`IsScalarTower`, `Module.Finite`, the degree
bound `finrank_le : finrank (RatFunc 𝕂) (bar) ≤ ℓ+1`, `IsSeparable`, and then a
place count: any cusp place restricts to the unique place of `RatFunc 𝕂` at
infinity; the ramification/inertia data gives `e = f = 1` at `cuspInftyBar` and
the `cuspZeroBar` case is the `S`-conjugate. Seams: AC's `Divisor`/`Place`
ramification API (ported), mathlib `RatFunc` (Ostrowski), and the **m6**
`transcendental_jqModC`/`finrank_adjoin_jqNModC_le`/`nonempty_modularPolynomialData_of_squarefree`
+ the **m5 bookkeeping** nodes above.

**Dedup — expose the `RatFunc` model for m8.** This file's first **160 content
lines** are byte-identical to the first 160 content lines of
`S_ModularCurve_finrank_adjoin_jqNModC_eq_of_prime.lean` (measured with
`difflib.SequenceMatcher`: one matching block of size 160, then the tails
diverge). The shared block is `prime'`, `dedekindPsi_prime`, `jb`, `coe_jb`,
`bar_eq_restrictScalars`, `σa`, `coe_σa_X`, `mem_bar_iff`, `jTr`, `coe_jTr`,
`φ`, `φ_apply`, `coe_algebraMap_tower`, `coe_φ`, `φ_algebraMap`, `φ_X`,
`algRatFunc`, `algebraMap_eq`, `isScalarTower_ratFunc`, `he_compat`,
`finite_ratFunc`, `finrank_le`, `isSeparable_ratFunc`, `restrict_eq_of_isCusp`,
`e_infty`, `e_zero`, `eq_cuspInftyBar_or_eq_cuspZeroBar`, `le_finrank`,
`finrank_tower_eq`. **Write it once** in this topic (a shared
`Analytic/RatFuncModel.lean`, or the public half of `CuspDichotomy.lean`) with
the names the pin uses, make the half m8 needs public, and let m8 import it. Do
not re-derive it in m8. Record the 160-line saving.

`ModularCurve.modularFunctionFieldBar_eq_restrictScalars` (169 content): the
wrapper identifies `modularFunctionFieldBar ℓ` with the two-step adjoin
`𝕂⟮jqModC⟯⟮jqNModC ℓ⟯` restricted to scalars. The pin's route uses the
`modularUnitSeries` unit `ubar`, its `ord`/Fricke symmetry
(`fricke_ubar`, `fricke_symm_ubar`, `ord_inf`, `ord_zero`), the integrality of
`ubar`/`ubar⁻¹` over `ℚ[jq]`, and concludes `(ℓ-1) · cuspidalDivisor` is
principal, hence `cuspidalClass` has order dividing `ℓ-1`; then the cusp
dichotomy and `coeffEmb_injective` give the equality. Seams: **m4**'s
`modularUnitSeries_mem_modularFunctionFieldFull`,
`isIntegral_adjoin_jq_modularUnitSeries(_inv)`, `coe_frickeInvolutionFull_modularUnitSeries`,
and AC's `Place.{ord_eq_zero_of_isIntegral_adjoin, ord_smul_of_ne_zero}`,
`isIntegral_adjoin_{map_algHom, of_isScalarTower, intermediateField_mk}`,
`Pic0.zsmul_mk_eq_zero_of_isPrincipal`, `Pic0.addOrderOf_mk_dvd_of_isPrincipal`.

## 3.5 The prime degree (the folded m8 node)

`ModularCurve.finrank_adjoin_jqNModC_eq_of_prime` (200 content):

```lean
theorem ModularCurve.finrank_adjoin_jqNModC_eq_of_prime (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set _))
      (IntermediateField.adjoin (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set _))
        ({jqNModC (AlgebraicClosure ℚ) ℓ} : Set _)) = ℓ + 1
```

This is the **last section of this topic**, not a topic of its own: its file is
the shared `RatFunc` model (160 content) plus a ~40-line tail. Once §3's model is
written, the tail is the assembly `finrank_le` + `le_finrank` + `finrank_tower_eq`.
Do not re-derive the model. Record the 160-line saving.



- Append the 17 wrappers to `SOURCES`, the three modules to `PORT_FILES`.
- checker 0 mismatched / 0 missing.
- `#print axioms` on the four named headlines.
- Consumer Zone E `[cusp]`: `eq_cuspInftyBar_or_eq_cuspZeroBar` at `ℓ = 2` (or
  `N = 1`), `modularFunctionFieldBar_eq_restrictScalars` at `ℓ = 2`, and the
  `cuspInftyBar ≠ cuspZeroBar` split.

## 5. Budget

**3 goal rounds.** Round 1: `CuspBookkeeping` + `FrickeAut`. Round 2:
`eq_cuspInftyBar_or_eq_cuspZeroBar`. Round 3:
`modularFunctionFieldBar_eq_restrictScalars`, log/README/consumer.

**Stop early on**: the `RatFunc` degree/separable obligations needing a mathlib
statement the pin's proof does not reach; the `cuspidalClass` order argument
needing an AC lemma the port lacks (report it); or a statement that will not
match its wrapper.

## 6. Reporting back

1. Module/line/decl table and checker before/after.
2. `exists_isFrickeAut_of_modularPolynomialData`'s route (the `AdjoinRoot` step).
3. `eq_cuspInftyBar_or_eq_cuspZeroBar`'s route: the `RatFunc` model, the degree
   bound, and the place count.
4. `modularFunctionFieldBar_eq_restrictScalars`'s route: the `ubar`/order
   argument and the AC lemmas consumed.
5. The SET-M3 hand-off: what m7–m9 import.
