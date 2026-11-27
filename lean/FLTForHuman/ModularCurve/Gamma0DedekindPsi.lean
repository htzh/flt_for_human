/-
The `Γ₀`-index bound against `dedekindPsi`.

For a level `N`, the index of `Γ₀(N)` in the full modular group is `N · ∏_{p | N} (1 + 1/p)` — the
arithmetic function usually written `ψ(N)` (`dedekindPsi`).  This module proves the **index bound in
the form the geometric arguments use**:

  `Nat.card (Γ₀(N) \\ SL₂(ℤ)) ≤ dedekindPsi N`,

i.e. the number of the quotient's points is bounded by the arithmetic function, which is what makes
`ψ` the right count for the degree of the modular polynomial `Φ_N` and for the fibre counts of
`X₀(N) → X(1)`.  The equality half is not needed here and not claimed: the statement is the
inequality a consumer can use without knowing `N`'s factorisation.

The engine is the index computation and the `q`-expansion dictionary
(`ModularCurve/Gamma0Index.lean`, `ModularForms/{IsArithmeticQExpansion}.lean`,
`ModularCurve/Analytic/{ANb,JqInverseIntegral}.lean`), the Laurent/degree glue
(`ModularCurve/Degree/{LaurentGlue,Relfinrank}.lean`), the `X₀` coefficient dictionary
(`ModularCurve/Defs/JqCoeff.lean`), the `jq`-integrality (`X1/IntegralityJqNModC.lean`) and the
function-field generation capstone (`FunctionFieldGeneration/Capstone.lean`).

## Substitutions (the pin's row is a two-step bridge)

The pin's 318 lines are all already public in the port; this module is the bridge, not a
re-proof.

* `ModularCurve.Gamma0_index` — the arithmetic half `[SL₂(ℤ) : Γ₀(N)] = ψ(N)` — is
  `ModularCurve/Gamma0Index.lean`'s (SET-3, public there, `spec-pin:`
  `Theorems/Thm_ModularCurve_Gamma0_index.lean`).  It is **imported, not restated**.
* `ModularCurve.dedekindPsi` is `ModularForms/Gamma0TwoIndex.lean`'s / `NumberTheory/DedekindPsi.lean`'s
  (the port's one home); not redefined here.
* The pin's whole `AHBridge` block (its lines 49–288: `qe`, `JQ`, `IsRatio`, `Kan`, `KanK0`,
  `exists_poly_of_isRatio`, `finrank_baseChange`, `main`, …) feeds the pin's *other* headline
  `ModularCurve.qExpansion_div_mem_laurentBaseChange`, which is **out of this row's wire**
  (`spec-pin:` names only the index row's two files) and which **no module of the port carries**:
  the port's `ModularCurve.XHRationalStructure.main` (`ModularCurve/X1/QExpansionDiv.lean`,
  `private`) is the `Γ_H(M)` analogue — the other row
  `qExpansion_div_mem_laurentBaseChange_xHFunctionField` — not this one.  So the block is an
  **unclaimed row** (report §5) and is not transcribed here.
* The pin's three anonymous `example` probes (`dedekindPsi 4 = 6`, `dedekindPsi 1 = 1`,
  `Nat.card (Γ₀(1) \\ SL₂(ℤ)) = 1`) are node-local regression checks of imported lemmas:
  dropped, as this set's other orders drop their `example` probes.

## Declarations

* `ModularCurve.card_quotient_gamma0_eq_index` — the pin's `private` bridge: the quotient's
  cardinality *is* the index.  Kept `private` (pin-faithful); see the report for its
  `private`-dropped reading.
* `ModularCurve.card_quotient_gamma0_le_dedekindPsi` — the headline.

## Axioms, and the heartbeat probe pair (recorded, never installed)

`#print axioms ModularCurve.card_quotient_gamma0_le_dedekindPsi`: `[propext, Classical.choice,
Quot.sound]`, no `sorryAx` (`lean/tmp/af106/AF106E-axioms.log`).

The playbook's **downward** heartbeat ladder, one run per value, over this file at
`-DautoImplicit=false`: **40000, 20000, 10000, 5000 and 1000 all ok**; 500 fails at `:96:6`
(`show Subgroup.relIndex _ _ = _` in the bridge, `isDefEq`) and 200 at `:92:14`.  **The pair is
1000 ok / 500 fail**, recorded and **not installed** (no `set_option maxHeartbeats`, no
`set_option synthInstance.maxHeartbeats`, and no `attribute [-instance]`/`[-simp]` wall — the pin
carries such a wall; it is not transcribed).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_card_quotient_gamma0_le_dedekindPsi.lean>

spec-pin: Theorems/Thm_ModularCurve_card_quotient_gamma0_le_dedekindPsi.lean
spec-pin: P2M/Sol/S_ModularCurve_card_quotient_gamma0_le_dedekindPsi.lean
-/
import FLTForHuman.ModularCurve.Analytic.ANb
import FLTForHuman.ModularCurve.Analytic.JqInverseIntegral
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Degree.LaurentGlue
import FLTForHuman.ModularCurve.Degree.Relfinrank
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.Gamma0Index
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.X1.IntegralityJqNModC
import FLTForHuman.ModularForms.IsArithmeticQExpansion

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve

/-- The cardinality of `Γ₀(N) \ SL₂(ℝ)`'s quotient by `Γ₀(N)` is the index of `Γ₀(N)` in
`SL₂(ℤ)`: `Subgroup.index_eq_card` plus the fact that `SL₂(ℤ) ↪ SL₂(ℝ)` so the relative
index against the top subgroup is the absolute one.  The pin's `private` bridge
(`S_…:33-39`: `index_eq_card`, the `relIndex` transport through
`mapGL_injective`, and `relIndex_top_right`), verbatim. -/
private theorem card_quotient_gamma0_eq_index (N : ℕ) :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).subgroupOf 𝒮ℒ) = (CongruenceSubgroup.Gamma0 N).index := by
  rw [← Subgroup.index_eq_card]
  show Subgroup.relIndex _ _ = _
  rw [MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]

/-- **The `Γ₀` index bound**: the number of points of `Γ₀(N) \ SL₂(ℤ)` is at most the
Dedekind psi function.  The pin's headline (`S_…:44`, `Theorems/Thm_…:19`), whose proof is
one `trans` of the quotient-cardinality bridge with the index computation
`ModularCurve.Gamma0_index`. -/
theorem card_quotient_gamma0_le_dedekindPsi (N : ℕ) [NeZero N] :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).subgroupOf 𝒮ℒ) ≤ ModularCurve.dedekindPsi N :=
  ((card_quotient_gamma0_eq_index N).trans (ModularCurve.Gamma0_index N)).le

end ModularCurve
