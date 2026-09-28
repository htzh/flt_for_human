/-
  Cross-module wire test for the general-weight Eichler–Shimura period map
  (TOPIC-period-map-injectivity, pin `aa2d8b3`).

  This is a `spec/` probe, not a library module. It `#check`s the public surface
  of the port's Eichler–Shimura modules — the four generic facts in their subject
  homes (`FLTForHuman/Algebra/MvPolynomialHomogeneous.lean`,
  `ModularForms/Analytic/StarConvexPrimitive.lean`,
  `ModularForms/Analytic/CuspBoundedness.lean`, `ModularForms/ModularGroup.lean`),
  the definitions (`BinaryForm.lean`, `CoeffCohomology.lean`,
  `EichlerIntegral.lean`), the nine Tier-2 leaves and the eight-node analytic
  chain plus the structural map (`PeriodMap.lean`) — and then runs executed
  compositions that a `#check` cannot catch:

  * the pin's `eichlerShimuraMap_injective` reproduced through the port's
    structural `periodMap`;
  * a vanishing period class forcing the cusp form to vanish;
  * the chosen Eichler integral's cocycle realising `periodMap`, composing
    `PeriodMap` with `EichlerIntegral`, `CoeffCohomology` and `BinaryForm`.

  The pin's `dif`ed `eichlerShimuraMap` is deliberately absent; the divergence is
  recorded in `PeriodMap.lean`'s header and `TOPIC-period-map-injectivity.md` §3.
-/
import FLTForHuman.Algebra.MvPolynomialHomogeneous
import FLTForHuman.ModularForms.Analytic.CuspBoundedness
import FLTForHuman.ModularForms.Analytic.StarConvexPrimitive
import FLTForHuman.ModularForms.EichlerShimura.BinaryForm
import FLTForHuman.ModularForms.EichlerShimura.CoeffCohomology
import FLTForHuman.ModularForms.EichlerShimura.EichlerIntegral
import FLTForHuman.ModularForms.EichlerShimura.PeriodMap
import FLTForHuman.ModularForms.ModularGroup

open HeckeEis UpperHalfPlane MvPolynomial CongruenceSubgroup
open scoped Manifold MatrixGroups ModularForm UpperHalfPlane

-- Tier 0 — the externals.
#check MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt
#check Complex.exists_hasDerivAt_of_starConvex
#check UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic
#check UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty
#check ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four

-- Tier 1 — the definitions.
#check BinaryForm
#check binaryFormRepSL
#check binaryFormRepSL_apply_coe
#check coeffH1par
#check coeffH1parMk
#check IsEquivariantPrimitiveWith
#check IsEichlerIntegral

-- Tier 2 — the leaves.
#check IsEichlerIntegral.add
#check IsEichlerIntegral.smul
#check IsEichlerIntegral.slash
#check IsEichlerIntegral.exists_sub_eq_const
#check IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries
#check jFactor_pow_mul_eval_binaryFormRepSL

-- Tier 3 — the analytic chain and the structural map.
#check IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv
#check IsEichlerIntegral.eq_zero_of_eval_eq_const
#check IsEichlerIntegral.isBoundedAtImInfty_eval
#check exists_isEichlerIntegral
#check isEquivariantPrimitiveWith_of_isEichlerIntegral
#check IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range
#check isParabolicCocycle_cocycle_of_isEichlerIntegral
#check exists_isEichlerIntegral_isParabolicCocycle
#check periodMap
#check periodMap_eq_coeffH1parMk
#check periodMap_injective

/-- The pin's `Thm_HeckeEis_eichlerShimuraMap_injective` reproduced through the
port's structural `periodMap`: `periodMap n N` is injective. -/
example (n N : ℕ) [NeZero N] :
    Function.Injective
      (fun f : CuspForm (Gamma0 N) ((n : ℤ) + 2) ↦ periodMap n N f) :=
  periodMap_injective n N

/-- Wire test (composition with the function): a vanishing period class forces the
cusp form to vanish. -/
example (n N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) ((n : ℤ) + 2))
    (hf : periodMap n N f = 0) : f = 0 :=
  periodMap_injective n N (by rw [hf, map_zero])

/-- Wire test (cross-module, four modules): the cocycle of any chosen Eichler
integral realises the period class. Uses `periodMap_eq_coeffH1parMk` (`PeriodMap`)
with `IsEichlerIntegral`/`IsEquivariantPrimitiveWith` (`EichlerIntegral`),
`coeffH1parMk` (`CoeffCohomology`) and `BinaryForm`/`binaryFormRepSL`
(`BinaryForm`). -/
example (n N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) ((n : ℤ) + 2))
    {F : UpperHalfPlane → ↥(BinaryForm ℂ n)} (hEI : IsEichlerIntegral n f F)
    (hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F)
    (hpar : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle) :
    periodMap n N f = coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩ :=
  periodMap_eq_coeffH1parMk n N f hEI hF hpar

/-- Wire test (executed construction): every cusp form admits an Eichler integral
whose cocycle is equivariant and parabolic. -/
example (n N : ℕ) [NeZero N] (f : CuspForm (Gamma0 N) ((n : ℤ) + 2)) :
    ∃ F : UpperHalfPlane → ↥(BinaryForm ℂ n), IsEichlerIntegral n f F ∧
      ∃ hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F,
        IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle :=
  exists_isEichlerIntegral_isParabolicCocycle N n f
