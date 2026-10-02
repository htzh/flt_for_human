/-
  Consumer specification for the `ModularCurve` Hecke layer (SET-M1: m1–m3).

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the Hecke vocabulary and the modular-unit analytic
  layer: the statements the port must make possible, expressed in Lean so each one
  is either bound or not. It is a deliverable measure, not a proof obligation.

  It is deliberately **not part of any library**. `lake build` does not see it
  (nothing globs `spec/`), so it cannot break the verified port's green build.
  Run it by hand:

      cd lean
      lake env lean spec/ModularCurveHeckeConsumer.lean 2>&1 | grep -c error

  The error count is the metric.

  HOW TO READ IT
  --------------
  Every block is labelled:

    [vocab]     ZONE A — after m1/m2. The objects exist with the pinned shapes
                (`JZero`, `heckeOperatorBar`, `HeckeExchangeAt`, the cusps and the
                modular unit), the two definitional bridges hold, and one concrete
                `qInftyPlaceBar` is inhabited. Live imports and `#check`s.
    [analytic]  ZONE B — after m3. The nine M7 nodes at their pinned statements,
                instantiated at `N = 2`/`ℓ = 2`.

  Later sets append: ZONE G `[payoff]` (the `HeckeAlg` module structure), ZONE C
  `[analytic]` (m4's Fricke/inclusion headlines), ZONE D `[degree]` (m6's Φ datum
  family), ZONE E `[cusp]` (m5b's cusp dichotomy), ZONE I `[relfinrank]` (SET-M3
  m7's Laurent glue and relative degrees), ZONE F `[roof]` (SET-M3 m9's roof
  generation and diagonal degree), ZONE J `[inputs]` (SET-M4 m10's
  integrality/finiteness and m11's principal divisors) and ZONE H `[reduction]`
  (SET-M4 m12's exchange reduction, composed with the capstone's `WEX` binder).
  The file stays at 0 errors / 0 warnings.
-/

import FLTForHuman.ModularCurve.Defs.HeckeOperator
import FLTForHuman.ModularCurve.Defs.DegeneracyTower
import FLTForHuman.ModularCurve.Defs.HeckeTotal
import FLTForHuman.ModularCurve.Defs.HeckeModule
import FLTForHuman.ModularCurve.Defs.ArithmeticGalois
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Defs.GeometricBaseChange
import FLTForHuman.ModularCurve.Defs.QAdicPlace
import FLTForHuman.ModularCurve.Defs.ModularUnit
import FLTForHuman.ModularCurve.Defs.AtkinLehner
import FLTForHuman.ModularCurve.Defs.CuspidalClass
import FLTForHuman.ModularCurve.Analytic.QParamUnique
import FLTForHuman.ModularCurve.Analytic.Gamma0Cosets
import FLTForHuman.ModularCurve.Analytic.ModularUnitQExpansion
import FLTForHuman.ModularCurve.Analytic.Gamma0InvariantCore
import FLTForHuman.ModularCurve.Analytic.FrickeInvariance
import FLTForHuman.ModularCurve.Analytic.CuspBookkeeping
import FLTForHuman.ModularCurve.Analytic.FrickeAut
import FLTForHuman.ModularCurve.Degree.PhiData
import FLTForHuman.ModularCurve.Degree.PhiDegree
import FLTForHuman.ModularCurve.Analytic.CuspDichotomy
import FLTForHuman.ModularCurve.Degree.Roof
import FLTForHuman.ModularCurve.HeckeInputs.Integrality
import FLTForHuman.ModularCurve.PrincipalDivisors.ModularCurveBar
import FLTForHuman.ModularCurve.HeckeExchange.Reduction
import FLTForHuman.ModularCurve.HeckeCommuteBar
import FLTForHuman.ModularCurve.X1.HeckeModule
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.ModularCurve.X1.QExpandStretch
import FLTForHuman.ModularCurve.X1.DiamondAut
import FLTForHuman.ModularCurve.X1.BaseChangeCover
import FLTForHuman.ModularCurve.X1.Inputs

open ModularCurve
open ModularCurve.QexpN
open AlgebraicCurve
open scoped MatrixGroups ModularForm

noncomputable section

/-! ## Zone A — `[vocab]` the Hecke correspondence and the cusp vocabulary -/

-- The pinned shapes. `#check` is against the port's live imports.
#check JZero
#check modularFunctionFieldBar
#check heckeOperatorBar
#check HeckeOperatorsCommuteBar
#check heckeAlphaBar
#check heckeBetaBar
#check towerInclBar
#check towerSubstBar
#check HeckeExchangeAt
#check HeckeInputsAlong
#check heckeOperatorAlong
#check heckeDivBar
#check heckePic0Bar
#check modularUnitSeries
#check qSeriesBar
#check qIntegersBar
#check qInftyPlaceBar
#check cuspInftyBar
#check cuspZeroBar
#check IsCusp
#check jqModC
#check jqNModC
#check modularFunctionFieldC
#check geomAut
#check baseChangeEquiv
#check frickeInvolutionFull

-- Inhabitedness: `JZero N` from zero.
example (N : ℕ) [NeZero N] : Inhabited (JZero N) := ⟨0⟩

-- One operator.
example (N : ℕ) [NeZero N] (ℓ : Nat.Primes) : Module.End ℤ (JZero N) :=
  heckeOperatorBar N ℓ

-- The target proposition, stated at the pin's shape.
example (N : ℕ) [NeZero N] : Prop := HeckeOperatorsCommuteBar N

-- One `HeckeExchangeAt`, stated as a `Prop` term.
example (L : Type*) [Field L] [Algebra ℚ L] (N ℓ ℓ' M : ℕ) [NeZero N] [NeZero ℓ]
    [NeZero ℓ'] [NeZero M] (hM : M = N * ℓ * ℓ') : Prop := HeckeExchangeAt L N ℓ ℓ' M hM

-- The two definitional bridges the rest of the cone rewrites through.
example (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    heckeAlphaBar L N ℓ = towerInclBar L (dvd_mul_right N ℓ) := rfl

example (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] :
    heckeBetaBar L N ℓ = towerSubstBar L N ℓ dvd_rfl :=
  heckeBetaBar_eq_towerSubstBar L ℓ

-- One concrete `q`-adic place: the cusp at infinity of `ℚ(j(q))`.
example : Place ℚ (modularFunctionField 1) := cuspInfty 1

-- The `bar`-level cusp and Fricke/cuspidal vocabulary at `N = 1`.
example : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) := cuspInftyBar 1
example : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) := cuspZeroBar 1

-- `jqModC` agrees with the ported `jq`/`jqN` over `ℚ`.
example (N : ℕ) [NeZero N] : jqNModC ℚ N = jqN N := rfl

-- The modular unit is the ratio `Δ / Δ(q ^ p)`.
#check modularUnitSeries_mul_deltaSeriesN
#check isMonicOfOrder_modularUnitSeries

/-! ## Zone B — `[analytic]` m3's modular-unit q-expansion core -/

-- The nine M7 nodes, at their pinned statements.
#check @hasSum_modularUnitSeries_qParam
#check @hasSum_modularUnitSeries_inv_qParam
#check @hasSum_smul_modularUnitSeries_qParam
#check @hasSum_smul_modularUnitSeries_inv_qParam
#check @qParam_coeff_unique
#check @laurent_qParam_coeff_unique
#check @exists_perm_gamma0_cosetReps
#check @exists_sl2_heckeDiagMatrix_smul_eq
#check @discriminant_div_discriminant_heckeDiagMatrix_smul

-- The two generic heads, public (the pin repeats them privately in four files).
#check @hasSum_modularUnit
#check @hasSum_modularUnitInv

-- The four hasSum heads at `N = 2`.
example (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (((modularUnitSeries 2).coeff m : ℚ) : ℂ) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.discriminant τ /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix 2 • τ)) :=
  hasSum_modularUnitSeries_qParam 2 τ

example (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => ((((modularUnitSeries 2)⁻¹).coeff m : ℚ) : ℂ) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.discriminant (ModularForm.heckeDiagMatrix 2 • τ) /
        ModularForm.discriminant τ) :=
  hasSum_modularUnitSeries_inv_qParam 2 τ

example (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (((((2 : ℚ) ^ 12)⁻¹ • modularUnitSeries 2).coeff m : ℚ) : ℂ) *
        Function.Periodic.qParam 2 (τ : ℂ) ^ m)
      (ModularForm.discriminant (ModularForm.heckeDiagMatrix 2 • ModularGroup.S • τ) /
        ModularForm.discriminant (ModularGroup.S • τ)) :=
  hasSum_smul_modularUnitSeries_qParam 2 τ

example (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => ((((2 : ℚ) ^ 12 • (modularUnitSeries 2)⁻¹).coeff m : ℚ) : ℂ) *
        Function.Periodic.qParam 2 (τ : ℂ) ^ m)
      (ModularForm.discriminant (ModularGroup.S • τ) /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix 2 • ModularGroup.S • τ)) :=
  hasSum_smul_modularUnitSeries_inv_qParam 2 τ

-- The `Δ`-ratio invariance at `N = 2` along `Γ₀(2)`.
example (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 2)
    (τ : UpperHalfPlane) :
    ModularForm.discriminant (γ • τ) /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix 2 • γ • τ) =
      ModularForm.discriminant τ /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix 2 • τ) :=
  discriminant_div_discriminant_heckeDiagMatrix_smul 2 γ hγ τ

-- The diagonal transport at `N = 2` on a concrete `Γ₀(2)` element.
example :
    ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (∀ τ : UpperHalfPlane, ModularForm.heckeDiagMatrix 2 • (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ
          = γ' • ModularForm.heckeDiagMatrix 2 • τ) ∧
      ∀ τ : UpperHalfPlane,
        UpperHalfPlane.denom (γ' : Matrix.GeneralLinearGroup (Fin 2) ℝ)
          (((ModularForm.heckeDiagMatrix 2 • τ : UpperHalfPlane)) : ℂ) =
        UpperHalfPlane.denom ((1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) :=
  exists_sl2_heckeDiagMatrix_smul_eq 2 1 (Subgroup.one_mem (CongruenceSubgroup.Gamma0 2))

-- One `Γ₀`-coset permutation at `ℓ = 2` (there are `ℓ + 1 = 3` classes).
example (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃ e : Equiv.Perm (Fin 3), ∀ i : Fin 3,
      (Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (fun b : Fin 2 => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i :
          Matrix.SpecialLinearGroup (Fin 2) ℤ) * γ *
        (Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)
          (fun b : Fin 2 => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) (e i) :
            Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ ∈ CongruenceSubgroup.Gamma0 2 :=
  exists_perm_gamma0_cosetReps 2 γ

/-! ## Zone G — `[payoff]` the `HeckeAlg`-module structure (m1's optional tail) -/

#check HeckeAlg
#check heckeGen
#check heckeEvalBar
#check heckeEvalBar_heckeGen
#check heckeModuleBar
#check heckeModuleBar_smul_def
#check heckeModuleBar_heckeGen_smul
#check heckeModuleBar_C_smul

-- The payoff's defining identity: on `HeckeAlg`'s generators, the `HeckeAlg`-action
-- is the Hecke operator.
example (N : ℕ) [NeZero N] (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) (x : JZero N) :
    (letI := heckeModuleBar N; heckeGen ℓ • x) = heckeOperatorBar N ℓ x :=
  heckeModuleBar_heckeGen_smul h ℓ x

/-! ## Zone C — `[analytic]` m4's Fricke/inclusion headlines -/

-- The two pinned headlines.
#check @mem_modularFunctionField_of_hasSum_of_gamma0_invariant
#check @isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant

-- The `modularUnitSeries` inclusion and integrality at `ℓ = 2`.
example : modularUnitSeries 2 ∈ modularFunctionField 2 :=
  modularUnitSeries_mem_modularFunctionField 2
example : IsIntegral (Algebra.adjoin ℚ {jq}) (modularUnitSeries 2) :=
  isIntegral_adjoin_jq_modularUnitSeries 2
example : IsIntegral (Algebra.adjoin ℚ {jq}) (modularUnitSeries 2)⁻¹ :=
  isIntegral_adjoin_jq_modularUnitSeries_inv 2

-- The Fricke transport of the modular unit: `W_2(u) = 2^12 · u⁻¹`.
example (hmem : modularUnitSeries 2 ∈ modularFunctionFieldFull 2) :
    ((frickeInvolutionFull 2 ⟨modularUnitSeries 2, hmem⟩ : modularFunctionFieldFull 2) :
      LaurentSeries ℚ) = (2 : ℚ) ^ 12 • (modularUnitSeries 2)⁻¹ :=
  coe_frickeInvolutionFull_modularUnitSeries 2 hmem

/-! ## Zone D — `[degree]` m6's Φ datum family and degree tail -/

-- The pinned statements.
#check @nonempty_modularPolynomialData_of_squarefree
#check @finrank_adjoin_jqNModC_le
#check @transcendental_jqModC

-- The Φ datum at `N = 2`, its degree bound, and `jqModC`'s transcendence.
example : Nonempty (ModularPolynomialData 2) :=
  nonempty_modularPolynomialData_of_squarefree 2 Nat.squarefree_two (by norm_num)
example (data : ModularPolynomialData 2) : Module.finrank
    (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
    (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jqModC ℚ} : Set (LaurentSeries ℚ)))
      ({jqNModC ℚ 2} : Set (LaurentSeries ℚ))) ≤ dedekindPsi 2 :=
  finrank_adjoin_jqNModC_le ℚ data
example : Transcendental ℚ (jqModC ℚ) := transcendental_jqModC ℚ

-- The modular polynomial family is unconditional.
example : ModularPolynomialFamily := modularPolynomialFamily

/-! ## Zone E — `[cusp]` m5b's cusp dichotomy, prime degree and restrict-scalars -/

-- The three pinned statements.
#check @eq_cuspInftyBar_or_eq_cuspZeroBar
#check @finrank_adjoin_jqNModC_eq_of_prime
#check @modularFunctionFieldBar_eq_restrictScalars

-- The dichotomy at `ℓ = 2`: every cusp place is one of the two cusps.
example (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar 2))
    (hc : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full 2)⟩ :
        modularFunctionFieldBar 2) w) :
    w = cuspInftyBar 2 ∨ w = cuspZeroBar 2 :=
  eq_cuspInftyBar_or_eq_cuspZeroBar 2 w hc

-- The two cusps differ, so the dichotomy is a genuine split.
example : cuspZeroBar 2 ≠ cuspInftyBar 2 :=
  cuspZeroBar_ne_cuspInftyBar 2 (isFrickeAutFull_frickeInvolutionFull_prime 2) (by norm_num)

-- The prime degree at `ℓ = 2`.
example : Module.finrank
    (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ))))
    (IntermediateField.adjoin (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ))))
      ({jqNModC (AlgebraicClosure ℚ) 2} : Set (LaurentSeries (AlgebraicClosure ℚ)))) = 3 :=
  finrank_adjoin_jqNModC_eq_of_prime 2

-- The restrict-scalars identity at `ℓ = 2`.
example : modularFunctionFieldBar 2 =
    (IntermediateField.adjoin (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ))))
      ({jqNModC (AlgebraicClosure ℚ) 2} : Set (LaurentSeries (AlgebraicClosure ℚ)))).restrictScalars
        (AlgebraicClosure ℚ) :=
  modularFunctionFieldBar_eq_restrictScalars 2

/-! ## Zone I — `[relfinrank]` m7's Laurent glue and relative degrees -/

-- The pinned statements.
#check @coeffEmb_jq
#check @coeffEmb_jqN
#check @order_qExpand
#check @order_coeffEmb
#check @laurentBaseChange_adjoin
#check @laurentBaseChange_modularFunctionField
#check @laurentBaseChange_modularFunctionFieldFull
#check @transcendental_jqN
#check @relfinrank_laurentBaseChange
#check @relfinrank_qExpand_full

-- `coeffEmb` at `L = ℂ` on `jq`/`jqN`.
example : coeffEmb ℂ jq = jqModC ℂ := coeffEmb_jq ℂ
example (N : ℕ) [NeZero N] : coeffEmb ℂ (jqN N) = jqNModC ℂ N := coeffEmb_jqN ℂ N

-- The relative degree at `N = 1`, `ℓ = 2`.
example : IntermediateField.relfinrank
    ((modularFunctionFieldFull 1).map (qExpandₐ 2)) (modularFunctionFieldFull (1 * 2))
      = if 2 ∣ 1 then 2 else 2 + 1 :=
  relfinrank_qExpand_full 1 2

/-! ## Zone F — `[roof]` m9's roof generation and diagonal degree -/

-- The pinned statements.
#check @heckeRoof_adjoin_range_union_eq_top
#check @finrankAlong_towerSubstBar_comp_heckeAlphaBar

-- The `N = 1`, `ℓ = 2`, `ℓ' = 3`, `M = 6` roof square.
example (hm : (6 : ℕ) = 1 * 2 * 3) :
    Algebra.adjoin ℂ
      (Set.range (towerSubstBar ℂ (1 * 3) 2 (dvd_of_eq_roof 1 2 3 6 hm).2)
        ∪ Set.range (towerInclBar ℂ (dvd_of_eq_roof 1 2 3 6 hm).1)) = ⊤ :=
  heckeRoof_adjoin_range_union_eq_top ℂ 1 2 3 6 hm (functionFieldGeneration 6)
    (exists_modularPolynomialData_evalSymm 3).choose

-- The diagonal degree at the same square: it is the product of the two Hecke
-- degrees, the shape `HeckeExchangeAt`/`heckeExchangeAt_of_WEX` consumes.
example (hm : (6 : ℕ) = 1 * 2 * 3) :
    AlgebraicCurve.finrankAlong ℂ
        ((towerSubstBar ℂ (1 * 3) 2 (dvd_of_eq_roof 1 2 3 6 hm).2).comp
          (heckeAlphaBar ℂ 1 3))
      = AlgebraicCurve.finrankAlong ℂ (heckeAlphaBar ℂ 1 3)
        * AlgebraicCurve.finrankAlong ℂ (heckeBetaBar ℂ 1 2) :=
  finrankAlong_towerSubstBar_comp_heckeAlphaBar ℂ 1 2 3 6 hm (by norm_num)

/-! ## Zone J — `[inputs]` m10's integrality/finiteness and m11's principal divisors -/

-- The pinned statements.
#check @towerInclBar_isIntegral
#check @towerSubstBar_isIntegral
#check @towerInclBar_finiteAlong
#check @towerSubstBar_finiteAlong
#check @towerInclBar_surjective_of_dvd_dvd
#check @finiteAlong_heckeAlphaBar_of_prime
#check @finiteAlong_heckeBetaBar_of_prime
#check @heckeAlphaBarIntegral_of_prime
#check @heckeBetaBarIntegral_of_prime
#check @hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull
#check @hasPrincipalDivisors_modularFunctionFieldBar

-- m10 at `N = 1`, `ℓ = 2`: the two `FiniteAlong` heads, the two integrality
-- predicates, and the degeneracy tower for `1 ∣ 2`.
example : FiniteAlong ℂ (heckeAlphaBar ℂ 1 2) := finiteAlong_heckeAlphaBar_of_prime ℂ 1 2
example : FiniteAlong ℂ (heckeBetaBar ℂ 1 2) := finiteAlong_heckeBetaBar_of_prime ℂ 1 2
example : HeckeAlphaBarIntegral ℂ 1 2 := heckeAlphaBarIntegral_of_prime ℂ 1 2
example : HeckeBetaBarIntegral ℂ 1 2 := heckeBetaBarIntegral_of_prime ℂ 1 2
example : (towerInclBar ℂ (show (1 : ℕ) ∣ 2 from by norm_num)).toRingHom.IsIntegral :=
  towerInclBar_isIntegral ℂ (by norm_num)
example : FiniteAlong ℂ (towerSubstBar ℂ 1 2 (show (1 : ℕ) * 2 ∣ 2 from by norm_num)) :=
  towerSubstBar_finiteAlong ℂ 2 (by norm_num)

-- m11 at `N = 1`: the unconditional principal-divisors instance (the Φ family is
-- unconditional) and the layer form it comes from.
example : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) :=
  hasPrincipalDivisors_modularFunctionFieldBar modularPolynomialFamily 1
example : HasPrincipalDivisors ℂ (laurentBaseChange ℂ (modularFunctionFieldFull 1)) :=
  hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull ℂ modularPolynomialFamily 1

-- The `HeckeInputsAlong` bundle at `N = 1`, `ℓ = 2`: m10's integrality and
-- finiteness plus the two exchange hypotheses the capstone's `WEX` will supply.
example [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * 2))]
    (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) 1 2)
      (heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) 1 2))
    (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) 1 2)
      (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) 1 2)) :
    HeckeInputsAlong (AlgebraicClosure ℚ) 1 2 :=
  heckeInputsAlong_intro (heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) 1 2)
    (heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) 1 2) hFI
    (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) 1 2) hN

-- The principal-divisors instance the bundle above needs is m11's, unconditional.
example : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * 2)) :=
  hasPrincipalDivisors_modularFunctionFieldBar modularPolynomialFamily (1 * 2)

/-! ## Zone H — `[reduction]` m12's exchange reduction at the `2`/`3`/`6` square -/

-- The pinned statements.
#check @heckeDivBar_heckeDivBar_of_heckeExchangeAt
#check @heckeDivBar_comm_of_heckeExchangeAt
#check @heckeOperatorBar_comm_of_heckeExchangeAt
#check @heckeOperatorsCommuteBar_of_heckeExchangeAt

-- The two divisor reductions at `N = 1`, `ℓ = 2`, `ℓ' = 3`, `M = 6`: the roof
-- collapse and the commutation (`2 * 3 = 3 * 2`).
example (hm : (6 : ℕ) = 1 * 2 * 3) (hm' : (6 : ℕ) = 1 * 3 * 2)
    (hα : HeckeAlphaBarIntegral ℂ 1 2) (hβ : HeckeBetaBarIntegral ℂ 1 2)
    (hα' : HeckeAlphaBarIntegral ℂ 1 3) (hβ' : HeckeBetaBarIntegral ℂ 1 3)
    [HasPrincipalDivisors ℂ (laurentBaseChange ℂ (modularFunctionFieldFull (1 * 2)))]
    [HasPrincipalDivisors ℂ (laurentBaseChange ℂ (modularFunctionFieldFull (1 * 3)))]
    [HasPrincipalDivisors ℂ (laurentBaseChange ℂ (modularFunctionFieldFull 6))]
    (hu : (towerInclBar ℂ (dvd_of_eq_roof 1 2 3 6 hm).1).toRingHom.IsIntegral)
    (hu' : (towerSubstBar ℂ (1 * 3) 2 (dvd_of_eq_roof 1 2 3 6 hm).2).toRingHom.IsIntegral)
    (hv : (towerInclBar ℂ (dvd_of_eq_roof 1 3 2 6 hm').1).toRingHom.IsIntegral)
    (hv' : (towerSubstBar ℂ (1 * 2) 3 (dvd_of_eq_roof 1 3 2 6 hm').2).toRingHom.IsIntegral)
    (hex : HeckeExchangeAt ℂ 1 2 3 6 hm) (hex' : HeckeExchangeAt ℂ 1 3 2 6 hm')
    (D : Divisor ℂ (laurentBaseChange ℂ (modularFunctionFieldFull 1))) :
    heckeDivBar hα hβ (heckeDivBar hα' hβ' D)
      = heckeDivBar hα' hβ' (heckeDivBar hα hβ D) :=
  heckeDivBar_comm_of_heckeExchangeAt ℂ hm hm' hα hβ hα' hβ' hu hu' hv hv' hex hex' D

-- The `HeckeInputsAlong` splits and the `Pic0` descent: the operator commutation
-- at the same square.
example (hM : (6 : ℕ) = 1 * 2 * 3) (hM' : (6 : ℕ) = 1 * 3 * 2)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * 2))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * 3))]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar 6)]
    (hex : HeckeExchangeAt (AlgebraicClosure ℚ) 1 2 3 6 hM)
    (hex' : HeckeExchangeAt (AlgebraicClosure ℚ) 1 3 2 6 hM') :
    heckeOperatorBar 1 ⟨2, Nat.prime_two⟩ * heckeOperatorBar 1 ⟨3, Nat.prime_three⟩
      = heckeOperatorBar 1 ⟨3, Nat.prime_three⟩ * heckeOperatorBar 1 ⟨2, Nat.prime_two⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact heckeOperatorBar_comm_of_heckeExchangeAt 1 2 3 6 hM hM' hex hex'

-- The wire test: composing the reduction with the capstone's `WEX` binder and
-- m11's principal divisors yields the target `HeckeOperatorsCommuteBar 1`.
example (hP : ∀ (M : ℕ) [NeZero M],
      HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (hex : ∀ (ℓ ℓ' M : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M]
      (hM : M = 1 * ℓ * ℓ'), ℓ ≠ ℓ' → HeckeExchangeAt (AlgebraicClosure ℚ) 1 ℓ ℓ' M hM) :
    HeckeOperatorsCommuteBar 1 :=
  heckeOperatorsCommuteBar_of_heckeExchangeAt 1 hP hex

/-! ## Zone K — `[capstone]` the unconditional target -/

-- The headline of the effort: `ModularCurve.heckeOperatorsCommuteBar`, proved
-- in `HeckeCommuteBar.lean` from m9's roof, m10's integrality, m11's principal divisors,
-- m12's reduction and the ported `AlgebraicCurve` exchange.
#check @ModularCurve.heckeOperatorsCommuteBar
example (N : ℕ) [NeZero N] : ModularCurve.HeckeOperatorsCommuteBar N :=
  ModularCurve.heckeOperatorsCommuteBar N

/-! ## Zone X1-DEF — `[x1]` the X₁ function field, Jacobian and Hecke definitions
(`SET-X1-A`) -/

-- The X₁ layer field at `M = 2`: its `ℚ`-form, the `Γ₁(2) ⊓ Γ₀(1)` collapse, the
-- `⊓ Γ₀(t)` monotonicity and the divisor-index monotonicity.
example : x1FunctionFieldC ℚ 2 = x1FunctionField 2 := x1FunctionFieldC_rat 2
example : x1x0FunctionFieldC ℚ 2 1 = x1FunctionFieldC ℚ 2 := x1x0FunctionFieldC_one ℚ 2
example : x1FunctionFieldC ℚ 2 ≤ x1x0FunctionFieldC ℚ 2 4 :=
  x1FunctionFieldC_le_x1x0 ℚ 2 4
example : x1FunctionFieldC ℚ 2 ≤ x1FunctionFieldC ℚ 4 :=
  x1FunctionFieldC_le_of_dvd ℚ (M := 2) (by norm_num)

-- The bar field at `M = 2` is inhabited by a concrete element of the subfield.
example : x1FunctionFieldBar 2 := 1
example : Inhabited (x1FunctionFieldBar 2) := ⟨1⟩

-- The Jacobian `J₁(2)` and its layer form carry an `AddCommGroup` structure.
example : AddCommGroup (JOne 2) := inferInstance
example : AddCommGroup (JOneC 2 ℂ) := inferInstance

-- The definitional bridges of the α and β degeneracy maps at `M = 2`, `ℓ = 3`.
-- The β bridge is stated at its pinned hypothesis `HeckeBetaOneDefined 2 3`.
example (x : laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField 2)) :
    (heckeAlphaOneBar (AlgebraicClosure ℚ) 2 3 x : LaurentSeries (AlgebraicClosure ℚ)) = x :=
  coe_heckeAlphaOneBar 2 3 x
example (h : HeckeBetaOneDefined 2 3)
    (x : laurentBaseChange (AlgebraicClosure ℚ) (x1FunctionField 2)) :
    (heckeBetaOneBar (AlgebraicClosure ℚ) 2 3 x : LaurentSeries (AlgebraicClosure ℚ))
      = qExpand (AlgebraicClosure ℚ) 3 x :=
  coe_heckeBetaOneBar 2 3 h x

-- The three new `AlgebraicCurve` facts at the concrete bar field
-- `modularFunctionFieldBar 1`, whose `HasPrincipalDivisors` is m11's unconditional
-- instance; `φ = AlgHom.id` (degree-one self-extension), its integrality from
-- `Algebra.IsIntegral.of_finite`.
-- `set_option … in` cannot follow a doc comment; this is a `--` line, and the
-- instance is genuinely used by `Algebra.IsIntegral.isIntegral`, so suppress
-- rather than weaken (porting-playbook §6).
set_option linter.style.haveILetI false in
private theorem barOne_id_isIntegral :
    (AlgHom.id (AlgebraicClosure ℚ) (modularFunctionFieldBar 1)).toRingHom.IsIntegral := by
  haveI : Algebra.IsIntegral (modularFunctionFieldBar 1) (modularFunctionFieldBar 1) :=
    Algebra.IsIntegral.of_finite _ _
  intro x
  exact Algebra.IsIntegral.isIntegral x

-- m11's instance for the bar field, local to this zone so the `FundamentalIdentityAlong`
-- and `NormFormulaAlong` types elaborate (`HasPrincipalDivisors` is a class argument
-- of neither `PushforwardNormFormula` nor of the `Along` predicates' *source*, but it
-- is needed to state them and to feed the norm formula).
private instance barOne_hasPrincipalDivisors :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) :=
  hasPrincipalDivisors_modularFunctionFieldBar modularPolynomialFamily 1

example : Divisor.PushforwardNormFormula (AlgebraicClosure ℚ) (modularFunctionFieldBar 1)
    (modularFunctionFieldBar 1) :=
  Divisor.pushforwardNormFormula

example : FundamentalIdentityAlong (AlgebraicClosure ℚ)
    (AlgHom.id (AlgebraicClosure ℚ) (modularFunctionFieldBar 1)) barOne_id_isIntegral :=
  fundamentalIdentityAlong (AlgHom.id (AlgebraicClosure ℚ) (modularFunctionFieldBar 1))
    barOne_id_isIntegral
    (finiteAlong_of_surjective _ (fun x => ⟨x, rfl⟩))
    (separableAlong_of_charZero _ barOne_id_isIntegral)

example : NormFormulaAlong (AlgebraicClosure ℚ)
    (AlgHom.id (AlgebraicClosure ℚ) (modularFunctionFieldBar 1))
    (finiteAlong_of_surjective (AlgHom.id (AlgebraicClosure ℚ) (modularFunctionFieldBar 1))
      (fun x => ⟨x, rfl⟩)) :=
  normFormulaAlong (AlgHom.id (AlgebraicClosure ℚ) (modularFunctionFieldBar 1))
    (finiteAlong_of_surjective _ (fun x => ⟨x, rfl⟩))
    (separableAlong_of_charZero _ barOne_id_isIntegral)

/-! ## Zone X1-FF — `[x1-ff]` the X₁ function-field transcendence (`SET-X1-B`) -/

-- At `Γ = Γ₁(2)`: the finite-index instance is the ported `CongruenceSubgroup`
-- one, and `T ∈ Γ₁(2)` is the pinned membership test at `T = !![1,1;0,1]`.
private theorem gammaOneTwo_T_mem : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 2 := by
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- Node 1, instantiated at `Γ₁(2)` (no `#check`: the witness is what the
-- statement asserts).
example :
    ∃ x : ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2),
      Transcendental ℚ x ∧
      FiniteDimensional
        (IntermediateField.adjoin ℚ
          ({x} : Set (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2))))
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2)) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
    (CongruenceSubgroup.Gamma1 2) gammaOneTwo_T_mem

-- Node 2, base-changed to the concrete `L = ℚ̄` at the same `Γ₁(2)`.
example :
    ∃ y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2)),
      Transcendental (AlgebraicClosure ℚ) y ∧
      FiniteDimensional
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2)))))
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2))) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 2) gammaOneTwo_T_mem

-- The executed composition: destruct node 1 to obtain the concrete `x` with
-- `Transcendental ℚ x` and `FiniteDimensional ℚ⟮x⟯ _`, invoke node 2 at
-- `L = ℚ̄` on the same `Γ₁(2)`, and consume every resulting fact.
example :
    ∃ x : ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2),
      Transcendental ℚ x ∧
      FiniteDimensional
        (IntermediateField.adjoin ℚ
          ({x} : Set (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2))))
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2)) ∧
      ∃ y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2)),
        Transcendental (AlgebraicClosure ℚ) y ∧
        FiniteDimensional
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2)))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 2))) := by
  obtain ⟨x, hx, hfin⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
      (CongruenceSubgroup.Gamma1 2) gammaOneTwo_T_mem
  obtain ⟨y, hy, hfinY⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
      (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 2) gammaOneTwo_T_mem
  exact ⟨x, hx, hfin, y, hy, hfinY⟩

/-! ## Zone X1-C — `[x1-c]` the Hecke/diamond statement nodes (`SET-X1-C`) -/

-- Node 1's `hΓ'` at `(Γ, Γ', ℓ) = (⊤, Γ₁(2), 2)`, discharged from the concrete
-- matrix entries of `γ ∈ Γ₁(2)`: the stretched matrix is
-- `γ₁ = !![γ₀₀, 2γ₀₁; γ₁₀/2, γ₁₁]` with `2 ∣ γ₁₀`.
private theorem x1c_stretch_hyp :
    ∀ γ ∈ (CongruenceSubgroup.Gamma1 2 : Subgroup SL(2, ℤ)), ∃ γ₁ ∈ (⊤ : Subgroup SL(2, ℤ)),
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (2 : ℤ) * γ 0 1 ∧
        (2 : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  have h10 : ((γ 1 0 : ℤ) : ZMod 2) = 0 := ((CongruenceSubgroup.Gamma1_mem 2 γ).mp hγ).2.2
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) 2).mp h10
  have hdet : Matrix.det !![(γ 0 0 : ℤ), 2 * γ 0 1; c, γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    rw [hc] at h
    linear_combination h
  refine ⟨⟨!![(γ 0 0 : ℤ), 2 * γ 0 1; c, γ 1 1], hdet⟩, Subgroup.mem_top _, rfl, rfl, ?_, rfl⟩
  show (2 : ℤ) * c = γ 1 0
  exact hc.symm

-- Node 1 at `(K, Γ, Γ', ℓ) = (ℚ, ⊤, Γ₁(2), 2)`, consumed at the concrete ratio `1`.
example : ModularCurve.qExpand ℚ 2 '' ModularCurve.intFormRatiosC ℚ (⊤ : Subgroup SL(2, ℤ)) ⊆
    ModularCurve.intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 2) :=
  ModularCurve.qExpand_image_intFormRatiosC_subset ℚ
    (Γ := (⊤ : Subgroup SL(2, ℤ))) (Γ' := CongruenceSubgroup.Gamma1 2)
    (Subgroup.mem_top _) 2 x1c_stretch_hyp

example : ModularCurve.qExpand ℚ 2 (1 : LaurentSeries ℚ) ∈
    ModularCurve.intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 2) :=
  (ModularCurve.qExpand_image_intFormRatiosC_subset ℚ
    (Γ := (⊤ : Subgroup SL(2, ℤ))) (Γ' := CongruenceSubgroup.Gamma1 2)
    (Subgroup.mem_top _) 2 x1c_stretch_hyp)
    ⟨1, ModularCurve.one_mem_intFormRatiosC ℚ (⊤ : Subgroup SL(2, ℤ)), rfl⟩

-- Node 2 at `M = 2`, on the constant form `1` (a real integral `q`-expansion).
example : ∃ (D : ℤ)
    (f₁ : ModularForm (CongruenceSubgroup.Gamma1 2 : Subgroup (GL (Fin 2) ℝ)) 0)
    (p₁ : PowerSeries ℤ), D ≠ 0 ∧ ModularCurve.IsIntegralQExp f₁ p₁ ∧
      (⇑f₁ : UpperHalfPlane → ℂ) =
        (D : ℂ) • ((⇑(1 : ModularForm (CongruenceSubgroup.Gamma1 2 : Subgroup (GL (Fin 2) ℝ)) 0) :
          UpperHalfPlane → ℂ) ∣[(0 : ℤ)] (1 : SL(2, ℤ))) :=
  ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 2
    (1 : ModularForm (CongruenceSubgroup.Gamma1 2 : Subgroup (GL (Fin 2) ℝ)) 0)
    (by rw [ModularForm.one_coe_eq_one]; exact ModularCurve.isIntegralQExp_one)
    (1 : SL(2, ℤ)) (CongruenceSubgroup.Gamma0_mem.mpr (by simp))

-- Node 3 at `(M, d) = (2, 1)`, the automorphism applied to `1`.
example : ∃ σ : ModularCurve.x1FunctionField 2 ≃ₐ[ℚ] ModularCurve.x1FunctionField 2,
    ModularCurve.IsDiamondAut 2 1 σ ∧ σ 1 = 1 := by
  obtain ⟨σ, hσ⟩ := ModularCurve.exists_isDiamondAut 2 (by decide : Nat.Coprime 1 2)
  exact ⟨σ, hσ, map_one σ⟩

-- Node 4 at `L = ℚ̄`, `F₀ = x1FunctionField 2`, `σ₀ = (diamondAut 2 1).toRingEquiv`,
-- applied to the coefficient image of `1`.
example : ∃ τ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.x1FunctionField 2)) ≃ₐ[AlgebraicClosure ℚ]
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField 2)),
    ((τ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ)
            ((1 : ↥(ModularCurve.x1FunctionField 2)) : LaurentSeries ℚ),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (1 : ↥(ModularCurve.x1FunctionField 2)).2⟩ :
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.x1FunctionField 2))) : LaurentSeries (AlgebraicClosure ℚ))
      = ModularCurve.coeffEmb (AlgebraicClosure ℚ)
          (((ModularCurve.diamondAut 2 1).toRingEquiv 1 : ↥(ModularCurve.x1FunctionField 2)) :
            LaurentSeries ℚ) := by
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ)
    (ModularCurve.x1FunctionField 2) (ModularCurve.diamondAut 2 1).toRingEquiv
  exact ⟨τ, hτ 1⟩

-- The executed composition: the diamond automorphism at `(M, d) = (2, 1)` feeds
-- its underlying ring equivalence into the cover, and the resulting `ℚ̄`-automorphism
-- is applied to `1`.
example : ∃ (σ : ModularCurve.x1FunctionField 2 ≃ₐ[ℚ] ModularCurve.x1FunctionField 2)
    (τ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.x1FunctionField 2)) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField 2))),
    ModularCurve.IsDiamondAut 2 1 σ ∧
      ((τ ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ)
              ((1 : ↥(ModularCurve.x1FunctionField 2)) : LaurentSeries ℚ),
            ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (1 : ↥(ModularCurve.x1FunctionField 2)).2⟩ :
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.x1FunctionField 2))) : LaurentSeries (AlgebraicClosure ℚ))
        = ModularCurve.coeffEmb (AlgebraicClosure ℚ)
            (((σ.toRingEquiv 1) : ↥(ModularCurve.x1FunctionField 2)) : LaurentSeries ℚ) := by
  obtain ⟨σ, hσ⟩ := ModularCurve.exists_isDiamondAut 2 (by decide : Nat.Coprime 1 2)
  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ)
    (ModularCurve.x1FunctionField 2) σ.toRingEquiv
  exact ⟨σ, τ, hσ, hτ 1⟩

/-! ## Zone X1-CAP — `[x1-cap]` the capstone `ModularCurve.heckeDiamondInputsAll`

The effort's final wire test: the bundle is produced, then both of its halves are
destructured and consumed — the Hecke half's β-definedness and the diamond half's
automorphism — so deleting any module of SET-X1-A/B/C makes this zone fail. -/

-- The capstone at `M = 2` (so the `ℚ̄`-level fields are concrete).
example : ModularCurve.HeckeDiamondInputsAll 2 := ModularCurve.heckeDiamondInputsAll 2

-- The Hecke half at the concrete prime `ℓ = 3`: a real `HeckeInputsOneAlong` value.
example : HeckeInputsOneAlong (AlgebraicClosure ℚ) 2 3 :=
  (ModularCurve.heckeDiamondInputsAll 2).1 ⟨3, Nat.prime_three⟩

-- Its first projection, the pinned `HeckeBetaOneDefined`, consumed.
example : HeckeBetaOneDefined 2 3 :=
  ((ModularCurve.heckeDiamondInputsAll 2).1 ⟨3, Nat.prime_three⟩).1

-- The diamond half at `d = 1`: a real diamond automorphism of `x1FunctionField 2`.
example : ∃ σ : ModularCurve.x1FunctionField 2 ≃ₐ[ℚ] ModularCurve.x1FunctionField 2,
    ModularCurve.IsDiamondAut 2 1 σ :=
  ((ModularCurve.heckeDiamondInputsAll 2).2 1 (by decide : Nat.Coprime 1 2)).1

-- The diamond half's base-change witness, consumed as a real `AlgEquiv` and an
-- `IsBaseChangeAutOf` at `diamondAut 2 1`.
example : ∃ σ' : ModularCurve.x1FunctionFieldBar 2 ≃ₐ[AlgebraicClosure ℚ]
      ModularCurve.x1FunctionFieldBar 2,
    ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut 2 1) σ' :=
  ((ModularCurve.heckeDiamondInputsAll 2).2 1 (by decide : Nat.Coprime 1 2)).2

end
