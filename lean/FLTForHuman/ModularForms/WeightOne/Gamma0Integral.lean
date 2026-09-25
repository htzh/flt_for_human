/-
  Bounded-denominator integrality for `Γ`-invariant forms (SET-10 order 2).

  Statements verbatim from the pinned wrappers
  `Theorems/Thm_ModularCurve_exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant.lean`,
  `Theorems/Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.lean`
  and
  `Theorems/Thm_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean`;
  proofs transcribed from the matching `P2M/Sol/S_*` files (1,362 + 597 + 488
  lines) and adapted to mathlib `v4.34.0`.  Order 1's headlines are imported.

  `ModularCurve.IsIntegralQExp` is the pin's definition from
  `Definitions/Def_ModularCurve_X1.lean`, transcribed verbatim because the third
  headline's statement names it; the two proof-only X1 helpers (`restrictForm`,
  `Gamma1_le_of_dvd`) are carried `private` inside each package that needs them,
  per the cross-module-`private` policy.  Each pin file's helpers stay `private`
  in the pin's own inner namespace (`GammaNBounded` /
  `X1DiamondRationalForms` / `X1BoundedDenominators`), nested in this module's
  `WLightS10.S_*` namespaces.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1.lean

  The pin's `set_option maxHeartbeats` bumps are **not** transcribed (the
  project's global `maxHeartbeats` cap is 4,000,000).
-/

import FLTForHuman.ModularForms.WeightOne.Basic
import FLTForHuman.ModularForms.WeightOne.MonicRel
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import FLTForHuman.ModularForms.WeightOne.FrickeFunction
import FLTForHuman.ModularForms.WeightOne.LevelFraction
import FLTForHuman.ModularForms.WeightOne.LevelN
import FLTForHuman.ModularForms.WeightOne.EisensteinChiNegThree
import FLTForHuman.ModularForms.WeightOne.Gamma0Rationality
import FLTForHuman.ModularForms.JqAnalyticModel
import FLTForHuman.ModularCurve.Defs.Jq
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Geometry.Manifold.Notation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.Unramified.Field

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section

open Complex Real UpperHalfPlane ModularForm CongruenceSubgroup
open scoped Real Manifold MatrixGroups ModularForm Topology UpperHalfPlane

namespace ModularCurve

/-- The pin's `Def_ModularCurve_X1.IsIntegralQExp`: integrality of a `q`-expansion
against an integral power series. -/
def IsIntegralQExp (f : ℍ → ℂ) (p : PowerSeries ℤ) : Prop :=
  p.map (Int.castRingHom ℂ) = qExpansion 1 f

end ModularCurve

namespace WLightS10.S_ModularCurve_exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace GammaNBounded

private def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp at h1 h2
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 τ.im_pos.ne'
    subst hs
    simp at h2
    exact ⟨rfl, h2⟩

private theorem tauPair_spec (τ : ℍ) : (tauPair τ).ω₁ = (τ : ℂ) ∧ (tauPair τ).ω₂ = 1 := ⟨rfl, rfl⟩

variable (N : ℕ)

private def WW (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))

private def fricke (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ

private def jf (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

private theorem WW_spec (v : Fin 2 → ZMod N) (τ : ℍ) : WW N v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)) :=
  rfl

private theorem fricke_spec (v : Fin 2 → ZMod N) (τ : ℍ) : fricke N v τ =
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ := rfl

private theorem jf_spec (τ : ℍ) : jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := rfl

private def zetaN : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

private def kN : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

private def AZ : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {zetaN N}

private abbrev Idx : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

private def gen : Idx N → ℍ → ℂ := fun o => o.elim jf fun v => fricke N v.1

private def ev (R : MvPolynomial (Idx N) (kN N)) : ℍ → ℂ :=
  MvPolynomial.aeval (gen N) (MvPolynomial.map (algebraMap (kN N) ℂ) R)

section Cyclo

variable [NeZero N]

private theorem isPrimitiveRoot_zetaN : IsPrimitiveRoot (zetaN N) N :=
  Complex.isPrimitiveRoot_exp N (NeZero.ne N)

private scoped instance instIsCyclotomic : IsCyclotomicExtension {N} ℚ (kN N) := by
  have hζ := isPrimitiveRoot_zetaN N
  change IsCyclotomicExtension {N} ℚ (IntermediateField.adjoin ℚ {zetaN N}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (hζ.isIntegral (NeZero.pos N)).tower_top.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ

private scoped instance instIsGalois : IsGalois ℚ (kN N) := IsCyclotomicExtension.isGalois {N} ℚ (kN N)

private scoped instance instFiniteDimensional : FiniteDimensional ℚ (kN N) :=
  IsCyclotomicExtension.finiteDimensional {N} ℚ (kN N)

private scoped instance instFintypeAut : Fintype ((kN N) ≃ₐ[ℚ] (kN N)) := AlgEquiv.fintype ℚ (kN N)

private def zetaK : kN N := ⟨zetaN N, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

@[scoped simp] private theorem coe_zetaK : ((zetaK N : kN N) : ℂ) = zetaN N := rfl

private theorem isPrimitiveRoot_zetaK : IsPrimitiveRoot (zetaK N) N := by
  have h := isPrimitiveRoot_zetaN N
  rw [← coe_zetaK] at h
  exact IsPrimitiveRoot.coe_submonoidClass_iff.mp h

private theorem exists_pow_of_aut (σ : (kN N) ≃ₐ[ℚ] (kN N)) : ∃ s : ℕ, σ (zetaK N) = zetaK N ^ s := by
  have hμ := isPrimitiveRoot_zetaK N
  exact ⟨((hμ.autToPow ℚ σ : (ZMod N)ˣ) : ZMod N).val, by rw [hμ.autToPow_spec ℚ σ]⟩

private theorem exists_rat_of_fixed (x : kN N) (hx : ∀ σ : (kN N) ≃ₐ[ℚ] (kN N), σ x = x) :
    ∃ r : ℚ, x = algebraMap ℚ (kN N) r := by
  have := (IsGalois.mem_bot_iff_fixed x).2 hx
  rw [IntermediateField.mem_bot] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨r, hr.symm⟩

private theorem ratCast_mem (K : IntermediateField ℚ ℂ) (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

private theorem mem_AZ_iff (x : ℂ) : x ∈ AZ N ↔ ∃ p : Polynomial ℤ, x = Polynomial.aeval (zetaN N) p := by
  rw [AZ, Algebra.adjoin_singleton_eq_range_aeval]
  constructor
  · rintro ⟨p, hp⟩; exact ⟨p, hp.symm⟩
  · rintro ⟨p, hp⟩; exact ⟨p, hp.symm⟩

private theorem zetaN_mem_AZ : zetaN N ∈ AZ N := Algebra.subset_adjoin (Set.mem_singleton _)

private theorem AZ_le_kN : ∀ x ∈ AZ N, x ∈ kN N := by
  intro x hx
  rw [mem_AZ_iff] at hx
  obtain ⟨p, rfl⟩ := hx
  rw [Polynomial.aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  rw [zsmul_eq_mul]
  refine mul_mem ?_ (pow_mem (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)) _)
  exact_mod_cast ratCast_mem (kN N) (p.coeff i : ℚ)

private theorem aut_mem_AZ (σ : (kN N) ≃ₐ[ℚ] (kN N)) (x : kN N) (hx : (x : ℂ) ∈ AZ N) :
    ((σ x : kN N) : ℂ) ∈ AZ N := by
  rw [mem_AZ_iff] at hx
  obtain ⟨p, hp⟩ := hx
  obtain ⟨s, hs⟩ := exists_pow_of_aut N σ
  rw [Polynomial.aeval_eq_sum_range] at hp
  set y : kN N := ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : kN N) * zetaK N ^ i with hy
  have hcoe : ∀ z : kN N, (z : ℂ) = algebraMap (kN N) ℂ z := fun z => rfl
  have hyc : (y : ℂ) = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * zetaN N ^ i := by
    rw [hcoe, hy, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_intCast, ← hcoe, coe_zetaK]
  have hxK : x = y := by
    apply Subtype.ext
    rw [hp, hyc]
    exact Finset.sum_congr rfl fun i _ => by rw [zsmul_eq_mul]
  have hσy : σ y = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : kN N) * (zetaK N ^ s) ^ i := by
    rw [hy, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_intCast, hs]
  have hσc : ((σ x : kN N) : ℂ) = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (zetaN N ^ s) ^ i := by
    rw [hxK, hσy, hcoe, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_pow, map_intCast, ← hcoe, coe_zetaK]
  rw [hσc]
  refine sum_mem fun i _ => ?_
  refine mul_mem (by exact_mod_cast (AZ N).algebraMap_mem (p.coeff i)) (pow_mem (pow_mem (zetaN_mem_AZ N) s) _)

private theorem exists_int_of_mem_AZ_of_rat (r : ℚ) (hr : ((r : ℂ)) ∈ AZ N) : ∃ z : ℤ, (r : ℂ) = (z : ℂ) := by
  have hint : IsIntegral ℤ ((r : ℂ)) := by
    have hle : AZ N ≤ integralClosure ℤ ℂ := by
      rw [AZ, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact (isPrimitiveRoot_zetaN N).isIntegral (NeZero.pos N)
    exact hle hr
  have hint' : IsIntegral ℤ r := by
    have hint2 : IsIntegral ℤ (algebraMap ℚ ℂ r) := hint
    exact (isIntegral_algebraMap_iff).mp hint2
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint'
  refine ⟨z, ?_⟩
  rw [← hz]
  simp

private theorem exists_nat_mul_mem_AZ (x : ℂ) (hx : x ∈ kN N) : ∃ D : ℕ, D ≠ 0 ∧ (D : ℂ) * x ∈ AZ N := by
  have hint : IsIntegral ℚ (zetaN N) := ((isPrimitiveRoot_zetaN N).isIntegral (NeZero.pos N)).tower_top
  have hx' : x ∈ (Algebra.adjoin ℚ {zetaN N} : Subalgebra ℚ ℂ) := by
    have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic
    rw [← this]
    exact hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨p, rfl⟩ := hx'

  refine ⟨∏ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).den, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => (p.coeff i).den_nz
  · change ((∏ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).den : ℕ) : ℂ) * Polynomial.aeval (zetaN N) p ∈ AZ N
    rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
    refine sum_mem fun i hi => ?_
    rw [Algebra.smul_def, ← mul_assoc]
    refine mul_mem ?_ (pow_mem (zetaN_mem_AZ N) _)

    have hdvd : ((p.coeff i).den : ℤ) ∣ ∏ j ∈ Finset.range (p.natDegree + 1), ((p.coeff j).den : ℤ) :=
      Finset.dvd_prod_of_mem _ hi
    obtain ⟨c, hc⟩ := hdvd
    have hq : ((∏ j ∈ Finset.range (p.natDegree + 1), (p.coeff j).den : ℕ) : ℚ) * p.coeff i
        = ((c * (p.coeff i).num : ℤ) : ℚ) := by
      have h1 : ((∏ j ∈ Finset.range (p.natDegree + 1), (p.coeff j).den : ℕ) : ℚ)
          = ((p.coeff i).den : ℚ) * (c : ℚ) := by exact_mod_cast hc
      rw [h1, mul_comm ((p.coeff i).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
      push_cast; ring
    have : ((∏ j ∈ Finset.range (p.natDegree + 1), (p.coeff j).den : ℕ) : ℂ) * (algebraMap ℚ ℂ) (p.coeff i)
        = ((c * (p.coeff i).num : ℤ) : ℂ) := by
      have := congrArg (algebraMap ℚ ℂ) hq
      simpa using this
    rw [this]
    exact_mod_cast (AZ N).algebraMap_mem (c * (p.coeff i).num)

end Cyclo

section Nice

variable [NeZero N]

local notation "Δ" => ModularForm.discriminant

private theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

private def nice : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {g | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ Periodic (g ∘ ofComplex) N ∧ IsBoundedAtImInfty g}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨ha1.mul hb1, ?_, ha3.mul hb3⟩
    intro z; have h1 := ha2 z; have h2 := hb2 z
    simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢; rw [h1, h2]
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨ha1.add hb1, ?_, ha3.add hb3⟩
    intro z; have h1 := ha2 z; have h2 := hb2 z
    simp only [comp_apply, Pi.add_apply] at h1 h2 ⊢; rw [h1, h2]
  algebraMap_mem' c := by
    refine ⟨mdifferentiable_const, fun z => rfl, ?_⟩
    exact Filter.const_boundedAtFilter _ _

variable {N}

private theorem mem_nice {g : ℍ → ℂ} :
    g ∈ nice N ↔ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ Periodic (g ∘ ofComplex) N ∧ IsBoundedAtImInfty g := Iff.rfl

private theorem analyticAt_of_mem {g : ℍ → ℂ} (hg : g ∈ nice N) : AnalyticAt ℂ (cuspFunction N g) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) hg.2.1 hg.1 hg.2.2

variable (N) in

private def qE : nice N →ₐ[ℂ] PowerSeries ℂ where
  toFun g := qExpansion N (g : ℍ → ℂ)
  map_one' := qExpansion_one _
  map_mul' a b := qExpansion_mul (analyticAt_of_mem a.2) (analyticAt_of_mem b.2)
  map_zero' := qExpansion_zero _
  map_add' a b := qExpansion_add (analyticAt_of_mem a.2) (analyticAt_of_mem b.2)
  commutes' c := by
    change qExpansion N ((algebraMap ℂ (ℍ → ℂ)) c) = PowerSeries.C c
    have h1 : (algebraMap ℂ (ℍ → ℂ)) c = c • (1 : ℍ → ℂ) := by
      funext τ; simp
    rw [h1, qExpansion_smul (analyticAt_of_mem (nice N).one_mem), qExpansion_one, PowerSeries.smul_eq_C_mul,
      mul_one]

private theorem qE_apply (g : nice N) : qE N g = qExpansion N (g : ℍ → ℂ) := rfl

private theorem qE_eq_zero_iff (g : nice N) : qE N g = 0 ↔ (g : ℍ → ℂ) = 0 :=
  qExpansion_eq_zero_iff (natCast_pos N) g.2.2.1 g.2.1 g.2.2.2

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem levelOne_mem {k : ℤ} (f : ModularForm 𝒮ℒ k) : (⇑f : ℍ → ℂ) ∈ nice N :=
  ⟨f.holo', periodic_ofComplex_natCast (SlashInvariantFormClass.periodic_comp_ofComplex f
    one_mem_strictPeriods_SL) N, ModularFormClass.bdd_at_infty f⟩

private theorem disc_mem : (Δ : ℍ → ℂ) ∈ nice N := by
  have := levelOne_mem (N := N) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  exact this

private def dN : nice N := ⟨Δ, disc_mem⟩

@[scoped simp] private theorem coe_dN : ((dN : nice N) : ℍ → ℂ) = Δ := rfl

private def E4cube : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)

private theorem coe_E4cube : (⇑E4cube : ℍ → ℂ) = (E₄ : ℍ → ℂ) ^ 3 := by
  rw [E4cube, coe_mcast, coe_pow]

private theorem jf_mul_disc : jf * Δ = ⇑E4cube := by
  funext τ
  rw [coe_E4cube]
  simp only [Pi.mul_apply, Pi.pow_apply, jf]
  field_simp [discriminant_ne_zero τ]

private theorem jf_disc_mem : jf * Δ ∈ nice N := by rw [jf_mul_disc]; exact levelOne_mem _

private theorem fricke_disc_mem {v : Fin 2 → ZMod N} (hv : v ≠ 0) : fricke N v * Δ ∈ nice N := by
  obtain ⟨-, -, h3, h4, h5, -⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact ⟨(h3 v hv).mul mdifferentiable_disc, (h5 v hv).1, h4 v hv⟩

private theorem mdifferentiable_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke N v) := by
  obtain ⟨-, -, h3, -⟩ := WLight.frickeFunction_modularity_package N tauPair tauPair_spec
  exact h3 v hv

private theorem gen_disc_mem (o : Idx N) : gen N o * Δ ∈ nice N := by
  cases o with
  | none => exact jf_disc_mem
  | some v => exact fricke_disc_mem v.2

private theorem mdifferentiable_gen (o : Idx N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen N o) := by
  cases o with
  | none =>
      intro τ
      have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ => E₄ τ ^ 3) τ := (E₄.holo' τ).pow 3
      exact h1.div (mdifferentiable_disc τ) (discriminant_ne_zero τ)
  | some v => exact mdifferentiable_fricke v.2

end Nice

section Bdd

variable [NeZero N]

private def IsRat (φ : PowerSeries ℂ) : Prop := ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = φ

private def BddA (φ : PowerSeries ℂ) : Prop := ∃ D : ℕ, D ≠ 0 ∧ ∀ n, (D : ℂ) * φ.coeff n ∈ AZ N

variable {N}

private theorem isRat_iff {φ : PowerSeries ℂ} : IsRat φ ↔ ∀ n, ∃ r : ℚ, φ.coeff n = (r : ℂ) := by
  constructor
  · rintro ⟨p, rfl⟩ n
    exact ⟨PowerSeries.coeff n p, by rw [PowerSeries.coeff_map]; rfl⟩
  · intro h
    choose r hr using h
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩

private theorem IsRat.mul {φ ψ : PowerSeries ℂ} (h : IsRat φ) (h' : IsRat ψ) : IsRat (φ * ψ) := by
  obtain ⟨p, rfl⟩ := h; obtain ⟨p', rfl⟩ := h'; exact ⟨p * p', by rw [map_mul]⟩

private theorem IsRat.pow {φ : PowerSeries ℂ} (h : IsRat φ) (n : ℕ) : IsRat (φ ^ n) := by
  obtain ⟨p, rfl⟩ := h; exact ⟨p ^ n, by rw [map_pow]⟩

private theorem isRat_of_int (P : PowerSeries ℤ) : IsRat (P.map (Int.castRingHom ℂ)) :=
  ⟨P.map (Int.castRingHom ℚ), by ext n; simp [PowerSeries.coeff_map]⟩

private theorem BddA.mul {φ ψ : PowerSeries ℂ} (h : BddA N φ) (h' : BddA N ψ) : BddA N (φ * ψ) := by
  obtain ⟨D, hD, hφ⟩ := h
  obtain ⟨D', hD', hψ⟩ := h'
  refine ⟨D * D', mul_ne_zero hD hD', fun n => ?_⟩
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  refine sum_mem fun ij _ => ?_
  have : ((D * D' : ℕ) : ℂ) * (PowerSeries.coeff ij.1 φ * PowerSeries.coeff ij.2 ψ)
      = ((D : ℂ) * PowerSeries.coeff ij.1 φ) * ((D' : ℂ) * PowerSeries.coeff ij.2 ψ) := by
    push_cast; ring
  rw [this]
  exact mul_mem (hφ _) (hψ _)

private theorem BddA.add {φ ψ : PowerSeries ℂ} (h : BddA N φ) (h' : BddA N ψ) : BddA N (φ + ψ) := by
  obtain ⟨D, hD, hφ⟩ := h
  obtain ⟨D', hD', hψ⟩ := h'
  refine ⟨D * D', mul_ne_zero hD hD', fun n => ?_⟩
  rw [map_add, mul_add]
  have h1 : ((D * D' : ℕ) : ℂ) * PowerSeries.coeff n φ = (D' : ℂ) * ((D : ℂ) * PowerSeries.coeff n φ) := by
    push_cast; ring
  have h2 : ((D * D' : ℕ) : ℂ) * PowerSeries.coeff n ψ = (D : ℂ) * ((D' : ℂ) * PowerSeries.coeff n ψ) := by
    push_cast; ring
  rw [h1, h2]
  exact add_mem (mul_mem (by exact_mod_cast (AZ N).algebraMap_mem (D' : ℤ)) (hφ n))
    (mul_mem (by exact_mod_cast (AZ N).algebraMap_mem (D : ℤ)) (hψ n))

private theorem bddA_one : BddA N (1 : PowerSeries ℂ) := by
  refine ⟨1, one_ne_zero, fun n => ?_⟩
  rw [PowerSeries.coeff_one]
  split_ifs <;> simp [one_mem, zero_mem]

private theorem BddA.pow {φ : PowerSeries ℂ} (h : BddA N φ) (n : ℕ) : BddA N (φ ^ n) := by
  induction n with
  | zero => simpa using bddA_one
  | succ n ih => rw [pow_succ]; exact ih.mul h

private theorem bddA_of_int (P : PowerSeries ℤ) : BddA N (P.map (Int.castRingHom ℂ)) := by
  refine ⟨1, one_ne_zero, fun n => ?_⟩
  rw [PowerSeries.coeff_map, Nat.cast_one, one_mul]
  exact_mod_cast (AZ N).algebraMap_mem (PowerSeries.coeff n P)

private theorem bddA_C {κ : ℂ} (hκ : κ ∈ kN N) : BddA N (PowerSeries.C κ) := by
  obtain ⟨D, hD, hDκ⟩ := exists_nat_mul_mem_AZ N κ hκ
  refine ⟨D, hD, fun n => ?_⟩
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact hDκ
  · simp [zero_mem]

private theorem BddA.coeff_mem {φ : PowerSeries ℂ} (h : BddA N φ) (n : ℕ) : φ.coeff n ∈ kN N := by
  obtain ⟨D, hD, hφ⟩ := h
  have hDC : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have : PowerSeries.coeff n φ = (D : ℂ)⁻¹ * ((D : ℂ) * PowerSeries.coeff n φ) := by
    field_simp
  rw [this]
  refine mul_mem ?_ (AZ_le_kN N _ (hφ n))
  exact inv_mem (show (D : ℂ) ∈ kN N from by
    rw [show (D : ℂ) = algebraMap ℚ ℂ (D : ℚ) from rfl]
    exact (kN N).algebraMap_mem _)

private theorem exists_int_of_bddA_of_isRat {φ : PowerSeries ℂ} (hB : BddA N φ) (hR : IsRat φ) :
    ∃ (D : ℕ) (P : PowerSeries ℤ), D ≠ 0 ∧ P.map (Int.castRingHom ℂ) = (D : ℂ) • φ := by
  obtain ⟨D, hD, hφ⟩ := hB
  obtain ⟨p, rfl⟩ := hR
  have hz : ∀ n, ∃ z : ℤ, (D : ℂ) * PowerSeries.coeff n (p.map (algebraMap ℚ ℂ)) = (z : ℂ) := by
    intro n
    have h1 := hφ n
    rw [PowerSeries.coeff_map] at h1 ⊢
    have h2 : (D : ℂ) * (algebraMap ℚ ℂ) (PowerSeries.coeff n p) = (((D : ℚ) * PowerSeries.coeff n p : ℚ) : ℂ) := by
      push_cast; rfl
    rw [h2] at h1 ⊢
    exact exists_int_of_mem_AZ_of_rat N _ h1
  choose z hz using hz
  refine ⟨D, PowerSeries.mk z, hD, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_smul, smul_eq_mul, hz n]
  simp

end Bdd

section Generators

variable [NeZero N]

local notation "Δ" => ModularForm.discriminant

variable {N}

private theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

variable (N) in
private theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

variable (N) in

private theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := periodic_ofComplex_natCast hper N
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam N τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam N τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

private def spread (P : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if (N : ℕ) ∣ n then PowerSeries.coeff (n / N) P else 0

private theorem qExpansion_widthN_of_int {k : ℤ} (f : ModularForm 𝒮ℒ k) (P : PowerSeries ℤ)
    (hP : P.map (Int.castRingHom ℂ) = qExpansion 1 (⇑f : ℍ → ℂ)) :
    (spread (N := N) P).map (Int.castRingHom ℂ) = qExpansion N (⇑f : ℍ → ℂ) := by
  ext n
  have hw := qExpansion_coeff_widthN N (g := (⇑f : ℍ → ℂ)) f.holo'
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL) (ModularFormClass.bdd_at_infty f) n
  rw [PowerSeries.coeff_map]
  refine Eq.trans ?_ hw.symm
  rw [spread, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [← hP, PowerSeries.coeff_map]
  · simp

private def P4 : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 m : ℤ)

private theorem map_P4 : P4.map (Int.castRingHom ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n,
    P4, PowerSeries.coeff_mk, eq_intCast]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by
      rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]]
    push_cast
    ring

private def JZ : PowerSeries ℤ := spread (N := N) (P4 ^ 3)

private theorem map_JZ : (JZ (N := N)).map (Int.castRingHom ℂ) = qExpansion N (jf * Δ) := by
  rw [jf_mul_disc, JZ]
  apply qExpansion_widthN_of_int
  rw [map_pow, map_P4, E4cube, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

private def DZ : PowerSeries ℤ := spread (N := N) (PowerSeries.X * ModularCurve.dedekindEtaUnit)

private def UZ : PowerSeries ℤ := spread (N := N) ModularCurve.dedekindEtaUnit

private theorem map_DZ : (DZ (N := N)).map (Int.castRingHom ℂ) = qExpansion N (Δ : ℍ → ℂ) := by
  have := qExpansion_widthN_of_int (N := N) (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
    (PowerSeries.X * ModularCurve.dedekindEtaUnit) (by
      rw [← ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit]; rfl)
  exact this

private theorem constantCoeff_UZ : PowerSeries.constantCoeff (UZ (N := N)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, UZ, spread, PowerSeries.coeff_mk]
  simp [ModularCurve.constantCoeff_dedekindEtaUnit]

private theorem DZ_eq : DZ (N := N) = PowerSeries.X ^ N * UZ (N := N) := by
  ext n
  rw [PowerSeries.coeff_X_pow_mul', DZ, UZ, spread, spread, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have hN : 0 < N := NeZero.pos N
  by_cases hdvd : (N : ℕ) ∣ n
  · obtain ⟨k, rfl⟩ := hdvd
    rw [ite_eq_left (dvd_mul_right N k), Nat.mul_div_cancel_left _ hN]
    cases k with
    | zero =>
        rw [mul_zero]
        rcases Nat.lt_or_ge 0 N with h | h
        · rw [ite_eq_right (by omega)]
          simp
        · omega
    | succ k =>
        have hle : N ≤ N * (k + 1) := Nat.le_mul_of_pos_right N (Nat.succ_pos k)
        rw [ite_eq_left hle]
        have h1 : N * (k + 1) - N = N * k := by rw [Nat.mul_succ, Nat.add_sub_cancel]
        rw [h1, ite_eq_left (dvd_mul_right N k), Nat.mul_div_cancel_left _ hN, PowerSeries.coeff_succ_X_mul]
  · rw [ite_eq_right hdvd]
    by_cases hle : N ≤ n
    · have : ¬ (N : ℕ) ∣ n - N := by
        intro h; apply hdvd
        have := Nat.dvd_add h (dvd_refl N)
        rwa [Nat.sub_add_cancel hle] at this
      rw [ite_eq_left hle, ite_eq_right this]
    · rw [ite_eq_right hle]

private theorem bddA_disc : BddA N (qExpansion N (Δ : ℍ → ℂ)) := by
  rw [← map_DZ]; exact bddA_of_int _

private theorem isRat_disc : IsRat (qExpansion N (Δ : ℍ → ℂ)) := by
  rw [← map_DZ]; exact isRat_of_int _

private theorem bddA_jf : BddA N (qExpansion N (jf * Δ)) := by
  rw [← map_JZ]; exact bddA_of_int _

private theorem isRat_jf : IsRat (qExpansion N (jf * Δ)) := by
  rw [← map_JZ]; exact isRat_of_int _

private theorem bddA_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : BddA N (qExpansion N (fricke N v * Δ)) := by
  obtain ⟨D, hD, h⟩ := ModularCurve.exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin N tauPair
    tauPair_spec (WW N) (WW_spec N) (fricke N) (fricke_spec N) v hv
  exact ⟨D, hD, h⟩

private theorem bddA_gen (o : Idx N) : BddA N (qExpansion N (gen N o * Δ)) := by
  cases o with
  | none => exact bddA_jf
  | some v => exact bddA_fricke v.2

end Generators

section GoodAt

variable [NeZero N]

local notation "Δ" => ModularForm.discriminant

variable {N}

private def GoodAt (e : ℕ) (g : ℍ → ℂ) : Prop := g * Δ ^ e ∈ nice N ∧ BddA N (qExpansion N (g * Δ ^ e))

private theorem GoodAt.mul {e e' : ℕ} {g g' : ℍ → ℂ} (h : GoodAt (N := N) e g) (h' : GoodAt (N := N) e' g') :
    GoodAt (N := N) (e + e') (g * g') := by
  have heq : g * g' * Δ ^ (e + e') = (g * Δ ^ e) * (g' * Δ ^ e') := by rw [pow_add]; ring
  refine ⟨by rw [heq]; exact mul_mem h.1 h'.1, ?_⟩
  rw [heq]
  have := (qE N).map_mul ⟨_, h.1⟩ ⟨_, h'.1⟩
  change qExpansion N ((g * Δ ^ e) * (g' * Δ ^ e')) = _ at this
  rw [this]
  exact h.2.mul h'.2

private theorem GoodAt.add {e : ℕ} {g g' : ℍ → ℂ} (h : GoodAt (N := N) e g) (h' : GoodAt (N := N) e g') :
    GoodAt (N := N) e (g + g') := by
  have heq : (g + g') * Δ ^ e = g * Δ ^ e + g' * Δ ^ e := by ring
  refine ⟨by rw [heq]; exact add_mem h.1 h'.1, ?_⟩
  rw [heq]
  have := (qE N).map_add ⟨_, h.1⟩ ⟨_, h'.1⟩
  change qExpansion N (g * Δ ^ e + g' * Δ ^ e) = _ at this
  rw [this]
  exact h.2.add h'.2

private theorem goodAt_disc : GoodAt (N := N) 0 (Δ : ℍ → ℂ) := by
  refine ⟨by simpa using (disc_mem (N := N)), ?_⟩
  simpa using (bddA_disc (N := N))

private theorem GoodAt.succ {e : ℕ} {g : ℍ → ℂ} (h : GoodAt (N := N) e g) : GoodAt (N := N) (e + 1) g := by
  have := h.mul goodAt_disc
  have heq : g * Δ ^ (e + 1) = g * Δ * Δ ^ (e + 0) := by ring
  refine ⟨?_, ?_⟩
  · rw [heq]; exact this.1
  · rw [heq]; exact this.2

private theorem GoodAt.of_le {e e' : ℕ} (hle : e ≤ e') {g : ℍ → ℂ} (h : GoodAt (N := N) e g) : GoodAt (N := N) e' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right e d)).succ

private theorem goodAt_const {κ : ℂ} (hκ : κ ∈ kN N) : GoodAt (N := N) 0 (fun _ : ℍ => κ) := by
  have hmem : (fun _ : ℍ => κ) ∈ nice N := (nice N).algebraMap_mem κ
  refine ⟨by simpa using hmem, ?_⟩
  have : qExpansion N ((fun _ : ℍ => κ) * Δ ^ 0) = PowerSeries.C κ := by
    rw [pow_zero, mul_one]
    have := (qE N).commutes κ
    exact this
  rw [this]
  exact bddA_C hκ

private theorem goodAt_gen (o : Idx N) : GoodAt (N := N) 1 (gen N o) :=
  ⟨by rw [pow_one]; exact gen_disc_mem o, by rw [pow_one]; exact bddA_gen o⟩

private theorem exists_goodAt_ev (R : MvPolynomial (Idx N) (kN N)) : ∃ e : ℕ, GoodAt (N := N) e (ev N R) := by
  induction R using MvPolynomial.induction_on with
  | C κ =>
      refine ⟨0, ?_⟩
      have : ev N (MvPolynomial.C κ) = fun _ : ℍ => (κ : ℂ) := by
        funext τ; simp [ev]
      rw [this]
      exact goodAt_const κ.2
  | add p q hp hq =>
      obtain ⟨e, he⟩ := hp
      obtain ⟨e', he'⟩ := hq
      refine ⟨e + e', ?_⟩
      have : ev N (p + q) = ev N p + ev N q := by simp [ev, map_add]
      rw [this]
      exact (he.of_le (Nat.le_add_right e e')).add (he'.of_le (Nat.le_add_left e' e))
  | mul_X p o hp =>
      obtain ⟨e, he⟩ := hp
      refine ⟨e + 1, ?_⟩
      have : ev N (p * MvPolynomial.X o) = ev N p * gen N o := by
        simp [ev, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
      rw [this]
      exact he.mul (goodAt_gen o)

end GoodAt

section Flat

variable [NeZero N]

local notation "Δ" => ModularForm.discriminant

variable (K : IntermediateField ℚ ℂ)

private structure RatAt (M : ℕ) (g : ℍ → ℂ) : Prop where
  mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g
  periodic : Periodic ((g * Δ ^ M) ∘ ofComplex) N
  bdd : IsBoundedAtImInfty (g * Δ ^ M)
  mem : ∀ n, (qExpansion N (g * Δ ^ M)).coeff n ∈ K

variable {N K}

private theorem ratAt_of_mem_nice {M : ℕ} {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hmem : g * Δ ^ M ∈ nice N)
    (hrat : IsRat (qExpansion N (g * Δ ^ M))) : RatAt N K M g where
  mdiff := hg
  periodic := hmem.2.1
  bdd := hmem.2.2
  mem n := by
    obtain ⟨r, hr⟩ := isRat_iff.mp hrat n
    rw [hr]; exact ratCast_mem K r

private theorem exists_rat_combination (K : IntermediateField ℚ ℂ) {ι : Type} [Fintype ι] {M : ℕ} {Gi : ι → ℍ → ℂ}
    {G : ℍ → ℂ} (hGi : ∀ i, RatAt N K M (Gi i)) (hG : RatAt N K M G)
    (hmem : G ∈ Submodule.span ℂ (Set.range Gi)) :
    ∃ κ : ι → K, G = ∑ i, (κ i : ℂ) • Gi i := by
  classical
  by_cases hW : G ∈ Submodule.span K (Set.range Gi)
  · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hW
    exact ⟨c, by rw [← hc]; rfl⟩
  exfalso
  obtain ⟨b, hb_sub, hb_span, hb_ind⟩ := exists_linearIndependent K (Set.range Gi)
  have hbfin : b.Finite := (Set.finite_range Gi).subset hb_sub
  have hGb : G ∉ b := fun h => hW (hb_span ▸ Submodule.subset_span h)
  have hGspan : G ∉ Submodule.span K b := by rwa [hb_span]
  have hins : LinearIndepOn K id (insert G b) := LinearIndepOn.id_insert hb_ind hGspan
  set sF : Finset (ℍ → ℂ) := (hbfin.insert G).toFinset with hsF
  have hcoe : (↑sF : Set (ℍ → ℂ)) = insert G b := Set.Finite.coe_toFinset _
  have hdata : ∀ f ∈ sF, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
      Function.Periodic ((f * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (f * ModularForm.discriminant ^ M) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f * ModularForm.discriminant ^ M)).coeff n ∈ K := by
    intro f hf
    have hf' : f ∈ insert G b := by rwa [← hcoe, Finset.mem_coe]
    rcases hf' with rfl | hf'
    · exact ⟨hG.mdiff, hG.periodic, hG.bdd, hG.mem⟩
    · obtain ⟨i, rfl⟩ := hb_sub hf'
      exact ⟨(hGi i).mdiff, (hGi i).periodic, (hGi i).bdd, (hGi i).mem⟩
  have hind : LinearIndependent K (fun w : ↥(↑sF : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) := by
    rw [hcoe]; exact hins
  have hC := WLight.linearIndependent_complex_of_qExpansion_rational N K sF M hdata hind
  rw [hcoe] at hC
  have hC' : LinearIndepOn ℂ id (insert G b) := hC
  have hnot := hC'.notMem_span_of_insert hGb
  rw [Set.image_id] at hnot
  apply hnot
  have hle : Submodule.span ℂ (Set.range Gi) ≤ Submodule.span ℂ b := by
    rw [Submodule.span_le]
    intro x hx
    have hxK : x ∈ Submodule.span K b := by rw [hb_span]; exact Submodule.subset_span hx
    exact Submodule.span_subset_span K ℂ b hxK
  exact hle hmem

private theorem exists_rat_monic (m : ℕ) {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (hGm : G * Δ ^ m ∈ nice N)
    (hrat : IsRat (qExpansion N (G * Δ ^ m)))
    {d : ℕ} (p : Fin d → Polynomial ℂ)
    (hrel : ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0) :
    ∃ (L : ℕ) (b : Fin d → Fin (L + 1) → ℚ),
      G ^ d = ∑ i : Fin d, ∑ l : Fin (L + 1), ((b i l : ℚ) : ℂ) • (jf ^ (l : ℕ) * G ^ (i : ℕ)) := by
  classical
  set L : ℕ := ∑ i, (p i).natDegree with hL
  have hLi : ∀ i, (p i).natDegree < L + 1 := fun i =>
    Nat.lt_succ_of_le (Finset.single_le_sum (f := fun j => (p j).natDegree) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i))
  set M : ℕ := L + m * d with hM

  set Gi : Fin d × Fin (L + 1) → ℍ → ℂ := fun il => jf ^ (il.2 : ℕ) * G ^ (il.1 : ℕ) with hGi

  have hjm : (jf * Δ) ∈ nice N := jf_disc_mem
  have key : ∀ (l i r : ℕ), jf ^ l * G ^ i * Δ ^ (l + m * i + r) ∈ nice N ∧
      IsRat (qExpansion N (jf ^ l * G ^ i * Δ ^ (l + m * i + r))) := by
    intro l i r
    have heq : jf ^ l * G ^ i * Δ ^ (l + m * i + r) = (jf * Δ) ^ l * (G * Δ ^ m) ^ i * Δ ^ r := by
      rw [pow_add, pow_add, pow_mul]; ring
    rw [heq]
    set a : nice N := ⟨jf * Δ, hjm⟩
    set g : nice N := ⟨G * Δ ^ m, hGm⟩
    have hmem : (jf * Δ) ^ l * (G * Δ ^ m) ^ i * Δ ^ r ∈ nice N := (a ^ l * g ^ i * dN ^ r).2
    refine ⟨hmem, ?_⟩
    have : qExpansion N ((jf * Δ) ^ l * (G * Δ ^ m) ^ i * Δ ^ r) = qE N (a ^ l * g ^ i * dN ^ r) := rfl
    rw [this, map_mul, map_mul, map_pow, map_pow, map_pow]
    exact ((isRat_jf.pow l).mul (hrat.pow i)).mul (isRat_disc.pow r)
  have hexp : ∀ (i : Fin d) (l : Fin (L + 1)), (l : ℕ) + m * i ≤ M := by
    intro i l
    have h1 : (l : ℕ) ≤ L := Nat.lt_succ_iff.mp l.2
    have h2 : m * (i : ℕ) ≤ m * d := Nat.mul_le_mul_left m i.2.le
    omega
  have hGiRat : ∀ il, RatAt N (⊥ : IntermediateField ℚ ℂ) M (Gi il) := by
    rintro ⟨i, l⟩
    obtain ⟨hn, hr⟩ := key l i (M - (l + m * i))
    have hM' : (l : ℕ) + m * i + (M - (l + m * i)) = M := Nat.add_sub_cancel' (hexp i l)
    rw [hM'] at hn hr
    exact ratAt_of_mem_nice (((mdifferentiable_gen (N := N) none).pow _).mul (hG.pow _)) hn hr
  have hGdRat : RatAt N (⊥ : IntermediateField ℚ ℂ) M (G ^ d) := by
    obtain ⟨hn, hr⟩ := key 0 d L
    have h0 : (0 : ℕ) + m * d + L = M := by omega
    rw [pow_zero, one_mul, h0] at hn hr
    exact ratAt_of_mem_nice (hG.pow _) hn hr

  have hmem : G ^ d ∈ Submodule.span ℂ (Set.range Gi) := by
    have hfun : G ^ d = ∑ i : Fin d, ∑ l : Fin (L + 1), (-(p i).coeff l) • Gi (i, l) := by
      funext τ
      have h1 := hrel τ
      have h2 : ∀ i : Fin d, (p i).eval (jf τ) = ∑ l : Fin (L + 1), (p i).coeff l * jf τ ^ (l : ℕ) := by
        intro i
        rw [Polynomial.eval_eq_sum_range' (hLi i), Finset.sum_range]
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul, hGi]
      have h3 : G τ ^ d = -∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) := eq_neg_of_add_eq_zero_left h1
      rw [h3, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h2 i, Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [hfun]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun l _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, l), rfl⟩)
  obtain ⟨κ, hκ⟩ := exists_rat_combination (N := N) ⊥ hGiRat hGdRat hmem
  have hb : ∀ il, ∃ r : ℚ, (κ il : ℂ) = (r : ℂ) := by
    intro il
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp (κ il).2
    exact ⟨r, hr.symm⟩
  choose b hb using hb
  refine ⟨L, fun i l => b (i, l), ?_⟩
  rw [hκ, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hb]

end Flat

section Series

variable [NeZero N]

local notation "Δ" => ModularForm.discriminant

variable {N}

private def BddQ (ψ : PowerSeries ℚ) : Prop :=
  ∃ (D : ℕ) (Ψ : PowerSeries ℤ), D ≠ 0 ∧ Ψ.map (Int.castRingHom ℚ) = (D : ℚ) • ψ

private theorem map_rat_injective : Function.Injective (PowerSeries.map (algebraMap ℚ ℂ)) := by
  intro a b h
  ext n
  have := congrArg (PowerSeries.coeff n) h
  simpa [PowerSeries.coeff_map] using this

private theorem map_int_rat (P : PowerSeries ℤ) :
    (P.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) = P.map (Int.castRingHom ℂ) := by
  ext n; simp [PowerSeries.coeff_map]

private theorem bddQ_of_bddA_isRat {ψ : PowerSeries ℚ} (hB : BddA N (ψ.map (algebraMap ℚ ℂ))) : BddQ ψ := by
  obtain ⟨D, P, hD, hP⟩ := exists_int_of_bddA_of_isRat hB ⟨ψ, rfl⟩
  refine ⟨D, P, hD, map_rat_injective ?_⟩
  rw [map_int_rat, hP]
  ext n
  simp [PowerSeries.coeff_map]

private theorem bddQ_ratCast_smul_int (r : ℚ) (P : PowerSeries ℤ) : BddQ (r • P.map (Int.castRingHom ℚ)) := by
  refine ⟨r.den, PowerSeries.C r.num * P, r.den_nz, ?_⟩
  ext n
  have h : (r.den : ℚ) * r = r.num := Rat.den_mul_eq_num r
  rw [PowerSeries.coeff_map, PowerSeries.coeff_C_mul, PowerSeries.coeff_smul, PowerSeries.coeff_smul,
    PowerSeries.coeff_map, smul_eq_mul, smul_eq_mul, eq_intCast, eq_intCast]
  push_cast
  rw [← h]
  ring

private theorem BddQ.add {ψ ψ' : PowerSeries ℚ} (h : BddQ ψ) (h' : BddQ ψ') : BddQ (ψ + ψ') := by
  obtain ⟨D, Ψ, hD, hΨ⟩ := h
  obtain ⟨D', Ψ', hD', hΨ'⟩ := h'
  refine ⟨D * D', PowerSeries.C (D' : ℤ) * Ψ + PowerSeries.C (D : ℤ) * Ψ', mul_ne_zero hD hD', ?_⟩
  ext n
  have h1 := congrArg (PowerSeries.coeff n) hΨ
  have h2 := congrArg (PowerSeries.coeff n) hΨ'
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_smul, smul_eq_mul, eq_intCast] at h1 h2
  have h3 : PowerSeries.coeff n (PowerSeries.C (D' : ℤ) * Ψ + PowerSeries.C (D : ℤ) * Ψ')
      = D' * PowerSeries.coeff n Ψ + D * PowerSeries.coeff n Ψ' := by
    rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_map, h3, PowerSeries.coeff_smul, smul_eq_mul, eq_intCast]
  push_cast
  rw [h1, h2, map_add]
  ring

private theorem BddQ.neg {ψ : PowerSeries ℚ} (h : BddQ ψ) : BddQ (-ψ) := by
  obtain ⟨D, Ψ, hD, hΨ⟩ := h
  exact ⟨D, -Ψ, hD, by rw [map_neg, hΨ, smul_neg]⟩

private theorem bddQ_zero : BddQ (0 : PowerSeries ℚ) := ⟨1, 0, one_ne_zero, by simp⟩

private theorem bddQ_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (h : ∀ i ∈ s, BddQ (f i)) :
    BddQ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bddQ_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem periodic_of_gamma_invariant {G : ℍ → ℂ}
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ) : Periodic (G ∘ ofComplex) N := by
  have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
    rw [Gamma_mem, ModularGroup.coe_T_zpow]
    simp
  intro w
  by_cases hw : 0 < im w
  · have this : 0 < im (w + N) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    have := hinv _ hT ⟨w, hw⟩
    convert this using 2
    ext
    rw [UpperHalfPlane.modular_T_zpow_smul]
    simp [add_comm, UpperHalfPlane.coe_vadd]
  · push Not at hw
    have : im (w + N) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

private theorem exists_series_data (m : ℕ) (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ : ℍ => G (α • τ)) * Δ ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion N (G * Δ ^ m)).coeff n = (r : ℂ)) :
    ∃ (L d : ℕ) (y₀ : PowerSeries ℚ) (c₀ : Fin d → PowerSeries ℚ) (q r : PowerSeries ℂ),
      y₀.map (algebraMap ℚ ℂ) = qExpansion N (G * Δ ^ m) * qExpansion N (Δ : ℍ → ℂ) ^ L ∧
      (∀ i, BddQ (c₀ i)) ∧
      y₀ ^ d + ∑ i : Fin d, c₀ i * y₀ ^ (i : ℕ) = 0 ∧
      q ≠ 0 ∧ BddA N q ∧ BddA N r ∧ y₀.map (algebraMap ℚ ℂ) * q = r := by
  classical

  have hperG : Periodic (G ∘ ofComplex) N := periodic_of_gamma_invariant hinv
  have hΔm : (Δ ^ m : ℍ → ℂ) ∈ nice N := pow_mem disc_mem m
  have hGm : G * Δ ^ m ∈ nice N := by
    refine ⟨hG.mul (mdifferentiable_disc.pow m), ?_, by simpa using hbd 1⟩
    intro w
    have h1 := hperG w
    have h2 := hΔm.2.1 w
    simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢
    rw [h1, h2]
  have hGrat : IsRat (qExpansion N (G * Δ ^ m)) := isRat_iff.mpr hrat

  have hcoeff : ∀ n, (qExpansion N (G * Δ ^ m)).coeff n ∈ kN N := by
    intro n; obtain ⟨r, hr⟩ := hrat n; rw [hr]; exact ratCast_mem (kN N) r
  obtain ⟨P, Q, hQ0, hGQ⟩ := ModularCurve.exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem N
    tauPair tauPair_spec (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) rfl m G hG hinv hbd hcoeff
  change ev N Q ≠ 0 at hQ0
  change G * ev N Q = ev N P at hGQ

  obtain ⟨d, p, -, hrel⟩ := WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient N tauPair tauPair_spec
    (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) rfl G hG P Q hQ0 hGQ

  obtain ⟨L, b, hb⟩ := exists_rat_monic m hG hGm hGrat p hrel

  obtain ⟨eQ, heQ⟩ := exists_goodAt_ev (N := N) Q
  obtain ⟨eP, heP⟩ := exists_goodAt_ev (N := N) P
  set e : ℕ := eQ + eP with he
  have hQe : GoodAt (N := N) e (ev N Q) := heQ.of_le (Nat.le_add_right _ _)
  have hPe : GoodAt (N := N) e (ev N P) := heP.of_le (Nat.le_add_left _ _)

  set E : ℕ := m + L with hE
  set gm : nice N := ⟨G * Δ ^ m, hGm⟩ with hgm
  set y : nice N := gm * dN ^ L with hy
  set jn : nice N := ⟨jf * Δ, jf_disc_mem⟩ with hjn
  set qn : nice N := ⟨ev N Q * Δ ^ e, hQe.1⟩ with hqn
  set pn : nice N := ⟨ev N P * Δ ^ e, hPe.1⟩ with hpn
  have hy_coe : ((y : nice N) : ℍ → ℂ) = G * Δ ^ m * Δ ^ L := rfl

  have hexp : ∀ (i : Fin d) (l : Fin (L + 1)), E * d = (l : ℕ) + E * i + (E * (d - i) - l) := by
    intro i l
    have hl : (l : ℕ) ≤ L := Nat.lt_succ_iff.mp l.2
    have hdi : 1 ≤ d - i := by have := i.2; omega
    have h1 : E ≤ E * (d - i) := Nat.le_mul_of_pos_right E hdi
    have h2 : E * d = E * i + E * (d - i) := by rw [← Nat.mul_add, Nat.add_sub_cancel' i.2.le]
    omega
  set kk : Fin d → Fin (L + 1) → ℕ := fun i l => E * (d - i) - l with hkk

  set Z : nice N := ∑ i : Fin d, ∑ l : Fin (L + 1), ((b i l : ℚ) : ℂ) • (jn ^ (l : ℕ) * y ^ (i : ℕ) * dN ^ kk i l)
    with hZ
  have hZ_coe : ((Z : nice N) : ℍ → ℂ) =
      ∑ i : Fin d, ∑ l : Fin (L + 1), ((b i l : ℚ) : ℂ) • ((jf * Δ) ^ (l : ℕ) * (G * Δ ^ m * Δ ^ L) ^ (i : ℕ) * Δ ^ kk i l) := by
    rw [hZ]
    push_cast
    rfl
  have hId1 : y ^ d = Z := by
    apply Subtype.ext
    rw [hZ_coe]
    change (G * Δ ^ m * Δ ^ L) ^ d = _
    calc (G * Δ ^ m * Δ ^ L) ^ d = G ^ d * Δ ^ (E * d) := by rw [hE]; ring
      _ = (∑ i : Fin d, ∑ l : Fin (L + 1), ((b i l : ℚ) : ℂ) • (jf ^ (l : ℕ) * G ^ (i : ℕ))) * Δ ^ (E * d) := by
          rw [← hb]
      _ = ∑ i : Fin d, ∑ l : Fin (L + 1), ((b i l : ℚ) : ℂ) • (jf ^ (l : ℕ) * G ^ (i : ℕ) * Δ ^ (E * d)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [smul_mul_assoc]
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
          congr 1
          rw [hexp i l, pow_add, pow_add, hkk, hE]
          ring

  have hS1 : (qE N y) ^ d = ∑ i : Fin d, ∑ l : Fin (L + 1),
      ((b i l : ℚ) : ℂ) • ((qE N jn) ^ (l : ℕ) * (qE N y) ^ (i : ℕ) * (qE N dN) ^ kk i l) := by
    rw [← map_pow, hId1, hZ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, map_mul, map_mul, map_pow, map_pow, map_pow]

  have hId2 : y * qn = pn * dN ^ E := by
    apply Subtype.ext
    change (G * Δ ^ m * Δ ^ L) * (ev N Q * Δ ^ e) = (ev N P * Δ ^ e) * Δ ^ E
    rw [← hGQ, hE, pow_add]
    ring
  have hS2 : qE N y * qE N qn = qE N pn * (qE N dN) ^ E := by
    rw [← map_mul, hId2, map_mul, map_pow]

  have hqEy : qE N y = qExpansion N (G * Δ ^ m) * qExpansion N (Δ : ℍ → ℂ) ^ L := by
    rw [hy, map_mul, map_pow]; rfl
  have hqEjn : qE N jn = (JZ (N := N)).map (Int.castRingHom ℂ) := by rw [map_JZ]; rfl
  have hqEdN : qE N dN = (DZ (N := N)).map (Int.castRingHom ℂ) := by rw [map_DZ]; rfl
  have hYrat : IsRat (qE N y) := by rw [hqEy]; exact hGrat.mul (isRat_disc.pow L)
  obtain ⟨y₀, hy₀⟩ := hYrat

  set c₀ : Fin d → PowerSeries ℚ := fun i =>
    -∑ l : Fin (L + 1), (b i l) • ((JZ (N := N) ^ (l : ℕ) * DZ (N := N) ^ kk i l).map (Int.castRingHom ℚ)) with hc₀
  have hc₀map : ∀ i, (c₀ i).map (algebraMap ℚ ℂ) =
      -∑ l : Fin (L + 1), ((b i l : ℚ) : ℂ) • ((qE N jn) ^ (l : ℕ) * (qE N dN) ^ kk i l) := by
    intro i
    rw [hc₀, map_neg, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_int_rat, map_mul, map_pow, map_pow,
      ← hqEjn, ← hqEdN, PowerSeries.smul_eq_C_mul]
    rfl
  refine ⟨L, d, y₀, c₀, qE N qn, qE N pn * (qE N dN) ^ E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hy₀, hqEy]
  · intro i
    rw [hc₀]
    refine (bddQ_sum _ _ fun l _ => ?_).neg
    exact bddQ_ratCast_smul_int _ _
  · apply map_rat_injective
    rw [map_add, map_pow, map_sum, map_zero, hy₀, hS1]
    simp only [map_mul, map_pow, hc₀map, hy₀]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [neg_mul, Finset.sum_mul, ← sub_eq_add_neg, sub_eq_zero]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc]
    congr 1
    ring
  · rw [Ne, qE_eq_zero_iff]
    change ev N Q * Δ ^ e ≠ 0
    intro h0
    apply hQ0
    funext τ
    have := congrFun h0 τ
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply, mul_eq_zero] at this
    rcases this with h1 | h1
    · exact h1
    · exact absurd h1 (pow_ne_zero _ (discriminant_ne_zero τ))
  · exact hQe.2
  · exact hPe.2.mul (bddA_disc.pow E)
  · rw [hy₀]; exact hS2

end Series

section Galois

variable [NeZero N]

variable {N}

private def liftK (φ : PowerSeries ℂ) (hφ : ∀ n, φ.coeff n ∈ kN N) : PowerSeries (kN N) :=
  PowerSeries.mk fun n => ⟨φ.coeff n, hφ n⟩

private theorem map_liftK (φ : PowerSeries ℂ) (hφ : ∀ n, φ.coeff n ∈ kN N) :
    (liftK φ hφ).map (algebraMap (kN N) ℂ) = φ := by
  ext n; simp [liftK]

private theorem coe_algebraMap (x : kN N) : algebraMap (kN N) ℂ x = (x : ℂ) := rfl

private theorem map_K_injective : Function.Injective (PowerSeries.map (algebraMap (kN N) ℂ)) := by
  intro a b h
  ext n
  have := congrArg (PowerSeries.coeff n) h
  simp only [PowerSeries.coeff_map] at this
  exact_mod_cast this

private theorem map_map' {R S T : Type*} [Semiring R] [Semiring S] [Semiring T] (f : R →+* S) (g : S →+* T)
    (φ : PowerSeries R) : (φ.map f).map g = φ.map (g.comp f) := by
  ext n; simp [PowerSeries.coeff_map]

private theorem map_rat_K (y : PowerSeries ℚ) :
    (y.map (algebraMap ℚ (kN N))).map (algebraMap (kN N) ℂ) = y.map (algebraMap ℚ ℂ) := by
  rw [map_map']
  congr 1

private def BddK (ψ : PowerSeries (kN N)) : Prop :=
  ∃ D : ℕ, D ≠ 0 ∧ ∀ n, (((D : kN N) * ψ.coeff n : kN N) : ℂ) ∈ AZ N

private theorem bddK_iff_map {ψ : PowerSeries (kN N)} : BddK ψ ↔ BddA N (ψ.map (algebraMap (kN N) ℂ)) := by
  constructor
  · rintro ⟨D, hD, h⟩
    refine ⟨D, hD, fun n => ?_⟩
    rw [PowerSeries.coeff_map, coe_algebraMap]
    have := h n
    push_cast at this
    exact this
  · rintro ⟨D, hD, h⟩
    refine ⟨D, hD, fun n => ?_⟩
    have := h n
    rw [PowerSeries.coeff_map, coe_algebraMap] at this
    push_cast
    exact this

private theorem bddK_liftK {φ : PowerSeries ℂ} (h : BddA N φ) (hφ : ∀ n, φ.coeff n ∈ kN N) : BddK (liftK φ hφ) := by
  rw [bddK_iff_map, map_liftK]; exact h

private theorem BddK.mul {ψ ψ' : PowerSeries (kN N)} (h : BddK ψ) (h' : BddK ψ') : BddK (ψ * ψ') := by
  rw [bddK_iff_map] at h h' ⊢
  rw [map_mul]
  exact h.mul h'

private theorem bddK_one : BddK (1 : PowerSeries (kN N)) := by
  rw [bddK_iff_map, map_one]; exact bddA_one

private theorem bddK_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries (kN N)) (h : ∀ i ∈ s, BddK (f i)) :
    BddK (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bddK_one
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private def autS (σ : (kN N) ≃ₐ[ℚ] (kN N)) : PowerSeries (kN N) →+* PowerSeries (kN N) :=
  PowerSeries.map (σ : (kN N) →+* (kN N))

private theorem coeff_autS (σ : (kN N) ≃ₐ[ℚ] (kN N)) (ψ : PowerSeries (kN N)) (n : ℕ) :
    (autS σ ψ).coeff n = σ (ψ.coeff n) := by
  rw [autS, PowerSeries.coeff_map]; rfl

private theorem autS_injective (σ : (kN N) ≃ₐ[ℚ] (kN N)) : Function.Injective (autS σ) := by
  intro a b h
  refine PowerSeries.ext fun n => ?_
  have := congrArg (PowerSeries.coeff n) h
  rw [coeff_autS, coeff_autS] at this
  exact σ.injective this

private theorem autS_mul (τ σ : (kN N) ≃ₐ[ℚ] (kN N)) (ψ : PowerSeries (kN N)) : autS τ (autS σ ψ) = autS (τ * σ) ψ := by
  ext n
  rw [coeff_autS, coeff_autS, coeff_autS, AlgEquiv.mul_apply]

private theorem autS_one (ψ : PowerSeries (kN N)) : autS 1 ψ = ψ := by
  ext n; rw [coeff_autS, AlgEquiv.one_apply]

private theorem BddK.autS {ψ : PowerSeries (kN N)} (h : BddK ψ) (σ : (kN N) ≃ₐ[ℚ] (kN N)) : BddK (autS σ ψ) := by
  obtain ⟨D, hD, hψ⟩ := h
  refine ⟨D, hD, fun n => ?_⟩
  rw [coeff_autS]
  have : (D : kN N) * σ (ψ.coeff n) = σ ((D : kN N) * ψ.coeff n) := by
    rw [map_mul, map_natCast]
  rw [this]
  exact aut_mem_AZ N σ _ (hψ n)

private theorem autS_map_rat (σ : (kN N) ≃ₐ[ℚ] (kN N)) (y : PowerSeries ℚ) :
    autS σ (y.map (algebraMap ℚ (kN N))) = y.map (algebraMap ℚ (kN N)) := by
  ext n
  rw [coeff_autS, PowerSeries.coeff_map, AlgEquiv.commutes]

private theorem bddQ_of_bddK_map {y : PowerSeries ℚ} (h : BddK (y.map (algebraMap ℚ (kN N)))) : BddQ y := by
  rw [bddK_iff_map, map_rat_K] at h
  exact bddQ_of_bddA_isRat h

private theorem galois_descent (y₀ : PowerSeries ℚ) (q r : PowerSeries ℂ) (hq0 : q ≠ 0) (hq : BddA N q)
    (hr : BddA N r) (hyq : y₀.map (algebraMap ℚ ℂ) * q = r) :
    ∃ h₀ u₀ : PowerSeries ℚ, h₀ ≠ 0 ∧ BddQ h₀ ∧ BddQ u₀ ∧ h₀ * y₀ = u₀ := by
  classical
  set qK : PowerSeries (kN N) := liftK q hq.coeff_mem with hqK
  set rK : PowerSeries (kN N) := liftK r hr.coeff_mem with hrK
  set yK : PowerSeries (kN N) := y₀.map (algebraMap ℚ (kN N)) with hyK
  have hqK_map : qK.map (algebraMap (kN N) ℂ) = q := map_liftK q _
  have hrK_map : rK.map (algebraMap (kN N) ℂ) = r := map_liftK r _
  have hyK_map : yK.map (algebraMap (kN N) ℂ) = y₀.map (algebraMap ℚ ℂ) := map_rat_K y₀
  have hidK : yK * qK = rK := map_K_injective (by rw [map_mul, hyK_map, hqK_map, hrK_map, hyq])
  have hqK0 : qK ≠ 0 := by
    intro h0; apply hq0; rw [← hqK_map, h0, map_zero]
  have hbq : BddK qK := bddK_liftK hq _
  have hbr : BddK rK := bddK_liftK hr _

  set hK : PowerSeries (kN N) := ∏ σ : (kN N) ≃ₐ[ℚ] (kN N), autS σ qK with hhK
  have hhK0 : hK ≠ 0 := by
    rw [hhK, Finset.prod_ne_zero_iff]
    intro σ _ h0
    apply hqK0
    apply autS_injective σ
    rw [h0, map_zero]
  have hbh : BddK hK := bddK_prod _ _ fun σ _ => hbq.autS σ
  have hfix : ∀ τ : (kN N) ≃ₐ[ℚ] (kN N), autS τ hK = hK := by
    intro τ
    rw [hhK, map_prod]
    simp_rw [autS_mul]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl

  have hcoef : ∀ n, ∃ c : ℚ, hK.coeff n = algebraMap ℚ (kN N) c := by
    intro n
    apply exists_rat_of_fixed N
    intro τ
    have := congrArg (PowerSeries.coeff n) (hfix τ)
    rwa [coeff_autS] at this
  choose c hc using hcoef
  set h₀ : PowerSeries ℚ := PowerSeries.mk c with hh₀
  have hh₀_map : h₀.map (algebraMap ℚ (kN N)) = hK := by
    ext n; rw [PowerSeries.coeff_map, hh₀, PowerSeries.coeff_mk, hc n]

  have hyh : yK * hK = rK * ∏ σ ∈ (Finset.univ : Finset ((kN N) ≃ₐ[ℚ] (kN N))).erase 1, autS σ qK := by
    rw [hhK, ← Finset.mul_prod_erase Finset.univ (fun σ => autS σ qK) (Finset.mem_univ 1), autS_one, ← mul_assoc,
      hidK]
  have hbu : BddK (yK * hK) := by
    rw [hyh]
    exact hbr.mul (bddK_prod _ _ fun σ _ => hbq.autS σ)
  refine ⟨h₀, h₀ * y₀, ?_, ?_, ?_, rfl⟩
  · intro h0; apply hhK0; rw [← hh₀_map, h0, map_zero]
  · exact bddQ_of_bddK_map (N := N) (by rw [hh₀_map]; exact hbh)
  · apply bddQ_of_bddK_map (N := N)
    rw [map_mul, hh₀_map, ← hyK, mul_comm]
    exact hbu

end Galois

section Integral

private theorem exists_int_multiple {d : ℕ} (y₀ : PowerSeries ℚ) (c₀ : Fin d → PowerSeries ℚ) (hc : ∀ i, BddQ (c₀ i))
    (hrel : y₀ ^ d + ∑ i : Fin d, c₀ i * y₀ ^ (i : ℕ) = 0) (h₀ u₀ : PowerSeries ℚ) (hh0 : h₀ ≠ 0)
    (hh : BddQ h₀) (hu : BddQ u₀) (hhy : h₀ * y₀ = u₀) :
    ∃ (c : ℕ) (g : PowerSeries ℤ), c ≠ 0 ∧ g.map (Int.castRingHom ℚ) = (c : ℚ) • y₀ := by
  classical
  choose D C hD hC using hc
  obtain ⟨Dh, H, hDh, hH⟩ := hh
  obtain ⟨Du, U, hDu, hU⟩ := hu
  set c : ℕ := ∏ i, D i with hcdef
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hD i

  set z : Fin d → ℕ := fun i => c ^ (d - 1 - i) * ∏ j ∈ Finset.univ.erase i, D j with hz
  have hzid : ∀ i : Fin d, z i * D i * c ^ (i : ℕ) = c ^ d := by
    intro i
    have h1 : (∏ j ∈ Finset.univ.erase i, D j) * D i = c := by
      rw [hcdef, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    have h2 : d - 1 - (i : ℕ) + 1 + i = d := by have := i.2; omega
    calc z i * D i * c ^ (i : ℕ) = c ^ (d - 1 - i) * ((∏ j ∈ Finset.univ.erase i, D j) * D i) * c ^ (i : ℕ) := by
          rw [hz]; ring
      _ = c ^ (d - 1 - i) * c * c ^ (i : ℕ) := by rw [h1]
      _ = c ^ (d - 1 - (i : ℕ) + 1 + i) := by rw [pow_add, pow_succ]
      _ = c ^ d := by rw [h2]

  set ι : PowerSeries ℤ →+* PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) with hι
  set a : Fin d → PowerSeries ℤ := fun i => PowerSeries.C (z i : ℤ) * C i with ha
  set Φ : Polynomial (PowerSeries ℤ) := Polynomial.X ^ d + ∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)
    with hΦ
  have hΦmonic : Φ.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt a)
  set g : PowerSeries ℚ := PowerSeries.C (c : ℚ) * y₀ with hg
  have hιa : ∀ i, ι (a i) = PowerSeries.C ((z i : ℚ) * D i) * c₀ i := by
    intro i
    have h1 : ι (a i) = ι (PowerSeries.C (z i : ℤ)) * ι (C i) := by rw [ha, map_mul]
    rw [h1, hC i, PowerSeries.smul_eq_C_mul, ← mul_assoc]
    congr 1
    rw [hι, PowerSeries.map_C, ← map_mul, eq_intCast, Int.cast_natCast]
  have hroot : Polynomial.eval₂ ι g Φ = 0 := by
    rw [hΦ, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, hιa]
    have hterm : ∀ i : Fin d, PowerSeries.C ((z i : ℚ) * D i) * c₀ i * g ^ (i : ℕ)
        = PowerSeries.C ((c : ℚ) ^ d) * (c₀ i * y₀ ^ (i : ℕ)) := by
      intro i
      have hnum : (z i : ℚ) * D i * (c : ℚ) ^ (i : ℕ) = (c : ℚ) ^ d := by exact_mod_cast hzid i
      rw [hg, mul_pow, ← map_pow, ← hnum]
      simp only [map_mul, map_pow]
      ring
    have hlead : g ^ d = PowerSeries.C ((c : ℚ) ^ d) * y₀ ^ d := by rw [hg, mul_pow, map_pow]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, hlead, ← mul_add, hrel, mul_zero]

  set h : PowerSeries ℤ := PowerSeries.C (Du : ℤ) * H with hh
  have hH0 : H ≠ 0 := by
    intro h0
    have : (Dh : ℚ) • h₀ = 0 := by rw [← hH, h0, map_zero]
    rcases smul_eq_zero.mp this with h1 | h1
    · exact hDh (by exact_mod_cast h1)
    · exact hh0 h1
  have hh0' : h ≠ 0 := by
    rw [hh]
    refine mul_ne_zero ?_ hH0
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    rw [PowerSeries.constantCoeff_C, map_zero] at this
    exact hDu (by exact_mod_cast this)
  have hmul : ι h * g ∈ ι.range := by
    refine ⟨PowerSeries.C ((c * Dh : ℕ) : ℤ) * U, ?_⟩
    rw [hh, map_mul, map_mul, hU, hH, hg, ← hhy]
    simp only [hι, PowerSeries.smul_eq_C_mul, Nat.cast_mul, map_natCast, map_mul]
    ring

  have hιalg : ι = PowerSeries.map (algebraMap ℤ ℚ) := by rw [hι, algebraMap_int_eq]
  have key : g ∈ (PowerSeries.map (algebraMap ℤ ℚ)).range := by
    rw [← hιalg]
    exact PowerSeries.mem_range_map_of_monic_of_mul_mem_range g Φ hΦmonic (by rw [← hιalg]; exact hroot) h hh0'
      (by rw [← hιalg]; exact hmul)
  obtain ⟨gZ, hgZ⟩ := key
  refine ⟨c, gZ, hc0, ?_⟩
  rw [hι, ← algebraMap_int_eq, hgZ, hg, PowerSeries.smul_eq_C_mul]

end Integral

section Main

variable [NeZero N]

local notation "Δ" => ModularForm.discriminant

private theorem main (m : ℕ) (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ : ℍ => G (α • τ)) * Δ ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion N (G * Δ ^ m)).coeff n = (r : ℂ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ n : ℕ, ∃ z : ℤ, (D : ℂ) * (qExpansion N (G * Δ ^ m)).coeff n = (z : ℂ) := by
  classical
  obtain ⟨L, d, y₀, c₀, q, r, hy₀, hc₀, hrel, hq0, hq, hr, hyq⟩ := exists_series_data (N := N) m G hG hinv hbd hrat
  obtain ⟨h₀, u₀, hh0, hh, hu, hhy⟩ := galois_descent (N := N) y₀ q r hq0 hq hr hyq
  obtain ⟨c, gZ, hc0, hgZ⟩ := exists_int_multiple y₀ c₀ hc₀ hrel h₀ u₀ hh0 hh hu hhy

  set Ghat : PowerSeries ℂ := qExpansion N (G * Δ ^ m) with hGhat
  have hC : gZ.map (Int.castRingHom ℂ) = (PowerSeries.C (c : ℂ) * Ghat * ((UZ (N := N)) ^ L).map (Int.castRingHom ℂ))
      * PowerSeries.X ^ (N * L) := by
    rw [← map_int_rat, hgZ, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, hy₀, ← map_DZ, DZ_eq, map_pow,
      map_mul, map_pow, PowerSeries.map_X]
    simp only [map_natCast]
    rw [hGhat]
    ring

  have hdvd : (PowerSeries.X : PowerSeries ℤ) ^ (N * L) ∣ gZ := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro k hk
    have h1 := congrArg (PowerSeries.coeff k) hC
    rw [PowerSeries.coeff_map, mul_comm, PowerSeries.coeff_X_pow_mul', ite_eq_right (not_le.mpr hk), eq_intCast] at h1
    exact_mod_cast h1
  obtain ⟨g', hg'⟩ := hdvd
  have hC' : g'.map (Int.castRingHom ℂ) = PowerSeries.C (c : ℂ) * Ghat * ((UZ (N := N)) ^ L).map (Int.castRingHom ℂ) := by
    have h1 := hC
    rw [hg', map_mul, map_pow, PowerSeries.map_X, mul_comm] at h1
    exact mul_right_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) h1

  have hUunit : IsUnit ((UZ (N := N)) ^ L) := by
    refine IsUnit.pow L ?_
    rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_UZ]; exact isUnit_one
  obtain ⟨w, hw⟩ := hUunit
  have hfinal : (g' * ↑w⁻¹).map (Int.castRingHom ℂ) = PowerSeries.C (c : ℂ) * Ghat := by
    rw [map_mul, hC', hw.symm, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  refine ⟨c, by exact_mod_cast hc0, fun n => ⟨PowerSeries.coeff n (g' * ↑w⁻¹), ?_⟩⟩
  have := congrArg (PowerSeries.coeff n) hfinal
  rw [PowerSeries.coeff_map, PowerSeries.coeff_C_mul, eq_intCast] at this
  push_cast
  rw [← this]

end Main
end GammaNBounded

theorem _root_.ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant
    (N : ℕ) [NeZero N] (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : UpperHalfPlane, G (γ • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ n : ℕ, ∃ z : ℤ,
      (D : ℂ) * (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n = (z : ℂ) :=
  GammaNBounded.main N m G hG hinv hbd hrat

end WLightS10.S_ModularCurve_exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant

namespace WLightS10.S_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace X1DiamondRationalForms
private def restrictForm {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ)
    (f : ModularForm Γ k) : ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)


local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Δ" => ModularForm.discriminant

private def IsRat (q : PowerSeries ℂ) : Prop := ∀ n, ∃ r : ℚ, q.coeff n = (r : ℂ)

private theorem isRat_iff_exists_map {q : PowerSeries ℂ} :
    IsRat q ↔ ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = q := by
  constructor
  · intro h
    choose r hr using h
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  · rintro ⟨p, rfl⟩ n
    exact ⟨PowerSeries.coeff n p, by rw [PowerSeries.coeff_map]; rfl⟩

private theorem IsRat.mul {q q' : PowerSeries ℂ} (h : IsRat q) (h' : IsRat q') : IsRat (q * q') := by
  rw [isRat_iff_exists_map] at h h' ⊢
  obtain ⟨p, rfl⟩ := h
  obtain ⟨p', rfl⟩ := h'
  exact ⟨p * p', by rw [map_mul]⟩

private theorem IsRat.pow {q : PowerSeries ℂ} (h : IsRat q) (n : ℕ) : IsRat (q ^ n) := by
  rw [isRat_iff_exists_map] at h ⊢
  obtain ⟨p, rfl⟩ := h
  exact ⟨p ^ n, by rw [map_pow]⟩

private theorem IsRat.smul {q : PowerSeries ℂ} (h : IsRat q) (r : ℚ) : IsRat ((r : ℂ) • q) := by
  intro n
  obtain ⟨s, hs⟩ := h n
  exact ⟨r * s, by simp [hs]⟩

private theorem IsRat.neg {q : PowerSeries ℂ} (h : IsRat q) : IsRat (-q) := by
  intro n
  obtain ⟨s, hs⟩ := h n
  exact ⟨-s, by simp [hs]⟩

private theorem IsRat.of_mul_eq {q u p : PowerSeries ℂ} (hu : IsRat u) (hu0 : PowerSeries.constantCoeff u = 1)
    (hp : IsRat p) (h : q * u = p) : IsRat q := by
  rw [isRat_iff_exists_map] at hu hp ⊢
  obtain ⟨U, rfl⟩ := hu
  obtain ⟨P, rfl⟩ := hp
  have hU0 : PowerSeries.constantCoeff U = 1 := by
    have : algebraMap ℚ ℂ (PowerSeries.constantCoeff U) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hu0,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    exact (algebraMap ℚ ℂ).injective (by rw [this, map_one])
  have hUunit : IsUnit U := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hU0]; exact isUnit_one
  obtain ⟨v, hv⟩ := hUunit
  refine ⟨P * ↑v⁻¹, ?_⟩
  have hne : (U.map (algebraMap ℚ ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (PowerSeries.coeff 0) h0
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0] at this
    simp at this
  apply mul_right_cancel₀ hne
  rw [h, map_mul, mul_assoc, ← map_mul, ← hv, Units.inv_mul, map_one, mul_one]

section Level

variable {M : ℕ} {k : ℤ}

private theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  simp

private theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

private theorem conj_mem_Gamma1 {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ Gamma1 M) :
    γ * A * γ⁻¹ ∈ Gamma1 M := by
  have hA0 : A ∈ Gamma0 M := Gamma1_in_Gamma0 M hA
  set A₀ : Gamma0 M := ⟨A, hA0⟩
  set γ₀ : Gamma0 M := ⟨γ, hγ⟩
  have hA1 : A₀ ∈ Gamma1' M := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem M A).mp hA
  haveI : (Gamma1' M).Normal := by
    change ((Gamma0Map M).ker).Normal
    infer_instance
  have hconj : γ₀ * A₀ * γ₀⁻¹ ∈ Gamma1' M := Subgroup.Normal.conj_mem inferInstance A₀ hA1 γ₀
  rw [Gamma1_to_Gamma0_mem] at hconj
  rw [Gamma1_mem]
  exact hconj

private theorem isBoundedAtImInfty_slash [NeZero M] (f : ModularForm Γ₁(M) k) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty ((⇑f : ℍ → ℂ) ∣[k] γ) := by
  rw [ModularForm.SL_slash, ← OnePoint.isBoundedAt_infty_iff, ← OnePoint.IsBoundedAt.smul_iff]
  apply f.bdd_at_cusps'
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_iff'.mpr ⟨γ, rfl⟩

private def diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁(M) k) :
    ModularForm Γ₁(M) k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
  slash_action_eq' := by
    intro A hA
    obtain ⟨A, hA, rfl⟩ := hA
    have hconj : γ * A * γ⁻¹ ∈ Gamma1 M := conj_mem_Gamma1 hγ hA
    have hGL : (γ : GL (Fin 2) ℝ) * (A : GL (Fin 2) ℝ)
        = ((γ * A * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) := by
      simp only [map_mul, map_inv, inv_mul_cancel_right]
    change ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] (A : GL (Fin 2) ℝ)
      = (⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)
    rw [← SlashAction.slash_mul, hGL, SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hconj)
  holo' := f.holo'.slash k _
  bdd_at_cusps' := by
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ₁(M)).mp hc
    have hc' : IsCusp ((γ : GL (Fin 2) ℝ) • c) Γ₁(M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact hcSL.smul_of_mem ⟨γ, rfl⟩
    exact OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' hc')

private theorem coe_diamondSlash [NeZero M] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁(M) k) :
    (⇑(diamondSlash γ hγ f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := by
  rw [ModularForm.SL_slash]; rfl

set_option backward.isDefEq.respectTransparency.types false in
private theorem mul_inv_mem_Gamma1 {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγ' : γ' ∈ Gamma0 M)
    (h : ((γ 1 1 : ℤ) : ZMod M) = ((γ' 1 1 : ℤ) : ZMod M)) : γ * γ'⁻¹ ∈ Gamma1 M := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  have hc' : ((γ' 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ'
  have hdet : ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
    have h1 : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.det_coe; rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod M) h1
    push_cast at this
    rw [hc, mul_zero, sub_zero] at this
    exact this
  have hdet' : ((γ' 0 0 : ℤ) : ZMod M) * ((γ' 1 1 : ℤ) : ZMod M) = 1 := by
    have h1 : (γ' 0 0 : ℤ) * γ' 1 1 - γ' 0 1 * γ' 1 0 = 1 := by
      have := γ'.det_coe; rwa [Matrix.det_fin_two] at this
    have := congrArg (Int.cast : ℤ → ZMod M) h1
    push_cast at this
    rw [hc', mul_zero, sub_zero] at this
    exact this
  have h00 : ((γ 0 0 : ℤ) : ZMod M) = ((γ' 0 0 : ℤ) : ZMod M) := by
    have hu : IsUnit ((γ 1 1 : ℤ) : ZMod M) := isUnit_iff_exists_inv.mpr ⟨_, by rw [mul_comm]; exact hdet⟩
    apply hu.mul_right_cancel
    rw [hdet, h, hdet']
  have hinv : (γ'⁻¹ : SL(2, ℤ)) = ⟨!![γ' 1 1, -(γ' 0 1); -(γ' 1 0), γ' 0 0], by
      rw [Matrix.det_fin_two_of]; have := γ'.det_coe; rw [Matrix.det_fin_two] at this
      linear_combination this⟩ := Matrix.SpecialLinearGroup.SL2_inv_expl γ'
  rw [Gamma1_mem, hinv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', Int.cast_add, Int.cast_mul, Int.cast_neg, hc, hc',
    Fin.isValue]
  refine ⟨?_, ?_, ?_⟩
  · rw [h00, neg_zero, mul_zero, add_zero, hdet']
  · rw [zero_mul, zero_add, ← h00, mul_comm, hdet]
  · simp
private theorem slash_eq_of_apply_eq [NeZero M] (f : ModularForm Γ₁(M) k) {γ γ' : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 M) (hγ' : γ' ∈ Gamma0 M)
    (h : ((γ 1 1 : ℤ) : ZMod M) = ((γ' 1 1 : ℤ) : ZMod M)) :
    (⇑f : ℍ → ℂ) ∣[k] γ = (⇑f : ℍ → ℂ) ∣[k] γ' := by
  have hmem := mul_inv_mem_Gamma1 hγ hγ' h
  have hinv : (⇑f : ℍ → ℂ) ∣[k] (γ * γ'⁻¹) = ⇑f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hmem)
  calc (⇑f : ℍ → ℂ) ∣[k] γ = (⇑f : ℍ → ℂ) ∣[k] (γ * γ'⁻¹ * γ') := by rw [inv_mul_cancel_right]
    _ = ((⇑f : ℍ → ℂ) ∣[k] (γ * γ'⁻¹)) ∣[k] γ' := SlashAction.slash_mul _ _ _ _
    _ = (⇑f : ℍ → ℂ) ∣[k] γ' := by rw [hinv]

private theorem Gamma1_le_of_dvd {M M' : ℕ} (h : M ∣ M') : Gamma1 M' ≤ Gamma1 M := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  obtain ⟨h00, h11, h10⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod M)) h00
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod M)) h11
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod M)) h10
    rwa [map_intCast, map_zero] at this

private theorem Gamma0_le_of_dvd {M' : ℕ} (h : M ∣ M') : Gamma0 M' ≤ Gamma0 M := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have := congrArg (ZMod.castHom h (ZMod M)) hA
  rwa [map_intCast, map_zero] at this

private def res {M' : ℕ} (h : M ∣ M') (f : ModularForm Γ₁(M) k) : ModularForm Γ₁(M') k :=
  restrictForm (Subgroup.map_mono (Gamma1_le_of_dvd h)) f

@[scoped simp] private theorem coe_res {M' : ℕ} (h : M ∣ M') (f : ModularForm Γ₁(M) k) : (⇑(res h f) : ℍ → ℂ) = f := rfl

private def resSL (M : ℕ) {k : ℤ} (f : ModularForm 𝒮ℒ k) : ModularForm Γ₁(M) k :=
  restrictForm (Subgroup.map_le_range _ _) f

@[scoped simp] private theorem coe_resSL (M : ℕ) {k : ℤ} (f : ModularForm 𝒮ℒ k) : (⇑(resSL M f) : ℍ → ℂ) = f := rfl

end Level

section Weight

variable {M : ℕ} [NeZero M] {k : ℤ}

private theorem apply_smul (f : ModularForm Γ₁(M) k) {g : SL(2, ℤ)} (hg : g ∈ Gamma1 M) (τ : ℍ) :
    f (g • τ) = denom (g : GL (Fin 2) ℝ) τ ^ k * f τ := by
  have := SlashInvariantForm.slash_action_eqn'' f (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hg) τ
  rw [ModularGroup.sl_moeb]
  exact this

private theorem disc_smul (α : SL(2, ℤ)) (τ : ℍ) :
    Δ (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

private theorem levelOne_smul {k' : ℤ} (E : ModularForm 𝒮ℒ k') (α : SL(2, ℤ)) (τ : ℍ) :
    E (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ k' * E τ := by
  have := SlashInvariantForm.slash_action_eqn'' E (Γ := 𝒮ℒ) (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [← ModularGroup.sl_moeb] at this
  exact this

private theorem levelOne_slash {k' : ℤ} (E : ModularForm 𝒮ℒ k') (α : SL(2, ℤ)) :
    (⇑E : ℍ → ℂ) ∣[k'] α = ⇑E := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq E _ ⟨α, rfl⟩

private theorem isRat_slash_mul (f : ModularForm Γ₁(M) k) (m : ℕ) {kE : ℤ} (E : ModularForm 𝒮ℒ kE)
    (hkE : k + kE = 12 * m) (hf : IsRat (qExpansion 1 f)) (hE : IsRat (qExpansion 1 E))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    IsRat (qExpansion 1 (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑E)) := by

  set H : ℍ → ℂ := (⇑f : ℍ → ℂ) * ⇑E with hH
  set G : ℍ → ℂ := fun τ => H τ / (Δ τ) ^ m with hG
  have hΔ : ∀ τ : ℍ, (Δ τ) ^ m ≠ 0 := fun τ => pow_ne_zero _ (discriminant_ne_zero τ)
  have hGΔ : G * Δ ^ m = H := by
    funext τ; simp only [Pi.mul_apply, Pi.pow_apply, hG]; field_simp [hΔ τ]
  have hmdH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := f.holo'.mul E.holo'
  have hmdΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
    rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'
  have hmdG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
    intro τ
    exact (hmdH τ).div ((hmdΔ τ).pow m) (hΔ τ)

  have hcw : ∀ α : SL(2, ℤ), (fun τ => G (α • τ)) * Δ ^ m = ((⇑f : ℍ → ℂ) ∣[k] α) * ⇑E := by
    intro α
    funext τ
    have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
    simp only [Pi.mul_apply, Pi.pow_apply, hG, hH]
    rw [ModularForm.SL_slash_apply, disc_smul, levelOne_smul E, ModularGroup.sl_moeb]
    have hpow : (denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ) ^ m
        = denom (α : GL (Fin 2) ℝ) τ ^ (k + kE) * (Δ τ) ^ m := by
      rw [mul_pow, ← zpow_natCast, ← zpow_mul, hkE]
    rw [hpow, zpow_add₀ hd, zpow_neg]
    field_simp [hΔ τ, zpow_ne_zero k hd, zpow_ne_zero kE hd]

  have hinv : ∀ g ∈ Gamma1 M, ∀ τ : ℍ, G (g • τ) = G τ := by
    intro g hg τ
    have h1 := congrFun (hcw g) τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h1
    have h2 : ((⇑f : ℍ → ℂ) ∣[k] g) = ⇑f := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hg)
    rw [h2] at h1
    have h3 : G τ * Δ τ ^ m = f τ * E τ := by
      have := congrFun hGΔ τ; exact this
    exact mul_right_cancel₀ (hΔ τ) (h1.trans h3.symm)

  have hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ => G (α • τ)) * Δ ^ m) := by
    intro α
    rw [hcw α]
    exact (isBoundedAtImInfty_slash f α).mul (ModularFormClass.bdd_at_infty E)

  have hrat : ∀ n, ∃ r : ℚ, (qExpansion 1 (G * Δ ^ m)).coeff n = (r : ℂ) := by
    rw [hGΔ, hH]
    have : qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑E) = qExpansion 1 ⇑f * qExpansion 1 ⇑(resSL M E) := by
      rw [← coe_resSL M E, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) f (resSL M E)]
    rw [this]
    exact hf.mul hE

  have key := ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0 M m G hmdG hinv hbd hrat γ hγ
  rw [hcw γ] at key
  exact key

end Weight

section Even

variable {M : ℕ} [NeZero M] {k : ℤ}

private theorem isRat_E4 : IsRat (qExpansion 1 (E₄ : ℍ → ℂ)) := by
  intro n
  rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩

private theorem isRat_E6 : IsRat (qExpansion 1 (E₆ : ℍ → ℂ)) := by
  intro n
  rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩

private theorem constantCoeff_E4 : PowerSeries.constantCoeff (qExpansion 1 (E₄ : ℍ → ℂ)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularForm.E₄,
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide)]

private theorem constantCoeff_E6 : PowerSeries.constantCoeff (qExpansion 1 (E₆ : ℍ → ℂ)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ModularForm.E₆,
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide)]

private def Eaux (a b : ℕ) : ModularForm 𝒮ℒ (a * 4 + b * 6) := (E₄.pow a).mul (E₆.pow b)

private theorem coe_Eaux (a b : ℕ) : (⇑(Eaux a b) : ℍ → ℂ) = (⇑E₄) ^ a * (⇑E₆) ^ b := by
  rw [Eaux, coe_mul, coe_pow, coe_pow]

private theorem qExpansion_Eaux (a b : ℕ) :
    qExpansion 1 (⇑(Eaux a b)) = qExpansion 1 ⇑E₄ ^ a * qExpansion 1 ⇑E₆ ^ b := by
  rw [Eaux, coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

private theorem isRat_Eaux (a b : ℕ) : IsRat (qExpansion 1 (⇑(Eaux a b))) := by
  rw [qExpansion_Eaux]; exact (isRat_E4.pow a).mul (isRat_E6.pow b)

private theorem constantCoeff_Eaux (a b : ℕ) : PowerSeries.constantCoeff (qExpansion 1 (⇑(Eaux a b))) = 1 := by
  rw [qExpansion_Eaux, map_mul, map_pow, map_pow, constantCoeff_E4, constantCoeff_E6, one_pow, one_pow,
    one_mul]

private theorem exists_weights (hk : Even k) : ∃ (m a b : ℕ), k + (a * 4 + b * 6 : ℕ) = 12 * (m : ℤ) := by
  obtain ⟨j, rfl⟩ := hk
  have hjabs : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  have hjabs' : -j ≤ (j.natAbs : ℤ) := by
    have := Int.le_natAbs (a := -j); rwa [Int.natAbs_neg] at this
  rcases Int.emod_two_eq_zero_or_one j with hpar | hpar
  ·
    set q : ℤ := j / 2 with hq
    have hjq : j = 2 * q := by omega
    have h0 : 0 ≤ 3 * (j.natAbs : ℤ) + 3 - q := by omega
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨j.natAbs + 1, a, 0, ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ← ha]
    omega
  ·
    set q : ℤ := j / 2 with hq
    have hjq : j = 2 * q + 1 := by omega
    have h0 : 0 ≤ 3 * (j.natAbs : ℤ) + 1 - q := by omega
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨j.natAbs + 1, a, 1, ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ← ha]
    omega

private theorem isRat_slash_of_even (hk : Even k) (f : ModularForm Γ₁(M) k) (hf : IsRat (qExpansion 1 f))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : IsRat (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] γ)) := by
  obtain ⟨m, a, b, hw⟩ := exists_weights hk
  have key := isRat_slash_mul f m (Eaux a b) (by exact_mod_cast hw) hf (isRat_Eaux a b) hγ

  have hprod : qExpansion 1 (((⇑f : ℍ → ℂ) ∣[k] γ) * ⇑(Eaux a b))
      = qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] γ) * qExpansion 1 ⇑(Eaux a b) := by
    rw [← coe_diamondSlash γ hγ f, ← coe_resSL M (Eaux a b),
      ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) (diamondSlash γ hγ f)
        (resSL M (Eaux a b))]
  exact IsRat.of_mul_eq (isRat_Eaux a b) (constantCoeff_Eaux a b) key hprod.symm

end Even

section Odd

private theorem exists_E1 : ∃ E : ModularForm Γ₁(3) 1,
    IsRat (qExpansion 1 E) ∧ PowerSeries.constantCoeff (qExpansion 1 (E : ℍ → ℂ)) = 1 := by
  obtain ⟨E, hE⟩ := EisensteinWeightOne.e1Chi3IsModular
  refine ⟨E, ?_⟩
  set c : ℕ → ℤ := fun n => PowerSeries.coeff n EisensteinWeightOne.e1Chi3 with hc

  have hchi : ∀ d : ℕ, |EisensteinWeightOne.chiNegThree d| ≤ 1 := by
    intro d
    unfold EisensteinWeightOne.chiNegThree
    split_ifs <;> simp
  have hcbound : ∀ n : ℕ, ‖((c n : ℤ) : ℂ)‖ ≤ 6 * n + 1 := by
    intro n
    rw [Complex.norm_intCast]
    simp only [hc, EisensteinWeightOne.e1Chi3, PowerSeries.coeff_mk]
    split_ifs with h0
    · subst h0; simp
    · have h1 : |EisensteinWeightOne.sigmaChi n| ≤ n := by
        unfold EisensteinWeightOne.sigmaChi
        calc |∑ d ∈ n.divisors, EisensteinWeightOne.chiNegThree d|
            ≤ ∑ d ∈ n.divisors, |EisensteinWeightOne.chiNegThree d| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _d ∈ n.divisors, (1 : ℤ) := Finset.sum_le_sum fun d _ => hchi d
          _ = n.divisors.card := by simp
          _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
      have h2 : |6 * EisensteinWeightOne.sigmaChi n| ≤ 6 * (n : ℤ) + 1 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℤ) ≤ 6)]; linarith
      rw [← Int.cast_abs]
      exact_mod_cast h2

  have hsum : ∀ z : ℍ, HasSum (fun n : ℕ => ((c n : ℤ) : ℂ) • Periodic.qParam 1 z ^ n) (E z) := by
    intro z
    have hq : ‖Periodic.qParam 1 z‖ < 1 := by
      have : 0 < 2 * π * z.im / 1 := by have := z.im_pos; positivity
      simpa [Periodic.qParam, Complex.norm_exp, neg_div] using this
    have hterm : ∀ n : ℕ, ((c n : ℤ) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ))
        = ((c n : ℤ) : ℂ) • Periodic.qParam 1 z ^ n := by
      intro n
      rw [smul_eq_mul, Periodic.qParam, ← Complex.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hS : Summable (fun n : ℕ => ((c n : ℤ) : ℂ) • Periodic.qParam 1 z ^ n) := by
      apply Summable.of_norm_bounded (g := fun n : ℕ => (6 * n + 1) * ‖Periodic.qParam 1 z‖ ^ n)
      · have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖Periodic.qParam 1 z‖) (by simpa using hq)
        have h2 := summable_geometric_of_norm_lt_one (by simpa using hq : ‖‖Periodic.qParam 1 z‖‖ < 1)
        have := (h1.mul_left 6).add h2
        refine this.congr fun n => ?_
        simp only [pow_one]; ring
      · intro n
        rw [norm_smul, norm_pow]
        exact mul_le_mul_of_nonneg_right (hcbound n) (pow_nonneg (norm_nonneg _) _)
    have := hS.hasSum
    have hEz : (∑' n : ℕ, ((c n : ℤ) : ℂ) • Periodic.qParam 1 z ^ n) = E z := by
      rw [hE z]; exact tsum_congr fun n => (hterm n).symm
    rwa [hEz] at this
  have hcoef : ∀ n, ((c n : ℤ) : ℂ) = (qExpansion 1 (E : ℍ → ℂ)).coeff n := fun n =>
    ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods 3) hsum n
  refine ⟨fun n => ⟨(c n : ℚ), by rw [← hcoef n]; push_cast; rfl⟩, ?_⟩
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hcoef 0]
  simp [hc, EisensteinWeightOne.e1Chi3]

variable {M : ℕ} [NeZero M] {k : ℤ}

private theorem slash_of_neg_mem {L : ℕ} {w : ℤ} (F : ModularForm Γ₁(L) w) {g : SL(2, ℤ)}
    (hg : -g ∈ Gamma1 L) : (⇑F : ℍ → ℂ) ∣[w] g = ((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ) := by
  have h1 : (⇑F : ℍ → ℂ) ∣[w] (-g) = ⇑F := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hg)
  have hneg : (⇑F : ℍ → ℂ) ∣[w] (-1 : SL(2, ℤ)) = ((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ) := by
    funext τ
    rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul]
    have hτ : (-1 : SL(2, ℤ)) • τ = τ := by rw [ModularGroup.SL_neg_smul, one_smul]
    have hd : denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = -1 := by
      rw [ModularGroup.denom_apply]
      simp [Matrix.SpecialLinearGroup.coe_neg]
    rw [hτ, hd, mul_comm]
    congr 1
    rw [zpow_neg, ← inv_zpow, inv_neg, inv_one]
  calc (⇑F : ℍ → ℂ) ∣[w] g = (⇑F : ℍ → ℂ) ∣[w] ((-1 : SL(2, ℤ)) * (-g)) := by rw [neg_one_mul, neg_neg]
    _ = ((⇑F : ℍ → ℂ) ∣[w] (-1 : SL(2, ℤ))) ∣[w] (-g) := SlashAction.slash_mul _ _ _ _
    _ = (((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ)) ∣[w] (-g) := by rw [hneg]
    _ = ((-1 : ℂ) ^ w) • ((⇑F : ℍ → ℂ) ∣[w] (-g)) := by rw [ModularForm.SL_smul_slash]
    _ = ((-1 : ℂ) ^ w) • (⇑F : ℍ → ℂ) := by rw [h1]

private theorem isCoprime_entry {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : IsCoprime (γ 1 1 : ℤ) (M : ℤ) := by
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp hc
  have h1 : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  refine ⟨γ 0 0, -(γ 0 1 * c'), ?_⟩
  rw [hc'] at h1
  linear_combination h1

private theorem exists_lift (d : ℤ) (hd : IsCoprime d (M : ℤ)) :
    ∃ d' : ℤ, IsCoprime d' (3 * M : ℤ) ∧ (∃ t : ℤ, d' = d + t * M) ∧ ((3 : ℤ) ∣ M ∨ (3 : ℤ) ∣ d' - 1) := by
  by_cases h3 : (3 : ℤ) ∣ M
  · refine ⟨d, ?_, ⟨0, by ring⟩, Or.inl h3⟩
    exact IsCoprime.mul_right (hd.of_isCoprime_of_dvd_right h3) hd
  · have hM3 : IsCoprime (M : ℤ) 3 := by
      have : Nat.Coprime M 3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        (fun h => h3 (by exact_mod_cast h)) |>.symm
      exact this.isCoprime
    obtain ⟨u, v, huv⟩ := hM3
    refine ⟨d + (1 - d) * u * M, ?_, ⟨(1 - d) * u, by ring⟩, Or.inr ?_⟩
    · apply IsCoprime.mul_right
      ·
        have : d + (1 - d) * u * M = 1 + 3 * (-(1 - d) * v) := by linear_combination (1 - d) * huv
        rw [this]
        exact (isCoprime_one_left.add_mul_left_left _)
      · exact hd.add_mul_right_left _
    · exact ⟨-(1 - d) * v, by linear_combination (1 - d) * huv⟩

private theorem isRat_slash_of_odd (hk : Odd k) (f : ModularForm Γ₁(M) k) (hf : IsRat (qExpansion 1 f))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : IsRat (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] γ)) := by
  obtain ⟨E, hE, hE0⟩ := exists_E1
  haveI : NeZero (3 * M) := ⟨mul_ne_zero three_ne_zero (NeZero.ne M)⟩

  obtain ⟨d', hcop, ⟨t, ht⟩, h3⟩ := exists_lift (M := M) (γ 1 1) (isCoprime_entry hγ)
  obtain ⟨x, y, hxy⟩ := hcop
  set γ' : SL(2, ℤ) := ⟨!![x, -y; 3 * M, d'], by
    rw [Matrix.det_fin_two_of]; linear_combination hxy⟩ with hγ'
  have hγ'11 : (γ' 1 1 : ℤ) = d' := by simp [hγ']
  have hγ'10 : (γ' 1 0 : ℤ) = 3 * M := by simp [hγ']
  have hγ'00 : (γ' 0 0 : ℤ) = x := by simp [hγ']
  have hγ'3M : γ' ∈ Gamma0 (3 * M) := by
    rw [Gamma0_mem, hγ'10]; push_cast; exact ZMod.natCast_self (3 * M) ▸ by push_cast; ring_nf
  have hγ'M : γ' ∈ Gamma0 M := Gamma0_le_of_dvd (dvd_mul_left M 3) hγ'3M
  have hγ'3 : γ' ∈ Gamma0 3 := Gamma0_le_of_dvd (dvd_mul_right 3 M) hγ'3M
  have hentry : ((γ 1 1 : ℤ) : ZMod M) = ((γ' 1 1 : ℤ) : ZMod M) := by
    rw [hγ'11, ht]; push_cast; simp

  have hfγ : (⇑f : ℍ → ℂ) ∣[k] γ = (⇑f : ℍ → ℂ) ∣[k] γ' := slash_eq_of_apply_eq f hγ hγ'M hentry

  obtain ⟨ε, hε, hEγ⟩ : ∃ ε : ℚ, ε * ε = 1 ∧ (⇑E : ℍ → ℂ) ∣[(1 : ℤ)] γ' = (ε : ℂ) • (⇑E : ℍ → ℂ) := by
    have h3z : (3 : ZMod 3) = 0 := by decide
    have hxd : ((x : ℤ) : ZMod 3) * ((d' : ℤ) : ZMod 3) = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod 3) hxy
      push_cast at this
      rw [h3z] at this
      simpa using this
    rcases h3 with h3 | h3
    ·
      have hd3 : ((d' : ℤ) : ZMod 3) = 1 ∨ ((d' : ℤ) : ZMod 3) = -1 := by
        have hne : ((d' : ℤ) : ZMod 3) ≠ 0 := by
          intro h0; rw [h0, mul_zero] at hxd; exact zero_ne_one hxd
        revert hne; generalize ((d' : ℤ) : ZMod 3) = e; decide +revert
      rcases hd3 with hd3 | hd3
      · refine ⟨1, by norm_num, ?_⟩
        have hmem : γ' ∈ Gamma1 3 := by
          rw [Gamma1_mem, hγ'11, hγ'00, hγ'10]
          refine ⟨?_, hd3, by push_cast; rw [h3z, zero_mul]⟩
          rw [hd3, mul_one] at hxd; exact hxd
        have hEinv : (⇑E : ℍ → ℂ) ∣[(1 : ℤ)] γ' = ⇑E := by
          rw [ModularForm.SL_slash]
          exact SlashInvariantFormClass.slash_action_eq E _ (Subgroup.mem_map_of_mem _ hmem)
        rw [hEinv]; push_cast; rw [one_smul]
      · refine ⟨-1, by norm_num, ?_⟩
        have hmem : -γ' ∈ Gamma1 3 := by
          rw [Gamma1_mem]
          simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, hγ'11, hγ'00, hγ'10]
          refine ⟨?_, by rw [hd3, neg_neg], by push_cast; rw [h3z, zero_mul, neg_zero]⟩
          rw [hd3, mul_neg, mul_one] at hxd
          exact hxd
        rw [slash_of_neg_mem E hmem]
        push_cast; norm_num
    ·
      refine ⟨1, by norm_num, ?_⟩
      have hd3 : ((d' : ℤ) : ZMod 3) = 1 := by
        obtain ⟨w, hw⟩ := h3
        have : d' = 1 + 3 * w := by linear_combination hw
        rw [this]; push_cast; rw [h3z]; ring
      have hmem : γ' ∈ Gamma1 3 := by
        rw [Gamma1_mem, hγ'11, hγ'00, hγ'10]
        refine ⟨?_, hd3, by push_cast; rw [h3z, zero_mul]⟩
        rw [hd3, mul_one] at hxd; exact hxd
      have hEinv : (⇑E : ℍ → ℂ) ∣[(1 : ℤ)] γ' = ⇑E := by
        rw [ModularForm.SL_slash]
        exact SlashInvariantFormClass.slash_action_eq E _ (Subgroup.mem_map_of_mem _ hmem)
      rw [hEinv]; push_cast; rw [one_smul]

  set f3 : ModularForm Γ₁(3 * M) k := res (dvd_mul_left M 3) f with hf3
  set E3 : ModularForm Γ₁(3 * M) 1 := res (dvd_mul_right 3 M) E with hE3
  set F : ModularForm Γ₁(3 * M) (k + 1) := f3.mul E3 with hF
  have hFrat : IsRat (qExpansion 1 F) := by
    rw [hF, coe_mul, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods (3 * M)) f3 E3]
    exact hf.mul hE
  have hk1 : Even (k + 1) := hk.add_one
  have key := isRat_slash_of_even hk1 F hFrat hγ'3M

  have hFγ : (⇑F : ℍ → ℂ) ∣[k + 1] γ' = ⇑(diamondSlash γ' hγ'3M f3) * ⇑(((ε : ℂ)) • E3) := by
    rw [hF, coe_mul, ModularForm.mul_slash_SL2, coe_diamondSlash, FunLike.coe_smul, coe_res, coe_res, hEγ]
  rw [hFγ, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods (3 * M)),
    FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods (3 * M)),
    coe_diamondSlash, coe_res, coe_res, ← hfγ] at key

  have key' : IsRat (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] γ) * qExpansion 1 ⇑E) := by
    have heq : qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] γ) * qExpansion 1 ⇑E
        = (ε : ℂ) • (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] γ) * ((ε : ℂ) • qExpansion 1 ⇑E)) := by
      rw [mul_smul_comm, smul_smul, ← Rat.cast_mul, hε, Rat.cast_one, one_smul]
    rw [heq]
    exact key.smul ε
  exact IsRat.of_mul_eq hE hE0 key' rfl

end Odd

private theorem isRat_slash {M : ℕ} [NeZero M] {k : ℤ} (f : ModularForm Γ₁(M) k) (hf : IsRat (qExpansion 1 f))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : IsRat (qExpansion 1 ((⇑f : ℍ → ℂ) ∣[k] γ)) := by
  rcases Int.even_or_odd k with hk | hk
  · exact isRat_slash_of_even hk f hf hγ
  · exact isRat_slash_of_odd hk f hf hγ
end X1DiamondRationalForms

theorem _root_.ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (n : ℕ) :
    ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ)).coeff n = (r : ℂ) :=
  X1DiamondRationalForms.isRat_slash f hf hγ n

end WLightS10.S_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0

namespace WLightS10.S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function ModularCurve
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace X1BoundedDenominators
private def restrictForm {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ)
    (f : ModularForm Γ k) : ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)


local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Δ" => ModularForm.discriminant

private def IsRat (q : PowerSeries ℂ) : Prop := ∀ n, ∃ r : ℚ, q.coeff n = (r : ℂ)

private def IsBdd (q : PowerSeries ℂ) : Prop :=
  ∃ (D : ℤ) (P : PowerSeries ℤ), D ≠ 0 ∧ P.map (Int.castRingHom ℂ) = (D : ℂ) • q

private theorem isRat_iff_exists_map {q : PowerSeries ℂ} :
    IsRat q ↔ ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = q := by
  constructor
  · intro h
    choose r hr using h
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  · rintro ⟨p, rfl⟩ n
    exact ⟨PowerSeries.coeff n p, by rw [PowerSeries.coeff_map]; rfl⟩

private theorem IsRat.mul {q q' : PowerSeries ℂ} (h : IsRat q) (h' : IsRat q') : IsRat (q * q') := by
  rw [isRat_iff_exists_map] at h h' ⊢
  obtain ⟨p, rfl⟩ := h
  obtain ⟨p', rfl⟩ := h'
  exact ⟨p * p', by rw [map_mul]⟩

private theorem IsRat.pow {q : PowerSeries ℂ} (h : IsRat q) (n : ℕ) : IsRat (q ^ n) := by
  rw [isRat_iff_exists_map] at h ⊢
  obtain ⟨p, rfl⟩ := h
  exact ⟨p ^ n, by rw [map_pow]⟩

private theorem isRat_of_int {q : PowerSeries ℂ} (P : PowerSeries ℤ) (h : P.map (Int.castRingHom ℂ) = q) :
    IsRat q := fun n => ⟨((PowerSeries.coeff n P : ℤ) : ℚ), by rw [← h, PowerSeries.coeff_map]; simp⟩

private theorem isBdd_iff {q : PowerSeries ℂ} :
    IsBdd q ↔ ∃ D : ℤ, D ≠ 0 ∧ ∀ n, ∃ z : ℤ, (D : ℂ) * q.coeff n = (z : ℂ) := by
  constructor
  · rintro ⟨D, P, hD, hP⟩
    refine ⟨D, hD, fun n => ⟨PowerSeries.coeff n P, ?_⟩⟩
    have := congrArg (PowerSeries.coeff n) hP
    rw [PowerSeries.coeff_map, PowerSeries.coeff_smul, smul_eq_mul] at this
    rw [← this]; simp
  · rintro ⟨D, hD, h⟩
    choose z hz using h
    refine ⟨D, PowerSeries.mk z, hD, ?_⟩
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_smul, PowerSeries.coeff_mk, smul_eq_mul, hz n]
    simp

private theorem IsBdd.of_mul_eq {q p : PowerSeries ℂ} {U : PowerSeries ℤ} (hU : PowerSeries.constantCoeff U = 1)
    (hp : IsBdd p) (h : q * U.map (Int.castRingHom ℂ) = p) : IsBdd q := by
  obtain ⟨D, P, hD, hP⟩ := hp
  have hUunit : IsUnit U := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hU]; exact isUnit_one
  obtain ⟨u, hu⟩ := hUunit
  refine ⟨D, P * ↑u⁻¹, hD, ?_⟩
  have h1 : (D : ℂ) • q * U.map (Int.castRingHom ℂ) = P.map (Int.castRingHom ℂ) := by
    rw [smul_mul_assoc, h, hP]
  calc (P * ↑u⁻¹).map (Int.castRingHom ℂ)
      = ((D : ℂ) • q * U.map (Int.castRingHom ℂ)) * (↑u⁻¹ : PowerSeries ℤ).map (Int.castRingHom ℂ) := by
        rw [map_mul, h1]
    _ = (D : ℂ) • q * ((U * ↑u⁻¹).map (Int.castRingHom ℂ)) := by rw [map_mul, mul_assoc]
    _ = (D : ℂ) • q := by rw [← hu, Units.mul_inv, map_one, mul_one]

section Level

variable {M : ℕ} {k : ℤ}

private theorem T_pow_mem_Gamma1 (M : ℕ) (t : ℤ) : ModularGroup.T ^ t ∈ Gamma1 M := by
  rw [Gamma1_mem, ModularGroup.coe_T_zpow]
  simp

private theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  simp

private theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

private theorem Gamma_le_Gamma1 (M : ℕ) : CongruenceSubgroup.Gamma M ≤ Gamma1 M := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

private theorem isBoundedAtImInfty_slash [NeZero M] (f : ModularForm Γ₁(M) k) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty ((⇑f : ℍ → ℂ) ∣[k] γ) := by
  rw [ModularForm.SL_slash, ← OnePoint.isBoundedAt_infty_iff, ← OnePoint.IsBoundedAt.smul_iff]
  apply f.bdd_at_cusps'
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_iff'.mpr ⟨γ, rfl⟩

private theorem Gamma1_le_of_dvd {M M' : ℕ} (h : M ∣ M') : Gamma1 M' ≤ Gamma1 M := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  obtain ⟨h00, h11, h10⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod M)) h00
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod M)) h11
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod M)) h10
    rwa [map_intCast, map_zero] at this


private def res {M' : ℕ} (h : M ∣ M') (f : ModularForm Γ₁(M) k) : ModularForm Γ₁(M') k :=
  restrictForm (Subgroup.map_mono (Gamma1_le_of_dvd h)) f

@[scoped simp] private theorem coe_res {M' : ℕ} (h : M ∣ M') (f : ModularForm Γ₁(M) k) : (⇑(res h f) : ℍ → ℂ) = f := rfl

private def resSL (M : ℕ) {k : ℤ} (f : ModularForm 𝒮ℒ k) : ModularForm Γ₁(M) k :=
  restrictForm (Subgroup.map_le_range _ _) f

@[scoped simp] private theorem coe_resSL (M : ℕ) {k : ℤ} (f : ModularForm 𝒮ℒ k) : (⇑(resSL M f) : ℍ → ℂ) = f := rfl

end Level

section Width

private theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

variable (N : ℕ) [NeZero N]

private theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

private theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := periodic_ofComplex_natCast hper N
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam N τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam N τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

private theorem coeff_widthN_mul {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff (N * n) = (qExpansion 1 g).coeff n := by
  rw [qExpansion_coeff_widthN N hg hper hbd, ite_eq_left (dvd_mul_right N n),
    Nat.mul_div_cancel_left _ (NeZero.pos N)]

end Width

section Core

variable {M : ℕ} [NeZero M] {k : ℤ}

private theorem disc_smul (α : SL(2, ℤ)) (τ : ℍ) :
    Δ (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

private theorem levelOne_smul {k' : ℤ} (E : ModularForm 𝒮ℒ k') (α : SL(2, ℤ)) (τ : ℍ) :
    E (α • τ) = denom (α : GL (Fin 2) ℝ) τ ^ k' * E τ := by
  have := SlashInvariantForm.slash_action_eqn'' E (Γ := 𝒮ℒ) (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
  rw [← ModularGroup.sl_moeb] at this
  exact this

private theorem isBdd_mul (f : ModularForm Γ₁(M) k) (m : ℕ) {kE : ℤ} (E : ModularForm 𝒮ℒ kE)
    (hkE : k + kE = 12 * m) (hf : IsRat (qExpansion 1 f)) (hE : IsRat (qExpansion 1 E)) :
    IsBdd (qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑E)) := by

  set H : ℍ → ℂ := (⇑f : ℍ → ℂ) * ⇑E with hH
  set G : ℍ → ℂ := fun τ => H τ / (Δ τ) ^ m with hG
  have hΔ : ∀ τ : ℍ, (Δ τ) ^ m ≠ 0 := fun τ => pow_ne_zero _ (discriminant_ne_zero τ)
  have hGΔ : G * Δ ^ m = H := by
    funext τ; simp only [Pi.mul_apply, Pi.pow_apply, hG]; field_simp [hΔ τ]

  set HF : ModularForm Γ₁(M) (k + kE) := f.mul (resSL M E) with hHF
  have hHF_coe : (⇑HF : ℍ → ℂ) = H := by rw [hHF, coe_mul, coe_resSL]
  have hmdH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := f.holo'.mul E.holo'
  have hperH : Periodic (H ∘ ofComplex) 1 := by
    rw [← hHF_coe]; exact SlashInvariantFormClass.periodic_comp_ofComplex HF (one_mem_strictPeriods M)
  have hbdH : IsBoundedAtImInfty H := by
    have := (isBoundedAtImInfty_slash f 1).mul (ModularFormClass.bdd_at_infty E)
    first | exact this | simpa only [SlashAction.slash_one, IsBoundedAtImInfty] using this
  have hmdΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
    rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'
  have hmdG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
    intro τ
    exact (hmdH τ).div ((hmdΔ τ).pow m) (hΔ τ)

  have hcw : ∀ α : SL(2, ℤ), (fun τ => G (α • τ)) * Δ ^ m = ((⇑f : ℍ → ℂ) ∣[k] α) * ⇑E := by
    intro α
    funext τ
    have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
    simp only [Pi.mul_apply, Pi.pow_apply, hG, hH]
    rw [ModularForm.SL_slash_apply, disc_smul, levelOne_smul E, ModularGroup.sl_moeb]
    have hpow : (denom (α : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ) ^ m
        = denom (α : GL (Fin 2) ℝ) τ ^ (k + kE) * (Δ τ) ^ m := by
      rw [mul_pow, ← zpow_natCast, ← zpow_mul, hkE]
    rw [hpow, zpow_add₀ hd, zpow_neg]
    field_simp [hΔ τ, zpow_ne_zero k hd, zpow_ne_zero kE hd]

  have hinv1 : ∀ g ∈ Gamma1 M, ∀ τ : ℍ, G (g • τ) = G τ := by
    intro g hg τ
    have h1 := congrFun (hcw g) τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h1
    have h2 : ((⇑f : ℍ → ℂ) ∣[k] g) = ⇑f := by
      rw [ModularForm.SL_slash]
      exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hg)
    rw [h2] at h1
    have h3 : G τ * Δ τ ^ m = f τ * E τ := by
      have := congrFun hGΔ τ; simpa only [Pi.mul_apply, Pi.pow_apply, hH] using this
    exact mul_right_cancel₀ (hΔ τ) (h1.trans h3.symm)
  have hinv : ∀ g ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, G (g • τ) = G τ := fun g hg =>
    hinv1 g (Gamma_le_Gamma1 M hg)

  have hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ => G (α • τ)) * Δ ^ m) := by
    intro α
    rw [hcw α]
    exact (isBoundedAtImInfty_slash f α).mul (ModularFormClass.bdd_at_infty E)

  have hrat1 : IsRat (qExpansion 1 H) := by
    rw [hH]
    have : qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑E) = qExpansion 1 ⇑f * qExpansion 1 ⇑(resSL M E) := by
      rw [← coe_resSL M E, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) f (resSL M E)]
    rw [this]
    exact hf.mul hE
  have hratM : ∀ n, ∃ r : ℚ, (qExpansion M (G * Δ ^ m)).coeff n = (r : ℂ) := by
    intro n
    rw [hGΔ, qExpansion_coeff_widthN M hmdH hperH hbdH n]
    split_ifs
    · exact hrat1 _
    · exact ⟨0, by simp⟩

  obtain ⟨D, hD, hint⟩ :=
    ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant M m G hmdG hinv
      hbd hratM

  rw [isBdd_iff]
  refine ⟨D, hD, fun n => ?_⟩
  obtain ⟨z, hz⟩ := hint (M * n)
  refine ⟨z, ?_⟩
  rw [hGΔ, coeff_widthN_mul M hmdH hperH hbdH n] at hz
  exact hz

end Core

section Even

variable {M : ℕ} [NeZero M] {k : ℤ}

private def P4 : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 m : ℤ)

private def P6 : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 m : ℤ)

private theorem map_P4 : P4.map (Int.castRingHom ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n,
    P4, PowerSeries.coeff_mk, eq_intCast]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by
      rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]]
    push_cast
    ring

private theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three,
    bernoulli'_four, Nat.choose]
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  rw [h5]
  norm_num

private theorem map_P6 : P6.map (Int.castRingHom ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n,
    P6, PowerSeries.coeff_mk, eq_intCast]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 6 = 1 / 42 by
      rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]]
    push_cast
    ring

private theorem constantCoeff_P4 : PowerSeries.constantCoeff P4 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P4, PowerSeries.coeff_mk]; simp

private theorem constantCoeff_P6 : PowerSeries.constantCoeff P6 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P6, PowerSeries.coeff_mk]; simp

private def Eaux (a b : ℕ) : ModularForm 𝒮ℒ (a * 4 + b * 6) := (E₄.pow a).mul (E₆.pow b)

private theorem qExpansion_Eaux (a b : ℕ) :
    qExpansion 1 (⇑(Eaux a b)) = (P4 ^ a * P6 ^ b).map (Int.castRingHom ℂ) := by
  rw [Eaux, coe_mul, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, map_mul, map_pow, map_pow, map_P4, map_P6]

private theorem isRat_Eaux (a b : ℕ) : IsRat (qExpansion 1 (⇑(Eaux a b))) :=
  isRat_of_int _ (qExpansion_Eaux a b).symm

private theorem constantCoeff_Eaux (a b : ℕ) : PowerSeries.constantCoeff (P4 ^ a * P6 ^ b) = 1 := by
  rw [map_mul, map_pow, map_pow, constantCoeff_P4, constantCoeff_P6, one_pow, one_pow, one_mul]

private theorem exists_weights (hk : Even k) : ∃ (m a b : ℕ), k + (a * 4 + b * 6 : ℕ) = 12 * (m : ℤ) := by
  obtain ⟨j, rfl⟩ := hk
  rcases Int.emod_two_eq_zero_or_one j with hpar | hpar
  · set q : ℤ := j / 2 with hq
    have hjq : j = 2 * q := by omega
    have h0 : 0 ≤ 3 * (j.natAbs : ℤ) + 3 - q := by omega
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨j.natAbs + 1, a, 0, ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ← ha]
    omega
  · set q : ℤ := j / 2 with hq
    have hjq : j = 2 * q + 1 := by omega
    have h0 : 0 ≤ 3 * (j.natAbs : ℤ) + 1 - q := by omega
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨j.natAbs + 1, a, 1, ?_⟩
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ← ha]
    omega

private theorem isBdd_of_even (hk : Even k) (f : ModularForm Γ₁(M) k) (hf : IsRat (qExpansion 1 f)) :
    IsBdd (qExpansion 1 f) := by
  obtain ⟨m, a, b, hw⟩ := exists_weights hk
  have key := isBdd_mul f m (Eaux a b) (by exact_mod_cast hw) hf (isRat_Eaux a b)

  have hprod : qExpansion 1 ((⇑f : ℍ → ℂ) * ⇑(Eaux a b))
      = qExpansion 1 (⇑f : ℍ → ℂ) * (P4 ^ a * P6 ^ b).map (Int.castRingHom ℂ) := by
    rw [← qExpansion_Eaux, ← coe_resSL M (Eaux a b),
      ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) f (resSL M (Eaux a b))]
  exact IsBdd.of_mul_eq (constantCoeff_Eaux a b) key hprod.symm

end Even

section Odd

private theorem exists_E1 : ∃ E : ModularForm Γ₁(3) 1,
    EisensteinWeightOne.e1Chi3.map (Int.castRingHom ℂ) = qExpansion 1 (E : ℍ → ℂ) ∧
      PowerSeries.constantCoeff EisensteinWeightOne.e1Chi3 = 1 := by
  obtain ⟨E, hE⟩ := EisensteinWeightOne.e1Chi3IsModular
  refine ⟨E, ?_, ?_⟩
  swap
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [EisensteinWeightOne.e1Chi3]
  set c : ℕ → ℤ := fun n => PowerSeries.coeff n EisensteinWeightOne.e1Chi3 with hc

  have hchi : ∀ d : ℕ, |EisensteinWeightOne.chiNegThree d| ≤ 1 := by
    intro d
    unfold EisensteinWeightOne.chiNegThree
    split_ifs <;> simp
  have hcbound : ∀ n : ℕ, ‖((c n : ℤ) : ℂ)‖ ≤ 6 * n + 1 := by
    intro n
    rw [Complex.norm_intCast]
    simp only [hc, EisensteinWeightOne.e1Chi3, PowerSeries.coeff_mk]
    split_ifs with h0
    · subst h0; simp
    · have h1 : |EisensteinWeightOne.sigmaChi n| ≤ n := by
        unfold EisensteinWeightOne.sigmaChi
        calc |∑ d ∈ n.divisors, EisensteinWeightOne.chiNegThree d|
            ≤ ∑ d ∈ n.divisors, |EisensteinWeightOne.chiNegThree d| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _d ∈ n.divisors, (1 : ℤ) := Finset.sum_le_sum fun d _ => hchi d
          _ = n.divisors.card := by simp
          _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
      have h2 : |6 * EisensteinWeightOne.sigmaChi n| ≤ 6 * (n : ℤ) + 1 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℤ) ≤ 6)]; linarith
      rw [← Int.cast_abs]
      exact_mod_cast h2

  have hsum : ∀ z : ℍ, HasSum (fun n : ℕ => ((c n : ℤ) : ℂ) • Periodic.qParam 1 z ^ n) (E z) := by
    intro z
    have hq : ‖Periodic.qParam 1 z‖ < 1 := by
      have : 0 < 2 * π * z.im / 1 := by have := z.im_pos; positivity
      simpa [Periodic.qParam, Complex.norm_exp, neg_div] using this
    have hterm : ∀ n : ℕ, ((c n : ℤ) : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ))
        = ((c n : ℤ) : ℂ) • Periodic.qParam 1 z ^ n := by
      intro n
      rw [smul_eq_mul, Periodic.qParam, ← Complex.exp_nat_mul]
      congr 2
      push_cast
      ring
    have hS : Summable (fun n : ℕ => ((c n : ℤ) : ℂ) • Periodic.qParam 1 z ^ n) := by
      apply Summable.of_norm_bounded (g := fun n : ℕ => (6 * n + 1) * ‖Periodic.qParam 1 z‖ ^ n)
      · have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖Periodic.qParam 1 z‖) (by simpa using hq)
        have h2 := summable_geometric_of_norm_lt_one (by simpa using hq : ‖‖Periodic.qParam 1 z‖‖ < 1)
        have := (h1.mul_left 6).add h2
        refine this.congr fun n => ?_
        simp only [pow_one]; ring
      · intro n
        rw [norm_smul, norm_pow]
        exact mul_le_mul_of_nonneg_right (hcbound n) (pow_nonneg (norm_nonneg _) _)
    have := hS.hasSum
    have hEz : (∑' n : ℕ, ((c n : ℤ) : ℂ) • Periodic.qParam 1 z ^ n) = E z := by
      rw [hE z]; exact tsum_congr fun n => (hterm n).symm
    rwa [hEz] at this
  have hcoef : ∀ n, ((c n : ℤ) : ℂ) = (qExpansion 1 (E : ℍ → ℂ)).coeff n := fun n =>
    ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods 3) hsum n
  ext n
  rw [PowerSeries.coeff_map, ← hcoef n]
  rfl

variable {M : ℕ} [NeZero M] {k : ℤ}

private theorem isBdd_of_odd (hk : Odd k) (f : ModularForm Γ₁(M) k) (hf : IsRat (qExpansion 1 f)) :
    IsBdd (qExpansion 1 f) := by
  obtain ⟨E, hE, hE0⟩ := exists_E1
  haveI : NeZero (3 * M) := ⟨mul_ne_zero three_ne_zero (NeZero.ne M)⟩
  set f3 : ModularForm Γ₁(3 * M) k := res (dvd_mul_left M 3) f with hf3
  set E3 : ModularForm Γ₁(3 * M) 1 := res (dvd_mul_right 3 M) E with hE3
  set F : ModularForm Γ₁(3 * M) (k + 1) := f3.mul E3 with hF
  have hprod : qExpansion 1 (F : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) *
      EisensteinWeightOne.e1Chi3.map (Int.castRingHom ℂ) := by
    rw [hF, coe_mul, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods (3 * M)) f3 E3, hE]
    rfl
  have hFrat : IsRat (qExpansion 1 F) := by
    rw [hprod]
    exact hf.mul (isRat_of_int _ rfl)
  have hk1 : Even (k + 1) := hk.add_one
  have key := isBdd_of_even hk1 F hFrat
  exact IsBdd.of_mul_eq hE0 key hprod.symm

end Odd

private theorem isBdd_of_isRat {M : ℕ} [NeZero M] {k : ℤ} (f : ModularForm Γ₁(M) k) (hf : IsRat (qExpansion 1 f)) :
    IsBdd (qExpansion 1 f) := by
  rcases Int.even_or_odd k with hk | hk
  · exact isBdd_of_even hk f hf
  · exact isBdd_of_odd hk f hf

private theorem main (M : ℕ) [NeZero M] {k : ℤ} (f : ModularForm Γ₁(M) k) (hf : IsRat (qExpansion 1 f)) :
    ∃ (D : ℤ) (p : PowerSeries ℤ), D ≠ 0 ∧ IsIntegralQExp ((D : ℂ) • (⇑f : ℍ → ℂ)) p := by
  obtain ⟨D, P, hD, hP⟩ := isBdd_of_isRat f hf
  refine ⟨D, P, hD, ?_⟩
  rw [IsIntegralQExp, hP]
  have : ((D : ℂ) • (⇑f : ℍ → ℂ)) = ⇑((D : ℂ) • f) := by rw [FunLike.coe_smul]
  rw [this, ← ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods M)]
  rfl
end X1BoundedDenominators

theorem _root_.ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ)) :
    ∃ (D : ℤ) (p : PowerSeries ℤ), D ≠ 0 ∧
      ModularCurve.IsIntegralQExp ((D : ℂ) • (⇑f : UpperHalfPlane → ℂ)) p :=
  X1BoundedDenominators.main M f hf

end WLightS10.S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion

end
