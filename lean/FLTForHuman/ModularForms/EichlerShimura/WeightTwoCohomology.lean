/-
  Eichler--Shimura in weight two for `Γ_H(M)`, and the two-dimensional eigenspace.

  * `CohCarrier.exists_eichlerShimura_H1_gammaH`: the weight-two Eichler--Shimura isomorphism between
    the `Γ_H(M)` parabolic cohomology and the cusp forms — the period map is injective, its range is the
    parabolic part, and it is equivariant for the Hecke operators.
  * `CohCarrier.nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two`: the
    parabolic cohomology of `Γ_H(M)` has a two-element eigenbasis for the Hecke algebra, and every
    character's simultaneous eigenspace is two-dimensional.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_CohCarrier_exists_eichlerShimura_H1_gammaH.lean` (409 lines) and
  `S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two.lean` (477),
  with the statements from the wrappers of the same names.  The pin label namespaces `ESGammaH` and
  `ESGH` are both rectified to `EichlerShimuraGammaH`.

  spec-pin: Theorems/Thm_CohCarrier_exists_eichlerShimura_H1_gammaH.lean
  spec-pin: P2M/Sol/S_CohCarrier_exists_eichlerShimura_H1_gammaH.lean
  spec-pin: Theorems/Thm_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two.lean
  spec-pin: P2M/Sol/S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two.lean
-/
import FLTForHuman.ModularForms.CohCarrier.GammaHAlgebra
import FLTForHuman.ModularForms.CohCarrier.CharInvolution
import FLTForHuman.ModularForms.WeightTwoMultiplicityOne
import FLTForHuman.ModularForms.PrimitiveFormExistence
import FLTForHuman.ModularForms.EichlerShimura.PeriodPrimitive
import FLTForHuman.ModularForms.EichlerShimura.ExistsEquivariantPrimitive
import FLTForHuman.ModularForms.EichlerShimura.PeriodOf
import FLTForHuman.ModularCurve.Period.ParabolicHoms
import FLTForHuman.ModularCurve.Period.ParabolicHomsBasis
import FLTForHuman.ModularCurve.Period.PeriodLatticeRank
import FLTForHuman.ModularCurve.Period.PeriodMapHecke
import FLTForHuman.ModularForms.WeightOne.Basic
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularCurve ModularCurve.Period UpperHalfPlane

open scoped MatrixGroups ModularForm ComplexConjugate
open CongruenceSubgroup ModularCurve ModularCurve.Period UpperHalfPlane
open scoped MatrixGroups ModularForm ComplexConjugate

namespace CohCarrier
namespace EichlerShimuraGammaH
open CohCarrier
variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

section Reflection

private theorem jConjSL_entry_00 (γ : SL(2, ℤ)) : (jConjSL γ) 0 0 = γ 0 0 := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = _
  rw [jConjMat_apply_zero_zero]

private theorem jConjSL_entry_01 (γ : SL(2, ℤ)) : (jConjSL γ) 0 1 = -(γ 0 1) := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = _
  rw [jConjMat_apply_zero_one]

private theorem jConjSL_entry_10 (γ : SL(2, ℤ)) : (jConjSL γ) 1 0 = -(γ 1 0) := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = _
  rw [jConjMat_apply_one_zero]

private theorem jConjSL_entry_11 (γ : SL(2, ℤ)) : (jConjSL γ) 1 1 = γ 1 1 := by
  show jConjMat ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = _
  rw [jConjMat_apply_one_one]

private theorem J_smul_sl_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.J • (γ • τ) = jConjSL γ • (UpperHalfPlane.J • τ) := by
  ext1
  rw [coe_J_smul, UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply, coe_J_smul,
    jConjSL_entry_00, jConjSL_entry_01, jConjSL_entry_10, jConjSL_entry_11,
    map_neg, map_neg, Complex.ofReal_neg, Complex.ofReal_neg, map_div₀, map_add, map_add,
    map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_ofReal]
  ring

private theorem J_smul_I : UpperHalfPlane.J • UpperHalfPlane.I = UpperHalfPlane.I := by
  ext1
  rw [coe_J_smul, coe_I, Complex.conj_I, neg_neg]

end Reflection

section Twins


omit [NeZero M] in
private theorem periodOf_jConj (f fρ : CuspForm (CohCarrier.GammaH M H) 2)
    (hρ : ∀ τ : ℍ, fρ τ = conj (f (UpperHalfPlane.J • τ))) (γ : ↥(CohCarrier.GammaH M H)) :
    periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) f =
      -conj (periodOf (CohCarrier.GammaH M H) γ fρ) := by
  have h := periodAlongOf_eq_neg_conj_periodAlongOf_J_smul (CohCarrier.GammaH M H) f fρ hρ
    UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
  rw [J_smul_sl_smul, J_smul_I] at h
  show periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I
      (((jConjGammaH M H γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) • UpperHalfPlane.I) f =
    -conj (periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I) fρ)
  rw [coe_jConjGammaH, h, map_neg, neg_neg, Complex.conj_conj]

private theorem eq_zero_of_periodOf_eq_conj (h h' : CuspForm (CohCarrier.GammaH M H) 2)
    (hc : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ h = conj (periodOf (CohCarrier.GammaH M H) γ h')) :
    h = 0 := by

  have hsum : Complex.I • (h + h') = 0 := by
    refine eq_zero_of_forall_re_periodOf_eq_zero (CohCarrier.GammaH M H) _ fun γ => ?_
    rw [map_smul, map_add, smul_eq_mul, hc γ]
    set p : ℂ := periodOf (CohCarrier.GammaH M H) γ h' with hp
    have e : conj p + p = ((2 * p.re : ℝ) : ℂ) := by rw [add_comm, Complex.add_conj]
    rw [e, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hh' : h' = -h := by
    have h0 : h + h' = 0 := (smul_eq_zero.mp hsum).resolve_left Complex.I_ne_zero
    exact eq_neg_of_add_eq_zero_right h0
  subst hh'
  refine eq_zero_of_forall_re_periodOf_eq_zero (CohCarrier.GammaH M H) h fun γ => ?_
  have h1 := hc γ
  rw [map_neg, map_neg] at h1
  have hre := congrArg Complex.re h1
  rw [Complex.neg_re, Complex.conj_re] at hre
  linarith

private theorem twin_plus (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ f +
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) f = 0) : f = 0 := by
  obtain ⟨fρ, hρ⟩ := CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
    (CohCarrier.GammaH M H) (fun γ hγ => jConjSL_mem_GammaH M H hγ) 2 f
  refine eq_zero_of_periodOf_eq_conj M H f fρ fun γ => ?_
  have h1 := hf γ
  rw [periodOf_jConj M H f fρ hρ γ] at h1
  linear_combination h1

private theorem twin_minus (g : CuspForm (CohCarrier.GammaH M H) 2)
    (hg : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ g -
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) g = 0) : g = 0 := by
  obtain ⟨gρ, hρ⟩ := CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
    (CohCarrier.GammaH M H) (fun γ hγ => jConjSL_mem_GammaH M H hγ) 2 g
  refine eq_zero_of_periodOf_eq_conj M H g (-gρ) fun γ => ?_
  have h1 := hg γ
  rw [periodOf_jConj M H g gρ hρ γ] at h1
  rw [map_neg, map_neg]
  linear_combination h1

end Twins

section Maps

private def perLin : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] CohCarrier.H1 M H ℂ where
  toFun f := periodMapOf (CohCarrier.GammaH M H) f
  map_add' f g := by
    refine AddMonoidHom.ext fun x => ?_
    have e : x = Additive.ofMul (Additive.toMul x) := rfl
    rw [AddMonoidHom.add_apply, e, periodMapOf_apply_eq_periodOf, periodMapOf_apply_eq_periodOf,
      periodMapOf_apply_eq_periodOf, map_add]
  map_smul' c f := by
    refine AddMonoidHom.ext fun x => ?_
    have e : x = Additive.ofMul (Additive.toMul x) := rfl
    rw [RingHom.id_apply, AddMonoidHom.smul_apply, e, periodMapOf_apply_eq_periodOf,
      periodMapOf_apply_eq_periodOf, map_smul]

private theorem perLin_apply (f : CuspForm (CohCarrier.GammaH M H) 2) :
    perLin M H f = periodMapOf (CohCarrier.GammaH M H) f := by
  rfl

private theorem perLin_apply_ofMul (f : CuspForm (CohCarrier.GammaH M H) 2) (γ : ↥(CohCarrier.GammaH M H)) :
    perLin M H f (Additive.ofMul γ) = periodOf (CohCarrier.GammaH M H) γ f := by
  exact periodMapOf_apply_eq_periodOf _ f γ

private def ι : CohCarrier.H1 M H ℂ →ₗ[ℂ] CohCarrier.H1 M H ℂ := CohCarrier.charInvolution M H ℂ ℂ

omit [NeZero M] in
private theorem ι_apply_ofMul (φ : CohCarrier.H1 M H ℂ) (γ : ↥(CohCarrier.GammaH M H)) :
    ι M H φ (Additive.ofMul γ) = φ (Additive.ofMul (jConjGammaH M H γ)) := rfl

omit [NeZero M] in
private theorem ι_ι (φ : CohCarrier.H1 M H ℂ) : ι M H (ι M H φ) = φ :=
  charInvolution_charInvolution M H ℂ ℂ φ


omit [NeZero M] in
private theorem ι_mem_parabolicHoms {φ : CohCarrier.H1 M H ℂ}
    (hφ : φ ∈ parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) :
    ι M H φ ∈ parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ := by
  rw [mem_parabolicHoms_iff] at hφ ⊢
  intro γ hγ
  rw [ι_apply_ofMul]
  refine hφ (jConjGammaH M H γ) ?_
  have htr : (((jConjGammaH M H γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
    rw [coe_jConjGammaH, jConjSL_coe, jConjMat_trace]
  rw [htr]
  exact hγ

private def ES : (CuspForm (CohCarrier.GammaH M H) 2 × CuspForm (CohCarrier.GammaH M H) 2) →ₗ[ℂ]
    CohCarrier.H1 M H ℂ :=
  LinearMap.coprod ((LinearMap.id + ι M H) ∘ₗ perLin M H) ((LinearMap.id - ι M H) ∘ₗ perLin M H)

private theorem ES_apply (f g : CuspForm (CohCarrier.GammaH M H) 2) :
    ES M H (f, g) = (perLin M H f + ι M H (perLin M H f)) + (perLin M H g - ι M H (perLin M H g)) := by
  rfl

private theorem ES_apply_ofMul (f g : CuspForm (CohCarrier.GammaH M H) 2) (γ : ↥(CohCarrier.GammaH M H)) :
    ES M H (f, g) (Additive.ofMul γ) =
      periodOf (CohCarrier.GammaH M H) γ f +
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) f +
        periodOf (CohCarrier.GammaH M H) γ g -
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) g := by
  rw [ES_apply, AddMonoidHom.add_apply, AddMonoidHom.add_apply, AddMonoidHom.sub_apply, ι_apply_ofMul,
    ι_apply_ofMul, perLin_apply_ofMul, perLin_apply_ofMul, perLin_apply_ofMul, perLin_apply_ofMul]
  ring

end Maps

section Injective

private theorem ES_injective : Function.Injective (ES M H) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  rintro ⟨f, g⟩ h0
  have hval : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ f +
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) f +
        periodOf (CohCarrier.GammaH M H) γ g -
        periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) g = 0 := by
    intro γ
    have := congrArg (fun φ : CohCarrier.H1 M H ℂ => φ (Additive.ofMul γ)) h0
    beta_reduce at this
    rwa [ES_apply_ofMul, AddMonoidHom.zero_apply] at this
  have hA : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ f + periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) f = 0 := by
    intro γ
    have h1 := hval γ
    have h2 := hval (jConjGammaH M H γ)
    rw [jConjGammaH_jConjGammaH] at h2
    linear_combination (h1 + h2) / 2
  have hB : ∀ γ : ↥(CohCarrier.GammaH M H),
      periodOf (CohCarrier.GammaH M H) γ g - periodOf (CohCarrier.GammaH M H) (jConjGammaH M H γ) g = 0 := by
    intro γ
    have h1 := hval γ
    have h2 := hval (jConjGammaH M H γ)
    rw [jConjGammaH_jConjGammaH] at h2
    linear_combination (h1 - h2) / 2
  have hf : f = 0 := twin_plus M H f hA
  have hg : g = 0 := twin_minus M H g hB
  rw [hf, hg]
  rfl

end Injective

section Range

private theorem ES_range_le :
    LinearMap.range (ES M H) ≤ parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ := by
  rintro _ ⟨⟨f, g⟩, rfl⟩
  have hf : perLin M H f ∈ parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ :=
    periodMapOf_mem_parabolicHoms (CohCarrier.GammaH M H) f
  have hg : perLin M H g ∈ parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ :=
    periodMapOf_mem_parabolicHoms (CohCarrier.GammaH M H) g
  rw [ES_apply]
  exact add_mem (add_mem hf (ι_mem_parabolicHoms M H hf)) (sub_mem hg (ι_mem_parabolicHoms M H hg))

private theorem isCongruenceSubgroup_GammaH : IsCongruenceSubgroup (CohCarrier.GammaH M H) :=
  ⟨M, NeZero.ne _, CohCarrier.Gamma_le_GammaH M H⟩

private theorem ES_range :
    LinearMap.range (ES M H) = parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ := by
  obtain ⟨n, b, hb⟩ := exists_basis_parabolicHoms_castAddHom_comp (CohCarrier.GammaH M H)
  obtain ⟨bC, -⟩ := hb ℂ
  have : Module.Finite ℂ ↥(parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) := Module.Finite.of_basis bC
  have : FiniteDimensional ℂ (CuspForm (CohCarrier.GammaH M H) 2) :=
    CuspForm.finiteDimensional_of_isArithmetic _ 2
  have hP : Module.finrank ℂ ↥(parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) ≤
      2 * Module.finrank ℂ (CuspForm (CohCarrier.GammaH M H) 2) := by
    have hZ := finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
      (CohCarrier.GammaH M H) (isCongruenceSubgroup_GammaH M H)
    rw [Module.finrank_eq_card_basis b] at hZ
    rw [Module.finrank_eq_card_basis bC]
    exact hZ
  have hr : Module.finrank ℂ ↥(LinearMap.range (ES M H)) =
      2 * Module.finrank ℂ (CuspForm (CohCarrier.GammaH M H) 2) := by
    rw [LinearMap.finrank_range_of_inj (ES_injective M H), Module.finrank_prod, two_mul]
  refine Submodule.eq_of_le_of_finrank_eq (ES_range_le M H) (le_antisymm ?_ ?_)
  · exact Submodule.finrank_mono (ES_range_le M H)
  · rw [hr]; exact hP

end Range

section Equivariance

private theorem ι_heckeT {ℓ : ℕ} (hℓ : ℓ.Prime) (φ : CohCarrier.H1 M H ℂ) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ι M H (CohCarrier.heckeT M H ℓ ℂ φ) = CohCarrier.heckeT M H ℓ ℂ (ι M H φ) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  by_cases hℓM : ℓ ∣ M
  · exact LinearMap.congr_fun (charInvolution_comp_opFamily M H (∅ : Set ℕ) ℂ (Gen.U ℓ hℓ hℓM)) φ
  · exact LinearMap.congr_fun
      (charInvolution_comp_opFamily M H (∅ : Set ℕ) ℂ (Gen.T ℓ hℓ (Set.notMem_empty ℓ) hℓM)) φ

private theorem ι_diamondL (d : (ZMod M)ˣ) (φ : CohCarrier.H1 M H ℂ) :
    ι M H (CohCarrier.diamondL M H ℂ d φ) = CohCarrier.diamondL M H ℂ d (ι M H φ) :=
  LinearMap.congr_fun (charInvolution_comp_opFamily M H (∅ : Set ℕ) ℂ (Gen.dia d)) φ

private theorem perLin_heckeTLinH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    perLin M H (CuspForm.heckeTLinH 2 hℓ hℓM f) = CohCarrier.heckeT M H ℓ ℂ (perLin M H f) :=
  periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash M H hℓ hℓM
    (CohCarrier.gammaLift M (CohCarrier.unitOfPrimeNotDvd hℓ hℓM)) (CohCarrier.gammaLift_apply_11 hℓ hℓM) f _
    (CuspForm.coe_heckeTLinH_apply 2 hℓ hℓM (CuspForm.stableT M H 2 hℓ hℓM) f)

private theorem perLin_heckeULinH {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) 2) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    perLin M H (CuspForm.heckeULinH 2 q f) = CohCarrier.heckeT M H q ℂ (perLin M H f) :=
  periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU M H hq hqM f _
    (CuspForm.coe_heckeULinH_apply 2 (CuspForm.stableU M H 2 hq hqM) f)

private theorem perLin_diamondLinH (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    perLin M H (CuspForm.diamondLinH 2 d f) = CohCarrier.diamondL M H ℂ d (perLin M H f) := by
  rw [CohCarrier.diamondL_eq_diamondRaw M H ℂ d (CohCarrier.gammaLift M d) (CohCarrier.gamma0Units_gammaLift d)]
  exact periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash M H (CohCarrier.gammaLift M d) f _
    (CuspForm.coe_diamondLinH_apply 2 (CuspForm.stableD M H 2) d f)

private theorem ES_heckeTLinH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ES M H (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) =
      CohCarrier.heckeT M H ℓ ℂ (ES M H (f, g)) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [ES_apply, ES_apply, perLin_heckeTLinH, perLin_heckeTLinH, ι_heckeT M H hℓ, ι_heckeT M H hℓ,
    map_add, map_add, map_sub]

private theorem ES_heckeULinH {q : ℕ} (hq : q.Prime) (hqM : q ∣ M)
    (f g : CuspForm (CohCarrier.GammaH M H) 2) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ES M H (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) =
      CohCarrier.heckeT M H q ℂ (ES M H (f, g)) := by
  have : NeZero q := ⟨hq.ne_zero⟩
  rw [ES_apply, ES_apply, perLin_heckeULinH M H hq hqM, perLin_heckeULinH M H hq hqM, ι_heckeT M H hq,
    ι_heckeT M H hq, map_add, map_add, map_sub]

private theorem ES_diamondLinH (d : (ZMod M)ˣ) (f g : CuspForm (CohCarrier.GammaH M H) 2) :
    ES M H (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) =
      CohCarrier.diamondL M H ℂ d (ES M H (f, g)) := by
  rw [ES_apply, ES_apply, perLin_diamondLinH, perLin_diamondLinH, ι_diamondL, ι_diamondL,
    map_add, map_add, map_sub]

end Equivariance

private theorem main :
    ∃ (J : ↥(CohCarrier.GammaH M H) →* ↥(CohCarrier.GammaH M H))
      (ES : (CuspForm (CohCarrier.GammaH M H) 2 × CuspForm (CohCarrier.GammaH M H) 2)
        →ₗ[ℂ] CohCarrier.H1 M H ℂ),
      (∀ γ : ↥(CohCarrier.GammaH M H), ((J γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) =
        ModularCurve.Period.jConjSL (γ : SL(2, ℤ))) ∧
      (∀ (f g : CuspForm (CohCarrier.GammaH M H) 2) (γ : ↥(CohCarrier.GammaH M H)),
        ES (f, g) (Additive.ofMul γ) =
          ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul γ) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul (J γ)) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul γ) -
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul (J γ))) ∧
      Function.Injective ES ∧
      LinearMap.range ES = ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ES (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) =
          CohCarrier.heckeT M H ℓ ℂ (ES (f, g))) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero q := ⟨hq.ne_zero⟩
        ES (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) =
          CohCarrier.heckeT M H q ℂ (ES (f, g))) ∧
      (∀ (d : (ZMod M)ˣ) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        ES (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) =
          CohCarrier.diamondL M H ℂ d (ES (f, g))) := by
  refine ⟨jConjGammaH M H, ES M H, fun γ => rfl, ?_, ES_injective M H, ES_range M H,
    fun ℓ hℓ hℓM f g => ES_heckeTLinH M H hℓ hℓM f g,
    fun q hq hqM f g => ES_heckeULinH M H hq hqM f g,
    fun d f g => ES_diamondLinH M H d f g⟩
  intro f g γ
  rw [ES_apply_ofMul, periodMapOf_apply_eq_periodOf, periodMapOf_apply_eq_periodOf,
    periodMapOf_apply_eq_periodOf, periodMapOf_apply_eq_periodOf]

end CohCarrier.EichlerShimuraGammaH


open scoped MatrixGroups

theorem CohCarrier.exists_eichlerShimura_H1_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ (J : ↥(CohCarrier.GammaH M H) →* ↥(CohCarrier.GammaH M H))
      (ES : (CuspForm (CohCarrier.GammaH M H) 2 × CuspForm (CohCarrier.GammaH M H) 2)
        →ₗ[ℂ] CohCarrier.H1 M H ℂ),
      (∀ γ : ↥(CohCarrier.GammaH M H), ((J γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) =
        ModularCurve.Period.jConjSL (γ : SL(2, ℤ))) ∧
      (∀ (f g : CuspForm (CohCarrier.GammaH M H) 2) (γ : ↥(CohCarrier.GammaH M H)),
        ES (f, g) (Additive.ofMul γ) =
          ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul γ) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) f (Additive.ofMul (J γ)) +
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul γ) -
            ModularCurve.periodMapOf (CohCarrier.GammaH M H) g (Additive.ofMul (J γ))) ∧
      Function.Injective ES ∧
      LinearMap.range ES = ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        ES (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) =
          CohCarrier.heckeT M H ℓ ℂ (ES (f, g))) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        haveI : NeZero q := ⟨hq.ne_zero⟩
        ES (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) =
          CohCarrier.heckeT M H q ℂ (ES (f, g))) ∧
      (∀ (d : (ZMod M)ˣ) (f g : CuspForm (CohCarrier.GammaH M H) 2),
        ES (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) =
          CohCarrier.diamondL M H ℂ d (ES (f, g))) := by
  exact CohCarrier.EichlerShimuraGammaH.main M H

open ModularCurve.Period

namespace EichlerShimuraGammaH

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

private abbrev S2 : Type := CuspForm (CohCarrier.GammaH M H) 2

private abbrev V : Type := ↥(parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)

scoped instance instAddCommGroupV : AddCommGroup (V M H) := Submodule.addCommGroup _

scoped instance (priority := 10000) instAddCommMonoidV : AddCommMonoid (V M H) :=
  (instAddCommGroupV M H).toAddCommMonoid

variable (S : Set ℕ)

private def Gf : Set (Module.End ℂ (S2 M H)) :=
  {T | (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
       (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
       (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)}

private abbrev 𝔸 : Subalgebra ℂ (Module.End ℂ (S2 M H)) := Algebra.adjoin ℂ (Gf M H S)

private def Gc : Set (Module.End ℂ (V M H)) :=
  {T : Module.End ℂ (V M H) |
    (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      ((T v : V M H) : CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
    (∃ d : (ZMod M)ˣ, ∀ v,
      ((T v : V M H) : CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))}

private def A : Subalgebra ℂ (Module.End ℂ (V M H)) := Algebra.adjoin ℂ (Gc M H S)

private theorem A_def : A M H S = Algebra.adjoin ℂ (Gc M H S) := by
  rfl

section Psi

variable {M H}
variable (E : (S2 M H × S2 M H) ≃ₗ[ℂ] V M H)

private def Ψ : Module.End ℂ (S2 M H) →ₐ[ℂ] Module.End ℂ (V M H) where
  toFun t := E.toLinearMap ∘ₗ (t.prodMap t) ∘ₗ E.symm.toLinearMap
  map_one' := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap 1 1 (E.symm v)) = v
    rw [LinearMap.prodMap_one]
    exact E.apply_symm_apply v
  map_mul' s t := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap (s * t) (s * t) (E.symm v)) =
      E (LinearMap.prodMap s s (E.symm (E (LinearMap.prodMap t t (E.symm v)))))
    rw [E.symm_apply_apply]
    rfl
  map_zero' := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap 0 0 (E.symm v)) = 0
    rw [LinearMap.prodMap_zero, LinearMap.zero_apply, map_zero]
  map_add' s t := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap (s + t) (s + t) (E.symm v)) =
      E (LinearMap.prodMap s s (E.symm v)) + E (LinearMap.prodMap t t (E.symm v))
    rw [← map_add]
    rfl
  commutes' c := by
    apply LinearMap.ext; intro v
    change E (LinearMap.prodMap (algebraMap ℂ (Module.End ℂ (S2 M H)) c)
      (algebraMap ℂ (Module.End ℂ (S2 M H)) c) (E.symm v)) = (algebraMap ℂ (Module.End ℂ (V M H)) c) v
    rw [Module.algebraMap_end_eq_smul_id, Module.algebraMap_end_eq_smul_id]
    change E (c • (E.symm v).1, c • (E.symm v).2) = c • v
    rw [← Prod.smul_mk, map_smul]
    exact congrArg (c • ·) (E.apply_symm_apply v)

omit [NeZero M] in
private theorem Ψ_apply_E (t : Module.End ℂ (S2 M H)) (f g : S2 M H) : Ψ E t (E (f, g)) = E (t f, t g) := by
  change E (LinearMap.prodMap t t (E.symm (E (f, g)))) = _
  rw [E.symm_apply_apply]
  rfl

omit [NeZero M] in
private theorem Ψ_injective : Function.Injective (Ψ E) := by
  intro s t h
  apply LinearMap.ext
  intro f
  have := congrArg (fun x : Module.End ℂ (V M H) => (E.symm (x (E (f, 0)))).1) h
  simp only [Ψ_apply_E, LinearEquiv.symm_apply_apply] at this
  exact this

end Psi

end EichlerShimuraGammaH

namespace EichlerShimuraGammaH

section Main

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ}
variable (E : (S2 M H × S2 M H) ≃ₗ[ℂ] V M H)
  (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f g : S2 M H),
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((E (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.heckeT M H ℓ ℂ ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ))
  (hU : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (f g : S2 M H),
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ((E (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.heckeT M H q ℂ ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ))
  (hD : ∀ (d : (ZMod M)ˣ) (f g : S2 M H),
    ((E (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.diamondL M H ℂ d ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ))

include hT in
private theorem coe_Ψ_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (v : V M H) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ((Ψ E (CuspForm.heckeTLinH 2 hℓ hℓM) v : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ) := by
  obtain ⟨⟨f, g⟩, rfl⟩ := E.surjective v
  rw [Ψ_apply_E]
  exact hT ℓ hℓ hℓM f g

include hU in
private theorem coe_Ψ_U (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (v : V M H) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ((Ψ E (CuspForm.heckeULinH 2 q) v : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.heckeT M H q ℂ (v : CohCarrier.H1 M H ℂ) := by
  obtain ⟨⟨f, g⟩, rfl⟩ := E.surjective v
  rw [Ψ_apply_E]
  exact hU q hq hqM f g

include hD in
private theorem coe_Ψ_D (d : (ZMod M)ˣ) (v : V M H) :
    ((Ψ E (CuspForm.diamondLinH 2 d) v : V M H) : CohCarrier.H1 M H ℂ) =
      CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ) := by
  obtain ⟨⟨f, g⟩, rfl⟩ := E.surjective v
  rw [Ψ_apply_E]
  exact hD d f g

include hT hU hD in
private theorem Gc_eq : Gc M H S = (Ψ E) '' (Gf M H S) := by
  ext T
  constructor
  · rintro (⟨ℓ, hℓ, hℓS, h⟩ | ⟨d, h⟩)
    · by_cases hℓM : ℓ ∣ M
      · refine ⟨CuspForm.heckeULinH 2 ℓ, Or.inr (Or.inl ⟨ℓ, hℓ, hℓM, rfl⟩), ?_⟩
        apply LinearMap.ext; intro v; apply Subtype.ext
        rw [coe_Ψ_U E hU ℓ hℓ hℓM, h v]
      · have hℓS' : ℓ ∉ S := by rcases hℓS with h' | h'; exacts [h', absurd h' hℓM]
        refine ⟨CuspForm.heckeTLinH 2 hℓ hℓM, Or.inl ⟨ℓ, hℓ, hℓM, hℓS', rfl⟩, ?_⟩
        apply LinearMap.ext; intro v; apply Subtype.ext
        rw [coe_Ψ_T E hT ℓ hℓ hℓM, h v]
    · refine ⟨CuspForm.diamondLinH 2 d, Or.inr (Or.inr ⟨d, rfl⟩), ?_⟩
      apply LinearMap.ext; intro v; apply Subtype.ext
      rw [coe_Ψ_D E hD d, h v]
  · rintro ⟨t, (⟨ℓ, hℓ, hℓM, hℓS, rfl⟩ | ⟨q, hq, hqM, rfl⟩ | ⟨d, rfl⟩), rfl⟩
    · exact Or.inl ⟨ℓ, hℓ, Or.inl hℓS, fun v => coe_Ψ_T E hT ℓ hℓ hℓM v⟩
    · exact Or.inl ⟨q, hq, Or.inr hqM, fun v => coe_Ψ_U E hU q hq hqM v⟩
    · exact Or.inr ⟨d, fun v => coe_Ψ_D E hD d v⟩

include hT hU hD in
private theorem A_eq_map : A M H S = (𝔸 M H S).map (Ψ E) := by
  rw [A_def, Gc_eq E hT hU hD, AlgHom.map_adjoin]

variable (b : Module.Basis (Fin 1) ↥(𝔸 M H S) (S2 M H))

private def f₀ : S2 M H := b 0

private theorem hf₀ (g : S2 M H) : ∃ T : ↥(𝔸 M H S), (T : Module.End ℂ (S2 M H)) (f₀ b) = g := by
  refine ⟨b.repr g 0, ?_⟩
  have := b.sum_repr g
  rw [Fin.sum_univ_one] at this
  exact this

private theorem eq_zero_of_apply_f₀ (t : ↥(𝔸 M H S)) (ht : (t : Module.End ℂ (S2 M H)) (f₀ b) = 0) : t = 0 := by
  have hli := b.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  exact hli (fun _ => t) (by rw [Fin.sum_univ_one]; exact ht) 0

private def κ : (↥(𝔸 M H S) × ↥(𝔸 M H S)) →ₗ[ℂ] V M H :=
  E.toLinearMap ∘ₗ
    (((LinearMap.applyₗ (f₀ b)).comp (𝔸 M H S).val.toLinearMap).prodMap
      ((LinearMap.applyₗ (f₀ b)).comp (𝔸 M H S).val.toLinearMap))

private theorem κ_apply (t : ↥(𝔸 M H S) × ↥(𝔸 M H S)) :
    κ E b t = E ((t.1 : Module.End ℂ (S2 M H)) (f₀ b), (t.2 : Module.End ℂ (S2 M H)) (f₀ b)) := by
  rfl

private theorem κ_bijective : Function.Bijective (κ E b) := by
  constructor
  · intro s t h
    rw [κ_apply, κ_apply] at h
    have h' := E.injective h
    simp only [Prod.mk.injEq] at h'
    have h1 : s.1 - t.1 = 0 := eq_zero_of_apply_f₀ b _ (by
      rw [Subalgebra.coe_sub, LinearMap.sub_apply, h'.1, sub_self])
    have h2 : s.2 - t.2 = 0 := eq_zero_of_apply_f₀ b _ (by
      rw [Subalgebra.coe_sub, LinearMap.sub_apply, h'.2, sub_self])
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  · intro v
    obtain ⟨⟨f, g⟩, rfl⟩ := E.surjective v
    obtain ⟨T₀, hT₀⟩ := hf₀ b f
    obtain ⟨T₁, hT₁⟩ := hf₀ b g
    exact ⟨(T₀, T₁), by rw [κ_apply, hT₀, hT₁]⟩

variable (hA : A M H S = (𝔸 M H S).map (Ψ E))

private def bv : Fin 2 → V M H := ![E (f₀ b, 0), E (0, f₀ b)]

include hA in
private theorem exists_of_mem_A (a : ↥(A M H S)) : ∃ t : ↥(𝔸 M H S), (a : Module.End ℂ (V M H)) = Ψ E t := by
  have ha : (a : Module.End ℂ (V M H)) ∈ (𝔸 M H S).map (Ψ E) := hA ▸ a.2
  obtain ⟨t, ht, hta⟩ := Subalgebra.mem_map.mp ha
  exact ⟨⟨t, ht⟩, hta.symm⟩

private theorem smul_bv_sum (t₀ t₁ : ↥(𝔸 M H S)) :
    (Ψ E t₀) (E (f₀ b, 0)) + (Ψ E t₁) (E (0, f₀ b)) =
      E ((t₀ : Module.End ℂ (S2 M H)) (f₀ b), (t₁ : Module.End ℂ (S2 M H)) (f₀ b)) := by
  rw [Ψ_apply_E, Ψ_apply_E, map_zero, map_zero, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

include hA in
private theorem linearIndependent_bv : LinearIndependent ↥(A M H S) (bv E b) := by
  refine (Fintype.linearIndependent_iff (ι := Fin 2) (R := ↥(A M H S)) (v := bv E b)).mpr ?_
  intro c hc
  obtain ⟨t₀, ht₀⟩ := exists_of_mem_A E hA (c 0)
  obtain ⟨t₁, ht₁⟩ := exists_of_mem_A E hA (c 1)
  rw [Fin.sum_univ_two] at hc
  change (c 0 : Module.End ℂ (V M H)) (E (f₀ b, 0)) + (c 1 : Module.End ℂ (V M H)) (E (0, f₀ b)) = 0 at hc
  rw [ht₀, ht₁, smul_bv_sum, ← κ_apply E b (t₀, t₁)] at hc
  have h0 : (t₀, t₁) = 0 := (κ_bijective E b).1 (hc.trans (map_zero _).symm)
  simp only [Prod.mk_eq_zero] at h0
  intro i
  fin_cases i
  · apply Subtype.ext; change (c 0 : Module.End ℂ (V M H)) = 0; rw [ht₀, h0.1]; exact map_zero _
  · apply Subtype.ext; change (c 1 : Module.End ℂ (V M H)) = 0; rw [ht₁, h0.2]; exact map_zero _

include hA in
private theorem span_bv : ⊤ ≤ Submodule.span ↥(A M H S) (Set.range (bv E b)) := by
  intro v _
  obtain ⟨⟨t₀, t₁⟩, rfl⟩ := (κ_bijective E b).2 v
  rw [κ_apply, ← smul_bv_sum]
  have hm0 : Ψ E t₀ ∈ A M H S := by rw [hA]; exact Subalgebra.mem_map.mpr ⟨_, t₀.2, rfl⟩
  have hm1 : Ψ E t₁ ∈ A M H S := by rw [hA]; exact Subalgebra.mem_map.mpr ⟨_, t₁.2, rfl⟩
  have e0 : (Ψ E t₀) (E (f₀ b, 0)) = (⟨Ψ E t₀, hm0⟩ : ↥(A M H S)) • bv E b 0 := rfl
  have e1 : (Ψ E t₁) (E (0, f₀ b)) = (⟨Ψ E t₁, hm1⟩ : ↥(A M H S)) • bv E b 1 := rfl
  rw [e0, e1]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

private def basisA : Module.Basis (Fin 2) ↥(A M H S) (V M H) :=
  Module.Basis.mk (linearIndependent_bv E b hA) (span_bv E b hA)

private def eig𝔸 (χ' : ↥(𝔸 M H S) → ℂ) : Submodule ℂ ↥(𝔸 M H S) where
  carrier := {x | ∀ t : ↥(𝔸 M H S), t * x = χ' t • x}
  zero_mem' t := by simp
  add_mem' {x y} hx hy t := by rw [mul_add, hx t, hy t, smul_add]
  smul_mem' c x hx t := by rw [mul_smul_comm, hx t, smul_comm]

include b in
private theorem eig𝔸_line (χ' : ↥(𝔸 M H S) →ₐ[ℂ] ℂ)
    (hone : Module.finrank ℂ ↥(⨅ a : ↥(𝔸 M H S),
      Module.End.eigenspace (a : Module.End ℂ (S2 M H)) (χ' a)) = 1) :
    ∃ x₀ : ↥(𝔸 M H S), x₀ ∈ eig𝔸 (S := S) χ' ∧ x₀ ≠ 0 ∧
      ∀ y ∈ eig𝔸 (S := S) χ', ∃ c : ℂ, y = c • x₀ := by
  set W : Submodule ℂ (S2 M H) := ⨅ a : ↥(𝔸 M H S),
    Module.End.eigenspace (a : Module.End ℂ (S2 M H)) (χ' a) with hW
  have hmemW : ∀ w : S2 M H, w ∈ W ↔ ∀ a : ↥(𝔸 M H S), (a : Module.End ℂ (S2 M H)) w = χ' a • w := by
    intro w
    simp only [hW, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have : Module.Finite ℂ ↥W := Module.finite_of_finrank_eq_succ hone
  obtain ⟨w₀, hw₀W, hw₀⟩ : ∃ w₀ : S2 M H, w₀ ∈ W ∧ w₀ ≠ 0 := by
    have : 0 < Module.finrank ℂ ↥W := by rw [hone]; exact one_pos
    obtain ⟨⟨w, hw⟩, hne⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp this
    exact ⟨w, hw, fun h => hne (Subtype.ext h)⟩
  have hline : ∀ w ∈ W, ∃ c : ℂ, w = c • w₀ := by
    intro w hw
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w₀, hw₀W⟩ : ↥W)
      (fun h => hw₀ (congrArg Subtype.val h))).mp hone ⟨w, hw⟩
    exact ⟨c, by have := congrArg Subtype.val hc; simpa using this.symm⟩
  obtain ⟨x₀, hx₀⟩ := hf₀ b w₀
  have hx₀mem : x₀ ∈ eig𝔸 (S := S) χ' := by
    intro t
    apply sub_eq_zero.mp
    apply eq_zero_of_apply_f₀ b
    rw [Subalgebra.coe_sub, LinearMap.sub_apply, Subalgebra.coe_mul, Module.End.mul_apply, hx₀,
      Subalgebra.coe_smul, LinearMap.smul_apply, hx₀, (hmemW w₀).mp hw₀W t, sub_self]
  have hx₀ne : x₀ ≠ 0 := by
    intro h; apply hw₀; rw [← hx₀, h]; rfl
  refine ⟨x₀, hx₀mem, hx₀ne, fun y hy => ?_⟩
  have hyW : (y : Module.End ℂ (S2 M H)) (f₀ b) ∈ W := by
    rw [hmemW]
    intro a
    rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, hy a, Subalgebra.coe_smul, LinearMap.smul_apply]
  obtain ⟨c, hc⟩ := hline _ hyW
  refine ⟨c, ?_⟩
  apply sub_eq_zero.mp
  apply eq_zero_of_apply_f₀ b
  rw [Subalgebra.coe_sub, LinearMap.sub_apply, hc, Subalgebra.coe_smul, LinearMap.smul_apply, hx₀, sub_self]

include b hA in
private theorem finrank_eigenspace_eq_two (χ : ↥(A M H S) →ₐ[ℂ] ℂ) (χ' : ↥(𝔸 M H S) → ℂ)
    (hχ' : ∀ t : ↥(𝔸 M H S), χ' t = χ ⟨Ψ E t, hA ▸ Subalgebra.mem_map.mpr ⟨_, t.2, rfl⟩⟩)
    (x₀ : ↥(𝔸 M H S)) (hx₀ : x₀ ∈ eig𝔸 (S := S) χ') (hx₀ne : x₀ ≠ 0)
    (hline : ∀ y ∈ eig𝔸 (S := S) χ', ∃ c : ℂ, y = c • x₀) :
    Module.finrank ℂ ↥(⨅ a : ↥(A M H S), Module.End.eigenspace (a : Module.End ℂ (V M H)) (χ a)) = 2 := by
  set Eχ : Submodule ℂ (V M H) := ⨅ a : ↥(A M H S), Module.End.eigenspace (a : Module.End ℂ (V M H)) (χ a)
  have hmem : ∀ t : ↥(𝔸 M H S) × ↥(𝔸 M H S),
      κ E b t ∈ Eχ ↔ t.1 ∈ eig𝔸 (S := S) χ' ∧ t.2 ∈ eig𝔸 (S := S) χ' := by
    intro t
    simp only [Eχ, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    constructor
    · intro h
      have key : ∀ s : ↥(𝔸 M H S), (s * t.1, s * t.2) = (χ' s • t.1, χ' s • t.2) := by
        intro s
        have hs := h ⟨Ψ E s, hA ▸ Subalgebra.mem_map.mpr ⟨_, s.2, rfl⟩⟩
        change Ψ E s (κ E b t) = _ at hs
        rw [κ_apply, Ψ_apply_E, ← hχ'] at hs
        apply (κ_bijective E b).1
        rw [κ_apply, κ_apply]
        simp only [Subalgebra.coe_mul, Module.End.mul_apply, Subalgebra.coe_smul, LinearMap.smul_apply]
          at hs ⊢
        rw [← Prod.smul_mk, map_smul]
        exact hs
      exact ⟨fun s => (Prod.ext_iff.mp (key s)).1, fun s => (Prod.ext_iff.mp (key s)).2⟩
    · rintro ⟨h1, h2⟩ a
      obtain ⟨s, hs⟩ := exists_of_mem_A E hA a
      have has : a = ⟨Ψ E s, hA ▸ Subalgebra.mem_map.mpr ⟨_, s.2, rfl⟩⟩ := Subtype.ext hs
      rw [has, ← hχ']
      change Ψ E s (κ E b t) = χ' s • κ E b t
      rw [κ_apply, Ψ_apply_E]
      have e1 : (s : Module.End ℂ (S2 M H)) ((t.1 : Module.End ℂ (S2 M H)) (f₀ b)) =
          χ' s • (t.1 : Module.End ℂ (S2 M H)) (f₀ b) := by
        rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, h1 s, Subalgebra.coe_smul, LinearMap.smul_apply]
      have e2 : (s : Module.End ℂ (S2 M H)) ((t.2 : Module.End ℂ (S2 M H)) (f₀ b)) =
          χ' s • (t.2 : Module.End ℂ (S2 M H)) (f₀ b) := by
        rw [← Module.End.mul_apply, ← Subalgebra.coe_mul, h2 s, Subalgebra.coe_smul, LinearMap.smul_apply]
      rw [e1, e2, ← Prod.smul_mk, map_smul]
  have hxf : (x₀ : Module.End ℂ (S2 M H)) (f₀ b) ≠ 0 := fun h => hx₀ne (eq_zero_of_apply_f₀ b x₀ h)
  let φ : (ℂ × ℂ) →ₗ[ℂ] ↥Eχ :=
    { toFun := fun c => ⟨κ E b (c.1 • x₀, c.2 • x₀), (hmem _).mpr
        ⟨Submodule.smul_mem _ _ hx₀, Submodule.smul_mem _ _ hx₀⟩⟩
      map_add' := fun c d => by
        apply Subtype.ext
        change κ E b ((c.1 + d.1) • x₀, (c.2 + d.2) • x₀) =
          κ E b (c.1 • x₀, c.2 • x₀) + κ E b (d.1 • x₀, d.2 • x₀)
        rw [← map_add, Prod.mk_add_mk, ← add_smul, ← add_smul]
      map_smul' := fun r c => by
        apply Subtype.ext
        change κ E b ((r * c.1) • x₀, (r * c.2) • x₀) = r • κ E b (c.1 • x₀, c.2 • x₀)
        rw [← map_smul, Prod.smul_mk, smul_smul, smul_smul] }
  have hφ : Function.Bijective φ := by
    constructor
    · intro c d h
      have h' := congrArg (fun z : ↥Eχ => (z : V M H)) h
      change κ E b _ = κ E b _ at h'
      rw [κ_apply, κ_apply] at h'
      have h'' := E.injective h'
      simp only [Prod.mk.injEq, Subalgebra.coe_smul, LinearMap.smul_apply] at h''
      obtain ⟨ha, hb⟩ := h''
      have ha' : (c.1 - d.1) • (x₀ : Module.End ℂ (S2 M H)) (f₀ b) = 0 := by rw [sub_smul, ha, sub_self]
      have hb' : (c.2 - d.2) • (x₀ : Module.End ℂ (S2 M H)) (f₀ b) = 0 := by rw [sub_smul, hb, sub_self]
      rw [smul_eq_zero] at ha' hb'
      exact Prod.ext (sub_eq_zero.mp (ha'.resolve_right hxf)) (sub_eq_zero.mp (hb'.resolve_right hxf))
    · rintro ⟨v, hv⟩
      obtain ⟨t, rfl⟩ := (κ_bijective E b).2 v
      obtain ⟨h1, h2⟩ := (hmem t).mp hv
      obtain ⟨a, ha⟩ := hline t.1 h1
      obtain ⟨b', hb'⟩ := hline t.2 h2
      refine ⟨(a, b'), Subtype.ext ?_⟩
      change κ E b (a • x₀, b' • x₀) = κ E b t
      rw [← ha, ← hb']
  rw [← (LinearEquiv.ofBijective φ hφ).finrank_eq, Module.finrank_prod, Module.finrank_self]

end Main

private def mkE {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    (ES : (S2 M H × S2 M H) →ₗ[ℂ] CohCarrier.H1 M H ℂ) (hinj : Function.Injective ES)
    (hrange : LinearMap.range ES = parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) :
    (S2 M H × S2 M H) ≃ₗ[ℂ] V M H :=
  LinearEquiv.ofBijective (ES.codRestrict _ (fun fg => hrange ▸ LinearMap.mem_range_self ES fg))
    ⟨fun x y h => hinj (congrArg Subtype.val h), by
      rintro ⟨v, hv⟩
      rw [← hrange] at hv
      obtain ⟨fg, rfl⟩ := hv
      exact ⟨fg, rfl⟩⟩

private theorem coe_mkE {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    (ES : (S2 M H × S2 M H) →ₗ[ℂ] CohCarrier.H1 M H ℂ) (hinj : Function.Injective ES)
    (hrange : LinearMap.range ES = parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) (fg : S2 M H × S2 M H) :
    ((mkE ES hinj hrange fg : V M H) : CohCarrier.H1 M H ℂ) = ES fg := by
  rfl

private theorem main (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite) :
    Nonempty (Module.Basis (Fin 2) ↥(A M H S) (V M H)) ∧
    ∀ χ : ↥(A M H S) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(A M H S), Module.End.eigenspace (a : Module.End ℂ (V M H)) (χ a)) = 2 := by
  obtain ⟨J, ES, -, -, hinj, hrange, hT', hU', hD'⟩ := CohCarrier.exists_eichlerShimura_H1_gammaH M H
  have hEcoe := coe_mkE ES hinj hrange
  generalize hE : mkE ES hinj hrange = E at hEcoe
  have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f g : S2 M H),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      ((E (CuspForm.heckeTLinH 2 hℓ hℓM f, CuspForm.heckeTLinH 2 hℓ hℓM g) : V M H) : CohCarrier.H1 M H ℂ) =
        CohCarrier.heckeT M H ℓ ℂ ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ) := by
    intro ℓ hℓ hℓM f g; rw [hEcoe, hEcoe]; exact hT' ℓ hℓ hℓM f g
  have hU : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (f g : S2 M H),
      haveI : NeZero q := ⟨hq.ne_zero⟩
      ((E (CuspForm.heckeULinH 2 q f, CuspForm.heckeULinH 2 q g) : V M H) : CohCarrier.H1 M H ℂ) =
        CohCarrier.heckeT M H q ℂ ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ) := by
    intro q hq hqM f g; rw [hEcoe, hEcoe]; exact hU' q hq hqM f g
  have hD : ∀ (d : (ZMod M)ˣ) (f g : S2 M H),
      ((E (CuspForm.diamondLinH 2 d f, CuspForm.diamondLinH 2 d g) : V M H) : CohCarrier.H1 M H ℂ) =
        CohCarrier.diamondL M H ℂ d ((E (f, g) : V M H) : CohCarrier.H1 M H ℂ) := by
    intro d f g; rw [hEcoe, hEcoe]; exact hD' d f g
  obtain ⟨⟨b⟩, hone⟩ := CuspForm.nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one M H S hSfin

  obtain ⟨hA⟩ : PLift (A M H S = (𝔸 M H S).map (Ψ E)) := ⟨A_eq_map E hT hU hD⟩
  refine ⟨Nonempty.intro (basisA (S := S) E b hA), fun χ => ?_⟩
  let ι : ↥(𝔸 M H S) →ₐ[ℂ] ↥(A M H S) :=
    ((Ψ E).comp (𝔸 M H S).val).codRestrict (A M H S)
      (fun t => hA ▸ Subalgebra.mem_map.mpr ⟨_, t.2, rfl⟩)
  let χ' : ↥(𝔸 M H S) →ₐ[ℂ] ℂ := χ.comp ι
  have hχ' : ∀ t : ↥(𝔸 M H S), χ' t = χ ⟨Ψ E t, hA ▸ Subalgebra.mem_map.mpr ⟨_, t.2, rfl⟩⟩ :=
    fun t => rfl
  obtain ⟨x₀, hx₀, hx₀ne, hline⟩ := eig𝔸_line b χ' (hone χ')
  exact finrank_eigenspace_eq_two E b hA χ χ' hχ' x₀ hx₀ hx₀ne hline

end EichlerShimuraGammaH


theorem CohCarrier.nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite) :
    Nonempty (Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) |
            (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
            (∃ d : (ZMod M)ˣ, ∀ v,
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))})
      ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) ∧
    ∀ χ : ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) |
            (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
            (∃ d : (ZMod M)ˣ, ∀ v,
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))}) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) |
            (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
            (∃ d : (ZMod M)ˣ, ∀ v,
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))}),
        Module.End.eigenspace (a : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) (χ a)) = 2 := by
  exact _root_.EichlerShimuraGammaH.main M H S hSfin


end
