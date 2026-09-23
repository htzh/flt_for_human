/-
The along-map transport layer and `Pic0` descent, after FLT's sixteen
`P2M/Sol/S_AlgebraicCurve_{Place,Divisor,Pic0,finiteAlong,separableAlong}_*` files,
plus the shared prelude the pin copies into `bifiber`, `exchange` and
`divisor_exchange` (as `BifibreDev.*`, `BifibreW2.*`, `BifibreWEX.*`;
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean>).

The prelude is public and written **once**; T5, T6 and T7 import it rather than
restating it (`TOPIC-t4-transport.md` §1). `algebraAlong` stays an `abbrev`:
`restrictAlong_restrictAlong` is `rfl`-level, and it is the topic's canary.
-/
import FLTForHuman.AlgebraicCurve.WeilExchange.GaloisRamification
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain AlgebraicCurve

namespace AlgebraicCurve

/-! ## The shared prelude (the pin's `BifibreDev` block) -/

namespace BifibreDev

section AlongBridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem inertiaDegAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = w.inertiaDegAlong φ' hφ' := by
  subst h; rfl

variable [Algebra F F'] [IsScalarTower K F F']

theorem isIntegral_toAlgHom [Algebra.IsIntegral F F'] :
    (IsScalarTower.toAlgHom K F F').toRingHom.IsIntegral :=
  fun x => Algebra.IsIntegral.isIntegral (R := F) x

end AlongBridge

section Tower

variable {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]

theorem toAlgHom_comp_toAlgHom :
    (IsScalarTower.toAlgHom K E M).comp (IsScalarTower.toAlgHom K F E) =
      IsScalarTower.toAlgHom K F M :=
  AlgHom.ext fun x => (IsScalarTower.algebraMap_apply F E M x).symm

theorem restrict_restrict [Algebra.IsIntegral F E] [Algebra.IsIntegral E M]
    [Algebra.IsIntegral F M] (W : Place K M) : (W.restrict E).restrict F = W.restrict F :=
  Place.ext (by
    simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])

end Tower

end BifibreDev



/-! ## The sixteen transport nodes -/

namespace Place

theorem restrictAlong_restrictAlong {K F F' F'' : Type*} [Field K] [Field F] [Field F']
    [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F')
    (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') :
    (W.restrictAlong χ hχ).restrictAlong φ hφ = W.restrictAlong (χ.comp φ) hχφ :=
  Place.ext (SetLike.ext fun _ => Iff.rfl)

theorem ramificationIndexAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F']
    [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F')
    (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') :
    Place.ramificationIndexAlong (χ.comp φ) W =
      Place.ramificationIndexAlong χ W * Place.ramificationIndexAlong φ (W.restrictAlong χ hχ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring
  have hπord : (W.restrictAlong (χ.comp φ) hχφ).ord
      ((π : (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring) : F) = 1 :=
    (W.restrictAlong (χ.comp φ) hχφ).ord_coe_irreducible hπ
  set f : F := ((π : (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring) : F) with hf
  have h1 : W.ord ((χ.comp φ) f) = (Place.ramificationIndexAlong (χ.comp φ) W : ℤ) := by
    rw [W.ord_restrictAlong (χ.comp φ) hχφ, hπord, mul_one]
  have h2 : W.ord ((χ.comp φ) f)
      = (Place.ramificationIndexAlong χ W : ℤ)
          * (Place.ramificationIndexAlong φ (W.restrictAlong χ hχ) : ℤ) := by
    rw [AlgHom.comp_apply, W.ord_restrictAlong χ hχ, (W.restrictAlong χ hχ).ord_restrictAlong φ hφ,
      AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ, hπord, mul_one]
  exact_mod_cast h1.symm.trans h2

theorem inertiaDegAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F']
    [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F')
    (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') :
    W.inertiaDegAlong (χ.comp φ) hχφ =
      W.inertiaDegAlong χ hχ * (W.restrictAlong χ hχ).inertiaDegAlong φ hφ := by
  letI iχ : Algebra F' F'' := algebraAlong χ
  haveI := isScalarTower_along χ
  haveI := isIntegral_along χ hχ
  letI iφ : Algebra F F' := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ

  let w : Place K F' := W.restrict F'
  let v : Place K F := w.restrict F

  letI iχφ : Algebra F F'' := algebraAlong (χ.comp φ)
  haveI := isScalarTower_along (χ.comp φ)
  haveI := isIntegral_along (χ.comp φ) hχφ
  letI : Algebra v.ResidueField W.ResidueField := (Place.restrictResidueMap F W).toAlgebra
  haveI : IsScalarTower v.ResidueField w.ResidueField W.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    show Place.restrictResidueMap F W (IsLocalRing.residue _ a)
      = Place.restrictResidueMap F' W (Place.restrictResidueMap F w (IsLocalRing.residue _ a))
    rw [Place.restrictResidueMap_residue W a, Place.restrictResidueMap_residue w a,
      Place.restrictResidueMap_residue W (Place.restrictInclusion F w a)]
    exact congrArg _ (Subtype.ext rfl)
  show Module.finrank v.ResidueField W.ResidueField
    = Module.finrank w.ResidueField W.ResidueField * Module.finrank v.ResidueField w.ResidueField
  rw [mul_comm]
  exact (Module.finrank_mul_finrank v.ResidueField w.ResidueField W.ResidueField).symm

end Place

namespace Divisor

theorem pushforwardAlong_pushforwardAlong {K F F' F'' : Type*} [Field K] [Field F] [Field F']
    [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F')
    (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F'') :
    Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ D) =
      Divisor.pushforwardAlong (χ.comp φ) hχφ D := by
  have key : (Divisor.pushforwardAlong φ hφ).comp (Divisor.pushforwardAlong χ hχ)
      = Divisor.pushforwardAlong (χ.comp φ) hχφ := by
    refine Finsupp.addHom_ext fun W n => ?_
    show Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ (Finsupp.single W n))
        = Divisor.pushforwardAlong (χ.comp φ) hχφ (Finsupp.single W n)
    rw [Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single,
      AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ,
      AlgebraicCurve.Place.inertiaDegAlong_comp φ χ hφ hχ hχφ W]
    refine congrArg (Finsupp.single _) ?_
    push_cast
    ring
  exact DFunLike.congr_fun key D

theorem pullbackAlong_pullbackAlong {K F F' F'' : Type*} [Field K] [Field F] [Field F']
    [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F')
    (χ : F' →ₐ[K] F'') [HasPrincipalDivisors K F'] [HasPrincipalDivisors K F'']
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong χ hχ (Divisor.pullbackAlong φ hφ D) =
      Divisor.pullbackAlong (χ.comp φ) hχφ D := by
  ext W
  rw [Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply,
    AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ,
    AlgebraicCurve.Place.ramificationIndexAlong_comp φ χ hφ hχ hχφ]
  push_cast
  ring

theorem correspondence_congr {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F]
    [Algebra K F₁] [HasPrincipalDivisors K F₁] {φ ψ φ' ψ' : F →ₐ[K] F₁} (hφeq : φ = φ')
    (hψeq : ψ = ψ') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.correspondence φ ψ hφ hψ D = Divisor.correspondence φ' ψ' hφ' hψ' D := by
  subst hφeq
  subst hψeq
  rfl

theorem correspondence_correspondence {K F F₁ F₂ Z : Type*} [Field K] [Field F] [Field F₁]
    [Field F₂] [Field Z] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z]
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] [HasPrincipalDivisors K Z]
    (φ ψ : F →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂) (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral)
    (hψ' : ψ'.toRingHom.IsIntegral) (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral)
    (huφ' : (u'.comp φ').toRingHom.IsIntegral) (huψ : (u.comp ψ).toRingHom.IsIntegral)
    (hex : ∀ D : Divisor K F₂,
      Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D) =
        Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D)) (D : Divisor K F) :
    Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) =
      Divisor.correspondence (u'.comp φ') (u.comp ψ) huφ' huψ D := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply, Divisor.correspondence_apply,
    hex (Divisor.pullbackAlong φ' hφ' D),
    AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong ψ u hψ hu huψ,
    AlgebraicCurve.Divisor.pullbackAlong_pullbackAlong φ' u' hφ' hu' huφ']

end Divisor

namespace Pic0

theorem correspondence_correspondence_comm {K F F₁ F₂ : Type*} [Field K] [Field F] [Field F₁]
    [Field F₂] [Algebra K F] [Algebra K F₁] [Algebra K F₂]
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] (φ ψ : F →ₐ[K] F₁)
    (φ' ψ' : F →ₐ[K] F₂) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) (hFI' : FundamentalIdentityAlong K φ' hφ')
    (hfin' : FiniteAlong K ψ') (hN' : NormFormulaAlong K ψ' hfin')
    (hcomm : ∀ D : Divisor K F,
      Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) =
        Divisor.correspondence φ' ψ' hφ' hψ' (Divisor.correspondence φ ψ hφ hψ D))
    (x : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN
        (Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' x) =
      Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN'
        (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.correspondence_mk, Pic0.correspondence_mk, Pic0.correspondence_mk, Pic0.correspondence_mk]
  exact congrArg Pic0.mk (Subtype.ext (hcomm (D : Divisor K F)))

theorem mk_eq_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F) := by
  rw [show Pic0.mk D = QuotientAddGroup.mk D from rfl, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf]
  exact Divisor.mem_principal

theorem zsmul_mk {K F : Type*} [Field K] [Field F] [Algebra K F] (m : ℤ)
    (D : Divisor.degZero (K := K) (F := F)) : m • Pic0.mk D = Pic0.mk (m • D) :=
  (map_zsmul (QuotientAddGroup.mk' _) m D).symm

theorem zsmul_mk_eq_zero_of_isPrincipal {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor.degZero (K := K) (F := F)) (m : ℤ)
    (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := by
  rw [AlgebraicCurve.Pic0.zsmul_mk, AlgebraicCurve.Pic0.mk_eq_zero_iff]
  exact hD

theorem nsmul_mk_eq_zero_of_isPrincipal {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor.degZero (K := K) (F := F)) (m : ℕ)
    (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := by
  have h := AlgebraicCurve.Pic0.zsmul_mk_eq_zero_of_isPrincipal D (m : ℤ) (by rwa [natCast_zsmul])
  rwa [natCast_zsmul] at h

theorem addOrderOf_mk_dvd_of_isPrincipal {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor.degZero (K := K) (F := F)) (m : ℕ)
    (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : addOrderOf (Pic0.mk D) ∣ m :=
  addOrderOf_dvd_of_nsmul_eq_zero (AlgebraicCurve.Pic0.nsmul_mk_eq_zero_of_isPrincipal D m hD)

end Pic0

theorem finiteAlong_comp {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : FiniteAlong K φ) (hχ : FiniteAlong K χ) : FiniteAlong K (χ.comp φ) := by
  letI := algebraAlong φ
  letI := algebraAlong χ
  letI := algebraAlong (χ.comp φ)
  haveI : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite F F' := hφ
  haveI : Module.Finite F' F'' := hχ
  exact Module.Finite.trans F' F''

theorem finiteAlong_of_surjective {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (φ : F →ₐ[K] F') (hφ : Function.Surjective φ) : FiniteAlong K φ := by
  letI := algebraAlong φ
  exact Module.Finite.of_surjective (Algebra.linearMap F F') hφ

theorem separableAlong_of_charZero {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F]
    [Algebra K F₁] [CharZero F] (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral) :
    SeparableAlong K φ := by
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  exact Algebra.IsSeparable.of_integral F F₁

namespace Place

variable {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]

theorem ramificationIndex_eq_mul_ramificationIndex_restrict
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] (W : Place K M) :
    W.ramificationIndex F = W.ramificationIndex E * (W.restrict E).ramificationIndex F := by
  have h := ramificationIndexAlong_comp (IsScalarTower.toAlgHom K F E)
    (IsScalarTower.toAlgHom K E M) BifibreDev.isIntegral_toAlgHom BifibreDev.isIntegral_toAlgHom
    (by rw [BifibreDev.toAlgHom_comp_toAlgHom]
        haveI : Algebra.IsIntegral F M := Algebra.IsIntegral.trans E
        exact BifibreDev.isIntegral_toAlgHom) W
  rw [BifibreDev.toAlgHom_comp_toAlgHom] at h
  exact h

theorem inertiaDeg_eq_mul_inertiaDeg_restrict
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] [Algebra.IsIntegral F M] (W : Place K M) :
    W.inertiaDeg F = W.inertiaDeg E * (W.restrict E).inertiaDeg F := by
  have h := inertiaDegAlong_comp (IsScalarTower.toAlgHom K F E)
    (IsScalarTower.toAlgHom K E M) BifibreDev.isIntegral_toAlgHom BifibreDev.isIntegral_toAlgHom
    (by rw [BifibreDev.toAlgHom_comp_toAlgHom]; exact BifibreDev.isIntegral_toAlgHom) W
  rw [BifibreDev.inertiaDegAlong_congr BifibreDev.toAlgHom_comp_toAlgHom _
    BifibreDev.isIntegral_toAlgHom] at h
  exact h

end Place

end AlgebraicCurve
