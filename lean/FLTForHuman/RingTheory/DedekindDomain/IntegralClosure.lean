/-
  Dedekind-domain supplement: the height-one places of an integral closure, and the
  base-change linear equivalences between an integral closure and its fraction field.

  Backported from the pin's `Definitions/Def_DedekindDomain_IntegralClosure.lean`
  (pinned `aa2d8b3`).  It supplies
  `IsDedekindDomain.HeightOneSpectrum.Extension` — the places of `B` above a height-one
  prime `v` of `A` — together with `Extension.finite`/`Extension.fintype` (the reason the
  type exists for the twisted-orbital program), the ramification-index identity
  `Ideal.sum_ramification_inertia_extensions`, the base-change `LinearEquivTensorProduct`
  family, and the instance `IsIntegralClosure.isLocalizedModule`.

  Substitutions against mathlib `v4.34.0`: none of the 22 pin declarations has a
  same-statement mathlib declaration, so all 22 are transcribed at the pin's name.  The
  underlying mathlib API is used throughout: `Ideal.ramificationIdx'`,
  `Ideal.IsDedekindDomain.ramificationIdx'_ne_zero`,
  `Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count`,
  `IsIntegralClosure.isLocalization`, `LocalizedModule.equivTensorProduct`,
  `IsLocalization.moduleTensorEquiv`/`moduleLid` and `LinearEquiv.extendScalarsOfIsLocalization`
  are all mathlib `v4.34.0`; only `IsLocalization.leftModuleTensorEquiv` comes from the
  already-landed `FLTForHuman/RingTheory/Localization/BaseChange.lean`.

  Statement-level and proof-level adjustments forced by mathlib `v4.34.0`:

  * `Ideal.inertiaDeg'` (pin `:147`) is deprecated in `v4.34.0` and would break the
    0-warning requirement, so the pin's `Ideal.sum_ramification_inertia_extensions` uses
    the replacement `Ideal.inertiaDeg`.  Its proof also uses the replacement
    `Ideal.sum_ramification_inertia_eq_finrank` for the pin's now-removed
    `Ideal.sum_ramification_inertia`, whose old home
    `Mathlib.NumberTheory.RamificationInertia.Basic` is a deprecated module whose content
    is not exported.
  * `Set.coe_setOf` is a deprecated alias for `Set.coe_ofPred`, used in `Extension.finite`.
-/
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Tower
import FLTForHuman.RingTheory.Localization.BaseChange

set_option autoImplicit false

section

namespace IsDedekindDomain.HeightOneSpectrum

section BaseChange

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsDedekindDomain B]
    [IsFractionRing B L]

variable (v : HeightOneSpectrum A)

variable {A} in

-- pin: Extension (Definitions/Def_DedekindDomain_IntegralClosure.lean:20)
def Extension (v : HeightOneSpectrum A) := {w : HeightOneSpectrum B // w.under A = v}

-- pin: mk_count_factors_map (Definitions/Def_DedekindDomain_IntegralClosure.lean:22)
lemma mk_count_factors_map
    (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (I : Ideal A) :
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.map (algebraMap A B) I)).factors =
    Ideal.ramificationIdx' (under A w).asIdeal w.asIdeal *
      (Associates.mk (under A w).asIdeal).count (Associates.mk I).factors := by
  classical
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Associates.mk_zero, Ideal.zero_eq_bot, Ideal.map_bot, ← Ideal.zero_eq_bot,
      Associates.mk_zero]
    simp [-under_asIdeal, Associates.count, Associates.factors_zero, w.associates_irreducible,
      associates_irreducible (under A w), Associates.bcount]
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp only [Ideal.map_top]
    simp only [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    rw [Associates.count_zero (associates_irreducible _),
      Associates.count_zero (associates_irreducible _), mul_zero]
  | h₃ I p hI hp IH =>
    simp only [Ideal.map_mul, ← Associates.mk_mul_mk]
    have hp_bot : p ≠ ⊥ := hp.ne_zero
    have hp_bot' := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hp_bot
    have hI_bot := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hI
    rw [Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot) (Associates.mk_ne_zero.mpr hI)
      (associates_irreducible _), Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot')
      (Associates.mk_ne_zero.mpr hI_bot) (associates_irreducible _)]
    simp only [IH, mul_add]
    congr 1
    by_cases hw : (w.under A).asIdeal = p
    · have : Irreducible (Associates.mk p) := Associates.irreducible_mk.mpr hp.irreducible
      rw [hw, Associates.factors_self this, Associates.count_some this]
      simp only [Multiset.nodup_singleton, Multiset.mem_singleton, Multiset.count_eq_one_of_mem,
        mul_one]
      rw [Ideal.count_associates_factors_eq hp_bot' w.2 w.3,
        Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp_bot' w.2 w.3]
    · have : (Associates.mk (under A w).asIdeal).count (Associates.mk p).factors = 0 :=
        Associates.count_eq_zero_of_ne (associates_irreducible _)
          (Associates.irreducible_mk.mpr hp.irreducible)
          (by rwa [ne_eq, Associates.mk_eq_mk_iff_associated, associated_iff_eq])
      rw [this, mul_zero, eq_comm]
      by_contra H
      rw [eq_comm, ← ne_eq, Associates.count_ne_zero_iff_dvd hp_bot' (irreducible w),
        Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at H
      apply hw (((Ideal.isPrime_of_prime hp).isMaximal hp_bot).eq_of_le
        (under A w).2.ne_top H).symm

-- pin: ramificationIdx_ne_zero (Definitions/Def_DedekindDomain_IntegralClosure.lean:69)
lemma ramificationIdx_ne_zero (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) :
    Ideal.ramificationIdx' (under A w).asIdeal w.asIdeal ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
    ((Ideal.map_eq_bot_iff_of_injective hAB).not.mpr (under A w).3) w.2 Ideal.map_comap_le

-- pin: intValuation_comap (Definitions/Def_DedekindDomain_IntegralClosure.lean:75)
lemma intValuation_comap (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (x : A) :
    (under A w).intValuation x ^
    (Ideal.ramificationIdx' (under A w).asIdeal w.asIdeal) =
    w.intValuation (algebraMap A B x) := by
  classical
  have h_ne_zero := ramificationIdx_ne_zero A B hAB w
  by_cases hx : x = 0
  · simpa [hx]
  simp only [intValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  change (ite _ _ _) ^ _ = ite _ _ _
  rw [map_eq_zero_iff _ hAB, ite_eq_right hx, ite_eq_right hx, ← Set.image_singleton, ← Ideal.map_span,
    mk_count_factors_map _ _ hAB]
  simp only [← WithZero.exp_nsmul, nsmul_eq_mul]
  rw [WithZero.exp_inj]
  push_cast
  ring

omit [IsIntegralClosure B A L] in

-- pin: valuation_comap (Definitions/Def_DedekindDomain_IntegralClosure.lean:92)
lemma valuation_comap (w : HeightOneSpectrum B) (x : K) :
    (under A w).valuation K x ^
      (Ideal.ramificationIdx' (under A w).asIdeal w.asIdeal) =
    w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp only [map_div₀, div_pow]
  rw [← IsScalarTower.algebraMap_apply A K L x, ← IsScalarTower.algebraMap_apply A K L y,
    IsScalarTower.algebraMap_apply A B L x, IsScalarTower.algebraMap_apply A B L y]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  rw [← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L),
    ← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L)]

include K L in
omit [IsDedekindDomain A] [IsIntegralClosure B A L]
    [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
-- pin: isTorsionFree (Definitions/Def_DedekindDomain_IntegralClosure.lean:103)
lemma isTorsionFree [IsDomain B] : Module.IsTorsionFree A B := by
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A K).mpr inferInstance
  infer_instance

include K L in
omit [IsIntegralClosure B A L] [IsFractionRing B L] in

-- pin: Extension.finite (Definitions/Def_DedekindDomain_IntegralClosure.lean:111)
theorem Extension.finite (v : HeightOneSpectrum A) : Finite (v.Extension B) := by
  have := isTorsionFree A K L B
  rw [Extension, ← Set.coe_ofPred]
  rw [@Set.finite_coe_iff]
  have := primesOver_finite v.asIdeal B
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) ?_ ?_
  · refine Set.Finite.subset this ?_
    simp only [Set.subset_def, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    rintro w rfl
    simp only [Ideal.primesOver, Set.mem_ofPred_eq, isPrime, true_and]
    constructor
    simp [Ideal.under_def, under]
  · intro x hx y hy hxy
    rwa [← @HeightOneSpectrum.ext_iff] at hxy

-- pin: Extension.fintype (Definitions/Def_DedekindDomain_IntegralClosure.lean:128)
@[reducible]
noncomputable def Extension.fintype : Fintype (Extension B v) :=
  have := Extension.finite A K L B v
  Fintype.ofFinite <| Extension B v

include K L in
omit [IsIntegralClosure B A L] [IsFractionRing B L] in
-- pin: preimage_comap_finite (Definitions/Def_DedekindDomain_IntegralClosure.lean:134)
theorem preimage_comap_finite (S : Set (HeightOneSpectrum A)) (hS : S.Finite) :
    ((under A : HeightOneSpectrum B → HeightOneSpectrum A) ⁻¹' S).Finite := by
  rw [← Set.biUnion_preimage_singleton (under A) S]
  exact Set.Finite.biUnion' hS <| fun v _ ↦ Extension.finite A K L B v

-- pin: preimageComapFinset (Definitions/Def_DedekindDomain_IntegralClosure.lean:139)
noncomputable def preimageComapFinset (S : Finset (HeightOneSpectrum A)) :
    Finset (HeightOneSpectrum B) :=
  Set.Finite.toFinset <| preimage_comap_finite A K L B S S.finite_toSet

omit [IsIntegralClosure B A L] in

-- pin: Ideal.sum_ramification_inertia_extensions (Definitions/Def_DedekindDomain_IntegralClosure.lean:145)
lemma _root_.Ideal.sum_ramification_inertia_extensions [Module.Finite A B] :
    letI := Extension.fintype A K L B v
    ∑ (w : Extension B v), Ideal.ramificationIdx' v.asIdeal w.val.asIdeal
      * (w.val.asIdeal).inertiaDeg A = Module.finrank K L := by
  have htf := isTorsionFree A K L B
  let hinst : Fintype (Extension B v) := Extension.fintype A K L B v
  rw [IsFractionRing.finrank_eq A K B L,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal B]
  refine Finset.sum_nbij (fun w : Extension B v =>
    (⟨w.val.asIdeal, w.val.isPrime,
      ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩⟩ : v.asIdeal.primesOver B)) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro a _ b _ h
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · intro b _
    exact ⟨⟨⟨b.val, b.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot b.val⟩,
      HeightOneSpectrum.ext (Ideal.over_def b.val v.asIdeal).symm⟩, Finset.mem_univ _,
      Subtype.ext rfl⟩
  · intro a _
    have hLies : a.val.asIdeal.LiesOver v.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal a.2).symm⟩
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal a.val.asIdeal v.ne_bot]

end BaseChange

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

open scoped TensorProduct

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]

-- pin: LinearEquivTensorProduct (Definitions/Def_DedekindDomain_IntegralClosure.lean:188)
noncomputable def LinearEquivTensorProduct :
    L ≃ₗ[K] K ⊗[A] B :=
  let f := LocalizedModule.equivTensorProduct (nonZeroDivisors A) B
  have := IsIntegralClosure.isLocalization A K L B
  have : IsLocalizedModule (nonZeroDivisors A) (IsScalarTower.toAlgHom A B L).toLinearMap :=
    inferInstance
  let g : LocalizedModule (nonZeroDivisors A) B ≃ₗ[A] L := @IsLocalizedModule.iso
      _ _ (nonZeroDivisors A) _ _ _ _ _ _ (IsScalarTower.toAlgHom A B L).toLinearMap this
  let h := TensorProduct.congr (Localization.algEquiv (nonZeroDivisors A) K) (LinearEquiv.refl A B)
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors A) K
    <| g.symm.trans (f.restrictScalars A) |>.trans h

-- pin: LinearEquivTensorProduct_symm_one_tmul (Definitions/Def_DedekindDomain_IntegralClosure.lean:200)
lemma LinearEquivTensorProduct_symm_one_tmul (b : B) :
    (LinearEquivTensorProduct A K L B).symm (1 ⊗ₜ b) =
    (algebraMap _ _ b) := by
  simp [LinearEquivTensorProduct]

-- pin: LinearEquivTensorProduct_symm_tmul (Definitions/Def_DedekindDomain_IntegralClosure.lean:208)
lemma LinearEquivTensorProduct_symm_tmul (k : K) (b : B) :
    (LinearEquivTensorProduct A K L B).symm (k ⊗ₜ b) =
    k • (algebraMap _ _ b) := by
  have : k ⊗ₜ b = k • (1 ⊗ₜ b : K ⊗[A] B) := by
    simp [TensorProduct.smul_tmul']
  rw [this, LinearEquiv.map_smul, LinearEquivTensorProduct_symm_one_tmul]

variable (M : Type*) [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower A K M]

-- pin: linearEquivTensorProductModule (Definitions/Def_DedekindDomain_IntegralClosure.lean:217)
noncomputable def linearEquivTensorProductModule : L ⊗[K] M ≃ₗ[A] B ⊗[A] M :=
  let f₁ : L ⊗[K] M ≃ₗ[A] L ⊗[A] M := IsLocalization.moduleTensorEquiv (nonZeroDivisors A) K L M
    |>.restrictScalars A
  let f₂ : L ≃ₗ[A] B ⊗[A] K := LinearEquivTensorProduct A K L B
    |>.restrictScalars A
    |>.trans (TensorProduct.comm A K B)
  let f₃ : L ⊗[A] M ≃ₗ[A] (B ⊗[A] K) ⊗[A] M := TensorProduct.congr f₂ (LinearEquiv.refl A M)
  let f₄ : (B ⊗[A] K) ⊗[A] M ≃ₗ[A] B ⊗[A] (K ⊗[A] M) :=
    TensorProduct.assoc A B K M
  let f₅ : B ⊗[A] (K ⊗[A] M) ≃ₗ[A] B ⊗[A] M := TensorProduct.congr (LinearEquiv.refl A B)
    (IsLocalization.moduleLid (nonZeroDivisors A) K M |>.restrictScalars A)
  f₁.trans f₃ |>.trans f₄ |>.trans f₅

-- pin: linearEquivTensorProductModuleLeft (Definitions/Def_DedekindDomain_IntegralClosure.lean:230)
noncomputable def linearEquivTensorProductModuleLeft : L ⊗[K] M ≃ₗ[B] B ⊗[A] M :=
  let f₁ : L ⊗[K] M ≃ₗ[B] L ⊗[A] M :=
    IsLocalization.leftModuleTensorEquiv B (nonZeroDivisors A) K L M
  let f₂ : B ⊗[A] K ≃ₗ[B] L := {
    __ := LinearEquivTensorProduct A K L B
        |>.restrictScalars A
        |>.trans (TensorProduct.comm A K B) |>.symm
    map_smul' b x := by
      induction x with
      | tmul l m => simp [LinearEquivTensorProduct_symm_tmul, Algebra.smul_def]; ring
      | add => simp_all
    }
  let f₃ : (B ⊗[A] K) ⊗[A] M ≃ₗ[B] L ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.congr f₂ (LinearEquiv.refl A M)
  let f₄ : (B ⊗[A] K) ⊗[A] M ≃ₗ[B] B ⊗[A] (K ⊗[A] M) :=
    TensorProduct.AlgebraTensorModule.assoc _ A B _ K M
  let f₅ : B ⊗[A] (K ⊗[A] M) ≃ₗ[B] B ⊗[A] M :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (IsLocalization.moduleLid (nonZeroDivisors A) K M |>.restrictScalars A)
  f₁.trans f₃.symm |>.trans f₄ |>.trans f₅

-- pin: linearEquivTensorProductModuleLeft_restrictScalars (Definitions/Def_DedekindDomain_IntegralClosure.lean:252)
lemma linearEquivTensorProductModuleLeft_restrictScalars :
    (linearEquivTensorProductModuleLeft A K L B M).restrictScalars A =
      linearEquivTensorProductModule A K L B M := by
  rfl

-- pin: linearEquivTensorProductModule_symm_tmul (Definitions/Def_DedekindDomain_IntegralClosure.lean:257)
lemma linearEquivTensorProductModule_symm_tmul (b : B) (m : M) :
    (linearEquivTensorProductModule A K L B M).symm (b ⊗ₜ m) = (algebraMap B L b) ⊗ₜ m := by
  simp [linearEquivTensorProductModule, LinearEquivTensorProduct_symm_one_tmul]

-- pin: linearEquivTensorProductModule_tmul (Definitions/Def_DedekindDomain_IntegralClosure.lean:261)
lemma linearEquivTensorProductModule_tmul (b : B) (m : M) :
    (linearEquivTensorProductModule A K L B M) ((algebraMap B L b) ⊗ₜ m) = b ⊗ₜ m := by
  rw [← LinearEquiv.eq_symm_apply, linearEquivTensorProductModule_symm_tmul]

-- pin: linearEquivTensorProductModuleLeft_symm_tmul (Definitions/Def_DedekindDomain_IntegralClosure.lean:265)
lemma linearEquivTensorProductModuleLeft_symm_tmul (b : B) (m : M) :
    (linearEquivTensorProductModuleLeft A K L B M).symm (b ⊗ₜ m) = (algebraMap B L b) ⊗ₜ m := by
  simp [linearEquivTensorProductModuleLeft, LinearEquivTensorProduct_symm_one_tmul]

-- pin: linearEquivTensorProductModuleLeft_tmul (Definitions/Def_DedekindDomain_IntegralClosure.lean:269)
lemma linearEquivTensorProductModuleLeft_tmul (b : B) (m : M) :
    (linearEquivTensorProductModuleLeft A K L B M) ((algebraMap B L b) ⊗ₜ m) = b ⊗ₜ m := by
  rw [← LinearEquiv.eq_symm_apply, linearEquivTensorProductModuleLeft_symm_tmul]

end IsDedekindDomain

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]

include K in
-- pin: IsIntegralClosure.isLocalizedModule (Definitions/Def_DedekindDomain_IntegralClosure.lean:281)
lemma _root_.IsIntegralClosure.isLocalizedModule : IsLocalizedModule (nonZeroDivisors A)
    ((Algebra.linearMap B L).restrictScalars A) := by
  have hlocal := IsIntegralClosure.isLocalization A K L B
  rw [← isLocalizedModule_iff_isLocalization'] at hlocal
  exact {
    map_units x := by
      obtain ⟨x, hx⟩ := x
      have h := hlocal.map_units ⟨_, x, hx, rfl⟩
      rw [Module.End.isUnit_iff] at h ⊢
      convert h using 1
      ext l
      simp [Module.algebraMap_end_apply, algebraMap_smul]
    surj y := by
      obtain ⟨⟨b, _, s, hs, rfl⟩, hx⟩ := (hlocal.surj) y
      exact ⟨(b, ⟨s, hs⟩), by simpa [Submonoid.smul_def] using hx⟩
    exists_of_eq {x₁ x₂} e := by
      obtain ⟨⟨_, c, hc, rfl⟩, he⟩ := hlocal.exists_of_eq e
      use ⟨c, hc⟩
      simpa only [Submonoid.smul_def, smul_eq_mul, Algebra.smul_def] using he
  }
