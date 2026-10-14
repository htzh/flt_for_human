/-
  Fujisaki compactness — proof engine (tier 3, unlisted).

  Ported from the pinned FLT repository
  `anthropics/fermats-last-theorem@aa2d8b3`,
  `P2M/Sol/S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean` (3,683 lines / 285 declarations), transcribed
  whole except its final `theorem solution` and the `M4aLocalCFT.ValuationOrd`
  prelude (pin lines 85–284), which is already homed in
  `NumberField/TateGlobal/Ideles.lean`.  The 364 declarations already in the
  port are imported, never re-transcribed.

  The only visibility change from the pin: the two engine kernels
  `M4aLocalCFT.FujisakiR1.exists_isCompact_impl` and
  `M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl` are public,
  because the tier-1 facade `NumberField/TateGlobalCompactness.lean` calls them;
  every other declaration keeps the pin's `private`.  See
  `lean/topics/numberTheory/tateGlobal/WORKORDER-T3-fujisaki-compactness.md`.
-/
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Algebra.Module.ZLattice.Basic
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Coordinates
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Ideles
import FLTForHuman.NumberTheory.NumberField.TateGlobal.FiniteSlab
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ArchSlab
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ArchMulHaar
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ValuedOrdBridge
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ZetaIntegrand
import FLTForHuman.NumberTheory.NumberField.TateGlobal.DistribHaarChar
import FLTForHuman.NumberTheory.NumberField.TateGlobal.LocalZetaUnramified
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ReferenceMeasure
import FLTForHuman.NumberTheory.NumberField.TateGlobal.MulHaar
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IntLocalIntegrability
import FLTForHuman.NumberTheory.NumberField.TateGlobal.HMajorant
import FLTForHuman.NumberTheory.NumberField.Completion.Finite
import FLTForHuman.NumberTheory.M4aHerbrand.IdeleClassVocab
import FLTForHuman.NumberTheory.AdelicModulus

set_option autoImplicit false

noncomputable section

/-! ### section Fold_TateSDecomp2 -/

open NumberField NumberField.TateGlobal NumberField.InfinitePlace IsDedekindDomain
open scoped NNReal
namespace NumberField.TateGlobal
variable {F : Type} [Field F] [NumberField F]

-- pin: ordAt_one (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:334)
private theorem ordAt_one (v : HeightOneSpectrum (𝓞 F)) : ordAt v (1 : (v.adicCompletion F)ˣ) = 0 := by
  simp [ordAt]

end NumberField.TateGlobal

/-! ### section Fold_IdeleIdealClass -/

open NumberField NumberField.TateGlobal IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors
namespace NumberField.TateGlobal
variable {F : Type} [Field F] [NumberField F]

-- pin: fracIdealAtUnit (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1059)
private def fracIdealAtUnit (v : HeightOneSpectrum (𝓞 F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) (coeIdeal_ne_zero.mpr v.ne_bot)

-- pin: fracIdealAtUnit_val (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1062)
private theorem fracIdealAtUnit_val (v : HeightOneSpectrum (𝓞 F)) :
    (fracIdealAtUnit (F := F) v : FractionalIdeal (𝓞 F)⁰ F) = v.asIdeal := rfl

-- pin: fracIdealProd (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1065)
private def fracIdealProd (exps : HeightOneSpectrum (𝓞 F) →₀ ℤ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  exps.prod fun v k => fracIdealAtUnit v ^ k

-- pin: fracIdealProd_zero (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1068)
private theorem fracIdealProd_zero : fracIdealProd (F := F) 0 = 1 := by
  simp [fracIdealProd, Finsupp.prod_zero_index]

-- pin: fracIdealProd_add (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1071)
private theorem fracIdealProd_add (e₁ e₂ : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    fracIdealProd (F := F) (e₁ + e₂) = fracIdealProd e₁ * fracIdealProd e₂ := by
  simp only [fracIdealProd]
  exact Finsupp.prod_add_index' (fun v => zpow_zero _) (fun v k₁ k₂ => zpow_add _ k₁ k₂)

-- pin: fracIdealProdHom (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1076)
private def fracIdealProdHom : Multiplicative (HeightOneSpectrum (𝓞 F) →₀ ℤ) →* (FractionalIdeal (𝓞 F)⁰ F)ˣ where
  toFun e := fracIdealProd e.toAdd
  map_one' := fracIdealProd_zero
  map_mul' e₁ e₂ := fracIdealProd_add e₁.toAdd e₂.toAdd

-- pin: fracIdealProd_val (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1081)
private theorem fracIdealProd_val (exps : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    (fracIdealProd (F := F) exps : FractionalIdeal (𝓞 F)⁰ F)
      = exps.prod fun v k => (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ k := by
  simp only [fracIdealProd, Finsupp.prod]
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Units.val_zpow_eq_zpow_val, fracIdealAtUnit_val]

-- pin: count_fracIdealProd (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1089)
private theorem count_fracIdealProd (v : HeightOneSpectrum (𝓞 F)) (exps : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    count F v (fracIdealProd (F := F) exps : FractionalIdeal (𝓞 F)⁰ F) = exps v := by
  rw [fracIdealProd_val]
  exact count_finsuppProd F v exps

-- pin: fracIdealProd_eq_one_iff (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1094)
private theorem fracIdealProd_eq_one_iff (exps : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    fracIdealProd (F := F) exps = 1 ↔ exps = 0 := by
  constructor
  · intro h
    refine Finsupp.ext fun v => ?_
    have := count_fracIdealProd (F := F) v exps
    rw [h, Units.val_one, count_one] at this
    exact this.symm
  · intro h; rw [h]; exact fracIdealProd_zero

-- pin: expVec_one (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1104)
private theorem expVec_one : expVec (F := F) ∅ 1 = 0 := by
  refine Finsupp.ext fun v => ?_
  rw [expVec_apply_of_not_mem 1 (Finset.notMem_empty v), map_one, ordAt_one]
  rfl

-- pin: expVec_mul (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1109)
private theorem expVec_mul (x y : (AdeleRing (𝓞 F) F)ˣ) :
    expVec (F := F) ∅ (x * y) = expVec ∅ x + expVec ∅ y := by
  refine Finsupp.ext fun v => ?_
  simp only [Finsupp.add_apply]
  rw [expVec_apply_of_not_mem _ (Finset.notMem_empty v),
    expVec_apply_of_not_mem _ (Finset.notMem_empty v),
    expVec_apply_of_not_mem _ (Finset.notMem_empty v), map_mul, ordAt_mul]

-- pin: expVecHom (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1117)
private def expVecHom : (AdeleRing (𝓞 F) F)ˣ →* Multiplicative (HeightOneSpectrum (𝓞 F) →₀ ℤ) where
  toFun x := Multiplicative.ofAdd (expVec ∅ x)
  map_one' := by rw [expVec_one]; rfl
  map_mul' x y := by rw [expVec_mul]; rfl

-- pin: expVec_eq_zero_iff (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1122)
private theorem expVec_eq_zero_iff (x : (AdeleRing (𝓞 F) F)ˣ) :
    expVec (F := F) ∅ x = 0 ↔ x ∈ unitsOutside ∅ := by
  rw [mem_unitsOutside_iff]
  constructor
  · intro h
    refine ⟨fun v _ => ?_, fun v _ => ?_⟩
    · have h1 : ordAt v (unitAtHom v x) = 0 := by
        rw [← expVec_apply_of_not_mem x (Finset.notMem_empty v), h]; rfl
      exact ((ordAt_eq_zero_iff v _).mp h1).1
    · have h1 : ordAt v (unitAtHom v x) = 0 := by
        rw [← expVec_apply_of_not_mem x (Finset.notMem_empty v), h]; rfl
      have h2 := ((ordAt_eq_zero_iff v _).mp h1).2
      rwa [← map_inv] at h2
  · intro ⟨h1, h2⟩
    refine Finsupp.ext fun v => ?_
    rw [expVec_apply_of_not_mem x (Finset.notMem_empty v), Finsupp.zero_apply,
      ordAt_eq_zero_iff]
    refine ⟨h1 v (Finset.notMem_empty v), ?_⟩
    have := h2 v (Finset.notMem_empty v)
    rwa [← map_inv]

-- pin: ideleIdeal (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1143)
private def ideleIdeal : (AdeleRing (𝓞 F) F)ˣ →* (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  fracIdealProdHom.comp expVecHom

-- pin: ideleIdeal_apply (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1146)
private theorem ideleIdeal_apply (x : (AdeleRing (𝓞 F) F)ˣ) :
    ideleIdeal x = fracIdealProd (expVec ∅ x) := rfl

-- pin: count_ideleIdeal (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1149)
private theorem count_ideleIdeal (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ) :
    count F v (ideleIdeal x : FractionalIdeal (𝓞 F)⁰ F) = ordAt v (unitAtHom v x) := by
  rw [ideleIdeal_apply, count_fracIdealProd, expVec_apply_of_not_mem x (Finset.notMem_empty v)]

-- pin: ideleIdeal_eq_one_iff (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1153)
private theorem ideleIdeal_eq_one_iff (x : (AdeleRing (𝓞 F) F)ˣ) :
    ideleIdeal x = 1 ↔ x ∈ unitsOutside ∅ := by
  rw [ideleIdeal_apply, fracIdealProd_eq_one_iff, expVec_eq_zero_iff]

-- pin: ker_ideleIdeal (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1157)
private theorem ker_ideleIdeal : (ideleIdeal (F := F)).ker = unitsOutside ∅ := by
  ext x
  exact ideleIdeal_eq_one_iff x

-- pin: ideleClass (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1161)
private def ideleClass : (AdeleRing (𝓞 F) F)ˣ →* ClassGroup (𝓞 F) :=
  (ClassGroup.mk F).comp ideleIdeal

-- pin: ideleIdeal_unifPow (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1164)
private theorem ideleIdeal_unifPow (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ideleIdeal (unifPow ϖ k) = fracIdealProd k := by
  rw [ideleIdeal_apply]
  congr 1
  refine Finsupp.ext fun v => ?_
  rw [expVec_apply_of_not_mem _ (Finset.notMem_empty v), ordAt_unitAtHom_unifPow]

-- pin: countFinsupp (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1171)
private def countFinsupp (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : HeightOneSpectrum (𝓞 F) →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => count F v (I : FractionalIdeal (𝓞 F)⁰ F))
    ((finite_factors (I : FractionalIdeal (𝓞 F)⁰ F)).subset fun v hv => by
      simp only [Function.mem_support, ne_eq] at hv ⊢
      exact hv)

-- pin: countFinsupp_apply (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1177)
private theorem countFinsupp_apply (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    countFinsupp I v = count F v (I : FractionalIdeal (𝓞 F)⁰ F) := by
  simp [countFinsupp, Finsupp.ofSupportFinite_coe]

-- pin: fracIdealProd_countFinsupp (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1181)
private theorem fracIdealProd_countFinsupp (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    fracIdealProd (countFinsupp I) = I := by
  refine Units.ext ?_
  rw [fracIdealProd_val]
  have hI : (I : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := I.ne_zero
  conv_rhs => rw [← finprod_heightOneSpectrum_factorization' (K := F) hI]
  rw [Finsupp.prod]
  rw [finprod_eq_finsetProd_of_mulSupport_subset
    (s := (countFinsupp I).support)]
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [countFinsupp_apply]
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, countFinsupp_apply]
    intro h
    rw [h, zpow_zero] at hv
    exact hv rfl

-- pin: ideleIdeal_surjective (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1199)
private theorem ideleIdeal_surjective (ϖ : Uniformizers F) : Function.Surjective (ideleIdeal (F := F)) :=
  fun I => ⟨unifPow ϖ (countFinsupp I), (ideleIdeal_unifPow ϖ _).trans (fracIdealProd_countFinsupp I)⟩

-- pin: ideleClass_surjective (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1202)
private theorem ideleClass_surjective (ϖ : Uniformizers F) : Function.Surjective (ideleClass (F := F)) := by
  have h1 : Function.Surjective
      (Units.map (canonicalEquiv (𝓞 F)⁰ F (FractionRing (𝓞 F))).toMonoidHom) :=
    (Units.mapEquiv (canonicalEquiv (𝓞 F)⁰ F (FractionRing (𝓞 F))).toMulEquiv).surjective
  exact (QuotientGroup.mk'_surjective _).comp (h1.comp (ideleIdeal_surjective ϖ))

-- pin: ideleClass_surjective' (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1225)
private theorem ideleClass_surjective' : Function.Surjective (ideleClass (F := F)) :=
  ideleClass_surjective someUniformizers

end NumberField.TateGlobal

/-! ### section Fold_IdeleIdealClass2 -/

open NumberField NumberField.TateGlobal IsDedekindDomain FractionalIdeal WithZero
open scoped nonZeroDivisors
namespace NumberField.TateGlobal
variable {F : Type} [Field F] [NumberField F]

-- pin: unitAtHom_principal_val (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1256)
private theorem unitAtHom_principal_val (v : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    ((unitAtHom v (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α) :
      (v.adicCompletion F)ˣ) : v.adicCompletion F) = ((α : F) : v.adicCompletion F) := by
  rw [unitAtHom_val]
  exact AdeleRing.algebraMap_snd_apply (𝓞 F) F (α : F) v

-- pin: valuation_eq_exp_neg_count_spanSingleton (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1262)
private theorem valuation_eq_exp_neg_count_spanSingleton (v : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    v.valuation F (α : F) = WithZero.exp (-(count F v (spanSingleton (𝓞 F)⁰ (α : F)))) := by
  classical
  obtain ⟨n, d, hd, hmk⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (α : F)
  have hα : (α : F) ≠ 0 := α.ne_zero
  have hn : n ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hmk
    exact hα hmk.symm
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hI : (spanSingleton (𝓞 F)⁰ (α : F) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rwa [ne_eq, spanSingleton_eq_zero_iff]
  have h_aJ : (spanSingleton (𝓞 F)⁰ (α : F) : FractionalIdeal (𝓞 F)⁰ F)
      = spanSingleton (𝓞 F)⁰ ((algebraMap (𝓞 F) F) d)⁻¹
        * ↑(Ideal.span {n} : Ideal (𝓞 F)) := by
    rw [coeIdeal_span_singleton, ← hmk, div_eq_inv_mul, ← spanSingleton_mul_spanSingleton]
  rw [count_well_defined (K := F) v hI h_aJ]
  have hmk' : IsLocalization.mk' F n (⟨d, hd⟩ : (𝓞 F)⁰) = (α : F) := by
    rw [IsFractionRing.mk'_eq_div]; exact hmk
  rw [← hmk', HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg hd0, ← WithZero.exp_sub, WithZero.exp_inj, neg_sub, neg_sub_neg]

-- pin: ordAt_unitAtHom_principal (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1284)
private theorem ordAt_unitAtHom_principal (v : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    ordAt v (unitAtHom v (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α))
      = count F v (spanSingleton (𝓞 F)⁰ (α : F)) := by
  rw [← neg_inj, ← WithZero.exp_inj]
  rw [show ordAt v (unitAtHom v _)
        = IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)
          (Additive.ofMul (unitAtHom v (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α)))
      from rfl]
  rw [← ValuedOrdBridge.valued_coe_units_eq_exp_neg_ord]
  rw [unitAtHom_principal_val, v.valuedAdicCompletion_eq_valuation' (α : F)]
  exact valuation_eq_exp_neg_count_spanSingleton v α

-- pin: fracIdealUnits_ext_count (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1296)
private theorem fracIdealUnits_ext_count {I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), count F v (I : FractionalIdeal (𝓞 F)⁰ F)
      = count F v (J : FractionalIdeal (𝓞 F)⁰ F)) : I = J := by
  refine Units.ext ?_
  rw [← finprod_heightOneSpectrum_factorization' (K := F) I.ne_zero,
    ← finprod_heightOneSpectrum_factorization' (K := F) J.ne_zero]
  exact finprod_congr fun v => by rw [h v]

-- pin: ideleIdeal_principal (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1304)
private theorem ideleIdeal_principal (α : Fˣ) :
    ideleIdeal (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α)
      = toPrincipalIdeal (𝓞 F) F α := by
  refine fracIdealUnits_ext_count fun v => ?_
  rw [count_ideleIdeal, ordAt_unitAtHom_principal, coe_toPrincipalIdeal]

end NumberField.TateGlobal

/-! ### section Fold_ArchLogEmbedding -/

open NumberField NumberField.TateGlobal IsDedekindDomain FractionalIdeal M4aHerbrand
open scoped nonZeroDivisors
namespace NumberField.TateGlobal
variable {F : Type} [Field F] [NumberField F]

-- pin: integralUnitEmb (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1338)
private def integralUnitEmb : (𝓞 F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom).comp
    (Units.map (algebraMap (𝓞 F) F).toMonoidHom)

-- pin: integralUnitEmb_mem_principalIdeles (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1342)
private theorem integralUnitEmb_mem_principalIdeles (u : (𝓞 F)ˣ) :
    integralUnitEmb u ∈ principalIdeles (𝓞 F) F :=
  ⟨Units.map (algebraMap (𝓞 F) F).toMonoidHom u, rfl⟩

-- pin: principal_mem_unitsOutside_empty_iff (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1346)
private theorem principal_mem_unitsOutside_empty_iff (α : Fˣ) :
    (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α) ∈ unitsOutside (F := F) ∅
      ↔ toPrincipalIdeal (𝓞 F) F α = 1 := by
  rw [← ker_ideleIdeal, MonoidHom.mem_ker, ideleIdeal_principal]

-- pin: toPrincipalIdeal_eq_one_iff (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1351)
private theorem toPrincipalIdeal_eq_one_iff (α : Fˣ) :
    toPrincipalIdeal (𝓞 F) F α = 1
      ↔ α ∈ (Units.map (algebraMap (𝓞 F) F).toMonoidHom).range := by
  rw [← Units.val_eq_one, coe_toPrincipalIdeal, ← spanSingleton_one (S := (𝓞 F)⁰),
    spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    rw [Units.smul_def, Algebra.smul_def] at hz
    have hz0 : algebraMap (𝓞 F) F ↑z ≠ 0 :=
      (FaithfulSMul.algebraMap_injective (𝓞 F) F).ne (Units.ne_zero z)
    have h1 : algebraMap (𝓞 F) F ↑z * algebraMap (𝓞 F) F ↑z⁻¹ = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    exact ⟨z⁻¹, Units.ext (mul_left_cancel₀ hz0 (h1.trans hz.symm))⟩
  · rintro ⟨z, rfl⟩
    refine ⟨z⁻¹, ?_⟩
    rw [Units.smul_def, Algebra.smul_def]
    show algebraMap (𝓞 F) F ↑z⁻¹ * algebraMap (𝓞 F) F ↑z = 1
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]

-- pin: range_integralUnitEmb (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1370)
private theorem range_integralUnitEmb :
    (integralUnitEmb (F := F)).range
      = principalIdeles (𝓞 F) F ⊓ unitsOutside (F := F) ∅ := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨integralUnitEmb_mem_principalIdeles u, ?_⟩
    have h := (principal_mem_unitsOutside_empty_iff
      (Units.map (algebraMap (𝓞 F) F).toMonoidHom u)).mpr
      ((toPrincipalIdeal_eq_one_iff _).mpr ⟨u, rfl⟩)
    exact h
  · rintro ⟨⟨α, hα⟩, hU⟩
    have hα' : (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom) α = x := hα
    rw [← hα'] at hU
    have hU' := (principal_mem_unitsOutside_empty_iff α).mp hU
    obtain ⟨u, rfl⟩ := (toPrincipalIdeal_eq_one_iff α).mp hU'
    exact ⟨u, hα'⟩

end NumberField.TateGlobal

/-! ### section Fold_FujisakiC1 -/

open MeasureTheory NumberField NumberField.TateGlobal M4aHerbrand
namespace M4aLocalCFT.FujisakiC1
variable (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]

-- pin: principalIdeles_le_normOneIdeles (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:1409)
private theorem principalIdeles_le_normOneIdeles :
    principalIdeles (𝓞 F) F ≤ normOneIdeles F := by
  rintro x ⟨a, rfl⟩
  exact NumberField.AdeleRing.distribHaarChar_algebraMap F a

end M4aLocalCFT.FujisakiC1

/-! ### section Fold_FujisakiC3 -/

open MeasureTheory NumberField NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion M4aHerbrand M4aLocalCFT
open scoped NNReal
namespace M4aLocalCFT.FujisakiC3
variable (F : Type) [Field F] [NumberField F]

-- pin: ideleNorm_archCentralUnit (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:2511)
private theorem ideleNorm_archCentralUnit (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    ideleNorm F (NumberField.AdelicVolume.archCentralUnit F w a) =
      ((distribHaarChar (w.Completion) a : ℝ≥0) : ℝ) := by
  unfold ideleNorm
  rw [distribHaarChar_archCentralUnit]

end M4aLocalCFT.FujisakiC3

/-! ### section Fold_FujisakiC3b -/

open MeasureTheory NumberField NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion M4aHerbrand M4aLocalCFT
open scoped NNReal
namespace M4aLocalCFT.FujisakiC3
variable {F : Type} [Field F] [NumberField F]

-- pin: ideleNorm_archUnitHom (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:2554)
private theorem ideleNorm_archUnitHom (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    ideleNorm F (archUnitHom w a) = ‖(a : w.Completion)‖ ^ w.mult := by
  borelize (w.Completion)
  rw [archUnitHom_apply, ideleNorm_archCentralUnit, NumberField.TateGlobal.FujisakiC3.distribHaarChar_completion_eq_pow_mult]
  push_cast
  rfl

end M4aLocalCFT.FujisakiC3

/-! ### section Fold_FujisakiC2a -/

open NumberField NumberField.TateGlobal NumberField.InfinitePlace IsDedekindDomain M4aHerbrand
open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory Topology
open scoped NNReal Classical
namespace M4aLocalCFT.FujisakiC2a
variable {F : Type} [Field F] [NumberField F]

-- pin: fiberGroup (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3158)
private abbrev fiberGroup (F : Type) [Field F] [NumberField F] : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  normOneIdeles F ⊓ unitsOutside (F := F) ∅

-- pin: fst_apply_mul (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3161)
private theorem fst_apply_mul (a b : AdeleRing (𝓞 F) F) (w : InfinitePlace F) : (a * b).1 w = a.1 w * b.1 w :=
  rfl

-- pin: fst_apply_one (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3164)
private theorem fst_apply_one (w : InfinitePlace F) : (1 : AdeleRing (𝓞 F) F).1 w = 1 := rfl

-- pin: archComp_ne_zero (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3166)
private theorem archComp_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    ((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  have h1 : (x : AdeleRing (𝓞 F) F).1 w * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 :=
    congrArg (fun z : AdeleRing (𝓞 F) F => z.1 w) x.mul_inv
  exact left_ne_zero_of_mul_eq_one h1

-- pin: norm_archComp_pos (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3172)
private theorem norm_archComp_pos (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    0 < ‖((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ :=
  norm_pos_iff.mpr (archComp_ne_zero x w)

-- pin: norm_algebraMap_fst_apply (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3176)
private theorem norm_algebraMap_fst_apply (x : F) (w : InfinitePlace F) :
    ‖(algebraMap F (AdeleRing (𝓞 F) F) x).1 w‖ = w x := by
  rw [AdeleRing.algebraMap_fst_apply, NumberField.InfinitePlace.Completion.norm_coe]
  rfl

-- pin: ideleNorm_eq_prod_of_mem_unitsOutside_empty (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3181)
private theorem ideleNorm_eq_prod_of_mem_unitsOutside_empty {x : (AdeleRing (𝓞 F) F)ˣ}
    (hx : x ∈ unitsOutside (F := F) ∅) :
    ideleNorm F x
      = ∏ w : InfinitePlace F, ‖((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
  have h0 : (∏ v : (↥(∅ : Finset (HeightOneSpectrum (𝓞 F)))),
      ((distribHaarChar (v.1.adicCompletion F) ((coord ∅ x).2.1 v) : ℝ≥0) : ℝ)) = 1 :=
    Fintype.prod_empty _
  rw [← asm_coord ∅ hx, ideleNorm_asm, h0, mul_one, asm_coord ∅ hx]
  refine Finset.prod_congr rfl fun w _ => ?_
  borelize (w.Completion)
  rw [NumberField.TateGlobal.FujisakiC3.distribHaarChar_completion_eq_pow_mult]
  push_cast
  rfl

-- pin: archLog (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3195)
private def archLog (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) : ℝ :=
  (w.mult : ℝ) * Real.log ‖((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖

-- pin: archLog_apply (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3198)
private theorem archLog_apply (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    archLog x w = (w.mult : ℝ) * Real.log ‖((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ := rfl

-- pin: archLog_mul (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3201)
private theorem archLog_mul (x y : (AdeleRing (𝓞 F) F)ˣ) : archLog (x * y) = archLog x + archLog y := by
  funext w
  rw [Pi.add_apply, archLog_apply, archLog_apply, archLog_apply, Units.val_mul, fst_apply_mul, norm_mul,
    Real.log_mul (norm_archComp_pos x w).ne' (norm_archComp_pos y w).ne', mul_add]

-- pin: archLog_one (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3206)
private theorem archLog_one : archLog (1 : (AdeleRing (𝓞 F) F)ˣ) = 0 := by
  funext w
  rw [archLog_apply, Units.val_one, fst_apply_one, norm_one, Real.log_one, mul_zero, Pi.zero_apply]

-- pin: archLog_inv (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3210)
private theorem archLog_inv (x : (AdeleRing (𝓞 F) F)ˣ) : archLog x⁻¹ = -archLog x := by
  have h : archLog x⁻¹ + archLog x = 0 := by rw [← archLog_mul, inv_mul_cancel, archLog_one]
  exact eq_neg_of_add_eq_zero_left h

-- pin: sum_archLog_eq_log_ideleNorm (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3214)
private theorem sum_archLog_eq_log_ideleNorm {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ unitsOutside (F := F) ∅) :
    ∑ w, archLog x w = Real.log (ideleNorm F x) := by
  rw [ideleNorm_eq_prod_of_mem_unitsOutside_empty hx, Real.log_prod]
  · simp only [archLog, Real.log_pow]
  · intro w _
    exact pow_ne_zero _ (norm_archComp_pos x w).ne'

-- pin: sum_archLog_coe_eq_zero (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3221)
private theorem sum_archLog_coe_eq_zero (g : ↥(fiberGroup F)) : ∑ w, archLog (g : (AdeleRing (𝓞 F) F)ˣ) w = 0 := by
  rw [sum_archLog_eq_log_ideleNorm (Subgroup.mem_inf.mp g.2).2,
    (mem_normOneIdeles_iff _).mp (Subgroup.mem_inf.mp g.2).1, Real.log_one]

-- pin: archLog_integralUnitEmb (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3225)
private theorem archLog_integralUnitEmb (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    archLog (integralUnitEmb u) w = (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)) := by
  rw [archLog_apply]
  congr 2
  exact norm_algebraMap_fst_apply (algebraMap (𝓞 F) F u) w

-- pin: archLog_integralUnitEmb_eq_logEmbedding (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3231)
private theorem archLog_integralUnitEmb_eq_logEmbedding (u : (𝓞 F)ˣ) (w : {w : InfinitePlace F // w ≠ w₀}) :
    archLog (integralUnitEmb u) w.1 = logEmbedding F (Additive.ofMul u) w := by
  rw [archLog_integralUnitEmb, logEmbedding_component]

-- pin: logBasis (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3235)
private def logBasis (F : Type) [Field F] [NumberField F] :
    Module.Basis (Fin (NumberField.Units.rank F)) ℝ (logSpace F) :=
  Module.Basis.ofZLatticeBasis ℝ (unitLattice F) (basisUnitLattice F)

-- pin: boundR (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3239)
private abbrev boundR (F : Type) [Field F] [NumberField F] : ℝ :=
  (Fintype.card (InfinitePlace F)) * ∑ i, ‖logBasis F i‖

-- pin: sum_norm_logBasis_nonneg (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3242)
private theorem sum_norm_logBasis_nonneg : 0 ≤ ∑ i, ‖logBasis F i‖ :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

-- pin: exists_unit_norm_sub_logEmbedding_le (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3245)
private theorem exists_unit_norm_sub_logEmbedding_le (v : logSpace F) :
    ∃ u : (𝓞 F)ˣ, ‖v - logEmbedding F (Additive.ofMul u)‖ ≤ ∑ i, ‖logBasis F i‖ := by
  have hfloor : ((ZSpan.floor (logBasis F) v : Submodule.span ℤ (Set.range ⇑(logBasis F))) : logSpace F)
      ∈ unitLattice F :=
    (Module.Basis.ofZLatticeBasis_span ℝ (unitLattice F) (basisUnitLattice F)).le (ZSpan.floor (logBasis F) v).2
  have hfloor' : ((ZSpan.floor (logBasis F) v : Submodule.span ℤ (Set.range ⇑(logBasis F))) : logSpace F)
      ∈ Submodule.map (logEmbedding F).toIntLinearMap ⊤ := hfloor
  obtain ⟨y, -, hy⟩ := Submodule.mem_map.mp hfloor'
  refine ⟨Additive.toMul y, ?_⟩
  have hfr := ZSpan.norm_fract_le (logBasis F) v
  rw [ZSpan.fract_apply, ← hy] at hfr
  exact hfr

-- pin: abs_le_card_mul_of_sum_eq_zero (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3258)
private theorem abs_le_card_mul_of_sum_eq_zero (c : InfinitePlace F → ℝ) (hsum : ∑ w, c w = 0)
    {r : ℝ} (hr : 0 ≤ r) (hc : ∀ w : InfinitePlace F, w ≠ w₀ → |c w| ≤ r) (w : InfinitePlace F) :
    |c w| ≤ (Fintype.card (InfinitePlace F)) * r := by
  have hcard : r ≤ (Fintype.card (InfinitePlace F)) * r := by
    nth_rw 1 [← one_mul r]
    exact mul_le_mul_of_nonneg_right (Nat.one_le_cast.mpr Fintype.card_pos) hr
  by_cases hw : w = w₀
  · subst hw
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, add_eq_zero_iff_eq_neg] at hsum
    rw [hsum, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ r fun w' _ => hc w'.1 w'.2).trans ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hr
    have hle : (Finset.univ : Finset {w' : InfinitePlace F // w' ≠ w₀}).card
        ≤ Fintype.card (InfinitePlace F) :=
      (Finset.card_univ (α := {w' : InfinitePlace F // w' ≠ w₀})).le.trans (Fintype.card_subtype_le _)
    exact_mod_cast hle
  · exact (hc w hw).trans hcard

-- pin: exp_neg_le_and_le_exp_of_abs_log_le (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3279)
omit [NumberField F] in
private theorem exp_neg_le_and_le_exp_of_abs_log_le {t R : ℝ} (ht : 0 < t) (h : |Real.log t| ≤ R) :
    Real.exp (-R) ≤ t ∧ t ≤ Real.exp R := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  exact ⟨(Real.exp_le_exp.mpr h1).trans_eq (Real.exp_log ht), (Real.log_le_iff_le_exp ht).mp h2⟩

-- pin: annulus (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3284)
private def annulus (w : InfinitePlace F) (R : ℝ) : Set (w.Completion)ˣ :=
  {t | Real.exp (-R) ≤ ‖(t : w.Completion)‖ ∧ ‖(t : w.Completion)‖ ≤ Real.exp R}

-- pin: isCompact_annulus_complex (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3287)
private theorem isCompact_annulus_complex (R : ℝ) :
    IsCompact {z : ℂ | Real.exp (-R) ≤ ‖z‖ ∧ ‖z‖ ≤ Real.exp R} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := Real.exp R)).subset fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz.2

-- pin: isCompact_annulus_val (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3296)
omit [NumberField F] in
private theorem isCompact_annulus_val (w : InfinitePlace F) (R : ℝ) :
    IsCompact {y : w.Completion | Real.exp (-R) ≤ ‖y‖ ∧ ‖y‖ ≤ Real.exp R} := by
  have hiso := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w
  have h := hiso.isClosedEmbedding.isCompact_preimage (isCompact_annulus_complex R)
  refine (congrArg IsCompact ?_).mp h
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hiso.norm_map_of_map_zero (map_zero _) y]

-- pin: isCompact_annulus (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3305)
omit [NumberField F] in
private theorem isCompact_annulus (w : InfinitePlace F) (R : ℝ) : IsCompact (annulus w R) := by
  refine Units.isEmbedding_val₀.isCompact_iff.mpr ?_
  refine (congrArg IsCompact ?_).mp (isCompact_annulus_val w R)
  ext y
  constructor
  · intro hy
    have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) hy.1)
    exact ⟨Units.mk0 y hy0, hy, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ht

-- pin: archBall (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3316)
private def archBall (R : ℝ) : Set (InfiniteAdeleRing F)ˣ :=
  {a | ∀ w : InfinitePlace F, Real.exp (-R) ≤ ‖(a : InfiniteAdeleRing F) w‖ ∧
    ‖(a : InfiniteAdeleRing F) w‖ ≤ Real.exp R}

-- pin: archBall_eq_preimage (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3321)
omit [NumberField F] in
private theorem archBall_eq_preimage (R : ℝ) :
    archBall (F := F) R = archPiUnits ⁻¹' Set.pi Set.univ (fun w => annulus w R) := by
  ext a
  simp only [archBall, annulus, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi, archPiUnits_apply]

-- pin: isCompact_archBall (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3327)
omit [NumberField F] in
private theorem isCompact_archBall (R : ℝ) : IsCompact (archBall (F := F) R) := by
  rw [archBall_eq_preimage]
  exact (archPiUnits (F := F)).toHomeomorph.isCompact_preimage.mpr
    (isCompact_univ_pi fun w => isCompact_annulus w R)

-- pin: paramSet (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3332)
private def paramSet (R : ℝ) : Set (Q (F := F) ∅) :=
  {q | (∏ w : InfinitePlace F, ‖((q.1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ ^ w.mult) = 1}
    ∩ archBall R ×ˢ Set.univ

-- pin: isCompact_paramSet (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3336)
private theorem isCompact_paramSet (R : ℝ) : IsCompact (paramSet (F := F) R) := by
  refine IsCompact.inter_left ((isCompact_archBall R).prod isCompact_univ) ?_
  refine isClosed_eq ?_ continuous_const
  refine continuous_finsetProd _ fun w _ => ?_
  exact (((continuous_apply w).comp (Units.continuous_val (M := InfiniteAdeleRing F) |>.comp continuous_fst)).norm).pow _

-- pin: asm_mem_of_mem_paramSet (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3342)
private theorem asm_mem_of_mem_paramSet {R : ℝ} {q : Q (F := F) ∅} (hq : q ∈ paramSet R) :
    asm ∅ q ∈ fiberGroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, asm_mem_unitsOutside ∅ q⟩
  rw [mem_normOneIdeles_iff, ideleNorm_eq_prod_of_mem_unitsOutside_empty (asm_mem_unitsOutside ∅ q)]
  have h1 : ((asm ∅ q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = (q.1 : InfiniteAdeleRing F) :=
    congrArg Units.val (archUnits_asm ∅ q)
  rw [h1]
  exact hq.1

-- pin: fiberCompact (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3351)
private def fiberCompact (F : Type) [Field F] [NumberField F] : Set ↥(fiberGroup F) :=
  Subtype.val ⁻¹' (asm ∅ '' paramSet (boundR F))

-- pin: val_image_fiberCompact (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3354)
private theorem val_image_fiberCompact :
    Subtype.val '' fiberCompact F = asm ∅ '' paramSet (boundR F) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨asm ∅ q, asm_mem_of_mem_paramSet hq⟩, ⟨q, hq, rfl⟩, rfl⟩

-- pin: isCompact_fiberCompact (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3363)
private theorem isCompact_fiberCompact : IsCompact (fiberCompact F) := by
  rw [IsEmbedding.subtypeVal.isCompact_iff, val_image_fiberCompact]
  exact (isCompact_paramSet (boundR F)).image (continuous_asm ∅)

-- pin: integralUnitEmb_mem (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3367)
private theorem integralUnitEmb_mem (u : (𝓞 F)ˣ) : integralUnitEmb u ∈ fiberGroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · borelize (AdeleRing (𝓞 F) F)
    exact M4aLocalCFT.FujisakiC1.principalIdeles_le_normOneIdeles F (integralUnitEmb_mem_principalIdeles u)
  · have h : integralUnitEmb u ∈ (integralUnitEmb (F := F)).range := ⟨u, rfl⟩
    rw [range_integralUnitEmb] at h
    exact (Subgroup.mem_inf.mp h).2

-- pin: unitElem (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3375)
private def unitElem (u : (𝓞 F)ˣ) : ↥(fiberGroup F) := ⟨integralUnitEmb u, integralUnitEmb_mem u⟩

-- pin: unitElem_mem_subgroupOf (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3377)
private theorem unitElem_mem_subgroupOf (u : (𝓞 F)ˣ) :
    unitElem u ∈ (principalIdeles (𝓞 F) F).subgroupOf (fiberGroup F) := by
  rw [Subgroup.mem_subgroupOf]
  exact integralUnitEmb_mem_principalIdeles u

-- pin: archLog_mul_unitElem_inv (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3382)
private theorem archLog_mul_unitElem_inv (g₀ : ↥(fiberGroup F)) (u : (𝓞 F)ˣ) (w : {w : InfinitePlace F // w ≠ w₀}) :
    archLog ((g₀ * (unitElem u)⁻¹ : ↥(fiberGroup F)) : (AdeleRing (𝓞 F) F)ˣ) w.1
      = archLog (g₀ : (AdeleRing (𝓞 F) F)ˣ) w.1 - logEmbedding F (Additive.ofMul u) w := by
  rw [Subgroup.coe_mul, Subgroup.coe_inv, archLog_mul, archLog_inv, Pi.add_apply, Pi.neg_apply,
    ← sub_eq_add_neg]
  congr 1
  exact archLog_integralUnitEmb_eq_logEmbedding u w

-- pin: exists_unit_mul_inv_mem_fiberCompact (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3390)
private theorem exists_unit_mul_inv_mem_fiberCompact (g₀ : ↥(fiberGroup F)) :
    ∃ u : (𝓞 F)ˣ, g₀ * (unitElem u)⁻¹ ∈ fiberCompact F := by
  obtain ⟨u, hu⟩ := exists_unit_norm_sub_logEmbedding_le (F := F)
    (fun w => archLog (g₀ : (AdeleRing (𝓞 F) F)ˣ) w.1)
  refine ⟨u, ?_⟩
  set g : ↥(fiberGroup F) := g₀ * (unitElem u)⁻¹ with hg
  have hgU : (g : (AdeleRing (𝓞 F) F)ˣ) ∈ unitsOutside (F := F) ∅ := (Subgroup.mem_inf.mp g.2).2
  have hg1 : ideleNorm F (g : (AdeleRing (𝓞 F) F)ˣ) = 1 :=
    (mem_normOneIdeles_iff _).mp (Subgroup.mem_inf.mp g.2).1
  have hbound : ∀ w : InfinitePlace F, |archLog (g : (AdeleRing (𝓞 F) F)ˣ) w| ≤ boundR F := by
    refine abs_le_card_mul_of_sum_eq_zero _ (sum_archLog_coe_eq_zero g) sum_norm_logBasis_nonneg ?_
    intro w hw
    have hcoord : archLog (g : (AdeleRing (𝓞 F) F)ˣ) w
        = ((fun w' : {w' : InfinitePlace F // w' ≠ w₀} => archLog (g₀ : (AdeleRing (𝓞 F) F)ˣ) w'.1)
            - logEmbedding F (Additive.ofMul u)) ⟨w, hw⟩ := by
      rw [Pi.sub_apply, hg]
      exact archLog_mul_unitElem_inv g₀ u ⟨w, hw⟩
    rw [hcoord, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ _).trans hu
  have hann : ∀ w : InfinitePlace F,
      Real.exp (-boundR F) ≤ ‖((g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ∧
        ‖((g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ≤ Real.exp (boundR F) := by
    intro w
    refine exp_neg_le_and_le_exp_of_abs_log_le (norm_archComp_pos _ w) ?_
    refine le_trans ?_ (hbound w)
    rw [archLog_apply, abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (Nat.one_le_cast.mpr mult_pos)
  refine ⟨coord ∅ (g : (AdeleRing (𝓞 F) F)ˣ), ⟨?_, ?_, Set.mem_univ _⟩, asm_coord ∅ hgU⟩
  · show ∏ w : InfinitePlace F, ‖((g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult = 1
    rw [← ideleNorm_eq_prod_of_mem_unitsOutside_empty hgU]
    exact hg1
  · exact fun w => hann w

-- pin: image_mk_fiberCompact (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3423)
private theorem image_mk_fiberCompact :
    (QuotientGroup.mk : ↥(fiberGroup F) → ↥(fiberGroup F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (fiberGroup F))
      '' fiberCompact F = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨u, hu⟩ := exists_unit_mul_inv_mem_fiberCompact g₀
  exact ⟨_, hu, QuotientGroup.mk_mul_of_mem g₀ (Subgroup.inv_mem _ (unitElem_mem_subgroupOf u))⟩

-- pin: compactSpace_fiberGroup_quot (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3431)
private theorem compactSpace_fiberGroup_quot :
    CompactSpace (↥(fiberGroup F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (fiberGroup F)) := by
  refine ⟨?_⟩
  rw [← image_mk_fiberCompact]
  exact (isCompact_fiberCompact (F := F)).image QuotientGroup.continuous_mk

end M4aLocalCFT.FujisakiC2a

/-! ### section Fold_FujisakiC2c -/

open NumberField NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open IsDedekindDomain FractionalIdeal M4aHerbrand MeasureTheory Topology M4aLocalCFT
open scoped NNReal nonZeroDivisors
namespace M4aLocalCFT.FujisakiC2c
variable {F : Type} [Field F] [NumberField F]

-- pin: exists_mul_principal_inv_mem_unitsOutside (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3464)
private theorem exists_mul_principal_inv_mem_unitsOutside {x : (AdeleRing (𝓞 F) F)ˣ} (hx : ideleClass x = 1) :
    ∃ α : Fˣ, x * (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α)⁻¹
      ∈ unitsOutside (F := F) ∅ := by
  have hP : (((ideleIdeal x : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) :
      Submodule (𝓞 F) F).IsPrincipal := by
    have h := hx
    rw [ideleClass, MonoidHom.comp_apply, ClassGroup.mk_eq_one_iff] at h
    exact h
  obtain ⟨a, ha⟩ := (FractionalIdeal.isPrincipal_iff _).mp hP
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [spanSingleton_zero] at ha
    exact (ideleIdeal x).ne_zero ha
  refine ⟨Units.mk0 a ha0, ?_⟩
  rw [← ker_ideleIdeal, MonoidHom.mem_ker, map_mul, map_inv, ideleIdeal_principal, mul_inv_eq_one]
  ext : 1
  rw [ha, coe_toPrincipalIdeal, Units.val_mk0]

-- pin: ideleClass_eq_one_of_mem_unitsOutside (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3482)
private theorem ideleClass_eq_one_of_mem_unitsOutside {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside (F := F) ∅) :
    ideleClass u = 1 := by
  rw [ideleClass, MonoidHom.comp_apply, (ideleIdeal_eq_one_iff u).mpr hu, map_one]

-- pin: exists_norm_pow_mult_eq (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3487)
omit [NumberField F] in
private theorem exists_norm_pow_mult_eq (w : InfinitePlace F) (r : ℝ) (hr : 0 < r) :
    ∃ t : w.Completion, t ≠ 0 ∧ ‖t‖ ^ w.mult = r := by
  rcases isReal_or_isComplex w with hv | hv
  · refine ⟨(ringEquivRealOfIsReal hv).symm r, ?_, ?_⟩
    · rw [ne_eq, ← map_zero (ringEquivRealOfIsReal hv).symm, (ringEquivRealOfIsReal hv).symm.injective.eq_iff]
      exact hr.ne'
    · have hn : ‖(ringEquivRealOfIsReal hv).symm r‖ = ‖r‖ := by
        have h := congrArg (fun z : ℝ≥0 => (z : ℝ))
          (NumberField.TateGlobal.ArchMulHaarCompletion.nnnorm_ringEquivReal hv ((ringEquivRealOfIsReal hv).symm r))
        simp only [RingEquiv.apply_symm_apply, coe_nnnorm] at h
        exact h.symm
      rw [mult, ite_eq_left hv, pow_one, hn, Real.norm_eq_abs, abs_of_pos hr]
  · refine ⟨(ringEquivComplexOfIsComplex hv).symm (Real.sqrt r : ℂ), ?_, ?_⟩
    · rw [ne_eq, ← map_zero (ringEquivComplexOfIsComplex hv).symm,
        (ringEquivComplexOfIsComplex hv).symm.injective.eq_iff, Complex.ofReal_eq_zero]
      exact fun h => hr.ne' ((Real.sqrt_eq_zero hr.le).mp h)
    · have hn : ‖(ringEquivComplexOfIsComplex hv).symm (Real.sqrt r : ℂ)‖ = ‖(Real.sqrt r : ℂ)‖ := by
        have h := congrArg (fun z : ℝ≥0 => (z : ℝ))
          (NumberField.TateGlobal.ArchMulHaarCompletion.nnnorm_ringEquivComplex hv
            ((ringEquivComplexOfIsComplex hv).symm (Real.sqrt r : ℂ)))
        simp only [RingEquiv.apply_symm_apply, coe_nnnorm] at h
        exact h.symm
      rw [mult, ite_eq_right (not_isReal_iff_isComplex.mpr hv), hn, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg r), Real.sq_sqrt hr.le]

-- pin: exists_mem_unitsOutside_ideleNorm_eq (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3512)
private theorem exists_mem_unitsOutside_ideleNorm_eq (r : ℝ) (hr : 0 < r) :
    ∃ y : (AdeleRing (𝓞 F) F)ˣ, y ∈ unitsOutside (F := F) ∅ ∧ ideleNorm F y = r := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨t, ht0, ht⟩ := exists_norm_pow_mult_eq w r hr
  refine ⟨archUnitHom w (Units.mk0 t ht0), ?_, ?_⟩
  · exact mem_unitsOutside_of_unitAtHom_eq_one ∅ fun v _ => Units.ext rfl
  · borelize (w.Completion)
    rw [M4aLocalCFT.FujisakiC3.ideleNorm_archUnitHom, Units.val_mk0, ht]

-- pin: exists_normOne_ideleClass_eq (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3521)
private theorem exists_normOne_ideleClass_eq (c : ClassGroup (𝓞 F)) :
    ∃ n : (AdeleRing (𝓞 F) F)ˣ, n ∈ normOneIdeles F ∧ ideleClass n = c := by
  obtain ⟨x, rfl⟩ := ideleClass_surjective' c
  obtain ⟨y, hyU, hy⟩ :=
    exists_mem_unitsOutside_ideleNorm_eq (F := F) (ideleNorm F x)⁻¹ (inv_pos.mpr (ideleNorm_pos x))
  refine ⟨x * y, ?_, ?_⟩
  · rw [mem_normOneIdeles_iff, ideleNorm_mul, hy, mul_inv_cancel₀ (ideleNorm_pos x).ne']
  · rw [map_mul, ideleClass_eq_one_of_mem_unitsOutside hyU, mul_one]

-- pin: fiberGroup_le_normOneIdeles (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3530)
private theorem fiberGroup_le_normOneIdeles : FujisakiC2a.fiberGroup F ≤ normOneIdeles F := inf_le_left

-- pin: inclHom (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3532)
private def inclHom : ↥(FujisakiC2a.fiberGroup F) →* ↥(normOneIdeles F) :=
  Subgroup.inclusion fiberGroup_le_normOneIdeles

-- pin: continuous_inclHom (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3535)
private theorem continuous_inclHom : Continuous (inclHom (F := F)) := by
  show Continuous fun x : ↥(FujisakiC2a.fiberGroup F) =>
    (⟨(x : (AdeleRing (𝓞 F) F)ˣ), fiberGroup_le_normOneIdeles x.2⟩ : ↥(normOneIdeles F))
  exact continuous_subtype_val.subtype_mk _

-- pin: fiberMap (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3540)
private def fiberMap :
    ↥(FujisakiC2a.fiberGroup F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (FujisakiC2a.fiberGroup F) →*
      ↥(normOneIdeles F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F) :=
  QuotientGroup.map _ _ inclHom fun g hg => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, inclHom, Subgroup.coe_inclusion]
    exact Subgroup.mem_subgroupOf.mp hg

-- pin: continuous_fiberMap (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3547)
private theorem continuous_fiberMap : Continuous (fiberMap (F := F)) := by
  rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
  have h : (⇑(fiberMap (F := F)) ∘ QuotientGroup.mk) = QuotientGroup.mk ∘ ⇑(inclHom (F := F)) := by
    funext x
    rfl
  rw [h]
  exact QuotientGroup.continuous_mk.comp continuous_inclHom

-- pin: isCompact_range_fiberMap (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3555)
private theorem isCompact_range_fiberMap : IsCompact (Set.range (fiberMap (F := F))) :=
  @isCompact_range _ _ _ _ (FujisakiC2a.compactSpace_fiberGroup_quot (F := F))
    (fiberMap (F := F)) continuous_fiberMap

-- pin: compactSpace_normOneIdeleClass_impl (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3559)
theorem compactSpace_normOneIdeleClass_impl (F : Type) [Field F] [NumberField F] :
    CompactSpace (↥(normOneIdeles F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F)) := by
  borelize (AdeleRing (𝓞 F) F)
  choose rep hrep using fun c : ClassGroup (𝓞 F) => exists_normOne_ideleClass_eq (F := F) c
  set K : Set (↥(normOneIdeles F) ⧸ (principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F)) :=
    ⋃ c : ClassGroup (𝓞 F),
      (fun y => (QuotientGroup.mk (⟨rep c, (hrep c).1⟩ : ↥(normOneIdeles F)) : ↥(normOneIdeles F) ⧸
        (principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F)) * y) '' Set.range (fiberMap (F := F))
  have hKc : IsCompact K :=
    isCompact_iUnion fun c => (isCompact_range_fiberMap (F := F)).image (continuous_const_mul _)
  have hKuniv : K = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
    set c : ClassGroup (𝓞 F) := ideleClass (n : (AdeleRing (𝓞 F) F)ˣ) with hc
    have h1 : ideleClass ((n : (AdeleRing (𝓞 F) F)ˣ) * (rep c)⁻¹) = 1 := by
      rw [map_mul, map_inv, (hrep c).2, hc, mul_inv_cancel]
    obtain ⟨α, hU⟩ := exists_mul_principal_inv_mem_unitsOutside h1
    set p : (AdeleRing (𝓞 F) F)ˣ := (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α) with hp
    have hpP : p ∈ principalIdeles (𝓞 F) F := ⟨α, rfl⟩
    have hpN : p ∈ normOneIdeles F := FujisakiC1.principalIdeles_le_normOneIdeles F hpP
    have huU : (rep c)⁻¹ * ((n : (AdeleRing (𝓞 F) F)ˣ) * p⁻¹) ∈ unitsOutside (F := F) ∅ := by
      rwa [mul_comm (n : (AdeleRing (𝓞 F) F)ˣ) (rep c)⁻¹, mul_assoc] at hU
    have huN : (rep c)⁻¹ * ((n : (AdeleRing (𝓞 F) F)ˣ) * p⁻¹) ∈ normOneIdeles F :=
      (normOneIdeles F).mul_mem ((normOneIdeles F).inv_mem (hrep c).1)
        ((normOneIdeles F).mul_mem n.2 ((normOneIdeles F).inv_mem hpN))
    let g : ↥(FujisakiC2a.fiberGroup F) :=
      ⟨(rep c)⁻¹ * ((n : (AdeleRing (𝓞 F) F)ˣ) * p⁻¹), Subgroup.mem_inf.mpr ⟨huN, huU⟩⟩
    refine Set.mem_iUnion.mpr ⟨c, fiberMap (QuotientGroup.mk g), ⟨QuotientGroup.mk g, rfl⟩, ?_⟩
    show QuotientGroup.mk (⟨rep c, (hrep c).1⟩ : ↥(normOneIdeles F)) * fiberMap (QuotientGroup.mk g)
      = QuotientGroup.mk n
    rw [fiberMap, QuotientGroup.map_mk, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show ((rep c * ((rep c)⁻¹ * ((n : (AdeleRing (𝓞 F) F)ˣ) * p⁻¹)))⁻¹ * (n : (AdeleRing (𝓞 F) F)ˣ))
      ∈ principalIdeles (𝓞 F) F
    rw [mul_inv_cancel_left, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    exact hpP
  refine ⟨?_⟩
  rw [← hKuniv]
  exact hKc

end M4aLocalCFT.FujisakiC2c

/-! ### section Fold_R1 -/

open NumberField NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open IsDedekindDomain FractionalIdeal M4aHerbrand MeasureTheory Topology M4aLocalCFT
open scoped NNReal nonZeroDivisors
namespace M4aLocalCFT.FujisakiR1
variable {F : Type} [Field F] [NumberField F]

-- pin: exists_isCompact_impl (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3623)
theorem exists_isCompact_impl (F : Type) [Field F] [NumberField F] :
    ∃ K : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact K ∧ K ⊆ (normOneIdeles F : Set _) ∧
      ∀ x ∈ normOneIdeles F, ∃ (η : Fˣ) (κ : (AdeleRing (𝓞 F) F)ˣ), κ ∈ K ∧
        x = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom η * κ := by
  borelize (AdeleRing (𝓞 F) F)
  choose rep hrep using fun c : ClassGroup (𝓞 F) => FujisakiC2c.exists_normOne_ideleClass_eq (F := F) c
  refine ⟨⋃ c : ClassGroup (𝓞 F),
    (fun κ : ↥(FujisakiC2a.fiberGroup F) => rep c * (κ : (AdeleRing (𝓞 F) F)ˣ)) '' FujisakiC2a.fiberCompact F,
    ?_, ?_, ?_⟩
  · exact isCompact_iUnion fun c =>
      (FujisakiC2a.isCompact_fiberCompact (F := F)).image (continuous_const.mul continuous_subtype_val)
  · intro y hy
    obtain ⟨c, κ, -, rfl⟩ := Set.mem_iUnion.mp hy
    exact (normOneIdeles F).mul_mem (hrep c).1 (FujisakiC2c.fiberGroup_le_normOneIdeles κ.2)
  · intro x hx
    set c : ClassGroup (𝓞 F) := ideleClass x with hc
    have h1 : ideleClass (x * (rep c)⁻¹) = 1 := by
      rw [map_mul, map_inv, (hrep c).2, hc, mul_inv_cancel]
    obtain ⟨α, hU⟩ := FujisakiC2c.exists_mul_principal_inv_mem_unitsOutside h1
    set p : (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom α with hp
    have hpP : p ∈ principalIdeles (𝓞 F) F := ⟨α, rfl⟩
    have hpN : p ∈ normOneIdeles F := M4aLocalCFT.FujisakiC1.principalIdeles_le_normOneIdeles F hpP
    have huU : (rep c)⁻¹ * (x * p⁻¹) ∈ unitsOutside (F := F) ∅ := by
      rwa [mul_comm x (rep c)⁻¹, mul_assoc] at hU
    have huN : (rep c)⁻¹ * (x * p⁻¹) ∈ normOneIdeles F :=
      (normOneIdeles F).mul_mem ((normOneIdeles F).inv_mem (hrep c).1)
        ((normOneIdeles F).mul_mem hx ((normOneIdeles F).inv_mem hpN))
    let g : ↥(FujisakiC2a.fiberGroup F) := ⟨(rep c)⁻¹ * (x * p⁻¹), Subgroup.mem_inf.mpr ⟨huN, huU⟩⟩
    obtain ⟨u, hu⟩ := FujisakiC2a.exists_unit_mul_inv_mem_fiberCompact g
    have hqP : p * integralUnitEmb u ∈ principalIdeles (𝓞 F) F :=
      (principalIdeles (𝓞 F) F).mul_mem hpP (integralUnitEmb_mem_principalIdeles u)
    obtain ⟨η, hη⟩ := hqP
    have hη' : Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom η = p * integralUnitEmb u := hη
    refine ⟨η, rep c * ((g * (FujisakiC2a.unitElem u)⁻¹ : ↥(FujisakiC2a.fiberGroup F)) : (AdeleRing (𝓞 F) F)ˣ),
      Set.mem_iUnion.mpr ⟨c, _, hu, rfl⟩, ?_⟩
    rw [hη']
    show x = p * integralUnitEmb u *
      (rep c * ((rep c)⁻¹ * (x * p⁻¹) * (integralUnitEmb u)⁻¹))
    rw [← mul_assoc (rep c), mul_inv_cancel_left, mul_mul_mul_comm, mul_inv_cancel, mul_one,
      mul_inv_cancel_comm_assoc]

end M4aLocalCFT.FujisakiR1

end
