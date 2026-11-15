/-
  The adèlic Fourier transform of a pure tensor, and its behaviour under a change of the
  multiplicative variable.

  A pure tensor `x ↦ g (x.1) * h (x.2)` is the basic probe of `schwartzBruhat F`.  Its Fourier
  transform factors (`fourierIntegral_pureTensor_eq`): the archimedean transform of `g` against the
  covolume of the lattice `mixedEmbedding.integerLattice F` times the finite transform of `h`, with
  the constant `μ (adelicBox F) / (covolume * ν (integralFiniteAdeles))` that the product
  fundamental domain `adelicBox F = infiniteBox F × integralFiniteAdeles` forces.  The module
  carries the homeomorphism `split` behind that domain and the two evaluations
  (`eHomeo_apply`, `split_apply`) the transport uses.

  `fourierIntegral_comp_mul_left` is the corresponding change of variable: multiplying the
  argument by a unit idèle scales the transform by the inverse of its module
  `distribHaarChar` and moves `w` to `a⁻¹ w`.

  Transcribed from the pin's proof files (pinned `aa2d8b3`), whose label namespaces `Ws25` and
  `R8Supply` are rectified to `NumberField.AdelicFourier`.

  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_fourierIntegral_comp_mul_left.lean
-/
import FLTForHuman.NumberTheory.AdelicFourier
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Topology.Algebra.Group.OpenMapping

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicBox NumberField.InfiniteAdeleRing IsDedekindDomain
open MeasureTheory
open scoped Classical NNReal ENNReal NumberField.AdelicCountability

namespace NumberField.AdelicFourier

section Split

variable (F : Type) [Field F] [NumberField F]

theorem isOpenMap_ringEquiv_mixedSpace : IsOpenMap (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  exact AddMonoidHom.isOpenMap_of_sigmaCompact
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddMonoidHom
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).surjective (continuous_ringEquiv_mixedSpace F)

def eHomeo : InfiniteAdeleRing F ≃ₜ (mixedEmbedding.mixedSpace F) where
  toEquiv := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv
  continuous_toFun := continuous_ringEquiv_mixedSpace F
  continuous_invFun := by
    refine continuous_def.2 fun s hs => ?_
    rw [show (InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv.invFun ⁻¹' s
        = (InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv '' s from
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toEquiv.image_eq_preimage_symm s).symm]
    exact isOpenMap_ringEquiv_mixedSpace F s hs

@[scoped simp] theorem eHomeo_apply (x : InfiniteAdeleRing F) :
    eHomeo F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x := rfl

def split : (AdeleRing (𝓞 F) F) ≃ₜ+ mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F :=
  ContinuousAddEquiv.mk' ((eHomeo F).prodCongr (Homeomorph.refl _)) fun x y => by
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace F (x + y).1, (x + y).2)
        : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F)
      = (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2)
        + (InfiniteAdeleRing.ringEquiv_mixedSpace F y.1, y.2)
    rw [Prod.mk_add_mk, ← map_add]
    rfl

@[scoped simp] theorem split_apply (x : (AdeleRing (𝓞 F) F)) :
    split F x = (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2) := rfl

theorem split_image_adelicBox :
    ⇑(split F) '' adelicBox F
      = ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F) ×ˢ integralFiniteAdeles (𝓞 F) F := by
  ext ⟨a, b⟩
  simp only [Set.mem_image, split_apply, Prod.mk.injEq, Set.mem_prod]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl, rfl⟩
    exact ⟨hx1, hx2⟩
  · rintro ⟨ha, hb⟩
    refine ⟨((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, b), ⟨?_, hb⟩,
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply a, rfl⟩
    change (InfiniteAdeleRing.ringEquiv_mixedSpace F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a)
      ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
    rw [RingEquiv.apply_symm_apply]
    exact ha

theorem covolume_integerLattice_eq_toReal :
    ZLattice.covolume (mixedEmbedding.integerLattice F) volume
      = (volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))).toReal := by
  have key : ∀ (L : Submodule ℤ (mixedEmbedding.mixedSpace F)) [DiscreteTopology L] [IsZLattice ℝ L],
      L = Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) →
      ZLattice.covolume L volume
        = (volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))).toReal := by
    intro L _ _ hL
    subst hL
    exact ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain (mixedEmbedding.latticeBasis F) volume)
  exact key _ (mixedEmbedding.span_latticeBasis F).symm

theorem addChar_prod_apply (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (x : (AdeleRing (𝓞 F) F)) :
    ψ x = ψ (x.1, 0) * ψ (0, x.2) := by
  conv_lhs => rw [show x = ((x.1, 0) : (AdeleRing (𝓞 F) F)) + ((0, x.2) : (AdeleRing (𝓞 F) F)) from
    Prod.ext (by simp) (by simp)]
  exact AddChar.map_add_eq_mul ψ _ _
end Split

section PureTensor

variable (F : Type) [Field F] [NumberField F]
variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]

theorem fourierIntegral_pureTensor_eq
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (g : (mixedEmbedding.mixedSpace F) → ℂ) (h : (FiniteAdeleRing (𝓞 F) F) → ℂ) (w : (AdeleRing (𝓞 F) F)) :
    fourierIntegral ψ μ
        (fun x ↦ g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2) w
      = ((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ)
        * fourierIntegral
            (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            volume g (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
        * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν h w.2 := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (𝓞 F) := AdelicCountability.instCountableRingOfIntegers F
  have : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := inferInstance
  have : SecondCountableTopology (mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) := inferInstance
  have : BorelSpace (mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) := Prod.borelSpace
  have : SigmaFinite ν := inferInstance

  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with he
  set ψV : AddChar (mixedEmbedding.mixedSpace F) ℂ :=
    ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp e.symm.toAddMonoidHom) with hψV
  set ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ := ψ.compAddMonoidHom (AddMonoidHom.inr _ _) with hψf
  set π : Measure (mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) := (volume : Measure (mixedEmbedding.mixedSpace F)).prod ν with hπ
  have hπHaar : π.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set μ' : Measure (mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F) := μ.map ⇑(split F) with hμ'
  have hμ'Haar : μ'.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ (split F)

  set c : ℝ≥0 := μ'.addHaarScalarFactor π with hc
  have huniq : μ' = c • π := Measure.isAddLeftInvariant_eq_smul μ' π

  set Φm : (AdeleRing (𝓞 F) F) ≃ᵐ mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F := (split F).toHomeomorph.toMeasurableEquiv with hΦm
  have hΦm_coe : ⇑Φm = ⇑(split F) := rfl

  have hbox : μ (adelicBox F)
      = c * (volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))
          * ν (integralFiniteAdeles (𝓞 F) F)) := by
    have h1 : μ (adelicBox F) = μ' (⇑(split F) '' adelicBox F) := by
      rw [hμ', ← hΦm_coe, MeasurableEquiv.map_apply, Φm.preimage_image]
    rw [h1, huniq, Measure.smul_apply, split_image_adelicBox, hπ, Measure.prod_prod,
      ENNReal.smul_def, smul_eq_mul]
  have hcov := covolume_integerLattice_eq_toReal F
  have hc_eq : (c : ℝ) = (μ (adelicBox F)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
        * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) := by
    have hne1 : ZLattice.covolume (mixedEmbedding.integerLattice F) volume ≠ 0 :=
      ZLattice.covolume_ne_zero _ _
    have hne2 : (ν (integralFiniteAdeles (𝓞 F) F)).toReal ≠ 0 := by
      refine ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩
      · exact ((isOpen_integralFiniteAdeles F).measure_pos ν ⟨0, fun v => zero_mem _⟩).ne'
      · exact (isCompact_integralFiniteAdeles F).measure_lt_top.ne
    rw [eq_div_iff (mul_ne_zero hne1 hne2), hcov, ← ENNReal.coe_toReal c, ← ENNReal.toReal_mul,
      ← ENNReal.toReal_mul, hbox]

  set G₁ : (mixedEmbedding.mixedSpace F) → ℂ := fun a => ψV (-(a * e w.1)) * g a with hG₁
  set G₂ : (FiniteAdeleRing (𝓞 F) F) → ℂ := fun b => ψf (-(b * w.2)) * h b with hG₂
  have hint : ∀ x : (AdeleRing (𝓞 F) F),
      ψ (-(x * w)) * (g (e x.1) * h x.2) = G₁ (split F x).1 * G₂ (split F x).2 := by
    intro x
    have hsplit := addChar_prod_apply F ψ (-(x * w))
    have h1 : ψ ((-(x * w)).1, 0) = ψV (-(e x.1 * e w.1)) := by
      rw [hψV]
      erw [AddChar.compAddMonoidHom_apply]
      congr 1
      change ((-(x * w)).1, (0 : FiniteAdeleRing (𝓞 F) F)) = (e.symm (-(e x.1 * e w.1)), 0)
      rw [map_neg, map_mul, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
      rfl
    have h2 : ψ (0, (-(x * w)).2) = ψf (-(x.2 * w.2)) := by
      rw [hψf]
      erw [AddChar.compAddMonoidHom_apply]
      rfl
    rw [hsplit, h1, h2]
    simp only [split_apply, hG₁, hG₂]
    ring

  calc fourierIntegral ψ μ (fun x ↦ g (e x.1) * h x.2) w
      = ∫ x, G₁ (split F x).1 * G₂ (split F x).2 ∂μ := by
        rw [fourierIntegral_def]; exact integral_congr_ae (Filter.Eventually.of_forall hint)
    _ = ∫ x, (fun p : mixedEmbedding.mixedSpace F × FiniteAdeleRing (𝓞 F) F => G₁ p.1 * G₂ p.2) (Φm x) ∂μ := by rfl
    _ = ∫ p, G₁ p.1 * G₂ p.2 ∂μ' := by
        rw [hμ', ← hΦm_coe]; exact (integral_map_equiv Φm (fun p => G₁ p.1 * G₂ p.2)).symm
    _ = (c : ℝ) • ∫ p, G₁ p.1 * G₂ p.2 ∂π := by
        rw [huniq, integral_smul_nnreal_measure]; rfl
    _ = (c : ℝ) • ((∫ a, G₁ a ∂volume) * ∫ b, G₂ b ∂ν) := by rw [hπ, integral_prod_mul]
    _ = ((c : ℝ) : ℂ) * (∫ a, G₁ a ∂volume) * ∫ b, G₂ b ∂ν := by
        rw [Complex.real_smul, mul_assoc]
    _ = _ := by
        rw [hc_eq, fourierIntegral_def, fourierIntegral_def, hG₁, hG₂]
        push_cast
        try rfl
end PureTensor

section MulLeft

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

theorem neg_mul_eq_neg_units_mul (a : 𝔸ˣ) (v w : 𝔸) : -(v * w) = -((↑a * v) * (↑a⁻¹ * w)) := by
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul]

theorem fourierIntegral_comp_mul_left [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (μ : Measure 𝔸) [μ.IsAddHaarMeasure] (ψ : AddChar 𝔸 ℂ) (f : 𝔸 → ℂ) (a : 𝔸ˣ) (w : 𝔸) :
    fourierIntegral ψ μ (fun v => f (a * v)) w
      = ((distribHaarChar 𝔸 a : ℝ) : ℂ)⁻¹ * fourierIntegral ψ μ f (↑a⁻¹ * w) := by
  have : Countable (𝓞 F) := AdelicCountability.instCountableRingOfIntegers F
  have : SecondCountableTopology 𝔸 := AdelicCountability.instSecondCountableAdeleRing (𝓞 F) F

  set G : 𝔸 → ℂ := fun u => ψ (-(u * (↑a⁻¹ * w))) * f u with hG
  have hint : fourierIntegral ψ μ (fun v => f (a * v)) w = ∫ v, G (a • v) ∂μ := by
    rw [fourierIntegral_def]
    congr 1
    funext v
    simp only [hG, Units.smul_def, smul_eq_mul]
    rw [neg_mul_eq_neg_units_mul F a v w]
  have hdom : ∫ v, G (a • v) ∂μ = ∫ u, G u ∂(DomMulAct.mk a⁻¹ • μ) := by
    rw [integral_domSMul]
    simp
  have huniq : (DomMulAct.mk a⁻¹ • μ : Measure 𝔸) = (distribHaarChar 𝔸 a)⁻¹ • μ := by
    have h := Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk a⁻¹ • μ) μ
    rwa [addHaarScalarFactor_smul_eq_distribHaarChar μ a⁻¹, map_inv (distribHaarChar 𝔸) a] at h
  rw [hint, hdom, huniq, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv,
    Complex.ofReal_inv]
  rfl

end MulLeft

end NumberField.AdelicFourier

end
