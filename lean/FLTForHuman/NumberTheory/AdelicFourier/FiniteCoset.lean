/-
  Character orthogonality over a compact subgroup of the finite adèles, and the Fourier
  transform of a principal coset.

  `setIntegral_addChar_mul_eq_ite_of_isCompact`: the integral of an additive character `ψ (ξ * z)`
  over a compact subgroup `K` of `𝔸_F^fin` is the measure of `K` when `ψ (ξ * ·)` is trivial on `K`
  and `0` otherwise — the orthogonality relation every lattice computation rests on.  The module
  proves it from the invariance of the Haar integral under translation by `K`
  (`setIntegral_comp_add_left_eq`) and the resulting eigen-equation `char_mul_setIntegral_eq`.

  `fourierIntegral_indicator_principalCoset_finiteAdeleRing(_apply)`: the Fourier transform of the
  indicator of a principal coset `k + d • 𝓞̂` of the finite adèles — the computation behind the
  Poisson summation of a Schwartz–Bruhat function over the diagonal.

  Transcribed from the pin's proof files (pinned `aa2d8b3`), whose label namespaces `Ws25OrthK`
  and `Ws25Fcoset` are rectified to `NumberField.AdelicFourier`.

  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_setIntegral_addChar_mul_eq_ite_of_isCompact.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply.lean
-/
import FLTForHuman.NumberTheory.AdelicFourier
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicBox IsDedekindDomain MeasureTheory
open scoped Classical NNReal ENNReal

namespace NumberField.AdelicFourier

section Orthogonality

variable {F : Type} [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)
  (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F))

omit [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem setIntegral_comp_add_left_eq [MeasurableAdd (FiniteAdeleRing (𝓞 F) F)]
    (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    {c : FiniteAdeleRing (𝓞 F) F} (hc : c ∈ K) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), g (c + z) ∂ν
      = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), g z ∂ν := by
  have hpre : (fun z : FiniteAdeleRing (𝓞 F) F => c + z) ⁻¹' (K : Set (FiniteAdeleRing (𝓞 F) F))
      = (K : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext z
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun h => by simpa using K.add_mem (K.neg_mem hc) h, fun h => K.add_mem hc h⟩
  have h := (measurePreserving_add_left ν c).setIntegral_preimage_emb
    (measurableEmbedding_addLeft c) g (K : Set (FiniteAdeleRing (𝓞 F) F))
  rwa [hpre] at h

theorem char_mul_setIntegral_eq (hKm : MeasurableSet (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) {c : FiniteAdeleRing (𝓞 F) F} (hc : c ∈ K) :
    ψf (ξ * c) * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν := by
  calc ψf (ξ * c) * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * c) * ψf (ξ * z) ∂ν :=
        (integral_const_mul _ _).symm
    _ = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * (c + z)) ∂ν := by
        refine setIntegral_congr_fun hKm (fun z _ => ?_)
        rw [mul_add, AddChar.map_add_eq_mul]
    _ = ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν :=
        setIntegral_comp_add_left_eq ν K (fun z => ψf (ξ * z)) hc

theorem setIntegral_addChar_mul_eq_ite (hK : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = if (∀ z ∈ K, ψf (ξ * z) = 1) then ((ν K).toReal : ℂ) else 0 := by
  have hKm : MeasurableSet (K : Set (FiniteAdeleRing (𝓞 F) F)) := hK.isClosed.measurableSet
  split_ifs with h
  · rw [setIntegral_congr_fun hKm (fun z hz => h z hz), setIntegral_const]
    simp [Measure.real, Complex.real_smul]
  · have h' : ∃ c ∈ K, ψf (ξ * c) ≠ 1 := by
      by_contra h'
      exact h (fun z hz => by_contra fun hz' => h' ⟨z, hz, hz'⟩)
    obtain ⟨c, hcK, hc⟩ := h'
    have hkey := char_mul_setIntegral_eq ν ψf K hKm ξ hcK
    by_contra hI
    apply hc
    have h1 : ψf (ξ * c) * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
        = 1 * ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν := by
      rw [hkey, one_mul]
    exact mul_right_cancel₀ hI h1

end Orthogonality

section Coset

variable {F : Type} [Field F] [NumberField F]
  [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
  (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
  (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)

omit [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] in
theorem addChar_neg_eq_one_iff (x : FiniteAdeleRing (𝓞 F) F) : ψf (-x) = 1 ↔ ψf x = 1 := by
  have key : ψf (-x) * ψf x = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  constructor
  · intro h
    rw [h, one_mul] at key
    exact key
  · intro h
    rw [h, mul_one] at key
    exact key

theorem setIntegral_image_add_left (g : FiniteAdeleRing (𝓞 F) F → ℂ)
    (c : FiniteAdeleRing (𝓞 F) F) (B : Set (FiniteAdeleRing (𝓞 F) F)) :
    ∫ v in (fun b => c + b) '' B, g v ∂ν = ∫ b in B, g (c + b) ∂ν := by
  have h := (measurePreserving_add_left ν c).setIntegral_preimage_emb
    (measurableEmbedding_addLeft c) g ((fun b => c + b) '' B)
  rw [Set.preimage_image_eq B (add_right_injective c)] at h
  exact h.symm

theorem setIntegral_addChar_eq_ite {B : Set (FiniteAdeleRing (𝓞 F) F)} (hBm : MeasurableSet B)
    (hadd : ∀ ⦃x y⦄, x ∈ B → y ∈ B → x + y ∈ B) (hneg : ∀ ⦃x⦄, x ∈ B → -x ∈ B)
    (ξ : FiniteAdeleRing (𝓞 F) F) :
    ∫ z in B, ψf (ξ * z) ∂ν = if (∀ z ∈ B, ψf (ξ * z) = 1) then ((ν B).toReal : ℂ) else 0 := by
  split_ifs with h
  · rw [setIntegral_congr_fun hBm (fun z hz => h z hz), setIntegral_const]
    simp [Measure.real, Complex.real_smul]
  · have h' : ∃ c ∈ B, ψf (ξ * c) ≠ 1 := by
      by_contra h'
      exact h (fun z hz => by_contra fun hz' => h' ⟨z, hz, hz'⟩)
    obtain ⟨c, hcB, hc⟩ := h'
    have hpre : (fun z : FiniteAdeleRing (𝓞 F) F => c + z) ⁻¹' B = B := by
      ext z
      simp only [Set.mem_preimage]
      exact ⟨fun hz => by simpa using hadd (hneg hcB) hz, fun hz => hadd hcB hz⟩
    have hshift : ∫ z in B, ψf (ξ * (c + z)) ∂ν = ∫ z in B, ψf (ξ * z) ∂ν := by
      have h := (measurePreserving_add_left ν c).setIntegral_preimage_emb
        (measurableEmbedding_addLeft c) (fun z => ψf (ξ * z)) B
      rwa [hpre] at h
    have hkey : ψf (ξ * c) * ∫ z in B, ψf (ξ * z) ∂ν = ∫ z in B, ψf (ξ * z) ∂ν := by
      calc ψf (ξ * c) * ∫ z in B, ψf (ξ * z) ∂ν
          = ∫ z in B, ψf (ξ * c) * ψf (ξ * z) ∂ν := (integral_const_mul _ _).symm
        _ = ∫ z in B, ψf (ξ * (c + z)) ∂ν := by
            refine setIntegral_congr_fun hBm (fun z _ => ?_)
            rw [mul_add, AddChar.map_add_eq_mul]
        _ = ∫ z in B, ψf (ξ * z) ∂ν := hshift
    by_contra hI
    apply hc
    have h1 : ψf (ξ * c) * ∫ z in B, ψf (ξ * z) ∂ν = 1 * ∫ z in B, ψf (ξ * z) ∂ν := by
      rw [hkey, one_mul]
    exact mul_right_cancel₀ hI h1

theorem fourierIntegral_indicator_coset (c a w : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral ψf ν
        (((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) w
      = ψf (-(c * w))
        * ((ν ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψf (a * w * z) = 1 then 1 else 0) := by
  have hO_cpt : IsCompact (integralFiniteAdeles (𝓞 F) F) := isCompact_integralFiniteAdeles (K := F)
  have hB_cpt : IsCompact ((fun z => a * z) '' integralFiniteAdeles (𝓞 F) F) :=
    hO_cpt.image (continuous_const.mul continuous_id)
  have hBm : MeasurableSet ((fun z => a * z) '' integralFiniteAdeles (𝓞 F) F) :=
    hB_cpt.isClosed.measurableSet
  have hS_eq : (fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F
      = (fun b => c + b) '' ((fun z => a * z) '' integralFiniteAdeles (𝓞 F) F) :=
    (Set.image_image (fun b => c + b) (fun z => a * z) (integralFiniteAdeles (𝓞 F) F)).symm
  have hS_cpt : IsCompact ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F) :=
    hO_cpt.image (continuous_const.add (continuous_const.mul continuous_id))
  have hSm : MeasurableSet ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F) :=
    hS_cpt.isClosed.measurableSet
  have hadd : ∀ ⦃x y⦄, x ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F →
      y ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F →
      x + y ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F := by
    rintro x y ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, rfl⟩
    exact ⟨z₁ + z₂, fun v => add_mem (hz₁ v) (hz₂ v), by simp only [mul_add]⟩
  have hneg : ∀ ⦃x⦄, x ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F →
      -x ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨-z, fun v => neg_mem (hz v), by simp only [mul_neg]⟩

  have h1 : fourierIntegral ψf ν
        (((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1) w
      = ∫ v in (fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F, ψf (-(v * w)) ∂ν := by
    rw [fourierIntegral_def]
    have hrw : (fun v => ψf (-(v * w))
          * ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1 v)
        = ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F).indicator
            (fun v => ψf (-(v * w))) := by
      funext v
      by_cases hv : v ∈ (fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, mul_zero]
    rw [hrw, integral_indicator hSm]

  have h2 : ∫ v in (fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F, ψf (-(v * w)) ∂ν
      = ψf (-(c * w))
        * ∫ b in (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F, ψf (-w * b) ∂ν := by
    rw [hS_eq, setIntegral_image_add_left ν (fun v => ψf (-(v * w))) c, ← integral_const_mul]
    refine setIntegral_congr_fun hBm (fun b _ => ?_)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring

  have h3 := setIntegral_addChar_eq_ite ν ψf hBm hadd hneg (-w)

  have h4 : (∀ b ∈ (fun z => a * z) '' integralFiniteAdeles (𝓞 F) F, ψf (-w * b) = 1)
      ↔ (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψf (a * w * z) = 1) := by
    constructor
    · intro h z hz
      have hb := h (a * z) ⟨z, hz, rfl⟩
      have e : -w * (a * z) = -(a * w * z) := by ring
      rw [e, addChar_neg_eq_one_iff] at hb
      exact hb
    · rintro h b ⟨z, hz, rfl⟩
      have e : -w * (a * z) = -(a * w * z) := by ring
      rw [e, addChar_neg_eq_one_iff]
      exact h z hz

  have h5 : ν ((fun z => c + a * z) '' integralFiniteAdeles (𝓞 F) F)
      = ν ((fun z => a * z) '' integralFiniteAdeles (𝓞 F) F) := by
    rw [hS_eq, Set.image_add_left, measure_preimage_add]
  rw [h1, h2, h3, h5]
  by_cases hc : ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψf (a * w * z) = 1
  · rw [ite_eq_left (h4.mpr hc), ite_eq_left hc, mul_one]
  · rw [ite_eq_right (fun h => hc (h4.mp h)), ite_eq_right hc, mul_zero, mul_zero]

end Coset

theorem setIntegral_addChar_mul_eq_ite_of_isCompact
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ)
    (K : AddSubgroup (FiniteAdeleRing (𝓞 F) F)) (hK : IsCompact (K : Set (FiniteAdeleRing (𝓞 F) F)))
    (ξ : FiniteAdeleRing (𝓞 F) F) :
    ∫ z in (K : Set (FiniteAdeleRing (𝓞 F) F)), ψf (ξ * z) ∂ν
      = if (∀ z ∈ K, ψf (ξ * z) = 1) then ((ν K).toReal : ℂ) else 0 :=
  setIntegral_addChar_mul_eq_ite ν ψf K hK ξ

theorem fourierIntegral_indicator_principalCoset_finiteAdeleRing
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf)
    (d : 𝓞 F) (hd : d ≠ 0) (k ξ : F) :
    fourierIntegral ψf ν
        (((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator 1)
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)
      = ψf (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) (k * ξ)))
        * ((ν ((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
              ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * ξ) * z) = 1
            then 1 else 0) := by
  -- `hψf` and `hd` are the pin's binders; the coset computation consumes only `hψf`
  have _ := hd
  set S := integralFiniteAdeles (𝓞 F) F
  set S' : Set (FiniteAdeleRing (𝓞 F) F) :=
    (fun z => algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' S with hS'_def
  set T := (fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k +
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' S with hT_def
  have hScomp : IsCompact S := isCompact_integralFiniteAdeles F
  have hS'comp : IsCompact S' := hScomp.image (continuous_const.mul continuous_id)
  have hS'meas : MeasurableSet S' := hS'comp.isClosed.measurableSet

  have hT_trans : T = (fun u => u + algebraMap F (FiniteAdeleRing (𝓞 F) F) k) '' S' := by
    rw [hT_def, hS'_def, ← Set.image_comp]; congr 1; funext z; dsimp; ring
  have hνT_eq : ν T = ν S' := by
    rw [hT_trans, Set.image_add_right, measure_preimage_add_right]

  have hSadd : ∀ ⦃y z⦄, y ∈ S → z ∈ S → y + z ∈ S := fun y z hy hz v => add_mem (hy v) (hz v)
  have hSneg : ∀ ⦃z⦄, z ∈ S → -z ∈ S := fun z hz v => neg_mem (hz v)
  have hS'add : ∀ ⦃u v⦄, u ∈ S' → v ∈ S' → u + v ∈ S' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩; exact ⟨y + z, hSadd hy hz, by ring⟩
  have hS'neg : ∀ ⦃u⦄, u ∈ S' → -u ∈ S' := by
    rintro _ ⟨z, hz, rfl⟩; exact ⟨-z, hSneg hz, by ring⟩

  have hmem : ∀ v, v ∈ T ↔ v + (-algebraMap F (FiniteAdeleRing (𝓞 F) F) k) ∈ S' := by
    intro v; rw [hT_trans]
    constructor
    · rintro ⟨u, hu, rfl⟩; simpa using hu
    · intro hu; exact ⟨v + (-algebraMap F (FiniteAdeleRing (𝓞 F) F) k), hu, by ring⟩
  have hind : (T.indicator (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
      = ((S'.indicator 1 : FiniteAdeleRing (𝓞 F) F → ℂ) ∘
          (· + (-algebraMap F (FiniteAdeleRing (𝓞 F) F) k))) := by
    funext v
    by_cases hv : v ∈ T
    · simp only [Set.indicator_of_mem hv, Function.comp_apply,
        Set.indicator_of_mem ((hmem v).mp hv), Pi.one_apply]
    · simp only [Set.indicator_of_notMem hv, Function.comp_apply,
        Set.indicator_of_notMem (fun h => hv ((hmem v).mpr h))]
  rw [hind,
    fourierIntegral_comp_add_right ψf ν (S'.indicator 1)
      (-algebraMap F (FiniteAdeleRing (𝓞 F) F) k)]
  simp only [neg_mul, ← map_mul]
  rw [mul_assoc]
  congr 1

  rw [fourierIntegral_def]
  have hrw : (fun v => ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) * S'.indicator 1 v)
      = S'.indicator (fun v => ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ))) := by
    funext v; by_cases hv : v ∈ S'
    · simp [Set.indicator_of_mem hv]
    · simp [Set.indicator_of_notMem hv]
  rw [hrw, integral_indicator hS'meas]
  have hcont : Continuous fun v => ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) :=
    hψf.comp (continuous_id.mul continuous_const).neg

  have hortho : ∫ v in S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) ∂ν
      = if (∀ v ∈ S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) = 1)
        then ((ν S').toReal : ℂ) else 0 := by
    by_cases hc : ∀ v ∈ S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) = 1
    · rw [ite_eq_left hc, setIntegral_congr_fun hS'meas (fun v hv => hc v hv), setIntegral_const]
      simp [Measure.real, Complex.real_smul]
    · rw [ite_eq_right hc]
      push Not at hc
      obtain ⟨u₀, hu₀, hψu₀⟩ := hc
      set I := ∫ v in S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) ∂ν with hI_def
      have hS'inv : (fun v => v + u₀) ⁻¹' S' = S' := by
        ext v; constructor
        · intro hv; have := hS'add hv (hS'neg hu₀); simpa using this
        · intro hv; exact hS'add hv hu₀
      have hν_right : ν.map (· + u₀) = ν := by
        have hcomm : (· + u₀) = (u₀ + · : FiniteAdeleRing (𝓞 F) F → _) :=
          funext fun v => add_comm v u₀
        rw [hcomm]; exact map_add_left_eq_self ν u₀
      have hI : I = ψf (-(u₀ * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) * I := by
        calc I = ∫ v in S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ))
              ∂(ν.map (· + u₀)) := by rw [hν_right]
          _ = ∫ v in (· + u₀) ⁻¹' S',
              ψf (-((v + u₀) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) ∂ν := by
              rw [setIntegral_map hS'meas hcont.aestronglyMeasurable
                (measurable_add_const u₀).aemeasurable]
          _ = ∫ v in S', ψf (-((v + u₀) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) ∂ν := by
              rw [hS'inv]
          _ = ∫ v in S', ψf (-(u₀ * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ))
                * ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) ∂ν := by
              congr 1 with v
              rw [add_mul, neg_add, AddChar.map_add_eq_mul, mul_comm]
          _ = ψf (-(u₀ * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) * I := by
              rw [integral_const_mul, hI_def]
      have key : (1 - ψf (-(u₀ * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ))) * I = 0 := by
        rw [sub_mul, one_mul, sub_eq_zero]; exact hI
      rcases mul_eq_zero.mp key with h | h
      · exact absurd (sub_eq_zero.mp h).symm hψu₀
      · exact h
  rw [hortho]

  have hcond_iff : (∀ v ∈ S', ψf (-(v * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)) = 1)
      ↔ (∀ z ∈ S, ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * ξ) * z) = 1) := by
    have heq : ∀ z, -(algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z
        * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ)
        = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * ξ) * (-z) := by
      intro z; rw [map_mul]; ring
    constructor
    · intro h z hz
      have := h _ ⟨z, hz, rfl⟩
      rw [heq, mul_neg, AddChar.map_neg_eq_inv, inv_eq_one] at this
      exact this
    · rintro h _ ⟨z, hz, rfl⟩
      rw [heq, mul_neg, AddChar.map_neg_eq_inv, inv_eq_one]
      exact h z hz
  rw [hνT_eq]
  by_cases hc : ∀ z ∈ S, ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * ξ) * z) = 1
  · rw [ite_eq_left (hcond_iff.mpr hc), ite_eq_left hc, mul_one]
  · rw [ite_eq_right (fun h => hc (hcond_iff.mp h)), ite_eq_right hc, mul_zero]

theorem fourierIntegral_indicator_principalCoset_finiteAdeleRing_apply
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf)
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) (w : FiniteAdeleRing (𝓞 F) F) :
    fourierIntegral ψf ν
        (((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F).indicator 1)
        w
      = ψf (-(algebraMap F (FiniteAdeleRing (𝓞 F) F) k * w))
        * ((ν ((fun z ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
            integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)
        * (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
              ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w * z) = 1
            then 1 else 0) := by
  -- `hψf` and `hd` are the pin's binders; the coset computation consumes neither
  have _ := hψf
  have _ := hd
  exact fourierIntegral_indicator_coset ν ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) k)
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) w

end NumberField.AdelicFourier

end
