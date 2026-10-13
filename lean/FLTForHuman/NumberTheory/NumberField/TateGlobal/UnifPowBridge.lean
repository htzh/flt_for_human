/-
  The uniformizer-power bridge: the order at a place of a unit, the integrality
  criterion `mem_integers_iff_ordAt_nonneg`, the value of `unifPow ϖ k * u` on the
  archimedean and finite components, the membership criterion
  `unifPow_mul_mem_integralOutside_iff`, and the factorizable-character evaluation
  `factorizable_apply_unifPow_mul`.

  Transcribed from the pin's `Fold_TateSDecomp4` section (`NumberField.TateGlobal`
  block), declared lines 4250-4342 of file A, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped, and so are the
  `set_option synthInstance.maxHeartbeats 1600000 in` /
  `set_option maxSynthPendingDepth 3 in` wrappers on `ordAt_nonneg_of_mem`.  No
  file-wide option beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ZetaIntegrand

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal

section Fold_TateSDecomp4

open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

-- pin: ordAt_nonneg_of_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4250)
theorem ordAt_nonneg_of_mem (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ)
    (ht : (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F) : 0 ≤ ordAt v t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have ha : (⟨(t : v.adicCompletion F), ht⟩ : v.adicCompletionIntegers F) ≠ 0 := by
    intro h
    exact t.ne_zero (congrArg Subtype.val h)
  have hbot : Ideal.span {(⟨(t : v.adicCompletion F), ht⟩ : v.adicCompletionIntegers F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hbot hϖ
  have hspan : Ideal.span {(⟨(t : v.adicCompletion F), ht⟩ : v.adicCompletionIntegers F)}
      = IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have h := NumberField.TateGlobal.ValuationOrd.ord_ofMul_of_mem (v.adicCompletionIntegers F) ht hspan
  rw [ordAt, h]
  exact Int.natCast_nonneg n

-- pin: mem_integers_iff_ordAt_nonneg (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4267)
theorem mem_integers_iff_ordAt_nonneg (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F ↔ 0 ≤ ordAt v t := by
  refine ⟨ordAt_nonneg_of_mem v t, fun h => ?_⟩
  rcases (v.adicCompletionIntegers F).mem_or_inv_mem (t : v.adicCompletion F) with ht | ht
  · exact ht
  · have ht' : ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
      rwa [Units.val_inv_eq_inv_val]
    have h1 := ordAt_nonneg_of_mem v t⁻¹ ht'
    rw [ordAt_inv] at h1
    have h0 : ordAt v t = 0 := le_antisymm (by omega) h
    exact ((ordAt_eq_zero_iff v t).mp h0).1

-- pin: unifPow_mul_val_fst (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4279)
theorem unifPow_mul_val_fst (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) (u : (AdeleRing (𝓞 F) F)ˣ) :
    ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = (u : AdeleRing (𝓞 F) F).1 := by
  have h1 : archUnits (unifPow ϖ k) = 1 := Units.ext (unifPow_val_fst ϖ k)
  have h : archUnits (unifPow ϖ k * u) = archUnits u := by rw [map_mul, h1, one_mul]
  exact congrArg (fun z : (InfiniteAdeleRing F)ˣ => (z : InfiniteAdeleRing F)) h

-- pin: unifPow_mul_val_snd_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4285)
theorem unifPow_mul_val_snd_apply (ϖ : Uniformizers F) (k : HeightOneSpectrum (𝓞 F) →₀ ℤ)
    (u : (AdeleRing (𝓞 F) F)ˣ) (w : HeightOneSpectrum (𝓞 F)) :
    (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w
      = (((ϖ.ϖ w ^ k w : (w.adicCompletion F)ˣ)) : w.adicCompletion F)
          * ((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w := by
  have h : unitAtHom w (unifPow ϖ k * u) = ϖ.ϖ w ^ k w * unitAtHom w u := by
    rw [map_mul, unitAtHom_unifPow]
  have h' := congrArg Units.val h
  rw [Units.val_mul] at h'
  exact h'

-- pin: unifPow_mul_val_snd_apply_of_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4296)
theorem unifPow_mul_val_snd_apply_of_mem (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) (u : (AdeleRing (𝓞 F) F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∈ S) :
    (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w
      = ((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w := by
  rw [unifPow_mul_val_snd_apply, hk w hw, zpow_zero, Units.val_one, one_mul]

-- pin: unifPow_mul_mem_integralOutside_iff (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4303)
theorem unifPow_mul_mem_integralOutside_iff (ϖ : Uniformizers F) {S : Finset (HeightOneSpectrum (𝓞 F))}
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ integralOutside S ↔ ∀ v ∉ S, 0 ≤ k v := by
  have hu' := (mem_unitsOutside_iff S u).mp hu
  rw [mem_integralOutside_iff]
  refine forall₂_congr fun v hv => ?_
  rw [show (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
      = ((unitAtHom v (unifPow ϖ k * u) : (v.adicCompletion F)ˣ) : v.adicCompletion F) from rfl,
    mem_integers_iff_ordAt_nonneg, map_mul, ordAt_mul, ordAt_unitAtHom_unifPow]
  have h0 : ordAt v (unitAtHom v u) = 0 := by
    rw [ordAt_eq_zero_iff]
    refine ⟨hu'.1 v hv, ?_⟩
    rw [← map_inv]
    exact hu'.2 v hv
  rw [h0, add_zero]

open scoped Classical in
-- pin: factorizable_apply_unifPow_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4320)
theorem factorizable_apply_unifPow_mul {f : AdeleRing (𝓞 F) F → ℂ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {g : (w : InfinitePlace F) → w.Completion → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsFactorizableStandardOutside f S g h) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = if ∀ v ∉ S, 0 ≤ k v then
          (∏ w, g w ((u : AdeleRing (𝓞 F) F).1 w)) * ∏ v ∈ S, h v (((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v)
        else 0 := by
  classical
  rw [hf]
  have hval : (fun x : AdeleRing (𝓞 F) F => (∏ w, g w (x.1 w)) * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v))
        ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = (∏ w, g w ((u : AdeleRing (𝓞 F) F).1 w)) * ∏ v ∈ S, h v (((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v) := by
    show (∏ w, g w (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w))
        * ∏ v ∈ S, h v ((((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v) = _
    rw [unifPow_mul_val_fst]
    congr 1
    exact Finset.prod_congr rfl fun v hv => by rw [unifPow_mul_val_snd_apply_of_mem ϖ hk u hv]
  by_cases hpos : ∀ v ∉ S, 0 ≤ k v
  · rw [ite_eq_left hpos, Set.indicator_of_mem ((unifPow_mul_mem_integralOutside_iff ϖ hu).mpr hpos)]
    exact hval
  · rw [ite_eq_right hpos, Set.indicator_of_notMem]
    exact fun hmem => hpos ((unifPow_mul_mem_integralOutside_iff ϖ hu).mp hmem)

end NumberField.TateGlobal

end

end Fold_TateSDecomp4
