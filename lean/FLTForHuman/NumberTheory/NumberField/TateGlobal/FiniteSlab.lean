/-
  The finite-place slab: the coordinate `coordAt`, the localized adèles
  `finSingle`/`adeleSingle`, the slab/box neighbourhoods, the pushed-forward
  Haar `slabPush`, and the finite part of the assembly character
  (`distribHaarChar_embUnit`).

  Transcribed from the pin's `Fold_LocalGlobalModulus` section (the
  `NumberField.TateGlobal` `LG`/`Measure` blocks), declared lines 3232-3586 of
  file A, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped; no file-wide option
  beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ReferenceMeasure

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal

section Fold_LocalGlobalModulus



open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

section LG

variable (v : HeightOneSpectrum (𝓞 F))

-- pin: coordAt (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3232)
def coordAt (x : AdeleRing (𝓞 F) F) : v.adicCompletion F := (x.2 : FiniteAdeleRing (𝓞 F) F) v

-- pin: continuous_coordAt (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3234)
theorem continuous_coordAt : Continuous (coordAt (F := F) v) :=
  (continuous_finAdeleEval (𝓞 F) F v).comp (continuous_adeleFin (𝓞 F) F)

open scoped Classical in
-- pin: finSingle (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3238)
def finSingle (c : v.adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨Function.update 0 v c,
    Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
      by_contra hwv
      exact hw (by rw [Function.update_of_ne hwv]; exact zero_mem _))⟩

open scoped Classical in
-- pin: finSingle_apply_self (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3245)
theorem finSingle_apply_self (c : v.adicCompletion F) : (finSingle v c : FiniteAdeleRing (𝓞 F) F) v = c := by
  show Function.update (0 : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v c v = c
  simp

open scoped Classical in
-- pin: finSingle_apply_of_ne (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3250)
theorem finSingle_apply_of_ne (c : v.adicCompletion F) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (finSingle v c : FiniteAdeleRing (𝓞 F) F) w = 0 := by
  show Function.update (0 : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v c w = 0
  simp [Function.update_of_ne hw]

-- pin: adeleSingle (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3255)
def adeleSingle (c : v.adicCompletion F) : AdeleRing (𝓞 F) F := ((0 : InfiniteAdeleRing F), finSingle v c)

-- pin: coordAt_adeleSingle_add (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3257)
theorem coordAt_adeleSingle_add (c : v.adicCompletion F) (x : AdeleRing (𝓞 F) F) :
    coordAt v (adeleSingle v c + x) = c + coordAt v x := by
  show (finSingle v c : FiniteAdeleRing (𝓞 F) F) v + (x.2 : FiniteAdeleRing (𝓞 F) F) v = c + _
  rw [finSingle_apply_self]
  rfl

-- pin: adeleSingle_add_fst (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3263)
theorem adeleSingle_add_fst (c : v.adicCompletion F) (x : AdeleRing (𝓞 F) F) :
    (adeleSingle v c + x).1 = x.1 := by
  show (0 : InfiniteAdeleRing F) + x.1 = x.1
  rw [zero_add]

-- pin: adeleSingle_add_snd_apply_of_ne (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3268)
theorem adeleSingle_add_snd_apply_of_ne (c : v.adicCompletion F) (x : AdeleRing (𝓞 F) F)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    ((adeleSingle v c + x).2 : FiniteAdeleRing (𝓞 F) F) w = (x.2 : FiniteAdeleRing (𝓞 F) F) w := by
  show (finSingle v c : FiniteAdeleRing (𝓞 F) F) w + (x.2 : FiniteAdeleRing (𝓞 F) F) w = _
  rw [finSingle_apply_of_ne v c hw, zero_add]

-- pin: slab (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3274)
def slab (B : Set (InfiniteAdeleRing F)) : Set (AdeleRing (𝓞 F) F) :=
  {x | x.1 ∈ B ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}

-- pin: box (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3277)
def box (B : Set (InfiniteAdeleRing F)) : Set (AdeleRing (𝓞 F) F) :=
  {x | x.1 ∈ B ∧ ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}

-- pin: preimage_adeleSingle_add_slab (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3280)
theorem preimage_adeleSingle_add_slab (B : Set (InfiniteAdeleRing F)) (c : v.adicCompletion F) :
    (fun x => adeleSingle v c + x) ⁻¹' slab v B = slab v B := by
  ext x
  simp only [Set.mem_preimage, slab, Set.mem_ofPred_eq, adeleSingle_add_fst]
  refine and_congr Iff.rfl (forall₂_congr fun w hw => ?_)
  rw [adeleSingle_add_snd_apply_of_ne v c x hw]

-- pin: preimage_adeleSingle_add_coordAt (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3287)
theorem preimage_adeleSingle_add_coordAt (c : v.adicCompletion F) (E : Set (v.adicCompletion F)) :
    (fun x => adeleSingle v c + x) ⁻¹' (coordAt v ⁻¹' E) = coordAt v ⁻¹' ((fun y => c + y) ⁻¹' E) := by
  ext x
  simp only [Set.mem_preimage, coordAt_adeleSingle_add]

-- pin: coordAt_preimage_integers_inter_slab (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3292)
theorem coordAt_preimage_integers_inter_slab (B : Set (InfiniteAdeleRing F)) :
    coordAt v ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∩ slab v B = box B := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, slab, box, Set.mem_ofPred_eq, coordAt]
  constructor
  · rintro ⟨hv, hB, hw⟩
    refine ⟨hB, fun w => ?_⟩
    by_cases h : w = v
    · subst h; exact hv
    · exact hw w h
  · rintro ⟨hB, hw⟩
    exact ⟨hw v, hB, fun w _ => hw w⟩

-- pin: isCompact_box (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3305)
theorem isCompact_box {B : Set (InfiniteAdeleRing F)} (hB : IsCompact B) : IsCompact (box (F := F) B) := by
  have h := hB.prod (isCompact_integralFiniteAdeles (𝓞 F) F)
  exact h

-- pin: isOpen_openBox (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3309)
theorem isOpen_openBox (B : Set (InfiniteAdeleRing F)) :
    IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
      ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B} :=
    isOpen_interior.preimage (continuous_adeleArch (𝓞 F) F)
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

-- pin: isOpen_openSlab (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3319)
theorem isOpen_openSlab (B : Set (InfiniteAdeleRing F)) :
    IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B} :=
    isOpen_interior.preimage (continuous_adeleArch (𝓞 F) F)
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} := by
    have h := RestrictedProduct.isOpen_forall_imp_mem
      (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      Fact.out (p := fun w => w ≠ v)
    exact h.preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

section Measure

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

-- pin: slabPush (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3338)
def slabPush (μ : Measure (AdeleRing (𝓞 F) F)) (B : Set (InfiniteAdeleRing F)) : Measure (v.adicCompletion F) :=
  Measure.map (coordAt v) (μ.restrict (slab v B))

-- pin: slabPush_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3341)
theorem slabPush_apply (μ : Measure (AdeleRing (𝓞 F) F)) (B : Set (InfiniteAdeleRing F))
    {E : Set (v.adicCompletion F)} (hE : MeasurableSet E) :
    slabPush v μ B E = μ (coordAt v ⁻¹' E ∩ slab v B) := by
  rw [slabPush, Measure.map_apply (continuous_coordAt v).measurable hE,
    Measure.restrict_apply ((continuous_coordAt v).measurable hE)]

-- pin: isAddLeftInvariant_slabPush (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3347)
theorem isAddLeftInvariant_slabPush (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddLeftInvariant]
    (B : Set (InfiniteAdeleRing F)) : (slabPush v μ B).IsAddLeftInvariant := by
  refine (forall_measure_preimage_add_iff _).mp fun c E hE => ?_
  rw [slabPush_apply v μ B hE, slabPush_apply v μ B (measurable_const_add c hE),
    ← preimage_adeleSingle_add_coordAt v c E]
  conv_lhs => rw [← preimage_adeleSingle_add_slab v B c]
  rw [← Set.preimage_inter]
  exact measure_preimage_add μ (adeleSingle v c) _

-- pin: slabPush_integers_lt_top (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3356)
theorem slabPush_integers_lt_top (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    {B : Set (InfiniteAdeleRing F)} (hB : IsCompact B) :
    slabPush v μ B (v.adicCompletionIntegers F : Set (v.adicCompletion F)) < ∞ := by
  rw [slabPush_apply v μ B (isClosed_adicCompletionIntegers v).measurableSet,
    coordAt_preimage_integers_inter_slab]
  exact (isCompact_box hB).measure_lt_top

set_option linter.style.haveILetI false in
-- The `haveI := isAddLeftInvariant_slabPush` is a load-bearing instance argument
-- for `measure_vadd` below, so the style linter is disabled for this declaration.
-- pin: isFiniteMeasureOnCompacts_slabPush (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3363)
theorem isFiniteMeasureOnCompacts_slabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    [μ.IsAddLeftInvariant] {B : Set (InfiniteAdeleRing F)} (hB : IsCompact B) :
    IsFiniteMeasureOnCompacts (slabPush v μ B) := by
  haveI := isAddLeftInvariant_slabPush v μ B
  refine ⟨fun K hK => ?_⟩
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := NumberField.isOpenAdicCompletionIntegers F v
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : v.adicCompletion F => c +ᵥ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun c => hO.vadd c)
    (fun c hc => Set.mem_iUnion.mpr ⟨c, Set.mem_vadd_set.mpr ⟨0, zero_mem _, by simp⟩⟩)
  calc slabPush v μ B K
      ≤ slabPush v μ B (⋃ c ∈ t, c +ᵥ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := measure_mono ht
    _ ≤ ∑ c ∈ t, slabPush v μ B (c +ᵥ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
        measure_biUnion_finset_le t _
    _ = ∑ _c ∈ t, slabPush v μ B (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact measure_vadd _ c _
    _ < ∞ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (slabPush_integers_lt_top v μ hB)

-- pin: isOpenPosMeasure_slabPush (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3384)
theorem isOpenPosMeasure_slabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsOpenPosMeasure μ]
    {B : Set (InfiniteAdeleRing F)} (hB : (interior B).Nonempty) : IsOpenPosMeasure (slabPush v μ B) := by
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨c, hc⟩ := hne
  obtain ⟨b, hb⟩ := hB
  rw [slabPush_apply v μ B hU.measurableSet]
  have hsub : {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
      ∩ coordAt v ⁻¹' U ⊆ coordAt v ⁻¹' U ∩ slab v B := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, interior_subset h1, h2⟩
  have hopen : IsOpen ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
      ∩ coordAt v ⁻¹' U) :=
    (isOpen_openSlab v B).inter (hU.preimage (continuous_coordAt v))
  have hne' : ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
      ∩ coordAt v ⁻¹' U).Nonempty := by
    refine ⟨((b, finSingle v c) : AdeleRing (𝓞 F) F), ⟨hb, fun w hw => ?_⟩, ?_⟩
    · show (finSingle v c : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F
      rw [finSingle_apply_of_ne v c hw]
      exact zero_mem _
    · show (finSingle v c : FiniteAdeleRing (𝓞 F) F) v ∈ U
      rw [finSingle_apply_self]
      exact hc
  exact ne_of_gt (lt_of_lt_of_le (hopen.measure_pos μ hne') (measure_mono hsub))

end Measure

-- pin: embUnit_val_mul_fst (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3414)
theorem embUnit_val_mul_fst (t : (v.adicCompletion F)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 = x.1 := by
  show ((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 * x.1 = x.1
  rw [embUnit_val_fst, one_mul]

-- pin: embUnit_val_mul_snd_apply_self (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3419)
theorem embUnit_val_mul_snd_apply_self (t : (v.adicCompletion F)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) v
      = (t : v.adicCompletion F) * (x.2 : FiniteAdeleRing (𝓞 F) F) v := by
  show ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
      * (x.2 : FiniteAdeleRing (𝓞 F) F) v = _
  rw [localUnit_apply_self]

-- pin: embUnit_val_mul_snd_apply_of_ne (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3426)
theorem embUnit_val_mul_snd_apply_of_ne (t : (v.adicCompletion F)ˣ) (x : AdeleRing (𝓞 F) F)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) w
      = (x.2 : FiniteAdeleRing (𝓞 F) F) w := by
  show ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w
      * (x.2 : FiniteAdeleRing (𝓞 F) F) w = _
  rw [localUnit_apply_of_ne (𝓞 F) F v t hw, one_mul]

-- pin: embUnit_smul_box (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3434)
theorem embUnit_smul_box (t : (v.adicCompletion F)ˣ) (B : Set (InfiniteAdeleRing F)) :
    (embUnit v t) • box (F := F) B
      = coordAt v ⁻¹' ((t : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∩ slab v B := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxB, hxint⟩, rfl⟩
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · show (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) v
        ∈ (t : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      rw [embUnit_val_mul_snd_apply_self]
      exact Set.smul_mem_smul_set (hxint v)
    · show (((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 ∈ B
      rw [embUnit_val_mul_fst]; exact hxB
    · show (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) w
        ∈ w.adicCompletionIntegers F
      rw [embUnit_val_mul_snd_apply_of_ne v t x hw]; exact hxint w
  · rintro ⟨hv, hB, hw⟩
    obtain ⟨z, hz, hvz⟩ := Set.mem_smul_set.mp hv
    refine ⟨(embUnit v t⁻¹) • y, ⟨?_, fun w => ?_⟩, ?_⟩
    · show (((embUnit v t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 ∈ B
      rw [embUnit_val_mul_fst]; exact hB
    · by_cases hwv : w = v
      · subst hwv
        show (((((embUnit w t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).2 : FiniteAdeleRing (𝓞 F) F)) w
          ∈ w.adicCompletionIntegers F
        rw [embUnit_val_mul_snd_apply_self]
        have hyv : (y.2 : FiniteAdeleRing (𝓞 F) F) w = (t : w.adicCompletion F) * z := by
          show coordAt w y = (t : w.adicCompletion F) * z
          rw [← hvz]; rfl
        rw [hyv, ← mul_assoc, Units.inv_mul, one_mul]
        exact hz
      · show (((((embUnit v t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).2 : FiniteAdeleRing (𝓞 F) F)) w
          ∈ w.adicCompletionIntegers F
        rw [embUnit_val_mul_snd_apply_of_ne v t⁻¹ y hwv]; exact hw w hwv
    · show (embUnit v t) • ((embUnit v t⁻¹) • y) = y
      rw [map_inv, smul_inv_smul]

set_option linter.style.haveILetI false in
-- The five `haveI`s below are load-bearing instance arguments for
-- `measure_smul_integers`, `regular_of_isAddLeftInvariant` and
-- `distribHaarChar_eq_of_measure_smul_eq_mul`; `have` would drop them from
-- instance search, so the style linter is disabled for this declaration.
-- pin: distribHaarChar_embUnit (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3471)
theorem distribHaarChar_embUnit (t : (v.adicCompletion F)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (embUnit v t)
      = ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-(ordAt v t)) := by
  borelize (AdeleRing (𝓞 F) F)
  borelize (v.adicCompletion F)
  obtain ⟨B⟩ : Nonempty (PositiveCompacts (InfiniteAdeleRing F)) := inferInstance
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀ with hμ
  have hBc : IsCompact (B : Set (InfiniteAdeleRing F)) := B.isCompact
  have hBi : (interior (B : Set (InfiniteAdeleRing F))).Nonempty := B.interior_nonempty
  have hs_top : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ ∞ := (isCompact_box hBc).measure_lt_top.ne
  have hs0 : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ 0 := by
    obtain ⟨b, hb⟩ := hBi
    have hsub : {x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
        ⊆ box (F := F) (B : Set (InfiniteAdeleRing F)) := fun x hx => ⟨interior_subset hx.1, hx.2⟩
    have hne : ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}).Nonempty :=
      ⟨((b, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F), hb, fun w => zero_mem _⟩
    exact ne_of_gt (lt_of_lt_of_le ((isOpen_openBox (F := F) _).measure_pos μ hne) (measure_mono hsub))
  haveI := isAddLeftInvariant_slabPush v μ (B : Set (InfiniteAdeleRing F))
  haveI := isFiniteMeasureOnCompacts_slabPush v μ hBc
  haveI := isOpenPosMeasure_slabPush v μ hBi
  haveI : (slabPush v μ (B : Set (InfiniteAdeleRing F))).IsAddHaarMeasure := {}
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := NumberField.isOpenAdicCompletionIntegers F v
  haveI : (slabPush v μ (B : Set (InfiniteAdeleRing F))).Regular :=
    Measure.regular_of_isAddLeftInvariant (NumberField.isCompactAdicCompletionIntegers F v)
      (by rw [hO.interior_eq]; exact ⟨0, zero_mem _⟩) (slabPush_integers_lt_top v μ hBc).ne
  have hlam := NumberField.TateGlobal.LocalHaarModulus.measure_smul_integers (slabPush v μ (B : Set (InfiniteAdeleRing F))) t
  rw [slabPush_apply v μ _ ((hO.smul₀ t.ne_zero).measurableSet),
    slabPush_apply v μ _ (isClosed_adicCompletionIntegers v).measurableSet,
    coordAt_preimage_integers_inter_slab] at hlam
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hs0 hs_top ?_
  rw [embUnit_smul_box]
  exact hlam

-- pin: distribHaarChar_embUnit_eq_local (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3507)
theorem distribHaarChar_embUnit_eq_local (t : (v.adicCompletion F)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (embUnit v t) = distribHaarChar (v.adicCompletion F) t := by
  rw [distribHaarChar_embUnit, NumberField.TateGlobal.LocalHaarModulus.distribHaarChar_adicCompletion]
  rfl

-- pin: distribHaarChar_eq_one_of_integral (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3512)
theorem distribHaarChar_eq_one_of_integral {g : (AdeleRing (𝓞 F) F)ˣ} (h1 : ((g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1)
    (hint : ∀ w : HeightOneSpectrum (𝓞 F), ((g : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F)
    (hint' : ∀ w : HeightOneSpectrum (𝓞 F), (((g⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w
      ∈ w.adicCompletionIntegers F) :
    distribHaarChar (AdeleRing (𝓞 F) F) g = 1 := by
  borelize (AdeleRing (𝓞 F) F)
  obtain ⟨B⟩ : Nonempty (PositiveCompacts (InfiniteAdeleRing F)) := inferInstance
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀ with hμ
  have hBc : IsCompact (B : Set (InfiniteAdeleRing F)) := B.isCompact
  have hs_top : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ ∞ := (isCompact_box hBc).measure_lt_top.ne
  have hs0 : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ 0 := by
    obtain ⟨b, hb⟩ := B.interior_nonempty
    have hsub : {x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
        ⊆ box (F := F) (B : Set (InfiniteAdeleRing F)) := fun x hx => ⟨interior_subset hx.1, hx.2⟩
    have hne : ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}).Nonempty :=
      ⟨((b, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F), hb, fun w => zero_mem _⟩
    exact ne_of_gt (lt_of_lt_of_le ((isOpen_openBox (F := F) _).measure_pos μ hne) (measure_mono hsub))
  have h1' : (((g⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1 = 1 := inv_val_fst_eq_one g h1
  have hfix : ∀ (k : (AdeleRing (𝓞 F) F)ˣ), ((k : AdeleRing (𝓞 F) F).1 = 1) →
      (∀ w : HeightOneSpectrum (𝓞 F), ((k : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F) →
      ∀ x ∈ box (F := F) (B : Set (InfiniteAdeleRing F)), k • x ∈ box (F := F) (B : Set (InfiniteAdeleRing F)) := by
    intro k hk1 hkint x hx
    refine ⟨?_, fun w => ?_⟩
    · show ((k : AdeleRing (𝓞 F) F).1 * x.1) ∈ (B : Set (InfiniteAdeleRing F))
      rw [hk1, one_mul]; exact hx.1
    · show ((k : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w * (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ _
      exact mul_mem (hkint w) (hx.2 w)
  have hset : g • box (F := F) (B : Set (InfiniteAdeleRing F)) = box (F := F) (B : Set (InfiniteAdeleRing F)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hfix g h1 hint x hx
    · intro hy
      exact ⟨g⁻¹ • y, hfix g⁻¹ h1' hint' y hy, smul_inv_smul g y⟩
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hs0 hs_top ?_
  rw [hset, ENNReal.coe_one, one_mul]

end LG

end NumberField.TateGlobal

end

end Fold_LocalGlobalModulus
