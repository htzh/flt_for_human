/-
  The archimedean slab: `archCoord`/`archSingle`, `archSlab`/`archBox`, the
  pushed-forward Haar `archSlabPush`, the central unit `archCentralUnit`, and the
  archimedean part of the assembly character
  (`distribHaarChar_archCentralUnit`/`_archUnitHom`).

  Transcribed from the pin's `Fold_ArchLocalGlobalModulus` section (the
  `NumberField.TateGlobal` `LGArch`/`Measure` blocks), declared lines 3587-3931 of
  file A, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped; no file-wide option
  beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.FiniteSlab

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal

section Fold_ArchLocalGlobalModulus



open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

section LGArch

variable (w : InfinitePlace F)

-- pin: archCoord (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3587)
def archCoord (x : AdeleRing (𝓞 F) F) : w.Completion := x.1 w

-- pin: continuous_archCoord (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3589)
theorem continuous_archCoord : Continuous (archCoord (F := F) w) := by
  show Continuous fun x : AdeleRing (𝓞 F) F => (fun y : InfiniteAdeleRing F => y w) (adeleArch (𝓞 F) F x)
  exact (continuous_apply w).comp (continuous_adeleArch (𝓞 F) F)

open scoped Classical in
-- pin: archSingle (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3594)
def archSingle (c : w.Completion) : AdeleRing (𝓞 F) F :=
  ((Function.update (0 : InfiniteAdeleRing F) w c), (0 : FiniteAdeleRing (𝓞 F) F))

open scoped Classical in
-- pin: archCoord_archSingle_add (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3598)
theorem archCoord_archSingle_add (c : w.Completion) (x : AdeleRing (𝓞 F) F) :
    archCoord w (archSingle w c + x) = c + archCoord w x := by
  show Function.update (0 : InfiniteAdeleRing F) w c w + x.1 w = c + x.1 w
  -- `InfiniteAdeleRing` is a `def`, not an `abbrev`: the pin's
  -- `rw [Function.update_self]` needs its function argument ascribed at the
  -- unfolded `Pi` type, and this `rfl` rewrite is that ascription.
  rw [show Function.update (0 : InfiniteAdeleRing F) w c
      = Function.update (0 : (a : InfinitePlace F) → a.Completion) w c from rfl]
  rw [Function.update_self]

open scoped Classical in
-- pin: archSingle_add_fst_of_ne (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3604)
theorem archSingle_add_fst_of_ne (c : w.Completion) (x : AdeleRing (𝓞 F) F) {w' : InfinitePlace F}
    (hw : w' ≠ w) : (archSingle w c + x).1 w' = x.1 w' := by
  show Function.update (0 : InfiniteAdeleRing F) w c w' + x.1 w' = x.1 w'
  -- see `archCoord_archSingle_add`: ascribe the unfolded `Pi` type first
  rw [show Function.update (0 : InfiniteAdeleRing F) w c
      = Function.update (0 : (a : InfinitePlace F) → a.Completion) w c from rfl]
  rw [Function.update_of_ne hw]
  exact zero_add _

-- pin: archSingle_add_snd (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3610)
theorem archSingle_add_snd (c : w.Completion) (x : AdeleRing (𝓞 F) F) : (archSingle w c + x).2 = x.2 := by
  show (0 : FiniteAdeleRing (𝓞 F) F) + x.2 = x.2
  exact zero_add _

-- pin: archSlab (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3614)
def archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) : Set (AdeleRing (𝓞 F) F) :=
  {x | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ B w') ∧
    ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}

-- pin: archBox (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3618)
def archBox (B : (w' : InfinitePlace F) → Set (w'.Completion)) : Set (AdeleRing (𝓞 F) F) :=
  box (F := F) (Set.pi Set.univ B)

-- pin: mem_archBox_iff (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3621)
theorem mem_archBox_iff (B : (w' : InfinitePlace F) → Set (w'.Completion)) (x : AdeleRing (𝓞 F) F) :
    x ∈ archBox B ↔ (∀ w' : InfinitePlace F, x.1 w' ∈ B w') ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' => h1 w' (Set.mem_univ _), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' _ => h1 w', h2⟩

-- pin: preimage_archSingle_add_archSlab (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3630)
theorem preimage_archSingle_add_archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) (c : w.Completion) :
    (fun x => archSingle w c + x) ⁻¹' archSlab w B = archSlab w B := by
  ext x
  simp only [Set.mem_preimage, archSlab, Set.mem_ofPred_eq, archSingle_add_snd]
  refine and_congr (forall₂_congr fun w' hw => ?_) Iff.rfl
  rw [archSingle_add_fst_of_ne w c x hw]

-- pin: preimage_archSingle_add_archCoord (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3637)
theorem preimage_archSingle_add_archCoord (c : w.Completion) (E : Set (w.Completion)) :
    (fun x => archSingle w c + x) ⁻¹' (archCoord w ⁻¹' E) = archCoord w ⁻¹' ((fun y => c + y) ⁻¹' E) := by
  ext x
  simp only [Set.mem_preimage, archCoord_archSingle_add]

-- pin: archCoord_preimage_inter_archSlab (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3642)
theorem archCoord_preimage_inter_archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    archCoord w ⁻¹' (B w) ∩ archSlab w B = archBox B := by
  ext x
  rw [mem_archBox_iff]
  simp only [Set.mem_inter_iff, Set.mem_preimage, archSlab, Set.mem_ofPred_eq, archCoord]
  constructor
  · rintro ⟨hw, hB, hv⟩
    refine ⟨fun w' => ?_, hv⟩
    by_cases h : w' = w
    · subst h; exact hw
    · exact hB w' h
  · rintro ⟨hB, hv⟩
    exact ⟨hB w, fun w' _ => hB w', hv⟩

-- pin: isCompact_archBox (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3656)
theorem isCompact_archBox {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w')) :
    IsCompact (archBox (F := F) B) :=
  isCompact_box (isCompact_univ_pi hB)

-- pin: isOpen_openArchSlab (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3660)
theorem isOpen_openArchSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    IsOpen {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')} := by
    have : {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')}
        = ⋂ w' : InfinitePlace F, ⋂ (_ : w' ≠ w), archCoord w' ⁻¹' interior (B w') := by
      ext x; simp [archCoord]
    rw [this]
    exact isOpen_iInter_of_finite fun w' => isOpen_iInter_of_finite fun _ =>
      isOpen_interior.preimage (continuous_archCoord w')
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

-- pin: isOpen_openArchBox (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3675)
theorem isOpen_openArchBox (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    IsOpen {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')} := by
    have : {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')}
        = ⋂ w' : InfinitePlace F, archCoord w' ⁻¹' interior (B w') := by
      ext x; simp [archCoord]
    rw [this]
    exact isOpen_iInter_of_finite fun w' => isOpen_interior.preimage (continuous_archCoord w')
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

section Measure

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (w.Completion)] [BorelSpace (w.Completion)]

-- pin: archSlabPush (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3694)
def archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    Measure (w.Completion) :=
  Measure.map (archCoord w) (μ.restrict (archSlab w B))

-- pin: archSlabPush_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3698)
theorem archSlabPush_apply (μ : Measure (AdeleRing (𝓞 F) F)) (B : (w' : InfinitePlace F) → Set (w'.Completion))
    {E : Set (w.Completion)} (hE : MeasurableSet E) :
    archSlabPush w μ B E = μ (archCoord w ⁻¹' E ∩ archSlab w B) := by
  rw [archSlabPush, Measure.map_apply (continuous_archCoord w).measurable hE,
    Measure.restrict_apply ((continuous_archCoord w).measurable hE)]

-- pin: isAddLeftInvariant_archSlabPush (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3704)
theorem isAddLeftInvariant_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddLeftInvariant]
    (B : (w' : InfinitePlace F) → Set (w'.Completion)) : (archSlabPush w μ B).IsAddLeftInvariant := by
  refine (forall_measure_preimage_add_iff _).mp fun c E hE => ?_
  rw [archSlabPush_apply w μ B hE, archSlabPush_apply w μ B (measurable_const_add c hE),
    ← preimage_archSingle_add_archCoord w c E]
  conv_lhs => rw [← preimage_archSingle_add_archSlab w B c]
  rw [← Set.preimage_inter]
  exact measure_preimage_add μ (archSingle w c) _

-- pin: archSlabPush_self_lt_top (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3713)
theorem archSlabPush_self_lt_top (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w')) :
    archSlabPush w μ B (B w) < ∞ := by
  rw [archSlabPush_apply w μ B (hB w).measurableSet, archCoord_preimage_inter_archSlab]
  exact (isCompact_archBox hB).measure_lt_top

set_option linter.style.haveILetI false in
-- The `haveI := isAddLeftInvariant_archSlabPush` is a load-bearing instance
-- argument for the compact-cover estimate below, so the style linter is disabled.
-- pin: isFiniteMeasureOnCompacts_archSlabPush (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3719)
theorem isFiniteMeasureOnCompacts_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    [μ.IsAddLeftInvariant] {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w'))
    (hBi : (interior (B w)).Nonempty) :
    IsFiniteMeasureOnCompacts (archSlabPush w μ B) := by
  haveI := isAddLeftInvariant_archSlabPush w μ B
  obtain ⟨b₀, hb₀⟩ := hBi
  refine ⟨fun K hK => ?_⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : w.Completion => (c - b₀) +ᵥ interior (B w))
    (fun c => isOpen_interior.vadd (c - b₀))
    (fun c _ => Set.mem_iUnion.mpr ⟨c, Set.mem_vadd_set.mpr ⟨b₀, hb₀, by simp⟩⟩)
  calc archSlabPush w μ B K
      ≤ archSlabPush w μ B (⋃ c ∈ t, (c - b₀) +ᵥ interior (B w)) := measure_mono ht
    _ ≤ ∑ c ∈ t, archSlabPush w μ B ((c - b₀) +ᵥ interior (B w)) := measure_biUnion_finset_le t _
    _ ≤ ∑ c ∈ t, archSlabPush w μ B ((c - b₀) +ᵥ B w) :=
        Finset.sum_le_sum fun c _ => measure_mono (Set.vadd_set_mono interior_subset)
    _ = ∑ _c ∈ t, archSlabPush w μ B (B w) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact measure_vadd _ (c - b₀) _
    _ < ∞ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (archSlabPush_self_lt_top w μ hB)

-- pin: isOpenPosMeasure_archSlabPush (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3742)
theorem isOpenPosMeasure_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsOpenPosMeasure μ]
    {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hBi : ∀ w', (interior (B w')).Nonempty) :
    IsOpenPosMeasure (archSlabPush w μ B) := by
  classical
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨c, hc⟩ := hne
  choose b hb using hBi
  rw [archSlabPush_apply w μ B hU.measurableSet]
  have hsub : {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
      ∩ archCoord w ⁻¹' U ⊆ archCoord w ⁻¹' U ∩ archSlab w B := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, fun w' hw => interior_subset (h1 w' hw), h2⟩
  have hopen := (isOpen_openArchSlab w B).inter (hU.preimage (continuous_archCoord w))
  have hne' : ({x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
      ∩ archCoord w ⁻¹' U).Nonempty := by
    refine ⟨((Function.update b w c, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F),
      ⟨fun w' hw => ?_, fun v => zero_mem _⟩, ?_⟩
    · show Function.update b w c w' ∈ interior (B w')
      rw [Function.update_of_ne hw]
      exact hb w'
    · show Function.update b w c w ∈ U
      rw [Function.update_self]
      exact hc
  exact ne_of_gt (lt_of_lt_of_le (hopen.measure_pos μ hne') (measure_mono hsub))

end Measure

-- pin: archCentralUnit_val_mul_fst_self (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3772)
theorem archCentralUnit_val_mul_fst_self (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w = (a : w.Completion) * x.1 w := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w * x.1 w = _
  rw [archCentralUnit_fst_self]

-- pin: archCentralUnit_val_mul_fst_of_ne (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3777)
theorem archCentralUnit_val_mul_fst_of_ne (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) {w' : InfinitePlace F}
    (hw : w' ≠ w) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' = x.1 w' := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w' * x.1 w' = _
  rw [archCentralUnit_fst_of_ne w a hw, one_mul]

-- pin: archCentralUnit_val_mul_snd (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3783)
theorem archCentralUnit_val_mul_snd (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 = x.2 := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * x.2 = _
  rw [archCentralUnit_snd, one_mul]

-- pin: archCentralUnit_smul_archBox (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3788)
theorem archCentralUnit_smul_archBox (a : (w.Completion)ˣ) (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    (archCentralUnit F w a) • archBox (F := F) B = archCoord w ⁻¹' (a • B w) ∩ archSlab w B := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_archBox_iff] at hy
    obtain ⟨hB, hv⟩ := hy
    refine ⟨?_, fun w' hw => ?_, fun v => ?_⟩
    · show (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 w ∈ a • B w
      rw [archCentralUnit_val_mul_fst_self]
      exact Set.smul_mem_smul_set (hB w)
    · show (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 w' ∈ B w'
      rw [archCentralUnit_val_mul_fst_of_ne w a y hw]
      exact hB w'
    · show ((((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).2 :
          FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      rw [archCentralUnit_val_mul_snd]
      exact hv v
  · rintro ⟨hw, hB, hv⟩
    refine ⟨(archUnitHom w a⁻¹) • x, ?_, ?_⟩
    · rw [mem_archBox_iff]
      refine ⟨fun w' => ?_, fun v => ?_⟩
      · by_cases h : w' = w
        · subst h
          show (((archCentralUnit F w' a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' ∈ B w'
          rw [archCentralUnit_val_mul_fst_self]
          obtain ⟨b, hb, hbx⟩ := Set.mem_smul_set.mp hw
          have : x.1 w' = (a : w'.Completion) * b := hbx.symm
          rw [this, ← mul_assoc, Units.inv_mul, one_mul]
          exact hb
        · show (((archCentralUnit F w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' ∈ B w'
          rw [archCentralUnit_val_mul_fst_of_ne w a⁻¹ x h]
          exact hB w' h
      · show ((((archCentralUnit F w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 :
            FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
        rw [archCentralUnit_val_mul_snd]
        exact hv v
    · show (archUnitHom w a) • ((archUnitHom w a⁻¹) • x) = x
      rw [map_inv, smul_inv_smul]

set_option linter.style.haveILetI false in
-- The `haveI`s below are load-bearing instance arguments for
-- `measure_smul_integers`, `regular_of_isAddLeftInvariant` and
-- `distribHaarChar_mul`; `have` would drop them from instance search, so the
-- style linter is disabled for this declaration.
-- pin: distribHaarChar_archCentralUnit (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3829)
theorem distribHaarChar_archCentralUnit (a : (w.Completion)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (archCentralUnit F w a) = distribHaarChar (w.Completion) a := by
  borelize (AdeleRing (𝓞 F) F)
  borelize (w.Completion)
  set B : (w' : InfinitePlace F) → PositiveCompacts (w'.Completion) := fun w' => Classical.arbitrary _ with hBdef
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀ with hμ
  set Bs : (w' : InfinitePlace F) → Set (w'.Completion) := fun w' => (B w' : Set (w'.Completion)) with hBs
  have hBc : ∀ w', IsCompact (Bs w') := fun w' => (B w').isCompact
  have hBi : ∀ w', (interior (Bs w')).Nonempty := fun w' => (B w').interior_nonempty
  have hs_top : μ (archBox (F := F) Bs) ≠ ∞ := (isCompact_archBox hBc).measure_lt_top.ne
  have hs0 : μ (archBox (F := F) Bs) ≠ 0 := by
    classical
    choose b hb using hBi
    have hsub : {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (Bs w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
        ⊆ archBox (F := F) Bs := by
      intro x hx
      rw [mem_archBox_iff]
      exact ⟨fun w' => interior_subset (hx.1 w'), hx.2⟩
    have hne : ({x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (Bs w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}).Nonempty :=
      ⟨((b, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F), fun w' => hb w', fun v => zero_mem _⟩
    exact ne_of_gt (lt_of_lt_of_le ((isOpen_openArchBox (F := F) Bs).measure_pos μ hne) (measure_mono hsub))
  haveI := isAddLeftInvariant_archSlabPush w μ Bs
  haveI := isFiniteMeasureOnCompacts_archSlabPush w μ hBc (hBi w)
  haveI := isOpenPosMeasure_archSlabPush w μ hBi
  haveI : (archSlabPush w μ Bs).IsAddHaarMeasure := {}
  haveI : (archSlabPush w μ Bs).Regular :=
    Measure.regular_of_isAddLeftInvariant (hBc w) (hBi w) (archSlabPush_self_lt_top w μ hBc).ne
  have key := distribHaarChar_mul (archSlabPush w μ Bs) a (Bs w)
  rw [archSlabPush_apply w μ Bs ((hBc w).smul (a : (w.Completion)ˣ)).measurableSet,
    archSlabPush_apply w μ Bs (hBc w).measurableSet, archCoord_preimage_inter_archSlab] at key
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hs0 hs_top ?_
  rw [archCentralUnit_smul_archBox]
  exact key.symm

-- pin: distribHaarChar_archUnitHom (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3866)
theorem distribHaarChar_archUnitHom (a : (w.Completion)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (archUnitHom w a) = distribHaarChar (w.Completion) a :=
  distribHaarChar_archCentralUnit w a

end LGArch

end NumberField.TateGlobal

end

end Fold_ArchLocalGlobalModulus
