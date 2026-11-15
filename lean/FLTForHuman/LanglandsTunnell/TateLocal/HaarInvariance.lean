/-
  Invariance of the additive Haar measure of a local field under inversion: `∫ f x⁻¹ = ∫ |modulus u|⁻² • f u`,
  with the modulus and unit-scaling lemmas it rests on.

  spec-pin: P2M/Sol/S_LanglandsTunnell_TateLocal_integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion.lean

  The declarations are the pin's, transcribed verbatim, and so are their telescopes: `measure_smul_units`,
  `lintegral_comp_smul_units`, `rho_smul` and `integral_comp_inv` all carry the pin's
  `[μ.IsAddHaarMeasure] [μ.Regular]` pair. Both binders give `IsFiniteMeasureOnCompacts μ`, so the pair
  overlaps, and v4.34's `linter.overlappingInstances` reports it on `integral_comp_inv` (its suggestion:
  drop `[μ.Regular]`). The binder list is the frozen statement — it is the checker's wire and the pin's own
  spelling — so neither binder can be dropped or `omit`ted: the warning is silenced on that one
  declaration, with `set_option linter.overlappingInstances false in`, rather than by repairing the
  statement. Nothing else in the module needs a silencer.
-/
import FLTForHuman.LanglandsTunnell.TateLocalZeta
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.AdeleRing
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.GroupWithZero

set_option autoImplicit false

noncomputable section

open MeasureTheory Topology LanglandsTunnell.TateLocal NumberField IsDedekindDomain
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell.TateLocal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K]

theorem modulus_units (c : Kˣ) : modulus (c : K) = distribHaarChar K c := by
  unfold modulus
  rw [dite_eq_right c.ne_zero, Units.mk0_val]

theorem modulus_inv (x : K) : modulus x⁻¹ = (modulus x)⁻¹ := by
  by_cases hx : x = 0
  · subst hx
    simp [modulus]
  · have h1 : modulus x * modulus x⁻¹ = 1 := by
      rw [← modulus_mul, mul_inv_cancel₀ hx]
      unfold modulus
      rw [dite_eq_right one_ne_zero]
      have : Units.mk0 (1 : K) one_ne_zero = 1 := Units.ext rfl
      rw [this, map_one]
    have hne : modulus x ≠ 0 := (modulus_pos hx).ne'
    calc modulus x⁻¹ = (modulus x)⁻¹ * (modulus x * modulus x⁻¹) := by
          rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      _ = (modulus x)⁻¹ := by rw [h1, mul_one]

variable [MeasurableSpace K] [BorelSpace K]

theorem measure_smul_units (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (c : Kˣ) (s : Set K) :
    μ ((c : K) • s) = modulus (c : K) * μ s := by
  rw [modulus_units]
  exact (distribHaarChar_mul μ c s).symm

theorem lintegral_comp_smul_units (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (c : Kˣ)
    (g : K → ℝ≥0∞) :
    ∫⁻ x, g ((c : K) • x) ∂μ = (modulus (c : K) : ℝ≥0∞)⁻¹ * ∫⁻ x, g x ∂μ := by
  have hc : (c : K) ≠ 0 := c.ne_zero
  let e : K ≃ᵐ K := MeasurableEquiv.smul₀ (c : K) hc
  have hmap : Measure.map e μ = (modulus (c : K) : ℝ≥0∞)⁻¹ • μ := by
    ext s hs
    rw [Measure.map_apply e.measurable hs, Measure.smul_apply, smul_eq_mul]
    have hpre : e ⁻¹' s = ((c⁻¹ : Kˣ) : K) • s := by
      ext x
      simp only [Set.mem_preimage]
      constructor
      · intro hx
        refine ⟨(c : K) • x, hx, ?_⟩
        simp [hc]
      · rintro ⟨y, hy, rfl⟩
        show (c : K) • (((c⁻¹ : Kˣ) : K) • y) ∈ s
        simpa [smul_smul, hc] using hy
    rw [hpre, measure_smul_units μ c⁻¹ s, Units.val_inv_eq_inv_val, modulus_inv, ENNReal.coe_inv (modulus_pos hc).ne']
  have := lintegral_map_equiv g e (μ := μ)
  rw [hmap] at this
  simp only [lintegral_smul_measure, smul_eq_mul] at this
  exact this.symm

variable (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]

noncomputable def dens (x : K) : ℝ≥0∞ := ((modulus x)⁻¹ : ℝ≥0)

theorem measurable_dens (hmod : Continuous (modulus : K → ℝ≥0)) : Measurable (dens : K → ℝ≥0∞) := by
  unfold dens
  exact (hmod.measurable.inv).coe_nnreal_ennreal

theorem rho_smul (c : Kˣ) (s : Set K) (hs : MeasurableSet s) :
    μ.withDensity dens ((c : K) • s) = μ.withDensity dens s := by
  have hc : (c : K) ≠ 0 := c.ne_zero
  have hcs : MeasurableSet ((c : K) • s) := hs.const_smul_of_ne_zero hc
  rw [withDensity_apply _ hcs, withDensity_apply _ hs, ← lintegral_indicator hcs, ← lintegral_indicator hs]
  have key := lintegral_comp_smul_units μ c (((c : K) • s).indicator dens)
  have hind : ∀ x : K, ((c : K) • s).indicator dens ((c : K) • x)
      = (modulus (c : K) : ℝ≥0∞)⁻¹ * s.indicator dens x := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.smul_mem_smul_set hx)]
      unfold dens
      rw [smul_eq_mul, modulus_mul, mul_inv, ENNReal.coe_mul, ENNReal.coe_inv (modulus_pos hc).ne']
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem, mul_zero]
      intro h
      apply hx
      obtain ⟨y, hy, hxy⟩ := h
      have : y = x := by
        have := congrArg (fun z => (c : K)⁻¹ • z) hxy
        simpa [smul_smul, hc] using this
      rwa [← this]
  simp_rw [hind] at key
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr (modulus_pos hc).ne'))] at key
  have hne : (modulus (c : K) : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  have hne' : (modulus (c : K) : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (ENNReal.coe_ne_zero.mpr (modulus_pos hc).ne')
  exact ((ENNReal.mul_right_inj hne hne').mp key).symm

set_option linter.overlappingInstances false in
theorem integral_comp_inv [T2Space K] [SecondCountableTopology K]
    (hmod : Continuous (modulus : K → ℝ≥0)) (h0 : μ {0} = 0) (f : K → ℂ) :
    ∫ x, f x⁻¹ ∂μ = ∫ u, ((((modulus u : ℝ≥0) : ℝ) ^ 2)⁻¹ : ℝ) • f u ∂μ := by
  classical

  let : MeasurableSpace Kˣ := borel Kˣ
  have : BorelSpace Kˣ := ⟨rfl⟩
  have : SecondCountableTopology Kˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hrange : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, rfl⟩; exact u.ne_zero
    · intro hx; exact ⟨Units.mk0 x hx, rfl⟩
  have hopen : IsOpenEmbedding (Units.val : Kˣ → K) :=
    ⟨Units.isEmbedding_val₀, by rw [hrange]; exact isOpen_compl_singleton⟩
  have hval : MeasurableEmbedding (Units.val : Kˣ → K) := hopen.measurableEmbedding
  have : TopologicalSpace.PseudoMetrizableSpace Kˣ := Units.isEmbedding_val₀.isInducing.pseudoMetrizableSpace
  set ρ : Measure K := μ.withDensity dens with hρ
  have hdm : Measurable (dens : K → ℝ≥0∞) := measurable_dens hmod
  set ν : Measure Kˣ := Measure.comap Units.val ρ with hν
  have hνapp : ∀ s : Set Kˣ, ν s = ρ (Units.val '' s) := fun s => hval.comap_apply ρ s

  have : ν.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, hνapp, hνapp]
    have himg : Units.val '' ((fun x => g * x) ⁻¹' s) = ((g⁻¹ : Kˣ) : K) • (Units.val '' s) := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨(g * u : Kˣ), ⟨g * u, hu, rfl⟩, ?_⟩
        simp [smul_eq_mul]
      · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
        refine ⟨g⁻¹ * w, ?_, ?_⟩
        · show g * (g⁻¹ * w) ∈ s
          simpa using hw
        · simp [smul_eq_mul]
    rw [himg]
    exact rho_smul μ g⁻¹ _ (hval.measurableSet_image.mpr hs)
  have : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun k hk => ?_⟩
    rw [hνapp]
    have hk' : IsCompact (Units.val '' k) := hk.image Units.continuous_val
    have hk0 : ∀ x ∈ Units.val '' k, x ≠ 0 := by
      rintro _ ⟨u, -, rfl⟩; exact u.ne_zero

    have hcont : ContinuousOn (fun x : K => ((modulus x)⁻¹ : ℝ≥0)) (Units.val '' k) := by
      refine ContinuousOn.inv₀ hmod.continuousOn ?_
      intro x hx
      exact (modulus_pos (hk0 x hx)).ne'
    obtain ⟨M, hM⟩ := hk'.bddAbove_image hcont
    have hle : ∀ x ∈ Units.val '' k, dens x ≤ (M : ℝ≥0∞) := by
      intro x hx
      unfold dens
      exact ENNReal.coe_le_coe.mpr (hM ⟨x, hx, rfl⟩)
    calc ρ (Units.val '' k) = ∫⁻ x in Units.val '' k, dens x ∂μ := withDensity_apply _ hk'.measurableSet
      _ ≤ ∫⁻ x in Units.val '' k, (M : ℝ≥0∞) ∂μ := setLIntegral_mono measurable_const hle
      _ = (M : ℝ≥0∞) * μ (Units.val '' k) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hk'.measure_lt_top
  have : ν.IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [hνapp]
    have hU' : IsOpen (Units.val '' U) := hopen.isOpenMap U hU
    have hne' : (Units.val '' U).Nonempty := hne.image _
    intro h0'
    rw [withDensity_apply _ hU'.measurableSet] at h0'
    have hae : ∀ᵐ x ∂(μ.restrict (Units.val '' U)), dens x = 0 :=
      (lintegral_eq_zero_iff hdm).mp h0'
    have hpos : ∀ x ∈ Units.val '' U, dens x ≠ 0 := by
      rintro _ ⟨u, -, rfl⟩
      unfold dens
      exact ENNReal.coe_ne_zero.mpr (inv_ne_zero (modulus_pos u.ne_zero).ne')
    have : μ (Units.val '' U) = 0 := by
      rw [ae_restrict_iff' hU'.measurableSet, ae_iff] at hae
      have hsub : Units.val '' U ⊆ {x | ¬ (x ∈ Units.val '' U → dens x = 0)} :=
        fun x hx h => hpos x hx (h hx)
      exact measure_mono_null hsub hae
    exact (hU'.measure_pos μ hne').ne' this
  have : ν.IsHaarMeasure := {}
  have : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  have : ν.IsInvInvariant := Measure.IsHaarMeasure.isInvInvariant_of_regular ν

  have hρ0 : ρ {0} = 0 := by
    rw [hρ, withDensity_apply _ (measurableSet_singleton 0), lintegral_singleton]
    simp [dens, modulus]
  have hρinv : Measure.map Inv.inv ρ = ρ := by
    ext A hA
    rw [Measure.map_apply measurable_inv hA]

    have hsplit : ∀ B : Set K, MeasurableSet B → ρ B = ν (Units.val ⁻¹' B) := by
      intro B hB
      rw [hνapp, Set.image_preimage_eq_inter_range, hrange]
      have : ρ (B ∩ {0}ᶜ) = ρ B := by
        apply measure_inter_conull
        rwa [compl_compl]
      rw [this]
    rw [hsplit _ (measurable_inv hA), hsplit _ hA]
    have hpre : Units.val ⁻¹' (Inv.inv ⁻¹' A) = Inv.inv ⁻¹' (Units.val ⁻¹' A : Set Kˣ) := by
      ext u
      simp [Units.val_inv_eq_inv_val]
    rw [hpre, Measure.measure_preimage_inv]

  let dens2 : K → ℝ≥0 := fun u => ((modulus u)⁻¹) ^ 2
  have hd2m : Measurable dens2 := (hmod.measurable.inv).pow_const 2
  have hmodm : Measurable (fun x : K => (modulus x : ℝ≥0∞)) := hmod.measurable.coe_nnreal_ennreal
  have hμρ : μ = ρ.withDensity (fun x => (modulus x : ℝ≥0∞)) := by
    rw [hρ, ← withDensity_mul _ hdm hmodm]
    have hprod : (dens * fun x => (modulus x : ℝ≥0∞)) = ({(0 : K)}ᶜ : Set K).indicator 1 := by
      funext x
      by_cases hx : x = 0
      · subst hx; simp [dens, modulus]
      · rw [Set.indicator_of_mem (by simpa using hx)]
        simp only [Pi.mul_apply, Pi.one_apply, dens]
        rw [← ENNReal.coe_mul, inv_mul_cancel₀ (modulus_pos hx).ne', ENNReal.coe_one]
    rw [hprod, withDensity_indicator_one (measurableSet_singleton 0).compl, Measure.restrict_eq_self_of_ae_mem]
    rw [ae_iff]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not, Set.ofPred_eq_eq_singleton]
    exact h0
  have hmapd : Measure.map Inv.inv μ = μ.withDensity (fun u => (dens2 u : ℝ≥0∞)) := by
    ext A hA
    rw [Measure.map_apply measurable_inv hA]
    conv_lhs => rw [hμρ]
    rw [withDensity_apply _ (measurable_inv hA), ← lintegral_indicator (measurable_inv hA)]

    have hsub := lintegral_map_equiv ((Inv.inv ⁻¹' A).indicator fun x => (modulus x : ℝ≥0∞))
      (MeasurableEquiv.inv K) (μ := ρ)
    rw [show ((MeasurableEquiv.inv K : K ≃ᵐ K) : K → K) = Inv.inv from rfl, hρinv] at hsub
    rw [hsub]
    have hind : ∀ x : K, (Inv.inv ⁻¹' A).indicator (fun x => (modulus x : ℝ≥0∞)) x⁻¹
        = A.indicator (fun x => (modulus x⁻¹ : ℝ≥0∞)) x := by
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
        show x⁻¹⁻¹ ∈ A
        rwa [inv_inv]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        show ¬ x⁻¹⁻¹ ∈ A
        rwa [inv_inv]
    simp_rw [hind]
    have hg : Measurable fun x : K => (modulus x⁻¹ : ℝ≥0∞) := hmodm.comp measurable_inv
    rw [lintegral_indicator hA, hρ, setLIntegral_withDensity_eq_setLIntegral_mul _ hdm hg hA,
      withDensity_apply _ hA]
    refine setLIntegral_congr_fun hA (fun x _ => ?_)
    simp only [Pi.mul_apply, dens, dens2, modulus_inv]
    rw [← ENNReal.coe_mul, ← pow_two]

  calc ∫ x, f x⁻¹ ∂μ = ∫ y, f y ∂(Measure.map (MeasurableEquiv.inv K) μ) :=
        (integral_map_equiv (MeasurableEquiv.inv K) f).symm
    _ = ∫ y, f y ∂(μ.withDensity (fun u => (dens2 u : ℝ≥0∞))) := by
        rw [show ((MeasurableEquiv.inv K : K ≃ᵐ K) : K → K) = Inv.inv from rfl, hmapd]
    _ = ∫ u, (dens2 u) • f u ∂μ := integral_withDensity_eq_integral_smul hd2m f
    _ = ∫ u, ((((modulus u : ℝ≥0) : ℝ) ^ 2)⁻¹ : ℝ) • f u ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
        simp only [dens2, NNReal.smul_def, NNReal.coe_pow, NNReal.coe_inv, inv_pow]


/-- The row's statement: inversion invariance specialized to a completed nonarchimedean place, without
the two local hypotheses of `integral_comp_inv` (continuity of the modulus and the vanishing of `μ {0}`),
both of which the completion supplies.  This is the pin's `solution` wrapper (`S_…:269–304`). -/
theorem integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (f : v.adicCompletion F → ℂ) :
    ∫ x, f x⁻¹ ∂μ
      = ∫ u, ((((LanglandsTunnell.TateLocal.modulus u : ℝ≥0) : ℝ) ^ 2)⁻¹ : ℝ) • f u ∂μ := by
  have hmod_eq : (LanglandsTunnell.TateLocal.modulus : v.adicCompletion F → ℝ≥0) = fun x => ‖x‖₊ :=
    funext fun x => NumberField.TateGlobal.modulus_adicCompletion_eq_nnnorm (v := v) x
  have hmod : Continuous (LanglandsTunnell.TateLocal.modulus : v.adicCompletion F → ℝ≥0) := by
    rw [hmod_eq]; exact continuous_nnnorm

  have h0 : μ {(0 : v.adicCompletion F)} = 0 := by
    obtain ⟨x, hx0, hx1⟩ : ∃ x : v.adicCompletion F, x ≠ 0 ∧ ‖x‖ < 1 := by
      obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
      refine ⟨NumberField.FinitePlace.embedding v (algebraMap _ F π), ?_, ?_⟩
      · exact map_ne_zero_iff _ (RingHom.injective _) |>.mpr
          ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hπ0)
      · exact (NumberField.FinitePlace.norm_lt_one_iff_mem (K := F) v π).mpr hπ
    have hsm : ((Units.mk0 x hx0 : (v.adicCompletion F)ˣ) : v.adicCompletion F) •
        ({0} : Set (v.adicCompletion F)) = {0} := by
      simp
    have := measure_smul_units μ (Units.mk0 x hx0) {0}
    rw [hsm, Units.val_mk0] at this
    have hm1 : (LanglandsTunnell.TateLocal.modulus x : ℝ≥0∞) ≠ 1 := by
      rw [hmod_eq]
      intro h
      have : ‖x‖₊ = 1 := by exact_mod_cast h
      rw [← coe_nnnorm, this] at hx1
      norm_num at hx1
    have hfin : μ {(0 : v.adicCompletion F)} ≠ ⊤ :=
      (isCompact_singleton.measure_lt_top (μ := μ)).ne
    by_contra hne
    have h2 : (LanglandsTunnell.TateLocal.modulus x : ENNReal) * μ {(0 : v.adicCompletion F)}
        = 1 * μ {(0 : v.adicCompletion F)} := by
      rw [one_mul]; exact this.symm
    exact hm1 ((ENNReal.mul_left_inj hne hfin).mp h2)
  exact integral_comp_inv μ hmod h0 f

end LanglandsTunnell.TateLocal

end
