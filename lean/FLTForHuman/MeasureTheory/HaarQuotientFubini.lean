/-
  Integration on the Haar quotient: the Fubini identity for the quotient measure.

  `HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out`: integrating an `ℝ≥0∞`-valued function of the
  class of a group element over the quotient by a closed subgroup, against the quotient measure, equals
  the iterated integral of the same function against the subgroup's measure and the ambient Haar measure.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out.lean` (616 lines), with the statement
  from the wrapper of the same name.  The pin label namespace `HaarDisM65` is rectified to
  `QuotientIntegration`.

  spec-pin: Theorems/Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out.lean
  spec-pin: P2M/Sol/S_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out.lean
-/
import FLTForHuman.MeasureTheory.HaarQuotient
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

open scoped ENNReal NNReal Pointwise Topology

namespace QuotientIntegration

open HaarQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private noncomputable def orb (H : Subgroup G) (μH : Measure H) (φ : G → ℝ≥0∞) (g : G) : ℝ≥0∞ :=
  ∫⁻ x : H, φ ((x : G) * g) ∂μH

section Orbit

variable (H : Subgroup G) (μH : Measure H)

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem orb_mul_left [μH.IsMulRightInvariant] (φ : G → ℝ≥0∞) (x₀ : H) (g : G) :
    orb H μH φ ((x₀ : G) * g) = orb H μH φ g := by
  unfold orb
  have : (fun x : H => φ ((x : G) * ((x₀ : G) * g))) = fun x : H => φ (((x * x₀ : H) : G) * g) := by
    funext x
    simp [mul_assoc]
  rw [this]
  exact lintegral_mul_right_eq_self (fun x : H => φ ((x : G) * g)) x₀

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem orb_out_mk [μH.IsMulRightInvariant] (φ : G → ℝ≥0∞) (g : G) :
    orb H μH φ (Quotient.mk (MulAction.orbitRel H G) g).out = orb H μH φ g := by
  have h : (MulAction.orbitRel H G) ((Quotient.mk (MulAction.orbitRel H G) g).out) g :=
    Quotient.mk_out g
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨x₀, hx₀⟩ := h
  rw [← hx₀]
  exact orb_mul_left H μH φ x₀ g

omit [LocallyCompactSpace G] in
private theorem measurable_comp_mul {φ : G → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun p : G × H => φ ((p.2 : G) * p.1) := by
  apply hφ.comp
  have : Continuous fun p : G × H => (p.2 : G) * p.1 := by
    exact (continuous_subtype_val.comp continuous_snd).mul continuous_fst
  exact this.measurable

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem measurable_subtype_mul (g : G) : Measurable fun x : H => (x : G) * g := by
  exact (continuous_subtype_val.mul continuous_const).measurable

omit [LocallyCompactSpace G] in
private theorem measurable_orb [SFinite μH] {φ : G → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (orb H μH φ) := by
  unfold orb
  exact (measurable_comp_mul H hφ).lintegral_prod_right'

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem secondCountable_subgroup : SecondCountableTopology H := by
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

omit [BorelSpace G] in
private theorem sigmaFinite_of_isClosed (hH : IsClosed (H : Set G)) [μH.IsHaarMeasure] :
    SigmaFinite μH := by
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := secondCountable_subgroup H
  infer_instance

end Orbit

section Weight

variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

private noncomputable def E : CompactExhaustion G := CompactExhaustion.choice G

private noncomputable def M (n : ℕ) : ℝ≥0∞ :=
  μH (((↑) : H → G) ⁻¹' ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹))

private noncomputable def coef (n : ℕ) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ n * (1 + M H μH n)⁻¹

private def V (n : ℕ) : Set G := interior (E (G := G) (n + 1) : Set G)

omit [BorelSpace G] [μH.IsHaarMeasure] [μH.IsMulRightInvariant] in
private theorem weight_eq (g : G) :
    weight H μH g = ∑' n : ℕ, coef H μH n * (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) g := by
  have h : SigmaCompactSpace G ∧ WeaklyLocallyCompactSpace G := ⟨inferInstance, inferInstance⟩
  unfold weight
  rw [dite_eq_left h]
  rfl

omit [MeasurableSpace G] [BorelSpace G] in
private theorem isOpen_V (n : ℕ) : IsOpen (V (G := G) n) := by
  exact isOpen_interior

omit [MeasurableSpace G] [BorelSpace G] in
private theorem V_subset (n : ℕ) : V (G := G) n ⊆ (E (G := G) (n + 1) : Set G) := by
  exact interior_subset

include hH in
omit [BorelSpace G] [μH.IsMulRightInvariant] in
private theorem M_lt_top (n : ℕ) : M H μH n < ⊤ := by
  unfold M
  have hc : IsCompact ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹) :=
    ((E (G := G)).isCompact (n + 1)).mul ((E (G := G)).isCompact (n + 1)).inv
  have hce : Topology.IsClosedEmbedding ((↑) : H → G) := hH.isClosedEmbedding_subtypeVal
  exact (hce.isCompact_preimage hc).measure_lt_top

include hH in
omit [BorelSpace G] [μH.IsMulRightInvariant] in
private theorem coef_pos (n : ℕ) : 0 < coef H μH n := by
  unfold coef
  apply ENNReal.mul_pos
  · exact (ENNReal.pow_pos (by norm_num) n).ne'
  · apply (ENNReal.inv_pos.mpr ?_).ne'
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, (M_lt_top H hH μH n).ne⟩

omit [BorelSpace G] [μH.IsHaarMeasure] [μH.IsMulRightInvariant] in
private theorem coef_mul_M_le (n : ℕ) : coef H μH n * M H μH n ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
  unfold coef
  rw [mul_assoc]
  calc (2⁻¹ : ℝ≥0∞) ^ n * ((1 + M H μH n)⁻¹ * M H μH n)
      ≤ (2⁻¹ : ℝ≥0∞) ^ n * 1 := by
        gcongr
        calc (1 + M H μH n)⁻¹ * M H μH n ≤ (1 + M H μH n)⁻¹ * (1 + M H μH n) := by
              gcongr
              exact le_add_self
          _ ≤ 1 := ENNReal.inv_mul_le_one _
    _ = (2⁻¹ : ℝ≥0∞) ^ n := mul_one _

omit [μH.IsHaarMeasure] [μH.IsMulRightInvariant] in
private theorem measurable_weight : Measurable (weight H μH) := by
  have : weight H μH = fun g => ∑' n : ℕ,
      coef H μH n * (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) g := by
    funext g; exact weight_eq H μH g
  rw [this]
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine Measurable.iSup fun s => ?_
  exact s.measurable_fun_sum fun n _ =>
    (measurable_const.indicator (isOpen_V n).measurableSet).const_mul _

private def slice (n : ℕ) (g : G) : Set H := {x : H | (x : G) * g ∈ V (G := G) n}

omit [MeasurableSpace G] [BorelSpace G] in
private theorem isOpen_slice (n : ℕ) (g : G) : IsOpen (slice H n g) := by
  unfold slice
  exact (isOpen_V n).preimage ((continuous_subtype_val.mul continuous_const))

omit [μH.IsHaarMeasure] [μH.IsMulRightInvariant] in
private theorem orb_weight_eq (g : G) :
    orb H μH (weight H μH) g = ∑' n : ℕ, coef H μH n * μH (slice H n g) := by
  unfold orb
  have hind : ∀ n, Measurable fun x : H =>
      (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) := fun n =>
    (measurable_const.indicator (isOpen_V n).measurableSet).comp (measurable_subtype_mul H g)
  have hterm : ∀ n, Measurable fun x : H =>
      coef H μH n * (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) := fun n =>
    (hind n).const_mul _
  simp_rw [weight_eq H μH]
  rw [lintegral_tsum fun n => (hterm n).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_const_mul _ (hind n)]
  congr 1
  have : (fun x : H => (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g))
      = (slice H n g).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    unfold slice
    by_cases hx : (x : G) * g ∈ V (G := G) n
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (show x ∈ {x : H | (x : G) * g ∈ V n} from hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (show x ∉ {x : H | (x : G) * g ∈ V n} from hx)]
  rw [this, lintegral_indicator ((isOpen_slice H n g).measurableSet), setLIntegral_one]

omit [μH.IsHaarMeasure] in
private theorem measure_slice_le (n : ℕ) (g : G) : μH (slice H n g) ≤ M H μH n := by
  by_cases hne : (slice H n g).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    have hsub : slice H n g ⊆
        (fun y : H => y * x₀⁻¹) ⁻¹'
          (((↑) : H → G) ⁻¹'
            ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹)) := by
      intro x hx
      simp only [Set.mem_preimage]
      have h1 : (x : G) * g ∈ (E (G := G) (n + 1) : Set G) := V_subset n hx
      have h2 : (x₀ : G) * g ∈ (E (G := G) (n + 1) : Set G) := V_subset n hx₀
      have : ((x * x₀⁻¹ : H) : G) = ((x : G) * g) * ((x₀ : G) * g)⁻¹ := by
        push_cast
        group
      rw [this]
      exact Set.mul_mem_mul h1 (Set.inv_mem_inv.mpr h2)
    calc μH (slice H n g)
        ≤ μH ((fun y : H => y * x₀⁻¹) ⁻¹'
            (((↑) : H → G) ⁻¹'
              ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹))) :=
          measure_mono hsub
      _ = M H μH n := by
          unfold M
          rw [measure_preimage_mul_right]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, measure_empty]
    exact zero_le

omit [μH.IsHaarMeasure] in
private theorem orb_weight_le_two (g : G) : orb H μH (weight H μH) g ≤ 2 := by
  rw [orb_weight_eq H μH g]
  calc ∑' n : ℕ, coef H μH n * μH (slice H n g)
      ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        exact (mul_le_mul_right (measure_slice_le H μH n g) _).trans (coef_mul_M_le H μH n)
    _ = 2 := by
        rw [ENNReal.tsum_geometric]
        norm_num

omit [μH.IsHaarMeasure] in
private theorem orb_weight_lt_top (g : G) : orb H μH (weight H μH) g < ⊤ := by
  exact (orb_weight_le_two H μH g).trans_lt ENNReal.ofNat_lt_top

include hH in
omit [μH.IsMulRightInvariant] in
private theorem orb_weight_pos (g : G) : 0 < orb H μH (weight H μH) g := by
  rw [orb_weight_eq H μH g]

  set m := (E (G := G)).find g with hm
  have hg : g ∈ V (G := G) m := (E (G := G)).subset_interior_succ m ((E (G := G)).mem_find g)
  have h1 : (1 : H) ∈ slice H m g := by
    show ((1 : H) : G) * g ∈ V (G := G) m
    simpa using hg
  have hpos : 0 < μH (slice H m g) :=
    (isOpen_slice H m g).measure_pos μH ⟨1, h1⟩
  have hterm : 0 < coef H μH m * μH (slice H m g) :=
    ENNReal.mul_pos (coef_pos H hH μH m).ne' hpos.ne'
  exact hterm.trans_le (ENNReal.le_tsum (f := fun n => coef H μH n * μH (slice H n g)) m)

include hH in
omit [μH.IsMulRightInvariant] in
private theorem orb_weight_ne_zero (g : G) : orb H μH (weight H μH) g ≠ 0 :=
  (orb_weight_pos H hH μH g).ne'

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G]
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant] in
private theorem density_eq (g : G) :
    density H μH g = weight H μH g / orb H μH (weight H μH) g := by
  rfl

include hH in
omit [μH.IsMulRightInvariant] in
private theorem measurable_density : Measurable (density H μH) := by
  have : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  have : density H μH = fun g => weight H μH g / orb H μH (weight H μH) g := rfl
  rw [this]
  exact (measurable_weight H μH).div (measurable_orb H μH (measurable_weight H μH))

include hH in
private theorem orb_density (g : G) : orb H μH (density H μH) g = 1 := by
  have hrw : (fun x : H => density H μH ((x : G) * g))
      = fun x : H => weight H μH ((x : G) * g) * (orb H μH (weight H μH) g)⁻¹ := by
    funext x
    rw [density_eq, orb_mul_left H μH (weight H μH) x g, div_eq_mul_inv]
  have hmeas : Measurable fun x : H => weight H μH ((x : G) * g) :=
    (measurable_weight H μH).comp (measurable_subtype_mul H g)
  unfold orb
  rw [show (fun x : H => density H μH ((x : G) * g)) = _ from hrw]
  rw [lintegral_mul_const _ hmeas]
  exact ENNReal.mul_inv_cancel (orb_weight_ne_zero H hH μH g) (orb_weight_lt_top H μH g).ne

end Weight

section Inv

variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

include hH in
private theorem isInvInvariant : μH.IsInvInvariant := by
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := secondCountable_subgroup H
  constructor
  let c : ℝ≥0∞ := Measure.haarScalarFactor μH.inv μH
  have hc : μH.inv = c • μH := Measure.isMulLeftInvariant_eq_smul μH.inv μH
  have : Measure.map Inv.inv (Measure.map Inv.inv μH) = c ^ 2 • μH := by
    rw [← Measure.inv_def μH, hc, Measure.map_smul, ← Measure.inv_def μH, hc, smul_smul, pow_two]
    exact continuous_inv.measurable.aemeasurable
  have μeq : μH = c ^ 2 • μH := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at this
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id]
  have K : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have hKpos : 0 < μH K :=
    (isOpen_interior.measure_pos μH K.interior_nonempty).trans_le (measure_mono interior_subset)
  have h1 : c ^ 2 * μH K = 1 ^ 2 * μH K := by
    conv_rhs => rw [μeq]
    simp
  have h2 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj hKpos.ne' K.isCompact.measure_lt_top.ne).1 h1
  have h3 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h2
  change μH.inv = μH
  rw [hc, h3, one_smul]

end Inv

section Symmetry

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
  (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

include hH in
private theorem lintegral_mul_orb {φ β : G → ℝ≥0∞} (hφ : Measurable φ) (hβ : Measurable β) :
    ∫⁻ g, φ g * orb H μH β g ∂μ = ∫⁻ g, orb H μH φ g * β g ∂μ := by
  have : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  have : μH.IsInvInvariant := isInvInvariant H hH μH
  have hmβ : ∀ g, Measurable fun x : H => β ((x : G) * g) := fun g =>
    hβ.comp (measurable_subtype_mul H g)
  have hmφ : ∀ g, Measurable fun x : H => φ ((x : G) * g) := fun g =>
    hφ.comp (measurable_subtype_mul H g)

  have hL : ∀ g, φ g * orb H μH β g = ∫⁻ x : H, φ g * β ((x : G) * g) ∂μH := by
    intro g
    unfold orb
    exact (lintegral_const_mul (φ g) (hmβ g)).symm
  have hR : ∀ g, orb H μH φ g * β g = ∫⁻ x : H, φ ((x : G) * g) * β g ∂μH := by
    intro g
    unfold orb
    exact (lintegral_mul_const (β g) (hmφ g)).symm
  simp_rw [hL, hR]

  have hm1 : Measurable (Function.uncurry fun (g : G) (x : H) => φ g * β ((x : G) * g)) := by
    exact (hφ.comp measurable_fst).mul (measurable_comp_mul H hβ)
  have hm2 : Measurable (Function.uncurry fun (g : G) (x : H) => φ ((x : G) * g) * β g) := by
    exact (measurable_comp_mul H hφ).mul (hβ.comp measurable_fst)
  rw [lintegral_lintegral_swap hm1.aemeasurable, lintegral_lintegral_swap hm2.aemeasurable]

  have hsub : ∀ x : H, ∫⁻ g, φ g * β ((x : G) * g) ∂μ = ∫⁻ g, φ (((x⁻¹ : H) : G) * g) * β g ∂μ := by
    intro x
    have := lintegral_mul_left_eq_self (μ := μ) (fun g => φ g * β ((x : G) * g)) ((x⁻¹ : H) : G)
    rw [← this]
    refine lintegral_congr fun g => ?_
    simp [← mul_assoc]
  simp_rw [hsub]

  have := lintegral_inv_eq_self (μ := μH) (fun x : H => ∫⁻ g, φ ((x : G) * g) * β g ∂μ)
  simpa using this

end Symmetry

section Core

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
  (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

include hH in
private theorem lintegral_eq_lintegral_measure {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ q, orb H μH f q.out ∂(HaarQuotient.measure μ H μH) := by
  have : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH

  have hF : (fun q : MulAction.orbitRel.Quotient H G => orb H μH f q.out) ∘
      Quotient.mk (MulAction.orbitRel H G) = orb H μH f := by
    funext g
    exact orb_out_mk H μH f g
  have hFm : Measurable fun q : MulAction.orbitRel.Quotient H G => orb H μH f q.out := by
    rw [measurable_from_quotient]
    show Measurable ((fun q : MulAction.orbitRel.Quotient H G => orb H μH f q.out) ∘
      Quotient.mk (MulAction.orbitRel H G))
    rw [hF]
    exact measurable_orb H μH hf
  unfold HaarQuotient.measure
  rw [lintegral_map hFm (measurable_quotient_mk'' (s := MulAction.orbitRel H G))]
  show ∫⁻ g, f g ∂μ = ∫⁻ g, ((fun q : MulAction.orbitRel.Quotient H G => orb H μH f q.out) ∘
      Quotient.mk (MulAction.orbitRel H G)) g ∂(μ.withDensity (density H μH))
  rw [hF, lintegral_withDensity_eq_lintegral_mul μ (measurable_density H hH μH)
    (measurable_orb H μH hf)]
  show ∫⁻ g, f g ∂μ = ∫⁻ g, density H μH g * orb H μH f g ∂μ
  simp_rw [mul_comm (density H μH _)]
  rw [← lintegral_mul_orb μ H hH μH hf (measurable_density H hH μH)]
  simp_rw [orb_density H hH μH, mul_one]

include hH in
private theorem core (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ q, (∫⁻ x, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) :=
  lintegral_eq_lintegral_measure μ H hH μH hf

end Core

end QuotientIntegration

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ q, (∫⁻ x, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by
  exact QuotientIntegration.core μ H hH μH f hf

end
