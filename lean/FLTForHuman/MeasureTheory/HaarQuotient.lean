/-
  A Haar measure on a quotient of a locally compact group.

  For a subgroup `H ≤ G` with a measure `μH` on `H`, the quotient
  `MulAction.orbitRel.Quotient H G` carries a measure built from any invariant measure `μ` on
  `G`: a positive weight `weight H μH` cutting `G` into an exhaustion by compact exhaustions,
  the Radon–Nikodym density `density H μH` of its `H`-translates, and

  `measure μ H μH = (Quotient.mk'' )_* (μ.withDensity (density H μH))`.

  This is the vocabulary in which the automorphic quotient measures are stated (the unipotent,
  the rational centre-unipotent and the rational torus-unipotent quotients of `GL₂(𝔸_K)`); the
  properties of the construction — that the result is a Haar measure when `μ` is, and how it
  compares with the quotient measure of a fundamental domain — are proved where they are used.

  Assumes: mathlib `v4.34.0`. Mathlib's `MeasureTheory/Measure/Haar/Quotient.lean` has the
  *fundamental-domain* quotient measure (`IsFundamentalDomain.quotientMeasure`, a
  `Measure.map` of a restricted measure), not this exhaustion-and-density construction; checked
  `rg "quotientMeasure|MeasureQuotient|orbitRel.Quotient" Mathlib/MeasureTheory/` on 2026-11-07.
  The pin's namespace `HaarQuotient` is kept for checker fidelity.

  Transcribed whole from `Definitions/Def_HaarQuotient.lean` (pinned `aa2d8b3`, 35 lines /
  3 declarations), a generic measure-theory supplement over an arbitrary group, so its home is
  `MeasureTheory/`, not `AutomorphicForm/`. The two *quotient integral* identities below are
  the pin's `setLIntegral_eq_lintegral_setLIntegral_mul_out` (`ℝ≥0∞` form: the `Γ`-integral
  over a fundamental domain `S` is the quotient integral of the `H`-integrals over `T`) and
  `integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out` (the same
  at `ℂ`, with its two integrability conclusions); their engine is transcribed from the pin's
  `P2M/Sol/S_…` files and stays `private` here, so this module's public surface is the three
  definitions and the two headlines.
  spec-pin: Definitions/Def_HaarQuotient.lean
  spec-pin: Theorems/Thm_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out.lean
  spec-pin: P2M/Sol/S_HaarQuotient_setLIntegral_eq_lintegral_setLIntegral_mul_out.lean
  spec-pin: Theorems/Thm_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out.lean
  spec-pin: P2M/Sol/S_HaarQuotient_integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out.lean
-/
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Compactness.SigmaCompact

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace HaarQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

/-- The weight cutting `G` into an exhaustion by compact sets, scaled by the `μH`-masses of the
`H`-translates of the pieces. It is `0` when `G` is not σ-compact and weakly locally compact. -/
def weight (H : Subgroup G) (μH : Measure H) : G → ℝ≥0∞ :=
  open Classical in
  if h : SigmaCompactSpace G ∧ WeaklyLocallyCompactSpace G then
    haveI := h.1
    haveI := h.2
    fun g => ∑' n : ℕ,
      (2⁻¹ : ℝ≥0∞) ^ n *
        (1 + μH (((↑) : H → G) ⁻¹'
          ((CompactExhaustion.choice G (n + 1) : Set G) *
            (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹ *
        (interior (CompactExhaustion.choice G (n + 1) : Set G)).indicator (fun _ => (1 : ℝ≥0∞)) g
  else 0

/-- The density of the `H`-translates of `weight H μH` at `g`. -/
def density (H : Subgroup G) (μH : Measure H) (g : G) : ℝ≥0∞ :=
  weight H μH g / ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH

/-- The quotient measure: push the `density`-weighted `μ` forward along `Quotient.mk''`. -/
def measure (μ : Measure G) (H : Subgroup G) (μH : Measure H) :
    Measure (MulAction.orbitRel.Quotient H G) :=
  Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
    (μ.withDensity (density H μH))

private noncomputable def orb {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) (φ : G → ℝ≥0∞)
    (g : G) : ℝ≥0∞ :=
  ∫⁻ x : H, φ ((x : G) * g) ∂μH

private theorem orb_mul_left {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) [μH.IsMulRightInvariant]
    (φ : G → ℝ≥0∞) (x₀ : H) (g : G) :
    orb H μH φ ((x₀ : G) * g) = orb H μH φ g := by
  unfold orb
  have : (fun x : H => φ ((x : G) * ((x₀ : G) * g))) = fun x : H => φ (((x * x₀ : H) : G) * g) := by
    funext x
    simp [mul_assoc]
  rw [this]
  exact lintegral_mul_right_eq_self (fun x : H => φ ((x : G) * g)) x₀

private theorem orb_out_mk {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) [μH.IsMulRightInvariant]
    (φ : G → ℝ≥0∞) (g : G) :
    orb H μH φ (Quotient.mk (MulAction.orbitRel H G) g).out = orb H μH φ g := by
  have h : (MulAction.orbitRel H G) ((Quotient.mk (MulAction.orbitRel H G) g).out) g :=
    Quotient.mk_out g
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨x₀, hx₀⟩ := h
  rw [← hx₀]
  exact orb_mul_left H μH φ x₀ g

private theorem exists_mul_eq_out {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (g : G) :
    ∃ x₀ : H, (x₀ : G) * g = (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out := by
  have h : (MulAction.orbitRel H G) ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) g :=
    Quotient.mk_out g
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨x₀, hx₀⟩ := h
  exact ⟨x₀, hx₀⟩

private theorem measurable_comp_mul {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) {φ : G → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun p : G × H => φ ((p.2 : G) * p.1) := by
  apply hφ.comp
  have : Continuous fun p : G × H => (p.2 : G) * p.1 := by
    exact (continuous_subtype_val.comp continuous_snd).mul continuous_fst
  exact this.measurable

private theorem measurable_subtype_mul {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (g : G) :
    Measurable fun x : H => (x : G) * g :=
  (continuous_subtype_val.mul continuous_const).measurable

private theorem measurable_orb {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) [SFinite μH]
    {φ : G → ℝ≥0∞} (hφ : Measurable φ) : Measurable (orb H μH φ) := by
  unfold orb
  exact (measurable_comp_mul H hφ).lintegral_prod_right'

private theorem secondCountable_subgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) : SecondCountableTopology H :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

private theorem sigmaFinite_of_isClosed {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) [μH.IsHaarMeasure]
    (hH : IsClosed (H : Set G)) : SigmaFinite μH := by
  have : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology H := secondCountable_subgroup H
  infer_instance

private noncomputable def E {G : Type*} [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    [SigmaCompactSpace G] : CompactExhaustion G := CompactExhaustion.choice G

private noncomputable def M {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [WeaklyLocallyCompactSpace G] [SigmaCompactSpace G] (H : Subgroup G) (μH : Measure H) (n : ℕ) : ℝ≥0∞ :=
  μH (((↑) : H → G) ⁻¹' ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹))

private noncomputable def coef {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [WeaklyLocallyCompactSpace G] [SigmaCompactSpace G] (H : Subgroup G) (μH : Measure H) (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ n * (1 + M H μH n)⁻¹

private def V {G : Type*} [TopologicalSpace G] [WeaklyLocallyCompactSpace G] [SigmaCompactSpace G]
    (n : ℕ) : Set G :=
  interior (E (G := G) (n + 1) : Set G)

private theorem weight_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) (g : G) :
    weight H μH g = ∑' n : ℕ, coef H μH n * (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) g := by
  have h : SigmaCompactSpace G ∧ WeaklyLocallyCompactSpace G := ⟨inferInstance, inferInstance⟩
  unfold weight
  rw [dite_eq_left h]
  rfl

private theorem isOpen_V {G : Type*} [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    [SigmaCompactSpace G] (n : ℕ) : IsOpen (V (G := G) n) := isOpen_interior

private theorem V_subset {G : Type*} [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    [SigmaCompactSpace G] (n : ℕ) : V (G := G) n ⊆ (E (G := G) (n + 1) : Set G) := interior_subset

private theorem M_lt_top {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] (n : ℕ) : M H μH n < ⊤ := by
  unfold M
  have hc : IsCompact ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹) :=
    ((E (G := G)).isCompact (n + 1)).mul ((E (G := G)).isCompact (n + 1)).inv
  have hce : Topology.IsClosedEmbedding ((↑) : H → G) := hH.isClosedEmbedding_subtypeVal
  exact (hce.isCompact_preimage hc).measure_lt_top

private theorem coef_pos {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] (n : ℕ) : 0 < coef H μH n := by
  unfold coef
  apply ENNReal.mul_pos
  · exact (ENNReal.pow_pos (by norm_num) n).ne'
  · apply (ENNReal.inv_pos.mpr ?_).ne'
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, (M_lt_top H hH μH n).ne⟩

private theorem coef_mul_M_le {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) (n : ℕ) :
    coef H μH n * M H μH n ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
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

private theorem measurable_weight {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) :
    Measurable (weight H μH) := by
  have : weight H μH = fun g => ∑' n : ℕ,
      coef H μH n * (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) g := by
    funext g; exact weight_eq H μH g
  rw [this]
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine Measurable.iSup fun s => ?_
  exact s.measurable_fun_sum fun n _ =>
    (measurable_const.indicator (isOpen_V n).measurableSet).const_mul _

private def slice {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [WeaklyLocallyCompactSpace G] [SigmaCompactSpace G] (H : Subgroup G) (n : ℕ) (g : G) : Set H :=
  {x : H | (x : G) * g ∈ V (G := G) n}

private theorem isOpen_slice {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (n : ℕ) (g : G) : IsOpen (slice H n g) := by
  unfold slice
  exact (isOpen_V n).preimage ((continuous_subtype_val.mul continuous_const))

private theorem orb_weight_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) (g : G) :
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

private theorem measure_slice_le {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) [μH.IsMulRightInvariant]
    (n : ℕ) (g : G) : μH (slice H n g) ≤ M H μH n := by
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

private theorem orb_weight_le_two {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) [μH.IsMulRightInvariant]
    (g : G) : orb H μH (weight H μH) g ≤ 2 := by
  rw [orb_weight_eq H μH g]
  calc ∑' n : ℕ, coef H μH n * μH (slice H n g)
      ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        exact (mul_le_mul_right (measure_slice_le H μH n g) _).trans (coef_mul_M_le H μH n)
    _ = 2 := by
        rw [ENNReal.tsum_geometric]
        norm_num

private theorem orb_weight_lt_top {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) [μH.IsMulRightInvariant]
    (g : G) : orb H μH (weight H μH) g < ⊤ :=
  (orb_weight_le_two H μH g).trans_lt ENNReal.ofNat_lt_top

private theorem orb_weight_pos {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (g : G) : 0 < orb H μH (weight H μH) g := by
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

private theorem orb_weight_ne_zero {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (g : G) :
    orb H μH (weight H μH) g ≠ 0 :=
  (orb_weight_pos H hH μH g).ne'

private theorem density_eq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    (μH : Measure H) (g : G) :
    density H μH g = weight H μH g / orb H μH (weight H μH) g := rfl

private theorem measurable_density {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] :
    Measurable (density H μH) := by
  have : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  have : density H μH = fun g => weight H μH g / orb H μH (weight H μH) g := rfl
  rw [this]
  exact (measurable_weight H μH).div (measurable_orb H μH (measurable_weight H μH))

private theorem orb_density {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (g : G) : orb H μH (density H μH) g = 1 := by
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

private theorem isInvInvariant {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] : μH.IsInvInvariant := by
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

private theorem lintegral_mul_orb {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant] {φ β : G → ℝ≥0∞} (hφ : Measurable φ) (hβ : Measurable β) :
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

  have hsub : ∀ x : H, ∫⁻ g, φ g * β ((x : G) * g) ∂μ
      = ∫⁻ g, φ (((x⁻¹ : H) : G) * g) * β g ∂μ := by
    intro x
    have := lintegral_mul_left_eq_self (μ := μ) (fun g => φ g * β ((x : G) * g)) ((x⁻¹ : H) : G)
    rw [← this]
    refine lintegral_congr fun g => ?_
    simp [← mul_assoc]
  simp_rw [hsub]

  have := lintegral_inv_eq_self (μ := μH) (fun x : H => ∫⁻ g, φ ((x : G) * g) * β g ∂μ)
  simpa using this

private theorem lintegral_eq_lintegral_measure {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [SFinite μ] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] {f : G → ℝ≥0∞} (hf : Measurable f) :
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

private theorem isFundamentalDomain_of_ae_eq {α : Type*} {Γ : Type*} [Group Γ]
    [MeasurableSpace α] [MulAction Γ α] [Countable Γ] [MeasurableConstSMul Γ α]
    {μ : Measure α} [SMulInvariantMeasure Γ α μ] {s t : Set α}
    (hs : IsFundamentalDomain Γ s μ) (hst : s =ᵐ[μ] t) (ht : NullMeasurableSet t μ) :
    IsFundamentalDomain Γ t μ := by
  have hg : ∀ g : Γ, g • s =ᵐ[μ] g • t := fun g => by
    have := ((measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving).preimage_ae_eq hst
    rwa [Set.preimage_smul_inv, Set.preimage_smul_inv] at this
  refine ⟨ht, ?_, ?_⟩
  · have h1 := hs.ae_covers
    have h2 : ∀ᵐ x ∂μ, ∀ g : Γ, x ∈ g⁻¹ • s ↔ x ∈ g⁻¹ • t := by
      rw [ae_all_iff]
      intro g
      exact (hg g⁻¹).mem_iff
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨g, hgx⟩ := hx1
    refine ⟨g, ?_⟩
    have := (hx2 g).1 (Set.mem_inv_smul_set_iff.mpr hgx)
    exact Set.mem_inv_smul_set_iff.mp this
  · intro a b hab
    have hs' := hs.aedisjoint hab
    exact hs'.congr (hg a).symm (hg b).symm

private def fibre {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (S : Set G) (g : G) : Set H := {x : H | (x : G) * g ∈ S}

private theorem mem_subgroupOf_of_mem {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (Γ : Subgroup G) (hΓ : Γ ≤ H)
    {γ : G} (hγ : γ ∈ Γ) : (⟨γ, hΓ hγ⟩ : H) ∈ Γ.subgroupOf H := by
  rw [Subgroup.mem_subgroupOf]
  exact hγ

private def bad {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) (S : Set G) : Set G :=
  {g : G | ∀ γ : Γ, (γ : G) * g ∉ S} ∪ ⋃ γ₁ : Γ, ⋃ γ₂ : Γ, ⋃ (_ : γ₁ ≠ γ₂),
    {g : G | (γ₁ : G) * g ∈ S ∧ (γ₂ : G) * g ∈ S}

private theorem measurableSet_bad {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] {S : Set G}
    (hS : MeasurableSet S) :
    MeasurableSet (bad Γ S) := by
  unfold bad
  refine MeasurableSet.union ?_ ?_
  · have : {g : G | ∀ γ : Γ, (γ : G) * g ∉ S} = ⋂ γ : Γ, (fun g => (γ : G) * g) ⁻¹' Sᶜ := by
      ext g; simp
    rw [this]
    exact MeasurableSet.iInter fun γ => (measurable_const_mul (γ : G)) hS.compl
  · refine MeasurableSet.iUnion fun γ₁ => MeasurableSet.iUnion fun γ₂ =>
      MeasurableSet.iUnion fun _ => ?_
    exact ((measurable_const_mul (γ₁ : G)) hS).inter ((measurable_const_mul (γ₂ : G)) hS)

private theorem measure_bad_eq_zero {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] {S : Set G} (hS : IsFundamentalDomain Γ S μ) : μ (bad Γ S) = 0 := by
  unfold bad
  refine measure_union_null ?_ ?_
  · have hc := hS.ae_covers
    apply compl_mem_ae_iff.mp
    filter_upwards [hc] with g hg
    obtain ⟨γ, hγ⟩ := hg
    have hγ' : (γ : G) * g ∈ S := by simpa [Subgroup.smul_def] using hγ
    exact fun h => h γ hγ'
  · refine (measure_iUnion_null_iff).mpr fun γ₁ => (measure_iUnion_null_iff).mpr fun γ₂ =>
      (measure_iUnion_null_iff).mpr fun hne => ?_
    have hdis := hS.aedisjoint (inv_injective.ne hne : γ₁⁻¹ ≠ γ₂⁻¹)
    refine measure_mono_null ?_ hdis
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg
    refine ⟨?_, ?_⟩
    · rw [Set.mem_inv_smul_set_iff, Subgroup.smul_def, smul_eq_mul]; exact hg.1
    · rw [Set.mem_inv_smul_set_iff, Subgroup.smul_def, smul_eq_mul]; exact hg.2

private theorem isFundamentalDomain_fibre {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (Γ : Subgroup G) (hΓ : Γ ≤ H) {S : Set G} (hS : MeasurableSet S)
    (g : G) (hg : μH (fibre H (bad Γ S) g) = 0) :
    IsFundamentalDomain (Γ.subgroupOf H) (fibre H S g) μH := by
  have hmeas : MeasurableSet (fibre H S g) :=
    (continuous_subtype_val.mul continuous_const).measurable hS
  refine IsFundamentalDomain.mk'' hmeas.nullMeasurableSet ?_ ?_ ?_
  ·
    have hg' : ∀ᵐ x ∂μH, x ∉ fibre H (bad Γ S) g := compl_mem_ae_iff.mpr hg
    filter_upwards [hg'] with x hx
    have hx' : (x : G) * g ∉ bad Γ S := hx
    unfold bad at hx'
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_forall, not_not] at hx'
    obtain ⟨⟨γ, hγS⟩, -⟩ := hx'
    refine ⟨⟨⟨(γ : G), hΓ γ.2⟩, mem_subgroupOf_of_mem H Γ hΓ γ.2⟩, ?_⟩
    show (((⟨⟨(γ : G), hΓ γ.2⟩, mem_subgroupOf_of_mem H Γ hΓ γ.2⟩ : Γ.subgroupOf H) • x : H) : G)
      * g ∈ S
    rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]
    simpa [mul_assoc] using hγS
  ·
    intro γ' hγ'
    refine measure_mono_null ?_ hg
    rintro x ⟨hx1, hx2⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hx1
    have h1 : (((γ'⁻¹ • x : H)) : G) * g ∈ S := hx1
    have h2 : (x : G) * g ∈ S := hx2
    rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul] at h1

    have hγmem : (((γ'⁻¹ : Γ.subgroupOf H) : H) : G) ∈ Γ := by
      have := (γ'⁻¹).2
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    have hne : (⟨_, hγmem⟩ : Γ) ≠ 1 := by
      intro h
      apply hγ'
      have h' : (((γ'⁻¹ : Γ.subgroupOf H) : H) : G) = 1 := by
        simpa using congrArg (fun z : Γ => (z : G)) h
      have : γ'⁻¹ = 1 := by
        ext
        exact_mod_cast h'
      simpa using this
    show (x : G) * g ∈ bad Γ S
    unfold bad
    refine Or.inr (Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨⟨_, hγmem⟩, Set.mem_iUnion.mpr
      ⟨hne.symm, ?_⟩⟩⟩)
    refine ⟨by simpa using h2, ?_⟩
    simpa [mul_assoc] using h1
  · intro γ'
    exact (measurePreserving_smul γ' μH).quasiMeasurePreserving

private theorem orb_indicator {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) [μH.IsMulRightInvariant]
    {S : Set G} (hS : MeasurableSet S) (f : G → ℝ≥0∞) (g : G) :
    orb H μH (S.indicator f) g = ∫⁻ x in fibre H S g, f ((x : G) * g) ∂μH := by
  have hfm : MeasurableSet (fibre H S g) :=
    (continuous_subtype_val.mul continuous_const).measurable hS
  unfold orb
  rw [← lintegral_indicator hfm]
  refine lintegral_congr fun x => ?_
  exact (Set.indicator_comp_right (fun x : H => (x : G) * g) (s := S) (g := f)).symm

private theorem d2 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant] (Γ : Subgroup G) (hΓ : Γ ≤ H) [Countable Γ]
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g)
    (S : Set G) (hS : IsFundamentalDomain Γ S μ)
    (T : Set H) (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH) :
    ∫⁻ g in S, f g ∂μ =
      ∫⁻ q, (∫⁻ x in T, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by
  have : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  have : Countable (Γ.subgroupOf H) := by
    have : Function.Injective fun x : Γ.subgroupOf H => (⟨((x : H) : G), x.2⟩ : Γ) := by
      intro a b h
      have h1 : ((a : H) : G) = ((b : H) : G) := congrArg (fun z : Γ => (z : G)) h
      exact Subtype.ext (Subtype.ext h1)
    exact this.countable

  obtain ⟨S', hS'sub, hS'm, hS'eq⟩ := hS.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hS' : IsFundamentalDomain Γ S' μ :=
    isFundamentalDomain_of_ae_eq hS hS'eq.symm hS'm.nullMeasurableSet
  rw [setLIntegral_congr hS'eq.symm]

  rw [← lintegral_indicator hS'm]
  rw [lintegral_eq_lintegral_measure μ H hH μH (hf.indicator hS'm)]

  have hbad0 : μ (bad Γ S') = 0 := measure_bad_eq_zero μ Γ hS'
  have hbadm : MeasurableSet (bad Γ S') := measurableSet_bad Γ hS'm
  have h1m : Measurable ((bad Γ S').indicator fun _ : G => (1 : ℝ≥0∞)) :=
    measurable_const.indicator hbadm
  have horb0 : ∫⁻ q, orb H μH ((bad Γ S').indicator fun _ => (1 : ℝ≥0∞)) q.out
      ∂(HaarQuotient.measure μ H μH) = 0 := by
    rw [← lintegral_eq_lintegral_measure μ H hH μH h1m, lintegral_indicator hbadm,
      setLIntegral_const, one_mul, hbad0]
  have hmeas_out : Measurable fun q : MulAction.orbitRel.Quotient H G =>
      orb H μH ((bad Γ S').indicator fun _ => (1 : ℝ≥0∞)) q.out := by
    rw [measurable_from_quotient]
    have : (fun q : MulAction.orbitRel.Quotient H G =>
        orb H μH ((bad Γ S').indicator fun _ => (1 : ℝ≥0∞)) q.out) ∘ Quotient.mk'' =
        orb H μH ((bad Γ S').indicator fun _ => (1 : ℝ≥0∞)) := by
      funext g; exact orb_out_mk H μH _ g
    rw [this]
    exact measurable_orb H μH h1m
  have hae : ∀ᵐ q ∂(HaarQuotient.measure μ H μH),
      orb H μH ((bad Γ S').indicator fun _ => (1 : ℝ≥0∞)) q.out = 0 :=
    (lintegral_eq_zero_iff hmeas_out).mp horb0
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with q hq

  have hfib0 : μH (fibre H (bad Γ S') q.out) = 0 := by
    rw [orb_indicator H μH hbadm (fun _ => (1 : ℝ≥0∞)) q.out, setLIntegral_const, one_mul] at hq
    exact hq
  have hFD : IsFundamentalDomain (Γ.subgroupOf H) (fibre H S' q.out) μH :=
    isFundamentalDomain_fibre H μH Γ hΓ hS'm q.out hfib0
  rw [orb_indicator H μH hS'm f q.out]

  refine hFD.setLIntegral_eq hT (fun x : H => f ((x : G) * q.out)) ?_
  intro γ' x
  show f ((((γ' • x : H)) : G) * q.out) = f ((x : G) * q.out)
  rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
  have hmem : (((γ' : Γ.subgroupOf H) : H) : G) ∈ Γ := by
    have := γ'.2; rw [Subgroup.mem_subgroupOf] at this; exact this
  exact hfΓ _ hmem _

private theorem countable_subgroupOf {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (Γ : Subgroup G) [Countable Γ] :
    Countable (Γ.subgroupOf H) := by
  have : Function.Injective fun x : Γ.subgroupOf H => (⟨((x : H) : G), x.2⟩ : Γ) := by
    intro a b h
    have h1 : ((a : H) : G) = ((b : H) : G) := congrArg (fun z : Γ => (z : G)) h
    exact Subtype.ext (Subtype.ext h1)
  exact this.countable

private theorem isFundamentalDomain_image_mul_right {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H)
    [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ]
    {T : Set H} (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH) (x₀ : H) :
    IsFundamentalDomain (Γ.subgroupOf H) ((fun x : H => x * x₀) '' T) μH := by
  have hmp : MeasurePreserving (MeasurableEquiv.mulRight x₀ : H ≃ᵐ H) μH μH :=
    measurePreserving_mul_right μH x₀
  exact hT.image_of_equiv (ν := μH) (MeasurableEquiv.mulRight x₀)
    (hmp.symm _).quasiMeasurePreserving (Equiv.refl _) fun γ x => by
      show (γ • x) * x₀ = γ • (x * x₀)
      rw [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, smul_eq_mul, mul_assoc]

private theorem setLIntegral_fibre_mul {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ]
    {T : Set H} (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH)
    (φ : G → ℝ≥0∞) (hφΓ : ∀ γ ∈ Γ, ∀ g : G, φ (γ * g) = φ g) (x₀ : H) (g : G) :
    ∫⁻ x in T, φ ((x : G) * ((x₀ : G) * g)) ∂μH = ∫⁻ x in T, φ ((x : G) * g) ∂μH := by
  have hT' := isFundamentalDomain_image_mul_right H μH Γ hT x₀
  have : Countable (Γ.subgroupOf H) := countable_subgroupOf H Γ
  have hinv : ∀ (γ : Γ.subgroupOf H) (x : H), φ (((γ • x : H) : G) * g) = φ ((x : G) * g) := by
    intro γ x
    rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
    exact hφΓ _ ((Subgroup.mem_subgroupOf).mp γ.2) _

  have hmp : MeasurePreserving (MeasurableEquiv.mulRight x₀ : H ≃ᵐ H) μH μH :=
    measurePreserving_mul_right μH x₀
  have hpre : (MeasurableEquiv.mulRight x₀ : H → H) ⁻¹' ((fun x : H => x * x₀) '' T) = T := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := mul_right_cancel hyx
      exact this ▸ hy
    · intro hx; exact ⟨x, hx, rfl⟩
  have h1 : ∫⁻ x in T, φ ((x : G) * ((x₀ : G) * g)) ∂μH =
      ∫⁻ y in (fun x : H => x * x₀) '' T, φ ((y : G) * g) ∂μH := by
    calc ∫⁻ x in T, φ ((x : G) * ((x₀ : G) * g)) ∂μH
        = ∫⁻ x in (MeasurableEquiv.mulRight x₀ : H → H) ⁻¹' ((fun x : H => x * x₀) '' T),
            (fun y : H => φ ((y : G) * g)) (MeasurableEquiv.mulRight x₀ x) ∂μH := by
          rw [hpre]
          refine lintegral_congr fun x => ?_
          show φ ((x : G) * ((x₀ : G) * g)) = φ (((x * x₀ : H) : G) * g)
          rw [Subgroup.coe_mul, mul_assoc]
      _ = ∫⁻ y in (fun x : H => x * x₀) '' T, φ ((y : G) * g) ∂μH :=
          hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.mulRight x₀).measurableEmbedding
            (fun y : H => φ ((y : G) * g)) ((fun x : H => x * x₀) '' T)
  rw [h1]
  exact hT'.setLIntegral_eq hT _ hinv

private theorem measurable_comp_mul' {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) {β : Type*} [MeasurableSpace β]
    {φ : G → β} (hφ : Measurable φ) : Measurable fun p : G × H => φ ((p.2 : G) * p.1) := by
  apply hφ.comp
  exact ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable

private theorem measurable_setLIntegral_fibre {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (Γ : Subgroup G)
    [Countable Γ] {T : Set H} (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) (hφΓ : ∀ γ ∈ Γ, ∀ g : G, φ (γ * g) = φ g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x in T, φ ((x : G) * q.out) ∂μH := by
  have : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  rw [measurable_from_quotient]
  have heq : (fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x in T, φ ((x : G) * q.out) ∂μH) ∘
      Quotient.mk'' = fun g : G => ∫⁻ x in T, φ ((x : G) * g) ∂μH := by
    funext g
    obtain ⟨x₀, hx₀⟩ := exists_mul_eq_out H g
    simp only [Function.comp_apply]
    rw [← hx₀]
    exact setLIntegral_fibre_mul H μH Γ hT φ hφΓ x₀ g
  rw [heq]
  exact (measurable_comp_mul' H hφ).lintegral_prod_right' (ν := μH.restrict T)

private theorem setIntegral_fibre_mul {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (μH : Measure H) [μH.IsHaarMeasure]
    [μH.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ]
    {T : Set H} (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH)
    (f : G → ℂ) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g) (x₀ : H) (g : G) :
    ∫ x in T, f ((x : G) * ((x₀ : G) * g)) ∂μH = ∫ x in T, f ((x : G) * g) ∂μH := by
  have hT' := isFundamentalDomain_image_mul_right H μH Γ hT x₀
  have : Countable (Γ.subgroupOf H) := countable_subgroupOf H Γ
  have hinv : ∀ (γ : Γ.subgroupOf H) (x : H), f (((γ • x : H) : G) * g) = f ((x : G) * g) := by
    intro γ x
    rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
    exact hfΓ _ ((Subgroup.mem_subgroupOf).mp γ.2) _
  have hmp : MeasurePreserving (MeasurableEquiv.mulRight x₀ : H ≃ᵐ H) μH μH :=
    measurePreserving_mul_right μH x₀
  have hpre : (MeasurableEquiv.mulRight x₀ : H → H) ⁻¹' ((fun x : H => x * x₀) '' T) = T := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := mul_right_cancel hyx
      exact this ▸ hy
    · intro hx; exact ⟨x, hx, rfl⟩
  have h1 : ∫ x in T, f ((x : G) * ((x₀ : G) * g)) ∂μH =
      ∫ y in (fun x : H => x * x₀) '' T, f ((y : G) * g) ∂μH := by
    calc ∫ x in T, f ((x : G) * ((x₀ : G) * g)) ∂μH
        = ∫ x in (MeasurableEquiv.mulRight x₀ : H → H) ⁻¹' ((fun x : H => x * x₀) '' T),
            (fun y : H => f ((y : G) * g)) (MeasurableEquiv.mulRight x₀ x) ∂μH := by
          rw [hpre]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show f ((x : G) * ((x₀ : G) * g)) = f (((x * x₀ : H) : G) * g)
          rw [Subgroup.coe_mul, mul_assoc]
      _ = ∫ y in (fun x : H => x * x₀) '' T, f ((y : G) * g) ∂μH :=
          hmp.setIntegral_preimage_emb (MeasurableEquiv.mulRight x₀).measurableEmbedding
            (fun y : H => f ((y : G) * g)) ((fun x : H => x * x₀) '' T)
  rw [h1]
  exact hT'.setIntegral_eq hT hinv

private theorem measurable_setIntegral_fibre {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (Γ : Subgroup G)
    [Countable Γ] {T : Set H} (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH)
    (f : G → ℂ) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => ∫ x in T, f ((x : G) * q.out) ∂μH := by
  have : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  rw [measurable_from_quotient]
  have heq : (fun q : MulAction.orbitRel.Quotient H G => ∫ x in T, f ((x : G) * q.out) ∂μH) ∘
      Quotient.mk'' = fun g : G => ∫ x in T, f ((x : G) * g) ∂μH := by
    funext g
    obtain ⟨x₀, hx₀⟩ := exists_mul_eq_out H g
    simp only [Function.comp_apply]
    rw [← hx₀]
    exact setIntegral_fibre_mul H μH Γ hT f hfΓ x₀ g
  rw [heq]
  have hsm : StronglyMeasurable (Function.uncurry fun (g : G) (x : H) => f ((x : G) * g)) :=
    (measurable_comp_mul' H hf).stronglyMeasurable
  exact (hsm.integral_prod_right' (ν := μH.restrict T)).measurable

/-- **The quotient integral, `ℝ≥0∞` form.** For `Γ ≤ H ≤ G`, `μ` a left-invariant measure on `G`,
`μH` a right-invariant Haar measure on `H`, `S` a fundamental domain of `Γ` in `G` and `T` one of
`Γ` in `H`, the integral of a `Γ`-invariant `f` over `S` is the integral over the quotient of the
integrals over `T`. -/
theorem setLIntegral_eq_lintegral_setLIntegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Γ : Subgroup G) (hΓ : Γ ≤ H) [Countable Γ]
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g)
    (S : Set G) (hS : IsFundamentalDomain Γ S μ)
    (T : Set H) (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH) :
    ∫⁻ g in S, f g ∂μ =
      ∫⁻ q, (∫⁻ x in T, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) :=
  d2 μ H hH μH Γ hΓ f hf hfΓ S hS T hT

/-- **The quotient integral, `ℂ` form**, with its integrability conclusions. -/
theorem integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Γ : Subgroup G) (hΓ : Γ ≤ H) [Countable Γ]
    (f : G → ℂ) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g)
    (S : Set G) (hS : IsFundamentalDomain Γ S μ)
    (T : Set H) (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH)
    (hfin : ∫⁻ g in S, ‖f g‖ₑ ∂μ < ∞) :
    (∀ᵐ q ∂(HaarQuotient.measure μ H μH), IntegrableOn (fun x : H => f ((x : G) * q.out)) T μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H G => ∫ x in T, f ((x : G) * q.out) ∂μH)
      (HaarQuotient.measure μ H μH) ∧
    ∫ g in S, f g ∂μ =
      ∫ q, (∫ x in T, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by
  have : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  set ν := HaarQuotient.measure μ H μH with hν

  have L : ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g : G, φ (γ * g) = φ g) →
      ∫⁻ g in S, φ g ∂μ = ∫⁻ q, (∫⁻ x in T, φ ((x : G) * q.out) ∂μH) ∂ν := fun φ hφ hφΓ =>
    HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out μ H hH μH Γ hΓ φ hφ hφΓ S hS T hT
  have M : ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g : G, φ (γ * g) = φ g) →
      Measurable fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x in T, φ ((x : G) * q.out) ∂μH :=
    fun φ hφ hφΓ => measurable_setLIntegral_fibre H hH μH Γ hT φ hφ hφΓ

  have hfib_meas : ∀ q : MulAction.orbitRel.Quotient H G, Measurable fun x : H => f ((x : G) * q.out) :=
    fun q => hf.comp (continuous_subtype_val.mul continuous_const).measurable

  have hnormΓ : ∀ γ ∈ Γ, ∀ g : G, (‖f (γ * g)‖ₑ) = ‖f g‖ₑ := fun γ hγ g => by rw [hfΓ γ hγ g]
  have hLn := L (fun g => ‖f g‖ₑ) hf.enorm hnormΓ
  have hfin' : ∫⁻ q, (∫⁻ x in T, ‖f ((x : G) * q.out)‖ₑ ∂μH) ∂ν < ∞ := by rw [← hLn]; exact hfin
  have hae_fin : ∀ᵐ q ∂ν, ∫⁻ x in T, ‖f ((x : G) * q.out)‖ₑ ∂μH < ∞ :=
    ae_lt_top (M _ hf.enorm hnormΓ) hfin'.ne
  have hint_fib : ∀ᵐ q ∂ν, IntegrableOn (fun x : H => f ((x : G) * q.out)) T μH := by
    filter_upwards [hae_fin] with q hq
    exact ⟨(hfib_meas q).aestronglyMeasurable, hq⟩

  have hPm : Measurable fun q : MulAction.orbitRel.Quotient H G =>
      ∫ x in T, f ((x : G) * q.out) ∂μH :=
    measurable_setIntegral_fibre H hH μH Γ hT f hf hfΓ
  have hB : Integrable (fun q : MulAction.orbitRel.Quotient H G =>
      (∫⁻ x in T, ‖f ((x : G) * q.out)‖ₑ ∂μH).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top (M _ hf.enorm hnormΓ).aemeasurable hfin'.ne
  have hPint : Integrable (fun q : MulAction.orbitRel.Quotient H G =>
      ∫ x in T, f ((x : G) * q.out) ∂μH) ν := by
    refine hB.mono' hPm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    have h := norm_integral_le_lintegral_norm (μ := μH.restrict T) (fun x : H => f ((x : G) * q.out))
    have heq : (∫⁻ a in T, ENNReal.ofReal ‖f ((a : G) * q.out)‖ ∂μH)
        = ∫⁻ x in T, ‖f ((x : G) * q.out)‖ₑ ∂μH :=
      lintegral_congr fun x => ofReal_norm _
    rw [heq] at h
    exact h
  refine ⟨hint_fib, hPint, ?_⟩

  have hS_int : IntegrableOn f S μ := ⟨hf.aestronglyMeasurable, hfin⟩
  have real_case : ∀ u : G → ℝ, Measurable u → (∀ γ ∈ Γ, ∀ g : G, u (γ * g) = u g) →
      ∫⁻ g in S, ‖u g‖ₑ ∂μ < ∞ →
      ∫ g in S, u g ∂μ = ∫ q, (∫ x in T, u ((x : G) * q.out) ∂μH) ∂ν := by
    intro u hu huΓ hufin

    set up : G → ℝ≥0∞ := fun g => ENNReal.ofReal (u g) with hup
    set um : G → ℝ≥0∞ := fun g => ENNReal.ofReal (-u g) with hum
    have hupm : Measurable up := ENNReal.measurable_ofReal.comp hu
    have humm : Measurable um := ENNReal.measurable_ofReal.comp hu.neg
    have hupΓ : ∀ γ ∈ Γ, ∀ g : G, up (γ * g) = up g := fun γ hγ g => by simp only [hup, huΓ γ hγ g]
    have humΓ : ∀ γ ∈ Γ, ∀ g : G, um (γ * g) = um g := fun γ hγ g => by simp only [hum, huΓ γ hγ g]
    have hup_le : ∀ g, up g ≤ ‖u g‖ₑ := fun g => by
      exact Real.ofReal_le_enorm (u g)
    have hum_le : ∀ g, um g ≤ ‖u g‖ₑ := fun g => by
      rw [← enorm_neg]; exact Real.ofReal_le_enorm (-u g)
    have hup_fin : ∫⁻ g in S, up g ∂μ < ∞ := lt_of_le_of_lt (lintegral_mono fun g => hup_le g) hufin
    have hum_fin : ∫⁻ g in S, um g ∂μ < ∞ := lt_of_le_of_lt (lintegral_mono fun g => hum_le g) hufin
    have hu_int : IntegrableOn u S μ := ⟨hu.aestronglyMeasurable, hufin⟩

    have hae_up : ∀ᵐ q ∂ν, ∫⁻ x in T, up ((x : G) * q.out) ∂μH < ∞ :=
      ae_lt_top (M up hupm hupΓ) (by rw [← L up hupm hupΓ]; exact hup_fin.ne)
    have hae_um : ∀ᵐ q ∂ν, ∫⁻ x in T, um ((x : G) * q.out) ∂μH < ∞ :=
      ae_lt_top (M um humm humΓ) (by rw [← L um humm humΓ]; exact hum_fin.ne)
    have huΓn : ∀ γ ∈ Γ, ∀ g : G, ‖u (γ * g)‖ₑ = ‖u g‖ₑ := fun γ hγ g => by rw [huΓ γ hγ g]
    have hufin' : ∫⁻ q, (∫⁻ x in T, ‖u ((x : G) * q.out)‖ₑ ∂μH) ∂ν < ∞ := by
      rw [← L (fun g => ‖u g‖ₑ) hu.enorm huΓn]; exact hufin
    have hae_ufin : ∀ᵐ q ∂ν, ∫⁻ x in T, ‖u ((x : G) * q.out)‖ₑ ∂μH < ∞ :=
      ae_lt_top (M _ hu.enorm huΓn) hufin'.ne

    have hfib : ∀ᵐ q ∂ν, ∫ x in T, u ((x : G) * q.out) ∂μH =
        (∫⁻ x in T, up ((x : G) * q.out) ∂μH).toReal
          - (∫⁻ x in T, um ((x : G) * q.out) ∂μH).toReal := by
      filter_upwards [hae_ufin] with q hq
      have hiq : Integrable (fun x : H => u ((x : G) * q.out)) (μH.restrict T) :=
        ⟨(hu.comp (continuous_subtype_val.mul continuous_const).measurable).aestronglyMeasurable, hq⟩
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiq]
    rw [integral_congr_ae hfib, integral_sub,
      integral_toReal (M up hupm hupΓ).aemeasurable hae_up,
      integral_toReal (M um humm humΓ).aemeasurable hae_um, ← L up hupm hupΓ, ← L um humm humΓ,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu_int]
    · exact integrable_toReal_of_lintegral_ne_top (M up hupm hupΓ).aemeasurable
        (by rw [← L up hupm hupΓ]; exact hup_fin.ne)
    · exact integrable_toReal_of_lintegral_ne_top (M um humm humΓ).aemeasurable
        (by rw [← L um humm humΓ]; exact hum_fin.ne)

  have hreΓ : ∀ γ ∈ Γ, ∀ g : G, (f (γ * g)).re = (f g).re := fun γ hγ g => by rw [hfΓ γ hγ g]
  have himΓ : ∀ γ ∈ Γ, ∀ g : G, (f (γ * g)).im = (f g).im := fun γ hγ g => by rw [hfΓ γ hγ g]
  have hre_le : ∀ g, ‖(f g).re‖ₑ ≤ ‖f g‖ₑ := fun g => by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
      coe_nnnorm, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  have him_le : ∀ g, ‖(f g).im‖ₑ ≤ ‖f g‖ₑ := fun g => by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
      coe_nnnorm, Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
  have hre := real_case (fun g => (f g).re) (Complex.measurable_re.comp hf) hreΓ
    (lt_of_le_of_lt (lintegral_mono fun g => hre_le g) hfin)
  have him := real_case (fun g => (f g).im) (Complex.measurable_im.comp hf) himΓ
    (lt_of_le_of_lt (lintegral_mono fun g => him_le g) hfin)

  have hfibC : ∀ᵐ q ∂ν, ∫ x in T, f ((x : G) * q.out) ∂μH =
      ((∫ x in T, (f ((x : G) * q.out)).re ∂μH : ℝ) : ℂ) +
        ((∫ x in T, (f ((x : G) * q.out)).im ∂μH : ℝ) : ℂ) * Complex.I := by
    filter_upwards [hint_fib] with q hq
    have h := (integral_re_add_im (𝕜 := ℂ) hq).symm
    simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at h
    exact h
  have hIre : Integrable (fun q : MulAction.orbitRel.Quotient H G =>
      ((∫ x in T, (f ((x : G) * q.out)).re ∂μH : ℝ) : ℂ)) ν := by
    refine (hPint.re).ofReal.congr ?_
    filter_upwards [hint_fib] with q hq
    have h := integral_re (𝕜 := ℂ) hq
    simp only [RCLike.re_to_complex] at h
    show (((∫ x in T, f ((x : G) * q.out) ∂μH).re : ℝ) : ℂ) = _
    rw [← h]
  have hIim : Integrable (fun q : MulAction.orbitRel.Quotient H G =>
      ((∫ x in T, (f ((x : G) * q.out)).im ∂μH : ℝ) : ℂ) * Complex.I) ν := by
    refine ((hPint.im).ofReal.mul_const Complex.I).congr ?_
    filter_upwards [hint_fib] with q hq
    have h := integral_im (𝕜 := ℂ) hq
    simp only [RCLike.im_to_complex] at h
    show (((∫ x in T, f ((x : G) * q.out) ∂μH).im : ℝ) : ℂ) * Complex.I = _
    rw [← h]
  rw [integral_congr_ae hfibC, integral_add hIre hIim, integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal]
  have hre' := hre
  have him' := him
  beta_reduce at hre' him'
  rw [← hre', ← him']
  have h := (integral_re_add_im (𝕜 := ℂ) hS_int).symm
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at h
  exact h

end HaarQuotient

end
