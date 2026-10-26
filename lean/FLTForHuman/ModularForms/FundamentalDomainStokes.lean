/-
  Green's theorem over the modular fundamental domain.

  The modular fundamental domain `{z : ℂ | |z.re| ≤ 1/2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im}`, the region
  `ModularGroup.𝒟` written in the coordinates of `ℂ`, is the part of the strip `|re| ≤ 1/2`
  above the unit circle in the upper half-plane. Its boundary consists of the two vertical
  rays `±1/2 + iy`, `y ≥ √3/2`, and the unit-circle arc `e^{iθ}`, `θ ∈ [π/3, 2π/3]`. For a
  function `Φ` that is real-differentiable on an open `U ⊇ 𝒟`, with real derivative `Φ'`, and
  such that both `Φ` and `Φ'` decay exponentially in `z.im`, the identity
  `∫_𝒟 (I • Φ' z 1 - Φ' z I) = I • ∫_{√3/2}^∞ Φ (1/2 + iy) - I • ∫_{√3/2}^∞ Φ (-1/2 + iy)
  - ∫_{π/3}^{2π/3} Φ (e^{iθ}) · i e^{iθ} dθ` holds: the area integral of the Jacobian
  combination `∂ₓΦ + i ∂ᵧΦ` equals the circulation of `Φ` along the boundary.

  The proof transfers the area integral to the product domain `{(x, y) | |x| ≤ 1/2 ∧ h x ≤ y}`
  in `ℝ × ℝ` through the measure isomorphism `ℂ ≃ᵐ ℝ × ℝ`, where `h x = √(1 - x²)` cuts the
  upper boundary at the unit circle. Fubini then gives the vertical rays as integrals of
  `Φ' ⟨x, y⟩ I` over `y` (the fundamental theorem of calculus on a half-line, the boundary term
  at infinity vanishing by the exponential decay), and the horizontal segments as integrals of
  `Φ' ⟨x, y⟩ 1` over `x`; pairing the two horizontal segments across `h` leaves the arc, whose
  integral is the substitution `x = cos θ` over `θ ∈ [π/3, 2π/3]`.

  spec-pin: Theorems/Thm_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt.lean
  spec-pin: P2M/Sol/S_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt.lean
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace Complex

/-- The modular fundamental domain, as the region of `ℂ` cut out by the three inequalities
`|z.re| ≤ 1/2`, `1 ≤ ‖z‖` and `0 < z.im`. -/
private def modularDomain : Set ℂ := {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im}

/-- The height of the unit circle above the abscissa `x`, `√(1 - x²)`: the upper boundary of
the fundamental domain at `x`. -/
private def sqrtOneSubSq (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

/-- The fundamental domain in the coordinates `ℝ × ℝ` of `ℂ ≃ᵐ ℝ × ℝ`. -/
private def prodDomain : Set (ℝ × ℝ) := {p | |p.1| ≤ 1 / 2 ∧ sqrtOneSubSq p.1 ≤ p.2}

private lemma three_quarters_le {x : ℝ} (hx : |x| ≤ 1 / 2) : 3 / 4 ≤ 1 - x ^ 2 := by
  have h1 : x ^ 2 ≤ (1 / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  linarith

private lemma sqrt3_sq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

private lemma sqrt3_pos : 0 < Real.sqrt 3 / 2 := by positivity

private lemma sqrt3_lt_one : Real.sqrt 3 / 2 < 1 := by
  rw [div_lt_one two_pos, Real.sqrt_lt' two_pos]; norm_num

private lemma sqrt3_le_sqrtOneSubSq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    Real.sqrt 3 / 2 ≤ sqrtOneSubSq x := by
  unfold sqrtOneSubSq
  rw [Real.le_sqrt' sqrt3_pos, sqrt3_sq]
  exact three_quarters_le hx

private lemma sqrtOneSubSq_pos {x : ℝ} (hx : |x| ≤ 1 / 2) : 0 < sqrtOneSubSq x :=
  lt_of_lt_of_le sqrt3_pos (sqrt3_le_sqrtOneSubSq hx)

private lemma sqrtOneSubSq_le_one (x : ℝ) : sqrtOneSubSq x ≤ 1 := by
  unfold sqrtOneSubSq
  rw [Real.sqrt_le_left zero_le_one]
  nlinarith [sq_nonneg x]

private lemma sqrtOneSubSq_sq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    sqrtOneSubSq x ^ 2 = 1 - x ^ 2 :=
  Real.sq_sqrt (le_trans (by norm_num) (three_quarters_le hx))

private lemma mem_modularDomain_iff {x y : ℝ} :
    (⟨x, y⟩ : ℂ) ∈ modularDomain ↔ |x| ≤ 1 / 2 ∧ sqrtOneSubSq x ≤ y := by
  simp only [modularDomain, mem_ofPred_eq, Complex.norm_def, Complex.normSq_mk,
    Real.one_le_sqrt]
  constructor
  · rintro ⟨hx, hn, hy⟩
    refine ⟨hx, ?_⟩
    unfold sqrtOneSubSq
    rw [Real.sqrt_le_iff]
    exact ⟨hy.le, by nlinarith⟩
  · rintro ⟨hx, hy⟩
    have hpos := sqrtOneSubSq_pos hx
    have hy' := hy
    unfold sqrtOneSubSq at hy'
    rw [Real.sqrt_le_iff] at hy'
    exact ⟨hx, by nlinarith [hy'.2], lt_of_lt_of_le hpos hy⟩

private lemma mk_mem_modularDomain {x y : ℝ} (hx : |x| ≤ 1 / 2) (hy : sqrtOneSubSq x ≤ y) :
    (⟨x, y⟩ : ℂ) ∈ modularDomain :=
  mem_modularDomain_iff.mpr ⟨hx, hy⟩

private lemma preimage_modularDomain :
    (measurableEquivRealProd.symm : ℝ × ℝ → ℂ) ⁻¹' modularDomain = prodDomain := by
  ext ⟨x, y⟩
  simp only [mem_preimage, measurableEquivRealProd_symm_apply, prodDomain, mem_ofPred_eq]
  exact mem_modularDomain_iff

private lemma isClosed_prodDomain : IsClosed prodDomain := by
  have h1 : IsClosed {p : ℝ × ℝ | |p.1| ≤ 1 / 2} :=
    isClosed_le (continuous_abs.comp continuous_fst) continuous_const
  have h2 : IsClosed {p : ℝ × ℝ | sqrtOneSubSq p.1 ≤ p.2} := by
    refine isClosed_le ?_ continuous_snd
    exact (Real.continuous_sqrt.comp (continuous_const.sub (continuous_fst.pow 2)))
  simpa [prodDomain, ofPred_and] using h1.inter h2

private lemma measurableSet_prodDomain : MeasurableSet prodDomain :=
  isClosed_prodDomain.measurableSet

private lemma prodDomain_subset_prod :
    prodDomain ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi (0 : ℝ) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact ⟨abs_le.mp hx, lt_of_lt_of_le (sqrtOneSubSq_pos hx) hy⟩

private lemma setIntegral_modularDomain (G : ℂ → ℂ) :
    ∫ z in modularDomain, G z = ∫ p in prodDomain, G ⟨p.1, p.2⟩ := by
  rw [← preimage_modularDomain]
  exact ((Complex.volume_preserving_equiv_real_prod.symm _).setIntegral_preimage_emb
    measurableEquivRealProd.symm.measurableEmbedding G modularDomain).symm

private lemma integrableOn_prodDomain_of_bound {G : ℝ × ℝ → ℂ} {C δ : ℝ} (hδ : 0 < δ)
    (hG : ContinuousOn G prodDomain) (hb : ∀ p ∈ prodDomain, ‖G p‖ ≤ C * Real.exp (-δ * p.2)) :
    IntegrableOn G prodDomain := by
  have hdom : IntegrableOn (fun p : ℝ × ℝ => (C : ℝ) * Real.exp (-δ * p.2))
      (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi (0 : ℝ)) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    have h1 : Integrable (fun _ : ℝ => (C : ℝ))
        (volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2))) :=
      integrable_const _
    have h2 : Integrable (fun y : ℝ => Real.exp (-δ * y)) (volume.restrict (Ioi (0 : ℝ))) :=
      exp_neg_integrableOn_Ioi 0 hδ
    exact h1.mul_prod h2
  refine Integrable.mono' (hdom.mono_set prodDomain_subset_prod)
    (hG.aestronglyMeasurable measurableSet_prodDomain) ?_
  exact (ae_restrict_iff' measurableSet_prodDomain).mpr (Eventually.of_forall hb)

private lemma setIntegral_prodDomain_eq_x_y {G : ℝ × ℝ → ℂ} (hG : IntegrableOn G prodDomain) :
    ∫ p in prodDomain, G p = ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), ∫ y in Ici (sqrtOneSubSq x), G (x, y) := by
  have hi : Integrable (prodDomain.indicator G) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hG.integrable_indicator measurableSet_prodDomain
  rw [← integral_indicator measurableSet_prodDomain, Measure.volume_eq_prod, integral_prod _ hi]
  have hS : {x : ℝ | |x| ≤ 1 / 2} = Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    ext x; simp [abs_le]
  rw [← hS, ← integral_indicator (measurableSet_le continuous_abs.measurable measurable_const)]
  congr 1 with x
  by_cases hx : |x| ≤ 1 / 2
  · rw [indicator_of_mem (by exact hx), ← integral_indicator measurableSet_Ici]
    congr 1 with y
    by_cases hy : sqrtOneSubSq x ≤ y
    · rw [indicator_of_mem (show (x, y) ∈ prodDomain from ⟨hx, hy⟩),
        indicator_of_mem (by exact hy)]
    · rw [indicator_of_notMem (show (x, y) ∉ prodDomain from fun hm => hy hm.2),
        indicator_of_notMem (by exact hy)]
  · rw [indicator_of_notMem (by exact hx)]
    have : ∀ y, prodDomain.indicator G (x, y) = 0 := fun y =>
      indicator_of_notMem (show (x, y) ∉ prodDomain from fun hm => hx hm.1) _
    simp [this]

private lemma setIntegral_prodDomain_eq_y_x {G : ℝ × ℝ → ℂ} (hG : IntegrableOn G prodDomain) :
    ∫ p in prodDomain, G p = ∫ y, ∫ x in {x | |x| ≤ 1 / 2 ∧ sqrtOneSubSq x ≤ y}, G (x, y) := by
  have hi : Integrable (prodDomain.indicator G) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hG.integrable_indicator measurableSet_prodDomain
  rw [← integral_indicator measurableSet_prodDomain, Measure.volume_eq_prod, integral_prod_symm _ hi]
  congr 1 with y
  have hm : MeasurableSet {x : ℝ | |x| ≤ 1 / 2 ∧ sqrtOneSubSq x ≤ y} := by
    have : IsClosed {x : ℝ | |x| ≤ 1 / 2 ∧ sqrtOneSubSq x ≤ y} := by
      rw [ofPred_and]
      exact (isClosed_le continuous_abs continuous_const).inter
        (isClosed_le (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))
          continuous_const)
    exact this.measurableSet
  rw [← integral_indicator hm]
  congr 1 with x

section Hyp

variable (Φ : ℂ → ℂ) (Φ' : ℂ → ℂ →L[ℝ] ℂ) (U : Set ℂ) (δ : ℝ) (hδ : 0 < δ) (hU : IsOpen U)
  (hDU : modularDomain ⊆ U) (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) (hc : ContinuousOn Φ' U)
  (hΦ : ∃ C : ℝ, ∀ z ∈ U, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im))
  (hΦ' : ∃ C : ℝ, ∀ z ∈ U, ‖Φ' z‖ ≤ C * Real.exp (-δ * z.im))

private lemma mk_eq (x y : ℝ) : (⟨x, y⟩ : ℂ) = (x : ℂ) + (y : ℂ) * I := Complex.mk_eq_add_mul_I x y

private lemma hasDerivAt_vert {x y : ℝ} (hz : (⟨x, y⟩ : ℂ) ∈ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) :
    HasDerivAt (fun t : ℝ => Φ ⟨x, t⟩) (Φ' ⟨x, y⟩ I) y := by
  have h1 : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I y := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (x : ℂ)
  have h2 : (fun t : ℝ => Φ ⟨x, t⟩) = Φ ∘ fun t : ℝ => (x : ℂ) + (t : ℂ) * I := by
    ext t; simp [mk_eq]
  rw [h2]
  have hz' : (x : ℂ) + (y : ℂ) * I ∈ U := by rwa [← mk_eq]
  have := (hd _ hz').comp_hasDerivAt y h1
  rwa [← mk_eq] at this

private lemma hasDerivAt_horiz {x y : ℝ} (hz : (⟨x, y⟩ : ℂ) ∈ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) :
    HasDerivAt (fun t : ℝ => Φ ⟨t, y⟩) (Φ' ⟨x, y⟩ 1) x := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * I)
  have h2 : (fun t : ℝ => Φ ⟨t, y⟩) = Φ ∘ fun t : ℝ => (t : ℂ) + (y : ℂ) * I := by
    ext t; simp [mk_eq]
  rw [h2]
  have hz' : (x : ℂ) + (y : ℂ) * I ∈ U := by rwa [← mk_eq]
  have := (hd _ hz').comp_hasDerivAt x h1
  rwa [← mk_eq] at this

private lemma continuous_mk_left (x : ℝ) : Continuous fun t : ℝ => (⟨x, t⟩ : ℂ) := by
  simp [mk_eq]
  exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

private lemma continuous_mk_right (y : ℝ) : Continuous fun t : ℝ => (⟨t, y⟩ : ℂ) := by
  simp [mk_eq]
  exact (Complex.continuous_ofReal.add continuous_const)

private lemma tendsto_const_mul_exp {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    Tendsto (fun t : ℝ => C * Real.exp (-δ * t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.exp (-δ * t)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_comp_nhds_zero.mpr ?_
    exact (tendsto_id (α := ℝ) (x := atTop)).const_mul_atTop_of_neg (neg_lt_zero.mpr hδ)
  simpa using h1.const_mul C

include hδ hDU hd hc hΦ hΦ' in

private lemma integral_vert {x : ℝ} (hx : |x| ≤ 1 / 2) :
    ∫ y in Ioi (sqrtOneSubSq x), Φ' ⟨x, y⟩ I = -Φ ⟨x, sqrtOneSubSq x⟩ := by
  obtain ⟨C, hC⟩ := hΦ
  obtain ⟨C', hC'⟩ := hΦ'
  have hmem : ∀ t ∈ Ici (sqrtOneSubSq x), (⟨x, t⟩ : ℂ) ∈ U := fun t ht =>
    hDU (mk_mem_modularDomain hx ht)
  have hderiv : ∀ t ∈ Ici (sqrtOneSubSq x), HasDerivAt (fun t : ℝ => Φ ⟨x, t⟩) (Φ' ⟨x, t⟩ I) t :=
    fun t ht => hasDerivAt_vert Φ Φ' U (hmem t ht) hd
  have hcont : ContinuousOn (fun t : ℝ => Φ' ⟨x, t⟩ I) (Ici (sqrtOneSubSq x)) := by
    have h1 : ContinuousOn (fun t : ℝ => Φ' ⟨x, t⟩) (Ici (sqrtOneSubSq x)) :=
      hc.comp (continuous_mk_left x).continuousOn hmem
    exact h1.clm_apply continuousOn_const
  have hint : IntegrableOn (fun t : ℝ => Φ' ⟨x, t⟩ I) (Ioi (sqrtOneSubSq x)) := by
    have hdom : IntegrableOn (fun t : ℝ => C' * Real.exp (-δ * t)) (Ioi (sqrtOneSubSq x)) :=
      (exp_neg_integrableOn_Ioi _ hδ).const_mul C'
    refine Integrable.mono' hdom
      ((hcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    calc ‖Φ' ⟨x, t⟩ I‖ ≤ ‖Φ' ⟨x, t⟩‖ * ‖I‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Φ' ⟨x, t⟩‖ := by rw [Complex.norm_I, mul_one]
      _ ≤ C' * Real.exp (-δ * t) := hC' _ (hmem t (mem_Ici.mpr (le_of_lt ht)))
  have hlim : Tendsto (fun t : ℝ => Φ ⟨x, t⟩) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_mul_exp hδ C)
    filter_upwards [Ici_mem_atTop (sqrtOneSubSq x)] with t ht
    exact hC _ (hmem t ht)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim, zero_sub]

include hd in

private lemma integral_horiz {a b y : ℝ} (hab : a ≤ b) (hmem : ∀ t ∈ Icc a b, (⟨t, y⟩ : ℂ) ∈ U)
    (hc : ContinuousOn Φ' U) :
    ∫ t in a..b, Φ' ⟨t, y⟩ 1 = Φ ⟨b, y⟩ - Φ ⟨a, y⟩ := by
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun t : ℝ => Φ ⟨t, y⟩) (Φ' ⟨t, y⟩ 1) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_horiz Φ Φ' U (hmem t ht) hd
  have hcont : ContinuousOn (fun t : ℝ => Φ' ⟨t, y⟩ 1) (uIcc a b) := by
    rw [uIcc_of_le hab]
    have h1 : ContinuousOn (fun t : ℝ => Φ' ⟨t, y⟩) (Icc a b) :=
      hc.comp (continuous_mk_right y).continuousOn hmem
    exact h1.clm_apply continuousOn_const
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)

private def arcWidth (y : ℝ) : ℝ := Real.sqrt (1 - y ^ 2)

private lemma arcWidth_nonneg (y : ℝ) : 0 ≤ arcWidth y := Real.sqrt_nonneg _

private lemma arcWidth_one : arcWidth 1 = 0 := by simp [arcWidth]

private lemma arcWidth_pos {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1) : 0 < arcWidth y := by
  unfold arcWidth; apply Real.sqrt_pos.mpr; nlinarith

private lemma arcWidth_le_half {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) : arcWidth y ≤ 1 / 2 := by
  unfold arcWidth
  rw [Real.sqrt_le_left (by norm_num)]
  have := sqrt3_sq
  nlinarith [sqrt3_pos]

private lemma arcWidth_lt_half {y : ℝ} (hy : Real.sqrt 3 / 2 < y) : arcWidth y < 1 / 2 := by
  unfold arcWidth
  rw [Real.sqrt_lt' (by norm_num)]
  have := sqrt3_sq
  nlinarith [sqrt3_pos]

private lemma sqrtOneSubSq_half : sqrtOneSubSq (1 / 2) = Real.sqrt 3 / 2 := by
  unfold sqrtOneSubSq
  rw [show (1 : ℝ) - (1 / 2) ^ 2 = (Real.sqrt 3 / 2) ^ 2 by rw [sqrt3_sq]; norm_num,
    Real.sqrt_sq sqrt3_pos.le]

private lemma sqrtOneSubSq_neg (x : ℝ) : sqrtOneSubSq (-x) = sqrtOneSubSq x := by
  simp [sqrtOneSubSq]

private lemma sqrtOneSubSq_arcWidth {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    sqrtOneSubSq (arcWidth y) = y := by
  unfold sqrtOneSubSq arcWidth
  rw [Real.sq_sqrt (by nlinarith), sub_sub_cancel, Real.sqrt_sq hy0]

private lemma sqrtOneSubSq_le_iff {x y : ℝ} (hy : 0 ≤ y) :
    sqrtOneSubSq x ≤ y ↔ arcWidth y ≤ |x| := by
  unfold sqrtOneSubSq arcWidth
  rw [Real.sqrt_le_left hy, Real.sqrt_le_left (abs_nonneg x), sq_abs]
  constructor <;> intro h <;> linarith

private lemma slice_of_one_le {y : ℝ} (hy : 1 ≤ y) :
    {x : ℝ | |x| ≤ 1 / 2 ∧ sqrtOneSubSq x ≤ y} = Icc (-(1 / 2)) (1 / 2) := by
  ext x
  simp only [mem_ofPred_eq, mem_Icc, abs_le]
  exact ⟨fun h => h.1, fun h => ⟨h, (sqrtOneSubSq_le_one x).trans hy⟩⟩

private lemma slice_of_lt_one {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1) :
    {x : ℝ | |x| ≤ 1 / 2 ∧ sqrtOneSubSq x ≤ y} =
      Icc (-(1 / 2)) (-arcWidth y) ∪ Icc (arcWidth y) (1 / 2) := by
  have hr := arcWidth_pos hy0 hy
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Icc, sqrtOneSubSq_le_iff hy0, abs_le, le_abs']
  constructor
  · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
    · exact Or.inl ⟨h1, h3⟩
    · exact Or.inr ⟨h3, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨⟨h1, by linarith⟩, Or.inl h2⟩
    · exact ⟨⟨by linarith, h2⟩, Or.inr h1⟩

private lemma slice_of_lt {y : ℝ} (hy : y < Real.sqrt 3 / 2) :
    {x : ℝ | |x| ≤ 1 / 2 ∧ sqrtOneSubSq x ≤ y} = ∅ := by
  ext x
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  exact fun hx => lt_of_lt_of_le hy (sqrt3_le_sqrtOneSubSq hx)

private lemma mem_modularDomain_arcWidth {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) (hy1 : y ≤ 1) :
    (⟨arcWidth y, y⟩ : ℂ) ∈ modularDomain := by
  have hy0 : 0 ≤ y := sqrt3_pos.le.trans hy
  refine mk_mem_modularDomain ?_ (sqrtOneSubSq_arcWidth hy0 hy1).le
  rw [abs_of_nonneg (arcWidth_nonneg y)]; exact arcWidth_le_half hy

private lemma mem_modularDomain_neg_arcWidth {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) (hy1 : y ≤ 1) :
    (⟨-arcWidth y, y⟩ : ℂ) ∈ modularDomain := by
  have hy0 : 0 ≤ y := sqrt3_pos.le.trans hy
  refine mk_mem_modularDomain ?_ (by rw [sqrtOneSubSq_neg]; exact (sqrtOneSubSq_arcWidth hy0 hy1).le)
  rw [abs_neg, abs_of_nonneg (arcWidth_nonneg y)]; exact arcWidth_le_half hy

private lemma continuous_arcWidth : Continuous arcWidth :=
  Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))

private lemma continuous_mk2 : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) := by
  simp [mk_eq]
  exact ((Complex.continuous_ofReal.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))

/-- The correction term pairing the two horizontal segments at height `y`. -/
private def rayCorrection (y : ℝ) : ℂ := Φ ⟨-arcWidth y, y⟩ - Φ ⟨arcWidth y, y⟩

include hd hDU in
private lemma continuousOn_rayCorrection :
    ContinuousOn (rayCorrection Φ) (Icc (Real.sqrt 3 / 2) 1) := by
  have hΦc : ContinuousOn Φ U := fun z hz => (hd z hz).continuousAt.continuousWithinAt
  apply ContinuousOn.sub
  · refine hΦc.comp (continuous_mk2.comp (continuous_arcWidth.neg.prodMk continuous_id)).continuousOn ?_
    exact fun y hy => hDU (mem_modularDomain_neg_arcWidth hy.1 hy.2)
  · refine hΦc.comp (continuous_mk2.comp (continuous_arcWidth.prodMk continuous_id)).continuousOn ?_
    exact fun y hy => hDU (mem_modularDomain_arcWidth hy.1 hy.2)

include hδ hd hDU hΦ in

private lemma integrableOn_vert {x : ℝ} (hx : |x| ≤ 1 / 2) :
    IntegrableOn (fun y : ℝ => Φ ⟨x, y⟩) (Ioi (sqrtOneSubSq x)) := by
  obtain ⟨C, hC⟩ := hΦ
  have hΦc : ContinuousOn Φ U := fun z hz => (hd z hz).continuousAt.continuousWithinAt
  have hmem : ∀ t ∈ Ioi (sqrtOneSubSq x), (⟨x, t⟩ : ℂ) ∈ U := fun t ht =>
    hDU (mk_mem_modularDomain hx (le_of_lt ht))
  have hcont : ContinuousOn (fun t : ℝ => Φ ⟨x, t⟩) (Ioi (sqrtOneSubSq x)) :=
    hΦc.comp (continuous_mk_left x).continuousOn hmem
  have hdom : IntegrableOn (fun t : ℝ => C * Real.exp (-δ * t)) (Ioi (sqrtOneSubSq x)) :=
    (exp_neg_integrableOn_Ioi _ hδ).const_mul C
  refine Integrable.mono' hdom (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hC _ (hmem t ht))

include hd hDU hc in

private lemma sliceIntegral {y : ℝ} (hy : Real.sqrt 3 / 2 < y) :
    ∫ x in {x : ℝ | |x| ≤ 1 / 2 ∧ sqrtOneSubSq x ≤ y}, Φ' ⟨x, y⟩ 1 =
      (Φ ⟨1 / 2, y⟩ - Φ ⟨-(1 / 2), y⟩) + (Iic (1 : ℝ)).indicator (rayCorrection Φ) y := by
  have hy0 : 0 ≤ y := sqrt3_pos.le.trans hy.le
  rcases lt_or_ge y 1 with hy1 | hy1
  · rw [indicator_of_mem (show y ∈ Iic (1 : ℝ) from hy1.le), slice_of_lt_one hy0 hy1]
    have hr := arcWidth_pos hy0 hy1
    have hr' := arcWidth_lt_half hy
    have hmem : ∀ t : ℝ, |t| ≤ 1 / 2 → arcWidth y ≤ |t| → (⟨t, y⟩ : ℂ) ∈ U :=
      fun t ht ht' => hDU (mk_mem_modularDomain ht ((sqrtOneSubSq_le_iff hy0).mpr ht'))
    have hmem₁ : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (-arcWidth y), (⟨t, y⟩ : ℂ) ∈ U := fun t ht =>
      hmem t (abs_le.mpr ⟨ht.1, by linarith [ht.2]⟩) (le_abs'.mpr (Or.inl ht.2))
    have hmem₂ : ∀ t ∈ Icc (arcWidth y) (1 / 2 : ℝ), (⟨t, y⟩ : ℂ) ∈ U := fun t ht =>
      hmem t (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩) (le_abs'.mpr (Or.inr ht.1))
    have hcont : ∀ s : Set ℝ, (∀ t ∈ s, (⟨t, y⟩ : ℂ) ∈ U) →
        ContinuousOn (fun t : ℝ => Φ' ⟨t, y⟩ 1) s := fun s hs =>
      (hc.comp (continuous_mk_right y).continuousOn hs).clm_apply continuousOn_const
    rw [setIntegral_union (Set.disjoint_iff.mpr ?_) measurableSet_Icc
      ((hcont _ hmem₁).integrableOn_Icc) ((hcont _ hmem₂).integrableOn_Icc),
      integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le hr'.le,
      integral_horiz Φ Φ' U hd (by linarith) hmem₁ hc, integral_horiz Φ Φ' U hd hr'.le hmem₂ hc]
    · simp only [rayCorrection]; ring
    · rintro t ⟨⟨-, h1⟩, ⟨h2, -⟩⟩; exact absurd (h2.trans h1) (by linarith)
  · rw [slice_of_one_le hy1, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
    have hmem : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), (⟨t, y⟩ : ℂ) ∈ U := fun t ht =>
      hDU (mk_mem_modularDomain (abs_le.mpr ⟨ht.1, ht.2⟩) ((sqrtOneSubSq_le_one t).trans hy1))
    rw [integral_horiz Φ Φ' U hd (by norm_num) hmem hc]
    rcases hy1.lt_or_eq with hy1 | rfl
    · rw [indicator_of_notMem (show y ∉ Iic (1 : ℝ) from not_le.mpr hy1), add_zero]
    · simp [rayCorrection, arcWidth_one]

include hδ hDU hd hc hΦ hΦ' in

private lemma integral_prodDomain_horiz :
    ∫ p in prodDomain, Φ' ⟨p.1, p.2⟩ 1 =
      ((∫ y in Ioi (Real.sqrt 3 / 2), Φ ⟨1 / 2, y⟩) -
          ∫ y in Ioi (Real.sqrt 3 / 2), Φ ⟨-(1 / 2), y⟩)
        + ∫ y in (Real.sqrt 3 / 2)..1, rayCorrection Φ y := by
  obtain ⟨C', hC'⟩ := hΦ'
  have hG : IntegrableOn (fun p : ℝ × ℝ => Φ' ⟨p.1, p.2⟩ 1) prodDomain := by
    refine integrableOn_prodDomain_of_bound hδ ?_ (C := C') fun p hp => ?_
    · refine (hc.comp continuous_mk2.continuousOn fun p hp =>
        hDU (mk_mem_modularDomain hp.1 hp.2)).clm_apply continuousOn_const
    · calc ‖Φ' ⟨p.1, p.2⟩ 1‖ ≤ ‖Φ' ⟨p.1, p.2⟩‖ * ‖(1 : ℂ)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖Φ' ⟨p.1, p.2⟩‖ := by rw [norm_one, mul_one]
        _ ≤ C' * Real.exp (-δ * p.2) := hC' _ (hDU (mk_mem_modularDomain hp.1 hp.2))
  rw [setIntegral_prodDomain_eq_y_x hG]

  have hae : (fun y => ∫ x in {x : ℝ | |x| ≤ 1 / 2 ∧ sqrtOneSubSq x ≤ y}, Φ' ⟨x, y⟩ 1) =ᵐ[volume]
      (Ioi (Real.sqrt 3 / 2)).indicator fun y =>
        (Φ ⟨1 / 2, y⟩ - Φ ⟨-(1 / 2), y⟩) + (Iic (1 : ℝ)).indicator (rayCorrection Φ) y := by
    have : ∀ᵐ y : ℝ ∂volume, y ∉ ({Real.sqrt 3 / 2} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp Real.volume_singleton
    filter_upwards [this] with y hy
    rcases lt_or_gt_of_ne (fun h : y = Real.sqrt 3 / 2 => hy h) with hy | hy
    · rw [indicator_of_notMem (show y ∉ Ioi (Real.sqrt 3 / 2) from not_lt.mpr hy.le),
        slice_of_lt hy, Measure.restrict_empty, integral_zero_measure]
    · rw [indicator_of_mem (show y ∈ Ioi (Real.sqrt 3 / 2) from hy)]
      exact sliceIntegral Φ Φ' U hDU hd hc hy
  rw [integral_congr_ae hae, integral_indicator measurableSet_Ioi]
  have h1 : IntegrableOn (fun y : ℝ => Φ ⟨1 / 2, y⟩) (Ioi (Real.sqrt 3 / 2)) := by
    have := integrableOn_vert Φ Φ' U δ hδ hDU hd hΦ (x := 1 / 2)
      (by rw [abs_of_pos (by norm_num)])
    rwa [sqrtOneSubSq_half] at this
  have h2 : IntegrableOn (fun y : ℝ => Φ ⟨-(1 / 2), y⟩) (Ioi (Real.sqrt 3 / 2)) := by
    have := integrableOn_vert Φ Φ' U δ hδ hDU hd hΦ (x := -(1 / 2))
      (by rw [abs_neg, abs_of_pos (by norm_num)])
    rwa [sqrtOneSubSq_neg, sqrtOneSubSq_half] at this
  have h3 : IntegrableOn ((Iic (1 : ℝ)).indicator (rayCorrection Φ)) (Ioi (Real.sqrt 3 / 2)) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic,
      show Iic (1 : ℝ) ∩ Ioi (Real.sqrt 3 / 2) = Ioc (Real.sqrt 3 / 2) 1 by
        rw [inter_comm, Ioi_inter_Iic]]
    exact ((continuousOn_rayCorrection Φ Φ' U hDU hd).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h12 : IntegrableOn (fun y : ℝ => Φ ⟨1 / 2, y⟩ - Φ ⟨-(1 / 2), y⟩)
      (Ioi (Real.sqrt 3 / 2)) := h1.sub h2
  rw [integral_add h12 h3, integral_sub h1 h2, setIntegral_indicator measurableSet_Iic,
    Ioi_inter_Iic, intervalIntegral.integral_of_le sqrt3_lt_one.le]

include hδ hDU hc hΦ' in
private lemma integrableOn_prodDomain_apply (v : ℂ) :
    IntegrableOn (fun p : ℝ × ℝ => Φ' ⟨p.1, p.2⟩ v) prodDomain := by
  obtain ⟨C', hC'⟩ := hΦ'
  refine integrableOn_prodDomain_of_bound hδ ?_ (C := C' * ‖v‖) fun p hp => ?_
  · exact (hc.comp continuous_mk2.continuousOn fun p hp =>
      hDU (mk_mem_modularDomain hp.1 hp.2)).clm_apply continuousOn_const
  · calc ‖Φ' ⟨p.1, p.2⟩ v‖ ≤ ‖Φ' ⟨p.1, p.2⟩‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C' * Real.exp (-δ * p.2) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (hC' _ (hDU (mk_mem_modularDomain hp.1 hp.2))) (norm_nonneg _)
      _ = C' * ‖v‖ * Real.exp (-δ * p.2) := by ring

include hδ hDU hd hc hΦ hΦ' in

private lemma integral_prodDomain_vert :
    ∫ p in prodDomain, Φ' ⟨p.1, p.2⟩ I =
      -∫ x in (-(1 / 2 : ℝ))..(1 / 2), Φ ⟨x, sqrtOneSubSq x⟩ := by
  rw [setIntegral_prodDomain_eq_x_y (integrableOn_prodDomain_apply Φ' U δ hδ hDU hc hΦ' I),
    intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  have hx' : |x| ≤ 1 / 2 := abs_le.mpr ⟨hx.1, hx.2⟩
  rw [integral_Ici_eq_integral_Ioi]
  exact integral_vert Φ Φ' U δ hδ hDU hd hc hΦ hΦ' hx'

/-- The unit-circle parametrization `θ ↦ e^{iθ}`. -/
private def circleParam (θ : ℝ) : ℂ := ⟨Real.cos θ, Real.sin θ⟩

private lemma exp_mul_I_eq (θ : ℝ) : Complex.exp (θ * I) = circleParam θ :=
  Complex.ext (Complex.exp_ofReal_mul_I_re θ) (Complex.exp_ofReal_mul_I_im θ)

private lemma continuous_circleParam : Continuous circleParam :=
  continuous_mk2.comp (Real.continuous_cos.prodMk Real.continuous_sin)

private lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

private lemma sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
    Real.sin_pi_div_three]

private lemma pi_div_three_le : Real.pi / 3 ≤ 2 * Real.pi / 3 := by linarith [Real.pi_pos]

private lemma abs_cos_le {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) :
    |Real.cos θ| ≤ 1 / 2 := by
  have hπ := Real.pi_pos
  rw [abs_le]
  constructor
  · have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith) hθ.2
    rw [cos_two_pi_div_three] at this
    exact this
  · have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2]) hθ.1
    rwa [Real.cos_pi_div_three] at this

private lemma sin_nonneg_arc {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) :
    0 ≤ Real.sin θ :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos])
    (by linarith [hθ.2, Real.pi_pos])

private lemma sqrtOneSubSq_cos {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) :
    sqrtOneSubSq (Real.cos θ) = Real.sin θ := by
  unfold sqrtOneSubSq
  rw [← Real.sin_sq θ, Real.sqrt_sq (sin_nonneg_arc hθ)]

private lemma arcWidth_sin (θ : ℝ) : arcWidth (Real.sin θ) = |Real.cos θ| := by
  unfold arcWidth
  rw [← Real.cos_sq' θ, Real.sqrt_sq_eq_abs]

private lemma circleParam_mem_modularDomain {θ : ℝ}
    (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) : circleParam θ ∈ modularDomain :=
  mk_mem_modularDomain (abs_cos_le hθ) (sqrtOneSubSq_cos hθ).le

private lemma continuousOn_Φ (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) : ContinuousOn Φ U :=
  fun z hz => (hd z hz).continuousAt.continuousWithinAt

include hd hDU in
private lemma continuousOn_arc :
    ContinuousOn (fun θ => Φ (circleParam θ)) (Icc (Real.pi / 3) (2 * Real.pi / 3)) :=
  (continuousOn_Φ Φ Φ' U hd).comp continuous_circleParam.continuousOn fun _ hθ =>
    hDU (circleParam_mem_modularDomain hθ)

private lemma arc_sin :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.sin θ • Φ (circleParam θ) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), Φ ⟨x, sqrtOneSubSq x⟩ := by
  have hab := pi_div_three_le
  have key : ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
      (-Real.sin θ) • ((fun x : ℝ => Φ ⟨x, sqrtOneSubSq x⟩) ∘ Real.cos) θ =
        -∫ x in (-(1 / 2 : ℝ))..(1 / 2), Φ ⟨x, sqrtOneSubSq x⟩ := by
    rw [intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos Real.continuous_cos.continuousOn
      (fun θ _ => Real.hasDerivAt_cos θ) (fun θ hθ => ?_), Real.cos_pi_div_three,
      cos_two_pi_div_three, intervalIntegral.integral_symm]
    rw [min_eq_left hab, max_eq_right hab] at hθ
    exact neg_nonpos.mpr (sin_nonneg_arc (Ioo_subset_Icc_self hθ))
  calc ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.sin θ • Φ (circleParam θ)
      = ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
          -((-Real.sin θ) • ((fun x : ℝ => Φ ⟨x, sqrtOneSubSq x⟩) ∘ Real.cos) θ) := by
        refine intervalIntegral.integral_congr fun θ hθ => ?_
        rw [uIcc_of_le hab] at hθ
        simp only [Function.comp_apply, neg_smul, neg_neg, sqrtOneSubSq_cos hθ, circleParam]
    _ = _ := by rw [intervalIntegral.integral_neg, key, neg_neg]

include hd hDU in

private lemma arc_cos :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.cos θ • Φ (circleParam θ) =
      -∫ y in (Real.sqrt 3 / 2)..1, rayCorrection Φ y := by
  have hπ := Real.pi_pos
  have h1 : Real.pi / 3 ≤ Real.pi / 2 := by linarith
  have h2 : Real.pi / 2 ≤ 2 * Real.pi / 3 := by linarith
  have hΦc := continuousOn_Φ Φ Φ' U hd
  have hcont : ContinuousOn (fun θ => Real.cos θ • Φ (circleParam θ))
      (Icc (Real.pi / 3) (2 * Real.pi / 3)) :=
    Real.continuous_cos.continuousOn.smul (continuousOn_arc Φ Φ' U hDU hd)
  have hi1 : IntervalIntegrable (fun θ => Real.cos θ • Φ (circleParam θ)) volume
      (Real.pi / 3) (Real.pi / 2) :=
    (hcont.mono (by rw [uIcc_of_le h1]; exact Icc_subset_Icc_right h2)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun θ => Real.cos θ • Φ (circleParam θ)) volume (Real.pi / 2)
      (2 * Real.pi / 3) :=
    (hcont.mono (by rw [uIcc_of_le h2]; exact Icc_subset_Icc_left h1)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]

  have k1 : ∫ θ in (Real.pi / 3)..(Real.pi / 2), Real.cos θ • Φ (circleParam θ) =
      ∫ y in (Real.sqrt 3 / 2)..1, Φ ⟨arcWidth y, y⟩ := by
    rw [← Real.sin_pi_div_three, ← Real.sin_pi_div_two,
      ← intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (g := fun y : ℝ => Φ ⟨arcWidth y, y⟩)
        Real.continuous_sin.continuousOn (fun θ _ => Real.hasDerivAt_sin θ) (fun θ hθ => ?_)]
    · refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le h1] at hθ
      have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩
      simp only [Function.comp_apply, circleParam, arcWidth_sin, abs_of_nonneg hc0]
    · rw [min_eq_left h1, max_eq_right h1] at hθ
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2.le⟩

  have k2 : ∫ θ in (Real.pi / 2)..(2 * Real.pi / 3), Real.cos θ • Φ (circleParam θ) =
      -∫ y in (Real.sqrt 3 / 2)..1, Φ ⟨-arcWidth y, y⟩ := by
    rw [← sin_two_pi_div_three, ← Real.sin_pi_div_two,
      ← intervalIntegral.integral_symm (Real.sin (2 * Real.pi / 3)) (Real.sin (Real.pi / 2)),
      ← intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos (g := fun y : ℝ => Φ ⟨-arcWidth y, y⟩)
        Real.continuous_sin.continuousOn (fun θ _ => Real.hasDerivAt_sin θ) (fun θ hθ => ?_)]
    · refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le h2] at hθ
      have hc0 : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2])
      simp only [Function.comp_apply, circleParam, arcWidth_sin, abs_of_nonpos hc0, neg_neg]
    · rw [min_eq_left h2, max_eq_right h2] at hθ
      exact Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1.le (by linarith [hθ.2])
  have hg1 : IntervalIntegrable (fun y : ℝ => Φ ⟨arcWidth y, y⟩) volume (Real.sqrt 3 / 2) 1 := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le sqrt3_lt_one.le])).intervalIntegrable
    exact hΦc.comp (continuous_mk2.comp (continuous_arcWidth.prodMk continuous_id)).continuousOn
      fun y hy => hDU (mem_modularDomain_arcWidth hy.1 hy.2)
  have hg2 : IntervalIntegrable (fun y : ℝ => Φ ⟨-arcWidth y, y⟩) volume (Real.sqrt 3 / 2) 1 := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le sqrt3_lt_one.le])).intervalIntegrable
    exact hΦc.comp (continuous_mk2.comp (continuous_arcWidth.neg.prodMk continuous_id)).continuousOn
      fun y hy => hDU (mem_modularDomain_neg_arcWidth hy.1 hy.2)
  rw [k1, k2, show (rayCorrection Φ) = fun y => Φ ⟨-arcWidth y, y⟩ - Φ ⟨arcWidth y, y⟩ from rfl,
    intervalIntegral.integral_sub hg2 hg1]
  ring

private lemma arc_integrand (θ : ℝ) :
    Φ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)) =
      -(Real.sin θ • Φ (circleParam θ)) + I * (Real.cos θ • Φ (circleParam θ)) := by
  rw [exp_mul_I_eq, Complex.real_smul, Complex.real_smul]
  have e : (circleParam θ : ℂ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := mk_eq _ _
  generalize Φ (circleParam θ) = w
  rw [e]
  linear_combination ((Real.sin θ : ℂ) * w) * Complex.I_mul_I

include hd hDU in
private lemma arc_split :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        Φ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)) =
      -(∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.sin θ • Φ (circleParam θ)) +
        I * ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.cos θ • Φ (circleParam θ) := by
  have hab := pi_div_three_le
  have harc := continuousOn_arc Φ Φ' U hDU hd
  have hi1 : IntervalIntegrable (fun θ => Real.sin θ • Φ (circleParam θ)) volume (Real.pi / 3)
      (2 * Real.pi / 3) := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le hab])).intervalIntegrable
    exact Real.continuous_sin.continuousOn.smul harc
  have hi2 : IntervalIntegrable (fun θ => Real.cos θ • Φ (circleParam θ)) volume (Real.pi / 3)
      (2 * Real.pi / 3) := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le hab])).intervalIntegrable
    exact Real.continuous_cos.continuousOn.smul harc
  have hi1' : IntervalIntegrable (fun θ => -(Real.sin θ • Φ (circleParam θ))) volume (Real.pi / 3)
      (2 * Real.pi / 3) := hi1.neg
  have hi2' : IntervalIntegrable (fun θ => I * (Real.cos θ • Φ (circleParam θ))) volume (Real.pi / 3)
      (2 * Real.pi / 3) := hi2.const_mul I
  rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hi1' hi2']
  exact intervalIntegral.integral_congr fun θ _ => arc_integrand Φ θ

end Hyp

-- The pin's statement carries `hU : IsOpen U`, which the Green identity does not use: the decay
-- bounds already make the boundary term at infinity vanish. The binder is kept because the
-- statement is transcribed verbatim, so the unused-variable linter is silenced for this one
-- declaration rather than the binder renamed.
set_option linter.unusedVariables false in
/-- **Green's theorem over the modular fundamental domain.** For `Φ` real-differentiable on an
open `U` containing the region `{z | |z.re| ≤ 1/2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im}` with real derivative
`Φ'`, both exponentially decaying in `z.im`, the area integral of the Jacobian combination
`I • Φ' z 1 - Φ' z I` equals the circulation of `Φ` around the boundary: the two vertical rays
`±1/2 + iy`, `y ≥ √3/2`, and the unit-circle arc `e^{iθ}`, `θ ∈ [π/3, 2π/3]`. -/
theorem integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt (Φ : ℂ → ℂ)
    (Φ' : ℂ → ℂ →L[ℝ] ℂ) (U : Set ℂ) (δ : ℝ) (hδ : 0 < δ) (hU : IsOpen U)
    (hDU : {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im} ⊆ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) (hc : ContinuousOn Φ' U)
    (hΦ : ∃ C : ℝ, ∀ z ∈ U, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im))
    (hΦ' : ∃ C : ℝ, ∀ z ∈ U, ‖Φ' z‖ ≤ C * Real.exp (-δ * z.im)) :
    (∫ z in {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im},
        (Complex.I • Φ' z 1 - Φ' z Complex.I)) =
      Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φ (1 / 2 + y * Complex.I)) -
        Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φ (-(1 / 2) + y * Complex.I)) -
        ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
          Φ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) := by
  change (∫ z in modularDomain, (I • Φ' z 1 - Φ' z I)) =
      I • (∫ y in Ioi (Real.sqrt 3 / 2), Φ (1 / 2 + y * I))
        - I • (∫ y in Ioi (Real.sqrt 3 / 2), Φ (-(1 / 2) + y * I))
        - ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            Φ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I))
  have hT := setIntegral_modularDomain (fun z => I • Φ' z 1 - Φ' z I)
  beta_reduce at hT
  rw [hT]
  have hA : Integrable (fun p : ℝ × ℝ => Φ' ⟨p.1, p.2⟩ I) (volume.restrict prodDomain) :=
    integrableOn_prodDomain_apply Φ' U δ hδ hDU hc hΦ' I
  have hB : Integrable (fun p : ℝ × ℝ => I • Φ' ⟨p.1, p.2⟩ 1) (volume.restrict prodDomain) :=
    (integrableOn_prodDomain_apply Φ' U δ hδ hDU hc hΦ' 1).smul I
  rw [integral_sub hB hA, integral_smul, integral_prodDomain_horiz Φ Φ' U δ hδ hDU hd hc hΦ hΦ',
    integral_prodDomain_vert Φ Φ' U δ hδ hDU hd hc hΦ hΦ', arc_split Φ Φ' U hDU hd,
    arc_sin Φ, arc_cos Φ Φ' U hDU hd]
  have e1 : ∀ y : ℝ, ((1 : ℂ) / 2 + y * I) = (⟨1 / 2, y⟩ : ℂ) := fun y =>
    Complex.ext (by simp) (by simp)
  have e2 : ∀ y : ℝ, (-((1 : ℂ) / 2) + y * I) = (⟨-(1 / 2), y⟩ : ℂ) := fun y =>
    Complex.ext (by simp) (by simp)
  simp_rw [e1, e2]
  simp only [smul_eq_mul]
  ring


end Complex
