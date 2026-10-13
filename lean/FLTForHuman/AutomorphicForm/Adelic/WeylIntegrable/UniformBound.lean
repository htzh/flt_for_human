/-
  The uniform `M`-bound and the lattice-sum summability for the Bruhat transversal.

  `exists_bound_on_unitBox_uniform`/`exists_bound_mFactor_uniform` upgrade the
  pointwise `M`-bound to a compact-set-uniform one; `norm_apply_weyl_unipotent_le_uniform`
  feeds it into the Weyl–unipotent norm estimate. `Dy` is the distributive Haar
  character of `yUnit`, shown a bounded lattice sum by translating the compact
  `Cset` over the `S2`-finite set of lattice points; `bruhatTransversal_norm_le_summable_uniform`
  and `bruhatTransversal_summand_norm_summable` conclude the Weierstrass majorant.

  Transcribed from `S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`
  lines 2369–2681 (pinned `aa2d8b3`), sections `LatticeSum` and `Uniform` of the pin
  namespace `AutomorphicForm.WeylIntegrable`.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.Assembly

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicHaar
open NumberField.AdelicBox IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Filter Asymptotics TopologicalSpace WithZero M4aS4
open scoped Classical ENNReal NNReal Topology Pointwise nonZeroDivisors

noncomputable section


open scoped ENNReal NNReal Classical Pointwise

namespace AutomorphicForm
namespace WeylIntegrable

attribute [local instance] M4aS4.placeBorel M4aS4.infMS

section LatticeSum

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "HOS" => HeightOneSpectrum (𝓞 F)
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

-- pin: Dy (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2395)
def Dy (x : 𝔸) : ℝ := (distribHaarChar 𝔸 (yUnit (selRel F x.1 x.2)) : ℝ)

-- pin: Dy_pos (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2397)
theorem Dy_pos (x : 𝔸) : 0 < Dy F x := by
  rw [Dy]; exact_mod_cast distribHaarChar_pos

-- pin: Dy_eq (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2400)
theorem Dy_eq (x : 𝔸) :
    Dy F x = (∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ w.mult) * ((intLattice F).relIndex (dilate F (finPart F (yUnit (selRel F x.1 x.2)))) : ℝ) := by
  set Y := yUnit (selRel F x.1 x.2) with hY
  have hYval : (Y : 𝔸) = selY F x.1 x.2 := rfl
  have hv : ∀ v, 1 ≤ Valued.v ((Y : 𝔸).2 v) := fun v => by rw [hYval]; exact one_le_valued_selY_snd F x.1 x.2 v
  rw [Dy, ← hY, distribHaarChar_split_real F Y hv, hYval]
  congr 1
  exact Finset.prod_congr rfl fun w _ => by rw [norm_selY_fst]

-- pin: valued_selY_snd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2409)
theorem valued_selY_snd (a : 𝔸∞) (b : 𝔸f) (v : HOS) : Valued.v ((selY F a b).2 v) = max 1 (Valued.v (b v)) := by
  rw [selY_snd]
  by_cases h : BigFin F b v
  · rw [ite_eq_left h, max_eq_right (one_lt_valued_of_bigFin F h).le]
  · rw [ite_eq_right h, map_one, max_eq_left ((mem_adicCompletionIntegers _ _ _).mp (not_not.mp h))]

-- pin: max_one_valued_add (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2415)
theorem max_one_valued_add {v : HOS} (p q : v.adicCompletion F) (hq : Valued.v q ≤ 1) : max 1 (Valued.v (p + q)) = max 1 (Valued.v p) := by
  by_cases hp : 1 < Valued.v p
  · rw [Valued.v.map_add_eq_of_lt_left (lt_of_le_of_lt hq hp)]
  · have hp' : Valued.v p ≤ 1 := not_lt.mp hp
    rw [max_eq_left hp', max_eq_left ((Valued.v.map_add p q).trans (max_le hp' hq))]

-- pin: dilate_finPart_translate (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2421)
theorem dilate_finPart_translate (x u : 𝔸) (hu : u.2 ∈ integralFiniteAdeles (𝓞 F) F) :
    dilate F (finPart F (yUnit (selRel F (x + u).1 (x + u).2))) = dilate F (finPart F (yUnit (selRel F x.1 x.2))) := by
  ext t
  rw [mem_dilate_iff, mem_dilate_iff]
  have key : ∀ v, Valued.v (((finPart F (yUnit (selRel F (x + u).1 (x + u).2)) : (𝔸f)ˣ) : 𝔸f) v) =
      Valued.v (((finPart F (yUnit (selRel F x.1 x.2)) : (𝔸f)ˣ) : 𝔸f) v) := fun v => by
    show Valued.v ((selY F (x + u).1 (x + u).2).2 v) = Valued.v ((selY F x.1 x.2).2 v)
    rw [valued_selY_snd, valued_selY_snd]
    exact max_one_valued_add F (x.2 v) (u.2 v) (hu v)
  simp only [key]

omit [NumberField F] in
-- pin: max_one_norm_add_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2433)
theorem max_one_norm_add_le {E : Type*} [SeminormedAddCommGroup E] (p q : E) (hq : ‖q‖ ≤ 1) : max 1 ‖p + q‖ ≤ 2 * max 1 ‖p‖ := by
  refine max_le (by linarith [le_max_left (1 : ℝ) ‖p‖]) ?_
  calc ‖p + q‖ ≤ ‖p‖ + ‖q‖ := norm_add_le p q
    _ ≤ max 1 ‖p‖ + max 1 ‖p‖ := add_le_add (le_max_right _ _) (hq.trans (le_max_left _ _))
    _ = 2 * max 1 ‖p‖ := by ring

-- pin: prod_max_one_norm_translate_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2439)
theorem prod_max_one_norm_translate_le (x u : 𝔸) (hu : ∀ w, ‖u.1 w‖ ≤ 1) :
    ∏ w : InfinitePlace F, (max 1 ‖(x + u).1 w‖) ^ w.mult ≤
      (2 : ℝ) ^ (∑ w : InfinitePlace F, w.mult) * ∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ w.mult := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun w _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (max_one_norm_add_le (x.1 w) (u.1 w) (hu w)) _

-- pin: Dy_translate_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2447)
theorem Dy_translate_le (x u : 𝔸) (hu1 : ∀ w, ‖u.1 w‖ ≤ 1) (hu2 : u.2 ∈ integralFiniteAdeles (𝓞 F) F) :
    Dy F (x + u) ≤ (2 : ℝ) ^ (∑ w : InfinitePlace F, w.mult) * Dy F x := by
  rw [Dy_eq, Dy_eq, dilate_finPart_translate F x u hu2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (prod_max_one_norm_translate_le F x u hu1) (Nat.cast_nonneg _)

-- pin: rpow_Dy_le_translate (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2452)
theorem rpow_Dy_le_translate (x u : 𝔸) (hu1 : ∀ w, ‖u.1 w‖ ≤ 1) (hu2 : u.2 ∈ integralFiniteAdeles (𝓞 F) F) {a : ℝ} (ha : 0 ≤ a) :
    Dy F x ^ (-a) ≤ ((2 : ℝ) ^ (∑ w : InfinitePlace F, w.mult)) ^ a * Dy F (x + u) ^ (-a) := by
  set c : ℝ := (2 : ℝ) ^ (∑ w : InfinitePlace F, w.mult) with hc
  have hcpos : 0 < c := by positivity
  have h := Real.rpow_le_rpow_of_nonpos (Dy_pos F (x + u)) (Dy_translate_le F x u hu1 hu2) (neg_nonpos.mpr ha)
  rw [Real.mul_rpow hcpos.le (Dy_pos F x).le, Real.rpow_neg hcpos.le] at h
  calc Dy F x ^ (-a) = c ^ a * ((c ^ a)⁻¹ * Dy F x ^ (-a)) := by rw [← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hcpos a).ne', one_mul]
    _ ≤ c ^ a * Dy F (x + u) ^ (-a) := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hcpos.le a)

-- pin: Cset (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2461)
def Cset : Set 𝔸 := slab F (Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) (integralFiniteAdeles (𝓞 F) F)

-- pin: mem_Cset (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2463)
theorem mem_Cset {u : 𝔸} : u ∈ Cset F ↔ (∀ w, ‖u.1 w‖ ≤ 1) ∧ u.2 ∈ integralFiniteAdeles (𝓞 F) F := by
  show ((∀ w, w ∈ Set.univ → u.1 w ∈ Metric.closedBall (0 : w.Completion) 1) ∧ u.2 ∈ integralFiniteAdeles (𝓞 F) F) ↔ _
  simp only [Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]

-- pin: isClosed_Cset (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2467)
theorem isClosed_Cset : IsClosed (Cset F) :=
  isClosed_slab F (isClosed_set_pi fun _ _ => Metric.isClosed_closedBall) (isClosed_integralFiniteAdeles F)

-- pin: measurableSet_Cset (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2470)
theorem measurableSet_Cset : MeasurableSet (Cset F) := (isClosed_Cset F).measurableSet

-- pin: isCompact_Cset (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2472)
theorem isCompact_Cset : IsCompact (Cset F) := by
  have : Cset F = (fun p : 𝔸∞ × 𝔸f => (p : 𝔸)) ''
      ((Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ integralFiniteAdeles (𝓞 F) F) := by
    ext x; simp only [Cset]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(x.1, x.2), ⟨h1, h2⟩, rfl⟩, by rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩⟩
  rw [this]
  exact ((isCompact_univ_pi fun w => isCompact_closedBall (0 : w.Completion) 1).prod (isCompact_integralFiniteAdeles F)).image continuous_id

-- pin: measure_Cset_ne_zero (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2480)
theorem measure_Cset_ne_zero : adelicAddHaar (𝓞 F) F (Cset F) ≠ 0 := by
  have hopen : IsOpen (slab F (Set.pi Set.univ fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1) (integralFiniteAdeles (𝓞 F) F)) := by
    have : slab F (Set.pi Set.univ fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1) (integralFiniteAdeles (𝓞 F) F) =
        (fun u : 𝔸 => u.1) ⁻¹' (Set.pi Set.univ fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1) ∩
          (fun u : 𝔸 => u.2) ⁻¹' integralFiniteAdeles (𝓞 F) F := rfl
    rw [this]
    exact ((isOpen_set_pi Set.finite_univ fun w _ => Metric.isOpen_ball).preimage continuous_fst).inter
      ((isOpen_integralFiniteAdeles F).preimage continuous_snd)
  have hne : (slab F (Set.pi Set.univ fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1) (integralFiniteAdeles (𝓞 F) F)).Nonempty :=
    ⟨0, ⟨fun w _ => Metric.mem_ball_self zero_lt_one, fun v => zero_mem _⟩⟩
  have hsub : slab F (Set.pi Set.univ fun w : InfinitePlace F => Metric.ball (0 : w.Completion) 1) (integralFiniteAdeles (𝓞 F) F) ⊆ Cset F :=
    fun u ⟨h1, h2⟩ => ⟨fun w hw => Metric.ball_subset_closedBall (h1 w hw), h2⟩
  exact fun h0 => (hopen.measure_pos (adelicAddHaar (𝓞 F) F) hne).ne' (measure_mono_null hsub h0)

-- pin: measure_Cset_ne_top (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2494)
theorem measure_Cset_ne_top : adelicAddHaar (𝓞 F) F (Cset F) ≠ ⊤ := (isCompact_Cset F).measure_lt_top.ne

-- pin: S2 (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2496)
def S2 : Set F := {η | (∀ w : InfinitePlace F, w η ≤ 2) ∧ ∀ v : HOS, v.valuation F η ≤ 1}

-- pin: S2_finite (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2498)
theorem S2_finite : (S2 F).Finite := by
  refine (Embeddings.finite_of_norm_le F ℂ 2).subset fun η ⟨h1, h2⟩ => ⟨?_, fun φ => ?_⟩
  · obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := 𝓞 F) F η h2
    rw [← hr]; exact RingOfIntegers.isIntegral_coe r
  · rw [← InfinitePlace.apply]; exact h1 _

-- pin: norm_algebraMap_fst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2504)
theorem norm_algebraMap_fst (η : F) (w : InfinitePlace F) : ‖(ι η).1 w‖ = w η := by
  rw [NumberField.AdeleRing.algebraMap_fst_apply]
  exact (InfinitePlace.Completion.norm_coe (v := w) (WithAbs.toAbs w.1 η)).trans rfl

-- pin: valued_algebraMap_snd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2508)
theorem valued_algebraMap_snd (η : F) (v : HOS) : Valued.v ((ι η).2 v) = v.valuation F η := by
  rw [NumberField.AdeleRing.algebraMap_snd_apply]
  exact valuedAdicCompletion_eq_valuation' v η

-- pin: sub_mem_S2 (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2512)
theorem sub_mem_S2 {ξ ξ' : F} {x : 𝔸} (h : x ∈ ι ξ +ᵥ Cset F) (h' : x ∈ ι ξ' +ᵥ Cset F) : ξ - ξ' ∈ S2 F := by
  obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.mp h
  obtain ⟨u', hu', hx⟩ := Set.mem_vadd_set.mp h'
  rw [mem_Cset] at hu hu'
  have hx' : ι ξ + u = ι ξ' + u' := hx.symm
  have hdiff : ι (ξ - ξ') = u' - u := by
    rw [map_sub]
    exact sub_eq_sub_iff_add_eq_add.mpr (hx'.trans (add_comm _ _))
  refine ⟨fun w => ?_, fun v => ?_⟩
  · rw [← norm_algebraMap_fst F, hdiff]
    calc ‖(u' - u).1 w‖ = ‖u'.1 w - u.1 w‖ := rfl
      _ ≤ ‖u'.1 w‖ + ‖u.1 w‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hu'.1 w) (hu.1 w)
      _ = 2 := by norm_num
  · rw [← valued_algebraMap_snd F, hdiff]
    exact sub_mem (hu'.2 v) (hu.2 v)

-- pin: card_filter_mem_translate_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2529)
theorem card_filter_mem_translate_le (T : Finset F) (x : 𝔸) :
    (T.filter fun ξ => x ∈ ι ξ +ᵥ Cset F).card ≤ (S2_finite F).toFinset.card := by
  classical
  by_cases hT : (T.filter fun ξ => x ∈ ι ξ +ᵥ Cset F) = ∅
  · rw [hT, Finset.card_empty]; exact Nat.zero_le _
  obtain ⟨ξ₀, hξ₀⟩ := Finset.nonempty_iff_ne_empty.mpr hT
  have hξ₀' : x ∈ ι ξ₀ +ᵥ Cset F := (Finset.mem_filter.mp hξ₀).2
  refine Finset.card_le_card_of_injOn (fun ξ => ξ - ξ₀) (fun ξ hξ => ?_) (fun ξ _ ξ' _ h => sub_left_injective h)
  rw [Finset.coe_filter] at hξ
  exact (S2_finite F).mem_toFinset.mpr (sub_mem_S2 F hξ.2 hξ₀')

-- pin: sum_indicator_translate_le (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2540)
theorem sum_indicator_translate_le (T : Finset F) (G : 𝔸 → ℝ≥0∞) (x : 𝔸) :
    ∑ ξ ∈ T, (ι ξ +ᵥ Cset F).indicator G x ≤ (S2_finite F).toFinset.card * G x := by
  classical
  have : ∑ ξ ∈ T, (ι ξ +ᵥ Cset F).indicator G x = ∑ ξ ∈ T.filter (fun ξ => x ∈ ι ξ +ᵥ Cset F), G x := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun ξ _ => by by_cases h : x ∈ ι ξ +ᵥ Cset F <;> simp [h]
  rw [this, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul' (by exact_mod_cast card_filter_mem_translate_le F T x) le_rfl

-- pin: measurable_domG (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2549)
theorem measurable_domG (a : ℝ) : Measurable (domG F a) := by
  have : domG F a = fun u => ⨆ T : Finset (HOS →₀ ℕ), ∑ k ∈ T,
      idx F k ^ (-a) * (slab F Set.univ (latt F k)).indicator (fun u : 𝔸 => ENNReal.ofReal (archWeight F a u.1)) u := by
    funext u; rw [domG, ENNReal.tsum_eq_iSup_sum]
  rw [this]
  exact Measurable.iSup fun T => Finset.measurable_fun_sum T fun k _ => measurable_domG_term F a k

-- pin: summable_rpow_Dy_algebraMap (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2556)
theorem summable_rpow_Dy_algebraMap {a : ℝ} (ha : 2 < a) : Summable (fun ξ : F => Dy F (ι ξ) ^ (-a)) := by
  have ha0 : 0 ≤ a := by linarith
  set μA := adelicAddHaar (𝓞 F) F with hμA
  set C := Cset F with hC
  set M : ℝ≥0∞ := ((S2_finite F).toFinset.card : ℝ≥0∞) with hM
  set c : ℝ≥0∞ := ENNReal.ofReal (((2 : ℝ) ^ (∑ w : InfinitePlace F, w.mult)) ^ a) with hc
  set I : ℝ≥0∞ := ∫⁻ x, domG F a x ∂μA with hI
  have hI : I < ⊤ := lintegral_domG_lt_top F ha

  set K : ℝ≥0∞ := c * M * I / μA C with hK
  have hKtop : K ≠ ⊤ := (ENNReal.div_lt_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)) hI.ne)
    (measure_Cset_ne_zero F)).ne
  refine summable_of_sum_le (fun ξ => Real.rpow_nonneg (Dy_pos F _).le _) (c := K.toReal) fun T => ?_

  rw [← ENNReal.ofReal_le_iff_le_toReal hKtop, ENNReal.ofReal_sum_of_nonneg fun ξ _ => Real.rpow_nonneg (Dy_pos F _).le _, hK,
    ENNReal.le_div_iff_mul_le (Or.inl (measure_Cset_ne_zero F)) (Or.inl (measure_Cset_ne_top F)), Finset.sum_mul]

  have hterm : ∀ ξ ∈ T, ENNReal.ofReal (Dy F (ι ξ) ^ (-a)) * μA C ≤ c * ∫⁻ x, (ι ξ +ᵥ C).indicator (domG F a) x ∂μA := fun ξ _ => by
    have hmeas : MeasurableSet (ι ξ +ᵥ C) := (measurableSet_Cset F).const_vadd _
    have hpt : ∀ x ∈ ι ξ +ᵥ C, ENNReal.ofReal (Dy F (ι ξ) ^ (-a)) ≤ c * domG F a x := fun x hx => by
      obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.mp hx
      rw [mem_Cset] at hu
      calc ENNReal.ofReal (Dy F (ι ξ) ^ (-a))
          ≤ ENNReal.ofReal (((2 : ℝ) ^ (∑ w : InfinitePlace F, w.mult)) ^ a * Dy F (ι ξ + u) ^ (-a)) :=
            ENNReal.ofReal_le_ofReal (rpow_Dy_le_translate F (ι ξ) u hu.1 hu.2 ha0)
        _ = c * ENNReal.ofReal (Dy F (ι ξ +ᵥ u) ^ (-a)) := by rw [ENNReal.ofReal_mul (by positivity)]; rfl
        _ ≤ c * domG F a (ι ξ +ᵥ u) := mul_le_mul' le_rfl (ofReal_rpow_le_domG F a _)
    calc ENNReal.ofReal (Dy F (ι ξ) ^ (-a)) * μA C = ENNReal.ofReal (Dy F (ι ξ) ^ (-a)) * μA (ι ξ +ᵥ C) := by rw [measure_vadd]
      _ = ∫⁻ x in ι ξ +ᵥ C, ENNReal.ofReal (Dy F (ι ξ) ^ (-a)) ∂μA := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in ι ξ +ᵥ C, c * domG F a x ∂μA := setLIntegral_mono' hmeas hpt
      _ = c * ∫⁻ x in ι ξ +ᵥ C, domG F a x ∂μA := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = c * ∫⁻ x, (ι ξ +ᵥ C).indicator (domG F a) x ∂μA := by rw [lintegral_indicator hmeas]
  calc ∑ ξ ∈ T, ENNReal.ofReal (Dy F (ι ξ) ^ (-a)) * μA C ≤ ∑ ξ ∈ T, c * ∫⁻ x, (ι ξ +ᵥ C).indicator (domG F a) x ∂μA := Finset.sum_le_sum hterm
    _ = c * ∫⁻ x, ∑ ξ ∈ T, (ι ξ +ᵥ C).indicator (domG F a) x ∂μA := by
        rw [← Finset.mul_sum, lintegral_finsetSum _ fun ξ _ => (measurable_domG F a).indicator ((measurableSet_Cset F).const_vadd _)]
    _ ≤ c * ∫⁻ x, M * domG F a x ∂μA := mul_le_mul' le_rfl (lintegral_mono fun x => sum_indicator_translate_le F T (domG F a) x)
    _ = c * M * I := by rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _), mul_assoc]

-- pin: jE1_hole (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2594)
theorem jE1_hole (a : ℝ) (ha : 2 < a) :
    Summable (fun ξ : F => ((distribHaarChar 𝔸 (yUnit (selRel F (algebraMap F 𝔸 ξ).1 (algebraMap F 𝔸 ξ).2)) : ℝ) ^ (-a))) :=
  summable_rpow_Dy_algebraMap F ha

end LatticeSum

end AutomorphicForm.WeylIntegrable

end

noncomputable section

open scoped NNReal

namespace AutomorphicForm
namespace WeylIntegrable

section Uniform

-- pin: exists_bound_on_unitBox_uniform (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2620)
theorem exists_bound_on_unitBox_uniform {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T1Space A] {C : Set A}
    (hC : IsCompact C) {φ : GL (Fin 2) A → ℂ} (hφ : Continuous φ) {K : Set (GL (Fin 2) A)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ k ∈ unitBox C, ∀ g ∈ K, ‖φ (k * g)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (((isCompact_unitBox hC).prod hK).image continuous_mul).exists_bound_of_continuousOn hφ.continuousOn
  exact ⟨B, fun k hk g hg => hB _ ⟨(k, g), ⟨hk, hg⟩, rfl⟩⟩

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

-- the pin's `letI` is load-bearing: it feeds the instance search below.
set_option linter.style.haveILetI false in
-- pin: exists_bound_mFactor_uniform (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2632)
theorem exists_bound_mFactor_uniform {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) {K : Set (AdelicGL2 (𝓞 F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ g ∈ K, ∀ (a : 𝔸∞) (b : 𝔸f), ‖φ (mFactor F a b * g)‖ ≤ B := by
  letI : TopologicalSpace 𝔸 := inferInstance
  obtain ⟨B, hB⟩ := exists_bound_on_unitBox_uniform (isCompact_entrySet F) hφ hK
  exact ⟨B, fun g hg a b => hB _ (mFactor_mem_unitBox F a b) g hg⟩

-- pin: norm_apply_weyl_unipotent_le_uniform (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2638)
theorem norm_apply_weyl_unipotent_le_uniform (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (𝔸)ˣ →* ℂˣ) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (hφc : Continuous φ)
    {K : Set (AdelicGL2 (𝓞 F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ K, ∀ u : 𝔸, ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)‖ ≤
      B * ((α (yUnit (selRel F u.1 u.2)) : ℝˣ) : ℝ) ^ (-(2 * s.re + 1)) := by
  obtain ⟨B, hB⟩ := exists_bound_mFactor_uniform F hφc hK
  refine ⟨max B 0, le_max_right _ _, fun g hg u => ?_⟩
  rw [norm_apply_weyl_unipotent_eq F α hα μ ν s φ hμ hν hφ u g, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hB g hg u.1 u.2).trans (le_max_left _ _)) (Real.rpow_nonneg (hα _).le _)

-- pin: bruhatTransversal_norm_le_summable_uniform (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2649)
theorem bruhatTransversal_norm_le_summable_uniform (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαΔ : ∀ x, ((α x : ℝˣ) : ℝ) = (distribHaarChar 𝔸 x : ℝ))
    (μ ν : (𝔸)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (s : ℂ) (hs : 1 / 2 < s.re)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (hφc : Continuous φ)
    {K : Set (AdelicGL2 (𝓞 F) F)} (hK : IsCompact K) :
    ∃ M : F → ℝ, Summable M ∧ ∀ g ∈ K, ∀ ξ : F,
      ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖ ≤ M ξ := by
  obtain ⟨B, hB0, hB⟩ := norm_apply_weyl_unipotent_le_uniform F α hα μ ν s φ hμ hν hφ hφc hK
  rw [adelicWeyl_inv'] at hB
  have ha : 2 < 2 * s.re + 1 := by linarith
  refine ⟨fun ξ => B * ((distribHaarChar 𝔸 (yUnit (selRel F (algebraMap F 𝔸 ξ).1 (algebraMap F 𝔸 ξ).2))) : ℝ) ^ (-(2 * s.re + 1)),
    (jE1_hole F (2 * s.re + 1) ha).mul_left B, fun g hg ξ => ?_⟩
  show _ ≤ B * _
  rw [← hαΔ]
  exact hB g hg (algebraMap F 𝔸 ξ)

-- pin: bruhatTransversal_summand_norm_summable (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2665)
theorem bruhatTransversal_summand_norm_summable (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαΔ : ∀ x, ((α x : ℝˣ) : ℝ) = (distribHaarChar 𝔸 x : ℝ))
    (μ ν : (𝔸)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) (s : ℂ) (hs : 1 / 2 < s.re)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ) (hφc : Continuous φ)
    (g : AdelicGL2 (𝓞 F) F) :
    Summable (fun ξ : F => ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F 𝔸 ξ) * g)‖) := by
  obtain ⟨M, hM, hle⟩ := bruhatTransversal_norm_le_summable_uniform F α hα hαΔ μ ν hμ hν s hs φ hφ hφc isCompact_singleton
  exact Summable.of_nonneg_of_le (fun ξ => norm_nonneg _) (fun ξ => hle g (Set.mem_singleton g) ξ) hM

end Uniform

end AutomorphicForm.WeylIntegrable

end
