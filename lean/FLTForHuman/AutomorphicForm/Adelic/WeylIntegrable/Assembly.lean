/-
  The assembly of the Bruhat-transversal integral bound and the shared integrability cap.

  `Asm` glues the coset measurability (`setLIntegral_slab_eq_relIndex_mul`), the
  distributive-Haar-character splitting `distribHaarChar_split` and the lattice-sum
  majorant `domG` into `integrable_weylIntegrand`; `Served` is the shared public cap
  `weylIntertwiningIntegrand_integrable_of_re_gt_half_impl` (the cousin `S_` file
  declares it `private`, the pair `public`).

  Transcribed from `S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`
  lines 2092–2366 (pinned `aa2d8b3`), sections `Asm` and `Served` of the pin namespace
  `AutomorphicForm.WeylIntegrable`. The cousin's `private` `_root_` copy at
  `S_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean:2339` is
  the same declaration; the public pin name is written once here.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.LatticeEstimates

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

section Asm

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "HOS" => HeightOneSpectrum (𝓞 F)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

-- pin: setLIntegral_vadd_slab_comp_fst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2117)
theorem setLIntegral_vadd_slab_comp_fst (μ : Measure 𝔸) [μ.IsAddLeftInvariant] {S : Set 𝔸∞} {T : Set 𝔸f} (hST : MeasurableSet (slab F S T))
    (c : 𝔸f) (h : 𝔸∞ → ℝ≥0∞) :
    ∫⁻ u in slab F S (c +ᵥ T), h u.1 ∂μ = ∫⁻ u in slab F S T, h u.1 ∂μ := by
  rw [← vadd_slab, ← lintegral_indicator (hST.const_vadd _), ← lintegral_indicator hST,
    ← lintegral_add_left_eq_self (μ := μ) (fun u => (toAdele F 0 c +ᵥ slab F S T).indicator (fun u => h u.1) u) (toAdele F 0 c)]
  refine lintegral_congr fun u => ?_
  by_cases hu : u ∈ slab F S T
  · rw [Set.indicator_of_mem (show toAdele F 0 c + u ∈ toAdele F 0 c +ᵥ slab F S T from Set.vadd_mem_vadd_set_iff.mpr hu),
      Set.indicator_of_mem hu]
    show h ((0 : 𝔸∞) + u.1) = h u.1
    rw [zero_add]
  · rw [Set.indicator_of_notMem (show toAdele F 0 c + u ∉ toAdele F 0 c +ᵥ slab F S T from fun h' => hu (Set.vadd_mem_vadd_set_iff.mp h')),
      Set.indicator_of_notMem hu]

-- pin: setLIntegral_slab_eq_relIndex_mul (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2131)
theorem setLIntegral_slab_eq_relIndex_mul (μ : Measure 𝔸) [μ.IsAddLeftInvariant] {S : Set 𝔸∞} (hS : IsClosed S)
    (A B : AddSubgroup 𝔸f) (hAB : A ≤ B) (hA : IsClosed (A : Set 𝔸f)) (hfin : A.relIndex B ≠ 0) (h : 𝔸∞ → ℝ≥0∞) :
    ∫⁻ u in slab F S B, h u.1 ∂μ = A.relIndex B * ∫⁻ u in slab F S A, h u.1 ∂μ := by
  classical
  set H : AddSubgroup B := A.addSubgroupOf B with hH
  have : H.FiniteIndex := ⟨hfin⟩
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 0
  have : Finite s := hs.finite_left_iff.mpr inferInstance
  have hcard : Nat.card s = A.relIndex B := hs.card_left
  have hcover : (B : Set 𝔸f) = ⋃ c : s, ((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f) := by
    ext b
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hb
      have hmem : (⟨b, hb⟩ : B) ∈ (Set.univ : Set B) := Set.mem_univ _
      rw [← hs.add_eq] at hmem
      obtain ⟨c, hc, h', hh, hsum⟩ := Set.mem_add.mp hmem
      refine ⟨⟨c, hc⟩, (h' : 𝔸f), ?_, ?_⟩
      · exact AddSubgroup.mem_addSubgroupOf.mp hh
      · exact congrArg Subtype.val hsum
    · rintro ⟨c, a, ha, rfl⟩
      exact B.add_mem (c : B).2 (hAB ha)
  have hdisj : Pairwise fun c c' : s => Disjoint (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) (((c' : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := by
    intro c c' hcc'
    have hd : Disjoint ((c : B) +ᵥ (H : Set B)) ((c' : B) +ᵥ (H : Set B)) :=
      hs.pairwiseDisjoint_vadd c.2 c'.2 (fun h => hcc' (Subtype.ext h))
    rw [Set.disjoint_iff_forall_ne]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ heq
    have haB : a ∈ B := hAB ha
    have ha'B : a' ∈ B := hAB ha'
    refine hd.ne_of_mem (Set.mem_vadd_set.mpr ⟨⟨a, haB⟩, AddSubgroup.mem_addSubgroupOf.mpr ha, rfl⟩)
      (Set.mem_vadd_set.mpr ⟨⟨a', ha'B⟩, AddSubgroup.mem_addSubgroupOf.mpr ha', rfl⟩) ?_
    exact Subtype.ext heq
  have hslab : slab F S B = ⋃ c : s, slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := by
    ext x; simp only [mem_slab, hcover, Set.mem_iUnion]; exact ⟨fun ⟨h1, c, h2⟩ => ⟨c, h1, h2⟩, fun ⟨c, h1, h2⟩ => ⟨h1, c, h2⟩⟩
  have hmeasA : MeasurableSet (slab F S (A : Set 𝔸f)) := (isClosed_slab F hS hA).measurableSet
  have hmeas : ∀ c : s, MeasurableSet (slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) := fun c => by
    rw [← vadd_slab]; exact hmeasA.const_vadd _
  have hdisj' : Pairwise fun c c' : s => Disjoint (slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) (slab F S (((c' : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) := by
    intro c c' hcc'
    rw [Set.disjoint_iff_forall_ne]
    rintro x ⟨-, hx⟩ x' ⟨-, hx'⟩ rfl
    exact Set.disjoint_iff_forall_ne.mp (hdisj hcc') hx hx' rfl
  have hconst : ∀ c : s, ∫⁻ u in slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)), h u.1 ∂μ = ∫⁻ u in slab F S A, h u.1 ∂μ := fun c =>
    setLIntegral_vadd_slab_comp_fst F μ hmeasA _ h
  rw [hslab, lintegral_iUnion hmeas hdisj', tsum_congr hconst]
  have := Fintype.ofFinite s
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]

-- pin: fst_mul (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2180)
theorem fst_mul (x y : 𝔸) : (x * y).1 = x.1 * y.1 := rfl

-- pin: snd_mul (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2182)
theorem snd_mul (x y : 𝔸) : (x * y).2 = x.2 * y.2 := rfl

-- pin: finPart (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2184)
def finPart (Y : (𝔸)ˣ) : (𝔸f)ˣ where
  val := (Y : 𝔸).2
  inv := ((Y⁻¹ : (𝔸)ˣ) : 𝔸).2
  val_inv := by rw [← snd_mul, Units.mul_inv]; rfl
  inv_val := by rw [← snd_mul, Units.inv_mul]; rfl

-- pin: archPart (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2190)
def archPart (Y : (𝔸)ˣ) : (𝔸)ˣ where
  val := toAdele F (Y : 𝔸).1 1
  inv := toAdele F ((Y⁻¹ : (𝔸)ˣ) : 𝔸).1 1
  val_inv := Prod.ext (show (Y : 𝔸).1 * ((Y⁻¹ : (𝔸)ˣ) : 𝔸).1 = 1 by rw [← fst_mul, Units.mul_inv]; rfl) (one_mul 1)
  inv_val := Prod.ext (show ((Y⁻¹ : (𝔸)ˣ) : 𝔸).1 * (Y : 𝔸).1 = 1 by rw [← fst_mul, Units.inv_mul]; rfl) (one_mul 1)

-- pin: archPart_mul_finIdele (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2196)
theorem archPart_mul_finIdele (Y : (𝔸)ˣ) : archPart F Y * finIdele F (finPart F Y) = Y := by
  ext : 1
  show toAdele F (Y : 𝔸).1 1 * toAdele F 1 ((Y : 𝔸).2) = (Y : 𝔸)
  exact Prod.ext (mul_one _) (one_mul _)

-- pin: distribHaarChar_split (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2201)
theorem distribHaarChar_split (Y : (𝔸)ˣ) (hY : ∀ v, 1 ≤ Valued.v ((Y : 𝔸).2 v)) :
    (distribHaarChar 𝔸 Y : ℝ≥0∞) =
      ENNReal.ofReal (∏ w : InfinitePlace F, ‖(Y : 𝔸).1 w‖ ^ w.mult) * (intLattice F).relIndex (dilate F (finPart F Y)) := by
  conv_lhs => rw [← archPart_mul_finIdele F Y, map_mul, ENNReal.coe_mul]
  congr 1
  · rw [← ENNReal.ofReal_coe_nnreal, NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one_impl F (archPart F Y) rfl]
    rfl
  · exact distribHaarChar_finIdele F (finPart F Y) (intLattice_le_dilate F hY) (relIndex_dilate_ne_zero F _)

-- pin: distribHaarChar_split_real (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2210)
theorem distribHaarChar_split_real (Y : (𝔸)ˣ) (hY : ∀ v, 1 ≤ Valued.v ((Y : 𝔸).2 v)) :
    (distribHaarChar 𝔸 Y : ℝ) = (∏ w : InfinitePlace F, ‖(Y : 𝔸).1 w‖ ^ w.mult) * ((intLattice F).relIndex (dilate F (finPart F Y)) : ℝ) := by
  have h := distribHaarChar_split F Y hY
  have hp : 0 ≤ ∏ w : InfinitePlace F, ‖(Y : 𝔸).1 w‖ ^ w.mult := Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_eq_ofReal_iff (NNReal.coe_nonneg _)
    (mul_nonneg hp (Nat.cast_nonneg _))] at h
  exact h

-- pin: norm_selY_fst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2218)
theorem norm_selY_fst (a : 𝔸∞) (b : 𝔸f) (w : InfinitePlace F) : ‖(selY F a b).1 w‖ = max 1 ‖a w‖ := by
  rw [selY_fst]
  by_cases h : BigInf F a w
  · rw [ite_eq_left h, max_eq_right (le_of_lt h)]
  · rw [ite_eq_right h, norm_one, max_eq_left (not_lt.mp h)]

-- pin: one_le_valued_selY_snd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2224)
theorem one_le_valued_selY_snd (a : 𝔸∞) (b : 𝔸f) (v : HOS) : 1 ≤ Valued.v ((selY F a b).2 v) := by
  rw [selY_snd]
  by_cases h : BigFin F b v
  · rw [ite_eq_left h]; exact (one_lt_valued_of_bigFin F h).le
  · rw [ite_eq_right h, map_one]

-- pin: valued_le_valued_selY_snd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2230)
theorem valued_le_valued_selY_snd (a : 𝔸∞) (b : 𝔸f) (v : HOS) : Valued.v (b v) ≤ Valued.v ((selY F a b).2 v) := by
  rw [selY_snd]
  by_cases h : BigFin F b v
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, map_one]
    exact (mem_adicCompletionIntegers _ _ _).mp (not_not.mp h)

-- pin: snd_mem_dilate (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2237)
theorem snd_mem_dilate (u : 𝔸) : u.2 ∈ dilate F (finPart F (yUnit (selRel F u.1 u.2))) :=
  (mem_dilate_iff F _ _).mpr fun v => valued_le_valued_selY_snd F u.1 u.2 v

-- pin: prod_norm_selY_rpow_neg (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2240)
theorem prod_norm_selY_rpow_neg (a : 𝔸∞) (b : 𝔸f) (r : ℝ) :
    (∏ w : InfinitePlace F, ‖(selY F a b).1 w‖ ^ w.mult) ^ (-r) = archWeight F r a := by
  rw [archWeight, ← Real.finsetProd_rpow Finset.univ
      (fun w => ‖(selY F a b).1 w‖ ^ w.mult) (fun w _ => pow_nonneg (norm_nonneg _) _)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [placeWeight, norm_selY_fst, ← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans (le_max_left _ _))]
  congr 1; ring

-- pin: idx (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2247)
def idx (k : HOS →₀ ℕ) : ℝ≥0∞ := ((intLattice F).relIndex (latt F k) : ℝ≥0∞)

-- pin: idx_ne_zero (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2249)
theorem idx_ne_zero (k : HOS →₀ ℕ) : idx F k ≠ 0 := by
  rw [idx, Ne, Nat.cast_eq_zero]; exact relIndex_latt_ne_zero F k

-- pin: domG (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2252)
def domG (a : ℝ) (u : 𝔸) : ℝ≥0∞ :=
  ∑' k : HOS →₀ ℕ, idx F k ^ (-a) * (slab F Set.univ (latt F k)).indicator (fun u : 𝔸 => ENNReal.ofReal (archWeight F a u.1)) u

-- pin: measurable_archWeight_comp_fst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2255)
theorem measurable_archWeight_comp_fst (a : ℝ) : Measurable fun u : 𝔸 => ENNReal.ofReal (archWeight F a u.1) :=
  ((measurable_archWeight F a).comp (measurable_adeleFst F)).ennreal_ofReal

-- pin: measurableSet_slab_latt (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2258)
theorem measurableSet_slab_latt (k : HOS →₀ ℕ) : MeasurableSet (slab F Set.univ (latt F k : Set 𝔸f)) :=
  (isClosed_slab F isClosed_univ (isCompact_latt F k).isClosed).measurableSet

-- pin: measurable_domG_term (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2261)
theorem measurable_domG_term (a : ℝ) (k : HOS →₀ ℕ) :
    Measurable fun u : 𝔸 => idx F k ^ (-a) * (slab F Set.univ (latt F k)).indicator (fun u : 𝔸 => ENNReal.ofReal (archWeight F a u.1)) u :=
  ((measurable_archWeight_comp_fst F a).indicator (measurableSet_slab_latt F k)).const_mul _

-- pin: lintegral_domG (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2265)
theorem lintegral_domG (a : ℝ) :
    ∫⁻ u, domG F a u ∂(adelicAddHaar (𝓞 F) F) =
      (∑' k : HOS →₀ ℕ, idx F k ^ (1 - a)) * ∫⁻ u in archSlab F, ENNReal.ofReal (archWeight F a u.1) ∂(adelicAddHaar (𝓞 F) F) := by
  simp only [domG]
  rw [lintegral_tsum fun k => (measurable_domG_term F a k).aemeasurable, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun k => ?_
  rw [lintegral_const_mul _ ((measurable_archWeight_comp_fst F a).indicator (measurableSet_slab_latt F k)), lintegral_indicator (measurableSet_slab_latt F k),
    setLIntegral_slab_eq_relIndex_mul F (adelicAddHaar (𝓞 F) F) isClosed_univ (intLattice F) (latt F k) (intLattice_le_latt F k)
      (isClosed_integralFiniteAdeles F) (relIndex_latt_ne_zero F k) (fun x => ENNReal.ofReal (archWeight F a x)),
    ← mul_assoc, archSlab, coe_intLattice]
  congr 1
  rw [show (1 - a) = -a + 1 by ring, ENNReal.rpow_add _ _ (idx_ne_zero F k) (ENNReal.natCast_ne_top _), ENNReal.rpow_one, idx]

-- pin: lintegral_domG_lt_top (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2278)
theorem lintegral_domG_lt_top {a : ℝ} (ha : 2 < a) : ∫⁻ u, domG F a u ∂(adelicAddHaar (𝓞 F) F) < ∞ := by
  rw [lintegral_domG]
  exact ENNReal.mul_lt_top (tsum_relIndex_rpow_lt_top F ha) (lintegral_archSlab_archWeight_lt_top F (by linarith))

-- pin: ofReal_rpow_le_domG (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2282)
theorem ofReal_rpow_le_domG (a : ℝ) (u : 𝔸) :
    ENNReal.ofReal ((distribHaarChar 𝔸 (yUnit (selRel F u.1 u.2)) : ℝ) ^ (-a)) ≤ domG F a u := by
  set Y := yUnit (selRel F u.1 u.2) with hY
  have hYval : (Y : 𝔸) = selY F u.1 u.2 := rfl
  have hv : ∀ v, 1 ≤ Valued.v ((Y : 𝔸).2 v) := fun v => by rw [hYval]; exact one_le_valued_selY_snd F u.1 u.2 v
  obtain ⟨k, hk, -⟩ := dilate_eq_latt F (finPart F Y) hv

  have hmem : u ∈ slab F Set.univ (latt F k : Set 𝔸f) := ⟨Set.mem_univ _, by rw [← hk]; exact snd_mem_dilate F u⟩
  have hterm : idx F k ^ (-a) * (slab F Set.univ (latt F k)).indicator (fun u : 𝔸 => ENNReal.ofReal (archWeight F a u.1)) u =
      ENNReal.ofReal ((distribHaarChar 𝔸 Y : ℝ) ^ (-a)) := by
    have hp : 0 ≤ ∏ w : InfinitePlace F, ‖(Y : 𝔸).1 w‖ ^ w.mult := Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _
    have hNpos : (0 : ℝ) < ((intLattice F).relIndex (dilate F (finPart F Y)) : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (relIndex_dilate_ne_zero F _))
    rw [Set.indicator_of_mem hmem, distribHaarChar_split_real F Y hv, Real.mul_rpow hp hNpos.le, hYval, prod_norm_selY_rpow_neg,
      ENNReal.ofReal_mul (archWeight_nonneg F a u.1), ← ENNReal.ofReal_rpow_of_pos hNpos, ENNReal.ofReal_natCast, idx, ← hk, mul_comm]
  rw [← hterm, domG]
  exact ENNReal.le_tsum (f := fun k => idx F k ^ (-a) *
    (slab F Set.univ (latt F k)).indicator (fun u : 𝔸 => ENNReal.ofReal (archWeight F a u.1)) u) k

-- pin: continuous_unipotentGL2' (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2299)
theorem continuous_unipotentGL2' : Continuous (fun u : 𝔸 => (unipotentGL2 u : AdelicGL2 (𝓞 F) F)) := by
  have hval : Continuous (fun u : 𝔸 => ((unipotentGL2 u : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸)) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hinv : ∀ u : 𝔸, ((unipotentGL2 u)⁻¹ : AdelicGL2 (𝓞 F) F) = unipotentGL2 (-u) := fun u =>
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp_rw [hinv]
  exact hval.comp continuous_neg

-- pin: integrable_weylIntegrand (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2310)
theorem integrable_weylIntegrand (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (hαΔ : ∀ x, ((α x : ℝˣ) : ℝ) = (distribHaarChar 𝔸 x : ℝ))
    (μc νc : (𝔸)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μc) (hν : IsUnitaryChar (𝓞 F) F νc) (s : ℂ) (hs : 1 / 2 < s.re)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsInducedSection (𝓞 F) F (etaFst μc α hα s) (etaSnd νc α hα s) φ) (hφc : Continuous φ)
    (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun u : 𝔸 => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)) (adelicAddHaar (𝓞 F) F) := by
  set a : ℝ := 2 * s.re + 1 with ha_def
  have ha2 : 2 < a := by rw [ha_def]; linarith

  have hcont : Continuous fun u : 𝔸 => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g) :=
    hφc.comp ((continuous_const.mul (continuous_unipotentGL2' F)).mul continuous_const)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩

  obtain ⟨B, hB0, hB⟩ := norm_apply_weyl_unipotent_le F α hα μc νc s φ hμ hν hφ hφc g
  have hpt : ∀ u : 𝔸, ‖φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 u * g)‖ₑ ≤ ENNReal.ofReal B * domG F a u := fun u => by
    rw [← ofReal_norm]
    refine (ENNReal.ofReal_le_ofReal (hB u)).trans ?_
    rw [ENNReal.ofReal_mul hB0, hαΔ]
    exact mul_le_mul' le_rfl (ofReal_rpow_le_domG F a u)
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_domG_lt_top F ha2)

end Asm

section Served

open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

-- pin: weylIntertwiningIntegrand_integrable_of_re_gt_half_impl (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:2341)
theorem weylIntertwiningIntegrand_integrable_of_re_gt_half_impl
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    Integrable (fun x : AdeleRing (𝓞 F) F =>
      φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * g)) (adelicAddHaar (𝓞 F) F) := by
  intro α hα μ ν hμ hν s hs φ hφ hφc g
  exact integrable_weylIntegrand F α hα (fun x => rfl) μ ν hμ hν s hs φ hφ hφc g

end Served

end AutomorphicForm.WeylIntegrable

end
