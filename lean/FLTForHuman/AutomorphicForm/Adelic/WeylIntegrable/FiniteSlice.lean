/-
  Integrability of the Weyl intertwining integrand over the finite-adèle slice.

  `adelicWeyl` is the Weyl element of `GL₂(𝔸_F)` and the Weyl intertwining operator integrates
  `φ (adelicWeyl * unipotentGL2 (0, t) * g)` over the adèle ring. This module supplies the analytic
  core on the **finite** part: for an induced-section vector `φ` at the parameters `etaFst μ α s` /
  `etaSnd ν α s` with `Re s > 1/2`, the finite-adèle slice
  `t ↦ φ (adelicWeyl * n(0, t) * g)` is integrable for any Haar measure on `𝔸_F^fin`.

  It is the finite-adelization of the archimedean integrability the `WeylIntegrable` trio carries, and
  the input to the Euler-product evaluation of the unramified integral. Transcribed from the pin's `S_`
  file and its `Theorems/` wrapper (pinned `aa2d8b3`, 1,349 lines / 133 declarations).

  The analytic core — the lattice-sum majorant `domGf` and the integrals that bound it — is the pin's
  `M4aP3C.Rho7cSol` chapter (`S_…:1118–1304`), transcribed into `AutomorphicForm.WeylIntegrable`
  beside the archimedean twin `domG` of `WeylIntegrable/Assembly.lean`: the pin's `M4aP3C.Rho7cSol`
  chapter labels are pipeline ids, not mathematics, and are dropped (playbook §4). The pin's own
  lattice, transfer, box and pointwise blocks (`S_…:33–1111`) are already landed in
  `WeylIntegrable/{Coset,Transfer,BoxBounds,LatticeEstimates,Assembly}.lean`; those declarations are
  imported here, not re-spelled.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half.lean
-/
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.Assembly
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.AdelicHaar NumberField.AdelicBox
  AutomorphicForm MeasureTheory IsDedekindDomain
open scoped NNReal ENNReal Pointwise

namespace AutomorphicForm

namespace WeylIntegrable

section FinSlice

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "HOS" => HeightOneSpectrum (𝓞 F)

-- the countable index type of the lattice sum, from `LatticeEstimates`
attribute [local instance] countable_heightOneSpectrum countable_finsupp

/-- At finite-part zero the finite coordinates of `selY` are trivial, so its archimedean part is `1`. -/
theorem selY_fst_zero (t : 𝔸f) (w : InfinitePlace F) : (selY F 0 t).1 w = 1 := by
  rw [selY_fst, ite_eq_right]
  intro h
  have h0 : (0 : 𝔸∞) w = 0 := rfl
  rw [BigInf, h0, norm_zero] at h
  exact (not_lt.mpr zero_le_one) h

/-- The archimedean part of `yUnit (selRel F 0 t)` is the identity idèle. -/
theorem archPart_yUnit_zero (t : 𝔸f) : archPart F (yUnit (selRel F 0 t)) = 1 := by
  ext : 1
  show toAdele F (selY F 0 t).1 1 = (1 : 𝔸)
  exact Prod.ext (funext fun w => selY_fst_zero F t w) rfl

/-- The finite point `t` lies in the lattice dilated by the finite component of `yUnit (selRel F 0 t)`. -/
theorem mem_dilate_finPart (t : 𝔸f) : t ∈ dilate F (finPart F (yUnit (selRel F 0 t))) :=
  (mem_dilate_iff F _ _).mpr fun v => valued_le_valued_selY_snd F 0 t v

/-- `distribHaarChar` of `yUnit (selRel F 0 t)` is the relative index of the dilated lattice. -/
theorem distribHaarChar_yUnit_zero (t : 𝔸f) :
    (distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0∞) =
      (intLattice F).relIndex (dilate F (finPart F (yUnit (selRel F 0 t)))) := by
  have hv : ∀ v, 1 ≤ Valued.v (((finPart F (yUnit (selRel F 0 t)) : (𝔸f)ˣ) : 𝔸f) v) := fun v =>
    one_le_valued_selY_snd F 0 t v
  conv_lhs => rw [← archPart_mul_finIdele F (yUnit (selRel F 0 t)), map_mul, ENNReal.coe_mul, archPart_yUnit_zero F t,
    map_one, ENNReal.coe_one, one_mul]
  exact distribHaarChar_finIdele F (finPart F (yUnit (selRel F 0 t))) (intLattice_le_dilate F hv) (relIndex_dilate_ne_zero F _)

/-- The measure of a subgroup equals its relative index times the measure of a finite-index
subgroup, for any left-invariant measure on the finite adèles. -/
theorem measure_addSubgroup_eq_relIndex_mul [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (σ : Measure 𝔸f) [σ.IsAddLeftInvariant]
    (A B : AddSubgroup 𝔸f) (hAB : A ≤ B) (hA : IsClosed (A : Set 𝔸f)) (hfin : A.relIndex B ≠ 0) :
    σ B = A.relIndex B * σ A := by
  classical
  set H : AddSubgroup B := A.addSubgroupOf B with hH
  have : H.FiniteIndex := ⟨hfin⟩
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 0
  have : Finite s := hs.finite_left_iff.mpr inferInstance
  have hcard : Nat.card s = A.relIndex B := hs.card_left
  have hcover : (B : Set 𝔸f) = ⋃ c : s, ((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f) := by
    ext b
    simp only [Set.mem_iUnion, Set.mem_vadd_set, SetLike.mem_coe]
    constructor
    · intro hb
      have hmem : (⟨b, hb⟩ : B) ∈ (Set.univ : Set B) := Set.mem_univ _
      rw [← hs.add_eq] at hmem
      obtain ⟨c, hc, h, hh, hsum⟩ := Set.mem_add.mp hmem
      refine ⟨⟨c, hc⟩, (h : 𝔸f), ?_, ?_⟩
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
  have hmeasA : MeasurableSet (A : Set 𝔸f) := hA.measurableSet
  have hmeas : ∀ c : s, MeasurableSet (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := fun c => hmeasA.const_vadd _
  have hconst : ∀ c : s, σ (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) = σ A := fun c => by rw [measure_vadd]
  rw [hcover, measure_iUnion hdisj hmeas, tsum_congr hconst]
  have := Fintype.ofFinite s
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]

/-- The integral finite adèles, as a closed additive subgroup. -/
theorem isClosed_intLattice : IsClosed (intLattice F : Set 𝔸f) := by
  rw [coe_intLattice]; exact isClosed_integralFiniteAdeles F

/-- The lattice-sum majorant on the finite adèles: the dilated lattice indicators weighted by
`idx ^ (-a)`. -/
def domGf (a : ℝ) (t : 𝔸f) : ℝ≥0∞ :=
  ∑' k : HOS →₀ ℕ, idx F k ^ (-a) * (latt F k : Set 𝔸f).indicator 1 t

theorem measurableSet_latt [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (k : HOS →₀ ℕ) : MeasurableSet (latt F k : Set 𝔸f) :=
  (isCompact_latt F k).isClosed.measurableSet

theorem measurable_domGf_term [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (a : ℝ) (k : HOS →₀ ℕ) :
    Measurable fun t : 𝔸f => idx F k ^ (-a) * (latt F k : Set 𝔸f).indicator 1 t :=
  (measurable_one.indicator (measurableSet_latt F k)).const_mul _

/-- The integral of `domGf` is the lattice-sum times the measure of the integral lattice. -/
theorem lintegral_domGf [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (σ : Measure 𝔸f) [σ.IsAddLeftInvariant] (a : ℝ) :
    ∫⁻ t, domGf F a t ∂σ = (∑' k : HOS →₀ ℕ, idx F k ^ (1 - a)) * σ (integralFiniteAdeles (𝓞 F) F) := by
  simp only [domGf]
  rw [lintegral_tsum fun k => (measurable_domGf_term F a k).aemeasurable, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun k => ?_
  rw [lintegral_const_mul _ (measurable_one.indicator (measurableSet_latt F k)),
    lintegral_indicator_one (measurableSet_latt F k),
    measure_addSubgroup_eq_relIndex_mul F σ (intLattice F) (latt F k) (intLattice_le_latt F k) (isClosed_intLattice F)
      (relIndex_latt_ne_zero F k),
    coe_intLattice, ← mul_assoc]
  congr 1
  rw [show (1 - a) = -a + 1 by ring, ENNReal.rpow_add _ _ (idx_ne_zero F k) (ENNReal.natCast_ne_top _), ENNReal.rpow_one, idx]

/-- `domGf` is integrable for `a > 2`: the lattice sum converges and the integral lattice is
compact. -/
theorem lintegral_domGf_lt_top [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (σ : Measure 𝔸f) [σ.IsAddLeftInvariant] [IsFiniteMeasureOnCompacts σ]
    {a : ℝ} (ha : 2 < a) : ∫⁻ t, domGf F a t ∂σ < ∞ := by
  rw [lintegral_domGf]
  exact ENNReal.mul_lt_top (tsum_relIndex_rpow_lt_top F ha) (isCompact_integralFiniteAdeles F).measure_lt_top

/-- The single-lattice term dominates `distribHaarChar ^ (-a)`: the `yUnit` lattice is one of the
summands of `domGf`. -/
theorem ofReal_rpow_le_domGf (a : ℝ) (t : 𝔸f) :
    ENNReal.ofReal ((distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ) ^ (-a)) ≤ domGf F a t := by
  have hv : ∀ v, 1 ≤ Valued.v (((finPart F (yUnit (selRel F 0 t)) : (𝔸f)ˣ) : 𝔸f) v) := fun v =>
    one_le_valued_selY_snd F 0 t v
  obtain ⟨k, hk, -⟩ := dilate_eq_latt F (finPart F (yUnit (selRel F 0 t))) hv
  have hmem : t ∈ (latt F k : Set 𝔸f) := by
    have h := mem_dilate_finPart F t
    rw [hk] at h
    exact h
  have hN : (distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0∞) = (((intLattice F).relIndex (latt F k) : ℕ) : ℝ≥0∞) := by
    rw [distribHaarChar_yUnit_zero F t, hk]
  have hNR : ((distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0) : ℝ) = ((intLattice F).relIndex (latt F k) : ℝ) := by
    have h2 : (distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0) = (((intLattice F).relIndex (latt F k) : ℕ) : ℝ≥0) := by
      exact_mod_cast hN
    rw [h2, NNReal.coe_natCast]
  have hNpos : (0 : ℝ) < ((intLattice F).relIndex (latt F k) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (relIndex_latt_ne_zero F k))
  have hterm : idx F k ^ (-a) * (latt F k : Set 𝔸f).indicator 1 t =
      ENNReal.ofReal (((distribHaarChar 𝔸 (yUnit (selRel F 0 t)) : ℝ≥0) : ℝ) ^ (-a)) := by
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one, hNR, ← ENNReal.ofReal_rpow_of_pos hNpos,
      ENNReal.ofReal_natCast, idx]
  rw [← hterm, domGf]
  exact ENNReal.le_tsum (f := fun k => idx F k ^ (-a) * (latt F k : Set 𝔸f).indicator 1 t) k

/-- The finite-adèle unipotent slice `t ↦ unipotentGL2 (0, t)` is continuous. -/
theorem continuous_unipotentGL2_slice :
    Continuous (fun t : 𝔸f => (unipotentGL2 (toAdele F 0 t) : AdelicGL2 (𝓞 F) F)) := by
  have hval : Continuous (fun u : 𝔸 => ((unipotentGL2 u : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸)) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hinv : ∀ u : 𝔸, ((unipotentGL2 u)⁻¹ : AdelicGL2 (𝓞 F) F) = unipotentGL2 (-u) := fun u =>
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
  have hu : Continuous (fun u : 𝔸 => (unipotentGL2 u : AdelicGL2 (𝓞 F) F)) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    simp_rw [hinv]
    exact hval.comp continuous_neg
  have hta : Continuous (fun t : 𝔸f => toAdele F 0 t) := continuous_const.prodMk continuous_id
  exact hu.comp hta

/-- The finite-adèle slice of the Weyl integrand is integrable for `Re s > 1/2`, for any Haar
measure on the finite adèles. -/
theorem integrable_weylIntegrand_finSlice [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)] (σ : Measure 𝔸f) [σ.IsAddHaarMeasure]
    (α : (𝔸)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (hαΔ : ∀ x, ((α x : ℝˣ) : ℝ) = (distribHaarChar 𝔸 x : ℝ))
    (μc νc : (𝔸)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μc) (hν : IsUnitaryChar (𝓞 F) F νc) (s : ℂ) (hs : 1 / 2 < s.re)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsInducedSection (𝓞 F) F (etaFst μc α hα s) (etaSnd νc α hα s) φ) (hφc : Continuous φ)
    (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun t : 𝔸f => φ (adelicWeyl (𝓞 F) F * unipotentGL2 (toAdele F 0 t) * g)) σ := by
  set a : ℝ := 2 * s.re + 1 with ha_def
  have ha2 : 2 < a := by rw [ha_def]; linarith

  have hcont : Continuous fun t : 𝔸f => φ (adelicWeyl (𝓞 F) F * unipotentGL2 (toAdele F 0 t) * g) :=
    hφc.comp ((continuous_const.mul (continuous_unipotentGL2_slice F)).mul continuous_const)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩

  obtain ⟨B, hB0, hB⟩ := norm_apply_weyl_unipotent_le F α hα μc νc s φ hμ hν hφ hφc g
  have hpt : ∀ t : 𝔸f, ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (toAdele F 0 t) * g)‖ₑ ≤
      ENNReal.ofReal B * domGf F a t := fun t => by
    rw [← ofReal_norm]
    have hBt := hB (toAdele F 0 t)
    rw [adelicWeyl_inv'] at hBt
    refine (ENNReal.ofReal_le_ofReal hBt).trans ?_
    rw [ENNReal.ofReal_mul hB0, hαΔ]
    exact mul_le_mul' le_rfl (ofReal_rpow_le_domGf F a t)
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_domGf_lt_top F σ ha2)

end FinSlice

end WeylIntegrable

theorem weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)]
    [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (σ : Measure (FiniteAdeleRing (𝓞 F) F))
    [σ.IsAddHaarMeasure] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ)
      (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ)
      (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    Integrable (fun t : FiniteAdeleRing (𝓞 F) F =>
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (R := AdeleRing (𝓞 F) F) (0, t) * g)) σ
    := by
  intro α hα μ ν hμ hν s hs φ hφ hφc g
  exact WeylIntegrable.integrable_weylIntegrand_finSlice F σ α hα (fun x => rfl) μ ν hμ hν s hs φ hφ hφc g

end AutomorphicForm
