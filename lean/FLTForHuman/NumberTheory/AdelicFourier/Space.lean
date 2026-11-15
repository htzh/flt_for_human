/-
  The Schwartz–Bruhat space of the adèles.

  `pureTensorSet F` and its ℂ-span `schwartzBruhat F` are the pin's space of test functions on
  `𝔸_F`.  This module carries the two algebraic facts the Fourier theory runs on — the space is
  closed under additive translation (`comp_add_right_mem_pureTensorSet`), under multiplication by a
  unit idèle (`comp_mul_mem_schwartzBruhat`) and under multiplication by a rational scalar
  (`comp_mul_algebraMap_mem_pureTensorSet`) — and the two analytic facts: every
  Schwartz–Bruhat function is integrable for an additive Haar measure
  (`integrable_of_mem_schwartzBruhat`) and its diagonal translates are summable
  (`summable_translate_of_mem_schwartzBruhat`).

  The integrability proof builds the pin's cell decomposition of the adèles — the closed
  fundamental cell `mixedCell` of the lattice `mixedEmbedding.integerLattice F`, the archimedean
  cell `archCell`, and the shifted cells `cell K l` — and bounds a pure tensor by the Gaussian-type
  majorant `exists_one_add_norm_pow_mul_norm_le`; the summability proof sums the same majorant over
  the lattice.

  Transcribed from the pin's proof files (pinned `aa2d8b3`), whose label namespaces `D2cPrime`,
  `Ws25DIL` and the `Ws25`-style section names are rectified to `NumberField.AdelicFourier`.

  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_comp_add_right_mem_pureTensorSet.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_comp_mul_algebraMap_mem_pureTensorSet.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_comp_mul_mem_schwartzBruhat.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicFourier_summable_translate_of_mem_schwartzBruhat.lean
-/
import FLTForHuman.NumberTheory.AdelicFourier
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.Countability
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicBox NumberField.InfiniteAdeleRing IsDedekindDomain
open MeasureTheory
open scoped SchwartzMap Classical NNReal ENNReal

namespace NumberField.AdelicFourier

section MulLeftAction

def mulLeftCLE {A : Type*} [CommRing A] [Algebra ℝ A] [TopologicalSpace A] [ContinuousMul A]
    (c c' : A) (h : c' * c = 1) : A ≃L[ℝ] A where
  toFun x := c * x
  invFun x := c' * x
  map_add' x y := mul_add c x y
  map_smul' r x := by simp only [RingHom.id_apply, mul_smul_comm]
  left_inv x := by show c' * (c * x) = x; rw [← mul_assoc, h, one_mul]
  right_inv x := by show c * (c' * x) = x; rw [← mul_assoc, mul_comm c, h, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id


def mulLeftHomeomorph {A : Type*} [CommRing A] [TopologicalSpace A] [ContinuousMul A]
    (c c' : A) (h : c' * c = 1) : A ≃ₜ A where
  toFun x := c * x
  invFun x := c' * x
  left_inv x := by show c' * (c * x) = x; rw [← mul_assoc, h, one_mul]
  right_inv x := by show c * (c' * x) = x; rw [← mul_assoc, mul_comm c, h, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def mulLeftLinearEquiv {A : Type*} [CommRing A] [Algebra ℝ A] (c c' : A) (h : c' * c = 1) :
    A ≃ₗ[ℝ] A where
  toFun x := c * x
  invFun x := c' * x
  map_add' x y := mul_add c x y
  map_smul' r x := by simp only [RingHom.id_apply, mul_smul_comm]
  left_inv x := by show c' * (c * x) = x; rw [← mul_assoc, h, one_mul]
  right_inv x := by show c * (c' * x) = x; rw [← mul_assoc, mul_comm c, h, one_mul]

end MulLeftAction

section PureTensor

variable (F : Type) [Field F] [NumberField F]

theorem comp_mul_algebraMap_mem_pureTensorSet {a : F} (ha : a ≠ 0)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x ↦ f (algebraMap F (AdeleRing (𝓞 F) F) a * x)) ∈ pureTensorSet F := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf

  set c : mixedEmbedding.mixedSpace F := mixedEmbedding F a with hc
  set c' : mixedEmbedding.mixedSpace F := mixedEmbedding F a⁻¹ with hc'
  have hcc : c' * c = 1 := by rw [hc, hc', ← map_mul, inv_mul_cancel₀ ha, map_one]
  let M : mixedEmbedding.mixedSpace F ≃L[ℝ] mixedEmbedding.mixedSpace F :=
    (mulLeftLinearEquiv c c' hcc).toContinuousLinearEquiv
  have _ : ∀ v, M v = c * v := fun v => rfl
  let g' : 𝓢(mixedEmbedding.mixedSpace F, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ M g
  have hg' : ∀ v, g' v = g (c * v) := fun v => by
    show (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ M g) v = _
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    rfl

  set d : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) a with hd
  set d' : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ with hd'
  have hdd : d' * d = 1 := by rw [hd, hd', ← map_mul, inv_mul_cancel₀ ha, map_one]
  let Φ : FiniteAdeleRing (𝓞 F) F ≃ₜ FiniteAdeleRing (𝓞 F) F := mulLeftHomeomorph d d' hdd
  have hΦ : (fun z => h (d * z)) = h ∘ Φ := rfl
  refine ⟨g', fun z => h (d * z), hlc.comp_continuous (continuous_const.mul continuous_id),
    by rw [hΦ]; exact hcs.comp_homeomorph Φ, ?_⟩
  funext x
  have h1 : (algebraMap F (AdeleRing (𝓞 F) F) a * x).1 = algebraMap F (InfiniteAdeleRing F) a * x.1 := rfl
  have h2 : (algebraMap F (AdeleRing (𝓞 F) F) a * x).2 = d * x.2 := rfl
  show g (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) a * x).1)
      * h (algebraMap F (AdeleRing (𝓞 F) F) a * x).2
    = g' (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h (d * x.2)
  rw [h1, h2, map_mul, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hg']
theorem comp_mul_mem_pureTensorSet (y : (AdeleRing (𝓞 F) F)ˣ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x ↦ f (↑y * x)) ∈ pureTensorSet F := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
  have hyinv : (↑y⁻¹ : AdeleRing (𝓞 F) F) * ↑y = 1 := y.inv_mul

  set c := InfiniteAdeleRing.ringEquiv_mixedSpace F (↑y : AdeleRing (𝓞 F) F).1 with hc
  set c' := InfiniteAdeleRing.ringEquiv_mixedSpace F (↑y⁻¹ : AdeleRing (𝓞 F) F).1 with hc'
  have hcc : c' * c = 1 := by
    rw [hc, hc', ← map_mul]
    have h1 : (↑y⁻¹ : AdeleRing (𝓞 F) F).1 * (↑y : AdeleRing (𝓞 F) F).1
        = (1 : AdeleRing (𝓞 F) F).1 := congrArg Prod.fst hyinv
    rw [h1]; exact map_one _
  let M := mulLeftCLE c c' hcc
  let g' : 𝓢(mixedEmbedding.mixedSpace F, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ M g
  have hg' : ∀ v, g' v = g (c * v) := fun v => by
    show (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ M g) v = _
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]; rfl

  set d := (↑y : AdeleRing (𝓞 F) F).2 with hd
  set d' := (↑y⁻¹ : AdeleRing (𝓞 F) F).2 with hd'
  have hdd : d' * d = 1 := congrArg Prod.snd hyinv
  let Φ := mulLeftHomeomorph d d' hdd
  have hΦ : (fun z => h (d * z)) = h ∘ Φ := rfl
  refine ⟨g', fun z => h (d * z), hlc.comp_continuous (continuous_const.mul continuous_id),
    by rw [hΦ]; exact hcs.comp_homeomorph Φ, ?_⟩
  funext x
  have h1 : (↑y * x : AdeleRing (𝓞 F) F).1 = (↑y : AdeleRing (𝓞 F) F).1 * x.1 := rfl
  have h2 : (↑y * x : AdeleRing (𝓞 F) F).2 = d * x.2 := rfl
  show g (InfiniteAdeleRing.ringEquiv_mixedSpace F (↑y * x : AdeleRing (𝓞 F) F).1)
      * h (↑y * x : AdeleRing (𝓞 F) F).2
    = g' (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h (d * x.2)
  rw [h1, h2, map_mul, hg']

theorem comp_mul_mem_schwartzBruhat (y : (AdeleRing (𝓞 F) F)ˣ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    (fun x ↦ f (↑y * x)) ∈ schwartzBruhat F := by
  -- The ascription on `↑y` is load-bearing: `· * x` only constrains the coercion's target up to
  -- unification, so without it the elaborator leaves the coercion a metavariable over the motive's
  -- local context, and solving it against the goal is an `isDefEq` that unfolds `AdeleRing`, the
  -- `InfiniteAdeleRing` function type and the completion quotient along with the `Mul` instance.
  refine schwartzBruhat_induction (F := F)
    (p := fun f _ => (fun x ↦ f ((↑y : AdeleRing (𝓞 F) F) * x)) ∈ schwartzBruhat F) ?_ ?_ ?_ ?_ hf
  · intro f hf
    exact mem_schwartzBruhat_of_mem_pureTensorSet (comp_mul_mem_pureTensorSet F y hf)
  · exact zero_mem_schwartzBruhat
  · intro f g _ _ hf hg
    exact Submodule.add_mem _ hf hg
  · intro c f _ hf
    exact Submodule.smul_mem _ c hf

theorem comp_add_right_mem_pureTensorSet
    {F : Type*} [Field F] [NumberField F] (y : AdeleRing (𝓞 F) F)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    (fun x => f (x + y)) ∈ pureTensorSet F := by
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
  set c := InfiniteAdeleRing.ringEquiv_mixedSpace F y.1
  have hTG : Function.HasTemperateGrowth (fun z : mixedEmbedding.mixedSpace F => z + c) :=
    Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const c)
  have hUp : ∃ (k : ℕ) (C : ℝ), ∀ z : mixedEmbedding.mixedSpace F,
      ‖z‖ ≤ C * (1 + ‖z + c‖) ^ k := by
    refine ⟨1, 1 + ‖c‖, fun z => ?_⟩
    have h1 : ‖z‖ ≤ ‖z + c‖ + ‖c‖ := by
      have := norm_add_le (z + c) (-c); simp only [add_neg_cancel_right, norm_neg] at this
      exact this
    nlinarith [norm_nonneg (z + c), norm_nonneg c]
  refine ⟨SchwartzMap.compCLM ℝ hTG hUp g, fun z => h (z + y.2),
    hlc.comp_continuous (continuous_add_const y.2),
    hcs.comp_homeomorph (Homeomorph.addRight y.2), ?_⟩
  funext x

  simp only [SchwartzMap.compCLM_apply, Function.comp_apply]
  congr 1
  rw [show (x + y).1 = x.1 + y.1 from rfl]
  exact congrArg g (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) x.1 y.1)

end PureTensor

section Cells

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "E∞" => mixedEmbedding.mixedSpace F

theorem exists_one_add_norm_pow_mul_norm_le (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (k : ℕ) :
    ∃ C : ℝ, ∀ y : mixedEmbedding.mixedSpace F, (1 + ‖y‖) ^ k * ‖g y‖ ≤ C := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g, fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl g y
  rwa [norm_iteratedFDeriv_zero] at h

def mixedCell : Set E∞ := closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))

theorem isCompact_mixedCell : IsCompact (mixedCell F) := by
  exact (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis F)).isCompact_closure

theorem isClosed_mixedCell : IsClosed (mixedCell F) := by
  exact isClosed_closure

theorem exists_norm_le_of_mem_mixedCell : ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ mixedCell F, ‖q‖ ≤ R := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (isCompact_mixedCell F).isBounded
  exact ⟨max R 0, le_max_right _ _, fun q hq => (hR q hq).trans (le_max_left _ _)⟩

def archCell : Set (InfiniteAdeleRing F) := ringEquiv_mixedSpace F ⁻¹' mixedCell F

open scoped M4aS4 in
theorem isCompact_archCell : IsCompact (archCell F) := by
  obtain ⟨R, -, hR⟩ := exists_norm_le_of_mem_mixedCell F
  have hbig : IsCompact {x : InfiniteAdeleRing F | ∀ v, ‖x v‖ ≤ R} := by
    have : {x : InfiniteAdeleRing F | ∀ v, ‖x v‖ ≤ R} =
        Set.pi Set.univ fun v : InfinitePlace F => Metric.closedBall (0 : v.Completion) R := by
      ext x
      exact ⟨fun h v _ => mem_closedBall_zero_iff.mpr (h v),
        fun h v => mem_closedBall_zero_iff.mp (h v (Set.mem_univ v))⟩
    rw [this]
    exact isCompact_univ_pi fun v => isCompact_closedBall _ _
  refine hbig.of_isClosed_subset ((isClosed_mixedCell F).preimage (AdelicBox.continuous_ringEquiv_mixedSpace F)) ?_
  intro x hx v
  have hx' : ‖ringEquiv_mixedSpace F x‖ ≤ R := hR _ hx
  by_cases hv : v.IsReal
  · exact (AdelicBox.norm_apply_le_of_isReal F x hv).trans hx'
  · exact (AdelicBox.norm_apply_le_of_isComplex F x (InfinitePlace.not_isReal_iff_isComplex.mp hv)).trans hx'

variable {F}

def cell0 (K : Set (FiniteAdeleRing (𝓞 F) F)) : Set 𝔸 := {x | x.1 ∈ archCell F ∧ x.2 ∈ K}

theorem isCompact_cell0 {K : Set (FiniteAdeleRing (𝓞 F) F)} (hK : IsCompact K) : IsCompact (cell0 K) := by
  have : IsCompact (archCell F ×ˢ K) := (isCompact_archCell F).prod hK
  exact this

def cellShift (l : E∞) : 𝔸 := ((ringEquiv_mixedSpace F).symm l, (0 : FiniteAdeleRing (𝓞 F) F))

def cell (K : Set (FiniteAdeleRing (𝓞 F) F)) (l : E∞) : Set 𝔸 := (fun z : 𝔸 => -cellShift l + z) ⁻¹' cell0 K

theorem isCompact_cell {K : Set (FiniteAdeleRing (𝓞 F) F)} (hK : IsCompact K) (l : E∞) : IsCompact (cell K l) := by
  exact (Homeomorph.addLeft (-cellShift l)).isCompact_preimage.mpr (isCompact_cell0 hK)

theorem mem_cell_iff {K : Set (FiniteAdeleRing (𝓞 F) F)} {l : E∞} {x : 𝔸} :
    x ∈ cell K l ↔ ringEquiv_mixedSpace F x.1 - l ∈ mixedCell F ∧ x.2 ∈ K := by
  show (-cellShift l + x).1 ∈ archCell F ∧ (-cellShift l + x).2 ∈ K ↔ _
  have h1 : (-cellShift l + x).1 = -(ringEquiv_mixedSpace F).symm l + x.1 := rfl
  have h2 : (-cellShift l + x).2 = -0 + x.2 := rfl
  rw [h2, neg_zero, zero_add, h1]
  simp only [archCell, Set.mem_preimage, map_add, map_neg, RingEquiv.apply_symm_apply]
  rw [neg_add_eq_sub]

theorem mem_cell_floor {K : Set (FiniteAdeleRing (𝓞 F) F)} {x : 𝔸} (hx : x.2 ∈ K) :
    x ∈ cell K (ZSpan.floor (mixedEmbedding.latticeBasis F) (ringEquiv_mixedSpace F x.1) : E∞) := by
  rw [mem_cell_iff]
  refine ⟨subset_closure ?_, hx⟩
  rw [← ZSpan.fract_apply]
  exact ZSpan.fract_mem_fundamentalDomain _ _

theorem measure_cell [MeasurableSpace 𝔸] [BorelSpace 𝔸] (μ : Measure 𝔸) [μ.IsAddLeftInvariant]
    (K : Set (FiniteAdeleRing (𝓞 F) F)) (l : E∞) : μ (cell K l) = μ (cell0 K) := by
  exact measure_preimage_add μ _ _

theorem integrable_pureTensor [MeasurableSpace 𝔸] [BorelSpace 𝔸] (μ : Measure 𝔸) [μ.IsAddHaarMeasure]
    (g : 𝓢(E∞, ℂ)) (h : FiniteAdeleRing (𝓞 F) F → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    Integrable (fun x : 𝔸 => g (ringEquiv_mixedSpace F x.1) * h x.2) μ := by

  set e := ringEquiv_mixedSpace F with he
  have hcont : Continuous fun x : 𝔸 => g (e x.1) * h x.2 :=
    (g.continuous.comp ((AdelicBox.continuous_ringEquiv_mixedSpace F).comp continuous_fst)).mul
      (hlc.continuous.comp continuous_snd)
  set f : C(𝔸, ℂ) := ⟨fun x : 𝔸 => g (e x.1) * h x.2, hcont⟩ with hf
  set K := tsupport h with hKdef
  have hK : IsCompact K := hcs

  set b := mixedEmbedding.latticeBasis F with hb
  let L : Submodule ℤ E∞ := Submodule.span ℤ (Set.range b)
  let s : L → TopologicalSpace.Compacts 𝔸 := fun l => ⟨cell K (l : E∞), isCompact_cell hK _⟩

  obtain ⟨R, hR0, hR⟩ := exists_norm_le_of_mem_mixedCell F
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hlc.continuous
  set k : ℕ := Module.finrank ℤ L + 1 with hk
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_le F g k
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hB0 : 0 ≤ max B 0 := le_max_right _ _

  have hsup : ∀ l : L, ‖f.restrict (s l)‖ ≤ max B 0 * (C * (1 + R) ^ k) / (1 + ‖(l : E∞)‖) ^ k := by
    intro l
    have hden : 0 < (1 + ‖(l : E∞)‖) ^ k := by positivity
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
    obtain ⟨x, hx⟩ := x
    have hx' : x ∈ cell K (l : E∞) := hx
    rw [mem_cell_iff] at hx'
    obtain ⟨hq, -⟩ := hx'
    have hqR : ‖e x.1 - (l : E∞)‖ ≤ R := hR _ hq

    have hcmp : 1 + ‖(l : E∞)‖ ≤ (1 + R) * (1 + ‖e x.1‖) := by
      have : ‖(l : E∞)‖ ≤ ‖e x.1‖ + R := by
        calc ‖(l : E∞)‖ = ‖e x.1 - (e x.1 - (l : E∞))‖ := by rw [sub_sub_cancel]
          _ ≤ ‖e x.1‖ + ‖e x.1 - (l : E∞)‖ := norm_sub_le _ _
          _ ≤ ‖e x.1‖ + R := by gcongr
      nlinarith [norm_nonneg (e x.1), norm_nonneg (l : E∞)]
    have hpow : (1 + ‖(l : E∞)‖) ^ k ≤ (1 + R) ^ k * (1 + ‖e x.1‖) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hcmp k

    have hg : ‖g (e x.1)‖ ≤ C / (1 + ‖e x.1‖) ^ k := by
      rw [le_div_iff₀ (by positivity), mul_comm]; exact hC _
    have hgx : ‖g (e x.1)‖ ≤ C * (1 + R) ^ k / (1 + ‖(l : E∞)‖) ^ k := by
      refine hg.trans ?_
      rw [div_le_div_iff₀ (by positivity) hden]
      calc C * (1 + ‖(l : E∞)‖) ^ k ≤ C * ((1 + R) ^ k * (1 + ‖e x.1‖) ^ k) :=
            mul_le_mul_of_nonneg_left hpow hC0
        _ = C * (1 + R) ^ k * (1 + ‖e x.1‖) ^ k := by ring
    show ‖g (e x.1) * h x.2‖ ≤ _
    rw [norm_mul]
    calc ‖g (e x.1)‖ * ‖h x.2‖ ≤ (C * (1 + R) ^ k / (1 + ‖(l : E∞)‖) ^ k) * max B 0 :=
          mul_le_mul hgx ((hB _).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
      _ = max B 0 * (C * (1 + R) ^ k) / (1 + ‖(l : E∞)‖) ^ k := by ring

  have hμ : ∀ l : L, μ.real (s l) = μ.real (cell0 K) := fun l => by
    show μ.real (cell K (l : E∞)) = μ.real (cell0 K)
    rw [measureReal_def, measureReal_def, measure_cell]
  have hsum : Summable fun l : L => ‖f.restrict (s l)‖ * μ.real (s l) := by
    simp_rw [hμ]
    refine Summable.mul_right _ ?_
    have hcomp : Summable fun l : L =>
        max B 0 * (C * (1 + R) ^ k) * ‖(l : E∞) - 0‖⁻¹ ^ k :=
      (ZLattice.summable_norm_sub_inv_pow L k (Nat.lt_succ_self _) 0).mul_left _
    refine Summable.of_norm_bounded_eventually hcomp ?_
    have hfin : {l : L | (l : E∞) = 0}.Finite :=
      Set.Subsingleton.finite fun a ha c hc => Subtype.val_injective (ha.trans hc.symm)
    filter_upwards [hfin.compl_mem_cofinite] with l hl
    have hl0 : (l : E∞) ≠ 0 := hl
    have hpos : 0 < ‖(l : E∞)‖ := norm_pos_iff.mpr hl0
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (hsup l).trans ?_
    rw [sub_zero]
    have hkey : ((1 + ‖(l : E∞)‖) ^ k)⁻¹ ≤ ‖(l : E∞)‖⁻¹ ^ k := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hpos (le_add_of_nonneg_left zero_le_one)) k
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hkey (mul_nonneg hB0 (by positivity))

  have hU : IntegrableOn f (⋃ l : L, (s l : Set 𝔸)) μ := integrableOn_iUnion_of_summable_norm_restrict hsum
  have hsupp : Function.support (fun x : 𝔸 => g (e x.1) * h x.2) ⊆ ⋃ l : L, (s l : Set 𝔸) := by
    intro x hx
    have hx2 : x.2 ∈ K := by
      refine subset_tsupport _ ?_
      intro h0
      exact hx (by simp only [h0, mul_zero])
    exact Set.mem_iUnion.mpr ⟨ZSpan.floor b (e x.1), mem_cell_floor hx2⟩
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hU

end Cells

section LatticeSum

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

private theorem exists_ringOfIntegers_of_mem_integralFiniteAdeles (k : F)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) k ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F) :
    ∃ o : 𝓞 F, (o : F) = k := by
  have hk : k ∈ (algebraMap (𝓞 F) F).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F k fun v => ?_
    have hv := h v
    have heval : (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = ((k : F) : v.adicCompletion F) := rfl
    rw [heval, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  obtain ⟨o, ho⟩ := hk
  exact ⟨o, ho⟩

theorem summable_norm_apply_add_integerLattice (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (z : mixedEmbedding.mixedSpace F) :
    Summable fun l : mixedEmbedding.integerLattice F => ‖g (z + (l : mixedEmbedding.mixedSpace F))‖ := by
  set L := mixedEmbedding.integerLattice F
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_norm_le F g (Module.finrank ℤ L + 1)
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hsum : Summable fun l : L =>
      C * ‖(l : mixedEmbedding.mixedSpace F) - (-z)‖⁻¹ ^ (Module.finrank ℤ L + 1) :=
    (ZLattice.summable_norm_sub_inv_pow L (Module.finrank ℤ L + 1) (Nat.lt_succ_self _) (-z)).mul_left C
  refine Summable.of_norm_bounded_eventually hsum ?_
  have hfin : {l : L | (l : mixedEmbedding.mixedSpace F) = -z}.Finite :=
    Set.Subsingleton.finite fun a ha b hb => Subtype.val_injective (ha.trans hb.symm)
  filter_upwards [hfin.compl_mem_cofinite] with l hl
  have hl' : (l : mixedEmbedding.mixedSpace F) - (-z) ≠ 0 := fun h => hl (sub_eq_zero.mp h)
  have hzl : z + (l : mixedEmbedding.mixedSpace F) = (l : mixedEmbedding.mixedSpace F) - (-z) := by
    rw [sub_neg_eq_add, add_comm]
  have hpos : 0 < ‖z + (l : mixedEmbedding.mixedSpace F)‖ := by
    rw [hzl]; exact norm_pos_iff.mpr hl'
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have h1 := hC (z + (l : mixedEmbedding.mixedSpace F))
  have h2 : 0 < (1 + ‖z + (l : mixedEmbedding.mixedSpace F)‖) ^ (Module.finrank ℤ L + 1) := by
    positivity
  calc ‖g (z + (l : mixedEmbedding.mixedSpace F))‖
        ≤ C / (1 + ‖z + (l : mixedEmbedding.mixedSpace F)‖) ^ (Module.finrank ℤ L + 1) := by
          rw [le_div_iff₀ h2, mul_comm]; exact h1
    _ ≤ C / ‖z + (l : mixedEmbedding.mixedSpace F)‖ ^ (Module.finrank ℤ L + 1) :=
          div_le_div_of_nonneg_left hC0 (pow_pos hpos _)
            (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) _)
    _ = C * ‖(l : mixedEmbedding.mixedSpace F) - (-z)‖⁻¹ ^ (Module.finrank ℤ L + 1) := by
          rw [hzl, div_eq_mul_inv, inv_pow]

def toIntegerLattice (o : 𝓞 F) : mixedEmbedding.integerLattice F :=
  ⟨mixedEmbedding F (o : F), LinearMap.mem_range.mpr ⟨o, rfl⟩⟩

omit [NumberField F] in
theorem coe_toIntegerLattice (o : 𝓞 F) :
    (toIntegerLattice F o : mixedEmbedding.mixedSpace F) = mixedEmbedding F (o : F) := by
  rfl

theorem toIntegerLattice_injective : Function.Injective (toIntegerLattice F) := by
  intro a b h
  have h' : mixedEmbedding F (a : F) = mixedEmbedding F (b : F) := congrArg Subtype.val h
  exact RingOfIntegers.ext ((mixedEmbedding_injective F) h')

theorem summable_norm_apply_add_mixedEmbedding (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (z : mixedEmbedding.mixedSpace F) :
    Summable fun o : 𝓞 F => ‖g (z + mixedEmbedding F (o : F))‖ := by
  have h : Summable ((fun l : mixedEmbedding.integerLattice F =>
      ‖g (z + (l : mixedEmbedding.mixedSpace F))‖) ∘ toIntegerLattice F) :=
    (summable_norm_apply_add_integerLattice F g z).comp_injective (toIntegerLattice_injective F)
  simpa only [Function.comp_def, coe_toIntegerLattice] using h

theorem zero_mem_integralFiniteAdeles' :
    (0 : FiniteAdeleRing (𝓞 F) F) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F := by
  exact fun v => (v.adicCompletionIntegers F).zero_mem

theorem sub_mem_integralFiniteAdeles {a b : FiniteAdeleRing (𝓞 F) F}
    (ha : a ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F) (hb : b ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F) :
    a - b ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F := by
  exact fun v => by
    have h__af := (v.adicCompletionIntegers F).sub_mem (ha v) (hb v); simp at h__af; exact h__af

theorem summable_translate_pureTensor (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (h : FiniteAdeleRing (𝓞 F) F → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) (x : 𝔸) :
    Summable fun ξ : F => g (ringEquiv_mixedSpace F (x + ι ξ).1) * h (x + ι ξ).2 := by
  set U := AdelicBox.integralFiniteAdeles (𝓞 F) F with hUdef
  obtain ⟨B, hB⟩ := hcs.exists_bound_of_continuous hlc.continuous

  have h1 : ∀ ξ : F, ringEquiv_mixedSpace F (x + ι ξ).1
      = ringEquiv_mixedSpace F x.1 + mixedEmbedding F ξ := fun ξ => by
    rw [mixedEmbedding_eq_algebraMap_comp, ← map_add]; rfl
  have h2 : ∀ ξ : F, (x + ι ξ).2 = x.2 + algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ := fun ξ => rfl
  simp_rw [h1, h2]
  set c := ringEquiv_mixedSpace F x.1 with hcdef
  set ιf := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hιfdef

  have hTo : ∀ y : FiniteAdeleRing (𝓞 F) F, IsOpen {w : FiniteAdeleRing (𝓞 F) F | w - y ∈ U} :=
    fun y => (AdelicBox.isOpen_integralFiniteAdeles F).preimage (continuous_sub_right y)
  obtain ⟨t, ht⟩ := (hcs : IsCompact (tsupport h)).elim_finite_subcover
    (fun y => {w : FiniteAdeleRing (𝓞 F) F | w - y ∈ U}) hTo
    (fun w _ => Set.mem_iUnion.mpr ⟨w, by
      show w - w ∈ U
      rw [sub_self]; exact zero_mem_integralFiniteAdeles' F⟩)

  let S : FiniteAdeleRing (𝓞 F) F → Set F := fun y => {ξ | x.2 + ιf ξ - y ∈ U}
  let ξ0 : FiniteAdeleRing (𝓞 F) F → F := fun y => if hy : (S y).Nonempty then hy.some else 0
  have hcoset : ∀ y, ∀ ξ ∈ S y, ∃ o : 𝓞 F, ξ = ξ0 y + o := by
    intro y ξ hξ
    have hne : (S y).Nonempty := ⟨ξ, hξ⟩
    have hξ0 : ξ0 y ∈ S y := by
      show (if hy : (S y).Nonempty then hy.some else 0) ∈ S y
      rw [dite_eq_left hne]; exact hne.some_mem
    have hdiff : ιf (ξ - ξ0 y) ∈ U := by
      have hsub := sub_mem_integralFiniteAdeles (F := F) hξ hξ0
      have heq : x.2 + ιf ξ - y - (x.2 + ιf (ξ0 y) - y) = ιf (ξ - ξ0 y) := by
        rw [map_sub]; abel
      rwa [heq] at hsub
    obtain ⟨o, ho⟩ := exists_ringOfIntegers_of_mem_integralFiniteAdeles F (ξ - ξ0 y) hdiff
    refine ⟨o, ?_⟩
    rw [ho]; abel

  let G : F → ℝ := fun ξ => ‖g (c + mixedEmbedding F ξ)‖
  have hGsum : ∀ y, Summable ((S y).indicator G) := by
    intro y
    have hφ : Function.Injective fun o : 𝓞 F => ξ0 y + (o : F) := fun a b hab =>
      RingOfIntegers.ext (add_left_cancel hab)
    refine (hφ.summable_iff ?_).mp ?_
    · intro ξ hξ
      apply Set.indicator_of_notMem
      intro hS
      obtain ⟨o, rfl⟩ := hcoset y ξ hS
      exact hξ ⟨o, rfl⟩
    · have hS' := summable_norm_apply_add_mixedEmbedding F g (c + mixedEmbedding F (ξ0 y))
      refine Summable.of_nonneg_of_le (fun o => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
        (fun o => ?_) hS'
      refine (Set.indicator_le_self' (fun _ _ => norm_nonneg _) _).trans (le_of_eq ?_)
      show ‖g (c + mixedEmbedding F (ξ0 y + (o : F)))‖ = ‖g (c + mixedEmbedding F (ξ0 y) + mixedEmbedding F (o : F))‖
      rw [map_add (mixedEmbedding F), add_assoc]

  have hdom : ∀ ξ : F, ‖g (c + mixedEmbedding F ξ) * h (x.2 + ιf ξ)‖
      ≤ max B 0 * ∑ y ∈ t, (S y).indicator G ξ := by
    intro ξ
    by_cases hz : h (x.2 + ιf ξ) = 0
    · rw [hz, mul_zero, norm_zero]
      exact mul_nonneg (le_max_right _ _)
        (Finset.sum_nonneg fun y _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
    · have hmem : x.2 + ιf ξ ∈ tsupport h := subset_tsupport _ hz
      obtain ⟨y, hy, hyU⟩ : ∃ y ∈ t, x.2 + ιf ξ - y ∈ U := by
        have := ht hmem
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at this
        obtain ⟨y, hy, hyU⟩ := this
        exact ⟨y, hy, hyU⟩
      have hξS : ξ ∈ S y := hyU
      calc ‖g (c + mixedEmbedding F ξ) * h (x.2 + ιf ξ)‖
            = ‖g (c + mixedEmbedding F ξ)‖ * ‖h (x.2 + ιf ξ)‖ := norm_mul _ _
        _ ≤ G ξ * max B 0 :=
              mul_le_mul_of_nonneg_left ((hB _).trans (le_max_left _ _)) (norm_nonneg _)
        _ = max B 0 * (S y).indicator G ξ := by rw [mul_comm, Set.indicator_of_mem hξS]
        _ ≤ max B 0 * ∑ y' ∈ t, (S y').indicator G ξ :=
              mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (f := fun y' => (S y').indicator G ξ)
                  (fun y' _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) _) hy)
                (le_max_right _ _)
  exact Summable.of_norm_bounded_eventually
    ((summable_sum fun y _ => hGsum y).mul_left (max B 0)) (Filter.Eventually.of_forall hdom)

end LatticeSum

section Headlines

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

theorem integrable_of_mem_schwartzBruhat [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (μ : Measure 𝔸) [μ.IsAddHaarMeasure] {f : 𝔸 → ℂ} (hf : f ∈ schwartzBruhat F) :
    Integrable f μ := by
  refine schwartzBruhat_induction (F := F) (p := fun f _ => Integrable f μ) ?_ ?_ ?_ ?_ hf
  · rintro f ⟨g, h, hlc, hcs, rfl⟩
    exact integrable_pureTensor μ g h hlc hcs
  · exact integrable_zero _ _ _
  · intro f g _ _ hf hg
    exact hf.add hg
  · intro c f _ hf
    exact hf.smul c

theorem summable_translate_of_mem_schwartzBruhat {f : 𝔸 → ℂ} (hf : f ∈ schwartzBruhat F) (x : 𝔸) :
    Summable fun ξ : F => f (x + ι ξ) := by
  revert x
  refine schwartzBruhat_induction (F := F)
    (p := fun f _ => ∀ x : 𝔸, Summable fun ξ : F => f (x + ι ξ)) ?_ ?_ ?_ ?_ hf
  · rintro f ⟨g, h, hlc, hcs, rfl⟩ x
    exact summable_translate_pureTensor F g h hlc hcs x
  · intro x
    exact summable_zero
  · intro f g _ _ hf hg x
    simpa [Pi.add_apply] using (hf x).add (hg x)
  · intro c f _ hf x
    simpa [Pi.smul_apply, smul_eq_mul] using (hf x).mul_left c

end Headlines

end NumberField.AdelicFourier

end
