/-
  The projected-Haar frame: the generic convolution engine of the right-convolution
  commutation proof.

  `ProjectedHaar.Frame` abstracts a group `G` split as a fibre product `A × B` through
  two projections `π`, `πf` with sections `ι`, `ιf` and the separation axiom. Against a
  frame and a subgroup `Uf ≤ B` the module builds the slab `πf ⁻¹' Uf`, the level
  subgroup `ker π ⊓ πf ⁻¹' Uf`, the two-sided translates `slice`, the cut function
  `cut`, and the pushed-forward measure `nu = (μ ↾ slab).map π` — a Haar measure on `A`
  when `μ` is one and the slab is open (`nu_isHaarMeasure`). Its engine is
  `convKer_cut_comm`: a left- and right-`level`-invariant `h` has the ambient kernel
  identity against a cut function as soon as the projected identity holds on every
  slice. `KernelReduction.rc_rc` is the Fubini re-association that reduces the headline
  to a kernel identity, and `KernelSides` the continuity/support/linearity side facts.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean:25–447`
  (`ProjectedHaar`), `:675–777` (`KernelReduction`) and `:1122–1287` (`KernelSides`),
  pinned `aa2d8b3`. All three namespaces are `private` at the pin and land here public
  as the shared engine; the statements are verbatim.
-/
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory

open scoped Pointwise

noncomputable section

namespace ProjectedHaar

structure Frame (G A B : Type*) [Group G] [Group A] [Group B] where
  π : G →* A
  πf : G →* B
  ι : A →* G
  ιf : B →* G
  π_ι : ∀ a, π (ι a) = a
  πf_ι : ∀ a, πf (ι a) = 1
  π_ιf : ∀ b, π (ιf b) = 1
  πf_ιf : ∀ b, πf (ιf b) = b
  sep : ∀ x y : G, π x = π y → πf x = πf y → x = y

def _root_.ProjectedHaar.convKer {H : Type*} [Group H] [MeasurableSpace H] (m : Measure H) (P Q : H → ℂ) (x : H) : ℂ :=
  ∫ y, P y * Q (y⁻¹ * x) ∂m

section Algebra

variable {G A B : Type*} [Group G] [Group A] [Group B] (Φ : Frame G A B) (Uf : Subgroup B)

def slab : Set G := Φ.πf ⁻¹' (Uf : Set B)

def level : Subgroup G := (MonoidHom.ker Φ.π) ⊓ Uf.comap Φ.πf

def slice (h : G → ℂ) (u : G) (a : A) : ℂ := h (Φ.ι a * Φ.ιf (Φ.πf u))

def cut (fa : A → ℂ) : G → ℂ := (slab Φ Uf).indicator (fun y => fa (Φ.π y))

theorem mem_slab_iff (y : G) : y ∈ slab Φ Uf ↔ Φ.πf y ∈ Uf := Iff.rfl

theorem mem_level_iff (v : G) : v ∈ level Φ Uf ↔ Φ.π v = 1 ∧ Φ.πf v ∈ Uf := by
  simp [level, Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_comap]

theorem level_map_eq (U : Subgroup G) (hU : ∀ u ∈ U, Φ.π u = 1) : level Φ (U.map Φ.πf) = U := by
  ext v
  rw [mem_level_iff]
  constructor
  · rintro ⟨hv, hvf⟩
    obtain ⟨u, huU, hu⟩ := Subgroup.mem_map.mp hvf
    have huv : u = v := Φ.sep u v (by rw [hU u huU, hv]) hu
    exact huv ▸ huU
  · intro hv
    exact ⟨hU v hv, Subgroup.mem_map_of_mem Φ.πf hv⟩

theorem mem_slab_map_iff (U : Subgroup G) (g : G) :
    g ∈ slab Φ (U.map Φ.πf) ↔ Φ.πf g ∈ Φ.πf '' (U : Set G) := by
  rw [mem_slab_iff, ← SetLike.mem_coe, Subgroup.coe_map]

theorem cut_map_apply (U : Subgroup G) (fa : A → ℂ) (g : G) :
    cut Φ (U.map Φ.πf) fa g
      = fa (Φ.π g) * Set.indicator (Φ.πf '' (U : Set G)) (fun _ => (1 : ℂ)) (Φ.πf g) := by
  unfold cut
  by_cases hg : Φ.πf g ∈ Φ.πf '' (U : Set G)
  · rw [Set.indicator_of_mem ((mem_slab_map_iff Φ U g).mpr hg), Set.indicator_of_mem hg, mul_one]
  · rw [Set.indicator_of_notMem (fun h' => hg ((mem_slab_map_iff Φ U g).mp h')), Set.indicator_of_notMem hg,
      mul_zero]

theorem inv_ι_π_mul_mem_level {y : G} (hy : y ∈ slab Φ Uf) : (Φ.ι (Φ.π y))⁻¹ * y ∈ level Φ Uf := by
  rw [mem_level_iff]
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_inv, Φ.π_ι, inv_mul_cancel]
  · rw [map_mul, map_inv, Φ.πf_ι, inv_one, one_mul]
    exact hy

theorem eq_ι_mul_ιf (u : G) : u = Φ.ι (Φ.π u) * Φ.ιf (Φ.πf u) := by
  apply Φ.sep
  · rw [map_mul, Φ.π_ι, Φ.π_ιf, mul_one]
  · rw [map_mul, Φ.πf_ι, Φ.πf_ιf, one_mul]

theorem ι_mul_ιf_comm (a : A) (b : B) : Φ.ι a * Φ.ιf b = Φ.ιf b * Φ.ι a := by
  apply Φ.sep
  · rw [map_mul, map_mul, Φ.π_ι, Φ.π_ιf, mul_one, one_mul]
  · rw [map_mul, map_mul, Φ.πf_ι, Φ.πf_ιf, mul_one, one_mul]

theorem preimage_ι_mul_slab (a : A) : (fun y : G => Φ.ι a * y) ⁻¹' slab Φ Uf = slab Φ Uf := by
  ext y
  simp only [Set.mem_preimage, mem_slab_iff, map_mul, Φ.πf_ι, one_mul]

theorem preimage_mul_ι_slab (a : A) : (fun y : G => y * Φ.ι a) ⁻¹' slab Φ Uf = slab Φ Uf := by
  ext y
  simp only [Set.mem_preimage, mem_slab_iff, map_mul, Φ.πf_ι, mul_one]

theorem inv_mul_mem_slab_iff (u y : G) :
    (Φ.ιf (Φ.πf u) * y)⁻¹ * u ∈ slab Φ Uf ↔ y ∈ slab Φ Uf := by
  simp only [mem_slab_iff, map_mul, map_inv, _root_.mul_inv_rev, Φ.πf_ιf]
  rw [mul_assoc, inv_mul_cancel, mul_one, Subgroup.inv_mem_iff]

theorem π_inv_mul_eq (u y : G) : Φ.π ((Φ.ιf (Φ.πf u) * y)⁻¹ * u) = (Φ.π y)⁻¹ * Φ.π u := by
  simp only [map_mul, map_inv, _root_.mul_inv_rev, Φ.π_ιf, inv_one, mul_one]

theorem preimage_inter_slab_eq_image (C : Set A) :
    Φ.π ⁻¹' C ∩ slab Φ Uf = (fun p : A × B => Φ.ι p.1 * Φ.ιf p.2) '' (C ×ˢ (Uf : Set B)) := by
  ext y
  constructor
  · rintro ⟨hyC, hyS⟩
    exact ⟨(Φ.π y, Φ.πf y), ⟨hyC, hyS⟩, (eq_ι_mul_ιf Φ y).symm⟩
  · rintro ⟨⟨a, b⟩, ⟨haC, hbU⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · show Φ.π (Φ.ι a * Φ.ιf b) ∈ C
      rw [map_mul, Φ.π_ι, Φ.π_ιf, mul_one]
      exact haC
    · show Φ.πf (Φ.ι a * Φ.ιf b) ∈ Uf
      rw [map_mul, Φ.πf_ι, Φ.πf_ιf, one_mul]
      exact hbU

variable (h : G → ℂ)

theorem apply_inv_mul_eq_slice (hL : ∀ v ∈ level Φ Uf, ∀ x, h (v * x) = h x) {y : G} (hy : y ∈ slab Φ Uf)
    (u : G) : h (y⁻¹ * u) = slice Φ h u ((Φ.π y)⁻¹ * Φ.π u) := by
  have hvl := inv_ι_π_mul_mem_level Φ Uf hy
  have hy' : y = Φ.ι (Φ.π y) * ((Φ.ι (Φ.π y))⁻¹ * y) := (mul_inv_cancel_left _ _).symm
  calc h (y⁻¹ * u) = h (((Φ.ι (Φ.π y))⁻¹ * y)⁻¹ * ((Φ.ι (Φ.π y))⁻¹ * u)) := by
        conv_lhs => rw [hy']
        rw [_root_.mul_inv_rev, mul_assoc]
    _ = h ((Φ.ι (Φ.π y))⁻¹ * u) := hL _ ((level Φ Uf).inv_mem hvl) _
    _ = slice Φ h u ((Φ.π y)⁻¹ * Φ.π u) := by
        unfold slice
        rw [map_mul, map_inv, mul_assoc, ← eq_ι_mul_ιf Φ u]

theorem apply_ιf_mul_eq_slice (hR : ∀ v ∈ level Φ Uf, ∀ x, h (x * v) = h x) {y : G} (hy : y ∈ slab Φ Uf)
    (u : G) : h (Φ.ιf (Φ.πf u) * y) = slice Φ h u (Φ.π y) := by
  have hvl := inv_ι_π_mul_mem_level Φ Uf hy
  have hy' : y = Φ.ι (Φ.π y) * ((Φ.ι (Φ.π y))⁻¹ * y) := (mul_inv_cancel_left _ _).symm
  calc h (Φ.ιf (Φ.πf u) * y)
      = h ((Φ.ιf (Φ.πf u) * Φ.ι (Φ.π y)) * ((Φ.ι (Φ.π y))⁻¹ * y)) := by
        conv_lhs => rw [hy']
        rw [mul_assoc]
    _ = h (Φ.ιf (Φ.πf u) * Φ.ι (Φ.π y)) := hR _ hvl _
    _ = slice Φ h u (Φ.π y) := by unfold slice; rw [ι_mul_ιf_comm]

end Algebra

section Projection

variable {G A B : Type*} [Group G] [Group A] [Group B] [MeasurableSpace G] [MeasurableSpace A]
  (Φ : Frame G A B) (μ : Measure G) (Uf : Subgroup B)

def nu : Measure A := (μ.restrict (slab Φ Uf)).map Φ.π

end Projection

section Slice

variable {G A B : Type*} [Group G] [Group A] [Group B] [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace A]
  (Φ : Frame G A B) (h : G → ℂ)

theorem continuous_slice (hh : Continuous h) (hι : Continuous Φ.ι) (u : G) : Continuous (slice Φ h u) :=
  hh.comp (hι.mul continuous_const)

end Slice

section Integral

variable {G A B : Type*} [Group G] [Group A] [Group B] [TopologicalSpace G] [TopologicalSpace A]
  [MeasurableSpace G] [MeasurableSpace A] [BorelSpace G] [BorelSpace A]
  (Φ : Frame G A B) (μ : Measure G) (Uf : Subgroup B)

theorem setIntegral_slab (hπ : Continuous Φ.π) (g : A → ℂ) (hg : AEStronglyMeasurable g (nu Φ μ Uf)) :
    ∫ y in slab Φ Uf, g (Φ.π y) ∂μ = ∫ a, g a ∂(nu Φ μ Uf) :=
  (integral_map hπ.measurable.aemeasurable hg).symm

end Integral

section Invariance

variable {G A B : Type*} [Group G] [Group A] [Group B]
  [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalGroup G] [IsTopologicalGroup A]
  [MeasurableSpace G] [MeasurableSpace A] [BorelSpace G] [BorelSpace A]
  (Φ : Frame G A B) (μ : Measure G) (Uf : Subgroup B)

theorem nu_isMulLeftInvariant [μ.IsMulLeftInvariant] (hπ : Continuous Φ.π) (hS : MeasurableSet (slab Φ Uf)) :
    (nu Φ μ Uf).IsMulLeftInvariant := by
  refine ⟨fun a => ?_⟩
  have hcomp : (fun x : A => a * x) ∘ Φ.π = Φ.π ∘ (fun y : G => Φ.ι a * y) := by
    funext y
    simp only [Function.comp_apply, map_mul, Φ.π_ι]
  have hres : (μ.restrict (slab Φ Uf)).map (fun y : G => Φ.ι a * y) = μ.restrict (slab Φ Uf) := by
    have h1 := Measure.restrict_map (μ := μ) (measurable_const_mul (Φ.ι a)) hS
    rw [map_mul_left_eq_self μ (Φ.ι a), preimage_ι_mul_slab] at h1
    exact h1.symm
  unfold nu
  rw [Measure.map_map (measurable_const_mul a) hπ.measurable, hcomp,
    ← Measure.map_map hπ.measurable (measurable_const_mul (Φ.ι a)), hres]

theorem nu_isMulRightInvariant [μ.IsMulRightInvariant] (hπ : Continuous Φ.π)
    (hS : MeasurableSet (slab Φ Uf)) : (nu Φ μ Uf).IsMulRightInvariant := by
  refine ⟨fun a => ?_⟩
  have hcomp : (fun x : A => x * a) ∘ Φ.π = Φ.π ∘ (fun y : G => y * Φ.ι a) := by
    funext y
    simp only [Function.comp_apply, map_mul, Φ.π_ι]
  have hres : (μ.restrict (slab Φ Uf)).map (fun y : G => y * Φ.ι a) = μ.restrict (slab Φ Uf) := by
    have h1 := Measure.restrict_map (μ := μ) (measurable_mul_const (Φ.ι a)) hS
    rw [map_mul_right_eq_self μ (Φ.ι a), preimage_mul_ι_slab] at h1
    exact h1.symm
  unfold nu
  rw [Measure.map_map (measurable_mul_const a) hπ.measurable, hcomp,
    ← Measure.map_map hπ.measurable (measurable_mul_const (Φ.ι a)), hres]

variable (fa : A → ℂ) (h : G → ℂ)

theorem convKer_cut_left (hπ : Continuous Φ.π) (hS : MeasurableSet (slab Φ Uf)) (hfa : Measurable fa)
    (hh : Continuous h) (hι : Continuous Φ.ι) (hL : ∀ v ∈ level Φ Uf, ∀ x, h (v * x) = h x) (u : G) :
    convKer μ (cut Φ Uf fa) h u = convKer (nu Φ μ Uf) fa (slice Φ h u) (Φ.π u) := by
  unfold convKer
  have h1 : ∀ y, cut Φ Uf fa y * h (y⁻¹ * u)
      = (slab Φ Uf).indicator (fun y => fa (Φ.π y) * h (y⁻¹ * u)) y := by
    intro y
    simp only [cut]
    by_cases hy : y ∈ slab Φ Uf
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
  simp_rw [h1]
  rw [integral_indicator hS]
  have h2 : ∫ y in slab Φ Uf, fa (Φ.π y) * h (y⁻¹ * u) ∂μ
      = ∫ y in slab Φ Uf, (fun a => fa a * slice Φ h u (a⁻¹ * Φ.π u)) (Φ.π y) ∂μ := by
    refine setIntegral_congr_fun hS fun y hy => ?_
    simp only
    rw [apply_inv_mul_eq_slice Φ Uf h hL hy u]
  rw [h2]
  refine setIntegral_slab Φ μ Uf hπ (fun a => fa a * slice Φ h u (a⁻¹ * Φ.π u)) ?_
  exact (hfa.mul ((continuous_slice Φ h hh hι u).measurable.comp
    (measurable_inv.mul_const _))).aestronglyMeasurable

theorem convKer_cut_right [μ.IsMulLeftInvariant] (hπ : Continuous Φ.π) (hS : MeasurableSet (slab Φ Uf))
    (hfa : Measurable fa) (hh : Continuous h) (hι : Continuous Φ.ι)
    (hR : ∀ v ∈ level Φ Uf, ∀ x, h (x * v) = h x) (u : G) :
    convKer μ h (cut Φ Uf fa) u = convKer (nu Φ μ Uf) (slice Φ h u) fa (Φ.π u) := by
  unfold convKer
  rw [← integral_mul_left_eq_self (fun y => h y * cut Φ Uf fa (y⁻¹ * u)) (Φ.ιf (Φ.πf u))]
  have h1 : ∀ y, (fun y => h y * cut Φ Uf fa (y⁻¹ * u)) (Φ.ιf (Φ.πf u) * y)
      = (slab Φ Uf).indicator (fun y => h (Φ.ιf (Φ.πf u) * y) * fa ((Φ.π y)⁻¹ * Φ.π u)) y := by
    intro y
    simp only [cut]
    by_cases hy : y ∈ slab Φ Uf
    · rw [Set.indicator_of_mem ((inv_mul_mem_slab_iff Φ Uf u y).mpr hy), Set.indicator_of_mem hy, π_inv_mul_eq]
    · rw [Set.indicator_of_notMem (fun h' => hy ((inv_mul_mem_slab_iff Φ Uf u y).mp h')),
        Set.indicator_of_notMem hy, mul_zero]
  simp_rw [h1]
  rw [integral_indicator hS]
  have h2 : ∫ y in slab Φ Uf, h (Φ.ιf (Φ.πf u) * y) * fa ((Φ.π y)⁻¹ * Φ.π u) ∂μ
      = ∫ y in slab Φ Uf, (fun a => slice Φ h u a * fa (a⁻¹ * Φ.π u)) (Φ.π y) ∂μ := by
    refine setIntegral_congr_fun hS fun y hy => ?_
    simp only
    rw [apply_ιf_mul_eq_slice Φ Uf h hR hy u]
  rw [h2]
  refine setIntegral_slab Φ μ Uf hπ (fun a => slice Φ h u a * fa (a⁻¹ * Φ.π u)) ?_
  exact ((continuous_slice Φ h hh hι u).measurable.mul
    (hfa.comp (measurable_inv.mul_const _))).aestronglyMeasurable

theorem convKer_cut_comm [μ.IsMulLeftInvariant] (hπ : Continuous Φ.π) (hS : MeasurableSet (slab Φ Uf))
    (hfa : Measurable fa) (hh : Continuous h) (hι : Continuous Φ.ι)
    (hL : ∀ v ∈ level Φ Uf, ∀ x, h (v * x) = h x) (hR : ∀ v ∈ level Φ Uf, ∀ x, h (x * v) = h x)
    (hcentral : ∀ u : G, convKer (nu Φ μ Uf) fa (slice Φ h u) = convKer (nu Φ μ Uf) (slice Φ h u) fa) :
    convKer μ (cut Φ Uf fa) h = convKer μ h (cut Φ Uf fa) := by
  funext u
  rw [convKer_cut_left Φ μ Uf fa h hπ hS hfa hh hι hL u, convKer_cut_right Φ μ Uf fa h hπ hS hfa hh hι hR u,
    hcentral u]

end Invariance

section HaarApply

variable {G A B : Type*} [Group G] [Group A] [Group B] [TopologicalSpace G] [TopologicalSpace A]
  [MeasurableSpace G] [MeasurableSpace A] [BorelSpace G] [BorelSpace A]
  (Φ : Frame G A B) (μ : Measure G) (Uf : Subgroup B)

theorem nu_apply (hπ : Continuous Φ.π) {C : Set A} (hC : MeasurableSet C) :
    nu Φ μ Uf C = μ (Φ.π ⁻¹' C ∩ slab Φ Uf) := by
  unfold nu
  rw [Measure.map_apply hπ.measurable hC, Measure.restrict_apply (hπ.measurable hC)]

theorem nu_isOpenPosMeasure [μ.IsOpenPosMeasure] (hπ : Continuous Φ.π) (hS : IsOpen (slab Φ Uf)) :
    (nu Φ μ Uf).IsOpenPosMeasure := by
  refine ⟨fun O hO hne => ?_⟩
  rw [nu_apply Φ μ Uf hπ hO.measurableSet]
  obtain ⟨o, ho⟩ := hne
  refine ((hO.preimage hπ).inter hS).measure_ne_zero (μ := μ) ⟨Φ.ι o, ?_, ?_⟩
  · show Φ.π (Φ.ι o) ∈ O
    rw [Φ.π_ι]
    exact ho
  · show Φ.πf (Φ.ι o) ∈ Uf
    rw [Φ.πf_ι]
    exact Uf.one_mem

end HaarApply

section HaarCompact

variable {G A B : Type*} [Group G] [Group A] [Group B] [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace B]
  [ContinuousMul G] [MeasurableSpace G] [MeasurableSpace A] [BorelSpace G] [BorelSpace A]
  (Φ : Frame G A B) (μ : Measure G) (Uf : Subgroup B)

theorem nu_isFiniteMeasureOnCompacts [T2Space A] [IsFiniteMeasureOnCompacts μ] (hπ : Continuous Φ.π)
    (hι : Continuous Φ.ι) (hιf : Continuous Φ.ιf) (hUf : IsCompact (Uf : Set B)) :
    IsFiniteMeasureOnCompacts (nu Φ μ Uf) := by
  refine ⟨fun C hC => ?_⟩
  rw [nu_apply Φ μ Uf hπ hC.measurableSet, preimage_inter_slab_eq_image]
  exact ((hC.prod hUf).image ((hι.comp continuous_fst).mul (hιf.comp continuous_snd))).measure_lt_top

end HaarCompact

section Haar

variable {G A B : Type*} [Group G] [Group A] [Group B]
  [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup G] [IsTopologicalGroup A]
  [MeasurableSpace G] [MeasurableSpace A] [BorelSpace G] [BorelSpace A]
  (Φ : Frame G A B) (μ : Measure G) (Uf : Subgroup B)

theorem nu_isHaarMeasure [T2Space A] [μ.IsHaarMeasure] (hπ : Continuous Φ.π) (hι : Continuous Φ.ι)
    (hιf : Continuous Φ.ιf) (hUf : IsCompact (Uf : Set B)) (hS : IsOpen (slab Φ Uf)) : (nu Φ μ Uf).IsHaarMeasure :=
  { toIsFiniteMeasureOnCompacts := nu_isFiniteMeasureOnCompacts Φ μ Uf hπ hι hιf hUf
    toIsMulLeftInvariant := nu_isMulLeftInvariant Φ μ Uf hπ hS.measurableSet
    toIsOpenPosMeasure := nu_isOpenPosMeasure Φ μ Uf hπ hS }

end Haar

section EquivAlgebra

variable {G A B : Type*} [Group G] [Group A] [Group B] (Φ : Frame G A B) (Uf : Subgroup B)

theorem ι_mul_comm_of_mem_level {v : G} (hv : v ∈ level Φ Uf) (k : A) : Φ.ι k * v = v * Φ.ι k := by
  have hv' : v = Φ.ιf (Φ.πf v) := by
    conv_lhs => rw [eq_ι_mul_ιf Φ v]
    rw [((mem_level_iff Φ Uf v).mp hv).1, map_one, one_mul]
  rw [hv', ι_mul_ιf_comm]

theorem level_invariant_left_translate (h : G → ℂ) (c : G) (hc : ∀ v ∈ level Φ Uf, c * v = v * c)
    (hL : ∀ v ∈ level Φ Uf, ∀ x, h (v * x) = h x) (hR : ∀ v ∈ level Φ Uf, ∀ x, h (x * v) = h x) :
    (∀ v ∈ level Φ Uf, ∀ x, h (c⁻¹ * (v * x)) = h (c⁻¹ * x)) ∧
      ∀ v ∈ level Φ Uf, ∀ x, h (c⁻¹ * (x * v)) = h (c⁻¹ * x) := by
  have hc' : ∀ v ∈ level Φ Uf, c⁻¹ * v = v * c⁻¹ := fun v hv => by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc v hv, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨fun v hv x => ?_, fun v hv x => ?_⟩
  · rw [← mul_assoc, hc' v hv, mul_assoc, hL v hv]
  · rw [← mul_assoc, hR v hv]

theorem level_invariant_right_translate (h : G → ℂ) (c : G) (hc : ∀ v ∈ level Φ Uf, c * v = v * c)
    (hL : ∀ v ∈ level Φ Uf, ∀ x, h (v * x) = h x) (hR : ∀ v ∈ level Φ Uf, ∀ x, h (x * v) = h x) :
    (∀ v ∈ level Φ Uf, ∀ x, h (v * x * c) = h (x * c)) ∧
      ∀ v ∈ level Φ Uf, ∀ x, h (x * v * c) = h (x * c) := by
  refine ⟨fun v hv x => ?_, fun v hv x => ?_⟩
  · rw [mul_assoc, hL v hv]
  · rw [mul_assoc, ← hc v hv, ← mul_assoc, hR v hv]

theorem ι_comm_level (k : A) : ∀ v ∈ level Φ Uf, Φ.ι k * v = v * Φ.ι k :=
  fun _ hv => ι_mul_comm_of_mem_level Φ Uf hv k

theorem conj_ι_mem_slab_iff (k : A) (x : G) : Φ.ι k * x * (Φ.ι k)⁻¹ ∈ slab Φ Uf ↔ x ∈ slab Φ Uf := by
  simp only [mem_slab_iff, map_mul, map_inv, Φ.πf_ι, one_mul, inv_one, mul_one]

theorem cut_conj_ι (fa : A → ℂ) (k : A) (hfa : ∀ a, fa (k * a * k⁻¹) = fa a) (x : G) :
    cut Φ Uf fa (Φ.ι k * x * (Φ.ι k)⁻¹) = cut Φ Uf fa x := by
  unfold cut
  by_cases hx : x ∈ slab Φ Uf
  · rw [Set.indicator_of_mem ((conj_ι_mem_slab_iff Φ Uf k x).mpr hx), Set.indicator_of_mem hx, map_mul, map_mul,
      map_inv, Φ.π_ι, hfa]
  · rw [Set.indicator_of_notMem (fun h' => hx ((conj_ι_mem_slab_iff Φ Uf k x).mp h')), Set.indicator_of_notMem hx]

theorem slice_conj (h : G → ℂ) (k : A) (hh : ∀ x, h (Φ.ι k * x * (Φ.ι k)⁻¹) = h x) (u : G) (a : A) :
    slice Φ h u (k * a * k⁻¹) = slice Φ h u a := by
  unfold slice
  have hcomm : (Φ.ι k)⁻¹ * Φ.ιf (Φ.πf u) = Φ.ιf (Φ.πf u) * (Φ.ι k)⁻¹ := by
    rw [← map_inv]
    exact ι_mul_ιf_comm Φ k⁻¹ _
  rw [← hh (Φ.ι a * Φ.ιf (Φ.πf u))]
  congr 1
  rw [map_mul, map_mul, map_inv, mul_assoc (Φ.ι k * Φ.ι a), hcomm]
  simp only [mul_assoc]

end EquivAlgebra

section EquivKernelAlgebra

variable {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G)

theorem convKer_right_arg (P Q : G → ℂ) (c x : G) :
    convKer μ P (fun y => Q (y * c)) x = convKer μ P Q (x * c) := by
  unfold convKer
  congr 1
  funext y
  simp only [mul_assoc]

end EquivKernelAlgebra

section EquivKernel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G)

theorem convKer_left_fun [μ.IsMulLeftInvariant] (F P : G → ℂ) (c x : G) :
    convKer μ (fun y => F (c⁻¹ * y)) P x = convKer μ F P (c⁻¹ * x) := by
  unfold convKer
  rw [← integral_mul_left_eq_self (fun y => F (c⁻¹ * y) * P (y⁻¹ * x)) c]
  congr 1
  funext y
  simp only [inv_mul_cancel_left, _root_.mul_inv_rev, mul_assoc]

theorem convKer_left_arg [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (P Q : G → ℂ) (c : G)
    (hP : ∀ y, P (c * y * c⁻¹) = P y) (x : G) :
    convKer μ P (fun y => Q (c⁻¹ * y)) x = convKer μ P Q (c⁻¹ * x) := by
  unfold convKer
  rw [← integral_mul_right_eq_self (fun y => P y * Q (c⁻¹ * (y⁻¹ * x))) c⁻¹]
  rw [← integral_mul_left_eq_self (fun y => P (y * c⁻¹) * Q (c⁻¹ * ((y * c⁻¹)⁻¹ * x))) c]
  congr 1
  funext y
  rw [hP]
  congr 2
  group

theorem convKer_right_fun [μ.IsMulRightInvariant] (F P : G → ℂ) (c : G) (hP : ∀ y, P (c * y * c⁻¹) = P y)
    (x : G) : convKer μ (fun y => F (y * c)) P x = convKer μ F P (x * c) := by
  unfold convKer
  rw [← integral_mul_right_eq_self (fun y => F (y * c) * P (y⁻¹ * x)) c⁻¹]
  congr 1
  funext y
  rw [inv_mul_cancel_right]
  congr 1
  rw [show (y * c⁻¹)⁻¹ * x = c * (y⁻¹ * (x * c)) * c⁻¹ by group, hP]

end EquivKernel

end ProjectedHaar

namespace KernelReduction

def _root_.KernelReduction.convKer {H : Type*} [Group H] [MeasurableSpace H] (m : Measure H) (P Q : H → ℂ) (x : H) : ℂ :=
  ∫ y, P y * Q (y⁻¹ * x) ∂m

def rc {H : Type*} [Group H] [MeasurableSpace H] (m : Measure H) (φ f : H → ℂ) (g : H) : ℂ :=
  ∫ x, φ (g * x) * f x ∂m

section Substitution

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant]

theorem rc_mul (φ f : G → ℂ) (g y : G) : rc μ φ f (g * y) = ∫ x, φ (g * x) * f (y⁻¹ * x) ∂μ := by
  unfold rc
  rw [← integral_mul_left_eq_self (fun x => φ (g * x) * f (y⁻¹ * x)) y]
  congr 1
  funext x
  simp only [mul_assoc, inv_mul_cancel_left]

end Substitution

section Support

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem hasCompactSupport_integrand (φ f h : G → ℂ) (g : G) (hfc : HasCompactSupport f)
    (hhc : HasCompactSupport h) :
    HasCompactSupport fun p : G × G => φ (g * p.1) * f (p.2⁻¹ * p.1) * h p.2 := by
  refine HasCompactSupport.intro ((hhc.isCompact.mul hfc.isCompact).prod hhc.isCompact) ?_
  rintro ⟨x, y⟩ hxy
  by_cases hy : y ∈ tsupport h
  · have hx : x ∉ tsupport h * tsupport f := fun hx => hxy ⟨hx, hy⟩
    have hfx : f (y⁻¹ * x) = 0 := by
      by_contra hne
      have hmem := Set.mul_mem_mul hy (subset_tsupport f (Function.mem_support.mpr hne))
      rw [mul_inv_cancel_left] at hmem
      exact hx hmem
    simp [hfx]
  · have hy0 : h y = 0 := by
      by_contra hne
      exact hy (subset_tsupport h (Function.mem_support.mpr hne))
    simp [hy0]

theorem continuous_integrand (φ f h : G → ℂ) (g : G) (hφ : Continuous φ) (hf : Continuous f)
    (hh : Continuous h) : Continuous fun p : G × G => φ (g * p.1) * f (p.2⁻¹ * p.1) * h p.2 :=
  ((hφ.comp (continuous_const.mul continuous_fst)).mul
    (hf.comp (continuous_snd.inv.mul continuous_fst))).mul (hh.comp continuous_snd)

end Support

section Reduction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

theorem rc_rc (φ f h : G → ℂ) (hφ : Continuous φ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h) (g : G) :
    rc μ (rc μ φ f) h g = rc μ φ (convKer μ h f) g := by
  have hint : Integrable (fun p : G × G => φ (g * p.1) * f (p.2⁻¹ * p.1) * h p.2) (μ.prod μ) :=
    (continuous_integrand φ f h g hφ hf hh).integrable_of_hasCompactSupport
      (hasCompactSupport_integrand φ f h g hfc hhc)
  calc rc μ (rc μ φ f) h g
      = ∫ y, (∫ x, φ (g * x) * f (y⁻¹ * x) ∂μ) * h y ∂μ := by
        unfold rc
        congr 1
        funext y
        rw [← rc_mul μ φ f g y]
        rfl
    _ = ∫ y, ∫ x, φ (g * x) * f (y⁻¹ * x) * h y ∂μ ∂μ := by
        congr 1
        funext y
        rw [← integral_mul_const]
    _ = ∫ x, ∫ y, φ (g * x) * f (y⁻¹ * x) * h y ∂μ ∂μ :=
        (integral_integral_swap (f := fun x y => φ (g * x) * f (y⁻¹ * x) * h y) hint).symm
    _ = ∫ x, φ (g * x) * convKer μ h f x ∂μ := by
        congr 1
        funext x
        unfold convKer
        rw [← integral_const_mul]
        congr 1
        funext y
        ring
    _ = rc μ φ (convKer μ h f) g := rfl

end Reduction

end KernelReduction

namespace KernelSides

section FrameFactors

variable {G A B : Type*} [Group G] [Group A] [Group B] [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace B]
  (Φ : ProjectedHaar.Frame G A B)

theorem continuous_of_factors (hπ : Continuous Φ.π) (hπf : Continuous Φ.πf) {h : G → ℂ} {fa : A → ℂ}
    {ff : B → ℂ}
    (hfa : Continuous fa) (hff : Continuous ff) (hh : ∀ g, h g = fa (Φ.π g) * ff (Φ.πf g)) : Continuous h := by
  have : h = fun g => fa (Φ.π g) * ff (Φ.πf g) := funext hh
  rw [this]
  exact (hfa.comp hπ).mul (hff.comp hπf)

variable [IsTopologicalGroup G]

theorem hasCompactSupport_of_factors (hι : Continuous Φ.ι) (hιf : Continuous Φ.ιf) {h : G → ℂ} {fa : A → ℂ}
    {ff : B → ℂ} (hfa : HasCompactSupport fa) (hff : HasCompactSupport ff)
    (hh : ∀ g, h g = fa (Φ.π g) * ff (Φ.πf g)) : HasCompactSupport h := by
  refine HasCompactSupport.intro
    ((hfa.isCompact.prod hff.isCompact).image ((hι.comp continuous_fst).mul (hιf.comp continuous_snd))) ?_
  intro g hg
  rw [hh g]
  by_cases ha : Φ.π g ∈ tsupport fa
  · have hb : Φ.πf g ∉ tsupport ff := fun hb =>
      hg ⟨(Φ.π g, Φ.πf g), ⟨ha, hb⟩, (ProjectedHaar.eq_ι_mul_ιf Φ g).symm⟩
    have h0 : ff (Φ.πf g) = 0 := by
      by_contra hne
      exact hb (subset_tsupport ff (Function.mem_support.mpr hne))
    rw [h0, mul_zero]
  · have h0 : fa (Φ.π g) = 0 := by
      by_contra hne
      exact ha (subset_tsupport fa (Function.mem_support.mpr hne))
    rw [h0, zero_mul]

end FrameFactors

section Indicator

variable {X : Type*} [TopologicalSpace X]

theorem continuous_indicator_of_isOpen_of_isClosed {S : Set X} (hSo : IsOpen S) (hSc : IsClosed S) :
    Continuous (S.indicator fun _ => (1 : ℂ)) := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ S
  · filter_upwards [hSo.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hSc.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem hasCompactSupport_indicator [R1Space X] {S : Set X} (hS : IsCompact S) :
    HasCompactSupport (S.indicator fun _ => (1 : ℂ)) :=
  HasCompactSupport.intro hS fun _ hx => Set.indicator_of_notMem hx _

end Indicator

section LinearityAlgebra

variable {H : Type*} [Group H] [MeasurableSpace H] (m : Measure H) (fa : H → ℂ)

theorem convKer_smul_right (c : ℂ) (ψ : H → ℂ) (x : H) :
    ProjectedHaar.convKer m fa (c • ψ) x = c * ProjectedHaar.convKer m fa ψ x := by
  unfold ProjectedHaar.convKer
  have h : (fun y => fa y * (c • ψ) (y⁻¹ * x)) = fun y => c * (fa y * ψ (y⁻¹ * x)) := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  rw [h, integral_const_mul]

theorem convKer_zero_right (x : H) : ProjectedHaar.convKer m fa (0 : H → ℂ) x = 0 := by
  unfold ProjectedHaar.convKer
  simp only [Pi.zero_apply, mul_zero, integral_zero]

theorem convKer_smul_left (c : ℂ) (ψ : H → ℂ) (x : H) :
    ProjectedHaar.convKer m (c • ψ) fa x = c * ProjectedHaar.convKer m ψ fa x := by
  unfold ProjectedHaar.convKer
  have h : (fun y => (c • ψ) y * fa (y⁻¹ * x)) = fun y => c * (ψ y * fa (y⁻¹ * x)) := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [h, integral_const_mul]

theorem convKer_zero_left (x : H) : ProjectedHaar.convKer m (0 : H → ℂ) fa x = 0 := by
  unfold ProjectedHaar.convKer
  simp only [Pi.zero_apply, zero_mul, integral_zero]

end LinearityAlgebra

section Linearity

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  (m : Measure H) [IsFiniteMeasureOnCompacts m] (fa : H → ℂ)

theorem integrable_right_integrand (hfa : Continuous fa) (hfs : HasCompactSupport fa) (ψ : H → ℂ)
    (hψ : Continuous ψ) (x : H) : Integrable (fun y => fa y * ψ (y⁻¹ * x)) m := by
  have hc : Continuous fun y => fa y * ψ (y⁻¹ * x) := hfa.mul (hψ.comp (continuous_inv.mul continuous_const))
  have hs : HasCompactSupport fun y => fa y * ψ (y⁻¹ * x) := by
    refine HasCompactSupport.intro hfs.isCompact fun y hy => ?_
    have h0 : fa y = 0 := by
      by_contra hne
      exact hy (subset_tsupport fa (Function.mem_support.mpr hne))
    show fa y * ψ (y⁻¹ * x) = 0
    rw [h0, zero_mul]
  exact hc.integrable_of_hasCompactSupport hs

theorem integrable_left_integrand (hfa : Continuous fa) (hfs : HasCompactSupport fa) (ψ : H → ℂ)
    (hψ : Continuous ψ) (x : H) : Integrable (fun y => ψ y * fa (y⁻¹ * x)) m := by
  have hc : Continuous fun y => ψ y * fa (y⁻¹ * x) := hψ.mul (hfa.comp (continuous_inv.mul continuous_const))
  have hs : HasCompactSupport fun y => ψ y * fa (y⁻¹ * x) := by
    have hK : IsCompact ((fun s : H => x * s⁻¹) '' tsupport fa) :=
      hfs.isCompact.image (continuous_const.mul continuous_inv)
    refine HasCompactSupport.intro hK fun y hy => ?_
    have h0 : fa (y⁻¹ * x) = 0 := by
      by_contra hne
      refine hy ⟨y⁻¹ * x, subset_tsupport fa (Function.mem_support.mpr hne), ?_⟩
      show x * (y⁻¹ * x)⁻¹ = y
      group
    show ψ y * fa (y⁻¹ * x) = 0
    rw [h0, mul_zero]
  exact hc.integrable_of_hasCompactSupport hs

theorem convKer_add_right (hfa : Continuous fa) (hfs : HasCompactSupport fa) (ψ₁ ψ₂ : H → ℂ)
    (hψ₁ : Continuous ψ₁) (hψ₂ : Continuous ψ₂) (x : H) :
    ProjectedHaar.convKer m fa (ψ₁ + ψ₂) x
      = ProjectedHaar.convKer m fa ψ₁ x + ProjectedHaar.convKer m fa ψ₂ x := by
  unfold ProjectedHaar.convKer
  have h : (fun y => fa y * (ψ₁ + ψ₂) (y⁻¹ * x)) = fun y => fa y * ψ₁ (y⁻¹ * x) + fa y * ψ₂ (y⁻¹ * x) := by
    funext y
    rw [Pi.add_apply, mul_add]
  rw [h]
  exact integral_add (integrable_right_integrand m fa hfa hfs ψ₁ hψ₁ x)
    (integrable_right_integrand m fa hfa hfs ψ₂ hψ₂ x)

theorem convKer_add_left (hfa : Continuous fa) (hfs : HasCompactSupport fa) (ψ₁ ψ₂ : H → ℂ)
    (hψ₁ : Continuous ψ₁) (hψ₂ : Continuous ψ₂) (x : H) :
    ProjectedHaar.convKer m (ψ₁ + ψ₂) fa x
      = ProjectedHaar.convKer m ψ₁ fa x + ProjectedHaar.convKer m ψ₂ fa x := by
  unfold ProjectedHaar.convKer
  have h : (fun y => (ψ₁ + ψ₂) y * fa (y⁻¹ * x)) = fun y => ψ₁ y * fa (y⁻¹ * x) + ψ₂ y * fa (y⁻¹ * x) := by
    funext y
    rw [Pi.add_apply, add_mul]
  rw [h]
  exact integral_add (integrable_left_integrand m fa hfa hfs ψ₁ hψ₁ x)
    (integrable_left_integrand m fa hfa hfs ψ₂ hψ₂ x)

end Linearity

end KernelSides

end
