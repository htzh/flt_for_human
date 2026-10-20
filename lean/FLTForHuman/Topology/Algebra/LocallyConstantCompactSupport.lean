/-
  Two locally-constant-function supplements:

  * `IsLocallyConstant.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport` —
    a locally constant function with compact support on a topological group is
    invariant under a two-sided neighbourhood `V` of `1`;
  * `IsLocallyConstant.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport` —
    consequently `(k, k') ↦ (s ↦ f (k * n s * k'))` is locally constant on `G × G`.

  The ports of the two pin leaves (95 and 62 pin lines), together with the
  statements of their `Theorems/` wrappers. They are one module because the
  second's proof uses the first (dot notation on `hf`).

  The mathematics of the first: at each `g` the set `O g = V g · g · V g` is a
  neighbourhood of `g` (translation is an open map), finitely many of them cover
  the compact support, and the intersection `V₀` of the corresponding `V g` works:
  points inside the cover are handled by the fourfold invariance of `f` at the
  covering centre, points outside by vanishing (both in the support and in the
  translates, since `V₀ ⊆ V₀⁻¹`).

  The mathematics of the second: near `(k₀, k₀')` both `k k₀⁻¹` and `k₀'⁻¹ k'` lie
  in `V`, and `k * n s * k' = (k k₀⁻¹) * (k₀ * n s * k₀') * (k₀'⁻¹ k')`.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): mathlib has neither statement — `rg -n
  "exists_nhds_one_forall_apply_mul_mul"` and `rg -n
  "isLocallyConstant_fun_mul_apply_mul"` over `Mathlib/` find nothing; the
  ingredients (`IsLocallyConstant.isOpen_fiber`, `MemNhdsProd`,
  `IsCompact.elim_nhds_subcover`, `biInter_finset_mem`, `inv_mem_nhds_one`,
  `image_eq_zero_of_notMem_tsupport`, `IsLocallyConstant.iff_eventually_eq`,
  `IsLocallyConstant.range_finite`) are imported, not restated.

  Drift: `haveI`/`letI` handling per the linter; the pin's inline `#print axioms`
  commands are verification, not port content, and are not carried.

  spec-pin: Theorems/Thm_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport.lean
  spec-pin: P2M/Sol/S_IsLocallyConstant_exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport.lean
  spec-pin: Theorems/Thm_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport.lean
  spec-pin: P2M/Sol/S_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport.lean
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

open Filter Topology Set

namespace M4aP3B
namespace Rows
namespace UniformLocConst

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]

omit [Zero Y] in

theorem exists_nhds_fourfold {f : G → Y} (hf : IsLocallyConstant f) (g : G) :
    ∃ V ∈ 𝓝 (1 : G), ∀ u ∈ V, ∀ v ∈ V, ∀ v' ∈ V, ∀ u' ∈ V, f (u * v * g * v' * u') = f g := by
  have hc : Continuous fun p : G × G × G × G => p.1 * p.2.1 * g * p.2.2.1 * p.2.2.2 := by fun_prop
  have ho : IsOpen ((fun p : G × G × G × G => p.1 * p.2.1 * g * p.2.2.1 * p.2.2.2) ⁻¹' {x | f x = f g}) :=
    (hf.isOpen_fiber (f g)).preimage hc
  have hmem : ((1 : G), (1 : G), (1 : G), (1 : G))
      ∈ (fun p : G × G × G × G => p.1 * p.2.1 * g * p.2.2.1 * p.2.2.2) ⁻¹' {x | f x = f g} := by
    simp
  have hn := ho.mem_nhds hmem
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hn
  obtain ⟨A₂, hA₂, B₂, hB₂, hAB₂⟩ := mem_nhds_prod_iff.1 hB
  obtain ⟨A₃, hA₃, A₄, hA₄, hAB₃⟩ := mem_nhds_prod_iff.1 hB₂
  refine ⟨A ∩ A₂ ∩ A₃ ∩ A₄, inter_mem (inter_mem (inter_mem hA hA₂) hA₃) hA₄, ?_⟩
  intro u hu v hv v' hv' u' hu'
  have : (u, v, v', u') ∈ (fun p : G × G × G × G => p.1 * p.2.1 * g * p.2.2.1 * p.2.2.2) ⁻¹'
      {x | f x = f g} :=
    hAB ⟨hu.1.1.1, hAB₂ ⟨hv.1.1.2, hAB₃ ⟨hv'.1.2, hu'.2⟩⟩⟩
  simpa using this

theorem exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport_impl
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) :
    ∃ V ∈ nhds (1 : G), ∀ u ∈ V, ∀ u' ∈ V, ∀ g : G, f (u * g * u') = f g := by
  classical
  choose V hV hV4 using exists_nhds_fourfold hf

  set O : G → Set G := fun g => (fun p : G × G => p.1 * g * p.2) '' (V g ×ˢ V g) with hO
  have hOn : ∀ g, O g ∈ 𝓝 g := by
    intro g
    have h1 : (fun v => v * g) '' V g ∈ 𝓝 (1 * g) := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds (hV g)
    rw [one_mul] at h1
    refine mem_of_superset h1 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨(v, 1), ⟨hv, mem_of_mem_nhds (hV g)⟩, by simp⟩
  obtain ⟨t, ht⟩ := hsupp.isCompact.elim_nhds_subcover O (fun g _ => hOn g)
  set V₀ : Set G := ⋂ g ∈ t, V g with hV₀
  have hV₀n : V₀ ∈ 𝓝 (1 : G) := (biInter_finset_mem t).2 fun g _ => hV g
  have hV₀sub : ∀ g ∈ t, V₀ ⊆ V g := fun g hg => biInter_subset_of_mem hg

  have hU : ∀ h ∈ ⋃ g ∈ t, O g, ∀ u ∈ V₀, ∀ u' ∈ V₀, f (u * h * u') = f h := by
    intro h hh u hu u' hu'
    simp only [mem_iUnion] at hh
    obtain ⟨g, hg, hhO⟩ := hh
    obtain ⟨⟨v, v'⟩, ⟨hv, hv'⟩, rfl⟩ := hhO
    have e1 := hV4 g u (hV₀sub g hg hu) v hv v' hv' u' (hV₀sub g hg hu')
    have e2 := hV4 g 1 (mem_of_mem_nhds (hV g)) v hv v' hv' 1 (mem_of_mem_nhds (hV g))
    simp only [one_mul, mul_one] at e2
    calc f (u * (v * g * v') * u') = f (u * v * g * v' * u') := by simp only [mul_assoc]
      _ = f g := e1
      _ = f (v * g * v') := e2.symm

  refine ⟨V₀ ∩ V₀⁻¹, inter_mem hV₀n (inv_mem_nhds_one G hV₀n), ?_⟩
  intro u hu u' hu' g
  by_cases h1 : g ∈ ⋃ g ∈ t, O g
  · exact hU g h1 u hu.1 u' hu'.1
  · by_cases h2 : u * g * u' ∈ ⋃ g ∈ t, O g
    · have e := hU (u * g * u') h2 u⁻¹ hu.2 u'⁻¹ hu'.2
      have : u⁻¹ * (u * g * u') * u'⁻¹ = g := by simp [mul_assoc]
      rw [this] at e
      exact e.symm
    · have hg0 : g ∉ tsupport f := fun h => h1 (ht.2 h)
      have hg1 : u * g * u' ∉ tsupport f := fun h => h2 (ht.2 h)
      rw [image_eq_zero_of_notMem_tsupport hg0, image_eq_zero_of_notMem_tsupport hg1]

omit [IsTopologicalGroup G] in

theorem gate_zero : ∃ V ∈ nhds (1 : G), ∀ u ∈ V, ∀ u' ∈ V, ∀ g : G, (0 : G → Y) (u * g * u') = (0 : G → Y) g :=
  ⟨univ, univ_mem, fun _ _ _ _ _ => rfl⟩

end UniformLocConst
end Rows
end M4aP3B

namespace IsLocallyConstant

theorem exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) :
    ∃ V ∈ nhds (1 : G), ∀ u ∈ V, ∀ u' ∈ V, ∀ g : G, f (u * g * u') = f g :=
  M4aP3B.Rows.UniformLocConst.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport_impl
    hf hsupp

end IsLocallyConstant

namespace M4aP3B
namespace Rows
namespace SliceLocConst

theorem isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport_impl
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) {S : Type*} (n : S → G) :
    IsLocallyConstant (fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) := by
  obtain ⟨V, hV1, hV⟩ := hf.exists_nhds_one_forall_apply_mul_mul_eq_of_hasCompactSupport hsupp
  refine (IsLocallyConstant.iff_eventually_eq _).2 ?_
  rintro ⟨k₀, k₀'⟩
  have c1 : Continuous (fun kk : G × G => kk.1 * k₀⁻¹) := continuous_fst.mul continuous_const
  have c2 : Continuous (fun kk : G × G => k₀'⁻¹ * kk.2) := continuous_const.mul continuous_snd
  have t1 : Tendsto (fun kk : G × G => kk.1 * k₀⁻¹) (𝓝 (k₀, k₀')) (𝓝 1) := by
    simpa using c1.tendsto (k₀, k₀')
  have t2 : Tendsto (fun kk : G × G => k₀'⁻¹ * kk.2) (𝓝 (k₀, k₀')) (𝓝 1) := by
    simpa using c2.tendsto (k₀, k₀')
  filter_upwards [t1 hV1, t2 hV1] with kk h1 h2
  funext s
  have e : kk.1 * n s * kk.2 = kk.1 * k₀⁻¹ * (k₀ * n s * k₀') * (k₀'⁻¹ * kk.2) := by
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  rw [e]
  exact hV _ h1 _ h2 _

theorem gate_discrete {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    {Y S : Type*} (f : G → Y) (n : S → G) :
    IsLocallyConstant (fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) :=
  IsLocallyConstant.of_discrete _

end SliceLocConst
end Rows
end M4aP3B

namespace M4aP3B
namespace Rows
namespace SliceLocConst

theorem finite_image_of_isCompact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) {S : Type*} (n : S → G)
    {K : Set (G × G)} (hK : IsCompact K) :
    ((fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) '' K).Finite := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have h := (isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport_impl hf hsupp n).comp_continuous
    continuous_subtype_val (X := K)
  have h__af := h.range_finite
  simp [Set.image_eq_range] at h__af ⊢
  exact h__af

end SliceLocConst
end Rows
end M4aP3B

namespace IsLocallyConstant

theorem isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) {S : Type*} (n : S → G) :
    IsLocallyConstant (fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) :=
  M4aP3B.Rows.SliceLocConst.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport_impl
    hf hsupp n

end IsLocallyConstant
