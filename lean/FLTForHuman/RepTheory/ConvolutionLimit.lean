/- 
  The double-convolution limit engine of the archimedean approximate identity.

  This is the generic movement `Q4` behind
  `AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`:
  the submodule `contSubmodule` of continuous functions, the double convolution
  `dconvWith` with its linearity and translate-substitution lemmas, the operators
  `convOpR`/`convOpL`, the type-membership lemmas `dconvWith_mem_iSup_dual` /
  `dconvWith_inv_mem_iSup`, compact support, the limit
  `tendsto_integral_mul_dconvWith`, and the parametric-integral differentiability
  (`contDiffNat_parametricIntegral_postcompCLM`, `contDiff_parametricIntegral_clm_comp`,
  `contDiff_parametricIntegral_mul`).

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:2212–2853`
  (pinned `aa2d8b3`), the `ZetaB` and `Carry4` sections. It mentions neither the adèles
  nor `GL₂`: everything is stated over the abstract compact group `Kc` and the abstract
  group `H`. The pin declares the engine `private`; here it is the shared engine and is
  public, so the statements are verbatim. The pin's `set_option maxHeartbeats 4000000 in`
  above `contDiffNat_parametricIntegral_postcompCLM` is not transcribed — the port runs at
  the low cap. The pin's `p2m_reactivate` lines are not transcribed.

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean
-/
import FLTForHuman.RepTheory.TypeReproducer
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory AutomorphicForm

namespace ArchApproxIdentity

section ZetaB

def contSubmodule (X : Type*) [TopologicalSpace X] : Submodule ℂ (X → ℂ) where
  carrier := {u | Continuous u}
  add_mem' hu hv := hu.add hv
  zero_mem' := continuous_const
  smul_mem' c _ hu := hu.const_smul c

theorem mem_contSubmodule {X : Type*} [TopologicalSpace X] {u : X → ℂ} : u ∈ contSubmodule X ↔ Continuous u :=
  Iff.rfl

variable {H Kc : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group Kc] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [SecondCountableTopology Kc]
  [MeasurableSpace Kc] [BorelSpace Kc]
variable (μ : Measure Kc) [IsFiniteMeasure μ] (a : Kc →* H)

def dconvWith (e₁ e₂ : Kc → ℂ) (ψ : H → ℂ) (y : H) : ℂ :=
  ∫ p : Kc × Kc, e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)

omit [IsTopologicalGroup Kc] [CompactSpace Kc] [SecondCountableTopology Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem continuous_dconvIntegrand {e₁ e₂ : Kc → ℂ} (he₁ : Continuous e₁) (he₂ : Continuous e₂) {ψ : H → ℂ}
    (hψ : Continuous ψ) (ha : Continuous a) (y : H) :
    Continuous fun p : Kc × Kc => e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) :=
  ((he₁.comp continuous_fst).mul (he₂.comp continuous_snd)).mul
    (hψ.comp ((((ha.comp continuous_fst).inv).mul continuous_const).mul (ha.comp continuous_snd).inv))

omit [Group Kc] [IsTopologicalGroup Kc] in
theorem integrable_of_continuous_prod {F : Kc × Kc → ℂ} (hF : Continuous F) : Integrable F (μ.prod μ) :=
  hF.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport F) (Set.subset_univ _))

section Linear

variable {μ a}
variable {e₁ e₂ u v : Kc → ℂ} {ψ : H → ℂ}

omit [IsTopologicalGroup Kc] in
theorem dconvWith_add_right (he₁ : Continuous e₁) (hu : Continuous u) (hv : Continuous v) (hψ : Continuous ψ)
    (ha : Continuous a) (y : H) :
    dconvWith μ a e₁ (u + v) ψ y = dconvWith μ a e₁ u ψ y + dconvWith μ a e₁ v ψ y := by
  unfold dconvWith
  rw [← integral_add (integrable_of_continuous_prod μ (continuous_dconvIntegrand a he₁ hu hψ ha y))
    (integrable_of_continuous_prod μ (continuous_dconvIntegrand a he₁ hv hψ ha y))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show e₁ p.1 * (u p.2 + v p.2) * _ = _
  ring

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc]
  [SecondCountableTopology Kc] [BorelSpace Kc] [IsFiniteMeasure μ] in
theorem dconvWith_smul_right (c : ℂ) (y : H) : dconvWith μ a e₁ (c • u) ψ y = c * dconvWith μ a e₁ u ψ y := by
  unfold dconvWith
  rw [show (fun p : Kc × Kc => e₁ p.1 * (c • u) p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹)) =
      fun p => c * (e₁ p.1 * u p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹)) from
    funext fun p => by simp only [Pi.smul_apply, smul_eq_mul]; ring]
  exact integral_const_mul c _

omit [IsTopologicalGroup Kc] in
theorem dconvWith_add_left (hu : Continuous u) (hv : Continuous v) (he₂ : Continuous e₂) (hψ : Continuous ψ)
    (ha : Continuous a) (y : H) :
    dconvWith μ a (u + v) e₂ ψ y = dconvWith μ a u e₂ ψ y + dconvWith μ a v e₂ ψ y := by
  unfold dconvWith
  rw [← integral_add (integrable_of_continuous_prod μ (continuous_dconvIntegrand a hu he₂ hψ ha y))
    (integrable_of_continuous_prod μ (continuous_dconvIntegrand a hv he₂ hψ ha y))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show (u p.1 + v p.1) * e₂ p.2 * _ = _
  ring

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc]
  [SecondCountableTopology Kc] [BorelSpace Kc] [IsFiniteMeasure μ] in
theorem dconvWith_smul_left (c : ℂ) (y : H) : dconvWith μ a (c • u) e₂ ψ y = c * dconvWith μ a u e₂ ψ y := by
  unfold dconvWith
  rw [show (fun p : Kc × Kc => (c • u) p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹)) =
      fun p => c * (u p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹)) from
    funext fun p => by simp only [Pi.smul_apply, smul_eq_mul]; ring]
  exact integral_const_mul c _

end Linear

section Substitution

variable {μ a}
variable [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
variable {Kw : Type*} [Group Kw] {j : Kw →* Kc} {ι' : Kw →* H} (haj : ∀ k, a (j k) = ι' k)
variable (e₁ e₂ : Kc → ℂ) (ψ : H → ℂ)

omit [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace Kc] [μ.IsMulLeftInvariant] in
include haj in
theorem dconvWith_rt_right (k : Kw) (y : H) :
    dconvWith μ a e₁ (fun κ => e₂ (κ * j k)) ψ y = dconvWith μ a e₁ e₂ ψ (y * ι' k) := by
  unfold dconvWith
  rw [← integral_mul_right_eq_self
    (fun p : Kc × Kc => e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * (y * ι' k) * (a p.2)⁻¹)) ((1 : Kc), j k)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show e₁ p.1 * e₂ (p.2 * j k) * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) =
    e₁ (p.1 * 1) * e₂ (p.2 * j k) * ψ ((a (p.1 * 1))⁻¹ * (y * ι' k) * (a (p.2 * j k))⁻¹)
  rw [mul_one, map_mul, haj, mul_inv_rev,
    show (a p.1)⁻¹ * (y * ι' k) * ((ι' k)⁻¹ * (a p.2)⁻¹) = (a p.1)⁻¹ * y * (a p.2)⁻¹ by group]

omit [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace Kc] [μ.IsMulRightInvariant] in
include haj in
theorem dconvWith_rt_left (u : Kc → ℂ) (k : Kw) (y : H) :
    dconvWith μ a (fun κ => u (κ⁻¹ * j k)) e₂ ψ y⁻¹ = dconvWith μ a (fun κ => u κ⁻¹) e₂ ψ (y * ι' k)⁻¹ := by
  unfold dconvWith
  rw [← integral_mul_left_eq_self
    (fun p : Kc × Kc => u p.1⁻¹ * e₂ p.2 * ψ ((a p.1)⁻¹ * (y * ι' k)⁻¹ * (a p.2)⁻¹)) (j k⁻¹, (1 : Kc))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show u (p.1⁻¹ * j k) * e₂ p.2 * ψ ((a p.1)⁻¹ * y⁻¹ * (a p.2)⁻¹) =
    u (j k⁻¹ * p.1)⁻¹ * e₂ (1 * p.2) * ψ ((a (j k⁻¹ * p.1))⁻¹ * (y * ι' k)⁻¹ * (a (1 * p.2))⁻¹)
  have hu : (j k⁻¹ * p.1)⁻¹ = p.1⁻¹ * j k := by
    rw [map_inv]
    group
  have harg : (a (j k⁻¹ * p.1))⁻¹ * (y * ι' k)⁻¹ * (a (1 * p.2))⁻¹ = (a p.1)⁻¹ * y⁻¹ * (a p.2)⁻¹ := by
    rw [one_mul, map_mul, map_inv, map_inv, haj]
    group
  rw [hu, harg, one_mul]

end Substitution

section Types

variable {μ a}
variable [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
variable {Kw : Type*} [Group Kw] {j : Kw →* Kc} {ι' : Kw →* H} (hι' : Function.Injective ι')
  (haj : ∀ k, a (j k) = ι' k)
variable {J : Type*} {W : J → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (ρ : ∀ i, Representation ℂ Kw (W i))
variable {e : Kc → ℂ} (he : Continuous e) {ψ : H → ℂ} (hψ : Continuous ψ) (ha : Continuous a)

variable (μ a) in
def convOpR : contSubmodule Kc →ₗ[ℂ] (H → ℂ) where
  toFun u y := dconvWith μ a e u ψ y
  map_add' u v := funext fun y => dconvWith_add_right he u.2 v.2 hψ ha y
  map_smul' c u := by
    funext y
    show dconvWith μ a e (c • (u : Kc → ℂ)) ψ y = c * dconvWith μ a e u ψ y
    exact dconvWith_smul_right c y

variable (μ a) in
def convOpL : contSubmodule Kc →ₗ[ℂ] (H → ℂ) where
  toFun u y := dconvWith μ a (fun κ => (u : Kc → ℂ) κ⁻¹) e ψ y⁻¹
  map_add' u v := funext fun y =>
    dconvWith_add_left (u.2.comp continuous_inv) (v.2.comp continuous_inv) he hψ ha y⁻¹
  map_smul' c u := by
    funext y
    show dconvWith μ a (c • fun κ => (u : Kc → ℂ) κ⁻¹) e ψ y⁻¹ =
      c * dconvWith μ a (fun κ => (u : Kc → ℂ) κ⁻¹) e ψ y⁻¹
    exact dconvWith_smul_left c y⁻¹

omit [μ.IsMulLeftInvariant] in
include hι' haj he hψ ha in
theorem dconvWith_mem_iSup_dual (hed : e ∈ ⨆ i, typeSubmodule j (ρ i).dual) :
    dconvWith μ a e e ψ ∈ ⨆ i, typeSubmodule ι' (ρ i).dual := by
  have hP₀ : ∀ (k : Kw), ∀ θ ∈ contSubmodule Kc, (fun x => θ (x * j k)) ∈ contSubmodule Kc :=
    fun k θ hθ => hθ.comp (continuous_id.mul continuous_const)
  have hA : ∀ (k : Kw) (θ : contSubmodule Kc) (y : H),
      convOpR μ a he hψ ha ⟨fun x => (θ : Kc → ℂ) (x * j k), hP₀ k θ θ.2⟩ y =
        convOpR μ a he hψ ha θ (y * ι' k) :=
    fun k θ y => dconvWith_rt_right haj e θ ψ k y
  exact mem_iSup_typeSubmodule_of_intertwines j hι' (fun i => (ρ i).dual) (contSubmodule Kc) hP₀
    (convOpR μ a he hψ ha) hA ⟨e, he⟩ hed

omit [μ.IsMulRightInvariant] in
include hι' haj he hψ ha in
theorem dconvWith_inv_mem_iSup (hel : (fun κ => e κ⁻¹) ∈ ⨆ i, typeSubmodule j (ρ i)) :
    (fun y => dconvWith μ a e e ψ y⁻¹) ∈ ⨆ i, typeSubmodule ι' (ρ i) := by
  have hP₀ : ∀ (k : Kw), ∀ θ ∈ contSubmodule Kc, (fun x => θ (x * j k)) ∈ contSubmodule Kc :=
    fun k θ hθ => hθ.comp (continuous_id.mul continuous_const)
  have hA : ∀ (k : Kw) (θ : contSubmodule Kc) (y : H),
      convOpL μ a he hψ ha ⟨fun x => (θ : Kc → ℂ) (x * j k), hP₀ k θ θ.2⟩ y =
        convOpL μ a he hψ ha θ (y * ι' k) :=
    fun k θ y => dconvWith_rt_left haj e ψ θ k y
  have hmem := mem_iSup_typeSubmodule_of_intertwines j hι' ρ (contSubmodule Kc) hP₀ (convOpL μ a he hψ ha) hA
    ⟨fun κ => e κ⁻¹, he.comp continuous_inv⟩ hel
  have heq : convOpL μ a he hψ ha ⟨fun κ => e κ⁻¹, he.comp continuous_inv⟩ =
      fun y => dconvWith μ a e e ψ y⁻¹ := by
    funext y
    show dconvWith μ a (fun κ => e κ⁻¹⁻¹) e ψ y⁻¹ = _
    simp only [inv_inv]
  rw [heq] at hmem
  exact hmem

end Types

section Support

variable {μ a}
variable {e : Kc → ℂ} {ψ : H → ℂ}

omit [IsTopologicalGroup Kc] [SecondCountableTopology Kc] [BorelSpace Kc] [IsFiniteMeasure μ] in
theorem hasCompactSupport_dconvWith (ha : Continuous a) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (dconvWith μ a e e ψ) := by

  let S : Set H := (fun q : (Kc × H) × Kc => a q.1.1 * q.1.2 * a q.2) '' ((Set.univ ×ˢ tsupport ψ) ×ˢ Set.univ)
  have hS : IsCompact S :=
    ((isCompact_univ.prod hψ).prod isCompact_univ).image
      (((ha.comp (continuous_fst.comp continuous_fst)).mul (continuous_snd.comp continuous_fst)).mul
        (ha.comp continuous_snd))
  refine HasCompactSupport.intro hS fun y hy => ?_

  have hzero : ∀ p : Kc × Kc, e p.1 * e p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) = 0 := by
    intro p
    have hnot : (a p.1)⁻¹ * y * (a p.2)⁻¹ ∉ tsupport ψ := by
      intro hmem
      refine hy ⟨((p.1, (a p.1)⁻¹ * y * (a p.2)⁻¹), p.2), ⟨⟨Set.mem_univ _, hmem⟩, Set.mem_univ _⟩, ?_⟩
      show a p.1 * ((a p.1)⁻¹ * y * (a p.2)⁻¹) * a p.2 = y
      group
    rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  show (∫ p : Kc × Kc, e p.1 * e p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) = 0
  simp_rw [hzero]
  exact integral_zero _ _

end Support

section Limit

variable {μ a}
variable {G : Type*} [Group G] (ιA : H →* G)
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H]
variable (ν : Measure H) [SFinite ν] [IsFiniteMeasureOnCompacts ν] [ν.IsMulLeftInvariant]

omit [IsTopologicalGroup Kc] [SecondCountableTopology Kc] [MeasurableSpace Kc] [BorelSpace Kc] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H] [LocallyCompactSpace H] in
theorem isCompact_image_mul_mul (ha : Continuous a) {T : Set H} (hT : IsCompact T) :
    IsCompact ((fun q : (Kc × H) × Kc => a q.1.1 * q.1.2 * a q.2) '' ((Set.univ ×ˢ T) ×ˢ Set.univ)) :=
  ((isCompact_univ.prod hT).prod isCompact_univ).image
    (((ha.comp (continuous_fst.comp continuous_fst)).mul (continuous_snd.comp continuous_fst)).mul
      (ha.comp continuous_snd))

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc]
  [SecondCountableTopology Kc] [MeasurableSpace Kc] [BorelSpace Kc] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] [LocallyCompactSpace H] in
theorem mem_image_mul_mul_of_ne {T : Set H} {ψ : H → ℂ} (hψT : ∀ z, ψ z ≠ 0 → z ∈ T) {y : H} {p : Kc × Kc}
    (h : ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) ≠ 0) :
    y ∈ (fun q : (Kc × H) × Kc => a q.1.1 * q.1.2 * a q.2) '' ((Set.univ ×ˢ T) ×ˢ Set.univ) :=
  ⟨((p.1, (a p.1)⁻¹ * y * (a p.2)⁻¹), p.2), ⟨⟨Set.mem_univ _, hψT _ h⟩, Set.mem_univ _⟩, by
    show a p.1 * ((a p.1)⁻¹ * y * (a p.2)⁻¹) * a p.2 = y
    group⟩

variable {ιA ν}

omit [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [SecondCountableTopology Kc] [MeasurableSpace Kc]
  [BorelSpace Kc] [SecondCountableTopology H] [LocallyCompactSpace H] [SFinite ν] [IsFiniteMeasureOnCompacts ν] in
theorem integral_mul_shift (hνR : ∀ (κ : Kc) (h : H → ℂ), Continuous h → HasCompactSupport h →
      ∫ y, h (y * a κ) ∂ν = ∫ y, h y ∂ν)
    {φ : H → ℂ} (hφ : Continuous φ) {ψ : H → ℂ} (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) (κ₁ κ₂ : Kc) :
    ∫ y, φ y * ψ ((a κ₁)⁻¹ * y * (a κ₂)⁻¹) ∂ν = ∫ y, φ (a κ₁ * y * a κ₂) * ψ y ∂ν := by
  have h1 : ∫ y, φ y * ψ ((a κ₁)⁻¹ * y * (a κ₂)⁻¹) ∂ν = ∫ y, φ (a κ₁ * y) * ψ (y * (a κ₂)⁻¹) ∂ν := by
    rw [← integral_mul_left_eq_self (fun y => φ y * ψ ((a κ₁)⁻¹ * y * (a κ₂)⁻¹)) (a κ₁)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show φ (a κ₁ * y) * ψ ((a κ₁)⁻¹ * (a κ₁ * y) * (a κ₂)⁻¹) = φ (a κ₁ * y) * ψ (y * (a κ₂)⁻¹)
    rw [inv_mul_cancel_left]
  have hM : Continuous fun y => φ (a κ₁ * y) * ψ (y * (a κ₂)⁻¹) :=
    (hφ.comp (continuous_const.mul continuous_id)).mul (hψ.comp (continuous_id.mul continuous_const))
  have hMs : HasCompactSupport fun y => φ (a κ₁ * y) * ψ (y * (a κ₂)⁻¹) :=
    (show HasCompactSupport fun y => ψ (y * (a κ₂)⁻¹) from
      hψs.comp_homeomorph (Homeomorph.mulRight (a κ₂)⁻¹)).mul_left
  have h2 := hνR κ₂ _ hM hMs
  rw [h1, ← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show φ (a κ₁ * (y * a κ₂)) * ψ (y * a κ₂ * (a κ₂)⁻¹) = φ (a κ₁ * y * a κ₂) * ψ y
  rw [mul_inv_cancel_right, mul_assoc]

theorem tendsto_integral_mul_dconvWith (ha : Continuous a) {e : Kc → ℂ} (he : Continuous e) (f : G → ℂ)
    (hfc : ∀ x : G, Continuous fun y : H => f (x * ιA y))
    (hrep : ∀ x : G, ∫ κ, e κ * f (x * ιA (a κ)) ∂μ = f x)
    (hνR : ∀ (κ : Kc) (h : H → ℂ), Continuous h → HasCompactSupport h → ∫ y, h (y * a κ) ∂ν = ∫ y, h y ∂ν)
    (ψ : ℕ → H → ℝ) (hψc : ∀ n, Continuous (ψ n)) (hψs : ∀ n, HasCompactSupport (ψ n))
    (hγ2 : ∀ φ : H → ℂ, Continuous φ →
      Filter.Tendsto (fun n => ∫ y, φ y * (ψ n y : ℂ) ∂ν) Filter.atTop (nhds (φ 1)))
    (g : G) :
    Filter.Tendsto (fun n => ∫ y, f (g * ιA y) * dconvWith μ a e e (fun z => (ψ n z : ℂ)) y ∂ν) Filter.atTop
      (nhds (f g)) := by

  let Φ : H → ℂ := fun y => ∫ κ, e κ * f (g * ιA (a κ * y)) ∂μ
  have hFc : Continuous (Function.uncurry fun (y : H) (κ : Kc) => e κ * f (g * ιA (a κ * y))) :=
    (he.comp continuous_snd).mul ((hfc g).comp ((ha.comp continuous_snd).mul continuous_fst))
  have hΦc : Continuous Φ := by
    have h := continuous_parametric_integral_of_continuous (μ := μ) hFc isCompact_univ
    simp only [Measure.restrict_univ] at h
    exact h
  have hΦ1 : Φ 1 = f g := by
    show (∫ κ, e κ * f (g * ιA (a κ * 1)) ∂μ) = f g
    simp only [mul_one]
    exact hrep g
  have key : ∀ n, (∫ y, f (g * ιA y) * dconvWith μ a e e (fun z => (ψ n z : ℂ)) y ∂ν) =
      ∫ y, Φ y * (ψ n y : ℂ) ∂ν := by
    intro n

    have hψC : Continuous fun z => (ψ n z : ℂ) := Complex.continuous_ofReal.comp (hψc n)
    have hψCs : HasCompactSupport fun z => (ψ n z : ℂ) :=
      (hψs n).comp_left (g := Complex.ofReal) Complex.ofReal_zero
    have hψT : ∀ z, (ψ n z : ℂ) ≠ 0 → z ∈ tsupport (ψ n) := fun z hz =>
      subset_tsupport _ (Function.mem_support.mpr fun h0 => hz (by rw [h0, Complex.ofReal_zero]))
    let S : Set H := (fun q : (Kc × H) × Kc => a q.1.1 * q.1.2 * a q.2) '' ((Set.univ ×ˢ tsupport (ψ n)) ×ˢ Set.univ)
    have hS : IsCompact S := isCompact_image_mul_mul ha (hψs n)

    let F : H → Kc × Kc → ℂ := fun y p => f (g * ιA y) * (e p.1 * e p.2 * (ψ n ((a p.1)⁻¹ * y * (a p.2)⁻¹) : ℂ))
    have hFcont : Continuous (Function.uncurry F) :=
      ((hfc g).comp continuous_fst).mul
        ((((he.comp (continuous_fst.comp continuous_snd)).mul (he.comp (continuous_snd.comp continuous_snd))).mul
          (hψC.comp ((((ha.comp (continuous_fst.comp continuous_snd)).inv).mul continuous_fst).mul
            (ha.comp (continuous_snd.comp continuous_snd)).inv))))
    have hFsupp : HasCompactSupport (Function.uncurry F) := by
      refine HasCompactSupport.intro (hS.prod isCompact_univ) fun q hq => ?_
      have hy : q.1 ∉ S := fun h => hq ⟨h, Set.mem_univ _⟩
      have h0 : (ψ n ((a q.2.1)⁻¹ * q.1 * (a q.2.2)⁻¹) : ℂ) = 0 := by
        by_contra h
        exact hy (mem_image_mul_mul_of_ne hψT h)
      show f (g * ιA q.1) * (e q.2.1 * e q.2.2 * (ψ n ((a q.2.1)⁻¹ * q.1 * (a q.2.2)⁻¹) : ℂ)) = 0
      rw [h0, mul_zero, mul_zero]
    have hFint : Integrable (Function.uncurry F) (ν.prod (μ.prod μ)) := hFcont.integrable_of_hasCompactSupport hFsupp
    have step1 : (∫ y, f (g * ιA y) * dconvWith μ a e e (fun z => (ψ n z : ℂ)) y ∂ν) =
        ∫ p, ∫ y, F y p ∂ν ∂(μ.prod μ) := by
      rw [← integral_integral_swap hFint]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      exact (integral_const_mul _ _).symm

    let F' : Kc × Kc → H → ℂ := fun p y => e p.1 * e p.2 * f (g * ιA (a p.1 * y * a p.2)) * (ψ n y : ℂ)
    have step2 : ∀ p : Kc × Kc, (∫ y, F y p ∂ν) = ∫ y, F' p y ∂ν := by
      intro p
      have hsub := integral_mul_shift (a := a) hνR (hfc g) hψC hψCs p.1 p.2
      calc (∫ y, F y p ∂ν)
          = ∫ y, (e p.1 * e p.2) * (f (g * ιA y) * (ψ n ((a p.1)⁻¹ * y * (a p.2)⁻¹) : ℂ)) ∂ν := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            show f (g * ιA y) * (e p.1 * e p.2 * (ψ n ((a p.1)⁻¹ * y * (a p.2)⁻¹) : ℂ)) = _
            ring
        _ = e p.1 * e p.2 * ∫ y, f (g * ιA y) * (ψ n ((a p.1)⁻¹ * y * (a p.2)⁻¹) : ℂ) ∂ν :=
            integral_const_mul _ _
        _ = e p.1 * e p.2 * ∫ y, f (g * ιA (a p.1 * y * a p.2)) * (ψ n y : ℂ) ∂ν := by rw [hsub]
        _ = ∫ y, (e p.1 * e p.2) * (f (g * ιA (a p.1 * y * a p.2)) * (ψ n y : ℂ)) ∂ν :=
            (integral_const_mul _ _).symm
        _ = ∫ y, F' p y ∂ν := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            show _ = e p.1 * e p.2 * f (g * ιA (a p.1 * y * a p.2)) * (ψ n y : ℂ)
            ring

    have hF'cont : Continuous (Function.uncurry F') :=
      ((((he.comp (continuous_fst.comp continuous_fst)).mul (he.comp (continuous_snd.comp continuous_fst))).mul
        ((hfc g).comp ((((ha.comp (continuous_fst.comp continuous_fst))).mul continuous_snd).mul
          (ha.comp (continuous_snd.comp continuous_fst))))).mul (hψC.comp continuous_snd))
    have hF'supp : HasCompactSupport (Function.uncurry F') := by
      refine HasCompactSupport.intro (isCompact_univ.prod (hψs n)) fun q hq => ?_
      have hy : q.2 ∉ tsupport (ψ n) := fun h => hq ⟨Set.mem_univ _, h⟩
      show e q.1.1 * e q.1.2 * f (g * ιA (a q.1.1 * q.2 * a q.1.2)) * (ψ n q.2 : ℂ) = 0
      rw [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, mul_zero]
    have hF'int : Integrable (Function.uncurry F') ((μ.prod μ).prod ν) :=
      hF'cont.integrable_of_hasCompactSupport hF'supp
    have step3 : (∫ p, ∫ y, F' p y ∂ν ∂(μ.prod μ)) = ∫ y, ∫ p, F' p y ∂(μ.prod μ) ∂ν := integral_integral_swap hF'int

    have step4 : ∀ y : H, (∫ p, F' p y ∂(μ.prod μ)) = Φ y * (ψ n y : ℂ) := by
      intro y
      have hGc : Continuous fun p : Kc × Kc => e p.1 * (e p.2 * f (g * ιA (a p.1 * y * a p.2))) :=
        (he.comp continuous_fst).mul ((he.comp continuous_snd).mul
          ((hfc g).comp (((ha.comp continuous_fst).mul continuous_const).mul (ha.comp continuous_snd))))
      have hint : Integrable (fun p : Kc × Kc => e p.1 * (e p.2 * f (g * ιA (a p.1 * y * a p.2)))) (μ.prod μ) :=
        integrable_of_continuous_prod μ hGc
      calc (∫ p, F' p y ∂(μ.prod μ))
          = ∫ p, e p.1 * (e p.2 * f (g * ιA (a p.1 * y * a p.2))) * (ψ n y : ℂ) ∂(μ.prod μ) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
            show e p.1 * e p.2 * f (g * ιA (a p.1 * y * a p.2)) * (ψ n y : ℂ) = _
            ring
        _ = (∫ p, e p.1 * (e p.2 * f (g * ιA (a p.1 * y * a p.2))) ∂(μ.prod μ)) * (ψ n y : ℂ) :=
            integral_mul_const _ _
        _ = (∫ κ₁, ∫ κ₂, e κ₁ * (e κ₂ * f (g * ιA (a κ₁ * y * a κ₂))) ∂μ ∂μ) * (ψ n y : ℂ) := by
            rw [integral_prod _ hint]
        _ = (∫ κ₁, e κ₁ * f (g * ιA (a κ₁ * y)) ∂μ) * (ψ n y : ℂ) := by
            congr 1
            refine integral_congr_ae (Filter.Eventually.of_forall fun κ₁ => ?_)
            show (∫ κ₂, e κ₁ * (e κ₂ * f (g * ιA (a κ₁ * y * a κ₂))) ∂μ) = e κ₁ * f (g * ιA (a κ₁ * y))
            calc (∫ κ₂, e κ₁ * (e κ₂ * f (g * ιA (a κ₁ * y * a κ₂))) ∂μ)
                = e κ₁ * ∫ κ₂, e κ₂ * f (g * ιA (a κ₁ * y * a κ₂)) ∂μ := integral_const_mul _ _
              _ = e κ₁ * ∫ κ₂, e κ₂ * f (g * ιA (a κ₁ * y) * ιA (a κ₂)) ∂μ := by
                  congr 1
                  refine integral_congr_ae (Filter.Eventually.of_forall fun κ₂ => ?_)
                  show e κ₂ * f (g * ιA (a κ₁ * y * a κ₂)) = e κ₂ * f (g * ιA (a κ₁ * y) * ιA (a κ₂))
                  rw [map_mul, ← mul_assoc]
              _ = e κ₁ * f (g * ιA (a κ₁ * y)) := by rw [hrep (g * ιA (a κ₁ * y))]
        _ = Φ y * (ψ n y : ℂ) := rfl

    calc (∫ y, f (g * ιA y) * dconvWith μ a e e (fun z => (ψ n z : ℂ)) y ∂ν)
        = ∫ p, ∫ y, F y p ∂ν ∂(μ.prod μ) := step1
      _ = ∫ p, ∫ y, F' p y ∂ν ∂(μ.prod μ) := integral_congr_ae (Filter.Eventually.of_forall step2)
      _ = ∫ y, ∫ p, F' p y ∂(μ.prod μ) ∂ν := step3
      _ = ∫ y, Φ y * (ψ n y : ℂ) ∂ν := integral_congr_ae (Filter.Eventually.of_forall step4)
  have hfun : (fun n => ∫ y, f (g * ιA y) * dconvWith μ a e e (fun z => (ψ n z : ℂ)) y ∂ν) =
      fun n => ∫ y, Φ y * (ψ n y : ℂ) ∂ν := funext key
  rw [hfun, ← hΦ1]
  exact hγ2 Φ hΦc

end Limit

end ZetaB

end ArchApproxIdentity

end



noncomputable section

open Set Filter Function MeasureTheory Matrix
open scoped ENNReal NNReal BigOperators Classical ContDiff

namespace ArchApproxIdentity

section DominatedDUIEngine

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
theorem archDUI_apply_mem_closedBall {Φw : P →L[ℝ] E} {C : ℝ} (hΦ : ‖Φw‖ ≤ C)
    {x₀ x : P} (hx : x ∈ Metric.ball x₀ 1) :
    Φw x ∈ Metric.closedBall (0 : E) (C * (‖x₀‖ + 1)) := by
  have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have h1 : ‖x‖ - ‖x₀‖ ≤ ‖x - x₀‖ := norm_sub_norm_le x x₀
    have h2 : ‖x - x₀‖ < 1 := mem_ball_iff_norm.mp hx
    linarith
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) hΦ
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖Φw x‖ ≤ ‖Φw‖ * ‖x‖ := Φw.le_opNorm x
    _ ≤ C * (‖x₀‖ + 1) := mul_le_mul hΦ hxn (norm_nonneg _) hC0

theorem contDiffNat_parametricIntegral_postcompCLM [IsFiniteMeasure μ]
    (Φ : α → P →L[ℝ] E) (hΦm : AEStronglyMeasurable Φ μ)
    {C : ℝ} (hC : 0 ≤ C) (hΦb : ∀ᵐ w ∂μ, ‖Φ w‖ ≤ C) (n : ℕ) :
    ∀ (E₁ E₂ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
      [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
      (G : E → E₁), ContDiff ℝ n G →
      ∀ T : α → E₁ →L[ℝ] E₂, AEStronglyMeasurable T μ →
      ∀ D : ℝ, 0 ≤ D → (∀ᵐ w ∂μ, ‖T w‖ ≤ D) →
      ContDiff ℝ n (fun x : P => ∫ w, T w (G (Φ w x)) ∂μ) := by
  induction n with
  | zero =>
    intro E₁ E₂ _ _ _ _ _ G hG T hT D hD hTD
    have h0 : ((0 : ℕ) : WithTop ℕ∞) = 0 := by norm_cast
    rw [h0, contDiff_zero, continuous_iff_continuousAt]
    intro x₀
    obtain ⟨M₀, hM₀⟩ :=
      (isCompact_closedBall (0 : E) (C * (‖x₀‖ + 1))).exists_bound_of_continuousOn
        (hG.continuous.continuousOn (s := Metric.closedBall (0 : E) (C * (‖x₀‖ + 1))))
    refine continuousAt_of_dominated (F := fun x w => T w (G (Φ w x)))
      (bound := fun _ => D * M₀) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x =>
        (ContinuousLinearMap.id ℝ (E₁ →L[ℝ] E₂)).aestronglyMeasurable_comp₂ hT
          (hG.continuous.comp_aestronglyMeasurable (hΦm.apply_continuousLinearMap x))
    · refine Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ one_pos) fun x hx => ?_
      filter_upwards [hTD, hΦb] with w hTw hΦw
      have hmem := archDUI_apply_mem_closedBall hΦw hx
      calc ‖T w (G (Φ w x))‖ ≤ ‖T w‖ * ‖G (Φ w x)‖ := (T w).le_opNorm _
        _ ≤ D * M₀ := mul_le_mul hTw (hM₀ _ hmem) (norm_nonneg _) hD
    · exact integrable_const _
    · exact Filter.Eventually.of_forall fun w =>
        ((T w).continuous.comp (hG.continuous.comp (Φ w).continuous)).continuousAt
  | succ n IH =>
    intro E₁ E₂ _ _ _ _ _ G hG T hT D hD hTD
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
      exact_mod_cast rfl
    rw [hcast] at hG ⊢
    have hGdiff : Differentiable ℝ G :=
      hG.differentiable (by exact_mod_cast Nat.succ_ne_zero n)
    have hG' : ContDiff ℝ n (fderiv ℝ G) := hG.fderiv_right le_rfl

    set T' : α → (E →L[ℝ] E₁) →L[ℝ] (P →L[ℝ] E₂) := fun w =>
      ((ContinuousLinearMap.compL ℝ P E₁ E₂) (T w)).comp
        ((ContinuousLinearMap.compL ℝ P E E₁).flip (Φ w)) with hT'def
    have hT'apply : ∀ (w : α) (Ψ : E →L[ℝ] E₁),
        T' w Ψ = (T w).comp (Ψ.comp (Φ w)) := by
      intro w Ψ
      simp only [hT'def, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
    have hAmeas : AEStronglyMeasurable
        (fun w => (ContinuousLinearMap.compL ℝ P E₁ E₂) (T w)) μ :=
      (ContinuousLinearMap.compL ℝ P E₁ E₂).continuous.comp_aestronglyMeasurable hT
    have hBmeas : AEStronglyMeasurable
        (fun w => (ContinuousLinearMap.compL ℝ P E E₁).flip (Φ w)) μ :=
      ((ContinuousLinearMap.compL ℝ P E E₁).flip).continuous.comp_aestronglyMeasurable hΦm
    have hT'meas : AEStronglyMeasurable T' μ := by
      have hcomp : Continuous fun q : ((P →L[ℝ] E₁) →L[ℝ] (P →L[ℝ] E₂)) ×
          ((E →L[ℝ] E₁) →L[ℝ] (P →L[ℝ] E₁)) => q.1.comp q.2 :=
        isBoundedBilinearMap_comp.continuous
      exact (hcomp.comp_aestronglyMeasurable (hAmeas.prodMk hBmeas) :)
    have hT'bd : ∀ᵐ w ∂μ, ‖T' w‖ ≤ D * C := by
      filter_upwards [hTD, hΦb] with w hTw hΦw
      refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hD hC) fun Ψ => ?_
      rw [hT'apply]
      calc ‖(T w).comp (Ψ.comp (Φ w))‖
          ≤ ‖T w‖ * ‖Ψ.comp (Φ w)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖T w‖ * (‖Ψ‖ * ‖Φ w‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
        _ ≤ D * (‖Ψ‖ * C) :=
            mul_le_mul hTw (mul_le_mul_of_nonneg_left hΦw (norm_nonneg _)) (by positivity) hD
        _ = D * C * ‖Ψ‖ := by ring

    have key : ∀ x₀ : P, HasFDerivAt (fun x : P => ∫ w, T w (G (Φ w x)) ∂μ)
        (∫ w, T' w (fderiv ℝ G (Φ w x₀)) ∂μ) x₀ := by
      intro x₀
      obtain ⟨M₀, hM₀⟩ :=
        (isCompact_closedBall (0 : E) (C * (‖x₀‖ + 1))).exists_bound_of_continuousOn
          (hG.continuous.continuousOn (s := Metric.closedBall (0 : E) (C * (‖x₀‖ + 1))))
      obtain ⟨M₁, hM₁⟩ :=
        (isCompact_closedBall (0 : E) (C * (‖x₀‖ + 1))).exists_bound_of_continuousOn
          (hG'.continuous.continuousOn (s := Metric.closedBall (0 : E) (C * (‖x₀‖ + 1))))
      have hM₁0 : 0 ≤ M₁ := by
        refine le_trans (norm_nonneg (fderiv ℝ G 0)) (hM₁ 0 ?_)
        rw [Metric.mem_closedBall, dist_self]
        positivity
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := fun x w => T w (G (Φ w x)))
        (F' := fun x w => T' w (fderiv ℝ G (Φ w x)))
        (bound := fun _ => D * (M₁ * C)) (s := Metric.ball x₀ 1)
        (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
      · exact Filter.Eventually.of_forall fun x =>
          (ContinuousLinearMap.id ℝ (E₁ →L[ℝ] E₂)).aestronglyMeasurable_comp₂ hT
            (hG.continuous.comp_aestronglyMeasurable (hΦm.apply_continuousLinearMap x))
      · refine (integrable_const (D * M₀)).mono'
          ((ContinuousLinearMap.id ℝ (E₁ →L[ℝ] E₂)).aestronglyMeasurable_comp₂ hT
            (hG.continuous.comp_aestronglyMeasurable (hΦm.apply_continuousLinearMap x₀))) ?_
        filter_upwards [hTD, hΦb] with w hTw hΦw
        have hmem : Φ w x₀ ∈ Metric.closedBall (0 : E) (C * (‖x₀‖ + 1)) :=
          archDUI_apply_mem_closedBall hΦw (Metric.mem_ball_self one_pos)
        calc ‖T w (G (Φ w x₀))‖ ≤ ‖T w‖ * ‖G (Φ w x₀)‖ := (T w).le_opNorm _
          _ ≤ D * M₀ := mul_le_mul hTw (hM₀ _ hmem) (norm_nonneg _) hD
      · have happly : Continuous fun q : ((E →L[ℝ] E₁) →L[ℝ] (P →L[ℝ] E₂)) × (E →L[ℝ] E₁) =>
            q.1 q.2 := isBoundedBilinearMap_apply.continuous
        exact (happly.comp_aestronglyMeasurable (hT'meas.prodMk
          (hG'.continuous.comp_aestronglyMeasurable (hΦm.apply_continuousLinearMap x₀))) :)
      · filter_upwards [hTD, hΦb] with w hTw hΦw
        intro x hx
        have hmem := archDUI_apply_mem_closedBall hΦw hx
        rw [hT'apply]
        calc ‖(T w).comp ((fderiv ℝ G (Φ w x)).comp (Φ w))‖
            ≤ ‖T w‖ * ‖(fderiv ℝ G (Φ w x)).comp (Φ w)‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖T w‖ * (‖fderiv ℝ G (Φ w x)‖ * ‖Φ w‖) :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
                (norm_nonneg _)
          _ ≤ D * (M₁ * C) :=
              mul_le_mul hTw (mul_le_mul (hM₁ _ hmem) hΦw (norm_nonneg _) hM₁0)
                (by positivity) hD
      · exact integrable_const (D * (M₁ * C))
      · refine Filter.Eventually.of_forall fun w => ?_
        intro x _hx
        show HasFDerivAt (fun y : P => T w (G (Φ w y))) (T' w (fderiv ℝ G (Φ w x))) x
        have h1 : HasFDerivAt G (fderiv ℝ G (Φ w x)) (Φ w x) :=
          (hGdiff (Φ w x)).hasFDerivAt
        have h2 : HasFDerivAt (fun y : P => G (Φ w y))
            ((fderiv ℝ G (Φ w x)).comp (Φ w)) x := h1.comp x (Φ w).hasFDerivAt
        have h3 : HasFDerivAt (fun y : P => T w (G (Φ w y)))
            ((T w).comp ((fderiv ℝ G (Φ w x)).comp (Φ w))) x :=
          (T w).hasFDerivAt.comp x h2
        rw [hT'apply]
        exact h3
    have hdiff : Differentiable ℝ (fun x : P => ∫ w, T w (G (Φ w x)) ∂μ) :=
      fun x => (key x).differentiableAt
    have hfd : (fderiv ℝ (fun x : P => ∫ w, T w (G (Φ w x)) ∂μ))
        = fun x => ∫ w, T' w (fderiv ℝ G (Φ w x)) ∂μ := by
      funext x
      exact (key x).fderiv
    rw [contDiff_succ_iff_fderiv]
    refine ⟨hdiff, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · rw [hfd]
      exact IH (E →L[ℝ] E₁) (P →L[ℝ] E₂) (fderiv ℝ G) hG' T' hT'meas (D * C)
        (mul_nonneg hD hC) hT'bd

theorem contDiff_parametricIntegral_clm_comp [IsFiniteMeasure μ]
    (Φ : α → P →L[ℝ] E) (hΦm : AEStronglyMeasurable Φ μ)
    {C : ℝ} (hΦb : ∀ᵐ w ∂μ, ‖Φ w‖ ≤ C)
    {F : E → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x : P => ∫ w, F (Φ w x) ∂μ) := by
  rw [contDiff_infty]
  intro n
  have hΦb' : ∀ᵐ w ∂μ, ‖Φ w‖ ≤ max C 0 :=
    hΦb.mono fun w h => le_trans h (le_max_left _ _)
  have h := contDiffNat_parametricIntegral_postcompCLM Φ hΦm (le_max_right C 0) hΦb' n
    ℝ ℝ F (hF.of_le (by exact_mod_cast le_top))
    (fun _ => ContinuousLinearMap.id ℝ ℝ) aestronglyMeasurable_const
    1 zero_le_one (Filter.Eventually.of_forall fun _ => ContinuousLinearMap.norm_id_le)
  simpa only [ContinuousLinearMap.id_apply] using h

end DominatedDUIEngine

section ScalarWeighted

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem contDiff_parametricIntegral_mul [IsFiniteMeasure μ]
    (Φ : α → P →L[ℝ] E) (hΦm : AEStronglyMeasurable Φ μ)
    {C : ℝ} (hΦb : ∀ᵐ w ∂μ, ‖Φ w‖ ≤ C)
    {G : E → ℂ} (hG : ContDiff ℝ ∞ G) {t : α → ℂ} (ht : AEStronglyMeasurable t μ)
    {D : ℝ} (hD : 0 ≤ D) (htD : ∀ᵐ w ∂μ, ‖t w‖ ≤ D) :
    ContDiff ℝ ∞ (fun x : P => ∫ w, t w * G (Φ w x) ∂μ) := by
  rw [contDiff_infty]
  intro n
  have hΦb' : ∀ᵐ w ∂μ, ‖Φ w‖ ≤ max C 0 :=
    hΦb.mono fun w h => le_trans h (le_max_left _ _)
  let T : α → ℂ →L[ℝ] ℂ := fun w => t w • ContinuousLinearMap.id ℝ ℂ
  have hTm : AEStronglyMeasurable T μ := ht.fun_smul aestronglyMeasurable_const
  have hTD : ∀ᵐ w ∂μ, ‖T w‖ ≤ D := htD.mono fun w hw =>
    (norm_smul_le (t w) (ContinuousLinearMap.id ℝ ℂ)).trans (by
      calc ‖t w‖ * ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ ‖t w‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ ≤ D := by rw [mul_one]; exact hw)
  have h := contDiffNat_parametricIntegral_postcompCLM Φ hΦm (le_max_right C 0) hΦb' n
    ℂ ℂ G (hG.of_le (by exact_mod_cast le_top)) T hTm D hD hTD
  have hT : ∀ w x, T w (G (Φ w x)) = t w * G (Φ w x) := fun w x => by
    simp only [T, _root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  simp_rw [hT] at h
  exact h

end ScalarWeighted

end ArchApproxIdentity

end
