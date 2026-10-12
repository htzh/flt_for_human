/-
  The type-transfer engine of the right-convolution commutation proof.

  Pullback of a function along a group homomorphism `Ξ : G' → G` intertwining a
  subgroup `H ≤ G` with `H ≤ G'`: `TypeTransfer.pullback` and its equivariance
  lemmas transport the type submodule `AutomorphicForm.typeSubmodule ι ρ` of a
  representation `ρ` along `Ξ`. The `Slices` section instantiates the engine on the
  adèlic group, where the two-sided translates of an archimedean-bi-finite test
  function land in the archimedean factor type submodules
  `archFactorTypeSubmoduleAt` / `archFactorDualTypeSubmoduleAt` — the input
  `SliceCentrality.convKer_comm_of_types` consumes.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean:2067–2205`
  (the `TypeTransfer` namespace, pinned `aa2d8b3`). The pin declares the whole
  namespace `private`; here it is the shared engine and is public, so the
  statements are verbatim and every declaration lands as a promotion.
-/
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel
open AutomorphicForm

noncomputable section

namespace TypeTransfer

section Generic

variable {H G G' : Type*} [Group H] [Group G] [Group G']
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def pullback (Ξ : G' → G) : (G → ℂ) →ₗ[ℂ] (G' → ℂ) where
  toFun u := fun a => u (Ξ a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Group G] [Group G'] in
theorem pullback_apply (Ξ : G' → G) (u : G → ℂ) (a : G') : pullback Ξ u a = u (Ξ a) :=
  rfl

theorem isRightEquivariant_pullback_comp {ι : H →* G} {ι' : H →* G'} {Ξ : G' → G}
    (hΞ : ∀ (a : G') (k : H), Ξ (a * ι' k) = Ξ a * ι k) {ρ : Representation ℂ H W}
    {T : W →ₗ[ℂ] (G → ℂ)} (hT : IsRightEquivariant ι ρ T) :
    IsRightEquivariant ι' ρ (pullback Ξ ∘ₗ T) := by
  intro k v a
  show T (ρ k v) (Ξ a) = T v (Ξ (a * ι' k))
  rw [hT k v (Ξ a), hΞ a k]

theorem map_typeSubmodule_le {ι : H →* G} {ι' : H →* G'} {Ξ : G' → G}
    (hΞ : ∀ (a : G') (k : H), Ξ (a * ι' k) = Ξ a * ι k) (ρ : Representation ℂ H W) :
    (typeSubmodule ι ρ).map (pullback Ξ) ≤ typeSubmodule ι' ρ := by
  refine (Submodule.map_span_le _ _ _).mpr ?_
  rintro _ ⟨T, hT, v, rfl⟩
  exact mem_typeSubmodule_of_isRightEquivariant (isRightEquivariant_pullback_comp hΞ hT) v

theorem pullback_mem_typeSubmodule {ι : H →* G} {ι' : H →* G'} {Ξ : G' → G}
    (hΞ : ∀ (a : G') (k : H), Ξ (a * ι' k) = Ξ a * ι k) {ρ : Representation ℂ H W} {u : G → ℂ}
    (hu : u ∈ typeSubmodule ι ρ) : (fun a => u (Ξ a)) ∈ typeSubmodule ι' ρ :=
  map_typeSubmodule_le hΞ ρ (Submodule.mem_map_of_mem hu)

end Generic

section Slices

variable (F : Type) [Field F] [NumberField F]

theorem mul_right_equivariant (c : AdelicGL2 (𝓞 F) F)
    (hc : ∀ a : GL (Fin 2) (InfiniteAdeleRing F), Commute c (adelicArchGLIncl F a)) (w : InfinitePlace F)
    (a : GL (Fin 2) (InfiniteAdeleRing F)) (k : rowIsometrySubgroup₀ w.Completion) :
    adelicArchGLIncl F (a * archRowIsometryInclAt₀ F w k) * c =
      adelicArchGLIncl F a * c * rowIsometryInclAt₀ F w k := by
  show adelicArchGLIncl F (a * archRowIsometryInclAt₀ F w k) * c =
    adelicArchGLIncl F a * c * adelicArchGLIncl F (archRowIsometryInclAt₀ F w k)
  rw [map_mul, mul_assoc, mul_assoc, (hc (archRowIsometryInclAt₀ F w k)).eq]

theorem inv_mul_left_equivariant (c : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F)
    (a : GL (Fin 2) (InfiniteAdeleRing F)) (k : rowIsometrySubgroup₀ w.Completion) :
    c⁻¹ * adelicArchGLIncl F (a * archRowIsometryInclAt₀ F w k) =
      c⁻¹ * adelicArchGLIncl F a * rowIsometryInclAt₀ F w k := by
  show c⁻¹ * adelicArchGLIncl F (a * archRowIsometryInclAt₀ F w k) =
    c⁻¹ * adelicArchGLIncl F a * adelicArchGLIncl F (archRowIsometryInclAt₀ F w k)
  rw [map_mul, mul_assoc]

theorem slice_inv_eq_pullback (c : AdelicGL2 (𝓞 F) F) (h : AdelicGL2 (𝓞 F) F → ℂ) :
    (fun a : GL (Fin 2) (InfiniteAdeleRing F) => h (adelicArchGLIncl F a⁻¹ * c)) =
      pullback (fun a => c⁻¹ * adelicArchGLIncl F a) (fun x => h x⁻¹) := by
  funext a
  simp only [pullback_apply, _root_.mul_inv_rev, inv_inv, map_inv]

theorem slice_mem_archFactorDualTypeSubmoduleAt (c : AdelicGL2 (𝓞 F) F)
    (hc : ∀ a : GL (Fin 2) (InfiniteAdeleRing F), Commute c (adelicArchGLIncl F a)) (w : InfinitePlace F)
    (τ : ArchRepAt F w) {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : h ∈ archDualTypeSubmoduleAt F w τ) :
    (fun a => h (adelicArchGLIncl F a * c)) ∈ archFactorDualTypeSubmoduleAt F w τ :=
  pullback_mem_typeSubmodule (Ξ := fun a => adelicArchGLIncl F a * c)
    (fun a k => mul_right_equivariant F c hc w a k) hh

theorem slice_inv_mem_archFactorTypeSubmoduleAt (c : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F)
    (τ : ArchRepAt F w) {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : (fun x => h x⁻¹) ∈ archTypeSubmoduleAt F w τ) :
    (fun a => h (adelicArchGLIncl F a⁻¹ * c)) ∈ archFactorTypeSubmoduleAt F w τ := by
  rw [slice_inv_eq_pullback]
  exact map_typeSubmodule_le (Ξ := fun a => c⁻¹ * adelicArchGLIncl F a)
    (fun a k => inv_mul_left_equivariant F c w a k) τ.ρ (Submodule.mem_map_of_mem hh)

theorem isArchFactorBiFinite_slice (tys : ArchTypeFamily F) (c : AdelicGL2 (𝓞 F) F)
    (hc : ∀ a : GL (Fin 2) (InfiniteAdeleRing F), Commute c (adelicArchGLIncl F a))
    {h : AdelicGL2 (𝓞 F) F → ℂ} (hh : IsArchBiFinite F tys h) :
    IsArchFactorBiFinite F tys (fun a => h (adelicArchGLIncl F a * c)) := by
  obtain ⟨hleft, hright⟩ := hh
  refine ⟨?_, ?_⟩
  · rw [archFactorCutSubmodule, Submodule.mem_iInf]
    intro w
    have hw := (mem_archCutSubmodule_iff F tys _).mp hleft w
    have key := Submodule.mem_map_of_mem (f := pullback fun a => c⁻¹ * adelicArchGLIncl F a) hw
    rw [Submodule.map_iSup] at key
    have hle : (⨆ i : Fin (tys.card w),
        (archTypeSubmoduleAt F w (tys.rep w i)).map (pullback fun a => c⁻¹ * adelicArchGLIncl F a)) ≤
          ⨆ i : Fin (tys.card w), archFactorTypeSubmoduleAt F w (tys.rep w i) :=
      iSup_mono fun i => map_typeSubmodule_le (Ξ := fun a => c⁻¹ * adelicArchGLIncl F a)
        (fun a k => inv_mul_left_equivariant F c w a k) _
    show (fun a => h (adelicArchGLIncl F a⁻¹ * c)) ∈ _
    rw [slice_inv_eq_pullback]
    exact hle key
  · rw [archFactorDualCutSubmodule, Submodule.mem_iInf]
    intro w
    have hw := (mem_archDualCutSubmodule_iff F tys _).mp hright w
    have key := Submodule.mem_map_of_mem (f := pullback fun a => adelicArchGLIncl F a * c) hw
    rw [Submodule.map_iSup] at key
    have hle : (⨆ i : Fin (tys.card w),
        (archDualTypeSubmoduleAt F w (tys.rep w i)).map (pullback fun a => adelicArchGLIncl F a * c)) ≤
          ⨆ i : Fin (tys.card w), archFactorDualTypeSubmoduleAt F w (tys.rep w i) :=
      iSup_mono fun i => map_typeSubmodule_le (Ξ := fun a => adelicArchGLIncl F a * c)
        (fun a k => mul_right_equivariant F c hc w a k) _
    exact hle key

omit [NumberField F] in

theorem mem_archFactorDualTypeSubmoduleAt_of_isArchFactorBiFinite
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchFactorBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) fa)
    (w : InfinitePlace F) : fa ∈ archFactorDualTypeSubmoduleAt F w (τ w) := by
  have hw : fa ∈ ⨆ _i : Fin 1, archFactorDualTypeSubmoduleAt F w (τ w) := by
    have h2 := hfa.2
    rw [archFactorDualCutSubmodule, Submodule.mem_iInf] at h2
    exact h2 w
  exact (iSup_le fun _ => le_rfl : (⨆ _i : Fin 1, archFactorDualTypeSubmoduleAt F w (τ w)) ≤ _) hw

omit [NumberField F] in

theorem inv_mem_archFactorTypeSubmoduleAt_of_isArchFactorBiFinite
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchFactorBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) fa)
    (w : InfinitePlace F) : (fun a => fa a⁻¹) ∈ archFactorTypeSubmoduleAt F w (τ w) := by
  have hw : (fun a => fa a⁻¹) ∈ ⨆ _i : Fin 1, archFactorTypeSubmoduleAt F w (τ w) := by
    have h1 := hfa.1
    rw [archFactorCutSubmodule, Submodule.mem_iInf] at h1
    exact h1 w
  exact (iSup_le fun _ => le_rfl : (⨆ _i : Fin 1, archFactorTypeSubmoduleAt F w (τ w)) ≤ _) hw

end Slices

end TypeTransfer
