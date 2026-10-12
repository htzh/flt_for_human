/-
  Centrality of the archimedean slices.

  `contSubmodule` is the continuous functions on `GL₂(𝔸_F^∞)`, and
  `typeSubmodule_eq_typeSpan` identifies the `IsotypicCuspSpace` type submodule with the
  `BiIsotypic` right-representation type span. On that surface `convKer_comm_of_types`
  proves the kernel commutation for a spherical test factor against a doubly
  type-bounded slice, `convKer_comm_slice` specializes it to the frame slice of an
  archimedean bi-finite function, and `adelicKernel_comm` assembles the two from
  `ProjectedHaar.convKer_cut_comm` and `levelSpherical_eq_cut`.

  Transcribed from the compact silo's general-`U` spelling,
  `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.lean:3162–3375`
  (the plain silo carries the same block at `:3203–3417` with `levelSubgroup F N` for
  `U`), pinned `aa2d8b3`. The declarations are `private` at the pin and land here public
  as the shared engine; the statements are verbatim.
-/
import FLTForHuman.RepTheory.BiIsotypic
import FLTForHuman.RepTheory.TypeSpan
import FLTForHuman.RepTheory.ProjectedHaar
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.ArchSpherical
import FLTForHuman.AutomorphicForm.Adelic.ArchWeightChar
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.MeasureAssembly
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.PlaceClassData
import Mathlib.Tactic

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls feed instance search, and `[NumberField F]` is
-- auto-included by statements that only use `[Field F]`.
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open scoped BigOperators

-- Activate the `scoped` instances of the measure assembly (the pin's
-- `p2m_reactivate "…MeasureAssembly"`).
open scoped MeasureAssembly

section SliceCentrality

open MeasureTheory NumberField AutomorphicForm

noncomputable section

namespace SliceCentrality

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.glBorel MeasureAssembly.archBorel

def contSubmodule : Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) where
  carrier := {ψ | Continuous ψ}
  add_mem' ha hb := ha.add hb
  zero_mem' := continuous_const
  smul_mem' c _ hψ := hψ.const_smul c

theorem mem_contSubmodule_iff (ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    ψ ∈ contSubmodule F ↔ Continuous ψ := Iff.rfl

theorem leftRep_eq {H : Type*} [Group H] (e : H →* GL (Fin 2) (InfiniteAdeleRing F)) (a : H)
    (ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    BiIsotypic.leftRep (k := ℂ) e a ψ = fun y => ψ ((e a)⁻¹ * y) :=
  funext fun y => BiIsotypic.leftRep_apply e a ψ y

theorem rightRep_eq {H : Type*} [Group H] (e : H →* GL (Fin 2) (InfiniteAdeleRing F)) (a : H)
    (ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    BiIsotypic.rightRep (k := ℂ) e a ψ = fun y => ψ (y * e a) :=
  funext fun y => BiIsotypic.rightRep_apply e a ψ y

theorem typeSubmodule_eq_typeSpan {H : Type*} [Group H]
    (e : H →* GL (Fin 2) (InfiniteAdeleRing F)) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ H W) :
    typeSubmodule e σ = BiIsotypic.typeSpan (BiIsotypic.rightRep e) σ := by
  unfold typeSubmodule BiIsotypic.typeSpan IsRightEquivariant
  congr 1
  ext f
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨T, hT, hf⟩
    exact ⟨T, fun g u => funext fun x => by rw [BiIsotypic.rightRep_apply]; exact hT g u x, hf⟩
  · rintro ⟨T, hT, hf⟩
    exact ⟨T, fun g u x => by rw [← BiIsotypic.rightRep_apply (k := ℂ) e g (T u) x]; exact congrFun (hT g u) x,
      hf⟩

variable (U : Subgroup (AdelicGL2 (𝓞 F) F))

theorem convKer_comm_of_types (hUc : IsCompact (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfac : Continuous fa) (hfas : HasCompactSupport fa)
    (hfaC : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x)
    {ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hψc : Continuous ψ)
    (hψL : ∀ w, ψ ∈ BiIsotypic.typeSpan (BiIsotypic.leftRep (k := ℂ) (archRowIsometryInclAt₀ F w)) (τ w).ρ)
    (hψR : ∀ w,
      ψ ∈ BiIsotypic.typeSpan (BiIsotypic.rightRep (k := ℂ) (archRowIsometryInclAt₀ F w)) (τ w).ρ.dual) :
    ProjectedHaar.convKer (MeasureAssembly.archNu F U) fa ψ =
      ProjectedHaar.convKer (MeasureAssembly.archNu F U) ψ fa := by
  haveI : (MeasureAssembly.archNu F U).IsHaarMeasure := MeasureAssembly.archNu_isHaarMeasure F U hUc hUo
  haveI : (MeasureAssembly.archNu F U).IsMulRightInvariant := MeasureAssembly.archNu_isMulRightInvariant F U hUo
  haveI : (MeasureAssembly.archNu F U).IsInvInvariant := MeasureAssembly.archNu_isInvInvariant F U hUc hUo
  haveI : ∀ w, (τ w).ρ.IsIrreducible := hirr
  have hν : (MeasureAssembly.archNu F U).map (PlaceClassData.thetaArch F) = MeasureAssembly.archNu F U :=
    MeasureAssembly.archNu_map_eq_self F U hUc hUo (PlaceClassData.archAntiInvolution F)

  have hemb : ∀ (w w' : InfinitePlace F), w ≠ w' → ∀ (a : rowIsometrySubgroup₀ w.Completion)
      (b : rowIsometrySubgroup₀ w'.Completion), Commute (archRowIsometryInclAt₀ F w a) (archRowIsometryInclAt₀ F w' b) :=
    fun w w' hww a b => commute_archGLIncl_of_ne (F := F) hww _ _
  have hCL : ∀ (w : InfinitePlace F) (a : rowIsometrySubgroup₀ w.Completion) (φ' : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      φ' ∈ contSubmodule F → BiIsotypic.leftRep (k := ℂ) (archRowIsometryInclAt₀ F w) a φ' ∈ contSubmodule F := by
    intro w a φ' hφ'
    rw [mem_contSubmodule_iff] at hφ' ⊢
    rw [leftRep_eq]
    exact hφ'.comp (continuous_const.mul continuous_id)
  have hCR : ∀ (w : InfinitePlace F) (b : rowIsometrySubgroup₀ w.Completion) (φ' : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      φ' ∈ contSubmodule F → BiIsotypic.rightRep (k := ℂ) (archRowIsometryInclAt₀ F w) b φ' ∈ contSubmodule F := by
    intro w b φ' hφ'
    rw [mem_contSubmodule_iff] at hφ' ⊢
    rw [rightRep_eq]
    exact hφ'.comp (continuous_id.mul continuous_const)
  have hKaddL : ∀ ψ₁ ψ₂, ψ₁ ∈ contSubmodule F → ψ₂ ∈ contSubmodule F →
      ProjectedHaar.convKer (MeasureAssembly.archNu F U) (ψ₁ + ψ₂) fa =
        ProjectedHaar.convKer (MeasureAssembly.archNu F U) ψ₁ fa +
          ProjectedHaar.convKer (MeasureAssembly.archNu F U) ψ₂ fa := by
    intro ψ₁ ψ₂ h₁ h₂
    funext x
    rw [Pi.add_apply]
    exact KernelSides.convKer_add_left (MeasureAssembly.archNu F U) fa hfac hfas ψ₁ ψ₂ h₁ h₂ x
  have hKsmulL : ∀ (c : ℂ) (ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ), ψ ∈ contSubmodule F →
      ProjectedHaar.convKer (MeasureAssembly.archNu F U) (c • ψ) fa =
        c • ProjectedHaar.convKer (MeasureAssembly.archNu F U) ψ fa := by
    intro c ψ _
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    exact KernelSides.convKer_smul_left (MeasureAssembly.archNu F U) fa c ψ x
  have hKaddR : ∀ ψ₁ ψ₂, ψ₁ ∈ contSubmodule F → ψ₂ ∈ contSubmodule F →
      ProjectedHaar.convKer (MeasureAssembly.archNu F U) fa (ψ₁ + ψ₂) =
        ProjectedHaar.convKer (MeasureAssembly.archNu F U) fa ψ₁ +
          ProjectedHaar.convKer (MeasureAssembly.archNu F U) fa ψ₂ := by
    intro ψ₁ ψ₂ h₁ h₂
    funext x
    rw [Pi.add_apply]
    exact KernelSides.convKer_add_right (MeasureAssembly.archNu F U) fa hfac hfas ψ₁ ψ₂ h₁ h₂ x
  have hKsmulR : ∀ (c : ℂ) (ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ), ψ ∈ contSubmodule F →
      ProjectedHaar.convKer (MeasureAssembly.archNu F U) fa (c • ψ) =
        c • ProjectedHaar.convKer (MeasureAssembly.archNu F U) fa ψ := by
    intro c ψ _
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    exact KernelSides.convKer_smul_right (MeasureAssembly.archNu F U) fa c ψ x
  have hKL : ∀ (w : InfinitePlace F) (a : rowIsometrySubgroup₀ w.Completion) (ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      ψ ∈ contSubmodule F →
        ProjectedHaar.convKer (MeasureAssembly.archNu F U) (BiIsotypic.leftRep (k := ℂ) (archRowIsometryInclAt₀ F w) a ψ) fa =
          BiIsotypic.leftRep (k := ℂ) (archRowIsometryInclAt₀ F w) a
            (ProjectedHaar.convKer (MeasureAssembly.archNu F U) ψ fa) := by
    intro w a ψ _
    rw [leftRep_eq, leftRep_eq]
    funext x
    exact ProjectedHaar.convKer_left_fun (MeasureAssembly.archNu F U) ψ fa (archRowIsometryInclAt₀ F w a) x
  have hKR : ∀ (w : InfinitePlace F) (a : rowIsometrySubgroup₀ w.Completion) (ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ),
      ψ ∈ contSubmodule F →
        ProjectedHaar.convKer (MeasureAssembly.archNu F U) fa (BiIsotypic.leftRep (k := ℂ) (archRowIsometryInclAt₀ F w) a ψ) =
          BiIsotypic.leftRep (k := ℂ) (archRowIsometryInclAt₀ F w) a
            (ProjectedHaar.convKer (MeasureAssembly.archNu F U) fa ψ) := by
    intro w a ψ _
    rw [leftRep_eq, leftRep_eq]
    funext x
    exact ProjectedHaar.convKer_left_arg (MeasureAssembly.archNu F U) fa ψ (archRowIsometryInclAt₀ F w a)
      (fun y => hfaC w a y) x
  have hB : ∀ ψ₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, ψ₀ ∈ contSubmodule F →
      (∀ (w : InfinitePlace F) (g : rowIsometrySubgroup₀ w.Completion),
        BiIsotypic.leftRep (k := ℂ) (archRowIsometryInclAt₀ F w) g
          (BiIsotypic.rightRep (k := ℂ) (archRowIsometryInclAt₀ F w) g ψ₀) = ψ₀) →
      ProjectedHaar.convKer (MeasureAssembly.archNu F U) fa ψ₀ =
        ProjectedHaar.convKer (MeasureAssembly.archNu F U) ψ₀ fa := by
    intro ψ₀ _ hinv
    exact PlaceClassData.convKer_comm_of_place_invariant F (MeasureAssembly.archNu F U) hν fa ψ₀ hfaC
      fun w g x => BiIsotypic.conj_invariant_of_invariant (archRowIsometryInclAt₀ F w) ψ₀ (hinv w) g x
  exact BiIsotypic.pairing_symm_of_mem_typeSpan (fun w => (τ w).ρ)
    (fun w => BiIsotypic.leftRep (k := ℂ) (archRowIsometryInclAt₀ F w))
    (fun w => BiIsotypic.rightRep (k := ℂ) (archRowIsometryInclAt₀ F w))
    (fun w w' a b => BiIsotypic.leftRep_comp_rightRep _ _ a b)
    (fun w w' hww a b => BiIsotypic.leftRep_comp_leftRep _ _ a b (hemb w w' hww a b))
    (fun w w' hww a b => BiIsotypic.rightRep_comp_rightRep _ _ a b (hemb w w' hww a b))
    (contSubmodule F) hCL hCR (ProjectedHaar.convKer (MeasureAssembly.archNu F U)) fa
    hKaddL hKsmulL hKaddR hKsmulR hKL hKR hB ψ hψc hψL hψR

theorem convKer_comm_slice (hUc : IsCompact (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) fa)
    {h : AdelicGL2 (𝓞 F) F → ℂ} (hhc : Continuous h)
    (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (u : AdelicGL2 (𝓞 F) F) :
    ProjectedHaar.convKer (MeasureAssembly.archNu F U) fa (ProjectedHaar.slice (ProjectedHaar.adelicFrame F) h u) =
      ProjectedHaar.convKer (MeasureAssembly.archNu F U) (ProjectedHaar.slice (ProjectedHaar.adelicFrame F) h u) fa := by
  obtain ⟨hfaT, -, hfaC⟩ := hfa

  have hslice : IsArchFactorBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)
      (ProjectedHaar.slice (ProjectedHaar.adelicFrame F) h u) :=
    TypeTransfer.isArchFactorBiFinite_slice F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)
      ((ProjectedHaar.adelicFrame F).ιf ((ProjectedHaar.adelicFrame F).πf u))
      (fun a => (ProjectedHaar.ι_mul_ιf_comm (ProjectedHaar.adelicFrame F) a _).symm) hht
  have hψR : ∀ w, ProjectedHaar.slice (ProjectedHaar.adelicFrame F) h u ∈
      BiIsotypic.typeSpan (BiIsotypic.rightRep (k := ℂ) (archRowIsometryInclAt₀ F w)) (τ w).ρ.dual := by
    intro w
    rw [← typeSubmodule_eq_typeSpan]
    exact TypeTransfer.mem_archFactorDualTypeSubmoduleAt_of_isArchFactorBiFinite F τ hslice w
  have hψL : ∀ w, ProjectedHaar.slice (ProjectedHaar.adelicFrame F) h u ∈
      BiIsotypic.typeSpan (BiIsotypic.leftRep (k := ℂ) (archRowIsometryInclAt₀ F w)) (τ w).ρ := by
    intro w
    refine BiIsotypic.mem_typeSpan_leftRep_of_inv_mem (archRowIsometryInclAt₀ F w) (τ w).ρ ?_
    rw [← typeSubmodule_eq_typeSpan]
    exact TypeTransfer.inv_mem_archFactorTypeSubmoduleAt_of_isArchFactorBiFinite F τ hslice w
  exact convKer_comm_of_types F U hUc hUo τ hirr (MeasureAssembly.testFactor_continuous F hfaT)
    (MeasureAssembly.testFactor_hasCompactSupport F hfaT) hfaC
    (ProjectedHaar.continuous_slice (ProjectedHaar.adelicFrame F) h hhc (ProjectedHaar.continuous_adelicFrame_ι F) u)
    hψL hψR

theorem adelicKernel_comm (hUK : U ≤ finiteAdelicGL2Subgroup F)
    (hUc : IsCompact (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)
      (U) f)
    {h : AdelicGL2 (𝓞 F) F → ℂ} (hhc : Continuous h)
    (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, h (u * x) = h x ∧ h (x * u) = h x) :
    MeasureAssembly.adelicKernel F h f = MeasureAssembly.adelicKernel F f h := by
  obtain ⟨fa, hfa, hfcut⟩ := MeasureAssembly.levelSpherical_eq_cut F U hf
  have hlev : ProjectedHaar.level (ProjectedHaar.adelicFrame F)
      ((U).map (ProjectedHaar.adelicFrame F).πf) = U :=
    ProjectedHaar.level_map_eq (ProjectedHaar.adelicFrame F) (U)
      fun u hu => MeasureGlue.glArch_eq_one_of_mem F U hUK hu
  have hL : ∀ v ∈ ProjectedHaar.level (ProjectedHaar.adelicFrame F)
      ((U).map (ProjectedHaar.adelicFrame F).πf), ∀ x, h (v * x) = h x :=
    fun v hv x => (hhU x v (hlev ▸ hv)).1
  have hR : ∀ v ∈ ProjectedHaar.level (ProjectedHaar.adelicFrame F)
      ((U).map (ProjectedHaar.adelicFrame F).πf), ∀ x, h (x * v) = h x :=
    fun v hv x => (hhU x v (hlev ▸ hv)).2
  rw [hfcut]
  symm
  exact ProjectedHaar.convKer_cut_comm (ProjectedHaar.adelicFrame F) (adelicGLHaar (Fin 2) (𝓞 F) F)
    ((U).map (ProjectedHaar.adelicFrame F).πf) fa h
    (ProjectedHaar.continuous_adelicFrame_π F) (MeasureAssembly.isOpen_level_slab F U hUo).measurableSet
    (MeasureAssembly.testFactor_continuous F hfa.1).measurable hhc (ProjectedHaar.continuous_adelicFrame_ι F) hL hR
    (convKer_comm_slice F U hUc hUo τ hirr hfa hhc hht)

end SliceCentrality

end

end SliceCentrality
