/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/IsotypicArchType.lean`.

  The four rows under test are exercised in composition, never by `#check`:

  * `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` (242) is fed the *defining*
    supremum of `isotypicCuspSubmodule` (which is a `Submodule.span`) to make the membership
    predicate an iff at non-zero vectors, and — through `Submodule.ne_bot_iff` — to read an
    actual isotypic form off a non-bottom isotypic cusp submodule. The second use is the one
    the spectrum theory performs: the span is only a `span`, so the pointwise predicate has to
    be recovered, and it is recovered exactly on the non-zero part;
  * `exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates` (390) is
    instantiated at the archimedean data `ι := rowIsometryInclAt₀ w`, `ρ i := (ρs i).ρ`, where
    its supremum `⨆ i, typeSubmodule ι (ρ i)` *is* the archimedean type cut
    `⨆ i, archTypeSubmoduleAt F w (ρs i)` (definitionally), so the row's first conjunct becomes
    the reproducer statement for the cut; the injectivity hypothesis the row asks for is the
    one the archimedean inclusion supplies;
  * `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` (214) is
    applied after splitting the `⊓` into its two components, which is the form in which the cut
    arguments hold their data (a member of `Q` that also lies in the cut);
  * `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` (282) is instantiated at
    `σ = 0`, where the determinant twist degenerates to the constant `1` and the row reads
    "the conjugate-inverse of an archimedean test factor is one", and then iterated: applying it
    to its own output shows the twist is stable under composing two exponents.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF32Consumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.IsotypicArchType

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
  AutomorphicForm.CuspidalSpectrum MeasureTheory
open IsDedekindDomain Filter Matrix Complex ComplexConjugate
open scoped ENNReal Topology ComplexConjugate
open scoped AutomorphicForm.ArchCompactOrbit

namespace AutomorphicFormSetAF32Consumer

variable (F : Type) [Field F] [NumberField F]
variable (D : Set (AdelicGL2 (𝓞 F) F))
  (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
  (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)

/-- Row 242 against the *defining* span: at a non-zero vector, being an isotypic form and lying
in the isotypic cusp submodule are the same statement. The forward direction is the span's own
`subset_span`; the backward direction is the row. -/
theorem isIsotypicCuspFormAt_iff_mem_of_ne_zero
    (ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h0 : φ ≠ 0) :
    IsIsotypicCuspFormAt F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ φ ↔
      φ ∈ isotypicCuspSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ := by
  refine ⟨fun h => h.mem_isotypicCuspSubmodule, fun h => ?_⟩
  exact isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule F D U gen ξ N S Φ φ h h0

/-- Row 242 read through `Submodule.ne_bot_iff`: a non-bottom isotypic cusp submodule carries a
non-zero isotypic form. This is the shape in which the constituent theory consumes the row. -/
theorem exists_isIsotypicCuspFormAt_of_ne_bot
    (ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (h : isotypicCuspSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ ≠ ⊥) :
    ∃ φ : AdelicGL2 (𝓞 F) F → ℂ,
      IsIsotypicCuspFormAt F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ φ ∧ φ ≠ 0 := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨φ, isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule F D U gen ξ N S Φ φ hφ hφ0, hφ0⟩

/-- The archimedean inclusion `rowIsometryInclAt₀ w` is injective — the hypothesis row 390 asks
for, discharged from the two components of `adelicArchGLInclAt`. -/
theorem injective_rowIsometryInclAt₀ (w : InfinitePlace F) :
    Function.Injective (rowIsometryInclAt₀ F w) := by
  intro a b hab
  have hgl : ∀ k : GL (Fin 2) w.Completion,
      glArch (𝓞 F) F (adelicArchGLInclAt F w k) = archGLIncl F w k := fun k => by
    simp only [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl]
  have h2 := congrArg (fun u => archComponent F w (glArch (𝓞 F) F u)) hab
  simp only [rowIsometryInclAt₀_apply, hgl, archComponent_archGLIncl_self] at h2
  exact Subtype.ext h2

/-- Row 390 instantiated at the archimedean type data: a right-equivariant continuous linear map
out of the model `(Fin n → ℂ)` lands in the archimedean type cut `⨆ i, archTypeSubmoduleAt w (ρs i)`
— the row's `⨆ i, typeSubmodule ι (ρ i)` at `ι := rowIsometryInclAt₀ w`. -/
theorem archType_model_first_conjunct (w : InfinitePlace F) (m : ℕ)
    (ρs : Fin m → ArchRepAt F w) :
    ∃ (n : ℕ) (ρc : rowIsometrySubgroup₀ w.Completion →* Matrix (Fin n) (Fin n) ℂ),
      Continuous ρc ∧
        ∀ (T : (Fin n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)),
          (∀ (k : rowIsometrySubgroup₀ w.Completion) (x : Fin n → ℂ),
            T ((ρc k).mulVec x) = fun y => T x (y * rowIsometryInclAt₀ F w k)) →
          ∀ x : Fin n → ℂ, T x ∈ ⨆ i, archTypeSubmoduleAt F w (ρs i) := by
  obtain ⟨n, ρc, hρc, hrow⟩ :=
    exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
      (K := rowIsometrySubgroup₀ w.Completion) (I := Fin m)
      (W := fun i => Fin (ρs i).n → ℂ) (fun i => (ρs i).ρ)
  refine ⟨n, ρc, hρc, fun T hT => ?_⟩
  exact (hrow (AdelicGL2 (𝓞 F) F) (rowIsometryInclAt₀ F w)
    (injective_rowIsometryInclAt₀ F w)).1 T hT

/-- Row 214 after splitting the `⊓`: a member of `Q` that also lies in the archimedean cut is
captured by the `Q`-parts of the `σ`-pieces, which is the form the cut arguments state. -/
theorem mem_iSup_inf_of_mem_inf_iSup (w : InfinitePlace F) (m : ℕ) (ρs : Fin m → ArchRepAt F w)
    (r : ℕ) (σs : Fin r → ArchRepAt F w)
    (hσ : ∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
          rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S',
            rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs j))
    (Q : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hQc : ∀ g ∈ Q, Continuous g)
    (hQs : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ Q,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ Q)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφQ : φ ∈ Q)
    (hφT : φ ∈ ⨆ i, archTypeSubmoduleAt F w (ρs i)) :
    φ ∈ ⨆ j, Q ⊓ archTypeSubmoduleAt F w (σs j) :=
  CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous F w m ρs r σs hσ
    Q hQc hQs (Submodule.mem_inf.mpr ⟨hφQ, hφT⟩)

/-- Row 282 at `σ = 0`: the determinant twist is the constant `1`, so the conjugate-inverse of an
archimedean test factor is again one. -/
theorem isArchTestFactor_conj_inv {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (fun y : GL (Fin 2) (InfiniteAdeleRing F) => conj (fa y⁻¹)) := by
  have h := isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow F 0 fa hfa
  simpa using h

/-- Row 282 applied to its own output: the character twist is stable under composing the two
exponents, so the doubly twisted factor is again an archimedean test factor. -/
theorem isArchTestFactor_conj_inv_twist_comp (σ σ' : ℝ)
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (fun y : GL (Fin 2) (InfiniteAdeleRing F) =>
      conj ((fun y : GL (Fin 2) (InfiniteAdeleRing F) => conj (fa y⁻¹) *
        ((NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ) : ℝ) : ℂ)) y⁻¹) *
        ((NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ') : ℝ) : ℂ)) :=
  isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow F σ'
    (fun y : GL (Fin 2) (InfiniteAdeleRing F) => conj (fa y⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ) : ℝ) : ℂ))
    (isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow F σ fa hfa)

/-- Row 282 at `σ = 0` fed the port's zero archimedean test factor: the twisted zero factor is a
test factor again, and it is the zero function. -/
theorem isArchTestFactor_zero_twist_eq_zero :
    IsArchTestFactor F (fun y : GL (Fin 2) (InfiniteAdeleRing F) =>
      conj ((fun _ => (0 : ℂ)) y⁻¹) *
        ((NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-(0 : ℝ)) : ℝ) : ℂ)) ∧
      (fun y : GL (Fin 2) (InfiniteAdeleRing F) =>
        conj ((fun _ => (0 : ℂ)) y⁻¹) *
          ((NumberField.TateGlobal.ideleNorm F
            (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-(0 : ℝ)) : ℝ) : ℂ))
        = fun _ => (0 : ℂ) :=
  ⟨isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow F 0 (fun _ => 0) (isArchTestFactor_zero F), by
    funext y
    simp⟩

end AutomorphicFormSetAF32Consumer
