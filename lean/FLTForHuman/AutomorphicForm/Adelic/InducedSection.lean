/-  Induced sections of the Borel character pair.

  `IsInducedSection χ₁ χ₂ φ` says `φ` transforms by `χ₁` on the first diagonal entry and
  `χ₂` on the second (`φ (b g) = χ₁ b₀₀ · χ₂ b₁₁ · φ g` for `b` upper-triangular), and
  `inducedSectionSubmodule` is the linear span of the induced sections. The file records
  the submodule and its right-translation/unipotent/central-scalar closure.

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_InducedSection.lean`
  (pinned `aa2d8b3`), the pin namespace `AutomorphicForm` kept.-/
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

section InducedSection

open NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

-- pin: IsInducedSection (Def_AutomorphicForm_InducedSection.lean:14)
def IsInducedSection (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) (φ : AdelicGL2 R K → ℂ) : Prop :=
  ∀ (b : AdelicGL2 R K) (hb : b ∈ adelicBorel R K) (g : AdelicGL2 R K),
    φ (b * g)
      = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
        * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ) * φ g

variable {R K}

-- pin: isInducedSection_zero (Def_AutomorphicForm_InducedSection.lean:22)
theorem isInducedSection_zero (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) :
    IsInducedSection R K χ₁ χ₂ (fun _ => (0 : ℂ)) := by
  intro b hb g
  simp

-- pin: chiDet_mul (Def_AutomorphicForm_InducedSection.lean:27)
theorem chiDet_mul (χ : (AdeleRing R K)ˣ →* ℂˣ) (x y : AdelicGL2 R K) :
    chiDet R K χ (x * y) = chiDet R K χ x * chiDet R K χ y := by
  unfold chiDet
  rw [map_mul, map_mul, Units.val_mul]

-- pin: isInducedSection_chiDet (Def_AutomorphicForm_InducedSection.lean:32)
theorem isInducedSection_chiDet (χ : (AdeleRing R K)ˣ →* ℂˣ) :
    IsInducedSection R K χ χ (chiDet R K χ) := by
  intro b hb g
  rw [chiDet_mul]
  congr 1
  show chiDet R K χ b = _
  unfold chiDet
  rw [det_borel_eq_diag_mul hb, map_mul, Units.val_mul]

-- pin: inducedSectionSubmodule (Def_AutomorphicForm_InducedSection.lean:41)
def inducedSectionSubmodule (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ) :
    Submodule ℂ (AdelicGL2 R K → ℂ) where
  carrier := {φ | IsInducedSection R K χ₁ χ₂ φ}
  zero_mem' := isInducedSection_zero χ₁ χ₂
  add_mem' := by
    intro φ ψ hφ hψ b hb g
    show φ (b * g) + ψ (b * g)
        = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
          * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ) * (φ g + ψ g)
    rw [hφ b hb g, hψ b hb g]
    ring
  smul_mem' := by
    intro c φ hφ b hb g
    show c * φ (b * g)
        = ((χ₁ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ)
          * ((χ₂ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel R K))) : ℂˣ) : ℂ) * (c * φ g)
    rw [hφ b hb g]
    ring

-- pin: mem_inducedSectionSubmodule_iff (Def_AutomorphicForm_InducedSection.lean:60)
@[simp] theorem mem_inducedSectionSubmodule_iff (χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ)
    {φ : AdelicGL2 R K → ℂ} :
    φ ∈ inducedSectionSubmodule χ₁ χ₂ ↔ IsInducedSection R K χ₁ χ₂ φ := Iff.rfl

-- pin: rightTranslate (Def_AutomorphicForm_InducedSection.lean:64)
theorem IsInducedSection.rightTranslate {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ) (h : AdelicGL2 R K) :
    IsInducedSection R K χ₁ χ₂ (fun g => φ (g * h)) := by
  intro b hb g
  show φ (b * g * h) = _
  rw [mul_assoc, hφ b hb (g * h)]

-- pin: rightTranslate_mem_inducedSectionSubmodule (Def_AutomorphicForm_InducedSection.lean:71)
theorem rightTranslate_mem_inducedSectionSubmodule {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : φ ∈ inducedSectionSubmodule χ₁ χ₂) (h : AdelicGL2 R K) :
    (fun g => φ (g * h)) ∈ inducedSectionSubmodule χ₁ χ₂ :=
  IsInducedSection.rightTranslate hφ h

-- pin: isInducedSection_unipotent_mul (Def_AutomorphicForm_InducedSection.lean:76)
theorem isInducedSection_unipotent_mul {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ) (x : AdeleRing R K)
    (g : AdelicGL2 R K) :
    φ (unipotentGL2 x * g) = φ g := by
  rw [hφ (unipotentGL2 x) (unipotentGL2_mem_borelSubgroup x) g, borelDiagFst_unipotentGL2,
    borelDiagSnd_unipotentGL2]
  simp

-- pin: isInducedSection_centralScalar_mul (Def_AutomorphicForm_InducedSection.lean:84)
theorem isInducedSection_centralScalar_mul {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ}
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ) (z : (AdeleRing R K)ˣ)
    (g : AdelicGL2 R K) :
    φ (centralScalar R K z * g) = ((χ₁ z : ℂˣ) : ℂ) * ((χ₂ z : ℂˣ) : ℂ) * φ g := by
  rw [hφ (centralScalar R K z) (centralScalar_mem_adelicBorel R K z) g,
    borelDiagFst_centralScalar R K z (centralScalar_mem_adelicBorel R K z),
    borelDiagSnd_centralScalar R K z (centralScalar_mem_adelicBorel R K z)]
end InducedSection

end AutomorphicForm
