/-
  Additive Fourier transform on adèles, and the Schwartz–Bruhat space.

  `fourierIntegral ψ μ f w = ∫ v, ψ (-(v * w)) · f v ∂μ` is the additive Fourier
  transform against an additive character `ψ`; it agrees with mathlib's
  `Fourier.fourierIntegral` after composing with `Circle.coeHom`, and it is additive
  and ℂ-homogeneous.

  `pureTensorSet F` is the set of pure tensors: an archimedean Schwartz function on
  `mixedEmbedding.mixedSpace F` (transported along
  `InfiniteAdeleRing.ringEquiv_mixedSpace F`) times a locally constant, compactly
  supported function of the finite adèles. `schwartzBruhat F` is its ℂ-span, the
  Schwartz–Bruhat space of `𝔸_F`, with the induction principle
  `schwartzBruhat_induction` over that spanning description.

  Transcribed whole from `Definitions/Def_NumberField_AdelicFourier.lean` (pinned
  `aa2d8b3`); the pin node imports only mathlib, so this file is its natural home
  beside the other `Adelic*` role modules (playbook §2.3, §3.1).
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped SchwartzMap

namespace NumberField.AdelicFourier

section Fourier

variable {A : Type*} [CommRing A] [MeasurableSpace A]

-- pin: fourierIntegral (Def_NumberField_AdelicFourier.lean:16)
def fourierIntegral (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ) (w : A) : ℂ :=
  ∫ v, ψ (-(v * w)) * f v ∂μ

-- pin: fourierIntegral_def (Def_NumberField_AdelicFourier.lean:19)
theorem fourierIntegral_def (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ) (w : A) :
    fourierIntegral ψ μ f w = ∫ v, ψ (-(v * w)) * f v ∂μ :=
  rfl

-- pin: fourierIntegral_compAddChar (Def_NumberField_AdelicFourier.lean:23)
theorem fourierIntegral_compAddChar (e : AddChar A Circle) (μ : Measure A) (f : A → ℂ) :
    fourierIntegral (Circle.coeHom.compAddChar e) μ f = Fourier.fourierIntegral e μ f := by
  funext w
  simp only [fourierIntegral, Fourier.fourierIntegral_def, Circle.smul_def, smul_eq_mul]
  rfl

-- pin: fourierIntegral_zero (Def_NumberField_AdelicFourier.lean:29)
theorem fourierIntegral_zero (ψ : AddChar A ℂ) (μ : Measure A) :
    fourierIntegral ψ μ 0 = 0 := by
  funext w
  simp only [fourierIntegral, Pi.zero_apply, mul_zero, integral_zero]

-- pin: fourierIntegral_smul (Def_NumberField_AdelicFourier.lean:34)
theorem fourierIntegral_smul (ψ : AddChar A ℂ) (μ : Measure A) (c : ℂ) (f : A → ℂ) :
    fourierIntegral ψ μ (c • f) = c • fourierIntegral ψ μ f := by
  funext w
  simp only [fourierIntegral, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1 with v
  ring

-- pin: fourierIntegral_add (Def_NumberField_AdelicFourier.lean:41)
theorem fourierIntegral_add (ψ : AddChar A ℂ) (μ : Measure A) {f g : A → ℂ} (w : A)
    (hf : Integrable (fun v => ψ (-(v * w)) * f v) μ)
    (hg : Integrable (fun v => ψ (-(v * w)) * g v) μ) :
    fourierIntegral ψ μ (f + g) w = fourierIntegral ψ μ f w + fourierIntegral ψ μ g w := by
  simp only [fourierIntegral, Pi.add_apply, mul_add]
  exact integral_add hf hg

-- pin: norm_fourierIntegral_le_integral_norm (Def_NumberField_AdelicFourier.lean:48)
theorem norm_fourierIntegral_le_integral_norm (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ)
    (w : A) : ‖fourierIntegral ψ μ f w‖ ≤ ∫ v, ‖ψ (-(v * w)) * f v‖ ∂μ :=
  norm_integral_le_integral_norm _

-- pin: fourierIntegral_comp_add_right (Def_NumberField_AdelicFourier.lean:52)
theorem fourierIntegral_comp_add_right [MeasurableAdd A] (ψ : AddChar A ℂ) (μ : Measure A)
    [μ.IsAddRightInvariant] (f : A → ℂ) (v₀ : A) :
    fourierIntegral ψ μ (f ∘ fun v => v + v₀) = fun w => ψ (v₀ * w) * fourierIntegral ψ μ f w := by
  funext w
  simp only [fourierIntegral, Function.comp_apply]
  have h : (fun v => ψ (-(v * w)) * f (v + v₀))
      = fun v => (fun u => ψ (-((u - v₀) * w)) * f u) (v + v₀) := by
    funext v
    simp only [add_sub_cancel_right]
  rw [h, integral_add_right_eq_self (fun u => ψ (-((u - v₀) * w)) * f u) v₀, ← integral_const_mul]
  congr 1 with u
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

end Fourier

section SchwartzBruhat

variable (F : Type*) [Field F] [NumberField F]

open scoped Classical in

-- pin: pureTensorSet (Def_NumberField_AdelicFourier.lean:75)
def pureTensorSet : Set (AdeleRing (𝓞 F) F → ℂ) :=
  {f | ∃ (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (h : FiniteAdeleRing (𝓞 F) F → ℂ),
      IsLocallyConstant h ∧ HasCompactSupport h ∧
      f = fun x => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2}

-- pin: schwartzBruhat (Def_NumberField_AdelicFourier.lean:80)
def schwartzBruhat : Submodule ℂ (AdeleRing (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (pureTensorSet F)

variable {F}

open scoped Classical in
-- pin: tensor_mem_pureTensorSet (Def_NumberField_AdelicFourier.lean:86)
theorem tensor_mem_pureTensorSet (g : 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (h : FiniteAdeleRing (𝓞 F) F → ℂ) (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    (fun x : AdeleRing (𝓞 F) F => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h x.2)
      ∈ pureTensorSet F :=
  ⟨g, h, hlc, hcs, rfl⟩

-- pin: mem_schwartzBruhat_of_mem_pureTensorSet (Def_NumberField_AdelicFourier.lean:92)
theorem mem_schwartzBruhat_of_mem_pureTensorSet {f : AdeleRing (𝓞 F) F → ℂ}
    (hf : f ∈ pureTensorSet F) : f ∈ schwartzBruhat F :=
  Submodule.subset_span hf

-- pin: zero_mem_pureTensorSet (Def_NumberField_AdelicFourier.lean:96)
theorem zero_mem_pureTensorSet : (0 : AdeleRing (𝓞 F) F → ℂ) ∈ pureTensorSet F :=
  ⟨0, 0, IsLocallyConstant.const 0, HasCompactSupport.zero, by funext x; simp⟩

-- pin: zero_mem_schwartzBruhat (Def_NumberField_AdelicFourier.lean:99)
theorem zero_mem_schwartzBruhat : (0 : AdeleRing (𝓞 F) F → ℂ) ∈ schwartzBruhat F :=
  Submodule.zero_mem _

-- pin: schwartzBruhat_induction (Def_NumberField_AdelicFourier.lean:102)
theorem schwartzBruhat_induction {p : (f : AdeleRing (𝓞 F) F → ℂ) → f ∈ schwartzBruhat F → Prop}
    (tensor : ∀ (f) (hf : f ∈ pureTensorSet F), p f (mem_schwartzBruhat_of_mem_pureTensorSet hf))
    (zero : p 0 zero_mem_schwartzBruhat)
    (add : ∀ f g (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F),
      p f hf → p g hg → p (f + g) (Submodule.add_mem _ hf hg))
    (smul : ∀ (c : ℂ) f (hf : f ∈ schwartzBruhat F), p f hf → p (c • f) (Submodule.smul_mem _ c hf))
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) : p f hf :=
  Submodule.span_induction tensor zero add smul hf

end SchwartzBruhat

end NumberField.AdelicFourier

end
