/-
The Fourier transform preserves the Schwartz–Bruhat space.

For a Haar measure `μ` on the adèles and a global additive character `ψ` whose archimedean component
is the standard character, the Fourier transform `fourierIntegral ψ μ` carries the Schwartz–Bruhat
space `schwartzBruhat F` into itself: the space of the Fourier transform is closed under Fourier
transformation. Together with SET-AF112's inversion row it makes `fourierIntegral` an automorphism of
that space, which is the form the functional-equation theory consumes.

Its proof is the pure-tensor computation `fourierIntegral_pureTensor_eq` (the transform of a pure
tensor is the product of the two local transforms, with the `covolume`/box factor), the induction over
the Schwartz–Bruhat space's generating set, and `integrable_of_mem_schwartzBruhat`.

Assumes: `NumberTheory/AdelicFourier` (`schwartzBruhat`, `fourierIntegral`), `Transform` (the
pure-tensor identity), `Space` (integrability), and `NumberField/GlobalAddChar`.

Transcribed from the pin below (pinned `aa2d8b3`, 141 `S_` lines).

## The rows

* `NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace` — 141 pin `S_` lines.
* `NumberField.AdelicFourier.integrable_fourierIntegrand` — the pin's `S_…:37` helper (the transform's
  integrand is dominated by `‖f‖`).
* `NumberField.AdelicFourier.fourierIntegral_psiV_eq` — the pin's `S_…:52` helper (the archimedean
  component of `ψ` is the standard character, so `ψV`'s transform is mathlib's
  `VectorFourier.fourierIntegral` against the trace form).
* `NumberField.AdelicFourier.fstab0_impl` — the pin's `S_…:68` helper (the induction over
  `pureTensorSet`); the pin's `Ws25FStab0` stage namespace is dropped, so all four declarations are
  flat in `NumberField.AdelicFourier`.

## Port deltas

Proof-level only; every statement is the pin's text.

* The pin's `fourierIntegral_pureTensor_eq` (`S_…:90`) takes `hψ.continuous` and
  `norm_apply_eq_one_of_isGlobalAddChar F hψ` on top of `g`, `hlc`, `hcs`. The port's copy
  (`NumberTheory/AdelicFourier/Transform.lean:119`) is a **generalisation** over an arbitrary
  `g : mixedSpace F → ℂ` with no continuity or unitarity hypothesis on `ψ`, so the call at
  `fstab0_impl` drops those two arguments and the `hT` hypothesis becomes
  `fourierIntegral_pureTensor_eq F μ ν ψ g h w`. Nothing is restated at the pin's narrower form.
* `integrable_of_mem_schwartzBruhat` (`Space.lean:541`) is likewise the pin's row at the pin's
  arguments; its `[MeasurableSpace 𝔸]`/`[BorelSpace 𝔸]` binders are the module's own.
* The three helpers keep the pin's section-variable shape (`variable` + `include hψ` /
  `include hψ_inf` / `include hψ hψ_inf`) precisely so that their statements are the pin's text: the
  pin's signatures for them do not mention `F`, `μ`, `ψ` because those are section variables.
* `fourierIntegral_psiV_eq` is stated at the pin's `VectorFourier.fourierIntegral` spelling; the port
  carries mathlib's `VectorFourier` (`Analysis/Fourier/VectorIntegralFlip.lean`), so no adapter is
  needed.
* Two imports are added to the scaffold's list because the rows consume them and neither is on the
  scaffold's chain: `NumberTheory/AdelicFourier/FourierInversion` (the finite-place
  local-constancy/compact-support row, `:697`) and `Analysis/Fourier/VectorIntegralFlip`
  (`SchwartzMap.exists_coe_eq_vectorFourierIntegral`, `:324`).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace.lean>

spec-pin: Theorems/Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace.lean
-/
import FLTForHuman.NumberTheory.AdelicFourier
import FLTForHuman.NumberTheory.AdelicFourier.Transform
import FLTForHuman.NumberTheory.AdelicFourier.Space
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar.Circle
import FLTForHuman.NumberTheory.AdelicFourier.FourierInversion
import FLTForHuman.Analysis.Fourier.VectorIntegralFlip

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm
open IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

namespace NumberField.AdelicFourier

noncomputable section

section

variable (F : Type) [Field F] [NumberField F]
  [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
  {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)

include hψ in
/-- The integrand of the adèlic Fourier transform is dominated by `‖f‖`: `‖ψ‖ ≡ 1` on a global
additive character. -/
theorem integrable_fourierIntegrand {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    (w : AdeleRing (𝓞 F) F) :
    Integrable (fun v => ψ (-(v * w)) * f v) μ := by
  have hfi : Integrable f μ := integrable_of_mem_schwartzBruhat F μ hf
  refine Integrable.mono' hfi.norm ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact ((hψ.continuous.comp ((continuous_id.mul continuous_const).neg)).aestronglyMeasurable).mul
      hfi.aestronglyMeasurable
  · rw [norm_mul, norm_apply_eq_one_of_isGlobalAddChar F hψ, one_mul]

variable (hψ_inf : ∀ x : InfiniteAdeleRing F,
    ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))

include hψ_inf in
omit [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] in
/-- On a global character with the standard archimedean component, the archimedean factor of the
transform is mathlib's Fourier integral against the trace form. -/
theorem fourierIntegral_psiV_eq (g : mixedEmbedding.mixedSpace F → ℂ) (w : mixedEmbedding.mixedSpace F) :
    fourierIntegral
        (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
        volume g w
      = VectorFourier.fourierIntegral Real.fourierChar volume
          (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace F)) g w := by
  rw [fourierIntegral_def, VectorFourier.fourierIntegral]
  congr 1 with v
  have h1 : (ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom)) (-(v * w))
      = ψ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (-(v * w)), 0) := rfl
  rw [h1, hψ_inf, RingEquiv.apply_symm_apply, Circle.smul_def, smul_eq_mul, map_neg,
    Algebra.traceForm_apply]

include hψ hψ_inf in
/-- The Fourier transform preserves `schwartzBruhat F`: on a pure tensor it is the product of the
two local transforms, and the pure tensors span the space. -/
theorem fstab0_impl {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    fourierIntegral ψ μ f ∈ schwartzBruhat F := by
  refine schwartzBruhat_induction (F := F) (p := fun f _ => fourierIntegral ψ μ f ∈ schwartzBruhat F)
    ?_ ?_ ?_ ?_ hf
  ·
    intro f hf
    obtain ⟨g, h, hlc, hcs, rfl⟩ := hf

    let _ : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
    have _ : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
    let ν : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar
    set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with he
    set ψV : AddChar (mixedEmbedding.mixedSpace F) ℂ :=
      ψ.compAddMonoidHom ((AddMonoidHom.inl _ _).comp e.symm.toAddMonoidHom) with hψV
    set ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
      ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) with hψf
    set C : ℂ := ((μ (adelicBox F)).toReal /
      (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
        * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) : ℂ) with hC

    have hT : ∀ w, fourierIntegral ψ μ (fun x ↦ g (e x.1) * h x.2) w
        = C * fourierIntegral ψV volume g (e w.1) * fourierIntegral ψf ν h w.2 :=
      fun w => fourierIntegral_pureTensor_eq F μ ν ψ g h w

    have hV : fourierIntegral ψV volume g
        = VectorFourier.fourierIntegral Real.fourierChar volume
            (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace F)) g :=
      funext (fourierIntegral_psiV_eq F hψ_inf g)
    obtain ⟨g₁, hg₁⟩ := SchwartzMap.exists_coe_eq_vectorFourierIntegral
      (volume : Measure (mixedEmbedding.mixedSpace F))
      (Algebra.traceForm ℝ (mixedEmbedding.mixedSpace F))
      (mixedEmbedding.traceForm_mixedSpace_nondegenerate F) g

    obtain ⟨hlc', hcs'⟩ :=
      isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing F ν hψ hψ_inf hlc hcs

    refine mem_schwartzBruhat_of_mem_pureTensorSet ⟨C • g₁, fourierIntegral ψf ν h, hlc', hcs', ?_⟩
    funext w
    rw [hT w, smul_apply, smul_eq_mul, hg₁, ← hV]
  ·
    show fourierIntegral ψ μ 0 ∈ schwartzBruhat F
    rw [fourierIntegral_zero]; exact zero_mem_schwartzBruhat
  ·
    intro f g hf hg ihf ihg
    show fourierIntegral ψ μ (f + g) ∈ schwartzBruhat F
    have : fourierIntegral ψ μ (f + g) = fourierIntegral ψ μ f + fourierIntegral ψ μ g := by
      funext w
      exact fourierIntegral_add ψ μ w (integrable_fourierIntegrand F μ hψ hf w)
        (integrable_fourierIntegrand F μ hψ hg w)
    rw [this]; exact Submodule.add_mem _ ihf ihg
  ·
    intro c f _ ih
    show fourierIntegral ψ μ (c • f) ∈ schwartzBruhat F
    rw [fourierIntegral_smul]; exact Submodule.smul_mem _ c ih

end

theorem fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F) :
    fourierIntegral ψ μ f ∈ schwartzBruhat F :=
  fstab0_impl F μ hψ hψ_inf hf

end

end NumberField.AdelicFourier
