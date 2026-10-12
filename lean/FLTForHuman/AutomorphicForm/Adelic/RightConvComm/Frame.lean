/-
  The adèlic frame: the `ProjectedHaar` instantiation for `GL₂(𝔸_F)`.

  `SecondCountableAdelic` supplies the second-countability/countability instances the
  projected-Haar engine needs on the adèlic group; `ProjectedHaar.adelicFrame` is the
  frame `GL₂(𝔸_F) → GL₂(𝔸_F^∞) × GL₂(𝔸_F^fin)` with the archimedean and finite
  embeddings as sections, separated by `AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq`
  (`eq_of_glArch_eq_of_glFin_eq`). `MeasureGlue` collects the level-`N` side facts of
  that frame: the `rfl` projection `pins_U`, the image of the level subgroup under
  `glFin`, and its compactness/openness, together with the two kernel spellings
  `rc`/`rightConv_eq_rc` and the Borel/Haar facts `haar_facts`.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean:786–1011`
  (and the compact silo's `U`-spelled `MeasureGlue` block,
  `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact.lean:946–982`),
  pinned `aa2d8b3`. The declarations are `private` at the pin and land here public as
  the shared engine; the `scoped` instances keep the pin's `p2m_reactivate` visibility
  through `open scoped SecondCountableAdelic` (see `MeasureAssembly.lean`).

  `glArch_eq_one_of_mem` and `isOpen_glFin_preimage_image_level` carry two bodies at the
  pin (a level-`N` spelling and a general-`U` spelling, one per silo). The engine's
  general-`U` spelling is landed here; the level-`N` specializations this file does not
  need are not written, and the level-`N`-only names (`pins_U`, `glFin_image_level`,
  `isCompact_glFin_image_level`) keep their plain-silo bodies (work order §1).
-/
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.RepTheory.ProjectedHaar
import FLTForHuman.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Tactic

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar

open scoped RestrictedProduct

noncomputable section

namespace SecondCountableAdelic

section Primes

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

noncomputable def generators (I : Ideal R) : Finset R :=
  ((isNoetherianRing_iff_ideal_fg R).mp ‹IsNoetherianRing R› I).choose

theorem span_generators (I : Ideal R) : Ideal.span (generators I : Set R) = I :=
  ((isNoetherianRing_iff_ideal_fg R).mp ‹IsNoetherianRing R› I).choose_spec

theorem generators_injective : Function.Injective (generators (R := R)) := fun I J h => by
  rw [← span_generators I, ← span_generators J, h]

private scoped instance countable_ideal [Countable R] : Countable (Ideal R) :=
  generators_injective.countable

end Primes

section Spectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Countable R]

private scoped instance countable_heightOneSpectrum : Countable (HeightOneSpectrum R) :=
  Function.Injective.countable (f := HeightOneSpectrum.asIdeal (R := R)) fun _ _ h => HeightOneSpectrum.ext h

end Spectrum

theorem secondCountable_units {M : Type*} [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ :=
  haveI : SecondCountableTopology Mᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

section NumberField

variable (F : Type*) [Field F] [NumberField F]

private scoped instance countable_ringOfIntegers : Countable (𝓞 F) := Finsupp.Countable.of_moduleFinite (R := ℤ)

private scoped instance countable_numberField : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)

private scoped instance secondCountable_completion (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

private scoped instance secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

private scoped instance secondCountable_finiteAdeleRing : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) :=
  (RestrictedProduct.secondCountableTopology
      (fun v : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring (v.adicCompletion F)) :
    SecondCountableTopology (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

private scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

private scoped instance secondCountable_matrix_adeleRing :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 F) F))

private scoped instance secondCountable_gl_adeleRing :
    SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) (AdeleRing (𝓞 F) F)) :=
  secondCountable_units

private scoped instance secondCountable_matrix_infiniteAdeleRing :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing F))

private scoped instance secondCountable_gl_infiniteAdeleRing :
    SecondCountableTopology (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F)) :=
  secondCountable_units

private scoped instance t2_matrix_infiniteAdeleRing : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))

private scoped instance locallyCompact_matrix_infiniteAdeleRing :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))

private scoped instance locallyCompact_gl_infiniteAdeleRing :
    LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstance

end NumberField

end SecondCountableAdelic

section

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

noncomputable section

namespace ProjectedHaar

section Adelic

variable (F : Type) [Field F] [NumberField F]

theorem eq_of_glArch_eq_of_glFin_eq {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : AdelicLevel.glArch (𝓞 F) F x = AdelicLevel.glArch (𝓞 F) F y)
    (h₂ : AdelicLevel.glFin (𝓞 F) F x = AdelicLevel.glFin (𝓞 F) F y) : x = y := by
  apply Units.ext
  apply AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F
  · exact congrArg Units.val h₁
  · exact congrArg Units.val h₂

def adelicFrame :
    Frame (AdelicGL2 (𝓞 F) F) (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing F))
      (Matrix.GeneralLinearGroup (Fin 2) (FiniteAdeleRing (𝓞 F) F)) where
  π := AdelicLevel.glArch (𝓞 F) F
  πf := AdelicLevel.glFin (𝓞 F) F
  ι := adelicArchGLIncl F
  ιf := AdelicDock.finEmbed (𝓞 F) F
  π_ι := glArch_adelicArchGLIncl F
  πf_ι := glFin_adelicArchGLIncl F
  π_ιf := AdelicDock.glArch_finEmbed (𝓞 F) F
  πf_ιf := AdelicDock.glFin_finEmbed (𝓞 F) F
  sep := fun _ _ h₁ h₂ => eq_of_glArch_eq_of_glFin_eq F h₁ h₂

theorem continuous_adelicFrame_π : Continuous (adelicFrame F).π := AdelicLevel.continuous_glArch (𝓞 F) F

theorem continuous_adelicFrame_πf : Continuous (adelicFrame F).πf := AdelicLevel.continuous_glFin (𝓞 F) F

theorem continuous_finMat : Continuous (AdelicDock.finMat (𝓞 F) F) :=
  continuous_matrix fun i j => continuous_const.prodMk (continuous_id.matrix_elem i j)

theorem continuous_adelicFrame_ιf : Continuous (adelicFrame F).ιf := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact (continuous_finMat F).comp Units.continuous_val
  · exact (continuous_finMat F).comp (Units.continuous_val.comp continuous_inv)

/-- The finite adèlic embedding is continuous. The compact silo proves this inline in
its `solution` (there is no pin declaration for it to promote against), so it lands
here `private`; the public `continuous_adelicFrame_ιf` is definitionally the same
statement and is what the specializations use. -/
private theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 F) F) := by
  refine Units.continuous_iff.mpr ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · show Continuous fun g : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      AdelicDock.finMat (𝓞 F) F g i j
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · show Continuous fun g : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      AdelicDock.finMat (𝓞 F) F ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2)
        (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _) i j
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

theorem continuous_archMat :
    Continuous fun M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) =>
      (Matrix.of fun i j => ((M i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :
        AdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
  continuous_matrix fun i j => (continuous_id.matrix_elem i j).prodMk continuous_const

theorem continuous_adelicFrame_ι : Continuous (adelicFrame F).ι := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact (continuous_archMat F).comp Units.continuous_val
  · exact (continuous_archMat F).comp (Units.continuous_val.comp continuous_inv)

end Adelic

end ProjectedHaar

end

end

section

set_option autoImplicit false

open NumberField NumberField.AdelicHaar MeasureTheory AutomorphicForm

noncomputable section

namespace MeasureGlue

variable (F : Type) [Field F] [NumberField F]

variable (U : Subgroup (AdelicGL2 (𝓞 F) F))

theorem glArch_eq_one_of_mem (hUK : U ≤ finiteAdelicGL2Subgroup F) {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ U) : AdelicLevel.glArch (𝓞 F) F u = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff F u).mp (hUK hu)

theorem isOpen_glFin_preimage_image_level (hUo : IsOpen (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)))) :
    IsOpen (AdelicLevel.glFin (𝓞 F) F ⁻¹' (AdelicLevel.glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F)))) :=
  hUo.preimage (AdelicLevel.continuous_glFin (𝓞 F) F)

theorem pins_U (D : Set (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) (N : Ideal (𝓞 F)) :
    (productionPinsOf F D (fun N => AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) gen B).U N
      = AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl

variable (N : Ideal (𝓞 F))

theorem glFin_image_level :
    AdelicLevel.glFin (𝓞 F) F '' ((AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :
        Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))
      = (AdelicLevel.finiteLevelOne (𝓞 F) F N : Set (Matrix.GeneralLinearGroup (Fin 2)
          (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) := by
  ext b
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact AdelicLevel.mem_levelOne_iff.mp (Subgroup.mem_inf.mp hu).1
  · intro hb
    refine ⟨AdelicDock.finEmbed (𝓞 F) F b, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, AdelicDock.glFin_finEmbed (𝓞 F) F b⟩
    · exact (AdelicDock.finEmbed_mem_levelOne_iff (𝓞 F) F b).mpr hb
    · exact (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F b)

theorem isCompact_glFin_image_level :
    IsCompact (AdelicLevel.glFin (𝓞 F) F '' ((AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :
        Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) := by
  rw [glFin_image_level]
  exact AdelicLevel.isCompact_finiteLevelOne (𝓞 F) F N

def rc (φ f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  letI := glBorel (Fin 2) (𝓞 F) F
  ∫ x, φ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 F) F)

theorem rightConv_eq_rc (φ f : AdelicGL2 (𝓞 F) F → ℂ) : rightConv F φ f = rc F φ f := rfl

theorem haar_facts :
    letI := glBorel (Fin 2) (𝓞 F) F
    BorelSpace (AdelicGL2 (𝓞 F) F) ∧ (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
  ⟨borelSpace_glBorel (Fin 2) (𝓞 F) F, isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F⟩

end MeasureGlue

end

end

end
