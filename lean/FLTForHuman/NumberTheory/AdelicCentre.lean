/-
  The adèlic centre and the projective quotient.

  The centre of `GL₂(𝔸_K)` is the image of the scalar matrices
  (`center_eq_range_scalar`, `scalar_injective`), and

  `AdelicPGL2 R K = GL₂(𝔸_K) ⧸ center`

  is the projective linear group of the adèle ring. Its Borel σ-algebra `pglBorel`
  and Haar measure `adelicPGLHaar` are the measure theory the automorphic carriers
  integrate over: an open nonempty set has positive image under the quotient map
  (`…_image_pos`), and a set contained in a compact `C` times the centre has
  finite image (`…_lt_top_of_subset`). This is the PGL₂ vocabulary the cusp and
  Siegel carriers and `NumberField.AdelicVolume` are stated over.

  Transcribed whole from `Definitions/Def_NumberField_AdelicCentre.lean` (pinned
  `aa2d8b3`; lines 11–53 the general quotient, 55–103 the `NumberField` case),
  the pin's one role module for the centre and the projective quotient
  (playbook §2.3). It is self-contained: the only port import is the landed
  `NumberTheory/AdelicHaar/GeneralLinear.lean` (the `GL₂(𝔸_K)` topology and Haar
  measure); `Matrix.GeneralLinearGroup.{scalar,center_eq_range_scalar}` are
  mathlib `v4.34.0`, so no promotion is needed.
-/
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are load-bearing: they feed instance search in the `exact`s.
set_option linter.style.haveILetI false

open IsDedekindDomain NumberField MeasureTheory
open scoped Pointwise

noncomputable section

namespace NumberField.AdelicCentre

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem center_eq_range_scalar :
    Subgroup.center (GL (Fin 2) (AdeleRing R K))
      = (Matrix.GeneralLinearGroup.scalar (Fin 2) : (AdeleRing R K)ˣ →* _).range :=
  Matrix.GeneralLinearGroup.center_eq_range_scalar

theorem scalar_injective :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin 2) : (AdeleRing R K)ˣ →* _) :=
  fun a b h => by
    have := congrArg (fun g : GL (Fin 2) (AdeleRing R K) => (g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0) h
    exact Units.ext (by simpa using this)

abbrev AdelicPGL2 : Type _ :=
  GL (Fin 2) (AdeleRing R K) ⧸ Subgroup.center (GL (Fin 2) (AdeleRing R K))

theorem measure_image_mk_pos {m : MeasurableSpace (AdelicPGL2 R K)} (μ : Measure (AdelicPGL2 R K))
    [μ.IsOpenPosMeasure] {D : Set (GL (Fin 2) (AdeleRing R K))}
    (h : ∃ U : Set (GL (Fin 2) (AdeleRing R K)), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    0 < μ ((QuotientGroup.mk : GL (Fin 2) (AdeleRing R K) → AdelicPGL2 R K) '' D) := by
  obtain ⟨U, hU, hne, hsub⟩ := h
  exact ((QuotientGroup.isOpenMap_coe U hU).measure_pos μ (hne.image _)).trans_le
    (measure_mono (Set.image_mono hsub))

theorem measure_image_mk_lt_top {m : MeasurableSpace (AdelicPGL2 R K)} (μ : Measure (AdelicPGL2 R K))
    [IsFiniteMeasureOnCompacts μ] {C : Set (GL (Fin 2) (AdeleRing R K))} (hC : IsCompact C) :
    μ ((QuotientGroup.mk : GL (Fin 2) (AdeleRing R K) → AdelicPGL2 R K) '' C) < ⊤ :=
  (hC.image QuotientGroup.continuous_mk).measure_lt_top

theorem image_mk_subset_of_subset_mul_center {D C : Set (GL (Fin 2) (AdeleRing R K))}
    (h : D ⊆ C * ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))) :
    (QuotientGroup.mk : _ → AdelicPGL2 R K) '' D ⊆ (QuotientGroup.mk : _ → AdelicPGL2 R K) '' C := by
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨c, hc, z, hz, rfl⟩ := h hd
  refine ⟨c, hc, ?_⟩
  rw [QuotientGroup.eq]
  simpa using hz

@[reducible] def pglBorel : MeasurableSpace (AdelicPGL2 R K) := borel _

theorem borelSpace_pglBorel : @BorelSpace (AdelicPGL2 R K) _ (pglBorel R K) :=
  @BorelSpace.mk _ _ (pglBorel R K) rfl

section NumberFieldCase

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]

instance isClosed_center :
    IsClosed ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K)))) := by
  have : ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))
      = ⋂ g : GL (Fin 2) (AdeleRing R K), {z | g * z = z * g} := by
    ext z
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun g =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

instance t2Space_adelicPGL2 : T2Space (AdelicPGL2 R K) := inferInstance

instance locallyCompactSpace_adelicPGL2 : LocallyCompactSpace (AdelicPGL2 R K) := inferInstance

instance isTopologicalGroup_adelicPGL2 : IsTopologicalGroup (AdelicPGL2 R K) := inferInstance

def adelicPGLHaar : @Measure (AdelicPGL2 R K) (pglBorel R K) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  exact Measure.haar

theorem isHaarMeasure_adelicPGLHaar :
    @Measure.IsHaarMeasure (AdelicPGL2 R K) _ _ (pglBorel R K) (adelicPGLHaar R K) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  exact Measure.isHaarMeasure_haarMeasure _

theorem adelicPGLHaar_image_pos {D : Set (GL (Fin 2) (AdeleRing R K))}
    (h : ∃ U : Set (GL (Fin 2) (AdeleRing R K)), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    0 < adelicPGLHaar R K ((QuotientGroup.mk : _ → AdelicPGL2 R K) '' D) := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  haveI := isHaarMeasure_adelicPGLHaar R K
  exact measure_image_mk_pos R K _ h

theorem adelicPGLHaar_image_lt_top_of_subset {D C : Set (GL (Fin 2) (AdeleRing R K))} (hC : IsCompact C)
    (h : D ⊆ C * ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))) :
    adelicPGLHaar R K ((QuotientGroup.mk : _ → AdelicPGL2 R K) '' D) < ⊤ := by
  letI := pglBorel R K
  haveI := borelSpace_pglBorel R K
  haveI := isHaarMeasure_adelicPGLHaar R K
  exact lt_of_le_of_lt (measure_mono (image_mk_subset_of_subset_mul_center R K h))
    (measure_image_mk_lt_top R K _ hC)

end NumberFieldCase

end NumberField.AdelicCentre

end
