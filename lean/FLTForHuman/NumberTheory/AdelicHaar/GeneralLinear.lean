/-
  `GL_n(𝔸_K)`: the Borel structure and Haar measure.

  The matrix ring `M_n(𝔸_K)` and its unit group `GL_n(𝔸_K)` inherit the product
  topology (Hausdorff, locally compact); `glBorel` is their Borel σ-algebra and
  `adelicGLHaar` the (unimodular) Haar measure. This is the measure the right
  convolution `rightConv` integrates against and the group the level subgroups
  `levelOne`/`levelZero` sit in.

  Transcribed verbatim from `Definitions/Def_NumberField_AdelicHaar.lean:159–201`
  (the pin's `GeneralLinear` section, pinned `aa2d8b3`), the third of the pin
  node's three role modules. It carries the port's former `Topology.lean`
  instance `t2Space_matrix_adeleRing`.
-/
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import Mathlib.Topology.Algebra.Group.Units

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are load-bearing: they feed instance search in the `exact`s.
set_option linter.style.haveILetI false

open IsDedekindDomain NumberField MeasureTheory
open scoped RestrictedProduct Topology

noncomputable section

namespace NumberField.AdelicHaar

section GeneralLinear

variable (n : Type*) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

instance t2Space_matrix_adeleRing : T2Space (Matrix n n (AdeleRing R K)) :=
  inferInstanceAs (T2Space (n → n → AdeleRing R K))

instance locallyCompactSpace_matrix_adeleRing [Finite n] [Module.Free ℤ R] [Module.Finite ℤ R]
    [NumberField K] : LocallyCompactSpace (Matrix n n (AdeleRing R K)) :=
  inferInstanceAs (LocallyCompactSpace (n → n → AdeleRing R K))

variable [Fintype n] [DecidableEq n]

instance t2Space_gl_adeleRing : T2Space (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  inferInstance

@[reducible] def glBorel : MeasurableSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  borel _

theorem borelSpace_glBorel :
    @BorelSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) _ (glBorel n R K) :=
  @BorelSpace.mk _ _ (glBorel n R K) rfl

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]

instance locallyCompactSpace_gl_adeleRing :
    LocallyCompactSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  inferInstance

def adelicGLHaar : @Measure (Matrix.GeneralLinearGroup n (AdeleRing R K)) (glBorel n R K) := by
  letI := glBorel n R K
  haveI := borelSpace_glBorel n R K
  exact Measure.haar

theorem isHaarMeasure_adelicGLHaar :
    @Measure.IsHaarMeasure (Matrix.GeneralLinearGroup n (AdeleRing R K)) _ _ (glBorel n R K)
      (adelicGLHaar n R K) := by
  letI := glBorel n R K
  haveI := borelSpace_glBorel n R K
  exact Measure.isHaarMeasure_haarMeasure _

end GeneralLinear

end NumberField.AdelicHaar

end
