/-
  The adele ring is Hausdorff.

  At the pin's mathlib this did not follow from the product structure by
  instance search, so FLT wrote the instances out; the current mathlib still
  lacks them, and the compact-support argument for factorisable test functions
  needs `T1Space` on `Matrix 2 2 (𝔸_K)` (hence on `𝔸_K` itself) to apply the
  closed-embedding property of `Units.embedProduct`.

  Transcribed from `Definitions/Def_NumberField_AdelicHaar.lean:118–201` (the
  pin's `Adele` and `GeneralLinear` sections, pinned `aa2d8b3`), carrying only
  the four `T2Space` instances on the path. The pin's Haar-measure and
  local-compactness instances from the same sections are not reached by this
  port and stay unported.
-/
import Mathlib.NumberTheory.NumberField.AdeleRing

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped RestrictedProduct Topology

namespace NumberField.AdelicHaar

section Adele

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

instance t2Space_infiniteAdeleRing : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))

instance t2Space_adeleRing : T2Space (AdeleRing R K) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing R K))

end Adele

section GeneralLinear

variable (n : Type*) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Fintype n] [DecidableEq n]

instance t2Space_matrix_adeleRing : T2Space (Matrix n n (AdeleRing R K)) :=
  inferInstanceAs (T2Space (n → n → AdeleRing R K))

end GeneralLinear

end NumberField.AdelicHaar

end
