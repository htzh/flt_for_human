/-
  The adelic projections onto the infinite and finite components.

  The adele ring is a product `𝔸_K = K_∞ × 𝔸_K^fin` (`AdeleRing R K` is a
  reducible product type), and this module carries the two ring projections
  `adeleArch`, `adeleFin` together with the induced maps
  `glArch : GL₂(𝔸_K) →* GL₂(K_∞)` and `glFin : GL₂(𝔸_K) →* GL₂(𝔸_K^fin)`, and
  their continuity. They are the vocabulary in which a factorisable test
  function on `GL₂(𝔸_K)` is split into an archimedean and a finite factor
  (`AutomorphicForm.IsFactorizableTestFn`).

  Transcribed from `Definitions/Def_NumberField_AdelicLevel.lean:137–221` (the
  pin's `Projections` section, pinned `aa2d8b3`). Only the projection slice the
  port reaches is carried: the pin's level subgroups, `idealBall`/Haar layers
  and component/evaluation projections live in other sections of that file and
  are not imported here. `continuous_glMap` is the pin's `private` generic
  helper, kept `private` for the same reason.

  The pin's imports of `Def_NumberField_AdelicHaar` are dropped along with the
  Haar sections; the projections need only the adele ring itself.
-/
import Mathlib.NumberTheory.NumberField.AdeleRing

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped Topology

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The projection `𝔸_K →+* K_∞` onto the infinite adeles. -/
def adeleArch : AdeleRing R K →+* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The projection `𝔸_K →+* 𝔸_K^fin` onto the finite adeles. -/
def adeleFin : AdeleRing R K →+* FiniteAdeleRing R K where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem adeleArch_apply (a : AdeleRing R K) : adeleArch R K a = a.1 := rfl
theorem adeleFin_apply (a : AdeleRing R K) : adeleFin R K a = a.2 := rfl

theorem continuous_adeleArch : Continuous (adeleArch R K) :=
  (continuous_fst : Continuous fun x : AdeleRing R K => x.1)

theorem continuous_adeleFin : Continuous (adeleFin R K) :=
  (continuous_snd : Continuous fun x : AdeleRing R K => x.2)

/-- The archimedean component `GL₂(𝔸_K) →* GL₂(K_∞)`. -/
def glArch : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (adeleArch R K)

/-- The finite component `GL₂(𝔸_K) →* GL₂(𝔸_K^fin)`. -/
def glFin : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.GeneralLinearGroup.map (adeleFin R K)

theorem glArch_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    (glArch R K g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).1 := rfl
theorem glFin_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    (glFin R K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 := rfl

private theorem continuous_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

theorem continuous_glArch : Continuous (glArch R K) := continuous_glMap _ (continuous_adeleArch R K)
theorem continuous_glFin : Continuous (glFin R K) := continuous_glMap _ (continuous_adeleFin R K)

end NumberField.AdelicLevel

end
