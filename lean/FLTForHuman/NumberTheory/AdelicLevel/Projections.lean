/-
  The adelic projections onto the infinite and finite components.

  The adele ring is a product `𝔸_K = K_∞ × 𝔸_K^fin` (`AdeleRing R K` is a
  reducible product type), and this module carries the local evaluations
  `archEval`/`finAdeleEval` and the two ring projections `adeleArch`, `adeleFin`
  together with the induced maps `glArch : GL₂(𝔸_K) →* GL₂(K_∞)` and
  `glFin : GL₂(𝔸_K) →* GL₂(𝔸_K^fin)` and their continuity. They are the
  vocabulary in which a factorisable test function on `GL₂(𝔸_K)` is split into an
  archimedean and a finite factor (`AutomorphicForm.IsFactorizableTestFn`) and in
  which the adèlic level subgroups are cut out (`AdelicLevel.levelZero`/`levelOne`).

  Transcribed verbatim from `Definitions/Def_NumberField_AdelicLevel.lean:135–223`
  (the pin's `Projections` section, pinned `aa2d8b3`), one of the four role modules
  the pin node is split into (playbook §3.1). `continuous_glMap` is the pin's
  `private` generic helper; the pin also states it **publicly** at
  `Definitions/Def_AutomorphicForm_BaseChangePlaces.lean:317`, and every later
  adelíc projection/embedding needs it, so the port promotes it here at the pin's
  name (`topics/PORTING-AutomorphicForm.md` §4.1).
-/
import Mathlib.NumberTheory.NumberField.AdeleRing

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped RestrictedProduct Topology

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

section Projections

def archEval (w : InfinitePlace K) : InfiniteAdeleRing K →+* w.Completion where
  toFun a := a w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def finAdeleEval (v : HeightOneSpectrum R) : FiniteAdeleRing R K →+* v.adicCompletion K where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def adeleArch : AdeleRing R K →+* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def adeleFin : AdeleRing R K →+* FiniteAdeleRing R K where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem archEval_apply (w : InfinitePlace K) (a : InfiniteAdeleRing K) : archEval K w a = a w := rfl
theorem finAdeleEval_apply (v : HeightOneSpectrum R) (a : FiniteAdeleRing R K) :
    finAdeleEval R K v a = a v := rfl
theorem adeleArch_apply (a : AdeleRing R K) : adeleArch R K a = a.1 := rfl
theorem adeleFin_apply (a : AdeleRing R K) : adeleFin R K a = a.2 := rfl

theorem continuous_archEval (w : InfinitePlace K) : Continuous (archEval K w) :=
  (continuous_apply w : Continuous fun a : (∀ w : InfinitePlace K, w.Completion) => a w)

theorem continuous_finAdeleEval (v : HeightOneSpectrum R) : Continuous (finAdeleEval R K v) :=
  (RestrictedProduct.continuous_eval v :
    Continuous fun x : Πʳ w : HeightOneSpectrum R, [w.adicCompletion K, w.adicCompletionIntegers K] => x v)

theorem continuous_adeleArch : Continuous (adeleArch R K) :=
  (continuous_fst : Continuous fun x : AdeleRing R K => x.1)

theorem continuous_adeleFin : Continuous (adeleFin R K) :=
  (continuous_snd : Continuous fun x : AdeleRing R K => x.2)

def archComponent (w : InfinitePlace K) : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) w.Completion :=
  Matrix.GeneralLinearGroup.map (archEval K w)

def finComponent (v : HeightOneSpectrum R) :
    GL (Fin 2) (FiniteAdeleRing R K) →* GL (Fin 2) (v.adicCompletion K) :=
  Matrix.GeneralLinearGroup.map (finAdeleEval R K v)

def glArch : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (adeleArch R K)

def glFin : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (FiniteAdeleRing R K) :=
  Matrix.GeneralLinearGroup.map (adeleFin R K)

theorem archComponent_apply (w : InfinitePlace K) (g : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    (archComponent K w g : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j w := rfl
theorem finComponent_apply (v : HeightOneSpectrum R) (g : GL (Fin 2) (FiniteAdeleRing R K))
    (i j : Fin 2) : (finComponent R K v g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      = (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j v := rfl
theorem glArch_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    (glArch R K g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).1 := rfl
theorem glFin_apply (g : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    (glFin R K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 := rfl

/-- Continuity of the induced map `GL (Fin 2) A →* GL (Fin 2) B` from a continuous
ring homomorphism. Promoted from the pin's `private` copy
(`Def_NumberField_AdelicLevel.lean:210`); the pin states it publicly at
`Def_AutomorphicForm_BaseChangePlaces.lean:317`. -/
theorem continuous_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

theorem continuous_archComponent (w : InfinitePlace K) : Continuous (archComponent K w) :=
  continuous_glMap _ (continuous_archEval K w)
theorem continuous_finComponent (v : HeightOneSpectrum R) : Continuous (finComponent R K v) :=
  continuous_glMap _ (continuous_finAdeleEval R K v)
theorem continuous_glArch : Continuous (glArch R K) := continuous_glMap _ (continuous_adeleArch R K)
theorem continuous_glFin : Continuous (glFin R K) := continuous_glMap _ (continuous_adeleFin R K)

end Projections

end NumberField.AdelicLevel

end
