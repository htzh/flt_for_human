/-
  Cross-module wire test for the factorisable-test-function port.

  A `spec/` probe, not a library module. Three executed zones: the adele-ring
  topology instances and level projections, the factorisable-test-function
  definitions, and the headline applied to a concrete (zero) test function —
  the composition that fails if any of the four modules is dropped.
-/
import FLTForHuman.AutomorphicForm.TestFnTop

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace AutomorphicFormConsumer

-- Zone 1: the adele ring is Hausdorff and the level projections are continuous.
#check @NumberField.AdelicHaar.t2Space_adeleRing
#check @NumberField.AdelicLevel.glArch
#check @NumberField.AdelicLevel.glFin
#check @NumberField.AdelicLevel.continuous_glArch
#check @NumberField.AdelicLevel.continuous_glFin

example (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) :
    NumberField.AdelicLevel.adeleArch (𝓞 F) F a = a.1 := rfl

example (F : Type) [Field F] [NumberField F] (g : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (i j : Fin 2) :
    (NumberField.AdelicLevel.glArch (𝓞 F) F g :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 := rfl

-- Zone 2: the definitions and their non-vacuity witness.
#check @AutomorphicForm.archEntries
#check @AutomorphicForm.IsArchTestFactor
#check @AutomorphicForm.IsFinTestFactor
#check @AutomorphicForm.IsFactorizableTestFn

example (F : Type) [Field F] [NumberField F] :
    AutomorphicForm.IsFactorizableTestFn F
      (fun _ : GL (Fin 2) (AdeleRing (𝓞 F) F) => (0 : ℂ)) :=
  AutomorphicForm.isFactorizableTestFn_zero F

-- Zone 3: the headline, applied to that witness.
example (F : Type) [Field F] [NumberField F] :
    Continuous (fun _ : GL (Fin 2) (AdeleRing (𝓞 F) F) => (0 : ℂ)) ∧
      HasCompactSupport (fun _ : GL (Fin 2) (AdeleRing (𝓞 F) F) => (0 : ℂ)) :=
  AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F _
    (AutomorphicForm.isFactorizableTestFn_zero F)

end AutomorphicFormConsumer

end
