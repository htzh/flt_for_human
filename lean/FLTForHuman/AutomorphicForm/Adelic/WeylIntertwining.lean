/-  The Weyl element and the Weyl intertwining integral.

  `gl2Weyl` is the transposition matrix in `GL₂(K)` and `adelicWeyl` its image in
  `GL₂(𝔸_K)`; `weylIntertwiningIntegral` is the integral of `φ (w⁻¹ n(x) g)` against a
  measure on `𝔸_K`. This is the operator the Bruhat/Eisenstein layer studies.

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_WeylIntertwining.lean`
  (pinned `aa2d8b3`), the pin namespace `AutomorphicForm` kept.-/
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory

namespace AutomorphicForm

section WeylElement

variable {K : Type*} [Field K]

-- pin: gl2Weyl (Def_AutomorphicForm_WeylIntertwining.lean:14)
def gl2Weyl : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

-- pin: gl2Weyl_val (Def_AutomorphicForm_WeylIntertwining.lean:23)
@[simp] theorem gl2Weyl_val :
    ((gl2Weyl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

-- pin: gl2Weyl_inv (Def_AutomorphicForm_WeylIntertwining.lean:26)
theorem gl2Weyl_inv : (gl2Weyl : GL (Fin 2) K)⁻¹ = gl2Weyl := Units.ext rfl

end WeylElement

section Intertwining

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [MeasurableSpace (NumberField.AdeleRing R K)]

-- pin: adelicWeyl (Def_AutomorphicForm_WeylIntertwining.lean:35)
def adelicWeyl : AdelicGL2 R K :=
  globalPoints R K gl2Weyl

-- pin: weylIntertwiningIntegral (Def_AutomorphicForm_WeylIntertwining.lean:38)
def weylIntertwiningIntegral (ν : Measure (NumberField.AdeleRing R K))
    (f : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) : ℂ :=
  ∫ x, f ((adelicWeyl R K)⁻¹ * unipotentGL2 x * g) ∂ν

-- pin: weylIntertwiningIntegral_const (Def_AutomorphicForm_WeylIntertwining.lean:42)
theorem weylIntertwiningIntegral_const (ν : Measure (NumberField.AdeleRing R K))
    [IsProbabilityMeasure ν] (c : ℂ) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K ν (fun _ => c) g = c := by
  unfold weylIntertwiningIntegral
  simp [integral_const, measureReal_def]

-- pin: weylIntertwiningIntegral_zero_measure (Def_AutomorphicForm_WeylIntertwining.lean:48)
theorem weylIntertwiningIntegral_zero_measure (f : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K 0 f g = 0 := by
  unfold weylIntertwiningIntegral
  simp

end Intertwining

end AutomorphicForm
