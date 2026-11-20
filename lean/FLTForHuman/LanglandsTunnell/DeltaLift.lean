/-
  The delta lift: the weight-one lift attached to a cusp form's discriminant.

  `deltaArchLift` is the archimedean factor of the lift of the discriminant `Δ`, `ratArchGL2`
  the real component of an idele-class representative, `HasDeltaDecomp` the decomposition of a
  finite adèle of `GL₂(𝔸_ℚ)` into a rational, a finite-level and a compact part, and `deltaLift`
  the resulting adelic function. `deltaRawTable`/`deltaLiftSystem` are its Hecke eigensystem.

  Transcribed verbatim from `Definitions/Def_LanglandsTunnell_DeltaLift.lean` (pinned `aa2d8b3`,
  46 lines / 6 declarations). The pin's stub imports are replaced by the port modules; the pin
  namespace `LanglandsTunnell` is kept.

  spec-pin: Definitions/Def_LanglandsTunnell_DeltaLift.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsCompact
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ArithRealization
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm AutomorphicForm.HeckeEigensystem
open scoped ModularForm MatrixGroups

namespace LanglandsTunnell

def deltaArchLift (h : GL (Fin 2) ℝ) : ℂ :=
  ((⇑CuspForm.discriminant) ∣[(12 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (-5 : ℤ)

def ratArchGL2 (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
    (AdelicLevel.archComponent ℚ default (AdelicLevel.glArch (𝓞 ℚ) ℚ g))

def HasDeltaDecomp (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Prop :=
  ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
    u ∈ (productionPinsCompact ℚ).U ⊤ ∧ AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
    ratArchGL2 h ∈ GLPos (Fin 2) ℝ ∧ g = globalPoints (𝓞 ℚ) ℚ γ * h * u

open scoped Classical in

def deltaLift (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  if H : HasDeltaDecomp g then deltaArchLift (ratArchGL2 H.choose_spec.choose) else 0

def deltaRawTable : HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := top_ne_bot
  a := fun v => (UpperHalfPlane.qExpansion 1 (⇑CuspForm.discriminant)).coeff
      (Ideal.absNorm v.asIdeal) * (cNorm v) ^ (-5 : ℤ)
  b := fun _ => 1

def deltaLiftSystem : HeckeEigensystem ℚ ℂ := ofRawCentral deltaRawTable

@[simp] theorem deltaLiftSystem_level : deltaLiftSystem.level = ⊤ := rfl

@[simp] theorem deltaLiftSystem_toRawCentral : deltaLiftSystem.toRawCentral = deltaRawTable :=
  HeckeEigensystem.toRawCentral_ofRawCentral deltaRawTable

end LanglandsTunnell

end
