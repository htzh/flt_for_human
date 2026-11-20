/-
  The dihedral weight-one lift.

  `weightOneArchLift` is the archimedean weight-one slash factor, `HasWeightOneDecomp` the
  decomposition of a finite adèle of `GL₂(𝔸_ℚ)` into a rational, a finite-level and a compact
  part with the real component in `GLPos`, and `weightOneLift` the function obtained by lifting
  a weight-one form along such a decomposition. It is the dihedral counterpart of `DeltaLift`
  and the object the boundedness-on-Siegel-windows row is stated for.

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_DihedralWeightOneLift.lean`
  (pinned `aa2d8b3`, 30 lines / 3 declarations). The pin's stub imports are replaced by the
  port modules; the pin namespace `DihedralWeightOne` is kept.

  spec-pin: Definitions/Def_AutomorphicForm_DihedralWeightOneLift.lean
-/
import FLTForHuman.LanglandsTunnell.DeltaLift

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm
open scoped ModularForm MatrixGroups

namespace DihedralWeightOne

def weightOneArchLift (f : UpperHalfPlane → ℂ) (h : GL (Fin 2) ℝ) : ℂ :=
  (f ∣[(1 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (1 : ℤ)

def HasWeightOneDecomp (N : Ideal (𝓞 ℚ)) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Prop :=
  ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
    u ∈ (productionPinsCompact ℚ).U N ∧ AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
    LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ ∧
    g = AutomorphicForm.globalPoints (𝓞 ℚ) ℚ γ * h * u

open scoped Classical in

def weightOneLift (N : Ideal (𝓞 ℚ)) (f : UpperHalfPlane → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  if H : HasWeightOneDecomp N g then
    weightOneArchLift f (LanglandsTunnell.ratArchGL2 H.choose_spec.choose) else 0

end DihedralWeightOne

end
