/-
  SET-AF89C consumer: a cuspidal constituent's vectors are real-`GL₂⁺`-invariant after monotonicity.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/Cusp/ConstituentRightConv.lean` carries both
  halves of the same argument: `isCuspConstituent_productionPinsOf_mono` (a cuspidal constituent for
  the compact set `D` is one for `D' ⊆ D`) and
  `forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` (one nonzero vector of a
  constituent invariant under the real unipotent subgroup with determinant one forces *every*
  vector to be invariant).

  **The reading.** The monotonicity row is applied first, so the archimedean-invariance row is read
  at the larger compact set `D'` — the direction a consumer that starts from a pin at `D` and
  finishes at the smaller `D'` needs. The two rows are the same story and compose without any
  other hypothesis than the pair the pin's own proof uses.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF89CConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ConstituentRightConv

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain Matrix
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators Manifold

namespace AutomorphicFormSetAF89CConsumer

/-- **The reading.** Monotonicity of the cuspidal constituent in the compact set `D`, followed by
the real-archimedean invariance row at the smaller set: a single invariant nonzero vector forces
invariance of the whole constituent. -/
theorem forall_apply_mul_archRealGLAt_eq_of_productionPinsOf_mono
    (F : Type) [Field F] [NumberField F]
    (D D' : Set (AdelicGL2 (𝓞 F) F)) (hD : D' ⊆ D) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ V)
    (w : InfinitePlace F) (hw : w.IsReal)
    (x₀ : AdelicGL2 (𝓞 F) F → ℂ) (hx₀ : x₀ ∈ V) (hne : x₀ ≠ 0)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      x₀ (g * archRealGLAt hw h) = x₀ g)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ V)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    x (g * archRealGLAt hw h) = x g := by
  have hV' : IsCuspConstituent F
      (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ V :=
    isCuspConstituent_productionPinsOf_mono F D D' hD B ξ V hV
  exact forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists F
    (productionPinsOf F D' (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) B) ξ V hV' w hw x₀ hx₀ hne hinv x hx g h hh

end AutomorphicFormSetAF89CConsumer
