/-
  The constant term is invariant under the rational unipotent flow.

  `constantTerm` along `unipotentGL2` at the `adelicBox`-conditioned additive Haar measure is
  unchanged when the base point is moved by `n(x0)`, `x0` any adele.  The proof is the box average:
  the additive Haar measure is translation invariant, the rational unipotents act trivially on
  `phi` by hypothesis, and the principal subgroup of the adeles is countable, so the box average of
  `phi` at `n(x0) * g` is the box average at `g`.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul.lean` (144 lines): five public
  prelude rows (`countable_principalSubgroup`, `setIntegral_adelicBox_comp_add_right`,
  `constantTerm_cond_adelicBox_eq`, `globalPoints_unipotentGL2`, and the `_impl` staging row) and the
  headline.  The pin's label namespace is rectified from its machine token to the word namespace
  `UnipotentInvariance`; the prelude keeps the pin's own statements, since the pin states them
  publicly in its file, which is why this module is checker-visible beyond the headline.

  Assumes from earlier modules: `Adelic/ConstantTerm.lean` (the constant term and its right-translate
  law), `NumberTheory/AdelicBox.lean` (the box and its additive Haar measure), and
  `NumberTheory/AdelicHaar/PlaceMeasure.lean` (the adele ring's measurable space).

  spec-pin: Theorems/Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set NumberField IsDedekindDomain NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm
open scoped ProbabilityTheory Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

namespace UnipotentInvariance

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

section FD

variable (K : Type) [Field K] [NumberField K]

theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 K) K) :=
  (Set.countable_range (algebraMap K (AdeleRing (𝓞 K) K))).to_subtype

theorem setIntegral_adelicBox_comp_add_right {f : AdeleRing (𝓞 K) K → ℂ}
    (hf : ∀ (k : K) (x : AdeleRing (𝓞 K) K), f (algebraMap K (AdeleRing (𝓞 K) K) k + x) = f x)
    (x₀ : AdeleRing (𝓞 K) K) :
    ∫ x in adelicBox K, f (x + x₀) ∂(adelicAddHaar (𝓞 K) K)
      = ∫ x in adelicBox K, f x ∂(adelicAddHaar (𝓞 K) K) := by
  have := countable_principalSubgroup K
  have hB := isAddFundamentalDomain_adelicBox_adelicAddHaar K
  have hBt : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (x₀ +ᵥ adelicBox K)
      (adelicAddHaar (𝓞 K) K) := hB.vadd_of_comm x₀
  have hf' : ∀ (g : AdeleRing.principalSubgroup (𝓞 K) K) (x : AdeleRing (𝓞 K) K),
      f (g +ᵥ x) = f x := by
    rintro ⟨_, k, rfl⟩ x
    exact hf k x
  have himg : (fun x => x + x₀) '' adelicBox K = x₀ +ᵥ adelicBox K := by
    ext y
    simp only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, add_comm _ _⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, add_comm _ _⟩
  have hmp := (measurePreserving_add_right (adelicAddHaar (𝓞 K) K) x₀).setIntegral_image_emb
    (measurableEmbedding_addRight x₀) f (adelicBox K)
  rw [himg] at hmp
  rw [← hmp]
  exact hBt.setIntegral_eq hB hf'

theorem constantTerm_cond_adelicBox_eq {G : Type*} [Group G] (u : AdeleRing (𝓞 K) K → G)
    (φ : G → ℂ) (g : G) :
    constantTerm ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) u φ g
      = ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹.toReal
          • ∫ x in adelicBox K, φ (u x * g) ∂(adelicAddHaar (𝓞 K) K) := by
  unfold constantTerm constantTermIntegrand
  rw [ProbabilityTheory.cond, integral_smul_measure]

theorem globalPoints_unipotentGL2 (k : K) :
    globalPoints (𝓞 K) K (unipotentGL2 k) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) := by
  ext i j
  change algebraMap K (AdeleRing (𝓞 K) K) ((unipotentGL2 k : Matrix (Fin 2) (Fin 2) K) i j)
    = (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) : Matrix (Fin 2) (Fin 2) _) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem constantTerm_adelicBox_unipotentGL2_mul' {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ (k : K) (h : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K (unipotentGL2 k) * h) = φ h)
    (x₀ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    constantTerm ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) (fun x => unipotentGL2 x) φ
        (unipotentGL2 x₀ * g)
      = constantTerm ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) (fun x => unipotentGL2 x) φ g := by
  rw [constantTerm_cond_adelicBox_eq, constantTerm_cond_adelicBox_eq]
  congr 1
  have hshift : ∀ x : AdeleRing (𝓞 K) K,
      φ (unipotentGL2 x * (unipotentGL2 x₀ * g)) = φ (unipotentGL2 (x + x₀) * g) := by
    intro x
    rw [unipotentGL2_add, mul_assoc]
  simp only [hshift]
  refine setIntegral_adelicBox_comp_add_right K (f := fun x => φ (unipotentGL2 x * g)) ?_ x₀
  intro k x
  show φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k + x) * g) = φ (unipotentGL2 x * g)
  rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hφ]

end FD

end UnipotentInvariance

end

theorem AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul (K : Type) [Field K] [NumberField K]
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K → ℂ}
    (hφ : ∀ (k : K) (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K),
      φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers K) K
        (AutomorphicForm.unipotentGL2 k) * h) = φ h)
    (x₀ : NumberField.AdeleRing (NumberField.RingOfIntegers K) K)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K) :
    @AutomorphicForm.constantTerm _
        (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K) _ _
        (@ProbabilityTheory.cond _
          (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K)
          (NumberField.AdelicHaar.adelicAddHaar (NumberField.RingOfIntegers K) K)
          (NumberField.AdelicBox.adelicBox K))
        (fun x => AutomorphicForm.unipotentGL2 x) φ (AutomorphicForm.unipotentGL2 x₀ * g)
      = @AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K) _ _
          (@ProbabilityTheory.cond _
            (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K)
            (NumberField.AdelicHaar.adelicAddHaar (NumberField.RingOfIntegers K) K)
            (NumberField.AdelicBox.adelicBox K))
          (fun x => AutomorphicForm.unipotentGL2 x) φ g := by
  exact UnipotentInvariance.constantTerm_adelicBox_unipotentGL2_mul' K hφ x₀ g
