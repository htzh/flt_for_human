/-
  SET-AF88C consumer: conjugated test functions, their pure tensors, and the `Kf`-level ideal.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/KfSmoothTensor.lean` carries `Kf`-smoothness giving a
  level ideal, conjugation by the finite subgroup times the row-isometry subgroup preserving factorizability
  and archimedean bi-finiteness, the level splitting of an integral element, and the pure-tensor set being
  preserved by the unipotent translate.

  **The readings.** Zone 1 composes two rows: a conjugated factorizable test function is again factorizable
  (row 2), and *that* function composed with a unipotent translate is a pure tensor (row 4) — the form the
  orbital analysis uses when it first conjugates a test function and then reads its coefficients. Zone 2 is
  the `Kf`-level row unpacked at a point.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF88CConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.KfSmoothTensor

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm
open scoped Classical ENNReal NNReal BigOperators Matrix ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicFormSetAF88CConsumer

/-- **Zone 1.** A conjugated factorizable test function, composed with a unipotent translate, is a pure
tensor: the conjugation row feeds the pure-tensor row. -/
theorem exists_pureTensor_of_conj_comp_unipotent
    (F : Type) [Field F] [NumberField F]
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F)
    (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (g₁ g₂ : AdelicGL2 (𝓞 F) F) :
    ∃ tys' : ArchTypeFamily F,
      IsFactorizableTestFn F (fun y => f ((g * k) * y * (g * k)⁻¹)) ∧
      IsArchBiFinite F tys' (fun y => f ((g * k) * y * (g * k)⁻¹)) ∧
      (fun s => (fun y => f ((g * k) * y * (g * k)⁻¹)) (g₁ * unipotentGL2 s * g₂))
        ∈ NumberField.AdelicFourier.pureTensorSet F := by
  obtain ⟨tys', hf', hbf'⟩ :=
    CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj F g hg k hk f tys hf hbf
  exact ⟨tys', hf', hbf', IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet F hf' g₁ g₂⟩

/-- **Zone 2.** The `Kf`-level row at a point: a `Kf`-smooth function has a level ideal beyond which the
conjugate-unipotent translate acts trivially. -/
theorem exists_ideal_forall_conj_unipotentGL2_eq (F : Type) [Field F] [NumberField F]
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ (g x : AdelicGL2 (𝓞 F) F), glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F →
      ∀ (t : AdeleRing (𝓞 F) F), adeleArch (𝓞 F) F t = 0 →
        adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F 𝔫 →
          φ (g * (x⁻¹ * unipotentGL2 t * x)) = φ g :=
  IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq hφ

end AutomorphicFormSetAF88CConsumer
