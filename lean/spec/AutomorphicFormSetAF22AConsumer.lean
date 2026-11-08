/-
  SET-AF22A consumer: the algebra of the factorizable test functions, read at `ℚ`.

  `Adelic/TestFnInvariance.lean` carries the three rows of SET-AF22A:

  * `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` — the factorizable test functions
    are closed under the right action `y ↦ f (t⁻¹ * y)` (the archimedean and finite factors are
    each composed with a left translate, which preserves `IsArchTestFactor` / `IsFinTestFactor`);
  * `isFactorizableTestFn_sum_mul_comp_mul_mul` — a finite sum `∑ i, c i * f (a i * y * b i)` is
    again factorizable when the `a i`, `b i` are row isometries, because those act trivially on the
    finite factor and by a continuous linear change of the archimedean matrix variable;
  * `exists_isRightEquivariant_comp_subtype_eq_of_injective` — a right-equivariant linear map on an
    invariant submodule extends to the whole space along an injective `ι`.

  **This zone.** Two chains, at concrete data, in one statement:

  * the non-vacuity witness `f = fun _ => 0` of `isFactorizableTestFn_zero` is first translated by
    `t⁻¹` (row 51) and then averaged over the two double translates at `a = b = 1` with all weights
    `1` (row 98 at `n = 2`), and the result is read to be factorizable. The two row-isometry
    hypotheses are discharged at the identity, which lies in each `(rowIsometryInclAt₀ ℚ w).range`
    and hence in the supremum;
  * row 70 is instantiated at the trivial group `H = G = PUnit` with the trivial representation,
    `A = ⊤` and `TA = 0`: it produces a linear map `T` out of `ℂ` with `T ∘ A.subtype = TA`, the
    extension half of the conclusion, on the nose.

  No `#check`: every headline is used at explicit arguments, so a change to any of the three
  statements shows up here as an error.
-/
import FLTForHuman.AutomorphicForm.Adelic.TestFnInvariance

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel
open scoped ENNReal Pointwise

namespace AutomorphicForm

namespace SetAF22A

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

/-- **The zone.** (i) The zero test function, translated by `t⁻¹` and averaged over the two double
row-isometry translates at `a = b = 1`, is factorizable. (ii) At the trivial group, the equivariant
extension lemma extends the zero map on `⊤ ⊆ ℂ` to a linear map `T` with `T ∘ A.subtype = TA`. -/
theorem consumer_zone_testFnInvariance
    (t : AdelicGL2 (𝓞 ℚ) ℚ) :
    IsFactorizableTestFn ℚ
        (fun y => ∑ _i : Fin 2, (1 : ℂ) * (fun z => (fun _ => (0 : ℂ)) (t⁻¹ * z)) (1 * y * 1)) ∧
      ∃ T : ℂ →ₗ[ℂ] (PUnit → ℂ),
        T ∘ₗ (⊤ : Submodule ℂ ℂ).subtype = (0 : ↥(⊤ : Submodule ℂ ℂ) →ₗ[ℂ] (PUnit → ℂ)) := by
  constructor
  · -- row 51: the zero test function, translated by `t⁻¹`
    have h0 : IsFactorizableTestFn ℚ (fun z => (fun _ => (0 : ℂ)) (t⁻¹ * z)) :=
      isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn ℚ (fun _ => (0 : ℂ))
        (isFactorizableTestFn_zero ℚ) t
    -- row 98 at `n = 2`, `a = b = 1`, all weights `1`
    refine isFactorizableTestFn_sum_mul_comp_mul_mul (F := ℚ) (n := 2) (c := fun _ => (1 : ℂ))
      (a := fun _ => 1) (b := fun _ => 1) h0 ?_ ?_
    · intro _
      exact Subgroup.mem_iSup_of_mem (Classical.choice (inferInstance : Nonempty (InfinitePlace ℚ)))
        (by simp)
    · intro _
      exact Subgroup.mem_iSup_of_mem (Classical.choice (inferInstance : Nonempty (InfinitePlace ℚ)))
        (by simp)
  · -- row 70 at the trivial group `H = G = PUnit`, trivial representation, `A = ⊤`, `TA = 0`
    obtain ⟨T, _, hT⟩ :=
      exists_isRightEquivariant_comp_subtype_eq_of_injective (H := PUnit) (G := PUnit) (W := ℂ)
        (MonoidHom.id PUnit) Function.injective_id (1 : Representation ℂ PUnit ℂ)
        (⊤ : Submodule ℂ ℂ) (fun k a _ => by simp)
        (0 : ↥(⊤ : Submodule ℂ ℂ) →ₗ[ℂ] (PUnit → ℂ)) (fun k a x => by simp)
    exact ⟨T, hT⟩

end SetAF22A

end AutomorphicForm

end
