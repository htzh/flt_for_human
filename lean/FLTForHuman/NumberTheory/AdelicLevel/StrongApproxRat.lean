/-
  Strong approximation for `GL₂` over the rationals.

  This is the listed façade of the GL₂ strong-approximation development: for every
  finite idèle class `g ∈ GL₂(𝔸_ℚ^fin)` there is a *rational* point `γ ∈ GL₂(ℚ)`
  whose diagonal image `glFin γ` maps `g` into the integral level subgroup
  `finiteIntegralGL2 ℤ ℚ`. Equivalently, the diagonal image of `GL₂(ℚ)` meets every
  coset of the integral level subgroup — strong approximation for `SL₂`/`GL₂` away
  from the archimedean place.

  Statement authority is the pin wrapper
  `Theorems/Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean`
  (pinned `aa2d8b3`), transcribed verbatim; the proof is the pin's `solution`
  (`P2M/Sol/S_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat.lean:884–898`),
  which instantiates the engine of `NumberTheory/AdelicLevel/StrongApprox/*` at
  `ℚ` (whose ring of integers is a PID, `Rat.classNumber_eq`).

  The wrapper's `attribute [-simp] AutomorphicForm.unipotentGL2_zero
  AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero
  AutomorphicForm.unipotentGL2_coe` is **not** reproduced: the port's
  `AutomorphicForm.unipotentGL2_coe` is a plain `@[simp]` lemma (not `scoped`), and
  no listed statement of this node is affected, so no local `simp` set needs
  adjusting. The `p2m_*` scaffolding of the pin's `S_` file is not transcribed.
-/
import FLTForHuman.NumberTheory.AdelicLevel.StrongApprox.Approximation
import Mathlib.NumberTheory.NumberField.ClassNumber

set_option autoImplicit false

noncomputable section

-- `ℚ`'s ring of integers is a PID. `local`, so nothing is exported to importers; this
-- is the pin's `haveI` (pin:891–892) hoisted out of the proof as a file-scope instance.
local instance : IsPrincipalIdealRing (NumberField.RingOfIntegers ℚ) :=
  NumberField.classNumber_eq_one_iff.mp Rat.classNumber_eq

theorem NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ γ : Matrix.GeneralLinearGroup (Fin 2) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ
          (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ) * g
        ∈ NumberField.AdelicLevel.finiteIntegralGL2 (NumberField.RingOfIntegers ℚ) ℚ := by
  obtain ⟨γ, hγ⟩ :=
    NumberField.AdelicLevel.GL2StrongApproxW8M.exists_map_mul_mem_finiteIntegralGL2
      (NumberField.RingOfIntegers ℚ) ℚ g
  refine ⟨γ, ?_⟩
  rw [NumberField.AdelicLevel.GL2StrongApproxW8M.glFin_globalPoints]
  exact hγ
