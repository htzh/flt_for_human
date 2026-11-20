import FLTForHuman.LanglandsTunnell.WeightOneLiftGlobalPoints
import FLTForHuman.LanglandsTunnell.WeightOneLiftKfSmooth

/-!
  SET-AF93 consumer: the weight-one lift is a function on the double coset space.

  **The rows.** `FLTForHuman/LanglandsTunnell/WeightOneLiftGlobalPoints.lean` carries
  `weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift`: the lift is invariant
  under left multiplication by `GL₂(ℚ)` (through `globalPoints`) and under right multiplication by
  `finiteLevelOne (ratLevel N)`, and on a finite-level element it is the archimedean slash factor.
  `FLTForHuman/LanglandsTunnell/WeightOneLiftKfSmooth.lean` carries `isKfSmooth_weightOneLift`: its
  stabilizer in the finite adèles contains an open subgroup.

  **The reading.** The two invariances are exactly the relation defining a function on
  `GL₂(ℚ) \ GL₂(𝔸) / K_f`, so they compose: the lift of `γ · x · u` (`γ` rational, `u` of level
  `N`) is the lift of `x`. That double-coset form is what the Nebentypus rows
  (`weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero` and its three
  companions, the rows SET-AF93 readies) consume: they read the lift through the right
  `finiteLevelZero` translate and the left rational one at once.

  The second theorem reads `IsKfSmooth` in the `IsSmoothVector` spelling: the stabilizer of the
  lift under right translation is open, which is the finite-adelic half of the admissibility of the
  automorphic representation the lift generates.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF93Consumer.lean` and never enters the build.
-/

set_option autoImplicit false
noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open UpperHalfPlane DihedralWeightOne
open scoped ModularForm MatrixGroups

namespace AutomorphicFormSetAF93Consumer

/-- The lift is invariant on the double coset `GL₂(ℚ) · x · K_f(N)`. -/
theorem weightOneLift_globalPoints_mul_finEmbed_mul
    {N : ℕ} (hN : N ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 N → f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = f)
    (γ : GL (Fin 2) ℚ) {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N))
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f
        (globalPoints (𝓞 ℚ) ℚ γ * (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u))
      = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f x := by
  obtain ⟨hinv, hfin, -⟩ :=
    weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift hN f hf
  calc weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f
        (globalPoints (𝓞 ℚ) ℚ γ * (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u))
      = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f
          (globalPoints (𝓞 ℚ) ℚ γ * x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) := by rw [mul_assoc]
    _ = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f (globalPoints (𝓞 ℚ) ℚ γ * x) := hfin u hu _
    _ = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f x := hinv γ x

/-- On a finite-level element the lift is the archimedean slash factor at the real component. -/
theorem weightOneLift_eq_weightOneArchLift_of_glFin_eq_one
    {N : ℕ} (hN : N ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 N → f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = f)
    {h : AdelicGL2 (𝓞 ℚ) ℚ} (hfin : glFin (𝓞 ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f h
      = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h) := by
  obtain ⟨-, -, harch⟩ :=
    weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift hN f hf
  exact harch h hfin hpos

/-- `IsKfSmooth` read as an open subgroup of the finite adèles fixing the lift. -/
theorem exists_isOpen_subgroup_smul_weightOneLift
    {N : ℕ} (hN : N ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 N → f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = f) :
    ∃ U : Subgroup (AutomorphicForm.finiteAdelicGL2Subgroup ℚ),
      IsOpen (U : Set (AutomorphicForm.finiteAdelicGL2Subgroup ℚ)) ∧
      ∀ u ∈ U, u • FLT.SmoothVectors.RightTranslationFn.mk
        (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f)
          = FLT.SmoothVectors.RightTranslationFn.mk (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f) := by
  refine (FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup
    (G := AutomorphicForm.finiteAdelicGL2Subgroup ℚ)
    (v := FLT.SmoothVectors.RightTranslationFn.mk
      (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f))).mp ?_
  exact LanglandsTunnell.isKfSmooth_weightOneLift (n := N) hN f hf

end AutomorphicFormSetAF93Consumer
