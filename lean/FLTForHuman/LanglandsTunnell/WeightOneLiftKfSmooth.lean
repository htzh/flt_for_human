/-
  The weight-one lift is `K_f`-smooth.

  For a weight-one form `f` on `Γ₁(n)`, the lift is invariant under right translation by the
  compact-open subgroup `K_f = ∏_v K_v` of the finite idèles.

  Transcribed from `P2M/Sol/S_LanglandsTunnell_isKfSmooth_weightOneLift.lean` (pinned `aa2d8b3`,
  438 lines / 26 declarations): every declaration of the pin except `solution` is part of the
  shared prelude and lives in `WeightOneLiftAdelic`, so this module is the row alone.

  spec-pin: P2M/Sol/S_LanglandsTunnell_isKfSmooth_weightOneLift.lean

  ## Heartbeat probe

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N <this file>` (the project's default is
  4,000,000): silent at N = 200000, fails at N = 100000. No `set_option maxHeartbeats` is installed
  (FR-0225).

  ## Port deltas

  - the pin's `P2GProbe.R4a.weightOneLift_mul_of_mem_U` is the shared prelude's
    `LanglandsTunnell.weightOneLift_mul_of_mem_U` (`WeightOneLiftAdelic.lean`).
  - the pin names the open subgroup by `(levelOne …).subgroupOf (finiteAdelicGL2Subgroup …)`; the
    port states the same subgroup as `(levelOne …).comap (finiteAdelicGL2Subgroup K).subtype`
    (`AutomorphicForm/Adelic/RightConvStructurePreservation.lean:307`), so the proof is written in
    that shape.
-/
import FLTForHuman.LanglandsTunnell.WeightOneLiftAdelic
import FLTForHuman.RepTheory.SmoothVectors
import FLTForHuman.AutomorphicForm.Adelic.RightConvStructurePreservation
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm UpperHalfPlane
open UpperHalfPlane Matrix
open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open Matrix Matrix.GeneralLinearGroup
open CongruenceSubgroup ModularGroup
open AdelicDock
open NumberField.AdelicHaar
open HeckeIntegralSeam HeckePair
open AutomorphicForm.SmoothCusp IsDedekindDomain.HeightOneSpectrum
open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel NumberField.AdelicVolume
open MeasureTheory
open scoped Topology Manifold
open DihedralWeightOne


namespace LanglandsTunnell

open RatArch DetIntegral ArchLift



theorem isKfSmooth_weightOneLift
    {n : ℕ} (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f) :
    IsKfSmooth ℚ (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by
  have hN : Ideal.span {(n : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  rw [AutomorphicForm.isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup]
  refine ⟨(NumberField.AdelicLevel.levelOne (𝓞 ℚ) ℚ (Ideal.span {(n : 𝓞 ℚ)})).comap
      (AutomorphicForm.finiteAdelicGL2Subgroup ℚ).subtype, ?_, ?_⟩
  · rw [Subgroup.coe_comap, Subgroup.coe_subtype]
    exact (NumberField.AdelicLevel.isOpen_levelOne (𝓞 ℚ) ℚ hN).preimage continuous_subtype_val
  · intro u hu
    rw [Subgroup.smul_def]
    refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
    rw [FLT.SmoothVectors.RightTranslationFn.toFun_smul,
      FLT.SmoothVectors.RightTranslationFn.toFun_mk]
    exact weightOneLift_mul_of_mem_U hn f hf x ⟨Subgroup.mem_comap.mp hu, u.2⟩

end LanglandsTunnell

end
