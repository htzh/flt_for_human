/-
  The weight-one lift's equivariance under global points, `K_f`, and the archimedean component.

  The lift is invariant under left multiplication by `GL₂(ℚ)` and under right multiplication by
  `finiteLevelOne`, and on a finite-level element with positive-determinant real component it is
  the archimedean slash factor.

  Transcribed from
  `P2M/Sol/S_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift.lean`
  (pinned `aa2d8b3`, 472 lines / 27 declarations): every declaration of the pin except `solution`
  is part of the shared prelude and lives in `WeightOneLiftAdelic`, so this module is the row
  alone, in the pin's `DihedralWeightOne` namespace.

  spec-pin: P2M/Sol/S_DihedralWeightOne_weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift.lean

  ## Heartbeat probe

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N <this file>` (the project's default is
  4,000,000): silent at N = 400000, fails at N = 200000. No `set_option maxHeartbeats` is installed
  (FR-0225).

  ## Port deltas

  - the pin's `P2GProbe.R4a.weightOneLift_globalPoints_mul`, `.weightOneLift_mul_of_mem_U` and
    `.weightOneLift_eq` are the shared prelude's `LanglandsTunnell.…` names
    (`WeightOneLiftAdelic.lean`), which this module opens.
-/


import FLTForHuman.LanglandsTunnell.WeightOneLiftAdelic
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


namespace DihedralWeightOne



theorem weightOneLift_globalPoints_mul_and_mul_finEmbed_and_eq_weightOneArchLift
    {N : ℕ} (hN : N ≠ 0) (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma1 N → f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = f) :
    (∀ (γ : GL (Fin 2) ℚ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f (globalPoints (𝓞 ℚ) ℚ γ * x) =
          weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f x) ∧
    (∀ u ∈ finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
          weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f x) ∧
    ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ h = 1 →
      LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ →
        weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) f h = weightOneArchLift f (LanglandsTunnell.ratArchGL2 h) := by
  refine ⟨fun γ x => LanglandsTunnell.weightOneLift_globalPoints_mul hN f hf γ x, fun u hu x => ?_,
    fun h hh hpos => ?_⟩
  · exact LanglandsTunnell.weightOneLift_mul_of_mem_U hN f hf x
      (Subgroup.mem_inf.mpr
        ⟨AdelicLevel.mem_levelOne_iff.mpr (by rw [AdelicDock.glFin_finEmbed]; exact hu),
         (mem_finiteAdelicGL2Subgroup_iff _ _).mpr (AdelicDock.glArch_finEmbed (𝓞 ℚ) ℚ u)⟩)
  · exact LanglandsTunnell.weightOneLift_eq hN f hf h 1 h 1 (one_mem _) hh hpos
      (by rw [map_one, one_mul, mul_one])

end DihedralWeightOne

end
