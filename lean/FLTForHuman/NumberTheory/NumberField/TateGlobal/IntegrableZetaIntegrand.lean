/-
  The G1 discharge: the shell bound `hole_G1_shellBound` for pure tensors, the
  pure-tensor integrability `hole_G1_pureTensor`, its extension to the Schwartz
  Bruhat space `integrable_zetaIntegrand_impl`, and the dev headline
  `NumberField.TateGlobal.integrable_zetaIntegrand_holds` (the pin's `solution`).

  Transcribed from the pin's `Fold_G1Proof` section (`NumberField.TateGlobal`
  block) and its trailing `solution`, declared lines 6083-6203 of file B, pinned
  `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_integrable_zetaIntegrand.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped, as are the file-scoped
  `set_option maxHeartbeats 1600000` / `maxSynthPendingDepth 3` (B 6063/6065); all
  declarations elaborate at the port's low edit cap.  `M4aLocalCFT.` is renamed to
  `NumberField.TateGlobal.`.  The pin's `solution` is renamed
  `integrable_zetaIntegrand_holds` and stays in the flat
  `NumberField.TateGlobal` namespace (the pin declared it at top level, outside
  any sub-namespace); the façade re-states it at the pin wrapper's name
  `NumberField.TateGlobal.integrable_zetaIntegrand`.  `hole_G1_shellBound` needs a
  per-declaration `linter.style.haveILetI` suppression for the pin's load-bearing
  `letI`/`haveI` instance wall.  No file-wide option beyond
  `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.PureTensor

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion NumberField.InfiniteAdeleRing
open NumberField.AdelicFourier
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open AutomorphicForm
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal Classical

section Fold_G1Proof

open AutomorphicForm IsDedekindDomain NumberField.TateGlobal

open scoped NNReal

noncomputable section

namespace NumberField
namespace TateGlobal

variable (F : Type) [Field F] [NumberField F]

-- The pin's `letI`/`haveI` instance wall is load-bearing here, and the goal is a
-- proposition, which `linter.style.haveILetI` flags.
set_option linter.style.haveILetI false in
-- pin: hole_G1_shellBound (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:6083)
theorem hole_G1_shellBound [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    {s : ℂ} (hs : 1 < s.re) :
    ∃ (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (M : ℝ), 0 ≤ M
      ∧ (∀ k : ExpIndex (F := F) S, IntegrableOn
          (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
          (shell S k.1) ν)
      ∧ (∀ k : ExpIndex (F := F) S, 0 ≤ k.1 →
          (∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν)
            ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat) * M)
      ∧ (∀ k : ExpIndex (F := F) S, ¬ 0 ≤ k.1 →
          (∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν) = 0) := by
  letI : ∀ w : InfinitePlace F, MeasurableSpace w.Completion := fun _ => borel _
  haveI : ∀ w : InfinitePlace F, BorelSpace w.Completion := fun _ => ⟨rfl⟩
  letI : ∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ := fun _ => borel _
  haveI : ∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ := fun _ => ⟨rfl⟩
  letI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) :=
    fun _ => borel _
  haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) :=
    fun _ => ⟨rfl⟩
  letI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ :=
    fun _ => borel _
  haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ :=
    fun _ => ⟨rfl⟩
  letI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      MeasurableSpace (v.adicCompletionIntegers F)ˣ := fun _ => borel _
  haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      BorelSpace (v.adicCompletionIntegers F)ˣ := fun _ => ⟨rfl⟩
  letI : MeasurableSpace (InfiniteAdeleRing F)ˣ := borel _
  haveI : BorelSpace (InfiniteAdeleRing F)ˣ := ⟨rfl⟩
  haveI hPCa : ∀ w : InfinitePlace F, Nonempty (TopologicalSpace.PositiveCompacts w.Completion) :=
    fun _ => inferInstance
  haveI hPCf : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      Nonempty (TopologicalSpace.PositiveCompacts (v.adicCompletion F)) := fun _ => inferInstance
  haveI hHa : ∀ w : InfinitePlace F,
      (Measure.addHaarMeasure (Classical.arbitrary (TopologicalSpace.PositiveCompacts w.Completion))).IsAddHaarMeasure :=
    fun _ => inferInstance
  haveI hRa : ∀ w : InfinitePlace F,
      (Measure.addHaarMeasure (Classical.arbitrary (TopologicalSpace.PositiveCompacts w.Completion))).Regular :=
    fun _ => inferInstance
  haveI hHf : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (Measure.addHaarMeasure (Classical.arbitrary (TopologicalSpace.PositiveCompacts (v.adicCompletion F)))).IsAddHaarMeasure :=
    fun _ => inferInstance
  haveI hRf : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      (Measure.addHaarMeasure (Classical.arbitrary (TopologicalSpace.PositiveCompacts (v.adicCompletion F)))).Regular :=
    fun _ => inferInstance
  exact G1Discharge.hole_of_measures
    (fun w => Measure.addHaarMeasure (Classical.arbitrary (TopologicalSpace.PositiveCompacts w.Completion)))
    (fun v => Measure.addHaarMeasure (Classical.arbitrary (TopologicalSpace.PositiveCompacts (v.adicCompletion F))))
    ν hf hχc hχu hs

-- pin: hole_G1_pureTensor (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:6136)
theorem hole_G1_pureTensor [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν := by
  obtain ⟨S, M, hM, hint, hbound, hzero⟩ := hole_G1_shellBound F ν hf hχc hχu hs
  have hsum : Summable (fun k : ExpIndex (F := F) S =>
      ∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν) :=
    ShellBound.summable_of_shell_bound hs _
      (fun k => integral_nonneg fun x => norm_nonneg _) hM hbound hzero
  have h := MeasureTheory.integrableOn_iUnion_of_summable_integral_norm hint hsum
  rw [iUnion_shell] at h
  exact integrableOn_univ.mp h

-- pin: integrable_zetaIntegrand_impl (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:6151)
theorem integrable_zetaIntegrand_impl [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν := by
  have key : ∀ f' ∈ pureTensorSet F,
      Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ =>
        f' x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν :=
    fun f' hf' => hole_G1_pureTensor F ν hf' hχc hχu hs
  induction hf using Submodule.span_induction with
  | mem f' hf' => exact key f' hf'
  | zero => simp
  | add f₁ f₂ _ _ ih₁ ih₂ =>
      have heq : (fun x : (AdeleRing (𝓞 F) F)ˣ =>
            (f₁ + f₂) x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
          = (fun x : (AdeleRing (𝓞 F) F)ˣ =>
                f₁ x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
            + (fun x : (AdeleRing (𝓞 F) F)ˣ =>
                f₂ x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) := by
        funext x; simp only [Pi.add_apply]; ring
      exact heq ▸ ih₁.add ih₂
  | smul c f' _ ih =>
      have heq : (fun x : (AdeleRing (𝓞 F) F)ˣ =>
            (c • f') x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
          = c • (fun x : (AdeleRing (𝓞 F) F)ˣ =>
                f' x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
      exact heq ▸ ih.smul c

end TateGlobal
end NumberField

end

end Fold_G1Proof

namespace NumberField
namespace TateGlobal

open AutomorphicForm IsDedekindDomain

-- B's pin `solution` is a top-level theorem (declared under an `open ... in` at
-- B 6191, outside any sub-namespace), so the dev headline stays in the flat
-- `NumberField.TateGlobal` namespace; it is given the dev-only suffix `_holds` so
-- that the façade `FLTForHuman/NumberTheory/NumberField/TateGlobal.lean` can
-- declare the pin wrapper's name `NumberField.TateGlobal.integrable_zetaIntegrand`.
-- pin: solution (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:6193)
theorem integrable_zetaIntegrand_holds (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν :=
  NumberField.TateGlobal.integrable_zetaIntegrand_impl F ν hf hχc hχu hs

end TateGlobal
end NumberField
