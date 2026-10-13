/-
  The `FujisakiC3` block: the idele norm is continuous.

  `normQ` is the explicit product of the archimedean norms (weighted by `w.mult`) and
  the finite norms on the shell coordinates `Q (F := F) S`; `ideleNorm_asm_eq_normQ`
  identifies it with `ideleNorm` through `asm`; `continuousOn_coord` transports
  continuity to `unitsOutside S`; and `continuous_ideleNorm` upgrades `ContinuousOn` to
  `Continuous` using `exists_mem_unitsOutside` and the openness of `unitsOutside S`.

  Transcribed from the pin's final `Fold_FujisakiC3d` section (`NumberField.TateGlobal` /
  `M4aLocalCFT.FujisakiC3` blocks), declared lines 2568-2637 of
  `P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm.lean`, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm.lean`

  The block is *shared*: the same section is re-proved in eight sibling `S_` files of
  the `S_NumberField_TateGlobal_*` family, so it is homed here once and at its pin
  names — see `topics/numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md`.  The
  pin's `M4aLocalCFT.FujisakiC3` is chapter-prefix renamed to
  `NumberField.TateGlobal.FujisakiC3`, as every other `M4aLocalCFT.*` block of the T1
  set.  The pin's `p2m_*` scaffolding is dropped; no file-wide option beyond
  `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Coordinates
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ZetaIntegrand
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IntLocalIntegrability
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal

section Fold_FujisakiC3d

open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
namespace TateGlobal
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

-- pin: exists_mem_unitsOutside (S_NumberField_TateGlobal_continuous_ideleNorm.lean:2578)
theorem exists_mem_unitsOutside (x : (AdeleRing (𝓞 F) F)ˣ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), x ∈ unitsOutside (F := F) S := by
  classical
  have h1 : {v : HeightOneSpectrum (𝓞 F) |
      ¬ ((((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
        ∈ v.adicCompletionIntegers F)}.Finite :=
    Filter.eventually_cofinite.mp (((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2).2
  have h2 : {v : HeightOneSpectrum (𝓞 F) |
      ¬ ((((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
        ∈ v.adicCompletionIntegers F)}.Finite :=
    Filter.eventually_cofinite.mp (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2).2
  refine ⟨h1.toFinset ∪ h2.toFinset, (mem_unitsOutside_iff _ x).mpr ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
  · by_contra hnot
    exact hv (Finset.mem_union_left _ (h1.mem_toFinset.mpr hnot))
  · by_contra hnot
    exact hv (Finset.mem_union_right _ (h2.mem_toFinset.mpr hnot))

section NormQ

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- pin: normQ (S_NumberField_TateGlobal_continuous_ideleNorm.lean:2599)
def normQ (q : Q (F := F) S) : ℝ :=
  (∏ w : InfinitePlace F, ‖((q.1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ ^ w.mult) *
    ∏ v : S, ‖((q.2.1 v : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)‖

-- Adapted: `Units.continuous_val (M := InfiniteAdeleRing F)` pins the base monoid, whose
-- `TopologicalSpace` instance is keyed on the non-reducible `def InfiniteAdeleRing`; the
-- pin's unannotated `Units.continuous_val` unfolds it and loses the instance.
-- pin: continuous_normQ (S_NumberField_TateGlobal_continuous_ideleNorm.lean:2603)
theorem continuous_normQ : Continuous (normQ (F := F) S) := by
  refine Continuous.mul ?_ ?_
  · refine continuous_finsetProd _ fun w _ => ?_
    exact (((continuous_apply w).comp
      (Units.continuous_val (M := InfiniteAdeleRing F) |>.comp continuous_fst)).norm).pow _
  · refine continuous_finsetProd _ fun v _ => ?_
    exact (Units.continuous_val.comp ((continuous_apply v).comp (continuous_fst.comp continuous_snd))).norm

-- pin: ideleNorm_asm_eq_normQ (S_NumberField_TateGlobal_continuous_ideleNorm.lean:2610)
theorem ideleNorm_asm_eq_normQ (q : Q (F := F) S) : ideleNorm F (asm S q) = normQ S q := by
  rw [ideleNorm_asm]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun v _ => ?_)
  · borelize (w.Completion)
    rw [distribHaarChar_completion_eq_pow_mult]
    push_cast
    rfl
  · exact coe_distribHaarChar_adicCompletion_eq_norm (q.2.1 v)

-- pin: continuousOn_ideleNorm (S_NumberField_TateGlobal_continuous_ideleNorm.lean:2619)
theorem continuousOn_ideleNorm : ContinuousOn (ideleNorm F) (unitsOutside (F := F) S) := by
  have h : Set.EqOn (ideleNorm F) (normQ S ∘ coord S) (unitsOutside (F := F) S) := fun x hx => by
    show ideleNorm F x = normQ S (coord S x)
    rw [← ideleNorm_asm_eq_normQ, asm_coord S hx]
  exact ((continuous_normQ S).comp_continuousOn (continuousOn_coord S)).congr h

end NormQ

-- pin: continuous_ideleNorm (S_NumberField_TateGlobal_continuous_ideleNorm.lean:2628)
theorem continuous_ideleNorm : Continuous (ideleNorm F) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨S, hS⟩ := exists_mem_unitsOutside x
  exact (continuousOn_ideleNorm S).continuousAt ((isOpen_unitsOutside S).mem_nhds hS)

end FujisakiC3
end NumberField.TateGlobal

end

end Fold_FujisakiC3d
