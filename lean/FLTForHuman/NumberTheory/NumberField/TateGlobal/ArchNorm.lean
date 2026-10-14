/-
  The archimedean norms, and the idèle norm on the archimedean unit embedding.

  `exists_norm_pow_mult_eq` — every positive real is `‖t‖ ^ w.mult` for a nonzero
  `t : w.Completion` — is the surjectivity of the archimedean norm onto the positive
  reals. `ideleNorm_archCentralUnit` computes the idèle norm of the archimedean central
  unit through the multiplicative Haar character,
  `ideleNorm F (archCentralUnit F w a) = ((distribHaarChar (w.Completion) a : ℝ≥0) : ℝ)`,
  and `ideleNorm_archUnitHom` is its unit-embedding form,
  `ideleNorm F (archUnitHom w a) = ‖(a : w.Completion)‖ ^ w.mult`. Together they are the
  archimedean-norm block that the norm-one idèles and the central-scalar covering
  arguments are built from (`exists_mem_unitsOutside_ideleNorm_eq` and its consumers).

  Transcribed from the pin
  `P2M/Sol/S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean`
  (pinned `aa2d8b3`), where the three are `private` prelude of the Fujisaki-compactness
  proof (pin lines 2511 / 2554 / 3487). They are public mathematics — the pin re-copies
  them into 21 / 35 / 13 `S_` files — so they are homed here by subject, at the theory
  namespace `NumberField.TateGlobal`; `TateGlobal/FujisakiCompact.lean` imports them
  rather than carrying its own copies. Statements are the pin's; the only proof
  adaptation is the port's `v4.34.0` spelling of the `ite` reductions (`ite_eq_left` /
  `ite_eq_right` for the pin's `if_pos` / `if_neg`), carried over unchanged from the
  module this block moves out of.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ArchMulHaar
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ArchSlab
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IntLocalIntegrability

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NNReal

noncomputable section

namespace NumberField

namespace TateGlobal

variable (F : Type) [Field F] [NumberField F]

-- pin: ideleNorm_archCentralUnit (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:2511)
theorem ideleNorm_archCentralUnit (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    ideleNorm F (NumberField.AdelicVolume.archCentralUnit F w a) =
      ((distribHaarChar (w.Completion) a : ℝ≥0) : ℝ) := by
  unfold ideleNorm
  rw [distribHaarChar_archCentralUnit]

variable {F}

-- pin: ideleNorm_archUnitHom (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:2554)
theorem ideleNorm_archUnitHom (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    ideleNorm F (archUnitHom w a) = ‖(a : w.Completion)‖ ^ w.mult := by
  borelize (w.Completion)
  rw [archUnitHom_apply, ideleNorm_archCentralUnit,
    NumberField.TateGlobal.FujisakiC3.distribHaarChar_completion_eq_pow_mult]
  push_cast
  rfl

-- pin: exists_norm_pow_mult_eq (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3487)
omit [NumberField F] in
theorem exists_norm_pow_mult_eq (w : InfinitePlace F) (r : ℝ) (hr : 0 < r) :
    ∃ t : w.Completion, t ≠ 0 ∧ ‖t‖ ^ w.mult = r := by
  rcases isReal_or_isComplex w with hv | hv
  · refine ⟨(ringEquivRealOfIsReal hv).symm r, ?_, ?_⟩
    · rw [ne_eq, ← map_zero (ringEquivRealOfIsReal hv).symm, (ringEquivRealOfIsReal hv).symm.injective.eq_iff]
      exact hr.ne'
    · have hn : ‖(ringEquivRealOfIsReal hv).symm r‖ = ‖r‖ := by
        have h := congrArg (fun z : ℝ≥0 => (z : ℝ))
          (NumberField.TateGlobal.ArchMulHaarCompletion.nnnorm_ringEquivReal hv ((ringEquivRealOfIsReal hv).symm r))
        simp only [RingEquiv.apply_symm_apply, coe_nnnorm] at h
        exact h.symm
      rw [mult, ite_eq_left hv, pow_one, hn, Real.norm_eq_abs, abs_of_pos hr]
  · refine ⟨(ringEquivComplexOfIsComplex hv).symm (Real.sqrt r : ℂ), ?_, ?_⟩
    · rw [ne_eq, ← map_zero (ringEquivComplexOfIsComplex hv).symm,
        (ringEquivComplexOfIsComplex hv).symm.injective.eq_iff, Complex.ofReal_eq_zero]
      exact fun h => hr.ne' ((Real.sqrt_eq_zero hr.le).mp h)
    · have hn : ‖(ringEquivComplexOfIsComplex hv).symm (Real.sqrt r : ℂ)‖ = ‖(Real.sqrt r : ℂ)‖ := by
        have h := congrArg (fun z : ℝ≥0 => (z : ℝ))
          (NumberField.TateGlobal.ArchMulHaarCompletion.nnnorm_ringEquivComplex hv
            ((ringEquivComplexOfIsComplex hv).symm (Real.sqrt r : ℂ)))
        simp only [RingEquiv.apply_symm_apply, coe_nnnorm] at h
        exact h.symm
      rw [mult, ite_eq_right (not_isReal_iff_isComplex.mpr hv), hn, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg r), Real.sq_sqrt hr.le]

end TateGlobal

end NumberField

end
