/-
  The idèle norm of a determinant: `|det X| = ∏_w archDetNorm w X ^ w.mult`.

  This is the glue the `GL₂` determinant-norm arguments share: the one-place
  computations `norm_eq_zpow_of_valued`, `valued_det_le_one`, `det_snd_apply`,
  `det_fst_apply`, `valued_det_finComponent_eq_one`, and the headline built from them.
  It lives in the `AutomorphicForm` tree, not beside `ideleNorm` in `NumberField`: its
  hypothesis is about `AdelicGL2 (𝓞 F) F`, whose home is `AutomorphicForm/Adelic/Basic`, so the
  import direction (`AutomorphicForm → NumberTheory`) puts the module here — the same side
  the pin keeps its copy on.

  Transcribed from the pin's
  `P2M/Sol/S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.lean`
  (pinned `aa2d8b3`), where the headline is `_pow_mult` and the glue lemma of the same
  statement is `ideleNorm_det_eq_prod_archDetNorm_pow`; the port keeps **one** copy, at
  the wrapper's name. The pin's private helpers stay public here (their statements are the
  pin's, so the checker reads them from the pin-private fallback) because
  `AutomorphicForm.Adelic.Siegel.SlabCovering` consumes three of them; that module used to
  carry its own private copies of all six, and now imports this one.

  spec-pin: Theorems/Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.lean
  spec-pin: P2M/Sol/S_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.NumberTheory.AdelicVolume
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.Projections

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicVolume
open NumberField.TateGlobal AutomorphicForm
open scoped MatrixGroups NNReal

namespace NumberField.TateGlobal.IdeleNormDetGlue

variable {F : Type} [Field F] [NumberField F]

theorem norm_eq_zpow_of_valued (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F} {m : ℤ}
    (hx : Valued.v x = WithZero.exp m) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem valued_det_le_one (v : HeightOneSpectrum (𝓞 F))
    {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)} (h : ∀ i j, Valued.v (M i j) ≤ 1) :
    Valued.v M.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
  · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

theorem det_snd_apply (X : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
      = ((finComponent (𝓞 F) F v (glFin (𝓞 F) F X) : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F))
    (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

theorem det_fst_apply (X : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = ((archComponent F w (glArch (𝓞 F) F X) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((archEval F w).comp (adeleArch (𝓞 F) F))
    (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

theorem valued_det_finComponent_eq_one (X : AdelicGL2 (𝓞 F) F)
    (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((finComponent (𝓞 F) F v (glFin (𝓞 F) F X) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
  set A := finComponent (𝓞 F) F v (glFin (𝓞 F) F X) with hA
  obtain ⟨h1, h2⟩ := mem_finiteIntegralGL2_iff.mp hX
  have ha : Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≤ 1 :=
    valued_det_le_one v fun i j =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h1 i j v)
  have hb : Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≤ 1 := by
    rw [hA, ← map_inv]
    exact valued_det_le_one v fun i j =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h2 i j v)
  have hab : (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      * ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hprod : Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      * Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
    rw [← map_mul, hab, map_one]
  refine le_antisymm ha ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
          * Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
              Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := hprod.symm
    _ ≤ Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det * 1 := mul_le_mul_right hb _
    _ = _ := mul_one _

end NumberField.TateGlobal.IdeleNormDetGlue

namespace NumberField.TateGlobal

open IdeleNormDetGlue

variable {F : Type} [Field F] [NumberField F]

theorem ideleNorm_det_eq_prod_archDetNorm_pow_mult (X : AdelicGL2 (𝓞 F) F)
    (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det X)
      = ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult := by
  have hS := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F
    (Matrix.GeneralLinearGroup.det X)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    intro v
    rw [det_snd_apply, norm_eq_zpow_of_valued v (m := 0)
      (by rw [valued_det_finComponent_eq_one X hX v, WithZero.exp_zero]), zpow_zero]
  have harch : ∀ w : InfinitePlace F,
      ‖((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖
        = archDetNorm w X := by
    intro w
    rw [det_fst_apply]
    rfl
  unfold ideleNorm
  rw [hS, finprod_eq_one_of_forall_eq_one hfin, mul_one]
  exact Finset.prod_congr rfl fun w _ => by rw [harch w]

end NumberField.TateGlobal
