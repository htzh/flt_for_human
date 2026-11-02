/-
  The values of the idèle norm on the three kinds of idèle.

  * `ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles`: an idèle with
    trivial archimedean part and unit-idèle finite part has norm `1` — the norm is the
    archimedean product, and every finite component has norm `1` because the element and
    its inverse are integral.
  * `ideleNorm_uniformizerIdele`: the uniformizer idèle at `v` has norm
    `|absNorm v.asIdeal|⁻¹` — the single non-trivial factor.

  Both proofs unfold `ideleNorm` through
  `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm` and then
  collapse the archimedean product (resp. the finite `finprod`).

  Transcribed from the pin's
  `P2M/Sol/S_NumberField_TateGlobal_ideleNorm_{eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles,
  uniformizerIdele}.lean` (pinned `aa2d8b3`), statements at the `Theorems/` wrappers'. The
  two files share the private `norm_one_apply_pow_mult`; it is written once here. The pin's
  `attribute [-instance]`/`attribute [-simp]` scaffolding is not transcribed.

  spec-pin: Theorems/Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles.lean
  spec-pin: P2M/Sol/S_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles.lean   -- comparable copy
  spec-pin: Theorems/Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele.lean
  spec-pin: P2M/Sol/S_NumberField_TateGlobal_ideleNorm_uniformizerIdele.lean   -- comparable copy
-/
import FLTForHuman.NumberTheory.NumberField.FiniteIdeles
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.AdelicModulus

set_option autoImplicit false

open NumberField NumberField.AdeleRing
open IsDedekindDomain NumberField.TateGlobal AutomorphicForm NumberField.AdelicLevel

namespace NumberField.TateGlobal

private theorem norm_le_one_of_mem {F : Type} [Field F] [NumberField F]
    {w : HeightOneSpectrum (𝓞 F)} {x : w.adicCompletion F}
    (hx : x ∈ w.adicCompletionIntegers F) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx)

private theorem norm_one_apply_pow_mult (F : Type) [Field F] [NumberField F]
    (w : InfinitePlace F) : ‖(1 : InfiniteAdeleRing F) w‖ ^ w.mult = 1 := by
  rw [show (1 : InfiniteAdeleRing F) w = 1 from rfl, norm_one, one_pow]

private theorem norm_snd_apply_eq_one {F : Type} [Field F] [NumberField F]
    (u : (AdeleRing (𝓞 F) F)ˣ)
    (hfin : finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F)
    (w : HeightOneSpectrum (𝓞 F)) : ‖(u : AdeleRing (𝓞 F) F).2 w‖ = 1 := by
  obtain ⟨h1, h2⟩ := (IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff _).mp hfin
  have ha : ‖(u : AdeleRing (𝓞 F) F).2 w‖ ≤ 1 := norm_le_one_of_mem (h1 w)
  have hb : ‖((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w‖ ≤ 1 :=
    norm_le_one_of_mem (h2 w)
  have hab : (u : AdeleRing (𝓞 F) F).2 w * ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w
      = 1 :=
    congrArg (fun x : AdeleRing (𝓞 F) F => x.2 w) u.mul_inv
  have hmul := norm_mul ((u : AdeleRing (𝓞 F) F).2 w)
    (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w)
  rw [hab, norm_one] at hmul
  have hge := mul_le_mul_of_nonneg_left hb (norm_nonneg ((u : AdeleRing (𝓞 F) F).2 w))
  exact le_antisymm ha (by linarith)

private theorem norm_coe_uniformizerUnit (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ‖(uniformizerUnit F v : v.adicCompletion F)‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, NumberField.AdelicLevel.valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [WithZero.exp, WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv,
    NNReal.coe_natCast]

theorem ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
    (F : Type) [Field F] [NumberField F] (u : (AdeleRing (𝓞 F) F)ˣ)
    (harch : (u : AdeleRing (𝓞 F) F).1 = 1)
    (hfin : finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F) :
    ideleNorm F u = 1 := by
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, harch,
    Finset.prod_eq_one (fun w _ => norm_one_apply_pow_mult F w), one_mul]
  exact finprod_eq_one_of_forall_eq_one (norm_snd_apply_eq_one u hfin)

theorem ideleNorm_uniformizerIdele (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  have hfst : (uniformizerIdele F v : AdeleRing (𝓞 F) F).1 = 1 := rfl
  have hself : (uniformizerIdele F v : AdeleRing (𝓞 F) F).2 v
      = (uniformizerUnit F v : v.adicCompletion F) :=
    localUnit_apply_self (𝓞 F) F v (uniformizerUnit F v)
  have hne : ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      (uniformizerIdele F v : AdeleRing (𝓞 F) F).2 w = 1 :=
    fun w hw => localUnit_apply_of_ne (𝓞 F) F v (uniformizerUnit F v) hw
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, hfst,
    Finset.prod_eq_one (fun w _ => norm_one_apply_pow_mult F w), one_mul,
    finprod_eq_single _ v (fun w hw => by simp only [hne w hw, norm_one]), hself,
    norm_coe_uniformizerUnit]

end NumberField.TateGlobal
