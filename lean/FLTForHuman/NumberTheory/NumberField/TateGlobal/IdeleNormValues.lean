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

  Two more values of the norm, both at trivial finite part: `ideleNorm` of an idèle whose second
  component is `1` is the archimedean product (`ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one`),
  and every positive real is the norm of such an idèle (`exists_ideleNorm_eq_and_snd_eq_one`) — the
  normalisation the `diagOne` family of Whittaker-coefficient rows needs.

  The pin's two `diagOne` matrix facts are homed here too (`map_diagOne`, `det_diagOne`): a ring
  map commutes with `diagOne`, and `diagOne a` has determinant `a`. They are the helpers of the
  first headline's pin file; that file's own proof reaches the statement through the determinant
  formula of the idèle norm, which lives on this repo's `AutomorphicForm` side — the direction the
  `NumberField` tree may not import — so the headline below is proved directly instead, by the
  finite-`finprod` collapse. The two facts are kept because the pin states them and the
  `diagOne` family consumes them.

  spec-pin: Theorems/Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles.lean
  spec-pin: P2M/Sol/S_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles.lean   -- comparable copy
  spec-pin: Theorems/Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele.lean
  spec-pin: P2M/Sol/S_NumberField_TateGlobal_ideleNorm_uniformizerIdele.lean   -- comparable copy
  spec-pin: Theorems/Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one.lean
  spec-pin: P2M/Sol/S_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one.lean
  spec-pin: Theorems/Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one.lean
  spec-pin: P2M/Sol/S_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one.lean
-/
import FLTForHuman.NumberTheory.NumberField.FiniteIdeles
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen

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

/-- A ring map commutes with the diagonal embedding of the units. -/
theorem map_diagOne {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagOne a) = diagOne (Units.map f.toMonoidHom a) := by
  ext i j
  change f ((diagOne a : Matrix (Fin 2) (Fin 2) A) i j)
    = (diagOne (Units.map f.toMonoidHom a) : Matrix (Fin 2) (Fin 2) B) i j
  rw [diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- The determinant of a diagonal matrix with entry `a` and `1` is `a`. -/
theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  apply Units.ext
  change ((diagOne a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).det = (a : A)
  rw [Matrix.det_fin_two]
  simp [diagOne_coe_apply]

/-- At trivial finite part the idèle norm is the archimedean product. -/
theorem ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
    (K : Type) [Field K] [NumberField K]
    (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) :
    NumberField.TateGlobal.ideleNorm K a =
      ∏ w : InfinitePlace K, ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult := by
  unfold ideleNorm
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, ha]
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one (fun v => by
      rw [show (1 : FiniteAdeleRing (𝓞 K) K) v = 1 from rfl, norm_one])
  rw [hfin, mul_one]

/-- The idèle `(t, 1)` with the prescribed archimedean unit components and trivial finite part. -/
private noncomputable def archIdele (K : Type) [Field K] [NumberField K]
    (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((fun w => ((t w : (w.Completion)ˣ) : w.Completion)), 1)
  inv := ((fun w => (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion)), 1)
  val_inv := by
    refine Prod.ext ?_ ?_
    · funext w
      change ((t w : (w.Completion)ˣ) : w.Completion)
          * (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion) = 1
      exact Units.mul_inv _
    · change (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul 1
  inv_val := by
    refine Prod.ext ?_ ?_
    · funext w
      change (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion)
          * ((t w : (w.Completion)ˣ) : w.Completion) = 1
      exact Units.inv_mul _
    · change (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul 1

private theorem archIdele_fst (K : Type) [Field K] [NumberField K]
    (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    ((archIdele K t : (AdeleRing (𝓞 K) K))).1 w = t w := rfl

private theorem archIdele_snd (K : Type) [Field K] [NumberField K]
    (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    ((archIdele K t : (AdeleRing (𝓞 K) K))).2 = 1 := rfl

private theorem exists_arch_norm_eq (K : Type) [Field K] [NumberField K]
    (r : ℝ) (hr : 0 < r) :
    ∃ t : ∀ w : InfinitePlace K, (w.Completion)ˣ,
      ∀ w, ‖((t w : (w.Completion)ˣ) : w.Completion)‖ = r := by
  have key : ∀ w : InfinitePlace K, ∃ u : (w.Completion)ˣ, ‖(u : w.Completion)‖ = r := by
    intro w
    by_cases hw : w.IsReal
    · let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
      have hnorm : ‖e.symm r‖ = r := by
        have h1 : ‖e.symm r‖ = dist (e.symm r) (e.symm 0) := by
          rw [show e.symm 0 = 0
            from map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm,
            dist_zero_right]
        rw [h1, e.symm.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hr]
      have hne : e.symm r ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; exact hr.ne' hnorm.symm
      exact ⟨Units.mk0 _ hne, hnorm⟩
    · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw'
      have hnorm : ‖e.symm (r : ℂ)‖ = r := by
        have h1 : ‖e.symm (r : ℂ)‖ = dist (e.symm r) (e.symm 0) := by
          rw [show e.symm 0 = 0
            from map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw').symm,
            dist_zero_right]
        rw [h1, e.symm.dist_eq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr]
      have hne : e.symm (r : ℂ) ≠ 0 := fun h => by
        rw [h, norm_zero] at hnorm; exact hr.ne' hnorm.symm
      exact ⟨Units.mk0 _ hne, hnorm⟩
  choose t ht using key
  exact ⟨t, ht⟩

/-- Every positive real is the norm of an idèle with trivial finite part. -/
theorem exists_ideleNorm_eq_and_snd_eq_one
    (K : Type) [Field K] [NumberField K] (r : ℝ) (hr : 0 < r) :
    ∃ z : (AdeleRing (𝓞 K) K)ˣ, ((z : AdeleRing (𝓞 K) K)).2 = 1 ∧ ideleNorm K z = r := by
  classical
  set d : ℕ := Module.finrank ℚ K with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hdpos' : 0 < (d : ℝ) := by exact_mod_cast hdpos
  set ρ : ℝ := r ^ (1 / (d : ℝ)) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hr _
  obtain ⟨t, ht⟩ := exists_arch_norm_eq K ρ hρpos
  refine ⟨archIdele K t, archIdele_snd K t, ?_⟩
  rw [ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _
    (archIdele_snd K t)]
  simp_rw [archIdele_fst, ht]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← hd, hρ, ← Real.rpow_natCast,
    ← Real.rpow_mul hr.le, one_div_mul_cancel hdpos'.ne', Real.rpow_one]

end NumberField.TateGlobal
