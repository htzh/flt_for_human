/-
  The `NumberField.AdelicHeight` layer: the local and adèlic heights on `GL₂`.

  `rowMaxNorm`/`finLocalHeight` are the non-archimedean local height of a `GL₂`-element
  and its reciprocal bound under a global point `globalPoints γ`; `finHeight` is the
  `finprod` of the local heights over the finite places and `adelicHeight` the product of
  `archHeight` and `finHeight`. The two height inequalities
  (`finHeight_globalPoints_mul_mul_finHeight_le`,
  `adelicHeight_globalPoints_mul_mul_adelicHeight_le_one`) and their corollary
  `archHeight_le_of_adelicHeight` are the height bookkeeping behind the adèlic reduction
  and the orbital-integral layer.

  Transcribed whole from `Definitions/Def_NumberField_AdelicHeight.lean`
  (pinned `aa2d8b3`, 323 lines / 24 declarations), the pin's one role module for the
  heights (playbook §2.3). Its prerequisite `Def_AutomorphicForm_SiegelReduction` is the
  port's `FLTForHuman.AutomorphicForm.Adelic.Siegel.Reduction`, and everything else it
  names — `NumberField.FinitePlace.{embedding,equivHeightOneSpectrum,hasFiniteMulSupport,pos_iff}`,
  `NumberField.prod_abs_eq_one`, `NumberField.InfinitePlace.prod_eq_abs_norm` — is mathlib
  `v4.34.0`. The pin's `p2m_*` scaffolding is dropped; no file-wide option beyond
  `set_option autoImplicit false`.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`;
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_NumberField_AdelicHeight.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.Reduction
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace NumberField

namespace AdelicHeight

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates
  AutomorphicForm.SiegelReduction NumberField.AdelicLevel NumberField.InfinitePlace

section Local

variable {K : Type*} [NormedField K]

-- pin: rowMaxNorm (Def_NumberField_AdelicHeight.lean:18)
def rowMaxNorm (M : Matrix (Fin 2) (Fin 2) K) : ℝ := max ‖M 1 0‖ ‖M 1 1‖

-- pin: rowMaxNorm_nonneg (Def_NumberField_AdelicHeight.lean:20)
theorem rowMaxNorm_nonneg (M : Matrix (Fin 2) (Fin 2) K) : 0 ≤ rowMaxNorm M :=
  (norm_nonneg _).trans (le_max_left _ _)

-- pin: rowMaxNorm_pos (Def_NumberField_AdelicHeight.lean:23)
theorem rowMaxNorm_pos (g : GL (Fin 2) K) : 0 < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  by_contra h
  have h0 : rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) = 0 :=
    le_antisymm (not_lt.mp h) (rowMaxNorm_nonneg _)
  have h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    norm_eq_zero.mp (le_antisymm ((le_max_left _ _).trans h0.le) (norm_nonneg _))
  have h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 :=
    norm_eq_zero.mp (le_antisymm ((le_max_right _ _).trans h0.le) (norm_nonneg _))
  have hdet := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two, h10, h11, mul_zero, mul_zero, sub_zero] at hdet
  exact hdet rfl

-- pin: finLocalHeight (Def_NumberField_AdelicHeight.lean:35)
def finLocalHeight (g : GL (Fin 2) K) : ℝ :=
  ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2

-- pin: finLocalHeight_pos (Def_NumberField_AdelicHeight.lean:38)
theorem finLocalHeight_pos (g : GL (Fin 2) K) : 0 < finLocalHeight g :=
  div_pos (norm_pos_iff.mpr (Matrix.isUnits_det_units g).ne_zero) (pow_pos (rowMaxNorm_pos g) 2)

variable [IsUltrametricDist K]

omit [IsUltrametricDist K] in
private theorem coe_mul' (γ g : GL (Fin 2) K) :
    ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl

-- pin: norm_mul_norm_det_le (Def_NumberField_AdelicHeight.lean:48)
theorem norm_mul_norm_det_le (γ g : GL (Fin 2) K) :
    ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖
      ≤ rowMaxNorm ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hid : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 * (g : Matrix (Fin 2) (Fin 2) K).det
      = ((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 0
          * (g : Matrix (Fin 2) (Fin 2) K) 1 1
        + -(((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 1
          * (g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
    simp only [Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [← norm_mul, hid, coe_mul']
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_neg, norm_mul, norm_mul]
  have h1 : ‖((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 0‖
      ≤ rowMaxNorm ((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) :=
    le_max_left _ _
  have h2 : ‖((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 1‖
      ≤ rowMaxNorm ((γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) :=
    le_max_right _ _
  have h3 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) :=
    le_max_right _ _
  have h4 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) :=
    le_max_left _ _
  exact max_le (mul_le_mul h1 h3 (norm_nonneg _) (rowMaxNorm_nonneg _))
    (mul_le_mul h2 h4 (norm_nonneg _) (rowMaxNorm_nonneg _))

-- pin: finLocalHeight_mul_mul_finLocalHeight_le (Def_NumberField_AdelicHeight.lean:75)
theorem finLocalHeight_mul_mul_finLocalHeight_le (γ g : GL (Fin 2) K)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    finLocalHeight (γ * g) * finLocalHeight g
      ≤ ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ / ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 := by
  have hkey := norm_mul_norm_det_le γ g
  have hr1 := rowMaxNorm_pos (γ * g)
  have hr2 := rowMaxNorm_pos g
  have hc : 0 < ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2 := by positivity
  have hdet : ‖((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [coe_mul', Matrix.det_mul, norm_mul]
  unfold finLocalHeight
  rw [hdet, div_mul_div_comm, div_le_div_iff₀ (by positivity) hc]
  have hsq : (‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖) ^ 2
      ≤ (rowMaxNorm ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hkey 2
  calc ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖
        * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ * ‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
      = ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖
          * (‖(γ : Matrix (Fin 2) (Fin 2) K) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖) ^ 2 := by
        ring
    _ ≤ ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖
          * (rowMaxNorm ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
            * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
    _ = ‖(γ : Matrix (Fin 2) (Fin 2) K).det‖
          * (rowMaxNorm ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ 2
            * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ^ 2) := by
        ring

-- pin: norm_det_le_one (Def_NumberField_AdelicHeight.lean:106)
theorem norm_det_le_one {M : Matrix (Fin 2) (Fin 2) K} (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (h 0 0)).trans (h 1 1)
  · rw [norm_neg, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (h 0 1)).trans (h 1 0)

-- pin: finLocalHeight_eq_one (Def_NumberField_AdelicHeight.lean:114)
theorem finLocalHeight_eq_one (g : GL (Fin 2) K)
    (h : ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (h' : ∀ i j, ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight g = 1 := by
  have hd : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h
  have hd' : ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one h'
  have hprod : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← coe_mul', mul_inv_cancel, Units.val_one, Matrix.det_one,
      norm_one]
  have hdet1 : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    refine le_antisymm hd ?_
    by_contra hlt
    push Not at hlt
    have := (mul_le_of_le_one_right (norm_nonneg _) hd').trans_lt hlt
    rw [hprod] at this
    exact lt_irrefl _ this
  have hrow_le : rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) ≤ 1 := max_le (h 1 0) (h 1 1)
  have hrow_ge : 1 ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    by_contra hlt
    push Not at hlt
    have h10 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ < 1 := (le_max_left _ _).trans_lt hlt
    have h11 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ < 1 := (le_max_right _ _).trans_lt hlt
    have hlt' : ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ < 1 := by
      rw [Matrix.det_fin_two, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (h 0 0)).trans_lt h11
      · rw [norm_neg, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (h 0 1)).trans_lt h10
    rw [hdet1] at hlt'
    exact lt_irrefl _ hlt'
  unfold finLocalHeight
  rw [hdet1, le_antisymm hrow_le hrow_ge, one_pow, div_one]

end Local

section Adelic

variable (F : Type) [Field F] [NumberField F]

-- pin: finHeight (Def_NumberField_AdelicHeight.lean:155)
def finHeight (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), finLocalHeight (finComponent (𝓞 F) F v g)

-- pin: adelicHeight (Def_NumberField_AdelicHeight.lean:158)
def adelicHeight (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  archHeight F (glArch (𝓞 F) F g) * finHeight F (glFin (𝓞 F) F g)

variable {F}

-- pin: norm_le_one_of_mem_adicCompletionIntegers (Def_NumberField_AdelicHeight.lean:163)
theorem norm_le_one_of_mem_adicCompletionIntegers {v : HeightOneSpectrum (𝓞 F)}
    {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) : ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hx)

-- pin: finLocalHeight_finComponent_eventually_eq_one (Def_NumberField_AdelicHeight.lean:168)
theorem finLocalHeight_finComponent_eventually_eq_one (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      finLocalHeight (finComponent (𝓞 F) F v g) = 1 := by
  have hg : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hg' : ∀ i j, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F :=
    fun i j => (((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j).2
  have hall : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v
        ∈ v.adicCompletionIntegers F)
      ∧ ∀ i j, ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j v ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg i)).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hg' i))
  filter_upwards [hall] with v hv
  refine finLocalHeight_eq_one _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.1 i j)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hv.2 i j)

-- pin: hasFiniteMulSupport_finLocalHeight (Def_NumberField_AdelicHeight.lean:193)
theorem hasFiniteMulSupport_finLocalHeight (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (fun v : HeightOneSpectrum (𝓞 F) =>
      finLocalHeight (finComponent (𝓞 F) F v g)).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp (finLocalHeight_finComponent_eventually_eq_one g)

-- pin: finHeight_pos (Def_NumberField_AdelicHeight.lean:198)
theorem finHeight_pos (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : 0 < finHeight F g :=
  finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun _ => finLocalHeight_pos _

-- pin: adelicHeight_pos (Def_NumberField_AdelicHeight.lean:201)
theorem adelicHeight_pos (g : AdelicGL2 (𝓞 F) F) : 0 < adelicHeight F g :=
  mul_pos (archHeight_pos F _) (finHeight_pos _)

-- pin: finHeight_eq_one_of_mem (Def_NumberField_AdelicHeight.lean:204)
theorem finHeight_eq_one_of_mem {g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hg : g ∈ finiteIntegralGL2 (𝓞 F) F) : finHeight F g = 1 := by
  rw [mem_finiteIntegralGL2_iff] at hg
  refine finprod_eq_one_of_forall_eq_one fun v =>
    finLocalHeight_eq_one _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hg.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hg.2 i j v)

-- pin: adelicHeight_eq_archHeight_of_mem (Def_NumberField_AdelicHeight.lean:214)
theorem adelicHeight_eq_archHeight_of_mem {g : AdelicGL2 (𝓞 F) F}
    (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F) :
    adelicHeight F g = archHeight F (glArch (𝓞 F) F g) := by
  rw [adelicHeight, finHeight_eq_one_of_mem hg, mul_one]

-- pin: finComponent_globalPoints_eq (Def_NumberField_AdelicHeight.lean:219)
theorem finComponent_globalPoints_eq (v : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin 2) F) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = (FinitePlace.embedding v).mapMatrix (γ : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  rfl

-- pin: finComponent_globalPoints_apply (Def_NumberField_AdelicHeight.lean:226)
theorem finComponent_globalPoints_apply (v : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin 2) F)
    (i j : Fin 2) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      = FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F) i j) := by
  rw [finComponent_globalPoints_eq]
  rfl

-- pin: det_finComponent_globalPoints (Def_NumberField_AdelicHeight.lean:234)
theorem det_finComponent_globalPoints (v : HeightOneSpectrum (𝓞 F)) (γ : GL (Fin 2) F) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      = FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F).det) := by
  rw [finComponent_globalPoints_eq, ← RingHom.map_det]

-- pin: norm_embedding_eq_equiv_symm (Def_NumberField_AdelicHeight.lean:240)
theorem norm_embedding_eq_equiv_symm (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    ‖FinitePlace.embedding v x‖ = (FinitePlace.equivHeightOneSpectrum.symm v) x := rfl

-- pin: hasFiniteMulSupport_norm_embedding (Def_NumberField_AdelicHeight.lean:243)
theorem hasFiniteMulSupport_norm_embedding {x : F} (hx : x ≠ 0) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖FinitePlace.embedding v x‖).HasFiniteMulSupport :=
  (FinitePlace.hasFiniteMulSupport hx).fun_comp_of_injective
    FinitePlace.equivHeightOneSpectrum.symm.injective

-- pin: finprod_norm_embedding (Def_NumberField_AdelicHeight.lean:248)
theorem finprod_norm_embedding (x : F) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v x‖ = ∏ᶠ w : FinitePlace F, w x :=
  finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm (f := fun w : FinitePlace F => w x)

-- pin: finHeight_globalPoints_mul_mul_finHeight_le (Def_NumberField_AdelicHeight.lean:252)
theorem finHeight_globalPoints_mul_mul_finHeight_le (γ : GL (Fin 2) F)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) * finHeight F h
      ≤ (∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F).det))
          / (∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0)) ^ 2 := by
  have hdet0 : (γ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  set fA := fun v : HeightOneSpectrum (𝓞 F) =>
    finLocalHeight (finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * h)) with hfAdef
  set fB := fun v : HeightOneSpectrum (𝓞 F) => finLocalHeight (finComponent (𝓞 F) F v h) with hfBdef
  set nD := fun v : HeightOneSpectrum (𝓞 F) =>
    ‖FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F).det)‖ with hnDdef
  set nE := fun v : HeightOneSpectrum (𝓞 F) =>
    ‖FinitePlace.embedding v ((γ : Matrix (Fin 2) (Fin 2) F) 1 0)‖ with hnEdef
  have hfA : fA.HasFiniteMulSupport := hasFiniteMulSupport_finLocalHeight _
  have hfB : fB.HasFiniteMulSupport := hasFiniteMulSupport_finLocalHeight _
  have hnD : nD.HasFiniteMulSupport := hasFiniteMulSupport_norm_embedding hdet0
  have hnE : nE.HasFiniteMulSupport := hasFiniteMulSupport_norm_embedding hγ
  have hle : ∀ v, fA v * fB v ≤ nD v / nE v ^ 2 := by
    intro v
    have h10 : ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0
          ≠ 0 := by
      rw [finComponent_globalPoints_apply, ← norm_pos_iff, norm_embedding_eq_equiv_symm]
      exact FinitePlace.pos_iff.mpr hγ
    have hv := finLocalHeight_mul_mul_finLocalHeight_le _ (finComponent (𝓞 F) F v h) h10
    rw [det_finComponent_globalPoints, finComponent_globalPoints_apply, ← map_mul] at hv
    exact hv
  have hnn : ∀ v, 0 ≤ fA v * fB v := fun v =>
    mul_nonneg (finLocalHeight_pos _).le (finLocalHeight_pos _).le
  calc finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) * finHeight F h
      = ∏ᶠ v, fA v * fB v := (finprod_mul_distrib hfA hfB).symm
    _ ≤ ∏ᶠ v, nD v / nE v ^ 2 :=
        finprod_le_finprod₀ (hfA.mul hfB) hnn
          (show (fun v => nD v / nE v ^ 2).HasFiniteMulSupport from hnD.div (hnE.pow 2)) hle
    _ = (∏ᶠ v, nD v) / (∏ᶠ v, nE v) ^ 2 := by
        have hnEsq : (fun v => nE v ^ 2).HasFiniteMulSupport := hnE.pow 2
        rw [finprod_div_distrib hnD hnEsq, finprod_pow hnE 2]
    _ = (∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F).det))
          / (∏ᶠ w : FinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0)) ^ 2 := by
        rw [hnDdef, hnEdef, finprod_norm_embedding, finprod_norm_embedding]

-- pin: adelicHeight_globalPoints_mul_mul_adelicHeight_le_one (Def_NumberField_AdelicHeight.lean:293)
theorem adelicHeight_globalPoints_mul_mul_adelicHeight_le_one (γ : GL (Fin 2) F)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (globalPoints (𝓞 F) F γ * g) * adelicHeight F g ≤ 1 := by
  have hdet0 : (γ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  have hA := archHeight_globalPoints_mul_mul_archHeight_le F γ hγ (glArch (𝓞 F) F g)
  rw [← Rat.cast_abs, ← Rat.cast_abs, ← prod_eq_abs_norm, ← prod_eq_abs_norm] at hA
  have hB := finHeight_globalPoints_mul_mul_finHeight_le γ hγ (glFin (𝓞 F) F g)
  have hBnn : 0 ≤ finHeight F (glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * glFin (𝓞 F) F g)
      * finHeight F (glFin (𝓞 F) F g) := mul_nonneg (finHeight_pos _).le (finHeight_pos _).le
  have hQnn : 0 ≤ (∏ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F).det) ^ w.mult)
      / (∏ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) ^ w.mult) ^ 2 := by
    positivity
  unfold adelicHeight
  rw [map_mul, map_mul, mul_mul_mul_comm]
  refine (mul_le_mul hA hB hBnn hQnn).trans (le_of_eq ?_)
  rw [div_mul_div_comm, ← mul_pow, prod_abs_eq_one hdet0, prod_abs_eq_one hγ, one_pow, div_one]

-- pin: archHeight_le_of_adelicHeight (Def_NumberField_AdelicHeight.lean:310)
theorem archHeight_le_of_adelicHeight {γ : GL (Fin 2) F}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F)
    (hγg : glFin (𝓞 F) F (globalPoints (𝓞 F) F γ * g) ∈ finiteIntegralGL2 (𝓞 F) F) :
    archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ * g)) * archHeight F (glArch (𝓞 F) F g)
      ≤ 1 := by
  have h := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hγ g
  rwa [adelicHeight_eq_archHeight_of_mem hγg, adelicHeight_eq_archHeight_of_mem hg] at h

end Adelic

end AdelicHeight

end NumberField
