/-
  The (central) slab-covering engine (tier 3, unlisted).

  The shared proof body behind the three pin ready nodes
  `AutomorphicForm.exists_finset_{central_,}slab_covering_of_coversModCentre[_centreCutSiegelSetAmple]`.
  The pinned repository carries the whole development inside each of three
  self-contained `S_` files (2,783 raw lines, 69 declaration groups, 1,213 net new
  lines after dedup); here its shared prelude is transcribed once, `private`, and the
  three `solution` kernels are public at `AutomorphicForm.SiegelCovering.Engine.<name>`
  with their `Theorems/` wrapper statements.

  The engine is the adelic Siegel covering of `GL₂(𝔸_F)` over a windowed-Siegel
  parameter range: the norm-one idèles decompose into a principal part, an open shell
  and a finite set (`exists_finset_normOne_decomposition`), the shells telescope into a
  finite decomposition of any norm window (`exists_finset_shell_decomposition`), and a
  central scalar normalises the archimedean determinant height to `d₂`
  (`exists_centralScalar_mul_mem_archDetNorm_eq`), assembling a finite covering
  (`central_assembled`).

  Two landed reuse edges are imported, not re-proved:
  `NumberField.TateGlobal.ideleNorm_archUnitHom` and
  `NumberField.TateGlobal.exists_norm_pow_mult_eq`
  (`FLTForHuman/NumberTheory/NumberField/TateGlobal/ArchNorm.lean`). The pin's slab copy
  of `exists_norm_pow_mult_eq` has `r` implicit while the landed lemma takes it
  explicitly, so the pin's `exists_norm_pow_mult_eq v hr` call sites become
  `exists_norm_pow_mult_eq v r hr`.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3` (Lean `v4.33.1` / mathlib
  `db584cd6`); port mathlib `v4.34.0`.
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.lean

  The ample file's copies of `exists_centralScalar_mul_mem_archDetNorm_eq`, `pointShape`
  and `mul_centralScalar_mem_of_mem_shellIdeles` share the name but not the statement of
  the central/slab copies (they are stated over `centreCutSiegelSetAmple`); they are
  written once here, generalised over the set `S` with the two set-specific inputs
  (`hwin`, `hmul`), so each shared name occurs a single time.
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.Covering
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSiegelSetAmple
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ArchNorm
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.NumberField.TateGlobalCompactness

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicLevel
open NumberField.AdelicVolume
open NumberField.AdelicCentre
open NumberField.AdelicHaar
open NumberField.TateGlobal
open Set
open AutomorphicForm.WindowedSiegel
open scoped MatrixGroups NNReal

namespace AutomorphicForm.SiegelCovering

section DecompositionAndNormalisation

variable (F : Type) [Field F] [NumberField F]

-- pin: archDetNorm_mul (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:26)
private theorem archDetNorm_mul (w : InfinitePlace F) (g h : AdelicGL2 (𝓞 F) F) :
    archDetNorm w (g * h) = archDetNorm w g * archDetNorm w h := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

variable {F}

-- pin: centralScalar_mul_comm (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:33)
private theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * g = g * centralScalar (𝓞 F) F z := by
  have hz : centralScalar (𝓞 F) F z ∈ Subgroup.center (GL (Fin 2) (AdeleRing (𝓞 F) F)) := by
    rw [NumberField.AdelicCentre.center_eq_range_scalar]
    exact ⟨z, rfl⟩
  exact (Subgroup.mem_center_iff.mp hz g).symm

-- pin: archDetNorm_centralScalar (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:40)
private theorem archDetNorm_centralScalar (v : InfinitePlace F) (w : (AdeleRing (𝓞 F) F)ˣ) :
    archDetNorm v (centralScalar (𝓞 F) F w)
      = ‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖ := by
  unfold archDetNorm
  set s := archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F w))
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) v.Completion) i j
      = if i = j then (w : AdeleRing (𝓞 F) F).1 v else 0 := by
    intro i j
    simp only [s, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, ite_eq_left rfl]
    · rw [centralScalar_apply_ne _ h, ite_eq_right h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

-- pin: archDetNorm_centralScalar_mul' (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:57)
private theorem archDetNorm_centralScalar_mul' (v : InfinitePlace F) (w : (AdeleRing (𝓞 F) F)ˣ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v (centralScalar (𝓞 F) F w * g)
      = (‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖) * archDetNorm v g := by
  rw [archDetNorm_mul F, archDetNorm_centralScalar]

omit [NumberField F] in

-- pin: exists_norm_eq (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:65)
private theorem exists_norm_eq (v : InfinitePlace F) {r : ℝ} (hr : 0 < r) :
    ∃ a : v.Completion, a ≠ 0 ∧ ‖a‖ = r := by
  rcases InfinitePlace.isReal_or_isComplex v with hv | hv
  · refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r, ?_, ?_⟩
    · rw [ne_eq, ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm,
        (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.injective.eq_iff]
      exact hr.ne'
    · have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
        (map_zero _) ((InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm r)
      rw [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hv, RingEquiv.apply_symm_apply,
        Real.norm_eq_abs, abs_of_pos hr] at h
      exact h.symm
  · refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm (r : ℂ), ?_, ?_⟩
    · rw [ne_eq, ← map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm,
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.injective.eq_iff,
        Complex.ofReal_eq_zero]
      exact hr.ne'
    · have h := (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
        (map_zero _) ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm (r : ℂ))
      rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hv, RingEquiv.apply_symm_apply,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
      exact h.symm

omit [NumberField F] in

-- pin: exists_norm_mul_self_eq (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:90)
private theorem exists_norm_mul_self_eq (v : InfinitePlace F) {r : ℝ} (hr : 0 < r) :
    ∃ a : v.Completion, a ≠ 0 ∧ ‖a‖ * ‖a‖ = r := by
  obtain ⟨a, ha0, ha⟩ := exists_norm_eq v (Real.sqrt_pos.mpr hr)
  exact ⟨a, ha0, by rw [ha, Real.mul_self_sqrt hr.le]⟩

variable (F) in

-- pin: archIdele (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:108)
private def archIdele (a : ∀ v : InfinitePlace F, (v.Completion)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (fun v => (a v : v.Completion), 1)
  inv := (fun v => ((a v)⁻¹ : (v.Completion)ˣ), 1)
  val_inv := Prod.ext (funext fun v => Units.mul_inv (a v)) (one_mul 1)
  inv_val := Prod.ext (funext fun v => Units.inv_mul (a v)) (one_mul 1)

-- pin: archIdele_fst (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:114)
private theorem archIdele_fst (a : ∀ v : InfinitePlace F, (v.Completion)ˣ) (v : InfinitePlace F) :
    ((archIdele F a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v = a v := rfl

-- pin: archIdele_snd (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:117)
private theorem archIdele_snd (a : ∀ v : InfinitePlace F, (v.Completion)ˣ) :
    ((archIdele F a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl

-- pin: archIdele_inv_snd (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:120)
private theorem archIdele_inv_snd (a : ∀ v : InfinitePlace F, (v.Completion)ˣ) :
    (((archIdele F a)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl

-- pin: glFin_centralScalar_of_snd_eq_one (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:123)
private theorem glFin_centralScalar_of_snd_eq_one {w : (AdeleRing (𝓞 F) F)ˣ}
    (hwf : (w : AdeleRing (𝓞 F) F).2 = 1) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F w) = 1 :=
  glFin_scalar_eq_one F hwf (centralScalar_apply_eq w 0) (centralScalar_apply_ne w (by decide))
    (centralScalar_apply_ne w (by decide)) (centralScalar_apply_eq w 1)

-- pin: glFin_centralScalar_mem_finiteIntegralGL2 (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:129)
private theorem glFin_centralScalar_mem_finiteIntegralGL2 {w : (AdeleRing (𝓞 F) F)ˣ}
    (h₁ : (w : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F)
    (h₂ : ((w⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F w) ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq]
      exact h₁
    · rw [centralScalar_apply_ne _ h]
      exact zero_mem_integralFiniteAdeles
  · rw [← map_inv, ← map_inv, glFin_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq]
      exact h₂
    · rw [centralScalar_apply_ne _ h]
      exact zero_mem_integralFiniteAdeles

-- pin: centralScalar_mul_mem_centreCutSiegelSet (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:150)
private theorem centralScalar_mul_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} {w : (AdeleRing (𝓞 F) F)ˣ}
    (hwK : glFin (𝓞 F) F (centralScalar (𝓞 F) F w) ∈ finiteIntegralGL2 (𝓞 F) F)
    (hwa : ∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0)
    {h : AdelicGL2 (𝓞 F) F} (hh : h ∈ centreCutSiegelSet F c u d₁ d₂)
    (hdet : ∀ v : InfinitePlace F, archDetNorm v (centralScalar (𝓞 F) F w * h) ∈ Set.Icc d₁ d₂) :
    centralScalar (𝓞 F) F w * h ∈ centreCutSiegelSet F c u d₁ d₂ := by
  obtain ⟨hK, hfloor, hwin, -⟩ := hh
  have hdiag : ∀ (v : InfinitePlace F) (i : Fin 2),
      ((archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F w)) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion) i i = (w : AdeleRing (𝓞 F) F).1 v := by
    intro v i
    simp only [archComponent_apply, glArch_apply]
    rw [centralScalar_apply_eq]
  have hoff : ∀ (v : InfinitePlace F) (i j : Fin 2), i ≠ j →
      ((archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F w)) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion) i j = 0 := by
    intro v i j hij
    simp only [archComponent_apply, glArch_apply]
    rw [centralScalar_apply_ne _ hij]
    rfl
  refine ⟨?_, fun v => ?_, fun v => ?_, hdet⟩
  · rw [map_mul]
    exact Subgroup.mul_mem _ hwK hK
  · have h00 := hdiag v 0
    have h11 := hdiag v 1
    have h01 := hoff v 0 1 (by decide)
    have h10 := hoff v 1 0 (by decide)
    rw [map_mul, map_mul, localHeight_scalar_entries_mul (hwa v) h00 h01 h10 h11]
    exact hfloor v
  · have h00 := hdiag v 0
    have h11 := hdiag v 1
    have h01 := hoff v 0 1 (by decide)
    have h10 := hoff v 1 0 (by decide)
    rw [map_mul, map_mul, xWindowSq_scalar_entries_mul (hwa v) h00 h01 h10 h11]
    exact hwin v

-- pin: centralScalar_mul_mem_centreCutSiegelSetAmple (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean:189)
private theorem centralScalar_mul_mem_centreCutSiegelSetAmple {c u d₁ d₂ κ : ℝ} {w : (AdeleRing (𝓞 F) F)ˣ}
    (hwK : glFin (𝓞 F) F (centralScalar (𝓞 F) F w) ∈ finiteIntegralGL2 (𝓞 F) F)
    (hwa : ∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0)
    {h : AdelicGL2 (𝓞 F) F} (hh : h ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ)
    (hdet : ∀ v : InfinitePlace F, archDetNorm v (centralScalar (𝓞 F) F w * h) ∈ Set.Icc d₁ d₂) :
    centralScalar (𝓞 F) F w * h ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ := by
  obtain ⟨hhS, hratio⟩ := hh
  have hdiag : ∀ (v : InfinitePlace F) (i : Fin 2),
      ((archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F w)) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion) i i = (w : AdeleRing (𝓞 F) F).1 v := by
    intro v i
    simp only [archComponent_apply, glArch_apply]
    rw [centralScalar_apply_eq]
  have hoff : ∀ (v : InfinitePlace F) (i j : Fin 2), i ≠ j →
      ((archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F w)) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion) i j = 0 := by
    intro v i j hij
    simp only [archComponent_apply, glArch_apply]
    rw [centralScalar_apply_ne _ hij]
    rfl
  have hkey : ∀ v : InfinitePlace F,
      localHeight (archComponent F v (glArch (𝓞 F) F (centralScalar (𝓞 F) F w * h))) =
        localHeight (archComponent F v (glArch (𝓞 F) F h)) := by
    intro v
    rw [map_mul, map_mul,
      localHeight_scalar_entries_mul (hwa v) (hdiag v 0) (hoff v 0 1 (by decide)) (hoff v 1 0 (by decide))
        (hdiag v 1)]
  refine ⟨centralScalar_mul_mem_centreCutSiegelSet hwK hwa hhS hdet, fun v v' => ?_⟩
  rw [hkey v, hkey v']
  exact hratio v v'

-- pin: exists_centralScalar_mul_mem_archDetNorm_eq (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:186)
-- pin: exists_centralScalar_mul_mem_archDetNorm_eq (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean:220)
private theorem exists_centralScalar_mul_mem_archDetNorm_eq {S : Set (AdelicGL2 (𝓞 F) F)} {d₁ d₂ : ℝ}
    (hwin : ∀ h ∈ S, ∀ v : InfinitePlace F, archDetNorm v h ∈ Set.Icc d₁ d₂)
    (hmul : ∀ (w : (AdeleRing (𝓞 F) F)ˣ),
      glFin (𝓞 F) F (centralScalar (𝓞 F) F w) ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0) →
      ∀ h ∈ S, (∀ v : InfinitePlace F,
          archDetNorm v (centralScalar (𝓞 F) F w * h) ∈ Set.Icc d₁ d₂) →
        centralScalar (𝓞 F) F w * h ∈ S) :
    ∀ h ∈ S, ∃ a : (AdeleRing (𝓞 F) F)ˣ, (a : AdeleRing (𝓞 F) F).2 = 1 ∧
      centralScalar (𝓞 F) F a * h ∈ S ∧
      ∀ v : InfinitePlace F, archDetNorm v (centralScalar (𝓞 F) F a * h) = d₂ := by
  intro h hh
  have hwindow : ∀ v : InfinitePlace F, archDetNorm v h ∈ Set.Icc d₁ d₂ := hwin h hh
  have hratio : ∀ v : InfinitePlace F, 0 < d₂ / archDetNorm v h := fun v =>
    div_pos ((archDetNorm_pos v h).trans_le (hwindow v).2) (archDetNorm_pos v h)
  choose t ht0 ht using fun v : InfinitePlace F => exists_norm_mul_self_eq v (hratio v)
  set a : (AdeleRing (𝓞 F) F)ˣ := archIdele F fun v => Units.mk0 (t v) (ht0 v) with ha
  have hdet : ∀ v : InfinitePlace F, archDetNorm v (centralScalar (𝓞 F) F a * h) = d₂ := by
    intro v
    rw [archDetNorm_centralScalar_mul', ha, archIdele_fst, Units.val_mk0, ht v,
      div_mul_cancel₀ _ (archDetNorm_pos v h).ne']
  have ha2 : (a : AdeleRing (𝓞 F) F).2 = 1 := by rw [ha]; exact archIdele_snd _
  refine ⟨a, ha2, ?_, hdet⟩
  refine hmul a ?_ (fun v => ?_) h hh (fun v => ?_)
  · rw [glFin_centralScalar_of_snd_eq_one ha2]
    exact Subgroup.one_mem _
  · rw [ha, archIdele_fst, Units.val_mk0]
    exact ht0 v
  · rw [hdet v]
    exact ⟨(hwindow v).1.trans (hwindow v).2, le_rfl⟩

-- pin: pointShape (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:210)
-- pin: pointShape (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean:244)
private theorem pointShape {S : Set (AdelicGL2 (𝓞 F) F)} {d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hwin : ∀ h ∈ S, ∀ v : InfinitePlace F, archDetNorm v h ∈ Set.Icc d₁ d₂)
    (hmul : ∀ (w : (AdeleRing (𝓞 F) F)ˣ),
      glFin (𝓞 F) F (centralScalar (𝓞 F) F w) ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0) →
      ∀ h ∈ S, (∀ v : InfinitePlace F,
          archDetNorm v (centralScalar (𝓞 F) F w * h) ∈ Set.Icc d₁ d₂) →
        centralScalar (𝓞 F) F w * h ∈ S)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' S)) :
    ∀ g : AdelicGL2 (𝓞 F) F, ∃ (γ : GL (Fin 2) F) (z : (AdeleRing (𝓞 F) F)ˣ)
      (h x : AdelicGL2 (𝓞 F) F), x ∈ T ∧ h ∈ S ∧
        (∀ v : InfinitePlace F, archDetNorm v h = d₂) ∧
        globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z = h * x := by
  intro g
  obtain ⟨γ, z, hz⟩ := hcov g
  rw [Set.mem_iUnion₂] at hz
  obtain ⟨x, hxT, h₀, hh₀, hrel⟩ := hz
  have hrel' : h₀ * x = globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z := hrel
  obtain ⟨a, -, hah, hadet⟩ := exists_centralScalar_mul_mem_archDetNorm_eq hwin hmul h₀ hh₀
  refine ⟨γ, z * a, centralScalar (𝓞 F) F a * h₀, x, hxT, hah, hadet, ?_⟩
  rw [map_mul, ← mul_assoc, ← hrel', mul_assoc, ← centralScalar_mul_comm a x, ← mul_assoc,
    centralScalar_mul_comm a h₀]

-- pin: shellIdeles (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:226)
private def shellIdeles (ρ : ℝ) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {w | ((w : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F ∧
      ((w⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F) ∧
    ∀ v : InfinitePlace F, ‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖ ∈ Set.Icc ρ 1}

-- pin: mul_centralScalar_mem_of_mem_shellIdeles (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:231)
-- pin: mul_centralScalar_mem_of_mem_shellIdeles (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean:265)
private theorem mul_centralScalar_mem_of_mem_shellIdeles {S : Set (AdelicGL2 (𝓞 F) F)} {d₁ d₂ ρ : ℝ}
    (hρ : 0 < ρ) (hρd : d₁ ≤ ρ * d₂)
    (hmul : ∀ (w : (AdeleRing (𝓞 F) F)ˣ),
      glFin (𝓞 F) F (centralScalar (𝓞 F) F w) ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0) →
      ∀ h ∈ S, (∀ v : InfinitePlace F,
          archDetNorm v (centralScalar (𝓞 F) F w * h) ∈ Set.Icc d₁ d₂) →
        centralScalar (𝓞 F) F w * h ∈ S)
    {h : AdelicGL2 (𝓞 F) F} (hh : h ∈ S)
    (hd : ∀ v : InfinitePlace F, archDetNorm v h = d₂)
    {w : (AdeleRing (𝓞 F) F)ˣ} (hw : w ∈ shellIdeles (F := F) ρ) :
    h * centralScalar (𝓞 F) F w ∈ S := by
  obtain ⟨⟨hw₁, hw₂⟩, hwa⟩ := hw
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hd₂ : 0 < d₂ := by
    rw [← hd v₀]
    exact archDetNorm_pos v₀ h
  rw [← centralScalar_mul_comm]
  refine hmul w (glFin_centralScalar_mem_finiteIntegralGL2 hw₁ hw₂) (fun v => ?_) h hh (fun v => ?_)
  · intro h0
    have := (hwa v).1
    rw [h0, norm_zero, mul_zero] at this
    exact absurd this (not_le.mpr hρ)
  · rw [archDetNorm_centralScalar_mul', hd v]
    refine ⟨hρd.trans (mul_le_mul_of_nonneg_right (hwa v).1 hd₂.le), ?_⟩
    calc (‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖) * d₂
        ≤ 1 * d₂ := mul_le_mul_of_nonneg_right (hwa v).2 hd₂.le
      _ = d₂ := one_mul d₂

variable (F) in

-- pin: ideleNorm_one (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:255)
private theorem ideleNorm_one : ideleNorm F (1 : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  simp [ideleNorm]

-- pin: ideleNorm_inv (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:258)
private theorem ideleNorm_inv (x : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F x⁻¹ = (ideleNorm F x)⁻¹ := by
  have h := ideleNorm_mul x x⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

-- pin: archUnitHom_snd (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:263)
private theorem archUnitHom_snd (w₀ : InfinitePlace F) (t : (w₀.Completion)ˣ) :
    ((archUnitHom w₀ t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  rw [archUnitHom_apply]
  exact archCentralUnit_snd w₀ t

-- pin: archUnitHom_fst_self (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:268)
private theorem archUnitHom_fst_self (w₀ : InfinitePlace F) (t : (w₀.Completion)ˣ) :
    ((archUnitHom w₀ t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w₀ = t := by
  rw [archUnitHom_apply]
  exact archCentralUnit_fst_self w₀ t

-- pin: archUnitHom_fst_of_ne (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:273)
private theorem archUnitHom_fst_of_ne (w₀ : InfinitePlace F) (t : (w₀.Completion)ˣ) {v : InfinitePlace F}
    (hv : v ≠ w₀) :
    ((archUnitHom w₀ t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v = 1 := by
  rw [archUnitHom_apply]
  exact archCentralUnit_fst_of_ne w₀ t hv

omit [NumberField F] in

-- pin: norm_mul_self_mem_of_norm_pow_mult_mem (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:297)
private theorem norm_mul_self_mem_of_norm_pow_mult_mem (v : InfinitePlace F) {b : v.Completion} {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (hb : ‖b‖ ^ v.mult ∈ Set.Icc s 1) :
    ‖b‖ * ‖b‖ ∈ Set.Icc (s * s) 1 := by
  rcases InfinitePlace.isReal_or_isComplex v with hv | hv
  · rw [InfinitePlace.mult, ite_eq_left hv, pow_one] at hb
    exact ⟨mul_le_mul hb.1 hb.1 hs₀ (norm_nonneg _), (mul_le_of_le_one_left (norm_nonneg b) hb.2).trans hb.2⟩
  · rw [InfinitePlace.mult, ite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hv), sq] at hb
    exact ⟨(mul_le_of_le_one_right hs₀ hs₁).trans hb.1, hb.2⟩

variable (F) in

-- pin: openShell (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:308)
private def openShell (σ : ℝ) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {w | (w : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F} ∩
    {w | ((w⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F} ∩
    ⋂ v : InfinitePlace F,
      {w | ‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖ ∈ Set.Ioo σ 1}

-- pin: mem_openShell_iff (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:314)
private theorem mem_openShell_iff {σ : ℝ} {w : (AdeleRing (𝓞 F) F)ˣ} :
    w ∈ openShell F σ ↔
      ((w : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F ∧
        ((w⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈ integralFiniteAdeles (𝓞 F) F) ∧
      ∀ v : InfinitePlace F,
        ‖(w : AdeleRing (𝓞 F) F).1 v‖ * ‖(w : AdeleRing (𝓞 F) F).1 v‖ ∈ Set.Ioo σ 1 := by
  simp only [openShell, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

-- pin: isOpen_openShell (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:322)
private theorem isOpen_openShell (σ : ℝ) : IsOpen (openShell F σ) := by
  unfold openShell
  have hval : Continuous fun w : (AdeleRing (𝓞 F) F)ˣ => (w : AdeleRing (𝓞 F) F) := Units.continuous_val
  have hinv : Continuous fun w : (AdeleRing (𝓞 F) F)ˣ => ((w⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) :=
    Units.continuous_coe_inv
  refine ((?_ : IsOpen _).inter (?_ : IsOpen _)).inter (isOpen_iInter_of_finite fun v => ?_)
  · exact (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_snd.comp hval)
  · exact (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_snd.comp hinv)
  · have hv : Continuous fun w : (AdeleRing (𝓞 F) F)ˣ => (w : AdeleRing (𝓞 F) F).1 v :=
      (continuous_archEval F v).comp (continuous_fst.comp hval)
    exact isOpen_Ioo.preimage (hv.norm.mul hv.norm)

-- pin: exists_mem_openShell (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:334)
private theorem exists_mem_openShell {σ : ℝ} (hσ₀ : 0 ≤ σ) (hσ₁ : σ < 1) : ∃ s, s ∈ openShell F σ := by
  have hmid : 0 < (σ + 1) / 2 := by linarith
  choose a ha0 ha using fun v : InfinitePlace F => exists_norm_mul_self_eq v hmid
  refine ⟨archIdele F fun v => Units.mk0 (a v) (ha0 v), mem_openShell_iff.mpr ⟨⟨?_, ?_⟩, fun v => ?_⟩⟩
  · rw [archIdele_snd]
    exact one_mem_integralFiniteAdeles
  · rw [archIdele_inv_snd]
    exact one_mem_integralFiniteAdeles
  · rw [archIdele_fst, Units.val_mk0, ha v]
    exact ⟨by linarith, by linarith⟩

-- pin: openShell_subset_shellIdeles (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:345)
private theorem openShell_subset_shellIdeles (σ : ℝ) : openShell F σ ⊆ shellIdeles (F := F) σ := by
  intro w hw
  obtain ⟨hfin, harch⟩ := mem_openShell_iff.mp hw
  exact ⟨hfin, fun v => Set.Ioo_subset_Icc_self (harch v)⟩

variable (F) in

-- pin: exists_finset_normOne_decomposition (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:352)
private theorem exists_finset_normOne_decomposition {σ : ℝ} (hσ₀ : 0 ≤ σ) (hσ₁ : σ < 1) :
    ∃ K : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ y ∈ normOneIdeles F,
      ∃ a : Fˣ, ∃ v ∈ openShell F σ, ∃ k ∈ K,
        y = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a * v * k := by
  classical
  obtain ⟨s, hs⟩ := exists_mem_openShell (F := F) hσ₀ hσ₁
  have := NumberField.TateGlobal.compactSpace_normOneIdeleClass F
  let P : Subgroup (normOneIdeles F) := (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F)
  let U : normOneIdeles F ⧸ P → Set (normOneIdeles F ⧸ P) := fun q =>
    (QuotientGroup.mk : normOneIdeles F → normOneIdeles F ⧸ P) ''
      {y : normOneIdeles F | (y : (AdeleRing (𝓞 F) F)ˣ) ∈
        (fun w => ((q.out : (AdeleRing (𝓞 F) F)ˣ) * s⁻¹) * w) '' openShell F σ}
  have hU : ∀ q, U q ∈ nhds q := by
    intro q
    refine IsOpen.mem_nhds (QuotientGroup.isOpenMap_coe _ ?_) ⟨q.out, ⟨s, hs, ?_⟩, QuotientGroup.out_eq' q⟩
    · exact (isOpenMap_mul_left _ _ (isOpen_openShell (F := F) σ)).preimage continuous_subtype_val
    · exact inv_mul_cancel_right _ s
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U hU
  refine ⟨t.image fun q => (q.out : (AdeleRing (𝓞 F) F)ˣ) * s⁻¹, fun y hy => ?_⟩
  have hmem : (QuotientGroup.mk (⟨y, hy⟩ : normOneIdeles F) : normOneIdeles F ⧸ P) ∈ ⋃ q ∈ t, U q := by
    rw [ht]
    exact Set.mem_univ _
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨q, hqt, y', ⟨v, hv, hyv⟩, hyy'⟩ := hmem
  have hprin : ((y'⁻¹ * ⟨y, hy⟩ : normOneIdeles F) : (AdeleRing (𝓞 F) F)ˣ) ∈
      M4aHerbrand.principalIdeles (𝓞 F) F := by
    rw [← Subgroup.mem_subgroupOf]
    exact (QuotientGroup.eq).mp hyy'
  obtain ⟨a, ha⟩ := hprin
  refine ⟨a, v, hv, (q.out : (AdeleRing (𝓞 F) F)ˣ) * s⁻¹, Finset.mem_image_of_mem _ hqt, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at ha
  have hy' : (y' : (AdeleRing (𝓞 F) F)ˣ) = ((q.out : (AdeleRing (𝓞 F) F)ˣ) * s⁻¹) * v := hyv.symm
  have hya : y = (y' : (AdeleRing (𝓞 F) F)ˣ) * Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a := by
    have ha' : Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a = (y' : (AdeleRing (𝓞 F) F)ˣ)⁻¹ * y := ha
    rw [ha', mul_inv_cancel_left]
  rw [hya, hy']
  ac_rfl

-- pin: exists_net (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:390)
private theorem exists_net {τ m M : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) (hm : 0 < m) (hmM : m ≤ M) :
    ∃ J : ℕ, ∀ r : ℝ, r ∈ Set.Icc m M → ∃ j : ℕ, j < J ∧ r / (M * τ ^ j) ∈ Set.Icc τ 1 := by
  have hM : 0 < M := hm.trans_le hmM
  have hy : 1 < τ⁻¹ := (one_lt_inv₀ hτ₀).mpr hτ₁
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (M / m) hy
  refine ⟨J, fun r ⟨hmr, hrM⟩ => ?_⟩
  have hr : 0 < r := hm.trans_le hmr
  have hx : 1 ≤ M / r := (one_le_div hr).mpr hrM
  obtain ⟨j, hj₁, hj₂⟩ := exists_nat_pow_near hx hy
  have hτj : 0 < τ ^ j := pow_pos hτ₀ j
  refine ⟨j, ?_, ?_, ?_⟩
  ·
    have h₁ : M / r ≤ M / m := div_le_div_of_nonneg_left hM.le hm hmr
    exact (pow_lt_pow_iff_right₀ hy).mp (hj₁.trans_lt (h₁.trans_lt hJ))
  ·
    rw [le_div_iff₀ (mul_pos hM hτj)]
    rw [inv_pow, div_lt_iff₀ hr, inv_mul_eq_div, lt_div_iff₀ (pow_pos hτ₀ (j + 1)), pow_succ] at hj₂
    calc τ * (M * τ ^ j) = M * (τ ^ j * τ) := by ring
      _ ≤ r := hj₂.le
  ·
    rw [div_le_one (mul_pos hM hτj)]
    rw [inv_pow, le_div_iff₀ hr, inv_mul_eq_div, div_le_iff₀ hτj] at hj₁
    exact hj₁

-- pin: mul_archUnitHom_mem_shellIdeles (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:414)
private theorem mul_archUnitHom_mem_shellIdeles {σ τ ρ : ℝ} (hσ₀ : 0 < σ) (hττ : τ * τ = σ) (hτ₀ : 0 < τ)
    (hτ₁ : τ ≤ 1) (hρ : σ * σ = ρ) {v : (AdeleRing (𝓞 F) F)ˣ} (hv : v ∈ openShell F σ)
    (w₀ : InfinitePlace F) {b : (w₀.Completion)ˣ} (hb : ‖(b : w₀.Completion)‖ ^ w₀.mult ∈ Set.Icc τ 1) :
    v * archUnitHom w₀ b ∈ shellIdeles (F := F) ρ := by
  subst hρ
  have hσ₁ : σ ≤ 1 := by rw [← hττ]; exact (mul_le_of_le_one_left hτ₀.le hτ₁).trans hτ₁
  obtain ⟨⟨hv₁, hv₂⟩, hvarch⟩ := mem_openShell_iff.mp hv
  have hfst : ∀ (p q : AdeleRing (𝓞 F) F) (w : InfinitePlace F), (p * q).1 w = p.1 w * q.1 w :=
    fun _ _ _ => rfl
  have hsnd : ∀ p q : AdeleRing (𝓞 F) F, (p * q).2 = p.2 * q.2 := fun _ _ => rfl
  refine ⟨⟨?_, ?_⟩, fun v' => ?_⟩
  · rw [Units.val_mul, hsnd, archUnitHom_snd, mul_one]
    exact hv₁
  · rw [mul_inv, Units.val_mul, hsnd, ← map_inv, archUnitHom_snd, mul_one]
    exact hv₂
  · rw [Units.val_mul, hfst, norm_mul]
    obtain ⟨hlo, hhi⟩ := hvarch v'
    rcases eq_or_ne v' w₀ with rfl | hne
    · rw [archUnitHom_fst_self]
      have hq := norm_mul_self_mem_of_norm_pow_mult_mem _ hτ₀.le hτ₁ hb
      rw [hττ] at hq
      have hrearr : ∀ x y : ℝ, (x * y) * (x * y) = (x * x) * (y * y) := fun x y => by ring
      rw [hrearr]
      exact ⟨mul_le_mul hlo.le hq.1 hσ₀.le (mul_self_nonneg _),
        (mul_le_of_le_one_left (mul_self_nonneg _) hhi.le).trans hq.2⟩
    · rw [archUnitHom_fst_of_ne w₀ b hne, norm_one, mul_one]
      exact ⟨(mul_le_of_le_one_left hσ₀.le hσ₁).trans hlo.le, hhi.le⟩

variable (F) in

-- pin: exists_finset_shell_decomposition (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:444)
private theorem exists_finset_shell_decomposition {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    ∀ m M : ℝ, 0 < m → m ≤ M → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ,
      ∀ z : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F z ∈ Set.Icc m M →
        ∃ a : Fˣ, ∃ w' ∈ shellIdeles (F := F) ρ, ∃ n ∈ N,
          z = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a * w' * n := by
  classical
  intro m M hm hmM

  obtain ⟨σ, hσσ, hσ₀, hσ₁⟩ : ∃ σ : ℝ, σ * σ = ρ ∧ 0 < σ ∧ σ < 1 :=
    ⟨Real.sqrt ρ, Real.mul_self_sqrt hρ₀.le, Real.sqrt_pos.mpr hρ₀,
      by rw [Real.sqrt_lt' one_pos, one_pow]; exact hρ₁⟩
  obtain ⟨τ, hττ, hτ₀, hτ₁⟩ : ∃ τ : ℝ, τ * τ = σ ∧ 0 < τ ∧ τ < 1 :=
    ⟨Real.sqrt σ, Real.mul_self_sqrt hσ₀.le, Real.sqrt_pos.mpr hσ₀,
      by rw [Real.sqrt_lt' one_pos, one_pow]; exact hσ₁⟩

  obtain ⟨K, hK⟩ := exists_finset_normOne_decomposition F hσ₀.le hσ₁
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  obtain ⟨J, hJ⟩ := exists_net hτ₀ hτ₁ hm hmM
  have hM : 0 < M := hm.trans_le hmM
  choose t ht0 ht using fun j : ℕ => exists_norm_pow_mult_eq w₀ (M * τ ^ j) (mul_pos hM (pow_pos hτ₀ j))
  refine ⟨(K ×ˢ Finset.range J).image fun p => p.1 * archUnitHom w₀ (Units.mk0 (t p.2) (ht0 p.2)),
    fun z hz => ?_⟩

  obtain ⟨j, hjJ, hx⟩ := hJ (ideleNorm F z) hz
  have hx₀ : 0 < ideleNorm F z / (M * τ ^ j) := hτ₀.trans_le hx.1
  obtain ⟨b, hb0, hb⟩ := exists_norm_pow_mult_eq w₀ (ideleNorm F z / (M * τ ^ j)) hx₀
  have hnuj : ideleNorm F (archUnitHom w₀ (Units.mk0 (t j) (ht0 j))) = M * τ ^ j := by
    rw [ideleNorm_archUnitHom, Units.val_mk0, ht j]
  have hnub : ideleNorm F (archUnitHom w₀ (Units.mk0 b hb0)) = ideleNorm F z / (M * τ ^ j) := by
    rw [ideleNorm_archUnitHom, Units.val_mk0, hb]

  have hy : z * (archUnitHom w₀ (Units.mk0 (t j) (ht0 j)))⁻¹ * (archUnitHom w₀ (Units.mk0 b hb0))⁻¹
      ∈ normOneIdeles F := by
    rw [mem_normOneIdeles_iff, ideleNorm_mul, ideleNorm_mul, ideleNorm_inv, ideleNorm_inv, hnuj, hnub,
      ← div_eq_mul_inv (ideleNorm F z) (M * τ ^ j)]
    exact mul_inv_cancel₀ hx₀.ne'
  obtain ⟨a, v, hv, k, hk, hyk⟩ := hK _ hy
  refine ⟨a, v * archUnitHom w₀ (Units.mk0 b hb0),
    mul_archUnitHom_mem_shellIdeles hσ₀ hττ hτ₀ hτ₁.le hσσ hv w₀ (by rw [Units.val_mk0, hb]; exact hx),
    k * archUnitHom w₀ (Units.mk0 (t j) (ht0 j)),
    Finset.mem_image.mpr ⟨(k, j), Finset.mem_product.mpr ⟨hk, Finset.mem_range.mpr hjJ⟩, rfl⟩, ?_⟩
  have hz' : z = z * (archUnitHom w₀ (Units.mk0 (t j) (ht0 j)))⁻¹ * (archUnitHom w₀ (Units.mk0 b hb0))⁻¹
      * archUnitHom w₀ (Units.mk0 b hb0) * archUnitHom w₀ (Units.mk0 (t j) (ht0 j)) := by
    rw [inv_mul_cancel_right, inv_mul_cancel_right]
  refine hz'.trans ?_
  rw [hyk]
  ac_rfl

end DecompositionAndNormalisation

section BookkeepingAndAssembly

variable {F : Type} [Field F] [NumberField F]

-- pin: norm_eq_zpow_of_valued (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:517)
private theorem norm_eq_zpow_of_valued (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F} {m : ℤ}
    (hx : Valued.v x = WithZero.exp m) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

-- pin: valued_det_le_one (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:525)
private theorem valued_det_le_one (v : HeightOneSpectrum (𝓞 F)) {M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (h : ∀ i j, Valued.v (M i j) ≤ 1) : Valued.v M.det ≤ 1 := by
  rw [Matrix.det_fin_two]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' (h 0 0) (h 1 1)
  · rw [map_mul]; exact mul_le_one' (h 0 1) (h 1 0)

-- pin: det_snd_apply (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:532)
private theorem det_snd_apply (X : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
      = ((finComponent (𝓞 F) F v (glFin (𝓞 F) F X) : GL (Fin 2) (v.adicCompletion F)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)) (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

-- pin: det_fst_apply (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:541)
private theorem det_fst_apply (X : AdelicGL2 (𝓞 F) F) (w : InfinitePlace F) :
    ((Matrix.GeneralLinearGroup.det X : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = ((archComponent F w (glArch (𝓞 F) F X) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  change ((archEval F w).comp (adeleArch (𝓞 F) F)) (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = _
  rw [RingHom.map_det]
  rfl

-- pin: valued_det_finComponent_eq_one (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:550)
private theorem valued_det_finComponent_eq_one (X : AdelicGL2 (𝓞 F) F)
    (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((finComponent (𝓞 F) F v (glFin (𝓞 F) F X) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
  set A := finComponent (𝓞 F) F v (glFin (𝓞 F) F X) with hA
  obtain ⟨h1, h2⟩ := mem_finiteIntegralGL2_iff.mp hX
  have ha : Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≤ 1 :=
    valued_det_le_one v fun i j =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h1 i j v)
  have hb : Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      ≤ 1 := by
    rw [hA, ← map_inv]
    exact valued_det_le_one v fun i j =>
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h2 i j v)
  have hab : (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      * ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hprod : Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
      * Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
        = 1 := by
    rw [← map_mul, hab, map_one]
  refine le_antisymm ha ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det
          * Valued.v ((A⁻¹ : GL (Fin 2) (v.adicCompletion F)) :
              Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := hprod.symm
    _ ≤ Valued.v (A : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det * 1 := mul_le_mul_right hb _
    _ = _ := mul_one _

-- pin: ideleNorm_det_eq_prod_archDetNorm_pow (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:579)
private theorem ideleNorm_det_eq_prod_archDetNorm_pow (X : AdelicGL2 (𝓞 F) F)
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

-- pin: ideleNorm_det_eq_archDetNorm_rat (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:600)
private theorem ideleNorm_det_eq_archDetNorm_rat (X : AdelicGL2 (𝓞 ℚ) ℚ)
    (hX : glFin (𝓞 ℚ) ℚ X ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    ideleNorm ℚ (Matrix.GeneralLinearGroup.det X) = archDetNorm Rat.infinitePlace X := by
  rw [ideleNorm_det_eq_prod_archDetNorm_pow X hX, Fintype.prod_subsingleton _ Rat.infinitePlace]
  unfold InfinitePlace.mult
  rw [ite_eq_left Rat.isReal_infinitePlace, pow_one]

-- pin: ideleNorm_det_globalPoints (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:607)
private theorem ideleNorm_det_globalPoints (γ : GL (Fin 2) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ)) = 1 := by
  have hdet : Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ)
      = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
    refine Units.ext ?_
    rw [Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.map_det]
    rfl
  let := adeleBorel (𝓞 F) F
  have := borelSpace_adeleBorel (𝓞 F) F
  unfold ideleNorm
  rw [hdet, NumberField.AdeleRing.distribHaarChar_algebraMap F (Matrix.GeneralLinearGroup.det γ)]
  rfl

-- pin: det_centralScalar_sq (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:634)
private theorem det_centralScalar_sq (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z ^ 2 := by
  rw [show centralScalar (𝓞 F) F = Matrix.GeneralLinearGroup.scalar (Fin 2) from rfl,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

-- pin: ideleNorm_pow (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:639)
private theorem ideleNorm_pow (z : (AdeleRing (𝓞 F) F)ˣ) (n : ℕ) :
    ideleNorm F (z ^ n) = ideleNorm F z ^ n := by
  unfold ideleNorm
  rw [map_pow, NNReal.coe_pow]

-- pin: ideleNorm_det_centralScalar (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:644)
private theorem ideleNorm_det_centralScalar (z : (AdeleRing (𝓞 F) F)ˣ) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z)) = ideleNorm F z ^ 2 := by
  rw [det_centralScalar_sq, ideleNorm_pow]

-- pin: ideleNorm_det_globalPoints_mul_mul_centralScalar (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:648)
private theorem ideleNorm_det_globalPoints_mul_mul_centralScalar (γ : GL (Fin 2) F)
    (g : AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ) :
    ideleNorm F (Matrix.GeneralLinearGroup.det
        (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z))
      = ideleNorm F (Matrix.GeneralLinearGroup.det g) * ideleNorm F z ^ 2 := by
  rw [map_mul, map_mul, ideleNorm_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul,
    ideleNorm_det_centralScalar]

-- pin: ideleNorm_det_of_archDetNorm_eq (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:656)
private theorem ideleNorm_det_of_archDetNorm_eq {h : AdelicGL2 (𝓞 F) F}
    (hh : glFin (𝓞 F) F h ∈ finiteIntegralGL2 (𝓞 F) F) {d : ℝ}
    (hd : ∀ w : InfinitePlace F, archDetNorm w h = d) :
    ideleNorm F (Matrix.GeneralLinearGroup.det h) = ∏ w : InfinitePlace F, d ^ w.mult := by
  rw [ideleNorm_det_eq_prod_archDetNorm_pow h hh]
  exact Finset.prod_congr rfl fun w _ => by rw [hd w]

-- pin: prod_pow_mult_pos (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:663)
private theorem prod_pow_mult_pos {d : ℝ} (hd : 0 < d) : 0 < ∏ w : InfinitePlace F, d ^ w.mult :=
  Finset.prod_pos fun _ _ => pow_pos hd _

-- pin: glFin_mem_of_mem_centreCutSiegelSet (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:666)
private theorem glFin_mem_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} {h : AdelicGL2 (𝓞 F) F}
    (hS : h ∈ centreCutSiegelSet F c u d₁ d₂) : glFin (𝓞 F) F h ∈ finiteIntegralGL2 (𝓞 F) F :=
  (mem_centreCutSiegelSet_iff.mp hS).1

-- pin: glFin_mem_of_mem_centreCutSiegelSetAmple (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean:689)
private theorem glFin_mem_of_mem_centreCutSiegelSetAmple {c u d₁ d₂ κ : ℝ} {h : AdelicGL2 (𝓞 F) F}
    (hS : h ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ) :
    glFin (𝓞 F) F h ∈ finiteIntegralGL2 (𝓞 F) F :=
  (mem_centreCutSiegelSet_iff.mp hS.1).1

-- pin: exists_bounds_ideleNorm_det (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:670)
private theorem exists_bounds_ideleNorm_det (T : Finset (AdelicGL2 (𝓞 F) F)) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ x ∈ T, ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ Icc a b := by
  classical
  set N : Finset ℝ :=
    insert (1 : ℝ) (T.image fun x : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det x))
  have hNne : N.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hpos : ∀ r ∈ N, 0 < r := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact one_pos
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hr
      exact ideleNorm_pos _
  refine ⟨N.min' hNne, N.max' hNne, hpos _ (N.min'_mem hNne), N.min'_le_max' hNne,
    fun x hx => ?_⟩
  have hmem : ideleNorm F (Matrix.GeneralLinearGroup.det x) ∈ N :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)
  exact ⟨N.min'_le _ hmem, N.le_max' _ hmem⟩

-- pin: exists_bounds_ideleNorm_central (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:689)
private theorem exists_bounds_ideleNorm_central {α β d₂ : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hd₂ : 0 < d₂)
    (T : Finset (AdelicGL2 (𝓞 F) F)) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) (z : (AdeleRing (𝓞 F) F)ˣ)
        (h x : AdelicGL2 (𝓞 F) F), x ∈ T →
        globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z = h * x →
        glFin (𝓞 F) F h ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, archDetNorm w h = d₂) →
        ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Icc α β →
        ideleNorm F z⁻¹ ∈ Icc m M := by
  obtain ⟨a, b, ha, hab, hT⟩ := exists_bounds_ideleNorm_det (F := F) T
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∏ w : InfinitePlace F, d₂ ^ w.mult := ⟨_, rfl⟩
  have hKpos : 0 < K := by
    rw [hK]
    exact prod_pow_mult_pos hd₂
  have hb : 0 < b := ha.trans_le hab
  have hβ : 0 < β := hα.trans_le hαβ
  refine ⟨Real.sqrt (α / (K * b)), Real.sqrt (β / (K * a)),
    Real.sqrt_pos.mpr (div_pos hα (mul_pos hKpos hb)), Real.sqrt_le_sqrt ?_, ?_⟩
  · gcongr
  intro γ g z h x hxT hrel hh hnorm hg
  obtain ⟨hgα, hgβ⟩ := hg
  obtain ⟨hxa, hxb⟩ := hT x hxT
  have hy : 0 < ideleNorm F z := ideleNorm_pos z
  have hng : 0 < ideleNorm F (Matrix.GeneralLinearGroup.det g) := hα.trans_le hgα
  have hnx : 0 < ideleNorm F (Matrix.GeneralLinearGroup.det x) := ideleNorm_pos _
  have hkey : ideleNorm F (Matrix.GeneralLinearGroup.det g) * ideleNorm F z ^ 2
      = K * ideleNorm F (Matrix.GeneralLinearGroup.det x) := by
    rw [← ideleNorm_det_globalPoints_mul_mul_centralScalar γ g z, hrel, map_mul, ideleNorm_mul,
      ideleNorm_det_of_archDetNorm_eq hh hnorm, hK]
  have hy2 : ideleNorm F z ^ 2
      = K * ideleNorm F (Matrix.GeneralLinearGroup.det x) / ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    rw [eq_div_iff hng.ne', mul_comm (ideleNorm F z ^ 2)]
    exact hkey
  have hq : (ideleNorm F z)⁻¹ ^ 2
      = ideleNorm F (Matrix.GeneralLinearGroup.det g) / (K * ideleNorm F (Matrix.GeneralLinearGroup.det x)) := by
    rw [inv_pow, hy2, inv_div]
  have hqpos : 0 < (ideleNorm F z)⁻¹ := inv_pos.mpr hy
  have hlo : α / (K * b) ≤ (ideleNorm F z)⁻¹ ^ 2 := by
    rw [hq]
    gcongr
  have hhi : (ideleNorm F z)⁻¹ ^ 2 ≤ β / (K * a) := by
    rw [hq]
    gcongr
  have hq_eq : (ideleNorm F z)⁻¹ = Real.sqrt ((ideleNorm F z)⁻¹ ^ 2) := (Real.sqrt_sq hqpos.le).symm
  rw [ideleNorm_inv]
  constructor
  · rw [hq_eq]
    exact Real.sqrt_le_sqrt hlo
  · rw [hq_eq]
    exact Real.sqrt_le_sqrt hhi

-- pin: globalPoints_scalar (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:749)
private theorem globalPoints_scalar (a : Fˣ) :
    globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) := by
  apply Units.ext
  ext i j
  by_cases h : i = j
  · subst h
    simp [globalPoints, centralScalar, Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar,
      Matrix.scalar_apply]
  · simp [globalPoints, centralScalar, Matrix.GeneralLinearGroup.map, Matrix.GeneralLinearGroup.scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]

-- pin: exists_finset_central_covering_of_point_of_stable_of_decomposition (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:772)
private theorem exists_finset_central_covering_of_point_of_stable_of_decomposition
    (S : Set (AdelicGL2 (𝓞 F) F)) (T : Finset (AdelicGL2 (𝓞 F) F)) (d₂ : ℝ)
    (W : Set (AdeleRing (𝓞 F) F)ˣ)
    (hSfin : ∀ h ∈ S, glFin (𝓞 F) F h ∈ finiteIntegralGL2 (𝓞 F) F)
    (hP : ∀ g : AdelicGL2 (𝓞 F) F, ∃ (γ : GL (Fin 2) F) (z : (AdeleRing (𝓞 F) F)ˣ)
      (h x : AdelicGL2 (𝓞 F) F), x ∈ T ∧ h ∈ S ∧ (∀ w : InfinitePlace F, archDetNorm w h = d₂) ∧
        globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z = h * x)
    (hSt : ∀ h ∈ S, (∀ w : InfinitePlace F, archDetNorm w h = d₂) →
      ∀ w' ∈ W, h * centralScalar (𝓞 F) F w' ∈ S)
    (hEn : ∀ m M : ℝ, 0 < m → m ≤ M → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ,
      ∀ z : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F z ∈ Icc m M → ∃ a : Fˣ, ∃ w' ∈ W, ∃ n ∈ N,
        z = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a * w' * n)
    {α β : ℝ} (hα : 0 < α) :
    ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Icc α β →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
          globalPoints (𝓞 F) F γ * g ∈ (· * (centralScalar (𝓞 F) F n * x)) '' S := by
  classical
  rcases lt_or_ge β α with hβα | hαβ
  · exact ⟨∅, fun _ hg => absurd (hg.1.trans hg.2) (not_le.mpr hβα)⟩
  have hd₂ : 0 < d₂ := by
    obtain ⟨_, _, h, _, -, -, hnorm, -⟩ := hP 1
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rw [← hnorm w₀]
    exact archDetNorm_pos w₀ h
  obtain ⟨m, M, hm, hmM, hbound⟩ := exists_bounds_ideleNorm_central hα hαβ hd₂ T
  obtain ⟨N, hN⟩ := hEn m M hm hmM
  refine ⟨N, fun g hg => ?_⟩
  obtain ⟨γ, z, h, x, hxT, hhS, hnorm, hrel⟩ := hP g
  have hz : ideleNorm F z⁻¹ ∈ Icc m M := hbound γ g z h x hxT hrel (hSfin h hhS) hnorm hg
  obtain ⟨a, w', hw'W, n, hnN, hz_eq⟩ := hN z⁻¹ hz
  set P : (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a
  have hc : ∀ (c : (AdeleRing (𝓞 F) F)ˣ) (y : AdelicGL2 (𝓞 F) F),
      y * centralScalar (𝓞 F) F c = centralScalar (𝓞 F) F c * y :=
    fun c y => (centralScalar_mul_comm c y).symm
  have hsa : globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) = centralScalar (𝓞 F) F P :=
    globalPoints_scalar a
  have hgz : globalPoints (𝓞 F) F γ * g
      = h * x * (centralScalar (𝓞 F) F P * centralScalar (𝓞 F) F w' * centralScalar (𝓞 F) F n) := by
    rw [← map_mul (centralScalar (𝓞 F) F), ← map_mul (centralScalar (𝓞 F) F), ← hz_eq, map_inv]
    exact eq_mul_inv_of_mul_eq hrel
  have hR : globalPoints (𝓞 F) F ((Matrix.GeneralLinearGroup.scalar (Fin 2) a)⁻¹ * γ) * g
      = h * x * (centralScalar (𝓞 F) F w' * centralScalar (𝓞 F) F n) := by
    rw [map_mul, map_inv, mul_assoc _ (globalPoints (𝓞 F) F γ) g, hgz, hsa,
      mul_assoc (centralScalar (𝓞 F) F P) (centralScalar (𝓞 F) F w'),
      ← mul_assoc (h * x) (centralScalar (𝓞 F) F P), hc P (h * x),
      mul_assoc (centralScalar (𝓞 F) F P) (h * x), inv_mul_cancel_left]
  refine ⟨(Matrix.GeneralLinearGroup.scalar (Fin 2) a)⁻¹ * γ, n, hnN, x, hxT,
    h * centralScalar (𝓞 F) F w', hSt h hhS hnorm w' hw'W, ?_⟩
  show h * centralScalar (𝓞 F) F w' * (centralScalar (𝓞 F) F n * x) = _
  rw [hR, ← mul_assoc (h * x), mul_assoc h x (centralScalar (𝓞 F) F w'), hc w' x,
    ← mul_assoc h (centralScalar (𝓞 F) F w') x,
    mul_assoc (h * centralScalar (𝓞 F) F w') x (centralScalar (𝓞 F) F n), ← hc n x]


-- pin: exists_finset_central_covering_centreCut_of_point_of_stable_of_decomposition (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:826)
-- pin: exists_finset_central_covering_centreCut_of_point_of_stable_of_decomposition (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean:851)
private theorem exists_finset_central_covering_centreCut_of_point_of_stable_of_decomposition
    (S : Set (AdelicGL2 (𝓞 F) F)) (T : Finset (AdelicGL2 (𝓞 F) F)) (d₂ : ℝ)
    (W : Set (AdeleRing (𝓞 F) F)ˣ)
    (hSfin : ∀ h ∈ S, glFin (𝓞 F) F h ∈ finiteIntegralGL2 (𝓞 F) F)
    (hP : ∀ g : AdelicGL2 (𝓞 F) F, ∃ (γ : GL (Fin 2) F) (z : (AdeleRing (𝓞 F) F)ˣ)
      (h x : AdelicGL2 (𝓞 F) F), x ∈ T ∧ h ∈ S ∧ (∀ w : InfinitePlace F, archDetNorm w h = d₂) ∧
        globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z = h * x)
    (hSt : ∀ h ∈ S, (∀ w : InfinitePlace F, archDetNorm w h = d₂) →
      ∀ w' ∈ W, h * centralScalar (𝓞 F) F w' ∈ S)
    (hEn : ∀ m M : ℝ, 0 < m → m ≤ M → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ,
      ∀ z : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F z ∈ Icc m M → ∃ a : Fˣ, ∃ w' ∈ W, ∃ n ∈ N,
        z = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a * w' * n)
    {α β : ℝ} (hα : 0 < α) :
    ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Icc α β →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
          globalPoints (𝓞 F) F γ * g ∈ (· * (centralScalar (𝓞 F) F n * x)) '' S :=
  exists_finset_central_covering_of_point_of_stable_of_decomposition S T d₂ W hSfin hP hSt hEn hα

end BookkeepingAndAssembly

section Assembly

variable {F : Type} [Field F] [NumberField F]

-- pin: exists_finset_slab_covering_of_point_of_stable_of_engine (S_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.lean:772)
private theorem exists_finset_slab_covering_of_point_of_stable_of_engine
    (S : Set (AdelicGL2 (𝓞 F) F)) (T : Finset (AdelicGL2 (𝓞 F) F)) (d₂ : ℝ)
    (W : Set (AdeleRing (𝓞 F) F)ˣ)
    (hSfin : ∀ h ∈ S, glFin (𝓞 F) F h ∈ finiteIntegralGL2 (𝓞 F) F)
    (hP : ∀ g : AdelicGL2 (𝓞 F) F, ∃ (γ : GL (Fin 2) F) (z : (AdeleRing (𝓞 F) F)ˣ)
      (h x : AdelicGL2 (𝓞 F) F), x ∈ T ∧ h ∈ S ∧ (∀ w : InfinitePlace F, archDetNorm w h = d₂) ∧
        globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z = h * x)
    (hSt : ∀ h ∈ S, (∀ w : InfinitePlace F, archDetNorm w h = d₂) →
      ∀ w' ∈ W, h * centralScalar (𝓞 F) F w' ∈ S)
    (hEn : ∀ m M : ℝ, 0 < m → m ≤ M → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ,
      ∀ z : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F z ∈ Icc m M → ∃ a : Fˣ, ∃ w' ∈ W, ∃ n ∈ N,
        z = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a * w' * n)
    {α β : ℝ} (hα : 0 < α) :
    ∃ T' : Finset (AdelicGL2 (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Icc α β →
        ∃ γ : GL (Fin 2) F, globalPoints (𝓞 F) F γ * g ∈ ⋃ x ∈ T', (· * x) '' S := by
  classical
  rcases lt_or_ge β α with hβα | hαβ
  · exact ⟨∅, fun _ hg => absurd (hg.1.trans hg.2) (not_le.mpr hβα)⟩
  have hd₂ : 0 < d₂ := by
    obtain ⟨_, _, h, _, -, -, hnorm, -⟩ := hP 1
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rw [← hnorm w₀]
    exact archDetNorm_pos w₀ h
  obtain ⟨m, M, hm, hmM, hbound⟩ := exists_bounds_ideleNorm_central hα hαβ hd₂ T
  obtain ⟨N, hN⟩ := hEn m M hm hmM
  refine ⟨(N ×ˢ T).image fun p => centralScalar (𝓞 F) F p.1 * p.2, fun g hg => ?_⟩
  obtain ⟨γ, z, h, x, hxT, hhS, hnorm, hrel⟩ := hP g
  have hz : ideleNorm F z⁻¹ ∈ Icc m M := hbound γ g z h x hxT hrel (hSfin h hhS) hnorm hg
  obtain ⟨a, w', hw'W, n, hnN, hz_eq⟩ := hN z⁻¹ hz
  set P : (AdeleRing (𝓞 F) F)ˣ := Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a
  have hc : ∀ (c : (AdeleRing (𝓞 F) F)ˣ) (y : AdelicGL2 (𝓞 F) F),
      y * centralScalar (𝓞 F) F c = centralScalar (𝓞 F) F c * y :=
    fun c y => (centralScalar_mul_comm c y).symm
  have hsa : globalPoints (𝓞 F) F (Matrix.GeneralLinearGroup.scalar (Fin 2) a) = centralScalar (𝓞 F) F P :=
    globalPoints_scalar a
  have hgz : globalPoints (𝓞 F) F γ * g
      = h * x * (centralScalar (𝓞 F) F P * centralScalar (𝓞 F) F w' * centralScalar (𝓞 F) F n) := by
    rw [← map_mul (centralScalar (𝓞 F) F), ← map_mul (centralScalar (𝓞 F) F), ← hz_eq, map_inv]
    exact eq_mul_inv_of_mul_eq hrel
  have hR : globalPoints (𝓞 F) F ((Matrix.GeneralLinearGroup.scalar (Fin 2) a)⁻¹ * γ) * g
      = h * x * (centralScalar (𝓞 F) F w' * centralScalar (𝓞 F) F n) := by
    rw [map_mul, map_inv, mul_assoc _ (globalPoints (𝓞 F) F γ) g, hgz, hsa,
      mul_assoc (centralScalar (𝓞 F) F P) (centralScalar (𝓞 F) F w'),
      ← mul_assoc (h * x) (centralScalar (𝓞 F) F P), hc P (h * x),
      mul_assoc (centralScalar (𝓞 F) F P) (h * x), inv_mul_cancel_left]
  refine ⟨(Matrix.GeneralLinearGroup.scalar (Fin 2) a)⁻¹ * γ, ?_⟩
  rw [Set.mem_iUnion₂]
  refine ⟨centralScalar (𝓞 F) F n * x,
    Finset.mem_image.mpr ⟨(n, x), Finset.mem_product.mpr ⟨hnN, hxT⟩, rfl⟩,
    h * centralScalar (𝓞 F) F w', hSt h hhS hnorm w' hw'W, ?_⟩
  show h * centralScalar (𝓞 F) F w' * (centralScalar (𝓞 F) F n * x) = _
  rw [hR, ← mul_assoc (h * x), mul_assoc h x (centralScalar (𝓞 F) F w'), hc w' x,
    ← mul_assoc h (centralScalar (𝓞 F) F w') x,
    mul_assoc (h * centralScalar (𝓞 F) F w') x (centralScalar (𝓞 F) F n), ← hc n x]

-- pin: exists_finset_slab_covering_centreCut_of_point_of_stable_of_engine (S_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.lean:828)
private theorem exists_finset_slab_covering_centreCut_of_point_of_stable_of_engine
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (W : Set (AdeleRing (𝓞 F) F)ˣ)
    (hP : ∀ g : AdelicGL2 (𝓞 F) F, ∃ (γ : GL (Fin 2) F) (z : (AdeleRing (𝓞 F) F)ˣ)
      (h x : AdelicGL2 (𝓞 F) F), x ∈ T ∧ h ∈ centreCutSiegelSet F c u d₁ d₂ ∧
        (∀ w : InfinitePlace F, archDetNorm w h = d₂) ∧
        globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z = h * x)
    (hSt : ∀ h ∈ centreCutSiegelSet F c u d₁ d₂, (∀ w : InfinitePlace F, archDetNorm w h = d₂) →
      ∀ w' ∈ W, h * centralScalar (𝓞 F) F w' ∈ centreCutSiegelSet F c u d₁ d₂)
    (hEn : ∀ m M : ℝ, 0 < m → m ≤ M → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ,
      ∀ z : (AdeleRing (𝓞 F) F)ˣ, ideleNorm F z ∈ Icc m M → ∃ a : Fˣ, ∃ w' ∈ W, ∃ n ∈ N,
        z = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a * w' * n)
    (α β : ℝ) (hα : 0 < α) :
    ∃ T' : Finset (AdelicGL2 (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Icc α β →
        ∃ γ : GL (Fin 2) F,
          globalPoints (𝓞 F) F γ * g ∈ ⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c u d₁ d₂ :=
  exists_finset_slab_covering_of_point_of_stable_of_engine (centreCutSiegelSet F c u d₁ d₂) T d₂ W
    (fun _ hh => glFin_mem_of_mem_centreCutSiegelSet hh) hP hSt hEn hα

-- pin: exists_shell_ratio (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:857)
private theorem exists_shell_ratio {d₁ d₂ : ℝ} (hd : d₁ < d₂) (hd₂ : 0 < d₂) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ d₁ ≤ ρ * d₂ := by
  refine ⟨max d₁ (d₂ / 2) / d₂, div_pos (lt_max_of_lt_right (half_pos hd₂)) hd₂,
    (div_lt_one hd₂).mpr (max_lt hd (half_lt_self hd₂)), ?_⟩
  rw [div_mul_cancel₀ _ hd₂.ne']
  exact le_max_left _ _

-- pin: central_assembled (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:864)
-- pin: central_assembled (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean:891)
private theorem central_assembled {S : Set (AdelicGL2 (𝓞 F) F)} (d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hwin : ∀ h ∈ S, ∀ v : InfinitePlace F, archDetNorm v h ∈ Set.Icc d₁ d₂)
    (hmul : ∀ (w : (AdeleRing (𝓞 F) F)ˣ),
      glFin (𝓞 F) F (centralScalar (𝓞 F) F w) ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0) →
      ∀ h ∈ S, (∀ v : InfinitePlace F,
          archDetNorm v (centralScalar (𝓞 F) F w * h) ∈ Set.Icc d₁ d₂) →
        centralScalar (𝓞 F) F w * h ∈ S)
    (hSfin : ∀ h ∈ S, glFin (𝓞 F) F h ∈ finiteIntegralGL2 (𝓞 F) F)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' S))
    (α β : ℝ) (hα : 0 < α) :
    ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Icc α β →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
          globalPoints (𝓞 F) F γ * g ∈
            (· * (centralScalar (𝓞 F) F n * x)) '' S := by
  have hP := pointShape hwin hmul hcov
  have hd₂ : 0 < d₂ := by
    obtain ⟨_, _, h, _, -, -, hnorm, -⟩ := hP 1
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rw [← hnorm w₀]
    exact archDetNorm_pos w₀ h
  obtain ⟨ρ, hρ₀, hρ₁, hρd⟩ := exists_shell_ratio hd hd₂
  exact exists_finset_central_covering_centreCut_of_point_of_stable_of_decomposition S T d₂ (shellIdeles ρ)
    hSfin hP (fun _ hh hdet _ hw' => mul_centralScalar_mem_of_mem_shellIdeles hρ₀ hρd hmul hh hdet hw')
    (exists_finset_shell_decomposition F hρ₀ hρ₁) hα

-- pin: e2a_assembled (S_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.lean:865)
private theorem e2a_assembled (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) :
    ∃ T' : Finset (AdelicGL2 (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Icc α β →
        ∃ γ : GL (Fin 2) F,
          globalPoints (𝓞 F) F γ * g ∈ ⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
  have hP := pointShape (S := centreCutSiegelSet F c u d₁ d₂) (d₁ := d₁) (d₂ := d₂)
    (fun _ hh => hh.2.2.2)
    (fun _ hwK hwa _h hh hdet => centralScalar_mul_mem_centreCutSiegelSet hwK hwa hh hdet) hcov
  have hd₂ : 0 < d₂ := by
    obtain ⟨_, _, h, _, -, -, hnorm, -⟩ := hP 1
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rw [← hnorm w₀]
    exact archDetNorm_pos w₀ h
  obtain ⟨ρ, hρ₀, hρ₁, hρd⟩ := exists_shell_ratio hd hd₂
  exact exists_finset_slab_covering_centreCut_of_point_of_stable_of_engine c u d₁ d₂ T (shellIdeles ρ)
    hP (fun _ hh hdet _ hw' => mul_centralScalar_mem_of_mem_shellIdeles hρ₀ hρd
      (fun _ hwK hwa _h hh hdet => centralScalar_mul_mem_centreCutSiegelSet hwK hwa hh hdet) hh hdet hw')
    (exists_finset_shell_decomposition F hρ₀ hρ₁) α β hα

end Assembly

namespace Engine

-- pin: exists_finset_central_slab_covering_of_coversModCentre (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre.lean:896)
theorem exists_finset_central_slab_covering_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) :
    ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N, ∃ x ∈ T,
          globalPoints (𝓞 F) F γ * g ∈
            (· * (centralScalar (𝓞 F) F n * x)) '' centreCutSiegelSet F c u d₁ d₂ :=
  central_assembled (S := centreCutSiegelSet F c u d₁ d₂) d₁ d₂ T hd
    (fun _ hh => hh.2.2.2)
    (fun _ hwK hwa _h hh hdet => centralScalar_mul_mem_centreCutSiegelSet hwK hwa hh hdet)
    (fun _h hh => glFin_mem_of_mem_centreCutSiegelSet hh) hcov α β hα

-- pin: exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple (S_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean:896)
theorem exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)) :
    ∀ a b : ℝ, 0 < a → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N,
          globalPoints (𝓞 F) F γ * g ∈
            (· * centralScalar (𝓞 F) F n) '' (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ) := by
  intro a b ha
  obtain ⟨N, hN⟩ := central_assembled (S := centreCutSiegelSetAmple F c u d₁ d₂ κ) d₁ d₂ T hd
    (fun _ hh => hh.1.2.2.2)
    (fun _ hwK hwa _h hh hdet => centralScalar_mul_mem_centreCutSiegelSetAmple hwK hwa hh hdet)
    (fun _h hh => glFin_mem_of_mem_centreCutSiegelSetAmple hh) hcov a b ha
  refine ⟨N, fun g hg => ?_⟩
  obtain ⟨γ, n, hn, x, hx, h, hh, hhx⟩ := hN g hg
  refine ⟨γ, n, hn, h * x, Set.mem_iUnion₂.mpr ⟨x, hx, h, hh, rfl⟩, ?_⟩
  show h * x * centralScalar (𝓞 F) F n = globalPoints (𝓞 F) F γ * g
  rw [← hhx]
  show h * x * centralScalar (𝓞 F) F n = h * (centralScalar (𝓞 F) F n * x)
  rw [mul_assoc, centralScalar_mul_comm n x]

-- pin: exists_finset_slab_covering_of_coversModCentre (S_AutomorphicForm_exists_finset_slab_covering_of_coversModCentre.lean:896)
theorem exists_finset_slab_covering_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α) :
    ∃ T' : Finset (AdelicGL2 (𝓞 F) F), ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
        ∃ γ : GL (Fin 2) F,
          globalPoints (𝓞 F) F γ * g ∈ ⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c u d₁ d₂ :=
  e2a_assembled c u d₁ d₂ T hd hcov α β hα

end Engine

end AutomorphicForm.SiegelCovering

end
