/-
  The Weyl translate of an induced section, evaluated.

  For an induced section `φ` of the character pair `(etaFst 1 α hα s, etaSnd 1 α hα s)` — `α` the
  modulus character `distribHaarChar` read through `ℝ≥0 → ℝ` — the translate
  `w⁻¹ · n(x) · k` acts on `φ` by a product of `‖·‖`-powers: the archimedean version
  (`apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply`) computes the whole translate at
  one infinite place `w`, with `k` supported at `w`, as `‖det k_w‖ ^ (s+1/2) · ‖k_w00 + x_w k_w10‖ ^ (-(2s+1))`
  times the value at the corrected finite-adèle point `x'`; the local version
  (`…_localWeyl_eq_modulus_cpow_mul_apply`) computes the translate by the finite-place Weyl element
  `finEmbed (localEmbed v gl2Weyl)` as `modulus (x_v) ^ (-(2s+1))` times the value at the spliced point.

  These are the two evaluations that turn the Weyl intertwining integrand into a product of local
  factors; they are the value side of the `WeylIntegrable` family of SET-AF33.

  Transcribed whole from the pin's proof files
  `P2M/Sol/S_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply.lean`
  (pinned `aa2d8b3`, 360 lines / 43 declarations) and
  `…_apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply.lean` (217 lines / 22 declarations),
  with the statements from their `Theorems/` wrappers.

  The two files share a 42-line private prelude and a public `Ext` block; the port has them already,
  in `AutomorphicForm/Adelic/IwasawaWeylUnipotent.lean` — `adele_ext` (`:398`), `mul_apply_fst`
  (`:390`), `mul_apply_snd` (`:394`), `coe_weylInv_mul_unipotent` (`:492`), and the two component
  evaluations as `archComponent_weylUnip_coe` (`:537`) / `finComponent_weylUnip_coe` (`:544`). They
  are imported, not re-proved: `MOEBW.gl_ext` and `MOEBW.glArch_ext` are the only members of the
  shared `Ext` block stated here, because the pin's `gl_ext` takes its finite hypothesis placewise
  (`∀ u, finComponent … = finComponent …`) and the port's public `gl_ext`
  (`Adelic/MaximalCompactFactors.lean:271`) takes it as `glFin … = glFin …`.  Both are now
  one-application restatements of the shared facts — `AutomorphicForm.eq_of_glArch_eq_of_glFin_eq`
  (`Adelic/LevelCompactness.lean`, via the `glFin_ext` bridge) and `AutomorphicForm.ext_archComponent`
  (`Adelic/ArchComponentDictionary.lean`) — rather than re-proofs (AF dedup wave).

  **Deviations** (proofs and private helpers only; not one statement moves):

  * `MOEBW.BM`/`BMinv` (pin `:67`–`:73`): the pin writes the dependent function
    `fun w' => if h : w' = w then h ▸ βloc … else 1` inline inside `Matrix.of`. The port's
    `Matrix.of` is an `Equiv` and no longer reduces that inline form, so the function is named
    (`atPlaceMat`/`atPlaceMatInv`) and the matrices are plain lambdas.
  * `MOEBW.βloc_mul`/`βlocInv_mul` (pin `:58`–`:65`) and `BM_mul_BMinv`/`BMinv_mul_BM`
    (pin `:102`–`:135`): the port's mathlib wraps the archimedean completion in the one-field
    structure `InfinitePlace.Completion` (`ofCompletion`/`toCompletion`, `AbsoluteValue`-completion
    inside), so `field_simp; ring` leaves `toCompletion`-atoms that `ring` cannot see through. The
    three private helpers `toCompletion_inv`/`toCompletion_neg`/`toCompletion_ne_zero` push
    inverse/negation/zero through `toCompletion` first and the entry computations then close.
  * `MOEBW.moeb_fst_self`/`moeb_fst_of_ne` (pin `:249`–`:255`): `simp [moeb]` does not fire
    `Function.update_self`/`update_of_ne` at `InfiniteAdeleRing` (a `def`, not syntactically the
    dependent function type), so the pin's `simp` is replaced by `unfold moeb` + `exact
    Function.update_self …` / `Function.update_of_ne …`.
  * `MOEBW.main`'s `modulus` step (local pin `:195`) is `NumberField.TateGlobal.modulus_adicCompletion_eq_nnnorm`;
    the port states that lemma in `NumberTheory/NumberField/TateGlobal/NormIntegrable.lean`, hence the
    one added import at `:34` (it is the module the pin's
    `Theorems/Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm` became).

  Visibility follows the pin per declaration: the `archSupportedAt` file states its helpers `private`
  (kept `private` here), the local-Weyl file states its own publicly (kept public here), so
  `check_port` diffs 34 declarations and passes all of them.

  spec-pin: Theorems/Thm_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply.lean
  spec-pin: Theorems/Thm_AutomorphicForm_apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.LevelCompactness
import FLTForHuman.AutomorphicForm.Adelic.ArchComponentDictionary
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.AutomorphicForm.Adelic.IwasawaWeylUnipotent
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.RowIsometry
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.LanglandsTunnell.TateLocalConstantsAt
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm AdelicDock
open scoped NNReal Classical

noncomputable section

namespace AutomorphicForm

namespace MOEBW

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

section Beta

variable (t₁ c t₂ : w.Completion) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0)

-- The port's mathlib wraps the archimedean completion in a one-field structure
-- (`InfinitePlace.Completion` with `ofCompletion`/`toCompletion`), so the pin's
-- `field_simp; ring` matrix computations run over the underlying completion and need the
-- inverse/negation pushed through `toCompletion` first.  Three private helpers do that.
omit [NumberField F] in
private theorem toCompletion_inv (x : w.Completion) : (x⁻¹).toCompletion = (x.toCompletion)⁻¹ :=
  map_inv₀ (InfinitePlace.Completion.equiv w) x

omit [NumberField F] in
private theorem toCompletion_neg (x : w.Completion) : (-x).toCompletion = -x.toCompletion := rfl

omit [NumberField F] in
private theorem toCompletion_ne_zero (x : w.Completion) (hx : x ≠ 0) : x.toCompletion ≠ 0 := by
  intro h
  rw [← InfinitePlace.Completion.toCompletion_zero] at h
  exact hx (InfinitePlace.Completion.ext h)

private def βloc : Matrix (Fin 2) (Fin 2) w.Completion := !![t₁, c; 0, t₂]
private def βlocInv : Matrix (Fin 2) (Fin 2) w.Completion := !![t₁⁻¹, -c * (t₁⁻¹ * t₂⁻¹); 0, t₂⁻¹]

include h₁ h₂ in
omit [NumberField F] in
private theorem βloc_mul : βloc F w t₁ c t₂ * βlocInv F w t₁ c t₂ = 1 := by
  have h1 : t₁.toCompletion ≠ 0 := toCompletion_ne_zero F w t₁ h₁
  have h2 : t₂.toCompletion ≠ 0 := toCompletion_ne_zero F w t₂ h₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [βloc, βlocInv, Matrix.mul_apply, Fin.sum_univ_two, toCompletion_inv, toCompletion_neg]
  all_goals
    try field_simp
    try ring

include h₁ h₂ in
omit [NumberField F] in
private theorem βlocInv_mul : βlocInv F w t₁ c t₂ * βloc F w t₁ c t₂ = 1 := by
  have h1 : t₁.toCompletion ≠ 0 := toCompletion_ne_zero F w t₁ h₁
  have h2 : t₂.toCompletion ≠ 0 := toCompletion_ne_zero F w t₂ h₂
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [βloc, βlocInv, Matrix.mul_apply, Fin.sum_univ_two, toCompletion_inv, toCompletion_neg]
  all_goals
    try field_simp
    try ring

/-- The value of `βloc` at the place `w`, and the identity elsewhere: the pin writes this
dependent function inline inside `Matrix.of`; the port names it, because the port's
`Matrix.of` is an `Equiv` and no longer reduces the inline form. -/
private def atPlaceMat (i j : Fin 2) : ∀ w' : InfinitePlace F, w'.Completion :=
  fun w' => if h : w' = w then h ▸ βloc F w t₁ c t₂ i j else (1 : Matrix (Fin 2) (Fin 2) w'.Completion) i j

private def atPlaceMatInv (i j : Fin 2) : ∀ w' : InfinitePlace F, w'.Completion :=
  fun w' => if h : w' = w then h ▸ βlocInv F w t₁ c t₂ i j else (1 : Matrix (Fin 2) (Fin 2) w'.Completion) i j

private def BM : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  fun i j => (atPlaceMat F w t₁ c t₂ i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)

private def BMinv : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  fun i j => (atPlaceMatInv F w t₁ c t₂ i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)

private theorem BM_fst_self (i j : Fin 2) : (BM F w t₁ c t₂ i j).1 w = βloc F w t₁ c t₂ i j := by
  simp [BM, atPlaceMat]
private theorem BM_fst_of_ne (i j : Fin 2) {w' : InfinitePlace F} (hw : w' ≠ w) :
    (BM F w t₁ c t₂ i j).1 w' = (1 : Matrix (Fin 2) (Fin 2) w'.Completion) i j := by
  simp [BM, atPlaceMat, hw]
private theorem BM_snd (i j : Fin 2) (u : HeightOneSpectrum (𝓞 F)) :
    (BM F w t₁ c t₂ i j).2 u = (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) i j := by
  change ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) u = _
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
private theorem BMinv_fst_self (i j : Fin 2) : (BMinv F w t₁ c t₂ i j).1 w = βlocInv F w t₁ c t₂ i j := by
  simp [BMinv, atPlaceMatInv]
private theorem BMinv_fst_of_ne (i j : Fin 2) {w' : InfinitePlace F} (hw : w' ≠ w) :
    (BMinv F w t₁ c t₂ i j).1 w' = (1 : Matrix (Fin 2) (Fin 2) w'.Completion) i j := by
  simp [BMinv, atPlaceMatInv, hw]
private theorem BMinv_snd (i j : Fin 2) (u : HeightOneSpectrum (𝓞 F)) :
    (BMinv F w t₁ c t₂ i j).2 u = (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) i j := by
  change ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) u = _
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl

private theorem one_fst (i j : Fin 2) (w' : InfinitePlace F) :
    ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w' = (1 : Matrix (Fin 2) (Fin 2) w'.Completion) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
private theorem one_snd (i j : Fin 2) (u : HeightOneSpectrum (𝓞 F)) :
    ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 u = (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl

include h₁ h₂ in
private theorem BM_mul_BMinv : BM F w t₁ c t₂ * BMinv F w t₁ c t₂ = 1 := by
  ext i j
  refine IwasawaWeyl.adele_ext F (fun w' => ?_) (fun u => ?_)
  · rw [IwasawaWeyl.mul_apply_fst, one_fst]
    by_cases hw : w' = w
    · subst hw
      simp only [BM_fst_self, BMinv_fst_self]
      have h := congrFun (congrFun (βloc_mul F w' t₁ c t₂ h₁ h₂) i) j
      rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h
    · simp only [BM_fst_of_ne F w t₁ c t₂ _ _ hw, BMinv_fst_of_ne F w t₁ c t₂ _ _ hw]
      have h := congrFun (congrFun (one_mul (1 : Matrix (Fin 2) (Fin 2) w'.Completion)) i) j
      rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h
  · rw [IwasawaWeyl.mul_apply_snd, one_snd]
    simp only [BM_snd, BMinv_snd]
    have h := congrFun (congrFun (one_mul (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F))) i) j
    rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h

include h₁ h₂ in
private theorem BMinv_mul_BM : BMinv F w t₁ c t₂ * BM F w t₁ c t₂ = 1 := by
  ext i j
  refine IwasawaWeyl.adele_ext F (fun w' => ?_) (fun u => ?_)
  · rw [IwasawaWeyl.mul_apply_fst, one_fst]
    by_cases hw : w' = w
    · subst hw
      simp only [BM_fst_self, BMinv_fst_self]
      have h := congrFun (congrFun (βlocInv_mul F w' t₁ c t₂ h₁ h₂) i) j
      rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h
    · simp only [BM_fst_of_ne F w t₁ c t₂ _ _ hw, BMinv_fst_of_ne F w t₁ c t₂ _ _ hw]
      have h := congrFun (congrFun (one_mul (1 : Matrix (Fin 2) (Fin 2) w'.Completion)) i) j
      rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h
  · rw [IwasawaWeyl.mul_apply_snd, one_snd]
    simp only [BM_snd, BMinv_snd]
    have h := congrFun (congrFun (one_mul (1 : Matrix (Fin 2) (Fin 2) (u.adicCompletion F))) i) j
    rw [Fin.sum_univ_two]; rwa [Matrix.mul_apply, Fin.sum_univ_two] at h

private def Bel : AdelicGL2 (𝓞 F) F :=
  ⟨BM F w t₁ c t₂, BMinv F w t₁ c t₂, BM_mul_BMinv F w t₁ c t₂ h₁ h₂, BMinv_mul_BM F w t₁ c t₂ h₁ h₂⟩

private theorem Bel_mem : Bel F w t₁ c t₂ h₁ h₂ ∈ adelicBorel (𝓞 F) F := by
  rw [mem_borelSubgroup_iff]
  change BM F w t₁ c t₂ 1 0 = 0
  refine IwasawaWeyl.adele_ext F (fun w' => ?_) (fun u => ?_)
  · by_cases hw : w' = w
    · subst hw; rw [BM_fst_self]; rfl
    · rw [BM_fst_of_ne F w t₁ c t₂ _ _ hw, Matrix.one_apply_ne (by decide)]; rfl
  · rw [BM_snd, Matrix.one_apply_ne (by decide)]; rfl

private theorem distribHaarChar_fst :
    (distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagFst (⟨Bel F w t₁ c t₂ h₁ h₂, Bel_mem F w t₁ c t₂ h₁ h₂⟩ : adelicBorel (𝓞 F) F)) : ℝ)
      = ‖t₁‖ ^ w.mult := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, borelDiagFst_apply_val]
  change (∏ w' : InfinitePlace F, ‖(BM F w t₁ c t₂ 0 0).1 w'‖ ^ w'.mult) * ∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖(BM F w t₁ c t₂ 0 0).2 u‖ = _
  rw [finprod_eq_one_of_forall_eq_one fun u => by rw [BM_snd, Matrix.one_apply_eq, norm_one], mul_one]
  rw [Finset.prod_eq_single w (fun w' _ hw' => by rw [BM_fst_of_ne F w t₁ c t₂ _ _ hw', Matrix.one_apply_eq, norm_one, one_pow])
    (fun h => absurd (Finset.mem_univ w) h), BM_fst_self]
  rfl

private theorem distribHaarChar_snd :
    (distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagSnd (⟨Bel F w t₁ c t₂ h₁ h₂, Bel_mem F w t₁ c t₂ h₁ h₂⟩ : adelicBorel (𝓞 F) F)) : ℝ)
      = ‖t₂‖ ^ w.mult := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, borelDiagSnd_apply_val]
  change (∏ w' : InfinitePlace F, ‖(BM F w t₁ c t₂ 1 1).1 w'‖ ^ w'.mult) * ∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖(BM F w t₁ c t₂ 1 1).2 u‖ = _
  rw [finprod_eq_one_of_forall_eq_one fun u => by rw [BM_snd, Matrix.one_apply_eq, norm_one], mul_one]
  rw [Finset.prod_eq_single w (fun w' _ hw' => by rw [BM_fst_of_ne F w t₁ c t₂ _ _ hw', Matrix.one_apply_eq, norm_one, one_pow])
    (fun h => absurd (Finset.mem_univ w) h), BM_fst_self]
  rfl

end Beta

section Ext

/-- Wire restatement of `AutomorphicForm.eq_of_glArch_eq_of_glFin_eq`
(`AutomorphicForm/Adelic/LevelCompactness.lean`) in the `glFin`-pointwise spelling this module's
`spec-pin:` file states; the finite part is the `glFin_ext` bridge, not a re-proof. -/
theorem gl_ext {g h : AdelicGL2 (𝓞 F) F} (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : ∀ u, finComponent (𝓞 F) F u (glFin (𝓞 F) F g) = finComponent (𝓞 F) F u (glFin (𝓞 F) F h)) :
    g = h :=
  eq_of_glArch_eq_of_glFin_eq F h₁ (glFin_ext F h₂)

omit [NumberField F] in
/-- Wire restatement of `AutomorphicForm.ext_archComponent`
(`AutomorphicForm/Adelic/ArchComponentDictionary.lean`, the one home of the fact). -/
theorem glArch_ext {g h : GL (Fin 2) (InfiniteAdeleRing F)}
    (H : ∀ w' : InfinitePlace F, archComponent F w' g = archComponent F w' h) : g = h :=
  ext_archComponent H

theorem archComponent_weylUnip (x : AdeleRing (𝓞 F) F) (w' : InfinitePlace F) :
    ((archComponent F w' (glArch (𝓞 F) F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)) : GL (Fin 2) w'.Completion) :
        Matrix (Fin 2) (Fin 2) w'.Completion) = !![0, 1; 1, x.1 w'] :=
  IwasawaWeyl.archComponent_weylUnip_coe F x w'

theorem finComponent_weylUnip (x : AdeleRing (𝓞 F) F) (u : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F u (glFin (𝓞 F) F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)) : GL (Fin 2) (u.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (u.adicCompletion F)) = !![0, 1; 1, x.2 u] :=
  IwasawaWeyl.finComponent_weylUnip_coe F x u

end Ext

section BelComponents

variable (t₁ c t₂ : w.Completion) (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0)

private theorem archComponent_Bel_self :
    ((archComponent F w (glArch (𝓞 F) F (Bel F w t₁ c t₂ h₁ h₂)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) = βloc F w t₁ c t₂ := by
  refine Matrix.ext fun i j => ?_
  rw [archComponent_apply, glArch_apply]
  exact BM_fst_self F w t₁ c t₂ i j

private theorem archComponent_Bel_of_ne {w' : InfinitePlace F} (hw : w' ≠ w) :
    archComponent F w' (glArch (𝓞 F) F (Bel F w t₁ c t₂ h₁ h₂)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [archComponent_apply, glArch_apply]
  exact BM_fst_of_ne F w t₁ c t₂ i j hw

private theorem finComponent_Bel (u : HeightOneSpectrum (𝓞 F)) :
    finComponent (𝓞 F) F u (glFin (𝓞 F) F (Bel F w t₁ c t₂ h₁ h₂)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [finComponent_apply, glFin_apply]
  exact BM_snd F w t₁ c t₂ i j u

end BelComponents

section Main

variable (k : AdelicGL2 (𝓞 F) F) (hkf : glFin (𝓞 F) F k = 1)
  (hka : ∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k) = 1)

local notation "KW" => (((archComponent F w (glArch (𝓞 F) F k)) : GL (Fin 2) (InfinitePlace.Completion w)) :
  Matrix (Fin 2) (Fin 2) (InfinitePlace.Completion w))

theorem det_ne : Matrix.det KW ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero

def moeb (x : AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F :=
  (Function.update x.1 w ((KW 0 1 + x.1 w * KW 1 1) / (KW 0 0 + x.1 w * KW 1 0)), x.2)

theorem moeb_fst_self (x : AdeleRing (𝓞 F) F) :
    (moeb F w k x).1 w = (KW 0 1 + x.1 w * KW 1 1) / (KW 0 0 + x.1 w * KW 1 0) := by
  unfold moeb
  exact Function.update_self w _ x.1

theorem moeb_fst_of_ne (x : AdeleRing (𝓞 F) F) {w' : InfinitePlace F} (hw : w' ≠ w) :
    (moeb F w k x).1 w' = x.1 w' := by
  unfold moeb
  exact Function.update_of_ne hw _ x.1

theorem moeb_snd (x : AdeleRing (𝓞 F) F) : (moeb F w k x).2 = x.2 := rfl

theorem local_identity {K : Type*} [Field K] (x : K) (M : Matrix (Fin 2) (Fin 2) K) (t : K)
    (ht : t = M 0 0 + x * M 1 0) (h : t ≠ 0) :
    !![(0 : K), 1; 1, x] * M = !![M.det / t, M 1 0; 0, t] * !![(0 : K), 1; 1, (M 0 1 + x * M 1 1) / t] := by
  conv_lhs => rw [Matrix.eta_fin_two M]
  simp only [Matrix.mul_fin_two, Matrix.det_fin_two, zero_mul, one_mul, zero_add, mul_one, mul_zero]
  rw [mul_div_cancel₀ _ h, ← ht]
  congr
  field_simp
  rw [ht]; ring

include hkf hka in
theorem bruhat (x : AdeleRing (𝓞 F) F) (hx : KW 0 0 + x.1 w * KW 1 0 ≠ 0) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k =
      Bel F w (Matrix.det KW / (KW 0 0 + x.1 w * KW 1 0)) (KW 1 0) (KW 0 0 + x.1 w * KW 1 0)
          (div_ne_zero (det_ne F w k) hx) hx *
        ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (moeb F w k x)) := by
  set A : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x with hA
  set A' : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (moeb F w k x) with hA'
  refine gl_ext F (glArch_ext F fun w' => ?_) fun u => ?_
  · simp only [map_mul]
    rcases eq_or_ne w' w with rfl | hw
    · refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, hA, hA', archComponent_weylUnip, archComponent_weylUnip, archComponent_Bel_self,
        moeb_fst_self]
      exact local_identity (x.1 _) _ _ rfl hx
    · rw [hka w' hw, archComponent_Bel_of_ne F w _ _ _ _ _ hw, mul_one, one_mul]
      refine Units.ext ?_
      rw [hA, hA', archComponent_weylUnip, archComponent_weylUnip, moeb_fst_of_ne F w k x hw]
  · simp only [map_mul]
    rw [hkf, finComponent_Bel, map_one, mul_one, one_mul]
    refine Units.ext ?_
    rw [hA, hA', finComponent_weylUnip, finComponent_weylUnip, moeb_snd]

theorem cpow_scalar {D A : ℝ} (hD : 0 ≤ D) (hA : 0 < A) (s : ℂ) :
    (((D / A : ℝ)) : ℂ) ^ (s + 1 / 2) * ((A : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = ((D : ℝ) : ℂ) ^ (s + 1 / 2) * ((A : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hA0 : ((A : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have harg : ((A : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hA.le]; exact Real.pi_ne_zero.symm
  have h2 : ((A : ℝ) : ℂ) ^ (-(2 * s + 1)) = ((A : ℝ) : ℂ) ^ (-(s + 1 / 2)) * ((A : ℝ) : ℂ) ^ (-(s + 1 / 2)) := by
    rw [← Complex.cpow_add _ _ hA0]; congr 1; ring
  rw [h2, div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hD (inv_nonneg.mpr hA.le),
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  ring

theorem etaFst_one_val (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((etaFst 1 α hα s t : ℂˣ) : ℂ) = ((((α t) : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) := by
  rw [etaFst, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]

theorem etaSnd_one_val (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((etaSnd 1 α hα s t : ℂˣ) : ℂ) = ((((α t) : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) := by
  rw [etaSnd, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]

include hkf hka in
theorem main (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαv : ∀ t, ((α t : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) t : ℝ))
    (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
    (x : AdeleRing (𝓞 F) F) (hx : KW 0 0 + x.1 w * KW 1 0 ≠ 0) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k)
      = (((‖Matrix.det KW‖ ^ w.mult : ℝ)) : ℂ) ^ (s + 1 / 2)
        * (((‖KW 0 0 + x.1 w * KW 1 0‖ ^ w.mult : ℝ)) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (moeb F w k x)) := by
  rw [bruhat F w k hkf hka x hx, hφ _ (Bel_mem F w _ _ _ _ _)]
  congr 1
  rw [etaFst_one_val, etaSnd_one_val, hαv, hαv, distribHaarChar_fst, distribHaarChar_snd, norm_div, div_pow]
  exact cpow_scalar (pow_nonneg (norm_nonneg _) _) (pow_pos (norm_pos_iff.mpr hx) _) s

end Main

end MOEBW

theorem apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (w : InfinitePlace F) (k : AdelicGL2 (𝓞 F) F)
      (_hkf : glFin (𝓞 F) F k = 1)
      (_hka : ∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k) = 1)
      (x : AdeleRing (𝓞 F) F),
    let kw : Matrix (Fin 2) (Fin 2) w.Completion := (archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion)
    ∀ (_hx : kw 0 0 + x.1 w * kw 1 0 ≠ 0),
    let x' : AdeleRing (𝓞 F) F := (Function.update x.1 w ((kw 0 1 + x.1 w * kw 1 1) / (kw 0 0 + x.1 w * kw 1 0)), x.2)
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k)
      = (((‖kw.det‖ ^ w.mult : ℝ)) : ℂ) ^ (s + 1 / 2)
        * (((‖kw 0 0 + x.1 w * kw 1 0‖ ^ w.mult : ℝ)) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x') := by
  intro α hα s φ hφ w k hkf hka x kw hx
  exact MOEBW.main F w k hkf hka α hα (fun t => rfl) s φ hφ x hx

namespace BRUHATW

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

abbrev atPlace (g : GL (Fin 2) (v.adicCompletion F)) : AdelicGL2 (𝓞 F) F :=
  AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v g)

theorem glArch_atPlace (g : GL (Fin 2) (v.adicCompletion F)) : glArch (𝓞 F) F (atPlace F v g) = 1 :=
  AdelicDock.glArch_finEmbed _ _ _

theorem finComponent_atPlace_self (g : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (atPlace F v g)) = g := by
  rw [atPlace, AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self]

theorem finComponent_atPlace_of_ne (g : GL (Fin 2) (v.adicCompletion F)) {u : HeightOneSpectrum (𝓞 F)} (hu : u ≠ v) :
    finComponent (𝓞 F) F u (glFin (𝓞 F) F (atPlace F v g)) = 1 := by
  rw [atPlace, AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hu]

theorem atPlace_entry (g : GL (Fin 2) (v.adicCompletion F)) (i j : Fin 2) :
    ((atPlace F v g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        AdelicDock.splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j)) := rfl

def beta (t : v.adicCompletion F) (ht : t ≠ 0) : GL (Fin 2) (v.adicCompletion F) :=
  ⟨!![-t⁻¹, 1; 0, t], !![-t, 1; 0, t⁻¹],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht]⟩

theorem coe_beta (t : v.adicCompletion F) (ht : t ≠ 0) :
    ((beta F v t ht : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![-t⁻¹, 1; 0, t] := rfl

theorem atPlace_beta_mem (t : v.adicCompletion F) (ht : t ≠ 0) : atPlace F v (beta F v t ht) ∈ adelicBorel (𝓞 F) F := by
  rw [mem_borelSubgroup_iff, atPlace_entry]
  refine Prod.ext ?_ (RestrictedProduct.ext _ _ fun u => ?_)
  · rfl
  · by_cases hu : u = v
    · subst hu
      change AdelicDock.splice (𝓞 F) F u _ _ u = (0 : FiniteAdeleRing (𝓞 F) F) u
      rw [AdelicDock.splice_apply_self, coe_beta]; rfl
    · change AdelicDock.splice (𝓞 F) F v _ _ u = (0 : FiniteAdeleRing (𝓞 F) F) u
      rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu, Matrix.one_apply_ne (by decide)]

def spl (x : AdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (x.1, AdelicDock.splice (𝓞 F) F v x.2 (x.2 v)⁻¹)

theorem spl_fst (x : AdeleRing (𝓞 F) F) : (spl F v x).1 = x.1 := rfl
theorem spl_snd_self (x : AdeleRing (𝓞 F) F) : (spl F v x).2 v = (x.2 v)⁻¹ := AdelicDock.splice_apply_self _ _ _ _ _
theorem spl_snd_of_ne (x : AdeleRing (𝓞 F) F) {u : HeightOneSpectrum (𝓞 F)} (hu : u ≠ v) : (spl F v x).2 u = x.2 u :=
  AdelicDock.splice_apply_of_ne _ _ _ _ _ hu

theorem bruhat (x : AdeleRing (𝓞 F) F) (hx : x.2 v ≠ 0) :
    (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * atPlace F v gl2Weyl =
      atPlace F v (beta F v (x.2 v) hx) *
        ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (spl F v x)) := by
  set A : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x with hA
  set A' : AdelicGL2 (𝓞 F) F := (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (spl F v x) with hA'
  refine MOEBW.gl_ext F ?_ fun u => ?_
  · simp only [map_mul, glArch_atPlace, mul_one, one_mul]
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [hA, hA', glArch_apply, glArch_apply, IwasawaWeyl.coe_weylInv_mul_unipotent, IwasawaWeyl.coe_weylInv_mul_unipotent]
    fin_cases i <;> fin_cases j <;> rfl
  · simp only [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [finComponent_atPlace_self, finComponent_atPlace_self]
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, hA, hA', IwasawaWeyl.finComponent_weylUnip_coe, IwasawaWeyl.finComponent_weylUnip_coe, coe_beta, gl2Weyl_val,
        spl_snd_self]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]
    · rw [finComponent_atPlace_of_ne F v _ hu, finComponent_atPlace_of_ne F v _ hu, mul_one, one_mul]
      refine Units.ext ?_
      rw [hA, hA', IwasawaWeyl.finComponent_weylUnip_coe, IwasawaWeyl.finComponent_weylUnip_coe, spl_snd_of_ne F v x hu]

theorem distribHaarChar_borelDiagFst_beta (t : v.adicCompletion F) (ht : t ≠ 0) :
    (distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagFst (⟨atPlace F v (beta F v t ht), atPlace_beta_mem F v t ht⟩ : adelicBorel (𝓞 F) F)) : ℝ)
      = ‖t‖⁻¹ := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, borelDiagFst_apply_val]
  change (∏ w : InfinitePlace F, ‖(((atPlace F v (beta F v t ht) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).1 w‖ ^ w.mult) *
    ∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖(((atPlace F v (beta F v t ht) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 u‖ = _
  rw [atPlace_entry]
  have h1 : ∀ w : InfinitePlace F, ‖((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0) w‖ ^ w.mult = 1 := fun w => by
    rw [Matrix.one_apply_eq]; change ‖(1 : w.Completion)‖ ^ w.mult = 1; rw [norm_one, one_pow]
  rw [Finset.prod_eq_one fun w _ => h1 w, one_mul]
  rw [finprod_eq_single _ v fun u hu => ?_]
  · change ‖(AdelicDock.splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0) _) v‖ = _
    rw [AdelicDock.splice_apply_self, coe_beta]
    simp
  · change ‖(AdelicDock.splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0) _) u‖ = 1
    rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu, Matrix.one_apply_eq]
    change ‖(1 : u.adicCompletion F)‖ = 1
    exact norm_one

theorem distribHaarChar_borelDiagSnd_beta (t : v.adicCompletion F) (ht : t ≠ 0) :
    (distribHaarChar (AdeleRing (𝓞 F) F) (borelDiagSnd (⟨atPlace F v (beta F v t ht), atPlace_beta_mem F v t ht⟩ : adelicBorel (𝓞 F) F)) : ℝ)
      = ‖t‖ := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm, borelDiagSnd_apply_val]
  change (∏ w : InfinitePlace F, ‖(((atPlace F v (beta F v t ht) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w‖ ^ w.mult) *
    ∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖(((atPlace F v (beta F v t ht) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 u‖ = _
  rw [atPlace_entry]
  have h1 : ∀ w : InfinitePlace F, ‖((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1) w‖ ^ w.mult = 1 := fun w => by
    rw [Matrix.one_apply_eq]; change ‖(1 : w.Completion)‖ ^ w.mult = 1; rw [norm_one, one_pow]
  rw [Finset.prod_eq_one fun w _ => h1 w, one_mul]
  rw [finprod_eq_single _ v fun u hu => ?_]
  · change ‖(AdelicDock.splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) _) v‖ = _
    rw [AdelicDock.splice_apply_self, coe_beta]
    simp
  · change ‖(AdelicDock.splice (𝓞 F) F v ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1) _) u‖ = 1
    rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ hu, Matrix.one_apply_eq]
    change ‖(1 : u.adicCompletion F)‖ = 1
    exact norm_one

theorem cpow_scalar {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((r⁻¹ : ℝ) : ℂ) ^ (s + 1 / 2) * ((r : ℝ) : ℂ) ^ (-(s + 1 / 2)) = ((r : ℝ) : ℂ) ^ (-(2 * s + 1)) := by
  have hr0 : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm),
    ← Complex.cpow_neg, ← Complex.cpow_add _ _ hr0]
  congr 1; ring

theorem main (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαv : ∀ t, ((α t : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) t : ℝ))
    (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
    (x : AdeleRing (𝓞 F) F) (hx : x.2 v ≠ 0) :
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * atPlace F v gl2Weyl)
      = (((LanglandsTunnell.TateLocal.modulus (x.2 v) : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (spl F v x)) := by
  rw [bruhat F v x hx, hφ _ (atPlace_beta_mem F v (x.2 v) hx)]
  congr 1
  have e1 : ((etaFst 1 α hα s (borelDiagFst (⟨atPlace F v (beta F v (x.2 v) hx), atPlace_beta_mem F v (x.2 v) hx⟩ : adelicBorel (𝓞 F) F)) : ℂˣ) : ℂ) =
      ((((α (borelDiagFst (⟨atPlace F v (beta F v (x.2 v) hx), atPlace_beta_mem F v (x.2 v) hx⟩ : adelicBorel (𝓞 F) F)) : ℝˣ) : ℝ)) : ℂ) ^ (s + 1 / 2) := by
    rw [etaFst, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]
  have e2 : ((etaSnd 1 α hα s (borelDiagSnd (⟨atPlace F v (beta F v (x.2 v) hx), atPlace_beta_mem F v (x.2 v) hx⟩ : adelicBorel (𝓞 F) F)) : ℂˣ) : ℂ) =
      ((((α (borelDiagSnd (⟨atPlace F v (beta F v (x.2 v) hx), atPlace_beta_mem F v (x.2 v) hx⟩ : adelicBorel (𝓞 F) F)) : ℝˣ) : ℝ)) : ℂ) ^ (-(s + 1 / 2)) := by
    rw [etaSnd, MonoidHom.mul_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul, cpowChar_apply_val]
  rw [e1, e2, hαv, hαv, distribHaarChar_borelDiagFst_beta, distribHaarChar_borelDiagSnd_beta,
    NumberField.TateGlobal.modulus_adicCompletion_eq_nnnorm, coe_nnnorm]
  exact cpow_scalar (norm_pos_iff.mpr hx) s

end BRUHATW

theorem apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (v : HeightOneSpectrum (𝓞 F)) (x : AdeleRing (𝓞 F) F) (_hx : x.2 v ≠ 0),
    let x' : AdeleRing (𝓞 F) F := (x.1, AdelicDock.splice (𝓞 F) F v x.2 (x.2 v)⁻¹)
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x
          * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v gl2Weyl))
      = (((LanglandsTunnell.TateLocal.modulus (x.2 v) : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x') := by
  intro α hα s φ hφ v x hx
  exact BRUHATW.main F v α hα (fun t => rfl) s φ hφ x hx

end AutomorphicForm
