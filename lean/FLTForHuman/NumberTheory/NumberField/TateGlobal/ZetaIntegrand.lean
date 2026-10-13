/-
  The zeta integrand: the assembly character `char_asm`, the factorized form
  `apply_asm_of_isFactorizableStandardOutside`, the truncation `truncDeep` and
  the triviality of the character on the deep units, the local integrands
  `archLocalIntegrand`/`finLocalIntegrand`/`archIntegrand`/`sIntegrand`, the
  factorized integrand `zetaIntegrand_asm` and the master identity
  `setIntegral_unitsOutside_zetaIntegrand_eq`.

  Transcribed from the pin's `Fold_TateFubini` section, declared lines
  3932-4211 of file A, pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped; no file-wide option
  beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ArchSlab

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal

section Fold_TateFubini



open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in
-- pin: archPiUnits_archUnits_archUnitHom (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3904)
theorem archPiUnits_archUnits_archUnitHom (w : InfinitePlace F) (u : (w.Completion)ˣ) :
    archPiUnits (archUnits (archUnitHom w u)) = Pi.mulSingle w u := by
  funext w'
  refine Units.ext ?_
  rw [archPiUnits_apply]
  show Function.update (1 : InfiniteAdeleRing F) w (u : w.Completion) w'
    = ((Pi.mulSingle w u : (w' : InfinitePlace F) → (w'.Completion)ˣ) w' : w'.Completion)
  -- `InfiniteAdeleRing` is a `def`: ascribe the unfolded `Pi` type for `Function.update`
  rw [show Function.update (1 : InfiniteAdeleRing F) w (u : w.Completion)
      = Function.update (1 : (a : InfinitePlace F) → a.Completion) w (u : w.Completion) from rfl]
  by_cases h : w' = w
  · subst h
    rw [Function.update_self, Pi.mulSingle_eq_same]
  · rw [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    rfl

open scoped Classical in
-- pin: archAsm_eq_prod_archUnitHom (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3918)
theorem archAsm_eq_prod_archUnitHom (a : (InfiniteAdeleRing F)ˣ) :
    archAsm a = ∏ w, archUnitHom w (archPiUnits a w) := by
  refine idele_ext ?_ (fun v => ?_)
  · apply (archPiUnits (F := F)).injective
    rw [archUnits_archAsm, map_prod, map_prod]
    simp_rw [archPiUnits_archUnits_archUnitHom]
    exact (Finset.univ_prod_mulSingle _).symm
  · rw [unitAtHom_archAsm, map_prod]
    exact (Finset.prod_eq_one fun w _ => Units.ext rfl).symm

section AlongAsm

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- pin: char_asm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3932)
theorem char_asm (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (q : Q (F := F) S) :
    χ (asm S q) = (∏ w, archLocalChar χ w (archPiUnits q.1 w))
      * ((∏ v : S, localChar χ v.1 (q.2.1 v)) * χ (deepAsm S q.2.2)) := by
  rw [asm_apply, map_mul, map_mul, archAsm_eq_prod_archUnitHom, map_prod, sAsm_apply, map_prod]
  rfl

-- pin: distribHaarChar_deepAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3938)
theorem distribHaarChar_deepAsm (o : DeepUnits (F := F) S) :
    distribHaarChar (AdeleRing (𝓞 F) F) (deepAsm S o) = 1 := by
  refine distribHaarChar_eq_one_of_integral (deepAsm_val_fst S o) (fun w => ?_) (fun w => ?_)
  · rw [deepAsm_val_snd_apply]
    exact SetLike.coe_mem _
  · rw [← map_inv, deepAsm_val_snd_apply]
    exact SetLike.coe_mem _

-- pin: ideleNorm_asm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3946)
theorem ideleNorm_asm (q : Q (F := F) S) :
    ideleNorm F (asm S q) = (∏ w, ((distribHaarChar (w.Completion) (archPiUnits q.1 w) : ℝ≥0) : ℝ))
      * ∏ v : S, ((distribHaarChar (v.1.adicCompletion F) (q.2.1 v) : ℝ≥0) : ℝ) := by
  unfold ideleNorm
  rw [asm_apply, map_mul, map_mul, archAsm_eq_prod_archUnitHom, map_prod, sAsm_apply, map_prod,
    distribHaarChar_deepAsm, mul_one]
  simp_rw [distribHaarChar_archUnitHom, distribHaarChar_embUnit_eq_local]
  push_cast
  rfl

-- pin: asm_val_fst_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3956)
theorem asm_val_fst_apply (q : Q (F := F) S) (w : InfinitePlace F) :
    ((asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = ((archPiUnits q.1 w : (w.Completion)ˣ) : w.Completion) :=
  congrArg (fun u : (InfiniteAdeleRing F)ˣ => (u : InfiniteAdeleRing F) w) (archUnits_asm S q)

-- pin: asm_val_snd_apply_of_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3961)
theorem asm_val_snd_apply_of_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (((asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
      = ((q.2.1 ⟨v, hv⟩ : (v.adicCompletion F)ˣ) : v.adicCompletion F) :=
  congrArg (fun u : (v.adicCompletion F)ˣ => (u : v.adicCompletion F)) (unitAtHom_asm_of_mem S q hv)

-- pin: asm_val_mem_integralOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3966)
theorem asm_val_mem_integralOutside (q : Q (F := F) S) :
    ((asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ integralOutside S :=
  ((mem_unitsOutside_iff S _).mp (asm_mem_unitsOutside S q)).1

-- pin: apply_asm_of_isFactorizableStandardOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3970)
theorem apply_asm_of_isFactorizableStandardOutside {f : AdeleRing (𝓞 F) F → ℂ}
    {g : (w : InfinitePlace F) → w.Completion → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsFactorizableStandardOutside f S g h) (q : Q (F := F) S) :
    f (asm S q) = (∏ w, g w (archPiUnits q.1 w)) * ∏ v : S, h v.1 (q.2.1 v) := by
  rw [hf, Set.indicator_of_mem (asm_val_mem_integralOutside S q)]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => by rw [asm_val_fst_apply]
  · rw [← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => by rw [asm_val_snd_apply_of_mem S q v.2]

end AlongAsm

-- pin: cpow_prod_ofReal_nonneg (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3983)
theorem cpow_prod_ofReal_nonneg {ι : Type*} (s : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) (z : ℂ) :
    (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ z = ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ z := by
  classical
  refine @Finset.induction_on ι (fun s => (∀ i ∈ s, 0 ≤ r i) →
      (((∏ i ∈ s, r i : ℝ)) : ℂ) ^ z = ∏ i ∈ s, ((r i : ℝ) : ℂ) ^ z) _ s (fun _ => by simp) ?_ hr
  intro a s ha ih hr
  rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (hr a (Finset.mem_insert_self a s))
      (Finset.prod_nonneg fun i hi => hr i (Finset.mem_insert_of_mem hi)) z,
    ih fun i hi => hr i (Finset.mem_insert_of_mem hi)]

section DeepTrivial

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

open scoped Classical in
-- pin: truncDeep (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:3999)
def truncDeep (T : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) (o : DeepUnits (F := F) S) :
    DeepUnits (F := F) S :=
  fun v => if v ∈ T then o v else 1

-- pin: truncDeep_empty (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4003)
theorem truncDeep_empty (o : DeepUnits (F := F) S) : truncDeep S ∅ o = 1 := by
  funext v
  simp [truncDeep]

open scoped Classical in
-- pin: truncDeep_insert (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4008)
theorem truncDeep_insert {T : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S}}
    {v₀ : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}} (hv₀ : v₀ ∉ T) (o : DeepUnits (F := F) S) :
    truncDeep S (insert v₀ T) o = Pi.mulSingle v₀ (o v₀) * truncDeep S T o := by
  funext v
  simp only [truncDeep, Pi.mul_apply, Finset.mem_insert]
  by_cases h : v = v₀
  · subst h
    rw [Pi.mulSingle_eq_same, ite_eq_left (Or.inl rfl), ite_eq_right hv₀, mul_one]
  · rw [Pi.mulSingle_eq_of_ne h, one_mul]
    by_cases hT : v ∈ T
    · rw [ite_eq_left (Or.inr hT), ite_eq_left hT]
    · rw [ite_eq_right (not_or.mpr ⟨h, hT⟩), ite_eq_right hT]

open scoped Classical in
-- pin: tendsto_truncDeep (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4022)
theorem tendsto_truncDeep (o : DeepUnits (F := F) S) : Tendsto (fun T => truncDeep S T o) atTop (𝓝 o) := by
  refine tendsto_pi_nhds.mpr fun v => ?_
  refine (tendsto_const_nhds (x := o v)).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ({v} : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S})] with T hT
  show o v = truncDeep S T o v
  simp only [truncDeep]
  rw [ite_eq_left (Finset.singleton_subset_iff.mp hT)]

-- pin: coe_unitsMap_integers_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4030)
theorem coe_unitsMap_integers_mem {v : HeightOneSpectrum (𝓞 F)} (u : (v.adicCompletionIntegers F)ˣ) :
    ((Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      ∈ v.adicCompletionIntegers F :=
  (u : v.adicCompletionIntegers F).2

-- pin: coe_unitsMap_integers_inv_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4035)
theorem coe_unitsMap_integers_inv_mem {v : HeightOneSpectrum (𝓞 F)} (u : (v.adicCompletionIntegers F)ˣ) :
    (((Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u : (v.adicCompletion F)ˣ)⁻¹
        : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  rw [← map_inv]
  exact ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2

open scoped Classical in
-- pin: deepAsm_mulSingle (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4042)
theorem deepAsm_mulSingle {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) (u : (v.adicCompletionIntegers F)ˣ) :
    deepAsm S (Pi.mulSingle (⟨v, hv⟩ : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) u)
      = embUnit v (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) := by
  refine idele_ext ?_ (fun w => ?_)
  · rw [archUnits_deepAsm]
    exact (Units.ext (embUnit_val_fst v (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u))).symm
  · by_cases hw : w ∈ S
    · rw [unitAtHom_deepAsm_of_mem S _ hw, unitAtHom_embUnit_of_ne]
      exact fun h => hv (h ▸ hw)
    · rw [unitAtHom_deepAsm_of_not_mem S _ hw]
      by_cases hwv : w = v
      · subst hwv
        rw [Pi.mulSingle_eq_same, unitAtHom_embUnit_self]
      · rw [Pi.mulSingle_eq_of_ne (fun h => hwv (congrArg Subtype.val h)), map_one, unitAtHom_embUnit_of_ne hwv]

open scoped Classical in
-- pin: char_deepAsm_truncDeep (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4058)
theorem char_deepAsm_truncDeep (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v)
    (T : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) (o : DeepUnits (F := F) S) :
    χ (deepAsm S (truncDeep S T o)) = 1 := by
  induction T using Finset.induction_on with
  | empty => rw [truncDeep_empty, map_one, map_one]
  | @insert v₀ T hv₀ ih =>
    rw [truncDeep_insert S hv₀, map_mul, map_mul, ih, mul_one]
    obtain ⟨v, hv⟩ := v₀
    rw [deepAsm_mulSingle S hv]
    exact hχS v hv _ (coe_unitsMap_integers_mem _) (coe_unitsMap_integers_inv_mem _)

-- pin: char_deepAsm_eq_one (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4069)
theorem char_deepAsm_eq_one (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ)
    (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (o : DeepUnits (F := F) S) : χ (deepAsm S o) = 1 := by
  have hcont : Continuous fun o : DeepUnits (F := F) S => χ (deepAsm S o) :=
    hχc.comp (continuous_deepAsm S)
  have h1 : Tendsto (fun T => χ (deepAsm S (truncDeep S T o))) atTop (𝓝 (χ (deepAsm S o))) :=
    (hcont.tendsto o).comp (tendsto_truncDeep S o)
  have h2 : Tendsto (fun T : Finset {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => χ (deepAsm S (truncDeep S T o)))
      atTop (𝓝 1) := by
    simp_rw [char_deepAsm_truncDeep S χ hχS]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 h2

end DeepTrivial

section Integrands

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- pin: archLocalIntegrand (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4088)
def archLocalIntegrand (g : (w : InfinitePlace F) → w.Completion → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
    (w : InfinitePlace F) (u : (w.Completion)ˣ) : ℂ :=
  g w u * (archLocalChar χ w u : ℂ) * (((distribHaarChar (w.Completion) u : ℝ≥0) : ℝ) : ℂ) ^ s

-- pin: finLocalIntegrand (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4092)
def finLocalIntegrand (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) : ℂ :=
  h v u * (localChar χ v u : ℂ) * (((distribHaarChar (v.adicCompletion F) u : ℝ≥0) : ℝ) : ℂ) ^ s

-- pin: archIntegrand (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4096)
def archIntegrand (g : (w : InfinitePlace F) → w.Completion → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
    (a : (InfiniteAdeleRing F)ˣ) : ℂ :=
  ∏ w, archLocalIntegrand g χ s w (archPiUnits a w)

-- pin: sIntegrand (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4100)
def sIntegrand (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (s : ℂ) (t : SUnits (F := F) S) : ℂ :=
  ∏ v : S, finLocalIntegrand h χ s v.1 (t v)

-- pin: zetaIntegrand_asm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4104)
theorem zetaIntegrand_asm {f : AdeleRing (𝓞 F) F → ℂ} {g : (w : InfinitePlace F) → w.Completion → ℂ}
    {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ} (hf : IsFactorizableStandardOutside f S g h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ)
    (q : Q (F := F) S) :
    f (asm S q) * ((χ (asm S q) : ℂˣ) : ℂ) * ((ideleNorm F (asm S q) : ℝ) : ℂ) ^ s
      = archIntegrand g χ s q.1 * (sIntegrand S h χ s q.2.1 * (1 : DeepUnits (F := F) S → ℂ) q.2.2) := by
  rw [apply_asm_of_isFactorizableStandardOutside S hf, char_asm S χ, char_deepAsm_eq_one S χ hχc hχS, mul_one,
    ideleNorm_asm S, Units.val_mul, Units.coe_prod, Units.coe_prod, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun w _ => NNReal.coe_nonneg _)
      (Finset.prod_nonneg fun v _ => NNReal.coe_nonneg _),
    cpow_prod_ofReal_nonneg _ _ (fun w _ => NNReal.coe_nonneg _),
    cpow_prod_ofReal_nonneg _ _ (fun v _ => NNReal.coe_nonneg _),
    Pi.one_apply, mul_one]
  unfold archIntegrand sIntegrand archLocalIntegrand finLocalIntegrand
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end Integrands

section LocalIntegrals

section ArchLocal

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion))

-- pin: integral_archLocalIntegrand (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4132)
theorem integral_archLocalIntegrand (g : (w : InfinitePlace F) → w.Completion → ℂ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (w : InfinitePlace F) :
    ∫ u, archLocalIntegrand g χ s w u ∂(ArchMulHaarCompletion.mulHaarCompletion w (μa w))
      = localZeta (μa w) (g w) (archLocalChar χ w) s := by
  rw [localZeta_eq_integral_mulHaarCompletion]
  simp_rw [modulus_coe_units]
  rfl

end ArchLocal

section FinLocal

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))

-- pin: integral_finLocalIntegrand (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4151)
theorem integral_finLocalIntegrand (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    ∫ u, finLocalIntegrand h χ s v u ∂(MulHaarFromAdditive.mulHaar (μf v))
      = localZeta (μf v) (h v) (localChar χ v) s := by
  rw [localZeta_eq_integral_mulHaar]
  simp_rw [modulus_coe_units]
  rfl

end FinLocal

end LocalIntegrals

section Master

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

-- pin: setIntegral_unitsOutside_zetaIntegrand_eq (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:4184)
theorem setIntegral_unitsOutside_zetaIntegrand_eq {f : AdeleRing (𝓞 F) F → ℂ}
    {g : (w : InfinitePlace F) → w.Completion → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsFactorizableStandardOutside f S g h) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ)
    (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) :
    ∫ x in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
        f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν
      = ((refConst S μa μf ν : ℝ) : ℂ)
          * ((∏ w, localZeta (μa w) (g w) (archLocalChar χ w) s)
              * ∏ v ∈ S, localZeta (μf v) (h v) (localChar χ v) s) := by
  rw [setIntegral_unitsOutside_eq_refConst_mul S μa μf ν]
  congr 1
  have hpt : (fun q : Q (F := F) S =>
        f (asm S q) * ((χ (asm S q) : ℂˣ) : ℂ) * ((ideleNorm F (asm S q) : ℝ) : ℂ) ^ s)
      = fun q => archIntegrand g χ s q.1 * (sIntegrand S h χ s q.2.1 * (1 : DeepUnits (F := F) S → ℂ) q.2.2) :=
    funext fun q => zetaIntegrand_asm S hf χ hχc hχS s q
  rw [hpt, integral_refMeasure_mul S μa μf (archIntegrand g χ s) (sIntegrand S h χ s) 1]
  simp only [Pi.one_apply, integral_deepRef_const, mul_one]
  unfold archIntegrand sIntegrand
  rw [integral_archRef_prod μa (archLocalIntegrand g χ s),
    integral_sRef_prod S μf (fun v => finLocalIntegrand h χ s v.1)]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => integral_archLocalIntegrand μa g χ s w
  · calc ∏ v : S, ∫ u, finLocalIntegrand h χ s v.1 u ∂(MulHaarFromAdditive.mulHaar (μf v.1))
        = ∏ v : S, localZeta (μf v.1) (h v.1) (localChar χ v.1) s :=
          Finset.prod_congr rfl fun v _ => integral_finLocalIntegrand μf h χ s v.1
      _ = ∏ v ∈ S, localZeta (μf v) (h v) (localChar χ v) s :=
          Finset.prod_coe_sort S fun v => localZeta (μf v) (h v) (localChar χ v) s

end Master

end NumberField.TateGlobal

end



end Fold_TateFubini
