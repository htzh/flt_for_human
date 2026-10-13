/-
  The jointly-factorizable (indicator) form of the Euler-factor identity: the
  predicate `IsJointFactorizableOutside`, its assembly lemmas `asm_val_fst` and
  `apply_asm_of_isJointFactorizableOutside`, the archimedean integrand
  `archIntegrandJ` of a joint factor `G`, the per-shell rewriting
  `zetaIntegrand_asm`/`zetaIntegrand_unifPow_mul`, the integral over
  `unitsOutside` in shell form (`integral_eq_tsum_shellCoef_mul`), the master
  unfolding `hole_G2`, the joint form `zetaIntegral_mul_eulerFactors_eq_joint`
  and the pin's `solution`.

  Transcribed from
  `P2M/Sol/S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean`
  (pinned `aa2d8b3`; see
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean),
  file C of the TateGlobal analytic core.  The module holds exactly the 19
  declarations that C does not share with A or B, with their pin names and
  statements.  They are collected in the C-specific sub-theory
  `NumberField.TateGlobal.IndicatorEulerFactors`: fourteen of the names also
  occur in A's `NumberField.TateGlobal.G2Proof` with a different statement (the
  `IsFactorizableStandardOutside` predicate), so placing C's copies in a
  sub-namespace keeps both public.  The pin's `M4aLocalCFT.G2Proof` helpers that
  C shares with A (`placeFactor`, `shellCoef`, `unifOf_ϖ`, the `unifPow`-bridge
  bookkeeping and the shared shell lemmas) are opened from the port's
  `NumberField.TateGlobal.G2Proof` module, so the statements stay verbatim; the
  local C declarations shadow the opened ones for the colliding names.

  Build notes: the pin's `p2m_*` scaffolding is dropped, as are the file-scoped
  `set_option maxHeartbeats 1600000` / `maxSynthPendingDepth 3` (C 5126/5128)
  and the per-declaration `set_option synthInstance.maxHeartbeats 1600000 in`
  before `factorizable_apply_unifPow_mul` (C 5132).  The pin's file-scoped
  `attribute [local instance] countable_heightOneSpectrum` (C 5142) is
  re-declared here (work order §8.5).  `M4aLocalCFT.` is renamed to
  `NumberField.TateGlobal.`.  No file-wide option beyond
  `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.EulerFactors

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open AutomorphicForm
open scoped NNReal ENNReal Pointwise Topology Classical

noncomputable section

namespace NumberField
namespace TateGlobal
namespace IndicatorEulerFactors

open NumberField.TateGlobal.G2Proof

variable {F : Type} [Field F] [NumberField F]

-- pin: IsJointFactorizableOutside (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:32)
def IsJointFactorizableOutside (f : AdeleRing (𝓞 F) F → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (G : InfiniteAdeleRing F → ℂ) (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) : Prop :=
  ∀ x, f x = (integralOutside S).indicator
      (fun x => G x.1 * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x

section AlongAsm

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- pin: asm_val_fst (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:3975)
theorem asm_val_fst (q : Q (F := F) S) :
    ((asm S q : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = ((q.1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) :=
  congrArg (fun u : (InfiniteAdeleRing F)ˣ => (u : InfiniteAdeleRing F)) (archUnits_asm S q)

-- pin: apply_asm_of_isJointFactorizableOutside (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:3979)
theorem apply_asm_of_isJointFactorizableOutside {f : AdeleRing (𝓞 F) F → ℂ}
    {G : InfiniteAdeleRing F → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsJointFactorizableOutside f S G h) (q : Q (F := F) S) :
    f (asm S q) = G ((q.1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) * ∏ v : S, h v.1 (q.2.1 v) := by
  rw [hf, Set.indicator_of_mem (asm_val_mem_integralOutside S q)]
  congr 1
  · rw [asm_val_fst]
  · rw [← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => by rw [asm_val_snd_apply_of_mem S q v.2]

end AlongAsm

section Integrands

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- pin: archIntegrandJ (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:4105)
def archIntegrandJ (G : InfiniteAdeleRing F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ)
    (a : (InfiniteAdeleRing F)ˣ) : ℂ :=
  G (a : InfiniteAdeleRing F)
    * ∏ w, ((archLocalChar χ w (archPiUnits a w) : ℂ)
        * (((distribHaarChar (w.Completion) (archPiUnits a w) : ℝ≥0) : ℝ) : ℂ) ^ s)

-- pin: zetaIntegrand_asm (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:4115)
theorem zetaIntegrand_asm {f : AdeleRing (𝓞 F) F → ℂ} {G : InfiniteAdeleRing F → ℂ}
    {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ} (hf : IsJointFactorizableOutside f S G h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ)
    (q : Q (F := F) S) :
    f (asm S q) * ((χ (asm S q) : ℂˣ) : ℂ) * ((ideleNorm F (asm S q) : ℝ) : ℂ) ^ s
      = archIntegrandJ G χ s q.1 * (sIntegrand S h χ s q.2.1 * (1 : DeepUnits (F := F) S → ℂ) q.2.2) := by
  rw [apply_asm_of_isJointFactorizableOutside S hf, char_asm S χ, char_deepAsm_eq_one S χ hχc hχS, mul_one,
    ideleNorm_asm S, Units.val_mul, Units.coe_prod, Units.coe_prod, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun w _ => NNReal.coe_nonneg _)
      (Finset.prod_nonneg fun v _ => NNReal.coe_nonneg _),
    cpow_prod_ofReal_nonneg _ _ (fun w _ => NNReal.coe_nonneg _),
    cpow_prod_ofReal_nonneg _ _ (fun v _ => NNReal.coe_nonneg _),
    Pi.one_apply, mul_one]
  unfold archIntegrandJ sIntegrand finLocalIntegrand
  simp only [Finset.prod_mul_distrib]
  ring

end Integrands

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

-- pin: setIntegral_unitsOutside_zetaIntegrand_eq (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:4195)
theorem setIntegral_unitsOutside_zetaIntegrand_eq {f : AdeleRing (𝓞 F) F → ℂ}
    {G : InfiniteAdeleRing F → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsJointFactorizableOutside f S G h) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ)
    (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) :
    ∫ x in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
        f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν
      = ((refConst S μa μf ν : ℝ) : ℂ)
          * ((∫ a, archIntegrandJ G χ s a ∂(archRef μa))
              * ∏ v ∈ S, localZeta (μf v) (h v) (localChar χ v) s) := by
  rw [setIntegral_unitsOutside_eq_refConst_mul S μa μf ν]
  congr 1
  have hpt : (fun q : Q (F := F) S =>
        f (asm S q) * ((χ (asm S q) : ℂˣ) : ℂ) * ((ideleNorm F (asm S q) : ℝ) : ℂ) ^ s)
      = fun q => archIntegrandJ G χ s q.1 * (sIntegrand S h χ s q.2.1 * (1 : DeepUnits (F := F) S → ℂ) q.2.2) :=
    funext fun q => zetaIntegrand_asm S hf χ hχc hχS s q
  rw [hpt, integral_refMeasure_mul S μa μf (archIntegrandJ G χ s) (sIntegrand S h χ s) 1]
  simp only [Pi.one_apply, integral_deepRef_const, mul_one]
  congr 1
  unfold sIntegrand
  rw [integral_sRef_prod S μf (fun v => finLocalIntegrand h χ s v.1)]
  calc ∏ v : S, ∫ u, finLocalIntegrand h χ s v.1 u ∂(MulHaarFromAdditive.mulHaar (μf v.1))
      = ∏ v : S, localZeta (μf v.1) (h v.1) (localChar χ v.1) s :=
        Finset.prod_congr rfl fun v _ => integral_finLocalIntegrand μf h χ s v.1
    _ = ∏ v ∈ S, localZeta (μf v) (h v) (localChar χ v) s :=
        Finset.prod_coe_sort S fun v => localZeta (μf v) (h v) (localChar χ v) s

end Master

section Decomp4

-- pin: factorizable_apply_unifPow_mul (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:4329)
theorem factorizable_apply_unifPow_mul {f : AdeleRing (𝓞 F) F → ℂ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {G : InfiniteAdeleRing F → ℂ} {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}
    (hf : IsJointFactorizableOutside f S G h) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ∀ v ∈ S, k v = 0) {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = if ∀ v ∉ S, 0 ≤ k v then
          G (u : AdeleRing (𝓞 F) F).1 * ∏ v ∈ S, h v (((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v)
        else 0 := by
  classical
  rw [hf]
  have hval : (fun x : AdeleRing (𝓞 F) F => G x.1 * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v))
        ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = G (u : AdeleRing (𝓞 F) F).1 * ∏ v ∈ S, h v (((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v) := by
    show G (((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1)
        * ∏ v ∈ S, h v ((((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v) = _
    rw [unifPow_mul_val_fst]
    congr 1
    exact Finset.prod_congr rfl fun v hv => by rw [unifPow_mul_val_snd_apply_of_mem ϖ hk u hv]
  by_cases hpos : ∀ v ∉ S, 0 ≤ k v
  · rw [ite_eq_left hpos, Set.indicator_of_mem ((unifPow_mul_mem_integralOutside_iff ϖ hu).mpr hpos)]
    exact hval
  · rw [ite_eq_right hpos, Set.indicator_of_notMem]
    exact fun hmem => hpos ((unifPow_mul_mem_integralOutside_iff ϖ hu).mp hmem)

end Decomp4

section G2Cap

attribute [local instance] NumberField.TateGlobal.countable_heightOneSpectrum

section TestFunction

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

variable {f : AdeleRing (𝓞 F) F → ℂ} {G : InfiniteAdeleRing F → ℂ}
  {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}

-- pin: apply_unifPow_mul_eq (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5230)
theorem apply_unifPow_mul_eq (hf : IsJointFactorizableOutside f S G h) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hkS : ∀ v ∈ S, k v = 0) (hk : 0 ≤ k)
    {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = f (u : AdeleRing (𝓞 F) F) := by
  have e1 := factorizable_apply_unifPow_mul hf ϖ hkS hu
  have e0 := factorizable_apply_unifPow_mul hf ϖ (k := 0) (fun _ _ => rfl) hu
  rw [ite_eq_left (show ∀ v ∉ S, 0 ≤ k v from fun v _ => Finsupp.le_def.mp hk v)] at e1
  rw [ite_eq_left (show ∀ v ∉ S, 0 ≤ (0 : HeightOneSpectrum (𝓞 F) →₀ ℤ) v from fun _ _ => le_rfl),
    unifPow_zero ϖ, one_mul] at e0
  exact e1.trans e0.symm

-- pin: apply_unifPow_mul_eq_zero (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5241)
theorem apply_unifPow_mul_eq_zero (hf : IsJointFactorizableOutside f S G h) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hkS : ∀ v ∈ S, k v = 0) (hk : ¬ 0 ≤ k)
    {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = 0 := by
  rw [factorizable_apply_unifPow_mul hf ϖ hkS hu, ite_eq_right (not_forall_nonneg_of_not_nonneg S hkS hk)]

-- pin: zetaIntegrand_unifPow_mul (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5247)
theorem zetaIntegrand_unifPow_mul (hf : IsJointFactorizableOutside f S G h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hkS : ∀ v ∈ S, k v = 0) (hk : 0 ≤ k)
    {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * ((χ (unifPow ϖ k * u) : ℂˣ) : ℂ)
        * ((ideleNorm F (unifPow ϖ k * u) : ℝ) : ℂ) ^ s
      = (k.prod fun v n => placeFactor χ ϖ s v ^ n.toNat)
          * (f (u : AdeleRing (𝓞 F) F) * ((χ u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ s) := by
  rw [apply_unifPow_mul_eq hf ϖ hkS hk hu, map_mul, Units.val_mul, ideleNorm_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (ideleNorm_pos _).le (ideleNorm_pos _).le,
    coe_char_unifPow χ ϖ hk, ideleNorm_unifPow_cpow ϖ s hk]
  have hprod : (k.prod fun v n => placeFactor χ ϖ s v ^ n.toNat)
      = (k.prod fun v n => ((localChar χ v (ϖ.ϖ v) : ℂˣ) : ℂ) ^ n.toNat)
          * k.prod fun v n => ((((Ideal.absNorm v.asIdeal : ℕ)) : ℂ) ^ (-s)) ^ n.toNat := by
    rw [← Finsupp.prod_mul]
    simp only [placeFactor, mul_pow]
  rw [hprod]
  ring

end TestFunction

section PerShell

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

variable {f : AdeleRing (𝓞 F) F → ℂ} {G : InfiniteAdeleRing F → ℂ}
  {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}

-- pin: setIntegral_unitsOutside_translate (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5288)
theorem setIntegral_unitsOutside_translate (hf : IsJointFactorizableOutside f S G h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ) (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (k : ExpIndex (F := F) S) :
    ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
        f ((unifPow ϖ k.1 * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
          * ((χ (unifPow ϖ k.1 * u) : ℂˣ) : ℂ) * ((ideleNorm F (unifPow ϖ k.1 * u) : ℝ) : ℂ) ^ s ∂ν
      = shellCoef χ ϖ s k.1
          * ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
              f (u : AdeleRing (𝓞 F) F) * ((χ u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ s ∂ν := by
  by_cases hk : 0 ≤ k.1
  · rw [shellCoef_of_nonneg χ ϖ s hk, ← integral_const_mul]
    refine setIntegral_congr_fun (isOpen_unitsOutside S).measurableSet fun u hu => ?_
    exact zetaIntegrand_unifPow_mul hf χ ϖ s k.2 hk hu
  · rw [shellCoef_of_not_nonneg χ ϖ s hk, zero_mul]
    refine (setIntegral_congr_fun (isOpen_unitsOutside S).measurableSet fun u hu => ?_).trans
      (integral_zero _ _)
    rw [apply_unifPow_mul_eq_zero hf ϖ k.2 hk hu, zero_mul, zero_mul]

-- pin: integrableOn_shell (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5306)
theorem integrableOn_shell (hf : IsJointFactorizableOutside f S G h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ) (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    [ν.IsMulLeftInvariant] (k : ExpIndex (F := F) S)
    (hU : IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ =>
        f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
      (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν) :
    IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
      (shell S k.1) ν := by
  by_cases hk : 0 ≤ k.1
  · rw [shell_eq_smul ϖ k.2]
    have hemb : MeasurableEmbedding (fun u : (AdeleRing (𝓞 F) F)ˣ => unifPow ϖ k.1 * u) :=
      (Homeomorph.mulLeft (unifPow ϖ k.1)).measurableEmbedding
    have hmp := measurePreserving_mul_left ν (unifPow ϖ k.1)
    rw [← hmp.integrableOn_comp_preimage hemb, preimage_mul_smul]
    have h1 : IntegrableOn (fun u : (AdeleRing (𝓞 F) F)ˣ =>
        (k.1.prod fun v n => placeFactor χ ϖ s v ^ n.toNat)
          * (f (u : AdeleRing (𝓞 F) F) * ((χ u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ s))
        (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν := hU.const_mul _
    exact (integrableOn_congr_fun (fun u hu => zetaIntegrand_unifPow_mul hf χ ϖ s k.2 hk hu)
      (isOpen_unitsOutside S).measurableSet).mpr h1
  · refine (integrableOn_congr_fun (fun x hx => ?_) (measurableSet_shell ϖ k.2)).mpr integrableOn_zero
    rw [shell_eq_smul ϖ k.2] at hx
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
    rw [smul_eq_mul, apply_unifPow_mul_eq_zero hf ϖ k.2 hk hu, zero_mul, zero_mul]

-- pin: setIntegral_shell_norm_le' (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5331)
theorem setIntegral_shell_norm_le' (hf : IsJointFactorizableOutside f S G h)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ) (ϖ : Uniformizers F) (s : ℂ)
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant] (k : ExpIndex (F := F) S) (hk : 0 ≤ k.1) :
    ∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν
      ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat)
          * ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ), ‖f (u : AdeleRing (𝓞 F) F)‖
              * ideleNorm F u ^ s.re ∂ν :=
  ShellTranslate.setIntegral_shell_norm_le ν ϖ hχu k hk (le_of_eq
    (setIntegral_congr_fun (isOpen_unitsOutside S).measurableSet fun u hu => by
      rw [apply_unifPow_mul_eq hf ϖ k.2 hk hu]))

-- pin: setIntegral_shell_norm_eq_zero (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5342)
theorem setIntegral_shell_norm_eq_zero (hf : IsJointFactorizableOutside f S G h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) (k : ExpIndex (F := F) S) (hk : ¬ 0 ≤ k.1) :
    ∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν = 0 := by
  refine (setIntegral_congr_fun (measurableSet_shell ϖ k.2) fun x hx => ?_).trans (integral_zero _ _)
  rw [shell_eq_smul ϖ k.2] at hx
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
  rw [smul_eq_mul, apply_unifPow_mul_eq_zero hf ϖ k.2 hk hu, zero_mul, zero_mul, norm_zero]

-- pin: integrable_of_integrableOn_unitsOutside (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5351)
theorem integrable_of_integrableOn_unitsOutside (hf : IsJointFactorizableOutside f S G h)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ) (ϖ : Uniformizers F)
    {s : ℂ} (hs : 1 < s.re) (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant]
    (hU : IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ =>
        f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
      (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν) :
    Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν := by
  have hint : ∀ k : ExpIndex (F := F) S, IntegrableOn
      (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s)
      (shell S k.1) ν := fun k => integrableOn_shell hf χ ϖ s ν k hU
  have hsum : Summable fun k : ExpIndex (F := F) S =>
      ∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν :=
    ShellBound.summable_of_shell_bound hs _ (fun k => integral_nonneg fun x => norm_nonneg _)
      (integral_nonneg fun u => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ideleNorm_pos u).le _))
      (fun k hk => setIntegral_shell_norm_le' hf hχu ϖ s ν k hk)
      (fun k hk => setIntegral_shell_norm_eq_zero hf χ ϖ s ν k hk)
  have hall := MeasureTheory.integrableOn_iUnion_of_summable_integral_norm hint hsum
  rw [iUnion_shell] at hall
  exact integrableOn_univ.mp hall

-- pin: integral_eq_tsum_shellCoef_mul (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5371)
theorem integral_eq_tsum_shellCoef_mul (hf : IsJointFactorizableOutside f S G h)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ) (ϖ : Uniformizers F)
    {s : ℂ} (hs : 1 < s.re) (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant] :
    ∫ x, f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν
      = (∑' k : ExpIndex (F := F) S, shellCoef χ ϖ s k.1)
          * ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
              f (u : AdeleRing (𝓞 F) F) * ((χ u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ s ∂ν := by
  by_cases hU : IntegrableOn (fun x : (AdeleRing (𝓞 F) F)ˣ =>
      f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) ν
  · have hsum := hasSum_setIntegral_unitsOutside ν ϖ S
      (integrable_of_integrableOn_unitsOutside hf hχu ϖ hs ν hU)
    have hsum' : HasSum (fun k : ExpIndex (F := F) S => shellCoef χ ϖ s k.1
        * ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
            f (u : AdeleRing (𝓞 F) F) * ((χ u : ℂˣ) : ℂ) * ((ideleNorm F u : ℝ) : ℂ) ^ s ∂ν)
        (∫ x, f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν) :=
      hsum.congr_fun fun k => (setIntegral_unitsOutside_translate hf χ ϖ s ν k).symm
    rw [← hsum'.tsum_eq, tsum_mul_right]
  · have hI : ¬ Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ =>
        f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν := fun hI => hU hI.integrableOn
    rw [integral_undef hI, integral_undef hU, mul_zero]

end PerShell

end G2Cap

-- pin: hole_G2 (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5489)
theorem hole_G2 (F : Type) [Field F] [NumberField F] [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    [BorelSpace (AdeleRing (𝓞 F) F)ˣ] (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (f : AdeleRing (𝓞 F) F → ℂ) (G : InfiniteAdeleRing F → ℂ)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hf : IsJointFactorizableOutside f S G h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (hs : 1 < s.re) :
    (Summable fun k : {v // v ∉ S} →₀ ℕ =>
        ‖EulerBookkeeping.mono (fun v : {v // v ∉ S} => ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) k‖) ∧
    zetaIntegral ν f χ s
      = ((((refConst S μa μf ν : ℝ) : ℂ) * ∫ a, archIntegrandJ G χ s a ∂(archRef μa))
          * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s)
        * ∑' k : {v // v ∉ S} →₀ ℕ,
            EulerBookkeeping.mono (fun v : {v // v ∉ S} => ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) k := by
  have hsum := summable_norm_mono_placeFactor S hχu (unifOf ϖ hϖ) hs
  refine ⟨hsum, ?_⟩
  have hshell := integral_eq_tsum_shellCoef_mul (S := S) hf hχu (unifOf ϖ hϖ) hs ν
  have hmaster := setIntegral_unitsOutside_zetaIntegrand_eq S μa μf ν hf χ hχc hχS s
  have hre := tsum_shellCoef_eq_tsum_mono S χ (unifOf ϖ hϖ) s
  show ∫ x, f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s ∂ν = _
  rw [hshell, hmaster, hre]
  unfold placeFactor
  simp only [unifOf_ϖ]
  ring

-- The pin's `letI`/`haveI` instance wall is load-bearing here (the measures on
-- the archimedean and adic completion units and on the ideles), and the goal is a
-- proposition, which `linter.style.haveILetI` flags.
set_option linter.style.haveILetI false in
-- pin: zetaIntegral_mul_eulerFactors_eq_joint (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5531)
theorem zetaIntegral_mul_eulerFactors_eq_joint (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ A : (InfiniteAdeleRing F → ℂ) → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) → ℂ → ℂ,
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (G : InfiniteAdeleRing F → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : IsJointFactorizableOutside f S G h)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        zetaIntegral ν f χ s
            * ∏' v : {v // v ∉ S},
                (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
          = A G χ s * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s := by
  letI : ∀ w : InfinitePlace F, MeasurableSpace (w.Completion) := fun _ => borel _
  haveI : ∀ w : InfinitePlace F, BorelSpace (w.Completion) := fun _ => ⟨rfl⟩
  letI : ∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ := fun _ => borel _
  haveI : ∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ := fun _ => ⟨rfl⟩
  letI : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ := fun _ => borel _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ := fun _ => ⟨rfl⟩
  letI : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ := fun _ => borel _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ := fun _ => ⟨rfl⟩
  letI : MeasurableSpace (InfiniteAdeleRing F)ˣ := borel _
  haveI : BorelSpace (InfiniteAdeleRing F)ˣ := ⟨rfl⟩
  let μa : (w : InfinitePlace F) → Measure w.Completion := fun w =>
    Measure.addHaarMeasure
      (Classical.choice (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts w.Completion)))
  haveI : ∀ w, (μa w).IsAddHaarMeasure := fun _ => Measure.isAddHaarMeasure_addHaarMeasure _
  refine ⟨fun G χ s => ((refConst S μa μf ν : ℝ) : ℂ) * ∫ a, archIntegrandJ G χ s a ∂(archRef μa), ?_⟩
  intro f G h hf χ hχc hχu hχS s hs
  obtain ⟨hS, hZ⟩ := hole_G2 F ν S μf μa ϖ hϖ f G h hf χ hχc hχu hχS s hs
  rw [hZ, mul_assoc, EulerBookkeeping.tsum_mono_mul_tprod_one_sub hS, mul_one]

-- The pin's `solution` is the jointly-factorizable headline; it is named for what
-- it states under the C-specific sub-theory namespace and is re-stated at the
-- wrapper's name by the façade `FLTForHuman/NumberTheory/NumberField/TateGlobal.lean`.
-- pin: solution (S_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean:5588)
theorem exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ A : (InfiniteAdeleRing F → ℂ) → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) → ℂ → ℂ,
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (G : InfiniteAdeleRing F → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : ∀ x, f x = (integralOutside S).indicator
          (fun x => G x.1 * ∏ v ∈ S, h v ((x.2 : FiniteAdeleRing (𝓞 F) F) v)) x)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        zetaIntegral ν f χ s
            * ∏' v : {v // v ∉ S},
                (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
          = A G χ s * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s :=
  zetaIntegral_mul_eulerFactors_eq_joint F ν S μf ϖ hϖ

end IndicatorEulerFactors
end TateGlobal
end NumberField

end
