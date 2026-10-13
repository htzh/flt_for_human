/-
  The G2 unfolding and the Euler-factor identity: the uniformizer family
  `unifOf`, the place factor `placeFactor` and shell coefficient `shellCoef`, the
  per-shell rewriting of the zeta integrand, the decomposition of the integral
  over `unitsOutside` into shells (`integral_eq_tsum_shellCoef_mul`), the reindexing
  `liftIdx` of nonnegative exponent vectors, the summability of the factorized
  monomials, the master unfolding `hole_G2`, the `_impl` form
  `zetaIntegral_mul_eulerFactors_eq_impl` and the headline
  `NumberField.TateGlobal.G2Proof.zetaIntegral_mul_eulerFactors_eq` (the pin's
  `solution`).

  Transcribed from the pin's `Fold_G2Proof` section (`M4aLocalCFT.G2Proof`
  namespace) and its trailing `solution`, declared lines 5133-5595 of file A,
  pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped, and so are the
  file-scoped `set_option maxHeartbeats 1600000` / `maxSynthPendingDepth 3`
  (A 5113/5115).  The pin's file-scoped `attribute [local instance]
  countable_heightOneSpectrum` (A 5133) is re-declared here (work order §8.5).
  The pin's `solution` is renamed `zetaIntegral_mul_eulerFactors_eq` and lives in
  the `NumberField.TateGlobal.G2Proof` sub-namespace, next to the `_impl` it
  concludes; the façade `FLTForHuman/NumberTheory/NumberField/TateGlobal.lean`
  re-states it at the pin wrapper's name
  `NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq`.  The pin's deprecated
  `if_pos`/`if_neg` are spelled `ite_eq_left`/`ite_eq_right` (proof-only change).
  No file-wide option beyond `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ShellTranslate

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal

section Fold_G2Proof

open AutomorphicForm IsDedekindDomain
open NumberField.TateGlobal LanglandsTunnell.TateLocal

open scoped NNReal Pointwise

noncomputable section

namespace NumberField
namespace TateGlobal
namespace G2Proof

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.TateGlobal.countable_heightOneSpectrum

-- pin: unifOf (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5135)
def unifOf (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) : Uniformizers F where
  ϖ := ϖ
  ordAt_eq_one v := by
    have h : WithZero.exp (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (ϖ v))))
        = WithZero.exp (-1 : ℤ) := by
      rw [← ValuedOrdBridge.valued_coe_units_eq_exp_neg_ord]
      exact hϖ v
    have h' := WithZero.exp_injective h
    show ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (ϖ v)) = 1
    omega

-- pin: unifOf_ϖ (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5147)
theorem unifOf_ϖ (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    (unifOf ϖ hϖ).ϖ = ϖ := rfl

-- pin: unifPow_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5151)
theorem unifPow_zero (ϖ : Uniformizers F) : unifPow ϖ (0 : HeightOneSpectrum (𝓞 F) →₀ ℤ) = 1 :=
  Finsupp.prod_zero_index

-- pin: ofReal_pow_cpow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5154)
theorem ofReal_pow_cpow {x : ℝ} (hx : 0 ≤ x) (m : ℕ) (s : ℂ) :
    (((x ^ m : ℝ)) : ℂ) ^ s = (((x : ℝ) : ℂ) ^ s) ^ m := by
  have h : (x ^ m : ℝ) = ∏ _i ∈ Finset.range m, x := by
    rw [Finset.prod_const, Finset.card_range]
  rw [h, cpow_prod_ofReal_nonneg _ _ (fun _ _ => hx), Finset.prod_const, Finset.card_range]

-- pin: ofReal_inv_natCast_pow_cpow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5160)
theorem ofReal_inv_natCast_pow_cpow (N : ℕ) (m : ℕ) (s : ℂ) :
    ((((N : ℝ)⁻¹ ^ m : ℝ)) : ℂ) ^ s = (((N : ℕ) : ℂ) ^ (-s)) ^ m := by
  rw [ofReal_pow_cpow (inv_nonneg.mpr (Nat.cast_nonneg N)) m s]
  congr 1
  have harg : ((N : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_pos.ne
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow _ _ harg, Complex.cpow_neg]

-- pin: ideleNorm_unifPow_cpow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5169)
theorem ideleNorm_unifPow_cpow (ϖ : Uniformizers F) (s : ℂ) {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : 0 ≤ k) :
    ((ideleNorm F (unifPow ϖ k) : ℝ) : ℂ) ^ s
      = k.prod fun v n => ((((Ideal.absNorm v.asIdeal : ℕ)) : ℂ) ^ (-s)) ^ n.toNat := by
  rw [ShellBound.ideleNorm_unifPow, Finsupp.prod, Finsupp.prod,
    cpow_prod_ofReal_nonneg _ _ (fun v _ => zpow_nonneg (Nat.cast_nonneg _) _) s]
  refine Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k v = m := Int.eq_ofNat_of_zero_le (Finsupp.le_def.mp hk v)
  rw [hm, Int.toNat_natCast, zpow_neg, ← inv_zpow, zpow_natCast]
  exact ofReal_inv_natCast_pow_cpow _ m s

-- pin: coe_char_unifPow (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5179)
theorem coe_char_unifPow (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : 0 ≤ k) :
    ((χ (unifPow ϖ k) : ℂˣ) : ℂ) = k.prod fun v n => ((localChar χ v (ϖ.ϖ v) : ℂˣ) : ℂ) ^ n.toNat := by
  rw [char_unifPow, Finsupp.prod, Finsupp.prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k v = m := Int.eq_ofNat_of_zero_le (Finsupp.le_def.mp hk v)
  rw [hm, Int.toNat_natCast, zpow_natCast, Units.val_pow_eq_pow_val]

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- pin: placeFactor (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5189)
def placeFactor (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  ((localChar χ v (ϖ.ϖ v) : ℂˣ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ)) : ℂ) ^ (-s)

-- pin: shellCoef (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5192)
def shellCoef (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    (k : HeightOneSpectrum (𝓞 F) →₀ ℤ) : ℂ := by
  classical exact if 0 ≤ k then k.prod (fun v n => placeFactor χ ϖ s v ^ n.toNat) else 0

-- pin: shellCoef_of_nonneg (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5196)
theorem shellCoef_of_nonneg (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : 0 ≤ k) :
    shellCoef χ ϖ s k = k.prod (fun v n => placeFactor χ ϖ s v ^ n.toNat) := by
  simp only [shellCoef, ite_eq_left hk]

-- pin: shellCoef_of_not_nonneg (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5201)
theorem shellCoef_of_not_nonneg (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hk : ¬ 0 ≤ k) : shellCoef χ ϖ s k = 0 := by
  simp only [shellCoef, ite_eq_right hk]

omit [NumberField F] in
-- pin: not_forall_nonneg_of_not_nonneg (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5206)
theorem not_forall_nonneg_of_not_nonneg {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hkS : ∀ v ∈ S, k v = 0)
    (hk : ¬ 0 ≤ k) : ¬ ∀ v ∉ S, 0 ≤ k v := fun h' =>
  hk (Finsupp.le_def.mpr fun v => by
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_cases hv : v ∈ S
    · exact (hkS v hv).symm.le
    · exact h' v hv)

section TestFunction

variable {S}

variable {f : AdeleRing (𝓞 F) F → ℂ} {g : (w : InfinitePlace F) → w.Completion → ℂ}
  {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}

-- pin: apply_unifPow_mul_eq (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5221)
theorem apply_unifPow_mul_eq (hf : IsFactorizableStandardOutside f S g h) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hkS : ∀ v ∈ S, k v = 0) (hk : 0 ≤ k)
    {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = f (u : AdeleRing (𝓞 F) F) := by
  have e1 := factorizable_apply_unifPow_mul hf ϖ hkS hu
  have e0 := factorizable_apply_unifPow_mul hf ϖ (k := 0) (fun _ _ => rfl) hu
  rw [ite_eq_left (show ∀ v ∉ S, 0 ≤ k v from fun v _ => Finsupp.le_def.mp hk v)] at e1
  rw [ite_eq_left (show ∀ v ∉ S, 0 ≤ (0 : HeightOneSpectrum (𝓞 F) →₀ ℤ) v from fun _ _ => le_rfl),
    unifPow_zero ϖ, one_mul] at e0
  exact e1.trans e0.symm

-- pin: apply_unifPow_mul_eq_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5232)
theorem apply_unifPow_mul_eq_zero (hf : IsFactorizableStandardOutside f S g h) (ϖ : Uniformizers F)
    {k : HeightOneSpectrum (𝓞 F) →₀ ℤ} (hkS : ∀ v ∈ S, k v = 0) (hk : ¬ 0 ≤ k)
    {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) :
    f ((unifPow ϖ k * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) = 0 := by
  rw [factorizable_apply_unifPow_mul hf ϖ hkS hu, ite_eq_right (not_forall_nonneg_of_not_nonneg S hkS hk)]

-- pin: zetaIntegrand_unifPow_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5238)
theorem zetaIntegrand_unifPow_mul (hf : IsFactorizableStandardOutside f S g h)
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

variable {S}

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

variable {f : AdeleRing (𝓞 F) F → ℂ} {g : (w : InfinitePlace F) → w.Completion → ℂ}
  {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] in
-- pin: preimage_mul_smul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5270)
theorem preimage_mul_smul (c : (AdeleRing (𝓞 F) F)ˣ) (U : Set (AdeleRing (𝓞 F) F)ˣ) :
    (fun u => c * u) ⁻¹' (c • U) = U := by
  ext u
  constructor
  · rintro ⟨u', hu', he⟩
    rwa [← mul_left_cancel (show c * u' = c * u from he)]
  · intro hu
    exact ⟨u, hu, rfl⟩

-- pin: setIntegral_unitsOutside_translate (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5279)
theorem setIntegral_unitsOutside_translate (hf : IsFactorizableStandardOutside f S g h)
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

-- pin: integrableOn_shell (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5297)
theorem integrableOn_shell (hf : IsFactorizableStandardOutside f S g h)
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

-- pin: setIntegral_shell_norm_le' (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5322)
theorem setIntegral_shell_norm_le' (hf : IsFactorizableStandardOutside f S g h)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ) (ϖ : Uniformizers F) (s : ℂ)
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant] (k : ExpIndex (F := F) S) (hk : 0 ≤ k.1) :
    ∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν
      ≤ (k.1.prod fun v n => ((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) ^ n.toNat)
          * ∫ u in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ), ‖f (u : AdeleRing (𝓞 F) F)‖
              * ideleNorm F u ^ s.re ∂ν :=
  ShellTranslate.setIntegral_shell_norm_le ν ϖ hχu k hk (le_of_eq
    (setIntegral_congr_fun (isOpen_unitsOutside S).measurableSet fun u hu => by
      rw [apply_unifPow_mul_eq hf ϖ k.2 hk hu]))

-- pin: setIntegral_shell_norm_eq_zero (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5333)
theorem setIntegral_shell_norm_eq_zero (hf : IsFactorizableStandardOutside f S g h)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) (k : ExpIndex (F := F) S) (hk : ¬ 0 ≤ k.1) :
    ∫ x in shell S k.1, ‖f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s‖ ∂ν = 0 := by
  refine (setIntegral_congr_fun (measurableSet_shell ϖ k.2) fun x hx => ?_).trans (integral_zero _ _)
  rw [shell_eq_smul ϖ k.2] at hx
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
  rw [smul_eq_mul, apply_unifPow_mul_eq_zero hf ϖ k.2 hk hu, zero_mul, zero_mul, norm_zero]

-- pin: integrable_of_integrableOn_unitsOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5342)
theorem integrable_of_integrableOn_unitsOutside (hf : IsFactorizableStandardOutside f S g h)
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

-- pin: integral_eq_tsum_shellCoef_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5362)
theorem integral_eq_tsum_shellCoef_mul (hf : IsFactorizableStandardOutside f S g h)
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

section Reindex

-- pin: liftVec (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5388)
def liftVec (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ) : HeightOneSpectrum (𝓞 F) →₀ ℤ :=
  Finsupp.embDomain (Function.Embedding.subtype _) (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero m)

omit [NumberField F] in
-- pin: liftVec_apply_of_not_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5392)
theorem liftVec_apply_of_not_mem (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : liftVec S m v = ((m ⟨v, hv⟩ : ℕ) : ℤ) := by
  have e := Finsupp.embDomain_apply_self (Function.Embedding.subtype fun v => v ∉ S)
    (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero m) ⟨v, hv⟩
  rw [Finsupp.mapRange_apply] at e
  exact e

omit [NumberField F] in
-- pin: liftVec_apply_of_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5400)
theorem liftVec_apply_of_mem (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : liftVec S m v = 0 := by
  refine Finsupp.embDomain_of_notMem_range _ _ _ fun ⟨i, hi⟩ => ?_
  have h : (i : HeightOneSpectrum (𝓞 F)) = v := hi
  exact i.2 (h ▸ hv)

omit [NumberField F] in
-- pin: liftVec_nonneg (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5407)
theorem liftVec_nonneg (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ) : 0 ≤ liftVec S m :=
  Finsupp.le_def.mpr fun v => by
    rw [Finsupp.coe_zero, Pi.zero_apply]
    by_cases hv : v ∈ S
    · rw [liftVec_apply_of_mem S m hv]
    · rw [liftVec_apply_of_not_mem S m hv]
      exact Int.natCast_nonneg _

-- pin: liftIdx (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5415)
def liftIdx (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ) : ExpIndex (F := F) S :=
  ⟨liftVec S m, fun _ hv => liftVec_apply_of_mem S m hv⟩

omit [NumberField F] in
-- pin: liftIdx_injective (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5419)
theorem liftIdx_injective : Function.Injective (liftIdx (F := F) S) := fun _ _ he =>
  Finsupp.mapRange_injective (fun n : ℕ => (n : ℤ)) Nat.cast_zero Nat.cast_injective
    (Finsupp.embDomain_injective _ (congrArg Subtype.val he))

omit [NumberField F] in
-- pin: mem_range_liftIdx (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5424)
theorem mem_range_liftIdx {k : ExpIndex (F := F) S} (hk : 0 ≤ k.1) : k ∈ Set.range (liftIdx (F := F) S) := by
  refine ⟨Finsupp.subtypeDomain (fun v => v ∉ S) (Finsupp.mapRange Int.toNat Int.toNat_zero k.1),
    Subtype.ext (Finsupp.ext fun v => ?_)⟩
  show liftVec S _ v = k.1 v
  by_cases hv : v ∈ S
  · rw [liftVec_apply_of_mem S _ hv, k.2 v hv]
  · rw [liftVec_apply_of_not_mem S _ hv, Finsupp.subtypeDomain_apply, Finsupp.mapRange_apply]
    exact Int.toNat_of_nonneg (Finsupp.le_def.mp hk v)

-- pin: shellCoef_liftIdx (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5433)
theorem shellCoef_liftIdx (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ)
    (m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ) :
    shellCoef χ ϖ s (liftIdx S m).1
      = EulerBookkeeping.mono (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => placeFactor χ ϖ s v.1) m := by
  show shellCoef χ ϖ s (liftVec S m) = _
  rw [shellCoef_of_nonneg χ ϖ s (liftVec_nonneg S m)]
  show (liftVec S m).prod (fun v n => placeFactor χ ϖ s v ^ n.toNat) = m.prod fun v n => placeFactor χ ϖ s v.1 ^ n
  rw [liftVec, Finsupp.prod_embDomain, Finsupp.prod_mapRange_index (fun _ => by rw [Int.toNat_zero, pow_zero])]
  refine Finsupp.prod_congr fun v _ => ?_
  rw [Int.toNat_natCast]
  rfl

-- pin: tsum_shellCoef_eq_tsum_mono (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5445)
theorem tsum_shellCoef_eq_tsum_mono (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ϖ : Uniformizers F) (s : ℂ) :
    ∑' k : ExpIndex (F := F) S, shellCoef χ ϖ s k.1
      = ∑' m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ,
          EulerBookkeeping.mono (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => placeFactor χ ϖ s v.1) m := by
  have hsupp : Function.support (fun k : ExpIndex (F := F) S => shellCoef χ ϖ s k.1)
      ⊆ Set.range (liftIdx (F := F) S) := by
    intro k hk
    by_cases hk0 : 0 ≤ k.1
    · exact mem_range_liftIdx S hk0
    · exact absurd (shellCoef_of_not_nonneg χ ϖ s hk0) hk
  rw [← (liftIdx_injective S).tsum_eq hsupp]
  exact tsum_congr fun m => shellCoef_liftIdx S χ ϖ s m

-- pin: norm_placeFactor (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5458)
theorem norm_placeFactor {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ)
    (ϖ : Uniformizers F) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖placeFactor χ ϖ s v‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  rw [placeFactor, norm_mul, localChar_apply, hχu, one_mul,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (absNorm_ne_zero v)), Complex.neg_re]

-- pin: summable_norm_mono_placeFactor (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5464)
theorem summable_norm_mono_placeFactor {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 F) F χ)
    (ϖ : Uniformizers F) {s : ℂ} (hs : 1 < s.re) :
    Summable fun m : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} →₀ ℕ =>
      ‖EulerBookkeeping.mono (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => placeFactor χ ϖ s v.1) m‖ := by
  have hnorm : ∀ v : HeightOneSpectrum (𝓞 F), ‖placeFactor χ ϖ s v‖ = ‖ShellBound.baseFam F s.re v‖ := fun v => by
    rw [norm_placeFactor hχu, ShellBound.norm_baseFam]
  refine EulerBookkeeping.summable_norm_mono ?_ fun v => ?_
  · have h := (ShellBound.summable_norm_baseFam (F := F) hs).comp_injective
      (Subtype.val_injective (p := fun v : HeightOneSpectrum (𝓞 F) => v ∉ S))
    exact h.congr fun v => (hnorm v.1).symm
  · rw [hnorm]
    exact ShellBound.norm_baseFam_lt_one hs v.1

end Reindex

set_option linter.style.haveILetI false in
-- The eight `letI`/`haveI` below supply the load-bearing `MeasurableSpace`/`BorelSpace`
-- instances on `w.Completion`, `v.adicCompletion F`, `v.adicCompletionIntegers F` and
-- `InfiniteAdeleRing F` (and their unit groups) that `refConst`/`zetaIntegral` need;
-- `let`/`have` would drop them from instance search, so the style linter is disabled
-- for this declaration only.
-- pin: hole_G2 (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5480)
theorem hole_G2 (F : Type) [Field F] [NumberField F] [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ]
    [BorelSpace (AdeleRing (𝓞 F) F)ˣ] (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))
    [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
    (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (g : (w : InfinitePlace F) → w.Completion → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : IsFactorizableStandardOutside f S g h)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        (Summable fun k : {v // v ∉ S} →₀ ℕ =>
            ‖EulerBookkeeping.mono (fun v : {v // v ∉ S} => ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) k‖) ∧
        zetaIntegral ν f χ s
          = (c * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w) (g w) (archLocalChar χ w) s)
              * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s)
            * ∑' k : {v // v ∉ S} →₀ ℕ,
                EulerBookkeeping.mono (fun v : {v // v ∉ S} => ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) k := by
  letI : ∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ := fun _ => borel _
  haveI : ∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ := fun _ => ⟨rfl⟩
  letI : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ := fun _ => borel _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ := fun _ => ⟨rfl⟩
  letI : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ := fun _ => borel _
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ := fun _ => ⟨rfl⟩
  letI : MeasurableSpace (InfiniteAdeleRing F)ˣ := borel _
  haveI : BorelSpace (InfiniteAdeleRing F)ˣ := ⟨rfl⟩
  refine ⟨(refConst S μa μf ν : ℝ), refConst_pos S μa μf ν, ?_⟩
  intro f g h hf χ hχc hχu hχS s hs
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

-- pin: zetaIntegral_mul_eulerFactors_eq_impl (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5527)
theorem zetaIntegral_mul_eulerFactors_eq_impl (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
    (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (g : (w : InfinitePlace F) → w.Completion → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : IsFactorizableStandardOutside f S g h)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        zetaIntegral ν f χ s
            * ∏' v : {v // v ∉ S},
                (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
          = c * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w) (g w) (archLocalChar χ w) s)
              * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s := by
  obtain ⟨c, hc, H⟩ := hole_G2 F ν S μf μa ϖ hϖ
  refine ⟨c, hc, fun f g h _hf χ _hχc _hχu _hχS s _hs => ?_⟩
  obtain ⟨hS, hZ⟩ := H f g h _hf χ _hχc _hχu _hχS s _hs
  rw [hZ, mul_assoc, EulerBookkeeping.tsum_mono_mul_tprod_one_sub hS, mul_one]

-- The pin's `solution` is the dev headline; it is named at the wrapper's name
-- `zetaIntegral_mul_eulerFactors_eq` here and re-stated at the pin wrapper's name
-- `NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq` by the façade
-- `FLTForHuman/NumberTheory/NumberField/TateGlobal.lean`.  The dev name lives in
-- the pin's `G2Proof` sub-namespace so that it does not collide with the façade.
-- pin: solution (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:5573)
theorem zetaIntegral_mul_eulerFactors_eq (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
    (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (g : (w : InfinitePlace F) → w.Completion → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : IsFactorizableStandardOutside f S g h)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        zetaIntegral ν f χ s
            * ∏' v : {v // v ∉ S},
                (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
          = c * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w) (g w) (archLocalChar χ w) s)
              * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s :=
  zetaIntegral_mul_eulerFactors_eq_impl F ν S μf μa ϖ hϖ

end G2Proof
end TateGlobal
end NumberField

end

end Fold_G2Proof
