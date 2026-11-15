/-
  The prime weight `pw F s v = |v|^{-s}` and its summability: the counting input behind every
  Euler-product estimate of the column.

  `Def_NumberField_PrimeNormSums.lean` is a prerequisite of the adelic-height Weyl mass
  (`AutomorphicForm/Adelic/HeightWeylMass.lean`, whose `P2mMassZeta` block states its Euler
  product `eulerR` in terms of `pw`), so the port needs these declarations before that module
  can be transcribed.  This module ports the *prefix* of the pin file that the mass module
  uses — `pw` through `summable_pw` and `primeSum_toReal` — and nothing else: the tail
  (`summable_card_absNorm`'s zeta-function consumer, the `LSeries` normalization, the
  Dirichlet-series block) belongs to the Dedekind-zeta row and is not on this row's path.

  The pin's unused-section-variable silencer and the phantom `{m : ℕ} [NeZero m]` section
  variable are dropped (pin scaffolding; no declaration mentions `m`), and
  `Ideal.finite_setOf_absNorm_eq` is spelled with v4.34's name
  `Ideal.finite_setOfPred_absNorm_eq` in the proof of `summable_pw`.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`;
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_NumberField_PrimeNormSums.lean

  spec-pin: Definitions/Def_NumberField_PrimeNormSums.lean
-/
import FLTForHuman.NumberTheory.FrobeniusDensity.PrimeSums
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.SumCoeff

set_option autoImplicit false

noncomputable section

namespace NumberField.PrimeNormSum

open NumberField NumberField.InfinitePlace IsDedekindDomain Filter Topology
open scoped Classical

section PrimeSums

variable (F : Type) [Field F] [NumberField F]

def pw (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)

variable {F}

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem one_lt_absNorm_real (v : HeightOneSpectrum (𝓞 F)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have := two_le_absNorm v
  exact_mod_cast (by omega : 1 < Ideal.absNorm v.asIdeal)

theorem pw_pos (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : 0 < pw F s v :=
  Real.rpow_pos_of_pos (by linarith [one_lt_absNorm_real v]) _

theorem pw_nonneg (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ pw F s v := (pw_pos s v).le

theorem pw_le_one {s : ℝ} (hs : 0 ≤ s) (v : HeightOneSpectrum (𝓞 F)) : pw F s v ≤ 1 := by
  unfold pw
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_lt_absNorm_real v).le (by linarith)

theorem pw_antitone {s s' : ℝ} (h : s ≤ s') (v : HeightOneSpectrum (𝓞 F)) : pw F s' v ≤ pw F s v := by
  unfold pw
  exact Real.rpow_le_rpow_of_exponent_le (one_lt_absNorm_real v).le (by linarith)

theorem tendsto_sum_card_div :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = k} : ℝ)) / n) atTop
      (𝓝 ((2 ^ nrRealPlaces F * (2 * Real.pi) ^ nrComplexPlaces F * Units.regulator F *
        classNumber F) / (Units.torsionOrder F * Real.sqrt |discr F|))) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem summable_card_absNorm {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) s := by
  set d : ℕ → ℝ := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) with hd
  have h1 := (tendsto_sum_card_div (F := F)).isBigO_one ℝ
  have h2 : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, d k) =ᶠ[atTop]
      fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, d k) / n * n := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, d k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine h2.trans_isBigO ?_
    have h3 := h1.mul (Asymptotics.isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)
    refine h3.congr_right fun n ↦ ?_
    rw [Real.rpow_one, one_mul]
  have h4 := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun n ↦ Nat.cast_nonneg _)
    zero_le_one (by simpa using hs)
  refine (LSeriesSummable_congr s fun {n} _ ↦ ?_).1 h4
  simp [hd]

theorem summable_dedekind_terms {s : ℝ} (hs : 1 < s) :
    Summable fun n : ℕ => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
  have h4 := summable_card_absNorm (F := F) (s := (s : ℂ)) (by simpa using hs)
  refine (h4.norm.congr fun n => ?_)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]
  · rw [Complex.norm_natCast, Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg _),
      div_eq_mul_inv]

theorem summable_pw {s : ℝ} (hs : 1 < s) : Summable (pw F s) := by
  set e : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)
    with he
  have h5 : Summable e := summable_dedekind_terms hs

  refine summable_of_sum_le (fun v => pw_nonneg s v) (c := ∑' n, e n) fun T => ?_
  have hmaps : ∀ v ∈ T, Ideal.absNorm v.asIdeal ∈ T.image fun v => Ideal.absNorm v.asIdeal :=
    fun v hv => Finset.mem_image_of_mem _ hv
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hstep : ∀ n : ℕ, ∀ S : Finset (HeightOneSpectrum (𝓞 F)),
      (∀ v ∈ S, Ideal.absNorm v.asIdeal = n) → ∑ v ∈ S, pw F s v ≤ e n := by
    intro n S hS
    have hterm : ∀ v ∈ S, pw F s v = (n : ℝ) ^ (-s) := by
      intro v hv
      rw [pw, hS v hv]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, he]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hle := @Nat.card_le_card_of_injective S {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n).to_subtype
      (fun v : S => (⟨v.1.asIdeal, hS v.1 v.2⟩ : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}))
      (fun a b h => by
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (HeightOneSpectrum.ext h))
    rw [Nat.card_eq_finsetCard] at hle
    exact_mod_cast hle
  calc ∑ n ∈ T.image (fun v => Ideal.absNorm v.asIdeal),
        ∑ v ∈ T with Ideal.absNorm v.asIdeal = n, pw F s v
      ≤ ∑ n ∈ T.image (fun v => Ideal.absNorm v.asIdeal), e n :=
        Finset.sum_le_sum fun n _ => hstep n _ (fun v hv => (Finset.mem_filter.mp hv).2)
    _ ≤ ∑' n, e n := h5.sum_le_tsum _ (fun n _ => by
        rw [he]
        exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem primeSum_toReal (s : ℝ) : (FrobeniusDensity.primeSum F s).toReal = ∑' v, pw F s v := by
  rw [FrobeniusDensity.primeSum, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun v => ?_
    rw [FrobeniusDensity.normRpow, pw, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]
  · intro v
    rw [FrobeniusDensity.normRpow, Ne, ENNReal.rpow_eq_top_iff]
    push Not
    constructor
    · intro h
      exfalso
      have := two_le_absNorm v
      have h' : Ideal.absNorm v.asIdeal = 0 := by exact_mod_cast h
      omega
    · intro h
      exact absurd h (ENNReal.natCast_ne_top _)

end PrimeSums

end NumberField.PrimeNormSum

end
