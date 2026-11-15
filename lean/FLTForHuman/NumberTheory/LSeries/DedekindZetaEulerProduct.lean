/-
  The full Euler product of the Dedekind zeta function: `ζ_K(s) = ∏'_𝔭 (1 - |𝔭|^{-s})^{-1}` is
  multiplicable, its product is differentiable, and it is non-zero on `re s > 1`.

  spec-pin: P2M/Sol/S_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one.lean
-/
import FLTForHuman.NumberTheory.LSeries.DedekindZetaEuler
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate NNReal ENNReal
open Filter Finset Topology MeasureTheory IsDedekindDomain Complex

namespace NumberField.ZetaEuler

universe u

variable (K : Type u) [Field K] [NumberField K]

theorem hasProd_spectrum {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (dedekindZeta K s) :=
  (primesEquiv K).hasProd_iff.mpr (hasProd_primes K hs)

theorem summable_spectrum {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) :=
  (summable_absNorm_cpow K hs).comp_injective fun _ _ h => HeightOneSpectrum.ext h

theorem two_le_absNorm_spectrum (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal :=
  two_le_absNorm K (primesEquiv K v)

theorem norm_cpow_le_half {s : ℂ} (hs : 1 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have h2 := two_le_absNorm_spectrum K v
  rw [Complex.norm_natCast_cpow_of_pos (by omega) (-s), Complex.neg_re]
  have h2' : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast h2
  calc ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re)
      ≤ (2 : ℝ) ^ (-s.re) := Real.rpow_le_rpow_of_nonpos (by norm_num) h2' (by linarith)
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

theorem norm_inv_factor_le_two {s : ℂ} (hs : 1 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖(1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹‖ ≤ 2 := by
  have hx := norm_cpow_le_half K hs v
  have hlow : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))
    rw [norm_one] at this
    linarith
  rw [norm_inv]
  calc ‖(1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
        inv_anti₀ (by norm_num) hlow
    _ = 2 := by norm_num

theorem multipliable_inv_factor_subtype {s : ℂ} (hs : 1 < s.re) (p : HeightOneSpectrum (𝓞 K) → Prop) :
    Multipliable fun v : {v // p v} => (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  have hxs : Summable fun v : {v // p v} => ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) :=
    (summable_spectrum K hs).subtype _
  have hne : ∀ v : {v // p v}, (1 : ℂ) - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 := by
    intro v h
    have hx := norm_cpow_le_half K hs.le v.1
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hx
    norm_num at hx
  have hg : Summable fun v : {v // p v} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) / (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) := by
    refine Summable.of_norm_bounded (g := fun v => 2 * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖)
      (hxs.norm.mul_left 2) fun v => ?_
    have hx := norm_cpow_le_half K hs.le v.1
    have hlow : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
      rw [norm_one] at this
      linarith
    rw [norm_div]
    calc ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ / ‖(1 : ℂ) - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖
        ≤ ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ / (1 / 2) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hlow
      _ = 2 * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by ring
  refine (Complex.multipliable_one_add_of_summable hg).congr fun v => ?_
  field_simp [hne v]
  ring

theorem dedekindZeta_eq_prod_mul_tprod {s : ℂ} (hs : 1 < s.re) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    dedekindZeta K s = (∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) *
      ∏' v : {v // v ∉ T}, (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ := by
  have hall := hasProd_spectrum K hs
  have hT := Finset.hasProd T (fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
  have hC : HasProd ((fun v : HeightOneSpectrum (𝓞 K) => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ∘
      ((↑) : ((↑T : Set (HeightOneSpectrum (𝓞 K)))ᶜ : Set (HeightOneSpectrum (𝓞 K))) → HeightOneSpectrum (𝓞 K)))
      (∏' v : {v // v ∉ T}, (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) :=
    (multipliable_inv_factor_subtype K hs (fun v => v ∉ T)).hasProd
  exact hall.unique (hT.mul_compl hC)

theorem tendsto_norm_dedekindZeta_atTop :
    Tendsto (fun σ : ℝ => ‖dedekindZeta K (σ : ℂ)‖) (𝓝[>] 1) atTop := by
  have hres := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hr : 0 < dedekindZeta_residue K := dedekindZeta_residue_pos K

  have hev : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      dedekindZeta_residue K / 2 < ‖((σ : ℂ) - 1) * dedekindZeta K (σ : ℂ)‖ := by
    have h := hres.norm
    have hlt : dedekindZeta_residue K / 2 < ‖((dedekindZeta_residue K : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hr.le]; linarith
    exact h.eventually (lt_mem_nhds hlt)

  have hshift : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun σ : ℝ => σ - 1) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) := tendsto_id.sub_const 1
      rw [sub_self] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Ioi.mp hσ))
  have hdiv : Tendsto (fun σ : ℝ => dedekindZeta_residue K / 2 * (σ - 1)⁻¹) (𝓝[>] (1 : ℝ)) atTop :=
    (tendsto_inv_nhdsGT_zero.comp hshift).const_mul_atTop (half_pos hr)
  refine tendsto_atTop_mono' _ ?_ hdiv
  filter_upwards [hev, self_mem_nhdsWithin] with σ hσ hσ1
  have hpos : 0 < σ - 1 := sub_pos.mpr hσ1
  rw [norm_mul, show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg hpos.le] at hσ
  rw [← div_eq_mul_inv, div_le_iff₀ hpos, mul_comm]
  exact hσ.le

theorem tendsto_norm_tprod_atTop (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (fun σ : ℝ => ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖) (𝓝[>] 1) atTop := by
  have hζ := tendsto_norm_dedekindZeta_atTop K
  have hpow : (0 : ℝ) < 2 ^ T.card := by positivity
  refine tendsto_atTop_mono' _ ?_ (hζ.atTop_div_const hpow)
  filter_upwards [self_mem_nhdsWithin] with σ hσ1
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ1
  rw [dedekindZeta_eq_prod_mul_tprod K hs T, norm_mul, div_le_iff₀ hpow, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖
      ≤ ∏ v ∈ T, ‖(1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _v ∈ T, (2 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun v _ => norm_inv_factor_le_two K hs.le v)
    _ = 2 ^ T.card := Finset.prod_const 2

theorem absNorm_cast_ne_zero (v : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

theorem absNorm_pos' (v : HeightOneSpectrum (𝓞 K)) : 0 < Ideal.absNorm v.asIdeal :=
  Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {z : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ}

theorem norm_term_le (hz : ∀ v, ‖z v‖ ≤ 1) (s : ℂ) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    ‖z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hz v)

theorem norm_term_le_half (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    ‖z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
  (norm_term_le K hz s v).trans (norm_cpow_le_half K hs v.1)

theorem half_le_re_one_sub_term (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    (1 : ℝ) / 2 ≤ ((1 : ℂ) - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)).re := by
  have h := norm_term_le_half K hz hs v
  have hre := abs_re_le_norm (z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
  rw [Complex.sub_re, Complex.one_re]
  have := le_abs_self ((z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)).re)
  linarith

theorem one_sub_term_ne_zero (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    (1 : ℂ) - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have := half_le_re_one_sub_term K hz hs v
  rw [h, Complex.zero_re] at this
  norm_num at this

theorem arg_one_sub_term_ne_pi (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    ((1 : ℂ) - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)).arg ≠ Real.pi := by
  rw [Ne, Complex.arg_eq_pi_iff, not_and_or]
  left
  have := half_le_re_one_sub_term K hz hs v
  linarith

theorem norm_log_inv_one_sub_le (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) :
    ‖log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)‖
      ≤ (3 / 2) * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
  rw [Complex.log_inv _ (arg_one_sub_term_ne_pi K hz hs v), norm_neg, sub_eq_add_neg]
  refine (Complex.norm_log_one_add_half_le_self ?_).trans ?_
  · rw [norm_neg]; exact norm_term_le_half K hz hs v
  · rw [norm_neg]; exact mul_le_mul_of_nonneg_left (norm_term_le K hz s v) (by norm_num)

theorem summable_log_inv_one_sub (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) := by
  have hxs : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) := (summable_spectrum K hs).subtype _
  exact Summable.of_norm_bounded (g := fun v => (3 / 2) * ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖)
    (hxs.norm.mul_left _) fun v => norm_log_inv_one_sub_le K hz hs.le v

theorem multipliable_factor (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ :=
  Complex.multipliable_of_summable_log (summable_log_inv_one_sub K hz hs)

theorem tprod_eq_cexp (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹
      = cexp (∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) :=
  (Complex.cexp_tsum_eq_tprod (fun v => inv_ne_zero (one_sub_term_ne_zero K hz hs.le v))
    (summable_log_inv_one_sub K hz hs)).symm

theorem differentiableAt_log_term (hz : ∀ v, ‖z v‖ ≤ 1) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    {s : ℂ} (hs : 1 ≤ s.re) :
    DifferentiableAt ℂ (fun s : ℂ => log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) s := by
  have hN : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ≠ 0 := absNorm_cast_ne_zero K v.1
  have h1 : DifferentiableAt ℂ (fun s : ℂ => ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hN)
  have h2 : DifferentiableAt ℂ
      (fun s : ℂ => (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) s :=
    ((differentiableAt_const _).sub (h1.const_mul _)).inv (one_sub_term_ne_zero K hz hs v)
  refine h2.clog (Complex.mem_slitPlane_iff.mpr (Or.inl ?_))
  rw [Complex.inv_re]
  exact div_pos (lt_of_lt_of_le (by norm_num) (half_le_re_one_sub_term K hz hs v))
    (Complex.normSq_pos.mpr (one_sub_term_ne_zero K hz hs v))

theorem differentiableOn_tsum_log_delta (hz : ∀ v, ‖z v‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ (fun s : ℂ => ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) {s : ℂ | 1 + δ < s.re} := by
  have hσ : 1 < 1 + δ := by linarith
  have hu : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      (3 / 2 : ℝ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(1 + δ)) := by
    have h := (summable_absNorm_rpow K hσ).comp_injective
      (fun (a b : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (h : a.1.asIdeal = b.1.asIdeal) =>
        Subtype.ext (HeightOneSpectrum.ext h))
    exact h.mul_left _
  refine differentiableOn_tsum_of_summable_norm hu
    (fun v s hs => (differentiableAt_log_term K hz v ?_).differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re) ?_
  · have hs' : 1 + δ < s.re := hs
    linarith
  · intro v s hs
    have hs' : 1 + δ < s.re := hs
    refine (norm_log_inv_one_sub_le K hz (by linarith) v).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Complex.norm_natCast_cpow_of_pos (absNorm_pos' K v.1), Complex.neg_re]
    have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.1.asIdeal : ℕ) := by exact_mod_cast two_le_absNorm_spectrum K v.1
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem differentiableOn_tsum_log (hz : ∀ v, ‖z v‖ ≤ 1) :
    DifferentiableOn ℂ (fun s : ℂ => ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      log ((1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs' : 1 < s.re := hs
  have hδ0 : 0 < (s.re - 1) / 2 := by linarith
  have hmem : s ∈ {w : ℂ | 1 + (s.re - 1) / 2 < w.re} := by
    show 1 + (s.re - 1) / 2 < s.re
    linarith
  exact ((differentiableOn_tsum_log_delta K hz hδ0).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

theorem differentiableOn_tprod (hz : ∀ v, ‖z v‖ ≤ 1) :
    DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) {s : ℂ | 1 < s.re} :=
  (differentiableOn_tsum_log K hz).cexp.congr fun _ hs => tprod_eq_cexp K hz hs

theorem multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
    (M : Type) [Field M] [NumberField M] (S : Finset (HeightOneSpectrum (𝓞 M)))
    (z : {v : HeightOneSpectrum (𝓞 M) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) :
    (∀ s : ℂ, 1 < s.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S} =>
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) ∧
      DifferentiableOn ℂ
        (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S},
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
        {s : ℂ | 1 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S},
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ≠ 0 :=
  ⟨fun _ hs => multipliable_factor M hz hs,
   differentiableOn_tprod M hz,
   fun _ hs => by rw [tprod_eq_cexp M hz hs]; exact Complex.exp_ne_zero _⟩

end NumberField.ZetaEuler

end
