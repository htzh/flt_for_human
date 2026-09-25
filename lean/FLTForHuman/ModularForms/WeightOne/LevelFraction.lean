/-
  The level-fraction packages (SET-9 order 1).

  Statements verbatim from the pinned wrappers
  `Theorems/Thm_WLight_{qExpansion_sigmaTransport_package,
  exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction,
  exists_levelFraction_of_stable_family,
  exists_monicRel_j_of_mdifferentiable_levelFraction}.lean`; proofs transcribed
  from the matching `P2M/Sol/S_WLight_*` files (786 + 1,069 + 1,331 + 667 lines)
  and adapted to mathlib `v4.34.0`.

  As in SET-8 each pin file's helpers are kept `private` inside the pin's own
  namespace (renamed `WLightS9.*`), so the four packages' repeated vocabulary
  (`j`, `periodPairOfTau`, `frickeF`, `KPoleAt`, `HolFn`, ...) does not collide;
  the four headlines are the module's only public surface.  Cross-package reuse is
  through the already-ported public headlines only (`WLight.levelOne_hauptmodul_package`,
  `WLight.frickeFunction_modularity_package`, `WLight.frickeFunction_orbit_package`).

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_qExpansion_sigmaTransport_package.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_exists_levelFraction_of_stable_family.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction.lean

  The pin's local `set_option maxHeartbeats`/`synthInstance.maxHeartbeats` bumps
  are **not** transcribed (the project's global `maxHeartbeats` cap is 4,000,000).
-/

import FLTForHuman.ModularForms.WeightOne.Basic
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import FLTForHuman.ModularForms.WeightOne.FrickeFunction
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Geometry.Manifold.Notation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.Unramified.Field
set_option autoImplicit false
-- The pin's `haveI` walls are load-bearing; keep them literal (cf. `Basic.lean`).
set_option linter.style.haveILetI false

namespace WLightS9.S_WLight_qExpansion_sigmaTransport_package

set_option autoImplicit false

noncomputable section

open _root_.Complex _root_.Real _root_.UpperHalfPlane _root_.Function _root_.Filter _root_.Polynomial _root_.Real.Polynomial
open scoped _root_.Complex _root_.Real _root_.UpperHalfPlane _root_.Function _root_.Filter _root_.Polynomial _root_.Real.Polynomial
open scoped Topology Manifold MatrixGroups ModularForm

namespace WLight

section CuspCriterion

variable {N : ℕ}

private lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

private lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ Filter.const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

private lemma IsBoundedAtImInfty.mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
    (h : IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)) :
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m') := by
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hshape]
  exact h.mul (isBoundedAtImInfty_discPow (m' - m))

private def discPowForm (m : ℕ) : ModularForm 𝒮ℒ (12 * m) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow m)

private lemma discPowForm_coe (m : ℕ) : ⇑(discPowForm m) = ⇑CuspForm.discriminant ^ m := by
  funext z
  simp [discPowForm, ModularForm.coe_mcast, ModularForm.coe_pow,
    CuspForm.toModularFormₗ_apply]

private lemma periodic_one_fn (c : ℝ) : Function.Periodic ((1 : ℍ → ℂ) ∘ ofComplex) c := fun _ => rfl

private lemma periodic_discPow_comp_ofComplex (k : ℕ) (N : ℕ) :
    Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) N := by
  have h1 : Function.Periodic (⇑CuspForm.discriminant ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL
  have hk : Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) 1 := by
    induction k with
    | zero => exact periodic_one_fn 1
    | succ k ih =>
      intro x
      have hx := (ih.mul h1) x
      simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply] at hx ⊢
      rw [pow_succ, pow_succ]
      exact hx
  simpa using hk.nat_mul N

private lemma mdiff_discPow (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑CuspForm.discriminant ^ k : ℍ → ℂ) := by
  rw [← discPowForm_coe]
  exact (discPowForm k).holo'

private lemma mdiff_mul_discPow {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (m : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) :=
  hf.mul (mdiff_discPow m)

private lemma analyticAt_cuspFunction_zero_of [NeZero N] {g : ℍ → ℂ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Function.Periodic (g ∘ ofComplex) N) (hbd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction N g) 0 :=
  analyticAt_cuspFunction_zero
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd

private lemma qExpansion_one_discPowForm (k : ℕ) :
    qExpansion 1 (discPowForm k) = (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [discPowForm, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hco : (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) =
      ModularForm.discriminant := by
    funext z
    rw [CuspForm.toModularFormₗ_apply]
    exact congrFun CuspForm.coe_discriminant z
  rw [hco]

private lemma qExpansion_one_discPow (k : ℕ) :
    qExpansion 1 (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [← discPowForm_coe]
  exact qExpansion_one_discPowForm k

private lemma qParam_one_eq_pow {N : ℕ} (hN : N ≠ 0) (τ : ℂ) :
    Function.Periodic.qParam 1 τ = Function.Periodic.qParam N τ ^ N := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

private theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperN : Function.Periodic (f ∘ ofComplex) N := by
    simpa using hper.nat_mul N
  let f' : C(ℍ, ℂ) := ⟨f, hhol.continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN' hperN hhol hbd
  set c : ℕ → ℂ := fun n ↦ if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 with hc
  have hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam N τ ^ m) (f' τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hhol hbd τ
    have hinj : Function.Injective fun m : ℕ ↦ N * m := fun a b h ↦ by
      simpa [Nat.mul_right_inj hN] using h
    refine (hinj.hasSum_iff (f := fun m ↦ c m • Function.Periodic.qParam N τ ^ m) ?_).mp ?_
    · intro x hx
      have : ¬ N ∣ x := fun ⟨k, hk⟩ ↦ hx ⟨k, hk.symm⟩
      simp [hc, this]
    · refine h1.congr_fun fun m ↦ ?_
      simp only [Function.comp_apply, hc, Nat.dvd_mul_right, ite_true,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN), qParam_one_eq_pow hN, ← pow_mul]
  exact (qExpansion_coeff_unique f' hN' hfan hf n).symm

end CuspCriterion

section RatCoeff

open _root_.UpperHalfPlane _root_.ModularForm _root_.SlashInvariantForm _root_.ModularFormClass _root_.CuspForm _root_.ModularForm.CuspForm _root_.EisensteinSeries
open scoped _root_.UpperHalfPlane _root_.ModularForm _root_.SlashInvariantForm _root_.ModularFormClass _root_.CuspForm _root_.ModularForm.CuspForm _root_.EisensteinSeries
open scoped MatrixGroups ArithmeticFunction.sigma

private lemma ratCoeff_mul {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p * q).coeff n = (a : ℂ) := by
  choose F hF using hp
  choose G hG using hq
  intro n
  refine ⟨∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, F ij.1 * G ij.2, ?_⟩
  rw [PowerSeries.coeff_mul]
  push_cast
  exact Finset.sum_congr rfl fun ij _ => by rw [hF, hG]

private lemma ratCoeff_sub {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p - q).coeff n = (a : ℂ) := by
  intro n
  obtain ⟨a, ha⟩ := hp n
  obtain ⟨b, hb⟩ := hq n
  exact ⟨a - b, by rw [map_sub, ha, hb]; push_cast; ring⟩

private lemma ratCoeff_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 (E hk)).coeff n = (q : ℂ) := by
  intro n
  rw [E_qExpansion_coeff hk hk2]
  by_cases hn : n = 0
  · exact ⟨1, by simp [hn]⟩
  · refine ⟨-(2 * k / _root_.bernoulli k) * (σ (k - 1) n : ℚ), ?_⟩
    rw [ite_eq_right hn]
    push_cast
    ring

private lemma ratCoeff_pow {p : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (k : ℕ) :
    ∀ n : ℕ, ∃ a : ℚ, (p ^ k).coeff n = (a : ℂ) := by
  induction k with
  | zero =>
    intro n
    rw [pow_zero]
    by_cases hn : n = 0
    · exact ⟨1, by simp [hn, PowerSeries.coeff_one]⟩
    · exact ⟨0, by simp [PowerSeries.coeff_one, hn]⟩
  | succ k ih =>
    rw [pow_succ]
    exact ratCoeff_mul ih hp

private def eCubeSubESq : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

private lemma eCubeSubESq_qExpansion :
    qExpansion 1 eCubeSubESq = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ -
      qExpansion 1 E₆ * qExpansion 1 E₆ := by
  simp only [eCubeSubESq, FunLike.coe_sub, ModularForm.coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

private lemma discriminant_eq_smul_eCubeSubESq :
    ModularForm.discriminant = (1 / 1728 : ℂ) • eCubeSubESq := by
  ext z
  have h := discriminant_eq_E₄_cube_sub_E₆_sq z
  simp only [Pi.smul_apply, eCubeSubESq, FunLike.coe_sub, Pi.sub_apply,
    ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul]
  rw [h]
  ring

private lemma ratCoeff_discriminant :
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 ModularForm.discriminant).coeff n = (q : ℂ) := by
  have h4 : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 E₄).coeff n = (q : ℂ) :=
    ratCoeff_E (by norm_num) (by decide)
  have h6 : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 E₆).coeff n = (q : ℂ) :=
    ratCoeff_E (by norm_num) (by decide)
  have hmain := ratCoeff_sub (ratCoeff_mul (ratCoeff_mul h4 h4) h4) (ratCoeff_mul h6 h6)
  intro n
  obtain ⟨a, ha⟩ := hmain n
  refine ⟨(1 / 1728 : ℚ) * a, ?_⟩
  rw [discriminant_eq_smul_eCubeSubESq,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, eCubeSubESq_qExpansion, smul_eq_mul, ha]
  push_cast
  ring

end RatCoeff

section KPoleAlgebra

open ModularForm

variable {N : ℕ}

private lemma mem_of_rat (K : IntermediateField ℚ ℂ) {x : ℂ} (h : ∃ q : ℚ, x = (q : ℂ)) : x ∈ K := by
  obtain ⟨q, rfl⟩ := h
  exact SubfieldClass.ratCast_mem K q

private def KPoleAt (K : IntermediateField ℚ ℂ) (N m : ℕ) (f : ℍ → ℂ) : Prop :=
  Function.Periodic ((f * ⇑CuspForm.discriminant ^ m) ∘ ofComplex) N ∧
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m) ∧
    ∀ n : ℕ, (qExpansion N (f * ⇑CuspForm.discriminant ^ m)).coeff n ∈ K

private def KPole (K : IntermediateField ℚ ℂ) (N : ℕ) (f : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ ∃ m : ℕ, KPoleAt K N m f

private lemma qExpansion_discPow_coeff_mem (K : IntermediateField ℚ ℂ) [NeZero N] (k n : ℕ) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff n ∈ K := by
  have hper : Function.Periodic
      ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
    have h := periodic_discPow_comp_ofComplex k 1
    simpa only [Nat.cast_one] using h
  rw [qExpansion_coeff_width _ (NeZero.ne N) hper (mdiff_discPow k)
    (isBoundedAtImInfty_discPow k), qExpansion_one_discPow]
  split
  · exact mem_of_rat K (ratCoeff_pow ratCoeff_discriminant k _)
  · exact zero_mem _

private lemma KPoleAt.pad {K : IntermediateField ℚ ℂ} [NeZero N] {f : ℍ → ℂ} {m m' : ℕ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hm : m ≤ m') (h : KPoleAt K N m f) :
    KPoleAt K N m' f := by
  obtain ⟨hper, hbd, hmem⟩ := h
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  refine ⟨?_, ?_, ?_⟩
  · rw [hshape]
    exact hper.mul (periodic_discPow_comp_ofComplex (m' - m) N)
  · exact IsBoundedAtImInfty.mul_discPow_mono hm hbd
  · intro n
    rw [hshape, qExpansion_mul
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hhol m) hper hbd)
      (analyticAt_cuspFunction_zero_of (mdiff_discPow (m' - m))
        (periodic_discPow_comp_ofComplex (m' - m) N) (isBoundedAtImInfty_discPow (m' - m))),
      PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hmem ij.1) (qExpansion_discPow_coeff_mem K _ ij.2)

private lemma kPole_algebraMap {K : IntermediateField ℚ ℂ} [NeZero N] (c : ↥K) :
    KPole K N (algebraMap ↥K (ℍ → ℂ) c) := by
  have hshape : ((algebraMap ↥K (ℍ → ℂ) c) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      (c : ℂ) • (1 : ℍ → ℂ) := by
    funext τ
    simp only [Pi.mul_apply, pow_zero, mul_one, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul]
    rfl
  have hone_bd : IsBoundedAtImInfty (1 : ℍ → ℂ) := by
    have h1 : (1 : ℍ → ℂ) = fun _ : ℍ => (1 : ℂ) := rfl
    rw [h1]
    exact Filter.const_boundedAtFilter _ _
  refine ⟨mdifferentiable_const, 0, ?_, ?_, ?_⟩
  · rw [hshape]
    intro x
    rfl
  · rw [hshape]
    have hc : ((c : ℂ) • (1 : ℍ → ℂ)) = fun _ : ℍ => (c : ℂ) := by
      funext τ
      simp
    rw [hc]
    exact Filter.const_boundedAtFilter _ _
  · intro n
    have han : AnalyticAt ℂ (cuspFunction N (1 : ℍ → ℂ)) 0 :=
      analyticAt_cuspFunction_zero_of (g := (1 : ℍ → ℂ)) mdifferentiable_const
        (periodic_one_fn N) hone_bd
    rw [hshape, qExpansion_smul han,
      qExpansion_one, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_one]
    split
    · rw [mul_one]
      exact c.2
    · rw [mul_zero]
      exact zero_mem _

private lemma KPole.add {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f + g) := by
  obtain ⟨hf1, m1, hfd⟩ := hf
  obtain ⟨hg1, m2, hgd⟩ := hg
  obtain ⟨hfper, hfbd, hfmem⟩ := hfd.pad hf1 (le_max_left m1 m2)
  obtain ⟨hgper, hgbd, hgmem⟩ := hgd.pad hg1 (le_max_right m1 m2)
  have hshape : ((f + g) * ⇑CuspForm.discriminant ^ max m1 m2 : ℍ → ℂ) =
      f * ⇑CuspForm.discriminant ^ max m1 m2 + g * ⇑CuspForm.discriminant ^ max m1 m2 := by
    funext τ
    simp [add_mul]
  refine ⟨hf1.add hg1, max m1 m2, ?_, ?_, ?_⟩
  · rw [hshape]
    exact hfper.add hgper
  · rw [hshape]
    exact hfbd.add hgbd
  · intro n
    rw [hshape, qExpansion_add
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hf1 _) hfper hfbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg1 _) hgper hgbd),
      map_add]
    exact add_mem (hfmem n) (hgmem n)

private lemma KPole.mul {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f * g) := by
  obtain ⟨hf1, m1, hfper, hfbd, hfmem⟩ := hf
  obtain ⟨hg1, m2, hgper, hgbd, hgmem⟩ := hg
  have hshape : ((f * g) * ⇑CuspForm.discriminant ^ (m1 + m2) : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m1) * (g * ⇑CuspForm.discriminant ^ m2) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  refine ⟨hf1.mul hg1, m1 + m2, ?_, ?_, ?_⟩
  · rw [hshape]
    exact hfper.mul hgper
  · rw [hshape]
    exact hfbd.mul hgbd
  · intro n
    rw [hshape, qExpansion_mul
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hf1 _) hfper hfbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg1 _) hgper hgbd),
      PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hfmem ij.1) (hgmem ij.2)

end KPoleAlgebra

section Transport

open ModularForm

variable {N : ℕ} {K : IntermediateField ℚ ℂ} {φ : ↥K →+* ℂ}

private def TransAt (K : IntermediateField ℚ ℂ) (φ : ↥K →+* ℂ) (N m : ℕ)
    (g g' : ℍ → ℂ) : Prop :=
  KPoleAt K N m g ∧ KPoleAt K N m g' ∧
  ∀ (n : ℕ) (z : ↥K), (z : ℂ) = (qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n →
    (qExpansion N (g' * ⇑CuspForm.discriminant ^ m)).coeff n = φ z

private def Trans (K : IntermediateField ℚ ℂ) (φ : ↥K →+* ℂ) (N : ℕ)
    (g g' : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g' ∧ ∃ m, TransAt K φ N m g g'

private lemma TransAt.of_eq {m m₂ : ℕ} {g₁ g₁' g₂ g₂' : ℍ → ℂ}
    (h : TransAt K φ N m g₁ g₁')
    (e : g₁ * ⇑CuspForm.discriminant ^ m = g₂ * ⇑CuspForm.discriminant ^ m₂)
    (e' : g₁' * ⇑CuspForm.discriminant ^ m = g₂' * ⇑CuspForm.discriminant ^ m₂) :
    TransAt K φ N m₂ g₂ g₂' := by
  obtain ⟨⟨h1, h2, h3⟩, ⟨h1', h2', h3'⟩, hrel⟩ := h
  rw [e] at h1 h2 h3
  rw [e'] at h1' h2' h3'
  refine ⟨⟨h1, h2, h3⟩, ⟨h1', h2', h3'⟩, ?_⟩
  intro n z hz
  rw [← e']
  rw [← e] at hz
  exact hrel n z hz

private lemma qExpansion_mul_pad [NeZero N] {m₁ m₂ : ℕ} {g₁ g₂ : ℍ → ℂ}
    (hg₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁) (hg₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂)
    (h₁per : Function.Periodic ((g₁ * ⇑CuspForm.discriminant ^ m₁) ∘ ofComplex) N)
    (h₁bd : IsBoundedAtImInfty (g₁ * ⇑CuspForm.discriminant ^ m₁))
    (h₂per : Function.Periodic ((g₂ * ⇑CuspForm.discriminant ^ m₂) ∘ ofComplex) N)
    (h₂bd : IsBoundedAtImInfty (g₂ * ⇑CuspForm.discriminant ^ m₂)) :
    qExpansion N ((g₁ * g₂) * ⇑CuspForm.discriminant ^ (m₁ + m₂)) =
      qExpansion N (g₁ * ⇑CuspForm.discriminant ^ m₁) *
        qExpansion N (g₂ * ⇑CuspForm.discriminant ^ m₂) := by
  have hshape : ((g₁ * g₂) * ⇑CuspForm.discriminant ^ (m₁ + m₂) : ℍ → ℂ) =
      (g₁ * ⇑CuspForm.discriminant ^ m₁) * (g₂ * ⇑CuspForm.discriminant ^ m₂) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  rw [hshape, qExpansion_mul
    (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₁ m₁) h₁per h₁bd)
    (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₂ m₂) h₂per h₂bd)]

private lemma KPoleAt.mulAt [NeZero N] {m₁ m₂ : ℕ} {g₁ g₂ : ℍ → ℂ}
    (hg₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁) (hg₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂)
    (h₁ : KPoleAt K N m₁ g₁) (h₂ : KPoleAt K N m₂ g₂) :
    KPoleAt K N (m₁ + m₂) (g₁ * g₂) := by
  obtain ⟨h₁per, h₁bd, h₁mem⟩ := h₁
  obtain ⟨h₂per, h₂bd, h₂mem⟩ := h₂
  have hshape : ((g₁ * g₂) * ⇑CuspForm.discriminant ^ (m₁ + m₂) : ℍ → ℂ) =
      (g₁ * ⇑CuspForm.discriminant ^ m₁) * (g₂ * ⇑CuspForm.discriminant ^ m₂) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hshape]
    exact h₁per.mul h₂per
  · rw [hshape]
    exact h₁bd.mul h₂bd
  · intro n
    rw [qExpansion_mul_pad hg₁ hg₂ h₁per h₁bd h₂per h₂bd, PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (h₁mem ij.1) (h₂mem ij.2)

private lemma TransAt.mulT [NeZero N] {m₁ m₂ : ℕ} {g₁ g₁' g₂ g₂' : ℍ → ℂ}
    (hg₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁) (hg₁' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁')
    (hg₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂) (hg₂' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂')
    (h₁ : TransAt K φ N m₁ g₁ g₁') (h₂ : TransAt K φ N m₂ g₂ g₂') :
    TransAt K φ N (m₁ + m₂) (g₁ * g₂) (g₁' * g₂') := by
  obtain ⟨hK₁, hK₁', hrel₁⟩ := h₁
  obtain ⟨hK₂, hK₂', hrel₂⟩ := h₂
  refine ⟨KPoleAt.mulAt hg₁ hg₂ hK₁ hK₂, KPoleAt.mulAt hg₁' hg₂' hK₁' hK₂', ?_⟩
  intro n z hz
  rw [qExpansion_mul_pad hg₁ hg₂ hK₁.1 hK₁.2.1 hK₂.1 hK₂.2.1, PowerSeries.coeff_mul] at hz
  rw [qExpansion_mul_pad hg₁' hg₂' hK₁'.1 hK₁'.2.1 hK₂'.1 hK₂'.2.1, PowerSeries.coeff_mul]
  have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      (qExpansion N (g₁' * ⇑CuspForm.discriminant ^ m₁)).coeff ij.1 *
        (qExpansion N (g₂' * ⇑CuspForm.discriminant ^ m₂)).coeff ij.2 =
      φ (⟨(qExpansion N (g₁ * ⇑CuspForm.discriminant ^ m₁)).coeff ij.1, hK₁.2.2 ij.1⟩ *
        ⟨(qExpansion N (g₂ * ⇑CuspForm.discriminant ^ m₂)).coeff ij.2, hK₂.2.2 ij.2⟩) := by
    intro ij _
    rw [map_mul, hrel₁ ij.1 ⟨_, hK₁.2.2 ij.1⟩ rfl, hrel₂ ij.2 ⟨_, hK₂.2.2 ij.2⟩ rfl]
  rw [Finset.sum_congr rfl hterm, ← map_sum]
  congr 1
  apply Subtype.ext
  rw [hz, AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun ij _ => rfl

private lemma transAt_self_of_rat [NeZero N] {m : ℕ} {g : ℍ → ℂ}
    (hper : Function.Periodic ((g * ⇑CuspForm.discriminant ^ m) ∘ ofComplex) N)
    (hbd : IsBoundedAtImInfty (g * ⇑CuspForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ q : ℚ, (qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n = (q : ℂ)) :
    TransAt K φ N m g g := by
  have hmem : ∀ n : ℕ, (qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n ∈ K :=
    fun n => mem_of_rat K (hrat n)
  refine ⟨⟨hper, hbd, hmem⟩, ⟨hper, hbd, hmem⟩, ?_⟩
  intro n z hz
  obtain ⟨q, hq⟩ := hrat n
  have hzq : z = (q : ↥K) := by
    apply Subtype.ext
    rw [hz, hq]
    push_cast
    rfl
  rw [hzq, map_ratCast, ← hq]

private lemma TransAt.padT [NeZero N] {m m' : ℕ} {g g' : ℍ → ℂ}
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hg' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g')
    (hm : m ≤ m') (h : TransAt K φ N m g g') : TransAt K φ N m' g g' := by
  have hone : ∀ k : ℕ, ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) *
      ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) = ⇑CuspForm.discriminant ^ k := by
    intro k; funext τ; simp
  have hΔ : TransAt K φ N 0 ((⇑CuspForm.discriminant : ℍ → ℂ) ^ (m' - m))
      ((⇑CuspForm.discriminant : ℍ → ℂ) ^ (m' - m)) := by
    refine transAt_self_of_rat ?_ ?_ ?_
    · rw [hone]
      exact periodic_discPow_comp_ofComplex (m' - m) N
    · rw [hone]
      exact isBoundedAtImInfty_discPow (m' - m)
    · intro n
      rw [hone]
      have hper1 : Function.Periodic
          ((⇑CuspForm.discriminant ^ (m' - m) : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
        have h2 := periodic_discPow_comp_ofComplex (m' - m) 1
        simpa only [Nat.cast_one] using h2
      rw [qExpansion_coeff_width _ (NeZero.ne N) hper1 (mdiff_discPow (m' - m))
        (isBoundedAtImInfty_discPow (m' - m)), qExpansion_one_discPow]
      split
      · exact ratCoeff_pow ratCoeff_discriminant (m' - m) _
      · exact ⟨0, by push_cast; ring⟩
  have hmul := TransAt.mulT hg hg' (mdiff_discPow (m' - m)) (mdiff_discPow (m' - m)) h hΔ
  refine hmul.of_eq ?_ ?_
  · funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, show m' - m + (m + 0) = m' by omega]
  · funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, show m' - m + (m + 0) = m' by omega]

private lemma TransAt.addT [NeZero N] {m : ℕ} {g₁ g₁' g₂ g₂' : ℍ → ℂ}
    (hg₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁) (hg₁' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁')
    (hg₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂) (hg₂' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂')
    (h₁ : TransAt K φ N m g₁ g₁') (h₂ : TransAt K φ N m g₂ g₂') :
    TransAt K φ N m (g₁ + g₂) (g₁' + g₂') := by
  obtain ⟨⟨h₁per, h₁bd, h₁mem⟩, ⟨h₁per', h₁bd', h₁mem'⟩, hrel₁⟩ := h₁
  obtain ⟨⟨h₂per, h₂bd, h₂mem⟩, ⟨h₂per', h₂bd', h₂mem'⟩, hrel₂⟩ := h₂
  have hshape : ∀ a b : ℍ → ℂ, ((a + b) * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) =
      a * ⇑CuspForm.discriminant ^ m + b * ⇑CuspForm.discriminant ^ m := by
    intro a b; funext τ; simp only [Pi.add_apply, Pi.mul_apply]; ring
  have hq : qExpansion N ((g₁ + g₂) * ⇑CuspForm.discriminant ^ m) =
      qExpansion N (g₁ * ⇑CuspForm.discriminant ^ m) +
        qExpansion N (g₂ * ⇑CuspForm.discriminant ^ m) := by
    rw [hshape, qExpansion_add
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₁ m) h₁per h₁bd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₂ m) h₂per h₂bd)]
  have hq' : qExpansion N ((g₁' + g₂') * ⇑CuspForm.discriminant ^ m) =
      qExpansion N (g₁' * ⇑CuspForm.discriminant ^ m) +
        qExpansion N (g₂' * ⇑CuspForm.discriminant ^ m) := by
    rw [hshape, qExpansion_add
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₁' m) h₁per' h₁bd')
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₂' m) h₂per' h₂bd')]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hshape]; exact h₁per.add h₂per
  · rw [hshape]; exact h₁bd.add h₂bd
  · intro n
    rw [hq, map_add]
    exact add_mem (h₁mem n) (h₂mem n)
  · rw [hshape]; exact h₁per'.add h₂per'
  · rw [hshape]; exact h₁bd'.add h₂bd'
  · intro n
    rw [hq', map_add]
    exact add_mem (h₁mem' n) (h₂mem' n)
  · intro n z hz
    rw [hq, map_add] at hz
    rw [hq', map_add, hrel₁ n ⟨_, h₁mem n⟩ rfl, hrel₂ n ⟨_, h₂mem n⟩ rfl, ← map_add]
    congr 1
    apply Subtype.ext
    rw [hz]
    rfl

private lemma Trans.addF [NeZero N] {g₁ g₁' g₂ g₂' : ℍ → ℂ}
    (h₁ : Trans K φ N g₁ g₁') (h₂ : Trans K φ N g₂ g₂') :
    Trans K φ N (g₁ + g₂) (g₁' + g₂') := by
  obtain ⟨hm₁, hm₁', m₁, hT₁⟩ := h₁
  obtain ⟨hm₂, hm₂', m₂, hT₂⟩ := h₂
  exact ⟨hm₁.add hm₂, hm₁'.add hm₂', max m₁ m₂,
    TransAt.addT hm₁ hm₁' hm₂ hm₂'
      (hT₁.padT hm₁ hm₁' (le_max_left m₁ m₂))
      (hT₂.padT hm₂ hm₂' (le_max_right m₁ m₂))⟩

private lemma Trans.mulF [NeZero N] {g₁ g₁' g₂ g₂' : ℍ → ℂ}
    (h₁ : Trans K φ N g₁ g₁') (h₂ : Trans K φ N g₂ g₂') :
    Trans K φ N (g₁ * g₂) (g₁' * g₂') := by
  obtain ⟨hm₁, hm₁', m₁, hT₁⟩ := h₁
  obtain ⟨hm₂, hm₂', m₂, hT₂⟩ := h₂
  exact ⟨hm₁.mul hm₂, hm₁'.mul hm₂', m₁ + m₂, TransAt.mulT hm₁ hm₁' hm₂ hm₂' hT₁ hT₂⟩

private lemma qExpansion_const_coeff [NeZero N] (x : ℂ) (n : ℕ) :
    (qExpansion N ((fun _ : ℍ => x) * ⇑CuspForm.discriminant ^ 0)).coeff n =
      if n = 0 then x else 0 := by
  have hshape : ((fun _ : ℍ => x) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      x • (1 : ℍ → ℂ) := by
    funext τ; simp
  have hone_bd : IsBoundedAtImInfty (1 : ℍ → ℂ) := by
    have h1 : (1 : ℍ → ℂ) = fun _ : ℍ => (1 : ℂ) := rfl
    rw [h1]
    exact Filter.const_boundedAtFilter _ _
  have han : AnalyticAt ℂ (cuspFunction N (1 : ℍ → ℂ)) 0 :=
    analyticAt_cuspFunction_zero_of (g := (1 : ℍ → ℂ)) mdifferentiable_const
      (periodic_one_fn N) hone_bd
  rw [hshape, qExpansion_smul han, qExpansion_one, PowerSeries.coeff_smul, smul_eq_mul,
    PowerSeries.coeff_one]
  split <;> simp

private lemma transAt_const [NeZero N] (hφK : ∀ z : ↥K, φ z ∈ K) (c : ↥K) :
    TransAt K φ N 0 (fun _ : ℍ => (c : ℂ)) (fun _ : ℍ => φ c) := by
  have hdata : ∀ x : ℂ, Function.Periodic
      (((fun _ : ℍ => x) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) ∘ ofComplex) N ∧
      IsBoundedAtImInfty ((fun _ : ℍ => x) * ⇑CuspForm.discriminant ^ 0) := by
    intro x
    have hshape : ((fun _ : ℍ => x) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
        fun _ : ℍ => x := by
      funext τ; simp
    rw [hshape]
    exact ⟨fun t => rfl, Filter.const_boundedAtFilter _ _⟩
  refine ⟨⟨(hdata _).1, (hdata _).2, ?_⟩, ⟨(hdata _).1, (hdata _).2, ?_⟩, ?_⟩
  · intro n
    rw [qExpansion_const_coeff]
    split
    · exact c.2
    · exact zero_mem _
  · intro n
    rw [qExpansion_const_coeff]
    split
    · exact hφK c
    · exact zero_mem _
  · intro n z hz
    rw [qExpansion_const_coeff] at hz
    rw [qExpansion_const_coeff]
    split at hz
    · rename_i hn
      rw [ite_eq_left hn]
      have hzc : z = c := Subtype.ext hz
      rw [hzc]
    · rename_i hn
      rw [ite_eq_right hn]
      have hz0 : z = 0 := Subtype.ext (by rw [hz]; rfl)
      rw [hz0, map_zero]

private lemma trans_jf [NeZero N] {jf : ℍ → ℂ}
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    Trans K φ N jf jf := by
  have hshape : (jf * ⇑CuspForm.discriminant ^ 1 : ℍ → ℂ) = ⇑(ModularForm.E₄.pow 3) := by
    funext τ
    rw [congrFun (ModularForm.coe_pow ModularForm.E₄ 3) τ, Pi.pow_apply]
    simp only [Pi.mul_apply, pow_one, hjf τ]
    rw [congrFun CuspForm.coe_discriminant τ]
    exact div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)
  have hhol3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) :=
    (ModularForm.E₄.pow 3).holo'
  have hbd3 : IsBoundedAtImInfty (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) :=
    ModularFormClass.bdd_at_infty (ModularForm.E₄.pow 3)
  have hper3 : Function.Periodic ((⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E₄.pow 3)
      one_mem_strictPeriods_SL
  have hjmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
    have h1 : jf = fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := funext hjf
    rw [h1]
    exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  refine ⟨hjmd, hjmd, 1, transAt_self_of_rat ?_ ?_ ?_⟩
  · rw [hshape]
    simpa using hper3.nat_mul N
  · rw [hshape]
    exact hbd3
  · intro n
    rw [hshape, qExpansion_coeff_width (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) (NeZero.ne N)
      hper3 hhol3 hbd3]
    split
    · have he : qExpansion 1 (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) =
          (qExpansion 1 ModularForm.E₄) ^ 3 :=
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3
      rw [he]
      exact ratCoeff_pow (ratCoeff_E (by norm_num) (by decide)) 3 _
    · exact ⟨0, by push_cast; ring⟩

private lemma trans_aeval [NeZero N] (hφK : ∀ z : ↥K, φ z ∈ K) {Idx : Type*}
    {gen gen' : Idx → ℍ → ℂ}
    (hgen : ∀ i, Trans K φ N (gen i) (gen' i)) (R : MvPolynomial Idx ↥K) :
    Trans K φ N (MvPolynomial.aeval gen (MvPolynomial.map (algebraMap ↥K ℂ) R))
      (MvPolynomial.aeval gen' (MvPolynomial.map (φ : ↥K →+* ℂ) R)) := by
  induction R using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    have e1 : (algebraMap ℂ (ℍ → ℂ)) ((algebraMap ↥K ℂ) c) = fun _ : ℍ => (c : ℂ) := rfl
    have e2 : (algebraMap ℂ (ℍ → ℂ)) (φ c) = fun _ : ℍ => φ c := rfl
    rw [e1, e2]
    exact ⟨mdifferentiable_const, mdifferentiable_const, 0, transAt_const hφK c⟩
  | add p q ihp ihq =>
    rw [map_add, map_add, map_add, map_add]
    exact Trans.addF ihp ihq
  | mul_X p i ih =>
    have e1 : MvPolynomial.map (algebraMap ↥K ℂ) (p * MvPolynomial.X i) =
        MvPolynomial.map (algebraMap ↥K ℂ) p * MvPolynomial.X i := by
      rw [map_mul, MvPolynomial.map_X]
    have e2 : MvPolynomial.map (φ : ↥K →+* ℂ) (p * MvPolynomial.X i) =
        MvPolynomial.map (φ : ↥K →+* ℂ) p * MvPolynomial.X i := by
      rw [map_mul, MvPolynomial.map_X]
    rw [e1, e2, map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact Trans.mulF ih (hgen i)

end Transport

section IdentityTransport

open ModularForm

variable {N : ℕ} {K : IntermediateField ℚ ℂ} {φ : ↥K →+* ℂ}

private lemma analyticAt_zero_fn [NeZero N] :
    AnalyticAt ℂ (cuspFunction N (0 : ℍ → ℂ)) 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine analyticAt_cuspFunction_zero hN' (fun x => rfl) mdifferentiable_const ?_
  have h0 : (0 : ℍ → ℂ) = fun _ : ℍ => (0 : ℂ) := rfl
  rw [h0]
  exact Filter.const_boundedAtFilter _ _

private lemma qExpansion_zero_fn [NeZero N] : qExpansion N (0 : ℍ → ℂ) = 0 := by
  have h0 : (0 : ℍ → ℂ) = (0 : ℂ) • (0 : ℍ → ℂ) := by rw [zero_smul]
  rw [h0, qExpansion_smul analyticAt_zero_fn, zero_smul]

private lemma discPow_ne_zero (m : ℕ) (τ : ℍ) :
    ((⇑CuspForm.discriminant : ℍ → ℂ) ^ m) τ ≠ 0 := by
  simp only [Pi.pow_apply]
  refine pow_ne_zero m ?_
  rw [congrFun CuspForm.coe_discriminant τ]
  exact ModularForm.discriminant_ne_zero τ

private lemma Trans.eq_zero_fwd [NeZero N] {g g' : ℍ → ℂ}
    (h : Trans K φ N g g') (hg0 : g = 0) : g' = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hm, hm', m, ⟨hK1, hK1', hrel⟩⟩ := h
  have hq0 : qExpansion N (g * ⇑CuspForm.discriminant ^ m) = 0 := by
    have h1 : (g * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = 0 := by
      rw [hg0]; funext τ; simp
    rw [h1, qExpansion_zero_fn]
  have hq0' : qExpansion N (g' * ⇑CuspForm.discriminant ^ m) = 0 := by
    ext n
    have hcoeff : (qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n = 0 := by
      rw [hq0, map_zero]
    have h2 := hrel n ⟨_, hK1.2.2 n⟩ rfl
    rw [h2]
    have hz0 : (⟨(qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n, hK1.2.2 n⟩ : ↥K)
        = 0 := Subtype.ext hcoeff
    rw [hz0, map_zero, map_zero]
  have hfn0 : (g' * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = 0 := by
    rw [qExpansion_eq_zero_iff hN' hK1'.1 (mdiff_mul_discPow hm' m) hK1'.2.1] at hq0'
    exact hq0'
  funext τ
  have h3 := congrFun hfn0 τ
  simp only [Pi.mul_apply, Pi.zero_apply] at h3 ⊢
  exact (mul_eq_zero.mp h3).resolve_right (discPow_ne_zero m τ)

private lemma Trans.eq_zero_rev [NeZero N] {g g' : ℍ → ℂ}
    (h : Trans K φ N g g') (hg0' : g' = 0) : g = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hm, hm', m, ⟨hK1, hK1', hrel⟩⟩ := h
  have hq0' : qExpansion N (g' * ⇑CuspForm.discriminant ^ m) = 0 := by
    have h1 : (g' * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = 0 := by
      rw [hg0']; funext τ; simp
    rw [h1, qExpansion_zero_fn]
  have hq0 : qExpansion N (g * ⇑CuspForm.discriminant ^ m) = 0 := by
    ext n
    have h2 := hrel n ⟨_, hK1.2.2 n⟩ rfl
    have h3 : φ (⟨(qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n, hK1.2.2 n⟩ : ↥K)
        = 0 := by
      rw [← h2, hq0', map_zero]
    have h4 := φ.injective (by rw [h3, map_zero] :
      φ (⟨(qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n, hK1.2.2 n⟩ : ↥K) = φ 0)
    have h5 := congrArg (fun z : ↥K => (z : ℂ)) h4
    simpa using h5
  have hfn0 : (g * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = 0 := by
    rw [qExpansion_eq_zero_iff hN' hK1.1 (mdiff_mul_discPow hm m) hK1.2.1] at hq0
    exact hq0
  funext τ
  have h3 := congrFun hfn0 τ
  simp only [Pi.mul_apply, Pi.zero_apply] at h3 ⊢
  exact (mul_eq_zero.mp h3).resolve_right (discPow_ne_zero m τ)

end IdentityTransport

end WLight

open _root_.WLight WLight in
theorem _root_.WLight.qExpansion_sigmaTransport_package (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ ℂ) (φ : ↥K →+* ℂ) (hφK : ∀ z : ↥K, φ z ∈ K)
    (T : (ℍ → ℂ) → (ℍ → ℂ) → Prop)
    (hT : ∀ g g' : ℍ → ℂ, T g g' ↔
        (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g' ∧
          ∃ m : ℕ,
            (Function.Periodic ((g * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
              IsBoundedAtImInfty (g * ModularForm.discriminant ^ m) ∧
              ∀ n : ℕ,
                (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
            (Function.Periodic ((g' * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
              IsBoundedAtImInfty (g' * ModularForm.discriminant ^ m) ∧
              ∀ n : ℕ,
                (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
            ∀ (n : ℕ) (z : ↥K),
              (z : ℂ) = (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n →
              (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n = φ z)) :
    (∀ {ι : Type} (g g' : ι → ℍ → ℂ), (∀ i : ι, T (g i) (g' i)) → ∀ R : MvPolynomial ι ↥K,
        T (MvPolynomial.aeval g (MvPolynomial.map (algebraMap ↥K ℂ) R))
          (MvPolynomial.aeval g' (MvPolynomial.map φ R))) ∧
    (∀ g g' : ℍ → ℂ, T g g' → (g = 0 ↔ g' = 0)) ∧
    ∀ jf : ℍ → ℂ, (∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) → T jf jf := by
  have hT' : ∀ g g' : ℍ → ℂ, T g g' ↔ Trans K φ N g g' := fun g g' => hT g g'
  refine ⟨fun g g' hg R => ?_, fun g g' h => ?_, fun jf hjf => (hT' jf jf).mpr (trans_jf hjf)⟩
  · exact (hT' _ _).mpr (trans_aeval hφK (fun i => (hT' _ _).mp (hg i)) R)
  · have h' := (hT' g g').mp h
    exact ⟨fun h0 => h'.eq_zero_fwd h0, fun h0 => h'.eq_zero_rev h0⟩
end
end WLightS9.S_WLight_qExpansion_sigmaTransport_package


namespace WLightS9.S_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction

set_option autoImplicit false

noncomputable section

open _root_.Complex _root_.Real _root_.UpperHalfPlane _root_.Function _root_.Filter _root_.Polynomial _root_.Real.Polynomial
open scoped _root_.Complex _root_.Real _root_.UpperHalfPlane _root_.Function _root_.Filter _root_.Polynomial _root_.Real.Polynomial
open scoped Topology Manifold MatrixGroups ModularForm

namespace WLight
open _root_.WLight
open _root_.WLight
open scoped _root_.WLight

section Division

private theorem powerSeries_coeff_mem_of_mul_eq {K : Type*} [Field K] (k : Subfield K)
    {g h f : PowerSeries K} (heq : g * h = f) (hg0 : PowerSeries.constantCoeff g ≠ 0)
    (hg : ∀ n, PowerSeries.coeff n g ∈ k) (hf : ∀ n, PowerSeries.coeff n f ∈ k) :
    ∀ n, PowerSeries.coeff n h ∈ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hcm := PowerSeries.coeff_mul n g h
  rw [heq] at hcm
  have h0n : (0, n) ∈ Finset.HasAntidiagonal.antidiagonal n := Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add n)
  rw [← Finset.add_sum_erase _ _ h0n] at hcm
  have hg0' : PowerSeries.coeff 0 g ≠ 0 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hrest : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
      PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 h) ∈ k := by
    refine sum_mem fun p hp ↦ mul_mem (hg p.1) (ih p.2 ?_)
    obtain ⟨hpne, hpmem⟩ := Finset.mem_erase.mp hp
    have hpsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hpmem
    rcases p with ⟨p1, p2⟩
    simp only [Prod.mk.injEq, not_and, ne_eq] at hpne
    dsimp only at hpsum
    omega
  have hn : PowerSeries.coeff n h = (PowerSeries.coeff 0 g)⁻¹ *
      (PowerSeries.coeff n f - ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
        PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 h) := by
    rw [eq_inv_mul_iff_mul_eq₀ hg0', eq_sub_iff_add_eq]
    exact hcm.symm
  rw [hn]
  exact mul_mem (inv_mem (hg 0)) (sub_mem (hf n) hrest)

private theorem powerSeries_coeff_mem_of_mul_eq' {K : Type*} [Field K] (k : Subfield K)
    {g h f : PowerSeries K} (heq : g * h = f) (hg0 : g ≠ 0)
    (hg : ∀ n, PowerSeries.coeff n g ∈ k) (hf : ∀ n, PowerSeries.coeff n f ∈ k) :
    ∀ n, PowerSeries.coeff n h ∈ k := by
  set r := (PowerSeries.order g).toNat with hr_def
  obtain ⟨g', hg'⟩ : (PowerSeries.X : PowerSeries K) ^ r ∣ g := PowerSeries.X_pow_dvd_iff.mpr
    (fun m hm ↦ PowerSeries.coeff_of_lt_order_toNat (φ := g) m hm)
  have hg'_coeff : ∀ n, PowerSeries.coeff n g' ∈ k := fun n ↦ by
    have h1 := hg (n + r)
    rwa [hg', PowerSeries.coeff_X_pow_mul g' r n] at h1
  have hg'_cc : PowerSeries.constantCoeff g' ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    intro habs
    refine (PowerSeries.coeff_order hg0) ?_
    show PowerSeries.coeff r g = 0
    rw [hg', PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, habs]
  obtain ⟨f', hf'⟩ : PowerSeries.X ^ r ∣ f := ⟨g' * h, by rw [← heq, hg', mul_assoc]⟩
  have hf'_coeff : ∀ n, PowerSeries.coeff n f' ∈ k := fun n ↦ by
    have h1 := hf (n + r); rwa [hf', PowerSeries.coeff_X_pow_mul f' r n] at h1
  have heq' : g' * h = f' := by
    have hX : (PowerSeries.X : PowerSeries K) ^ r ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
    have h2 := hf' ▸ hg' ▸ heq
    rw [mul_assoc] at h2
    exact mul_left_cancel₀ hX h2
  exact powerSeries_coeff_mem_of_mul_eq k heq' hg'_cc hg'_coeff hf'_coeff

private theorem norm_le_of_monicRel {K : Type*} [NormedField K] {z : K} {a : ℕ → K} {d : ℕ}
    (h : z ^ d + ∑ n ∈ Finset.range d, a n * z ^ n = 0) :
    ‖z‖ ≤ 1 + ∑ n ∈ Finset.range d, ‖a n‖ := by
  have hsum : ‖z‖ ^ d ≤ ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ n := by
    calc ‖z‖ ^ d = ‖z ^ d‖ := (norm_pow _ _).symm
      _ = ‖-∑ n ∈ Finset.range d, a n * z ^ n‖ :=
          congrArg _ (eq_neg_of_add_eq_zero_left h)
      _ = ‖∑ n ∈ Finset.range d, a n * z ^ n‖ := norm_neg _
      _ ≤ ∑ n ∈ Finset.range d, ‖a n * z ^ n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ n :=
          Finset.sum_congr rfl fun n _ ↦ by rw [norm_mul, norm_pow]
  rcases le_or_gt ‖z‖ 1 with h1 | h1
  · exact h1.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
  · have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos h1.le
    have hd : 0 < d := by
      by_contra hd0
      simp only [Nat.eq_zero_of_not_pos hd0, pow_zero, Finset.range_zero,
        Finset.sum_empty] at hsum
      exact absurd hsum (not_le.mpr one_pos)
    have hpow : ∀ n ∈ Finset.range d, ‖z‖ ^ n ≤ ‖z‖ ^ (d - 1) := fun n hn ↦
      pow_le_pow_right₀ h1.le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hn))
    have : ‖z‖ ^ d ≤ (∑ n ∈ Finset.range d, ‖a n‖) * ‖z‖ ^ (d - 1) := by
      calc ‖z‖ ^ d ≤ ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ n := hsum
        _ ≤ ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ (d - 1) :=
            Finset.sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_left (hpow n hn) (norm_nonneg _)
        _ = (∑ n ∈ Finset.range d, ‖a n‖) * ‖z‖ ^ (d - 1) := (Finset.sum_mul ..).symm
    have hzd : ‖z‖ ^ d = ‖z‖ * ‖z‖ ^ (d - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hd]
    rw [hzd] at this
    have := le_of_mul_le_mul_right (a := ‖z‖ ^ (d - 1)) this (pow_pos hzpos _)
    linarith

open Asymptotics in

private theorem isBoundedAtImInfty_of_monicRel {H : ℍ → ℂ} {c : ℕ → ℍ → ℂ} {d : ℕ}
    (hc : ∀ n < d, IsBoundedAtImInfty (c n))
    (hrel : ∀ τ : ℍ, H τ ^ d + ∑ n ∈ Finset.range d, c n τ * H τ ^ n = 0) :
    IsBoundedAtImInfty H := by
  classical
  choose! C hC using fun n (hn : n < d) ↦ isBigO_iff.mp (hc n hn)
  simp only [Pi.one_apply, norm_one, mul_one] at hC
  have hCev : ∀ᶠ τ in atImInfty, ∀ n ∈ Finset.range d, ‖c n τ‖ ≤ C n :=
    eventually_all_finset (Finset.range d) |>.mpr fun n hn ↦ hC n (Finset.mem_range.mp hn)
  refine IsBigO.of_bound (1 + ∑ n ∈ Finset.range d, C n) (hCev.mono fun τ hτ ↦ ?_)
  rw [Pi.one_apply, norm_one, mul_one]
  calc ‖H τ‖ ≤ 1 + ∑ n ∈ Finset.range d, ‖c n τ‖ :=
        norm_le_of_monicRel (a := fun n ↦ c n τ) (hrel τ)
    _ ≤ 1 + ∑ n ∈ Finset.range d, C n := by gcongr with n hn; exact hτ n hn

end Division

section CuspCriterion

variable {N : ℕ}

private lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

private lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ Filter.const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

private lemma IsBoundedAtImInfty.mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
    (h : IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)) :
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m') := by
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hshape]
  exact h.mul (isBoundedAtImInfty_discPow (m' - m))

private def discPowForm (m : ℕ) : ModularForm 𝒮ℒ (12 * m) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow m)

private lemma discPowForm_coe (m : ℕ) : ⇑(discPowForm m) = ⇑CuspForm.discriminant ^ m := by
  funext z
  simp [discPowForm, ModularForm.coe_mcast, ModularForm.coe_pow,
    CuspForm.toModularFormₗ_apply]

private lemma periodic_one_fn (c : ℝ) : Function.Periodic ((1 : ℍ → ℂ) ∘ ofComplex) c := fun _ => rfl

private lemma periodic_discPow_comp_ofComplex (k : ℕ) (N : ℕ) :
    Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) N := by
  have h1 : Function.Periodic (⇑CuspForm.discriminant ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL
  have hk : Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) 1 := by
    induction k with
    | zero => exact periodic_one_fn 1
    | succ k ih =>
      intro x
      have hx := (ih.mul h1) x
      simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply] at hx ⊢
      rw [pow_succ, pow_succ]
      exact hx
  simpa using hk.nat_mul N

private lemma mdiff_discPow (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑CuspForm.discriminant ^ k : ℍ → ℂ) := by
  rw [← discPowForm_coe]
  exact (discPowForm k).holo'

private lemma mdiff_mul_discPow {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (m : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) :=
  hf.mul (mdiff_discPow m)

private lemma analyticAt_cuspFunction_zero_of [NeZero N] {g : ℍ → ℂ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Function.Periodic (g ∘ ofComplex) N) (hbd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction N g) 0 :=
  analyticAt_cuspFunction_zero
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd

private lemma qExpansion_one_discPowForm (k : ℕ) :
    qExpansion 1 (discPowForm k) = (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [discPowForm, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hco : (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) =
      ModularForm.discriminant := by
    funext z
    rw [CuspForm.toModularFormₗ_apply]
    exact congrFun CuspForm.coe_discriminant z
  rw [hco]

private lemma qExpansion_one_discPow (k : ℕ) :
    qExpansion 1 (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [← discPowForm_coe]
  exact qExpansion_one_discPowForm k

private lemma coeff_pow_eq_zero_of_lt {D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) {k n : ℕ}
    (hn : n < k) : (D ^ k).coeff n = 0 := by
  have hX : (PowerSeries.X : PowerSeries ℂ) ∣ D :=
    PowerSeries.X_dvd_iff.mpr (by rwa [← PowerSeries.coeff_zero_eq_constantCoeff])
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX k) n hn

private lemma discriminant_qExpansion_coeff_zero :
    (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

private lemma qParam_one_eq_pow {N : ℕ} (hN : N ≠ 0) (τ : ℂ) :
    Function.Periodic.qParam 1 τ = Function.Periodic.qParam N τ ^ N := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

private theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperN : Function.Periodic (f ∘ ofComplex) N := by
    simpa using hper.nat_mul N
  let f' : C(ℍ, ℂ) := ⟨f, hhol.continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN' hperN hhol hbd
  set c : ℕ → ℂ := fun n ↦ if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 with hc
  have hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam N τ ^ m) (f' τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hhol hbd τ
    have hinj : Function.Injective fun m : ℕ ↦ N * m := fun a b h ↦ by
      simpa [Nat.mul_right_inj hN] using h
    refine (hinj.hasSum_iff (f := fun m ↦ c m • Function.Periodic.qParam N τ ^ m) ?_).mp ?_
    · intro x hx
      have : ¬ N ∣ x := fun ⟨k, hk⟩ ↦ hx ⟨k, hk.symm⟩
      simp [hc, this]
    · refine h1.congr_fun fun m ↦ ?_
      simp only [Function.comp_apply, hc, Nat.dvd_mul_right, ite_true,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN), qParam_one_eq_pow hN, ← pow_mul]
  exact (qExpansion_coeff_unique f' hN' hfan hf n).symm

private theorem isZeroAtImInfty_iff_qExpansion_coeff_zero_eq_zero {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfbdd : IsBoundedAtImInfty f) :
    IsZeroAtImInfty f ↔ (qExpansion h f).coeff 0 = 0 := by
  have hanal := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  rw [qExpansion_coeff_zero hh hanal hfper]
  refine ⟨fun hf ↦ hf.valueAtInfty_eq_zero, fun hv ↦ ?_⟩
  rw [IsZeroAtImInfty, ZeroAtFilter, ← hv, ← cuspFunction_apply_zero hh hanal hfper]
  exact (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr
    (fun τ ↦ eq_cuspFunction τ hh.ne' hfper)

open Asymptotics in

private theorem isBigO_qParam_pow_of_qExpansion_coeff_eq_zero {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfbdd : IsBoundedAtImInfty f)
    {k : ℕ} (hcoeff : ∀ n ≤ k, (qExpansion h f).coeff n = 0) :
    f =O[atImInfty] fun τ ↦ (Periodic.qParam h τ) ^ (k + 1) := by
  have hanal := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  have hideriv : ∀ i < k + 1, iteratedDeriv i (cuspFunction h f) 0 = 0 := by
    intro i hi
    have hci := hcoeff i (Nat.lt_succ_iff.mp hi)
    rw [qExpansion_coeff] at hci
    have hfac : ((i.factorial : ℂ))⁻¹ ≠ 0 :=
      inv_ne_zero (Nat.cast_ne_zero.mpr i.factorial_ne_zero)
    exact (mul_eq_zero.mp hci).resolve_left hfac
  have hord : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanal).mpr hideriv
  obtain ⟨g, hgan, hfac⟩ := (natCast_le_analyticOrderAt hanal).mp hord
  have hOcf : (cuspFunction h f) =O[𝓝 0] fun q : ℂ ↦ q ^ (k + 1) := by
    have hg1 : g =O[𝓝 (0 : ℂ)] (fun _ : ℂ ↦ (1 : ℂ)) := hgan.continuousAt.isBigO_one ℂ
    refine ((isBigO_refl (fun q : ℂ ↦ q ^ (k + 1)) (𝓝 0)).mul hg1).congr' ?_
      (.of_forall fun q ↦ mul_one _)
    filter_upwards [hfac] with q hq
    rw [hq, sub_zero, smul_eq_mul]
  refine (hOcf.comp_tendsto (qParam_tendsto_atImInfty hh)).congr' ?_ (.of_forall fun τ ↦ rfl)
  exact .of_forall fun τ ↦ eq_cuspFunction τ hh.ne' hfper

open Asymptotics ModularForm in

private theorem qParam_pow_isBigO_discPow {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    (fun τ : ℍ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * k)) =O[atImInfty]
      (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ k) := by
  refine .trans (IsBigO.of_bound 1 (.of_forall fun τ ↦ le_of_eq ?_)) (exp_isBigO_discriminant.pow k)
  rw [one_mul, norm_pow, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le,
    pow_mul, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, UpperHalfPlane.coe_im]
  congr 2
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp

open Asymptotics ModularForm in

private theorem isZeroAtImInfty_mul_disc_of_coeff_le {N : ℕ} (hN : N ≠ 0) {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M)
    (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F * ⇑CuspForm.discriminant ^ M))
    (hfper : Periodic ((F * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N)
    (hfbd : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ M))
    (hcoeff : ∀ n ≤ N * (M - 1), (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0) :
    IsZeroAtImInfty (F * ⇑CuspForm.discriminant) := by
  set G : ℍ → ℂ := F * ⇑CuspForm.discriminant ^ M with hGdef
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hGO : G =O[atImInfty]
      fun τ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * (M - 1) + 1) :=
    isBigO_qParam_pow_of_qExpansion_coeff_eq_zero hN' hfper hfhol hfbd hcoeff
  have hqO : (fun τ : ℍ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * (M - 1) + 1))
      =O[atImInfty]
        (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ (M - 1) *
          Periodic.qParam (N : ℝ) (τ : ℂ)) :=
    ((qParam_pow_isBigO_discPow hN (M - 1)).mul
        (isBigO_refl (fun τ : ℍ ↦ Periodic.qParam (N : ℝ) (τ : ℂ)) atImInfty)).congr_left
      (fun τ ↦ (pow_succ _ _).symm)
  have hGO' : G =O[atImInfty]
      (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ (M - 1) *
        Periodic.qParam (N : ℝ) (τ : ℂ)) := hGO.trans hqO
  have hfdeq : ∀ τ : ℍ, (F * ⇑CuspForm.discriminant) τ
      = G τ / (ModularForm.discriminant τ) ^ (M - 1) := fun τ ↦ by
    have hΔ := ModularForm.discriminant_ne_zero τ
    simp only [hGdef, Pi.mul_apply, Pi.pow_apply, CuspForm.coe_discriminant]
    rw [eq_div_iff (pow_ne_zero _ hΔ), mul_assoc, ← pow_succ', Nat.sub_add_cancel hM]
  have hfneq : (fun τ : ℍ ↦ ‖G τ / ((ModularForm.discriminant τ : ℂ) ^ (M - 1) *
        Periodic.qParam (N : ℝ) (τ : ℂ))‖)
      = (fun τ ↦ ‖(F * ⇑CuspForm.discriminant) τ / Periodic.qParam (N : ℝ) (τ : ℂ)‖) :=
    funext fun τ ↦ by rw [hfdeq, div_div]
  have hbnd : IsBoundedUnder (· ≤ ·) atImInfty
      (fun τ : ℍ ↦ ‖(F * ⇑CuspForm.discriminant) τ / Periodic.qParam (N : ℝ) (τ : ℂ)‖) :=
    hfneq ▸ div_isBoundedUnder_of_isBigO hGO'
  have hq_ne : ∀ τ : ℍ, Periodic.qParam (N : ℝ) (τ : ℂ) ≠ 0 := fun τ ↦
    Complex.exp_ne_zero _
  have hFDO : (F * ⇑CuspForm.discriminant) =O[atImInfty]
      (fun τ : ℍ ↦ Periodic.qParam (N : ℝ) (τ : ℂ)) :=
    (isBigO_iff_div_isBoundedUnder (.of_forall fun τ h ↦ absurd h (hq_ne τ))).mpr hbnd
  exact hFDO.trans_tendsto (qParam_tendsto_atImInfty hN')

open ModularForm in

private lemma qExpansion_discPow_coeff_eq_zero_of_lt [NeZero N] (k : ℕ) {j : ℕ} (hj : j < N * k) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff j = 0 := by
  have hper : Function.Periodic
      ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
    have h := periodic_discPow_comp_ofComplex k 1
    simpa only [Nat.cast_one] using h
  rw [qExpansion_coeff_width _ (NeZero.ne N) hper
    (mdiff_discPow k) (isBoundedAtImInfty_discPow k), qExpansion_one_discPow]
  split_ifs with hN
  · exact coeff_pow_eq_zero_of_lt discriminant_qExpansion_coeff_zero
      (Nat.div_lt_of_lt_mul (Nat.mul_comm N k ▸ hj))
  · rfl

open ModularForm in

private theorem qExpansion_coeff_eq_zero_of_isZeroAtImInfty_mul_disc [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M) (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ ofComplex) N)
    (hz : IsZeroAtImInfty (F * ⇑CuspForm.discriminant)) :
    ∀ n ≤ N * (M - 1), (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hFDhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F * ⇑CuspForm.discriminant) := by
    have := mdiff_mul_discPow hFhol 1; rwa [pow_one] at this
  have hFDper : Function.Periodic ((F * ⇑CuspForm.discriminant) ∘ ofComplex) N := by
    have := hFper.mul (periodic_discPow_comp_ofComplex 1 N); rwa [pow_one] at this
  have hFDbd : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant) := hz.isBoundedAtImInfty
  have hc0 : (qExpansion N (F * ⇑CuspForm.discriminant)).coeff 0 = 0 :=
    (isZeroAtImInfty_iff_qExpansion_coeff_zero_eq_zero hN' hFDper hFDhol hFDbd).mp hz
  have hshape : (F * ⇑CuspForm.discriminant ^ M : ℍ → ℂ)
      = (F * ⇑CuspForm.discriminant) * ⇑CuspForm.discriminant ^ (M - 1) := by
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hM]
  intro n hn
  rw [hshape, qExpansion_mul (analyticAt_cuspFunction_zero_of hFDhol hFDper hFDbd)
      (analyticAt_cuspFunction_zero_of (mdiff_discPow (M - 1))
        (periodic_discPow_comp_ofComplex (M - 1) N) (isBoundedAtImInfty_discPow (M - 1))),
    PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rcases lt_or_eq_of_le (show j ≤ N * (M - 1) by omega) with hlt | heq
  · rw [qExpansion_discPow_coeff_eq_zero_of_lt (M - 1) hlt, mul_zero]
  · have : i = 0 := by omega
    rw [this, hc0, zero_mul]

end CuspCriterion

section RatCoeff

open _root_.UpperHalfPlane _root_.ModularForm _root_.SlashInvariantForm _root_.ModularFormClass _root_.CuspForm _root_.ModularForm.CuspForm _root_.EisensteinSeries
open scoped _root_.UpperHalfPlane _root_.ModularForm _root_.SlashInvariantForm _root_.ModularFormClass _root_.CuspForm _root_.ModularForm.CuspForm _root_.EisensteinSeries
open scoped MatrixGroups ArithmeticFunction.sigma

private lemma ratCoeff_mul {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p * q).coeff n = (a : ℂ) := by
  choose F hF using hp
  choose G hG using hq
  intro n
  refine ⟨∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, F ij.1 * G ij.2, ?_⟩
  rw [PowerSeries.coeff_mul]
  push_cast
  exact Finset.sum_congr rfl fun ij _ => by rw [hF, hG]

private lemma ratCoeff_sub {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p - q).coeff n = (a : ℂ) := by
  intro n
  obtain ⟨a, ha⟩ := hp n
  obtain ⟨b, hb⟩ := hq n
  exact ⟨a - b, by rw [map_sub, ha, hb]; push_cast; ring⟩

private lemma ratCoeff_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 (E hk)).coeff n = (q : ℂ) := by
  intro n
  rw [E_qExpansion_coeff hk hk2]
  by_cases hn : n = 0
  · exact ⟨1, by simp [hn]⟩
  · refine ⟨-(2 * k / _root_.bernoulli k) * (σ (k - 1) n : ℚ), ?_⟩
    rw [ite_eq_right hn]
    push_cast
    ring

private lemma ratCoeff_pow {p : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (k : ℕ) :
    ∀ n : ℕ, ∃ a : ℚ, (p ^ k).coeff n = (a : ℂ) := by
  induction k with
  | zero =>
    intro n
    rw [pow_zero]
    by_cases hn : n = 0
    · exact ⟨1, by simp [hn, PowerSeries.coeff_one]⟩
    · exact ⟨0, by simp [PowerSeries.coeff_one, hn]⟩
  | succ k ih =>
    rw [pow_succ]
    exact ratCoeff_mul ih hp

private def eCubeSubESq : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

private lemma eCubeSubESq_qExpansion :
    qExpansion 1 eCubeSubESq = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ -
      qExpansion 1 E₆ * qExpansion 1 E₆ := by
  simp only [eCubeSubESq, FunLike.coe_sub, ModularForm.coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

private lemma discriminant_eq_smul_eCubeSubESq :
    ModularForm.discriminant = (1 / 1728 : ℂ) • eCubeSubESq := by
  ext z
  have h := discriminant_eq_E₄_cube_sub_E₆_sq z
  simp only [Pi.smul_apply, eCubeSubESq, FunLike.coe_sub, Pi.sub_apply,
    ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul]
  rw [h]
  ring

private lemma ratCoeff_discriminant :
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 ModularForm.discriminant).coeff n = (q : ℂ) := by
  have h4 : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 E₄).coeff n = (q : ℂ) :=
    ratCoeff_E (by norm_num) (by decide)
  have h6 : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 E₆).coeff n = (q : ℂ) :=
    ratCoeff_E (by norm_num) (by decide)
  have hmain := ratCoeff_sub (ratCoeff_mul (ratCoeff_mul h4 h4) h4) (ratCoeff_mul h6 h6)
  intro n
  obtain ⟨a, ha⟩ := hmain n
  refine ⟨(1 / 1728 : ℚ) * a, ?_⟩
  rw [discriminant_eq_smul_eCubeSubESq,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, eCubeSubESq_qExpansion, smul_eq_mul, ha]
  push_cast
  ring

end RatCoeff

section KPoleAlgebra

open ModularForm

variable {N : ℕ}

private lemma mem_of_rat (K : IntermediateField ℚ ℂ) {x : ℂ} (h : ∃ q : ℚ, x = (q : ℂ)) : x ∈ K := by
  obtain ⟨q, rfl⟩ := h
  exact SubfieldClass.ratCast_mem K q

private def KPoleAt (K : IntermediateField ℚ ℂ) (N m : ℕ) (f : ℍ → ℂ) : Prop :=
  Function.Periodic ((f * ⇑CuspForm.discriminant ^ m) ∘ ofComplex) N ∧
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m) ∧
    ∀ n : ℕ, (qExpansion N (f * ⇑CuspForm.discriminant ^ m)).coeff n ∈ K

private def KPole (K : IntermediateField ℚ ℂ) (N : ℕ) (f : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ ∃ m : ℕ, KPoleAt K N m f

private lemma qExpansion_discPow_coeff_mem (K : IntermediateField ℚ ℂ) [NeZero N] (k n : ℕ) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff n ∈ K := by
  have hper : Function.Periodic
      ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
    have h := periodic_discPow_comp_ofComplex k 1
    simpa only [Nat.cast_one] using h
  rw [qExpansion_coeff_width _ (NeZero.ne N) hper (mdiff_discPow k)
    (isBoundedAtImInfty_discPow k), qExpansion_one_discPow]
  split
  · exact mem_of_rat K (ratCoeff_pow ratCoeff_discriminant k _)
  · exact zero_mem _

private lemma KPoleAt.pad {K : IntermediateField ℚ ℂ} [NeZero N] {f : ℍ → ℂ} {m m' : ℕ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hm : m ≤ m') (h : KPoleAt K N m f) :
    KPoleAt K N m' f := by
  obtain ⟨hper, hbd, hmem⟩ := h
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  refine ⟨?_, ?_, ?_⟩
  · rw [hshape]
    exact hper.mul (periodic_discPow_comp_ofComplex (m' - m) N)
  · exact IsBoundedAtImInfty.mul_discPow_mono hm hbd
  · intro n
    rw [hshape, qExpansion_mul
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hhol m) hper hbd)
      (analyticAt_cuspFunction_zero_of (mdiff_discPow (m' - m))
        (periodic_discPow_comp_ofComplex (m' - m) N) (isBoundedAtImInfty_discPow (m' - m))),
      PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hmem ij.1) (qExpansion_discPow_coeff_mem K _ ij.2)

private lemma kPole_algebraMap {K : IntermediateField ℚ ℂ} [NeZero N] (c : ↥K) :
    KPole K N (algebraMap ↥K (ℍ → ℂ) c) := by
  have hshape : ((algebraMap ↥K (ℍ → ℂ) c) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      (c : ℂ) • (1 : ℍ → ℂ) := by
    funext τ
    simp only [Pi.mul_apply, pow_zero, mul_one, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul]
    rfl
  have hone_bd : IsBoundedAtImInfty (1 : ℍ → ℂ) := by
    have h1 : (1 : ℍ → ℂ) = fun _ : ℍ => (1 : ℂ) := rfl
    rw [h1]
    exact Filter.const_boundedAtFilter _ _
  refine ⟨mdifferentiable_const, 0, ?_, ?_, ?_⟩
  · rw [hshape]
    intro x
    rfl
  · rw [hshape]
    have hc : ((c : ℂ) • (1 : ℍ → ℂ)) = fun _ : ℍ => (c : ℂ) := by
      funext τ
      simp
    rw [hc]
    exact Filter.const_boundedAtFilter _ _
  · intro n
    have han : AnalyticAt ℂ (cuspFunction N (1 : ℍ → ℂ)) 0 :=
      analyticAt_cuspFunction_zero_of (g := (1 : ℍ → ℂ)) mdifferentiable_const
        (periodic_one_fn N) hone_bd
    rw [hshape, qExpansion_smul han,
      qExpansion_one, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_one]
    split
    · rw [mul_one]
      exact c.2
    · rw [mul_zero]
      exact zero_mem _

private lemma KPole.add {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f + g) := by
  obtain ⟨hf1, m1, hfd⟩ := hf
  obtain ⟨hg1, m2, hgd⟩ := hg
  obtain ⟨hfper, hfbd, hfmem⟩ := hfd.pad hf1 (le_max_left m1 m2)
  obtain ⟨hgper, hgbd, hgmem⟩ := hgd.pad hg1 (le_max_right m1 m2)
  have hshape : ((f + g) * ⇑CuspForm.discriminant ^ max m1 m2 : ℍ → ℂ) =
      f * ⇑CuspForm.discriminant ^ max m1 m2 + g * ⇑CuspForm.discriminant ^ max m1 m2 := by
    funext τ
    simp [add_mul]
  refine ⟨hf1.add hg1, max m1 m2, ?_, ?_, ?_⟩
  · rw [hshape]
    exact hfper.add hgper
  · rw [hshape]
    exact hfbd.add hgbd
  · intro n
    rw [hshape, qExpansion_add
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hf1 _) hfper hfbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg1 _) hgper hgbd),
      map_add]
    exact add_mem (hfmem n) (hgmem n)

private lemma KPole.mul {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f * g) := by
  obtain ⟨hf1, m1, hfper, hfbd, hfmem⟩ := hf
  obtain ⟨hg1, m2, hgper, hgbd, hgmem⟩ := hg
  have hshape : ((f * g) * ⇑CuspForm.discriminant ^ (m1 + m2) : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m1) * (g * ⇑CuspForm.discriminant ^ m2) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  refine ⟨hf1.mul hg1, m1 + m2, ?_, ?_, ?_⟩
  · rw [hshape]
    exact hfper.mul hgper
  · rw [hshape]
    exact hfbd.mul hgbd
  · intro n
    rw [hshape, qExpansion_mul
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hf1 _) hfper hfbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg1 _) hgper hgbd),
      PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hfmem ij.1) (hgmem ij.2)

private lemma kPole_jf (K : IntermediateField ℚ ℂ) [NeZero N] {jf : ℍ → ℂ}
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    KPole K N jf := by
  have hshape : (jf * ⇑CuspForm.discriminant ^ 1 : ℍ → ℂ) = ⇑(ModularForm.E₄.pow 3) := by
    funext τ
    rw [congrFun (ModularForm.coe_pow ModularForm.E₄ 3) τ, Pi.pow_apply]
    simp only [Pi.mul_apply, pow_one, hjf τ]
    rw [congrFun CuspForm.coe_discriminant τ]
    exact div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)
  have hhol3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) :=
    (ModularForm.E₄.pow 3).holo'
  have hbd3 : IsBoundedAtImInfty (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) :=
    ModularFormClass.bdd_at_infty (ModularForm.E₄.pow 3)
  have hper3 : Function.Periodic ((⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E₄.pow 3)
      one_mem_strictPeriods_SL
  have hjmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
    have : jf = fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := funext hjf
    rw [this]
    exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  refine ⟨hjmd, 1, ?_, ?_, ?_⟩
  · rw [hshape]
    simpa using hper3.nat_mul N
  · rw [hshape]
    exact hbd3
  · intro n
    rw [hshape, qExpansion_coeff_width (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) (NeZero.ne N)
      hper3 hhol3 hbd3]
    split
    · have he : qExpansion 1 (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) =
          (qExpansion 1 ModularForm.E₄) ^ 3 :=
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3
      rw [he]
      exact mem_of_rat K (ratCoeff_pow (ratCoeff_E (by norm_num) (by decide)) 3 _)
    · exact zero_mem _

end KPoleAlgebra

section HeadTwo

open ModularForm

variable {N : ℕ}

private lemma analyticOnNhd_comp_ofComplex {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet

private theorem mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero {f g : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hfg : f * g = 0) : f = 0 ∨ g = 0 := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf hg
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have key := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (hf.analyticOnNhd hU)
    (hg.analyticOnNhd hU) (fun z hz ↦ by
      have := congrFun hfg (ofComplex z)
      simpa using this) (convex_halfSpace_im_gt 0).isPreconnected
  rcases key with k | k
  · left; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos
  · right; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos

private lemma jf_smul {jf : ℍ → ℂ}
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ) : jf (γ • τ) = jf τ := by
  have hγ : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  rw [CuspForm.coe_discriminant] at hΔ
  rw [show (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ = γ • τ from rfl] at h4 hΔ
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  rw [hjf, hjf, h4, hΔ, zpow_ofNat, zpow_ofNat]
  field_simp

private lemma map_castRingHom_eq_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem'] at hγ
  rw [hγ, Matrix.SpecialLinearGroup.coe_one]

private def precompSmul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (ℍ → ℂ) →ₐ[ℂ] (ℍ → ℂ) where
  toFun f := f ∘ (γ • ·)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private lemma KPole.pow {K : IntermediateField ℚ ℂ} [NeZero N] {g : ℍ → ℂ}
    (hg : KPole K N g) (e : ℕ) : KPole K N (g ^ e) := by
  induction e with
  | zero =>
    have h1 : (g ^ 0 : ℍ → ℂ) = algebraMap ↥K (ℍ → ℂ) 1 := by
      funext τ; simp
    rw [h1]
    exact kPole_algebraMap 1
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul hg

private lemma KPole.finsetSum {K : IntermediateField ℚ ℂ} [NeZero N] {ι : Type*}
    (s : Finset ι) {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, KPole K N (f i)) :
    KPole K N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    have h0 : (0 : ℍ → ℂ) = algebraMap ↥K (ℍ → ℂ) 0 := by funext τ; simp
    rw [h0]
    exact kPole_algebraMap 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma KPole.finsetProd {K : IntermediateField ℚ ℂ} [NeZero N] {ι : Type*}
    (s : Finset ι) {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, KPole K N (f i)) :
    KPole K N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have h1 : (1 : ℍ → ℂ) = algebraMap ↥K (ℍ → ℂ) 1 := by funext τ; simp
    rw [h1]
    exact kPole_algebraMap 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma kPole_polyEval {K : IntermediateField ℚ ℂ} [NeZero N] {g : ℍ → ℂ}
    (hg : KPole K N g) {P : Polynomial ℂ} (hP : ∀ n, P.coeff n ∈ K) :
    KPole K N (fun τ => P.eval (g τ)) := by
  classical
  have hfun : (fun τ => P.eval (g τ)) =
      ∑ e ∈ P.support, (fun τ => P.coeff e * g τ ^ e) := by
    funext τ
    rw [Finset.sum_apply, Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [hfun]
  refine KPole.finsetSum _ fun e _ => ?_
  have hconst : KPole K N (algebraMap ↥K (ℍ → ℂ) ⟨P.coeff e, hP e⟩) := kPole_algebraMap _
  have := hconst.mul (hg.pow e)
  have hshape : algebraMap ↥K (ℍ → ℂ) ⟨P.coeff e, hP e⟩ * g ^ e =
      fun τ => P.coeff e * g τ ^ e := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rfl
  rwa [hshape] at this

private lemma kPole_aeval {K : IntermediateField ℚ ℂ} [NeZero N] {σ : Type*}
    {gen : σ → ℍ → ℂ} (hgen : ∀ i, KPole K N (gen i))
    {P : MvPolynomial σ ℂ} (hP : ∀ m, P.coeff m ∈ K) :
    KPole K N (MvPolynomial.aeval gen P) := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine KPole.finsetSum _ fun d _ => ?_
  have hconst : KPole K N ((algebraMap ℂ (ℍ → ℂ)) (P.coeff d)) := by
    have h1 : (algebraMap ℂ (ℍ → ℂ)) (P.coeff d) =
        algebraMap ↥K (ℍ → ℂ) ⟨P.coeff d, hP d⟩ := rfl
    rw [h1]
    exact kPole_algebraMap _
  exact hconst.mul (KPole.finsetProd _ fun i _ => (hgen i).pow (d i))

private theorem exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction_of_deps
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (hR2 : ∀ v : Fin 2 → ZMod N, v ≠ 0 → ∃ m : ℕ,
      Function.Periodic ((fricke v * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (fricke v * ModularForm.discriminant ^ m)).coeff n ∈ K)
    (hR4a : ∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v))
    (hR4c : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ)
    {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ)
    (hPK : ∀ m, P.coeff m ∈ K) (hQK : ∀ m, Q.coeff m ∈ K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) Q ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) Q =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) P)
    (hint : ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0) :
    ∃ m : ℕ, Function.Periodic ((G * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (G * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n ∈ K := by
  classical
  have _hL := hL
  have _hW := hW
  have _hfricke := hfricke
  have _hK := hK

  rw [show (ModularForm.discriminant : ℍ → ℂ) = ⇑CuspForm.discriminant from
    CuspForm.coe_discriminant.symm]
  simp only [show (ModularForm.discriminant : ℍ → ℂ) = ⇑CuspForm.discriminant from
    CuspForm.coe_discriminant.symm] at hR2
  set gen : Option {v : Fin 2 → ZMod N // v ≠ 0} → ℍ → ℂ :=
    fun o => o.elim jf fun v => fricke v.1 with hgen_def

  have hgenKP : ∀ o, KPole K N (gen o) := by
    intro o
    cases o with
    | none => exact kPole_jf K hjf
    | some v =>
      obtain ⟨m, hper, hbd, hmem⟩ := hR2 v.1 v.2
      exact ⟨hR4a v.1 v.2, m, hper, hbd, hmem⟩

  set Ptil : ℍ → ℂ := MvPolynomial.aeval gen P with hPtil_def
  set Qtil : ℍ → ℂ := MvPolynomial.aeval gen Q with hQtil_def
  have hPKP : KPole K N Ptil := kPole_aeval hgenKP hPK
  have hQKP : KPole K N Qtil := kPole_aeval hgenKP hQK
  obtain ⟨hPmd, mP, hPat⟩ := hPKP
  obtain ⟨hQmd, mQ, hQat⟩ := hQKP

  have hgen_inv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ o, gen o ∘ (γ • ·) = gen o := by
    intro γ hγ o
    cases o with
    | none =>
      funext τ
      exact jf_smul hjf γ τ
    | some v =>
      funext τ
      show fricke v.1 (γ • τ) = fricke v.1 τ
      rw [hR4c v.1 γ τ, map_castRingHom_eq_one hγ, Matrix.vecMul_one]
  have haeval_inv : ∀ γ ∈ CongruenceSubgroup.Gamma N,
      ∀ R : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ,
        MvPolynomial.aeval gen R ∘ (γ • ·) = MvPolynomial.aeval gen R := by
    intro γ hγ R
    have h1 : MvPolynomial.aeval gen R ∘ (γ • ·) = precompSmul γ (MvPolynomial.aeval gen R) := rfl
    rw [h1, MvPolynomial.comp_aeval_apply]
    have hfam : (fun i => precompSmul γ (gen i)) = gen :=
      funext fun o => hgen_inv γ hγ o
    rw [hfam]
  have hGinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, G ∘ (γ • ·) = G := by
    intro γ hγ
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G ∘ (γ • ·) - G) := by
      refine MDifferentiable.sub ?_ hG
      have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G ∣[(0 : ℤ)] γ) := hG.slash 0 _
      have h2 : G ∣[(0 : ℤ)] γ = G ∘ (γ • ·) := by
        funext τ
        simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
        rfl
      rwa [h2] at h1
    have hprod : (G ∘ (γ • ·) - G) * Qtil = 0 := by
      funext τ
      have h1 : G (γ • τ) * Qtil (γ • τ) = Ptil (γ • τ) := congrFun hGQ (γ • τ)
      have h2 : G τ * Qtil τ = Ptil τ := congrFun hGQ τ
      have hQγ : Qtil (γ • τ) = Qtil τ := congrFun (haeval_inv γ hγ Q) τ
      have hPγ : Ptil (γ • τ) = Ptil τ := congrFun (haeval_inv γ hγ P) τ
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, Function.comp_apply]
      rw [sub_mul, h2]
      rw [show G (γ • τ) * Qtil τ = G (γ • τ) * Qtil (γ • τ) by rw [hQγ], h1, hPγ, sub_self]
    rcases mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero hdiff hQmd hprod with h | h
    · funext τ
      have := congrFun h τ
      simpa [sub_eq_zero] using this
    · exact absurd h hQ0

  have hGper : Function.Periodic (G ∘ ofComplex) N := by
    have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
      have := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma N N (dvd_refl _)
      rwa [Int.natAbs_natCast] at this
    intro w
    by_cases hw : 0 < Complex.im w
    · have hw' : 0 < Complex.im (w + N) := by simpa using hw
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw',
        ofComplex_apply_of_im_pos hw]
      have := congrFun (hGinv _ hT) ⟨w, hw⟩
      simp only [Function.comp_apply] at this
      rw [UpperHalfPlane.modular_T_zpow_smul] at this
      rw [← this]
      congr 1
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.coe_vadd, add_comm]
    · have hw0 : Complex.im w ≤ 0 := not_lt.mp hw
      have hw' : Complex.im (w + N) ≤ 0 := by simpa using hw0
      simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw',
        ofComplex_apply_of_im_nonpos hw0]

  obtain ⟨d, p, hpK, hprel⟩ := hint
  have hcKP : ∀ i : Fin d, KPole K N (fun τ => (p i).eval (jf τ)) := fun i =>
    kPole_polyEval (kPole_jf K hjf) (hpK i)
  choose mc hmc using fun i : Fin d => (hcKP i).2
  set M₀ : ℕ := 1 + Finset.univ.sup mc with hM₀_def
  have hbdG : IsBoundedAtImInfty (G * ⇑CuspForm.discriminant ^ M₀) := by
    refine isBoundedAtImInfty_of_monicRel
      (c := fun n => if hn : n < d then
        (fun τ => (p ⟨n, hn⟩).eval (jf τ)) * ⇑CuspForm.discriminant ^ (M₀ * (d - n)) else 0)
      (d := d) ?_ ?_
    · intro n hn
      simp only [dite_eq_left hn]
      have h1 : IsBoundedAtImInfty ((fun τ => (p ⟨n, hn⟩).eval (jf τ)) *
          ⇑CuspForm.discriminant ^ mc ⟨n, hn⟩) := (hmc ⟨n, hn⟩).2.1
      refine IsBoundedAtImInfty.mul_discPow_mono ?_ h1
      calc mc ⟨n, hn⟩ ≤ Finset.univ.sup mc := Finset.le_sup (Finset.mem_univ _)
        _ ≤ M₀ * 1 := by omega
        _ ≤ M₀ * (d - n) := by
            have : 1 ≤ d - n := by omega
            exact Nat.mul_le_mul_left M₀ this
    · intro τ
      have h0 := hprel τ
      have hΔ : CuspForm.discriminant τ ≠ 0 := by
        rw [congrFun CuspForm.coe_discriminant τ]
        exact ModularForm.discriminant_ne_zero τ
      have hkey : (G τ * CuspForm.discriminant τ ^ M₀) ^ d
          + ∑ n ∈ Finset.range d, ((if hn : n < d then
              ((fun τ' => (p ⟨n, hn⟩).eval (jf τ')) * ⇑CuspForm.discriminant ^ (M₀ * (d - n)))
            else 0) τ) * (G τ * CuspForm.discriminant τ ^ M₀) ^ n
          = CuspForm.discriminant τ ^ (M₀ * d) *
            (G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ)) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · rw [mul_pow, ← pow_mul]
          ring
        · rw [← Fin.sum_univ_eq_sum_range (fun n => ((if hn : n < d then
              ((fun τ' => (p ⟨n, hn⟩).eval (jf τ')) *
                ⇑CuspForm.discriminant ^ (M₀ * (d - n)))
            else 0) τ) * (G τ * CuspForm.discriminant τ ^ M₀) ^ n) d]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dite_eq_left i.isLt]
          simp only [Pi.mul_apply, Pi.pow_apply]
          rw [mul_pow, ← pow_mul]
          have hexp : M₀ * (d - (i : ℕ)) + M₀ * (i : ℕ) = M₀ * d := by
            rw [← Nat.mul_add, Nat.sub_add_cancel i.isLt.le]
          calc (p i).eval (jf τ) * CuspForm.discriminant τ ^ (M₀ * (d - (i : ℕ))) *
                (G τ ^ (i : ℕ) * CuspForm.discriminant τ ^ (M₀ * (i : ℕ)))
              = CuspForm.discriminant τ ^ (M₀ * (d - (i : ℕ)) + M₀ * (i : ℕ)) *
                ((p i).eval (jf τ) * G τ ^ (i : ℕ)) := by ring
            _ = CuspForm.discriminant τ ^ (M₀ * d) *
                ((p i).eval (jf τ) * G τ ^ (i : ℕ)) := by rw [hexp]
      simp only [Pi.mul_apply, Pi.pow_apply]
      rw [hkey, h0, mul_zero]

  set M : ℕ := M₀ + mP with hM_def
  have hbdGM : IsBoundedAtImInfty (G * ⇑CuspForm.discriminant ^ M) :=
    IsBoundedAtImInfty.mul_discPow_mono (by omega) hbdG
  have hperGM : Function.Periodic ((G * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N :=
    hGper.mul (periodic_discPow_comp_ofComplex M N)
  refine ⟨M, hperGM, hbdGM, ?_⟩

  have hPat' : ∀ n : ℕ, (qExpansion N (Ptil * ⇑CuspForm.discriminant ^ (mQ + M))).coeff n ∈ K :=
    (hPat.pad hPmd (by omega)).2.2
  obtain ⟨hQper, hQbd, hQmem⟩ := hQat
  have hprod : (Qtil * ⇑CuspForm.discriminant ^ mQ) * (G * ⇑CuspForm.discriminant ^ M)
      = Ptil * ⇑CuspForm.discriminant ^ (mQ + M) := by
    funext τ
    have h2 : G τ * Qtil τ = Ptil τ := congrFun hGQ τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    calc Qtil τ * CuspForm.discriminant τ ^ mQ * (G τ * CuspForm.discriminant τ ^ M)
        = G τ * Qtil τ * (CuspForm.discriminant τ ^ mQ * CuspForm.discriminant τ ^ M) := by ring
      _ = Ptil τ * (CuspForm.discriminant τ ^ mQ * CuspForm.discriminant τ ^ M) := by rw [h2]
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hqmul : qExpansion N (Qtil * ⇑CuspForm.discriminant ^ mQ) *
      qExpansion N (G * ⇑CuspForm.discriminant ^ M)
        = qExpansion N (Ptil * ⇑CuspForm.discriminant ^ (mQ + M)) := by
    rw [← qExpansion_mul (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hQmd mQ)
        hQper hQbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hG M) hperGM hbdGM), hprod]
  have hg_ne : qExpansion N (Qtil * ⇑CuspForm.discriminant ^ mQ) ≠ 0 := by
    rw [ne_eq, qExpansion_eq_zero_iff hN' hQper (mdiff_mul_discPow hQmd mQ) hQbd]
    intro h0
    refine hQ0 ?_
    funext τ
    have hτ := congrFun h0 τ
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at hτ
    have hΔ : CuspForm.discriminant τ ≠ 0 := by
      rw [congrFun CuspForm.coe_discriminant τ]
      exact ModularForm.discriminant_ne_zero τ
    exact (mul_eq_zero.mp hτ).resolve_right (pow_ne_zero mQ hΔ)
  exact fun n ↦ powerSeries_coeff_mem_of_mul_eq' K.toSubfield hqmul hg_ne
    (fun n' ↦ hQmem n') (fun n' ↦ hPat' n') n

end HeadTwo

end WLight

open _root_.WLight WLight in
theorem _root_.WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ)
    (hPK : ∀ m, P.coeff m ∈ K) (hQK : ∀ m, Q.coeff m ∈ K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) Q ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) Q =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) P)
    (hint : ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0) :
    ∃ m : ℕ, Function.Periodic ((G * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (G * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n ∈ K := by
  subst hK
  have hfeq : fricke = fun a τ => -(ModularForm.E₄ τ * ModularForm.E₆ τ /
      ModularForm.discriminant τ) / 2592 *
    (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ)
        ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ))) := by
    funext v τ; rw [hfricke v τ, hW v τ]
  obtain ⟨h1, _h2, h3, h4, h5, _h6, _h7, h8⟩ :=
    WLight.frickeFunction_modularity_package N L hL
  have _h8 := h8
  refine WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction_of_deps
    N L hL W hW fricke hfricke jf hjf _ rfl ?_ ?_ ?_ hG P Q hPK hQK hQ0 hGQ hint
  ·
    intro v hv
    refine ⟨1, ?_, ?_, ?_⟩ <;> rw [pow_one, hfeq]
    · exact (h5 v hv).1
    · exact h4 v hv
    · exact (h5 v hv).2
  ·
    rw [hfeq]; exact h3
  ·
    rw [hfeq]; exact fun v γ τ => h1 v γ τ

end
end WLightS9.S_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction


namespace WLightS9.S_WLight_exists_levelFraction_of_stable_family

set_option autoImplicit false
noncomputable section
open Complex Real
namespace WLight
open _root_.WLight
open _root_.WLight
open scoped _root_.WLight

section Floor
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm
open _root_.PeriodPair _root_.ModularForm _root_.CuspForm _root_.ModularForm.CuspForm
open scoped _root_.PeriodPair _root_.ModularForm _root_.CuspForm _root_.ModularForm.CuspForm
open UpperHalfPlane hiding I

private def j : ℍ → ℂ := fun z => E₄ z ^ 3 / ModularForm.discriminant z

private theorem j_surjective : Function.Surjective j :=
  levelOne_hauptmodul_package.2.2.1

private def periodPairOfTau (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := LinearIndependent.pair_iff.mpr fun s t hst ↦ by
    have him : s * (τ : ℂ).im = 0 := by
      have := congrArg Complex.im hst
      simpa [Complex.add_im, Complex.smul_im, smul_eq_mul] using this
    have hs : s = 0 :=
      (mul_eq_zero.mp him).resolve_right (UpperHalfPlane.coe_im τ ▸ τ.im_ne_zero)
    subst hs
    simpa using hst

@[scoped simp] private lemma periodPairOfTau_ω₁ (τ : ℍ) : (periodPairOfTau τ).ω₁ = (τ : ℂ) := rfl
@[scoped simp] private lemma periodPairOfTau_ω₂ (τ : ℍ) : (periodPairOfTau τ).ω₂ = 1 := rfl

private def wpTorsion (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ :=
  PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N)

private def wpNorm (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ := ((2 * π * I) ^ 2)⁻¹ * wpTorsion N a₁ a₂ τ

section B6_fixedFrac

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G A]

private lemma smul_prod_smul_eq (v : A) (g₀ : G) : g₀ • (∏ g : G, g • v) = ∏ g : G, g • v := by
  rw [show g₀ • (∏ g : G, g • v) = MulSemiringAction.toRingHom G A g₀ (∏ g : G, g • v) from rfl,
    map_prod]
  simp only [MulSemiringAction.toRingHom_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g₀) _ _ fun g ↦ rfl

variable [IsDomain A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  [MulSemiringAction G K]

private theorem exists_fixed_div_of_fixed
    (hcompat : ∀ (g : G) (a : A), g • algebraMap A K a = algebraMap A K (g • a))
    (x : K) (hx : ∀ g : G, g • x = x) :
    ∃ a b : A, (∀ g : G, g • a = a) ∧ (∀ g : G, g • b = b) ∧ algebraMap A K b ≠ 0 ∧
      x * algebraMap A K b = algebraMap A K a := by
  classical
  obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  set b : A := ∏ g : G, g • v with hb
  set a : A := u * ∏ g ∈ (Finset.univ : Finset G).erase 1, g • v with ha
  have hbfix : ∀ g : G, g • b = b := fun g ↦ smul_prod_smul_eq v g
  have hb0 : algebraMap A K b ≠ 0 := by
    rw [map_ne_zero_iff _ hinj, hb]
    exact Finset.prod_ne_zero_iff.mpr fun g _ ↦ (smul_ne_zero_iff_ne g).mpr hv0
  have hxb : algebraMap A K u / algebraMap A K v * algebraMap A K b = algebraMap A K a := by
    have hv0' : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv0
    rw [hb, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : G)), one_smul, ha, map_mul,
      map_mul]
    field_simp
  refine ⟨a, b, fun g ↦ ?_, hbfix, hb0, hxb⟩
  apply hinj
  rw [← hcompat, ← hxb, smul_mul', hx, hcompat, hbfix]

end B6_fixedFrac

private def denomZ (γ : SL(2, ℤ)) (τ : ℂ) : ℂ := (γ 1 0 : ℤ) * τ + (γ 1 1 : ℤ)

private lemma denomZ_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : denomZ γ (τ : ℂ) ≠ 0 := by
  intro h
  have him : ((γ 1 0 : ℤ) : ℝ) * (τ : ℂ).im = 0 := by
    have := congrArg Complex.im h
    simp only [denomZ, Complex.add_im, Complex.mul_im, Complex.intCast_im, zero_mul,
      Complex.intCast_re, add_zero, Complex.zero_im] at this
    linarith
  have hc0 : (γ 1 0 : ℤ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact_mod_cast h
    · exact absurd h (UpperHalfPlane.coe_im τ ▸ τ.im_ne_zero)
  have hd0 : (γ 1 1 : ℤ) = 0 := by
    have := h
    rw [denomZ, hc0] at this
    simpa using this
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rwa [Matrix.det_fin_two] at this
  rw [hc0, hd0] at hdet
  simp at hdet

private def vecMulSL (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : Fin 2 → ZMod N :=
  Matrix.vecMul a ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))

private lemma vecMulSL_apply (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (j : Fin 2) :
    vecMulSL N a γ j = a 0 * (γ 0 j : ℤ) + a 1 * (γ 1 j : ℤ) := by
  simp [vecMulSL, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]

section B3_spelling2

open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open Matrix.SpecialLinearGroup

private lemma denom_mapGL_eq_denomZ (γ : SL(2, ℤ)) (τ : ℍ) :
    denom (mapGL ℝ γ) τ = denomZ γ τ := by
  simp [denom, denomZ]

private def wpNormZ (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ := wpNorm N (a 0).val (a 1).val τ

private def frickeF (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * wpNormZ N a τ

private theorem r4a_package (N : ℕ) [NeZero N] :

    (∀ (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ), (frickeF N) a (γ • τ) =
        (frickeF N) (Matrix.vecMul a ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))) τ) ∧

    (∀ a : Fin 2 → ZMod N, (frickeF N) (-a) = (frickeF N) a) ∧

    (∀ a : Fin 2 → ZMod N, a ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((frickeF N) a)) ∧

    (∀ a : Fin 2 → ZMod N, a ≠ 0 →
      IsBoundedAtImInfty ((frickeF N) a * ModularForm.discriminant)) ∧

    (∀ a : Fin 2 → ZMod N, a ≠ 0 →
      Function.Periodic (((frickeF N) a * ModularForm.discriminant) ∘ ofComplex) N ∧
      ∀ n : ℕ, (qExpansion N ((frickeF N) a * ModularForm.discriminant)).coeff n ∈
        IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}) ∧

    (∀ a b : Fin 2 → ZMod N, a ≠ 0 → b ≠ 0 → (frickeF N) a = (frickeF N) b → b = a ∨ b = -a) ∧

    (∀ a : Fin 2 → ZMod N, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ,
      (frickeF N) a (γ • τ) = (frickeF N) a τ) ∧

    (∀ s : ℕ, s.Coprime N →
      ∀ φ : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}) →+* ℂ,
        (∀ z : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}),
            (z : ℂ) = cexp (2 * π * I / N) → φ z = cexp (2 * π * I / N) ^ s) →
        ∀ a : Fin 2 → ZMod N, a ≠ 0 →
          ∀ (n : ℕ) (z : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)})),
            (z : ℂ) = (qExpansion N ((frickeF N) a * ModularForm.discriminant)).coeff n →
            (qExpansion N ((frickeF N) ![a 0, (s : ZMod N) * a 1] * ModularForm.discriminant)).coeff n = φ z) :=
  frickeFunction_modularity_package N periodPairOfTau fun _ ↦ ⟨rfl, rfl⟩

private theorem r4b_package (N : ℕ) [NeZero N] :

    (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j ∧
      ∃ m : ℕ, IsBoundedAtImInfty (j * ModularForm.discriminant ^ m)) ∧

    (∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((frickeF N) v) ∧
      ∃ m : ℕ, IsBoundedAtImInfty ((frickeF N) v * ModularForm.discriminant ^ m)) ∧

    (∃ P : ℕ → Polynomial ℂ,
      (∀ k i, (P k).coeff i ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N)}) ∧
      ∀ v : Fin 2 → ZMod N, v ≠ 0 → ∀ τ : ℍ,
        (frickeF N) v τ ^ (N ^ 2 - 1) + ∑ k ∈ Finset.range (N ^ 2 - 1),
          (P k).eval (j τ) * (frickeF N) v τ ^ k = 0) :=
  frickeFunction_orbit_package N periodPairOfTau (fun _ ↦ ⟨rfl, rfl⟩) (wpNormZ N) (fun _ _ ↦ rfl)
    (frickeF N) (fun _ _ ↦ rfl) j fun _ ↦ rfl

private theorem frickeF_slash {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    frickeF N a (γ • τ) = frickeF N (vecMulSL N a γ) τ :=
  (r4a_package N).1 a γ τ

private theorem frickeF_invariant_Gamma {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) : frickeF N a (γ • τ) = frickeF N a τ :=
  (r4a_package N).2.2.2.2.2.2.1 a γ hγ τ

private lemma vecMulSL_mul (N : ℕ) (a : Fin 2 → ZMod N) (γ δ : SL(2, ℤ)) :
    vecMulSL N a (γ * δ) = vecMulSL N (vecMulSL N a γ) δ := by
  have hmap : ((γ * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) *
        (δ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact Matrix.map_mul (f := Int.castRingHom (ZMod N))
  simp only [vecMulSL, hmap, Matrix.vecMul_vecMul]

private lemma vecMulSL_one (N : ℕ) (a : Fin 2 → ZMod N) : vecMulSL N a 1 = a := by
  simp [vecMulSL]

private lemma vecMulSL_zero (N : ℕ) (γ : SL(2, ℤ)) : vecMulSL N 0 γ = 0 := by
  funext j; simp [vecMulSL_apply]

private lemma vecMulSL_ne_zero {N : ℕ} {a : Fin 2 → ZMod N} (ha : a ≠ 0) (γ : SL(2, ℤ)) :
    vecMulSL N a γ ≠ 0 := by
  intro h
  apply ha
  have := congrArg (fun b ↦ vecMulSL N b γ⁻¹) h
  simpa [← vecMulSL_mul, vecMulSL_one, vecMulSL_zero] using this

private abbrev FrickeIdx (N : ℕ) : Type := {a : Fin 2 → ZMod N // a ≠ 0}

scoped instance (N : ℕ) [NeZero N] : Fintype (FrickeIdx N) := by unfold FrickeIdx; infer_instance

private theorem mdifferentiable_frickeF {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (frickeF N i.1) :=
  (r4a_package N).2.2.1 i.1 i.2

private theorem frickeF_eq_imp {N : ℕ} [NeZero N] (a b : FrickeIdx N)
    (h : frickeF N a.1 = frickeF N b.1) : b.1 = a.1 ∨ b.1 = -a.1 :=
  (r4a_package N).2.2.2.2.2.1 a.1 b.1 a.2 b.2 h

private theorem mem_Gamma_or_neg_mem_of_vecMulSL {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (h : ∀ a : Fin 2 → ZMod N, a ≠ 0 → vecMulSL N a γ = a ∨ vecMulSL N a γ = -a) :
    γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N := by

  rcases Nat.lt_or_ge 1 N with hN | hN
  · haveI : Fact (1 < N) := ⟨hN⟩
    have h10 : (1 : ZMod N) ≠ 0 := one_ne_zero
    have r1 := h ![1, 0] (fun e ↦ h10 (by simpa using congrFun e 0))
    have r2 := h ![0, 1] (fun e ↦ h10 (by simpa using congrFun e 1))
    have r3 := h ![1, 1] (fun e ↦ h10 (by simpa using congrFun e 0))
    simp only [funext_iff, Fin.forall_fin_two, vecMulSL_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero, zero_add,
      Pi.neg_apply, neg_zero] at r1 r2 r3
    have e01 : ((γ 0 1 : ℤ) : ZMod N) = 0 := by rcases r1 with ⟨_, e⟩ | ⟨_, e⟩ <;> exact e
    have e10 : ((γ 1 0 : ℤ) : ZMod N) = 0 := by rcases r2 with ⟨e, _⟩ | ⟨e, _⟩ <;> exact e
    have e0011 : ((γ 0 0 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) := by
      rcases r3 with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
        (rw [e10, add_zero] at c1; rw [e01, zero_add] at c2; rw [c1, c2])
    rw [CongruenceSubgroup.Gamma_mem, CongruenceSubgroup.Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero]
    rcases r1 with ⟨a1, _⟩ | ⟨a1, _⟩
    · left; exact ⟨a1, e01, e10, by rw [← e0011]; exact a1⟩
    · right; exact ⟨by rw [a1, neg_neg], e01, e10, by rw [← e0011, a1, neg_neg]⟩
  · have : N = 1 := by have := NeZero.ne N; omega
    subst this
    left
    simp [CongruenceSubgroup.Gamma_one_top]

private theorem frickeF_faithful {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (h : ∀ i : FrickeIdx N, ∀ τ : ℍ, frickeF N i.1 (γ • τ) = frickeF N i.1 τ) :
    γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N := by
  refine mem_Gamma_or_neg_mem_of_vecMulSL γ fun a ha ↦ ?_
  have hfun : frickeF N a = frickeF N (vecMulSL N a γ) := by
    funext τ; rw [← frickeF_slash, h ⟨a, ha⟩ τ]
  rcases frickeF_eq_imp ⟨a, ha⟩ ⟨vecMulSL N a γ, vecMulSL_ne_zero ha γ⟩ hfun with e | e
  · exact Or.inl e
  · exact Or.inr e

end B3_spelling2

section B6Instance

open _root_.UpperHalfPlane _root_.ModularForm _root_.CuspForm _root_.ModularForm.CuspForm _root_.Polynomial _root_.Real.Polynomial
open scoped _root_.UpperHalfPlane _root_.ModularForm _root_.CuspForm _root_.ModularForm.CuspForm _root_.Polynomial _root_.Real.Polynomial
open scoped MatrixGroups Manifold

private theorem frickeF_integral_over_j (N : ℕ) [NeZero N] :
    ∃ P : ℕ → Polynomial ℂ,
      ∀ (i : FrickeIdx N) (τ : ℍ),
        frickeF N i.1 τ ^ (N ^ 2 - 1) +
          ∑ k ∈ Finset.range (N ^ 2 - 1),
            Polynomial.eval (j τ) (P k) * frickeF N i.1 τ ^ k = 0 := by
  obtain ⟨P, -, hP⟩ := (r4b_package N).2.2
  exact ⟨P, fun i τ => hP i.1 i.2 τ⟩

end B6Instance

section B6Ring

open _root_.UpperHalfPlane _root_.ModularForm _root_.SlashInvariantForm _root_.ModularFormClass _root_.CuspForm _root_.ModularForm.CuspForm _root_.Polynomial _root_.Real.Polynomial _root_.Filter
open scoped _root_.UpperHalfPlane _root_.ModularForm _root_.SlashInvariantForm _root_.ModularFormClass _root_.CuspForm _root_.ModularForm.CuspForm _root_.Polynomial _root_.Real.Polynomial _root_.Filter
open scoped MatrixGroups Manifold

private def PoleBounded (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ ∃ m : ℕ, IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)

private lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

private lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

private lemma IsBoundedAtImInfty.mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
    (h : IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)) :
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m') := by
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hshape]
  exact h.mul (isBoundedAtImInfty_discPow (m' - m))

private lemma poleBounded_algebraMap (r : ℂ) : PoleBounded (algebraMap ℂ (ℍ → ℂ) r) := by
  refine ⟨mdifferentiable_const, 0, ?_⟩
  have hshape : ((algebraMap ℂ (ℍ → ℂ) r) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      fun _ => r := by
    funext τ
    simp
  rw [hshape]
  exact const_boundedAtFilter _ r

private lemma PoleBounded.add {f g : ℍ → ℂ} (hf : PoleBounded f) (hg : PoleBounded g) :
    PoleBounded (f + g) := by
  obtain ⟨hf1, m1, hf2⟩ := hf
  obtain ⟨hg1, m2, hg2⟩ := hg
  refine ⟨hf1.add hg1, max m1 m2, ?_⟩
  have hshape : ((f + g) * ⇑CuspForm.discriminant ^ max m1 m2 : ℍ → ℂ) =
      f * ⇑CuspForm.discriminant ^ max m1 m2 + g * ⇑CuspForm.discriminant ^ max m1 m2 := by
    funext τ
    simp [add_mul]
  rw [hshape]
  exact (IsBoundedAtImInfty.mul_discPow_mono (le_max_left _ _) hf2).add
    (IsBoundedAtImInfty.mul_discPow_mono (le_max_right _ _) hg2)

private lemma PoleBounded.mul {f g : ℍ → ℂ} (hf : PoleBounded f) (hg : PoleBounded g) :
    PoleBounded (f * g) := by
  obtain ⟨hf1, m1, hf2⟩ := hf
  obtain ⟨hg1, m2, hg2⟩ := hg
  refine ⟨hf1.mul hg1, m1 + m2, ?_⟩
  have hshape : ((f * g) * ⇑CuspForm.discriminant ^ (m1 + m2) : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m1) * (g * ⇑CuspForm.discriminant ^ m2) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  rw [hshape]
  exact hf2.mul hg2

private theorem poleBounded_of_mem_adjoin {S : Set (ℍ → ℂ)} (hS : ∀ f ∈ S, PoleBounded f)
    {a : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ S) : PoleBounded a := by
  induction ha using Algebra.adjoin_induction with
  | mem f hf => exact hS f hf
  | algebraMap r => exact poleBounded_algebraMap r
  | add x y hx hy ihx ihy => exact ihx.add ihy
  | mul x y hx hy ihx ihy => exact ihx.mul ihy

private lemma poleBounded_j : PoleBounded j := by
  rw [PoleBounded, CuspForm.coe_discriminant]
  exact (r4b_package 1).1

private lemma poleBounded_frickeF {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    PoleBounded (frickeF N i.1) := by
  rw [PoleBounded, CuspForm.coe_discriminant]
  exact (r4b_package N).2.1 i.1 i.2

private theorem eq_polynomial_j_of_invariant_of_mem_adjoin {S : Set (ℍ → ℂ)}
    (hS : ∀ f ∈ S, PoleBounded f) {a : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ S)
    (hinv : ∀ γ : SL(2, ℤ), a ∣[(0 : ℤ)] γ = a) :
    ∃ P : Polynomial ℂ, a = fun τ => Polynomial.eval (j τ) P := by
  obtain ⟨hhol, m, hbd⟩ := poleBounded_of_mem_adjoin hS ha
  rw [CuspForm.coe_discriminant] at hbd
  obtain ⟨P, -, hP⟩ := levelOne_hauptmodul_package.1 m a hhol hinv hbd
  exact ⟨P, hP⟩

end B6Ring

end Floor

section B5_carrier

open scoped UpperHalfPlane Manifold MatrixGroups ModularForm
open UpperHalfPlane hiding I

scoped instance slFnAction : MulSemiringAction SL(2, ℤ) (ℍ → ℂ) where
  smul γ f := fun τ ↦ f (γ⁻¹ • τ)
  one_smul f := by funext τ; show f ((1 : SL(2, ℤ))⁻¹ • τ) = f τ; rw [inv_one, one_smul]
  mul_smul γ δ f := by
    funext τ
    show f ((γ * δ)⁻¹ • τ) = f (δ⁻¹ • (γ⁻¹ • τ))
    rw [mul_inv_rev, mul_smul]
  smul_zero γ := rfl
  smul_add γ f g := rfl
  smul_one γ := rfl
  smul_mul γ f g := rfl

private lemma sl_smul_apply (γ : SL(2, ℤ)) (f : ℍ → ℂ) (τ : ℍ) : (γ • f) τ = f (γ⁻¹ • τ) := rfl

scoped instance slFn_smulCommClass : SMulCommClass SL(2, ℤ) ℂ (ℍ → ℂ) where
  smul_comm _ _ _ := rfl

private lemma sl_smul_eq_self_iff (f : ℍ → ℂ) :
    (∀ γ : SL(2, ℤ), γ • f = f) ↔ ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ := by
  constructor
  · intro h γ τ
    have := congrFun (h γ⁻¹) τ
    rwa [sl_smul_apply, inv_inv] at this
  · intro h γ
    funext τ
    rw [sl_smul_apply, h]

private def HolFn : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {f | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f}
  mul_mem' hf hg := hf.mul hg
  add_mem' hf hg := hf.add hg
  algebraMap_mem' c := by
    show MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun _ : ℍ ↦ c)
    exact mdifferentiable_const

private lemma mem_HolFn {f : ℍ → ℂ} : f ∈ HolFn ↔ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := Iff.rfl

private theorem HolFn.eq_zero_or_eq_zero_of_mul_eq_zero {f g : ℍ → ℂ} (hf : f ∈ HolFn) (hg : g ∈ HolFn)
    (h : f * g = 0) : f = 0 ∨ g = 0 := by
  rw [mem_HolFn, UpperHalfPlane.mdifferentiable_iff] at hf hg
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have key := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (hf.analyticOnNhd hU)
    (hg.analyticOnNhd hU) (fun z hz ↦ by
      have := congrFun h (ofComplex z)
      simpa using this) (convex_halfSpace_im_gt 0).isPreconnected
  rcases key with k | k
  · left; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos
  · right; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos

scoped instance : NoZeroDivisors ↥HolFn where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    rcases HolFn.eq_zero_or_eq_zero_of_mul_eq_zero f.2 g.2 (congrArg Subtype.val h) with e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Subtype.ext e)

scoped instance : Nontrivial ↥HolFn := ⟨⟨0, 1, fun h ↦ zero_ne_one (congrFun (congrArg Subtype.val h) UpperHalfPlane.I)⟩⟩

scoped instance : IsDomain ↥HolFn := NoZeroDivisors.to_isDomain _

private lemma j_smul_eq (γ : SL(2, ℤ)) (τ : ℍ) : j (γ • τ) = j τ := by
  have hγ : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  rw [CuspForm.coe_discriminant] at hΔ
  rw [show (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ = γ • τ from rfl,
    denom_mapGL_eq_denomZ] at h4 hΔ
  have hd : denomZ γ τ ≠ 0 := denomZ_ne_zero γ τ
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  simp only [j]
  rw [h4, hΔ, zpow_ofNat, zpow_ofNat]
  field_simp

private lemma smul_j (γ : SL(2, ℤ)) : γ • j = j := by
  funext τ; rw [sl_smul_apply, j_smul_eq]

private lemma smul_frickeF {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (a : Fin 2 → ZMod N) :
    γ • frickeF N a = frickeF N (vecMulSL N a γ⁻¹) := by
  funext τ; rw [sl_smul_apply, frickeF_slash]

private def levelGen (N : ℕ) : Set (ℍ → ℂ) := insert j (Set.range fun i : FrickeIdx N ↦ frickeF N i.1)

private def levelRing (N : ℕ) : Subalgebra ℂ (ℍ → ℂ) := Algebra.adjoin ℂ (levelGen N)

private lemma j_mem_levelRing (N : ℕ) : j ∈ levelRing N := Algebra.subset_adjoin (Set.mem_insert _ _)

private lemma frickeF_mem_levelRing {N : ℕ} (i : FrickeIdx N) : frickeF N i.1 ∈ levelRing N :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)

private lemma mdifferentiable_j : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j :=
  (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo' ModularForm.discriminant_ne_zero

private lemma levelGen_subset_HolFn (N : ℕ) [NeZero N] : levelGen N ⊆ HolFn := by
  rintro f (rfl | ⟨i, rfl⟩)
  · exact mdifferentiable_j
  · exact mdifferentiable_frickeF i

private lemma levelRing_le_HolFn (N : ℕ) [NeZero N] : levelRing N ≤ HolFn :=
  Algebra.adjoin_le (levelGen_subset_HolFn N)

scoped instance (N : ℕ) [NeZero N] : IsDomain ↥(levelRing N) := by
  have : NoZeroDivisors ↥(levelRing N) := ⟨fun {f g} h ↦ by
    rcases HolFn.eq_zero_or_eq_zero_of_mul_eq_zero (levelRing_le_HolFn N f.2)
      (levelRing_le_HolFn N g.2) (congrArg Subtype.val h) with e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Subtype.ext e)⟩
  have : Nontrivial ↥(levelRing N) :=
    ⟨⟨0, 1, fun h ↦ zero_ne_one (congrFun (congrArg Subtype.val h) UpperHalfPlane.I)⟩⟩
  exact NoZeroDivisors.to_isDomain _

private lemma smul_mem_levelGen {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) {f : ℍ → ℂ} (hf : f ∈ levelGen N) :
    γ • f ∈ levelGen N := by
  rcases hf with rfl | ⟨i, rfl⟩
  · rw [smul_j]; exact Set.mem_insert _ _
  · rw [smul_frickeF]
    exact Set.mem_insert_of_mem _ ⟨⟨_, vecMulSL_ne_zero i.2 γ⁻¹⟩, rfl⟩

private theorem smul_mem_levelRing {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) {f : ℍ → ℂ}
    (hf : f ∈ levelRing N) : γ • f ∈ levelRing N := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (smul_mem_levelGen γ hx)
  | algebraMap c => rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
                    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) _
  | add x y _ _ hx hy => rw [smul_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [smul_mul']; exact Subalgebra.mul_mem _ hx hy

scoped instance levelRingAction (N : ℕ) [NeZero N] : MulSemiringAction SL(2, ℤ) ↥(levelRing N) where
  smul γ f := ⟨γ • f.1, smul_mem_levelRing γ f.2⟩
  one_smul f := Subtype.ext (one_smul _ f.1)
  mul_smul γ δ f := Subtype.ext (mul_smul γ δ f.1)
  smul_zero γ := Subtype.ext (smul_zero γ)
  smul_add γ f g := Subtype.ext (smul_add γ f.1 g.1)
  smul_one γ := Subtype.ext (smul_one γ)
  smul_mul γ f g := Subtype.ext (smul_mul' γ f.1 g.1)

@[scoped simp] private lemma levelRing_coe_smul {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (f : ↥(levelRing N)) :
    ((γ • f : ↥(levelRing N)) : ℍ → ℂ) = γ • (f : ℍ → ℂ) := rfl

scoped instance levelRing_smulCommClass (N : ℕ) [NeZero N] :
    SMulCommClass SL(2, ℤ) ℂ ↥(levelRing N) where
  smul_comm _ _ _ := rfl

private def levelFixer (N : ℕ) [NeZero N] : Subgroup SL(2, ℤ) :=
  (MulSemiringAction.toAlgAut SL(2, ℤ) ℂ ↥(levelRing N)).ker

scoped instance (N : ℕ) [NeZero N] : (levelFixer N).Normal := MonoidHom.normal_ker _

private lemma mem_levelFixer_iff {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) :
    γ ∈ levelFixer N ↔ ∀ f : ↥(levelRing N), γ • f = f := by
  rw [levelFixer, MonoidHom.mem_ker, AlgEquiv.ext_iff]
  rfl

private lemma mem_levelFixer_iff_frickeF {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) :
    γ ∈ levelFixer N ↔ ∀ (i : FrickeIdx N) (τ : ℍ), frickeF N i.1 (γ • τ) = frickeF N i.1 τ := by
  rw [mem_levelFixer_iff]
  constructor
  · intro h i τ
    have e := congrArg Subtype.val (h (γ⁻¹ • ⟨frickeF N i.1, frickeF_mem_levelRing i⟩))
    rw [← mul_smul, mul_inv_cancel, one_smul, levelRing_coe_smul] at e
    have := congrFun e τ
    rw [sl_smul_apply, inv_inv] at this
    exact this.symm
  · intro h f
    obtain ⟨f, hf⟩ := f
    apply Subtype.ext
    show γ • f = f
    induction hf using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | ⟨i, rfl⟩
      · exact smul_j γ
      · funext τ
        rw [sl_smul_apply]
        have := h i (γ⁻¹ • τ)
        rw [← mul_smul, mul_inv_cancel, one_smul] at this
        exact this.symm
    | algebraMap c => rfl
    | add x y _ _ hx hy => rw [smul_add, hx, hy]
    | mul x y _ _ hx hy => rw [smul_mul', hx, hy]

private lemma Gamma_le_levelFixer (N : ℕ) [NeZero N] : CongruenceSubgroup.Gamma N ≤ levelFixer N :=
  fun _ hγ ↦ (mem_levelFixer_iff_frickeF _).mpr fun i τ ↦ frickeF_invariant_Gamma i.1 hγ τ

private theorem mem_levelFixer_iff_pm {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) :
    γ ∈ levelFixer N ↔ γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N := by
  constructor
  · intro h; exact frickeF_faithful γ ((mem_levelFixer_iff_frickeF γ).mp h)
  · rintro (h | h)
    · exact Gamma_le_levelFixer N h
    · have : γ = -(-γ) := (neg_neg γ).symm
      rw [this, mem_levelFixer_iff_frickeF]
      intro i τ
      rw [ModularGroup.SL_neg_smul]
      exact frickeF_invariant_Gamma i.1 h τ

scoped instance (N : ℕ) [NeZero N] : (levelFixer N).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_levelFixer N)

private abbrev LevelGrp (N : ℕ) [NeZero N] : Type := SL(2, ℤ) ⧸ levelFixer N

noncomputable scoped instance (N : ℕ) [NeZero N] : Fintype (LevelGrp N) := Fintype.ofFinite _

private lemma card_LevelGrp (N : ℕ) [NeZero N] : Fintype.card (LevelGrp N) = (levelFixer N).index := by
  rw [Fintype.card_eq_nat_card]; rfl

noncomputable scoped instance levelGrpRingAction (N : ℕ) [NeZero N] :
    MulSemiringAction (LevelGrp N) ↥(levelRing N) :=
  MulSemiringAction.compHom _
    (QuotientGroup.kerLift (MulSemiringAction.toAlgAut SL(2, ℤ) ℂ ↥(levelRing N)))

@[scoped simp] private lemma levelGrp_mk_smul {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (f : ↥(levelRing N)) :
    (QuotientGroup.mk γ : LevelGrp N) • f = γ • f := rfl

scoped instance levelGrp_smulCommClass (N : ℕ) [NeZero N] :
    SMulCommClass (LevelGrp N) ℂ ↥(levelRing N) where
  smul_comm q c f := by
    induction q using QuotientGroup.induction_on with
    | H γ => simp only [levelGrp_mk_smul]; exact smul_comm γ c f

scoped instance levelGrp_faithful (N : ℕ) [NeZero N] : FaithfulSMul (LevelGrp N) ↥(levelRing N) where
  eq_of_smul_eq_smul {q₁ q₂} h := by
    apply QuotientGroup.kerLift_injective (MulSemiringAction.toAlgAut SL(2, ℤ) ℂ ↥(levelRing N))
    exact AlgEquiv.ext fun f ↦ h f

private abbrev levelField (N : ℕ) [NeZero N] : Type := FractionRing ↥(levelRing N)

noncomputable scoped instance levelGrpFieldAction (N : ℕ) [NeZero N] :
    MulSemiringAction (LevelGrp N) (levelField N) :=
  IsFractionRing.mulSemiringAction (LevelGrp N) ↥(levelRing N) (levelField N)

scoped instance levelGrp_smulDistribClass (N : ℕ) [NeZero N] :
    SMulDistribClass (LevelGrp N) ↥(levelRing N) (levelField N) :=
  IsFractionRing.smulDistribClass (LevelGrp N) ↥(levelRing N) (levelField N)

private lemma levelGrp_smul_algebraMap {N : ℕ} [NeZero N] (g : LevelGrp N) (a : ↥(levelRing N)) :
    g • algebraMap ↥(levelRing N) (levelField N) a = algebraMap ↥(levelRing N) (levelField N) (g • a) :=
  (algebraMap.coe_smul' g a (levelField N)).symm

scoped instance levelGrpField_faithful (N : ℕ) [NeZero N] : FaithfulSMul (LevelGrp N) (levelField N) :=
  IsFractionRing.faithfulSMul (LevelGrp N) ↥(levelRing N) (levelField N)

scoped instance levelGrpField_smulCommClass (N : ℕ) [NeZero N] :
    SMulCommClass (LevelGrp N) ℂ (levelField N) :=
  IsFractionRing.smulCommClass (LevelGrp N) ℂ ↥(levelRing N) ℂ (levelField N)

private theorem finrank_levelField_fixed (N : ℕ) [NeZero N] :
    Module.finrank (FixedPoints.subfield (LevelGrp N) (levelField N)) (levelField N) =
      (levelFixer N).index := by
  rw [FixedPoints.finrank_eq_card, card_LevelGrp]

private def _root_.WLight.jA (N : ℕ) : ↥(levelRing N) := ⟨j, j_mem_levelRing N⟩

open _root_.WLight

private def _root_.WLight.jK (N : ℕ) [NeZero N] : levelField N := algebraMap ↥(levelRing N) (levelField N) (jA N)

open _root_.WLight
private lemma aeval_j_apply (P : Polynomial ℂ) (τ : ℍ) :
    (Polynomial.aeval j P : ℍ → ℂ) τ = Polynomial.eval (j τ) P := by
  rw [show (Polynomial.aeval j P : ℍ → ℂ) τ = Pi.evalAlgHom ℂ (fun _ : ℍ ↦ ℂ) τ (Polynomial.aeval j P)
    from rfl, ← Polynomial.aeval_algHom_apply, ← Polynomial.coe_aeval_eq_eval]
  rfl

private lemma coe_aeval_jA (N : ℕ) (P : Polynomial ℂ) :
    ((Polynomial.aeval (jA N) P : ↥(levelRing N)) : ℍ → ℂ) = fun τ ↦ Polynomial.eval (j τ) P := by
  rw [Polynomial.aeval_subalgebra_coe]
  funext τ
  exact aeval_j_apply P τ

private lemma levelGen_poleBounded (N : ℕ) [NeZero N] : ∀ f ∈ levelGen N, PoleBounded f := by
  rintro f (rfl | ⟨i, rfl⟩)
  · exact poleBounded_j
  · exact poleBounded_frickeF i

private theorem levelRing_fixed_eq_aeval_j {N : ℕ} [NeZero N] (a : ↥(levelRing N))
    (ha : ∀ γ : SL(2, ℤ), γ • a = a) : ∃ P : Polynomial ℂ, a = Polynomial.aeval (jA N) P := by
  have ha' : ∀ γ : SL(2, ℤ), γ • (a : ℍ → ℂ) = a := fun γ ↦ congrArg Subtype.val (ha γ)
  have hinv : ∀ γ : SL(2, ℤ), (a : ℍ → ℂ) ∣[(0 : ℤ)] γ = a := by
    intro γ
    funext τ
    rw [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
    exact (sl_smul_eq_self_iff _).mp ha' γ τ
  obtain ⟨P, hP⟩ := eq_polynomial_j_of_invariant_of_mem_adjoin (levelGen_poleBounded N) a.2 hinv
  exact ⟨P, Subtype.ext (by rw [coe_aeval_jA]; exact hP)⟩

private theorem levelRing_fixed_eq_aeval_j' {N : ℕ} [NeZero N] (a : ↥(levelRing N))
    (ha : ∀ g : LevelGrp N, g • a = a) : ∃ P : Polynomial ℂ, a = Polynomial.aeval (jA N) P :=
  levelRing_fixed_eq_aeval_j a fun γ ↦ ha (QuotientGroup.mk γ)

private lemma _root_.WLight.smul_jK {N : ℕ} [NeZero N] (g : LevelGrp N) : g • jK N = jK N := by
  rw [jK, levelGrp_smul_algebraMap]
  congr 1
  induction g using QuotientGroup.induction_on with
  | H γ => exact Subtype.ext (smul_j γ)

open _root_.WLight

private theorem fixedPoints_levelField_eq_adjoin_j (N : ℕ) [NeZero N] :
    (MulAction.fixedPoints (LevelGrp N) (levelField N) : Set (levelField N)) =
      (IntermediateField.adjoin ℂ {jK N} : Set (levelField N)) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [MulAction.mem_fixedPoints] at hx
    obtain ⟨a, b, ha, hb, hb0, hab⟩ :=
      exists_fixed_div_of_fixed (A := ↥(levelRing N)) (K := levelField N) (G := LevelGrp N)
        levelGrp_smul_algebraMap x hx
    obtain ⟨P, rfl⟩ := levelRing_fixed_eq_aeval_j' a ha
    obtain ⟨Q, rfl⟩ := levelRing_fixed_eq_aeval_j' b hb
    rw [SetLike.mem_coe, IntermediateField.mem_adjoin_simple_iff]
    refine ⟨P, Q, ?_⟩
    rw [jK, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_algebraMap_apply,
      eq_div_iff hb0, hab]
  · change (IntermediateField.adjoin ℂ {jK N} : Set (levelField N)) ⊆
      (FixedPoints.intermediateField (F := ℂ) (LevelGrp N) : IntermediateField ℂ (levelField N))
    exact SetLike.coe_subset_coe.mpr (IntermediateField.adjoin_simple_le_iff.mpr fun g ↦ smul_jK g)

end B5_carrier

section B7_group

open Matrix
open scoped UpperHalfPlane MatrixGroups CongruenceSubgroup

private def adjoinNegOneSL {R : Type*} [CommRing R] (H : Subgroup SL(2, R)) : Subgroup SL(2, R) where
  carrier := {g | g ∈ H ∨ -g ∈ H}
  mul_mem' ha hb := by
    rcases ha with ha | ha <;>
      rcases hb with hb | hb <;>
      · have := mul_mem ha hb
        simp_all [neg_mul, mul_neg, neg_neg]
  one_mem' := .inl H.one_mem
  inv_mem' ha := by
    rcases ha with ha | ha <;>
    · have := inv_mem ha
      simp_all

@[scoped simp] private lemma mem_adjoinNegOneSL {R : Type*} [CommRing R] {H : Subgroup SL(2, R)} {g : SL(2, R)} :
    g ∈ adjoinNegOneSL H ↔ g ∈ H ∨ -g ∈ H := Iff.rfl

private lemma le_adjoinNegOneSL {R : Type*} [CommRing R] (H : Subgroup SL(2, R)) :
    H ≤ adjoinNegOneSL H := fun _ hg ↦ .inl hg

private lemma normal_adjoinNegOneSL {R : Type*} [CommRing R] {H : Subgroup SL(2, R)} (hH : H.Normal) :
    (adjoinNegOneSL H).Normal := by
  constructor
  intro γ hγ g
  rcases hγ with h | h
  · exact .inl (hH.conj_mem γ h g)
  · refine .inr ?_
    rw [show -(g * γ * g⁻¹) = g * (-γ) * g⁻¹ by rw [mul_neg, neg_mul]]
    exact hH.conj_mem (-γ) h g

private abbrev pmGamma (N : ℕ) : Subgroup SL(2, ℤ) := adjoinNegOneSL Γ(N)

private lemma Gamma_le_pmGamma (N : ℕ) : Γ(N) ≤ pmGamma N := le_adjoinNegOneSL _

scoped instance instNormal_pmGamma (N : ℕ) : (pmGamma N).Normal :=
  normal_adjoinNegOneSL (CongruenceSubgroup.Gamma_normal N)

scoped instance instFiniteIndex_pmGamma (N : ℕ) [NeZero N] : (pmGamma N).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_pmGamma N)

private def frickeKernel (N : ℕ) [NeZero N] : Subgroup SL(2, ℤ) where
  carrier := {γ | ∀ (i : FrickeIdx N) (τ : ℍ), frickeF N i.1 (γ • τ) = frickeF N i.1 τ}
  mul_mem' {a b} ha hb i τ := by rw [mul_smul, ha, hb]
  one_mem' i τ := by rw [one_smul]
  inv_mem' {a} ha i τ := by
    have := ha i (a⁻¹ • τ); rw [smul_inv_smul] at this; exact this.symm

private lemma mem_frickeKernel {N : ℕ} [NeZero N] {γ : SL(2, ℤ)} :
    γ ∈ frickeKernel N ↔ ∀ (i : FrickeIdx N) (τ : ℍ), frickeF N i.1 (γ • τ) = frickeF N i.1 τ :=
  Iff.rfl

private lemma neg_one_smul_upperHalfPlane (τ : ℍ) : (-1 : SL(2, ℤ)) • τ = τ := by
  rw [show (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) from rfl, ModularGroup.SL_neg_smul, one_smul]

private lemma neg_one_mem_frickeKernel (N : ℕ) [NeZero N] : (-1 : SL(2, ℤ)) ∈ frickeKernel N :=
  fun _ τ ↦ by rw [neg_one_smul_upperHalfPlane]

private lemma Gamma_le_frickeKernel (N : ℕ) [NeZero N] : Γ(N) ≤ frickeKernel N :=
  fun _ hγ i τ ↦ frickeF_invariant_Gamma i.1 hγ τ

private theorem frickeKernel_eq_pmGamma (N : ℕ) [NeZero N] : frickeKernel N = pmGamma N := by
  refine le_antisymm ?_ ?_
  · intro γ hγ
    exact mem_adjoinNegOneSL.mpr (frickeF_faithful γ hγ)
  · intro γ hγ
    rcases mem_adjoinNegOneSL.mp hγ with h | h
    · exact Gamma_le_frickeKernel N h
    · have hrw : γ = -1 * (-γ) := by simp
      rw [hrw]
      exact (frickeKernel N).mul_mem (neg_one_mem_frickeKernel N) (Gamma_le_frickeKernel N h)

scoped instance instFiniteIndex_frickeKernel (N : ℕ) [NeZero N] : (frickeKernel N).FiniteIndex :=
  frickeKernel_eq_pmGamma N ▸ instFiniteIndex_pmGamma N

scoped instance instNormal_frickeKernel (N : ℕ) [NeZero N] : (frickeKernel N).Normal :=
  frickeKernel_eq_pmGamma N ▸ instNormal_pmGamma N

scoped instance instFinite_quotient_pmGamma (N : ℕ) [NeZero N] : Finite (SL(2, ℤ) ⧸ pmGamma N) :=
  Subgroup.finite_quotient_of_finiteIndex

scoped instance instFinite_quotient_frickeKernel (N : ℕ) [NeZero N] :
    Finite (SL(2, ℤ) ⧸ frickeKernel N) :=
  Subgroup.finite_quotient_of_finiteIndex

end B7_group

section B7_assembled

open scoped UpperHalfPlane MatrixGroups IntermediateField

private lemma levelFixer_eq_frickeKernel (N : ℕ) [NeZero N] : levelFixer N = frickeKernel N :=
  Subgroup.ext fun γ ↦ (mem_levelFixer_iff_frickeF γ).trans mem_frickeKernel.symm

private lemma levelFixer_eq_pmGamma (N : ℕ) [NeZero N] : levelFixer N = pmGamma N := by
  rw [levelFixer_eq_frickeKernel, frickeKernel_eq_pmGamma]

private def fixedIF (N : ℕ) [NeZero N] : IntermediateField ℂ (levelField N) :=
  FixedPoints.intermediateField (F := ℂ) (LevelGrp N)

private lemma fixedIF_eq_adjoin (N : ℕ) [NeZero N] : fixedIF N = ℂ⟮jK N⟯ :=
  SetLike.coe_injective (fixedPoints_levelField_eq_adjoin_j N)

private lemma finrank_fixedIF (N : ℕ) [NeZero N] :
    Module.finrank ↥(fixedIF N) (levelField N) = (levelFixer N).index :=
  finrank_levelField_fixed N

private theorem finrank_adjoin_j_levelField (N : ℕ) [NeZero N] :
    Module.finrank ↥ℂ⟮jK N⟯ (levelField N) = (pmGamma N).index := by
  rw [← fixedIF_eq_adjoin, finrank_fixedIF, levelFixer_eq_pmGamma]

private theorem transcendental_jA (N : ℕ) [NeZero N] : Transcendental ℂ (jA N) := by
  rw [transcendental_iff]
  intro P hP
  have hfun : (fun τ : ℍ ↦ Polynomial.eval (j τ) P) = 0 := by
    rw [← coe_aeval_jA N P, hP]; rfl
  apply Polynomial.eq_zero_of_infinite_isRoot
  have : {x : ℂ | P.IsRoot x} = Set.univ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Polynomial.IsRoot.def]
    obtain ⟨τ, rfl⟩ := j_surjective z
    exact congrFun hfun τ
  rw [this]
  exact Set.infinite_univ

private theorem transcendental_jK (N : ℕ) [NeZero N] : Transcendental ℂ (jK N) := by
  rw [transcendental_iff]
  intro P hP
  rw [jK, Polynomial.aeval_algebraMap_apply,
    map_eq_zero_iff _ (IsFractionRing.injective ↥(levelRing N) (levelField N))] at hP
  exact (transcendental_iff.mp (transcendental_jA N)) P hP

end B7_assembled

section C1_carrier

open scoped UpperHalfPlane MatrixGroups IntermediateField IntermediateField.algebraAdjoinAdjoin
open _root_.Polynomial _root_.Real.Polynomial
open scoped _root_.Polynomial _root_.Real.Polynomial

private abbrev polyJ (N : ℕ) [NeZero N] : Subalgebra ℂ (levelField N) := Algebra.adjoin ℂ {jK N}

private abbrev _root_.WLight.ratJ (N : ℕ) [NeZero N] : IntermediateField ℂ (levelField N) := ℂ⟮jK N⟯

open _root_.WLight

private noncomputable def polyJEquiv (N : ℕ) [NeZero N] : ℂ[X] ≃ₐ[ℂ] ↥(polyJ N) :=
  Polynomial.algEquivOfTranscendental ℂ (jK N) (transcendental_jK N)

scoped instance (N : ℕ) [NeZero N] : IsDomain ↥(polyJ N) := inferInstance

scoped instance (N : ℕ) [NeZero N] : IsPrincipalIdealRing ↥(polyJ N) :=
  IsPrincipalIdealRing.of_surjective (polyJEquiv N).toRingEquiv.toRingHom
    (polyJEquiv N).surjective

scoped instance (N : ℕ) [NeZero N] : IsDedekindDomain ↥(polyJ N) :=
  IsPrincipalIdealRing.isDedekindDomain ↥(polyJ N)

scoped instance (N : ℕ) [NeZero N] : CharZero (levelField N) :=
  charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℂ (levelField N))

scoped instance (N : ℕ) [NeZero N] : CharZero ↥(ratJ N) :=
  charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℂ ↥(ratJ N))

private lemma index_pmGamma_pos (N : ℕ) [NeZero N] : 0 < (pmGamma N).index := Nat.pos_of_ne_zero
  Subgroup.FiniteIndex.index_ne_zero

scoped instance (N : ℕ) [NeZero N] : FiniteDimensional ↥(ratJ N) (levelField N) :=
  haveI : Module.Free ↥(ratJ N) (levelField N) := Module.Free.of_divisionRing _ _
  Module.finite_of_finrank_pos (by rw [finrank_adjoin_j_levelField]; exact index_pmGamma_pos N)

scoped instance (N : ℕ) [NeZero N] : Algebra.IsSeparable ↥(ratJ N) (levelField N) :=
  haveI : Algebra.IsIntegral ↥(ratJ N) (levelField N) := Algebra.IsIntegral.of_finite _ _
  Algebra.IsSeparable.of_integral ↥(ratJ N) (levelField N)

private abbrev levelIntClosure (N : ℕ) [NeZero N] : Subalgebra ↥(polyJ N) (levelField N) :=
  integralClosure ↥(polyJ N) (levelField N)

scoped instance (N : ℕ) [NeZero N] : IsDedekindDomain ↥(levelIntClosure N) :=
  integralClosure.isDedekindDomain ↥(polyJ N) ↥(ratJ N) (levelField N)

private def levelRingEval (N : ℕ) (τ : ℍ) : ↥(levelRing N) →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : ℍ ↦ ℂ) τ).comp (levelRing N).val

@[scoped simp] private lemma levelRingEval_apply (N : ℕ) (τ : ℍ) (a : ↥(levelRing N)) :
    levelRingEval N τ a = (a : ℍ → ℂ) τ := rfl

end C1_carrier

section C0_membership

open scoped UpperHalfPlane Manifold MatrixGroups ModularForm IntermediateField
open UpperHalfPlane hiding I

private structure LevelGens (N : ℕ) [NeZero N] where
  S : Set (ℍ → ℂ)
  levelGen_subset : levelGen N ⊆ S
  poleBounded : ∀ f ∈ S, PoleBounded f
  smul_mem : ∀ (γ : SL(2, ℤ)), ∀ f ∈ S, γ • f ∈ S
  invariant : ∀ f ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ

namespace LevelGens

variable {N : ℕ} [NeZero N] (D : LevelGens N)

private def std (N : ℕ) [NeZero N] : LevelGens N where
  S := levelGen N
  levelGen_subset := subset_rfl
  poleBounded := levelGen_poleBounded N
  smul_mem γ f hf := smul_mem_levelGen γ hf
  invariant := by
    rintro f (rfl | ⟨i, rfl⟩) γ hγ τ
    · exact j_smul_eq γ τ
    · exact frickeF_invariant_Gamma i.1 hγ τ

private def ring : Subalgebra ℂ (ℍ → ℂ) := Algebra.adjoin ℂ D.S

private lemma ring_le_HolFn : D.ring ≤ HolFn :=
  Algebra.adjoin_le fun f hf ↦ (D.poleBounded f hf).1

private lemma levelRing_le_ring : levelRing N ≤ D.ring := Algebra.adjoin_mono D.levelGen_subset

scoped instance : IsDomain ↥D.ring := by
  have : NoZeroDivisors ↥D.ring := ⟨fun {f g} h ↦ by
    rcases HolFn.eq_zero_or_eq_zero_of_mul_eq_zero (D.ring_le_HolFn f.2)
      (D.ring_le_HolFn g.2) (congrArg Subtype.val h) with e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Subtype.ext e)⟩
  have : Nontrivial ↥D.ring :=
    ⟨⟨0, 1, fun h ↦ zero_ne_one (congrFun (congrArg Subtype.val h) UpperHalfPlane.I)⟩⟩
  exact NoZeroDivisors.to_isDomain _

private theorem smul_mem_ring (γ : SL(2, ℤ)) {f : ℍ → ℂ} (hf : f ∈ D.ring) : γ • f ∈ D.ring := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (D.smul_mem γ x hx)
  | algebraMap c => rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
                    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) _
  | add x y _ _ hx hy => rw [smul_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [smul_mul']; exact Subalgebra.mul_mem _ hx hy

scoped instance ringAction : MulSemiringAction SL(2, ℤ) ↥D.ring where
  smul γ f := ⟨γ • f.1, D.smul_mem_ring γ f.2⟩
  one_smul f := Subtype.ext (one_smul _ f.1)
  mul_smul γ δ f := Subtype.ext (mul_smul γ δ f.1)
  smul_zero γ := Subtype.ext (smul_zero γ)
  smul_add γ f g := Subtype.ext (smul_add γ f.1 g.1)
  smul_one γ := Subtype.ext (smul_one γ)
  smul_mul γ f g := Subtype.ext (smul_mul' γ f.1 g.1)

@[scoped simp] private lemma ring_coe_smul (γ : SL(2, ℤ)) (f : ↥D.ring) :
    ((γ • f : ↥D.ring) : ℍ → ℂ) = γ • (f : ℍ → ℂ) := rfl

scoped instance ring_smulCommClass : SMulCommClass SL(2, ℤ) ℂ ↥D.ring where
  smul_comm _ _ _ := rfl

private lemma smul_eq_self_of_pm {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N)
    {f : ℍ → ℂ} (hf : f ∈ D.ring) : γ • f = f := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    funext τ
    rw [sl_smul_apply]
    rcases hγ with h | h
    · exact D.invariant x hx γ⁻¹ (inv_mem h) τ
    · have : γ⁻¹ = -(-γ)⁻¹ := by simp
      rw [this, ModularGroup.SL_neg_smul]
      exact D.invariant x hx (-γ)⁻¹ (inv_mem h) τ
  | algebraMap c => rfl
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | mul x y _ _ hx hy => rw [smul_mul', hx, hy]

private lemma levelFixer_le_ker :
    levelFixer N ≤ (MulSemiringAction.toAlgAut SL(2, ℤ) ℂ ↥D.ring).ker := by
  intro γ hγ
  rw [MonoidHom.mem_ker]
  ext f
  exact congrFun (D.smul_eq_self_of_pm ((mem_levelFixer_iff_pm γ).mp hγ) f.2) _

private lemma ker_le_levelFixer :
    (MulSemiringAction.toAlgAut SL(2, ℤ) ℂ ↥D.ring).ker ≤ levelFixer N := by
  intro γ hγ
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff] at hγ
  have h' : ∀ a : ↥D.ring, γ • a = a := fun a ↦ hγ a
  rw [mem_levelFixer_iff_frickeF]
  intro i τ
  set fa : ↥D.ring := ⟨frickeF N i.1, D.levelRing_le_ring (frickeF_mem_levelRing i)⟩
  have e : γ • (γ⁻¹ • frickeF N i.1) = γ⁻¹ • frickeF N i.1 :=
    congrArg Subtype.val (h' (γ⁻¹ • fa))
  rw [← mul_smul, mul_inv_cancel, one_smul] at e
  have := congrFun e τ
  rw [sl_smul_apply, inv_inv] at this
  exact this.symm

noncomputable scoped instance grpRingAction : MulSemiringAction (LevelGrp N) ↥D.ring :=
  MulSemiringAction.compHom _
    (QuotientGroup.lift (levelFixer N) (MulSemiringAction.toAlgAut SL(2, ℤ) ℂ ↥D.ring)
      D.levelFixer_le_ker)

@[scoped simp] private lemma grp_mk_smul (γ : SL(2, ℤ)) (f : ↥D.ring) :
    (QuotientGroup.mk γ : LevelGrp N) • f = γ • f := rfl

scoped instance grp_smulCommClass : SMulCommClass (LevelGrp N) ℂ ↥D.ring where
  smul_comm q c f := by
    induction q using QuotientGroup.induction_on with
    | H γ => simp only [grp_mk_smul]; exact smul_comm γ c f

scoped instance grp_faithful : FaithfulSMul (LevelGrp N) ↥D.ring where
  eq_of_smul_eq_smul {q₁ q₂} h := by
    induction q₁ using QuotientGroup.induction_on with
    | H γ₁ =>
    induction q₂ using QuotientGroup.induction_on with
    | H γ₂ =>
    apply QuotientGroup.eq.mpr
    apply D.ker_le_levelFixer
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    exact AlgEquiv.ext fun f ↦ h f

private abbrev field : Type := FractionRing ↥D.ring

noncomputable scoped instance grpFieldAction : MulSemiringAction (LevelGrp N) D.field :=
  IsFractionRing.mulSemiringAction (LevelGrp N) ↥D.ring D.field

scoped instance grp_smulDistribClass : SMulDistribClass (LevelGrp N) ↥D.ring D.field :=
  IsFractionRing.smulDistribClass (LevelGrp N) ↥D.ring D.field

private lemma grp_smul_algebraMap (g : LevelGrp N) (a : ↥D.ring) :
    g • algebraMap ↥D.ring D.field a = algebraMap ↥D.ring D.field (g • a) :=
  (algebraMap.coe_smul' g a D.field).symm

scoped instance grpField_faithful : FaithfulSMul (LevelGrp N) D.field :=
  IsFractionRing.faithfulSMul (LevelGrp N) ↥D.ring D.field

scoped instance grpField_smulCommClass : SMulCommClass (LevelGrp N) ℂ D.field :=
  IsFractionRing.smulCommClass (LevelGrp N) ℂ ↥D.ring ℂ D.field

private theorem finrank_field_fixed :
    Module.finrank (FixedPoints.subfield (LevelGrp N) D.field) D.field = (levelFixer N).index := by
  rw [FixedPoints.finrank_eq_card, card_LevelGrp]

private def jA : ↥D.ring := ⟨j, D.levelRing_le_ring (j_mem_levelRing N)⟩

private def jK : D.field := algebraMap ↥D.ring D.field D.jA

private lemma coe_aeval_jA (P : Polynomial ℂ) :
    ((Polynomial.aeval D.jA P : ↥D.ring) : ℍ → ℂ) = fun τ ↦ Polynomial.eval (j τ) P := by
  rw [Polynomial.aeval_subalgebra_coe]
  funext τ
  exact aeval_j_apply P τ

private theorem ring_fixed_eq_aeval_j (a : ↥D.ring) (ha : ∀ g : LevelGrp N, g • a = a) :
    ∃ P : Polynomial ℂ, a = Polynomial.aeval D.jA P := by
  have ha' : ∀ γ : SL(2, ℤ), γ • (a : ℍ → ℂ) = a :=
    fun γ ↦ congrArg Subtype.val (ha (QuotientGroup.mk γ))
  have hinv : ∀ γ : SL(2, ℤ), (a : ℍ → ℂ) ∣[(0 : ℤ)] γ = a := by
    intro γ
    funext τ
    rw [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
    exact (sl_smul_eq_self_iff _).mp ha' γ τ
  obtain ⟨P, hP⟩ := eq_polynomial_j_of_invariant_of_mem_adjoin D.poleBounded a.2 hinv
  exact ⟨P, Subtype.ext (by rw [coe_aeval_jA]; exact hP)⟩

private lemma smul_jK (g : LevelGrp N) : g • D.jK = D.jK := by
  rw [jK, grp_smul_algebraMap]
  congr 1
  induction g using QuotientGroup.induction_on with
  | H γ => exact Subtype.ext (smul_j γ)

private theorem fixedPoints_field_eq_adjoin_j :
    (MulAction.fixedPoints (LevelGrp N) D.field : Set D.field) =
      (IntermediateField.adjoin ℂ {D.jK} : Set D.field) := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [MulAction.mem_fixedPoints] at hx
    obtain ⟨a, b, ha, hb, hb0, hab⟩ :=
      exists_fixed_div_of_fixed (A := ↥D.ring) (K := D.field) (G := LevelGrp N)
        D.grp_smul_algebraMap x hx
    obtain ⟨P, rfl⟩ := D.ring_fixed_eq_aeval_j a ha
    obtain ⟨Q, rfl⟩ := D.ring_fixed_eq_aeval_j b hb
    rw [SetLike.mem_coe, IntermediateField.mem_adjoin_simple_iff]
    refine ⟨P, Q, ?_⟩
    rw [jK, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_algebraMap_apply,
      eq_div_iff hb0, hab]
  · change (IntermediateField.adjoin ℂ {D.jK} : Set D.field) ⊆
      (FixedPoints.intermediateField (F := ℂ) (LevelGrp N) : IntermediateField ℂ D.field)
    exact SetLike.coe_subset_coe.mpr
      (IntermediateField.adjoin_simple_le_iff.mpr fun g ↦ D.smul_jK g)

private abbrev ratJ : IntermediateField ℂ D.field := ℂ⟮D.jK⟯

private theorem finrank_ratJ : Module.finrank ↥D.ratJ D.field = (levelFixer N).index := by
  have h : (FixedPoints.intermediateField (F := ℂ) (LevelGrp N) : IntermediateField ℂ D.field) =
      D.ratJ := SetLike.coe_injective D.fixedPoints_field_eq_adjoin_j
  rw [← h]
  exact D.finrank_field_fixed

private def incl : ↥(levelRing N) →ₐ[ℂ] ↥D.ring := Subalgebra.inclusion D.levelRing_le_ring

private lemma incl_injective : Function.Injective D.incl := Subalgebra.inclusion_injective _

@[scoped simp] private lemma coe_incl (a : ↥(levelRing N)) : ((D.incl a : ↥D.ring) : ℍ → ℂ) = a :=
  Subalgebra.coe_inclusion _ a

private lemma toRingField_injective :
    Function.Injective ((IsScalarTower.toAlgHom ℂ ↥D.ring D.field).comp D.incl) :=
  (IsFractionRing.injective ↥D.ring D.field).comp D.incl_injective

private noncomputable def toField : levelField N →ₐ[ℂ] D.field :=
  IsFractionRing.liftAlgHom D.toRingField_injective

private lemma toField_algebraMap (a : ↥(levelRing N)) :
    D.toField (algebraMap ↥(levelRing N) (levelField N) a) = algebraMap ↥D.ring D.field (D.incl a) :=
  IsFractionRing.lift_algebraMap D.toRingField_injective a

private lemma toField_jK : D.toField (WLight.jK N) = D.jK := D.toField_algebraMap (WLight.jA N)

noncomputable scoped instance (priority := 3000) algebraField : Algebra (levelField N) D.field :=
  D.toField.toRingHom.toAlgebra

noncomputable scoped instance (priority := 3000) moduleField : Module (levelField N) D.field :=
  Algebra.toModule

noncomputable scoped instance (priority := 3000) smulField : SMul (levelField N) D.field :=
  Algebra.toSMul

scoped instance : IsScalarTower ℂ (levelField N) D.field :=
  IsScalarTower.of_algebraMap_eq fun c ↦ (D.toField.commutes c).symm

noncomputable scoped instance (priority := 3000) algebraRatJ : Algebra ↥(WLight.ratJ N) D.field :=
  ((algebraMap (levelField N) D.field).comp (algebraMap ↥(WLight.ratJ N) (levelField N))).toAlgebra

noncomputable scoped instance (priority := 3000) moduleRatJ : Module ↥(WLight.ratJ N) D.field :=
  Algebra.toModule

noncomputable scoped instance (priority := 3000) smulRatJ : SMul ↥(WLight.ratJ N) D.field :=
  Algebra.toSMul

scoped instance : IsScalarTower ↥(WLight.ratJ N) (levelField N) D.field :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

private lemma ratJ_map_toField : (WLight.ratJ N).map D.toField = D.ratJ := by
  rw [IntermediateField.adjoin_map, Set.image_singleton, toField_jK]

private noncomputable def ratJEquiv : ↥(WLight.ratJ N) ≃ₐ[ℂ] ↥D.ratJ :=
  ((WLight.ratJ N).equivMap D.toField).trans (IntermediateField.equivOfEq D.ratJ_map_toField)

private theorem finrank_ratJN_field : Module.finrank ↥(WLight.ratJ N) D.field = (levelFixer N).index := by
  rw [← D.finrank_ratJ]
  refine Algebra.finrank_eq_of_equiv_equiv D.ratJEquiv.toRingEquiv (RingEquiv.refl D.field) ?_
  ext x
  rfl

private theorem finrank_levelField_field : Module.finrank (levelField N) D.field = 1 := by
  haveI : Module.Free (levelField N) D.field := Module.Free.of_divisionRing _ _
  haveI : Module.Free ↥(WLight.ratJ N) (levelField N) := Module.Free.of_divisionRing _ _
  have h := Module.finrank_mul_finrank ↥(WLight.ratJ N) (levelField N) D.field
  rw [finrank_ratJN_field, finrank_adjoin_j_levelField, ← levelFixer_eq_pmGamma] at h
  have hpos : 0 < (levelFixer N).index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have : (levelFixer N).index * Module.finrank (levelField N) D.field = (levelFixer N).index * 1 := by
    rw [h, mul_one]
  exact Nat.eq_of_mul_eq_mul_left hpos this

private theorem toField_surjective : Function.Surjective D.toField := by
  intro x
  haveI : Module.Free (levelField N) D.field := Module.Free.of_divisionRing _ _
  haveI : FiniteDimensional (levelField N) D.field :=
    Module.finite_of_finrank_pos (by rw [finrank_levelField_field]; exact one_pos)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : D.field) one_ne_zero).mp
    D.finrank_levelField_field x
  refine ⟨c, ?_⟩
  rw [← hc, Algebra.smul_def, mul_one]
  rfl

private theorem exists_frac {F : ℍ → ℂ} (hF : F ∈ D.S) :
    ∃ a b : ↥(levelRing N), b ≠ 0 ∧ F * b = a := by
  obtain ⟨y, hy⟩ := D.toField_surjective (algebraMap ↥D.ring D.field ⟨F, Algebra.subset_adjoin hF⟩)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ↥(levelRing N)) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨a, b, hb0, ?_⟩
  rw [map_div₀, toField_algebraMap, toField_algebraMap, div_eq_iff
    ((map_ne_zero_iff _ (IsFractionRing.injective ↥D.ring D.field)).mpr
      ((map_ne_zero_iff _ D.incl_injective).mpr hb0)), ← map_mul] at hy
  have := congrArg Subtype.val (IsFractionRing.injective ↥D.ring D.field hy)
  rw [Subalgebra.coe_mul, coe_incl, coe_incl] at this
  exact this.symm

end LevelGens

private theorem exists_levelRing_frac {N : ℕ} [NeZero N] {S : Set (ℍ → ℂ)}
    (hpb : ∀ G ∈ S, PoleBounded G) (hst : ∀ (γ : SL(2, ℤ)), ∀ G ∈ S, γ • G ∈ S)
    (hinv : ∀ G ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    {F : ℍ → ℂ} (hF : F ∈ S) : ∃ a b : ↥(levelRing N), b ≠ 0 ∧ F * b = a := by
  let D : LevelGens N :=
    { S := levelGen N ∪ S
      levelGen_subset := Set.subset_union_left
      poleBounded := fun f hf ↦ hf.elim (levelGen_poleBounded N f) (hpb f)
      smul_mem := fun γ f hf ↦ hf.elim (fun h ↦ Or.inl (smul_mem_levelGen γ h))
        (fun h ↦ Or.inr (hst γ f h))
      invariant := fun f hf ↦ hf.elim ((LevelGens.std N).invariant f) (hinv f) }
  exact D.exists_frac (Or.inr hF)

end C0_membership

section R5bBridge

open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

private lemma periodPair_extb {L₁ L₂ : PeriodPair} (h₁ : L₁.ω₁ = L₂.ω₁)
    (h₂ : L₁.ω₂ = L₂.ω₂) : L₁ = L₂ := by
  cases L₁; cases L₂; simp_all

private theorem exists_levelFraction_of_stable_family_core
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (S : Set (ℍ → ℂ))
    (hhol : ∀ G ∈ S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hpb : ∀ G ∈ S, ∃ m : ℕ, IsBoundedAtImInfty (G * ModularForm.discriminant ^ m))
    (hst : ∀ (γ : SL(2, ℤ)), ∀ G ∈ S, (G ∘ (γ • ·)) ∈ S)
    (hinv : ∀ G ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    {F : ℍ → ℂ} (hF : F ∈ S) :
    ∃ a b : ℍ → ℂ,
      a ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
      b ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
      b ≠ 0 ∧ F * b = a := by
  have hLpp : ∀ τ : ℍ, L τ = periodPairOfTau τ := fun τ =>
    periodPair_extb ((hL τ).1.trans (periodPairOfTau_ω₁ τ).symm)
      ((hL τ).2.trans (periodPairOfTau_ω₂ τ).symm)
  have hfr : ∀ v : Fin 2 → ZMod N, fricke v = frickeF N v := by
    intro v
    funext τ
    rw [hfricke v τ, hW v τ, hLpp τ]
    with_unfolding_all rfl
  have hjeq : jf = j := by
    funext τ
    rw [hjf τ]
    rfl
  have hset : (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) =
      levelGen N := by
    rw [hjeq]
    unfold levelGen
    congr 1
    ext g
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, (hfr v).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, (hfr i.1).symm⟩
  have hpb' : ∀ G ∈ S, PoleBounded G := by
    intro G hG
    refine ⟨hhol G hG, ?_⟩
    obtain ⟨m, hm⟩ := hpb G hG
    exact ⟨m, by rw [CuspForm.coe_discriminant]; exact hm⟩
  have hst' : ∀ (γ : SL(2, ℤ)), ∀ G ∈ S, γ • G ∈ S := by
    intro γ G hG
    exact hst γ⁻¹ G hG
  obtain ⟨a, b, hb0, hab⟩ := exists_levelRing_frac (N := N) hpb' hst' hinv hF
  refine ⟨↑a, ↑b, ?_, ?_, ?_, hab⟩
  · rw [hset]
    exact a.2
  · rw [hset]
    exact b.2
  · intro h
    exact hb0 (Subtype.coe_injective (h.trans (ZeroMemClass.coe_zero _).symm))

end R5bBridge

end WLight

open UpperHalfPlane in
open scoped Manifold MatrixGroups ModularForm in
open _root_.WLight WLight in
theorem _root_.WLight.exists_levelFraction_of_stable_family
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (S : Set (ℍ → ℂ))
    (hhol : ∀ G ∈ S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hpb : ∀ G ∈ S, ∃ m : ℕ, IsBoundedAtImInfty (G * ModularForm.discriminant ^ m))
    (hst : ∀ (γ : SL(2, ℤ)), ∀ G ∈ S, (G ∘ (γ • ·)) ∈ S)
    (hinv : ∀ G ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    {F : ℍ → ℂ} (hF : F ∈ S) :
    ∃ a b : ℍ → ℂ,
      a ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
      b ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
      b ≠ 0 ∧ F * b = a :=
  exists_levelFraction_of_stable_family_core N L hL W hW fricke hfricke jf hjf
    S hhol hpb hst hinv hF

end
end WLightS9.S_WLight_exists_levelFraction_of_stable_family


namespace WLightS9.S_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction

set_option autoImplicit false

noncomputable section

open _root_.Complex _root_.Real _root_.UpperHalfPlane _root_.ModularForm _root_.Polynomial _root_.Real.Polynomial
open scoped _root_.Complex _root_.Real _root_.UpperHalfPlane _root_.ModularForm _root_.Polynomial _root_.Real.Polynomial
open scoped Topology Manifold MatrixGroups ModularForm

namespace WLight
open _root_.WLight
open _root_.WLight
open scoped _root_.WLight

section ValuationEngine

private theorem le_meromorphicOrderAt_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} (s : Finset ι) {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) (m : WithTop ℤ)
    (hm : ∀ i ∈ s, m ≤ meromorphicOrderAt (f i) x) :
    m ≤ meromorphicOrderAt (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc m ≤ min (meromorphicOrderAt (f a) x) (meromorphicOrderAt (∑ i ∈ s, f i) x) := by
            refine le_min (hm a (Finset.mem_insert_self a s)) ?_
            exact ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
              (fun i hi ↦ hm i (Finset.mem_insert_of_mem hi))
      _ ≤ meromorphicOrderAt (f a + ∑ i ∈ s, f i) x := by
            apply meromorphicOrderAt_add (hf a (Finset.mem_insert_self a s))
            exact MeromorphicAt.sum (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

private theorem meromorphicOrderAt_le_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ} {τ : 𝕜}
    (hF : AnalyticAt 𝕜 F τ) (hG : AnalyticAt 𝕜 G τ)
    (hGord : meromorphicOrderAt G τ ≠ ⊤) (hc : ∀ k < n, AnalyticAt 𝕜 (c k) τ)
    (hrel : F ^ n + (∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) =ᶠ[𝓝 τ] 0) :
    meromorphicOrderAt G τ ≤ meromorphicOrderAt F τ := by
  by_contra hlt
  rw [not_le] at hlt
  lift meromorphicOrderAt G τ to ℤ using hGord with m hm
  have hFord : meromorphicOrderAt F τ ≠ ⊤ := hlt.ne_top
  lift meromorphicOrderAt F τ to ℤ using hFord with r hr
  have hrm : r < m := WithTop.coe_lt_coe.mp hlt
  set S := ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k with hS
  have hMerS : ∀ k ∈ Finset.range n, MeromorphicAt (c k * G ^ (n - k) * F ^ k) τ := by
    intro k hk
    exact (((hc k (Finset.mem_range.mp hk)).mul ((hG.pow _))).mul (hF.pow _)).meromorphicAt
  have hsum_ord : (↑(n * r) + 1 : WithTop ℤ) ≤ meromorphicOrderAt S τ := by
    refine le_meromorphicOrderAt_sum _ hMerS _ ?_
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hterm : meromorphicOrderAt (c k * G ^ (n - k) * F ^ k) τ
        = meromorphicOrderAt (c k) τ + ((n - k : ℕ) * meromorphicOrderAt G τ
            + k * meromorphicOrderAt F τ) := by
      rw [meromorphicOrderAt_mul (((hc k hk').mul (hG.pow (n - k))).meromorphicAt)
            ((hF.pow k).meromorphicAt),
          meromorphicOrderAt_mul (hc k hk').meromorphicAt ((hG.pow (n - k)).meromorphicAt),
          meromorphicOrderAt_pow hG.meromorphicAt (n := n - k),
          meromorphicOrderAt_pow hF.meromorphicAt (n := k), add_assoc]
    rw [hterm, ← hm, ← hr]
    have hc_ord : (0 : WithTop ℤ) ≤ meromorphicOrderAt (c k) τ :=
      (hc k hk').meromorphicOrderAt_nonneg
    have hnk : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by omega
    have key : (↑(n * r) + 1 : WithTop ℤ)
        ≤ (↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r := by
      rw [show ((n - k : ℕ) : WithTop ℤ) = (((n - k : ℕ) : ℤ) : WithTop ℤ) by push_cast; rfl,
          show ((k : ℕ) : WithTop ℤ) = (((k : ℕ) : ℤ) : WithTop ℤ) by push_cast; rfl,
          ← WithTop.coe_mul, ← WithTop.coe_mul, ← WithTop.coe_add,
          ← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe, hnk]
      have h1 : (1 : ℤ) ≤ (n : ℤ) - k := by omega
      nlinarith [h1, hrm]
    calc (↑(n * r) + 1 : WithTop ℤ)
        ≤ (↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r := key
      _ = 0 + ((↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r) := (zero_add _).symm
      _ ≤ meromorphicOrderAt (c k) τ + ((↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r) := by
          gcongr
  have hFn_ord : meromorphicOrderAt (F ^ n) τ = (↑(n * r) : WithTop ℤ) := by
    rw [meromorphicOrderAt_pow hF.meromorphicAt, ← hr]; push_cast; ring_nf
  have hlt2 : meromorphicOrderAt (F ^ n) τ < meromorphicOrderAt S τ := by
    rw [hFn_ord]
    refine lt_of_lt_of_le ?_ hsum_ord
    exact_mod_cast lt_add_one (n * r)
  have heq : meromorphicOrderAt (F ^ n + S) τ = meromorphicOrderAt (F ^ n) τ :=
    meromorphicOrderAt_add_eq_left_of_lt
      (MeromorphicAt.sum (fun i hi ↦ hMerS i hi)) hlt2
  have hzero : (F ^ n + S) =ᶠ[𝓝[≠] τ] 0 :=
    hrel.filter_mono nhdsWithin_le_nhds
  have htop : meromorphicOrderAt (F ^ n + S) τ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]; exact hzero
  rw [heq, hFn_ord] at htop
  exact WithTop.coe_ne_top htop

open WithTop.LinearOrderedAddCommGroup in

private theorem meromorphicOrderAt_div_nonneg_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ} {τ : 𝕜}
    (hF : AnalyticAt 𝕜 F τ) (hG : AnalyticAt 𝕜 G τ)
    (hGord : meromorphicOrderAt G τ ≠ ⊤) (hc : ∀ k < n, AnalyticAt 𝕜 (c k) τ)
    (hrel : F ^ n + (∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) =ᶠ[𝓝 τ] 0) :
    0 ≤ meromorphicOrderAt (F / G) τ := by
  have hle := meromorphicOrderAt_le_of_monicRel hF hG hGord hc hrel
  rw [meromorphicOrderAt_div hF.meromorphicAt hG.meromorphicAt,
      ← LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top hGord]
  exact (LinearOrderedAddCommGroupWithTop.sub_le_sub_iff_left_of_ne_top hGord).mpr hle

end ValuationEngine

section HBridge

private lemma analyticOnNhd_comp_ofComplex {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet

private lemma mdifferentiable_of_analyticOnNhd {f : ℍ → ℂ}
    (hf : AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  UpperHalfPlane.mdifferentiable_iff.mpr hf.differentiableOn

private theorem mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero {f g : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hfg : f * g = 0) : f = 0 ∨ g = 0 := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf hg
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have key := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (hf.analyticOnNhd hU)
    (hg.analyticOnNhd hU) (fun z hz ↦ by
      have := congrFun hfg (ofComplex z)
      simpa using this) (convex_halfSpace_im_gt 0).isPreconnected
  rcases key with k | k
  · left; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos
  · right; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos

end HBridge

section JfFacts

private lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

private lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ Filter.const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

private lemma IsBoundedAtImInfty.mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
    (h : IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)) :
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m') := by
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hshape]
  exact h.mul (isBoundedAtImInfty_discPow (m' - m))

variable {jf : ℍ → ℂ}
  (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
include hjf

private lemma mdiff_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  have : jf = fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := funext hjf
  rw [this]
  exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
    ModularForm.discriminant_ne_zero

private lemma jf_smul (γ : SL(2, ℤ)) (τ : ℍ) : jf (γ • τ) = jf τ := by
  have hγ : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  rw [CuspForm.coe_discriminant] at hΔ
  rw [show (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ = γ • τ from rfl] at h4 hΔ
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  rw [hjf, hjf, h4, hΔ, zpow_ofNat, zpow_ofNat]
  field_simp

end JfFacts

section AdjoinFacts

variable {N : ℕ} [NeZero N] {jf : ℍ → ℂ} {fricke : (Fin 2 → ZMod N) → ℍ → ℂ}

omit [NeZero N] in

private lemma map_castRingHom_eq_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem'] at hγ
  rw [hγ, Matrix.SpecialLinearGroup.coe_one]

omit [NeZero N] in

private lemma mdiff_of_mem_adjoin
    (hjmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf)
    (hfmd : ∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v))
    {x : ℍ → ℂ}
    (hx : x ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v})) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) x := by
  induction hx using Algebra.adjoin_induction with
  | mem g hg =>
    rcases hg with rfl | ⟨v, hv, rfl⟩
    · exact hjmd
    · exact hfmd v hv
  | algebraMap r => exact mdifferentiable_const
  | add x y _ _ ihx ihy => exact ihx.add ihy
  | mul x y _ _ ihx ihy => exact ihx.mul ihy

omit [NeZero N] in

private lemma invariant_of_mem_adjoin
    (hjinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ), jf (γ • τ) = jf τ)
    (hfslash : ∀ (v : Fin 2 → ZMod N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ)
    {x : ℍ → ℂ}
    (hx : x ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    x (γ • τ) = x τ := by
  induction hx using Algebra.adjoin_induction with
  | mem g hg =>
    rcases hg with rfl | ⟨v, hv, rfl⟩
    · exact hjinv γ τ
    · rw [hfslash v γ τ, map_castRingHom_eq_one hγ, Matrix.vecMul_one]
  | algebraMap r => rfl
  | add x y _ _ ihx ihy => simp only [Pi.add_apply, ihx, ihy]
  | mul x y _ _ ihx ihy => simp only [Pi.mul_apply, ihx, ihy]

end AdjoinFacts

section GammaOrbit

variable {N : ℕ} [NeZero N]

private lemma mdiff_comp_smul {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ∘ (γ • ·)) := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ∣[(0 : ℤ)] γ) := hF.slash 0 _
  have h2 : F ∣[(0 : ℤ)] γ = F ∘ (γ • ·) := by
    funext τ
    simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
    rfl
  rwa [h2] at h1

variable (N) in

private def gammaOrbit (F : ℍ → ℂ)
    (hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∘ (γ • ·) = F) :
    (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N) → ℍ → ℂ :=
  Quotient.lift (fun γ : Matrix.SpecialLinearGroup (Fin 2) ℤ => F ∘ (γ • ·)) (by
    intro γ γ' hrel
    replace hrel : γ⁻¹ * γ' ∈ CongruenceSubgroup.Gamma N :=
      QuotientGroup.leftRel_apply.mp hrel
    have hconj : γ * (γ⁻¹ * γ') * γ⁻¹ ∈ CongruenceSubgroup.Gamma N :=
      (CongruenceSubgroup.Gamma_normal N).conj_mem _ hrel γ
    funext τ
    have h1 := congrFun (hFinv _ hconj) (γ • τ)
    simp only [Function.comp_apply] at h1 ⊢
    rw [← mul_smul, show γ * (γ⁻¹ * γ') * γ⁻¹ * γ = γ' by group] at h1
    exact h1.symm)

omit [NeZero N] in
private lemma gammaOrbit_mk (F : ℍ → ℂ)
    (hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∘ (γ • ·) = F)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    gammaOrbit N F hFinv (QuotientGroup.mk γ) = F ∘ (γ • ·) := rfl

omit [NeZero N] in
private lemma gammaOrbit_one (F : ℍ → ℂ)
    (hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∘ (γ • ·) = F) :
    gammaOrbit N F hFinv (QuotientGroup.mk 1) = F := by
  rw [gammaOrbit_mk]
  funext τ
  simp [one_smul]

variable (N) in

private def orbitPerm (γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Equiv.Perm (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N) where
  toFun := Quotient.map (· * γ₀) (by
    intro x y h
    replace h : x⁻¹ * y ∈ CongruenceSubgroup.Gamma N := QuotientGroup.leftRel_apply.mp h
    refine QuotientGroup.leftRel_apply.mpr ?_
    have := (CongruenceSubgroup.Gamma_normal N).conj_mem _ h γ₀⁻¹
    simpa [mul_assoc, mul_inv_rev] using this)
  invFun := Quotient.map (· * γ₀⁻¹) (by
    intro x y h
    replace h : x⁻¹ * y ∈ CongruenceSubgroup.Gamma N := QuotientGroup.leftRel_apply.mp h
    refine QuotientGroup.leftRel_apply.mpr ?_
    have := (CongruenceSubgroup.Gamma_normal N).conj_mem _ h γ₀
    simpa [mul_assoc, mul_inv_rev] using this)
  left_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ => simp [Quotient.map_mk, mul_assoc]
  right_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ => simp [Quotient.map_mk, mul_assoc]

omit [NeZero N] in
private lemma orbitPerm_mk (γ₀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    orbitPerm N γ₀ (QuotientGroup.mk γ) = QuotientGroup.mk (γ * γ₀) := rfl

omit [NeZero N] in
private lemma gammaOrbit_perm (F : ℍ → ℂ)
    (hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∘ (γ • ·) = F)
    (γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (q : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    gammaOrbit N F hFinv q (γ₀ • τ) = gammaOrbit N F hFinv (orbitPerm N γ₀ q) τ := by
  induction q using QuotientGroup.induction_on with
  | H γ =>
    rw [orbitPerm_mk, gammaOrbit_mk, gammaOrbit_mk]
    simp only [Function.comp_apply, mul_smul]

end GammaOrbit

section OrbitEngine

variable {I : Type*} [Fintype I] (h : I → ℍ → ℂ) (m : ℕ)

private def orbitCoeff (k : ℕ) : ℍ → ℂ := fun τ => (∏ i, (X - C (h i τ))).coeff k

private lemma coeff_X_sub_C_mul (a : ℂ) (p : Polynomial ℂ) (k : ℕ) :
    ((X - C a) * p).coeff k = (if k = 0 then 0 else p.coeff (k - 1)) - a * p.coeff k := by
  rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  congr 1
  cases k with
  | zero => simp [Polynomial.mul_coeff_zero]
  | succ k' => simp [Polynomial.coeff_X_mul]

omit [Fintype I] in
private lemma mdiff_orbitCoeff_prod (hhol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h i)) (s : Finset I)
    (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((fun τ : ℍ => (∏ i ∈ s, (X - C (h i τ))).coeff k) : ℍ → ℂ) := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    exact mdifferentiable_const
  | cons a s ha ih =>
    have hrw : ∀ τ : ℍ, (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff k =
        (if k = 0 then 0 else (∏ i ∈ s, (X - C (h i τ))).coeff (k - 1)) -
          h a τ * (∏ i ∈ s, (X - C (h i τ))).coeff k := by
      intro τ
      rw [Finset.prod_cons, coeff_X_sub_C_mul]
    simp only [hrw]
    cases k with
    | zero =>
      exact mdifferentiable_const.sub ((hhol a).mul (ih 0))
    | succ k' =>
      simp only [ite_eq_right (Nat.succ_ne_zero k'), Nat.add_sub_cancel]
      exact (ih k').sub ((hhol a).mul (ih (k' + 1)))

omit [Fintype I] in
private lemma bounded_orbitCoeff_prod
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) (s : Finset I) (k : ℕ) :
    IsBoundedAtImInfty (fun τ =>
      (∏ i ∈ s, (X - C (h i τ))).coeff k * CuspForm.discriminant τ ^ ((s.card - k) * m)) := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one, Finset.card_empty, Nat.zero_sub,
      Nat.zero_mul, pow_zero, mul_one]
    exact Filter.const_boundedAtFilter _ _
  | cons a s ha ih =>
    have hdeg : ∀ τ : ℍ, (∏ i ∈ s, (X - C (h i τ))).natDegree = s.card := by
      intro τ
      rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (h i τ))]
      simp
    cases k with
    | zero =>
      have hshape : (fun τ : ℍ =>
          (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff 0 *
            CuspForm.discriminant τ ^ (((Finset.cons a s ha).card - 0) * m)) = fun τ : ℍ =>
          -((h a τ * CuspForm.discriminant τ ^ m) *
            ((∏ i ∈ s, (X - C (h i τ))).coeff 0 *
              CuspForm.discriminant τ ^ ((s.card - 0) * m))) := by
        funext τ
        rw [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_left rfl, Finset.card_cons, Nat.sub_zero,
          Nat.sub_zero, zero_sub, show (s.card + 1) * m = m + s.card * m by ring, pow_add]
        ring
      rw [hshape]
      exact ((hbd a).mul (ih 0)).neg
    | succ k' =>
      rcases Nat.lt_or_ge s.card (k' + 1) with hk | hk
      · have hzero : ∀ τ : ℍ, (∏ i ∈ s, (X - C (h i τ))).coeff (k' + 1) = 0 := fun τ =>
          coeff_eq_zero_of_natDegree_lt (by rw [hdeg τ]; exact hk)
        have hshape : (fun τ : ℍ =>
            (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff (k' + 1) *
              CuspForm.discriminant τ ^ (((Finset.cons a s ha).card - (k' + 1)) * m)) =
            fun τ : ℍ =>
            (∏ i ∈ s, (X - C (h i τ))).coeff k' *
              CuspForm.discriminant τ ^ ((s.card - k') * m) := by
          funext τ
          rw [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_right (Nat.succ_ne_zero k'),
            Nat.add_sub_cancel, hzero τ, mul_zero, sub_zero, Finset.card_cons,
            Nat.succ_sub_succ]
        rw [hshape]
        exact ih k'
      · have he2 : (s.card - k') * m = m + (s.card - (k' + 1)) * m := by
          have h1 : s.card - k' = 1 + (s.card - (k' + 1)) := by omega
          rw [h1]
          ring
        have hshape : (fun τ : ℍ =>
            (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff (k' + 1) *
              CuspForm.discriminant τ ^ (((Finset.cons a s ha).card - (k' + 1)) * m)) =
            fun τ : ℍ =>
            ((∏ i ∈ s, (X - C (h i τ))).coeff k' *
              CuspForm.discriminant τ ^ ((s.card - k') * m)) -
            ((h a τ * CuspForm.discriminant τ ^ m) *
              ((∏ i ∈ s, (X - C (h i τ))).coeff (k' + 1) *
                CuspForm.discriminant τ ^ ((s.card - (k' + 1)) * m))) := by
          funext τ
          rw [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_right (Nat.succ_ne_zero k'),
            Nat.add_sub_cancel, Finset.card_cons, Nat.succ_sub_succ, sub_mul]
          congr 1
          rw [he2, pow_add]
          ring
        rw [hshape]
        exact (ih k').sub ((hbd a).mul (ih (k' + 1)))

private theorem orbitCoeff_slash_invariant
    (hperm : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (k : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    orbitCoeff h k ∣[(0 : ℤ)] γ = orbitCoeff h k := by
  obtain ⟨σ, hσ⟩ := hperm γ
  funext τ
  simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
  show (∏ i, (X - C (h i (γ • τ)))).coeff k = (∏ i, (X - C (h i τ))).coeff k
  refine congrArg (fun p : Polynomial ℂ => p.coeff k) ?_
  calc ∏ i, (X - C (h i (γ • τ)))
      = ∏ i, (X - C (h (σ i) τ)) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hσ i τ]
    _ = ∏ i, (X - C (h i τ)) := Equiv.prod_comp σ (fun i' => X - C (h i' τ))

variable {jf : ℍ → ℂ}

private theorem exists_poly_j_orbitCoeff
    (hR3 : ∀ (m' : ℕ) (g : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, g ∣[(0 : ℤ)] γ = g) →
      IsBoundedAtImInfty (g * ModularForm.discriminant ^ m') →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m' ∧ g = fun τ => P.eval (jf τ))
    (hperm : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (hhol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h i))
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) (k : ℕ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ (Fintype.card I - k) * m ∧
      orbitCoeff h k = fun τ => P.eval (jf τ) := by
  refine hR3 ((Fintype.card I - k) * m) (orbitCoeff h k)
    (mdiff_orbitCoeff_prod h hhol Finset.univ k)
    (orbitCoeff_slash_invariant h hperm k) ?_
  have hb := bounded_orbitCoeff_prod h m hbd Finset.univ k
  rw [Finset.card_univ] at hb
  have hshape : ((orbitCoeff h k * ModularForm.discriminant ^ ((Fintype.card I - k) * m)
      : ℍ → ℂ)) =
      fun τ : ℍ => (∏ i, (X - C (h i τ))).coeff k *
        CuspForm.discriminant τ ^ ((Fintype.card I - k) * m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, orbitCoeff, ← CuspForm.coe_discriminant]
  rw [hshape]
  exact hb

private theorem orbit_integral_over_j
    (hR3 : ∀ (m' : ℕ) (g : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, g ∣[(0 : ℤ)] γ = g) →
      IsBoundedAtImInfty (g * ModularForm.discriminant ^ m') →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m' ∧ g = fun τ => P.eval (jf τ))
    (hperm : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (hhol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h i))
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) :
    ∃ P : ℕ → Polynomial ℂ, (∀ k, (P k).natDegree ≤ (Fintype.card I - k) * m) ∧
      ∀ (i : I) (τ : ℍ), h i τ ^ Fintype.card I +
        ∑ k ∈ Finset.range (Fintype.card I),
          Polynomial.eval (jf τ) (P k) * h i τ ^ k = 0 := by
  choose P hPdeg hP using fun k => exists_poly_j_orbitCoeff h m hR3 hperm hhol hbd k
  refine ⟨P, hPdeg, fun i τ => ?_⟩
  set Q : Polynomial ℂ := ∏ i', (X - C (h i' τ)) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun i' _ => monic_X_sub_C (h i' τ)
  have hQdeg : Q.natDegree = Fintype.card I := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun i' _ => monic_X_sub_C (h i' τ))]
    simp
  have hroot : Polynomial.eval (h i τ) Q = 0 := by
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hexp := Polynomial.eval_eq_sum_range' (n := Fintype.card I + 1)
    (by rw [hQdeg]; exact Nat.lt_succ_self _) (h i τ) (p := Q)
  rw [Finset.sum_range_succ] at hexp
  have hlead : Q.coeff (Fintype.card I) = 1 := by
    have := hQmonic.coeff_natDegree
    rwa [hQdeg] at this
  have hcoeffs : ∀ k, Q.coeff k = Polynomial.eval (jf τ) (P k) := by
    intro k
    have := congrFun (hP k) τ
    simpa [orbitCoeff, hQ] using this
  rw [hroot.symm, hexp, hlead, one_mul, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hcoeffs k]

end OrbitEngine

section HeadThree

private theorem exists_monicRel_j_of_mdifferentiable_levelFraction_of_deps
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (hR3 : ∀ (m' : ℕ) (g : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
      (∀ γ : SL(2, ℤ), g ∣[(0 : ℤ)] γ = g) →
      IsBoundedAtImInfty (g * ModularForm.discriminant ^ m') →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m' ∧ g = fun τ => P.eval (jf τ))
    (hR4a : ∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v))
    (hR4c : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ)
    {a b F : ℍ → ℂ}
    (ha : a ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb : b ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb0 : b ≠ 0)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hFb : F * b = a)
    (hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ModularForm.discriminant ^ m)) :
    ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), ∀ τ : ℍ,
      F τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * F τ ^ (i : ℕ) = 0 := by
  have _hL := hL
  have _hW := hW
  have _hfricke := hfricke
  classical

  have hbmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b := mdiff_of_mem_adjoin (mdiff_jf hjf) hR4a hb
  have hainv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, a (γ • τ) = a τ := fun γ hγ τ =>
    invariant_of_mem_adjoin (fun γ' τ' => jf_smul hjf γ' τ') hR4c ha hγ τ
  have hbinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, b (γ • τ) = b τ := fun γ hγ τ =>
    invariant_of_mem_adjoin (fun γ' τ' => jf_smul hjf γ' τ') hR4c hb hγ τ

  have hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∘ (γ • ·) = F := by
    intro γ hγ
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ∘ (γ • ·) - F) :=
      (mdiff_comp_smul hF γ).sub hF
    have hprod : (F ∘ (γ • ·) - F) * b = 0 := by
      funext τ
      have h1 : F (γ • τ) * b (γ • τ) = a (γ • τ) := congrFun hFb (γ • τ)
      have h2 : F τ * b τ = a τ := congrFun hFb τ
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, Function.comp_apply]
      rw [sub_mul, h2]
      rw [show F (γ • τ) * b τ = F (γ • τ) * b (γ • τ) by rw [hbinv γ hγ τ], h1,
        hainv γ hγ τ, sub_self]
    rcases mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero hdiff hbmd hprod with h | h
    · funext τ
      have := congrFun h τ
      simpa [sub_eq_zero] using this
    · exact absurd h hb0

  haveI : Fintype (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N) := Fintype.ofFinite _
  set orb := gammaOrbit N F (fun γ hγ => hFinv γ hγ) with horb
  have hperm : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ σ : Equiv.Perm (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N),
        ∀ q τ, orb q (γ • τ) = orb (σ q) τ :=
    fun γ => ⟨orbitPerm N γ, fun q τ => gammaOrbit_perm F _ γ q τ⟩
  have hhol : ∀ q, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (orb q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ => exact mdiff_comp_smul hF γ

  choose mq hmq using fun q : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N => hpb q.out
  set M := Finset.univ.sup mq with hM
  have hbd : ∀ q, IsBoundedAtImInfty (orb q * ⇑CuspForm.discriminant ^ M) := by
    intro q
    have hq : orb q = F ∘ (q.out • ·) := by
      conv_lhs => rw [horb, ← Quotient.out_eq q]
      rfl
    have h1 : IsBoundedAtImInfty ((F ∘ (q.out • ·)) * ⇑CuspForm.discriminant ^ mq q) := by
      rw [CuspForm.coe_discriminant]
      exact hmq q
    rw [hq]
    exact IsBoundedAtImInfty.mul_discPow_mono (Finset.le_sup (Finset.mem_univ q)) h1

  obtain ⟨P, -, hP⟩ := orbit_integral_over_j orb M hR3 hperm hhol hbd
  set d := Fintype.card (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N) with hd
  refine ⟨d, fun i => P (i : ℕ), fun τ => ?_⟩
  have h1 := hP (QuotientGroup.mk 1) τ
  rw [show orb (QuotientGroup.mk 1) = F from gammaOrbit_one F _] at h1
  have h2 : (∑ i : Fin d, (P (i : ℕ)).eval (jf τ) * F τ ^ (i : ℕ))
      = ∑ k ∈ Finset.range d, Polynomial.eval (jf τ) (P k) * F τ ^ k :=
    Fin.sum_univ_eq_sum_range (fun k => Polynomial.eval (jf τ) (P k) * F τ ^ k) d
  rw [h2]
  exact h1

end HeadThree

end WLight

open UpperHalfPlane hiding I in
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm in
open _root_.WLight WLight in
theorem _root_.WLight.exists_monicRel_j_of_mdifferentiable_levelFraction
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    {a b F : ℍ → ℂ}
    (ha : a ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb : b ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb0 : b ≠ 0)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hFb : F * b = a)
    (hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ModularForm.discriminant ^ m)) :
    ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), ∀ τ : ℍ,
      F τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * F τ ^ (i : ℕ) = 0 := by
  refine exists_monicRel_j_of_mdifferentiable_levelFraction_of_deps N L hL W hW fricke hfricke
      jf hjf ?_ ?_ ?_ ha hb hb0 hF hFb hpb
  · intro m' g hg hinv hbd
    obtain ⟨P, hdeg, heq⟩ := levelOne_hauptmodul_package.1 m' g hg hinv hbd
    refine ⟨P, hdeg, ?_⟩
    rw [show (fun τ : ℍ => P.eval (jf τ))
        = fun τ : ℍ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P from
      funext fun τ => by rw [hjf τ]]
    exact heq
  · intro v hv
    rw [show fricke v = fun τ : ℍ =>
        -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
          (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ * PeriodPair.weierstrassP (L τ)
            ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))) from
      funext fun τ => by rw [hfricke, hW]]
    exact (frickeFunction_modularity_package N L hL).2.2.1 v hv
  · intro v γ τ
    have hfeq : ∀ w : Fin 2 → ZMod N, fricke w = fun τ : ℍ =>
        -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
          (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ * PeriodPair.weierstrassP (L τ)
            ((((w 0).val : ℂ) * (τ : ℂ) + ((w 1).val : ℂ)) / (N : ℂ))) :=
      fun w => funext fun τ' => by rw [hfricke, hW]
    rw [hfeq, hfeq]
    exact (frickeFunction_modularity_package N L hL).1 v γ τ
end
end WLightS9.S_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction
