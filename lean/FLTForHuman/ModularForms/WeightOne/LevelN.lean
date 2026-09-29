/-
  The level-`N` structure and `sigmaTransport` packages (SET-9 order 2).

  Statements verbatim from the pinned wrappers
  `Theorems/Thm_WLight_{levelN_structure_package,
  exists_monicRel_j_K_of_mdifferentiable_frickeQuotient}.lean` and
  `Theorems/Thm_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.lean`;
  proofs transcribed from the matching `P2M/Sol/S_*` files (1,239 + 1,388 +
  739 lines) and adapted to mathlib `v4.34.0`.

  Each pin file's helpers stay `private` in the pin's own namespace (renamed
  `WLightS9.*` / the pin's `FrickeTransport`), so the three packages' repeated
  vocabulary does not collide; the three headlines are the module's only public
  surface.  The package-to-package edges are the pin's own and consume order 1's
  `WLight.exists_monicRel_j_of_mdifferentiable_levelFraction`,
  `WLight.qExpansion_sigmaTransport_package` and
  `WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction`, SET-5's
  `UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem` and SET-8's
  `WLight.exists_mdifferentiable_div_of_monicRel`.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_levelN_structure_package.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.lean

  The pin's local `set_option maxHeartbeats`/`synthInstance.maxHeartbeats` bumps
  are **not** transcribed (the project's global `maxHeartbeats` cap is 4,000,000).
-/

import FLTForHuman.ModularForms.WeightOne.Basic
import FLTForHuman.ModularForms.WeightOne.MonicRel
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import FLTForHuman.ModularForms.WeightOne.FrickeFunction
import FLTForHuman.ModularForms.WeightOne.LevelFraction
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
import FLTForHuman.ModularForms.WeightOne.Defs.PeriodPair
import FLTForHuman.ModularForms.WeightOne.Defs.PTorsion
import FLTForHuman.ModularForms.WeightOne.Defs.Gamma
import FLTForHuman.ModularForms.WeightOne.Fricke
import FLTForHuman.ModularForms.DiscPow
import FLTForHuman.ModularForms.WeightOne.LevelField
import FLTForHuman.ModularForms.WeightOne.Defs.RatAt
open X1DiamondRational
open UpperHalfPlaneAux
open WLight
open WLight.WLightFriIntBC.R8b
set_option autoImplicit false
-- The pin's `haveI` walls are load-bearing; keep them literal (cf. `Basic.lean`).
set_option linter.style.haveILetI false

namespace WLightS9.S_WLight_levelN_structure_package

set_option autoImplicit false
noncomputable section
open Complex Real

open scoped UpperHalfPlane Manifold MatrixGroups ModularForm in
open _root_.WLight WLight in
theorem _root_.WLight.levelN_structure_package
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    let A_N : Subalgebra ℂ (ℍ → ℂ) := Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v})
    let vecMul : (Fin 2 → ZMod N) → SL(2, ℤ) → Fin 2 → ZMod N := fun v γ ↦
      Matrix.vecMul v ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))
    ({γ : SL(2, ℤ) | ∀ v : Fin 2 → ZMod N, v ≠ 0 → fricke (vecMul v γ) = fricke v} =
      {γ : SL(2, ℤ) | γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N})
    ∧ (∀ a b : ℍ → ℂ, a ∈ A_N → b ∈ A_N → b ≠ 0 →
        (∀ γ : SL(2, ℤ), a * (b ∘ (γ • ·)) = (a ∘ (γ • ·)) * b) →
        ∃ p q : Polynomial ℂ, q ≠ 0 ∧ a * (fun τ ↦ q.eval (jf τ)) = b * (fun τ ↦ p.eval (jf τ)))
    ∧ (∀ v : Fin 2 → ZMod N, v ≠ 0 → ∃ d : ℕ, ∃ c : ℕ → Polynomial ℂ,
        ∀ τ, fricke v τ ^ d
          + ∑ k ∈ Finset.range d, (c k).eval (jf τ) * fricke v τ ^ k = 0)
    ∧ (∀ P : Polynomial ℂ, (∀ τ : ℍ, P.eval (jf τ) = 0) → P = 0)
    ∧ (∀ F ∈ A_N, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    ∧ (∀ a b : ℍ → ℂ, a ∈ A_N → b ∈ A_N → a * b = 0 → a = 0 ∨ b = 0) := by

  obtain rfl : jf = j := funext fun τ ↦ hjf τ
  have hLp : ∀ τ, L τ = periodPairOfTau τ :=
    fun τ ↦ periodPair_eq_of_ω _ _ (hL τ).1 (hL τ).2
  obtain rfl : fricke = frickeF N := funext₂ fun v τ ↦ by
    rw [hfricke, hW, hLp]; rfl
  intro A_N vecMul
  have hAN : A_N = levelRing N := by
    simp only [A_N]
    congr 1
    refine congrArg (insert j) (Set.ext fun g ↦ ?_)
    exact ⟨fun ⟨v, hv, hg⟩ ↦ ⟨⟨v, hv⟩, hg.symm⟩, fun ⟨i, hi⟩ ↦ ⟨i.1, i.2, hi.symm⟩⟩
  have hvm : vecMul = vecMulSL N := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hvm]
    ext γ
    simp only [Set.mem_ofPred_eq]
    rw [← mem_levelFixer_iff_pm γ, mem_levelFixer_iff_frickeF γ]
    exact ⟨fun h i τ ↦ (frickeF_slash i.1 γ τ).trans (congrFun (h i.1 i.2) τ),
      fun h v hv ↦ funext fun τ ↦ (frickeF_slash v γ τ).symm.trans (h ⟨v, hv⟩ τ)⟩
  ·
    intro a b haA hbA hb0 hinv; rw [hAN] at haA hbA
    exact r5_fixed_frac_polynomial haA hbA hb0 hinv
  ·
    intro v hv
    obtain ⟨P, hrel⟩ := frickeF_integral_over_j N
    exact ⟨_, P, hrel ⟨v, hv⟩⟩
  ·
    intro P hP
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    rw [show {x : ℂ | P.IsRoot x} = Set.univ from Set.eq_univ_of_forall fun c ↦ by
      obtain ⟨τ, hτ⟩ := j_surjective c
      exact hτ ▸ hP τ]
    exact Set.infinite_univ
  ·
    intro F hF; rw [hAN] at hF; exact levelRing_le_HolFn N hF
  ·
    intro a b haA hbA hab; rw [hAN] at haA hbA
    exact HolFn.eq_zero_or_eq_zero_of_mul_eq_zero (levelRing_le_HolFn N haA)
      (levelRing_le_HolFn N hbA) hab
end
end WLightS9.S_WLight_levelN_structure_package


namespace WLightS9.S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient

set_option autoImplicit false

noncomputable section

open _root_.Complex _root_.Real _root_.UpperHalfPlane _root_.Function _root_.Filter _root_.Polynomial _root_.Real.Polynomial
open scoped _root_.Complex _root_.Real _root_.UpperHalfPlane _root_.Function _root_.Filter _root_.Polynomial _root_.Real.Polynomial
open scoped Topology Manifold MatrixGroups ModularForm

namespace WLight
open _root_.WLight
open _root_.WLight
open scoped _root_.WLight

section Descent

private lemma exists_K_point_of_C_point (K : IntermediateField ℚ ℂ) {n q : ℕ}
    (A : Fin q → Fin n → ↥K) (bv : Fin q → ↥K) (x : Fin n → ℂ)
    (hx : ∀ j, ∑ i, (A j i : ℂ) * x i = (bv j : ℂ)) :
    ∃ y : Fin n → ↥K, ∀ j, ∑ i, A j i * y i = bv j := by
  classical
  set cols : Fin n → (Fin q → ↥K) := fun i j => A j i with hcols
  have hmem : bv ∈ Submodule.span ↥K (Set.range cols) := by
    by_contra hbv
    set W : Submodule ↥K (Fin q → ↥K) := Submodule.span ↥K (Set.range cols) with hW
    have hq0 : W.mkQ bv ≠ 0 := by
      intro h0
      exact hbv ((Submodule.Quotient.mk_eq_zero W).mp (by simpa using h0))
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ↥K ((Fin q → ↥K) ⧸ W), φ (W.mkQ bv) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hq0 ((Module.forall_dual_apply_eq_zero_iff ↥K _).mp hall)
    set f : (Fin q → ↥K) →ₗ[↥K] ↥K := φ.comp W.mkQ with hf
    have hfcols : ∀ i, f (cols i) = 0 := by
      intro i
      have hmem' : cols i ∈ W := Submodule.subset_span (Set.mem_range_self i)
      simp only [hf, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [(Submodule.Quotient.mk_eq_zero W).mpr hmem', map_zero]
    set c : Fin q → ↥K := fun j => f (fun j' => if j = j' then 1 else 0) with hc
    have hf_eq : ∀ w : Fin q → ↥K, f w = ∑ j, w j * c j := by
      intro w
      conv_lhs => rw [pi_eq_sum_univ w]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    have h1 : ∀ i, ∑ j, (A j i : ℂ) * (c j : ℂ) = 0 := by
      intro i
      have h0 : (∑ j, A j i * c j : ↥K) = 0 := by
        have := hfcols i
        rwa [hf_eq] at this
      have h0' := congrArg (fun z : ↥K => (z : ℂ)) h0
      push_cast at h0'
      exact h0'
    have hC : ((f bv : ↥K) : ℂ) = 0 := by
      rw [hf_eq]
      push_cast
      have h3 : ∑ j, (bv j : ℂ) * (c j : ℂ) =
          ∑ j, (∑ i, (A j i : ℂ) * x i) * (c j : ℂ) :=
        Finset.sum_congr rfl fun j _ => by rw [hx j]
      rw [h3]
      have h4 : ∑ j, (∑ i, (A j i : ℂ) * x i) * (c j : ℂ) =
          ∑ i, x i * ∑ j, (A j i : ℂ) * (c j : ℂ) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [h4]
      simp [h1]
    have hfbv : f bv = 0 := by exact_mod_cast hC
    exact hφ (by simpa [hf] using hfbv)
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ↥K).mp hmem
  refine ⟨y, fun j => ?_⟩
  have := congrFun hy j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcols] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Descent

section GlueBFold

open ModularForm

namespace R8cGlue

section Kit

variable {N : ℕ}

private lemma jf_smul {jf : ℍ → ℂ} (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (γ : SL(2, ℤ)) (τ : ℍ) : jf (γ • τ) = jf τ := by
  have hγ : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  rw [CuspForm.coe_discriminant] at hΔ
  rw [show (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ = γ • τ from rfl] at h4 hΔ
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  rw [hjf, hjf, h4, hΔ, zpow_ofNat, zpow_ofNat]
  field_simp

variable (jf : ℍ → ℂ) (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)

private def gen : Option {v : Fin 2 → ZMod N // v ≠ 0} → ℍ → ℂ :=
  fun o => o.elim jf fun v => fricke v.1

variable {jf fricke}

private def genPerm (γ : SL(2, ℤ)) :
    Option {v : Fin 2 → ZMod N // v ≠ 0} → Option {v : Fin 2 → ZMod N // v ≠ 0} :=
  Option.map fun v => ⟨Matrix.vecMul v.1
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)), by
    intro h
    apply v.2
    have := congrArg (fun w => Matrix.vecMul w
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ⁻¹ :
        Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) h
    simp only [Matrix.zero_vecMul, Matrix.vecMul_vecMul] at this
    rwa [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one] at this⟩

private lemma aeval_gen_comp_smul {R : Type*} [CommSemiring R] [Algebra R ℂ]
    (hjinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), jf (γ • τ) = jf τ)
    (hfslash : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ)
    (γ : SL(2, ℤ)) (P : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) R) :
    (MvPolynomial.aeval (gen jf fricke) P : ℍ → ℂ) ∘ (γ • ·) =
      MvPolynomial.aeval (gen jf fricke) (MvPolynomial.rename (genPerm γ) P) := by
  let Cγ : (ℍ → ℂ) →ₐ[R] (ℍ → ℂ) :=
    { toFun := fun F => F ∘ (γ • ·)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun r => by
        funext τ
        simp only [Function.comp_apply, Pi.algebraMap_apply] }
  have h1 : (MvPolynomial.aeval (gen jf fricke) P : ℍ → ℂ) ∘ (γ • ·) =
      Cγ (MvPolynomial.aeval (gen jf fricke) P) := rfl
  have h2 : (fun o => Cγ (gen jf fricke o)) = gen jf fricke ∘ genPerm γ := by
    funext o
    cases o with
    | none => funext τ; exact hjinv γ τ
    | some v => funext τ; exact hfslash v.1 γ τ
  rw [MvPolynomial.aeval_rename, h1, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, h2]

private lemma mem_adjoin_gen_iff {R : Type*} [CommRing R] [Algebra R ℂ] {x : ℍ → ℂ} :
    x ∈ Algebra.adjoin R (Set.range (gen jf fricke)) ↔
      ∃ P : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) R,
        MvPolynomial.aeval (gen jf fricke) P = x := by
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range]


end Kit

section Analysis

variable {N : ℕ}

private lemma eq_zero_of_forall_im_ge {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {A : ℝ}
    (h : ∀ τ : ℍ, A ≤ τ.im → f τ = 0) : f = 0 := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have han := hf.analyticOnNhd hU
  have hB : 0 < max A 0 + 1 := lt_of_le_of_lt (le_max_right A 0) (lt_add_one _)
  have hz₀ : (⟨0, max A 0 + 1⟩ : ℂ) ∈ {z : ℂ | 0 < z.im} := hB
  have hev : f ∘ ofComplex =ᶠ[𝓝 (⟨0, max A 0 + 1⟩ : ℂ)] 0 := by
    have hopen : IsOpen {z : ℂ | max A 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have hmem : (⟨0, max A 0 + 1⟩ : ℂ) ∈ {z : ℂ | max A 0 < z.im} := by
      show max A 0 < max A 0 + 1
      exact lt_add_one _
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : 0 < z.im := lt_of_le_of_lt (le_max_right A 0) hz
    simp only [Function.comp_apply, Pi.zero_apply, ofComplex_apply_of_im_pos hz']
    exact h ⟨z, hz'⟩ ((le_max_left A 0).trans (le_of_lt hz))
  have key := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected hz₀ hev
  funext τ
  have := key τ.im_pos
  simpa [ofComplex_apply] using this

private lemma exists_qParam_pow_le [NeZero N] {Q : ℍ → ℂ} (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Q)
    (hper : Function.Periodic (Q ∘ ofComplex) N) (hbd : IsBoundedAtImInfty Q) (hQ0 : Q ≠ 0) :
    ∃ (r : ℕ) (C A : ℝ), 0 < C ∧
      ∀ τ : ℍ, A ≤ τ.im → C * ‖Function.Periodic.qParam N τ‖ ^ r ≤ ‖Q τ‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hg : AnalyticAt ℂ (cuspFunction N Q) 0 := analyticAt_cuspFunction_zero hN hper hhol hbd
  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam N τ) atImInfty (𝓝 0) :=
    qParam_tendsto_atImInfty hN
  have heq : ∀ τ : ℍ, cuspFunction N Q (Function.Periodic.qParam N τ) = Q τ := fun τ =>
    eq_cuspFunction τ hN.ne' hper
  by_cases h0 : ∀ᶠ z in 𝓝 (0 : ℂ), cuspFunction N Q z = 0
  ·
    exfalso
    apply hQ0
    have h1 : ∀ᶠ τ : ℍ in atImInfty, Q τ = 0 :=
      (hq.eventually h0).mono fun τ hτ => by rwa [heq τ] at hτ
    rw [Filter.Eventually, atImInfty_mem] at h1
    obtain ⟨A, hA⟩ := h1
    exact eq_zero_of_forall_im_ge hhol hA
  · obtain ⟨r, u, hu, hu0, hfe⟩ := hg.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h0
    have hpos : 0 < ‖u 0‖ / 2 := by positivity
    have hu_lb : ∀ᶠ z in 𝓝 (0 : ℂ), ‖u 0‖ / 2 ≤ ‖u z‖ := by
      have ht : Tendsto (fun z => ‖u z‖) (𝓝 0) (𝓝 ‖u 0‖) := hu.continuousAt.norm
      exact (ht.eventually_const_lt (half_lt_self (norm_pos_iff.mpr hu0))).mono fun z hz => hz.le
    have hloc : ∀ᶠ z in 𝓝 (0 : ℂ), ‖u 0‖ / 2 * ‖z‖ ^ r ≤ ‖cuspFunction N Q z‖ := by
      filter_upwards [hfe, hu_lb] with z hz hz'
      rw [hz, sub_zero, norm_smul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left hz' (pow_nonneg (norm_nonneg _) _)
    have hev : ∀ᶠ τ : ℍ in atImInfty,
        ‖u 0‖ / 2 * ‖Function.Periodic.qParam N τ‖ ^ r ≤ ‖Q τ‖ :=
      (hq.eventually hloc).mono fun τ hτ => by rwa [heq τ] at hτ
    rw [Filter.Eventually, atImInfty_mem] at hev
    obtain ⟨A, hA⟩ := hev
    exact ⟨r, ‖u 0‖ / 2, A, hpos, fun τ hτ => hA τ hτ⟩

private lemma map_T_pow_eq_one :
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (ModularGroup.T ^ (N : ℤ)) :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma periodic_comp_ofComplex_of_T {x : ℍ → ℂ}
    (h : ∀ τ : ℍ, x (ModularGroup.T ^ (N : ℤ) • τ) = x τ) :
    Function.Periodic (x ∘ ofComplex) N := by
  intro w
  by_cases! hw : 0 < im w
  · have hw' : 0 < im (w + N) := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← h ⟨w, hw⟩]
    congr 1
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  · have hw' : im (w + N) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

end Analysis

section Quotient

variable {N : ℕ} [NeZero N] {jf : ℍ → ℂ} {fricke : (Fin 2 → ZMod N) → ℍ → ℂ}

private structure GenData (jf : ℍ → ℂ) (fricke : (Fin 2 → ZMod N) → ℍ → ℂ) : Prop where
  jmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf
  jbd : ∃ m : ℕ, IsBoundedAtImInfty (jf * ⇑CuspForm.discriminant ^ m)
  fmd : ∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v)
  fbd : ∀ v : Fin 2 → ZMod N, v ≠ 0 →
    ∃ m : ℕ, IsBoundedAtImInfty (fricke v * ⇑CuspForm.discriminant ^ m)
  jinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), jf (γ • τ) = jf τ
  fslash : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ),
    fricke v (γ • τ) = fricke (Matrix.vecMul v
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
        Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ

omit [NeZero N] in

private lemma adjoin_props (hg : GenData jf fricke) {x : ℍ → ℂ}
    (hx : x ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) x ∧
      (∃ m : ℕ, IsBoundedAtImInfty (x * ⇑CuspForm.discriminant ^ m)) ∧
      ∀ τ : ℍ, x (ModularGroup.T ^ (N : ℤ) • τ) = x τ := by
  induction hx using Algebra.adjoin_induction with
  | mem g hg' =>
    obtain ⟨o, rfl⟩ := hg'
    cases o with
    | none => exact ⟨hg.jmd, hg.jbd, fun τ => hg.jinv _ τ⟩
    | some v =>
      refine ⟨hg.fmd v.1 v.2, hg.fbd v.1 v.2, fun τ => ?_⟩
      show fricke v.1 _ = fricke v.1 τ
      rw [hg.fslash, map_T_pow_eq_one, Matrix.vecMul_one]
  | algebraMap c =>
    refine ⟨mdifferentiable_const, ⟨0, ?_⟩, fun τ => rfl⟩
    rw [pow_zero, mul_one]
    exact Filter.const_boundedAtFilter atImInfty c
  | add x y _ _ ihx ihy =>
    obtain ⟨hxm, ⟨m, hm⟩, hxT⟩ := ihx
    obtain ⟨hym, ⟨n, hn⟩, hyT⟩ := ihy
    refine ⟨hxm.add hym, ⟨max m n, ?_⟩, fun τ => by simp only [Pi.add_apply, hxT, hyT]⟩
    rw [add_mul]
    exact (IsBoundedAtImInfty.mul_discPow_mono (le_max_left m n) hm).add (IsBoundedAtImInfty.mul_discPow_mono (le_max_right m n) hn)
  | mul x y _ _ ihx ihy =>
    obtain ⟨hxm, ⟨m, hm⟩, hxT⟩ := ihx
    obtain ⟨hym, ⟨n, hn⟩, hyT⟩ := ihy
    refine ⟨hxm.mul hym, ⟨m + n, ?_⟩, fun τ => by simp only [Pi.mul_apply, hxT, hyT]⟩
    have : (x * y * ⇑CuspForm.discriminant ^ (m + n) : ℍ → ℂ) =
        (x * ⇑CuspForm.discriminant ^ m) * (y * ⇑CuspForm.discriminant ^ n) := by
      rw [pow_add]; ring
    rw [this]
    exact hm.mul hn

omit [NeZero N] in

private lemma comp_smul_mem_adjoin (hg : GenData jf fricke) (γ : SL(2, ℤ)) {x : ℍ → ℂ}
    (hx : x ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke))) :
    x ∘ (γ • ·) ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke)) := by
  rw [mem_adjoin_gen_iff] at hx ⊢
  obtain ⟨P, rfl⟩ := hx
  exact ⟨_, (aeval_gen_comp_smul hg.jinv hg.fslash γ P).symm⟩

private theorem exists_isBoundedAtImInfty_of_mul_eq (hg : GenData jf fricke) {h q p : ℍ → ℂ}
    (hq : q ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke)))
    (hp : p ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke))) (hq0 : q ≠ 0) (hhq : h * q = p) :
    ∃ m : ℕ, IsBoundedAtImInfty (h * ⇑CuspForm.discriminant ^ m) := by
  obtain ⟨hqm, ⟨mq, hmq⟩, hqT⟩ := adjoin_props hg hq
  obtain ⟨_, ⟨mp, hmp⟩, _⟩ := adjoin_props hg hp

  have hQhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (q * ⇑CuspForm.discriminant ^ mq) :=
    hqm.mul (mdiff_discPow mq)
  have hQper : Function.Periodic ((q * ⇑CuspForm.discriminant ^ mq : ℍ → ℂ) ∘ ofComplex) N :=
    (periodic_comp_ofComplex_of_T hqT).mul (periodic_discPow_comp_ofComplex mq N)
  have hQ0 : (q * ⇑CuspForm.discriminant ^ mq : ℍ → ℂ) ≠ 0 := by
    intro hz
    apply hq0
    funext τ
    have := congrFun hz τ
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff',
      ne_eq] at this
    rcases this with h1 | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 (ModularForm.discriminant_ne_zero τ)
  obtain ⟨r, C, A, hC, hlb⟩ := exists_qParam_pow_le hQhol hQper hmq hQ0

  obtain ⟨Mp, Ap, hMp⟩ := isBoundedAtImInfty_iff.mp hmp
  obtain ⟨MΔ, AΔ, hMΔ⟩ := isBoundedAtImInfty_iff.mp isBoundedAtImInfty_discriminant
  obtain ⟨c, hc, hcO⟩ := (CuspFormClass.exp_decay_atImInfty (h := 1) CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL).exists_pos
  have hcO' := hcO.bound
  rw [Filter.Eventually, atImInfty_mem] at hcO'
  obtain ⟨Ac, hAc⟩ := hcO'
  refine ⟨mp + r, isBoundedAtImInfty_iff.mpr ⟨Mp * c ^ r * MΔ ^ mq / C,
    max (max A Ap) (max AΔ Ac), fun τ hτ => ?_⟩⟩
  have hA' : A ≤ τ.im := (le_max_left _ _).trans ((le_max_left _ _).trans hτ)
  have hAp' : Ap ≤ τ.im := (le_max_right _ _).trans ((le_max_left _ _).trans hτ)
  have hAΔ' : AΔ ≤ τ.im := (le_max_left _ _).trans ((le_max_right _ _).trans hτ)
  have hAc' : Ac ≤ τ.im := (le_max_right _ _).trans ((le_max_right _ _).trans hτ)

  set a : ℝ := ‖Function.Periodic.qParam N τ‖ with ha
  set d : ℝ := ‖CuspForm.discriminant τ‖ with hd
  have ha0 : 0 < a := by rw [ha, norm_pos_iff]; exact Complex.exp_ne_zero _
  have hd0 : 0 ≤ d := norm_nonneg _
  have hB := hlb τ hA'
  have hBpos : 0 < ‖(q * ⇑CuspForm.discriminant ^ mq) τ‖ := lt_of_lt_of_le (by positivity) hB
  have hY : ‖(p * ⇑CuspForm.discriminant ^ mp) τ‖ ≤ Mp := hMp τ hAp'
  have hMp0 : 0 ≤ Mp := (norm_nonneg _).trans hY
  have hdM : d ≤ MΔ := hMΔ τ hAΔ'
  have hMΔ0 : 0 ≤ MΔ := hd0.trans hdM

  have hde : d ≤ c * a := by
    have h1 : d ≤ c * ‖Real.exp (-2 * π * τ.im / 1)‖ := hAc τ hAc'
    have h2 : Real.exp (-2 * π * τ.im / 1) ≤ a := by
      rw [ha, Function.Periodic.norm_qParam]
      apply Real.exp_le_exp.mpr
      rw [div_one, UpperHalfPlane.coe_im]
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
      have hN0 : (0 : ℝ) < N := one_pos.trans_le hN1
      rw [div_eq_mul_inv, neg_mul, neg_mul, neg_mul, neg_le_neg_iff]
      have : 2 * π * τ.im * (N : ℝ)⁻¹ ≤ 2 * π * τ.im * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [inv_le_one_iff₀]
        exact Or.inr hN1
      simpa using this
    calc d ≤ c * ‖Real.exp (-2 * π * τ.im / 1)‖ := h1
      _ = c * Real.exp (-2 * π * τ.im / 1) := by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ c * a := mul_le_mul_of_nonneg_left h2 hc.le

  have hX : ‖(h * ⇑CuspForm.discriminant ^ (mp + r)) τ‖ * ‖(q * ⇑CuspForm.discriminant ^ mq) τ‖
      = ‖(p * ⇑CuspForm.discriminant ^ mp) τ‖ * d ^ r * d ^ mq := by
    rw [← hhq]
    simp only [Pi.mul_apply, Pi.pow_apply, norm_mul, norm_pow, hd, pow_add]
    ring
  have hnum0 : 0 ≤ ‖(p * ⇑CuspForm.discriminant ^ mp) τ‖ * d ^ r * d ^ mq := by positivity
  calc ‖(h * ⇑CuspForm.discriminant ^ (mp + r)) τ‖
      = ‖(p * ⇑CuspForm.discriminant ^ mp) τ‖ * d ^ r * d ^ mq /
          ‖(q * ⇑CuspForm.discriminant ^ mq) τ‖ := by
        rw [eq_div_iff hBpos.ne', hX]
    _ ≤ ‖(p * ⇑CuspForm.discriminant ^ mp) τ‖ * d ^ r * d ^ mq / (C * a ^ r) :=
        div_le_div_of_nonneg_left hnum0 (by positivity) hB
    _ ≤ Mp * (c * a) ^ r * MΔ ^ mq / (C * a ^ r) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul (mul_le_mul hY (pow_le_pow_left₀ hd0 hde r) (by positivity) hMp0)
          (pow_le_pow_left₀ hd0 hdM mq) (by positivity) (by positivity)
    _ = Mp * c ^ r * MΔ ^ mq / C := by
        rw [mul_pow]
        field_simp

private theorem isBoundedAtImInfty_smul_quotient_of_aeval
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
    (hR4c : ∀ (v : Fin 2 → ZMod N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ)
    (hR4b12 : (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf ∧
        ∃ m : ℕ, IsBoundedAtImInfty (jf * ModularForm.discriminant ^ m)) ∧
      (∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) ∧
        ∃ m : ℕ, IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ m)))
    {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P₀ Q₀ : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q₀.map (algebraMap ↥K ℂ)) ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (Q₀.map (algebraMap ↥K ℂ)) =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (P₀.map (algebraMap ↥K ℂ))) :
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ m : ℕ,
      IsBoundedAtImInfty ((G ∘ (γ • ·)) * ModularForm.discriminant ^ m) := by
  have _hL := hL
  have _hW := hW
  have _hfricke := hfricke
  have _hK := hK
  have _hG := hG
  intro γ
  have hg : GenData jf fricke := ⟨hR4b12.1.1, by simpa only [CuspForm.coe_discriminant] using
    hR4b12.1.2, fun v hv => (hR4b12.2 v hv).1, fun v hv => by
      simpa only [CuspForm.coe_discriminant] using (hR4b12.2 v hv).2, jf_smul hjf, hR4c⟩
  have hgen : (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} => o.elim jf fun v => fricke v.1) =
      gen jf fricke := rfl
  rw [hgen] at hQ0 hGQ
  set q : ℍ → ℂ := MvPolynomial.aeval (gen jf fricke) (Q₀.map (algebraMap ↥K ℂ)) with hqdef
  set p : ℍ → ℂ := MvPolynomial.aeval (gen jf fricke) (P₀.map (algebraMap ↥K ℂ)) with hpdef
  have hqmem : q ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke)) := mem_adjoin_gen_iff.mpr ⟨_, rfl⟩
  have hpmem : p ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke)) := mem_adjoin_gen_iff.mpr ⟨_, rfl⟩
  have hq0' : q ∘ (γ • ·) ≠ 0 := by
    intro hz
    apply hQ0
    funext τ
    have := congrFun hz (γ⁻¹ • τ)
    simpa only [comp_apply, smul_inv_smul, Pi.zero_apply] using this
  have hhq : (G ∘ (γ • ·)) * (q ∘ (γ • ·)) = p ∘ (γ • ·) := by
    funext τ
    exact congrFun hGQ (γ • τ)
  simpa only [CuspForm.coe_discriminant] using exists_isBoundedAtImInfty_of_mul_eq hg
    (comp_smul_mem_adjoin hg γ hqmem) (comp_smul_mem_adjoin hg γ hpmem) hq0' hhq

end Quotient

end R8cGlue

end GlueBFold

section QKitA

variable {N : ℕ}


end QKitA

section RatCoeff

open _root_.UpperHalfPlane _root_.ModularForm _root_.SlashInvariantForm _root_.ModularFormClass _root_.CuspForm _root_.ModularForm.CuspForm _root_.EisensteinSeries
open scoped _root_.UpperHalfPlane _root_.ModularForm _root_.SlashInvariantForm _root_.ModularFormClass _root_.CuspForm _root_.ModularForm.CuspForm _root_.EisensteinSeries
open scoped MatrixGroups ArithmeticFunction.sigma

end RatCoeff

section KPoleAlgebra

open ModularForm

variable {N : ℕ}

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

end KPoleAlgebra

section QKitB

open ModularForm

variable {N : ℕ} {K : IntermediateField ℚ ℂ}


end QKitB

section AevalKit

open ModularForm

variable {N : ℕ} {K : IntermediateField ℚ ℂ}

private lemma kPole_fricke [NeZero N] {fricke : (Fin 2 → ZMod N) → ℍ → ℂ}
    {v : Fin 2 → ZMod N}
    (hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v))
    (hper : Function.Periodic ((fricke v * ModularForm.discriminant ^ 1) ∘
      UpperHalfPlane.ofComplex) N)
    (hbd : IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ 1))
    (hmem : ∀ n : ℕ, (qExpansion N (fricke v * ModularForm.discriminant ^ 1)).coeff n ∈ K) :
    KPole K N (fricke v) := by
  have hsh : (fricke v * ⇑CuspForm.discriminant ^ 1 : ℍ → ℂ) =
      fricke v * ModularForm.discriminant ^ 1 := by
    funext τ
    simp only [Pi.mul_apply, pow_one]
    rw [congrFun CuspForm.coe_discriminant τ]
  exact ⟨hmd, 1, by rw [hsh]; exact hper, by rw [hsh]; exact hbd, by rw [hsh]; exact hmem⟩

private lemma kPole_aeval [NeZero N]
    {fricke : (Fin 2 → ZMod N) → ℍ → ℂ} {jf : ℍ → ℂ}
    (hkjf : KPole K N jf)
    (hkfr : ∀ v : {v : Fin 2 → ZMod N // v ≠ 0}, KPole K N (fricke v.1))
    (p : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K) :
    KPole K N (MvPolynomial.aeval
      (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} => o.elim jf fun v => fricke v.1)
      (p.map (algebraMap ↥K ℂ))) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
    have htower : (algebraMap ℂ (ℍ → ℂ)) ((algebraMap ↥K ℂ) c) =
        algebraMap ↥K (ℍ → ℂ) c := by
      rw [← IsScalarTower.algebraMap_apply]
    rw [htower]
    exact kPole_algebraMap c
  | add p q hp hq =>
    rw [map_add, map_add]
    exact KPole.add hp hq
  | mul_X p o hp =>
    rw [map_mul, MvPolynomial.map_X, map_mul, MvPolynomial.aeval_X]
    refine KPole.mul hp ?_
    cases o with
    | none => exact hkjf
    | some v => exact hkfr v

end AevalKit

end WLight

open _root_.WLight WLight WLight.R8cGlue in
theorem _root_.WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient
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
    (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P₀ Q₀ : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q₀.map (algebraMap ↥K ℂ)) ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (Q₀.map (algebraMap ↥K ℂ)) =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (P₀.map (algebraMap ↥K ℂ))) :
    ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0 := by

  have hR6h3 : ∀ {a b F : ℍ → ℂ},
      a ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) →
      b ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) →
      b ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → F * b = a →
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ m : ℕ,
        IsBoundedAtImInfty ((F ∘ (γ • ·)) * ModularForm.discriminant ^ m)) →
      ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), ∀ τ : ℍ,
        F τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * F τ ^ (i : ℕ) = 0 :=
    fun ha hb hb0 hF hFb hpb =>
      exists_monicRel_j_of_mdifferentiable_levelFraction N L hL W hW fricke hfricke jf hjf
        ha hb hb0 hF hFb hpb
  have hR7a : ∀ {ι : Type} (f : ι → ℍ → ℂ),
      (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i) ∧ ∃ m : ℕ,
        Function.Periodic ((f i * ModularForm.discriminant ^ m) ∘
          UpperHalfPlane.ofComplex) N ∧
        IsBoundedAtImInfty (f i * ModularForm.discriminant ^ m) ∧
        ∀ n : ℕ, (UpperHalfPlane.qExpansion N
          (f i * ModularForm.discriminant ^ m)).coeff n ∈ K) →
      LinearIndependent ↥K f → LinearIndependent ℂ f :=
    fun f hf hli => UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem N K f hf hli
  have hR4b12 : (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf ∧
        ∃ m : ℕ, IsBoundedAtImInfty (jf * ModularForm.discriminant ^ m)) ∧
      (∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) ∧
        ∃ m : ℕ, IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ m)) :=
    ⟨(frickeFunction_orbit_package N L hL W hW fricke hfricke jf hjf).1,
      (frickeFunction_orbit_package N L hL W hW fricke hfricke jf hjf).2.1⟩
  have hfeq : fricke = fun a τ =>
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
        (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
          PeriodPair.weierstrassP (L τ)
            ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ))) := by
    funext a τ; rw [hfricke, hW]
  have hR4a := frickeFunction_modularity_package N L hL
  dsimp only at hR4a
  have hR4c : ∀ (v : Fin 2 → ZMod N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ := by
    intro v γ τ; rw [hfeq]; exact hR4a.1 v γ τ
  have hQrat : ∀ v : Fin 2 → ZMod N, v ≠ 0 →
      Function.Periodic ((fricke v * ModularForm.discriminant ^ 1) ∘
        UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ 1) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N
        (fricke v * ModularForm.discriminant ^ 1)).coeff n ∈ K := by
    intro v hv; rw [pow_one, hfeq, hK]
    exact ⟨(hR4a.2.2.2.2.1 v hv).1, hR4a.2.2.2.1 v hv, (hR4a.2.2.2.2.1 v hv).2⟩
  clear hR4a
  classical
  set gen : Option {v : Fin 2 → ZMod N // v ≠ 0} → ℍ → ℂ :=
    fun o => o.elim jf fun v => fricke v.1 with hgen
  set Pt : ℍ → ℂ := MvPolynomial.aeval gen (P₀.map (algebraMap ↥K ℂ)) with hPt
  set Qt : ℍ → ℂ := MvPolynomial.aeval gen (Q₀.map (algebraMap ↥K ℂ)) with hQt

  have hkjf : KPole K N jf := kPole_jf K hjf
  have hkfr : ∀ v : {v : Fin 2 → ZMod N // v ≠ 0}, KPole K N (fricke v.1) := fun v =>
    kPole_fricke ((hR4b12.2 v.1 v.2).1) (hQrat v.1 v.2).1 (hQrat v.1 v.2).2.1
      (hQrat v.1 v.2).2.2
  have hkA : ∀ r : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K,
      KPole K N (MvPolynomial.aeval gen (r.map (algebraMap ↥K ℂ))) := fun r =>
    kPole_aeval hkjf hkfr r

  have hrange : Set.range gen =
      insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v} := by
    ext g
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Set.mem_insert _ _
      | some v => exact Set.mem_insert_of_mem _ ⟨v.1, v.2, rfl⟩
    · rintro (rfl | ⟨v, hv, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨v, hv⟩, rfl⟩
  have hmemA : ∀ r : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ,
      MvPolynomial.aeval gen r ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) := by
    intro r
    rw [← hrange, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨r, rfl⟩

  have hpb := R8cGlue.isBoundedAtImInfty_smul_quotient_of_aeval N L hL W hW fricke hfricke
    jf hjf K hK hR4c hR4b12 hG P₀ Q₀ hQ0 hGQ
  obtain ⟨d, p, hrel⟩ := hR6h3 (hmemA (P₀.map (algebraMap ↥K ℂ)))
    (hmemA (Q₀.map (algebraMap ↥K ℂ))) hQ0 hG hGQ hpb

  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · exfalso
    have h0 := hrel ⟨Complex.I, by simp⟩
    subst hd0
    simp at h0

  have hGQτ : ∀ τ : ℍ, G τ * Qt τ = Pt τ := fun τ => by
    have := congrFun hGQ τ
    simpa using this
  have hpow : ∀ (τ : ℍ) (k : ℕ), G τ ^ k * Qt τ ^ k = Pt τ ^ k := fun τ k => by
    rw [← mul_pow, hGQτ τ]
  set D : ℕ := (Finset.univ.sup fun i : Fin d => (p i).natDegree) + 1 with hD
  have hdeg : ∀ i : Fin d, (p i).natDegree < D := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i : Fin d => (p i).natDegree)
      (Finset.mem_univ i))
  have hcleared : ∀ τ : ℍ, Pt τ ^ d + ∑ i : Fin d, ∑ k ∈ Finset.range D,
      (p i).coeff k * (jf τ ^ k * (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ))) = 0 := by
    intro τ
    have h1 : (G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ)) * Qt τ ^ d = 0 := by
      rw [hrel τ, zero_mul]
    rw [add_mul, Finset.sum_mul] at h1
    have hterm : ∀ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) * Qt τ ^ d =
        ∑ k ∈ Finset.range D,
          (p i).coeff k * (jf τ ^ k * (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ))) := by
      intro i
      rw [Polynomial.eval_eq_sum_range' (hdeg i), Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsplit : Qt τ ^ d = Qt τ ^ (d - (i : ℕ)) * Qt τ ^ (i : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt i.2)]
      rw [hsplit]
      linear_combination (p i).coeff k * jf τ ^ k * Qt τ ^ (d - (i : ℕ)) * hpow τ (i : ℕ)
    calc Pt τ ^ d + ∑ i : Fin d, ∑ k ∈ Finset.range D,
          (p i).coeff k * (jf τ ^ k * (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ)))
        = G τ ^ d * Qt τ ^ d +
            ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) * Qt τ ^ d := by
          rw [hpow τ d]
          exact congrArg₂ (· + ·) rfl
            (Finset.sum_congr rfl fun i _ => (hterm i).symm)
      _ = 0 := h1

  set u : Option (Fin d × Fin D) → ℍ → ℂ := fun o => o.elim
    (MvPolynomial.aeval gen ((P₀ ^ d).map (algebraMap ↥K ℂ)))
    (fun ik => MvPolynomial.aeval gen
      ((MvPolynomial.X none ^ (ik.2 : ℕ) *
        (Q₀ ^ (d - (ik.1 : ℕ)) * P₀ ^ (ik.1 : ℕ))).map (algebraMap ↥K ℂ))) with hu
  have hu_top : ∀ τ : ℍ, u none τ = Pt τ ^ d := by
    intro τ
    simp only [hu, Option.elim, map_pow, Pi.pow_apply, hPt]
  have hu_mon : ∀ (ik : Fin d × Fin D) (τ : ℍ), u (some ik) τ =
      jf τ ^ (ik.2 : ℕ) * (Qt τ ^ (d - (ik.1 : ℕ)) * Pt τ ^ (ik.1 : ℕ)) := by
    intro ik τ
    simp only [hu, Option.elim, map_mul, map_pow, MvPolynomial.map_X,
      MvPolynomial.aeval_X, Pi.mul_apply, Pi.pow_apply, hPt, hQt, hgen]
  have hkU : ∀ o, KPole K N (u o) := by
    intro o
    cases o with
    | none => exact hkA _
    | some ik => exact hkA _

  set lam : Fin d × Fin D → ℂ := fun ik => (p ik.1).coeff ik.2 with hlam
  have hfunrel : u none + ∑ ik : Fin d × Fin D, lam ik • u (some ik) = 0 := by
    funext τ
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [hu_top τ]
    have hsum : ∑ ik : Fin d × Fin D, lam ik * u (some ik) τ =
        ∑ i : Fin d, ∑ k ∈ Finset.range D,
          (p i).coeff k * (jf τ ^ k * (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ))) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_range fun k => (p i).coeff k *
        (jf τ ^ k * (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ)))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hu_mon (i, k) τ, hlam]
    rw [hsum]
    exact hcleared τ

  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent ↥K (Set.range u)
  have hbfin : b.Finite := (Set.finite_range u).subset hbsub
  haveI : Fintype ↥b := hbfin.fintype
  have hdata : ∀ w : ↥b, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((w : ℍ → ℂ)) ∧ ∃ m : ℕ,
      Function.Periodic (((w : ℍ → ℂ) * ModularForm.discriminant ^ m) ∘
        UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty ((w : ℍ → ℂ) * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N
        ((w : ℍ → ℂ) * ModularForm.discriminant ^ m)).coeff n ∈ K := by
    intro w
    obtain ⟨o, ho⟩ := hbsub w.2
    obtain ⟨hmd, m, hper, hbd, hmem⟩ := ho ▸ hkU o
    have hsh : ((w : ℍ → ℂ) * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) =
        (w : ℍ → ℂ) * ModularForm.discriminant ^ m := by
      funext τ
      simp only [Pi.mul_apply, Pi.pow_apply]
      rw [congrFun CuspForm.coe_discriminant τ]
    rw [hsh] at hper hbd hmem
    exact ⟨hmd, m, hper, hbd, hmem⟩
  have hCind : LinearIndependent ℂ (fun w : ↥b => (w : ℍ → ℂ)) :=
    hR7a (fun w : ↥b => (w : ℍ → ℂ)) hdata hbind

  have hcoords : ∀ o, ∃ c : ↥b → ↥K, ∑ w : ↥b, c w • (w : ℍ → ℂ) = u o := by
    intro o
    have h1 : u o ∈ Submodule.span ↥K (Set.range ((↑) : b → ℍ → ℂ)) := by
      rw [Subtype.range_coe, hbspan]
      exact Submodule.subset_span (Set.mem_range_self o)
    exact (Submodule.mem_span_range_iff_exists_fun ↥K).mp h1
  choose co hco using hcoords

  have hKsmul : ∀ (c : ↥K) (g : ℍ → ℂ), c • g = (c : ℂ) • g := fun c g =>
    (algebraMap_smul ℂ c g).symm
  have hpiece : ∀ o, ∑ w : ↥b, (co o w : ℂ) • (w : ℍ → ℂ) = u o := by
    intro o
    rw [← hco o]
    exact Finset.sum_congr rfl fun w _ => (hKsmul _ _).symm
  have hsys : ∀ w : ↥b, (co none w : ℂ) +
      ∑ ik : Fin d × Fin D, lam ik * (co (some ik) w : ℂ) = 0 := by
    have hcomb : ∑ w : ↥b, ((co none w : ℂ) +
        ∑ ik : Fin d × Fin D, lam ik * (co (some ik) w : ℂ)) • (w : ℍ → ℂ) = 0 := by
      have hstep : ∑ w : ↥b, ((co none w : ℂ) +
          ∑ ik : Fin d × Fin D, lam ik * (co (some ik) w : ℂ)) • (w : ℍ → ℂ) =
          ∑ w : ↥b, (co none w : ℂ) • (w : ℍ → ℂ) +
          ∑ ik : Fin d × Fin D, lam ik •
            ∑ w : ↥b, (co (some ik) w : ℂ) • (w : ℍ → ℂ) := by
        simp only [add_smul, Finset.sum_smul, mul_smul]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ik _ => (Finset.smul_sum).symm
      rw [hstep, hpiece none]
      rw [Finset.sum_congr rfl fun ik _ => congrArg (lam ik • ·) (hpiece (some ik))]
      exact hfunrel
    intro w
    exact (Fintype.linearIndependent_iff.mp hCind) _ hcomb w

  set em : (Fin d × Fin D) ≃ Fin (Fintype.card (Fin d × Fin D)) :=
    Fintype.equivFin (Fin d × Fin D) with hem
  set eb : ↥b ≃ Fin (Fintype.card ↥b) := Fintype.equivFin ↥b with heb
  obtain ⟨y0, hy0⟩ := exists_K_point_of_C_point K
    (A := fun j i => co (some (em.symm i)) (eb.symm j))
    (bv := fun j => - co none (eb.symm j))
    (x := fun i => lam (em.symm i))
    (by
      intro j
      have h0 := hsys (eb.symm j)
      calc ∑ i, ((co (some (em.symm i)) (eb.symm j) : ↥K) : ℂ) * lam (em.symm i)
          = ∑ ik : Fin d × Fin D, (co (some ik) (eb.symm j) : ℂ) * lam ik :=
            Equiv.sum_comp em.symm fun ik => (co (some ik) (eb.symm j) : ℂ) * lam ik
        _ = ∑ ik : Fin d × Fin D, lam ik * (co (some ik) (eb.symm j) : ℂ) :=
            Finset.sum_congr rfl fun ik _ => mul_comm _ _
        _ = ((- co none (eb.symm j) : ↥K) : ℂ) := by
            push_cast
            linear_combination h0)
  set y : Fin d × Fin D → ↥K := fun ik => y0 (em ik) with hy
  have hyK : ∀ w : ↥b, co none w + ∑ ik : Fin d × Fin D, co (some ik) w * y ik = 0 := by
    intro w
    have h0 := hy0 (eb w)
    simp only [Equiv.symm_apply_apply] at h0
    have hre : ∑ ik : Fin d × Fin D, co (some ik) w * y ik =
        ∑ i, co (some (em.symm i)) w * y0 i := by
      rw [← Equiv.sum_comp em.symm (fun ik => co (some ik) w * y ik)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hy]
      simp only [Equiv.apply_symm_apply]
    rw [hre, h0]
    ring

  set p' : Fin d → Polynomial ℂ := fun i =>
    ∑ k : Fin D, Polynomial.C ((y (i, k) : ↥K) : ℂ) * Polynomial.X ^ (k : ℕ) with hp'
  have hp'coeff : ∀ (i : Fin d) (n : ℕ), (p' i).coeff n ∈ K := by
    intro i n
    rw [hp', Polynomial.finsetSum_coeff]
    refine sum_mem fun k _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split
    · rw [mul_one]
      exact SetLike.coe_mem _
    · rw [mul_zero]
      exact zero_mem _
  have hp'eval : ∀ (i : Fin d) (z : ℂ),
      (p' i).eval z = ∑ k : Fin D, ((y (i, k) : ↥K) : ℂ) * z ^ (k : ℕ) := by
    intro i z
    rw [hp', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

  have hKfun : u none + ∑ ik : Fin d × Fin D, ((y ik : ↥K) : ℂ) • u (some ik) = 0 := by
    calc u none + ∑ ik : Fin d × Fin D, ((y ik : ↥K) : ℂ) • u (some ik)
        = ∑ w : ↥b, ((co none w : ℂ) +
            ∑ ik : Fin d × Fin D, (co (some ik) w : ℂ) * ((y ik : ↥K) : ℂ)) •
              (w : ℍ → ℂ) := by
          rw [← hpiece none,
            Finset.sum_congr rfl fun ik _ =>
              congrArg (((y ik : ↥K) : ℂ) • ·) (hpiece (some ik)).symm]
          simp only [Finset.smul_sum]
          rw [Finset.sum_comm, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [add_smul, Finset.sum_smul]
          congr 1
          refine Finset.sum_congr rfl fun ik _ => ?_
          rw [smul_smul, mul_comm]
      _ = 0 := by
          refine Finset.sum_eq_zero fun w _ => ?_
          have h3 : (co none w : ℂ) +
              ∑ ik : Fin d × Fin D, (co (some ik) w : ℂ) * ((y ik : ↥K) : ℂ) = 0 := by
            exact_mod_cast congrArg (fun z : ↥K => (z : ℂ)) (hyK w)
          rw [h3, zero_smul]
  have hfinal0 : ∀ τ : ℍ, Pt τ ^ d + ∑ ik : Fin d × Fin D,
      ((y ik : ↥K) : ℂ) * (jf τ ^ (ik.2 : ℕ) *
        (Qt τ ^ (d - (ik.1 : ℕ)) * Pt τ ^ (ik.1 : ℕ))) = 0 := by
    intro τ
    have h0 := congrFun hKfun τ
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at h0
    rw [hu_top τ] at h0
    have hsum2 : ∑ ik : Fin d × Fin D, ((y ik : ↥K) : ℂ) * u (some ik) τ =
        ∑ ik : Fin d × Fin D, ((y ik : ↥K) : ℂ) * (jf τ ^ (ik.2 : ℕ) *
          (Qt τ ^ (d - (ik.1 : ℕ)) * Pt τ ^ (ik.1 : ℕ))) :=
      Finset.sum_congr rfl fun ik _ => by rw [hu_mon ik τ]
    rw [hsum2] at h0
    exact h0
  have hback : ∀ τ : ℍ,
      (G τ ^ d + ∑ i : Fin d, (p' i).eval (jf τ) * G τ ^ (i : ℕ)) * Qt τ ^ d = 0 := by
    intro τ
    have hterm : ∀ i : Fin d, (p' i).eval (jf τ) * G τ ^ (i : ℕ) * Qt τ ^ d =
        ∑ k : Fin D, ((y (i, k) : ↥K) : ℂ) * (jf τ ^ (k : ℕ) *
          (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ))) := by
      intro i
      rw [hp'eval, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsplit : Qt τ ^ d = Qt τ ^ (d - (i : ℕ)) * Qt τ ^ (i : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt i.2)]
      rw [hsplit]
      linear_combination ((y (i, k) : ↥K) : ℂ) * jf τ ^ (k : ℕ) *
        Qt τ ^ (d - (i : ℕ)) * hpow τ (i : ℕ)
    rw [add_mul, Finset.sum_mul, hpow τ d,
      Finset.sum_congr rfl fun i _ => hterm i]
    have h0 := hfinal0 τ
    rw [Fintype.sum_prod_type] at h0
    exact h0

  have hQtmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Qt := (hkA Q₀).1
  have hjfmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := hR4b12.1.1
  have hhmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ => G τ ^ d + ∑ i : Fin d, (p' i).eval (jf τ) * G τ ^ (i : ℕ)) := by
    have hsummd : ∀ i : Fin d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (fun τ => (p' i).eval (jf τ) * G τ ^ (i : ℕ)) := by
      intro i
      have hev : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (p' i).eval (jf τ)) := by
        have hsh : (fun τ => (p' i).eval (jf τ)) =
            fun τ => ∑ k : Fin D, ((y (i, k) : ↥K) : ℂ) * jf τ ^ (k : ℕ) := by
          funext τ
          rw [hp'eval]
        rw [hsh]
        have : ∀ s : Finset (Fin D), MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
            (fun τ => ∑ k ∈ s, ((y (i, k) : ↥K) : ℂ) * jf τ ^ (k : ℕ)) := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa using mdifferentiable_const
          | insert a t ha ih =>
            have hsh2 : (fun τ => ∑ k ∈ insert a t,
                ((y (i, k) : ↥K) : ℂ) * jf τ ^ (k : ℕ)) =
                (fun τ => ((y (i, a) : ↥K) : ℂ) * jf τ ^ (a : ℕ)) +
                fun τ => ∑ k ∈ t, ((y (i, k) : ↥K) : ℂ) * jf τ ^ (k : ℕ) := by
              funext τ
              simp [Finset.sum_insert ha]
            rw [hsh2]
            exact (mdifferentiable_const.mul (hjfmd.pow _)).add ih
        exact this Finset.univ
      exact hev.mul (hG.pow _)
    have : ∀ s : Finset (Fin d), MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (fun τ => ∑ i ∈ s, (p' i).eval (jf τ) * G τ ^ (i : ℕ)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using mdifferentiable_const
      | insert a t ha ih =>
        have hsh2 : (fun τ => ∑ i ∈ insert a t, (p' i).eval (jf τ) * G τ ^ (i : ℕ)) =
            (fun τ => (p' a).eval (jf τ) * G τ ^ (a : ℕ)) +
            fun τ => ∑ i ∈ t, (p' i).eval (jf τ) * G τ ^ (i : ℕ) := by
          funext τ
          simp [Finset.sum_insert ha]
        rw [hsh2]
        exact (hsummd a).add ih
    exact (hG.pow d).add (this Finset.univ)
  have hmul0 : ((fun τ => G τ ^ d + ∑ i : Fin d, (p' i).eval (jf τ) * G τ ^ (i : ℕ)) *
      Qt ^ d : ℍ → ℂ) = 0 := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    exact hback τ
  rcases mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero hhmd (hQtmd.pow d) hmul0 with
    hzero | hzero
  · refine ⟨d, p', hp'coeff, fun τ => ?_⟩
    exact congrFun hzero τ
  · exfalso
    apply hQ0
    funext τ
    have h1 := congrFun hzero τ
    simp only [Pi.pow_apply, Pi.zero_apply] at h1
    have h2 := pow_eq_zero_iff hdpos.ne' |>.mp h1
    simpa using h2
end
end WLightS9.S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient


namespace WLightS9.S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm Function Filter
open scoped _root_.Real _root_.Manifold _root_.MatrixGroups _root_.ModularForm _root_.Topology _root_.Polynomial _root_.Real.Polynomial

namespace FrickeTransport

local notation "Δ" => ModularForm.discriminant

section Analytic



private theorem disc_pow_ne_zero (m : ℕ) (τ : ℍ) : (Δ ^ m : ℍ → ℂ) τ ≠ 0 := by
  rw [Pi.pow_apply]; exact pow_ne_zero _ (discriminant_ne_zero τ)

end Analytic

section Params

variable {N : ℕ} [NeZero N]
variable (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
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
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)

private abbrev Idx (N : ℕ) : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

private def gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) : Idx N → ℍ → ℂ :=
  fun o => o.elim jf fun v => fricke (t v.1)

def genSet : Set (ℍ → ℂ) := insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}

private def ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) : ℍ → ℂ :=
  MvPolynomial.aeval (gen fricke jf t) (MvPolynomial.map ψ R)

private def ds (s : ℕ) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := ![v 0, (s : ZMod N) * v 1]

theorem ds_ne_zero {s : ℕ} (hs : s.Coprime N) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : ds s v ≠ 0 := by
  intro h
  apply hv
  have h0 : v 0 = 0 := by simpa [ds] using congrFun h 0
  have h1 : (s : ZMod N) * v 1 = 0 := by simpa [ds] using congrFun h 1
  have hu : IsUnit (s : ZMod N) := (ZMod.unitOfCoprime s hs).isUnit
  have h1' : v 1 = 0 := by simpa using hu.mul_left_cancel (h1.trans (mul_zero _).symm)
  funext i; fin_cases i <;> simp [h0, h1']

private theorem ev_id_eq (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) :
    ev fricke jf K id ψ R = MvPolynomial.aeval (fun o : Idx N => o.elim jf fun v => fricke v.1)
      (MvPolynomial.map ψ R) := rfl

private theorem ev_ds_eq (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) :
    ev fricke jf K (ds s) ψ R = MvPolynomial.aeval (fun o : Idx N =>
      o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (MvPolynomial.map ψ R) := rfl

theorem ev_mul (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R S : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (R * S) = ev fricke jf K t ψ R * ev fricke jf K t ψ S := by
  simp [ev]

theorem ev_pow (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) (n : ℕ) :
    ev fricke jf K t ψ (R ^ n) = ev fricke jf K t ψ R ^ n := by
  simp [ev]

private theorem ev_add (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R S : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (R + S) = ev fricke jf K t ψ R + ev fricke jf K t ψ S := by
  simp [ev]

private theorem ev_sum {ι : Type*} (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (S : Finset ι)
    (R : ι → MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (∑ i ∈ S, R i) = ∑ i ∈ S, ev fricke jf K t ψ (R i) := by
  simp [ev, map_sum]

include hW hfricke in
theorem fricke_eq : fricke = fun (a : Fin 2 → ZMod N) (τ : ℍ) =>
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
      (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ))) := by
  funext a τ; rw [hfricke, hW]

include hL hW hfricke in
theorem mdifferentiable_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  exact pkg.2.2.1 v hv

include hL hW hfricke in
private theorem isBoundedAtImInfty_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : IsBoundedAtImInfty (fricke v * Δ) := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  exact pkg.2.2.2.1 v hv

include hL hW hfricke hK in
private theorem periodic_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    Periodic ((fricke v * Δ) ∘ ofComplex) N ∧ ∀ n : ℕ, (qExpansion N (fricke v * Δ)).coeff n ∈ K := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  subst hK
  exact pkg.2.2.2.2.1 v hv

include hL hW hfricke hK hs hφ in

private theorem coeff_fricke_ds {v : Fin 2 → ZMod N} (hv : v ≠ 0) (n : ℕ) (z : K)
    (hz : (z : ℂ) = (qExpansion N (fricke v * Δ)).coeff n) :
    (qExpansion N (fricke (ds s v) * Δ)).coeff n = φ z := by
  have pkg := WLight.frickeFunction_modularity_package N L hL
  rw [← fricke_eq L W hW fricke hfricke] at pkg
  subst hK
  exact pkg.2.2.2.2.2.2.2 s hs φ hφ v hv n z hz

include hjf in
theorem mdifferentiable_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  have : jf = fun τ => E₄ τ ^ 3 / Δ τ := funext hjf
  rw [this]
  intro τ
  exact ((E₄.holo' τ).pow 3).div (mdifferentiable_disc τ) (discriminant_ne_zero τ)

include hL hW hfricke hjf in
theorem mdifferentiable_gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (o : Idx N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen fricke jf t o) := by
  cases o with
  | none => exact mdifferentiable_jf jf hjf
  | some v => exact mdifferentiable_fricke L hL W hW fricke hfricke (ht v.1 v.2)

include hL hW hfricke hjf in
theorem mdifferentiable_ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ev fricke jf K t ψ R) := by
  rw [ev]
  induction (MvPolynomial.map ψ R) using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact mdifferentiable_const
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact hp.mul (mdifferentiable_gen L hL W hW fricke hfricke jf hjf t ht o)

private theorem gen_mem_genSet (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0) (o : Idx N) :
    gen fricke jf t o ∈ genSet (N := N) fricke jf := by
  cases o with
  | none => exact Set.mem_insert _ _
  | some v => exact Set.mem_insert_of_mem _ ⟨t v.1, ht v.1 v.2, rfl⟩

private theorem ev_mem_adjoin (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ R ∈ Algebra.adjoin ℂ (genSet (N := N) fricke jf) := by
  rw [ev]
  induction (MvPolynomial.map ψ R) using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (Algebra.subset_adjoin (gen_mem_genSet fricke jf t ht o))

include hK hφ in

private theorem phi_mem (z : K) : φ z ∈ K := by
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) with hζdef
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hζK : ζ ∈ K := by rw [hK]; exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral (NeZero.pos N)).tower_top

  have hzmem : (z : ℂ) ∈ (Polynomial.aeval ζ : ℚ[X] →ₐ[ℚ] ℂ).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      IntermediateField.mem_toSubalgebra, ← hK]
    exact z.2
  obtain ⟨p, hp⟩ := hzmem
  let ζK : K := ⟨ζ, hζK⟩
  have hz : z = Polynomial.aeval ζK p := by
    apply Subtype.ext
    change (z : ℂ) = (IntermediateField.val K) (Polynomial.aeval ζK p)
    rw [← Polynomial.aeval_algHom_apply]
    exact hp.symm
  have hφz : φ z = Polynomial.aeval (ζ ^ s) p := by
    rw [hz, ← RingHom.toRatAlgHom_apply φ, ← Polynomial.aeval_algHom_apply, RingHom.toRatAlgHom_apply,
      hφ ζK rfl]
  rw [hφz]
  have hle : Algebra.adjoin ℚ {ζ ^ s} ≤ K.toSubalgebra := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact pow_mem hζK s
  exact hle (Polynomial.aeval_mem_adjoin_singleton ℚ _)

include hK hφ in

private theorem exists_phiK : ∃ φK : K →+* K, (algebraMap K ℂ).comp φK = φ := by
  refine ⟨{ toFun := fun z => ⟨φ z, phi_mem K hK s φ hφ z⟩
            map_one' := Subtype.ext (by simp)
            map_mul' := fun x y => Subtype.ext (by simp)
            map_zero' := Subtype.ext (by simp)
            map_add' := fun x y => Subtype.ext (by simp) }, ?_⟩
  ext z
  rfl

private def dsIdx (hs : s.Coprime N) : Idx N → Idx N := fun o => o.map fun v => ⟨ds s v.1, ds_ne_zero hs v.2⟩

private theorem gen_comp_dsIdx : gen fricke jf id ∘ dsIdx s hs = gen fricke jf (ds s) := by
  funext o; cases o <;> rfl

private theorem ev_ds_eq_ev_id {φK : K →+* K} (hφK : (algebraMap K ℂ).comp φK = φ) (R : MvPolynomial (Idx N) K) :
    ev fricke jf K (ds s) φ R =
      ev fricke jf K id (algebraMap K ℂ) (MvPolynomial.rename (dsIdx s hs) (MvPolynomial.map φK R)) := by
  rw [ev, ev, MvPolynomial.map_rename, MvPolynomial.aeval_rename, gen_comp_dsIdx, MvPolynomial.map_map, hφK]

section Width

variable (N)

private theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)






variable {N K}








private theorem exists_discSeries : ∃ δ : PowerSeries K, δ.map (algebraMap K ℂ) = qExpansion N (Δ : ℍ → ℂ) ∧
    δ.map φ = qExpansion N (Δ : ℍ → ℂ) := by
  choose r hr using qExpansion_disc_rat N
  refine ⟨PowerSeries.mk fun n => ⟨(r n : ℂ), ratCast_mem (K := K) (r n)⟩, ?_, ?_⟩
  · ext n; simp [hr n]
  · ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hr n]
    have : (⟨(r n : ℂ), ratCast_mem (K := K) (r n)⟩ : K) = algebraMap ℚ K (r n) := by
      apply Subtype.ext; rfl
    rw [this, ← RingHom.comp_apply, eq_ratCast]

end Width

section TRel

private def TRel (g g' : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g' ∧
    ∃ m : ℕ,
      (Function.Periodic ((g * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
        IsBoundedAtImInfty (g * ModularForm.discriminant ^ m) ∧
        ∀ n : ℕ,
          (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
      (Function.Periodic ((g' * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
        IsBoundedAtImInfty (g' * ModularForm.discriminant ^ m) ∧
        ∀ n : ℕ,
          (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
      ∀ (n : ℕ) (z : K),
        (z : ℂ) = (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n →
        (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n = φ z

include hK hφ in

private theorem transportPkg :
    (∀ {ι : Type} (g g' : ι → ℍ → ℂ), (∀ i : ι, TRel (N := N) K φ (g i) (g' i)) →
      ∀ R : MvPolynomial ι K,
        TRel (N := N) K φ (MvPolynomial.aeval g (MvPolynomial.map (algebraMap K ℂ) R))
          (MvPolynomial.aeval g' (MvPolynomial.map φ R))) ∧
    (∀ g g' : ℍ → ℂ, TRel (N := N) K φ g g' → (g = 0 ↔ g' = 0)) ∧
    ∀ jf' : ℍ → ℂ, (∀ τ : ℍ, jf' τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) →
      TRel (N := N) K φ jf' jf' :=
  WLight.qExpansion_sigmaTransport_package N K φ (phi_mem K hK s φ hφ) (TRel (N := N) K φ)
    (fun _g _g' => Iff.rfl)

include hL hW hfricke hK hs hφ in
private theorem tRel_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : TRel (N := N) K φ (fricke v) (fricke (ds s v)) := by
  have hv' : ds s v ≠ 0 := ds_ne_zero hs hv
  obtain ⟨hp, hm⟩ := periodic_fricke L hL W hW fricke hfricke K hK hv
  obtain ⟨hp', hm'⟩ := periodic_fricke L hL W hW fricke hfricke K hK hv'
  refine ⟨mdifferentiable_fricke L hL W hW fricke hfricke hv, mdifferentiable_fricke L hL W hW fricke hfricke hv',
    1, ?_, ?_, ?_⟩
  · rw [pow_one]; exact ⟨hp, isBoundedAtImInfty_fricke L hL W hW fricke hfricke hv, hm⟩
  · rw [pow_one]; exact ⟨hp', isBoundedAtImInfty_fricke L hL W hW fricke hfricke hv', hm'⟩
  · intro n z hz
    rw [pow_one] at hz ⊢
    exact coeff_fricke_ds L hL W hW fricke hfricke K hK s hs φ hφ hv n z hz

include hL hW hfricke hjf hK hs hφ in
private theorem tRel_gen (o : Idx N) : TRel (N := N) K φ (gen fricke jf id o) (gen fricke jf (ds s) o) := by
  cases o with
  | none => exact (transportPkg K hK s φ hφ).2.2 jf hjf
  | some v => exact tRel_fricke L hL W hW fricke hfricke K hK s hs φ hφ v.2

include hL hW hfricke hjf hK hs hφ in

private theorem tRel_ev (R : MvPolynomial (Idx N) K) :
    TRel (N := N) K φ (ev fricke jf K id (algebraMap K ℂ) R) (ev fricke jf K (ds s) φ R) :=
  (transportPkg K hK s φ hφ).1 _ _ (tRel_gen L hL W hW fricke hfricke jf hjf K hK s hs φ hφ) R

include hK hφ in
private theorem tRel_zero_iff {g g' : ℍ → ℂ} (h : TRel (N := N) K φ g g') : g = 0 ↔ g' = 0 :=
  (transportPkg K hK s φ hφ).2.1 g g' h

private theorem TRel.lift {g g' : ℍ → ℂ} (h : TRel (N := N) K φ g g') :
    ∃ m : ℕ, RatAt N K m g ∧ RatAt N K m g' ∧ ∀ M : ℕ, m ≤ M →
      ∃ p : PowerSeries K, p.map (algebraMap K ℂ) = qExpansion N (g * Δ ^ M) ∧
        p.map φ = qExpansion N (g' * Δ ^ M) := by
  obtain ⟨hg, hg', m, ⟨h1, h2, h3⟩, ⟨h1', h2', h3'⟩, h4⟩ := h
  have hR : RatAt N K m g := ⟨hg, h1, h2, h3⟩
  have hR' : RatAt N K m g' := ⟨hg', h1', h2', h3'⟩
  refine ⟨m, hR, hR', ?_⟩
  intro M hM
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  obtain ⟨p₀, hp₀⟩ := hR.exists_map
  have hp₀' : p₀.map φ = qExpansion N (g' * Δ ^ m) := by
    ext n
    rw [PowerSeries.coeff_map]
    symm
    apply h4
    rw [← hp₀, PowerSeries.coeff_map]
    rfl
  obtain ⟨δ, hδ, hδ'⟩ := exists_discSeries (N := N) (K := K) φ
  refine ⟨p₀ * δ ^ d, ?_, ?_⟩
  · induction d with
    | zero => simpa using hp₀
    | succ d ih =>
        have hRd : RatAt N K (m + d) g := hR.of_le (Nat.le_add_right _ _)
        rw [pow_succ, ← mul_assoc, map_mul, ih (Nat.le_add_right _ _), hδ, ← add_assoc, pow_succ,
          ← mul_assoc, qExpansion_mul hRd.analyticAt analyticAt_disc]
  · induction d with
    | zero => simpa using hp₀'
    | succ d ih =>
        have hRd : RatAt N K (m + d) g' := hR'.of_le (Nat.le_add_right _ _)
        rw [pow_succ, ← mul_assoc, map_mul, ih (Nat.le_add_right _ _), hδ', ← add_assoc, pow_succ,
          ← mul_assoc, qExpansion_mul hRd.analyticAt analyticAt_disc]

end TRel

section Construction

variable {L hL W hW fricke hfricke jf hjf K hK s hs φ hφ}
variable (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (P Q : MvPolynomial (Idx N) K)
    (hQ0 : ev fricke jf K id (algebraMap K ℂ) Q ≠ 0)
    (hGQ : G * ev fricke jf K id (algebraMap K ℂ) Q = ev fricke jf K id (algebraMap K ℂ) P)

local notation "𝔢" => ev fricke jf K id (algebraMap K ℂ)
local notation "𝔢'" => ev fricke jf K (ds s) φ

private def toIdxPoly (p : ℂ[X]) (hp : ∀ n, p.coeff n ∈ K) : MvPolynomial (Idx N) K :=
  ∑ n ∈ p.support, MvPolynomial.C (⟨p.coeff n, hp n⟩ : K) * MvPolynomial.X none ^ n

private theorem ev_toIdxPoly (p : ℂ[X]) (hp : ∀ n, p.coeff n ∈ K) :
    𝔢 (toIdxPoly p hp) = fun τ => p.eval (jf τ) := by
  funext τ
  rw [toIdxPoly, ev_sum, Finset.sum_apply, Polynomial.eval_eq_sum, Polynomial.sum_def]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ev_mul, ev_pow]
  simp only [ev, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Pi.mul_apply, Pi.pow_apply]
  rfl

include hL hW hfricke hjf hK hs hφ hG hQ0 hGQ in

private theorem exists_transport : 𝔢' Q ≠ 0 ∧ ∃ G' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G' ∧ G' * 𝔢' Q = 𝔢' P := by
  classical

  have hQ'0 : 𝔢' Q ≠ 0 := fun h0 =>
    hQ0 ((tRel_zero_iff K hK s φ hφ (tRel_ev L hL W hW fricke hfricke jf hjf K hK s hs φ hφ Q)).2 h0)
  refine ⟨hQ'0, ?_⟩

  obtain ⟨d, p, hpK, hrel⟩ := WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient N L hL W hW fricke
    hfricke jf hjf K hK G hG P Q hQ0 hGQ

  let a : Fin d → MvPolynomial (Idx N) K := fun i => toIdxPoly (p i) (hpK i)
  let Rrel : MvPolynomial (Idx N) K := P ^ d + ∑ i : Fin d, a i * Q ^ (d - (i : ℕ)) * P ^ (i : ℕ)
  have hRrel : 𝔢 Rrel = 0 := by
    funext τ
    have h1 := hrel τ
    have hGQτ : G τ * 𝔢 Q τ = 𝔢 P τ := by
      have := congrFun hGQ τ; simpa only [Pi.mul_apply] using this
    have hev : 𝔢 Rrel τ = 𝔢 P τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * 𝔢 Q τ ^ (d - (i : ℕ)) * 𝔢 P τ ^ (i : ℕ) := by
      simp only [Rrel, ev_add, ev_pow, ev_sum, ev_mul, Pi.add_apply, Pi.pow_apply, Finset.sum_apply,
        Pi.mul_apply, a, ev_toIdxPoly]
    rw [hev, Pi.zero_apply, ← hGQτ]
    have key : (G τ * 𝔢 Q τ) ^ d + ∑ i : Fin d, (p i).eval (jf τ) * 𝔢 Q τ ^ (d - (i : ℕ)) * (G τ * 𝔢 Q τ) ^ (i : ℕ)
        = (G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ)) * 𝔢 Q τ ^ d := by
      rw [add_mul, Finset.sum_mul, mul_pow]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (i : ℕ) ≤ d := i.2.le
      rw [mul_pow, show 𝔢 Q τ ^ d = 𝔢 Q τ ^ (i : ℕ) * 𝔢 Q τ ^ (d - (i : ℕ)) by
        rw [← pow_add, Nat.add_sub_cancel' hi]]
      ring
    rw [key, h1, zero_mul]

  have hRrel' : 𝔢' Rrel = 0 :=
    (tRel_zero_iff K hK s φ hφ (tRel_ev L hL W hW fricke hfricke jf hjf K hK s hs φ hφ Rrel)).1 hRrel

  let c : ℕ → ℍ → ℂ := fun n => if h : n < d then 𝔢' (a ⟨n, h⟩) else 0
  have hc : ∀ n < d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c n) := by
    intro n hn
    simp only [c, dite_eq_left hn]
    exact mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv => ds_ne_zero hs hv) φ _
  have hmonic : 𝔢' P ^ d + ∑ n ∈ Finset.range d, c n * 𝔢' Q ^ (d - n) * 𝔢' P ^ n = 0 := by
    have hev : 𝔢' Rrel = 𝔢' P ^ d + ∑ i : Fin d, 𝔢' (a i) * 𝔢' Q ^ (d - (i : ℕ)) * 𝔢' P ^ (i : ℕ) := by
      simp only [Rrel, ev_add, ev_pow, ev_sum, ev_mul]
    rw [hev] at hRrel'
    rw [← hRrel', Finset.sum_range (fun n => c n * 𝔢' Q ^ (d - n) * 𝔢' P ^ n)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [c, dite_eq_left i.2]
  exact WLight.exists_mdifferentiable_div_of_monicRel
    (mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv => ds_ne_zero hs hv) φ P)
    (mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv => ds_ne_zero hs hv) φ Q)
    hQ'0 hc hmonic

include hL hW hfricke hjf hK in

private theorem exists_ratAt_of_quotient {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (P₁ Q₁ : MvPolynomial (Idx N) K)
    (hQ₁ : 𝔢 Q₁ ≠ 0) (huQ : u * 𝔢 Q₁ = 𝔢 P₁) : ∃ m, RatAt N K m u := by
  have hint := WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient N L hL W hW fricke hfricke jf hjf
    K hK u hu P₁ Q₁ hQ₁ huQ
  have hcoef : ∀ (R : MvPolynomial (Idx N) K) (mo : Idx N →₀ ℕ),
      (MvPolynomial.map (algebraMap K ℂ) R).coeff mo ∈ K := by
    intro R mo; rw [MvPolynomial.coeff_map]; exact (R.coeff mo).2
  obtain ⟨m, hper, hbdd, hmem⟩ := WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction N L hL
    W hW fricke hfricke jf hjf K hK hu (MvPolynomial.map (algebraMap K ℂ) P₁)
    (MvPolynomial.map (algebraMap K ℂ) Q₁) (hcoef P₁) (hcoef Q₁) hQ₁ huQ hint
  exact ⟨m, ⟨hu, hper, hbdd, hmem⟩⟩

include hL hW hfricke hjf hK hs hφ hG hQ0 hGQ in

private theorem tRel_of_transport {G' : ℍ → ℂ} (hG' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G') (hG'Q : G' * 𝔢' Q = 𝔢' P) :
    TRel (N := N) K φ G G' := by
  classical
  obtain ⟨hQ'0, -⟩ := exists_transport (hL := hL) (hW := hW) (hfricke := hfricke) (hjf := hjf) (hK := hK)
    (hs := hs) (hφ := hφ) G hG P Q hQ0 hGQ

  obtain ⟨mG, hRG⟩ := exists_ratAt_of_quotient (hL := hL) (hW := hW) (hfricke := hfricke) (hjf := hjf)
    (hK := hK) hG P Q hQ0 hGQ
  obtain ⟨φK, hφK⟩ := exists_phiK K hK s φ hφ
  have hQ₁ : 𝔢 (MvPolynomial.rename (dsIdx s hs) (MvPolynomial.map φK Q)) ≠ 0 := by
    rw [← ev_ds_eq_ev_id fricke jf K s hs φ hφK]; exact hQ'0
  have hG'Q₁ : G' * 𝔢 (MvPolynomial.rename (dsIdx s hs) (MvPolynomial.map φK Q)) =
      𝔢 (MvPolynomial.rename (dsIdx s hs) (MvPolynomial.map φK P)) := by
    rw [← ev_ds_eq_ev_id fricke jf K s hs φ hφK, ← ev_ds_eq_ev_id fricke jf K s hs φ hφK]; exact hG'Q
  obtain ⟨mG', hRG'⟩ := exists_ratAt_of_quotient (hL := hL) (hW := hW) (hfricke := hfricke) (hjf := hjf)
    (hK := hK) hG' _ _ hQ₁ hG'Q₁

  obtain ⟨mQ, hRQ, hRQ', hQlift⟩ := (tRel_ev L hL W hW fricke hfricke jf hjf K hK s hs φ hφ Q).lift
  obtain ⟨mP, -, -, hPlift⟩ := (tRel_ev L hL W hW fricke hfricke jf hjf K hK s hs φ hφ P).lift

  set M : ℕ := mG + mG' + mQ + mP with hM
  have hRGM : RatAt N K M G := hRG.of_le (by omega)
  have hRG'M : RatAt N K M G' := hRG'.of_le (by omega)
  have hRQM : RatAt N K M (𝔢 Q) := hRQ.of_le (by omega)
  have hRQ'M : RatAt N K M (𝔢' Q) := hRQ'.of_le (by omega)
  obtain ⟨pQ, hpQ, hpQ'⟩ := hQlift M (by omega)
  obtain ⟨pP, hpP, hpP'⟩ := hPlift (M + M) (by omega)
  obtain ⟨pG, hpG⟩ := hRGM.exists_map

  have hsplit : ∀ u w : ℍ → ℂ, u * w * Δ ^ (M + M) = (u * Δ ^ M) * (w * Δ ^ M) := by
    intro u w; rw [pow_add]; ring
  have hprod : pG * pQ = pP := by
    apply PowerSeries.map_injective (algebraMap K ℂ) Subtype.val_injective
    rw [map_mul, hpG, hpQ, hpP, ← hGQ, hsplit, qExpansion_mul hRGM.analyticAt hRQM.analyticAt]

  have hG'exp : qExpansion N (G' * Δ ^ M) = pG.map φ := by
    have h1 : qExpansion N (G' * Δ ^ M) * qExpansion N (𝔢' Q * Δ ^ M) = pG.map φ * qExpansion N (𝔢' Q * Δ ^ M) := by
      rw [← qExpansion_mul hRG'M.analyticAt hRQ'M.analyticAt, ← hsplit, hG'Q, ← hpP', ← hprod, map_mul, hpQ']
    have hne : qExpansion N (𝔢' Q * Δ ^ M) ≠ 0 := hRQ'M.qExpansion_ne_zero hQ'0
    exact mul_right_cancel₀ hne h1
  refine ⟨hG, hG', M, ⟨hRGM.periodic, hRGM.bdd, hRGM.mem⟩, ⟨hRG'M.periodic, hRG'M.bdd, hRG'M.mem⟩, ?_⟩
  intro n z hz
  have hz' : z = PowerSeries.coeff n pG := by
    apply Subtype.val_injective
    rw [hz, ← hpG, PowerSeries.coeff_map]
    rfl
  rw [hG'exp, PowerSeries.coeff_map, hz']

end Construction

end Params

end FrickeTransport

end

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem _root_.ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient
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
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (P.map (algebraMap ↥K ℂ))) :
    MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) ≠ 0 ∧
    ∃ G' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G' ∧
      G' * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) =
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (P.map φ) ∧
      ∃ m : ℕ, ∀ M : ℕ, m ≤ M →
        (Function.Periodic ((G * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
          IsBoundedAtImInfty (G * ModularForm.discriminant ^ M) ∧
          ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ M)).coeff n ∈ K) ∧
        (Function.Periodic ((G' * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
          IsBoundedAtImInfty (G' * ModularForm.discriminant ^ M) ∧
          ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G' * ModularForm.discriminant ^ M)).coeff n ∈ K) ∧
        ∀ (n : ℕ) (z : ↥K),
          (z : ℂ) = (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ M)).coeff n →
          (UpperHalfPlane.qExpansion N (G' * ModularForm.discriminant ^ M)).coeff n = φ z := by
  obtain ⟨hQ'0, G', hG', hG'Q⟩ := FrickeTransport.exists_transport (hL := hL) (hW := hW) (hfricke := hfricke)
    (hjf := hjf) (hK := hK) (hs := hs) (hφ := hφ) G hG P Q hQ0 hGQ
  have hT := FrickeTransport.tRel_of_transport (hL := hL) (hW := hW) (hfricke := hfricke) (hjf := hjf)
    (hK := hK) (hs := hs) (hφ := hφ) G hG P Q hQ0 hGQ hG' hG'Q
  obtain ⟨m, hR, hR', hlift⟩ := hT.lift
  refine ⟨hQ'0, G', hG', hG'Q, m, fun M hM => ?_⟩
  have hRM := hR.of_le hM
  have hRM' := hR'.of_le hM
  obtain ⟨p, hp, hp'⟩ := hlift M hM
  refine ⟨⟨hRM.periodic, hRM.bdd, hRM.mem⟩, ⟨hRM'.periodic, hRM'.bdd, hRM'.mem⟩, fun n z hz => ?_⟩
  have hz' : z = PowerSeries.coeff n p := by
    apply Subtype.val_injective
    rw [hz, ← hp, PowerSeries.coeff_map]
    rfl
  rw [← hp', PowerSeries.coeff_map, hz']
end WLightS9.S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient
