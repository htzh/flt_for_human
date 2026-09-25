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
set_option autoImplicit false
-- The pin's `haveI` walls are load-bearing; keep them literal (cf. `Basic.lean`).
set_option linter.style.haveILetI false

namespace WLightS9.S_WLight_levelN_structure_package

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

private lemma sl_smul_def (γ : SL(2, ℤ)) (f : ℍ → ℂ) : γ • f = fun τ ↦ f (γ⁻¹ • τ) := rfl

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

private lemma smul_jK {N : ℕ} [NeZero N] (g : LevelGrp N) : g • jK N = jK N := by
  rw [jK, levelGrp_smul_algebraMap]
  congr 1
  induction g using QuotientGroup.induction_on with
  | H γ => exact Subtype.ext (smul_j γ)

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

private abbrev ratJ (N : ℕ) [NeZero N] : IntermediateField ℂ (levelField N) := ℂ⟮jK N⟯

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

private def jA : ↥D.ring := ⟨j, D.levelRing_le_ring (j_mem_levelRing N)⟩

private def jK : D.field := algebraMap ↥D.ring D.field D.jA

private lemma coe_aeval_jA (P : Polynomial ℂ) :
    ((Polynomial.aeval D.jA P : ↥D.ring) : ℍ → ℂ) = fun τ ↦ Polynomial.eval (j τ) P := by
  rw [Polynomial.aeval_subalgebra_coe]
  funext τ
  exact aeval_j_apply P τ

private lemma smul_jK (g : LevelGrp N) : g • D.jK = D.jK := by
  rw [jK, grp_smul_algebraMap]
  congr 1
  induction g using QuotientGroup.induction_on with
  | H γ => exact Subtype.ext (smul_j γ)

private abbrev ratJ : IntermediateField ℂ D.field := ℂ⟮D.jK⟯

private def incl : ↥(levelRing N) →ₐ[ℂ] ↥D.ring := Subalgebra.inclusion D.levelRing_le_ring

private lemma incl_injective : Function.Injective D.incl := Subalgebra.inclusion_injective _

@[scoped simp] private lemma coe_incl (a : ↥(levelRing N)) : ((D.incl a : ↥D.ring) : ℍ → ℂ) = a :=
  Subalgebra.coe_inclusion _ a

private lemma toRingField_injective :
    Function.Injective ((IsScalarTower.toAlgHom ℂ ↥D.ring D.field).comp D.incl) :=
  (IsFractionRing.injective ↥D.ring D.field).comp D.incl_injective

private noncomputable def toField : levelField N →ₐ[ℂ] D.field :=
  IsFractionRing.liftAlgHom D.toRingField_injective

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

end LevelGens

end C0_membership

section Solution
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

private lemma periodPair_eq_of_ω (P P' : PeriodPair) (h1 : P.ω₁ = P'.ω₁) (h2 : P.ω₂ = P'.ω₂) :
    P = P' := by
  rcases P with ⟨_, _, _⟩; rcases P' with ⟨_, _, _⟩
  simp only [PeriodPair.mk.injEq]; exact ⟨h1, h2⟩


private theorem r5_fixed_frac_polynomial {N : ℕ} [NeZero N] {a b : ℍ → ℂ}
    (haA : a ∈ levelRing N) (hbA : b ∈ levelRing N) (hb0 : b ≠ 0)
    (hinv : ∀ γ : SL(2, ℤ), a * (b ∘ (γ • ·)) = (a ∘ (γ • ·)) * b) :
    ∃ p q : Polynomial ℂ, q ≠ 0 ∧ a * (fun τ ↦ q.eval (j τ)) = b * (fun τ ↦ p.eval (j τ)) := by
  set aR : ↥(levelRing N) := ⟨a, haA⟩
  set bR : ↥(levelRing N) := ⟨b, hbA⟩
  have hbR0 : bR ≠ 0 := fun h ↦ hb0 (congrArg Subtype.val h)
  have hinvR : ∀ γ : SL(2, ℤ), aR * (γ • bR) = (γ • aR) * bR := fun γ ↦ by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, levelRing_coe_smul, sl_smul_def]
    exact hinv γ⁻¹
  set x : levelField N := (algebraMap _ (levelField N) aR) / (algebraMap _ (levelField N) bR)
  have hbRK : algebraMap _ (levelField N) bR ≠ 0 := fun h ↦ hbR0
    ((map_eq_zero_iff _ (IsFractionRing.injective ↥(levelRing N) (levelField N))).mp h)
  have hxfix : ∀ g : LevelGrp N, g • x = x := fun g ↦ by
    have hgb : algebraMap _ (levelField N) (g • bR) ≠ 0 := fun h ↦ hbR0 (by
      have h0 : g • bR = 0 := (map_eq_zero_iff _
        (IsFractionRing.injective ↥(levelRing N) (levelField N))).mp h
      have := congrArg (g⁻¹ • ·) h0
      simpa only [inv_smul_smul, smul_zero] using this)
    have hgx : g • x = algebraMap _ (levelField N) (g • aR)
        / algebraMap _ (levelField N) (g • bR) := by
      rw [← levelGrp_smul_algebraMap, ← levelGrp_smul_algebraMap]
      exact map_div₀ (MulSemiringAction.toRingHom (LevelGrp N) (levelField N) g) _ _
    have hgeq : aR * (g • bR) = (g • aR) * bR := by
      induction g using QuotientGroup.induction_on with
      | H γ => rw [levelGrp_mk_smul, levelGrp_mk_smul]; exact hinvR γ
    rw [hgx, div_eq_div_iff hgb hbRK, ← map_mul, ← map_mul]
    exact congrArg _ hgeq.symm
  obtain ⟨a', b', ha'f, hb'f, hb'0, hx⟩ :=
    exists_fixed_div_of_fixed (G := LevelGrp N) (A := ↥(levelRing N)) (K := levelField N)
      levelGrp_smul_algebraMap x hxfix
  have ha'fS : ∀ γ : SL(2, ℤ), γ • a' = a' :=
    fun γ ↦ (levelGrp_mk_smul γ a').symm.trans (ha'f (QuotientGroup.mk γ))
  have hb'fS : ∀ γ : SL(2, ℤ), γ • b' = b' :=
    fun γ ↦ (levelGrp_mk_smul γ b').symm.trans (hb'f (QuotientGroup.mk γ))
  obtain ⟨p, hp⟩ := levelRing_fixed_eq_aeval_j a' ha'fS
  obtain ⟨q, hq⟩ := levelRing_fixed_eq_aeval_j b' hb'fS
  refine ⟨p, q, ?_, ?_⟩
  · intro hq0; apply hb'0
    rw [hq, hq0, map_zero, map_zero]
  · have hab' : aR * b' = bR * a' := by
      have hdm := hx
      rw [show x = algebraMap _ (levelField N) aR / algebraMap _ (levelField N) bR from rfl,
        div_mul_eq_mul_div, div_eq_iff hbRK, ← map_mul, ← map_mul] at hdm
      exact (IsFractionRing.injective ↥(levelRing N) (levelField N) hdm).trans (mul_comm a' bR)
    have hfun := congrArg (Subtype.val : ↥(levelRing N) → ℍ → ℂ) hab'
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, hp, hq, coe_aeval_jA, coe_aeval_jA] at hfun
    exact hfun

end Solution
end WLight

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

private lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

private lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ Filter.const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

private lemma mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
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
    exact (mul_discPow_mono (le_max_left m n) hm).add (mul_discPow_mono (le_max_right m n) hn)
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

end QKitA

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

section QKitB

open ModularForm

variable {N : ℕ} {K : IntermediateField ℚ ℂ}

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

private theorem differentiableAt_comp_ofComplex {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (τ : ℍ) :
    DifferentiableAt ℂ (u ∘ ofComplex) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.1 (hu τ)

private theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) := (differentiableAt_comp_ofComplex hv τ₀).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hvc.eventually_ne hv0'] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hEq := ((UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd
    isOpen_upperHalfPlaneSet).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  simpa [Function.comp, ofComplex_apply] using hEq τ.im_pos

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

private theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
  rwa [CuspForm.coe_discriminant] at this

private theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) := by
  have := ModularFormClass.bdd_at_infty CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

private theorem disc_pow_ne_zero (m : ℕ) (τ : ℍ) : (Δ ^ m : ℍ → ℂ) τ ≠ 0 := by
  rw [Pi.pow_apply]; exact pow_ne_zero _ (discriminant_ne_zero τ)

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem periodic_mul {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g * g') ∘ ofComplex) c := by
  intro z
  have h1 := h z
  have h2 := h' z
  simp only [comp_apply, Pi.mul_apply] at h1 h2 ⊢
  rw [h1, h2]

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

private def genSet : Set (ℍ → ℂ) := insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}

private def ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) : ℍ → ℂ :=
  MvPolynomial.aeval (gen fricke jf t) (MvPolynomial.map ψ R)

private def ds (s : ℕ) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := ![v 0, (s : ZMod N) * v 1]

private theorem ds_ne_zero {s : ℕ} (hs : s.Coprime N) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : ds s v ≠ 0 := by
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

private theorem ev_mul (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R S : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (R * S) = ev fricke jf K t ψ R * ev fricke jf K t ψ S := by
  simp [ev]

private theorem ev_pow (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) (n : ℕ) :
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
private theorem fricke_eq : fricke = fun (a : Fin 2 → ZMod N) (τ : ℍ) =>
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
      (((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
        PeriodPair.weierstrassP (L τ) ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ))) := by
  funext a τ; rw [hfricke, hW]

include hL hW hfricke in
private theorem mdifferentiable_fricke {v : Fin 2 → ZMod N} (hv : v ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) := by
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
private theorem mdifferentiable_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  have : jf = fun τ => E₄ τ ^ 3 / Δ τ := funext hjf
  rw [this]
  intro τ
  exact ((E₄.holo' τ).pow 3).div (mdifferentiable_disc τ) (discriminant_ne_zero τ)

include hL hW hfricke hjf in
private theorem mdifferentiable_gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (o : Idx N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen fricke jf t o) := by
  cases o with
  | none => exact mdifferentiable_jf jf hjf
  | some v => exact mdifferentiable_fricke L hL W hW fricke hfricke (ht v.1 v.2)

include hL hW hfricke hjf in
private theorem mdifferentiable_ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
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

private theorem qExpansion_coeff_unique' {h : ℝ} (hh : 0 < h) {g : ℍ → ℂ} {c : ℕ → ℂ}
    (hg : AnalyticAt ℂ (cuspFunction h g) 0)
    (hc : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam h τ ^ m) (g τ)) (m : ℕ) :
    c m = (qExpansion h g).coeff m := by
  have h1 := (hasFPowerSeriesOnBall_cuspFunction hh hg hc).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction h g)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (qExpansion h g).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using hg.hasFPowerSeriesAt
  simpa [FormalMultilinearSeries.coeff_ofScalars] using
    congr_arg (FormalMultilinearSeries.coeff · m) (h1.eq_formalMultilinearSeries h2)

private theorem qParam_one_eq_pow (τ : ℍ) : Periodic.qParam 1 τ = Periodic.qParam N τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

private theorem qExpansion_coeff_widthN {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) 1) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion N g).coeff n = if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 := by
  classical
  have hperN : Periodic (g ∘ ofComplex) N := periodic_ofComplex_natCast hper N
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion 1 g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam N τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam N τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_one_eq_pow N τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos N) (analyticAt_cuspFunction_zero (natCast_pos N)
    hperN hg hbd) hsum n]

private theorem qExpansion_disc_rat_one (n : ℕ) : ∃ r : ℚ, (qExpansion 1 (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  let A : ModularForm 𝒮ℒ 12 := (E₄.pow 3).mcast (by norm_num)
  let B : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)
  have hfun : (Δ : ℍ → ℂ) = ⇑((1728 : ℂ)⁻¹ • (A - B)) := by
    funext z
    rw [discriminant_eq_E₄_cube_sub_E₆_sq, smul_apply, sub_apply]
    simp only [A, B, coe_mcast, coe_pow, Pi.pow_apply, smul_eq_mul]
    ring
  have h4 : ∀ n, ∃ r : ℚ, (qExpansion 1 (E₄ : ℍ → ℂ)).coeff n = (r : ℂ) := by
    intro n
    rw [ModularForm.E₄, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨-(2 * 4 / bernoulli 4) * (ArithmeticFunction.sigma 3 n : ℚ), by push_cast; ring⟩
  have h6 : ∀ n, ∃ r : ℚ, (qExpansion 1 (E₆ : ℍ → ℂ)).coeff n = (r : ℂ) := by
    intro n
    rw [ModularForm.E₆, EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) n]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨-(2 * 6 / bernoulli 6) * (ArithmeticFunction.sigma 5 n : ℚ), by push_cast; ring⟩
  obtain ⟨p4, hp4⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₄ : ℍ → ℂ) := by
    choose r hr using h4
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  obtain ⟨p6, hp6⟩ : ∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
    choose r hr using h6
    exact ⟨PowerSeries.mk r, by ext n; simp [hr n]⟩
  have hq : qExpansion 1 (Δ : ℍ → ℂ) = ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)).map (algebraMap ℚ ℂ) := by
    rw [hfun, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL]
    simp only [A, B, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, PowerSeries.map_C, map_sub,
      map_pow, map_pow, hp4, hp6]
    congr 1
    simp
  refine ⟨PowerSeries.coeff n ((1728 : ℚ)⁻¹ • (p4 ^ 3 - p6 ^ 2)), ?_⟩
  rw [hq, PowerSeries.coeff_map]
  rfl

private theorem qExpansion_disc_rat (n : ℕ) : ∃ r : ℚ, (qExpansion N (Δ : ℍ → ℂ)).coeff n = (r : ℂ) := by
  rw [qExpansion_coeff_widthN N mdifferentiable_disc periodic_disc_one isBoundedAtImInfty_disc n]
  split_ifs with h
  · exact qExpansion_disc_rat_one _
  · exact ⟨0, by simp⟩

private theorem ratCast_mem (r : ℚ) : ((r : ℂ)) ∈ K := by
  have : (r : ℂ) = algebraMap ℚ ℂ r := rfl
  rw [this]; exact K.algebraMap_mem r

private structure RatAt (m : ℕ) (g : ℍ → ℂ) : Prop where
  mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g
  periodic : Periodic ((g * Δ ^ m) ∘ ofComplex) N
  bdd : IsBoundedAtImInfty (g * Δ ^ m)
  mem : ∀ n, (qExpansion N (g * Δ ^ m)).coeff n ∈ K

variable {N K}

private theorem RatAt.mdiff_mul {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g * Δ ^ m) :=
  h.mdiff.mul (mdifferentiable_disc.pow m)

private theorem RatAt.analyticAt {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : AnalyticAt ℂ (cuspFunction N (g * Δ ^ m)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) h.periodic h.mdiff_mul h.bdd

private theorem analyticAt_disc : AnalyticAt ℂ (cuspFunction N (Δ : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) (periodic_ofComplex_natCast periodic_disc_one N)
    mdifferentiable_disc isBoundedAtImInfty_disc

private theorem RatAt.succ {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K (m + 1) g where
  mdiff := h.mdiff
  periodic := by
    rw [pow_succ, ← mul_assoc]
    exact periodic_mul h.periodic (periodic_ofComplex_natCast periodic_disc_one N)
  bdd := by rw [pow_succ, ← mul_assoc]; exact h.bdd.mul isBoundedAtImInfty_disc
  mem := by
    intro n
    rw [pow_succ, ← mul_assoc, qExpansion_mul h.analyticAt analyticAt_disc, PowerSeries.coeff_mul]
    refine sum_mem fun ij _ => mul_mem (h.mem _) ?_
    obtain ⟨r, hr⟩ := qExpansion_disc_rat N ij.2
    rw [hr]; exact ratCast_mem K r

private theorem RatAt.of_le {m m' : ℕ} (hm : m ≤ m') {g : ℍ → ℂ} (h : RatAt N K m g) : RatAt N K m' g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => simpa using h
  | succ d ih => exact (ih (Nat.le_add_right m d)).succ

private theorem RatAt.exists_map {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) :
    ∃ p : PowerSeries K, p.map (algebraMap K ℂ) = qExpansion N (g * Δ ^ m) := by
  refine ⟨PowerSeries.mk fun n => ⟨_, h.mem n⟩, ?_⟩
  ext n
  simp

private theorem RatAt.qExpansion_ne_zero {m : ℕ} {g : ℍ → ℂ} (h : RatAt N K m g) (hg : g ≠ 0) :
    qExpansion N (g * Δ ^ m) ≠ 0 := by
  rw [Ne, qExpansion_eq_zero_iff (natCast_pos N) h.periodic h.mdiff_mul h.bdd]
  intro h0
  apply hg
  funext τ
  have := congrFun h0 τ
  simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at this
  rcases this with h1 | h1
  · exact h1
  · exact absurd h1 (disc_pow_ne_zero m τ)

private theorem exists_discSeries : ∃ δ : PowerSeries K, δ.map (algebraMap K ℂ) = qExpansion N (Δ : ℍ → ℂ) ∧
    δ.map φ = qExpansion N (Δ : ℍ → ℂ) := by
  choose r hr using qExpansion_disc_rat N
  refine ⟨PowerSeries.mk fun n => ⟨(r n : ℂ), ratCast_mem K (r n)⟩, ?_, ?_⟩
  · ext n; simp [hr n]
  · ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hr n]
    have : (⟨(r n : ℂ), ratCast_mem K (r n)⟩ : K) = algebraMap ℚ K (r n) := by
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
