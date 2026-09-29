/-
  The Fricke function vocabulary: the denominator row `denomZ`, the row action
  `vecMulSL`, and `frickeF` itself (defined from the ℘-normalised `wpNorm`).

  Shared by the `WLight` Fricke packages and the level-fraction packages; lifted
  from the repeated `private` prelude (`P2M/Sol/S_WLight_frickeFunction_*`,
  `S_WLight_levelFraction_*`, pinned `aa2d8b3`).  The slash-invariance lemmas stay
  in the consumers, because they consume the torsion-point package that sits above
  this module.  Namespace `WLight`.
-/
import FLTForHuman.ModularForms.WeightOne.Defs.PTorsion
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Unramified.Field
import FLTForHuman.ModularForms.DiscPow

noncomputable section

open Complex Real

open scoped UpperHalfPlane Manifold MatrixGroups ModularForm
open UpperHalfPlane hiding I
open Matrix.SpecialLinearGroup
open ModularForm CuspForm ModularForm.CuspForm Polynomial Real.Polynomial Filter
open PeriodPair

namespace WLight

def denomZ (γ : SL(2, ℤ)) (τ : ℂ) : ℂ := (γ 1 0 : ℤ) * τ + (γ 1 1 : ℤ)

lemma denomZ_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : denomZ γ (τ : ℂ) ≠ 0 := by
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

def vecMulSL (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : Fin 2 → ZMod N :=
  Matrix.vecMul a ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))

lemma vecMulSL_apply (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (j : Fin 2) :
    vecMulSL N a γ j = a 0 * (γ 0 j : ℤ) + a 1 * (γ 1 j : ℤ) := by
  simp [vecMulSL, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]

lemma vecMulSL_of_mem_Gamma {N : ℕ} (a : Fin 2 → ZMod N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) : vecMulSL N a γ = a := by
  obtain ⟨h₀₀, h₀₁, h₁₀, h₁₁⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  funext j
  fin_cases j <;> simp [vecMulSL_apply, h₀₀, h₀₁, h₁₀, h₁₁]

lemma denom_mapGL_eq_denomZ (γ : SL(2, ℤ)) (τ : ℍ) :
    denom (mapGL ℝ γ) τ = denomZ γ τ := by
  simp [denom, denomZ]

def wpNormZ (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ := wpNorm N (a 0).val (a 1).val τ

def frickeF (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * wpNormZ N a τ

lemma vecMulSL_mul (N : ℕ) (a : Fin 2 → ZMod N) (γ δ : SL(2, ℤ)) :
    vecMulSL N a (γ * δ) = vecMulSL N (vecMulSL N a γ) δ := by
  have hmap : ((γ * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) *
        (δ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact Matrix.map_mul (f := Int.castRingHom (ZMod N))
  simp only [vecMulSL, hmap, Matrix.vecMul_vecMul]

lemma vecMulSL_one (N : ℕ) (a : Fin 2 → ZMod N) : vecMulSL N a 1 = a := by
  simp [vecMulSL]

lemma vecMulSL_zero (N : ℕ) (γ : SL(2, ℤ)) : vecMulSL N 0 γ = 0 := by
  funext j; simp [vecMulSL_apply]

lemma vecMulSL_ne_zero {N : ℕ} {a : Fin 2 → ZMod N} (ha : a ≠ 0) (γ : SL(2, ℤ)) :
    vecMulSL N a γ ≠ 0 := by
  intro h
  apply ha
  have := congrArg (fun b ↦ vecMulSL N b γ⁻¹) h
  simpa [← vecMulSL_mul, vecMulSL_one, vecMulSL_zero] using this

abbrev FrickeIdx (N : ℕ) : Type := {a : Fin 2 → ZMod N // a ≠ 0}

scoped instance (N : ℕ) [NeZero N] : Fintype (FrickeIdx N) := by unfold FrickeIdx; infer_instance

theorem mem_Gamma_or_neg_mem_of_vecMulSL {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (h : ∀ a : Fin 2 → ZMod N, a ≠ 0 → vecMulSL N a γ = a ∨ vecMulSL N a γ = -a) :
    γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N := by
  rcases Nat.lt_or_ge 1 N with hN | hN
  · have : Fact (1 < N) := ⟨hN⟩
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

section FixedDivShare

open Function

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G A]

/-- A product over a group is fixed by every group element. -/
lemma smul_prod_smul_eq (v : A) (g₀ : G) : g₀ • (∏ g : G, g • v) = ∏ g : G, g • v := by
  rw [show g₀ • (∏ g : G, g • v) = MulSemiringAction.toRingHom G A g₀ (∏ g : G, g • v) from rfl,
    map_prod]
  simp only [MulSemiringAction.toRingHom_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g₀) _ _ fun g ↦ rfl

variable [IsDomain A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  [MulSemiringAction G K]

/-- A group-fixed element of a fraction ring is a quotient of fixed elements — the
algebra lemma the Fricke/level packages each re-proved. -/
theorem exists_fixed_div_of_fixed
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

end FixedDivShare


section PoleBoundedShare

open scoped UpperHalfPlane Manifold ModularForm
open UpperHalfPlane
open Filter

def PoleBounded (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ ∃ m : ℕ, IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)

lemma poleBounded_algebraMap (r : ℂ) : PoleBounded (algebraMap ℂ (ℍ → ℂ) r) := by
  refine ⟨mdifferentiable_const, 0, ?_⟩
  have hshape : ((algebraMap ℂ (ℍ → ℂ) r) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      fun _ => r := by
    funext τ
    simp
  rw [hshape]
  exact const_boundedAtFilter _ r

lemma PoleBounded.add {f g : ℍ → ℂ} (hf : PoleBounded f) (hg : PoleBounded g) :
    PoleBounded (f + g) := by
  obtain ⟨hf1, m1, hf2⟩ := hf
  obtain ⟨hg1, m2, hg2⟩ := hg
  refine ⟨hf1.add hg1, max m1 m2, ?_⟩
  have hshape : ((f + g) * ⇑CuspForm.discriminant ^ max m1 m2 : ℍ → ℂ) =
      f * ⇑CuspForm.discriminant ^ max m1 m2 + g * ⇑CuspForm.discriminant ^ max m1 m2 := by
    funext τ
    simp [add_mul]
  rw [hshape]
  exact (UpperHalfPlaneAux.IsBoundedAtImInfty.mul_discPow_mono (le_max_left _ _) hf2).add
    (UpperHalfPlaneAux.IsBoundedAtImInfty.mul_discPow_mono (le_max_right _ _) hg2)

lemma PoleBounded.mul {f g : ℍ → ℂ} (hf : PoleBounded f) (hg : PoleBounded g) :
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

theorem poleBounded_of_mem_adjoin {S : Set (ℍ → ℂ)} (hS : ∀ f ∈ S, PoleBounded f)
    {a : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ S) : PoleBounded a := by
  induction ha using Algebra.adjoin_induction with
  | mem f hf => exact hS f hf
  | algebraMap r => exact poleBounded_algebraMap r
  | add x y hx hy ihx ihy => exact ihx.add ihy
  | mul x y hx hy ihx ihy => exact ihx.mul ihy

end PoleBoundedShare

section CoeffXSubCShare

/-- The coefficient of `(X - C a) * p`: a generic polynomial identity the orbit
package and the level-fraction packages each re-proved. -/
lemma coeff_X_sub_C_mul (a : ℂ) (p : Polynomial ℂ) (k : ℕ) :
    ((X - C a) * p).coeff k = (if k = 0 then 0 else p.coeff (k - 1)) - a * p.coeff k := by
  rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  congr 1
  cases k with
  | zero => simp [Polynomial.mul_coeff_zero]
  | succ k' => simp [Polynomial.coeff_X_mul]

end CoeffXSubCShare



section OrbitProdShare

open scoped UpperHalfPlane Manifold ModularForm
open UpperHalfPlane
open Filter Polynomial

variable {I : Type*} [Fintype I] (h : I → ℍ → ℂ) (m : ℕ)

omit [Fintype I] in
lemma bounded_orbitCoeff_prod
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

end OrbitProdShare

end WLight
