/-
  The integral-slash Γ₁-basis (SET-11 order 2).

  Statements verbatim from the pinned wrappers
  `Theorems/Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even.lean`,
  `Theorems/Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp.lean`,
  `Theorems/Thm_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean`
  and
  `Theorems/Thm_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast.lean`;
  proofs transcribed from the matching `P2M/Sol/S_*` files (128 + 458 + 261 +
  183 lines) and adapted to mathlib `v4.34.0`.

  Order 1's `Gamma1Basis.lean` is imported and supplies
  `CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top`,
  `ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq` and
  `CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply`.  Each pin file's helpers
  stay `private` in the pin's own inner namespace (`GammaOneCyclotomicEven` /
  `GammaOneCyclotomic` / `GammaOneRationalStructure` / `DeligneSerre271`),
  nested in this module's `WLightS11.S_*` namespaces; the four headlines are the
  module's only public surface.  Inside the module the dependency chain is
  `adjoin_exp_of_even → adjoin_exp → ratCast → slash_intCast`; the last is the
  capstone's input.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast.lean

  The pin's `set_option maxHeartbeats` bumps are **not** transcribed (the
  project's global `maxHeartbeats` cap is 4,000,000).
-/

import FLTForHuman.ModularForms.WeightOne.Gamma1Basis
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Geometry.Manifold.Notation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
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
import FLTForHuman.ModularForms.WeightOne.Basic
import FLTForHuman.ModularForms.WeightOne.MonicRel
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import FLTForHuman.ModularForms.WeightOne.FrickeFunction
import FLTForHuman.ModularForms.WeightOne.LevelFraction
import FLTForHuman.ModularForms.WeightOne.LevelN
import FLTForHuman.ModularForms.WeightOne.EisensteinSeries
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.WeightOne.Gamma0Rationality
import FLTForHuman.ModularForms.WeightOne.Gamma0Integral
import FLTForHuman.ModularForms.JqAnalyticModel
import FLTForHuman.ModularCurve.Defs.Jq

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section

open Complex Real UpperHalfPlane ModularForm CongruenceSubgroup
open scoped Real Manifold MatrixGroups ModularForm Topology UpperHalfPlane

namespace WLightS11.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup
open scoped Real MatrixGroups ModularForm

namespace GammaOneCyclotomicEven

private def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp at h1 h2
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 τ.im_pos.ne'
    subst hs
    simp at h2
    exact ⟨rfl, h2⟩

private theorem tauPair_spec (τ : ℍ) : (tauPair τ).ω₁ = (τ : ℂ) ∧ (tauPair τ).ω₂ = 1 := ⟨rfl, rfl⟩

variable (N : ℕ)

private def WW (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))

private def fricke (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ

private def jf (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

private theorem WW_spec (v : Fin 2 → ZMod N) (τ : ℍ) : WW N v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (tauPair τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)) := rfl

private theorem fricke_spec (v : Fin 2 → ZMod N) (τ : ℍ) : fricke N v τ =
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * WW N v τ := rfl

private theorem jf_spec (τ : ℍ) : jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := rfl

private def kN : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}

private theorem kN_eq : kN N = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} := rfl

private theorem Gamma_le_Gamma1 : CongruenceSubgroup.Gamma N ≤ Gamma1 N := by
  intro g hg
  rw [Gamma_mem] at hg
  rw [Gamma1_mem]
  exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩

private theorem exists_abm {k : ℤ} (hk : Even k) :
    ∃ a b m : ℕ, k + 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (m : ℤ) := by
  obtain ⟨r, rfl⟩ := hk
  rcases le_or_gt 0 r with hr | hr
  · refine ⟨r.toNat, r.toNat, r.toNat, ?_⟩
    rw [Int.toNat_of_nonneg hr]; ring
  · refine ⟨2 * (-r).toNat, (-r).toNat, (-r).toNat, ?_⟩
    have h : ((-r).toNat : ℤ) = -r := Int.toNat_of_nonneg (by omega)
    push_cast
    rw [h]; ring

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

private theorem main (N : ℕ) [NeZero N] (k : ℤ) (hk : Even k) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ kN N := by
  classical
  obtain ⟨a, b, m, habm⟩ := exists_abm hk

  set S : Set (CuspForm (Γ₁ℝ N) k) := {f : CuspForm (Γ₁ℝ N) k |
      ∃ P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ,
        (∀ mo, P.coeff mo ∈ kN N) ∧ (∀ mo, Q.coeff mo ∈ kN N) ∧
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke N v.1) Q ≠ 0 ∧
        ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke N v.1) Q τ =
          ModularForm.discriminant τ ^ m *
            MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
              o.elim jf fun v => fricke N v.1) P τ} with hS
  have hspan : Submodule.span ℂ S = ⊤ :=
    CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top N tauPair tauPair_spec (WW N) (WW_spec N)
      (fricke N) (fricke_spec N) jf jf_spec (kN N) (kN_eq N) (Gamma1 N) (Gamma_le_Gamma1 N) k a b m habm

  have hcoef : ∀ f ∈ S, ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ kN N := by
    rintro f ⟨P, Q, hP, hQ, hQ0, hid⟩ n
    exact ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational N tauPair tauPair_spec (WW N) (WW_spec N)
      (fricke N) (fricke_spec N) jf jf_spec (kN N) (kN_eq N) k a b m (f : ModularForm (Γ₁ℝ N) k) P Q hP hQ
      hQ0 hid n

  haveI : FiniteDimensional ℂ (CuspForm (Γ₁ℝ N) k) := CuspForm.finiteDimensional_of_isArithmetic _ k
  obtain ⟨t, ht_sub, ht_span, ht_ind⟩ := exists_linearIndependent ℂ S
  have ht_fin : t.Finite := LinearIndependent.set_finite_of_isNoetherian ht_ind
  letI : Fintype t := ht_fin.fintype
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : t → CuspForm (Γ₁ℝ N) k)) := by
    rw [Subtype.range_coe, ht_span, hspan]
  let B : Module.Basis t ℂ (CuspForm (Γ₁ℝ N) k) := Module.Basis.mk ht_ind htop
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  refine ⟨Fintype.card t, B.reindex e, fun i n => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  exact hcoef _ (ht_sub (e.symm i).2) n

end GammaOneCyclotomicEven

end

theorem _root_.CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even (N : ℕ) [NeZero N] (k : ℤ)
    (hk : Even k) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} :=
  GammaOneCyclotomicEven.main N k hk

end WLightS11.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even

namespace WLightS11.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp

set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Filter Topology
open scoped MatrixGroups ModularForm Manifold

namespace GammaOneCyclotomic

section FieldFacts

variable (K : IntermediateField ℚ ℂ)

private theorem mem_of_forall_algEquiv_apply_eq (x : ℂ) (hx : ∀ σ : ℂ ≃ₐ[K] ℂ, σ x = x) : x ∈ K := by
  by_contra hxK
  have hx' : x ∉ Set.range (algebraMap K ℂ) := by
    rintro ⟨y, rfl⟩
    exact hxK y.2
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range hx'
  exact hσ (hx σ)

private theorem algEquiv_apply_of_mem (σ : ℂ ≃ₐ[K] ℂ) {x : ℂ} (hx : x ∈ K) : σ x = x :=
  σ.commutes ⟨x, hx⟩

end FieldFacts

section Descent

variable (K : IntermediateField ℚ ℂ) {V : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] {ι : Type*} (c : ι → V →ₗ[ℂ] ℂ)

private theorem span_range_eq_top (hc : ∀ v : V, (∀ i, c i v = 0) → v = 0) :
    Submodule.span ℂ (Set.range c) = ⊤ := by
  set W : Submodule ℂ (Module.Dual ℂ V) := Submodule.span ℂ (Set.range c) with hWdef
  have hW : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_dualCoannihilator] at hv
    rw [Submodule.mem_bot]
    exact hc v fun i => hv (c i) (Submodule.subset_span ⟨i, rfl⟩)
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
  rw [hW, Submodule.dualAnnihilator_bot] at h
  exact h.symm

private theorem exists_basis_of_stable (hc : ∀ v : V, (∀ i, c i v = 0) → v = 0)
    (hstab : ∀ (σ : ℂ ≃ₐ[K] ℂ) (v : V), ∃ w : V, ∀ i, c i w = σ (c i v)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ V), ∀ (j : Fin n) (i : ι), c i (b j) ∈ K := by
  classical
  obtain ⟨t, ht_sub, ht_span, ht_ind⟩ := exists_linearIndependent ℂ (Set.range c)
  have ht_fin : t.Finite := LinearIndependent.set_finite_of_isNoetherian ht_ind
  letI : Fintype t := ht_fin.fintype
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : t → Module.Dual ℂ V)) := by
    rw [Subtype.range_coe, ht_span, span_range_eq_top c hc]
  let β : Module.Basis t ℂ (Module.Dual ℂ V) := Module.Basis.mk ht_ind htop

  let T : V →ₗ[ℂ] (t → ℂ) := LinearMap.pi fun i : t => (i : Module.Dual ℂ V)
  have hT_apply : ∀ (v : V) (i : t), T v i = (i : Module.Dual ℂ V) v := fun v i => rfl
  have hT_inj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hc v
    intro i
    have hmem : c i ∈ Submodule.span ℂ t := by
      rw [ht_span]; exact Submodule.subset_span ⟨i, rfl⟩
    refine Submodule.span_induction (p := fun φ _ => φ v = 0) ?_ ?_ ?_ ?_ hmem
    · intro φ hφ
      have := congrFun hv ⟨φ, hφ⟩
      simpa [hT_apply] using this
    · simp
    · intro φ ψ _ _ h₁ h₂
      simp [h₁, h₂]
    · intro a φ _ h
      simp [h]
  have hdim : Module.finrank ℂ V = Module.finrank ℂ (t → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, ← Subspace.dual_finrank_eq,
      Module.finrank_eq_card_basis β]
  let e : V ≃ₗ[ℂ] (t → ℂ) := T.linearEquivOfInjective hT_inj hdim
  have he_apply : ∀ (v : V) (i : t), e v i = (i : Module.Dual ℂ V) v := fun v i => rfl
  let b₀ : Module.Basis t ℂ V := (Pi.basisFun ℂ t).map e.symm
  have hb₀ : ∀ j i : t, (i : Module.Dual ℂ V) (b₀ j) = if i = j then 1 else 0 := by
    intro j i
    rw [← he_apply]
    simp [b₀, Pi.single_apply]

  have hfix : ∀ (σ : ℂ ≃ₐ[K] ℂ) (j : t) (i : ι), σ (c i (b₀ j)) = c i (b₀ j) := by
    intro σ j
    obtain ⟨w, hw⟩ := hstab σ (b₀ j)
    have hew : e w = e (b₀ j) := by
      funext i
      obtain ⟨i₀, hi₀⟩ := ht_sub i.2
      have h₁ := hb₀ j i
      rw [← hi₀] at h₁
      rw [he_apply, he_apply, ← hi₀, hw i₀, h₁]
      split_ifs <;> simp
    have hwj : w = b₀ j := e.injective hew
    intro i
    rw [← hw i, hwj]
  refine ⟨Fintype.card t, b₀.reindex (Fintype.equivFin t), fun j i => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact mem_of_forall_algEquiv_apply_eq K _ fun σ => hfix σ _ i

end Descent

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QExp

variable {N : ℕ} {k : ℤ}

private theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

private theorem coe_eq_of_qExpansion_eq [NeZero N] {F G : Type*} [FunLike F ℍ ℂ] [FunLike G ℍ ℂ] {a b : ℤ}
    [ModularFormClass F (Γ₁ℝ N) a] [ModularFormClass G (Γ₁ℝ N) b] (f : F) (g : G)
    (h : qExpansion 1 (⇑f) = qExpansion 1 (⇑g)) : (⇑f : ℍ → ℂ) = ⇑g := by
  funext τ
  have hf := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods N))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  have hg := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex g (one_mem_strictPeriods N))
    (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g) τ
  rw [h] at hf
  exact hf.unique hg

private theorem eq_of_qExpansion_eq [NeZero N] (f g : CuspForm (Γ₁ℝ N) k)
    (h : qExpansion 1 (⇑f) = qExpansion 1 (⇑g)) : f = g :=
  DFunLike.ext' (coe_eq_of_qExpansion_eq f g h)

variable (N k) in

private def qExpLin : CuspForm (Γ₁ℝ N) k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 (⇑f)
  map_add' f g := by
    rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) f g]
  map_smul' a f := by
    rw [FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) a f, RingHom.id_apply]

@[scoped simp] private theorem qExpLin_apply (f : CuspForm (Γ₁ℝ N) k) : qExpLin N k f = qExpansion 1 (⇑f) := rfl

private theorem coe_modularForm (f : CuspForm (Γ₁ℝ N) k) :
    (⇑(ModularFormClass.modularForm f : ModularForm (Γ₁ℝ N) k) : ℍ → ℂ) = ⇑f := rfl

private theorem coe_mulModularForm {a b : ℤ} (f : CuspForm (Γ₁ℝ N) a) (g : ModularForm (Γ₁ℝ N) b) :
    (⇑(f.mulModularForm g) : ℍ → ℂ) = ⇑f * ⇑g := rfl

private theorem qExpansion_mulModularForm {a b : ℤ} (f : CuspForm (Γ₁ℝ N) a) (g : ModularForm (Γ₁ℝ N) b) :
    qExpansion 1 (⇑(f.mulModularForm g)) = qExpansion 1 (⇑f) * qExpansion 1 (⇑g) := by
  rw [coe_mulModularForm]
  exact ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods N) f g

end QExp

private def Stab (K : IntermediateField ℚ ℂ) (N : ℕ) (k : ℤ) : Prop :=
  ∀ (σ : ℂ ≃ₐ[K] ℂ) (f : CuspForm (Γ₁ℝ N) k),
    ∃ f' : CuspForm (Γ₁ℝ N) k, qExpansion 1 (⇑f') = (qExpansion 1 (⇑f)).map (σ : ℂ →+* ℂ)

section Stability

variable (K : IntermediateField ℚ ℂ) {N : ℕ} {k : ℤ}

private theorem stab_of_basis {n : ℕ} (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ N) k))
    (hb : ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ K) : Stab K N k := by
  intro σ f
  set r : Fin n → ℂ := fun i => b.repr f i with hr
  have hf : f = ∑ i, r i • b i := by simp [hr]
  refine ⟨∑ i, σ (r i) • b i, ?_⟩
  have key : ∀ s : Fin n → ℂ,
      qExpansion 1 (⇑(∑ i, s i • b i)) = ∑ i, s i • qExpansion 1 (⇑(b i)) := by
    intro s
    change qExpLin N k (∑ i, s i • b i) = ∑ i, s i • qExpLin N k (b i)
    simp [map_sum, map_smul]
  conv_rhs => rw [hf]
  rw [key, key]
  ext m
  simp only [map_sum, map_smul, smul_eq_mul, PowerSeries.coeff_map, RingHom.coe_coe, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact (algEquiv_apply_of_mem K σ (hb i m)).symm

private theorem stab_of_forall_eq_zero (h : ∀ f : CuspForm (Γ₁ℝ N) k, f = 0) : Stab K N k := by
  intro σ f
  refine ⟨0, ?_⟩
  rw [h f, FunLike.coe_zero, qExpansion_zero, map_zero]

private theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) :=
    (UpperHalfPlane.mdifferentiableAt_iff.1 (hv τ₀)).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hne : ∀ᶠ z in 𝓝 (τ₀ : ℂ), (v ∘ ofComplex) z ≠ 0 := hvc.eventually_ne hv0'
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hne] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hana : AnalyticOnNhd ℂ (u ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd isOpen_upperHalfPlaneSet
  have hEq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  have := hEq τ.im_pos
  simpa [Function.comp, ofComplex_apply] using this

private theorem isZeroAtImInfty_of_mul_self {g : ℍ → ℂ} (h : IsZeroAtImInfty (g * g)) :
    IsZeroAtImInfty g := by
  rw [UpperHalfPlane.IsZeroAtImInfty, Filter.ZeroAtFilter] at h ⊢
  have h₁ : Tendsto (fun τ => ‖g τ‖ * ‖g τ‖) atImInfty (𝓝 0) := by
    have := tendsto_zero_iff_norm_tendsto_zero.mp h
    simpa [norm_mul] using this
  have h₂ : Tendsto (fun τ => Real.sqrt (‖g τ‖ * ‖g τ‖)) atImInfty (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h₁
    simpa [Function.comp_def] using this
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (h₂.congr fun τ => ?_)
  exact Real.sqrt_mul_self (norm_nonneg _)

variable [NeZero N]

private theorem stab_of_anchor {w : ℤ} (E : ModularForm (Γ₁ℝ N) w) (hE : E ≠ 0)
    (hEK : ∀ σ : ℂ ≃ₐ[K] ℂ, (qExpansion 1 (⇑E)).map (σ : ℂ →+* ℂ) = qExpansion 1 (⇑E))
    (h1 : Stab K N (k + w)) (h2 : Stab K N (k + k)) : Stab K N k := by
  classical
  intro σ f
  set φh : PowerSeries ℂ := (qExpansion 1 (⇑f)).map (σ : ℂ →+* ℂ) with hφh

  obtain ⟨G, hG⟩ := h1 σ (f.mulModularForm E)
  obtain ⟨H, hH⟩ := h2 σ (f.mulModularForm (ModularFormClass.modularForm f))
  have hQE : qExpansion 1 (⇑E) ≠ 0 := fun h =>
    hE ((ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N) E).mp h)
  have hG' : qExpansion 1 (⇑G) = φh * qExpansion 1 (⇑E) := by
    rw [hG, qExpansion_mulModularForm, map_mul, hEK]
  have hH' : qExpansion 1 (⇑H) = φh * φh := by
    rw [hH, qExpansion_mulModularForm, coe_modularForm, map_mul]

  have hval : ∀ τ : ℍ, G τ * G τ = H τ * E τ * E τ := by
    have hq : qExpansion 1 (⇑(G.mulModularForm (ModularFormClass.modularForm G))) =
        qExpansion 1 (⇑((H.mulModularForm E).mulModularForm E)) := by
      rw [qExpansion_mulModularForm, qExpansion_mulModularForm, qExpansion_mulModularForm,
        coe_modularForm, hG', hH']
      ring
    have hfun := coe_eq_of_qExpansion_eq _ _ hq
    intro τ
    have hτ := congrFun hfun τ
    simpa [coe_mulModularForm, coe_modularForm, mul_assoc] using hτ

  have hEfun : (⇑E : ℍ → ℂ) ≠ 0 := by
    intro h0
    exact hE ((FunLike.coe_zero_iff E).mp h0)
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℍ, E τ₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hEfun (funext hcon)
  have hEhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑E) := ModularFormClass.holo E
  have hGhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑G) := ModularFormClass.holo G
  have hHhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑H) := ModularFormClass.holo H
  let cc : ℕ → ℍ → ℂ := fun i => if i = 0 then -⇑H else 0
  have hcc : ∀ i < 2, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cc i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [cc, hi] using hHhol.neg
    · have h__af := (mdifferentiable_const : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun _ : ℍ => (0 : ℂ))
      simp [cc, hi] at h__af ⊢
      exact h__af
  have hrel : (⇑G) ^ 2 + ∑ i ∈ Finset.range 2, cc i * (⇑E) ^ (2 - i) * (⇑G) ^ i = 0 := by
    funext τ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      Pi.zero_apply, cc, ite_true, show (1 : ℕ) ≠ 0 from one_ne_zero, ite_false, Pi.neg_apply]
    rw [pow_two, hval τ]; ring
  obtain ⟨φ, hφhol, hφE⟩ := WLight.exists_mdifferentiable_div_of_monicRel hGhol hEhol hEfun hcc hrel
  have hφE' : ∀ τ : ℍ, φ τ * E τ = G τ := fun τ => congrFun hφE τ

  have hφsq : ∀ τ : ℍ, φ τ * φ τ = H τ := by
    have hzero : ∀ τ : ℍ, (φ τ * φ τ - H τ) * (E τ * E τ) = 0 := by
      intro τ
      have h := hval τ
      rw [← hφE' τ] at h
      linear_combination h
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => φ τ * φ τ - H τ) := (hφhol.mul hφhol).sub hHhol
    have hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => E τ * E τ) := hEhol.mul hEhol
    have := eq_zero_of_mul_eq_zero hdiff hv hzero (τ₀ := τ₀) (mul_ne_zero hτ₀ hτ₀)
    intro τ
    exact sub_eq_zero.mp (congrFun this τ)

  have hinv : ∀ γ ∈ Gamma1 N, φ ∣[k] γ = φ := by
    intro γ hγ
    have hGγ : (⇑G : ℍ → ℂ) ∣[k + w] γ = ⇑G := by
      have := SlashInvariantForm.slash_action_eqn G (γ : GL (Fin 2) ℝ) (Subgroup.mem_map_of_mem _ hγ)
      simpa [ModularForm.SL_slash] using this
    have hEγ : (⇑E : ℍ → ℂ) ∣[w] γ = ⇑E := by
      have := SlashInvariantForm.slash_action_eqn E (γ : GL (Fin 2) ℝ) (Subgroup.mem_map_of_mem _ hγ)
      simpa [ModularForm.SL_slash] using this
    have hprod : (φ ∣[k] γ) * ⇑E = φ * ⇑E := by
      have h := ModularForm.mul_slash_SL2 k w γ φ ⇑E
      rw [hEγ, hφE, hGγ] at h
      rw [hφE]; exact h.symm
    have hzero : ∀ τ : ℍ, ((φ ∣[k] γ) τ - φ τ) * E τ = 0 := by
      intro τ
      have := congrFun hprod τ
      simp only [Pi.mul_apply] at this
      linear_combination this
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (φ ∣[k] γ) τ - φ τ) := by
      have h₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (φ ∣[k] γ) := by
        rw [ModularForm.SL_slash]; exact hφhol.slash k _
      exact h₁.sub hφhol
    have := eq_zero_of_mul_eq_zero hdiff hEhol hzero hτ₀
    funext τ
    exact sub_eq_zero.mp (by simpa using congrFun this τ)

  have hcusp : ∀ A : SL(2, ℤ), IsZeroAtImInfty (φ ∣[k] A) := by
    intro A
    apply isZeroAtImInfty_of_mul_self
    have hφφ : φ * φ = ⇑H := funext fun τ => hφsq τ
    have h := ModularForm.mul_slash_SL2 k k A φ φ
    rw [hφφ] at h
    rw [← h]
    exact CuspFormClass.zero_at_infty_slash H A

  let φC : CuspForm (Γ₁ℝ N) k :=
    { toFun := φ
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        have := hinv γ hγ
        rwa [ModularForm.SL_slash] at this
      holo' := hφhol
      zero_at_cusps' := fun {c} hc =>
        (OnePoint.isZeroAt_iff_forall_SL2Z
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)).mpr fun A _ => hcusp A }
  refine ⟨φC, ?_⟩
  have hprod : qExpansion 1 (⇑φC) * qExpansion 1 (⇑E) = φh * qExpansion 1 (⇑E) := by
    rw [← hG', ← qExpansion_mulModularForm, coe_mulModularForm]
    exact congrArg (qExpansion 1) hφE
  exact mul_right_cancel₀ hQE hprod

private theorem exists_basis_of_stab (h : Stab K N k) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ K := by
  haveI : FiniteDimensional ℂ (CuspForm (Γ₁ℝ N) k) := CuspForm.finiteDimensional_of_isArithmetic _ k
  let c : ℕ → CuspForm (Γ₁ℝ N) k →ₗ[ℂ] ℂ := fun m => (PowerSeries.coeff m).comp (qExpLin N k)
  have hc_apply : ∀ (m : ℕ) (f : CuspForm (Γ₁ℝ N) k),
      c m f = PowerSeries.coeff m (qExpansion 1 (⇑f)) := fun m f => rfl
  have hc : ∀ f : CuspForm (Γ₁ℝ N) k, (∀ m, c m f = 0) → f = 0 := by
    intro f hf
    refine eq_of_qExpansion_eq f 0 ?_
    ext m
    rw [FunLike.coe_zero, qExpansion_zero, map_zero, ← hc_apply, hf m]
  have hstab : ∀ (σ : ℂ ≃ₐ[K] ℂ) (f : CuspForm (Γ₁ℝ N) k),
      ∃ f' : CuspForm (Γ₁ℝ N) k, ∀ m, c m f' = σ (c m f) := by
    intro σ f
    obtain ⟨f', hf'⟩ := h σ f
    refine ⟨f', fun m => ?_⟩
    rw [hc_apply, hc_apply, hf', PowerSeries.coeff_map, RingHom.coe_coe]
  obtain ⟨n, b, hb⟩ := exists_basis_of_stable K c hc hstab
  exact ⟨n, b, fun i m => hb i m⟩

end Stability

section Assembly

variable (N : ℕ)

private def kN : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))}

private theorem anchor [NeZero N] (h10 : (1 : ZMod N) ≠ 0) (h11 : (1 : ZMod N) ≠ -1) :
    ∃ E : ModularForm (Γ₁ℝ N) ((3 : ℕ) : ℤ), E ≠ 0 ∧
      ∀ σ' : ℂ →+* ℂ, (qExpansion 1 (⇑E)).map σ' = qExpansion 1 (⇑E) := by
  classical
  obtain ⟨G, hG, -⟩ := ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq N 3 le_rfl
  have hint := hG 1 h10
  rw [ModularCurve.IsIntegralQExp] at hint
  refine ⟨G 1, ?_, fun σ' => ?_⟩
  · intro h0
    have h1 := congrArg (PowerSeries.coeff 1) hint
    rw [h0, FunLike.coe_zero, qExpansion_zero, map_zero, PowerSeries.coeff_map,
      PowerSeries.coeff_mk] at h1
    simp [Nat.divisors_one, Finset.filter_singleton, h11] at h1
  · rw [← hint]
    ext n
    simp only [PowerSeries.coeff_map]
    exact (RingHom.congr_fun (RingHom.ext_int (σ'.comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ)) _)

private theorem neg_one_mem_Gamma1 (hN : N ∣ 2) : (-1 : SL(2, ℤ)) ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have h2 : ((2 : ℕ) : ZMod N) = 0 := (ZMod.natCast_eq_zero_iff 2 N).mpr hN
  have hneg : ((-1 : ℤ) : ZMod N) = 1 := by
    have h11 : (1 : ZMod N) + 1 = 0 := by simpa [one_add_one_eq_two] using h2
    push_cast
    linear_combination -h11
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Matrix.SpecialLinearGroup.coe_neg, hneg]

private theorem neg_one_mem_Gamma1GL (hN : N ∣ 2) : (-1 : GL (Fin 2) ℝ) ∈ Γ₁ℝ N := by
  refine Subgroup.mem_map.mpr ⟨-1, neg_one_mem_Gamma1 N hN, ?_⟩
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  fin_cases i <;> fin_cases j <;> simp [Units.val_neg]

private theorem main [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ kN N := by
  rcases Int.even_or_odd k with hk | hk
  · exact CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even N k hk
  by_cases hN : N ∣ 2
  ·
    refine exists_basis_of_stab (kN N) (stab_of_forall_eq_zero (kN N) fun f => ?_)
    have h := ModularForm.eq_zero_of_neg_one_mem (neg_one_mem_Gamma1GL N hN) hk
      (ModularFormClass.modularForm f)
    have hcoe : (⇑f : ℍ → ℂ) = 0 := by
      rw [← coe_modularForm f, h, FunLike.coe_zero]
    exact DFunLike.ext' (by rw [hcoe, FunLike.coe_zero])
  ·
    have h10 : (1 : ZMod N) ≠ 0 := by
      intro h
      have hN1 : N ∣ 1 := (ZMod.natCast_eq_zero_iff 1 N).mp (by simpa using h)
      exact hN ((Nat.dvd_one.mp hN1).symm ▸ one_dvd 2)
    have h11 : (1 : ZMod N) ≠ -1 := by
      intro h
      have h2 : ((2 : ℕ) : ZMod N) = 0 := by
        rw [Nat.cast_two, ← one_add_one_eq_two]
        nth_rewrite 2 [h]
        exact add_neg_cancel 1
      exact hN ((ZMod.natCast_eq_zero_iff 2 N).mp h2)
    obtain ⟨E, hE0, hEfix⟩ := anchor N h10 h11
    have heven : ∀ k' : ℤ, Even k' → Stab (kN N) N k' := fun k' hk' => by
      obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even N k' hk'
      exact stab_of_basis (kN N) b hb
    have hk3 : Even (k + ((3 : ℕ) : ℤ)) := by
      push_cast
      exact hk.add_odd ⟨1, by norm_num⟩
    have hs : Stab (kN N) N k :=
      stab_of_anchor (kN N) E hE0 (fun σ => hEfix _) (heven _ hk3) (heven _ ⟨k, rfl⟩)
    exact exists_basis_of_stab (kN N) hs

end Assembly

end GammaOneCyclotomic

end

theorem _root_.CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} :=
  GammaOneCyclotomic.main N k

end WLightS11.S_CuspForm_exists_basis_gamma1_qCoeff_mem_adjoin_exp

namespace WLightS11.S_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast


set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GammaOneRationalStructure

variable (N : ℕ)

private def zetaN : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))

private def kN : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

private theorem kN_eq : kN N = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} :=
  rfl

section Cyclo

variable [NeZero N]

private theorem isPrimitiveRoot_zetaN : IsPrimitiveRoot (zetaN N) N :=
  Complex.isPrimitiveRoot_exp N (NeZero.ne N)

scoped instance instIsCyclotomic : IsCyclotomicExtension {N} ℚ (kN N) := by
  have hζ := isPrimitiveRoot_zetaN N
  change IsCyclotomicExtension {N} ℚ (IntermediateField.adjoin ℚ {zetaN N}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (hζ.isIntegral (NeZero.pos N)).tower_top.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ

scoped instance instIsGalois : IsGalois ℚ (kN N) := IsCyclotomicExtension.isGalois {N} ℚ (kN N)

scoped instance instFiniteDimensional : FiniteDimensional ℚ (kN N) :=
  IsCyclotomicExtension.finiteDimensional {N} ℚ (kN N)

omit [NeZero N] in

private theorem coe_algebraMap_rat (r : ℚ) : ((algebraMap ℚ (kN N) r : kN N) : ℂ) = (r : ℂ) := by
  rw [eq_ratCast (algebraMap ℚ (kN N)) r, SubfieldClass.coe_ratCast]

private theorem exists_rat_sum_aut (x : kN N) :
    ∃ r : ℚ, (∑ σ : (kN N) ≃ₐ[ℚ] (kN N), ((σ x : kN N) : ℂ)) = (r : ℂ) := by
  refine ⟨Algebra.trace ℚ (kN N) x, ?_⟩
  have h := trace_eq_sum_automorphisms (K := ℚ) (L := kN N) x
  rw [← AddSubmonoidClass.coe_finsetSum, ← h, coe_algebraMap_rat]

end Cyclo

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {N} {k : ℤ}

private theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

private def qCoeffLin (N : ℕ) (k : ℤ) (m : ℕ) : CuspForm (Γ₁ℝ N) k →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff f m
  map_add' f g := by
    change (qExpansion 1 (⇑(f + g))).coeff m = (qExpansion 1 ⇑f).coeff m + (qExpansion 1 ⇑g).coeff m
    rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) f g, map_add]
  map_smul' a f := by
    change (qExpansion 1 (⇑(a • f))).coeff m = a * (qExpansion 1 ⇑f).coeff m
    rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) a f,
      map_smul, smul_eq_mul]

@[scoped simp] private theorem qCoeffLin_apply (m : ℕ) (f : CuspForm (Γ₁ℝ N) k) :
    qCoeffLin N k m f = ModularFormClass.qCoeff f m := rfl

private theorem eq_of_qCoeff_eq [NeZero N] (f g : CuspForm (Γ₁ℝ N) k)
    (h : ∀ m : ℕ, ModularFormClass.qCoeff f m = ModularFormClass.qCoeff g m) : f = g := by
  have hsub : ∀ m, ModularFormClass.qCoeff (⇑(f - g)) m = 0 := by
    intro m
    have := (qCoeffLin N k m).map_sub f g
    simp only [qCoeffLin_apply] at this
    rw [this, h m, sub_self]
  have hq : qExpansion 1 (⇑(f - g)) = 0 := by
    ext m
    simpa [ModularFormClass.qCoeff] using hsub m
  have hzero : (⇑(f - g) : ℍ → ℂ) = 0 := by
    have hper := SlashInvariantFormClass.periodic_comp_ofComplex (f - g) (one_mem_strictPeriods N)
    have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑(f - g)) := (f - g).holo'
    have hbdd : IsBoundedAtImInfty (⇑(f - g)) := ModularFormClass.bdd_at_infty (f - g)
    exact (qExpansion_eq_zero_iff one_pos hper hhol hbdd).1 hq
  have : f - g = 0 := DFunLike.ext _ _ fun τ => by simpa using congrFun hzero τ
  exact sub_eq_zero.1 this

section Trace

variable (N) [NeZero N] (k)

private def ratForms : Set (CuspForm (Γ₁ℝ N) k) :=
  {g | ∀ m : ℕ, ModularFormClass.qCoeff g m ∈ Set.range ((↑) : ℚ → ℂ)}

variable {N k}

private theorem mem_span_ratForms (f : CuspForm (Γ₁ℝ N) k) (c : ℕ → kN N)
    (hf : ∀ m : ℕ, ModularFormClass.qCoeff f m = (c m : ℂ)) :
    f ∈ Submodule.span ℂ (ratForms N k) := by
  classical

  have hpart : ∀ σ : (kN N) ≃ₐ[ℚ] (kN N), ∃ f' : CuspForm (Γ₁ℝ N) k,
      ∀ m : ℕ, ModularFormClass.qCoeff f' m = (σ (c m) : ℂ) := fun σ =>
    CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply N k (kN N) (kN_eq N) σ f c hf
  choose fσ hfσ using hpart

  have hone : fσ 1 = f := eq_of_qCoeff_eq _ _ fun m => by rw [hfσ 1 m, hf m]; rfl

  let T : kN N → CuspForm (Γ₁ℝ N) k := fun x => ∑ σ, ((σ x : kN N) : ℂ) • fσ σ
  have hT : ∀ x, T x ∈ ratForms N k := by
    intro x m
    have hlin : ModularFormClass.qCoeff (⇑(T x)) m = ∑ σ : (kN N) ≃ₐ[ℚ] (kN N),
        ((σ x : kN N) : ℂ) * (σ (c m) : ℂ) := by
      have := map_sum (qCoeffLin N k m) (fun σ => ((σ x : kN N) : ℂ) • fσ σ) Finset.univ
      simp only [qCoeffLin_apply, map_smul, smul_eq_mul] at this
      rw [show T x = ∑ σ, ((σ x : kN N) : ℂ) • fσ σ from rfl, this]
      exact Finset.sum_congr rfl fun σ _ => by rw [hfσ σ m]
    obtain ⟨r, hr⟩ := exists_rat_sum_aut N (x * c m)
    refine ⟨r, ?_⟩
    rw [hlin, ← hr]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_mul, MulMemClass.coe_mul]

  have hded : LinearIndependent ℂ (fun σ : (kN N) ≃ₐ[ℚ] (kN N) => fun y : kN N => ((σ y : kN N) : ℂ)) := by
    have h0 := linearIndependent_monoidHom (kN N) ℂ
    let ι : ((kN N) ≃ₐ[ℚ] (kN N)) → (kN N →* ℂ) := fun σ =>
      ((algebraMap (kN N) ℂ : kN N →+* ℂ) : kN N →* ℂ).comp (σ : (kN N) ≃ₐ[ℚ] (kN N)).toRingEquiv.toMonoidHom
    have hι : Function.Injective ι := by
      intro σ τ hστ
      apply AlgEquiv.ext
      intro y
      have := DFunLike.congr_fun hστ y
      exact Subtype.ext this
    have h1 := h0.comp ι hι
    convert h1 using 1
    rfl

  set n : ℕ := Module.finrank ℚ (kN N) with hn
  let bK := Module.finBasis ℚ (kN N)
  have hcard : Fintype.card ((kN N) ≃ₐ[ℚ] (kN N)) = n := by
    rw [← Nat.card_eq_fintype_card]; exact IsGalois.card_aut_eq_finrank ℚ (kN N)
  let e : ((kN N) ≃ₐ[ℚ] (kN N)) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => (((e.symm i) (bK j) : kN N) : ℂ)

  have hinj : Function.Injective M.vecMul := by
    intro a a' haa
    have hzero : ∀ a₀ : Fin n → ℂ, M.vecMul a₀ = 0 → a₀ = 0 := by
      intro a₀ ha₀

      have hvan : ∀ y : kN N, ∑ i, a₀ i * (((e.symm i) y : kN N) : ℂ) = 0 := by
        intro y
        have hy := bK.sum_repr y
        have step : ∀ i, (((e.symm i) y : kN N) : ℂ) = ∑ j, ((bK.repr y j : ℚ) : ℂ) *
            (((e.symm i) (bK j) : kN N) : ℂ) := by
          intro i
          conv_lhs => rw [← hy, map_sum, AddSubmonoidClass.coe_finsetSum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, MulMemClass.coe_mul, coe_algebraMap_rat]
        have hj : ∀ j, ∑ i, a₀ i * (((e.symm i) (bK j) : kN N) : ℂ) = 0 := by
          intro j
          have := congrFun ha₀ j
          simpa [Matrix.vecMul, dotProduct, M] using this
        calc ∑ i, a₀ i * (((e.symm i) y : kN N) : ℂ)
            = ∑ i, a₀ i * ∑ j, ((bK.repr y j : ℚ) : ℂ) * (((e.symm i) (bK j) : kN N) : ℂ) := by
              exact Finset.sum_congr rfl fun i _ => by rw [step i]
          _ = ∑ j, ((bK.repr y j : ℚ) : ℂ) * ∑ i, a₀ i * (((e.symm i) (bK j) : kN N) : ℂ) := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
          _ = 0 := by simp [hj]

      have hfam : ∑ σ : (kN N) ≃ₐ[ℚ] (kN N), a₀ (e σ) •
          (fun y : kN N => ((σ y : kN N) : ℂ)) = 0 := by
        funext y
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hvan y]
        exact Fintype.sum_equiv e _ _ fun σ => by simp
      have := linearIndependent_iff'.1 hded Finset.univ (fun σ => a₀ (e σ)) hfam
      funext i
      have hi := this (e.symm i) (Finset.mem_univ _)
      simpa using hi
    have hlinmap : M.vecMul (a - a') = 0 := by
      have h' : M.vecMul a = M.vecMul a' := haa
      rw [show M.vecMul (a - a') = M.vecMul a - M.vecMul a' from Matrix.sub_vecMul M a a', h', sub_self]
    exact sub_eq_zero.1 (hzero _ hlinmap)
  have hunit : IsUnit M := Matrix.vecMul_injective_iff_isUnit.1 hinj
  obtain ⟨d, hd⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hunit (Pi.single (e 1) 1)

  have hδ : ∀ σ : (kN N) ≃ₐ[ℚ] (kN N), ∑ j, (((σ (bK j) : kN N) : ℂ)) * d j =
      if σ = 1 then 1 else 0 := by
    intro σ
    have := congrFun hd (e σ)
    simp only [Matrix.mulVec, dotProduct, M, Equiv.symm_apply_apply] at this
    rw [this, Pi.single_apply]
    simp [e.injective.eq_iff]

  have hcomb : (∑ j, d j • T (bK j)) = f := by
    have : (∑ j, d j • T (bK j)) = ∑ σ, (∑ j, ((σ (bK j) : kN N) : ℂ) * d j) • fσ σ := by
      simp only [T, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
    rw [this]
    have hσ : ∀ σ : (kN N) ≃ₐ[ℚ] (kN N),
        (∑ j, ((σ (bK j) : kN N) : ℂ) * d j) • fσ σ = if σ = 1 then fσ σ else 0 := fun σ => by
      rw [hδ σ]; split_ifs <;> simp
    rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_ite_eq']
    simp [hone]
  rw [← hcomb]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hT _))

end Trace

private theorem main (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℚ → ℂ) := by
  classical

  obtain ⟨n₀, b₀, hb₀⟩ := CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp N k
  haveI : FiniteDimensional ℂ (CuspForm (Γ₁ℝ N) k) := b₀.finiteDimensional_of_finite

  have hspan : Submodule.span ℂ (ratForms N k) = ⊤ := by
    rw [eq_top_iff, ← b₀.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    let c : ℕ → kN N := fun m => ⟨ModularFormClass.qCoeff (b₀ i) m, hb₀ i m⟩
    exact mem_span_ratForms (b₀ i) c fun m => rfl

  obtain ⟨t, ht_sub, ht_span, ht_ind⟩ := exists_linearIndependent ℂ (ratForms N k)
  have ht_fin : t.Finite := LinearIndependent.set_finite_of_isNoetherian ht_ind
  letI : Fintype t := ht_fin.fintype
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : t → CuspForm (Γ₁ℝ N) k)) := by
    rw [Subtype.range_coe, ht_span, hspan]
  let B : Module.Basis t ℂ (CuspForm (Γ₁ℝ N) k) := Module.Basis.mk ht_ind htop
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  refine ⟨Fintype.card t, B.reindex e, fun i m => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  exact ht_sub (e.symm i).2 m

end GammaOneRationalStructure

end

theorem _root_.CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℚ → ℂ) :=
  GammaOneRationalStructure.main N k

end WLightS11.S_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast

namespace WLightS11.S_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast

set_option autoImplicit false

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped ModularForm UpperHalfPlane MatrixGroups

noncomputable section

namespace DeligneSerre271

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {N : ℕ} {k : ℤ}

private theorem conj_mem_Gamma1 {γ x : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (hx : x ∈ Gamma1 N) :
    γ * x * γ⁻¹ ∈ Gamma1 N := by
  have hx0 : x ∈ Gamma0 N := Gamma1_in_Gamma0 N hx
  have hx' : (⟨x, hx0⟩ : Gamma0 N) ∈ Gamma1' N := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem N x).1 hx
  haveI : (Gamma1' N).Normal := MonoidHom.normal_ker _
  have hc : (⟨γ, hγ⟩ : Gamma0 N) * ⟨x, hx0⟩ * (⟨γ, hγ⟩ : Gamma0 N)⁻¹ ∈ Gamma1' N :=
    Subgroup.Normal.conj_mem inferInstance _ hx' _
  rw [Gamma1_to_Gamma0_mem] at hc
  exact (Gamma1_mem N _).2 hc

private theorem mem_coe_Gamma1_iff (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ N) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 N ∧ (Matrix.SpecialLinearGroup.mapGL ℝ γ) = x :=
  Subgroup.mem_map

open ConjAct Pointwise in

private theorem toConjAct_inv_smul_coe_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • (Γ₁ℝ N) = (Γ₁ℝ N) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := (mem_coe_Gamma1_iff _).1 h
    have hx : x = Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ * Matrix.SpecialLinearGroup.mapGL ℝ y
        * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
      rw [hyx, map_inv]; group
    have hmem := conj_mem_Gamma1 (Subgroup.inv_mem _ hγ) hy
    rw [inv_inv] at hmem
    rw [hx, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hmem
  · intro h
    obtain ⟨y, hy, rfl⟩ := (mem_coe_Gamma1_iff _).1 h
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (conj_mem_Gamma1 hγ hy)

private def slashMF {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (F : ModularForm (Γ₁ℝ N) k) : ModularForm (Γ₁ℝ N) k :=
  (ModularForm.translate F (Matrix.SpecialLinearGroup.mapGL ℝ γ)).copy
    ((⇑F : ℍ → ℂ) ∣[k] γ) rfl (toConjAct_inv_smul_coe_Gamma1 hγ).symm

@[scoped simp] private theorem coe_slashMF {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (F : ModularForm (Γ₁ℝ N) k) :
    ⇑(slashMF hγ F) = (⇑F : ℍ → ℂ) ∣[k] γ := rfl

private theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

private theorem isIntegralQExp_coeff {f : ℍ → ℂ} {p : PowerSeries ℤ}
    (h : ModularCurve.IsIntegralQExp f p) (n : ℕ) :
    ((PowerSeries.coeff n p : ℤ) : ℂ) = PowerSeries.coeff n (qExpansion 1 f) := by
  rw [← h, PowerSeries.coeff_map, eq_intCast]
private theorem exists_int_clearing [NeZero N] (F : ModularForm (Γ₁ℝ N) k)
    (hF : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑F)).coeff n = (r : ℂ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ m : ℕ,
      (D : ℂ) * ModularFormClass.qCoeff ((⇑F : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) := by

  have hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑(slashMF hγ F))).coeff n = (r : ℂ) := fun n =>
    ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 N F hF γ hγ n

  obtain ⟨D, p, hD0, hp⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion N (slashMF hγ F) hrat
  refine ⟨D, hD0, fun m => ⟨PowerSeries.coeff m p, ?_⟩⟩
  have h1 := isIntegralQExp_coeff hp m
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) (D : ℂ) (slashMF hγ F),
    map_smul, smul_eq_mul] at h1
  rw [h1]
  rfl

private theorem exists_int_clearing_forall [NeZero N] (F : ModularForm (Γ₁ℝ N) k)
    (hF : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (⇑F)).coeff n = (r : ℂ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ m : ℕ,
      (D : ℂ) * ModularFormClass.qCoeff ((⇑F : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) := by
  classical

  let Q := Quotient (QuotientGroup.rightRel (Gamma1 N))
  haveI : Finite Q :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (Gamma1 N)).symm
  letI : Fintype Q := Fintype.ofFinite Q

  have hcoset : ∀ q : Q, ∃ D : ℤ, D ≠ 0 ∧ (q.out ∈ Gamma0 N → ∀ m : ℕ,
      (D : ℂ) * ModularFormClass.qCoeff ((⇑F : ℍ → ℂ) ∣[k] q.out) m ∈ Set.range ((↑) : ℤ → ℂ)) := by
    intro q
    by_cases hq : q.out ∈ Gamma0 N
    · obtain ⟨D, hD0, hD⟩ := exists_int_clearing F hF hq
      exact ⟨D, hD0, fun _ => hD⟩
    · exact ⟨1, one_ne_zero, fun h => (hq h).elim⟩
  choose Dq hDq0 hDq using hcoset
  refine ⟨∏ q : Q, Dq q, Finset.prod_ne_zero_iff.2 fun q _ => hDq0 q, fun γ hγ m => ?_⟩

  let q : Q := Quotient.mk'' γ
  have hrel : QuotientGroup.rightRel (Gamma1 N) q.out γ := Quotient.mk_out' γ
  rw [QuotientGroup.rightRel_apply] at hrel

  have hout_eq : q.out = (γ * q.out⁻¹)⁻¹ * γ := by group
  have hout_mem : q.out ∈ Gamma0 N := by
    rw [hout_eq]
    exact mul_mem (inv_mem (Gamma1_in_Gamma0 N hrel)) hγ

  have hslash : (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ q.out)
      = (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := by
    have hinv : (⇑F : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (γ * q.out⁻¹)⁻¹) = ⇑F :=
      SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (inv_mem hrel))
    conv_lhs => rw [hout_eq]
    rw [map_mul, SlashAction.slash_mul, hinv]
  have hslashSL : (⇑F : ℍ → ℂ) ∣[k] q.out = (⇑F : ℍ → ℂ) ∣[k] γ := hslash

  obtain ⟨a, ha⟩ := hDq q hout_mem m
  rw [hslashSL] at ha
  have hprod : (∏ q' : Q, Dq q') = Dq q * ∏ q' ∈ Finset.univ.erase q, Dq q' :=
    (Finset.mul_prod_erase Finset.univ Dq (Finset.mem_univ q)).symm
  refine ⟨(∏ q' ∈ Finset.univ.erase q, Dq q') * a, ?_⟩
  rw [hprod]
  push_cast
  rw [mul_comm ((Dq q : ℤ) : ℂ), mul_assoc, ha]

private theorem main (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Γ₁ℝ N) k)),
      ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ Gamma0 N → ∀ m : ℕ,
        ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) := by

  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast N k

  have key : ∀ i : Fin n, ∃ D : ℤ, D ≠ 0 ∧ ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ m : ℕ,
      (D : ℂ) * ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) := by
    intro i
    have hF : ∀ n : ℕ, ∃ r : ℚ,
        (qExpansion 1 (⇑((b i : CuspForm (Γ₁ℝ N) k) : ModularForm (Γ₁ℝ N) k))).coeff n = (r : ℂ) := by
      intro n
      obtain ⟨r, hr⟩ := hb i n
      exact ⟨r, hr.symm⟩
    exact exists_int_clearing_forall ((b i : CuspForm (Γ₁ℝ N) k) : ModularForm (Γ₁ℝ N) k) hF
  choose D hD0 hD using key

  refine ⟨n, b.unitsSMul fun i => Units.mk0 ((D i : ℤ) : ℂ) (Int.cast_ne_zero.2 (hD0 i)), ?_⟩
  intro i γ hγ m
  rw [Module.Basis.unitsSMul_apply, Units.smul_mk0, FunLike.coe_smul,
    ModularForm.SL_smul_slash]

  have hlin : ModularFormClass.qCoeff (((D i : ℤ) : ℂ) • ((⇑(b i) : ℍ → ℂ) ∣[k] γ)) m
      = ((D i : ℤ) : ℂ) * ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m := by
    have h := ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) ((D i : ℤ) : ℂ)
      (slashMF hγ ((b i : CuspForm (Γ₁ℝ N) k) : ModularForm (Γ₁ℝ N) k))
    change qExpansion 1 (((D i : ℤ) : ℂ) • ((⇑(b i) : ℍ → ℂ) ∣[k] γ))
      = ((D i : ℤ) : ℂ) • qExpansion 1 ((⇑(b i) : ℍ → ℂ) ∣[k] γ) at h
    change (qExpansion 1 _).coeff m = _ * (qExpansion 1 _).coeff m
    rw [h, map_smul, smul_eq_mul]
  rw [hlin]
  exact hD i γ hγ m

end DeligneSerre271

end

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups

theorem _root_.CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast
    (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1 N) k)),
      ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ Gamma0 N → ∀ m : ℕ,
        ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ) :=
  DeligneSerre271.main N k

end WLightS11.S_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast

