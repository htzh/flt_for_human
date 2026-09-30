/-
The Riemann–Roch assembly: the two-carrier `H¹` identification, the curve-level
wrappers, and Riemann–Roch with the cohomological genus.  Ported from the pin's
`P2M/Sol/S_AlgebraicCurve_{indexOfSpecialty_eq_finrank_H1,
exists_genus_riemannIndex_of_isCurveOver, weilDifferentialRankOne_of_isCurveOver,
weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists,
exists_weilCanonical_riemannRoch,
exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists}.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.lean>).

Definitions come from Set D; the index engine and the Stichtenoth tower are
imported from H1a (`Genus/Index.lean`) and H1b (`Genus/Stichtenoth.lean`) — none of
them are restated here.

## Curve-level helper (promoted in the refactor round)

The curve-level helper `stichtenothGenusExists_of_isCurveOver`
(`Theorems/Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean:17`) is
proved from the pin's `IsCurveOver.exists_separating_transcendental`.  H2
re-provisioned both `private` here; the refactor round landed
`IsCurveOver.exists_separating_transcendental` publicly in
`AlgebraicCurve/IsCurveOver/SeparatingTranscendental.lean`, deleted the private
block, and promoted this wrapper under the pin's public name.  See
`lean/logs/riemann-roch-friction.md` § Set H2 and § Refactor round.
-/
import FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
import FLTForHuman.AlgebraicCurve.Defs.Repartitions
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.PoleDivisorPackage
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.LinearAlgebra.Basis.Basic

set_option autoImplicit false

noncomputable section

open WithZero
open scoped IntermediateField.algebraAdjoinAdjoin

namespace AlgebraicCurve


variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-! ## The two-carrier bridge: `indexOfSpecialty` (adelic) ↔ `H1` (repartitions) -/

theorem mem_repartitionsOf_iff_coe_mem_adeleBdd {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D := Iff.rfl

theorem mem_repartitions_of_mem_adeleBdd {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    α ∈ repartitions K F :=
  mem_repartitions_of_forall_le_exp D α hα

theorem mem_repartitions_of_mem_adeleSpace {α : Place K F → F} (hα : α ∈ adeleSpace K F) :
    α ∈ repartitions K F := by
  obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
  exact mem_repartitions_of_mem_adeleBdd hD

theorem diagonalHom_eq_coe_algebraMap (f : F) :
    diagonalHom K F f = ((algebraMap F ↥(repartitions K F) f : ↥(repartitions K F)) : Place K F → F) := rfl

theorem mem_principalRepartitions_iff_coe_mem_globalSub {α : ↥(repartitions K F)} :
    α ∈ principalRepartitions K F ↔ (α : Place K F → F) ∈ globalSub K F := by
  rw [mem_principalRepartitions_iff]
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩

noncomputable def boundedFamilies [HasPrincipalDivisors K F] : Subalgebra F (Place K F → F) where
  carrier := {α | ∃ D : Divisor K F, ∀ v : Place K F, v.adicValuation (α v) ≤ exp (D v)}
  mul_mem' := by
    rintro α β ⟨D, hD⟩ ⟨E, hE⟩
    refine ⟨D + E, fun v => ?_⟩
    rw [Pi.mul_apply, map_mul, Finsupp.add_apply, exp_add]
    exact mul_le_mul' (hD v) (hE v)
  add_mem' := by
    rintro α β ⟨D, hD⟩ ⟨E, hE⟩
    refine ⟨D ⊔ E, fun v => ?_⟩
    rw [Pi.add_apply]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · exact (hD v).trans (exp_le_exp.mpr (le_sup_left (a := D) (b := E) v))
    · exact (hE v).trans (exp_le_exp.mpr (le_sup_right (a := D) (b := E) v))
  algebraMap_mem' := by
    intro f
    rcases eq_or_ne f 0 with rfl | hf
    · exact ⟨0, fun v => by simp⟩
    · obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
      refine ⟨-P, fun v => ?_⟩
      rw [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        v.adicValuation_eq_exp_neg_ord hf, Finsupp.neg_apply, hP]

theorem mem_adeleSpace_iff_mem_repartitions [HasPrincipalDivisors K F] {α : Place K F → F} :
    α ∈ adeleSpace K F ↔ α ∈ repartitions K F := by
  constructor
  · exact mem_repartitions_of_mem_adeleSpace
  · intro hα
    have h : repartitions K F ≤ boundedFamilies (K := K) (F := F) := by
      refine Algebra.adjoin_le ?_
      intro β hβ
      classical
      let S : Finset (Place K F) := hβ.toFinset
      refine ⟨∑ v ∈ S, Finsupp.single v (-(v.ord (β v))), fun v => ?_⟩
      by_cases hv : v ∈ S
      · have hβv : β v ≠ 0 := by
          intro h0
          have : ¬v.adicValuation (β v) ≤ 1 := by simpa [S] using hv
          apply this; simp [h0]
        rw [v.adicValuation_eq_exp_neg_ord hβv, exp_le_exp, Finsupp.finset_sum_apply,
          Finset.sum_eq_single v (fun w _ hw => Finsupp.single_eq_of_ne (Ne.symm hw)) (fun h => (h hv).elim),
          Finsupp.single_eq_same]
      · have : v.adicValuation (β v) ≤ 1 := by
          by_contra h; exact hv (by simpa [S] using h)
        refine this.trans ?_
        rw [Finsupp.finset_sum_apply, Finset.sum_eq_zero (fun w hw => ?_), exp_zero]
        exact Finsupp.single_eq_of_ne (fun h => hv (h ▸ hw))
    obtain ⟨D, hD⟩ := h hα
    exact adeleBdd_le_adeleSpace (D := D) hD

theorem adeleSpace_eq_restrictScalars_repartitions [HasPrincipalDivisors K F] :
    adeleSpace K F = (Subalgebra.toSubmodule (repartitions K F)).restrictScalars K := by
  ext α
  exact mem_adeleSpace_iff_mem_repartitions

noncomputable def adeleSpaceEquivRepartitions [HasPrincipalDivisors K F] :
    ↥(adeleSpace K F) ≃ₗ[K] ↥(repartitions K F) where
  toFun α := ⟨α, mem_adeleSpace_iff_mem_repartitions.mp α.2⟩
  invFun α := ⟨α, mem_adeleSpace_iff_mem_repartitions.mpr α.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `H¹` identification: the adelic index of `D` is the `K`-dimension of the
repartition quotient `H1 D`. -/
theorem indexOfSpecialty_eq_finrank_H1 {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (D : Divisor K F) :
    indexOfSpecialty D = Module.finrank K (H1 D) := by
  let e := adeleSpaceEquivRepartitions (K := K) (F := F)
  have hmap : (adeleBddPrincipal K F D).map (e : ↥(adeleSpace K F) →ₗ[K] ↥(repartitions K F))
      = repartitionsOf D ⊔ principalRepartitions K F := by
    rw [Submodule.map_sup]
    congr 1
    · ext α
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨β, hβ, rfl⟩; exact hβ
      · intro hα; exact ⟨e.symm α, hα, e.apply_symm_apply α⟩
    · ext α
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨β, hβ, rfl⟩; exact mem_principalRepartitions_iff_coe_mem_globalSub.mpr hβ
      · intro hα
        exact ⟨e.symm α, mem_principalRepartitions_iff_coe_mem_globalSub.mp hα, e.apply_symm_apply α⟩
  rw [indexOfSpecialty_eq]
  exact LinearEquiv.finrank_eq (Submodule.Quotient.equiv _ _ e hmap)

/-! ## Effective-divisor and `omegaSpace` lemmas (from the `weilCanonical` source) -/

theorem self_mem_lSpace_neg {z : F} {P : Divisor K F} (hP : ∀ v, P v = v.ord z) :
    z ∈ LSpace (-P) := by
  rw [mem_lSpace_iff_ord]
  exact Or.inr fun v => by simp [hP v]

theorem inv_mem_lSpace {z : F} {P : Divisor K F} (hP : ∀ v, P v = v.ord z) :
    z⁻¹ ∈ LSpace P := by
  rw [mem_lSpace_iff_ord]
  exact Or.inr fun v => by simp [Place.ord_inv, hP v]

theorem ell_add_eq_of_ord_eq {z : F} (hz : z ≠ 0) {P : Divisor K F}
    (hP : ∀ v, P v = v.ord z) (A : Divisor K F) : ell (A + P) = ell A := by
  have h1 : ∀ f : F, f ∈ LSpace (A + P) → f * z ∈ LSpace A := fun f hf => by
    have := mul_mem_lSpace_add hf (self_mem_lSpace_neg hP)
    rwa [add_neg_cancel_right] at this
  have h2 : ∀ g : F, g ∈ LSpace A → g * z⁻¹ ∈ LSpace (A + P) := fun g hg =>
    mul_mem_lSpace_add hg (inv_mem_lSpace hP)
  let e : LSpace (A + P) ≃ₗ[K] LSpace A :=
    { toFun := fun f => ⟨f.1 * z, h1 f.1 f.2⟩
      map_add' := fun f g => by
        ext
        simp [add_mul]
      map_smul' := fun c f => by
        ext
        simp
      invFun := fun g => ⟨g.1 * z⁻¹, h2 g.1 g.2⟩
      left_inv := fun f => by
        ext
        simp [mul_inv_cancel_right₀ hz]
      right_inv := fun g => by
        ext
        simp [inv_mul_cancel_right₀ hz] }
  exact e.finrank_eq

theorem degree_eq_zero_of_ord_eq [HasPrincipalDivisors K F] {z : F} (hz : z ≠ 0)
    {P : Divisor K F} (hP : ∀ v, P v = v.ord z) : Divisor.degree P = 0 := by
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz
  have : D = P := Finsupp.ext fun v => by rw [hD v, hP v]
  rwa [this] at hdeg

theorem degree_pos_of_nonneg_of_ne_zero [IsCurveOver K F] {E : Divisor K F} (hE : 0 ≤ E)
    (hE0 : E ≠ 0) : 0 < Divisor.degree E := by
  classical
  have hEnn : ∀ w, 0 ≤ E w := fun w => by simpa using (Finsupp.le_def.mp hE) w
  obtain ⟨v, hv⟩ : ∃ v, E v ≠ 0 := by
    by_contra h
    push Not at h
    exact hE0 (Finsupp.ext h)
  have hEv : 1 ≤ E v := by
    have := hEnn v
    omega
  have hsplit : E = Finsupp.single v (E v) + Finsupp.erase v E :=
    (Finsupp.single_add_erase v E).symm
  have herase : ∀ w, 0 ≤ Finsupp.erase v E w := fun w => by
    rw [Finsupp.erase_apply]
    split_ifs
    · exact le_rfl
    · exact hEnn w
  have h1 : 0 ≤ Divisor.degree (Finsupp.erase v E) := Divisor.degree_nonneg_of_nonneg herase
  have h2 : (1 : ℤ) ≤ v.deg := by exact_mod_cast one_le_deg v
  rw [hsplit, map_add, Divisor.degree_single]
  nlinarith

theorem degree_lt_of_lt [IsCurveOver K F] {D E : Divisor K F} (h : D < E) :
    Divisor.degree D < Divisor.degree E := by
  have h1 : 0 ≤ E - D := by
    refine Finsupp.le_def.mpr fun w => ?_
    have := (Finsupp.le_def.mp h.le) w
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply]
    linarith
  have h2 : E - D ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
  have := degree_pos_of_nonneg_of_ne_zero h1 h2
  rw [map_sub] at this
  linarith

theorem adeleBdd_sup_le (A B : Divisor K F) :
    adeleBdd (A ⊔ B) ≤ adeleBdd A ⊔ adeleBdd B := by
  classical
  intro x hx
  let y : Place K F → F := fun v => if B v ≤ A v then x v else 0
  have hy : y ∈ adeleBdd A := fun v => by
    simp only [y]
    split_ifs with h
    · have := hx v
      rwa [Finsupp.sup_apply, sup_eq_left.mpr h] at this
    · rw [map_zero]
      exact zero_le'
  have hz : x - y ∈ adeleBdd B := fun v => by
    simp only [Pi.sub_apply, y]
    split_ifs with h
    · rw [sub_self, map_zero]
      exact zero_le'
    · have := hx v
      rw [Finsupp.sup_apply, sup_eq_right.mpr (not_le.mp h).le] at this
      rwa [sub_zero]
  have hx' : x = y + (x - y) := by abel
  rw [hx']
  exact Submodule.add_mem_sup hy hz

theorem mem_omegaSpace_sup {A B : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hA : φ ∈ omegaSpace A) (hB : φ ∈ omegaSpace B) : φ ∈ omegaSpace (A ⊔ B) := by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]
  intro w hw
  obtain ⟨b, hb, g, hg, rfl⟩ := Submodule.mem_sup.mp hw
  have hb' : (b : Place K F → F) ∈ adeleBdd A ⊔ adeleBdd B :=
    adeleBdd_sup_le A B (Submodule.mem_comap.mp hb)
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hb'
  have hbeq : b = ⟨s, adeleBdd_le_adeleSpace hs⟩ + ⟨t, adeleBdd_le_adeleSpace ht⟩ :=
    Subtype.ext hst.symm
  rw [map_add, hbeq, map_add, omegaSpace_vanishBdd hA (α := ⟨s, _⟩) hs,
    omegaSpace_vanishBdd hB (α := ⟨t, _⟩) ht,
    omegaSpace_vanishGlobal hA (Submodule.mem_comap.mp hg)]
  simp

/-! ## The rank-one / Weil-duality targets -/

theorem weilDifferentialRankOne_of_stichtenothGenusExists [IsCurveOver K F]
    (h : StichtenothGenusExists K F) : WeilDifferentialRankOne K F := by
  obtain ⟨hne, hfin, γ, D₀, hγ⟩ := h
  haveI := hne; haveI := hfin
  intro φ hφ hφ0 μ hμ
  exact weilDifferentialRankOne_of_genusReached hγ hφ hφ0 hμ

theorem indexOfSpecialty_eq_ell_sub_of_rankOne_max [HasPrincipalDivisors K F]
    (hRankOne : WeilDifferentialRankOne K F)
    {W : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) (D : Divisor K F) :
    indexOfSpecialty D = ell (W - D) := by
  rw [← finrank_omegaSpace_eq_indexOfSpecialty]
  exact (LinearEquiv.ofBijective (residuePairing K F W D hφ)
    ⟨residuePairing_injective W D hφ hφ0, residuePairing_surjective_of_rankOne_max hRankOne hφ hφ0 hWmax D⟩).finrank_eq.symm

theorem weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hRR : FunctionFieldRiemannRoch K F)
    (hSG : StichtenothGenusExists K F) :
    WeilDualityAdelic K F := by
  intro _instCurve _instCan _instDC ω hω D
  obtain ⟨⟨v⟩, hfd, γ, D₀, hγ⟩ := hSG
  haveI : Nonempty (Place K F) := ⟨v⟩
  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := hfd

  have hi : ∀ D' : Divisor K F,
      (indexOfSpecialty D' : ℤ) = (ell D' : ℤ) - (Divisor.degree D' + 1 - γ) :=
    fun D' => (indexOfSpecialty_eq_of_genusReached hγ D').2

  have hdegv : 0 < (v.deg : ℤ) := by
    haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank K v.ResidueField)

  have hγle : γ ≤ (genus K F : ℤ) := by
    have h₁ := hRR hω D₀
    have h₂ := hγ.eq
    have h₃ : (0 : ℤ) ≤ (ell (canonicalDivisorOf hω - D₀) : ℤ) := Nat.cast_nonneg _
    linarith

  have hgeγ : (genus K F : ℤ) ≤ γ := by
    set D₁ : Divisor K F := canonicalDivisorOf hω + Finsupp.single v 1 with hD₁
    have hKD : canonicalDivisorOf hω - D₁ = -Finsupp.single v 1 := by
      rw [hD₁]; abel
    have hneg : Divisor.degree (canonicalDivisorOf hω - D₁) < 0 := by
      rw [hKD, map_neg, Divisor.degree_single]
      linarith
    have hℓ : ell (canonicalDivisorOf hω - D₁) = 0 := ell_eq_zero_of_degree_neg hneg
    have h₁ := hRR hω D₁
    have h₂ := hγ.isMax D₁
    rw [hℓ] at h₁
    push_cast at h₁
    linarith
  have hγg : γ = (genus K F : ℤ) := le_antisymm hγle hgeγ
  have h₁ := hi D
  have h₂ := hRR hω D
  rw [hγg] at h₁
  linarith

theorem exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (Q : Place K F) :
    ∃ n : ℕ, RiemannGenusReachedAt γ ((n : ℤ) • Finsupp.single Q 1) := by
  classical
  obtain ⟨n, hn⟩ :=
    exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached h Q
  refine ⟨n, ?_⟩
  have hidx := (indexOfSpecialty_eq_of_genusReached h
    ((n : ℤ) • Finsupp.single Q (1 : ℤ))).2
  rw [hn] at hidx
  have heq : Divisor.degree ((n : ℤ) • Finsupp.single Q (1 : ℤ)) -
      (ell ((n : ℤ) • Finsupp.single Q (1 : ℤ)) : ℤ) = γ - 1 := by
    push_cast at hidx ⊢
    linarith
  exact ⟨finiteDimensional_lSpace _, heq, h.isMax⟩

section CurveLevel

open IntermediateField

/-- The pin's public curve-level wrapper
(`Theorems/Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean:17`): it
rests on the now-public `IsCurveOver.exists_separating_transcendental` of
`IsCurveOver/SeparatingTranscendental.lean`. -/
theorem stichtenothGenusExists_of_isCurveOver {K : Type*} {F : Type*} [Field K] [Field F]
    [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (hC : ConstantsAreBase K F) : StichtenothGenusExists K F := by
  classical
  obtain ⟨x, htr, hfd, hsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := hfd; haveI := hsep
  set e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr with he
  letI : Algebra (RatFunc K) F := ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact RationalFunctionField.stichtenothGenusExists K F hC

theorem exists_genus_riemannIndex_of_isCurveOver {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    ∃ γ : ℤ, ∀ D : Divisor K F,
      Module.Finite K (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) ∧
        (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by
  exact exists_genus_riemannIndex_of_stichtenothGenusExists
    (stichtenothGenusExists_of_isCurveOver hC)

theorem weilDifferentialRankOne_of_isCurveOver {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    WeilDifferentialRankOne K F := by
  exact weilDifferentialRankOne_of_stichtenothGenusExists
    (stichtenothGenusExists_of_isCurveOver hC)

/-- The pin's private proof body of `exists_weilCanonical_riemannRoch`
(`S_AlgebraicCurve_exists_weilCanonical_riemannRoch.lean:146`), kept `private`. -/
private theorem main [PerfectField K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) :
    ∃ W : Divisor K F, ∀ D : Divisor K F,
      (ell D : ℤ) - (ell (W - D) : ℤ) = Divisor.degree D + 1 - (genusFF K F : ℤ) := by
  classical
  obtain ⟨hne, hfin, γ, D₀, hR⟩ := stichtenothGenusExists_of_isCurveOver hC
  haveI : Nonempty (Place K F) := hne
  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) := hfin

  have hidx : ∀ D : Divisor K F,
      Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) ∧
        (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) :=
    fun D => indexOfSpecialty_eq_of_genusReached hR D

  have hg0 : indexOfSpecialty (0 : Divisor K F) = genusFF K F := indexOfSpecialty_eq_finrank_H1 0
  have hγ : (genusFF K F : ℤ) = γ := by
    have h := (hidx 0).2
    rw [hg0, ell_zero_eq_one_of_constantsAreBase hC, map_zero] at h
    push_cast at h
    linarith
  have hγnn : (0 : ℤ) ≤ γ := by
    rw [← hγ]
    positivity

  have hfinΩ : ∀ E : Divisor K F, Module.Finite K (omegaSpace E) := fun E => by
    haveI := (hidx E).1
    exact Module.Finite.equiv (omegaSpaceEquivIndexDual E).symm
  have hpos : ∀ (E : Divisor K F) (ψ : Module.Dual K (adeleSpace K F)),
      ψ ∈ omegaSpace E → ψ ≠ 0 → 1 ≤ indexOfSpecialty E := by
    intro E ψ hψ hψ0
    haveI := hfinΩ E
    rw [← finrank_omegaSpace_eq_indexOfSpecialty, Nat.one_le_iff_ne_zero, Ne,
      Submodule.finrank_eq_zero]
    intro hbot
    rw [hbot] at hψ
    exact hψ0 ((Submodule.mem_bot K).mp hψ)

  have hshift : ∀ (E P : Divisor K F) (z : F), z ≠ 0 → (∀ v, P v = v.ord z) →
      indexOfSpecialty (E + P) = indexOfSpecialty E := by
    intro E P z hz hP
    have h1 := (hidx (E + P)).2
    have h2 := (hidx E).2
    rw [ell_add_eq_of_ord_eq hz hP, map_add, degree_eq_zero_of_ord_eq hz hP, add_zero] at h1
    exact_mod_cast h1.trans h2.symm

  have hzero : ∀ E : Divisor K F, D₀ ≤ E → indexOfSpecialty E = 0 := by
    intro E hE
    have h0 : indexOfSpecialty D₀ = 0 := by
      have h := (hidx D₀).2
      have := hR.eq
      have : (indexOfSpecialty D₀ : ℤ) = 0 := by linarith
      exact_mod_cast this
    have hbot : omegaSpace D₀ = ⊥ := by
      haveI := hfinΩ D₀
      rw [← Submodule.finrank_eq_zero, finrank_omegaSpace_eq_indexOfSpecialty, h0]
    have hle : omegaSpace E ≤ ⊥ := hbot ▸ omegaSpace_antitone hE
    haveI := hfinΩ E
    rw [← finrank_omegaSpace_eq_indexOfSpecialty, Submodule.finrank_eq_zero]
    exact le_bot_iff.mp hle

  let v₀ : Place K F := Classical.arbitrary _
  set D₁ : Divisor K F := -Finsupp.single v₀ 2 with hD₁
  have hdegD₁ : Divisor.degree D₁ = -(2 * (v₀.deg : ℤ)) := by
    rw [hD₁, map_neg, Divisor.degree_single]
  have hv₀ : (1 : ℤ) ≤ v₀.deg := by exact_mod_cast one_le_deg v₀
  have hellD₁ : ell D₁ = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD₁]; linarith)
  have hiD₁ : 1 ≤ indexOfSpecialty D₁ := by
    have h := (hidx D₁).2
    rw [hellD₁, hdegD₁] at h
    have : (1 : ℤ) ≤ indexOfSpecialty D₁ := by
      push_cast at h
      linarith
    exact_mod_cast this
  obtain ⟨φ, hφD₁, hφ0⟩ : ∃ φ ∈ omegaSpace D₁, φ ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro hbot
    have h := finrank_omegaSpace_eq_indexOfSpecialty D₁
    rw [hbot, finrank_bot] at h
    omega

  have hbound : ∀ E : Divisor K F, φ ∈ omegaSpace E →
      Divisor.degree E < Divisor.degree D₀ + γ := by
    intro E hE
    by_contra hle
    push Not at hle
    have h1 : 1 ≤ ell (E - D₀) := by
      have := hR.isMax (E - D₀)
      rw [map_sub] at this
      have : (1 : ℤ) ≤ ell (E - D₀) := by linarith
      exact_mod_cast this
    obtain ⟨z, hzmem, hz0⟩ : ∃ z ∈ LSpace (E - D₀), z ≠ 0 := by
      apply Submodule.exists_mem_ne_zero_of_ne_bot
      intro hbot
      have : ell (E - D₀) = 0 := by
        show Module.finrank K (LSpace (E - D₀)) = 0
        rw [hbot, finrank_bot]
      omega
    obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) z hz0
    have hEP : D₀ ≤ E + P := by
      refine Finsupp.le_def.mpr fun v => ?_
      have h := (mem_lSpace_iff_ord.mp hzmem).resolve_left hz0 v
      rw [← hP v] at h
      simp only [Finsupp.coe_sub, Pi.sub_apply] at h
      simp only [Finsupp.coe_add, Pi.add_apply]
      linarith
    have h2 : indexOfSpecialty (E + P) = 0 := hzero (E + P) hEP
    have h3 : 1 ≤ indexOfSpecialty E := hpos E φ hE hφ0
    rw [hshift E P z hz0 hP] at h2
    omega

  obtain ⟨m, ⟨W, hφW, hWm⟩, hmax⟩ := Int.exists_greatest_of_bdd
      (P := fun n : ℤ => ∃ E : Divisor K F, φ ∈ omegaSpace E ∧ Divisor.degree E = n)
      ⟨Divisor.degree D₀ + γ, fun n ⟨E, hE, hEn⟩ => hEn ▸ (hbound E hE).le⟩
      ⟨Divisor.degree D₁, D₁, hφD₁, rfl⟩
  have hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W := by
    intro E hE
    by_contra hEW
    have hsup : φ ∈ omegaSpace (E ⊔ W) := mem_omegaSpace_sup hE hφW
    have hlt : W < E ⊔ W := right_lt_sup.mpr hEW
    have h1 := degree_lt_of_lt hlt
    have h2 := hmax _ ⟨E ⊔ W, hsup, rfl⟩
    rw [← hWm] at h2
    linarith

  have hrank : WeilDifferentialRankOne K F := weilDifferentialRankOne_of_isCurveOver hC
  refine ⟨W, fun D => ?_⟩
  have hdual : indexOfSpecialty D = ell (W - D) :=
    indexOfSpecialty_eq_ell_sub_of_rankOne_max hrank hφW hφ0 hWmax D
  have h := (hidx D).2
  rw [hdual] at h
  rw [hγ]
  linarith

theorem exists_weilCanonical_riemannRoch
    (K F : Type*) [Field K] [PerfectField K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) :
    ∃ W : Divisor K F, ∀ D : Divisor K F,
      (ell D : ℤ) - (ell (W - D) : ℤ) =
        Divisor.degree D + 1 - (genusFF K F : ℤ) :=
  main hC

end CurveLevel

end AlgebraicCurve

end
