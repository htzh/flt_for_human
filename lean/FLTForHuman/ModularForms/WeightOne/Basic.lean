/-
  The weight-one toolbox layer.

  Transcribed from the pinned `fermats-last-theorem@aa2d8b3` wrappers
  `Theorems/Thm_<name>.lean`, with the proofs ported from the matching
  `P2M/Sol/S_<name>.lean`. Statements are verbatim; proofs are adapted to
  mathlib `v4.34.0`. The pin's local `set_option maxHeartbeats` bumps are not
  transcribed; the module elaborates under the project's global cap via
  `lake build`.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Geometry.Manifold.Notation
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import FLTForHuman.ModularForms.SturmBound

set_option autoImplicit false
-- The pin's `haveI` walls are load-bearing; keep them literal.
set_option linter.style.haveILetI false




namespace PowerSeriesAux

open Polynomial

variable {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

omit [IsDomain R] [IsPrincipalIdealRing R] in
private theorem map_injective : Function.Injective (PowerSeries.map (algebraMap R K)) := by
  intro a b h
  ext n
  apply IsFractionRing.injective R K
  have := congrArg (PowerSeries.coeff n) h
  simpa only [PowerSeries.coeff_map] using this

private theorem main (g : PowerSeries K) (Φ : Polynomial (PowerSeries R)) (hΦ : Φ.Monic)
    (hroot : Polynomial.eval₂ (PowerSeries.map (algebraMap R K)) g Φ = 0)
    (h : PowerSeries R) (h0 : h ≠ 0)
    (hmul : PowerSeries.map (algebraMap R K) h * g ∈ (PowerSeries.map (algebraMap R K)).range) :
    g ∈ (PowerSeries.map (algebraMap R K)).range := by
  classical
  set ι : PowerSeries R →+* PowerSeries K := PowerSeries.map (algebraMap R K) with hι
  let F := FractionRing (PowerSeries R)
  let F' := FractionRing (PowerSeries K)
  let alg' : PowerSeries K →+* F' := algebraMap (PowerSeries K) F'
  have hι_inj : Function.Injective ι := map_injective
  have halg'_inj : Function.Injective alg' := IsFractionRing.injective (PowerSeries K) F'
  have hcomp_inj : Function.Injective (alg'.comp ι) := halg'_inj.comp hι_inj
  let θ : F →+* F' := IsFractionRing.lift (A := PowerSeries R) (K := F) (g := alg'.comp ι) hcomp_inj
  have hθ_alg : ∀ a : PowerSeries R, θ (algebraMap (PowerSeries R) F a) = alg' (ι a) := fun a =>
    IsFractionRing.lift_algebraMap hcomp_inj a
  have hθ_comp : θ.comp (algebraMap (PowerSeries R) F) = alg'.comp ι := RingHom.ext hθ_alg
  have hθ_inj : Function.Injective θ := θ.injective
  obtain ⟨u, hu⟩ := hmul
  set x : F := algebraMap (PowerSeries R) F u / algebraMap (PowerSeries R) F h with hx
  have hιh : ι h ≠ 0 := fun h' => h0 (hι_inj (by rw [h', map_zero]))
  have halg'h : alg' (ι h) ≠ 0 := fun h' => hιh (halg'_inj (by rw [h', map_zero]))
  have hθx : θ x = alg' g := by
    rw [hx, map_div₀, hθ_alg, hθ_alg, div_eq_iff halg'h, ← map_mul, mul_comm, ← hu]
  have hint : IsIntegral (PowerSeries R) x := by
    refine ⟨Φ, hΦ, ?_⟩
    apply hθ_inj
    rw [Polynomial.hom_eval₂, hθ_comp, hθx, map_zero, ← Polynomial.hom_eval₂, hroot, map_zero]
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨p, halg'_inj ?_⟩
  change alg' (ι p) = alg' g
  rw [← hθ_alg, hp, hθx]

end PowerSeriesAux

theorem PowerSeries.mem_range_map_of_monic_of_mul_mem_range
    {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (g : PowerSeries K) (Φ : Polynomial (PowerSeries R)) (hΦ : Φ.Monic)
    (hroot : Polynomial.eval₂ (PowerSeries.map (algebraMap R K)) g Φ = 0)
    (h : PowerSeries R) (h0 : h ≠ 0)
    (hmul : PowerSeries.map (algebraMap R K) h * g ∈ (PowerSeries.map (algebraMap R K)).range) :
    g ∈ (PowerSeries.map (algebraMap R K)).range :=
  PowerSeriesAux.main g Φ hΦ hroot h h0 hmul




set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial
open scoped IntermediateField

namespace IsIntAux

variable {K : Type*} [Field K] [Algebra ℂ K]

omit [Algebra ℂ K] in

private theorem isIntegral_subring_iff (T : Subring K) (y : K) :
    IsIntegral ↥T y ↔ ∃ p : K[X], p.Monic ∧ (∀ n, p.coeff n ∈ T) ∧ p.eval y = 0 := by
  constructor
  · rintro ⟨p, hm, hp⟩
    refine ⟨p.map (algebraMap ↥T K), hm.map _, fun n ↦ ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff n).2
    · rwa [Polynomial.eval_map]
  · rintro ⟨p, hm, hc, hp⟩
    have hl : p ∈ Polynomial.lifts (algebraMap ↥T K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; exact ⟨⟨p.coeff n, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hp]

omit [Algebra ℂ K] in

private theorem isIntegral_subalgebra_iff {R₀ : Type*} [CommRing R₀] [Algebra R₀ K]
    (T : Subalgebra R₀ K) (y : K) :
    IsIntegral ↥T y ↔ ∃ p : K[X], p.Monic ∧ (∀ n, p.coeff n ∈ T) ∧ p.eval y = 0 := by
  constructor
  · rintro ⟨p, hm, hp⟩
    refine ⟨p.map (algebraMap ↥T K), hm.map _, fun n ↦ ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff n).2
    · rwa [Polynomial.eval_map]
  · rintro ⟨p, hm, hc, hp⟩
    have hl : p ∈ Polynomial.lifts (algebraMap ↥T K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; exact ⟨⟨p.coeff n, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hp]

omit [Algebra ℂ K] in

private theorem isIntegral_adjoin_iff_closure {R₀ : Type*} [CommRing R₀] [Algebra R₀ K] (B : Set K) (y : K) :
    IsIntegral ↥(Algebra.adjoin R₀ B) y ↔
      IsIntegral ↥(Subring.closure (Set.range (algebraMap R₀ K) ∪ B)) y := by
  rw [isIntegral_subalgebra_iff, isIntegral_subring_iff]
  simp only [Algebra.mem_adjoin_iff]

omit [Algebra ℂ K] in

private theorem isIntegral_of_isIntegral_adjoin_singleton {A : Type*} [CommRing A] [Algebra A K] {r z : K}
    (hr : IsIntegral A r) (hz : IsIntegral ↥(Algebra.adjoin A {r}) z) : IsIntegral A z := by
  haveI : Algebra.IsIntegral A ↥(Algebra.adjoin A {r}) :=
    Algebra.IsIntegral.adjoin fun _ h ↦ by rw [Set.mem_singleton_iff] at h; rw [h]; exact hr
  exact isIntegral_trans z hz

private theorem range_algebraMap_subfield (F : IntermediateField ℚ ℂ) :
    Set.range (algebraMap ↥F K) = ⇑(algebraMap ℂ K) '' (F : Set ℂ) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, c.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, hc⟩, rfl⟩

private theorem algebraMap_subfield_apply' (F : IntermediateField ℚ ℂ) (E₀ : IntermediateField ↥F ℂ)
    (c : ↥E₀) : algebraMap ↥E₀ K c = algebraMap ℂ K (c : ℂ) := rfl

private theorem range_algebraMap_subfield' (F : IntermediateField ℚ ℂ) (E₀ : IntermediateField ↥F ℂ) :
    Set.range (algebraMap ↥E₀ K) = ⇑(algebraMap ℂ K) '' (E₀ : Set ℂ) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, c.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, hc⟩, rfl⟩

private theorem charZero_KFld (F : IntermediateField ℚ ℂ) (L₀ : IntermediateField ↥F K) : CharZero ↥L₀ :=
  haveI : CharZero ↥F := charZero_of_injective_algebraMap (algebraMap ℚ ↥F).injective
  charZero_of_injective_algebraMap (algebraMap ↥F ↥L₀).injective

variable (F : IntermediateField ℚ ℂ) (B S : Set K)

private abbrev KFld : IntermediateField ↥F K := IntermediateField.adjoin ↥F S

private abbrev TRng : Subalgebra ↥F K := Algebra.adjoin ↥F B

private def RSet : Set K := {y | y ∈ KFld F S ∧ IsIntegral ↥(TRng F B) y}

variable {B S}

private theorem isIntegral_TRng_algebraMap {a : ℂ} (ha : IsIntegral ↥F a) :
    IsIntegral ↥(TRng F B) (algebraMap ℂ K a) :=
  (ha.algebraMap (B := K)).tower_top

private theorem isIntegral_KFld_algebraMap {a : ℂ} (ha : IsIntegral ↥F a) :
    IsIntegral ↥(KFld F S) (algebraMap ℂ K a) :=
  (ha.algebraMap (B := K)).tower_top

private theorem minpoly_KFld_dvd (c : ℂ) :
    minpoly ↥(KFld F S) (algebraMap ℂ K c) ∣ (minpoly ↥F c).map (algebraMap ↥F ↥(KFld F S)) := by
  apply minpoly.dvd
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]

private theorem root_minpoly_KFld_eq_algebraMap {c : ℂ} (hc : IsIntegral ↥F c) {r : K}
    (hr : r ∈ (minpoly ↥(KFld F S) (algebraMap ℂ K c)).aroots K) :
    ∃ a : ℂ, IsIntegral ↥F a ∧ algebraMap ℂ K a = r := by
  set ι := algebraMap ℂ K
  set q : ℂ[X] := (minpoly ↥F c).map (algebraMap ↥F ℂ) with hq
  have hqm : q.Monic := (minpoly.monic hc).map _
  have hq0 : q.map ι ≠ 0 := (hqm.map ι).ne_zero
  have hdvd : (minpoly ↥(KFld F S) (ι c)).map (algebraMap ↥(KFld F S) K) ∣ q.map ι := by
    have := Polynomial.map_dvd (algebraMap ↥(KFld F S) K) (minpoly_KFld_dvd F (S := S) c)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
    rwa [hq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq ↥F ℂ K]
  have hroots : (q.map ι).roots = q.roots.map ι :=
    (IsAlgClosed.splits q).roots_map_of_injective (algebraMap ℂ K).injective
  have hr' : r ∈ (q.map ι).roots := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hq0 hdvd) hr
  rw [hroots, Multiset.mem_map] at hr'
  obtain ⟨a, ha, rfl⟩ := hr'
  refine ⟨a, ?_, rfl⟩
  rw [Polynomial.mem_roots hqm.ne_zero, Polynomial.IsRoot.def, hq, Polynomial.eval_map,
    ← Polynomial.aeval_def] at ha
  exact ⟨minpoly ↥F c, minpoly.monic hc, by rwa [← Polynomial.aeval_def]⟩

attribute [local instance] Classical.propDecidable in

private theorem card_rootFinset_minpoly_KFld {c : ℂ} (hc : IsIntegral ↥F c) :
    ((minpoly ↥(KFld F S) (algebraMap ℂ K c)).aroots K).toFinset.card =
      (minpoly ↥(KFld F S) (algebraMap ℂ K c)).natDegree := by
  set ι := algebraMap ℂ K
  set L₀ := KFld F S
  haveI : CharZero ↥L₀ := charZero_KFld F L₀
  have hint : IsIntegral ↥L₀ (ι c) := isIntegral_KFld_algebraMap F hc
  set m₁ := minpoly ↥L₀ (ι c)
  have hsep : (m₁.map (algebraMap ↥L₀ K)).Separable :=
    (PerfectField.separable_of_irreducible (minpoly.irreducible hint)).map
  rw [Polynomial.aroots_def, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)]
  set q : ℂ[X] := (minpoly ↥F c).map (algebraMap ↥F ℂ) with hq
  have hqm : q.Monic := (minpoly.monic hc).map _
  have hdvd : m₁.map (algebraMap ↥L₀ K) ∣ q.map ι := by
    have := Polynomial.map_dvd (algebraMap ↥L₀ K) (minpoly_KFld_dvd F (S := S) c)
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
    rwa [hq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq ↥F ℂ K]
  have hspl : (m₁.map (algebraMap ↥L₀ K)).Splits :=
    ((IsAlgClosed.splits q).map ι).of_dvd (hqm.map ι).ne_zero hdvd
  rw [← hspl.natDegree_eq_card_roots, Polynomial.natDegree_map]

private theorem algebraMap_adjoinF_mem {c : ℂ} {z : ℂ} (hz : z ∈ IntermediateField.adjoin ↥F {c}) :
    algebraMap ℂ K z ∈
      IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c} := by
  set f := IsScalarTower.toAlgHom ↥F ℂ K
  have h1 : algebraMap ℂ K z ∈ (IntermediateField.adjoin ↥F {c}).map f := by
    rw [← SetLike.mem_coe, IntermediateField.coe_map]
    exact ⟨z, hz, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton] at h1
  have h2 : IntermediateField.adjoin ↥F {f c} ≤
      (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).restrictScalars ↥F :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.mem_adjoin_simple_self ↥(KFld F S) _))
  exact h2 h1

private theorem closure_adjoin_le {c : ℂ} :
    Subfield.closure
        (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S) ≤
      (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).toSubfield := by
  refine Subfield.closure_le.mpr ?_
  rintro y (⟨z, hz, rfl⟩ | hy)
  · exact algebraMap_adjoinF_mem F hz
  · exact (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).algebraMap_mem
      ⟨y, IntermediateField.subset_adjoin ↥F S hy⟩

variable (B) in

private theorem exists_lift_of_mem_adjoin (hBS : B ⊆ S) {c : ℂ} (hc : IsIntegral ↥F c) {y : K}
    (hy : y ∈ Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) B) :
    ∃ y' : ↥(IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}),
      (y' : K) = y ∧
      ∀ φ : ↥(IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}) →ₐ[↥(KFld F S)] K,
        φ y' ∈ Algebra.adjoin ↥(TRng F B) {φ (IntermediateField.AdjoinSimple.gen ↥(KFld F S)
          (algebraMap ℂ K c))} := by
  set ι := algebraMap ℂ K
  set L₀ := KFld F S
  set E := IntermediateField.adjoin ↥L₀ {ι c}
  set g := IntermediateField.AdjoinSimple.gen ↥L₀ (ι c)
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨algebraMap ↥L₀ ↥E ⟨x, IntermediateField.subset_adjoin ↥F S (hBS hx)⟩, rfl, fun φ ↦ ?_⟩
    rw [AlgHom.commutes]
    exact Subalgebra.algebraMap_mem (Algebra.adjoin ↥(TRng F B) {φ g})
      (⟨x, Algebra.subset_adjoin hx⟩ : ↥(TRng F B))
  | algebraMap z =>
    have hz : (z : ℂ) ∈ IntermediateField.adjoin ↥F {c} := z.2
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hc.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨u, hu⟩ := hz
    refine ⟨Polynomial.aeval g (u.map (algebraMap ↥F ↥L₀)), ?_, fun φ ↦ ?_⟩
    · rw [algebraMap_subfield_apply', ← IntermediateField.aeval_coe,
        Polynomial.aeval_map_algebraMap, IntermediateField.AdjoinSimple.coe_gen,
        Polynomial.aeval_algebraMap_apply]
      exact congrArg ι hu
    · rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap,
        ← Polynomial.aeval_map_algebraMap ↥(TRng F B)]
      exact Polynomial.aeval_mem_adjoin_singleton _ _
  | add x y _ _ ihx ihy =>
    obtain ⟨x', hx', hx⟩ := ihx
    obtain ⟨y', hy', hy⟩ := ihy
    exact ⟨x' + y', by rw [IntermediateField.coe_add, hx', hy'], fun φ ↦ by
      rw [map_add]; exact Subalgebra.add_mem _ (hx φ) (hy φ)⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨x', hx', hx⟩ := ihx
    obtain ⟨y', hy', hy⟩ := ihy
    exact ⟨x' * y', by rw [IntermediateField.coe_mul, hx', hy'], fun φ ↦ by
      rw [map_mul]; exact Subalgebra.mul_mem _ (hx φ) (hy φ)⟩

attribute [local instance] Classical.propDecidable in

private theorem isIntegral_coeff_lagrangeBasis {s : Finset K}
    (hs : ∀ r ∈ s, ∃ a : ℂ, IsIntegral ↥F a ∧ algebraMap ℂ K a = r)
    {r : K} (hr : r ∈ s) (k : ℕ) :
    IsIntegral ↥(TRng F B) ((Lagrange.basis s id r).coeff k) := by
  set ι := algebraMap ℂ K
  set Sf : Subfield K := (algebraicClosure ↥F ℂ).toSubfield.map ι
  have hmemS : ∀ r ∈ s, r ∈ Sf := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := hs r hr
    exact ⟨a, mem_algebraicClosure_iff.mpr ha.isAlgebraic, rfl⟩
  have hlift : Lagrange.basis s id r ∈ Polynomial.liftsRing Sf.subtype := by
    unfold Lagrange.basis
    refine Subring.prod_mem _ fun j hj ↦ ?_
    unfold Lagrange.basisDivisor
    have hrS : (id r : K) ∈ Set.range Sf.subtype := ⟨⟨r, hmemS r hr⟩, rfl⟩
    have hjS : (id j : K) ∈ Set.range Sf.subtype :=
      ⟨⟨j, hmemS j (Finset.mem_of_mem_erase hj)⟩, rfl⟩
    refine Subring.mul_mem _ ?_ (Subring.sub_mem _ ?_ ?_)
    · rw [← Polynomial.lifts_iff_liftsRing]
      apply Polynomial.C'_mem_lifts
      obtain ⟨a, ha⟩ := hrS; obtain ⟨b, hb⟩ := hjS
      exact ⟨(a - b)⁻¹, by rw [map_inv₀, map_sub, ha, hb]⟩
    · rw [← Polynomial.lifts_iff_liftsRing]; exact Polynomial.X_mem_lifts _
    · rw [← Polynomial.lifts_iff_liftsRing]; exact Polynomial.C'_mem_lifts hjS
  rw [← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts] at hlift
  obtain ⟨⟨w, hw⟩, hw'⟩ := hlift k
  obtain ⟨a, ha, rfl⟩ := hw
  change ι a = _ at hw'
  rw [← hw']
  exact isIntegral_TRng_algebraMap F
    (isAlgebraic_iff_isIntegral.mp (mem_algebraicClosure_iff.mp ha))

variable (B S) in

private theorem mem_span_RSet_of_adjoin_simple (hBS : B ⊆ S) {c : ℂ} (hc : IsIntegral ↥F c) {x : K}
    (hxK : x ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hxint : IsIntegral ↥(Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) B) x) :
    x ∈ Submodule.span ℂ (RSet F B S) := by
  classical
  set ι := algebraMap ℂ K
  set L₀ := KFld F S
  haveI : CharZero ↥L₀ := charZero_KFld F L₀
  have hint : IsIntegral ↥L₀ (ι c) := isIntegral_KFld_algebraMap F hc
  set E := IntermediateField.adjoin ↥L₀ {ι c}
  set g := IntermediateField.AdjoinSimple.gen ↥L₀ (ι c)
  set pb := IntermediateField.adjoin.powerBasis hint
  have hpbg : pb.gen = g := IntermediateField.adjoin.powerBasis_gen hint
  have hpbd : pb.dim = (minpoly ↥L₀ (ι c)).natDegree :=
    IntermediateField.adjoin.powerBasis_dim hint
  set x' : ↥E := ⟨x, closure_adjoin_le F hxK⟩
  set y : Fin pb.dim → ↥L₀ := fun i ↦ pb.basis.repr x' i
  have hx' : x' = ∑ i, y i • g ^ (i : ℕ) := by
    conv_lhs => rw [← pb.basis.sum_repr x']
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pb.coe_basis, hpbg]

  obtain ⟨P, hPm, hPc, hPx⟩ := (isIntegral_subalgebra_iff _ x).mp hxint
  set d := P.natDegree
  choose pc hpc hpcφ using fun n ↦ exists_lift_of_mem_adjoin F B hBS hc (hPc n)
  have hw : x' ^ d + ∑ n ∈ Finset.range d, pc n * x' ^ n = 0 := by
    apply Subtype.ext
    rw [IntermediateField.coe_add, IntermediateField.coe_pow, AddSubmonoidClass.coe_finsetSum,
      ZeroMemClass.coe_zero]
    have := hPx
    rw [hPm.as_sum, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum] at this
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      at this
    rw [← this]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow, hpc]

  set roots := (minpoly ↥L₀ (ι c)).aroots K
  set s := roots.toFinset
  have hsconst : ∀ r ∈ s, ∃ a : ℂ, IsIntegral ↥F a ∧ ι a = r := fun r hr ↦
    root_minpoly_KFld_eq_algebraMap F hc (Multiset.mem_toFinset.mp hr)
  let φ : ∀ r, r ∈ roots → (↥E →ₐ[↥L₀] K) := fun r hr ↦
    (IntermediateField.algHomAdjoinIntegralEquiv ↥L₀ hint).symm ⟨r, hr⟩
  have hφg : ∀ r hr, φ r hr g = r := fun r hr ↦
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ↥L₀ hint ⟨r, hr⟩
  let zf : K → K := fun r ↦ if hr : r ∈ roots then φ r hr x' else 0

  have hZ1 : ∀ r hr, IsIntegral ↥(TRng F B) (φ r hr x') := by
    intro r hr
    set T := Algebra.adjoin ↥(TRng F B) {r}
    have hrint : IsIntegral ↥(TRng F B) r := by
      obtain ⟨a, ha, rfl⟩ := root_minpoly_KFld_eq_algebraMap F hc hr
      exact isIntegral_TRng_algebraMap F ha
    have hpcT : ∀ n, φ r hr (pc n) ∈ T := by
      intro n
      have := hpcφ n (φ r hr)
      rwa [hφg] at this
    have hT : IsIntegral ↥T (φ r hr x') := by
      rw [isIntegral_subalgebra_iff]
      refine ⟨X ^ d + ∑ n ∈ Finset.range d, C (φ r hr (pc n)) * X ^ n, ?_, ?_, ?_⟩
      · apply Polynomial.monic_X_pow_add
        refine (Polynomial.degree_sum_le _ _).trans_lt ?_
        refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun k hk ↦ ?_
        exact (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt
          (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk))
      · intro k
        rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
        refine Subalgebra.add_mem _ ?_ (Subalgebra.sum_mem _ fun n _ ↦ ?_)
        · split_ifs
          · exact Subalgebra.one_mem _
          · exact Subalgebra.zero_mem _
        · rw [Polynomial.coeff_C_mul_X_pow]
          split_ifs
          · exact hpcT n
          · exact Subalgebra.zero_mem _
      · rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum]
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [← map_pow]
        simp_rw [← map_pow, ← map_mul]
        rw [← map_sum, ← map_add, hw, map_zero]
    exact isIntegral_of_isIntegral_adjoin_singleton hrint hT

  have hZ2 : ∀ r hr, φ r hr x' = ∑ i, (y i : K) * r ^ (i : ℕ) := by
    intro r hr
    rw [hx', map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_pow, hφg, AlgHom.commutes]
    rfl

  set Y : K[X] := ∑ i : Fin pb.dim, C (y i : K) * X ^ (i : ℕ)
  have hcard : s.card = pb.dim := by
    rw [hpbd]; exact card_rootFinset_minpoly_KFld F hc
  have hYdeg : Y.degree < s.card := by
    rw [hcard]; exact Polynomial.degree_sum_fin_lt _
  have hYeval : ∀ r ∈ s, Y.eval (id r) = zf r := by
    intro r hr
    have hr' : r ∈ roots := Multiset.mem_toFinset.mp hr
    simp only [zf, dite_eq_left hr', id, hZ2 r hr', Y, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hY : Y = Lagrange.interpolate s id zf :=
    Lagrange.eq_interpolate_of_eval_eq zf (Set.injOn_id _) hYdeg hYeval
  have hYcoeff : ∀ i : Fin pb.dim, Y.coeff i = (y i : K) := by
    intro i
    simp only [Y, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [ite_eq_right (fun h ↦ hji (Fin.ext h.symm))]
    · intro h; exact absurd (Finset.mem_univ i) h

  have hZ4 : ∀ i : Fin pb.dim, IsIntegral ↥(TRng F B) (y i : K) := by
    intro i
    rw [← hYcoeff, hY, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff]
    refine IsIntegral.sum _ fun r hr ↦ ?_
    rw [Polynomial.coeff_C_mul]
    refine IsIntegral.mul ?_ (isIntegral_coeff_lagrangeBasis F hsconst hr _)
    have hr' : r ∈ roots := Multiset.mem_toFinset.mp hr
    simp only [zf, dite_eq_left hr']
    exact hZ1 r hr'

  have hZ5 : ∀ i : Fin pb.dim, (y i : K) ∈ RSet F B S := fun i ↦ ⟨(y i).2, hZ4 i⟩

  have hxsum : x = ∑ i : Fin pb.dim, (y i : K) * ι c ^ (i : ℕ) := by
    have := congrArg (fun e : ↥E ↦ (e : K)) hx'
    rw [IntermediateField.coe_sum] at this
    rw [show x = (x' : K) from rfl, this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [IntermediateField.coe_smul, IntermediateField.coe_pow,
      IntermediateField.AdjoinSimple.coe_gen, IntermediateField.smul_def, smul_eq_mul]
  rw [hxsum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  have : (y i : K) * ι c ^ (i : ℕ) = (c ^ (i : ℕ)) • (y i : K) := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hZ5 i))

private theorem mem_KFld_iff_closure (z : K) :
    z ∈ KFld F S ↔ z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield,
    range_algebraMap_subfield]

private theorem isIntegral_TRng_iff_closure (z : K) :
    IsIntegral ↥(TRng F B) z ↔
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ B)) z := by
  rw [isIntegral_adjoin_iff_closure, range_algebraMap_subfield]

private theorem isIntegral_adjoin_iff_closure' (E₀ : IntermediateField ↥F ℂ) (z : K) :
    IsIntegral ↥(Algebra.adjoin ↥E₀ B) z ↔
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (E₀ : Set ℂ) ∪ B)) z := by
  rw [isIntegral_adjoin_iff_closure, range_algebraMap_subfield']

end IsIntAux

theorem IsIntegral.mem_span_of_adjoin_simple_constants {K : Type*} [Field K] [Algebra ℂ K]
    (F : IntermediateField ℚ ℂ) (B S : Set K) (hBS : B ⊆ S) (c : ℂ) (hc : IsAlgebraic ↥F c)
    (y : K)
    (hyS : y ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hyB : IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ B)) y) :
    y ∈ Submodule.span ℂ {z : K | z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ B)) z} := by
  have hyB' : IsIntegral ↥(Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) B) y := by
    rw [IsIntAux.isIntegral_adjoin_iff_closure' F]
    exact hyB
  have h := IsIntAux.mem_span_RSet_of_adjoin_simple F B S hBS hc.isIntegral hyS hyB'
  refine Submodule.span_mono (fun z hz => ?_) h
  exact ⟨(IsIntAux.mem_KFld_iff_closure F z).mp hz.1,
    (IsIntAux.isIntegral_TRng_iff_closure F z).mp hz.2⟩





set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace IsIntAuxT

variable {K : Type*} [Field K] [Algebra ℂ K]

omit [Algebra ℂ K] in

private theorem isIntegral_subring_iff (T : Subring K) (y : K) :
    IsIntegral ↥T y ↔ ∃ p : K[X], p.Monic ∧ (∀ n, p.coeff n ∈ T) ∧ p.eval y = 0 := by
  constructor
  · rintro ⟨p, hm, hp⟩
    refine ⟨p.map (algebraMap ↥T K), hm.map _, fun n ↦ ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff n).2
    · rwa [Polynomial.eval_map]
  · rintro ⟨p, hm, hc, hp⟩
    have hl : p ∈ Polynomial.lifts (algebraMap ↥T K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; exact ⟨⟨p.coeff n, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hp]

omit [Algebra ℂ K] in

private theorem isIntegral_subalgebra_iff {R₀ : Type*} [CommRing R₀] [Algebra R₀ K]
    (T : Subalgebra R₀ K) (y : K) :
    IsIntegral ↥T y ↔ ∃ p : K[X], p.Monic ∧ (∀ n, p.coeff n ∈ T) ∧ p.eval y = 0 := by
  constructor
  · rintro ⟨p, hm, hp⟩
    refine ⟨p.map (algebraMap ↥T K), hm.map _, fun n ↦ ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff n).2
    · rwa [Polynomial.eval_map]
  · rintro ⟨p, hm, hc, hp⟩
    have hl : p ∈ Polynomial.lifts (algebraMap ↥T K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; exact ⟨⟨p.coeff n, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hp]

omit [Algebra ℂ K] in

private theorem isIntegral_adjoin_iff_closure {R₀ : Type*} [CommRing R₀] [Algebra R₀ K] (B : Set K) (y : K) :
    IsIntegral ↥(Algebra.adjoin R₀ B) y ↔
      IsIntegral ↥(Subring.closure (Set.range (algebraMap R₀ K) ∪ B)) y := by
  rw [isIntegral_subalgebra_iff, isIntegral_subring_iff]
  simp only [Algebra.mem_adjoin_iff]

omit [Algebra ℂ K] in

private theorem isIntegral_of_isIntegral_adjoin_singleton {A : Type*} [CommRing A] [Algebra A K] {r z : K}
    (hr : IsIntegral A r) (hz : IsIntegral ↥(Algebra.adjoin A {r}) z) : IsIntegral A z := by
  haveI : Algebra.IsIntegral A ↥(Algebra.adjoin A {r}) :=
    Algebra.IsIntegral.adjoin fun _ h ↦ by rw [Set.mem_singleton_iff] at h; rw [h]; exact hr
  exact isIntegral_trans z hz

private theorem algebraMap_subfield_apply (F : IntermediateField ℚ ℂ) (c : ↥F) :
    algebraMap ↥F K c = algebraMap ℂ K (c : ℂ) := rfl

private theorem range_algebraMap_subfield (F : IntermediateField ℚ ℂ) :
    Set.range (algebraMap ↥F K) = ⇑(algebraMap ℂ K) '' (F : Set ℂ) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, c.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, hc⟩, rfl⟩

private theorem algebraMap_subfield_apply' (F : IntermediateField ℚ ℂ) (E₀ : IntermediateField ↥F ℂ)
    (c : ↥E₀) : algebraMap ↥E₀ K c = algebraMap ℂ K (c : ℂ) := rfl

private theorem range_algebraMap_subfield' (F : IntermediateField ℚ ℂ) (E₀ : IntermediateField ↥F ℂ) :
    Set.range (algebraMap ↥E₀ K) = ⇑(algebraMap ℂ K) '' (E₀ : Set ℂ) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, c.2, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact ⟨⟨c, hc⟩, rfl⟩

private theorem charZero_K : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective

private theorem charZero_KFld (F : IntermediateField ℚ ℂ) (L₀ : IntermediateField ↥F K) : CharZero ↥L₀ :=
  haveI : CharZero ↥F := charZero_of_injective_algebraMap (algebraMap ℚ ↥F).injective
  charZero_of_injective_algebraMap (algebraMap ↥F ↥L₀).injective

variable (F : IntermediateField ℚ ℂ) (t : K) (S : Set K)

private abbrev KFld : IntermediateField ↥F K := IntermediateField.adjoin ↥F S

private abbrev TRng : Subalgebra ↥F K := Algebra.adjoin ↥F {t}

private def RSet : Set K := {y | y ∈ KFld F S ∧ IsIntegral ↥(TRng F t) y}

private abbrev RFld : IntermediateField ↥F K := (↥F)⟮t⟯

private abbrev KFldT : IntermediateField ↥(RFld F t) K := IntermediateField.adjoin ↥(RFld F t) S

noncomputable scoped instance algebraTRng_KFldT : Algebra ↥(TRng F t) ↥(KFldT F t S) :=
  ((algebraMap ↥(RFld F t) ↥(KFldT F t S)).comp (algebraMap ↥(TRng F t) ↥(RFld F t))).toAlgebra

noncomputable scoped instance smulTRng_KFldT : SMul ↥(TRng F t) ↥(KFldT F t S) := Algebra.toSMul

noncomputable scoped instance moduleTRng_KFldT : Module ↥(TRng F t) ↥(KFldT F t S) := Algebra.toModule

scoped instance : IsScalarTower ↥(TRng F t) ↥(RFld F t) ↥(KFldT F t S) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

scoped instance : IsScalarTower ↥(TRng F t) ↥(KFldT F t S) K :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

scoped instance : FaithfulSMul ↥(TRng F t) ↥(KFldT F t S) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact (FaithfulSMul.algebraMap_injective ↥(RFld F t) ↥(KFldT F t S)).comp
    (FaithfulSMul.algebraMap_injective ↥(TRng F t) ↥(RFld F t))

private abbrev RFa : Subalgebra ↥(TRng F t) ↥(KFldT F t S) := integralClosure ↥(TRng F t) ↥(KFldT F t S)

scoped instance commRing_RFa : CommRing ↥(RFa F t S) := inferInstance

private theorem KFldT_restrictScalars (htS : t ∈ S) :
    (KFldT F t S).restrictScalars ↥F = KFld F S := by
  rw [show KFldT F t S = IntermediateField.adjoin ↥(RFld F t) S from rfl,
    IntermediateField.adjoin_adjoin_left]
  congr 1
  simp [Set.insert_eq_self.mpr htS]

private theorem mem_KFldT_iff (htS : t ∈ S) (z : K) : z ∈ KFldT F t S ↔ z ∈ KFld F S := by
  rw [← KFldT_restrictScalars F t S htS, IntermediateField.mem_restrictScalars]

section instances

scoped instance : IsDomain ↥(TRng F t) := Subalgebra.isDomain _

private def TRngEquiv (ht : Transcendental ℂ t) : (↥F)[X] ≃ₐ[↥F] ↥(TRng F t) :=
  Polynomial.algEquivOfTranscendental ↥F t
    (ht.restrictScalars (FaithfulSMul.algebraMap_injective ↥F ℂ))

private theorem isPrincipalIdealRing_TRng (ht : Transcendental ℂ t) :
    IsPrincipalIdealRing ↥(TRng F t) :=
  IsPrincipalIdealRing.of_surjective (TRngEquiv F t ht).toRingEquiv.toRingHom
    (TRngEquiv F t ht).surjective

private theorem finiteDimensional_KFldT (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s) :
    FiniteDimensional ↥(RFld F t) ↥(KFldT F t S) := by
  haveI : Finite ↥S := hSfin.to_subtype
  refine IntermediateField.finiteDimensional_adjoin (fun s hs => ?_)
  exact (hSint s hs).tower_top

scoped instance charZero_KFldT : CharZero ↥(KFldT F t S) :=
  haveI : CharZero ↥(RFld F t) := charZero_KFld F (RFld F t)
  charZero_of_injective_algebraMap (algebraMap ↥(RFld F t) ↥(KFldT F t S)).injective

private theorem isDedekindDomain_RFa (ht : Transcendental ℂ t) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s) : IsDedekindDomain ↥(RFa F t S) := by
  haveI := isPrincipalIdealRing_TRng F t ht
  haveI := finiteDimensional_KFldT F t S hSfin hSint
  exact integralClosure.isDedekindDomain ↥(TRng F t) ↥(RFld F t) ↥(KFldT F t S)

private theorem isFractionRing_RFa (ht : Transcendental ℂ t) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s) :
    IsFractionRing ↥(RFa F t S) ↥(KFldT F t S) := by
  have hPID := isPrincipalIdealRing_TRng F t ht
  haveI : IsDedekindDomain ↥(TRng F t) := @IsPrincipalIdealRing.isDedekindDomain _ _ _ hPID
  haveI := finiteDimensional_KFldT F t S hSfin hSint
  exact integralClosure.isFractionRing_of_finite_extension ↥(RFld F t) ↥(KFldT F t S)

end instances


private theorem isIntegrallyClosed_RFa_polynomial (ht : Transcendental ℂ t) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s) :
    IsIntegrallyClosed (Polynomial ↥(RFa F t S)) := by
  haveI : IsDedekindDomain ↥(RFa F t S) := isDedekindDomain_RFa F t S ht hSfin hSint
  exact instIsIntegrallyClosedPolynomialOfIsDomain

private theorem algebraMap_adjoinF_mem {c : ℂ} {z : ℂ} (hz : z ∈ IntermediateField.adjoin ↥F {c}) :
    algebraMap ℂ K z ∈
      IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c} := by
  set f := IsScalarTower.toAlgHom ↥F ℂ K
  have h1 : algebraMap ℂ K z ∈ (IntermediateField.adjoin ↥F {c}).map f := by
    rw [← SetLike.mem_coe, IntermediateField.coe_map]
    exact ⟨z, hz, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton] at h1
  have h2 : IntermediateField.adjoin ↥F {f c} ≤
      (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).restrictScalars ↥F :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.mem_adjoin_simple_self ↥(KFld F S) _))
  exact h2 h1

private theorem closure_adjoin_le {c : ℂ} :
    Subfield.closure
        (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S) ≤
      (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).toSubfield := by
  refine Subfield.closure_le.mpr ?_
  rintro y (⟨z, hz, rfl⟩ | hy)
  · exact algebraMap_adjoinF_mem F S hz
  · exact (IntermediateField.adjoin ↥(KFld F S) {algebraMap ℂ K c}).algebraMap_mem
      ⟨y, IntermediateField.subset_adjoin ↥F S hy⟩

private theorem t_mem_RSet (htS : t ∈ S) : t ∈ RSet F t S :=
  ⟨IntermediateField.subset_adjoin ↥F S htS, isIntegral_algebraMap
    (x := (⟨t, Algebra.self_mem_adjoin_singleton ↥F t⟩ : ↥(TRng F t)))⟩

private theorem algebraMap_mem_RSet (z : ↥F) : algebraMap ↥F K z ∈ RSet F t S :=
  ⟨(KFld F S).algebraMap_mem z, isIntegral_algebraMap (x := algebraMap ↥F ↥(TRng F t) z)⟩

variable (c : ℂ)


private def rfPolyEval : (↥(RFa F t S))[X] →+* K :=
  Polynomial.eval₂RingHom ((algebraMap ↥(KFldT F t S) K).comp (RFa F t S).val.toRingHom)
    (algebraMap ℂ K c)

variable {c}

private theorem rfPolyEval_injective
    (htc : Transcendental ↥(KFldT F t S) (algebraMap ℂ K c)) :
    Function.Injective (rfPolyEval F t S c) := by
  have h1 : Function.Injective
      (Polynomial.aeval (R := ↥(KFldT F t S)) (algebraMap ℂ K c)) :=
    transcendental_iff_injective.mp htc
  have h2 : Function.Injective (Polynomial.map (RFa F t S).val.toRingHom) :=
    Polynomial.map_injective _ Subtype.val_injective
  have hcomp : ⇑(rfPolyEval F t S c) =
      ⇑(Polynomial.aeval (R := ↥(KFldT F t S)) (algebraMap ℂ K c)) ∘
        Polynomial.map (RFa F t S).val.toRingHom := by
    funext q
    simp only [rfPolyEval, Polynomial.coe_eval₂RingHom, Function.comp_apply,
      Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [hcomp]; exact h1.comp h2


private theorem isIntegral_KFldT_of (htS : t ∈ S) {y : K} (hyK : y ∈ KFld F S)
    (hyI : IsIntegral ↥(TRng F t) y) :
    IsIntegral ↥(TRng F t) (⟨y, (mem_KFldT_iff F t S htS y).mpr hyK⟩ : ↥(KFldT F t S)) := by
  obtain ⟨P, hPm, hPe⟩ := hyI
  refine ⟨P, hPm, ?_⟩
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, ← hPe, Polynomial.eval₂_def, Polynomial.eval₂_def,
    Polynomial.sum_def, Polynomial.sum_def, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul]
  rfl

private theorem mem_range_rfPolyEval_of_mem_RSet (htS : t ∈ S) {y : K} (hy : y ∈ RSet F t S) :
    y ∈ Set.range ⇑(rfPolyEval F t S c) := by
  obtain ⟨hyK, hyI⟩ := hy
  exact ⟨Polynomial.C ⟨_, isIntegral_KFldT_of F t S htS hyK hyI⟩, by simp [rfPolyEval]⟩

private theorem evalF_mem_range_rfPolyEval (htS : t ∈ S) (q : (↥F)[X]) :
    Polynomial.aeval (algebraMap ℂ K c) q ∈ Set.range ⇑(rfPolyEval F t S c) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p₁, h₁⟩ := hp; obtain ⟨p₂, h₂⟩ := hq
    exact ⟨p₁ + p₂, by rw [map_add, map_add, h₁, h₂]⟩
  | monomial n z =>
    have hz := algebraMap_mem_RSet F t S z
    obtain ⟨w, hw⟩ := mem_range_rfPolyEval_of_mem_RSet F t S htS (c := c) hz
    refine ⟨w * Polynomial.X ^ n, ?_⟩
    rw [Polynomial.aeval_monomial, map_mul, map_pow, hw]
    simp only [rfPolyEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      algebraMap_subfield_apply]

private theorem evalF_ne_zero (hc : Transcendental ↥F c) {q : (↥F)[X]} (hq : q ≠ 0) :
    Polynomial.aeval (algebraMap ℂ K c) q ≠ 0 := by
  intro h0
  rw [Polynomial.aeval_algebraMap_apply] at h0
  have h1 : Polynomial.aeval c q = 0 :=
    (map_eq_zero_iff _ (algebraMap ℂ K).injective).mp h0
  exact hq ((transcendental_iff.mp hc) q h1)

private theorem range_rfPolyEval_subset_span (htS : t ∈ S) :
    Set.range ⇑(rfPolyEval F t S c) ⊆
      (Submodule.span ℂ (RSet F t S) : Set K) := by
  rintro _ ⟨p, rfl⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n z =>
    have hshape : rfPolyEval F t S c (Polynomial.monomial n z) =
        (c ^ n) • ((z : ↥(KFldT F t S)) : K) := by
      rw [Algebra.smul_def, map_pow, rfPolyEval]
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
      exact mul_comm _ _
    rw [hshape]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨?_, ?_⟩)
    · exact (mem_KFldT_iff F t S htS _).mp (z : ↥(KFldT F t S)).2
    · have hzK : ((z : ↥(KFldT F t S)) : K) =
          algebraMap ↥(KFldT F t S) K (z : ↥(KFldT F t S)) := rfl
      rw [hzK]
      exact (z.2 : IsIntegral ↥(TRng F t) (z : ↥(KFldT F t S))).algebraMap


private theorem exists_clear_denominator (htS : t ∈ S) {a : K}
    (ha : a ∈ Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) ({t} : Set K)) :
    ∃ q : (↥F)[X], q ≠ 0 ∧
      Polynomial.aeval (algebraMap ℂ K c) q * a ∈ Set.range ⇑(rfPolyEval F t S c) := by
  induction ha using Algebra.adjoin_induction with
  | mem w hw =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [map_one, one_mul, Set.mem_singleton_iff.mp hw]
    exact mem_range_rfPolyEval_of_mem_RSet F t S htS (t_mem_RSet F t S htS)
  | algebraMap z =>
    obtain ⟨r, s, hz⟩ := (IntermediateField.mem_adjoin_simple_iff ↥F ((z : ℂ))).mp z.2
    by_cases hs : Polynomial.aeval c s = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      have hz0 : (z : ℂ) = 0 := by rw [hz, hs, div_zero]
      have hmap0 : algebraMap ↥(IntermediateField.adjoin ↥F {c}) K z = 0 := by
        rw [algebraMap_subfield_apply', hz0, map_zero]
      rw [map_one, one_mul, hmap0]
      exact ⟨0, map_zero _⟩
    · refine ⟨s, fun h0 => hs (by rw [h0, map_zero]), ?_⟩
      have hid : Polynomial.aeval (algebraMap ℂ K c) s *
          algebraMap ↥(IntermediateField.adjoin ↥F {c}) K z =
          Polynomial.aeval (algebraMap ℂ K c) r := by
        rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_algebraMap_apply,
          algebraMap_subfield_apply', ← map_mul]
        congr 1; rw [hz]; field_simp
      rw [hid]; exact evalF_mem_range_rfPolyEval F t S htS r
  | add u v _ _ ihu ihv =>
    obtain ⟨q₁, h₁0, A₁, hA₁⟩ := ihu; obtain ⟨q₂, h₂0, A₂, hA₂⟩ := ihv
    obtain ⟨B₁, hB₁⟩ := evalF_mem_range_rfPolyEval F t S htS (c := c) q₁
    obtain ⟨B₂, hB₂⟩ := evalF_mem_range_rfPolyEval F t S htS (c := c) q₂
    refine ⟨q₁ * q₂, mul_ne_zero h₁0 h₂0, B₂ * A₁ + B₁ * A₂, ?_⟩
    rw [map_add, map_mul, map_mul, hB₁, hB₂, hA₁, hA₂, map_mul]; ring
  | mul u v _ _ ihu ihv =>
    obtain ⟨q₁, h₁0, A₁, hA₁⟩ := ihu; obtain ⟨q₂, h₂0, A₂, hA₂⟩ := ihv
    refine ⟨q₁ * q₂, mul_ne_zero h₁0 h₂0, A₁ * A₂, ?_⟩
    rw [map_mul, map_mul, hA₁, hA₂]; ring

variable {F t}


private theorem mem_span_RSet_of_adjoin_simple_transcendental
    (ht : Transcendental ℂ t) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral ↥(TRng F t) s)
    {c : ℂ} (hc : Transcendental ↥F c)
    (htc : Transcendental ↥(KFldT F t S) (algebraMap ℂ K c))
    {x : K}
    (hxK : x ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hxint : IsIntegral ↥(Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) ({t} : Set K)) x) :
    x ∈ Submodule.span ℂ (RSet F t S) := by
  classical
  set c' : K := algebraMap ℂ K c with hc'

  set ψ : FractionRing ((↥(RFa F t S))[X]) →+* K :=
    IsFractionRing.lift (rfPolyEval_injective F t S htc) with hψ
  have hψalg : ∀ a : (↥(RFa F t S))[X], ψ (algebraMap _ _ a) = rfPolyEval F t S c a :=
    fun a => IsFractionRing.lift_algebraMap _ _
  have hψinj : Function.Injective ψ := ψ.injective
  haveI hDD : IsDedekindDomain ↥(RFa F t S) := isDedekindDomain_RFa F t S ht hSfin hSint
  haveI hFR : IsFractionRing ↥(RFa F t S) ↥(KFldT F t S) :=
    isFractionRing_RFa F t S ht hSfin hSint
  haveI hDomRFa0 : IsDomain ↥(RFa F t S) := Subalgebra.isDomain _
  haveI hA0 : NonUnitalNonAssocSemiring (FractionRing ((↥(RFa F t S))[X])) := inferInstance
  haveI hA : AddMonoidHomClass (FractionRing ((↥(RFa F t S))[X]) →+* K)
      (FractionRing ((↥(RFa F t S))[X])) K := RingHom.instRingHomClass.toAddMonoidHomClass

  have hrange : ∀ z ∈ IntermediateField.adjoin ↥(KFldT F t S) {c'}, z ∈ ψ.fieldRange := by
    intro z hz
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield] at hz
    refine Subfield.closure_le (t := ψ.fieldRange) |>.mpr ?_ hz
    rintro w (⟨w', rfl⟩ | rfl)
    · obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := ↥(RFa F t S)) w'
      rw [← hrs]
      have h1 : algebraMap ↥(KFldT F t S) K (algebraMap ↥(RFa F t S) ↥(KFldT F t S) r) =
          ψ (algebraMap _ _ (Polynomial.C r)) := by rw [hψalg]; simp [rfPolyEval]
      have h2 : algebraMap ↥(KFldT F t S) K (algebraMap ↥(RFa F t S) ↥(KFldT F t S) s) =
          ψ (algebraMap _ _ (Polynomial.C s)) := by rw [hψalg]; simp [rfPolyEval]
      rw [map_div₀, h1, h2]
      exact div_mem (RingHom.mem_fieldRange_self ψ _) (RingHom.mem_fieldRange_self ψ _)
    · exact ⟨algebraMap _ _ Polynomial.X, by rw [hψalg, hc']; simp [rfPolyEval]⟩

  have hxψ : x ∈ ψ.fieldRange := by
    refine hrange x ?_
    have h1 := closure_adjoin_le F S hxK
    have heq : (IntermediateField.adjoin ↥(KFld F S) {c'}).toSubfield =
        (IntermediateField.adjoin ↥(KFldT F t S) {c'}).toSubfield := by
      rw [IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield]
      have hrng : Set.range ⇑(algebraMap ↥(KFld F S) K) =
          Set.range ⇑(algebraMap ↥(KFldT F t S) K) := by
        ext z
        exact ⟨fun ⟨w, hw⟩ => ⟨⟨w, (mem_KFldT_iff F t S htS w).mpr w.2⟩, hw⟩,
          fun ⟨w, hw⟩ => ⟨⟨w, (mem_KFldT_iff F t S htS w).mp w.2⟩, hw⟩⟩
      rw [hrng]
    rw [← IntermediateField.mem_toSubfield, ← heq]; exact h1

  obtain ⟨P, hPmonic, hPc, hPx⟩ := (isIntegral_subalgebra_iff _ x).mp hxint
  set n := P.natDegree with hn
  have hrel : x ^ n + ∑ k ∈ Finset.range n, (P.coeff k) * x ^ k = 0 := by
    have h1 := hPx
    rw [hPmonic.as_sum, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      at h1
    linear_combination h1
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hrel; simp at hrel
    · exact h0

  choose qd hqd0 hqdW using fun (k : ℕ) (hk : k ∈ Finset.range n) =>
    exists_clear_denominator F t S htS (c := c) (hPc k)
  set Q : ℕ → (↥F)[X] := fun k => if h : k ∈ Finset.range n then qd k h else 1 with hQ
  have hQ0 : ∀ k, Q k ≠ 0 := by
    intro k; by_cases h : k ∈ Finset.range n
    · simp only [hQ, dite_eq_left h]; exact hqd0 k h
    · simp only [hQ, dite_eq_right h]; exact one_ne_zero
  set D : (↥F)[X] := ∏ k ∈ Finset.range n, Q k with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ0 k
  set Dv : K := Polynomial.aeval c' D with hDv
  have hDv0 : Dv ≠ 0 := evalF_ne_zero F hc hD0
  have hDvrange : Dv ∈ Set.range ⇑(rfPolyEval F t S c) := evalF_mem_range_rfPolyEval F t S htS D

  have hbW : ∀ k ∈ Finset.range n, Dv ^ (n - k) * (P.coeff k) ∈
      Set.range ⇑(rfPolyEval F t S c) := by
    intro k hk
    have hQk : Q k = qd k hk := by simp only [hQ, dite_eq_left hk]
    obtain ⟨A₁, hA₁⟩ := hqdW k hk
    obtain ⟨B₁, hB₁⟩ := evalF_mem_range_rfPolyEval F t S htS (c := c)
      ((∏ j ∈ (Finset.range n).erase k, Q j) * D ^ (n - k - 1))
    refine ⟨B₁ * A₁, ?_⟩
    rw [map_mul, hB₁, hA₁, map_mul, map_pow, ← hDv]
    have hDvsplit : Dv ^ (n - k) = Polynomial.aeval c' (qd k hk) *
        Polynomial.aeval c' (∏ j ∈ (Finset.range n).erase k, Q j) * Dv ^ (n - k - 1) := by
      have h1 : Polynomial.aeval c' (qd k hk) *
          Polynomial.aeval c' (∏ j ∈ (Finset.range n).erase k, Q j) = Dv := by
        rw [← hQk, ← map_mul, Finset.mul_prod_erase _ _ hk, hDv, hD]
      rw [h1, ← pow_succ']
      congr 1
      have hkn := Finset.mem_range.mp hk; omega
    rw [hDvsplit]; ring

  set y : K := Dv * x with hy
  have hDψ : Dv ∈ ψ.fieldRange := by
    obtain ⟨a, ha⟩ := hDvrange
    exact ⟨algebraMap _ _ a, by rw [hψalg]; exact ha⟩
  have hyψ : y ∈ ψ.fieldRange := mul_mem hDψ hxψ
  have hyrel : y ^ n + ∑ k ∈ Finset.range n, (Dv ^ (n - k) * (P.coeff k)) * y ^ k = 0 := by
    have h1 : ∀ k ∈ Finset.range n, (Dv ^ (n - k) * (P.coeff k)) * y ^ k =
        Dv ^ n * ((P.coeff k) * x ^ k) := by
      intro k hk
      have hkn : k ≤ n := (Finset.mem_range.mp hk).le
      rw [hy, mul_pow, show Dv ^ n = Dv ^ (n - k) * Dv ^ k from by
        rw [← pow_add, Nat.sub_add_cancel hkn]]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hy, mul_pow, ← mul_add, hrel, mul_zero]

  choose B hB using fun k (hk : k ∈ Finset.range n) => hbW k hk
  set BB : ℕ → (↥(RFa F t S))[X] := fun k => if h : k ∈ Finset.range n then B k h else 0 with hBB
  obtain ⟨m, hm⟩ := RingHom.mem_fieldRange.mp hyψ
  have hmrel : m ^ n + ∑ k ∈ Finset.range n, algebraMap _ _ (BB k) * m ^ k = 0 := by
    apply hψinj
    have hsum : ψ (∑ k ∈ Finset.range n, algebraMap (↥(RFa F t S))[X] (FractionRing ((↥(RFa F t S))[X])) (BB k) * m ^ k)
        = ∑ k ∈ Finset.range n, ψ (algebraMap (↥(RFa F t S))[X] (FractionRing ((↥(RFa F t S))[X])) (BB k) * m ^ k) :=
      map_sum ψ (fun k => algebraMap (↥(RFa F t S))[X] (FractionRing ((↥(RFa F t S))[X])) (BB k) * m ^ k) (Finset.range n)
    rw [map_add ψ _ _]
    rw [map_pow ψ]
    rw [hsum]
    rw [ψ.map_zero, hm]
    rw [show (∑ k ∈ Finset.range n, ψ (algebraMap _ _ (BB k) * m ^ k)) =
        ∑ k ∈ Finset.range n, (Dv ^ (n - k) * (P.coeff k)) * y ^ k from
      Finset.sum_congr rfl fun k hk => by
        rw [ψ.map_mul, map_pow ψ, hm, hψalg]; simp only [hBB, dite_eq_left hk]; rw [hB k hk]]
    exact hyrel

  have hmint : IsIntegral ((↥(RFa F t S))[X]) m := by
    refine ⟨Polynomial.X ^ n + ∑ k ∈ Finset.range n, Polynomial.C (BB k) * Polynomial.X ^ k,
      ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add ((Polynomial.degree_sum_le _ _).trans_lt
        ((Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun k hk =>
          (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt
            (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk))))
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_finsetSum]
      rw [show (∑ k ∈ Finset.range n, Polynomial.eval₂ (algebraMap _ _) m
          (Polynomial.C (BB k) * Polynomial.X ^ k)) =
          ∑ k ∈ Finset.range n, algebraMap _ _ (BB k) * m ^ k from
        Finset.sum_congr rfl fun k _ => by
          rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
            Polynomial.eval₂_X]]
      exact hmrel
  haveI hDomRFa : IsDomain ↥(RFa F t S) := Subalgebra.isDomain _
  haveI hICX : IsIntegrallyClosed ((↥(RFa F t S))[X]) :=
    isIntegrallyClosed_RFa_polynomial F t S ht hSfin hSint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hmint
  have hyrange : y ∈ Set.range ⇑(rfPolyEval F t S c) :=
    ⟨a, by rw [← hψalg, ha, hm]⟩
  have hyspan := range_rfPolyEval_subset_span F t S htS hyrange

  have hsmul : (Polynomial.aeval c D : ℂ) • x = y := by
    rw [Algebra.smul_def, hy, hDv, Polynomial.aeval_algebraMap_apply]
  have hs0 : (Polynomial.aeval c D : ℂ) ≠ 0 := by
    intro h0; exact hD0 ((transcendental_iff.mp hc) D h0)
  have hsx : (Polynomial.aeval c D : ℂ) • x ∈ Submodule.span ℂ (RSet F t S) := by
    rw [hsmul]; exact hyspan
  have h2 := Submodule.smul_mem (Submodule.span ℂ (RSet F t S))
    ((Polynomial.aeval c D : ℂ))⁻¹ hsx
  rwa [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ hs0, one_smul] at h2

variable (F) in
private theorem mem_KFld_iff_closure (z : K) :
    z ∈ KFld F S ↔ z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) := by
  rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield,
    range_algebraMap_subfield]

variable (F t) in
private theorem isIntegral_TRng_iff_closure (z : K) :
    IsIntegral ↥(TRng F t) z ↔
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ {t})) z := by
  rw [isIntegral_adjoin_iff_closure, range_algebraMap_subfield]

variable (F) in
private theorem isIntegral_adjoin_iff_closure' (E₀ : IntermediateField ↥F ℂ) (z : K) :
    IsIntegral ↥(Algebra.adjoin ↥E₀ ({t} : Set K)) z ↔
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (E₀ : Set ℂ) ∪ {t})) z := by
  rw [isIntegral_adjoin_iff_closure, range_algebraMap_subfield']

variable (F t) in
private theorem KFldT_toSubfield_eq (htS : t ∈ S) :
    (KFldT F t S).toSubfield = Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) := by
  have h1 : (KFldT F t S).toSubfield = ((KFldT F t S).restrictScalars ↥F).toSubfield := rfl
  rw [h1, KFldT_restrictScalars F t S htS, IntermediateField.adjoin_toSubfield,
    range_algebraMap_subfield]

variable (F t) in
private theorem transcendental_KFldT_of_closure (htS : t ∈ S)
    (htc : Transcendental ↥(Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S))
      (algebraMap ℂ K c)) :
    Transcendental ↥(KFldT F t S) (algebraMap ℂ K c) := by
  rw [Transcendental] at htc ⊢
  intro ⟨P, hP0, hPe⟩
  set e := (RingEquiv.subfieldCongr (KFldT_toSubfield_eq F t S htS)).toRingHom
  refine htc ⟨P.map e, fun h => hP0 (Polynomial.map_eq_zero_iff (RingEquiv.injective _) |>.mp h),
    ?_⟩
  have hcomp : (algebraMap ↥(Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S)) K).comp e =
      algebraMap ↥(KFldT F t S) K := by
    ext z; rfl
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  exact hPe

end IsIntAuxT


theorem IsIntegral.mem_span_of_adjoin_simple_constants_transcendental {K : Type*} [Field K] [Algebra ℂ K]
    (F : IntermediateField ℚ ℂ) (t : K) (ht : Transcendental ℂ t)
    (S : Set K) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral
      ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ {t})) s)
    (c : ℂ) (hc : Transcendental ↥F c)
    (htc : Transcendental ↥(Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S))
      (algebraMap ℂ K c))
    (y : K)
    (hyS : y ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hyB : IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ {t})) y) :
    y ∈ Submodule.span ℂ {z : K | z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ {t})) z} := by
  have hSint' : ∀ s ∈ S, IsIntegral ↥(IsIntAuxT.TRng F t) s := fun s hs =>
    (IsIntAuxT.isIntegral_TRng_iff_closure F t s).mpr (hSint s hs)
  have hyB' : IsIntegral
      ↥(Algebra.adjoin ↥(IntermediateField.adjoin ↥F {c}) ({t} : Set K)) y :=
    (IsIntAuxT.isIntegral_adjoin_iff_closure' F _ y).mpr hyB
  have htc' := IsIntAuxT.transcendental_KFldT_of_closure F t S htS htc
  have h := IsIntAuxT.mem_span_RSet_of_adjoin_simple_transcendental
    S ht htS hSfin hSint' hc htc' hyS hyB'
  refine Submodule.span_mono (fun z hz => ?_) h
  exact ⟨(IsIntAuxT.mem_KFld_iff_closure F S z).mp hz.1,
    (IsIntAuxT.isIntegral_TRng_iff_closure F t z).mp hz.2⟩





namespace IsAlgClosedAux

open IntermediateField

private theorem exists_algEquiv_apply_ne_of_exists_notMem {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsAlgClosed E] [CharZero F] {c : E}
    (h : ∃ K₁ : IntermediateField F E, Algebra.IsAlgebraic ↥K₁ E ∧ c ∉ K₁) :
    ∃ σ : E ≃ₐ[F] E, σ c ≠ c := by
  obtain ⟨K₁, halg, hcK₁⟩ := h
  haveI : IsAlgClosure ↥K₁ E := ⟨inferInstance, halg⟩
  haveI : CharZero ↥K₁ :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F ↥K₁)
  haveI : IsGalois ↥K₁ E := IsAlgClosure.isGalois _ _
  have hcbot : c ∉ (⊥ : IntermediateField ↥K₁ E) := by
    rw [IntermediateField.mem_bot]
    rintro ⟨a, rfl⟩
    exact hcK₁ a.2
  rw [InfiniteGalois.mem_bot_iff_fixed] at hcbot
  push Not at hcbot
  obtain ⟨σ, hσ⟩ := hcbot
  exact ⟨σ.restrictScalars F, hσ⟩

open MvPolynomial Polynomial in

private theorem mem_bot_of_isAlgebraic_of_mem_adjoin_algebraicIndependent {F E : Type*} [Field F]
    [Field E] [Algebra F E] {ι : Type*} {x : ι → E} (hx : AlgebraicIndependent F x)
    {c : E} (hmem : c ∈ IntermediateField.adjoin F (Set.range x)) (halg : IsAlgebraic F c) :
    c ∈ (⊥ : IntermediateField F E) := by
  classical

  set K₁ := IntermediateField.adjoin F (Set.range x)
  let φ := hx.aevalEquivField
  set r : FractionRing (MvPolynomial ι F) := φ.symm ⟨c, hmem⟩ with hr_def
  have hφr : φ r = ⟨c, hmem⟩ := φ.apply_symm_apply _

  have h1 : IsAlgebraic F (⟨c, hmem⟩ : ↥K₁) :=
    (isAlgebraic_algHom_iff K₁.val Subtype.val_injective).mp halg
  have hr_alg : IsAlgebraic F r :=
    (isAlgebraic_algHom_iff φ.toAlgHom φ.injective).mp (hφr ▸ h1)

  haveI : IsIntegrallyClosed (MvPolynomial ι F) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  have hr_int : IsIntegral (MvPolynomial ι F) r :=
    (isAlgebraic_iff_isIntegral.mp hr_alg).tower_top
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.isIntegral_iff.mp hr_int

  set m := minpoly F c
  have hc_int : IsIntegral F c := isAlgebraic_iff_isIntegral.mp halg
  have hmc' : (Polynomial.aeval (⟨c, hmem⟩ : ↥K₁)) m = 0 := by
    refine Subtype.val_injective ?_
    rw [ZeroMemClass.coe_zero,
      show ((Polynomial.aeval (⟨c, hmem⟩ : ↥K₁)) m : E)
        = (Polynomial.aeval (K₁.val ⟨c, hmem⟩)) m from
      (Polynomial.aeval_algHom_apply K₁.val (⟨c, hmem⟩ : ↥K₁) m).symm]
    exact minpoly.aeval F c
  have hmr : (Polynomial.aeval r) m = 0 := by
    rw [show r = φ.symm ⟨c, hmem⟩ from rfl,
      show (Polynomial.aeval (φ.symm ⟨c, hmem⟩)) m = φ.symm ((Polynomial.aeval ⟨c, hmem⟩) m) from
        Polynomial.aeval_algHom_apply (f := φ.symm) (⟨c, hmem⟩ : ↥K₁) m,
      hmc', map_zero]
  have hmp : (Polynomial.aeval p) m = 0 := by
    have h2 := Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom F (MvPolynomial ι F) (FractionRing (MvPolynomial ι F))) p m
    rw [IsScalarTower.toAlgHom_apply, hp, hmr] at h2
    exact (map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial ι F)
      (FractionRing (MvPolynomial ι F)))).mp h2.symm

  let ev : MvPolynomial ι F →ₐ[F] F := MvPolynomial.aeval (fun _ ↦ (0 : F))
  have hma : (Polynomial.aeval (ev p)) m = 0 := by
    rw [show (Polynomial.aeval (ev p)) m = ev ((Polynomial.aeval p) m) from
      Polynomial.aeval_algHom_apply ev p m, hmp, map_zero]
  have hma' : m.IsRoot (ev p) := by
    rwa [Polynomial.IsRoot, ← congrFun (Polynomial.coe_aeval_eq_eval (ev p)) m]

  have hm_irr : Irreducible m := minpoly.irreducible hc_int
  have hdeg : m.degree = 1 := Polynomial.degree_eq_one_of_irreducible_of_root hm_irr hma'
  rw [IntermediateField.mem_bot]
  obtain ⟨y, hy⟩ := minpoly.degree_eq_one_iff.mp hdeg
  exact ⟨y, hy⟩

private theorem exists_intermediateField_isAlgebraic_notMem_of_isAlgebraic {F E : Type*} [Field F]
    [Field E] [Algebra F E] {c : E} (halg : IsAlgebraic F c)
    (hc : c ∉ (⊥ : IntermediateField F E)) :
    ∃ K₁ : IntermediateField F E, Algebra.IsAlgebraic ↥K₁ E ∧ c ∉ K₁ := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F E
  refine ⟨IntermediateField.adjoin F (Set.range ((↑) : s → E)), hs.isAlgebraic_field, ?_⟩
  intro hmem
  exact hc (mem_bot_of_isAlgebraic_of_mem_adjoin_algebraicIndependent hs.1 hmem halg)

open Polynomial in

private theorem notMem_adjoin_sq_of_transcendental {F E : Type*} [Field F] [Field E] [Algebra F E]
    {c : E} (hc : Transcendental F c) : c ∉ IntermediateField.adjoin F {c ^ 2} := by
  intro hmem
  rw [IntermediateField.mem_adjoin_simple_iff] at hmem
  obtain ⟨r, s, hrs⟩ := hmem
  have hcomp : ∀ P : F[X], (aeval (c ^ 2)) P = (aeval c) (P.comp (X ^ 2)) := fun P ↦ by
    rw [aeval_comp, map_pow, aeval_X]
  rw [hcomp r, hcomp s] at hrs
  have hc0 : c ≠ 0 := fun h ↦ hc (h ▸ isAlgebraic_zero)
  have hsc_ne : (aeval c) (s.comp (X ^ 2)) ≠ 0 := fun h0 ↦ hc0 (by rw [hrs, h0, div_zero])
  have heq : (aeval c) (X * s.comp (X ^ 2)) = (aeval c) (r.comp (X ^ 2)) := by
    rw [map_mul, aeval_X]; exact (eq_div_iff hsc_ne).mp hrs
  have hpeq : (X : F[X]) * s.comp (X ^ 2) = r.comp (X ^ 2) :=
    (transcendental_iff_injective.mp hc) heq
  have hsc2_ne : s.comp ((X : F[X]) ^ 2) ≠ 0 := fun h ↦ hsc_ne (h ▸ map_zero _)
  have hdeg := congrArg Polynomial.natDegree hpeq
  rw [natDegree_mul X_ne_zero hsc2_ne, natDegree_X, natDegree_comp, natDegree_comp,
    natDegree_X_pow] at hdeg
  omega

private theorem exists_algEquiv_apply_ne_of_transcendental {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsAlgClosed E] [CharZero F] {c : E} (hc : Transcendental F c) :
    ∃ σ : E ≃ₐ[F] E, σ c ≠ c := by
  set F' := IntermediateField.adjoin F ({c ^ 2} : Set E) with hF'_def
  have halg_F' : IsAlgebraic ↥F' c :=
    ⟨Polynomial.X ^ 2 - Polynomial.C ⟨c ^ 2, IntermediateField.mem_adjoin_simple_self F (c ^ 2)⟩,
      Polynomial.X_pow_sub_C_ne_zero two_pos _, by simp⟩
  have hc_F' : c ∉ (⊥ : IntermediateField ↥F' E) := by
    rw [IntermediateField.mem_bot]; rintro ⟨a, ha⟩
    exact notMem_adjoin_sq_of_transcendental hc (hF'_def ▸ ha ▸ a.2)
  haveI : CharZero ↥F' :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F ↥F')
  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_ne_of_exists_notMem
    (exists_intermediateField_isAlgebraic_notMem_of_isAlgebraic halg_F' hc_F')
  exact ⟨σ.restrictScalars F, hσ⟩

private theorem exists_algEquiv_apply_ne {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsAlgClosed E] [CharZero F] {c : E} (hc : c ∉ (⊥ : IntermediateField F E)) :
    ∃ σ : E ≃ₐ[F] E, σ c ≠ c := by
  by_cases halg : IsAlgebraic F c
  · exact exists_algEquiv_apply_ne_of_exists_notMem
      (exists_intermediateField_isAlgebraic_notMem_of_isAlgebraic halg hc)
  · exact exists_algEquiv_apply_ne_of_transcendental halg

end IsAlgClosedAux

theorem IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsAlgClosed E] [CharZero F] {c : E} (hc : c ∉ Set.range (algebraMap F E)) :
    ∃ σ : E ≃ₐ[F] E, σ c ≠ c :=
  IsAlgClosedAux.exists_algEquiv_apply_ne fun h => hc (IntermediateField.mem_bot.mp h)




set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Complex Real

namespace UpperHalfPlaneAux

section RatCoeff

open UpperHalfPlane ModularForm SlashInvariantForm ModularFormClass CuspForm ModularForm.CuspForm EisensteinSeries
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

private lemma ratCoeff_pow {p : PowerSeries ℂ} (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (k : ℕ) :
    ∀ n : ℕ, ∃ a : ℚ, (p ^ k).coeff n = (a : ℂ) := by
  induction k with
  | zero =>
    intro n
    refine ⟨if n = 0 then 1 else 0, ?_⟩
    rw [pow_zero, PowerSeries.coeff_one]
    split <;> simp
  | succ k ih =>
    rw [pow_succ]
    exact ratCoeff_mul ih hp

end RatCoeff

section DiscPow

open UpperHalfPlane ModularForm SlashInvariantForm ModularFormClass CuspForm ModularForm.CuspForm EisensteinSeries OnePoint Matrix.SpecialLinearGroup

open scoped MatrixGroups Manifold

private def discPowForm (m : ℕ) : ModularForm 𝒮ℒ (12 * m) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow m)

private lemma discPowForm_coe (m : ℕ) : ⇑(discPowForm m) = ⇑CuspForm.discriminant ^ m := by
  funext z
  simp [discPowForm, ModularForm.coe_mcast, ModularForm.coe_pow,
    CuspForm.toModularFormₗ_apply]

end DiscPow

section Width

open scoped UpperHalfPlane Manifold
open UpperHalfPlane hiding I

private lemma qParam_one_eq_pow {N : ℕ} (hN : N ≠ 0) (τ : ℂ) :
    Function.Periodic.qParam 1 τ = Function.Periodic.qParam N τ ^ N := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

private theorem qExpansion_coeff_width_fn (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
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


end Width

section WidthMF

open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open SlashInvariantFormClass ModularFormClass

namespace ModularFormClass
private theorem qExpansion_coeff_width {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) {N : ℕ} (hN : N ≠ 0) (n : ℕ) :
    (qExpansion N f).coeff n = if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos h1⟩
  exact qExpansion_coeff_width_fn f hN (by simpa using periodic_comp_ofComplex f h1)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) n

end ModularFormClass

end WidthMF

section BSix

open UpperHalfPlane ModularForm SlashInvariantForm UpperHalfPlaneAux.ModularFormClass CuspForm ModularForm.CuspForm Polynomial Real.Polynomial Filter
open scoped MatrixGroups Manifold

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

end BSix

section KPoleSec

open UpperHalfPlane ModularForm UpperHalfPlaneAux.ModularFormClass CuspForm ModularForm.CuspForm Polynomial Real.Polynomial Filter
open scoped MatrixGroups Manifold

variable {N : ℕ}

private lemma mem_of_rat (K : IntermediateField ℚ ℂ) {x : ℂ} (h : ∃ q : ℚ, x = (q : ℂ)) : x ∈ K := by
  obtain ⟨q, rfl⟩ := h
  exact SubfieldClass.ratCast_mem K q

private def KPoleAt (K : IntermediateField ℚ ℂ) (N m : ℕ) (f : ℍ → ℂ) : Prop :=
  Function.Periodic ((f * ⇑CuspForm.discriminant ^ m) ∘ ofComplex) N ∧
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m) ∧
    ∀ n : ℕ, (qExpansion N (f * ⇑CuspForm.discriminant ^ m)).coeff n ∈ K

private def KPole (K : IntermediateField ℚ ℂ) (N : ℕ) (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ ∃ m : ℕ, KPoleAt K N m f

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

private lemma mdiff_discPow (k : ℕ) : MDiff (⇑CuspForm.discriminant ^ k : ℍ → ℂ) := by
  rw [← discPowForm_coe]
  exact (discPowForm k).holo'

private lemma mdiff_mul_discPow {f : ℍ → ℂ} (hf : MDiff f) (m : ℕ) :
    MDiff (f * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) :=
  hf.mul (mdiff_discPow m)

private lemma analyticAt_cuspFunction_zero_of [NeZero N] {g : ℍ → ℂ} (hhol : MDiff g)
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

private lemma qExpansion_discPow_coeff_mem (K : IntermediateField ℚ ℂ) [NeZero N] (k n : ℕ) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff n ∈ K := by
  have h1 : qExpansion (N : ℝ) (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      qExpansion (N : ℝ) (discPowForm k) := by
    rw [← discPowForm_coe]
  rw [h1, ModularFormClass.qExpansion_coeff_width (discPowForm k)
    one_mem_strictPeriods_SL (NeZero.ne N)]
  split
  · rw [qExpansion_one_discPowForm]
    exact mem_of_rat K (ratCoeff_pow ratCoeff_discriminant k _)
  · exact zero_mem _

private lemma KPoleAt.pad {K : IntermediateField ℚ ℂ} [NeZero N] {f : ℍ → ℂ} {m m' : ℕ}
    (hhol : MDiff f) (hm : m ≤ m') (h : KPoleAt K N m f) : KPoleAt K N m' f := by
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

end KPoleSec

section BEightEngine

open Function

private theorem linearIndependent_pi_algebraMap_of_field {k K σ ι : Type*}
    [Field k] [CommRing K] [Nontrivial K] [Algebra k K]
    {v : ι → σ → k} (hv : LinearIndependent k v) :
    LinearIndependent K (fun i n ↦ algebraMap k K (v i n)) := by
  classical
  obtain ⟨⟨β, b⟩⟩ := Module.Free.exists_basis (R := k) (M := K)
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hc i hi
  have key : ∀ n : σ, (∑ j ∈ s, (v j n) • c j) = 0 := by
    intro n
    have := congrFun hc n
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  have key2 : ∀ (α : β) (n : σ), (∑ j ∈ s, (v j n) * (b.repr (c j) α)) = 0 := by
    intro α n
    have h1 := congrArg b.repr (key n)
    rw [map_sum, map_zero] at h1
    have h2 := congrFun (congrArg DFunLike.coe h1) α
    simpa only [Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] using h2
  have key3 : ∀ (α : β) (j : ι), j ∈ s → b.repr (c j) α = 0 := by
    intro α
    refine hv s (fun j ↦ b.repr (c j) α) ?_
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← key2 α n]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hzero : b.repr (c i) = 0 := Finsupp.ext fun α ↦ key3 α i hi
  exact b.repr.injective (by rw [hzero, map_zero])

end BEightEngine

section BEightHelper

open UpperHalfPlane Function Filter
open scoped Manifold

variable {N : ℕ}

private lemma mdpb_finsetSum_smul [NeZero N] {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {g : ι → ℍ → ℂ}
    (hhol : ∀ i ∈ s, MDiff (g i)) (hper : ∀ i ∈ s, Periodic ((g i) ∘ ofComplex) N)
    (hbd : ∀ i ∈ s, IsBoundedAtImInfty (g i)) :
    MDiff (∑ j ∈ s, c j • g j) ∧ Periodic ((∑ j ∈ s, c j • g j) ∘ ofComplex) N
      ∧ IsBoundedAtImInfty (∑ j ∈ s, c j • g j) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    refine ⟨?_, fun _ ↦ rfl, const_boundedAtFilter _ 0⟩
    have h__af := (mdifferentiable_const : MDiff (fun _ : ℍ ↦ (0 : ℂ)))
    simp at h__af ⊢
    exact h__af
  | cons a t hat ih =>
    have ⟨hh, hp, hb⟩ := ih (fun i hi ↦ hhol i (Finset.mem_cons_of_mem hi))
      (fun i hi ↦ hper i (Finset.mem_cons_of_mem hi))
      (fun i hi ↦ hbd i (Finset.mem_cons_of_mem hi))
    have haS : a ∈ Finset.cons a t hat := Finset.mem_cons_self a t
    simp only [Finset.sum_cons]
    refine ⟨((hhol a haS).const_smul _).add hh, ?_, ((hbd a haS).smul (c a)).add hb⟩
    intro z
    have h1 := hper a haS z; have h2 := hp z
    simp only [comp_apply] at h1 h2
    simp only [comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2]

private theorem qExpansion_finsetSum_smul [NeZero N] {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {g : ι → ℍ → ℂ} (hhol : ∀ i ∈ s, MDiff (g i))
    (hper : ∀ i ∈ s, Periodic ((g i) ∘ ofComplex) N) (hbd : ∀ i ∈ s, IsBoundedAtImInfty (g i)) :
    qExpansion N (∑ j ∈ s, c j • g j) = ∑ j ∈ s, c j • qExpansion N (g j) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using qExpansion_zero (N : ℝ)
  | cons a t hat ih =>
    have haS : a ∈ Finset.cons a t hat := Finset.mem_cons_self a t
    have htS : ∀ i ∈ t, i ∈ Finset.cons a t hat := fun i hi ↦ Finset.mem_cons_of_mem hi
    obtain ⟨hhS, hpS, hbS⟩ := mdpb_finsetSum_smul t c
      (fun i hi ↦ hhol i (htS i hi)) (fun i hi ↦ hper i (htS i hi))
      (fun i hi ↦ hbd i (htS i hi))
    have hper_a : Periodic ((c a • g a) ∘ ofComplex) N := fun z ↦ by
      have h1 := hper a haS z; simp only [comp_apply] at h1
      simp only [comp_apply, Pi.smul_apply, smul_eq_mul, h1]
    have han_a : AnalyticAt ℂ (cuspFunction N (c a • g a)) 0 :=
      analyticAt_cuspFunction_zero_of ((hhol a haS).const_smul _) hper_a ((hbd a haS).smul (c a))
    have han_t : AnalyticAt ℂ (cuspFunction N (∑ j ∈ t, c j • g j)) 0 :=
      analyticAt_cuspFunction_zero_of hhS hpS hbS
    rw [Finset.sum_cons, Finset.sum_cons, qExpansion_add han_a han_t,
      qExpansion_smul (analyticAt_cuspFunction_zero_of (hhol a haS) (hper a haS) (hbd a haS)),
      ih (fun i hi ↦ hhol i (htS i hi)) (fun i hi ↦ hper i (htS i hi))
        (fun i hi ↦ hbd i (htS i hi))]

end BEightHelper

section QNonzero

open scoped UpperHalfPlane Manifold MatrixGroups IntermediateField
open UpperHalfPlane hiding I

variable {N : ℕ} [NeZero N]

private lemma exists_qExpansion_coeff_ne_zero {g : ℍ → ℂ} (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Function.Periodic (g ∘ ofComplex) N) (hbd : IsBoundedAtImInfty g) (hg : g ≠ 0) :
    ∃ n, (qExpansion N g).coeff n ≠ 0 := by
  by_contra h
  push Not at h
  apply hg
  funext τ
  have hs := hasSum_qExpansion (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd τ
  simp only [h, zero_smul] at hs
  exact (hs.unique hasSum_zero)

end QNonzero

section BEightStageTwo

open UpperHalfPlane Function Filter
open scoped Manifold

variable {N : ℕ}

private lemma eq_zero_of_mul_discPow_eq_zero (M : ℕ) {h : ℍ → ℂ}
    (h0 : h * (⇑CuspForm.discriminant ^ M : ℍ → ℂ) = 0) : h = 0 := by
  funext τ
  have := congrFun h0 τ
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at this
  refine (mul_eq_zero.mp this).resolve_right ?_
  rw [congrFun CuspForm.coe_discriminant τ]
  exact pow_ne_zero M (ModularForm.discriminant_ne_zero τ)

private lemma finsetSum_smul_eq_zero_iff_qCoeff [NeZero N] {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {f : ι → ℍ → ℂ} (M : ℕ)
    (hhol : ∀ j ∈ s, MDiff (f j))
    (hper : ∀ j ∈ s, Periodic ((f j * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N)
    (hbd : ∀ j ∈ s, IsBoundedAtImInfty (f j * ⇑CuspForm.discriminant ^ M)) :
    (∑ j ∈ s, c j • f j = 0)
      ↔ ∀ n, ∑ j ∈ s, c j * (qExpansion N (f j * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
  set g : ι → ℍ → ℂ := fun j ↦ f j * ⇑CuspForm.discriminant ^ M with hg_def
  have hghol : ∀ j ∈ s, MDiff (g j) := fun j hj ↦ mdiff_mul_discPow (hhol j hj) M
  have hpull : ∑ j ∈ s, c j • g j = (∑ j ∈ s, c j • f j) * ⇑CuspForm.discriminant ^ M := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ (smul_mul_assoc (c j) (f j) _).symm
  have hq := qExpansion_finsetSum_smul s c hghol hper hbd
  constructor
  · intro h0 n
    rw [hpull, h0, zero_mul, qExpansion_zero (N : ℝ)] at hq
    have := congrArg (fun p : PowerSeries ℂ ↦ p.coeff n) hq.symm
    simpa only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, map_zero] using this
  · intro h0
    have hqeq : qExpansion N (∑ j ∈ s, c j • g j) = 0 := by
      rw [hq]; ext n
      simpa only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, map_zero] using h0 n
    obtain ⟨hh, hp, hb⟩ := mdpb_finsetSum_smul s c hghol hper hbd
    apply eq_zero_of_mul_discPow_eq_zero M
    rw [← hpull]
    by_contra hne
    obtain ⟨n, hn⟩ := exists_qExpansion_coeff_ne_zero hh hp hb hne
    rw [hqeq] at hn; simp at hn

private theorem linearIndependent_complex_of_kPole [NeZero N] (K : IntermediateField ℚ ℂ)
    {ι : Type*} {f : ι → ℍ → ℂ} (hKP : ∀ i, KPole K N (f i))
    (hli : LinearIndependent ↥K f) : LinearIndependent ℂ f := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi

  set m : ι → ℕ := fun j ↦ (hKP j).2.choose
  set M : ℕ := s.sup m
  have hKPM : ∀ j ∈ s, KPoleAt K N M (f j) := fun j hj ↦
    KPoleAt.pad (hKP j).1 (Finset.le_sup hj) (hKP j).2.choose_spec
  have hhol : ∀ (j : s), MDiff (f j) := fun j ↦ (hKP j).1
  have hper : ∀ (j : s), Periodic ((f j * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N :=
    fun j ↦ (hKPM j j.2).1
  have hbd : ∀ (j : s), IsBoundedAtImInfty (f j * ⇑CuspForm.discriminant ^ M) :=
    fun j ↦ (hKPM j j.2).2.1

  have hiff : ∀ (t : Finset s) (c' : s → ℂ),
      (∑ j ∈ t, c' j • f j = 0)
        ↔ ∀ n, ∑ j ∈ t, c' j * (qExpansion N (f j * ⇑CuspForm.discriminant ^ M)).coeff n = 0 :=
    fun t c' ↦ finsetSum_smul_eq_zero_iff_qCoeff t c' M (fun j _ ↦ hhol j)
      (fun j _ ↦ hper j) (fun j _ ↦ hbd j)

  set vK : s → ℕ → ↥K := fun j n ↦
    ⟨(qExpansion N (f j * ⇑CuspForm.discriminant ^ M)).coeff n, (hKPM j j.2).2.2 n⟩ with hvK_def
  have halg : ∀ x : ↥K, (x : ℂ) = algebraMap ↥K ℂ x := fun _ ↦ rfl
  have hvKcoe : ∀ (j : s) n, algebraMap ↥K ℂ (vK j n)
      = (qExpansion N (f j * ⇑CuspForm.discriminant ^ M)).coeff n := fun _ _ ↦ rfl

  have hli_s := hli.comp (Subtype.val : s → ι) Subtype.val_injective
  have hvKli : LinearIndependent ↥K vK := by
    rw [linearIndependent_iff']
    intro t d hd j hj
    have hcoeff : ∀ n, ∑ j' ∈ t, (d j' : ℂ)
        * (qExpansion N (f j' * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
      intro n
      have h1 := congrFun hd n
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h1
      have h2 := congrArg (fun x : ↥K ↦ (x : ℂ)) h1
      simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
        ZeroMemClass.coe_zero] at h2
      simp only [halg, hvKcoe] at h2; exact h2
    have hsumC : ∑ j' ∈ t, (d j' : ℂ) • f j' = 0 :=
      (hiff t (fun j' ↦ (d j' : ℂ))).mpr hcoeff
    have hsumK : ∑ j' ∈ t, d j' • (fun j'' : s ↦ f j'') j' = 0 := by
      rw [← hsumC]
      exact Finset.sum_congr rfl fun j' _ ↦ (algebraMap_smul ℂ (d j') (f j')).symm
    exact linearIndependent_iff'.mp hli_s t d hsumK j hj

  have hvCli := linearIndependent_pi_algebraMap_of_field (K := ℂ) hvKli

  have hcoeff' : ∀ n, ∑ j' ∈ (Finset.univ : Finset s), c j'
      * (qExpansion N (f j' * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
    intro n
    have := (hiff Finset.univ (fun j' ↦ c j')).mp ?_ n
    · exact this
    · rw [Finset.sum_coe_sort s (fun j' ↦ c j' • f j')]; exact hc
  have hsum0 : ∑ j' ∈ (Finset.univ : Finset s), (fun j'' : s ↦ c j''.1) j'
      • (fun n ↦ (algebraMap ↥K ℂ) (vK j' n)) = 0 := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hvKcoe]
    exact hcoeff' n
  exact linearIndependent_iff'.mp hvCli Finset.univ (fun j'' ↦ c j''.1) hsum0 ⟨i, hi⟩
    (Finset.mem_univ _)

end BEightStageTwo

end UpperHalfPlaneAux

open scoped Manifold in
theorem UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ ℂ) {ι : Type*} (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i) ∧ ∃ m : ℕ,
      Function.Periodic ((f i * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      UpperHalfPlane.IsBoundedAtImInfty (f i * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f i * ModularForm.discriminant ^ m)).coeff n ∈ K)
    (hli : LinearIndependent ↥K f) : LinearIndependent ℂ f :=
  UpperHalfPlaneAux.linearIndependent_complex_of_kPole K
    (fun i => ⟨(hf i).1, by
      obtain ⟨m, hm⟩ := (hf i).2
      exact ⟨m, by simpa only [UpperHalfPlaneAux.KPoleAt, CuspForm.coe_discriminant] using hm⟩⟩) hli







set_option linter.style.haveILetI false

open UpperHalfPlane ModularForm SlashInvariantForm Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Topology Manifold Pointwise

noncomputable section

namespace ModularForm

/-- The `q`-expansion coefficients, as a linear map to a finite function space. -/
private def qExpansionCoeffs_W2D {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] (k : ℤ) {h : ℝ}
    (hh : 0 < h) (h𝒢 : h ∈ 𝒢.strictPeriods) (B : ℕ) : ModularForm 𝒢 k →ₗ[ℂ] (Fin B → ℂ) where
  toFun f n := (qExpansion h f).coeff n
  map_add' f g := by
    ext n
    simp [ModularForm.qExpansion_add hh h𝒢]
  map_smul' a f := by
    ext n
    simp [ModularForm.qExpansion_smul hh h𝒢]

private lemma le_order_of_qExpansionCoeffs_eq_zero_W2D {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne]
    {k : ℤ} {h : ℝ} (hh : 0 < h) (h𝒢 : h ∈ 𝒢.strictPeriods) {B : ℕ} {f : ModularForm 𝒢 k}
    (hf : ModularForm.qExpansionCoeffs_W2D k hh h𝒢 B f = 0) : (B : ℕ∞) ≤ (qExpansion h f).order :=
  PowerSeries.nat_le_order _ _ fun n hn ↦ by
    have h__af := congr_fun hf ⟨n, hn⟩
    simp at h__af
    exact h__af

theorem finiteDimensional_of_isArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]
    [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (ModularForm 𝒢 k) := by
  obtain ⟨M, hM, hconj⟩ := Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj 𝒢
  have hM𝒢 : (M : ℝ) ∈ 𝒢.strictPeriods := by simpa using hconj 1
  set B := M * ((k * 𝒢.relIndex 𝒮ℒ).toNat / 12) + 1 with hB
  refine Module.Finite.of_injective (ModularForm.qExpansionCoeffs_W2D k (Nat.cast_pos.mpr hM) hM𝒢 B) ?_
  rw [injective_iff_map_eq_zero]
  intro f hf
  refine f.eq_zero_of_lt_order_qExpansion_of_isArithmetic hM hconj (lt_of_lt_of_le ?_
    (ModularForm.le_order_of_qExpansionCoeffs_eq_zero_W2D _ hM𝒢 hf))
  exact_mod_cast Nat.lt_succ_self _
end ModularForm

namespace CuspForm

theorem finiteDimensional_of_isArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]
    [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒢 k) := by
  haveI := ModularForm.finiteDimensional_of_isArithmetic 𝒢 k
  exact Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
end CuspForm

