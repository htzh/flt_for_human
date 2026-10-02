/-
Principal divisors for a finite separable extension of `RatFunc K`, after FLT's
`P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.lean`
(192 ln) and
`P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable.lean`
(39 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable.lean>).

Unlike the port's earlier `hasPrincipalDivisors_of_finiteDimensional_ratFunc`
(`PrincipalDivisors/Transcendence.lean`), which is stated over an extension
`F/RatFunc K` and carries `[CharZero K]`, FLT's node here is *characteristic-free*:
it passes to the splitting field of a primitive element, where the extension is
Galois, and descends the degree-zero statement along the tower.  That is what the
characteristic-`ℓ` Frobenius relation needs.

The two public headlines are their wrappers verbatim; the pin's `HPDfdPort`
helpers are transcribed `private`.  The pin's private `principalDivisorOf` is the
already-ported `RationalFunctionField.principalDivisorOf`
(`P1/DXCoeff.lean`), so it is not re-derived here.

Mathlib search negatives (recorded): there is no mathlib
`HasPrincipalDivisors`-shaped statement (the notion is FLT's), so the whole node
is transcription; `Field.exists_primitive_element`, the splitting-field Galois
machinery and `Algebra.norm_eq_prod_automorphisms` are the load-bearing mathlib
inputs. -/
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.P1.DXCoeff
import FLTForHuman.AlgebraicCurve.WeilExchange.FiberOverCount
import FLTForHuman.AlgebraicCurve.Defs.PlaceDictionary
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PrimitiveElement

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

open AlgebraicCurve Polynomial IntermediateField

namespace AlgebraicCurve

namespace HPDfdPort

section General

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

private theorem degree_eq_finrank_mul {g : F}
    {D' : Divisor K F'} (hD' : ∀ w : Place K F', D' w = w.ord (algebraMap F F' g))
    {D : Divisor K F} (hD : ∀ v : Place K F, D v = v.ord g) :
    Divisor.degree D' = (Module.finrank F F' : ℤ) * Divisor.degree D := by
  classical
  have hmaps : ∀ w ∈ D'.support, w.restrict F ∈ D.support := by
    intro w hw
    rw [Finsupp.mem_support_iff] at hw ⊢
    intro h0
    apply hw
    rw [hD' w, w.ord_restrict g, hD (w.restrict F)] at *
    rw [h0, mul_zero]
  have happ : ∀ w : Place K F', D' w = (w.ramificationIndex F : ℤ) * D (w.restrict F) := by
    intro w
    rw [hD' w, w.ord_restrict g, hD]
  rw [Divisor.degree_eq_sum, Divisor.degree_eq_sum,
    ← Finset.sum_fiberwise_of_maps_to hmaps fun w => D' w * (w.deg : ℤ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_

  have hfiber : D'.support.filter (fun w => w.restrict F = v) = v.fiberOver F' := by
    ext w
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, Place.mem_fiberOver,
      and_iff_right_iff_imp]
    intro hw
    rw [happ w, hw]
    have he : 0 < w.ramificationIndex F := w.ramificationIndex_pos (F := F)
    have hv0 : D v ≠ 0 := Finsupp.mem_support_iff.mp hv
    exact mul_ne_zero (by exact_mod_cast he.ne') hv0
  calc
    ∑ w ∈ D'.support with w.restrict F = v, D' w * (w.deg : ℤ)
        = D v * ∑ w ∈ v.fiberOver F',
            (w.ramificationIndex F : ℤ) * (w.deg : ℤ) := by
          rw [hfiber, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [happ w, (Place.mem_fiberOver v).mp hw]
          ring
    _ = D v * ((Module.finrank F F' : ℤ) * (v.deg : ℤ)) := by
          congr 1
          rw [← Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver (K := K) (F' := F') v]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun w hw => ?_
          have hwr := (Place.mem_fiberOver v).mp hw
          have hdeg := w.deg_restrict_mul_inertiaDeg (F := F)
          rw [hwr] at hdeg
          have hdegZ : (w.deg : ℤ) = (v.deg : ℤ) * (w.inertiaDeg F : ℤ) := by
            exact_mod_cast hdeg.symm
          rw [hdegZ]; ring
    _ = (Module.finrank F F' : ℤ) * (D v * (v.deg : ℤ)) := by ring

private theorem Place.ord_prod' {ι : Type*} (v : Place K F') (s : Finset ι)
    (g : ι → F') (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      v.ord_mul (hg i (Finset.mem_cons_self i s))
        (Finset.prod_ne_zero_iff.mpr fun j hj => hg j (Finset.mem_cons_of_mem hj)),
      ih fun j hj => hg j (Finset.mem_cons_of_mem hj)]

private theorem sum_smul_apply_eq_ord_prod {f : F'} (hf : f ≠ 0)
    {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) (w : Place K F') :
    (∑ σ : F' ≃ₐ[F] F', (AlgEquiv.restrictScalars K σ) • D) w
      = w.ord (∏ σ : F' ≃ₐ[F] F', σ f) := by
  classical
  rw [Place.ord_prod' w _ _ (fun σ _ => by simpa using hf), Finset.sum_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Divisor.smul_apply, hD]
  have h := Place.ord_smul (AlgEquiv.restrictScalars K σ)
    ((AlgEquiv.restrictScalars K σ)⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

private theorem degree_eq_zero_of_isGalois [IsGalois F F'] [HasPrincipalDivisors K F]
    {f : F'} {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) :
    Divisor.degree D = 0 := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · have : D = 0 := Finsupp.ext fun w => by simpa using hD w
    rw [this, map_zero]
  set D'' : Divisor K F' := ∑ σ : F' ≃ₐ[F] F', (AlgEquiv.restrictScalars K σ) • D with hE
  have hEord : ∀ w : Place K F', D'' w = w.ord (algebraMap F F' (Algebra.norm F f)) := by
    intro w
    rw [hE, sum_smul_apply_eq_ord_prod hf hD w, Algebra.norm_eq_prod_automorphisms F f]
  have hnorm : Algebra.norm F f ≠ 0 := (Algebra.norm_ne_zero_iff (R := F)).mpr hf
  obtain ⟨D₀, hD₀, hD₀deg⟩ := HasPrincipalDivisors.exists_divisor (K := K)
    (Algebra.norm F f) hnorm
  have hEdeg : Divisor.degree D'' = 0 := by
    rw [degree_eq_finrank_mul hEord hD₀, hD₀deg, mul_zero]
  have hEdeg' : Divisor.degree D'' = (Module.finrank F F' : ℤ) * Divisor.degree D := by
    rw [hE, map_sum]
    simp only [Divisor.degree_smul]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    exact_mod_cast (Nat.card_eq_fintype_card (α := F' ≃ₐ[F] F')).symm.trans
      (IsGalois.card_aut_eq_finrank F F')
  have hpos : (0 : ℤ) < (Module.finrank F F' : ℤ) := by
    exact_mod_cast Module.finrank_pos (R := F) (M := F')
  rw [hEdeg] at hEdeg'
  exact (mul_eq_zero.mp hEdeg'.symm).resolve_left hpos.ne'

private theorem degree_eq_zero_of_tower
    (htop : ∀ (h : F') (E : Divisor K F'), (∀ w : Place K F', E w = w.ord h) →
      Divisor.degree E = 0)
    (hex : ∀ h : F', h ≠ 0 → ∃ E : Divisor K F', ∀ w : Place K F', E w = w.ord h)
    {f : F} {D : Divisor K F} (hD : ∀ v : Place K F, D v = v.ord f) :
    Divisor.degree D = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · have : D = 0 := Finsupp.ext fun w => by simpa using hD w
    rw [this, map_zero]
  obtain ⟨E, hE⟩ := hex (algebraMap F F' f) (by simpa using hf)
  have hcomp : Divisor.degree E = (Module.finrank F F' : ℤ) * Divisor.degree D :=
    degree_eq_finrank_mul hE hD
  rw [htop _ E hE] at hcomp
  have hpos : (0 : ℤ) < (Module.finrank F F' : ℤ) := by
    exact_mod_cast Module.finrank_pos (R := F) (M := F')
  exact (mul_eq_zero.mp hcomp.symm).resolve_left hpos.ne'

end General

end HPDfdPort

open HPDfdPort in
/-- **Principal divisors for a finite separable `RatFunc K`-extension.**  Verbatim
from `Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.lean`. -/
theorem hasPrincipalDivisors_of_finiteDimensional_of_isSeparable {K : Type*} [Field K]
    (E : Type*) [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E] [Algebra.IsSeparable (RatFunc K) E] :
    HasPrincipalDivisors K E := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (RatFunc K) E
  have hint : IsIntegral (RatFunc K) α := Algebra.IsIntegral.isIntegral α
  have hsep : (minpoly (RatFunc K) α).Separable := Algebra.IsSeparable.isSeparable _ α
  obtain ⟨g⟩ : Nonempty (E →ₐ[RatFunc K] (minpoly (RatFunc K) α).SplittingField) := by
    refine IntermediateField.nonempty_algHom_of_adjoin_splits (fun s hs => ?_) hα
    obtain rfl : s = α := by simpa using hs
    exact ⟨hint, Polynomial.SplittingField.splits _⟩
  letI : Algebra E (minpoly (RatFunc K) α).SplittingField := g.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc K) E (minpoly (RatFunc K) α).SplittingField :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  haveI : IsScalarTower K E (minpoly (RatFunc K) α).SplittingField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show algebraMap K (minpoly (RatFunc K) α).SplittingField x = g (algebraMap K E x)
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) E x, g.commutes,
        ← IsScalarTower.algebraMap_apply K (RatFunc K)
          (minpoly (RatFunc K) α).SplittingField x]
  haveI : IsGalois (RatFunc K) (minpoly (RatFunc K) α).SplittingField :=
    IsGalois.of_separable_splitting_field hsep
  haveI : FiniteDimensional E (minpoly (RatFunc K) α).SplittingField :=
    FiniteDimensional.right (RatFunc K) E _
  haveI : Algebra.IsSeparable E (minpoly (RatFunc K) α).SplittingField :=
    Algebra.isSeparable_tower_top_of_isSeparable (RatFunc K) E _
  haveI : HasPrincipalDivisors K (RatFunc K) := RationalFunctionField.hasPrincipalDivisors K
  refine ⟨fun f hf => ⟨RationalFunctionField.principalDivisorOf hf, fun _ => rfl, ?_⟩⟩

  refine degree_eq_zero_of_tower (K := K) (F := E)
    (F' := (minpoly (RatFunc K) α).SplittingField)
    (fun h E' hE' => degree_eq_zero_of_isGalois (K := K) (F := RatFunc K)
      (F' := (minpoly (RatFunc K) α).SplittingField) hE')
    (fun h hh => ⟨RationalFunctionField.principalDivisorOf hh, fun _ => rfl⟩)
    (fun _ => rfl)

/-- **Principal divisors via a separating transcendental.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_transcendental_of_isSeparable.lean`. -/
theorem hasPrincipalDivisors_of_transcendental_of_isSeparable {K F : Type*} [Field K] [Field F]
    [Algebra K F] {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    HasPrincipalDivisors K F := by
  haveI := hfd; haveI := hsep
  let e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
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
  exact hasPrincipalDivisors_of_finiteDimensional_of_isSeparable F

end AlgebraicCurve

end
