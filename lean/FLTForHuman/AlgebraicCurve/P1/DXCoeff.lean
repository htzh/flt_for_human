/-
DXCoeff — part of the ℙ¹ residue core, split from
`Defs/P1ResidueCore.lean` (R1 of `topics/riemannRoch/PLAN-RECTIFY-DEFS.md`).
The original declaration order is preserved; import the preceding slice.
-/
import FLTForHuman.AlgebraicCurve.P1.UnitNormalForm

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing KaehlerDifferential
open scoped Polynomial
open scoped AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurve

open RationalFunctionField

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- Pin row #233. -/
def KaehlerRankOne : Prop :=
  Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

variable {K F}

namespace IsCurveOver

/-- Pin row #234. -/
theorem of_finiteResidue_of_kaehlerRankOne
    [HasPrincipalDivisors K F] [∀ v : Place K F, v.FiniteResidue]
    (hΩ : KaehlerRankOne K F) : IsCurveOver K F where
  finiteResidue v := Place.FiniteResidue.finite (v := v)
  kaehler_free_rank_one := hΩ

end IsCurveOver

namespace RationalFunctionField

variable (K : Type*) [Field K]

/-- Pin row #235. -/
theorem isCurveOver_of_kaehlerRankOne (hΩ : KaehlerRankOne K (RatFunc K)) :
    IsCurveOver K (RatFunc K) :=
  IsCurveOver.of_finiteResidue_of_kaehlerRankOne hΩ

end RationalFunctionField

section Identity

variable (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

/-- Pin row #236. -/
def RamificationInertiaIdentity : Prop :=
  ∀ (v : Place K F) (s : Finset (Place K F')), (∀ w : Place K F', w ∈ s ↔ w.restrict F = v) →
    ∑ w ∈ s, (w.ramificationIndex F : ℤ) * (w.deg : ℤ)
      = (Module.finrank F F' : ℤ) * (v.deg : ℤ)

variable {K F F'}

end Identity

namespace Divisor

section Pullback

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F']

-- Pin row #237 `Divisor.degree_eq_sum_support` is already provided by the
-- imported `FLTForHuman.AlgebraicCurve.Genus.Index` (`AlgebraicCurve.Divisor.
-- degree_eq_sum_support`, statement identical), so it is not restated here.

/-- Pin row #238. -/
theorem degree_eq_finrank_mul_of_forall_eq_ord_algebraMap
    (H : RamificationInertiaIdentity K F F') {g : F}
    {D' : Divisor K F'} (hD' : ∀ w : Place K F', D' w = w.ord (algebraMap F F' g))
    {D : Divisor K F} (hD : ∀ v : Place K F, D v = v.ord g) :
    degree D' = (Module.finrank F F' : ℤ) * degree D := by
  classical

  have hmaps : ∀ w ∈ D'.support, w.restrict F ∈ D.support := by
    intro w hw
    rw [Finsupp.mem_support_iff] at hw ⊢
    intro h0
    apply hw
    rw [hD' w, w.ord_restrict g, hD] at *
    rw [h0, mul_zero]

  have happ : ∀ w : Place K F', D' w = (w.ramificationIndex F : ℤ) * D (w.restrict F) := by
    intro w
    rw [hD' w, w.ord_restrict g, hD]

  rw [degree_eq_sum_support, degree_eq_sum_support,
    ← Finset.sum_fiberwise_of_maps_to hmaps fun w => D' w * (w.deg : ℤ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_

  have hfiber : ∀ w : Place K F',
      w ∈ D'.support.filter (fun w => w.restrict F = v) ↔ w.restrict F = v := by
    intro w
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, and_iff_right_iff_imp]
    intro hw
    rw [happ w, hw]
    have he : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    have hv0 : D v ≠ 0 := Finsupp.mem_support_iff.mp hv
    exact mul_ne_zero (by exact_mod_cast he.ne') hv0

  calc
    ∑ w ∈ D'.support with w.restrict F = v, D' w * (w.deg : ℤ)
        = D v * ∑ w ∈ D'.support.filter (fun w => w.restrict F = v),
            (w.ramificationIndex F : ℤ) * (w.deg : ℤ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [happ w, ((hfiber w).mp hw)]
          ring
    _ = D v * ((Module.finrank F F' : ℤ) * (v.deg : ℤ)) := by
          rw [H v _ hfiber]
    _ = (Module.finrank F F' : ℤ) * (D v * (v.deg : ℤ)) := by ring

end Pullback

section Galois

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']

/-- Pin row #239 (`private`). -/
private theorem _root_.AlgebraicCurve.Place.ord_prod {ι : Type*} (v : Place K F') (s : Finset ι)
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

variable [FiniteDimensional F F']

/-- Pin row #240. -/
theorem sum_smul_apply_eq_ord_prod {f : F'} (hf : f ≠ 0)
    {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) (w : Place K F') :
    (∑ σ : F' ≃ₐ[F] F', (AlgEquiv.restrictScalars K σ) • D) w
      = w.ord (∏ σ : F' ≃ₐ[F] F', σ f) := by
  classical
  rw [w.ord_prod _ _ fun σ _ => by simpa using hf, Finset.sum_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_

  rw [smul_apply, hD]
  have h := Place.ord_smul (AlgEquiv.restrictScalars K σ)
    ((AlgEquiv.restrictScalars K σ)⁻¹ • w) f
  rw [smul_inv_smul] at h
  exact h.symm

/-- Pin row #241. -/
theorem degree_eq_zero_of_isGalois [IsGalois F F'] [HasPrincipalDivisors K F]
    (H : RamificationInertiaIdentity K F F')
    {f : F'} {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) :
    degree D = 0 := by
  classical

  rcases eq_or_ne f 0 with rfl | hf
  · have : D = 0 := Finsupp.ext fun w => by simpa using hD w
    rw [this, _root_.map_zero]

  set E : Divisor K F' := ∑ σ : F' ≃ₐ[F] F', (AlgEquiv.restrictScalars K σ) • D with hE

  have hEord : ∀ w : Place K F', E w = w.ord (algebraMap F F' (Algebra.norm F f)) := by
    intro w
    rw [hE, sum_smul_apply_eq_ord_prod hf hD w, Algebra.norm_eq_prod_automorphisms F f]

  have hnorm : Algebra.norm F f ≠ 0 := (Algebra.norm_ne_zero_iff (R := F)).mpr hf
  obtain ⟨D₀, hD₀, hD₀deg⟩ := HasPrincipalDivisors.exists_divisor (K := K)
    (Algebra.norm F f) hnorm

  have hEdeg : degree E = 0 := by
    rw [degree_eq_finrank_mul_of_forall_eq_ord_algebraMap H hEord hD₀, hD₀deg, mul_zero]

  have hEdeg' : degree E = (Module.finrank F F' : ℤ) * degree D := by
    rw [hE, map_sum]
    simp only [degree_smul]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    exact_mod_cast (Nat.card_eq_fintype_card (α := F' ≃ₐ[F] F')).symm.trans
      (IsGalois.card_aut_eq_finrank F F')

  have hpos : (0 : ℤ) < (Module.finrank F F' : ℤ) := by
    exact_mod_cast Module.finrank_pos (R := F) (M := F')
  rw [hEdeg] at hEdeg'
  exact (mul_eq_zero.mp hEdeg'.symm).resolve_left hpos.ne'

end Galois

end Divisor

namespace RationalFunctionField

section Descent

variable {K : Type*} [Field K] {F' : Type*} [Field F'] [Algebra K F']
  [Algebra (RatFunc K) F'] [IsScalarTower K (RatFunc K) F']
  [FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable (RatFunc K) F']

/-- Pin row #242. -/
def principalDivisorOf {f : F'} (hf : f ≠ 0) : Divisor K F' :=
  ⟨(finite_setOf_ord_ne_zero_of_finiteDimensional hf).toFinset, fun w => w.ord f, fun w => by
    simp [Set.Finite.mem_toFinset]⟩

/-- Pin row #243. -/
theorem degree_eq_zero_of_forall_eq_ord_of_isGalois [IsGalois (RatFunc K) F']
    (H : RamificationInertiaIdentity K (RatFunc K) F')
    {f : F'} {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) :
    Divisor.degree D = 0 :=
  Divisor.degree_eq_zero_of_isGalois H hD

/-- Pin row #244. -/
theorem hasPrincipalDivisors_of_isGalois [IsGalois (RatFunc K) F']
    (H : RamificationInertiaIdentity K (RatFunc K) F') :
    HasPrincipalDivisors K F' where
  exists_divisor _ hf :=
    ⟨principalDivisorOf hf, fun _ => rfl,
      degree_eq_zero_of_forall_eq_ord_of_isGalois H fun _ => rfl⟩

end Descent

end RationalFunctionField

section SurjectivePlaceInfty

variable (K) [DecidableEq (RatFunc K)]

/-- Pin row #245. -/
theorem surjective_algebraMap_residueField_placeInfty :
    Function.Surjective (algebraMap K (p1PlaceInfty K).ResidueField) := by
  intro z
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (1 : (p1PlaceInfty K).ResidueField) one_ne_zero).mp
      (show Module.finrank K (p1PlaceInfty K).ResidueField = 1 from deg_placeInfty K) z
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

end SurjectivePlaceInfty

section NamedRow

variable (K F)
variable [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

/-- Pin row #246. -/
def CanonicalLocalResidueKDifferentialCoordIndep : Prop :=
  ∀ (v : Place K F) (π' : F), v.ord π' = 1 →
    ∀ (R : v.CanonicalLocalResidueDataK) (n : ℕ), 1 ≤ n →
      R.res (v.differentialCoeff (KaehlerDifferential.D K F π') * ((π') ^ (n + 1))⁻¹) = 0

end NamedRow

section XInvCoordinate

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

omit [DecidableEq (RatFunc K)]
  [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] in

/-- Pin row #247. -/
theorem ratFuncX_inv_pow_inv (m : ℕ) :
    (((RatFunc.X : RatFunc K)⁻¹) ^ m)⁻¹ = (RatFunc.X : RatFunc K) ^ m := by
  rw [inv_pow, inv_inv]

/-- Pin row #248. -/
theorem X_pow_mul_differentialCoeff_D_X_eq_neg (n : ℕ) :
    (RatFunc.X : RatFunc K) ^ n
        * (p1PlaceInfty K).differentialCoeff (KaehlerDifferential.D K (RatFunc K) RatFunc.X)
      = -((p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) (RatFunc.X : RatFunc K)⁻¹)
          * (((RatFunc.X : RatFunc K)⁻¹) ^ (n + 2))⁻¹) := by
  rw [ratFuncX_inv_pow_inv, differentialCoeff_placeInfty_D_X_eq K]
  ring

end XInvCoordinate

section Bridge

variable (K) [DecidableEq (RatFunc K)]
variable [∀ v : Place K (RatFunc K), v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]

/-- Pin row #249. -/
theorem canonicalLocalResidueDataK_res_X_pow_mul_D_X_of_coordIndep
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (R : (p1PlaceInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    R.res ((RatFunc.X : RatFunc K) ^ n
        * (p1PlaceInfty K).differentialCoeff
            (KaehlerDifferential.D K (RatFunc K) RatFunc.X)) = 0 := by
  rw [X_pow_mul_differentialCoeff_D_X_eq_neg K n, _root_.map_neg, neg_eq_zero]
  exact hcoord (p1PlaceInfty K) (RatFunc.X : RatFunc K)⁻¹ (ord_placeInfty_X_inv K) R (n + 1)
    (by omega)

/-- Pin row #250. -/
theorem canonicalLocalResidueDataK_kaehlerResidueTerm_X_pow_of_coordIndep
    (_hwd : OrdDifferentialWellDefined K (RatFunc K))
    (hcoord : CanonicalLocalResidueKDifferentialCoordIndep K (RatFunc K))
    (R : (p1PlaceInfty K).CanonicalLocalResidueDataK) (n : ℕ) :
    Algebra.trace K (p1PlaceInfty K).ResidueField
        (R.res (diagonalHom K (RatFunc K) ((RatFunc.X : RatFunc K) ^ n) (p1PlaceInfty K)
          * (p1PlaceInfty K).differentialCoeff
              (KaehlerDifferential.D K (RatFunc K) RatFunc.X))) = 0 := by
  rw [diagonalHom_apply,
    canonicalLocalResidueDataK_res_X_pow_mul_D_X_of_coordIndep K hcoord R n, _root_.map_zero]

end Bridge

end AlgebraicCurve

end

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false
