/-
Galois ramification and inertia: the Galois action on places preserves
restriction, ramification index and inertia degree, after FLT's seven
`P2M/Sol/S_AlgebraicCurve_{Place,SemilinearAut}_*` files
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean>).

`Place.restrict_ofAlgAut_smul` is written once (the pin has a `private` copy of
the same proof inside the first node's file); `restrictSmulValuationSubringEquiv`,
`coe_restrictSmulValuationSubringEquiv_apply`, `ord_smul_eq` and
`intertwinesAlong_one_ofAlgAut` stay `private` (`TOPIC-t3-galois-ramification.md` §1).
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceDictionary
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.IsGaloisGroup.Basic
import Mathlib.FieldTheory.Galois.Basic

set_option autoImplicit false

set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

open scoped Pointwise

namespace AlgebraicCurve

namespace Place

private theorem ord_smul_eq {K F' : Type*} [Field K] [Field F'] [Algebra K F']
    (g : SemilinearAut K F') (W : Place K F') (y : F') :
    (g • W).ord y = W.ord (g⁻¹ • y) := by
  conv_lhs => rw [← smul_inv_smul g y]
  exact SemilinearAut.ord_smul g W (g⁻¹ • y)

theorem restrict_ofAlgAut_smul {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [Algebra.IsIntegral F' M] (σ : M ≃ₐ[F'] M) (W : Place K M) :
    (SemilinearAut.ofAlgAut (σ.restrictScalars K) • W).restrict F' = W.restrict F' := by
  refine Place.ext ?_
  ext x
  rw [restrict_toValuationSubring, restrict_toValuationSubring, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  have : ((σ.restrictScalars K : M ≃+* M).symm (algebraMap F' M x)) = algebraMap F' M x := by
    rw [RingEquiv.symm_apply_eq]
    exact (σ.commutes x).symm
  rw [this]

theorem exists_algEquiv_smul_eq_of_restrict_eq {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    ∃ σ : M ≃ₐ[F'] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W = W' := by
  set w : Place K F' := W.restrict F'
  have hW : W.restrict F' = w := rfl
  letI := IsIntegralClosure.MulSemiringAction w.toValuationSubring F' M (integralClosureAt M w)
  haveI : IsGaloisGroup Gal(M/F') w.toValuationSubring (integralClosureAt M w) :=
    IsGaloisGroup.of_isFractionRing Gal(M/F') w.toValuationSubring (integralClosureAt M w) F' M
  haveI hp : (fiberCenter M w hW).asIdeal.IsPrime := (fiberCenter M w hW).isPrime
  haveI hp' : (fiberCenter M w h).asIdeal.IsPrime := (fiberCenter M w h).isPrime
  haveI := fiberCenter_liesOver (F' := M) hW
  haveI := fiberCenter_liesOver (F' := M) h
  obtain ⟨σ, hσ'⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (IsLocalRing.maximalIdeal w.toValuationSubring) (fiberCenter M w hW).asIdeal
    (fiberCenter M w h).asIdeal Gal(M/F')
  refine ⟨σ, eq_of_fiberCenter_eq (restrict_ofAlgAut_smul σ W) h ?_⟩
  refine HeightOneSpectrum.ext (Ideal.ext fun c => ?_)
  rw [← hσ', Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  by_cases hc : c = 0
  · simp [hc]
  have hc' : σ⁻¹ • c ≠ 0 := fun h0 => hc (by simpa using congrArg (σ • ·) h0)
  rw [mem_fiberCenter_iff_ord_pos _ hc, mem_fiberCenter_iff_ord_pos _ hc', ord_smul_eq,
    SemilinearAut.inv_smul_def, SemilinearAut.toRingAut_ofAlgAut]
  have key : algebraMap (integralClosureAt M w) M (σ⁻¹ • c)
      = ((σ.restrictScalars K : M ≃+* M)).symm (algebraMap (integralClosureAt M w) M c) := by
    rw [show σ⁻¹ • c = galRestrict w.toValuationSubring F' M (integralClosureAt M w) σ⁻¹ c
      from rfl, algebraMap_galRestrict_apply, AlgEquiv.aut_inv]
    rfl
  rw [key]

private theorem intertwinesAlong_one_ofAlgAut {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M] (σ : M ≃ₐ[F'] M) :
    SemilinearAut.IntertwinesAlong (algebraMap F' M) (1 : SemilinearAut K F')
      (SemilinearAut.ofAlgAut (σ.restrictScalars K)) := by
  intro x
  rw [one_smul, SemilinearAut.ofAlgAut_smul]
  exact σ.commutes x

end Place

namespace SemilinearAut

theorem ord_algebraMap_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') (f : F) :
    (g' • w).ord (algebraMap F F' f) = w.ord (algebraMap F F' (g⁻¹ • f)) := by
  have hrw : algebraMap F F' f = g' • (algebraMap F F' (g⁻¹ • f)) := by
    rw [hgg' (g⁻¹ • f), smul_inv_smul]
  rw [hrw]
  exact ord_smul g' w _

theorem ramificationIndex_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') :
    (g' • w).ramificationIndex F = w.ramificationIndex F := by
  unfold Place.ramificationIndex
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hford⟩
    exact ⟨g⁻¹ • f, by rwa [ne_eq, smul_eq_zero_iff_eq], by rw [← ord_algebraMap_smul hgg', hford]⟩
  · rintro ⟨f, hf, hford⟩
    refine ⟨g • f, by rwa [ne_eq, smul_eq_zero_iff_eq], ?_⟩
    rw [ord_algebraMap_smul hgg', inv_smul_smul, hford]

private def restrictSmulValuationSubringEquiv {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') :
    (w.restrict F).toValuationSubring ≃+* ((g' • w).restrict F).toValuationSubring where
  toFun x := ⟨g • (x : F), by
    show algebraMap F F' (g • (x : F)) ∈ (g' • w).toValuationSubring
    rw [← hgg' (x : F), smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g' _ _ x.2⟩
  invFun y := ⟨g⁻¹ • (y : F), by
    show algebraMap F F' (g⁻¹ • (y : F)) ∈ w.toValuationSubring
    rw [← hgg'.inv (y : F)]
    have hy : algebraMap F F' (y : F) ∈ (g' • w).toValuationSubring := y.2
    rw [smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hy
    exact hy⟩
  left_inv x := by ext; exact inv_smul_smul g (x : F)
  right_inv y := by ext; exact smul_inv_smul g (y : F)
  map_mul' x y := by ext; exact smul_mul' g (x : F) (y : F)
  map_add' x y := by ext; exact smul_add g (x : F) (y : F)

@[scoped simp]
private theorem coe_restrictSmulValuationSubringEquiv_apply {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F')
    (x : (w.restrict F).toValuationSubring) :
    ((restrictSmulValuationSubringEquiv hgg' w x :
      ((g' • w).restrict F).toValuationSubring) : F) = g • (x : F) :=
  rfl

theorem inertiaDeg_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') :
    (g' • w).inertiaDeg F = w.inertiaDeg F := by
  refine (Algebra.finrank_eq_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (restrictSmulValuationSubringEquiv hgg' w))
    (smulResidueRingEquiv g' w) ?_).symm
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show (Place.restrictResidueMap F (g' • w))
        (IsLocalRing.ResidueField.map _ (IsLocalRing.residue _ a))
      = (smulResidueRingEquiv g' w) ((Place.restrictResidueMap F w) (IsLocalRing.residue _ a))
  rw [IsLocalRing.ResidueField.map_residue, Place.restrictResidueMap_residue,
    Place.restrictResidueMap_residue, smulResidueRingEquiv,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  refine congrArg _ (Subtype.ext ?_)
  show algebraMap F F' (g • (a : F)) = g' • (algebraMap F F' (a : F))
  exact (hgg' (a : F)).symm

end SemilinearAut

namespace Place

theorem ramificationIndex_eq_of_restrict_eq {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    W'.ramificationIndex F' = W.ramificationIndex F' := by
  obtain ⟨σ, rfl⟩ := exists_algEquiv_smul_eq_of_restrict_eq W W' h
  exact SemilinearAut.ramificationIndex_smul (intertwinesAlong_one_ofAlgAut σ) W

theorem inertiaDeg_eq_of_restrict_eq {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    W'.inertiaDeg F' = W.inertiaDeg F' := by
  obtain ⟨σ, rfl⟩ := exists_algEquiv_smul_eq_of_restrict_eq W W' h
  exact SemilinearAut.inertiaDeg_smul (intertwinesAlong_one_ofAlgAut σ) W

end Place

end AlgebraicCurve
