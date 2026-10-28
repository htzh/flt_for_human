/-
Galois ramification and inertia: the Galois action on places preserves
restriction, ramification index and inertia degree, after FLT's seven
`P2M/Sol/S_AlgebraicCurve_{Place,SemilinearAut}_*` files
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean>).

`Place.restrict_ofAlgAut_smul` is written once (the pin has a `private` copy of
the same proof inside the first node's file); `restrictSmulValuationSubringEquiv`,
`coe_restrictSmulValuationSubringEquiv_apply`, `ord_smul_eq` and
`intertwinesAlong_one_ofAlgAut` stay `private`. The public headlines are their
`Theorems/` wrappers verbatim (explicit binders, so they verify by last-name lookup).

The last two carry the action on divisors: `SemilinearAut.restrict_smul` records that
restriction of places is equivariant for a pair of intertwined semilinear
automorphisms `g`, `g'`, and `SemilinearAut.pushforward_smul` that `Divisor.pushforward`
is, so that pushing forward a transported divisor transports its pushforward.  They are
stated over the same tower as the ramification-index and inertia-degree laws, whose
proof of `inertiaDeg_smul` they consume.  The last headline,
`SemilinearAut.correspondence_smul`, combines the two along-laws: the correspondence
`ψ_* φ^*` commutes with the semilinear action, at a single intertwined pair.  SET 7 adds
the `Pic0`-level wrapper `SemilinearAut.pic0_correspondence_smul`, the class-level form of
the same law.

spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Place_restrict_ofAlgAut_smul.lean
spec-pin: Theorems/Thm_AlgebraicCurve_SemilinearAut_ramificationIndex_smul.lean
spec-pin: Theorems/Thm_AlgebraicCurve_SemilinearAut_inertiaDeg_smul.lean
spec-pin: Theorems/Thm_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.lean
spec-pin: Theorems/Thm_AlgebraicCurve_SemilinearAut_restrict_smul.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_SemilinearAut_restrict_smul.lean
spec-pin: Theorems/Thm_AlgebraicCurve_SemilinearAut_pushforward_smul.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_SemilinearAut_pushforward_smul.lean
spec-pin: Theorems/Thm_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul.lean
spec-pin: Theorems/Thm_AlgebraicCurve_SemilinearAut_correspondence_smul.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_SemilinearAut_correspondence_smul.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul.lean   -- comparable copy
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

/-- A place and its transport along an intertwined pair of semilinear automorphisms
restrict to places that are again transported into each other. -/
theorem restrict_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') :
    (g' • w).restrict F = g • (w.restrict F) := by
  apply Place.toValuationSubring_injective
  rw [Place.restrict_toValuationSubring, smul_toValuationSubring, smul_toValuationSubring,
    Place.restrict_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap,
    hgg'.inv x]

/-- `Divisor.pushforward` is equivariant for the semilinear action, along an
intertwined pair: pushing a transported divisor forward transports the pushforward. -/
theorem pushforward_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (D : Divisor K F') :
    Divisor.pushforward F (g' • D) = g • Divisor.pushforward F D := by
  induction D using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | single_add w n D _ _ ih =>
    rw [smul_add, map_add, map_add, smul_add, ih]
    congr 1
    rw [smul_single, Divisor.pushforward_single, Divisor.pushforward_single, smul_single,
      restrict_smul hgg' w, inertiaDeg_smul hgg' w]

/-- **The along-version of `pushforward_smul`**: along an integral `φ : F →ₐ[K] F'`,
`Divisor.pushforwardAlong` is equivariant for a pair of semilinear automorphisms
intertwined through `φ`. Statement from
`Theorems/Thm_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul.lean`; proof after the
pin's `S_` file — the along-instances turn it into the `F`-algebra form above. -/
theorem pushforwardAlong_smul {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hgg' : IntertwinesAlong φ.toRingHom g g') (D : Divisor K F') :
    Divisor.pushforwardAlong φ hφ (g' • D) = g • Divisor.pushforwardAlong φ hφ D := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact pushforward_smul hgg' D

/-- **The `ψ_* φ^*` correspondence commutes with the semilinear action**: for a pair of
maps `φ`, `ψ` and an intertwined pair of semilinear automorphisms `g`, `g'`, the
transported divisor has the transported correspondence.  Statement from
`Theorems/Thm_AlgebraicCurve_SemilinearAut_correspondence_smul.lean`; proof after the
pin's `S_` file — unfold the correspondence (`correspondence_apply` is `rfl`) and apply
the pullback and pushforward along-laws. -/
theorem correspondence_smul {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong ψ.toRingHom g g')
    (D : Divisor K F) :
    Divisor.correspondence φ ψ hφ hψ (g • D) = g • Divisor.correspondence φ ψ hφ hψ D := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    Divisor.pullbackAlong_smul hφ hφ hgφ, pushforwardAlong_smul ψ hψ hgψ]

/-- **The `Pic0` correspondence commutes with the semilinear action.**  The `Pic0`-level
wrapper of `correspondence_smul`: both sides are the class of the corresponding divisor,
and the divisor statement is the previous theorem.  Statement from
`Theorems/Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul.lean`; proof after the
pin's `S_` file. -/
theorem pic0_correspondence_smul {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin)
    (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong ψ.toRingHom g g')
    (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN (g • c)
      = g • Pic0.correspondence φ ψ hφ hψ hFI hfin hN c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [pic0_smul_mk, Pic0.correspondence_mk, Pic0.correspondence_mk, pic0_smul_mk]
  congr 1
  apply Subtype.ext
  rw [Pic0.coe_degZeroCorrespondence, coe_degZeroSMulHom, coe_degZeroSMulHom,
    Pic0.coe_degZeroCorrespondence]
  exact correspondence_smul φ ψ hφ hψ hgφ hgψ (D : Divisor K F)

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
