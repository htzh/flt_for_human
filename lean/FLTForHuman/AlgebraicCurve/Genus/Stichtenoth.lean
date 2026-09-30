/-
The Stichtenoth genus-existence tower, after FLT's
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean`
(2,545 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists.lean>).

Statements are transcribed textually.  The two public targets
(`RationalFunctionField.stichtenothGenusExists`,
`RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase`) are spelled
from their `Theorems/Thm_AlgebraicCurve_RationalFunctionField_*` wrappers; the remaining
declarations come from the `S_` file in its own declaration order.  The pin's `_port`
duplicates are collapsed, and the adelic-index/`ell` prelude already landed in
`Genus/Index.lean` is imported rather than re-stated.  The pin's own `import Mathlib`
and `Definitions/` imports are replaced by the port's `Defs` modules plus specific
mathlib modules.
-/
import FLTForHuman.AlgebraicCurve.Defs.PoleDivisorPackage
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.RatFuncPlaces
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.WeilExchange.Bifibre
import FLTForHuman.AlgebraicCurve.WeilExchange.FiberOverCount
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.RatFuncDegree
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false

set_option linter.style.haveILetI false

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem indexOfSpecialty_sub_of_ge [IsCurveOver K F] [Nonempty (Place K F)]
    {D₀ D : Divisor K F} (hD : D₀ ≤ D)
    [FiniteDimensional K (LSpace D)]
    [hfin : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D₀)] :
    Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) ∧
      (Divisor.degree D - ell D) - (Divisor.degree D₀ - ell D₀)
        = (indexOfSpecialty D₀ : ℤ) - (indexOfSpecialty D : ℤ) := by

  have hABsub : adeleBdd D₀ ⊔ globalSub K F ≤ adeleBdd D ⊔ globalSub K F :=
    sup_le_sup_right (adeleBdd_mono hD) _
  have hBCsub : adeleBdd D ⊔ globalSub K F ≤ adeleSpace K F :=
    adeleBdd_sup_globalSub_le_adeleSpace _

  obtain ⟨hfinBA, hdimBA⟩ := finrank_adeleBddSup_quotient (K := K) hD
  haveI := hfinBA

  haveI hfinCA : Module.Finite K (adeleSpace K F ⧸
      (adeleBdd D₀ ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [← adeleBddPrincipal_eq_comap]; exact hfin

  obtain ⟨hfinCB, hdimCB⟩ := Submodule.finrank_quotient_chain'
    (A := adeleBdd D₀ ⊔ globalSub K F) (B := adeleBdd D ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub

  have hi0 : indexOfSpecialty D₀
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D₀ ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]
  have hiD : indexOfSpecialty D
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]

  haveI := hfinCB
  obtain ⟨_, hdimCA⟩ := Submodule.finrank_quotient_chain
    (A := adeleBdd D₀ ⊔ globalSub K F) (B := adeleBdd D ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub
  refine ⟨?_, ?_⟩
  · rw [show adeleBddPrincipal K F D
        = (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype
      from adeleBddPrincipal_eq_comap D]
    exact hfinCB
  ·
    have hcast : (indexOfSpecialty D₀ : ℤ)
        = (indexOfSpecialty D : ℤ)
          + (finrank K (↥(adeleBdd D ⊔ globalSub K F)
              ⧸ (adeleBdd D₀ ⊔ globalSub K F).comap
                (adeleBdd D ⊔ globalSub K F).subtype) : ℤ) := by
      rw [hiD, hi0]; exact_mod_cast hdimCA
    linarith [hdimBA, hcast]

theorem degreeSub_ell_le_of_indexFinite [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {D₀ : Divisor K F}
    (hfin : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D₀))
    (D : Divisor K F) :
    Divisor.degree D - ell D ≤ (Divisor.degree D₀ - ell D₀) + indexOfSpecialty D₀ := by

  haveI := hfin
  haveI := finiteDimensional_lSpace (K := K) (D ⊔ D₀)
  have hmono : Divisor.degree D - (ell D : ℤ)
      ≤ Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) := by
    have h := ell_sub_ell_le_degree_sub_degree (K := K) (le_sup_left : D ≤ D ⊔ D₀)
    linarith

  obtain ⟨_, heq⟩ :=
    indexOfSpecialty_sub_of_ge (K := K) (le_sup_right : D₀ ≤ D ⊔ D₀)
  have hi0 : (0 : ℤ) ≤ indexOfSpecialty (D ⊔ D₀) := Int.natCast_nonneg _
  linarith

theorem riemannGenusBounded_of_indexFinite [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hfin : IndexOfSpecialtyFinite K F) :
    RiemannGenusBounded K F := by
  obtain ⟨D₀, hD₀⟩ := hfin
  exact ⟨(Divisor.degree D₀ - ell D₀) + indexOfSpecialty D₀,
    degreeSub_ell_le_of_indexFinite hD₀⟩

theorem stichtenothGenusExists_of_indexFinite
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hfin : IndexOfSpecialtyFinite K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_bounded (riemannGenusBounded_of_indexFinite hfin)

theorem indexOfSpecialtyFinite_of_stichtenothGenusExists
    [IsCurveOver K F] (hSG : StichtenothGenusExists K F) :
    IndexOfSpecialtyFinite K F := by
  obtain ⟨hne, hL0, γ, D₀, hD₀⟩ := hSG
  haveI := hne; haveI := hL0
  refine ⟨D₀, ?_⟩
  rw [show adeleBddPrincipal K F D₀
      = (adeleBdd D₀ ⊔ globalSub K F).comap (adeleSpace K F).subtype
    from adeleBddPrincipal_eq_comap D₀, ← adeleSpace_eq_of_genusReached hD₀,
    Submodule.comap_subtype_self]
  haveI : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.Finite.of_finite

theorem stichtenothGenusExists_iff_indexFinite
    [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))] :
    StichtenothGenusExists K F ↔ IndexOfSpecialtyFinite K F :=
  ⟨indexOfSpecialtyFinite_of_stichtenothGenusExists,
    stichtenothGenusExists_of_indexFinite⟩

theorem gate_indexOfSpecialty_engine_at_witness [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    (indexOfSpecialty D₀ : ℤ) = 0 := by
  exact_mod_cast indexOfSpecialty_eq_zero_of_genusReached h

theorem gate_stichtenothGenus_le_of_indexFinite [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {D₀ : Divisor K F}
    (hfin : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D₀))
    {γ : ℤ} {D₁ : Divisor K F} (h : RiemannGenusReachedAt γ D₁) :
    γ - 1 ≤ (Divisor.degree D₀ - ell D₀) + indexOfSpecialty D₀ := by
  have := degreeSub_ell_le_of_indexFinite hfin D₁
  rw [h.eq] at this; exact this

theorem gate_riemannGenusBounded_of_reachedAt
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    RiemannGenusBounded K F :=
  ⟨γ - 1, h.isMax⟩

theorem gate_indexOfSpecialtyFinite_at_zero [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F (0 : Divisor K F)) :=
  (indexOfSpecialty_eq_of_genusReached h 0).1

end AlgebraicCurve

end


noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem indexOfSpecialtyFinite_of_poleDivisorPackage [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_stichtenothGenusExists
    (stichtenothGenusExists_of_poleDivisorPackage P)

theorem indexOfSpecialtyFinite_of_hasPoleDivisorPackage [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (h : HasPoleDivisorPackage K F) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_poleDivisorPackage h.some

theorem stichtenothGenusExists_of_hasPoleDivisorPackage [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (h : HasPoleDivisorPackage K F) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_poleDivisorPackage h.some

theorem gate_stichtenothGenus_le_of_poleDivisorPackage [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F)
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    γ ≤ (P.n : ℤ) * (P.c - 1) + 1 := by
  have := P.degree_sub_ell_le D₀
  rw [h.eq] at this; linarith

theorem gate_ell_c_nsmul_ge [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (P : PoleDivisorPackage K F) :
    (P.n : ℤ) ≤ ell (P.c • P.B) := by
  have h := P.ell_nsmul_poleDivisor_ge (le_refl P.c)
  simp only [sub_self, zero_add, mul_one] at h
  exact h

theorem gate_x_transcendental_of_poleDivisorPackage (P : PoleDivisorPackage K F) :
    LinearIndependent K (fun j : ℕ => P.x ^ j * P.u ⟨0, P.hn_pos⟩) := by
  refine P.lin_indep.comp (fun j => (j, ⟨0, P.hn_pos⟩)) ?_
  intro a b hab
  exact (Prod.mk.injEq .. ▸ hab).1

theorem gate_u_linearIndependent_of_poleDivisorPackage (P : PoleDivisorPackage K F) :
    LinearIndependent K P.u := by
  have h : LinearIndependent K (fun i : Fin P.n => P.x ^ (0 : ℕ) * P.u i) := by
    refine P.lin_indep.comp (fun i => (0, i)) ?_
    intro a b hab
    exact (Prod.mk.injEq .. ▸ hab).2
  simpa using h

end AlgebraicCurve

end


set_option autoImplicit false

noncomputable section

open Module IsDedekindDomain WithZero

namespace AlgebraicCurve

/-- Infrastructure mirroring the pin's scoped `instSumRamificationInertia_port`
(`S_..._stichtenothGenusExists.lean:1784`): the port's fundamental-identity sum is
`Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver`, over `fiberOver`; the class
field sums over `fiber`.  `private`, so it stays outside the checked surface. -/
private instance instSumRamificationInertiaOfFiniteDimensional {K E F : Type*} [Field K]
    [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] :
    SumRamificationInertia K E F :=
  ⟨fun v => by
    have hfe : v.fiber F = v.fiberOver F := Finset.ext fun w => by
      rw [Place.mem_fiber, Place.mem_fiberOver]
    rw [hfe]
    exact Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver v⟩

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

namespace TranscendenceTower

variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
variable (T : TranscendenceTower K E F)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

private theorem x_ne_zero : T.x ≠ 0 := fun h => by
  have := T.hxv; rw [h, Place.ord_zero] at this; exact absurd this (by decide)

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in
theorem xF_ne_zero : T.xF ≠ 0 :=
  fun h => T.x_ne_zero ((algebraMap E F).injective (by rwa [map_zero]))

omit [FiniteDimensional E F] in

private theorem poleDivisor_apply (w : Place K F) :
    T.poleDivisor w = (w.ramificationIndex E : ℤ) * (Finsupp.single T.v 1) (w.restrict E) :=
  Divisor.pullback_apply (Finsupp.single T.v 1) w

omit [FiniteDimensional E F] in

private theorem poleDivisor_nonneg : 0 ≤ T.poleDivisor := by
  classical
  intro w
  rw [Finsupp.coe_zero, Pi.zero_apply, T.poleDivisor_apply, Finsupp.single_apply]
  refine mul_nonneg (Int.natCast_nonneg _) ?_
  split_ifs <;> simp

omit [FiniteDimensional E F] in

private theorem xF_mem_lSpace_poleDivisor : T.xF ∈ LSpace T.poleDivisor := by
  classical
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun w => ?_
  rw [T.poleDivisor_apply, Place.ord_restrict, Finsupp.single_apply]
  rcases eq_or_ne (w.restrict E) T.v with hw | hw
  · simp only [hw, T.hxv, ite_true, mul_one, mul_neg_one, le_refl]
  · simp only [if_neg (Ne.symm hw), mul_zero, neg_zero]
    exact mul_nonneg (Int.natCast_nonneg _) (T.hxreg _ hw)

private theorem degree_poleDivisor_eq_finrank :
    Divisor.degree T.poleDivisor = (Module.finrank E F : ℤ) := by
  rw [poleDivisor, Divisor.degree_pullback, Divisor.degree_single, T.hvdeg]
  push_cast; ring

omit [FiniteDimensional E F] in

private theorem mem_lSpace_nsmul_poleDivisor_of_regular_outside {f : F}
    (hreg : ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord f)
    {c : ℕ} (hc : ∀ w ∈ T.v.fiber F, -(c : ℤ) ≤ w.ord f) :
    f ∈ LSpace (c • T.poleDivisor) := by
  classical
  rcases eq_or_ne f 0 with rfl | hf0
  · exact (LSpace _).zero_mem
  rw [mem_lSpace_iff_ord]
  refine Or.inr fun w => ?_
  rw [Finsupp.smul_apply, T.poleDivisor_apply, Finsupp.single_apply, nsmul_eq_mul]
  rcases eq_or_ne (w.restrict E) T.v with hw | hw
  ·
    simp only [hw, ite_true, mul_one]
    have he : (1 : ℤ) ≤ w.ramificationIndex E := by
      exact_mod_cast w.ramificationIndex_pos (F := E)
    have hbdd := hc w (Place.mem_fiber.mpr hw)
    nlinarith [Int.natCast_nonneg c]
  ·
    simp only [if_neg (Ne.symm hw), mul_zero, neg_zero]
    exact hreg w hw

omit [FiniteDimensional E F] in

private theorem exists_forall_mem_lSpace_nsmul_poleDivisor {n : ℕ} (u : Fin n → F)
    (hreg : ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)) :
    ∃ c : ℕ, ∀ i, u i ∈ LSpace (c • T.poleDivisor) := by
  classical

  refine ⟨(Finset.univ : Finset (Fin n)).sup fun i =>
    (T.v.fiber F).sup fun w => (-(w.ord (u i))).toNat,
    fun i => T.mem_lSpace_nsmul_poleDivisor_of_regular_outside (hreg i) ?_⟩
  intro w hw

  have h1 : (-(w.ord (u i))).toNat
      ≤ (T.v.fiber F).sup fun w' => (-(w'.ord (u i))).toNat :=
    Finset.le_sup (f := fun w' => (-(w'.ord (u i))).toNat) hw
  have h2 : ((T.v.fiber F).sup fun w' => (-(w'.ord (u i))).toNat)
      ≤ (Finset.univ : Finset (Fin n)).sup fun i' =>
          (T.v.fiber F).sup fun w' => (-(w'.ord (u i'))).toNat :=
    Finset.le_sup (f := fun i' => (T.v.fiber F).sup fun w' => (-(w'.ord (u i'))).toNat)
      (Finset.mem_univ i)
  have htnat : -(w.ord (u i)) ≤ ((-(w.ord (u i))).toNat : ℤ) := Int.self_le_toNat _
  omega

end TranscendenceTower

variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

def IntegralBasisInLSpace.ofRegularOutside (T : TranscendenceTower K E F)
    (u : Fin (Module.finrank E F) → F) (hu_indep : LinearIndependent E u)
    (hreg : ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)) :
    IntegralBasisInLSpace T where
  c := (T.exists_forall_mem_lSpace_nsmul_poleDivisor u hreg).choose
  u := u
  hu_indep := hu_indep
  hu_mem := (T.exists_forall_mem_lSpace_nsmul_poleDivisor u hreg).choose_spec

omit [FiniteDimensional E F] in

theorem hasIntegralBasisInLSpace_of_regularOutside (T : TranscendenceTower K E F)
    (h : HasIntegralBasisRegularOutside K E F T) :
    HasIntegralBasisInLSpace K E F T := by
  obtain ⟨u, hu_indep, hreg⟩ := h
  exact ⟨IntegralBasisInLSpace.ofRegularOutside T u hu_indep hreg⟩

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

theorem linearIndependent_pow_mul {x : E} {n : ℕ} {u : Fin n → F}
    (hx : LinearIndependent K (fun j : ℕ => x ^ j)) (hu : LinearIndependent E u) :
    LinearIndependent K (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2) := by
  have heq : (fun p : ℕ × Fin n => (algebraMap E F x) ^ p.1 * u p.2)
      = (fun p : ℕ × Fin n => (x ^ p.1) • u p.2) := by
    funext p
    rw [Algebra.smul_def, map_pow]
  rw [heq]
  exact linearIndependent_smul (R := K) (S := E) (A := F) hx hu

def PoleDivisorPackage.ofTranscendenceTower (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    PoleDivisorPackage K F where
  x := T.xF
  B := T.poleDivisor
  hB_eff := T.poleDivisor_nonneg
  hx_mem := T.xF_mem_lSpace_poleDivisor
  n := Module.finrank E F
  hn_pos := Module.finrank_pos
  degB_eq := T.degree_poleDivisor_eq_finrank
  c := IB.c
  u := IB.u
  hu_mem := IB.hu_mem
  lin_indep := linearIndependent_pow_mul T.hx_indep IB.hu_indep

theorem hasPoleDivisorPackage_of_transcendenceTower
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    HasPoleDivisorPackage K F :=
  ⟨PoleDivisorPackage.ofTranscendenceTower T IB⟩

theorem hasPoleDivisorPackage_of_hasIntegralBasisInLSpace
    (T : TranscendenceTower K E F) (h : HasIntegralBasisInLSpace K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_transcendenceTower T h.some

theorem hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside
    (T : TranscendenceTower K E F) (h : HasIntegralBasisRegularOutside K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisInLSpace T
    (hasIntegralBasisInLSpace_of_regularOutside T h)

theorem indexOfSpecialtyFinite_of_transcendenceTower [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB)

theorem stichtenothGenusExists_of_transcendenceTower [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB)

theorem gate_ofTranscendenceTower_n_eq (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    (PoleDivisorPackage.ofTranscendenceTower T IB).n = Module.finrank E F := rfl

theorem gate_ofTranscendenceTower_B_eq (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    (PoleDivisorPackage.ofTranscendenceTower T IB).B = T.poleDivisor := rfl

theorem gate_ofTranscendenceTower_x_transcendental (T : TranscendenceTower K E F)
    (IB : IntegralBasisInLSpace T) :
    LinearIndependent K
      (fun j : ℕ => T.xF ^ j *
        (PoleDivisorPackage.ofTranscendenceTower T IB).u ⟨0, Module.finrank_pos⟩) :=
  gate_x_transcendental_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB)

theorem gate_degree_pullback_single_of_deg_eq (v : Place K E) (d : ℕ) (hd : v.deg = d) :
    Divisor.degree (Divisor.pullback F (Finsupp.single v (1 : ℤ)))
      = (Module.finrank E F : ℤ) * d := by
  rw [Divisor.degree_pullback, Divisor.degree_single, hd]; ring

theorem gate_stichtenothGenus_le_of_transcendenceTower [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (IB : IntegralBasisInLSpace T)
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    γ ≤ (Module.finrank E F : ℤ) * (IB.c - 1) + 1 :=
  gate_stichtenothGenus_le_of_poleDivisorPackage
    (PoleDivisorPackage.ofTranscendenceTower T IB) h

end AlgebraicCurve

end


set_option autoImplicit false

noncomputable section

open Module

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (w : Place K F)

private theorem mem_of_isIntegral {f : F} (hf : IsIntegral w.toValuationSubring f) :
    f ∈ w.toValuationSubring := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hf
  exact hy ▸ y.2

theorem ord_nonneg_of_isIntegral {f : F} (hf : IsIntegral w.toValuationSubring f) :
    0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral hf)

private theorem mem_of_isIntegral_of_algebraMap_mem {A : Type*} [CommRing A] [Algebra A F]
    (hA : ∀ a : A, algebraMap A F a ∈ w.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : f ∈ w.toValuationSubring := by

  letI : Algebra A w.toValuationSubring :=
    ((algebraMap A F).codRestrict w.toValuationSubring.toSubring hA).toAlgebra
  haveI : IsScalarTower A w.toValuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun a => rfl
  exact w.mem_of_isIntegral hf.tower_top

theorem ord_nonneg_of_isIntegral_of_algebraMap_mem {A : Type*} [CommRing A] [Algebra A F]
    (hA : ∀ a : A, algebraMap A F a ∈ w.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : 0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral_of_algebraMap_mem hA hf)

end Place

section Bridge

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable {A : Type*} [CommRing A] [Algebra A E] [Algebra A F] [IsScalarTower A E F]

namespace Place

private theorem mem_of_isIntegral_of_restrict [Algebra.IsIntegral E F] (w : Place K F)
    {u : Place K E} (hw : w.restrict E = u)
    (hA : ∀ a : A, algebraMap A E a ∈ u.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : f ∈ w.toValuationSubring := by

  refine w.mem_of_isIntegral_of_algebraMap_mem (fun a => ?_) hf
  rw [IsScalarTower.algebraMap_apply A E F, ← w.mem_restrict_iff, hw]
  exact hA a

end Place

namespace Place

private theorem ord_nonneg_of_isIntegral_of_restrict [Algebra.IsIntegral E F] (w : Place K F)
    {u : Place K E} (hw : w.restrict E = u)
    (hA : ∀ a : A, algebraMap A E a ∈ u.toValuationSubring)
    {f : F} (hf : IsIntegral A f) : 0 ≤ w.ord f :=
  w.ord_nonneg_of_mem (w.mem_of_isIntegral_of_restrict hw hA hf)

end Place

namespace TranscendenceTower

private theorem ord_nonneg_of_isIntegral_of_regularOutside
    [Algebra.IsIntegral E F] (T : TranscendenceTower K E F) (hA : T.RegularOutside A)
    {f : F} (hf : IsIntegral A f) :
    ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord f := fun w hw =>
  w.ord_nonneg_of_isIntegral_of_restrict rfl (hA _ hw) hf

end TranscendenceTower
end Bridge

section Headline

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] in

theorem linearIndependent_reindex_basis {s : Finset F} (b : Basis s E F) :
    LinearIndependent E (fun i : Fin (Module.finrank E F) =>
      b ((Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm i)) :=
  b.linearIndependent.comp _ (Equiv.injective _)

omit [HasPrincipalDivisors K F] in

theorem hasIntegralBasisRegularOutside_of_isFractionRing
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    HasIntegralBasisRegularOutside K E F T := by

  obtain ⟨s, b, hint⟩ := FiniteDimensional.exists_is_basis_integral A E F

  set e : Fin (Module.finrank E F) ≃ s :=
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm).symm
  refine ⟨fun i => b (e i), linearIndependent_reindex_basis b, fun i w hw => ?_⟩

  exact T.ord_nonneg_of_isIntegral_of_regularOutside hA (hint (e i)) w hw

omit [HasPrincipalDivisors K F] in

theorem hasIntegralBasisRegularOutside_of_hasRegularFractionSubring
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    HasIntegralBasisRegularOutside K E F T := by
  obtain ⟨A, hfrac, hreg⟩ := h

  haveI : IsFractionRing A E := hfrac
  exact hasIntegralBasisRegularOutside_of_isFractionRing (A := A) T
    (fun u hu a => hreg u hu (a : E) a.property)

theorem hasPoleDivisorPackage_of_isFractionRing
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside T
    (hasIntegralBasisRegularOutside_of_isFractionRing T hA)

theorem stichtenothGenusExists_of_isFractionRing [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra A E] [IsFractionRing A E]
    [Algebra A F] [IsScalarTower A E F]
    (T : TranscendenceTower K E F) (hA : T.RegularOutside A) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasPoleDivisorPackage
    (hasPoleDivisorPackage_of_isFractionRing T hA)

theorem hasPoleDivisorPackage_of_hasRegularFractionSubring
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasIntegralBasisRegularOutside T
    (hasIntegralBasisRegularOutside_of_hasRegularFractionSubring T h)

theorem stichtenothGenusExists_of_hasRegularFractionSubring [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F) (h : HasRegularFractionSubring K E F T) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasPoleDivisorPackage
    (hasPoleDivisorPackage_of_hasRegularFractionSubring T h)

namespace TranscendenceTower

omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

private theorem adjoin_x_regularOutside (T : TranscendenceTower K E F) :
    ∀ u : Place K E, u ≠ T.v →
      ∀ a ∈ Algebra.adjoin K {T.x}, a ∈ u.toValuationSubring := by
  intro u hu a ha

  let S : Subalgebra K E :=
    { u.toValuationSubring.toSubsemiring with
      algebraMap_mem' := u.algebraMap_mem' }
  suffices h : a ∈ S from h
  refine Algebra.adjoin_le ?_ ha
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  show T.x ∈ u.toValuationSubring
  exact u.mem_of_ord_nonneg T.x_ne_zero (T.hxreg u hu)

end TranscendenceTower
omit [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] in

theorem hasRegularFractionSubring_of_adjoin_x_isFractionRing
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    HasRegularFractionSubring K E F T :=
  ⟨Algebra.adjoin K {T.x}, hfrac, T.adjoin_x_regularOutside⟩

omit [HasPrincipalDivisors K F] in

theorem hasIntegralBasisRegularOutside_of_adjoin_x_isFractionRing
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    HasIntegralBasisRegularOutside K E F T :=
  hasIntegralBasisRegularOutside_of_hasRegularFractionSubring T
    (hasRegularFractionSubring_of_adjoin_x_isFractionRing T hfrac)

theorem stichtenothGenusExists_of_adjoin_x_isFractionRing [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (T : TranscendenceTower K E F)
    (hfrac : IsFractionRing (Algebra.adjoin K {T.x}) E) :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_hasRegularFractionSubring T
    (hasRegularFractionSubring_of_adjoin_x_isFractionRing T hfrac)

end Headline


section Gates

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem gate_mem_of_isIntegral_recovers_comap (w : Place K F) (E : Type*) [Field E]
    [Algebra E F] [Algebra.IsIntegral E F]
    (hE : ∀ a : E, algebraMap E F a ∈ w.toValuationSubring) (f : F) :
    f ∈ w.toValuationSubring := by
  letI : Algebra E w.toValuationSubring :=
    ((algebraMap E F).codRestrict w.toValuationSubring.toSubring hE).toAlgebra
  haveI : IsScalarTower E w.toValuationSubring F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact w.mem_of_isIntegral (Algebra.IsIntegral.isIntegral (R := E) f).tower_top

variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

theorem gate_bridge_recovers_hxreg [Algebra.IsIntegral E F]
    (T : TranscendenceTower K E F) (w : Place K F) (hw : w.restrict E ≠ T.v) :
    0 ≤ w.ord T.xF := by
  rw [TranscendenceTower.xF, Place.ord_restrict]
  exact mul_nonneg (Int.natCast_nonneg _) (T.hxreg _ hw)

theorem gate_regularOutside_mono (T : TranscendenceTower K E F) {A A' : Subalgebra K E}
    (hle : A ≤ A')
    (hA' : ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A', a ∈ u.toValuationSubring) :
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A, a ∈ u.toValuationSubring :=
  fun u hu a ha => hA' u hu a (hle ha)

theorem gate_bot_regularOutside (T : TranscendenceTower K E F) :
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ (⊥ : Subalgebra K E), a ∈ u.toValuationSubring := by
  intro u _ a ha
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp ha
  exact u.algebraMap_mem' c

theorem gate_adjoin_x_not_regular_at_v (T : TranscendenceTower K E F) :
    ¬ ∀ a ∈ Algebra.adjoin K {T.x}, a ∈ T.v.toValuationSubring := by
  intro h
  have hx := T.v.ord_nonneg_of_mem (h T.x (Algebra.subset_adjoin rfl))
  rw [T.hxv] at hx
  exact absurd hx (by decide)

end Gates


end AlgebraicCurve

end


set_option autoImplicit false

noncomputable section

open Module Polynomial

namespace AlgebraicCurve

section Transcendental

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem linearIndependent_pow_of_transcendental {x : A} (hx : Transcendental K x) :
    LinearIndependent K (fun j : ℕ => x ^ j) := by
  have hinj : Function.Injective (Polynomial.aeval x : K[X] →ₐ[K] A) :=
    transcendental_iff_injective.mp hx

  have hXj : LinearIndependent K (fun j : ℕ => (X : K[X]) ^ j) := by
    have hb := (Polynomial.basisMonomials K).linearIndependent
    simp only [Polynomial.coe_basisMonomials] at hb
    convert hb using 2 with j
    exact (Polynomial.monomial_one_right_eq_X_pow j).symm
  have heq : (fun j : ℕ => x ^ j)
      = (fun j : ℕ => (Polynomial.aeval x : K[X] →ₐ[K] A) (X ^ j)) := by
    funext j; simp
  rw [heq]
  exact hXj.map' (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot_of_injective hinj)

theorem transcendental_of_linearIndependent_pow {x : A}
    (hx : LinearIndependent K (fun j : ℕ => x ^ j)) :
    Transcendental K x := by
  rw [transcendental_iff]
  intro p hp
  rw [Polynomial.aeval_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at hp
  ext j
  rcases lt_or_ge j (p.natDegree + 1) with hj | hj
  · exact (Fintype.linearIndependent_iff.mp
      (hx.comp (Fin.val : Fin (p.natDegree + 1) → ℕ) Fin.val_injective))
      (fun i => p.coeff i) hp ⟨j, hj⟩
  · exact p.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hj)

end Transcendental

end AlgebraicCurve

end


set_option autoImplicit false

noncomputable section

open Module Polynomial IsDedekindDomain

namespace AlgebraicCurve

namespace RationalFunctionField

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

theorem ord_placeInfty_X : (placeInfty K).ord (RatFunc.X : RatFunc K) = -1 := by
  rw [ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum (placeInfty K)
        (fun w => placeInfty_ne_ofHeightOneSpectrum K w) RatFunc.X_ne_zero,
      RatFunc.intDegree_X]

theorem algebraMap_polynomial_mem_of_ne_placeInfty
    {u : Place K (RatFunc K)} (hu : u ≠ placeInfty K) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ u.toValuationSubring := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty u with ⟨w, hw⟩ | hw
  · subst hw; exact algebraMap_mem_ofHeightOneSpectrum K w q
  · exact absurd hw hu

theorem ord_X_nonneg_of_ne_placeInfty
    {u : Place K (RatFunc K)} (hu : u ≠ placeInfty K) :
    0 ≤ u.ord (RatFunc.X : RatFunc K) := by
  rw [← RatFunc.algebraMap_X]
  exact u.ord_nonneg_of_mem (algebraMap_polynomial_mem_of_ne_placeInfty K hu Polynomial.X)

variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]

def transcendenceTower : TranscendenceTower K (RatFunc K) F where
  x := RatFunc.X
  hx_indep := linearIndependent_pow_of_transcendental RatFunc.transcendental_X
  v := placeInfty K
  hvdeg := deg_eq_one_of_forall_ne_ofHeightOneSpectrum (placeInfty K)
    (fun w => placeInfty_ne_ofHeightOneSpectrum K w)
  hxv := ord_placeInfty_X K
  hxreg := fun _ hu => ord_X_nonneg_of_ne_placeInfty K hu

@[scoped simp]
theorem transcendenceTower_x : (transcendenceTower K F).x = RatFunc.X := rfl

@[scoped simp]
theorem transcendenceTower_v : (transcendenceTower K F).v = placeInfty K := rfl

omit [DecidableEq (RatFunc K)] in

theorem aeval_X_eq_algebraMap (q : K[X]) :
    (Polynomial.aeval (R := K) (RatFunc.X : RatFunc K)) q
      = algebraMap K[X] (RatFunc K) q := by
  have hext : (Polynomial.aeval (R := K) (RatFunc.X : RatFunc K))
      = IsScalarTower.toAlgHom K K[X] (RatFunc K) :=
    Polynomial.algHom_ext (by simp [RatFunc.algebraMap_X])
  rw [hext]; rfl

omit [DecidableEq (RatFunc K)] in

theorem algebraMap_polynomial_mem_adjoin_X (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ Algebra.adjoin K {(RatFunc.X : RatFunc K)} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨q, aeval_X_eq_algebraMap K q⟩

omit [DecidableEq (RatFunc K)] in

theorem isFractionRing_adjoin_X :
    IsFractionRing (Algebra.adjoin K {(RatFunc.X : RatFunc K)}) (RatFunc K) := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  refine ⟨⟨algebraMap K[X] (RatFunc K) z.num, algebraMap_polynomial_mem_adjoin_X K z.num⟩,
    ⟨algebraMap K[X] (RatFunc K) z.denom, algebraMap_polynomial_mem_adjoin_X K z.denom⟩, ?_⟩
  show z = algebraMap K[X] (RatFunc K) z.num / algebraMap K[X] (RatFunc K) z.denom
  exact z.num_div_denom.symm

theorem hasRegularFractionSubring :
    HasRegularFractionSubring K (RatFunc K) F (transcendenceTower K F) :=
  hasRegularFractionSubring_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

theorem hasIntegralBasisRegularOutside :
    HasIntegralBasisRegularOutside K (RatFunc K) F (transcendenceTower K F) :=
  hasIntegralBasisRegularOutside_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

variable [HasPrincipalDivisors K F]

theorem hasPoleDivisorPackage_of_ratFunc_tower :
    HasPoleDivisorPackage K F :=
  hasPoleDivisorPackage_of_hasRegularFractionSubring
    (transcendenceTower K F) (hasRegularFractionSubring K F)

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

theorem stichtenothGenusExists_of_ratFunc_tower :
    StichtenothGenusExists K F :=
  stichtenothGenusExists_of_adjoin_x_isFractionRing
    (transcendenceTower K F) (isFractionRing_adjoin_X K)

theorem indexOfSpecialtyFinite_of_ratFunc_tower :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_stichtenothGenusExists
    (stichtenothGenusExists_of_ratFunc_tower K F)

end RationalFunctionField

end AlgebraicCurve

end


set_option autoImplicit false

noncomputable section

open Module Polynomial IsDedekindDomain

namespace AlgebraicCurve

namespace RationalFunctionField

section LyingOver

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]

theorem nonempty_place_of_ratFunc_tower : Nonempty (Place K F) :=
  (Place.exists_restrict_eq (M := F) (placeInfty K)).nonempty

end LyingOver

theorem finiteDimensional_lSpace_zero_of_constantsAreBase (K : Type*) [Field K]
    (F : Type*) [Field F] [Algebra K F] (hC : ConstantsAreBase K F) :
    FiniteDimensional K (LSpace (0 : Divisor K F)) := by
  rw [show LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) from hC]
  exact LinearMap.finiteDimensional_range _

theorem stichtenothGenusExists (K : Type*) [Field K] [DecidableEq (RatFunc K)]
    (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] [IsCurveOver K F]
    (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F :=
  haveI := nonempty_place_of_ratFunc_tower K F
  haveI := finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  stichtenothGenusExists_of_ratFunc_tower K F

section Tail

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
  [IsScalarTower K (RatFunc K) F]
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
variable [IsCurveOver K F]

theorem indexOfSpecialtyFinite (hC : ConstantsAreBase K F) :
    IndexOfSpecialtyFinite K F :=
  indexOfSpecialtyFinite_of_stichtenothGenusExists (stichtenothGenusExists K F hC)

theorem riemannGenusBounded (hC : ConstantsAreBase K F) : RiemannGenusBounded K F :=
  haveI := nonempty_place_of_ratFunc_tower K F
  haveI := finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  riemannGenusBounded_of_poleDivisorPackage (hasPoleDivisorPackage_of_ratFunc_tower K F).some

end Tail

end RationalFunctionField

end AlgebraicCurve

end
