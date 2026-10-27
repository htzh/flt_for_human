/-
The valuation-subring ↔ place dictionary of a one-variable function field: FLT's
`AlgebraicCurve.Place.exists_of_valuationSubring` and
`AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom`, after the pin
`P2M/Sol/S_AlgebraicCurve_Place_exists_of_valuationSubring.lean` and
`P2M/Sol/S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom.lean`
(207 lines each) and their `Theorems/` statement wrappers.

Given a field `K`, a finite extension `F` of `K(x)` with `x : F` transcendental
over `K`, and a valuation subring `A ≤ F` containing the constants and not
everything, there is a place `v` of `F` over `K` whose valuation subring is `A`;
and the comap of a valuation subring along a ring hom with the same two
properties is again a place's valuation subring.

The pin carries the same ten-helper prelude verbatim in both `S_` files; it is
written once here, and the second headline is the pin's one-line application of
the first. The headline statements are the pin's `theorem solution`s (which the
`Theorems/` wrappers restate verbatim) and are spelled with the pin's qualified
names.

Deviations from the pin are API drift only (playbook §4): the pin's
`include`/`omit` section-variable scaffolding is replaced by explicit binders,
and the pin's `private scoped instance`s of `IsFractionRing` for the valuation
subring are supplied locally (`have`) where the proofs need them. No statement
changes.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_of_valuationSubring.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_exists_of_valuationSubring.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom.lean

spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_of_valuationSubring.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_of_valuationSubring.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom.lean   -- comparable copy
-/

import FLTForHuman.AlgebraicCurve.Defs.Place
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Algebra.CharP.IntermediateField

set_option autoImplicit false

noncomputable section

open IsDedekindDomain IsLocalRing

open scoped IntermediateField.algebraAdjoinAdjoin

namespace AlgebraicCurve.Place

/-! ## The private engine

The ten-helper prelude that the pin repeats verbatim in both `S_` files: the
Dedekind/valuation theory of `K[x] ⊆ F` and of the integral closure, the
domination of a given valuation subring by a height-one prime of that integral
closure, and the place so produced. -/

section Crux

/-- `K[x]` is a Dedekind domain for transcendental `x`. -/
private theorem isDedekindDomain_Kx {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x) :
    IsDedekindDomain (Algebra.adjoin K ({x} : Set F)) := by
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hrange : (Polynomial.aeval x : Polynomial K →ₐ[K] F).range
      = Algebra.adjoin K ({x} : Set F) :=
    (Algebra.adjoin_singleton_eq_range_aeval K x).symm
  let e : Polynomial K ≃ₐ[K] Algebra.adjoin K ({x} : Set F) :=
    (AlgEquiv.ofInjective _ hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  have : IsPrincipalIdealRing (Algebra.adjoin K ({x} : Set F)) :=
    IsPrincipalIdealRing.of_surjective (e : Polynomial K →+* _) e.surjective
  infer_instance

/-- The integral closure of `K[x]` in the finite extension `F` is a Dedekind domain. -/
private theorem isDedekindDomain_integralClosure {K F : Type*} [Field K] [Field F]
    [Algebra K F] [CharZero K] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    IsDedekindDomain (integralClosure (Algebra.adjoin K ({x} : Set F)) F) := by
  have := isDedekindDomain_Kx x hx
  have : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsSeparable.of_integral _ _
  exact integralClosure.isDedekindDomain (Algebra.adjoin K ({x} : Set F))
    (IntermediateField.adjoin K ({x} : Set F)) F

/-- `F` is the fraction field of the integral closure of `K[x]` in `F`. -/
private theorem isFractionRing_integralClosure {K F : Type*} [Field K] [Field F]
    [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    IsFractionRing (integralClosure (Algebra.adjoin K ({x} : Set F)) F) F :=
  integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin K ({x} : Set F))
    (IntermediateField.adjoin K ({x} : Set F)) F

/-- A valuation subring containing the constants and a transcendental element
contains `K[x]`. -/
private theorem Kx_le_A {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hxA : x ∈ A) :
    (Algebra.adjoin K ({x} : Set F)).toSubring ≤ A.toSubring := by
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem z hz => obtain rfl : z = x := hz; exact hxA
  | algebraMap a => exact hAK a
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

/-- The integral closure of `K[x]` in `F` lies in a valuation subring containing
the constants and a transcendental element. -/
private theorem integralClosure_Kx_le_A {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hxA : x ∈ A) :
    (integralClosure (Algebra.adjoin K ({x} : Set F)) F).toSubring ≤ A.toSubring := by
  intro y hy
  have hyI : IsIntegral (Algebra.adjoin K ({x} : Set F)) y := hy
  let : Algebra (Algebra.adjoin K ({x} : Set F)) A :=
    (Subring.inclusion (Kx_le_A x A hAK hxA)).toAlgebra
  have : IsScalarTower (Algebra.adjoin K ({x} : Set F)) A F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hyA : IsIntegral A y := hyI.tower_top
  have : IsFractionRing A.toSubring F := by rw [← A.integer_valuation]; infer_instance
  obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff (R := A.toSubring) F).mp inferInstance hyA
  exact hz ▸ z.2

/-- An element of the integral closure whose image in `A` is a unit of `A` has
inverse in `A`. -/
private theorem inv_mem_of_notMem_maximalIdeal {K F : Type*} [Field K] [Field F]
    [Algebra K F] (x : F) (A : ValuationSubring F)
    (hAK : ∀ a : K, algebraMap K F a ∈ A) (hxA : x ∈ A)
    {b : integralClosure (Algebra.adjoin K ({x} : Set F)) F}
    (hb : Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA) b
        ∉ IsLocalRing.maximalIdeal A) :
    ((b : F))⁻¹ ∈ A := by
  have hbA : (b : F) ∈ A := integralClosure_Kx_le_A x A hAK hxA b.2
  have hbU : IsUnit (⟨(b : F), hbA⟩ : A) := IsLocalRing.notMem_maximalIdeal.mp hb
  obtain ⟨u, hu⟩ := hbU
  have hcoe : (((u⁻¹ : Aˣ) : A) : F) * (b : F) = 1 := by
    have h1 : ((u⁻¹ : Aˣ) : A) * ⟨(b : F), hbA⟩ = 1 := by rw [← hu]; exact u.inv_mul
    have := congrArg (Subtype.val : A → F) h1; simpa using this
  exact (eq_inv_of_mul_eq_one_left hcoe) ▸ ((u⁻¹ : Aˣ) : A).2

/-- The maximal ideal of `A`, pulled back to the integral closure, is nonzero. -/
private theorem idealOfA_ne_bot {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤)
    (hxA : x ∈ A) :
    (IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA)) ≠ ⊥ := by
  have : IsFractionRing (integralClosure (Algebra.adjoin K ({x} : Set F)) F) F :=
    isFractionRing_integralClosure x
  intro hP
  apply hA
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, b, hb, hab⟩ :=
    IsFractionRing.div_surjective (A := integralClosure (Algebra.adjoin K ({x} : Set F)) F) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have haA : (a : F) ∈ A := integralClosure_Kx_le_A x A hAK hxA a.2
  have hbm : Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA) b
      ∉ IsLocalRing.maximalIdeal A := by
    intro hbm
    have hmem : b ∈ (IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA)) := hbm
    rw [hP, Ideal.mem_bot] at hmem
    exact hb0 hmem
  rw [← hab, div_eq_mul_inv]
  exact mul_mem haA (inv_mem_of_notMem_maximalIdeal x A hAK hxA hbm)

/-- The place of a height-one prime of the integral closure that cuts out the
maximal ideal of `A` is dominated by `A`. -/
private theorem place_of_idealOfA_le {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hxA : x ∈ A)
    (P : HeightOneSpectrum (integralClosure (Algebra.adjoin K ({x} : Set F)) F))
    [IsDedekindDomain (integralClosure (Algebra.adjoin K ({x} : Set F)) F)]
    [IsFractionRing (integralClosure (Algebra.adjoin K ({x} : Set F)) F) F]
    (hP : P.asIdeal = (IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA))) :
    (ofHeightOneSpectrum (K := K) (F := F) P).toValuationSubring ≤ A := by
  rw [ofHeightOneSpectrum_toValuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rintro y ⟨a, s, hs, rfl⟩
  have haA : (a : F) ∈ A := integralClosure_Kx_le_A x A hAK hxA a.2
  have hsm : Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA) s
      ∉ IsLocalRing.maximalIdeal A := by
    intro h
    exact hs (hP ▸ h : s ∈ P.asIdeal)
  exact mul_mem haA (inv_mem_of_notMem_maximalIdeal x A hAK hxA hsm)

/-- The valuation-subring ↔ place dictionary: a valuation subring containing the
constants of a one-variable function field is a place's valuation subring. -/
private theorem exists_place_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤)
    (hx : Transcendental K x) (hxA : x ∈ A) :
    ∃ v : Place K F, v.toValuationSubring = A := by
  have := isDedekindDomain_integralClosure x hx
  have : IsFractionRing (integralClosure (Algebra.adjoin K ({x} : Set F)) F) F :=
    isFractionRing_integralClosure x
  let P : HeightOneSpectrum (integralClosure (Algebra.adjoin K ({x} : Set F)) F) :=
    ⟨(IsLocalRing.maximalIdeal A).comap
        (Subring.inclusion (integralClosure_Kx_le_A x A hAK hxA)),
      inferInstance, idealOfA_ne_bot x A hAK hA hxA⟩
  let V : Place K F := ofHeightOneSpectrum P
  have hVA : V.toValuationSubring ≤ A := place_of_idealOfA_le x A hAK hxA P rfl
  exact ⟨V, ValuationSubring.eq_of_le_of_ne_top _ hVA hA⟩

end Crux

/-! ## The headlines -/

theorem exists_of_valuationSubring {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (A : ValuationSubring F) (hAK : ∀ a : K, algebraMap K F a ∈ A) (hA : A ≠ ⊤) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = A := by
  by_cases hx : Transcendental K x
  · rcases A.mem_or_inv_mem x with hxA | hxiA
    · exact exists_place_of_mem x A hAK hA hx hxA
    · have hx0 : x ≠ 0 := by
        rintro rfl; exact hx (isAlgebraic_zero (R := K))
      have hxinv : Transcendental K x⁻¹ := by
        rw [Transcendental, IsAlgebraic.inv_iff]; exact hx
      have hadj : IntermediateField.adjoin K ({x⁻¹} : Set F) =
          IntermediateField.adjoin K ({x} : Set F) := by
        refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
          (IntermediateField.adjoin_le_iff.mpr ?_)
        · intro z hz; rw [show z = x⁻¹ from hz]
          exact inv_mem (IntermediateField.mem_adjoin_simple_self K x)
        · intro z hz; rw [show z = x from hz]
          have h : x⁻¹⁻¹ ∈ IntermediateField.adjoin K ({x⁻¹} : Set F) :=
            inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
          rwa [inv_inv] at h
      have : FiniteDimensional (IntermediateField.adjoin K ({x⁻¹} : Set F)) F := by
        rw [hadj]; infer_instance
      exact exists_place_of_mem x⁻¹ A hAK hA hxinv hxiA
  · rw [Transcendental, not_not] at hx
    refine absurd ?_ hA
    rw [eq_top_iff]
    intro y _
    have : FiniteDimensional K (IntermediateField.adjoin K ({x} : Set F)) :=
      IntermediateField.adjoin.finiteDimensional hx.isIntegral
    have : FiniteDimensional K F :=
      FiniteDimensional.trans K (IntermediateField.adjoin K ({x} : Set F)) F
    have : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
    have hyI : IsIntegral K y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
    let : Algebra K A :=
      ((algebraMap K F).codRestrict A.toSubring hAK).toAlgebra
    have : IsScalarTower K A F := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hyA : IsIntegral A y := hyI.tower_top
    have : IsFractionRing A.toSubring F := by rw [← A.integer_valuation]; infer_instance
    obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff (R := A.toSubring) F).mp inferInstance hyA
    exact hz ▸ z.2

theorem exists_toValuationSubring_eq_comap_ringHom {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (φ : F →+* F')
    (w : ValuationSubring F') (hwK : ∀ a : K, φ (algebraMap K F a) ∈ w)
    (hwx : ∃ y : F, φ y ∉ w) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = w.comap φ := by
  refine exists_of_valuationSubring x (w.comap φ) (fun a => hwK a) ?_
  intro h
  obtain ⟨y, hy⟩ := hwx
  exact hy (h ▸ ValuationSubring.mem_top y : y ∈ w.comap φ)

end AlgebraicCurve.Place
