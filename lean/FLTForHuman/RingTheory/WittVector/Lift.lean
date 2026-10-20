/-
  A lift of the Witt vectors of a perfect field of characteristic `p` into an
  algebraically closed field of characteristic zero, with prescribed residue
  behaviour and a transcendental element:

      there are `L` algebraically closed of characteristic `0`, a valuation subring
      `A ≤ L`, `φ : W(k) →+* L` landing in `A`, `ι : k →+* residueField A`
      compatible with `φ ∘ teichmuller`, and `t ∈ A` in the maximal ideal that is
      transcendental over `φ (W(k))`.

  The port of the pin leaf `WittVector.exists_valuationSubring_lift_with_transcendental`
  (152 pin lines), together with the statement of its `Theorems/` wrapper.

  The mathematics: `W(k)` has characteristic zero, hence so do `W(k)⟦X⟧`, its
  fraction field and the algebraic closure `L` of that; the composite
  `ψ : W(k)⟦X⟧ → L` is injective and factors through a valuation subring `A` of
  `L` by `IsLocalRing.exists_factor_valuationRing`, and `t = ψ X` is transcendental
  over `φ (W(k))` because a polynomial relation would give
  `ψ (P ∘ C) = 0` and hence `P = 0` by injectivity; `t` is in the maximal ideal
  because its constant coefficient vanishes.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): mathlib has no such lift statement — `rg -n
  "valuationSubring_lift_with_transcendental"` and `rg -n
  "teichmuller.*transcendental"` over `Mathlib/` find nothing, and
  `IsLocalRing.exists_factor_valuationRing` is the general factorisation lemma,
  imported rather than restated, together with
  `WittVector.isUnit_of_coeff_zero_ne_zero`, `WittVector.coeff_p_one`,
  `WittVector.ker_constantCoeff`, `IsFractionRing.charZero`,
  `charZero_of_injective_algebraMap`, `Polynomial.hom_eval₂`,
  `Polynomial.coe_eq_zero_iff`.

  Heartbeats — the pin's own bumps, measured. The pin sets
  `set_option maxHeartbeats 12800000 in` and `set_option synthInstance.maxHeartbeats
  1600000 in` on the headline; both are dropped and the pin's price is paid in the
  measured result: **neither bump is needed in `v4.34.0`**. The file is green at
  `-DmaxHeartbeats=200000` (3 s) and also at a deliberately lowered
  `-DmaxHeartbeats=60000`, so no declaration here comes anywhere near the pin's
  12,800,000 — the pin's price belongs to its own `import Mathlib` prelude, not to
  this proof.

  Not carried: the pin's `p2m_export "WittLift" "charZero"` (a P2M.Util macro).

  spec-pin: Theorems/Thm_WittVector_exists_valuationSubring_lift_with_transcendental.lean
  spec-pin: P2M/Sol/S_WittVector_exists_valuationSubring_lift_with_transcendental.lean
-/
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.CharP.Algebra

set_option autoImplicit false

namespace WittVector

open WittVector IsLocalRing

section Witt
variable (p : ℕ) [hp : Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

omit [CharP k p] [PerfectRing k p] in
theorem coeff_zero_natCast (m : ℕ) : ((m : WittVector p k)).coeff 0 = (m : k) := by
  rw [← WittVector.constantCoeff_apply, map_natCast]

end Witt

end WittVector

private theorem WittVector.charZero (p : ℕ) [hp : Fact p.Prime] (k : Type*) [Field k] [CharP k p]
    [PerfectRing k p] : CharZero (WittVector p k) := by
  have : IsDomain (WittVector p k) := inferInstance
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.out.ne_one
  have hmunit : IsUnit ((m : ℕ) : WittVector p k) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [WittVector.coeff_zero_natCast]
    intro h0
    exact hm ((CharP.cast_eq_zero_iff k p m).mp h0)
  have hp0 : ((p : WittVector p k)) ≠ 0 := fun h => by
    have h1 := congrArg (fun x : WittVector p k => x.coeff 1) h
    simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at h1
    exact one_ne_zero h1
  have hpa : ((p ^ a : ℕ) : WittVector p k) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hp0
  rw [Nat.cast_mul] at hn
  exact hpa ((hmunit.mul_left_eq_zero).mp hn)

namespace WittVector

open WittVector IsLocalRing

section Witt
variable (p : ℕ) [hp : Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

omit [PerfectRing k p] in

theorem not_isUnit_p : ¬ IsUnit ((p : WittVector p k)) := by
  intro hu
  have h0 : WittVector.constantCoeff ((p : WittVector p k)) = (0 : k) := by
    rw [map_natCast, CharP.cast_eq_zero]
  have := hu.map (WittVector.constantCoeff : WittVector p k →+* k)
  rw [h0] at this
  exact not_isUnit_zero this

noncomputable def residueMap {A : Type*} [CommRing A] [IsLocalRing A] (f : WittVector p k →+* A) [IsLocalHom f] :
    k →+* ResidueField A :=
  (RingHom.liftOfRightInverse (WittVector.constantCoeff : WittVector p k →+* k) (WittVector.teichmuller p)
    (fun a => by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]))
    ⟨(residue A).comp f, by
      rw [WittVector.ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => not_isUnit_p p k (IsUnit.of_map f _ hu)⟩

theorem residueMap_constantCoeff {A : Type*} [CommRing A] [IsLocalRing A] (f : WittVector p k →+* A)
    [IsLocalHom f] (x : WittVector p k) :
    residueMap p k f (WittVector.constantCoeff x) = residue A (f x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem residueMap_comp_teichmuller {A : Type*} [CommRing A] [IsLocalRing A] (f : WittVector p k →+* A)
    [IsLocalHom f] (a : k) :
    residueMap p k f a = residue A (f (WittVector.teichmuller p a)) := by
  conv_lhs => rw [show a = WittVector.constantCoeff (WittVector.teichmuller p a) by
    rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]]
  exact residueMap_constantCoeff p k f _

end Witt

theorem isLocalHom_powerSeriesC (R : Type*) [CommRing R] : IsLocalHom (PowerSeries.C (R := R)) := by
  refine ⟨fun a ha => ?_⟩
  rwa [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C] at ha

theorem powerSeriesC_injective (R : Type*) [CommRing R] : Function.Injective (PowerSeries.C (R := R)) :=
  Function.LeftInverse.injective (g := PowerSeries.constantCoeff) fun a => PowerSeries.constantCoeff_C a

theorem eval₂_C_X_powerSeries {R : Type*} [CommRing R] (P : Polynomial R) :
    P.eval₂ (PowerSeries.C (R := R)) PowerSeries.X = (P : PowerSeries R) := by
  have h : Polynomial.eval₂RingHom (PowerSeries.C (R := R)) PowerSeries.X =
      Polynomial.coeToPowerSeries.ringHom := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact (Polynomial.coe_C a).symm
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      exact Polynomial.coe_X.symm
  exact congrArg (fun φ : Polynomial R →+* PowerSeries R => φ P) h

end WittVector

universe u

theorem WittVector.exists_valuationSubring_lift_with_transcendental
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p] [PerfectRing K p] :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L)
      (A : ValuationSubring L) (φ : WittVector p K →+* L) (hφ : ∀ x, φ x ∈ A)
      (ι : K →+* IsLocalRing.ResidueField A),
      (∀ a : K, IsLocalRing.residue A ⟨φ (WittVector.teichmuller p a), hφ _⟩ = ι a) ∧
      ∃ (t : L) (ht : t ∈ A), (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧
        ∀ P : Polynomial (WittVector p K), P ≠ 0 → P.eval₂ φ t ≠ 0 := by
  classical
  have hW0 : CharZero (WittVector p K) := WittVector.charZero p K
  have hR'0 : CharZero (PowerSeries (WittVector p K)) :=
    charZero_of_injective_ringHom (f := PowerSeries.C (R := WittVector p K))
      (WittVector.powerSeriesC_injective _)
  have : CharZero (FractionRing (PowerSeries (WittVector p K))) :=
    IsFractionRing.charZero (PowerSeries (WittVector p K))
  have hL : CharZero (AlgebraicClosure (FractionRing (PowerSeries (WittVector p K)))) :=
    charZero_of_injective_algebraMap
      (algebraMap (FractionRing (PowerSeries (WittVector p K))) _).injective

  let ψ : PowerSeries (WittVector p K) →+* AlgebraicClosure (FractionRing (PowerSeries (WittVector p K))) :=
    (algebraMap (FractionRing (PowerSeries (WittVector p K))) _).comp
      (algebraMap (PowerSeries (WittVector p K)) (FractionRing (PowerSeries (WittVector p K))))
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing (PowerSeries (WittVector p K))) _).injective.comp
      (IsFractionRing.injective (PowerSeries (WittVector p K)) _)

  obtain ⟨A, hAmem, hAloc⟩ := IsLocalRing.exists_factor_valuationRing ψ
  let g : PowerSeries (WittVector p K) →+* A := ψ.codRestrict A.toSubring hAmem
  have : IsLocalHom g := hAloc
  have := WittVector.isLocalHom_powerSeriesC (WittVector p K)
  let f : WittVector p K →+* A := g.comp (PowerSeries.C (R := WittVector p K))
  have : IsLocalHom f := RingHom.isLocalHom_comp g _
  let φ : WittVector p K →+* AlgebraicClosure (FractionRing (PowerSeries (WittVector p K))) :=
    ψ.comp (PowerSeries.C (R := WittVector p K))
  have hφ : ∀ x, φ x ∈ A := fun x => hAmem _
  refine ⟨AlgebraicClosure (FractionRing (PowerSeries (WittVector p K))), inferInstance, inferInstance, hL,
    A, φ, hφ, WittVector.residueMap p K f, fun a => ?_, ψ PowerSeries.X, hAmem _, ?_, ?_⟩
  ·
    exact (WittVector.residueMap_comp_teichmuller p K f a).symm
  ·
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hX : IsUnit (PowerSeries.X : PowerSeries (WittVector p K)) := IsUnit.of_map g _ hu
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X] at hX
    exact not_isUnit_zero hX
  ·
    intro P hP h0
    apply hP
    rw [show P.eval₂ φ (ψ PowerSeries.X) = ψ (P.eval₂ (PowerSeries.C (R := WittVector p K)) PowerSeries.X)
      from (Polynomial.hom_eval₂ P _ ψ PowerSeries.X).symm, WittVector.eval₂_C_X_powerSeries] at h0
    exact Polynomial.coe_eq_zero_iff.mp (hψ (by rw [h0, map_zero]))
