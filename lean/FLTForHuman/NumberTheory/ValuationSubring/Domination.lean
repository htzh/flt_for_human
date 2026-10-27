/-
The generic, `Place`-free valuation-subring core of the place-realisation
development: the domination- and value-theory shared by `ValuationSubring`,
`Subring`, `RingHom` and `Valuation` — the closure/integral-closure dictionary,
`exists_valuationSubring_dominating`, the `centreOver`/`valuationSubringAtPrime`
construction, `constants` and the residue/`CharP` block, `RingHom.imagePrime`, and
the adjoin helper `IntermediateField.adjoin_simple_inv_eq`.

No declaration here mentions a `Place`. The module was split out of
`FLTForHuman/AlgebraicCurve/Place/ValuationSubringCore.lean` (itself split from
`Place/IsPrimeOverValuationSubring.lean`); the `Place`-specific half now lives in
`FLTForHuman/AlgebraicCurve/Place/ValueDictionary.lean`, which imports this module.
See the reuse note `lean/topics/algebraicCurve/TOPIC-valuation-subring-core.md`.

This module is public but **tier 3** (unwired): it is built and importable, but it
is deliberately not listed in the statement checker's `PORT_FILES`; its surface is
recorded in `lean/spec/UNWIRED-PUBLIC.md`. Every declaration carries a `-- pin:`
comment naming its line in the pin original.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean
-/

import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Int.CharZero
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are kept literal, as in `Defs/PlacesOverDVR.lean`.
set_option linter.style.haveILetI false

open Polynomial
open IsLocalRing
open IsDedekindDomain
open IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

namespace ValuationSubring

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (A : ValuationSubring K)

-- pin: closureConstantsAdjoin_eq_range_aeval (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:34)
theorem closureConstantsAdjoin_eq_range_aeval (x : F) :
    Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {x}) =
      (aeval (R := A) x).toRingHom.range := by
  apply le_antisymm
  · rw [Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl)
    · refine ⟨C a, ?_⟩
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, RingHom.coe_comp,
        Function.comp_apply]
      rfl
    · exact ⟨X, by simp⟩
  · rintro y ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using Polynomial.induction_on with
    | C a =>
      rw [aeval_C]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    | add p q hp hq =>
      rw [map_add]
      exact Subring.add_mem _ hp hq
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      exact Subring.mul_mem _ h (Subring.subset_closure (Or.inr rfl))

-- pin: ValuationSubring.aeval_injective_of_transcendental (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:58)
theorem _root_.ValuationSubring.aeval_injective_of_transcendental {x : F} (hx : Transcendental K x) :
    Function.Injective (aeval (R := A) x) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hK : aeval x (p.map (algebraMap A K)) = 0 := by rwa [aeval_map_algebraMap]
  have hp' : p.map (algebraMap A K) = 0 :=
    (injective_iff_map_eq_zero _).mp (transcendental_iff_injective.mp hx) _ hK
  exact (Polynomial.map_injective (algebraMap A K) Subtype.val_injective)
    (by rw [hp', Polynomial.map_zero])


-- pin: ValuationSubring.aeval_mem_closure (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:70)
theorem _root_.ValuationSubring.aeval_mem_closure (x : F) (p : A[X]) :
    aeval x p ∈ Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {x}) := by
  rw [closureConstantsAdjoin_eq_range_aeval]
  exact ⟨p, rfl⟩


-- pin: ValuationSubring.polynomialEquivClosure (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:77)
noncomputable def _root_.ValuationSubring.polynomialEquivClosure {x : F} (hx : Transcendental K x) :
    A[X] ≃+* Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {x}) :=
  RingEquiv.ofBijective
    ((aeval (R := A) x).toRingHom.codRestrict _ (A.aeval_mem_closure x))
    ⟨fun p q h => A.aeval_injective_of_transcendental hx (Subtype.ext_iff.mp h),
      fun y => by
        obtain ⟨p, hp⟩ : (y : F) ∈ (aeval (R := A) x).toRingHom.range := by
          rw [← closureConstantsAdjoin_eq_range_aeval]
          exact y.2
        exact ⟨p, Subtype.ext hp⟩⟩

@[scoped simp]
-- pin: polynomialEquivClosure_apply (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:90)
theorem polynomialEquivClosure_apply {x : F} (hx : Transcendental K x) (p : A[X]) :
    (A.polynomialEquivClosure hx p : F) = aeval x p := rfl

-- pin: ValuationSubring.isIntegrallyClosed_closure (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:93)
theorem _root_.ValuationSubring.isIntegrallyClosed_closure {x : F} (hx : Transcendental K x) :
    IsIntegrallyClosed (Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {x})) :=
  IsIntegrallyClosed.of_equiv (A.polynomialEquivClosure hx)

end ValuationSubring

namespace Subring

variable {F : Type*} [Field F]

-- pin: isIntegral_iff_exists_monic_eval₂ (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:107)
theorem isIntegral_iff_exists_monic_eval₂ (S : Subring F) (b : F) :
    IsIntegral S b ↔ ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype b p = 0 :=
  Iff.rfl

-- pin: exists_ideal_le_comap_eq_of_isIntegral (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:111)
theorem exists_ideal_le_comap_eq_of_isIntegral {S B : Subring F} (hSB : S ≤ B)
    [IsIntegrallyClosed S] (hint : ∀ b : B, IsIntegral S (b : F))
    {p q : Ideal S} [p.IsPrime] [q.IsPrime] (hpq : p ≤ q)
    (Q : Ideal B) [Q.IsPrime] (hQ : Q.comap (Subring.inclusion hSB) = q) :
    ∃ P : Ideal B, P ≤ Q ∧ P.IsPrime ∧ P.comap (Subring.inclusion hSB) = p := by
  letI : Algebra S B := (Subring.inclusion hSB).toAlgebra
  have halg : ∀ s : S, algebraMap S B s = Subring.inclusion hSB s := fun _ => rfl
  haveI : FaithfulSMul S B := (faithfulSMul_iff_algebraMap_injective S B).mpr fun a b h => by
    rw [halg, halg] at h
    have h' : (a : F) = (b : F) := congrArg (fun y : B => (y : F)) h
    exact Subtype.ext h'
  haveI : Algebra.IsIntegral S B := ⟨fun b => by
    obtain ⟨f, hf, hfb⟩ := hint b
    refine ⟨f, hf, ?_⟩
    apply Subtype.val_injective
    change B.subtype (Polynomial.eval₂ (algebraMap S B) b f) = ((0 : B) : F)
    have hc : B.subtype.comp (algebraMap S B) = S.subtype := RingHom.ext fun _ => rfl
    rw [Polynomial.hom_eval₂, hc]
    exact hfb⟩
  haveI : Q.LiesOver q := ⟨by rw [Ideal.under_def, ← hQ]; rfl⟩
  obtain ⟨P, hPQ, hP, hPp⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q) Q hpq
  exact ⟨P, hPQ, hP, by rw [hPp.over, Ideal.under_def]; rfl⟩

end Subring

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)

-- pin: ValuationSubring.algebraMap_bijective_of_isIntegral_of_isAlgClosed (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:728)
theorem _root_.ValuationSubring.algebraMap_bijective_of_isIntegral_of_isAlgClosed [IsAlgClosed K]
    (R : Type*) [CommRing R] [IsDomain R] [Algebra A R] [FaithfulSMul A R]
    [Algebra.IsIntegral A R] : Function.Bijective (algebraMap A R) := by
  have hinj : Function.Injective (algebraMap A R) := FaithfulSMul.algebraMap_injective A R
  refine ⟨hinj, fun r => ?_⟩
  haveI : Algebra.IsAlgebraic A R := Algebra.IsIntegral.isAlgebraic

  let φ : R →ₐ[A] K := IsAlgClosed.lift

  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hker : RingHom.ker φ.toRingHom = ⊥ := by
      refine Ideal.eq_bot_of_under_eq_bot (R := A) ?_
      rw [eq_bot_iff]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker] at ha
      change φ (algebraMap A R a) = 0 at ha
      rw [AlgHom.commutes] at ha

      have h0 : (a : K) = 0 := ha
      have ha0 : a = 0 := by exact_mod_cast h0
      rw [ha0]
      exact Ideal.zero_mem _
    have hmem : x ∈ RingHom.ker φ.toRingHom := hx
    rw [hker] at hmem
    exact Ideal.mem_bot.mp hmem

  have hint : IsIntegral A (φ r) := (Algebra.IsIntegral.isIntegral (R := A) r).map φ
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, hφ ?_⟩
  rw [AlgHom.commutes, ha]


section Quotient

open Polynomial

variable {F : Type*} [Field F] [Algebra K F]

-- pin: ValuationSubring.constants (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:769)
abbrev _root_.ValuationSubring.constants : A →+* F := (algebraMap K F).comp A.subtype

variable {A}

-- pin: exists_sub_constants_mem (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:774)
theorem exists_sub_constants_mem [IsAlgClosed K] {x : F} {B : Subring F}
    (hconst : ∀ a : A, A.constants a ∈ B) (hxB : x ∈ B)
    (hint : ∀ b : B, IsIntegral (Subring.closure (Set.range (A.constants (F := F)) ∪ {x})) (b : F))
    (𝔭 : Ideal B) [𝔭.IsPrime]
    (hbot : ∀ a : A, (⟨A.constants a, hconst a⟩ : B) ∈ 𝔭 → a = 0)
    (a₀ : A) (hx : (⟨x, hxB⟩ : B) - ⟨A.constants a₀, hconst a₀⟩ ∈ 𝔭) (b : B) :
    ∃ a : A, b - ⟨A.constants a, hconst a⟩ ∈ 𝔭 := by
  classical

  set S : Subring F := Subring.closure (Set.range (A.constants (F := F)) ∪ {x}) with hS
  have hSB : S ≤ B := by
    rw [hS, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl)
    exacts [hconst a, hxB]

  let cB : A →+* B := (A.constants (F := F)).codRestrict B hconst
  letI alg : Algebra A (B ⧸ 𝔭) := ((Ideal.Quotient.mk 𝔭).comp cB).toAlgebra
  have halg : ∀ a : A, algebraMap A (B ⧸ 𝔭) a = Ideal.Quotient.mk 𝔭 (cB a) := fun _ => rfl

  let ψ : S →+* B ⧸ 𝔭 := (Ideal.Quotient.mk 𝔭).comp (Subring.inclusion hSB)
  have step1 : ∀ (y : F) (hy : y ∈ S), ψ ⟨y, hy⟩ ∈ (algebraMap A (B ⧸ 𝔭)).range := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | h
      · exact ⟨a, rfl⟩
      · have h' : x = y := (Set.mem_singleton_iff.mp h).symm
        subst h'
        refine ⟨a₀, ?_⟩
        rw [halg]
        change Ideal.Quotient.mk 𝔭 (cB a₀) = Ideal.Quotient.mk 𝔭 ⟨x, hxB⟩
        rw [Ideal.Quotient.eq]
        have := 𝔭.neg_mem hx
        rwa [neg_sub] at this
    | zero =>
      change ψ 0 ∈ _
      rw [map_zero]
      exact Subring.zero_mem _
    | one =>
      change ψ 1 ∈ _
      rw [map_one]
      exact Subring.one_mem _
    | add y z hy hz ihy ihz =>
      change ψ (⟨y, hy⟩ + ⟨z, hz⟩) ∈ _
      rw [map_add]
      exact Subring.add_mem _ ihy ihz
    | neg y hy ihy =>
      change ψ (-⟨y, hy⟩) ∈ _
      rw [map_neg]
      exact Subring.neg_mem _ ihy
    | mul y z hy hz ihy ihz =>
      change ψ (⟨y, hy⟩ * ⟨z, hz⟩) ∈ _
      rw [map_mul]
      exact Subring.mul_mem _ ihy ihz
  have step1' : ∀ s : S, ψ s ∈ (algebraMap A (B ⧸ 𝔭)).range := fun s => step1 s s.2

  haveI hintq : Algebra.IsIntegral A (B ⧸ 𝔭) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨f, hf, hfb⟩ := hint b

    set g : Polynomial B := f.map (Subring.inclusion hSB) with hg
    have hgm : g.Monic := hf.map _
    have hgb : g.eval b = 0 := by
      apply Subtype.val_injective
      change B.subtype (eval b (f.map (Subring.inclusion hSB))) = ((0 : B) : F)
      rw [eval_map, hom_eval₂]
      exact hfb
    set gq : Polynomial (B ⧸ 𝔭) := g.map (Ideal.Quotient.mk 𝔭) with hgq
    have hgqm : gq.Monic := hgm.map _
    have hgqb : gq.eval (Ideal.Quotient.mk 𝔭 b) = 0 := by
      rw [hgq, eval_map, eval₂_hom, hgb, map_zero]

    have hlifts : gq ∈ Polynomial.lifts (algebraMap A (B ⧸ 𝔭)) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [hgq, coeff_map, hg, coeff_map]
      exact step1' (f.coeff n)
    obtain ⟨q, hqmap, -, hqm⟩ := lifts_and_degree_eq_and_monic hlifts hgqm
    refine ⟨q, hqm, ?_⟩
    rw [← eval_map, hqmap, hgqb]

  haveI : FaithfulSMul A (B ⧸ 𝔭) := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro a ha
    rw [halg, Ideal.Quotient.eq_zero_iff_mem] at ha
    exact hbot a ha
  obtain ⟨a, ha⟩ :=
    (A.algebraMap_bijective_of_isIntegral_of_isAlgClosed (B ⧸ 𝔭)).2 (Ideal.Quotient.mk 𝔭 b)
  refine ⟨a, ?_⟩
  rw [halg, Ideal.Quotient.eq] at ha
  have := 𝔭.neg_mem ha
  rwa [neg_sub] at this

-- pin: constants_unique_mod (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:868)
theorem constants_unique_mod {B : Subring F} (hconst : ∀ a : A, A.constants a ∈ B)
    (𝔭 : Ideal B) (hbot : ∀ a : A, (⟨A.constants a, hconst a⟩ : B) ∈ 𝔭 → a = 0)
    {a c : A} (h : (⟨A.constants a, hconst a⟩ : B) - ⟨A.constants c, hconst c⟩ ∈ 𝔭) : a = c := by
  have : (⟨A.constants (a - c), hconst (a - c)⟩ : B) ∈ 𝔭 := by
    convert h using 1
    apply Subtype.ext
    push_cast
    rw [map_sub]
  exact sub_eq_zero.mp (hbot _ this)

end Quotient

end ValuationSubring

noncomputable section

open IsLocalRing IsDedekindDomain

namespace Subring

variable {F : Type*} [Field F] {B : Subring F}

-- pin: exists_valuationSubring_dominating (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:896)
theorem exists_valuationSubring_dominating (𝔭 : Ideal B) [𝔭.IsPrime] :
    ∃ O : ValuationSubring F, B ≤ O.toSubring ∧ ∀ b : B, (b : F) ∈ O.nonunits ↔ b ∈ 𝔭 := by
  let L := Localization.AtPrime 𝔭
  have hunit : ∀ y : 𝔭.primeCompl, IsUnit (B.subtype y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr fun h => y.2 ?_
    have : (y : B) = 0 := Subtype.ext h
    rw [this]
    exact 𝔭.zero_mem
  let f : L →+* F := IsLocalization.lift hunit
  have hf : ∀ b : B, f (algebraMap B L b) = b := fun b => IsLocalization.lift_eq hunit b
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨O, fun b hb => ?_, fun b => ?_⟩
  · have := hO (algebraMap B L ⟨b, hb⟩)
    rwa [hf] at this
  ·
    let z : O := ⟨f (algebraMap B L b), hO _⟩
    have hz : f.codRestrict O.toSubring hO (algebraMap B L b) = z := rfl
    have key : IsUnit z ↔ b ∉ 𝔭 := by
      rw [← hz, isUnit_map_iff (f.codRestrict O.toSubring hO),
        IsLocalization.AtPrime.isUnit_to_map_iff L 𝔭 b]
      rfl
    have hzF : (z : F) = b := hf b
    rw [← hzF, ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      key, not_not]

-- pin: ne_top_of_dominating (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:922)
theorem ne_top_of_dominating {𝔭 : Ideal B} {O : ValuationSubring F}
    (hdom : ∀ b : B, (b : F) ∈ O.nonunits ↔ b ∈ 𝔭) (h𝔭 : 𝔭 ≠ ⊥) : O ≠ ⊤ := by
  intro htop
  apply h𝔭
  rw [eq_bot_iff]
  intro b hb
  have hn : (b : F) ∈ O.nonunits := (hdom b).mpr hb
  rcases (ValuationSubring.mem_nonunits_iff_or _).mp hn with h0 | hinv
  · exact (Ideal.mem_bot).mpr (Subtype.ext h0)
  · exact absurd (htop ▸ ValuationSubring.mem_top _) hinv

-- pin: algebraMap_mem_of_dominating (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:933)
theorem algebraMap_mem_of_dominating {K : Type*} [Field K] [Algebra K F] (A : ValuationSubring K)
    (hconst : ∀ a : A, algebraMap K F a ∈ B) {𝔭 : Ideal B} {O : ValuationSubring F}
    (hle : B ≤ O.toSubring) (hdom : ∀ b : B, (b : F) ∈ O.nonunits ↔ b ∈ 𝔭)
    (hbot : ∀ a : A, (⟨algebraMap K F a, hconst a⟩ : B) ∈ 𝔭 → a = 0) (c : K) :
    algebraMap K F c ∈ O := by
  by_cases hc : c ∈ A
  · exact hle (hconst ⟨c, hc⟩)
  · have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hc
    have hc0 : c ≠ 0 := fun h => hc (h ▸ A.zero_mem)

    have hnot : (⟨algebraMap K F (c⁻¹ : K), hconst ⟨c⁻¹, hcinv⟩⟩ : B) ∉ 𝔭 := fun h =>
      inv_ne_zero hc0 (by simpa using congrArg Subtype.val (hbot ⟨c⁻¹, hcinv⟩ h))
    have hnu : algebraMap K F c⁻¹ ∉ O.nonunits := fun h => hnot ((hdom _).mp h)
    rw [map_inv₀, ValuationSubring.inv_mem_nonunits_iff, not_or] at hnu
    exact not_not.mp hnu.2

end Subring

namespace ValuationSubring

variable {F : Type*} [Field F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (O : ValuationSubring F)

-- pin: ValuationSubring.centreOver (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:960)
def _root_.ValuationSubring.centreOver (hO : ∀ r : R, algebraMap R F r ∈ O) : Ideal R :=
  (IsLocalRing.maximalIdeal O).comap ((algebraMap R F).codRestrict O.toSubring hO)

-- pin: centreOver_isPrime (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:964)
scoped instance centreOver_isPrime (hO : ∀ r : R, algebraMap R F r ∈ O) : (O.centreOver hO).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsDedekindDomain R] [IsFractionRing R F] in
-- pin: ValuationSubring.mem_centreOver_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:968)
theorem _root_.ValuationSubring.mem_centreOver_iff (hO : ∀ r : R, algebraMap R F r ∈ O) {r : R} :
    r ∈ O.centreOver hO ↔ algebraMap R F r ∈ O.nonunits := by
  rw [centreOver, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

omit [IsDedekindDomain R] [IsFractionRing R F] in
-- pin: ValuationSubring.inv_algebraMap_mem (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:975)
theorem _root_.ValuationSubring.inv_algebraMap_mem (hO : ∀ r : R, algebraMap R F r ∈ O) {s : R}
    (hs : s ∉ O.centreOver hO) : (algebraMap R F s)⁻¹ ∈ O := by
  rw [mem_centreOver_iff, ValuationSubring.mem_nonunits_iff, not_lt] at hs
  have hy : O.valuation (algebraMap R F s) ≤ 1 := (O.valuation_le_one_iff _).mpr (hO s)
  have h1 : O.valuation (algebraMap R F s) = 1 := le_antisymm hy hs
  apply (O.valuation_le_one_iff _).mp
  rw [map_inv₀, h1, inv_one]


-- pin: ValuationSubring.centreOver_ne_bot (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:985)
theorem _root_.ValuationSubring.centreOver_ne_bot (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    O.centreOver hO ≠ ⊥ := by
  intro hbot
  apply hne
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  rw [div_eq_mul_inv]
  refine O.mul_mem _ _ (hO a) (O.inv_algebraMap_mem hO fun hmem => ?_)
  rw [hbot, Ideal.mem_bot] at hmem
  exact nonZeroDivisors.ne_zero hb hmem


-- pin: ValuationSubring.centreHeightOneSpectrum (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:998)
def _root_.ValuationSubring.centreHeightOneSpectrum (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    HeightOneSpectrum R :=
  ⟨O.centreOver hO, inferInstance, O.centreOver_ne_bot hO hne⟩


-- pin: ValuationSubring.valuationSubringAtPrime_centre_le (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1004)
theorem _root_.ValuationSubring.valuationSubringAtPrime_centre_le (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime F (O.centreHeightOneSpectrum hO hne) ≤ O := by
  rintro x ⟨a, s, hs, rfl⟩
  exact O.mul_mem _ _ (hO a) (O.inv_algebraMap_mem hO hs)


-- pin: ValuationSubring.eq_valuationSubringAtPrime_centre (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1011)
theorem _root_.ValuationSubring.eq_valuationSubringAtPrime_centre (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    O = HeightOneSpectrum.valuationSubringAtPrime F (O.centreHeightOneSpectrum hO hne) :=
  (ValuationSubring.eq_of_le_of_ne_top _ (O.valuationSubringAtPrime_centre_le hO hne) hne).symm


-- pin: ValuationSubring.isPrincipalIdealRing_of_dedekind_le (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1017)
theorem _root_.ValuationSubring.isPrincipalIdealRing_of_dedekind_le (hO : ∀ r : R, algebraMap R F r ∈ O) (hne : O ≠ ⊤) :
    IsPrincipalIdealRing O := by
  rw [O.eq_valuationSubringAtPrime_centre hO hne]
  infer_instance

end ValuationSubring

open IsLocalRing Polynomial

namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]

-- pin: Valuation.exists_ne_map_eq_of_sum_eq_zero (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1071)
theorem _root_.Valuation.exists_ne_map_eq_of_sum_eq_zero {ι : Type*} [DecidableEq ι] (v : Valuation R Γ₀)
    {s : Finset ι} {f : ι → R} (hs : ∑ i ∈ s, f i = 0) {j : ι} (hj : j ∈ s)
    (hj0 : v (f j) ≠ 0) (hmax : ∀ i ∈ s, v (f i) ≤ v (f j)) :
    ∃ i ∈ s, i ≠ j ∧ v (f i) = v (f j) := by
  by_contra h
  push Not at h
  have hlt : ∀ i ∈ s \ {j}, v (f i) < v (f j) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact lt_of_le_of_ne (hmax i hi.1) (h i hi.1 hi.2)
  have := v.map_sum_eq_of_lt hj hlt
  rw [hs, map_zero] at this
  exact hj0 this.symm

end Valuation

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K)
variable {k : Type*} [Field k]

-- pin: ValuationSubring.natCast_mem_ker (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1096)
theorem _root_.ValuationSubring.natCast_mem_ker (ℓ : ℕ) [CharP k ℓ] (red : A →+* k) :
    ((ℓ : ℕ) : A) ∈ RingHom.ker red := by
  rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]


-- pin: ValuationSubring.natCast_mem_maximalIdeal (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1102)
theorem _root_.ValuationSubring.natCast_mem_maximalIdeal (ℓ : ℕ) [CharP k ℓ] (red : A →+* k) :
    ((ℓ : ℕ) : A) ∈ maximalIdeal A :=
  IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red) (A.natCast_mem_ker ℓ red)


-- pin: ValuationSubring.isUnit_intCast_of_not_dvd (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1108)
theorem _root_.ValuationSubring.isUnit_intCast_of_not_dvd (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k)
    {m : ℤ} (hm : ¬ (ℓ : ℤ) ∣ m) : IsUnit ((m : ℤ) : A) := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hprime.irreducible).mpr hm
  have hA : (a : A) * ((ℓ : ℕ) : A) + (b : A) * (m : A) = 1 := by
    have := congrArg (Int.cast : ℤ → A) hab
    push_cast at this
    exact this
  have hℓm : (a : A) * ((ℓ : ℕ) : A) ∈ maximalIdeal A :=
    Ideal.mul_mem_left _ _ (A.natCast_mem_maximalIdeal ℓ red)
  have hu : IsUnit ((b : A) * (m : A)) := by
    by_contra hnu
    have hmem : (b : A) * (m : A) ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h1 : (1 : A) ∈ maximalIdeal A := hA ▸ Ideal.add_mem _ hℓm hmem
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  exact isUnit_of_mul_isUnit_right hu


-- pin: ValuationSubring.map_intCast_eq_zero_of_not_isUnit (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1127)
theorem _root_.ValuationSubring.map_intCast_eq_zero_of_not_isUnit (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k)
    {m : ℤ} (hm : ¬ IsUnit ((m : ℤ) : A)) : red (m : A) = 0 := by
  have hdvd : (ℓ : ℤ) ∣ m := by
    by_contra h
    exact hm (A.isUnit_intCast_of_not_dvd ℓ red h)
  obtain ⟨c, rfl⟩ := hdvd
  rw [map_intCast]
  push_cast
  rw [CharP.cast_eq_zero k ℓ, zero_mul]


-- pin: ValuationSubring.map_eq_zero_of_rat_mem_maximalIdeal (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1139)
theorem _root_.ValuationSubring.map_eq_zero_of_rat_mem_maximalIdeal (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (red : A →+* k) (φ : ℚ →+* K) (r : ℚ) (hrA : φ r ∈ A)
    (hr : (⟨φ r, hrA⟩ : A) ∈ maximalIdeal A) : red ⟨φ r, hrA⟩ = 0 := by

  have hnum : (⟨φ r, hrA⟩ : A) * ((r.den : ℕ) : A) = ((r.num : ℤ) : A) := by
    apply Subtype.ext
    change φ r * (((r.den : ℕ) : A) : K) = (((r.num : ℤ) : A) : K)
    push_cast
    rw [← map_natCast φ, ← map_intCast φ, ← map_mul, Rat.mul_den_eq_num]

  have hnum_mem : ((r.num : ℤ) : A) ∈ maximalIdeal A := hnum ▸ Ideal.mul_mem_right _ _ hr
  have hnum0 : red ((r.num : ℤ) : A) = 0 :=
    A.map_intCast_eq_zero_of_not_isUnit ℓ red ((IsLocalRing.mem_maximalIdeal _).mp hnum_mem)

  have hden : ¬ (ℓ : ℤ) ∣ (r.den : ℤ) := by
    intro h
    have hℓnum : (ℓ : ℤ) ∣ r.num := by
      by_contra h'
      have hu : IsUnit ((r.num : ℤ) : A) := A.isUnit_intCast_of_not_dvd ℓ red h'
      exact (IsLocalRing.mem_maximalIdeal _).mp hnum_mem hu
    have h1 : (ℓ : ℤ) ∣ (Int.gcd r.num (r.den : ℤ) : ℤ) := Int.dvd_coe_gcd hℓnum h
    have hg : Int.gcd r.num (r.den : ℤ) = 1 := by
      simpa [Int.gcd, Int.natAbs_natCast] using r.reduced
    rw [hg] at h1
    have := Int.eq_one_of_dvd_one (by positivity) h1
    have hℓ1 : ℓ = 1 := by exact_mod_cast this
    exact (Fact.out : ℓ.Prime).one_lt.ne' hℓ1
  have hden0 : red ((r.den : ℕ) : A) ≠ 0 := by
    rw [map_natCast]
    intro h0
    rw [CharP.cast_eq_zero_iff k ℓ] at h0
    exact hden (by exact_mod_cast h0)

  have := congrArg red hnum
  rw [map_mul, hnum0] at this
  exact (mul_eq_zero.mp this).resolve_right hden0


-- pin: ValuationSubring.exists_pow_valuation_eq_of_isRoot (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1178)
theorem _root_.ValuationSubring.exists_pow_valuation_eq_of_isRoot (φ : ℚ →+* K) {x : K} (hx0 : x ≠ 0)
    {p : ℚ[X]} (hp0 : p ≠ 0) (hpx : p.eval₂ φ x = 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : ℚ, r ≠ 0 ∧ A.valuation (x ^ n) = A.valuation (φ r) := by
  classical
  set v := A.valuation with hv
  let f : ℕ → K := fun i => φ (p.coeff i) * x ^ i
  have hsum : ∑ i ∈ p.support, f i = 0 := by
    rw [eval₂_eq_sum, Polynomial.sum_def] at hpx
    exact hpx
  have hvx : v x ≠ 0 := (v.ne_zero_iff).mpr hx0
  have hf0 : ∀ i ∈ p.support, v (f i) ≠ 0 := by
    intro i hi
    refine (v.ne_zero_iff).mpr (mul_ne_zero ?_ (pow_ne_zero _ hx0))
    exact (map_ne_zero φ).mpr (mem_support_iff.mp hi)
  obtain ⟨j, hj, hjmax⟩ :=
    Finset.exists_max_image p.support (fun i => v (f i)) (support_nonempty.mpr hp0)
  obtain ⟨i, hi, hij, heq⟩ := v.exists_ne_map_eq_of_sum_eq_zero hsum hj (hf0 j hj) hjmax

  obtain ⟨a, b, hab, ha, hb, heq'⟩ :
      ∃ a b : ℕ, a < b ∧ a ∈ p.support ∧ b ∈ p.support ∧ v (f a) = v (f b) := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h, hi, hj, heq⟩
    · exact ⟨j, i, h, hj, hi, heq.symm⟩
  have hca0 : v (φ (p.coeff a)) ≠ 0 := (v.ne_zero_iff).mpr ((map_ne_zero φ).mpr (mem_support_iff.mp ha))
  have hcb0 : v (φ (p.coeff b)) ≠ 0 := (v.ne_zero_iff).mpr ((map_ne_zero φ).mpr (mem_support_iff.mp hb))

  have h1 : v (φ (p.coeff a)) * v x ^ a = (v (φ (p.coeff b)) * v x ^ (b - a)) * v x ^ a := by
    have e : v x ^ b = v x ^ (b - a) * v x ^ a := by rw [← pow_add, Nat.sub_add_cancel hab.le]
    have := heq'
    simp only [f, map_mul, map_pow] at this
    rw [this, e, ← mul_assoc]
  have h2 : v (φ (p.coeff a)) = v (φ (p.coeff b)) * v x ^ (b - a) :=
    mul_right_cancel₀ (pow_ne_zero _ hvx) h1
  refine ⟨b - a, Nat.sub_pos_of_lt hab, p.coeff a / p.coeff b,
    div_ne_zero (mem_support_iff.mp ha) (mem_support_iff.mp hb), ?_⟩
  rw [map_div₀, map_div₀, map_pow, h2, mul_div_cancel_left₀ _ hcb0]


-- pin: ValuationSubring.ker_eq_maximalIdeal_of_isAlgebraic (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1217)
theorem _root_.ValuationSubring.ker_eq_maximalIdeal_of_isAlgebraic [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k) :
    RingHom.ker red = maximalIdeal A := by
  refine le_antisymm (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top red)) ?_
  intro x hx
  rw [RingHom.mem_ker]
  rcases eq_or_ne x 0 with rfl | hx0
  · exact map_zero red
  have hxK : (x : K) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hx0
  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x : K)
  obtain ⟨n, hn, r, hr0, hval⟩ :=
    A.exists_pow_valuation_eq_of_isRoot (algebraMap ℚ K) hxK hp0 (by rwa [← aeval_def])

  obtain ⟨u, hu⟩ := (A.valuation_eq_iff _ _).mp hval
  have hcoe : ((((u⁻¹ : Aˣ) : A) * x ^ n : A) : K) = algebraMap ℚ K r := by
    push_cast
    rw [← hu, ← mul_assoc, ← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one, one_mul]
  have hrA : algebraMap ℚ K r ∈ A := hcoe ▸ SetLike.coe_mem _
  have hxn : x ^ n = (u : A) * ⟨algebraMap ℚ K r, hrA⟩ := by
    apply Subtype.ext
    push_cast
    exact hu.symm
  have hrm : (⟨algebraMap ℚ K r, hrA⟩ : A) ∈ maximalIdeal A := by
    have hxnm : x ^ n ∈ maximalIdeal A := Ideal.pow_mem_of_mem _ hx n hn
    rw [hxn] at hxnm
    exact ((IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_or_mem hxnm).resolve_left
      (fun h => (IsLocalRing.mem_maximalIdeal _).mp h u.isUnit)
  have hr0' : red ⟨algebraMap ℚ K r, hrA⟩ = 0 :=
    A.map_eq_zero_of_rat_mem_maximalIdeal ℓ red (algebraMap ℚ K) r hrA hrm
  have : red (x ^ n) = 0 := by rw [hxn, map_mul, hr0', mul_zero]
  rw [map_pow] at this
  exact pow_eq_zero_iff hn.ne' |>.mp this


-- pin: exists_mul_eq_one_of_map_ne_zero (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1252)
theorem exists_mul_eq_one_of_map_ne_zero [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k) {a : A} (ha : red a ≠ 0) :
    ∃ b : A, red a * red b = 1 := by
  have hunit : IsUnit a := by
    by_contra h
    have : a ∈ RingHom.ker red := by
      rw [A.ker_eq_maximalIdeal_of_isAlgebraic ℓ red]
      exact (IsLocalRing.mem_maximalIdeal _).mpr h
    exact ha this
  obtain ⟨u, rfl⟩ := hunit
  exact ⟨((u⁻¹ : Aˣ) : A), by rw [← map_mul, Units.mul_inv, map_one]⟩

-- pin: ker_eq_maximalIdeal_apply (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1264)
theorem ker_eq_maximalIdeal_apply [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (red : A →+* k) (a : A) :
    red a = 0 ↔ a ∈ maximalIdeal A := by
  rw [← RingHom.mem_ker, A.ker_eq_maximalIdeal_of_isAlgebraic ℓ red]

end ValuationSubring

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField Polynomial

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {j : F}

-- pin: isPrincipalIdealRing_adjoin_singleton (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1285)
theorem isPrincipalIdealRing_adjoin_singleton (hj : Transcendental K j) :
    IsPrincipalIdealRing (Algebra.adjoin K ({j} : Set F)) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental K j hj).toRingHom
    (Polynomial.algEquivOfTranscendental K j hj).surjective

-- pin: isDedekindDomain_adjoin_singleton (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1290)
theorem isDedekindDomain_adjoin_singleton (hj : Transcendental K j) :
    IsDedekindDomain (Algebra.adjoin K ({j} : Set F)) :=
  haveI := isPrincipalIdealRing_adjoin_singleton hj
  inferInstance

-- pin: isDedekindDomain_integralClosure_adjoin (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1295)
theorem isDedekindDomain_integralClosure_adjoin_of_transcendental (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F] [Algebra.IsSeparable K⟮j⟯ F] :
    IsDedekindDomain (integralClosure (Algebra.adjoin K ({j} : Set F)) F) :=
  haveI := isDedekindDomain_adjoin_singleton hj
  integralClosure.isDedekindDomain (Algebra.adjoin K ({j} : Set F)) K⟮j⟯ F

-- pin: isFractionRing_integralClosure_adjoin (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1301)
theorem isFractionRing_integralClosure_adjoin_of_transcendental (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F] :
    IsFractionRing (integralClosure (Algebra.adjoin K ({j} : Set F)) F) F :=
  haveI := isDedekindDomain_adjoin_singleton hj
  integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin K ({j} : Set F)) K⟮j⟯ F

-- pin: integralClosure_adjoin_le_valuationSubring (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1307)
theorem integralClosure_adjoin_le_valuationSubring (O : ValuationSubring F)
    (hK : ∀ c : K, algebraMap K F c ∈ O) (hjO : j ∈ O)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) : (r : F) ∈ O := by

  let O' : Subalgebra K F :=
    { O.toSubring with
      algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({j} : Set F) ≤ O' :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjO)
  let φ : Algebra.adjoin K ({j} : Set F) →+* O :=
    (Subalgebra.val _).toRingHom.codRestrict O.toSubring (fun y => hle y.2)

  obtain ⟨p, hp, hpr⟩ : IsIntegral (Algebra.adjoin K ({j} : Set F)) (r : F) := r.2
  have hint : IsIntegral O (r : F) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [eval₂_map]
    exact hpr
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

-- pin: algebraMap_mem_integralClosure_adjoin (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1328)
theorem algebraMap_mem_integralClosure_adjoin (c : K) :
    algebraMap K F c ∈ integralClosure (Algebra.adjoin K ({j} : Set F)) F := by
  rw [mem_integralClosure_iff, IsScalarTower.algebraMap_apply K (Algebra.adjoin K ({j} : Set F)) F]
  exact isIntegral_algebraMap

-- pin: self_mem_integralClosure_adjoin (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1333)
theorem self_mem_integralClosure_adjoin :
    j ∈ integralClosure (Algebra.adjoin K ({j} : Set F)) F := by
  rw [mem_integralClosure_iff]
  have : j = algebraMap (Algebra.adjoin K ({j} : Set F)) F ⟨j, Algebra.self_mem_adjoin_singleton K j⟩ :=
    rfl
  rw [this]
  exact isIntegral_algebraMap

-- pin: le_integralClosure_adjoin_of_isIntegral (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1341)
theorem le_integralClosure_adjoin_of_isIntegral {S B : Subring F}
    (hS : S ≤ (Algebra.adjoin K ({j} : Set F)).toSubring)
    (hint : ∀ b : B, IsIntegral S (b : F)) (b : B) :
    (b : F) ∈ integralClosure (Algebra.adjoin K ({j} : Set F)) F := by
  rw [mem_integralClosure_iff]
  obtain ⟨p, hp, hpb⟩ := hint b
  let φ : S →+* Algebra.adjoin K ({j} : Set F) :=
    S.subtype.codRestrict (Algebra.adjoin K ({j} : Set F)).toSubring (fun y => hS y.2)
  refine ⟨p.map φ, hp.map φ, ?_⟩
  rw [eval₂_map]
  exact hpb

end AlgebraicCurve

open Polynomial

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K) {k : Type*} [Field k]

-- pin: isAlgClosed_of_surjective (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1366)
theorem isAlgClosed_of_surjective [IsAlgClosed K] (red : A →+* k)
    (hred : Function.Surjective red) : IsAlgClosed k := by
  refine IsAlgClosed.of_exists_root k fun p hp hirr => ?_

  have hlifts : p ∈ Polynomial.lifts red := (lifts_iff_coeff_lifts p).mpr fun n => hred _
  obtain ⟨P, hPp, hPdeg, hP⟩ := lifts_and_degree_eq_and_monic hlifts hp

  have hdegK : (P.map (algebraMap A K)).degree ≠ 0 := by
    rw [hP.degree_map, hPdeg]
    exact (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (P.map (algebraMap A K)) hdegK

  have hint : IsIntegral A x := ⟨P, hP, by rwa [IsRoot.def, eval_map] at hx⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint

  have hy : P.eval y = 0 := by
    apply IsFractionRing.injective A K
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← eval_map]
    exact hx
  refine ⟨red y, ?_⟩
  rw [← hPp, eval_map, Polynomial.eval₂_at_apply, hy, map_zero]

end ValuationSubring

namespace RingHom

variable {B C : Type*} [CommRing B] [CommRing C] (π : B →+* C)

-- pin: RingHom.imagePrime (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1399)
def _root_.RingHom.imagePrime (𝔮 : Ideal B) : Ideal π.range := 𝔮.map π.rangeRestrict

variable {π} in

-- pin: rangeRestrict_mem_imagePrime_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1404)
theorem rangeRestrict_mem_imagePrime_iff {𝔮 : Ideal B} (hker : ker π ≤ 𝔮) (b : B) :
    π.rangeRestrict b ∈ π.imagePrime 𝔮 ↔ b ∈ 𝔮 := by
  rw [imagePrime, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ π.rangeRestrict_surjective,
    ← RingHom.ker, ker_rangeRestrict, sup_eq_left.mpr hker]

variable {π} in

-- pin: mk_mem_imagePrime_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1411)
theorem mk_mem_imagePrime_iff {𝔮 : Ideal B} (hker : ker π ≤ 𝔮) (b : B)
    (hb : π b ∈ π.range := π.mem_range_self b) :
    (⟨π b, hb⟩ : π.range) ∈ π.imagePrime 𝔮 ↔ b ∈ 𝔮 :=
  rangeRestrict_mem_imagePrime_iff hker b

variable {π} in

-- pin: mem_imagePrime_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1418)
theorem mem_imagePrime_iff {𝔮 : Ideal B} (y : π.range) :
    y ∈ π.imagePrime 𝔮 ↔ ∃ b ∈ 𝔮, π.rangeRestrict b = y := by
  rw [imagePrime, Ideal.mem_map_iff_of_surjective _ π.rangeRestrict_surjective]

variable {π} in

-- pin: imagePrime_ne_top (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1424)
theorem imagePrime_ne_top {𝔮 : Ideal B} (hker : ker π ≤ 𝔮) (h𝔮 : 𝔮 ≠ ⊤) :
    π.imagePrime 𝔮 ≠ ⊤ := by
  intro htop
  apply h𝔮
  rw [Ideal.eq_top_iff_one, ← rangeRestrict_mem_imagePrime_iff hker, map_one, htop]
  exact Submodule.mem_top

variable {π} in

-- pin: imagePrime_isPrime (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1433)
theorem imagePrime_isPrime {𝔮 : Ideal B} [𝔮.IsPrime] (hker : ker π ≤ 𝔮) :
    (π.imagePrime 𝔮).IsPrime :=
  Ideal.map_isPrime_of_surjective π.rangeRestrict_surjective (by rwa [ker_rangeRestrict])

variable {π} in

-- pin: imagePrime_isMaximal (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1439)
theorem imagePrime_isMaximal {𝔮 : Ideal B} [h : 𝔮.IsMaximal] (hker : ker π ≤ 𝔮) :
    (π.imagePrime 𝔮).IsMaximal :=
  (Ideal.map_eq_top_or_isMaximal_of_surjective _ π.rangeRestrict_surjective h).resolve_left
    (imagePrime_ne_top hker h.ne_top)

variable {π} in

-- pin: eq_zero_of_const_mem_imagePrime (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1446)
theorem eq_zero_of_const_mem_imagePrime {A k : Type*} [CommRing A] [CommRing k]
    (σ : A →+* B) (red : A →+* k) (ι : k →+* C) (hcompat : ∀ a : A, π (σ a) = ι (red a))
    (hred : Function.Surjective red) {𝔮 : Ideal B} (hker : ker π ≤ 𝔮)
    (h𝔮 : ∀ a : A, σ a ∈ 𝔮 → red a = 0) (c : k) (hc : ι c ∈ π.range)
    (hmem : (⟨ι c, hc⟩ : π.range) ∈ π.imagePrime 𝔮) : c = 0 := by
  obtain ⟨a, rfl⟩ := hred c
  refine h𝔮 a ((rangeRestrict_mem_imagePrime_iff hker (σ a)).mp ?_)
  convert hmem using 1
  exact Subtype.ext (hcompat a)

variable {π} in

-- pin: const_mem_range (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1458)
theorem const_mem_range {A k : Type*} [CommRing A] [CommRing k]
    (σ : A →+* B) (red : A →+* k) (ι : k →+* C) (hcompat : ∀ a : A, π (σ a) = ι (red a))
    (hred : Function.Surjective red) (c : k) : ι c ∈ π.range := by
  obtain ⟨a, rfl⟩ := hred c
  exact ⟨σ a, hcompat a⟩

end RingHom


namespace IntermediateField

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

-- pin: IntermediateField.adjoin_simple_inv_eq (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1722)
theorem _root_.IntermediateField.adjoin_simple_inv_eq (x : E) :
    IntermediateField.adjoin K ({x⁻¹} : Set E) = IntermediateField.adjoin K ({x} : Set E) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self K x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have h := inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
    rwa [inv_inv] at h

end IntermediateField

namespace ValuationSubring

variable {F : Type*} [Field F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]

-- pin: eq_of_forall_mem_nonunits_iff (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1762)
theorem eq_of_forall_mem_nonunits_iff {O₁ O₂ : ValuationSubring F}
    (h₁ : ∀ r : R, algebraMap R F r ∈ O₁) (hne₁ : O₁ ≠ ⊤)
    (h₂ : ∀ r : R, algebraMap R F r ∈ O₂) (hne₂ : O₂ ≠ ⊤)
    (h : ∀ r : R, algebraMap R F r ∈ O₁.nonunits ↔ algebraMap R F r ∈ O₂.nonunits) :
    O₁ = O₂ := by
  have hc : O₁.centreHeightOneSpectrum h₁ hne₁ = O₂.centreHeightOneSpectrum h₂ hne₂ := by
    ext r
    change r ∈ O₁.centreOver h₁ ↔ r ∈ O₂.centreOver h₂
    rw [mem_centreOver_iff, mem_centreOver_iff]
    exact h r
  rw [O₁.eq_valuationSubringAtPrime_centre h₁ hne₁, O₂.eq_valuationSubringAtPrime_centre h₂ hne₂,
    hc]

end ValuationSubring
