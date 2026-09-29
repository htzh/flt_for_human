/-
  Extending characters along an integral extension, and the `ℤ̄`-valued
  characters of a finite `ℤ`-algebra.

  Two generic algebra facts that the T-side eigenform extraction consumes:

  * `RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed` — a ring
    hom `χ : A →+* K` into an algebraically closed field whose kernel contains
    `ker (algebraMap A B)` extends along an integral extension `A → B`.
  * `Ideal.exists_ringHom_integralClosure_ker_eq` — every prime `𝔓` of a finite
    `ℤ`-algebra `T` whose contraction to `ℤ` is `⊥` is the kernel of a ring hom
    `T →+* integralClosure ℤ ℂ`.

  Both statements are the pin's `Theorems/` wrappers verbatim; the proofs are
  transcribed from the `P2M/Sol/S_*` files, pinned `aa2d8b3`:

  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed.lean
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Ideal_exists_ringHom_integralClosure_ker_eq.lean

  The pin's blanket `import Mathlib` and the `P2M.Util` shims are replaced by the
  specific mathlib modules actually used.
-/
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option autoImplicit false

-- The pin's `haveI` walls are load-bearing; keep them literal (port convention).
set_option linter.style.haveILetI false

noncomputable section

open Ideal

/-- **Extending a character along an integral extension.** Stated verbatim from
`Theorems/Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed.lean`. -/
theorem RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed {A B K : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] [Field K] [IsAlgClosed K]
    (χ : A →+* K) (hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker χ) :
    ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = χ := by
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨Q, -, hQ, hQP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker χ) (⊥ : Ideal B) hker
  haveI := hQ
  have hPker : ∀ a : A, a ∈ Q.comap (algebraMap A B) → χ a = 0 := fun a ha => by
    change a ∈ Ideal.under A Q at ha
    rw [hQP] at ha
    exact RingHom.mem_ker.mp ha
  let χbar : A ⧸ Q.comap (algebraMap A B) →+* K := Ideal.Quotient.lift _ χ hPker
  have hχbar_inj : Function.Injective χbar :=
    RingHom.lift_injective_of_ker_le_ideal _ hPker (le_of_eq hQP.symm)
  letI : Algebra (A ⧸ Q.comap (algebraMap A B)) K := χbar.toAlgebra
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : IsDomain (A ⧸ Q.comap (algebraMap A B)) := Ideal.Quotient.isDomain _
  haveI : Module.IsTorsionFree (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (A ⧸ Q.comap (algebraMap A B)) K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hχbar_inj
  let ψbar : (B ⧸ Q) →ₐ[A ⧸ Q.comap (algebraMap A B)] K := IsAlgClosed.lift
  refine ⟨ψbar.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun a => ?_⟩
  have h1 : Ideal.Quotient.mk Q (algebraMap A B a) =
      algebraMap (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q) (Ideal.Quotient.mk _ a) := rfl
  show ψbar (Ideal.Quotient.mk Q (algebraMap A B a)) = χ a
  rw [h1, ψbar.commutes]
  rfl

/-- **Primes of a finite `ℤ`-algebra as kernels of `ℤ̄`-valued characters.** Stated
verbatim from `Theorems/Thm_Ideal_exists_ringHom_integralClosure_ker_eq.lean`. -/
theorem Ideal.exists_ringHom_integralClosure_ker_eq {T : Type*} [CommRing T]
    [Module.Finite ℤ T] (𝔓 : Ideal T) (h𝔓 : 𝔓.IsPrime)
    (hint : ∀ n : ℤ, (n : T) ∈ 𝔓 → n = 0) :
    ∃ f : T →+* integralClosure ℤ ℂ, RingHom.ker f = 𝔓 := by
  classical
  haveI := h𝔓

  set D := T ⧸ 𝔓 with hD
  haveI : IsDomain D := Ideal.Quotient.isDomain 𝔓
  have hinjD : Function.Injective (algebraMap ℤ D) := by
    intro a b hab
    have h : ((a - b : ℤ) : T) ∈ 𝔓 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast, Int.cast_sub, sub_eq_zero]
      simpa [Algebra.algebraMap_eq_smul_one] using hab
    exact sub_eq_zero.mp (hint _ h)
  haveI : CharZero D := by
    refine ⟨fun a b hab => ?_⟩
    have := hinjD (show algebraMap ℤ D (a : ℤ) = algebraMap ℤ D (b : ℤ) by simpa using hab)
    exact_mod_cast this
  haveI : @Module.IsTorsionFree ℤ D _ _ Algebra.toModule := by
    refine ⟨fun n hn => ?_⟩
    intro a b hab
    have hn0 : algebraMap ℤ D n ≠ 0 := (map_ne_zero_iff _ hinjD).mpr hn.ne_zero
    have h' : algebraMap ℤ D n * a = algebraMap ℤ D n * b := by
      simpa only [Algebra.smul_def] using hab
    exact mul_left_cancel₀ hn0 h'
  haveI : Module.Finite ℤ D :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔓).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ 𝔓)
  haveI : Algebra.IsIntegral ℤ D := inferInstance
  haveI : Algebra.IsAlgebraic ℤ D := ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩

  let φ : D →ₐ[ℤ] ℂ := IsAlgClosed.lift
  have hφker : RingHom.ker φ.toRingHom = ⊥ := by
    refine Ideal.eq_bot_of_under_eq_bot (R := ℤ) ?_
    refine eq_bot_iff.mpr fun n hn => ?_
    rw [Ideal.mem_under, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes] at hn
    simpa using hn
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    have : d ∈ RingHom.ker φ.toRingHom := hd
    rw [hφker, Ideal.mem_bot] at this
    exact this

  have hmem : ∀ t : T, (φ.toRingHom.comp (Ideal.Quotient.mk 𝔓)) t ∈ integralClosure ℤ ℂ := by
    intro t
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) (Ideal.Quotient.mk 𝔓 t)).map φ
  refine ⟨(φ.toRingHom.comp (Ideal.Quotient.mk 𝔓)).codRestrict (integralClosure ℤ ℂ) hmem, ?_⟩
  ext t
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    apply hφinj
    rw [map_zero]
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    show φ (Ideal.Quotient.mk 𝔓 t) = 0
    rw [h, map_zero]

end
