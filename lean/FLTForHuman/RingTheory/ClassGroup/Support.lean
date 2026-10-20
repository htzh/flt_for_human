/-
  A finite class group has a finite set of height-one primes that supports a
  representative of every class:

      `∃ S : Finset (HeightOneSpectrum R), ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰,
         ClassGroup.mk0 I = c ∧ ∀ v, v.asIdeal ∣ (I : Ideal R) → v ∈ S`.

  The port of the pin leaf `ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd`
  (`Theorems/Thm_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd.lean` and
  `P2M/Sol/S_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd.lean`, pinned
  `aa2d8b3`; 18 pin lines). The statement is the wrapper's verbatim, the proof the
  `S_` file's `solution` body; the pin's `solution` wrapper is not ported, and the
  pin's `open scoped nonZeroDivisors` is kept.

  The mathematics: `ClassGroup.mk0_surjective` chooses one nonzero ideal `I c` per
  class, `Ideal.finite_factors` says each nonzero ideal has finitely many maximal
  divisors, and the finite union `⋃ c, {v | v.asIdeal ∣ I c}` is the set `S`.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.
  Mathlib has the ingredients (`ClassGroup.mk0_surjective`,
  `Mathlib/RingTheory/ClassGroup/Basic.lean:348`; `Ideal.finite_factors`,
  `Mathlib/RingTheory/DedekindDomain/Factorization.lean:85`) but not the packaged
  statement: `rg -F "Finset (IsDedekindDomain.HeightOneSpectrum" Mathlib/` and
  `rg "exists_finset.*mk0" Mathlib/` are empty (2026-10-20).

  spec-pin: Theorems/Thm_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd.lean
  spec-pin: P2M/Sol/S_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd.lean
-/

import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false

open scoped nonZeroDivisors

theorem ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd
    (R : Type*) [CommRing R] [IsDedekindDomain R] [Finite (ClassGroup R)] :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum R), ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰,
      ClassGroup.mk0 I = c ∧ ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S := by
  classical
  choose I hI using (ClassGroup.mk0_surjective (R := R))
  have hfin : (⋃ c : ClassGroup R, {v : IsDedekindDomain.HeightOneSpectrum R | v.asIdeal ∣ (I c : Ideal R)}).Finite :=
    Set.finite_iUnion fun c => Ideal.finite_factors (nonZeroDivisors.coe_ne_zero (I c))
  refine ⟨hfin.toFinset, fun c => ⟨I c, hI c, fun v hv => ?_⟩⟩
  rw [Set.Finite.mem_toFinset]
  exact Set.mem_iUnion.2 ⟨c, hv⟩
