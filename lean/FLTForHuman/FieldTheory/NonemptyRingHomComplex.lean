/-
  `Field.nonempty_ringHom_complex_of_countable`: a countable field of characteristic `0`
  embeds into `ℂ`.

  Statement authority: `Theorems/Thm_Field_nonempty_ringHom_complex_of_countable.lean`; proof
  from the pin's `P2M/Sol/S_Field_nonempty_ringHom_complex_of_countable.lean` (`:9–45`), pinned
  `anthropics/fermats-last-theorem@aa2d8b3`.

  One of SC's two leaves (row S, `topics/velu/WORKORDER-SC-capstone.md`), used by the capstone's
  `solution0` to reach the `ℂ` case. The argument is mathlib-foundational: an injection of
  transcendence bases `s ↪ t` (`#K = ℵ₀ ≤ #ℂ`, and `#ℂ = #t` by
  `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'`), lifted to an injection
  of the algebraic extensions `Algebra.adjoin ℚ s →ₐ[ℚ] ℂ`, which `IsAlgClosed.lift` extends.

  Reference (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Field_nonempty_ringHom_complex_of_countable.lean>
-/
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Continuum

set_option autoImplicit false
set_option linter.style.haveILetI false

open Cardinal

universe u

namespace Field

theorem nonempty_ringHom_complex_of_countable (K : Type u) [Field K] [CharZero K] [Countable K] :
    Nonempty (K →+* ℂ) := by
  classical
  haveI : FaithfulSMul ℚ K :=
    (faithfulSMul_iff_algebraMap_injective ℚ K).2 (algebraMap ℚ K).injective
  haveI : FaithfulSMul ℚ ℂ :=
    (faithfulSMul_iff_algebraMap_injective ℚ ℂ).2 (algebraMap ℚ ℂ).injective

  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ

  have hct : #ℂ = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' (R := ℚ) _ ht
      mk_le_aleph0 (by rw [mk_complex]; exact aleph0_lt_continuum)

  have h1 : Cardinal.lift.{0} #s ≤ Cardinal.lift.{u} #t := by
    rw [← hct, mk_complex, lift_continuum]
    calc Cardinal.lift.{0} #s ≤ Cardinal.lift.{0} ℵ₀ := lift_le.2 mk_le_aleph0
      _ = ℵ₀ := lift_aleph0
      _ ≤ 𝔠 := aleph0_le_continuum
  obtain ⟨e⟩ := Cardinal.lift_mk_le'.1 h1

  have hind : AlgebraicIndependent ℚ (fun i : s => ((e i : t) : ℂ)) :=
    ht.1.comp e e.injective
  set A := Algebra.adjoin ℚ (Set.range ((↑) : s → K)) with hA
  let g : A →ₐ[ℚ] ℂ :=
    (MvPolynomial.aeval (fun i : s => ((e i : t) : ℂ))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g :=
    (algebraicIndependent_iff_injective_aeval.1 hind).comp hs.1.aevalEquiv.symm.injective

  haveI : Algebra.IsAlgebraic A K := hs.isAlgebraic
  letI : Algebra A ℂ := g.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree A ℂ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hg
  haveI : Module.IsTorsionFree A K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  exact ⟨(IsAlgClosed.lift (R := A) (S := K) (M := ℂ)).toRingHom⟩

end Field
