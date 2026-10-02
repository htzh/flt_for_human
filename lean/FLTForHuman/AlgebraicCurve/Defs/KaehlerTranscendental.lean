/-
The two Kähler-transcendence facts the canonical-divisor construction rests on,
after FLT's
`P2M/Sol/S_KaehlerDifferential_span_D_eq_top_of_transcendental.lean` (64 ln) and
`P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean` (63 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_KaehlerDifferential_span_D_eq_top_of_transcendental.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean>).

Both public headlines are spelled from their `Theorems/Thm_*` wrappers, which take
`(K : Type*)` explicitly and `{F : Type*}` implicitly.  The two `S_` files carry the
same private `exists_basis` prelude; the port writes it once.  The pin's
`p2m_open`/`p2m_export` scaffolding is replaced by `open Polynomial
KaehlerDifferential`; the notation `Ω[F⁄K]` is mathlib's unscoped
`KaehlerDifferential` notation.  No `P2M.Util` is needed.

Mathlib search negatives (recorded): there is no `KaehlerDifferential.D_eq_zero`,
no `D_ne_zero` and no `span_singleton_D`; the statements are bespoke and the proofs
are transcription over mathlib's `tensorKaehlerEquivOfFormallyEtale`,
`polynomialEquiv`, `Module.Basis.singleton`/`baseChange`/`map`, the
`Algebra.FormallyEtale.*` combinators and `RatFunc.algEquivOfTranscendental`.
-/
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally (SET-1 §3).
set_option linter.style.haveILetI false

noncomputable section

open Polynomial KaehlerDifferential

namespace KaehlerDifferential

namespace FF2

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {x : F} (hx : Transcendental K x)
  [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]

include hx in

private theorem exists_basis : ∃ b : Module.Basis Unit F Ω[F⁄K], b () = D K F x := by

  let e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({x} : Set F) := RatFunc.algEquivOfTranscendental x hx
  letI algKx : Algebra K[X] (IntermediateField.adjoin K ({x} : Set F)) := (e.toAlgHom.toRingHom.comp (algebraMap K[X] (RatFunc K))).toAlgebra
  letI algF : Algebra K[X] F := ((algebraMap (IntermediateField.adjoin K ({x} : Set F)) F).comp (algebraMap K[X] (IntermediateField.adjoin K ({x} : Set F)))).toAlgebra
  haveI : IsScalarTower K[X] (IntermediateField.adjoin K ({x} : Set F)) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K K[X] (IntermediateField.adjoin K ({x} : Set F)) := IsScalarTower.of_algebraMap_eq (fun c => by
    change _ = (e.toAlgHom.toRingHom.comp (algebraMap K[X] (RatFunc K))) (C c)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_algHom]
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K), AlgEquiv.commutes])
  haveI : IsScalarTower K K[X] F := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply K (IntermediateField.adjoin K ({x} : Set F)) F, IsScalarTower.algebraMap_apply K[X] (IntermediateField.adjoin K ({x} : Set F)) F,
      ← IsScalarTower.algebraMap_apply K K[X] (IntermediateField.adjoin K ({x} : Set F))])

  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])
  haveI : Algebra.FormallyEtale K[X] (IntermediateField.adjoin K ({x} : Set F)) :=
    Algebra.FormallyEtale.of_equiv (R := K[X]) (A := RatFunc K) { e with commutes' := fun _ => rfl }
  haveI : Algebra.FormallyEtale (IntermediateField.adjoin K ({x} : Set F)) F := Algebra.FormallyEtale.of_isSeparable (IntermediateField.adjoin K ({x} : Set F)) F
  haveI : Algebra.FormallyEtale K[X] F := Algebra.FormallyEtale.comp K[X] (IntermediateField.adjoin K ({x} : Set F)) F

  let b₀ : Module.Basis Unit K[X] Ω[K[X]⁄K] :=
    (Module.Basis.singleton Unit K[X]).map (polynomialEquiv K).symm
  have hb₀ : b₀ () = D K K[X] X := by simp [b₀]
  let ψ := tensorKaehlerEquivOfFormallyEtale K K[X] F
  refine ⟨(b₀.baseChange F).map ψ, ?_⟩
  have hX : algebraMap K[X] F X = x := by
    change algebraMap (IntermediateField.adjoin K ({x} : Set F)) F (e (algebraMap K[X] (RatFunc K) X)) = x
    rw [RatFunc.algebraMap_X]
    exact RatFunc.algEquivOfTranscendental_X x hx
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb₀, ψ,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D, hX]

end FF2

theorem span_D_eq_top_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) = ⊤ := by
  obtain ⟨b, hb⟩ := FF2.exists_basis hx
  have h := b.span_eq
  rwa [show Set.range b = {KaehlerDifferential.D K F x} by ext ω; simp [Set.range_unique, hb]] at h

theorem D_ne_zero_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    KaehlerDifferential.D K F x ≠ 0 := by
  obtain ⟨b, hb⟩ := FF2.exists_basis hx
  simpa [hb] using b.ne_zero ()

end KaehlerDifferential

namespace AlgebraicCurve

/-! ## `kaehlerRankOne_of_transcendental`

The Kähler module of a function field is free of rank one, after FLT's
`P2M/Sol/S_AlgebraicCurve_kaehlerRankOne_of_transcendental.lean` (73 ln).  The
pin's `S12Kaehler` helper block is transcribed `private`; only the wrapper
statement `AlgebraicCurve.kaehlerRankOne_of_transcendental` is public. -/

section KaehlerRankOne

open Module Polynomial KaehlerDifferential

private def kaehlerPolynomialBasis (K : Type*) [Field K] : Basis Unit K[X] Ω[K[X]⁄K] :=
  (Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

private def kaehlerRatFuncBasis (K : Type*) [Field K] : Basis Unit (RatFunc K) Ω[(RatFunc K)⁄K] :=
  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])
  ((kaehlerPolynomialBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

private def kaehlerOfRatFuncTowerBasis (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F] :
    Basis Unit F Ω[F⁄K] :=
  haveI : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  ((kaehlerRatFuncBasis K).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (RatFunc K) F)

private theorem kaehlerRankOne_of_ratFuncTower (K : Type*) [Field K] {F : Type*} [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] :
    Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 :=
  ⟨Module.Free.of_basis (kaehlerOfRatFuncTowerBasis K),
    (Module.finrank_eq_card_basis (kaehlerOfRatFuncTowerBasis K)).trans (by simp)⟩

/-- **The Kähler module of a function field is free of rank one.**
Verbatim from `Theorems/Thm_AlgebraicCurve_kaehlerRankOne_of_transcendental.lean`. -/
theorem kaehlerRankOne_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :
    Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 := by
  haveI := hsep
  let e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({x} : Set F) :=
    RatFunc.algEquivOfTranscendental x htr
  letI : Algebra (RatFunc K) F :=
    ((algebraMap (IntermediateField.adjoin K ({x} : Set F)) F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : (IntermediateField.adjoin K ({x} : Set F)) →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F)
          (algebraMap (IntermediateField.adjoin K ({x} : Set F)) F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap (IntermediateField.adjoin K ({x} : Set F)) F (e (e.symm a)) =
      algebraMap (IntermediateField.adjoin K ({x} : Set F)) F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap (IntermediateField.adjoin K ({x} : Set F)) F
        (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact kaehlerRankOne_of_ratFuncTower K

end KaehlerRankOne

end AlgebraicCurve
