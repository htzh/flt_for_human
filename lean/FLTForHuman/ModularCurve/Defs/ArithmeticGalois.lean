/-
  m1 — the `bar` layer of the pin's `ArithmeticGalois`: the arithmetic automorphism
  `arithmeticRingAut` of a base-changed Laurent field, its `SemilinearAut` packaging
  `arithmeticGalois`, and the two `bar` abbreviations `modularFunctionFieldBar` and
  `JZero`.

  The pin's `PicAction` section (the `SMul`/`DistribMulAction` of `L ≃ₐ[ℚ] L` on
  `Pic0`) and `JZero.torsionGaloisRep` (+ its two lemmas) are **deferred**. The
  decided home is two layers: the generic `SMul (SemilinearAut K F) (Pic0 K F)`
  and `SemilinearAut.torsionRep` in `AlgebraicCurve/Defs/SemilinearAut.lean`,
  and the modular `PicAction`/`torsionGaloisRep` wrappers here. They are out of
  the exchange cone (zero occurrences in the 82-node cone's proofs), so the
  restoration waits for the modular Hecke/Galois-rep layer
  (mc-retrospective §8 item 3).

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_ArithmeticGalois.lean` (140 lines), sections
  `ArithmeticGalois` and `ModularInstance`.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean
-/
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.Fields
import FLTForHuman.AlgebraicCurve.Defs.SemilinearAut
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

open IntermediateField HahnSeries AlgebraicCurve

namespace ModularCurve

section ArithmeticGalois

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

def arithmeticRingAut (σ : L ≃ₐ[ℚ] L) :
    (laurentBaseChange L F₀) ≃+* (laurentBaseChange L F₀) where
  toFun x := ⟨coeffMap (σ : L →+* L) (x : LaurentSeries L),
    coeffMap_mem_laurentBaseChange σ x.2⟩
  invFun x := ⟨coeffMap (σ.symm : L →+* L) (x : LaurentSeries L),
    coeffMap_mem_laurentBaseChange σ.symm x.2⟩
  left_inv x := Subtype.ext <| by
    show coeffMap (σ.symm : L →+* L) (coeffMap (σ : L →+* L) (x : LaurentSeries L))
      = (x : LaurentSeries L)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id L) (RingHom.ext fun a => σ.symm_apply_apply a)
        (x : LaurentSeries L),
      coeffMap_id]
  right_inv x := Subtype.ext <| by
    show coeffMap (σ : L →+* L) (coeffMap (σ.symm : L →+* L) (x : LaurentSeries L))
      = (x : LaurentSeries L)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id L) (RingHom.ext fun a => σ.apply_symm_apply a)
        (x : LaurentSeries L),
      coeffMap_id]
  map_mul' x y :=
    Subtype.ext (map_mul (coeffMap (σ : L →+* L)) (x : LaurentSeries L) (y : LaurentSeries L))
  map_add' x y :=
    Subtype.ext (map_add (coeffMap (σ : L →+* L)) (x : LaurentSeries L) (y : LaurentSeries L))

@[simp]
theorem coe_arithmeticRingAut_apply (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    (arithmeticRingAut F₀ σ x : LaurentSeries L) = coeffMap (σ : L →+* L) (x : LaurentSeries L) :=
  rfl

theorem arithmeticRingAut_algebraMap (σ : L ≃ₐ[ℚ] L) (a : L) :
    arithmeticRingAut F₀ σ (algebraMap L (laurentBaseChange L F₀) a)
      = algebraMap L (laurentBaseChange L F₀) (σ a) :=
  Subtype.ext (coeffMap_algebraMap (σ : L →+* L) a)

def arithmeticGalois : (L ≃ₐ[ℚ] L) →* SemilinearAut L (laurentBaseChange L F₀) where
  toFun σ := ⟨(arithmeticRingAut F₀ σ, σ.toRingEquiv), fun a => arithmeticRingAut_algebraMap F₀ σ a⟩
  map_one' := by
    refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext ?_) rfl)
    show coeffMap ((1 : L ≃ₐ[ℚ] L) : L →+* L) (x : LaurentSeries L) = (x : LaurentSeries L)
    rw [show ((1 : L ≃ₐ[ℚ] L) : L →+* L) = RingHom.id L from RingHom.ext fun _ => rfl,
      coeffMap_id]
  map_mul' σ τ := by
    refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext ?_) rfl)
    show coeffMap ((σ * τ : L ≃ₐ[ℚ] L) : L →+* L) (x : LaurentSeries L)
      = coeffMap (σ : L →+* L) (coeffMap (τ : L →+* L) (x : LaurentSeries L))
    rw [coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext fun _ => rfl) _

@[simp]
theorem toRingAut_arithmeticGalois (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.toRingAut (arithmeticGalois F₀ σ) = arithmeticRingAut F₀ σ :=
  rfl

@[simp]
theorem baseAut_arithmeticGalois (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.baseAut (arithmeticGalois F₀ σ) = σ.toRingEquiv :=
  rfl

theorem coe_arithmeticGalois_smul (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    ((arithmeticGalois F₀ σ • x : laurentBaseChange L F₀) : LaurentSeries L)
      = coeffMap (σ : L →+* L) (x : LaurentSeries L) :=
  rfl

end ArithmeticGalois

section ModularInstance

variable (N : ℕ) [NeZero N]

abbrev modularFunctionFieldBar : IntermediateField (AlgebraicClosure ℚ)
    (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)

abbrev JZero : Type _ :=
  Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)

end ModularInstance

end ModularCurve

end
