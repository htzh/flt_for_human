/-
The `X_H(M)` Hecke degeneracy maps on the base-changed function field, after FLT's
`Definitions/Def_ModularCurve_XHHeckeOperator.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XHHeckeOperator.lean>).

The pin's `PrivateSupply` block (lines 14–57) is **not** transcribed: its four
lemmas `coeffMap_qExpandH`, `coeffEmb_qExpandH`, `laurentBaseChange_monoH`,
`qExpand_mem_laurentBaseChangeH` are byte-for-byte the level-H prelude already
public in `ModularCurve/Defs/Laurent.lean` (`coeffMap_qExpand`, `coeffEmb_qExpand`,
`laurentBaseChange_mono`, `qExpand_mem_laurentBaseChange`). The pin's
`HeckePic0HBar` block (`heckeDivHBar`, `heckePic0HBar`, the transposes) and its
`Total` block's `heckeOperatorHAlong` are off this cone (0 references in the four
`S_` files) and deferred to the successor Jacobian topics; this module lands the
`α`/`β` maps, the two integrality predicates and the seven-input bundle
`HeckeInputsHAlong` plus its two accessors. The pin's `section ModularInstance`
examples (lines 233–245) are typecheck-only and dropped.

`HeckeInputsHAlong` is **not** the ported `ModularCurve.HeckeInputsAlong`
(`ModularCurve/Defs/HeckeTotal.lean`): the latter is stated on
`modularFunctionFieldFull`/`heckeAlphaBar`, this one on
`xHTopFunctionFieldC`/`heckeAlphaHBar`. Same type (`Prop`), different proposition;
the pin's body is transcribed verbatim.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XHHeckeOperator.lean
-/
import FLTForHuman.ModularCurve.XH.FunctionField
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.AlgebraicCurve.Defs.Correspondence

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace ModularCurve

open AlgebraicCurve IntermediateField HahnSeries

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

section DegeneracyMaps

variable (L) in

/-- The identity inclusion `X_H(M) ↪ X_H(M) ∩ X₀(Mℓ)`: the α degeneracy map. -/
def heckeAlphaHBar :
    laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  IntermediateField.inclusion (laurentBaseChange_mono L (xHFunctionFieldC_le_top ℚ M H (M * ℓ)))

omit [NeZero ℓ] in
@[simp]
theorem coe_heckeAlphaHBar (x : laurentBaseChange L (xHFunctionField M H)) :
    (heckeAlphaHBar L M H ℓ x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

omit [NeZero ℓ] in

theorem heckeAlphaHBar_eq_inclusion
    (h : laurentBaseChange L (xHFunctionField M H) ≤
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) :
    heckeAlphaHBar L M H ℓ = IntermediateField.inclusion h :=
  rfl

/-- The β degeneracy map lands in `X_H(M) ∩ X₀(Mℓ)` precisely when `q ↦ q^ℓ`
preserves `X_H(M)`. -/
def HeckeBetaHDefined : Prop :=
  ∀ y ∈ xHFunctionField M H, qExpand ℚ ℓ y ∈ xHTopFunctionFieldC ℚ M H (M * ℓ)

variable (L) in

def heckeBetaHBarRingHomOf (h : HeckeBetaHDefined M H ℓ) :
    laurentBaseChange L (xHFunctionField M H) →+*
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChange ℓ h x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)

variable (L) in

/-- The β degeneracy map `q ↦ q^ℓ`, when it is defined. -/
def heckeBetaHBarOf (h : HeckeBetaHDefined M H ℓ) :
    laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  { heckeBetaHBarRingHomOf L M H ℓ h with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

@[simp]
theorem coe_heckeBetaHBarOf (h : HeckeBetaHDefined M H ℓ)
    (x : laurentBaseChange L (xHFunctionField M H)) :
    (heckeBetaHBarOf L M H ℓ h x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

open Classical in
variable (L) in

/-- The β degeneracy map, falling back to α when `q ↦ q^ℓ` does not preserve
`X_H(M)`. -/
def heckeBetaHBar :
    laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  if h : HeckeBetaHDefined M H ℓ then heckeBetaHBarOf L M H ℓ h else heckeAlphaHBar L M H ℓ

theorem heckeBetaHBar_eq (h : HeckeBetaHDefined M H ℓ) :
    (heckeBetaHBar L M H ℓ) = heckeBetaHBarOf L M H ℓ h := by
  rw [heckeBetaHBar, dite_eq_left h]

theorem heckeBetaHBar_of_not (h : ¬ HeckeBetaHDefined M H ℓ) :
    (heckeBetaHBar L M H ℓ) = heckeAlphaHBar L M H ℓ := by
  rw [heckeBetaHBar, dite_eq_right h]

theorem coe_heckeBetaHBar (h : HeckeBetaHDefined M H ℓ)
    (x : laurentBaseChange L (xHFunctionField M H)) :
    (heckeBetaHBar L M H ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) := by
  rw [heckeBetaHBar_eq M H ℓ h, coe_heckeBetaHBarOf]

end DegeneracyMaps

section Integrality

variable (L) in

/-- The α degeneracy map is integral. -/
def HeckeAlphaHBarIntegral : Prop :=
  (heckeAlphaHBar L M H ℓ).toRingHom.IsIntegral

variable (L) in

/-- The β degeneracy map is integral. -/
def HeckeBetaHBarIntegral : Prop :=
  (heckeBetaHBar L M H ℓ).toRingHom.IsIntegral

end Integrality

section Total

variable (L)

/-- The bundle of inputs making the `X_H(M)` Hecke operator well defined at
`(M, H, ℓ)`. -/
def HeckeInputsHAlong : Prop :=
  ∃ (_ : HeckeBetaHDefined M H ℓ) (_ : HeckeAlphaHBarIntegral L M H ℓ) (hβ : HeckeBetaHBarIntegral L M H ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))))
    (hfin : FiniteAlong L (heckeAlphaHBar L M H ℓ)),
    FundamentalIdentityAlong L (heckeBetaHBar L M H ℓ) hβ ∧
      NormFormulaAlong L (heckeAlphaHBar L M H ℓ) hfin

variable {L M H ℓ}

theorem heckeInputsHAlong_intro (h0 : HeckeBetaHDefined M H ℓ)
    (hα : HeckeAlphaHBarIntegral L M H ℓ) (hβ : HeckeBetaHBarIntegral L M H ℓ)
    [hP : HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaHBar L M H ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaHBar L M H ℓ))
    (hN : NormFormulaAlong L (heckeAlphaHBar L M H ℓ) hfin) : HeckeInputsHAlong L M H ℓ :=
  ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩

theorem HeckeInputsHAlong.betaHDefined (h : HeckeInputsHAlong L M H ℓ) : HeckeBetaHDefined M H ℓ :=
  h.fst

end Total

end ModularCurve

end
