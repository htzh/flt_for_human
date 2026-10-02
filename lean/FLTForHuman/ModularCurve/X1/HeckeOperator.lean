/-
X₁'s Hecke degeneracy maps on the base-changed function field, after FLT's
`Definitions/Def_ModularCurve_X1HeckeOperator.lean` lines 59–228
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1HeckeOperator.lean>).

The pin's `PrivateSupply` block (lines 14–57) is **not** transcribed: its four
lemmas `coeffMap_qExpand₁`, `coeffEmb_qExpand₁`, `laurentBaseChange_mono₁`,
`qExpand_mem_laurentBaseChange₁` are byte-for-byte the level-H prelude already
public in `ModularCurve/Defs/Laurent.lean` (`coeffMap_qExpand`, `coeffEmb_qExpand`,
`laurentBaseChange_mono`, `qExpand_mem_laurentBaseChange`). The pin's
`section ModularInstance` examples (lines 234–240) are typecheck-only and dropped.
-/
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.AlgebraicCurve.Defs.Correspondence

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace ModularCurve

open AlgebraicCurve IntermediateField HahnSeries

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (M ℓ : ℕ) [NeZero ℓ]

section DegeneracyMaps

variable (L) in

/-- The identity inclusion `X₁(M) ↪ X₁(M) ∩ X₀(Mℓ)`: the α degeneracy map. -/
def heckeAlphaOneBar :
    laurentBaseChange L (x1FunctionField M) →ₐ[L]
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)) :=
  IntermediateField.inclusion (laurentBaseChange_mono L (x1FunctionFieldC_le_x1x0 ℚ M (M * ℓ)))

omit [NeZero ℓ] in
@[simp]
theorem coe_heckeAlphaOneBar (x : laurentBaseChange L (x1FunctionField M)) :
    (heckeAlphaOneBar L M ℓ x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

omit [NeZero ℓ] in

theorem heckeAlphaOneBar_eq_inclusion
    (h : laurentBaseChange L (x1FunctionField M) ≤ laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))) :
    heckeAlphaOneBar L M ℓ = IntermediateField.inclusion h :=
  rfl

/-- The β degeneracy map lands in `X₁(M) ∩ X₀(Mℓ)` precisely when `q ↦ q^ℓ`
preserves `X₁(M)`. -/
def HeckeBetaOneDefined : Prop :=
  ∀ y ∈ x1FunctionField M, qExpand ℚ ℓ y ∈ x1x0FunctionFieldC ℚ M (M * ℓ)

variable (L) in

def heckeBetaOneBarRingHomOf (h : HeckeBetaOneDefined M ℓ) :
    laurentBaseChange L (x1FunctionField M) →+*
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChange ℓ h x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)

variable (L) in

/-- The β degeneracy map `q ↦ q^ℓ`, when it is defined. -/
def heckeBetaOneBarOf (h : HeckeBetaOneDefined M ℓ) :
    laurentBaseChange L (x1FunctionField M) →ₐ[L]
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)) :=
  { heckeBetaOneBarRingHomOf L M ℓ h with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

@[simp]
theorem coe_heckeBetaOneBarOf (h : HeckeBetaOneDefined M ℓ) (x : laurentBaseChange L (x1FunctionField M)) :
    (heckeBetaOneBarOf L M ℓ h x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

open Classical in
variable (L) in

/-- The β degeneracy map, falling back to α when `q ↦ q^ℓ` does not preserve
`X₁(M)`. -/
def heckeBetaOneBar :
    laurentBaseChange L (x1FunctionField M) →ₐ[L]
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)) :=
  if h : HeckeBetaOneDefined M ℓ then heckeBetaOneBarOf L M ℓ h else heckeAlphaOneBar L M ℓ

theorem heckeBetaOneBar_eq (h : HeckeBetaOneDefined M ℓ) :
    (heckeBetaOneBar L M ℓ) = heckeBetaOneBarOf L M ℓ h := by
  rw [heckeBetaOneBar, dite_eq_left h]

theorem heckeBetaOneBar_of_not (h : ¬ HeckeBetaOneDefined M ℓ) :
    (heckeBetaOneBar L M ℓ) = heckeAlphaOneBar L M ℓ := by
  rw [heckeBetaOneBar, dite_eq_right h]

theorem coe_heckeBetaOneBar (h : HeckeBetaOneDefined M ℓ) (x : laurentBaseChange L (x1FunctionField M)) :
    (heckeBetaOneBar L M ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) := by
  rw [heckeBetaOneBar_eq M ℓ h, coe_heckeBetaOneBarOf]

end DegeneracyMaps

section HeckePic0OneBar

variable (L) in

def HeckeAlphaOneBarIntegral : Prop :=
  (heckeAlphaOneBar L M ℓ).toRingHom.IsIntegral

variable (L) in

def HeckeBetaOneBarIntegral : Prop :=
  (heckeBetaOneBar L M ℓ).toRingHom.IsIntegral

variable {M ℓ}
variable (hα : HeckeAlphaOneBarIntegral L M ℓ) (hβ : HeckeBetaOneBarIntegral L M ℓ)
variable [HasPrincipalDivisors L (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)))]

/-- The Hecke correspondence on divisors, `β* α_*`. -/
def heckeDivOneBar :
    Divisor L (laurentBaseChange L (x1FunctionField M)) →+
      Divisor L (laurentBaseChange L (x1FunctionField M)) :=
  Divisor.correspondence (heckeBetaOneBar L M ℓ) (heckeAlphaOneBar L M ℓ) hβ hα

def heckePic0OneBar
    (hFI : FundamentalIdentityAlong L (heckeBetaOneBar L M ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaOneBar L M ℓ))
    (hN : NormFormulaAlong L (heckeAlphaOneBar L M ℓ) hfin) :
    Pic0 L (laurentBaseChange L (x1FunctionField M)) →+
      Pic0 L (laurentBaseChange L (x1FunctionField M)) :=
  Pic0.correspondence (heckeBetaOneBar L M ℓ) (heckeAlphaOneBar L M ℓ) hβ hα hFI hfin hN

def heckeDivOneBarTranspose :
    Divisor L (laurentBaseChange L (x1FunctionField M)) →+
      Divisor L (laurentBaseChange L (x1FunctionField M)) :=
  Divisor.correspondence (heckeAlphaOneBar L M ℓ) (heckeBetaOneBar L M ℓ) hα hβ

def heckePic0OneBarTranspose
    (hFI : FundamentalIdentityAlong L (heckeAlphaOneBar L M ℓ) hα)
    (hfin : FiniteAlong L (heckeBetaOneBar L M ℓ))
    (hN : NormFormulaAlong L (heckeBetaOneBar L M ℓ) hfin) :
    Pic0 L (laurentBaseChange L (x1FunctionField M)) →+
      Pic0 L (laurentBaseChange L (x1FunctionField M)) :=
  Pic0.correspondence (heckeAlphaOneBar L M ℓ) (heckeBetaOneBar L M ℓ) hα hβ hFI hfin hN

end HeckePic0OneBar

section Total

variable (L)

/-- The bundle of inputs making the X₁ Hecke operator well defined at `(M, ℓ)`. -/
def HeckeInputsOneAlong : Prop :=
  ∃ (_ : HeckeBetaOneDefined M ℓ) (_ : HeckeAlphaOneBarIntegral L M ℓ) (hβ : HeckeBetaOneBarIntegral L M ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ))))
    (hfin : FiniteAlong L (heckeAlphaOneBar L M ℓ)),
    FundamentalIdentityAlong L (heckeBetaOneBar L M ℓ) hβ ∧
      NormFormulaAlong L (heckeAlphaOneBar L M ℓ) hfin

open Classical in

/-- The X₁ Hecke operator on `Pic⁰`, junk value `0` when the inputs are absent. -/
def heckeOperatorOneAlong :
    Pic0 L (laurentBaseChange L (x1FunctionField M)) →+
      Pic0 L (laurentBaseChange L (x1FunctionField M)) :=
  if h : HeckeInputsOneAlong L M ℓ then
    haveI := h.snd.snd.snd.fst
    heckePic0OneBar h.snd.fst h.snd.snd.fst h.snd.snd.snd.snd.snd.1 h.snd.snd.snd.snd.fst
      h.snd.snd.snd.snd.snd.2
  else 0

variable {L M ℓ}

theorem heckeInputsOneAlong_intro (h0 : HeckeBetaOneDefined M ℓ)
    (hα : HeckeAlphaOneBarIntegral L M ℓ) (hβ : HeckeBetaOneBarIntegral L M ℓ)
    [hP : HasPrincipalDivisors L (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaOneBar L M ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaOneBar L M ℓ))
    (hN : NormFormulaAlong L (heckeAlphaOneBar L M ℓ) hfin) : HeckeInputsOneAlong L M ℓ :=
  ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩

theorem HeckeInputsOneAlong.betaOneDefined (h : HeckeInputsOneAlong L M ℓ) : HeckeBetaOneDefined M ℓ :=
  h.fst

theorem heckeOperatorOneAlong_eq (h0 : HeckeBetaOneDefined M ℓ)
    (hα : HeckeAlphaOneBarIntegral L M ℓ) (hβ : HeckeBetaOneBarIntegral L M ℓ)
    [HasPrincipalDivisors L (laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaOneBar L M ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaOneBar L M ℓ))
    (hN : NormFormulaAlong L (heckeAlphaOneBar L M ℓ) hfin) :
    heckeOperatorOneAlong L M ℓ = heckePic0OneBar hα hβ hFI hfin hN := by
  have h : HeckeInputsOneAlong L M ℓ := heckeInputsOneAlong_intro h0 hα hβ hFI hfin hN
  rw [heckeOperatorOneAlong, dite_eq_left h]

theorem heckeOperatorOneAlong_of_not (h : ¬ HeckeInputsOneAlong L M ℓ) :
    heckeOperatorOneAlong L M ℓ = 0 := by
  rw [heckeOperatorOneAlong, dite_eq_right h]

end Total

end ModularCurve

end
