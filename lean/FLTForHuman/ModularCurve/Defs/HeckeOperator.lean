/-
  m1 — the Hecke correspondence vocabulary: the two degeneracy maps `heckeAlphaBar`
  (inclusion) and `heckeBetaBar` (`q ↦ q ^ ℓ`), the correspondence `heckeDivBar` on
  divisors and `heckePic0Bar` on `Pic0`, and their transposes.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_HeckeOperator.lean` (191 lines).
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperator.lean

  The pin's private prelude is four supply lemmas. Two dedup to the ported public
  `Defs/Laurent.lean` (`coeffMap_qExpand`, `coeffEmb_qExpand`); the two generic
  ones (`laurentBaseChange_mono`, `qExpand_mem_laurentBaseChange`) are **not**
  ported in this generic form, and they are themselves `Theorems/` wrapper targets
  (`Thm_ModularCurve_{laurentBaseChange_mono,qExpand_mem_laurentBaseChange}.lean`).
  They are written once here, **publicly**, from those wrappers (binders
  verbatim) — one home for a lemma the pin writes twice privately
  (`laurentBaseChange_mono'` in `HeckeOperator`, `laurentBaseChange_mono''` in
  `DegeneracyTower`). The workspace rule forbids editing `Defs/Laurent.lean`, so
  they are not moved there.

  The pin's `section ModularInstance` carries two `example`s (typecheck-only, no
  declaration); they are dropped (not API).
-/
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.Fields
import FLTForHuman.AlgebraicCurve.Defs.Correspondence

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField HahnSeries

namespace ModularCurve

section PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]

theorem laurentBaseChange_mono (L : Type*) [Field L] [Algebra ℚ L]
    {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) :
    laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem qExpand_mem_laurentBaseChange {L : Type*} [Field L] [Algebra ℚ L]
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ) [NeZero n]
    {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L n x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [← coeffEmb_qExpand]
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

section DegeneracyMapsBar

variable (L) in

def heckeAlphaBar :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
  IntermediateField.inclusion
    (laurentBaseChange_mono L (full_degeneracy_le (dvd_mul_right N ℓ)))

@[simp]
theorem coe_heckeAlphaBar (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (heckeAlphaBar L N ℓ x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

variable (L) in

def heckeBetaBarRingHom :
    laurentBaseChange L (modularFunctionFieldFull N) →+*
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L),
    qExpand_mem_laurentBaseChange ℓ
      (fun y hy => full_degeneracy_map_le (N := N) ℓ ⟨y, hy, rfl⟩) x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)

omit [NeZero N] in
@[simp]
theorem coe_heckeBetaBarRingHom (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (heckeBetaBarRingHom L N ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

variable (L) in

def heckeBetaBar :
    laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull (N * ℓ)) :=
  { heckeBetaBarRingHom L N ℓ with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

theorem heckeAlphaBar_eq_inclusion
    (h : laurentBaseChange L (modularFunctionFieldFull N)
      ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :
    heckeAlphaBar L N ℓ = IntermediateField.inclusion h :=
  rfl

omit [NeZero N] in
@[simp]
theorem coe_heckeBetaBar (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (heckeBetaBar L N ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

end DegeneracyMapsBar

section HeckePic0Bar

variable (L) in

def HeckeAlphaBarIntegral : Prop :=
  (heckeAlphaBar L N ℓ).toRingHom.IsIntegral

variable (L) in

def HeckeBetaBarIntegral : Prop :=
  (heckeBetaBar L N ℓ).toRingHom.IsIntegral

variable {N ℓ}
variable (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
variable [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]

def heckeDivBar :
    Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  Divisor.correspondence (heckeBetaBar L N ℓ) (heckeAlphaBar L N ℓ) hβ hα

def heckePic0Bar
    (hFI : FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ))
    (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin) :
    Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  Pic0.correspondence (heckeBetaBar L N ℓ) (heckeAlphaBar L N ℓ) hβ hα hFI hfin hN

end HeckePic0Bar

section Transpose

variable {N ℓ}
variable (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
variable [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]

def heckeDivBarTranspose :
    Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  Divisor.correspondence (heckeAlphaBar L N ℓ) (heckeBetaBar L N ℓ) hα hβ

def heckePic0BarTranspose
    (hFI : FundamentalIdentityAlong L (heckeAlphaBar L N ℓ) hα)
    (hfin : FiniteAlong L (heckeBetaBar L N ℓ))
    (hN : NormFormulaAlong L (heckeBetaBar L N ℓ) hfin) :
    Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  Pic0.correspondence (heckeAlphaBar L N ℓ) (heckeBetaBar L N ℓ) hα hβ hFI hfin hN

end Transpose

end ModularCurve

end
