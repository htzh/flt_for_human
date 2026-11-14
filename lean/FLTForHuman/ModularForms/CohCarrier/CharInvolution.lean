/-
  The character involution of the cohomology of `Γ_H(M)`.

  * `CohCarrier.jConjGammaH` — the conjugation `γ ↦ J γ J⁻¹` restricted to `Γ_H(M)`: it preserves
    `Γ_H(M)` because it preserves `Γ₀(M)` and fixes the character of an element at the same time.
  * `CohCarrier.charInvolution` — the pullback of a cohomology class along this involution, as a
    linear map; it is an involution (`charInvolution_charInvolution`) and therefore composes with
    itself to the identity.

  Transcribed from the pin's definition file (pinned `aa2d8b3`)
  `Definitions/Def_CohCarrier_CharInvolution.lean` (65 lines), at the pin's names.

  spec-pin: Definitions/Def_CohCarrier_CharInvolution.lean
-/
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularCurve.PeriodHomPair

set_option autoImplicit false

noncomputable section

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CohCarrier

section Level

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem jConjSL_mem_GammaH {A : SL(2, ℤ)} (hA : A ∈ GammaH M H) :
    ModularCurve.Period.jConjSL A ∈ GammaH M H := by
  obtain ⟨hA0, hAH⟩ := mem_GammaH_iff.mp hA
  rw [mem_GammaH_iff]
  refine ⟨ModularCurve.Period.jConjSL_mem_Gamma0 hA0, ?_⟩
  exact hAH

def jConjGammaH : ↥(GammaH M H) →* ↥(GammaH M H) where
  toFun γ := ⟨ModularCurve.Period.jConjSL (γ : SL(2, ℤ)), jConjSL_mem_GammaH M H γ.2⟩
  map_one' := Subtype.ext (by
    show ModularCurve.Period.jConjSL ((1 : ↥(GammaH M H)) : SL(2, ℤ)) = 1
    rw [OneMemClass.coe_one, map_one])
  map_mul' γ δ := Subtype.ext (by
    show ModularCurve.Period.jConjSL ((γ * δ : ↥(GammaH M H)) : SL(2, ℤ)) =
      ModularCurve.Period.jConjSL (γ : SL(2, ℤ)) * ModularCurve.Period.jConjSL (δ : SL(2, ℤ))
    rw [Subgroup.coe_mul, map_mul])

@[simp] theorem coe_jConjGammaH (γ : ↥(GammaH M H)) :
    ((jConjGammaH M H γ : ↥(GammaH M H)) : SL(2, ℤ)) = ModularCurve.Period.jConjSL (γ : SL(2, ℤ)) :=
  rfl

@[simp] theorem jConjGammaH_jConjGammaH (γ : ↥(GammaH M H)) :
    jConjGammaH M H (jConjGammaH M H γ) = γ :=
  Subtype.ext (ModularCurve.Period.jConjSL_jConjSL _)

variable (A : Type*) [AddCommGroup A]

def charInvolution (R : Type*) [Semiring R] [Module R A] : H1 M H A →ₗ[R] H1 M H A where
  toFun φ := φ.comp (MonoidHom.toAdditive (jConjGammaH M H))
  map_add' := by intro φ ψ; ext; rfl
  map_smul' := by intro r φ; ext; rfl

@[simp] theorem charInvolution_apply (R : Type*) [Semiring R] [Module R A] (φ : H1 M H A)
    (γ : Additive ↥(GammaH M H)) :
    charInvolution M H A R φ γ = φ (Additive.ofMul (jConjGammaH M H (Additive.toMul γ))) := rfl

theorem charInvolution_charInvolution (R : Type*) [Semiring R] [Module R A] (φ : H1 M H A) :
    charInvolution M H A R (charInvolution M H A R φ) = φ := by
  have h : ∀ x : Additive ↥(GammaH M H),
      MonoidHom.toAdditive (jConjGammaH M H) (MonoidHom.toAdditive (jConjGammaH M H) x) = x := by
    intro x
    show Additive.ofMul (jConjGammaH M H (jConjGammaH M H (Additive.toMul x))) = x
    rw [jConjGammaH_jConjGammaH]
    rfl
  calc charInvolution M H A R (charInvolution M H A R φ)
      = (charInvolution M H A R φ).comp (MonoidHom.toAdditive (jConjGammaH M H)) := rfl
    _ = (φ.comp (MonoidHom.toAdditive (jConjGammaH M H))).comp
          (MonoidHom.toAdditive (jConjGammaH M H)) := rfl
    _ = φ.comp ((MonoidHom.toAdditive (jConjGammaH M H)).comp
          (MonoidHom.toAdditive (jConjGammaH M H))) := AddMonoidHom.comp_assoc _ _ _
    _ = φ.comp (AddMonoidHom.id (Additive ↥(GammaH M H))) := by
          rw [show (MonoidHom.toAdditive (jConjGammaH M H)).comp
                (MonoidHom.toAdditive (jConjGammaH M H)) = AddMonoidHom.id _ from
              AddMonoidHom.ext h]
    _ = φ := AddMonoidHom.comp_id _

theorem charInvolution_comp_charInvolution (R : Type*) [Semiring R] [Module R A] :
    charInvolution M H A R ∘ₗ charInvolution M H A R = LinearMap.id :=
  LinearMap.ext (charInvolution_charInvolution M H A R)

end Level

end CohCarrier
