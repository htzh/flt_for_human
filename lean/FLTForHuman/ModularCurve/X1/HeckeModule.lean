/-
The X₁ Hecke-and-diamond input bundle `ModularCurve.HeckeDiamondInputsAll`, from
FLT's `Definitions/Def_ModularCurve_X1HeckeModule.lean` lines 58–65
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1HeckeModule.lean#L58-L65>).

Only that predicate is transcribed. The other 41 declarations of the pin file
(the `HeckeAlgOne`/`heckeGenOne`/`diamondGen` polynomial algebra, the
`heckeOperatorOneBar` operator, `HeckeDiamondCommuteBar`, the Hecke module and
the Tate-representation data) are the successor targets' surface and are
deliberately out of scope for `SET-X1-A` (see the topic file §3 item 4).
-/
import FLTForHuman.ModularCurve.X1.HeckeOperator
import FLTForHuman.ModularCurve.X1.Diamond

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open AlgebraicCurve

section Operators

variable (M : ℕ)

/-- The X₁ Hecke/diamond input bundle: the Hecke inputs for every prime `ℓ`, and
for every `d` coprime to `M` both a diamond automorphism and its base change to
`ℚ̄`. -/
def HeckeDiamondInputsAll : Prop :=
  (∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ) ∧
    ∀ d : ℕ, Nat.Coprime d M →
      (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ) ∧
        ∃ σ' : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M,
          IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) σ'

end Operators

end ModularCurve

end
