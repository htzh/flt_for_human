/-
The X₁ Hecke-and-diamond input bundle `ModularCurve.HeckeDiamondInputsAll` and the
`ℤ`-linear Hecke operator `ModularCurve.heckeOperatorOneBar` on `J₁(M)`, from FLT's
`Definitions/Def_ModularCurve_X1HeckeModule.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1HeckeModule.lean>):
the bundle is pin 58–65, the operator pin 36–43.

The rest of the pin file (the `HeckeAlgOne`/`heckeGenOne`/`diamondGen` polynomial
algebra, `HeckeDiamondCommuteBar`, the Hecke module and the Tate-representation data)
is the successor targets' surface and is not transcribed here.

`heckeOperatorOneBar` is the `Module.End ℤ (JOne M)` wrapper of the ported
`heckeOperatorOneAlong`, which is total: it is `0` when `HeckeInputsOneAlong` fails.
The same wrapper shape is already used for the abstract `Bar` family in
`ModularCurve/Defs/HeckeModule.lean` (`heckeOperatorBar`).

  spec-pin: Definitions/Def_ModularCurve_X1HeckeModule.lean

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1HeckeModule.lean
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

/-- The `ℓ`-th Hecke operator on `J₁(M)`, as a `ℤ`-linear endomorphism: the
`Module.End ℤ` wrapper of `heckeOperatorOneAlong`. -/
def heckeOperatorOneBar (ℓ : Nat.Primes) : Module.End ℤ (JOne M) :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  (heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ).toIntLinearMap

theorem heckeOperatorOneBar_apply (ℓ : Nat.Primes) (x : JOne M) :
    heckeOperatorOneBar M ℓ x =
      (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ x) :=
  rfl

end Operators

end ModularCurve

end
