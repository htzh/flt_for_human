/-
  m1 — the total Hecke operator with its junk branch.

  `HeckeInputsAlong` bundles the five inputs the correspondence needs at a pair
  `(N, ℓ)`; `heckeOperatorAlong` is the operator when the bundle is inhabited and
  `0` otherwise (the `if h : … then … else 0` with `open Classical`). The pin
  splits these across `Def_ModularCurve_HeckeOperatorTotal.lean` (54) and
  `Def_ModularCurve_HeckeInputsAll.lean` (13); the port keeps them in one module.

  FLT provenance, pinned `aa2d8b3`:
  * `Definitions/Def_ModularCurve_HeckeOperatorTotal.lean`
  * `Definitions/Def_ModularCurve_HeckeInputsAll.lean`
-/
import FLTForHuman.ModularCurve.Defs.DegeneracyTower
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

def HeckeInputsAlong : Prop :=
  ∃ (_ : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ))))
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ)),
    FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ ∧
      NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin

open Classical in

def heckeOperatorAlong :
    Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  if h : HeckeInputsAlong L N ℓ then
    haveI := h.snd.snd.fst
    heckePic0Bar h.fst h.snd.fst h.snd.snd.snd.snd.1 h.snd.snd.snd.fst h.snd.snd.snd.snd.2
  else 0

variable {L N ℓ}

theorem heckeInputsAlong_intro (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    [hP : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ))
    (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin) : HeckeInputsAlong L N ℓ :=
  ⟨hα, hβ, hP, hfin, hFI, hN⟩

theorem heckeOperatorAlong_eq (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaBar L N ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ))
    (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin) :
    heckeOperatorAlong L N ℓ = heckePic0Bar hα hβ hFI hfin hN := by
  have h : HeckeInputsAlong L N ℓ := heckeInputsAlong_intro hα hβ hFI hfin hN
  rw [heckeOperatorAlong, dite_eq_left h]

theorem heckeOperatorAlong_of_not (h : ¬ HeckeInputsAlong L N ℓ) :
    heckeOperatorAlong L N ℓ = 0 := by
  rw [heckeOperatorAlong, dite_eq_right h]

def HeckeInputsAll (N : ℕ) [NeZero N] : Prop :=
  ∀ ℓ : Nat.Primes,
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ

end ModularCurve

end
