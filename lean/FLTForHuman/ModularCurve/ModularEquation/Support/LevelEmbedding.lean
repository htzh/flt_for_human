/-
  The level-`ℓ` nome substitution `ℚ((q)) → K((q))`.

  Coefficients are extended to `K` and the nome is raised to the `ℓ`-th power, so `j(q) ↦ j(q ^ ℓ)`
  and `j(q ^ ℓ) ↦ j(q ^ (ℓ * ℓ))`. The map is injective, which is what lets a vanishing read in
  `K((q))` come back to `ℚ((q))`. Composed with `evalAtJ` it is `evalAtJK`, the `X`-slot
  substitution every splitting hypothesis is stated with; `conj_succ_zero` is the other reading it
  needs, that the untwisted conjugate `conj 1` is `j(q)` itself.
-/

import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.PhiGen

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve

namespace PhiGen

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem coeffMap_jq : coeffMap (algebraMap ℚ K) jq = coeffEmb K jq := by
  ext k
  rfl

variable (ℓ : ℕ) [NeZero ℓ]

/-- The level-`ℓ` embedding `ℚ((q)) → K((q))`, the map that sends the nome `q` to `q ^ ℓ`. -/
def qEmbedT : LaurentSeries ℚ →+* LaurentSeries K :=
  (qExpand K ℓ).comp (coeffMap (algebraMap ℚ K))

private theorem qEmbedT_apply (x : LaurentSeries ℚ) :
    qEmbedT K ℓ x = qExpand K ℓ (coeffMap (algebraMap ℚ K) x) := rfl

/-- The level-`ℓ` embedding is injective. -/
theorem qEmbedT_injective : Function.Injective (qEmbedT K ℓ) :=
  (qEmbedT K ℓ).injective

/-- On the nome: `j(q)` becomes the `ℓ`-substituted series. -/
theorem qEmbedT_jq : qEmbedT K ℓ jq = qExpand K ℓ (coeffEmb K jq) := by
  rw [qEmbedT_apply, coeffMap_jq]

/-- Evaluation of an integer polynomial at `j(q ^ ℓ)` over `K((q))`: `qEmbedT` after `evalAtJ`, so
on `X` it is `j(q ^ ℓ)`. -/
def evalAtJK : Polynomial ℤ →+* LaurentSeries K :=
  (qEmbedT K ℓ).comp evalAtJ

theorem evalAtJK_def : evalAtJK K ℓ = (qEmbedT K ℓ).comp evalAtJ := rfl

@[simp]
theorem evalAtJK_X : evalAtJK K ℓ Polynomial.X = qExpand K ℓ (coeffEmb K jq) := by
  simp [evalAtJK, qEmbedT_jq]

/-- The level embedding is `coeffEmb` after the level change of the coefficients' nome. -/
theorem qEmbedT_eq_coeffEmb_qExpand (x : LaurentSeries ℚ) :
    qEmbedT K ℓ x = coeffEmb K (qExpand ℚ ℓ x) := by
  rw [qEmbedT_apply]
  exact (coeffEmb_qExpand K ℓ x).symm

variable [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

/-- On the level nome: `j(q ^ ℓ)` becomes the `(ℓ, 0)` conjugate `j(q ^ (ℓ * ℓ))`. -/
theorem qEmbedT_jqN : qEmbedT K ℓ (jqN ℓ) = conj ℓ ζ (0 : Fin (ℓ + 1)) := by
  rw [conj_zero, qEmbedT_apply, jqN, coeffMap_qExpand, coeffMap_jq, qExpand_qExpand]

/-- The untwisted conjugate is `j(q)`: the tame twist at coset `(1, 0)` is the identity. -/
theorem conj_succ_zero : conj ℓ ζ (0 : Fin ℓ).succ = (coeffEmb K jq) := by
  rw [conj_succ, Fin.val_zero, pow_zero, qTwist_one_apply]

end PhiGen

end ModularCurve
