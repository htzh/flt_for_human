/-
  SET-AF71A consumer: the `q`-expansion/differential descent headline, executed at `Γ₁(2)`.

  **The zone.** `FLTForHuman/ModularCurve/QExpansionDifferentialLift.lean` closes with one row:

  * **A** —
    `ModularCurve.exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion`:
    for `Γ₁(M) ≤ Γ ≤ Γ₀(M)`, a coefficient map `ι₀ : AlgebraicClosure ℚ →+* ℂ` and a weight-`2` cusp
    form `f` whose `q`-coefficients all lie in `ι₀.range`, there is a Kähler differential `ω` on the
    Laurent base change `Fbar Γ = laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)` of
    the `q`-expansion function field such that the coefficient map of `qExpansionDiffAlong Fbar.val ω`
    is the `q`-expansion of `f`.

  The statement is `∃ ω` over a differential module of an `IntermediateField` of a Hahn series ring,
  quantified over an arbitrary level `M`, an arbitrary subgroup `Γ` between `Γ₁(M)` and `Γ₀(M)`, an
  arbitrary embedding of `AlgebraicClosure ℚ`, and an arbitrary cusp form with algebraic
  `q`-coefficients: nothing in it is executable until those are chosen. So the zone picks the
  smallest choice that makes every hypothesis inhabited and the conclusion computable:

  * `M = 2` and `Γ = Γ₁(2)` — the level is `2` (`NeZero 2` is the instance), and `Γ₁(2)` sits between
    `Γ₁(2)` (`le_rfl`) and `Γ₀(2)` (`CongruenceSubgroup.Gamma1_in_Gamma0`), so both hypotheses of the
    row are discharged by a proof, not assumed;
  * `ι₀ = iota` — `IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ` read as a ring hom, the standard
    embedding of the algebraic closure of `ℚ` into `ℂ`;
  * `f = f0 = 0` — the weight-`2` cusp form whose `q`-expansion is the *constant* `0`; a cusp form has
    no constant term, so `0` is the only such form. Its `q`-coefficients are `0 ∈ ι₀.range`
    (`hf0`), so `hf` is discharged too.

  Under that choice the row produces a genuine `ω` and the identity becomes computable: the right
  side is `qL (qExpansion 1 0)`, i.e. the `qL` spelling of the headline's right-hand side, and the
  coefficient at `n = 1` of the left side is read through `coeffMap` (`row_A`'s second conjunct is
  definitional: `coeffMap_coeff`) and evaluates to `0`.

  **Zone A** therefore runs: `obtain` the `ω` from the headline, rewrite the right side into `qL`
  (the `qL` consistency), read `coeffMap` at `n = 1`, and evaluate. No `#check`, no `sorry`: every
  line of the zone is a proof, and the `∃` is *used*, not merely stated.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.ModularCurve.QExpansionDifferentialLift

set_option autoImplicit false

noncomputable section

open UpperHalfPlane HahnSeries
open scoped MatrixGroups

namespace ModularCurveSetAF71AConsumer

/-- The embedding of the algebraic closure of `ℚ` into `ℂ`, as a ring hom: the coefficient map
`ι₀` at which the row is read. -/
noncomputable def iota : AlgebraicClosure ℚ →+* ℂ :=
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom

/-- The level: `Γ = Γ₁(2)`, a subgroup between `Γ₁(2)` and `Γ₀(2)`. -/
abbrev Gamma12 : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma1 2

/-- The pin's `Fbar Γ` at `Γ = Γ₁(2)`: the Laurent base change of the `q`-expansion function field of
`X(Γ₁(2))` to `AlgebraicClosure ℚ`. -/
abbrev F12 : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Gamma12)

/-- The weight-`2` cusp form for `Γ₁(2)` whose `q`-expansion is the constant `0`. -/
def f0 : CuspForm (Gamma12 : Subgroup (GL (Fin 2) ℝ)) 2 := 0

/-- Its `q`-coefficients lie in `iota.range`: they are all `0`. -/
theorem hf0 : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f0 : ℍ → ℂ) n ∈ iota.range := by
  intro n
  have h : ModularFormClass.qCoeff (⇑f0 : ℍ → ℂ) n = 0 := by
    simp [ModularFormClass.qCoeff, f0, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero]
  rw [h]
  exact ⟨0, map_zero iota⟩

/-- **Zone A.** The headline executed at `M = 2`, `Γ = Γ₁(2)`, `ι₀ = iota` and `f = 0`: the
differential `ω` exists, its coefficient map is the `q`-expansion written in `qL` form, that
coefficient map is read at `n = 1` through `coeffMap_coeff` (definitionally, hence `rfl`), and the
read value is `0`. -/
theorem row_A :
    ∃ ω : Ω[↥F12⁄AlgebraicClosure ℚ],
      ModularCurve.coeffMap iota (ModularCurve.qExpansionDiffAlong F12.val ω) =
        ModularCurve.QExpansionLift.qL (⇑f0 : ℍ → ℂ) ∧
      (ModularCurve.coeffMap iota (ModularCurve.qExpansionDiffAlong F12.val ω)).coeff 1 =
        iota ((ModularCurve.qExpansionDiffAlong F12.val ω).coeff 1) ∧
      (ModularCurve.coeffMap iota (ModularCurve.qExpansionDiffAlong F12.val ω)).coeff 1 = 0 := by
  obtain ⟨ω, hω⟩ :=
    ModularCurve.exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion
      2 Gamma12 le_rfl (CongruenceSubgroup.Gamma1_in_Gamma0 2) iota f0 hf0
  refine ⟨ω, by rw [hω], rfl, ?_⟩
  rw [hω]
  simp [f0, UpperHalfPlane.qExpansion_zero]

end ModularCurveSetAF71AConsumer
