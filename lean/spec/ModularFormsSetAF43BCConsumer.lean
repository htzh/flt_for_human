/-
  Cross-module wire test for WORKORDER-AF43BC (a `spec/` probe, not a library module).

  Two executed zones, no `#check`: deleting either imported module makes the probe fail.

  * Zone 1 — the `Γ₁` cusp-space structure: `U_2` and `U_3` on a `Γ_H(6)`-cusp form commute
    (`CuspForm.heckeULinH_comm` read at `q = 2`, `q' = 3`), read at the module's own `qCoeff`, and
    a primitive `Γ₁(4)`-form has `q`-coefficient `qCoeff g 2 = 0`
    (`CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div` at `q = 2`, `q ∣ M / q`).
  * Zone 2 — the weight-four diamond divisor sums: the headline at `M = 3`, read at `γ = 1`, the
    diamond class of `1`; the `Γ₀(3)`-slash transformation there is the identity on each `R c`.

  The order's zone-2 suggestion asked for the `Γ₀(3)`-slash at `γ = 1` "the diamond class of `1`";
  typed as `((1 : SL(2, ℤ)) : GL (Fin 2) ℝ)` and then *reduced*, since
  `CohCarrier.gamma0Units 3 ⟨1, _⟩ = 1`: this is the recorded substitution (the raw statement with
  the untouched unit factor is not typeable without first fixing the `Gamma0` proof argument).
-/
import FLTForHuman.ModularForms.Gamma1CuspStructure
import FLTForHuman.ModularForms.CohCarrier.DiamondDivisorSum

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

/-- Zone 1: `U_2 ∘ U_3 = U_3 ∘ U_2` on a `Γ_H(6)`-cusp form, at the module's own `qCoeff`, together
with the primitive-form vanishing of the `q`-th coefficient. -/
theorem zone1 (k : ℤ) (f : CuspForm (CohCarrier.GammaH 6 ⊤) k)
    (g : CuspForm (CongruenceSubgroup.Gamma1 4) k)
    (ε' : DirichletCharacter ℂ (4 / 2))
    (hg : CuspForm.IsPrimitiveForm
      (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd (show 2 ∣ 4 by norm_num)) ε') g) :
    (∀ n : ℕ, ModularFormClass.qCoeff (CuspForm.heckeULinH k 2 (CuspForm.heckeULinH k 3 f)) n
        = ModularFormClass.qCoeff (CuspForm.heckeULinH k 3 (CuspForm.heckeULinH k 2 f)) n) ∧
      ModularFormClass.qCoeff g 2 = 0 := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [CuspForm.heckeULinH_comm 6 ⊤ k Nat.prime_two (by norm_num) Nat.prime_three (by norm_num) f]
  · exact CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div 4 k Nat.prime_two
      (by norm_num) (by norm_num) ε' g hg

/-- Zone 2: the weight-four partial divisor sums at `M = 3`, read at `γ = 1` (the diamond class of
`1`), where the `Γ₀(3)`-slash is the identity. -/
theorem zone2 :
    ∃ R : (ZMod 3)ˣ → ModularForm (CongruenceSubgroup.Gamma1 3 : Subgroup (GL (Fin 2) ℝ)) 4,
      (∀ c : (ZMod 3)ˣ, ModularCurve.IsIntegralQExp (R c)
        (PowerSeries.mk fun n : ℕ => if n = 0 then 0 else
          ∑ d ∈ n.divisors,
            if ((n / d : ℕ) : ZMod 3) = (c : ZMod 3) ∨ ((n / d : ℕ) : ZMod 3) = -(c : ZMod 3)
            then (d : ℤ) ^ 3 else 0)) ∧
      (∀ c : (ZMod 3)ˣ,
        ((⇑(R c) : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] (((1 : SL(2, ℤ)) : GL (Fin 2) ℝ))) =
          (⇑(R c) : UpperHalfPlane → ℂ)) := by
  obtain ⟨R, hR, hslash⟩ :=
    ModularForm.exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq 3 (by norm_num)
  refine ⟨R, hR, fun c => ?_⟩
  rw [hslash c 1 (Subgroup.one_mem _)]
  have hone : (⟨(1 : SL(2, ℤ)), Subgroup.one_mem (CongruenceSubgroup.Gamma0 3)⟩ :
      CongruenceSubgroup.Gamma0 3) = 1 := rfl
  rw [hone, map_one, inv_one, mul_one]
