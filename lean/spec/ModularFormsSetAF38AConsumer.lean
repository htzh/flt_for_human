/-
  Consumer zone for `FLTForHuman/ModularForms/HeckeULevel.lean` (order AF38A).

  A `spec/` probe, not a library module: it *consumes* the two headlines in composition, never by
  `#check`.

  Both headlines are about the same operator `U_p`: row A (`exists_gamma1_coe_eq_heckeU_of_dvd`)
  keeps the level, row B (`exists_gamma1_div_coe_eq_heckeU_of_dvd_div`) lowers it when `p ∣ N / p`.
  The zones below apply both to one `f` at `N = p ^ 2` and `ℓ = p`, where the two hypotheses are
  satisfied by `Nat.dvd_pow_self` and by `p ^ 2 / p = p` (`sq_div_self` below):

  * **Zone 1** is row A at `N = p ^ 2`, `ℓ = p`: the `U_p`-image of `f` is again a cusp form at the
    *same* level `p ^ 2`, with the `p`-subsequence `q`-expansion and the same Nebentypus.

  * **Zone 2** is row B at `N = p ^ 2`, `ℓ = p`: since `p ∣ p ^ 2 / p`, the very same `U_p f`
    descends to level `p ^ 2 / p = p`, with the Nebentypus `ε'` read through
    `DirichletCharacter.changeLevel` at level `p ^ 2`.

  * **Zone 3** composes the two: the two forms are the same *function* (`⇑U = ⇑h`), hence have the
    same `q`-expansion coefficientwise, although they live at different levels (`Γ₁(p ^ 2)` versus
    `Γ₁(p ^ 2 / p)`) and the level-`p ^ 2` form carries the raised character
    `changeLevel ε'` while the level-`p ^ 2 / p` form carries `ε'` itself.

  * **Zone 4** draws out the `n = 1` coefficient: `qCoeff (U_p f) 1 = qCoeff f p`, the shape in
    which `U_p` is normally read off an eigenform.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/ModularFormsSetAF38AConsumer.lean` and never enters the build.
-/
import FLTForHuman.ModularForms.HeckeULevel

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularForm
open scoped MatrixGroups

namespace ModularFormsSetAF38AConsumer

variable {p : ℕ} [NeZero p] {k : ℤ}

/-- The level the lowering row lands at: `p ^ 2 / p = p`. -/
theorem sq_div_self : p ^ 2 / p = p := by
  rw [pow_two, Nat.mul_div_cancel _ (NeZero.pos p)]

/-- **Zone 1.** Row A at `N = p ^ 2`, `ℓ = p`: `U_p f` is a cusp form at the same level `p ^ 2`,
with the `p`-subsequence `q`-expansion and `f`'s Nebentypus. -/
theorem sameLevel (f : CuspForm (Gamma1 (p ^ 2)) k) :
    ∃ U : CuspForm (Gamma1 (p ^ 2)) k,
      (⇑U : (ℍ → ℂ)) = heckeU k p ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff U n = ModularFormClass.qCoeff f (p * n)) ∧
      ∀ ε : DirichletCharacter ℂ (p ^ 2),
        CuspForm.HasNebentypus ε f → CuspForm.HasNebentypus ε U :=
  CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd (N := p ^ 2) k (dvd_pow_self p (by norm_num)) f

/-- **Zone 2.** Row B at `N = p ^ 2`, `ℓ = p`: `U_p f` descends to level `p ^ 2 / p`, where it
carries the character `ε'` (while at level `p ^ 2` it carries `changeLevel ε'`). -/
theorem lowered (hp2 : p ∣ p ^ 2) {ε' : DirichletCharacter ℂ (p ^ 2 / p)}
    (f : CuspForm (Gamma1 (p ^ 2)) k)
    (hf : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hp2) ε') f) :
    ∃ h : CuspForm (Gamma1 (p ^ 2 / p)) k,
      (⇑h : (ℍ → ℂ)) = heckeU k p ⇑f ∧
      (∀ n : ℕ, ModularFormClass.qCoeff h n = ModularFormClass.qCoeff f (p * n)) ∧
      CuspForm.HasNebentypus ε' h := by
  have hℓ : p ∣ p ^ 2 / p := by
    simpa only [sq_div_self] using (dvd_refl p : p ∣ p)
  exact CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div k hp2 hℓ ε' f hf

/-- **Zone 3.** The two rows applied to one `f` give one function at two levels: `⇑U = ⇑h`, hence
the same `q`-coefficients, with the Nebentypus raised at level `p ^ 2` and lowered at level
`p ^ 2 / p`. -/
theorem same_qExpansion (hp2 : p ∣ p ^ 2) {ε' : DirichletCharacter ℂ (p ^ 2 / p)}
    (f : CuspForm (Gamma1 (p ^ 2)) k)
    (hf : CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hp2) ε') f) :
    ∃ (U : CuspForm (Gamma1 (p ^ 2)) k) (h : CuspForm (Gamma1 (p ^ 2 / p)) k),
      (⇑U : (ℍ → ℂ)) = ⇑h ∧
      (∀ n : ℕ, ModularFormClass.qCoeff U n = ModularFormClass.qCoeff h n) ∧
      (∀ n : ℕ, ModularFormClass.qCoeff h n = ModularFormClass.qCoeff f (p * n)) ∧
      CuspForm.HasNebentypus ε' h ∧
      CuspForm.HasNebentypus (DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd hp2) ε') U := by
  obtain ⟨U, hU, hUq, hUε⟩ := sameLevel (p := p) (k := k) f
  obtain ⟨h, hh, hhq, hhε⟩ := lowered (p := p) (k := k) hp2 f hf
  refine ⟨U, h, hU.trans hh.symm, fun n => ?_, hhq, hhε, hUε _ hf⟩
  rw [hUq n, hhq n]

/-- **Zone 4.** The `n = 1` coefficient of the `U_p`-image is the `p`-th coefficient of `f`. -/
theorem coeff_one (f : CuspForm (Gamma1 (p ^ 2)) k) :
    ∃ U : CuspForm (Gamma1 (p ^ 2)) k,
      (⇑U : (ℍ → ℂ)) = heckeU k p ⇑f ∧
      ModularFormClass.qCoeff U 1 = ModularFormClass.qCoeff f p := by
  obtain ⟨U, hU, hUq, -⟩ := sameLevel (p := p) (k := k) f
  exact ⟨U, hU, by rw [hUq 1, Nat.mul_one]⟩

end ModularFormsSetAF38AConsumer
