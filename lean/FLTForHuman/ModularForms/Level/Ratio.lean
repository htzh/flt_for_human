/-
  A `Γ₀(ℓ)`-level realisation of the level-one ratio `E₄³ / Δ`.

  `ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant`: for every level `ℓ ≥ 2` there
  are weight-`12` forms `G H` for `Γ₀(ℓ)` with `H ≠ 0` whose ratio of `q`-expansions is the level-one
  ratio `E₄ ^ 3 / Δ`. It is the level-raising step the weight-one lift spends: a level-one modular
  function is realised as the quotient of two level-`Γ₀` forms of weight `12`.

  Transcribed from the pin `S_` file below (pinned `aa2d8b3`, 66 lines).

  The pin's `SolJJ0Aux` block (`S_` file `:11-35`) is the pipeline's solution-stage namespace; it is
  dropped as a label, and the block's declarations stay `private` — they are `private` in the pin too,
  and they are this row's proof (the two level-one weight-`12` representatives at `Γ₀(1)`), not a new
  interface.

  Imports: one line was added to the scaffold's four —
  `Mathlib.NumberTheory.ModularForms.CuspFormSubmodule`, for `CuspForm.toModularFormₗ` (the pin reaches
  it through its full `Mathlib` import; the port's narrower statement closure did not carry it).

  Heartbeat probe (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N` on this file): silent at
  `N = 2000`, fails at `N = 1000`. Nothing is installed — the edit loop runs at the playbook's
  `200000` and the module carries no `set_option maxHeartbeats`.

  spec-pin: P2M/Sol/S_ModularForm_exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant.lean
-/
import FLTForHuman.ModularForms.Level.Degeneracy
import Mathlib.RingTheory.LaurentSeries
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open UpperHalfPlane
open ModularForm
open scoped Classical MatrixGroups

namespace ModularForm

/-! ### The level-one representatives as `Γ₀(1)`-forms

The pin's `SolJJ0Aux` block (pinned `aa2d8b3`, `S_` file `:11-35`), which is `private` there and
stays `private` here: the two level-one weight-`12` forms `E₄³` and `Δ` viewed at `Γ₀(1)`, so that
the degeneracy map `exists_degeneracy_Gamma0` (whose level hypothesis is `1 * 1 ∣ ℓ`) applies to
them. The pin's label namespace is dropped; the declarations keep the pin's names. -/

private theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private theorem gamma0_one_coe :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  simp [gamma0_one_eq_top, MonoidHom.range_eq_map]

private theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  simp [Matrix.one_fin_two]

private noncomputable def e4cube : ModularForm (CongruenceSubgroup.Gamma0 1) 12 :=
  ModularForm.mcast (by norm_num) (ModularForm.E₄.pow 3) gamma0_one_coe

private noncomputable def delta1 : ModularForm (CongruenceSubgroup.Gamma0 1) 12 :=
  ModularForm.mcast rfl (CuspForm.toModularFormₗ CuspForm.discriminant) gamma0_one_coe

private theorem coe_e4cube : ⇑e4cube = ⇑(ModularForm.E₄.pow 3) := rfl

private theorem coe_delta1 : ⇑delta1 = ModularForm.discriminant := rfl

/-- **The `Γ₀(ℓ)` ratio.** A level-one ratio of two weight-`12` modular forms is realised at level
`Γ₀(ℓ)`. -/
theorem exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant (ℓ : ℕ) [NeZero ℓ] : ∃ G H : ModularForm (CongruenceSubgroup.Gamma0 ℓ) 12,
    H ≠ 0 ∧ ((qExpansion 1 (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
      ((qExpansion 1 (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
    (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 /
      ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by
  obtain ⟨G, hG⟩ := ModularForm.exists_degeneracy_Gamma0
    (show 1 * 1 ∣ ℓ by simp) e4cube
  obtain ⟨H, hH⟩ := ModularForm.exists_degeneracy_Gamma0
    (show 1 * 1 ∣ ℓ by simp) delta1
  have hGfun : ⇑G = ⇑(ModularForm.E₄.pow 3) := by
    rw [hG, heckeDiagMatrix_one]
    funext τ
    rw [one_smul]
    exact congrFun coe_e4cube τ
  have hHfun : ⇑H = ModularForm.discriminant := by
    rw [hH, heckeDiagMatrix_one]
    funext τ
    rw [one_smul]
    exact congrFun coe_delta1 τ
  refine ⟨G, H, ?_, ?_⟩
  · intro h0
    refine ModularForm.discriminant_ne_zero UpperHalfPlane.I ?_
    rw [← hHfun, h0]
    simp
  · have hqG : qExpansion 1 (G : ℍ → ℂ) = (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
      rw [hGfun]
      exact ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3
    have hqH : qExpansion 1 (H : ℍ → ℂ) = qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) := by
      rw [hHfun]
    rw [hqG, hqH, PowerSeries.coe_pow]

end ModularForm
