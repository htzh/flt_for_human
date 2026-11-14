/-
  Cross-module wire test for SET-AF70A (the group-and-operator algebra of `Γ_H`).

  A `spec/` probe, not a library module. One zone per headline of
  `ModularForms/CohCarrier/GammaHAlgebra.lean`, each *consuming* the headline rather than
  restating it: every zone below applies the row and uses its output. No `#check`, no `sorry`.

  * **Zone A, row `CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0` at `M = 2`, `H = ⊤`.**
    The row is fired on `Γ = Γ_H(2, ⊤)`, which sits between `Γ₁(2)` and `Γ₀(2)`, and its output
    `H` is *used*: the sandwich `Γ₁(2) ≤ Γ_H(2, ⊤)` is transported across the row's equation
    `Γ_H(2, ⊤) = Γ_H(2, H)` to give `Γ₁(2) ≤ Γ_H(2, H)`. The content is the subgroup dictionary
    of `Γ_H` — the image of `Γ` in `(ZMod 2)ˣ` is a subgroup `H` that reproduces `Γ`.

  * **Zone B, row `CohCarrier.index_gammaH_eq_index_gamma0_mul_index` at `M = 2`, `H = ⊤`.**
    At `H = ⊤` the second factor is `⊤.index = 1`, so the row collapses to
    `[Γ₀(2) : Γ_H(2, ⊤)] = [Γ₀(2) : ⊤] = 1`: the top `Γ_H` *is* `Γ₀`. The collapse is the row's
    content read at the top, which the row does not state.

  * **Zone C, row `CohCarrier.exists_gamma0_lift_dvd` at `M = 2`, `ℓ = 2`, `d = 1`.**
    The lift `σ` of the trivial unit has lower-left entry divisible by `ℓ * M = 4`, and the row's
    divisibility is *spent*: `2 ∣ 4 ∣ σ₁₀` gives `σ ∈ Γ₀(2)` directly, i.e. the lift produced by
    the row is a genuine `Γ₀`-matrix.

  * **Zone D, row `CohCarrier.H1_moduleFinite` at `M = 2`, `H = ⊤` with `A = ℂ`.**
    The row's finiteness instance is fed to `Module.Finite.prod`, so `H¹(Γ_H(2, ⊤), ℂ)` is a
    finite module and so is its square. Nothing about `H¹` is assumed: the square's finiteness is
    *derived* from the row.

  * **Zone E, row `CohCarrier.charInvolution_comp_opFamily` at `M = 2`, `H = ⊤`, `S = ∅`.**
    Fired on the `T_3` generator of `Gen 2 ∅` (`3 ∉ ∅`, `3 ∤ 2`), and the operator identity is
    then *evaluated* at a class `φ : H¹(Γ_H(2, ⊤), ℂ)`: the character involution commutes with
    every generator of the Hecke family, so the two orders of applying `T_3` and `ι` agree on
    classes.

  * **Zone F, row `CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq`
    at `M = 2` with the unit `1`.** The row's surjectivity is *executed*: the double-coset class
    of the identity has a preimage among the vectors of additive order `2` in `(Z/2)²`, i.e. the
    classification by double cosets has no gaps at `M = 2`.
-/
import FLTForHuman.ModularForms.CohCarrier.GammaHAlgebra

set_option autoImplicit false

noncomputable section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace SetAF70AConsumer

/-! ## Zone A: the subgroup dictionary at `M = 2`, `H = ⊤` -/

/-- **Zone A.** The row's `H` at `Γ = Γ_H(2, ⊤)` still sees the principal congruence subgroup:
the output equation `Γ_H(2, ⊤) = Γ_H(2, H)` transports `Γ₁(2) ≤ Γ_H(2, ⊤)` to `Γ_H(2, H)`. -/
theorem zoneA :
    ∃ H : Subgroup (ZMod 2)ˣ, CongruenceSubgroup.Gamma1 2 ≤ CohCarrier.GammaH 2 H := by
  obtain ⟨H, hH⟩ :=
    CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0 2 (CohCarrier.GammaH 2 ⊤)
      (CohCarrier.Gamma1_le_GammaH 2 ⊤) (CohCarrier.GammaH_le_Gamma0 (M := 2) ⊤)
  exact ⟨H, hH ▸ CohCarrier.Gamma1_le_GammaH 2 ⊤⟩

/-! ## Zone B: the index formula at `M = 2`, `H = ⊤` -/

/-- **Zone B.** At `H = ⊤` the row's right-hand factor is `⊤.index = 1`, so the index of
`Γ_H(2, ⊤)` is that of `Γ₀(2)`: the top `Γ_H` is the full `Γ₀`. -/
theorem zoneB : (CohCarrier.GammaH 2 ⊤).index = (CongruenceSubgroup.Gamma0 2).index := by
  rw [CohCarrier.index_gammaH_eq_index_gamma0_mul_index 2 ⊤, Subgroup.index_top, mul_one]

/-! ## Zone C: the divisible lift at `M = 2`, `ℓ = 2`, `d = 1` -/

/-- **Zone C.** The lift of `1` produced by the row has lower-left entry divisible by `4`, and
that divisibility *is* the `Γ₀(2)`-condition on the entry: the row's lift is a `Γ₀`-matrix twice
over, by construction and by its own statement. -/
theorem zoneC :
    ∃ σ : CongruenceSubgroup.Gamma0 2, CohCarrier.gamma0Units 2 σ = 1 ∧
      ((σ : SL(2, ℤ)) 1 0 : ZMod 2) = 0 := by
  obtain ⟨σ, hσ, hdvd⟩ := CohCarrier.exists_gamma0_lift_dvd 2 2 1
  refine ⟨σ, hσ, ?_⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_trans (by norm_num : (2 : ℤ) ∣ ((2 * 2 : ℕ) : ℤ)) hdvd

/-! ## Zone D: `H¹` finiteness at `M = 2`, `H = ⊤`, `A = ℂ` -/

/-- **Zone D.** The row's finiteness of `H¹(Γ_H(2, ⊤), ℂ)` is spent on `Module.Finite.prod`:
the square of the carrier is again a finite `ℂ`-module. -/
theorem zoneD : Module.Finite ℂ (CohCarrier.H1 2 ⊤ ℂ × CohCarrier.H1 2 ⊤ ℂ) := by
  have h : Module.Finite ℂ (CohCarrier.H1 2 ⊤ ℂ) := CohCarrier.H1_moduleFinite 2 ⊤ ℂ ℂ
  infer_instance

/-! ## Zone E: the character involution against a generator at `M = 2`, `H = ⊤`, `S = ∅` -/

/-- **Zone E, the operator identity.** The row, fired on the `T_3` generator of `Gen 2 ∅` and
evaluated at a class: `ι` commutes with `T_3` on `H¹(Γ_H(2, ⊤), ℂ)`. -/
theorem zoneE (φ : CohCarrier.H1 2 ⊤ ℂ) :
    CohCarrier.charInvolution 2 ⊤ ℂ ℂ
        (CohCarrier.opFamily 2 ⊤ ∅ ℂ
          (CohCarrier.Gen.T 3 (by norm_num) (by simp) (by norm_num)) φ) =
      CohCarrier.opFamily 2 ⊤ ∅ ℂ
        (CohCarrier.Gen.T 3 (by norm_num) (by simp) (by norm_num))
        (CohCarrier.charInvolution 2 ⊤ ℂ ℂ φ) :=
  LinearMap.congr_fun (CohCarrier.charInvolution_comp_opFamily 2 ⊤ ∅ ℂ _) φ

/-- **Zone E, the operator form.** The same row, read as a commuting square of `ℂ`-linear
endomorphisms: no evaluation is needed for the diamond generator `dia 1`. -/
theorem zoneE_diamond :
    CohCarrier.charInvolution 2 ⊤ ℂ ℂ ∘ₗ
        CohCarrier.opFamily 2 ⊤ ∅ ℂ (CohCarrier.Gen.dia 1) =
      CohCarrier.opFamily 2 ⊤ ∅ ℂ (CohCarrier.Gen.dia 1) ∘ₗ
        CohCarrier.charInvolution 2 ⊤ ℂ ℂ :=
  CohCarrier.charInvolution_comp_opFamily 2 ⊤ ∅ ℂ (CohCarrier.Gen.dia 1)

/-! ## Zone F: the double-coset classification at `M = 2` with the unit `1` -/

/-- **Zone F.** The row's classifying map is surjective, and its surjectivity is executed on the
double-coset class of `1`: some vector of additive order `2` in `(Z/2)²` represents it. -/
theorem zoneF :
    ∃ c : {v : Fin 2 → ZMod 2 // addOrderOf v = 2} →
        DoubleCoset.Quotient (CohCarrier.GammaH 2 ⊤ : Set SL(2, ℤ))
          (Subgroup.zpowers (1 : SL(2, ℤ)) : Set SL(2, ℤ)),
      Function.Surjective c ∧
        ∃ v, c v = DoubleCoset.mk (CohCarrier.GammaH 2 ⊤) (Subgroup.zpowers (1 : SL(2, ℤ)))
          (1 : SL(2, ℤ)) := by
  obtain ⟨c, hc, _⟩ :=
    CohCarrier.exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq 2 ⊤ 1
  exact ⟨c, hc, hc _⟩

end SetAF70AConsumer
