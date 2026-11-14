/-
  Cross-module wire test for SET-AF71B (the diamond pullback modulo a maximal ideal, on the
  `X_H`-component).

  A `spec/` probe, not a library module. One zone: the headline
  `ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem` is *fired* at concrete data
  and its two sides are read in the shapes the downstream cone will read them, rather than
  restated.

  * **Zone A, the row at `M = 2`, `H = ⊤`.** The `iff` is read
    - at `d = 1`, i.e. at the identity of `Γ₀(2)`: the diamond operator fixes `1` because
      `gamma0Units 2 1` is the identity unit, which lies in `⊤ ⊔ zpowers (-1)`;
    - at the image of a `Γ_H`-unit: an `A ∈ Γ_H(2, ⊤)` carries a `Γ₀(2)`-element `⟨A, _⟩` whose
      unit lies in `H = ⊤`, so `ρ ⟨A, _⟩ = 1`; and conversely, whenever `ρ γ = 1` the row returns
      the membership `gamma0Units 2 γ ∈ ⊤ ⊔ zpowers (-1)`, which is the direction the pin's proof
      of the row consumes through `faith_exact`.

  At `M = 2` the unit group `(ZMod 2)ˣ` is trivial, so `H = ⊤` is the honest choice: it is the
  component on which *every* `Γ₀`-element is a `Γ_H`-element, and the row must then say that every
  `γ` is fixed — which is what the zone reads.

  The file contains no `#check`s, no `sorry`s and no placeholder proofs.
-/
import FLTForHuman.ModularCurve.IsDiamondPullbackModL

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace ModularCurveSetAF71BConsumer

/-- Zone A: the diamond-pullback row at `M = 2`, `H = ⊤`, read at `d = 1`, at the image of a
`Γ_H`-unit, and in the converse direction. -/
theorem zoneA_two
    (ρ : CongruenceSubgroup.Gamma0 2 →*
      (ModularCurve.qExpFunctionFieldC ℂ (CohCarrier.GammaH 2 ⊤) ≃ₐ[ℂ]
        ModularCurve.qExpFunctionFieldC ℂ (CohCarrier.GammaH 2 ⊤)))
    (hρ : ModularCurve.IsDiamondPullbackModL ℂ 2 ⊤ ρ) :
    ρ (1 : CongruenceSubgroup.Gamma0 2) = 1 ∧
      (∀ (A : SL(2, ℤ)) (hA : A ∈ CohCarrier.GammaH 2 ⊤),
        ρ ⟨A, (CohCarrier.mem_GammaH_iff.mp hA).1⟩ = 1) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 2, ρ γ = 1 →
        CohCarrier.gamma0Units 2 γ ∈ (⊤ : Subgroup (ZMod 2)ˣ) ⊔
          Subgroup.zpowers (-1 : (ZMod 2)ˣ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem hρ 1).mpr
      (Subgroup.mem_sup_left (Subgroup.mem_top _))
  · intro A hA
    exact (ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem hρ
      ⟨A, (CohCarrier.mem_GammaH_iff.mp hA).1⟩).mpr
        (Subgroup.mem_sup_left (Subgroup.mem_top _))
  · intro γ hγ
    exact (ModularCurve.IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem hρ γ).mp hγ

end ModularCurveSetAF71BConsumer
