/-
  Cross-module wire test for SET-AF9 (the archimedean derivative algebra and the Casimir bridge).

  A `spec/` probe, not a library module. **One zone**, and it is a real composition of the set's two
  orders on one and the same function:

  * the **bridge** (order B,
    `archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt` in
    `Adelic/ArchDerivRightConv.lean`) takes a factorizable `f`, produces the archimedean smoothness
    of `β := rightConv x f` together with the Casimir identity
    `archCasimirAt β = rightConv (archCasimirAt x) f`;
  * the smoothness the bridge produces is exactly the `IsArchSmoothAt` premise the **algebra**
    (order A, `Adelic/ArchCasimir.lean`) needs, so order A's character identity
    (`archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt`) and its `[E, F⁻]`
    commutator (`archDerivAt_commutator_of_isArchSmoothAt`) are then read at `β` itself.

  So the zone dies if either module loses either statement, and its conclusion is about the
  convolution, not about `x` or `f` alone. It imports only the two modules it composes.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivRightConv

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm IsDedekindDomain
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace SetAF9ArchCasimirConsumer

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

/-- **Zone A — the Casimir bridge feeding the real derivative algebra.** At a real place `w`, let
`x` be archimedean-smooth with continuous first and second flow derivatives and `f` a factorizable
test function; the bridge then makes `β = rightConv x f` archimedean-smooth and computes its
Casimir, and that smoothness is what the character identity and the `[E, F⁻]` commutator are read
at. The weight-`n` character hypothesis is carried on `β` itself, so the four conclusions are all
statements about the same convolution. -/
theorem casimir_bridge_with_character_and_commutator
    (hw : w.IsReal) (x f : AdelicGL2 (𝓞 F) F → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x)))
    (tys : ArchTypeFamily F) (hf : IsFactorizableTestFn F f) (hfb : IsArchBiFinite F tys f)
    (n : ℤ) (hχ : HasArchCharacterAt₀ F w (archWeightCharAt hw n) (rightConv F x f)) :
    let β : AdelicGL2 (𝓞 F) F → ℂ := rightConv F x f
    IsArchSmoothAt hw β ∧
    archCasimirAt hw β = rightConv F (archCasimirAt hw x) f ∧
    archDerivAt hw .E β - archDerivAt hw .Fm β = (Complex.I * n) • β ∧
    archDerivAt hw .E (archDerivAt hw .Fm β) - archDerivAt hw .Fm (archDerivAt hw .E β) =
      archDerivAt hw .H β := by
  intro β
  obtain ⟨hsm, -, -, hcas⟩ :=
    archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt F w hw x hxc hxs hD1 hD2
      f tys hf hfb
  exact ⟨hsm, hcas,
    archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt F w hw n β hsm hχ,
    (archDerivAt_commutator_of_isArchSmoothAt F hw β hsm).2.2⟩

end SetAF9ArchCasimirConsumer
