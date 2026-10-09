/-
The shared point-transport prelude of the exceptional-automorphism set
(WORKORDER-W1-automorphisms.md, order 1).

Statements are transcribed verbatim from the pinned FLT `aa2d8b3` sources.  Both

* `P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean`
  (`§Action`, lines 320–363) and
* `P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three.lean`
  (lines 18–84)

declare this block byte-identically (char 2's `act`/`heq_act`/`xy_act` are char 3's
`vcHom`/`heq_vcHom`/`xy_vcHom` specialised to `E₀`; that specialisation is order 2's
business, not this module's).  It is written once here, public, at the pin's names,
and imported by both headlines.

Only proof bodies are adapted to mathlib `v4.34.0`; no statement moves.  The
vocabulary it is stated in (`vcXInv`/`vcYInv`, `Point.vcInvFun`,
`Point.vcInvFun_zero`, `Point.vcInvFun_add`, `W.toAffine.Point`) is already public in
`FLTForHuman/WeierstrassCurve/Velu/Equivariance.lean` and
`FLTForHuman/WeierstrassCurve/Velu/VariableChangePoint.lean`, and is imported, never
redeclared.  The pin's `import Mathlib` is replaced by that specific module.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.VariableChangePoint

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace WeierstrassCurve.Automorphism

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [DecidableEq K]

def xy {W : WeierstrassCurve K} : W.toAffine.Point → Option (K × K)
  | 0 => none
  | .some x y _ => some (x, y)

theorem xy_injective {W : WeierstrassCurve K} : Function.Injective (xy (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hh
  · rfl
  · exact absurd hh (by simp [xy])
  · exact absurd hh (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl

theorem xy_vcInvFun (γ : VariableChange K) {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xy (Point.vcInvFun γ W.toAffine P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem heq_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P) := by subst e; exact HEq.rfl

theorem xy_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    xy (castPt e P) = xy P := by subst e; rfl

noncomputable def vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hW).toAddMonoidHom.comp
    { toFun := Point.vcInvFun γ W.toAffine
      map_zero' := Point.vcInvFun_zero
      map_add' := Point.vcInvFun_add γ W.toAffine }

theorem vcHom_apply (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) : vcHom γ W hW P = castPt hW (Point.vcInvFun γ W.toAffine P) := rfl

theorem heq_vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) : HEq (Point.vcInvFun γ W.toAffine P) (vcHom γ W hW P) :=
  heq_castPt hW _

theorem xy_vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) :
    xy (vcHom γ W hW P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rw [vcHom_apply, xy_castPt, xy_vcInvFun]

theorem heq_of_xy_eq {W : WeierstrassCurve K} (γ : VariableChange K) (hW : γ • W = W)
    (T : W.toAffine.Point) (Q : W.toAffine.Point)
    (h : (xy T).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) = xy Q) :
    HEq (Point.vcInvFun γ W.toAffine T) Q := by
  have h1 : castPt hW (Point.vcInvFun γ W.toAffine T) = Q := by
    apply xy_injective
    rw [xy_castPt, xy_vcInvFun, h]
  exact (heq_castPt hW _).trans (h1 ▸ HEq.rfl)

end WeierstrassCurve.Automorphism
