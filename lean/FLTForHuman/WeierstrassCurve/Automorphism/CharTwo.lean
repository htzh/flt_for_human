/-
The exceptional automorphisms of the supersingular curve `y² + y = x³` in
characteristic two (WORKORDER-W1-automorphisms.md, order 2).

Statement is transcribed verbatim from the pinned FLT `aa2d8b3` wrapper

* `Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean`

(the statement authority); the proof body comes from
`P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean`
(988 lines), adapted to mathlib `v4.34.0`.  Silverman III.10.1 + Appendix A
Prop. 1.2: on `y² + y = x³` over an algebraically closed `L` of characteristic 2,
the order-three automorphism `(x, y) ↦ (ωx, y)` and the order-four automorphism
`(x, y) ↦ (x + 1, y + ω)` are packaged as additive endomorphisms `σ`, `ι` of
`E₀(L)`, realized through the variable-change action recorded as a heterogeneous
equality; then `σ² + σ + 1 = 0`, `ι² = -1`, and neither is scalar on any
`p`-torsion for `p ∣ M`.

The pin's internal machinery (`E₀`, the field lemmas, `βv`/`αv`/`δv`, the
`σ`/`τ` block and both torsion arguments) is `private` here, so the checker diffs
only the wrapper's public surface.  The pin's `VariableChange` component lemmas
(`mul_u`/`mul_r`/`mul_s`/`mul_t`) are `rfl` in FLT and are not ported: mathlib
supplies `VariableChange.mul_def`, which the proofs below rewrite with.  The
shared point-transport prelude is imported from
`FLTForHuman/WeierstrassCurve/Automorphism/Basic.lean`, and the `p`-torsion step
uses the public
`WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`.  The
pin's `set_option maxHeartbeats 6400000` is **not** transcribed — this project's
global cap is 4,000,000 — while the pin's `linter.unusedSectionVars false`,
`linter.unusedVariables false` and `linter.unusedSimpArgs false` suppressions (its
own header, lines 11–13) **are**, at the pin's own line list.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean>
-/
import FLTForHuman.WeierstrassCurve.Automorphism.Basic
import FLTForHuman.Elliptic.TorsionZMod

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

-- The headline's FQN is fixed by the wrapper as `WeierstrassCurve.…`, so the
-- private machinery lives in that same namespace (a `private` declaration is
-- only resolvable from its own enclosing namespace).  The shared prelude is
-- imported from `Automorphism/Basic.lean` and opened here.
namespace WeierstrassCurve

open Automorphism

section CharTwo

variable {K : Type*} [Field K] [CharP K 2]

private theorem two_eq_zero : (2 : K) = 0 := by
  simpa using CharP.cast_eq_zero K 2

private theorem three_eq_one : (3 : K) = 1 := by
  have : (3 : K) = 2 + 1 := by norm_num
  rw [this, two_eq_zero, zero_add]

private theorem neg_eq (a : K) : -a = a := by
  have h : a + a = 0 := by rw [← two_mul, two_eq_zero, zero_mul]
  exact (neg_eq_of_add_eq_zero_left h)

private theorem sub_eq_add' (a b : K) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq]

private theorem add_self (a : K) : a + a = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

private theorem sq_add (a b : K) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring
  rw [this, two_eq_zero, zero_mul, add_zero]

private theorem sq_add_self_eq_zero_iff (x : K) : x ^ 2 + x = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have : x * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · right
      have := neg_eq (1 : K)
      linear_combination h1 + this
  · rintro (rfl | rfl)
    · ring
    · have := add_self (1 : K); simpa [sq] using this

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

private theorem omega_pow_three : ω ^ 3 = 1 := by
  have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
  rw [hω, mul_zero] at h1
  linear_combination -h1

private theorem omega_ne_one : ω ≠ 1 := by
  intro h
  rw [h] at hω
  have : (3 : K) = 0 := by linear_combination hω
  rw [three_eq_one] at this
  exact one_ne_zero this

private theorem omega_ne_zero : ω ≠ 0 := by
  intro h
  rw [h] at hω
  simp at hω

private theorem omega_sq : ω ^ 2 = ω + 1 := by
  have h1 := neg_eq ω
  have h2 := neg_eq (1 : K)
  linear_combination hω + h1 + h2

private theorem sq_add_self_add_one_eq_zero_iff (x : K) : x ^ 2 + x + 1 = 0 ↔ x = ω ∨ x = ω + 1 := by
  constructor
  · intro h
    have : (x + ω) * (x + ω + 1) = 0 := by
      have h2 := two_eq_zero (K := K)
      linear_combination h + hω + (x * ω - 1) * h2
    rcases mul_eq_zero.mp this with h0 | h1
    · left
      have := neg_eq ω
      linear_combination h0 + this
    · right
      have := neg_eq (ω + 1)
      linear_combination h1 + this
  · rintro (rfl | rfl)
    · exact hω
    · have h2 := two_eq_zero (K := K)
      linear_combination hω + (ω + 1) * h2

end CharTwo

section Curve

variable (K : Type*) [Field K] [CharP K 2]

private def E₀ : WeierstrassCurve K := ⟨0, 0, 1, 0, 0⟩

private theorem E₀_a₁ : (E₀ K).a₁ = 0 := rfl
private theorem E₀_a₂ : (E₀ K).a₂ = 0 := rfl
private theorem E₀_a₃ : (E₀ K).a₃ = 1 := rfl
private theorem E₀_a₄ : (E₀ K).a₄ = 0 := rfl
private theorem E₀_a₆ : (E₀ K).a₆ = 0 := rfl

private theorem E₀_Δ : (E₀ K).Δ = 1 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, E₀_a₁, E₀_a₂, E₀_a₃, E₀_a₄, E₀_a₆]
  have h2 := two_eq_zero (K := K)
  linear_combination (-14 : K) * h2

private instance E₀_isElliptic : (E₀ K).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, E₀_Δ]; exact isUnit_one

private theorem E₀_c₄ : (E₀ K).c₄ = 0 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, E₀_a₁, E₀_a₂, E₀_a₃,
    E₀_a₄]
  ring

private theorem E₀_j : (E₀ K).j = 0 := by
  rw [WeierstrassCurve.j, E₀_c₄]; ring

variable {K}

private theorem smul_E₀_eq_iff (γ : VariableChange K) :
    γ • E₀ K = E₀ K ↔
      (γ.u : K) ^ 3 = 1 ∧ γ.r = γ.s ^ 2 ∧ γ.s ^ 4 = γ.s ∧ γ.t ^ 2 + γ.t = γ.s ^ 3 := by
  have h2 := two_eq_zero (K := K)
  have h3 := three_eq_one (K := K)
  have hu : (γ.u : K) ≠ 0 := γ.u.ne_zero
  have hui : ((γ.u⁻¹ : Kˣ) : K) * (γ.u : K) = 1 := by simp
  have hv : ((γ.u⁻¹ : Kˣ) : K) ≠ 0 := (γ.u⁻¹).ne_zero
  constructor
  · intro h
    have e₂ := congrArg WeierstrassCurve.a₂ h
    have e₃ := congrArg WeierstrassCurve.a₃ h
    have e₄ := congrArg WeierstrassCurve.a₄ h
    have e₆ := congrArg WeierstrassCurve.a₆ h
    simp only [E₀, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆] at e₂ e₃ e₄ e₆

    have hv3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      linear_combination e₃ - ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2
    have hu3 : (γ.u : K) ^ 3 = 1 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 3 * (γ.u : K) ^ 3 = 1 := by rw [← mul_pow, hui, one_pow]
      rwa [hv3, one_mul] at this

    have hr : γ.r = γ.s ^ 2 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 2 * ((3 : K) * γ.r - γ.s ^ 2) = 0 := by linear_combination e₂
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0) hv
      · rw [h3, one_mul, sub_eq_zero] at h0
        exact h0

    have hs : γ.s ^ 4 = γ.s := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 4 * (-γ.s + (3 : K) * γ.r ^ 2 - 2 * γ.s * γ.t) = 0 := by
        linear_combination e₄
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h0) hv
      · rw [h3, h2, hr] at h0
        linear_combination h0

    have ht : γ.t ^ 2 + γ.t = γ.s ^ 3 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 6 * (γ.r ^ 3 - γ.t - γ.t ^ 2) = 0 := by linear_combination e₆
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd (pow_eq_zero_iff (n := 6) (by norm_num) |>.mp h0) hv
      · rw [hr] at h0
        have e : (γ.s ^ 2) ^ 3 = γ.s ^ 4 * γ.s ^ 2 := by ring
        rw [e, hs] at h0
        linear_combination -h0
    exact ⟨hu3, hr, hs, ht⟩
  · rintro ⟨hu3, hr, hs, ht⟩
    have hv3 : ((γ.u⁻¹ : Kˣ) : K) ^ 3 = 1 := by
      have : ((γ.u⁻¹ : Kˣ) : K) ^ 3 * (γ.u : K) ^ 3 = 1 := by rw [← mul_pow, hui, one_pow]
      rwa [hu3, mul_one] at this
    have hs3 : γ.s ^ 6 = γ.s ^ 3 := by
      calc γ.s ^ 6 = γ.s ^ 4 * γ.s ^ 2 := by ring
        _ = γ.s ^ 3 := by rw [hs]; ring
    have hns := neg_eq γ.s
    have hn1 := neg_eq γ.t
    have hn2 := neg_eq (γ.t ^ 2)
    have hss : γ.s + γ.s ^ 4 = 0 := by rw [hs, add_self]
    ext
    · simp only [variableChange_a₁, E₀]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) * γ.s * h2
    · simp only [variableChange_a₂, E₀]
      rw [h3, hr]; ring
    · simp only [variableChange_a₃, E₀]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 3 * γ.t * h2 + hv3
    · simp only [variableChange_a₄, E₀]
      rw [h2, h3, hr]
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 4 * hss - ((γ.u⁻¹ : Kˣ) : K) ^ 4 * γ.s * h2
    · simp only [variableChange_a₆, E₀]
      rw [hr]
      have : (γ.s ^ 2) ^ 3 - γ.t * 1 - γ.t ^ 2 = 0 := by
        have e : (γ.s ^ 2) ^ 3 = γ.s ^ 6 := by ring
        rw [e, hs3, ← ht]
        ring
      linear_combination ((γ.u⁻¹ : Kˣ) : K) ^ 6 * this

end Curve

section Explicit

variable {K : Type*} [Field K] [CharP K 2]

private def ε : VariableChange K := ⟨1, 0, 0, 1⟩

private theorem ε_smul : (ε : VariableChange K) • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simp [ε], by simp [ε], by simp [ε], by simpa [ε] using add_self (1 : K)⟩

variable (u : Kˣ) (hu : (u : K) ^ 3 = 1) (hu1 : (u : K) ≠ 1)

private def βv : VariableChange K := ⟨u, 0, 0, 0⟩

private def αv : VariableChange K := ⟨1, 1, 1, (u : K)⟩

private def δv : VariableChange K := ⟨1, (u : K), (u : K) ^ 2, (u : K)⟩

include hu hu1

private theorem hq : (u : K) ^ 2 + (u : K) + 1 = 0 := by
  have : ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = 0 := by linear_combination hu
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hu1
  · exact h0

private theorem u_sq : (u : K) ^ 2 = (u : K) + 1 := omega_sq (u : K) (hq u hu hu1)

private theorem coe_inv_u : (((u⁻¹ : Kˣ)) : K) = (u : K) ^ 2 := by
  rw [Units.val_inv_eq_inv_val]
  exact inv_eq_of_mul_eq_one_right (by
    calc (u : K) * (u : K) ^ 2 = (u : K) ^ 3 := by ring
      _ = 1 := hu)

private theorem u_pow_four : (u : K) ^ 4 = (u : K) := by
  calc (u : K) ^ 4 = (u : K) ^ 3 * (u : K) := by ring
    _ = (u : K) := by rw [hu, one_mul]

private theorem βv_smul : βv u • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simpa [βv] using hu, by simp [βv], by simp [βv], by simp [βv]⟩

private theorem αv_smul : αv u • E₀ K = E₀ K :=
  (smul_E₀_eq_iff _).2 ⟨by simp [αv], by simp [αv], by simp [αv], by
    simp only [αv, one_pow]
    have := neg_eq (1 : K)
    linear_combination hq u hu hu1 + this⟩

private theorem δv_smul : δv u • E₀ K = E₀ K := by
  have h4 := u_pow_four u hu hu1
  have hsq := u_sq u hu hu1
  refine (smul_E₀_eq_iff _).2 ⟨by simp [δv], ?_, ?_, ?_⟩
  · show (u : K) = ((u : K) ^ 2) ^ 2
    calc (u : K) = (u : K) ^ 4 := h4.symm
      _ = ((u : K) ^ 2) ^ 2 := by ring
  · show ((u : K) ^ 2) ^ 4 = (u : K) ^ 2
    calc ((u : K) ^ 2) ^ 4 = ((u : K) ^ 4) ^ 2 := by ring
      _ = (u : K) ^ 2 := by rw [h4]
  · show (u : K) ^ 2 + (u : K) = ((u : K) ^ 2) ^ 3
    have : ((u : K) ^ 2) ^ 3 = ((u : K) ^ 3) ^ 2 := by ring
    rw [this, hu, one_pow]
    have h1 := neg_eq (1 : K)
    linear_combination hq u hu hu1 + h1

private theorem βv_mul_βv_mul_βv : βv u * βv u * βv u = 1 := by
  have hu' : u * u * u = 1 := Units.ext (by simp only [Units.val_mul, Units.val_one]; rw [← hu]; ring)
  ext
  · simp only [VariableChange.mul_def, βv, VariableChange.one_def]; exact congrArg Units.val hu'
  · simp [VariableChange.mul_def, βv, VariableChange.one_def]
  · simp [VariableChange.mul_def, βv, VariableChange.one_def]
  · simp [VariableChange.mul_def, βv, VariableChange.one_def]

private theorem δv_eq : δv u = (βv u)⁻¹ * (αv u * βv u * (αv u)⁻¹) := by
  have h2 := two_eq_zero (K := K)
  have hsq := u_sq u hu hu1
  have hui := coe_inv_u u hu hu1
  have h4 := u_pow_four u hu hu1
  have hq' := hq u hu hu1
  have h6 : (u : K) ^ 6 = 1 := by
    calc (u : K) ^ 6 = ((u : K) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hu, one_pow]
  simp only [VariableChange.inv_def]
  ext
  · simp [VariableChange.mul_def, αv, βv, δv]
  · simp only [VariableChange.mul_def, αv, βv, δv, Units.val_mul, Units.val_one, hui, inv_one]
    linear_combination -hq' + ((u : K) + 1) * h2
  · simp only [VariableChange.mul_def, αv, βv, δv, Units.val_mul, Units.val_one, hui, inv_one]
    linear_combination hq' - (u : K) * h2
  · simp only [VariableChange.mul_def, αv, βv, δv, Units.val_mul, Units.val_one, hui, inv_one]
    linear_combination -h4 + hq' - h2

private theorem δv_mul_δv : δv u * δv u = (ε : VariableChange K) := by
  have h2 := two_eq_zero (K := K)
  ext
  · simp [VariableChange.mul_def, δv, ε]
  · simp only [VariableChange.mul_def, δv, ε, Units.val_one]
    linear_combination (u : K) * h2
  · simp only [VariableChange.mul_def, δv, ε, Units.val_one]
    linear_combination (u : K) ^ 2 * h2
  · simp only [VariableChange.mul_def, δv, ε, Units.val_one]
    linear_combination (u : K) * h2 + hu

end Explicit

section Action

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]

private abbrev act (γ : VariableChange K) (hγ : γ • E₀ K = E₀ K) :
    (E₀ K).toAffine.Point →+ (E₀ K).toAffine.Point := vcHom γ (E₀ K) hγ

private theorem heq_act (γ : VariableChange K) (hγ : γ • E₀ K = E₀ K) (P : (E₀ K).toAffine.Point) :
    HEq (Point.vcInvFun γ (E₀ K).toAffine P) (act γ hγ P) :=
  heq_vcHom γ (E₀ K) hγ P

private theorem xy_act (γ : VariableChange K) (hγ : γ • E₀ K = E₀ K) (P : (E₀ K).toAffine.Point) :
    xy (act γ hγ P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  show xy (castPt hγ (Point.vcInvFun γ (E₀ K).toAffine P)) = _
  rw [xy_castPt, xy_vcInvFun]

private theorem act_injective (γ : VariableChange K) (hγ : γ • E₀ K = E₀ K) : Function.Injective (act γ hγ) := by
  intro P Q h
  have h' := congrArg xy h
  rw [xy_act, xy_act] at h'
  have hinj : Function.Injective (fun q : K × K => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ hq
    simp only [Prod.mk.injEq] at hq
    obtain ⟨hx, hy⟩ := hq
    have hx' : x = x' := by simpa using congrArg (vcX γ) hx
    subst hx'
    have hy' : y = y' := by simpa using congrArg (vcY γ (vcXInv γ x)) hy
    exact Prod.ext rfl hy'
  exact xy_injective (Option.map_injective hinj h')

private theorem act_mul (γ γ' : VariableChange K) (hγ : γ • E₀ K = E₀ K) (hγ' : γ' • E₀ K = E₀ K)
    (h : (γ * γ') • E₀ K = E₀ K) (P : (E₀ K).toAffine.Point) :
    act (γ * γ') h P = act γ hγ (act γ' hγ' P) := by
  apply xy_injective
  rw [xy_act, xy_act, xy_act]
  rcases P with _ | ⟨x, y, hP⟩
  · rfl
  · show some (vcXInv (γ * γ') x, vcYInv (γ * γ') x y) =
      some (vcXInv γ (vcXInv γ' x), vcYInv γ (vcXInv γ' x) (vcYInv γ' x y))
    have hu : (γ.u : K) ≠ 0 := γ.u.ne_zero
    have hu' : (γ'.u : K) ≠ 0 := γ'.u.ne_zero
    simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val,
      Option.some.injEq, Prod.mk.injEq]
    constructor
    · field_simp; ring
    · field_simp; ring

private theorem mul_smul_E₀ {γ γ' : VariableChange K} (hγ : γ • E₀ K = E₀ K) (hγ' : γ' • E₀ K = E₀ K) :
    (γ * γ') • E₀ K = E₀ K := by rw [mul_smul, hγ', hγ]

private theorem inv_smul_E₀ {γ : VariableChange K} (hγ : γ • E₀ K = E₀ K) : γ⁻¹ • E₀ K = E₀ K := by
  rw [inv_smul_eq_iff, hγ]

private theorem act_ε (P : (E₀ K).toAffine.Point) : act ε ε_smul P = -P := by
  apply xy_injective
  rw [xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]
    show some (vcXInv (ε : VariableChange K) x, vcYInv (ε : VariableChange K) x y) =
      some (x, (E₀ K).toAffine.negY x y)
    simp only [vcXInv, vcYInv, ε, inv_one, Units.val_one, one_pow, one_mul, sub_zero,
      zero_mul, WeierstrassCurve.Affine.negY, Option.some.injEq, Prod.mk.injEq, true_and]
    show y - 1 = -y - (E₀ K).a₁ * x - (E₀ K).a₃
    rw [E₀_a₁, E₀_a₃, neg_eq]; ring

private theorem act_congr {γ γ' : VariableChange K} (h : γ = γ') (hγ : γ • E₀ K = E₀ K) (hγ' : γ' • E₀ K = E₀ K)
    (P : (E₀ K).toAffine.Point) : act γ hγ P = act γ' hγ' P := by subst h; rfl

private theorem act_act_inv {γ : VariableChange K} (hγ : γ • E₀ K = E₀ K) (P : (E₀ K).toAffine.Point) :
    act γ hγ (act γ⁻¹ (inv_smul_E₀ hγ) P) = P := by
  rw [← act_mul γ γ⁻¹ hγ (inv_smul_E₀ hγ) (mul_smul_E₀ hγ (inv_smul_E₀ hγ))]
  rw [act_congr (mul_inv_cancel γ) _ (one_smul _ _)]
  apply xy_injective
  rw [xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · show some (vcXInv (1 : VariableChange K) x, vcYInv (1 : VariableChange K) x y) = some (x, y)
    simp [vcXInv, vcYInv, VariableChange.one_def]

end Action

section Sigma

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]
variable (u : Kˣ) (hu : (u : K) ^ 3 = 1) (hu1 : (u : K) ≠ 1)
include hu hu1

private def σ : (E₀ K).toAffine.Point →+ (E₀ K).toAffine.Point := act (βv u) (βv_smul u hu hu1)

private theorem σ_apply (P : (E₀ K).toAffine.Point) : σ u hu hu1 P = act (βv u) (βv_smul u hu hu1) P := rfl

omit hu hu1 in
private theorem eq_some_of_xy {W : WeierstrassCurve K} (Q : W.toAffine.Point) {x y : K}
    (h : xy Q = some (x, y)) : ∃ hQ, Q = Point.some x y hQ := by
  rcases Q with _ | ⟨x', y', h'⟩
  · simp [xy] at h
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h', rfl⟩

private theorem σ_some {x y : K} (h : (E₀ K).toAffine.Nonsingular x y) :
    ∃ h', σ u hu hu1 (Point.some x y h) = Point.some ((u : K) * x) y h' := by
  apply eq_some_of_xy
  rw [σ_apply, xy_act]
  show some (vcXInv (βv u) x, vcYInv (βv u) x y) = some ((u : K) * x, y)
  have hui := coe_inv_u u hu hu1
  have h4 := u_pow_four u hu hu1
  have h6 : (u : K) ^ 6 = 1 := by
    calc (u : K) ^ 6 = ((u : K) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hu, one_pow]
  simp only [vcXInv, vcYInv, βv, hui, sub_zero, zero_mul, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rw [← pow_mul, show 2 * 2 = 4 by norm_num, h4]
  · rw [← pow_mul, show 2 * 3 = 6 by norm_num, h6, one_mul]

private theorem σ_σ_add (P : (E₀ K).toAffine.Point) : σ u hu hu1 (σ u hu hu1 P) + σ u hu hu1 P + P = 0 := by
  have h2 := two_eq_zero (K := K)
  have hq' := hq u hu hu1
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hnegY : ∀ a b : K, (E₀ K).toAffine.negY a b = b + 1 := by
    intro a b
    rw [WeierstrassCurve.Affine.negY]
    simp only [E₀_a₁, E₀_a₃]
    have := neg_eq b
    have h1 := neg_eq (1 : K)
    linear_combination this + h1
  rcases P with _ | ⟨x, y, h⟩
  · show σ u hu hu1 (σ u hu hu1 0) + σ u hu hu1 0 + 0 = 0
    rw [map_zero, map_zero, add_zero, add_zero]
  · by_cases hx : x = 0
    ·
      subst hx
      have hfix : σ u hu hu1 (Point.some 0 y h) = Point.some 0 y h := by
        obtain ⟨h', e⟩ := σ_some u hu hu1 h
        rw [e]
        apply xy_injective
        simp [xy]
      rw [hfix, hfix]
      have hyne : y ≠ (E₀ K).toAffine.negY 0 y := by
        rw [hnegY]; intro e
        have : (1 : K) = 0 := by linear_combination -e
        exact one_ne_zero this
      rw [Point.add_of_Y_ne hyne]
      have hsl : (E₀ K).toAffine.slope 0 0 y y = 0 := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne]
        simp [E₀_a₁, E₀_a₂, E₀_a₄]
      apply Point.add_of_Y_eq
      · simp [hsl, E₀_a₁, E₀_a₂]
      · simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
          WeierstrassCurve.Affine.addX, hsl, hnegY, E₀_a₁, E₀_a₂]
        ring
    ·
      obtain ⟨h₁, e₁⟩ := σ_some u hu hu1 h
      obtain ⟨h₂, e₂⟩ := σ_some u hu hu1 h₁
      rw [e₁, e₂]
      have hne : (u : K) * ((u : K) * x) ≠ (u : K) * x := by
        intro e
        have : (u : K) * x * ((u : K) - 1) = 0 := by linear_combination e
        rcases mul_eq_zero.mp this with h0 | h0
        · rcases mul_eq_zero.mp h0 with h00 | h00
          · exact hu0 h00
          · exact hx h00
        · exact hu1 (sub_eq_zero.mp h0)
      rw [Point.add_of_X_ne hne]
      have hsl : (E₀ K).toAffine.slope ((u : K) * ((u : K) * x)) ((u : K) * x) y y = 0 := by
        rw [WeierstrassCurve.Affine.slope_of_X_ne hne, sub_self, zero_div]
      apply Point.add_of_Y_eq
      · simp only [WeierstrassCurve.Affine.addX, hsl, E₀_a₁, E₀_a₂]
        linear_combination (-x) * hq'
      · simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
          WeierstrassCurve.Affine.addX, hsl, hnegY, E₀_a₁, E₀_a₂]
        ring

private theorem σ_σ_σ (P : (E₀ K).toAffine.Point) : σ u hu hu1 (σ u hu hu1 (σ u hu hu1 P)) = P := by
  have hβ := βv_smul u hu hu1
  have h2 : (βv u * βv u) • E₀ K = E₀ K := mul_smul_E₀ hβ hβ
  have h3 : (βv u * βv u * βv u) • E₀ K = E₀ K := mul_smul_E₀ h2 hβ
  rw [σ_apply, σ_apply, σ_apply, ← act_mul _ _ hβ hβ h2, ← act_mul _ _ h2 hβ h3,
    act_congr (βv_mul_βv_mul_βv u hu hu1) _ (one_smul _ _)]
  apply xy_injective
  rw [xy_act]
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · show some (vcXInv (1 : VariableChange K) x, vcYInv (1 : VariableChange K) x y) = some (x, y)
    simp [vcXInv, vcYInv, VariableChange.one_def]

private theorem act_inv_eq (P : (E₀ K).toAffine.Point) :
    act (βv u)⁻¹ (inv_smul_E₀ (βv_smul u hu hu1)) P = σ u hu hu1 (σ u hu hu1 P) := by
  set Q := act (βv u)⁻¹ (inv_smul_E₀ (βv_smul u hu hu1)) P with hQ
  have hPQ : σ u hu hu1 Q = P := by rw [σ_apply, hQ, act_act_inv]
  conv_rhs => rw [← hPQ]
  rw [σ_σ_σ]

private theorem δ_eq_comp (P : (E₀ K).toAffine.Point) :
    act (δv u) (δv_smul u hu hu1) P =
      act (βv u)⁻¹ (inv_smul_E₀ (βv_smul u hu hu1)) (act (αv u) (αv_smul u hu hu1)
        (σ u hu hu1 (act (αv u)⁻¹ (inv_smul_E₀ (αv_smul u hu hu1)) P))) := by
  have hβ := βv_smul u hu hu1
  have hα := αv_smul u hu hu1
  have hβi := inv_smul_E₀ hβ
  have hαi := inv_smul_E₀ hα
  have h1 : (αv u * βv u) • E₀ K = E₀ K := mul_smul_E₀ hα hβ
  have h2 : (αv u * βv u * (αv u)⁻¹) • E₀ K = E₀ K := mul_smul_E₀ h1 hαi
  have h3 : ((βv u)⁻¹ * (αv u * βv u * (αv u)⁻¹)) • E₀ K = E₀ K := mul_smul_E₀ hβi h2
  rw [act_congr (δv_eq u hu hu1) _ h3, act_mul _ _ hβi h2 h3, act_mul _ _ h1 hαi h2, act_mul _ _ hα hβ h1]
  rfl

private theorem δ_δ (P : (E₀ K).toAffine.Point) :
    act (δv u) (δv_smul u hu hu1) (act (δv u) (δv_smul u hu hu1) P) = -P := by
  rw [← act_mul (δv u) (δv u) _ _ (mul_smul_E₀ (δv_smul u hu hu1) (δv_smul u hu hu1)) P,
    act_congr (δv_mul_δv u hu hu1) _ ε_smul, act_ε]

omit hu hu1 in
private theorem two_not_dvd_of_ne_zero {N : ℕ} (hN : (N : K) ≠ 0) : ¬2 ∣ N := by
  rintro ⟨c, rfl⟩
  apply hN
  push_cast
  rw [two_eq_zero, zero_mul]

private theorem exists_addOrderOf_eq_and_ne_smul [IsAlgClosed K] (N : ℕ) (hN : (N : K) ≠ 0)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    ∃ a : (E₀ K).toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, σ u hu hu1 a ≠ k • a := by
  have hp2 : p ≠ 2 := fun h => two_not_dvd_of_ne_zero hN (h ▸ hpN)
  have hN0 : N ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  have : NeZero N := ⟨hN0⟩
  obtain ⟨m, hm⟩ := hpN
  have hm0 : m ≠ 0 := fun h => hN0 (by rw [hm, h, mul_zero])
  have hp0 : p ≠ 0 := hp.ne_zero

  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) (E₀ K) (n := N) hN
  have hb : (E₀ K).baseChange K = E₀ K := by
    show (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).baseChange K = ⟨0, 0, 1, 0, 0⟩
    cases (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K)
    rfl
  obtain ⟨e⟩ : Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ (E₀ K).toAffine.Point N) :=
    hb ▸ ⟨e⟩
  set T := Submodule.torsionBy ℤ (E₀ K).toAffine.Point N with hT
  let Φ : ZMod N × ZMod N →+ (E₀ K).toAffine.Point :=
    T.subtype.toAddMonoidHom.comp e.toAddMonoidHom
  have hΦ : ∀ x, Φ x = Subtype.val (e x) := fun x => rfl
  have hΦinj : Function.Injective Φ := Subtype.val_injective.comp e.injective
  have hordm : addOrderOf ((m : ℕ) : ZMod N) = p := by
    rw [ZMod.addOrderOf_coe m hN0, hm, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hord : ∀ x : ZMod N × ZMod N, addOrderOf (Φ x) = addOrderOf x := fun x =>
    addOrderOf_injective Φ hΦinj x
  set u₀ : (E₀ K).toAffine.Point := Φ ((m : ZMod N), 0) with hu₀
  set v₀ : (E₀ K).toAffine.Point := Φ (0, (m : ZMod N)) with hv₀
  have hou : addOrderOf u₀ = p := by
    rw [hu₀, hord, Prod.addOrderOf, hordm, addOrderOf_zero, Nat.lcm_one_right]
  have hov : addOrderOf v₀ = p := by
    rw [hv₀, hord, Prod.addOrderOf, hordm, addOrderOf_zero, Nat.lcm_one_left]
  have houv : addOrderOf (u₀ + v₀) = p := by
    rw [hu₀, hv₀, ← map_add, hord, Prod.mk_add_mk, add_zero, zero_add, Prod.addOrderOf, hordm, Nat.lcm_self]
  have hsmulΦ : ∀ (k : ℕ) (x : ZMod N × ZMod N), k • Φ x = Φ (k • x) := fun k x => (map_nsmul Φ k x).symm

  have hspan : ∀ a : (E₀ K).toAffine.Point, p • a = 0 → ∃ i j : ℕ, a = i • u₀ + j • v₀ := by
    intro a ha
    have haT : a ∈ T := by
      rw [hT, Submodule.mem_torsionBy_iff]
      show (N : ℤ) • a = 0
      rw [natCast_zsmul, hm, mul_nsmul, ha, nsmul_zero]
    obtain ⟨⟨x, y⟩, hxy⟩ : ∃ q : ZMod N × ZMod N, e q = ⟨a, haT⟩ := e.surjective _
    have haΦ : a = Φ (x, y) := by rw [hΦ, hxy]
    have hpxy : (p : ℕ) • (x, y) = 0 := by
      apply hΦinj
      rw [← hsmulΦ, ← haΦ, ha, map_zero]
    simp only [Prod.smul_mk, Prod.mk_eq_zero, nsmul_eq_mul] at hpxy
    obtain ⟨hpx, hpy⟩ := hpxy
    have hdiv : ∀ z : ZMod N, (p : ZMod N) * z = 0 → ∃ i : ℕ, z = i • ((m : ℕ) : ZMod N) := by
      intro z hz
      have hz' : ((p * z.val : ℕ) : ZMod N) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact hz
      rw [ZMod.natCast_eq_zero_iff] at hz'
      have hz'' : p * m ∣ p * z.val := by rw [← hm]; exact hz'
      obtain ⟨i, hi⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hp0) hz''
      refine ⟨i, ?_⟩
      rw [nsmul_eq_mul, ← Nat.cast_mul, mul_comm, ← hi, ZMod.natCast_zmod_val]
    obtain ⟨i, hi⟩ := hdiv x hpx
    obtain ⟨j, hj⟩ := hdiv y hpy
    refine ⟨i, j, ?_⟩
    rw [haΦ, hu₀, hv₀, hsmulΦ, hsmulΦ, ← map_add]
    congr 1
    rw [hi, hj]
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add]

  by_contra hall
  push Not at hall
  obtain ⟨k₁, hk₁⟩ := hall u₀ hou
  obtain ⟨k₂, hk₂⟩ := hall v₀ hov
  obtain ⟨k, hk⟩ := hall (u₀ + v₀) houv
  have hcomp : (((k₁ * m : ℕ) : ZMod N), ((k₂ * m : ℕ) : ZMod N)) =
      (((k * m : ℕ) : ZMod N), ((k * m : ℕ) : ZMod N)) := by
    apply hΦinj
    have : σ u hu hu1 (u₀ + v₀) = k₁ • u₀ + k₂ • v₀ := by rw [map_add, hk₁, hk₂]
    rw [hk, smul_add] at this
    have e1 : k₁ • u₀ + k₂ • v₀ = Φ (((k₁ * m : ℕ) : ZMod N), ((k₂ * m : ℕ) : ZMod N)) := by
      rw [hu₀, hv₀, hsmulΦ, hsmulΦ, ← map_add]
      congr 1
      simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add, nsmul_eq_mul, Nat.cast_mul]
    have e2 : k • u₀ + k • v₀ = Φ (((k * m : ℕ) : ZMod N), ((k * m : ℕ) : ZMod N)) := by
      rw [hu₀, hv₀, hsmulΦ, hsmulΦ, ← map_add]
      congr 1
      simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add, nsmul_eq_mul, Nat.cast_mul]
    rw [← e1, ← e2, this]
  simp only [Prod.mk.injEq] at hcomp
  obtain ⟨hc₁, hc₂⟩ := hcomp
  have hσu : σ u hu hu1 u₀ = k • u₀ := by
    rw [hk₁, hu₀, hsmulΦ, hsmulΦ]
    congr 1
    simp only [Prod.smul_mk, smul_zero, nsmul_eq_mul, Nat.cast_mul] at hc₁ ⊢
    rw [hc₁]
  have hσv : σ u hu hu1 v₀ = k • v₀ := by
    rw [hk₂, hv₀, hsmulΦ, hsmulΦ]
    congr 1
    simp only [Prod.smul_mk, smul_zero, nsmul_eq_mul, Nat.cast_mul] at hc₂ ⊢
    rw [hc₂]

  have hpu : p • u₀ = 0 := by rw [← hou]; exact addOrderOf_nsmul_eq_zero u₀
  have hscalar : ∀ a : (E₀ K).toAffine.Point, p • a = 0 → σ u hu hu1 a = k • a := by
    intro a ha
    obtain ⟨i, j, rfl⟩ := hspan a ha
    rw [map_add, map_nsmul, map_nsmul, hσu, hσv, smul_add, smul_comm i k, smul_comm j k]

  have hkkk : k • (k • (k • u₀)) = u₀ := by
    have h3 := σ_σ_σ u hu hu1 u₀
    rwa [hσu, map_nsmul, hσu, map_nsmul, map_nsmul, hσu] at h3

  have hα := αv_smul u hu hu1
  have hδu : act (δv u) (δv_smul u hu hu1) u₀ = u₀ := by
    have hw : p • act (αv u)⁻¹ (inv_smul_E₀ hα) u₀ = 0 := by rw [← map_nsmul, hpu, map_zero]
    rw [δ_eq_comp u hu hu1, hscalar _ hw, map_nsmul, act_act_inv, map_nsmul, act_inv_eq u hu hu1, hσu,
      map_nsmul, hσu, hkkk]

  have hδδ := δ_δ u hu hu1 u₀
  rw [hδu, hδu] at hδδ
  have h2u : 2 • u₀ = 0 := by
    rw [two_nsmul]
    nth_rewrite 1 [hδδ]
    rw [neg_add_cancel]
  have hp2' : p ∣ 2 := hou ▸ addOrderOf_dvd_of_nsmul_eq_zero h2u
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2')

end Sigma

section Iota

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]
variable (u : Kˣ) (hu : (u : K) ^ 3 = 1) (hu1 : (u : K) ≠ 1)

private def δI : VariableChange K := ⟨1, (u : K) ^ 2, (u : K), (u : K) ^ 2⟩

include hu hu1

private theorem αv_mul_αv : αv u * αv u = (ε : VariableChange K) := by
  ext
  · simp [VariableChange.mul_def, αv, ε]
  · simp only [VariableChange.mul_def, αv, ε, Units.val_one]; simpa using add_self (1 : K)
  · simp only [VariableChange.mul_def, αv, ε, Units.val_one]; simpa using add_self (1 : K)
  · simp only [VariableChange.mul_def, αv, ε, Units.val_one]
    have := add_self (u : K)
    linear_combination this

private theorem conj_αv_eq : βv u * αv u * (βv u)⁻¹ = (⟨1, (u : K), (u : K) ^ 2, (u : K)⟩ : VariableChange K) := by
  have huinv := coe_inv_u u hu hu1
  have h4 := u_pow_four u hu hu1
  have h7 : (u : K) ^ 7 = (u : K) := by
    calc (u : K) ^ 7 = ((u : K) ^ 3) ^ 2 * (u : K) := by ring
      _ = (u : K) := by rw [hu]; ring
  rw [VariableChange.inv_def]
  ext
  · simp [VariableChange.mul_def, αv, βv]
  · simp only [VariableChange.mul_def, αv, βv, Units.val_mul, Units.val_one, huinv]
    linear_combination h4
  · simp only [VariableChange.mul_def, αv, βv, Units.val_mul, Units.val_one, huinv]
    ring
  · simp only [VariableChange.mul_def, αv, βv, Units.val_mul, Units.val_one, huinv]
    linear_combination h7

private theorem δI_smul : δI u • E₀ K = E₀ K := by
  have hsq := u_sq u hu hu1
  have h4 := u_pow_four u hu hu1
  refine (smul_E₀_eq_iff _).2 ⟨by simp [δI], by simp [δI], ?_, ?_⟩
  · show (u : K) ^ 4 = (u : K)
    exact h4
  · show ((u : K) ^ 2) ^ 2 + (u : K) ^ 2 = (u : K) ^ 3
    rw [hu]
    have h2 := two_eq_zero (K := K)
    have : ((u : K) ^ 2) ^ 2 = (u : K) ^ 3 * (u : K) := by ring
    rw [this, hu, one_mul, hsq]
    linear_combination (u : K) * h2

private theorem δI_eq : δI u = αv u * (βv u * αv u * (βv u)⁻¹) := by
  rw [conj_αv_eq u hu hu1]
  have h2 := two_eq_zero (K := K)
  have hsq := u_sq u hu hu1
  have hq' := hq u hu hu1
  ext
  · simp [VariableChange.mul_def, αv, δI]
  · simp only [VariableChange.mul_def, αv, δI, Units.val_one]
    rw [hsq]; ring
  · simp only [VariableChange.mul_def, αv, δI, Units.val_one]
    have := neg_eq (u : K)
    linear_combination -hq' - this
  · simp only [VariableChange.mul_def, αv, δI, Units.val_one]
    linear_combination -(u : K) * h2

private theorem δI_mul_δI : δI u * δI u = (ε : VariableChange K) := by
  have h2 := two_eq_zero (K := K)
  ext
  · simp [VariableChange.mul_def, δI, ε]
  · simp only [VariableChange.mul_def, δI, ε, Units.val_one]
    linear_combination (u : K) ^ 2 * h2
  · simp only [VariableChange.mul_def, δI, ε, Units.val_one]
    linear_combination (u : K) * h2
  · simp only [VariableChange.mul_def, δI, ε, Units.val_one]
    linear_combination (u : K) ^ 2 * h2 + hu

private def τ : (E₀ K).toAffine.Point →+ (E₀ K).toAffine.Point := act (αv u) (αv_smul u hu hu1)

private theorem τ_apply (P : (E₀ K).toAffine.Point) : τ u hu hu1 P = act (αv u) (αv_smul u hu hu1) P := rfl

private theorem τ_τ (P : (E₀ K).toAffine.Point) : τ u hu hu1 (τ u hu hu1 P) = -P := by
  rw [τ_apply, τ_apply, ← act_mul (αv u) (αv u) _ _ (mul_smul_E₀ (αv_smul u hu hu1) (αv_smul u hu hu1)) P,
    act_congr (αv_mul_αv u hu hu1) _ ε_smul, act_ε]

private theorem δI_δI (P : (E₀ K).toAffine.Point) :
    act (δI u) (δI_smul u hu hu1) (act (δI u) (δI_smul u hu hu1) P) = -P := by
  rw [← act_mul (δI u) (δI u) _ _ (mul_smul_E₀ (δI_smul u hu hu1) (δI_smul u hu hu1)) P,
    act_congr (δI_mul_δI u hu hu1) _ ε_smul, act_ε]

private theorem δI_eq_comp (P : (E₀ K).toAffine.Point) :
    act (δI u) (δI_smul u hu hu1) P =
      τ u hu hu1 (act (βv u) (βv_smul u hu hu1)
        (τ u hu hu1 (act (βv u)⁻¹ (inv_smul_E₀ (βv_smul u hu hu1)) P))) := by
  have hβ := βv_smul u hu hu1
  have hα := αv_smul u hu hu1
  have hβi := inv_smul_E₀ hβ
  have h1 : (βv u * αv u) • E₀ K = E₀ K := mul_smul_E₀ hβ hα
  have h2 : (βv u * αv u * (βv u)⁻¹) • E₀ K = E₀ K := mul_smul_E₀ h1 hβi
  have h3 : (αv u * (βv u * αv u * (βv u)⁻¹)) • E₀ K = E₀ K := mul_smul_E₀ hα h2
  rw [act_congr (δI_eq u hu hu1) _ h3, act_mul _ _ hα h2 h3, act_mul _ _ h1 hβi h2, act_mul _ _ hβ hα h1]
  rfl

private theorem exists_addOrderOf_eq_and_ne_smul_I [IsAlgClosed K] (N : ℕ) (hN : (N : K) ≠ 0)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) :
    ∃ a : (E₀ K).toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, τ u hu hu1 a ≠ k • a := by
  have hp2 : p ≠ 2 := fun h => two_not_dvd_of_ne_zero hN (h ▸ hpN)
  have hN0 : N ≠ 0 := fun h => hN (by rw [h, Nat.cast_zero])
  have : NeZero N := ⟨hN0⟩
  obtain ⟨m, hm⟩ := hpN
  have hm0 : m ≠ 0 := fun h => hN0 (by rw [hm, h, mul_zero])
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨e⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) (E₀ K) (n := N) hN
  have hb : (E₀ K).baseChange K = E₀ K := by
    show (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).baseChange K = ⟨0, 0, 1, 0, 0⟩
    cases (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K)
    rfl
  obtain ⟨e⟩ : Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ (E₀ K).toAffine.Point N) :=
    hb ▸ ⟨e⟩
  set T := Submodule.torsionBy ℤ (E₀ K).toAffine.Point N with hT
  let Φ : ZMod N × ZMod N →+ (E₀ K).toAffine.Point :=
    T.subtype.toAddMonoidHom.comp e.toAddMonoidHom
  have hΦ : ∀ x, Φ x = Subtype.val (e x) := fun x => rfl
  have hΦinj : Function.Injective Φ := Subtype.val_injective.comp e.injective
  have hordm : addOrderOf ((m : ℕ) : ZMod N) = p := by
    rw [ZMod.addOrderOf_coe m hN0, hm, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hord : ∀ x : ZMod N × ZMod N, addOrderOf (Φ x) = addOrderOf x := fun x =>
    addOrderOf_injective Φ hΦinj x
  set u₀ : (E₀ K).toAffine.Point := Φ ((m : ZMod N), 0) with hu₀
  set v₀ : (E₀ K).toAffine.Point := Φ (0, (m : ZMod N)) with hv₀
  have hou : addOrderOf u₀ = p := by
    rw [hu₀, hord, Prod.addOrderOf, hordm, addOrderOf_zero, Nat.lcm_one_right]
  have hov : addOrderOf v₀ = p := by
    rw [hv₀, hord, Prod.addOrderOf, hordm, addOrderOf_zero, Nat.lcm_one_left]
  have houv : addOrderOf (u₀ + v₀) = p := by
    rw [hu₀, hv₀, ← map_add, hord, Prod.mk_add_mk, add_zero, zero_add, Prod.addOrderOf, hordm, Nat.lcm_self]
  have hsmulΦ : ∀ (k : ℕ) (x : ZMod N × ZMod N), k • Φ x = Φ (k • x) := fun k x => (map_nsmul Φ k x).symm
  have hspan : ∀ a : (E₀ K).toAffine.Point, p • a = 0 → ∃ i j : ℕ, a = i • u₀ + j • v₀ := by
    intro a ha
    have haT : a ∈ T := by
      rw [hT, Submodule.mem_torsionBy_iff]
      show (N : ℤ) • a = 0
      rw [natCast_zsmul, hm, mul_nsmul, ha, nsmul_zero]
    obtain ⟨⟨x, y⟩, hxy⟩ : ∃ q : ZMod N × ZMod N, e q = ⟨a, haT⟩ := e.surjective _
    have haΦ : a = Φ (x, y) := by rw [hΦ, hxy]
    have hpxy : (p : ℕ) • (x, y) = 0 := by
      apply hΦinj
      rw [← hsmulΦ, ← haΦ, ha, map_zero]
    simp only [Prod.smul_mk, Prod.mk_eq_zero, nsmul_eq_mul] at hpxy
    obtain ⟨hpx, hpy⟩ := hpxy
    have hdiv : ∀ z : ZMod N, (p : ZMod N) * z = 0 → ∃ i : ℕ, z = i • ((m : ℕ) : ZMod N) := by
      intro z hz
      have hz' : ((p * z.val : ℕ) : ZMod N) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact hz
      rw [ZMod.natCast_eq_zero_iff] at hz'
      have hz'' : p * m ∣ p * z.val := by rw [← hm]; exact hz'
      obtain ⟨i, hi⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hp0) hz''
      refine ⟨i, ?_⟩
      rw [nsmul_eq_mul, ← Nat.cast_mul, mul_comm, ← hi, ZMod.natCast_zmod_val]
    obtain ⟨i, hi⟩ := hdiv x hpx
    obtain ⟨j, hj⟩ := hdiv y hpy
    refine ⟨i, j, ?_⟩
    rw [haΦ, hu₀, hv₀, hsmulΦ, hsmulΦ, ← map_add]
    congr 1
    rw [hi, hj]
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add]
  by_contra hall
  push Not at hall
  obtain ⟨k₁, hk₁⟩ := hall u₀ hou
  obtain ⟨k₂, hk₂⟩ := hall v₀ hov
  obtain ⟨k, hk⟩ := hall (u₀ + v₀) houv
  have hcomp : (((k₁ * m : ℕ) : ZMod N), ((k₂ * m : ℕ) : ZMod N)) =
      (((k * m : ℕ) : ZMod N), ((k * m : ℕ) : ZMod N)) := by
    apply hΦinj
    have : τ u hu hu1 (u₀ + v₀) = k₁ • u₀ + k₂ • v₀ := by rw [map_add, hk₁, hk₂]
    rw [hk, smul_add] at this
    have e1 : k₁ • u₀ + k₂ • v₀ = Φ (((k₁ * m : ℕ) : ZMod N), ((k₂ * m : ℕ) : ZMod N)) := by
      rw [hu₀, hv₀, hsmulΦ, hsmulΦ, ← map_add]
      congr 1
      simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add, nsmul_eq_mul, Nat.cast_mul]
    have e2 : k • u₀ + k • v₀ = Φ (((k * m : ℕ) : ZMod N), ((k * m : ℕ) : ZMod N)) := by
      rw [hu₀, hv₀, hsmulΦ, hsmulΦ, ← map_add]
      congr 1
      simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add, nsmul_eq_mul, Nat.cast_mul]
    rw [← e1, ← e2, this]
  simp only [Prod.mk.injEq] at hcomp
  obtain ⟨hc₁, hc₂⟩ := hcomp
  have hσu : τ u hu hu1 u₀ = k • u₀ := by
    rw [hk₁, hu₀, hsmulΦ, hsmulΦ]
    congr 1
    simp only [Prod.smul_mk, smul_zero, nsmul_eq_mul, Nat.cast_mul] at hc₁ ⊢
    rw [hc₁]
  have hσv : τ u hu hu1 v₀ = k • v₀ := by
    rw [hk₂, hv₀, hsmulΦ, hsmulΦ]
    congr 1
    simp only [Prod.smul_mk, smul_zero, nsmul_eq_mul, Nat.cast_mul] at hc₂ ⊢
    rw [hc₂]
  have hpu : p • u₀ = 0 := by rw [← hou]; exact addOrderOf_nsmul_eq_zero u₀
  have hscalar : ∀ a : (E₀ K).toAffine.Point, p • a = 0 → τ u hu hu1 a = k • a := by
    intro a ha
    obtain ⟨i, j, rfl⟩ := hspan a ha
    rw [map_add, map_nsmul, map_nsmul, hσu, hσv, smul_add, smul_comm i k, smul_comm j k]
  have hβ := βv_smul u hu hu1
  have hσ' : act (βv u) hβ (τ u hu hu1 (act (βv u)⁻¹ (inv_smul_E₀ hβ) u₀)) = k • u₀ := by
    have hw : p • act (βv u)⁻¹ (inv_smul_E₀ hβ) u₀ = 0 := by rw [← map_nsmul, hpu, map_zero]
    rw [hscalar _ hw, map_nsmul, act_act_inv]
  have hδu : act (δI u) (δI_smul u hu hu1) u₀ = k • (k • u₀) := by
    rw [δI_eq_comp u hu hu1, hσ', map_nsmul, hσu]
  have hkk : k • (k • u₀) = -u₀ := by
    rw [← τ_τ u hu hu1 u₀, hσu, map_nsmul, hσu]
  have hδδ : act (δI u) (δI_smul u hu hu1) (act (δI u) (δI_smul u hu hu1) u₀) = u₀ := by
    rw [hδu, map_nsmul, map_nsmul, hδu, hkk, smul_neg, smul_neg, hkk, neg_neg]
  rw [δI_δI u hu hu1 u₀] at hδδ
  have h2u : 2 • u₀ = 0 := by
    rw [two_nsmul]
    nth_rewrite 1 [← hδδ]
    rw [neg_add_cancel]
  have hp2' : p ∣ 2 := hou ▸ addOrderOf_dvd_of_nsmul_eq_zero h2u
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2')

end Iota

section Main

variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K]

private theorem act_pow_eq_iterate (γ : VariableChange K) (hγ : γ • E₀ K = E₀ K)
    (φ : (E₀ K).toAffine.Point →+ (E₀ K).toAffine.Point) (hφ : ∀ P, act γ hγ P = φ P) :
    ∀ (k : ℕ) (hk : (γ ^ k) • E₀ K = E₀ K) (P : (E₀ K).toAffine.Point), act (γ ^ k) hk P = φ^[k] P := by
  intro k
  induction k with
  | zero =>
    intro hk P
    rw [act_congr (pow_zero γ) hk (one_smul _ _)]
    show act 1 (one_smul _ _) P = P
    apply xy_injective
    rw [xy_act]
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · show some (vcXInv (1 : VariableChange K) x, vcYInv (1 : VariableChange K) x y) = some (x, y)
      simp [vcXInv, vcYInv, VariableChange.one_def]
  | succ k ih =>
    intro hk P
    have hk' : (γ ^ k) • E₀ K = E₀ K := by
      clear ih hk
      induction k with
      | zero => rw [pow_zero, one_smul]
      | succ k ih => rw [pow_succ, mul_smul, hγ, ih]
    rw [act_congr (pow_succ γ k) hk (mul_smul_E₀ hk' hγ), act_mul _ _ hk' hγ (mul_smul_E₀ hk' hγ), ih hk',
      hφ, Function.iterate_succ_apply]

private theorem pow_smul_E₀ {γ : VariableChange K} (hγ : γ • E₀ K = E₀ K) (k : ℕ) : (γ ^ k) • E₀ K = E₀ K := by
  induction k with
  | zero => rw [pow_zero, one_smul]
  | succ k ih => rw [pow_succ, mul_smul, hγ, ih]

variable [IsAlgClosed K] (u : Kˣ) (hu : (u : K) ^ 3 = 1) (hu1 : (u : K) ≠ 1)
include hu hu1

private theorem main (M : ℕ) (hM : (M : K) ≠ 0) :
    ∃ σ' ι' : (E₀ K).toAffine.Point →+ (E₀ K).toAffine.Point,
      (∀ (k : ℕ) (P : (E₀ K).toAffine.Point),
        HEq (Point.vcInvFun ((⟨u, 0, 0, 0⟩ : VariableChange K) ^ k) (E₀ K).toAffine P) (σ'^[k] P)) ∧
      (∀ (k : ℕ) (P : (E₀ K).toAffine.Point),
        HEq (Point.vcInvFun ((⟨1, 1, 1, (u : K)⟩ : VariableChange K) ^ k) (E₀ K).toAffine P) (ι'^[k] P)) ∧
      (∀ P, σ' (σ' P) + σ' P + P = 0) ∧ (∀ P, ι' (ι' P) = -P) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → ∃ a : (E₀ K).toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, σ' a ≠ k • a) ∧
      (∀ p : ℕ, p.Prime → p ∣ M → ∃ a : (E₀ K).toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, ι' a ≠ k • a) := by
  refine ⟨σ u hu hu1, τ u hu hu1, ?_, ?_, σ_σ_add u hu hu1, τ_τ u hu hu1,
    fun p hp hpM => exists_addOrderOf_eq_and_ne_smul u hu hu1 M hM p hp hpM,
    fun p hp hpM => exists_addOrderOf_eq_and_ne_smul_I u hu hu1 M hM p hp hpM⟩
  · intro k P
    have hk := pow_smul_E₀ (βv_smul u hu hu1) k
    have h1 : HEq (Point.vcInvFun ((⟨u, 0, 0, 0⟩ : VariableChange K) ^ k) (E₀ K).toAffine P)
        (act (βv u ^ k) hk P) := heq_act _ hk P
    refine h1.trans (heq_of_eq ?_)
    exact act_pow_eq_iterate (βv u) (βv_smul u hu hu1) (σ u hu hu1) (fun P => rfl) k hk P
  · intro k P
    have hk := pow_smul_E₀ (αv_smul u hu hu1) k
    have h1 : HEq (Point.vcInvFun ((⟨1, 1, 1, (u : K)⟩ : VariableChange K) ^ k) (E₀ K).toAffine P)
        (act (αv u ^ k) hk P) := heq_act _ hk P
    refine h1.trans (heq_of_eq ?_)
    exact act_pow_eq_iterate (αv u) (αv_smul u hu hu1) (τ u hu hu1) (fun P => rfl) k hk P

end Main

/-- **The exceptional automorphisms in characteristic two.**  On
`E₀ : y² + y = x³` over an algebraically closed field `L` of characteristic `2`,
the order-three variable change `(x, y) ↦ (wx, y)` and the order-four variable
change `(x, y) ↦ (x + 1, y + w)` (with `w³ = 1`, `w ≠ 1`) are packaged as additive
endomorphisms `σ`, `ι` of `E₀(L)`, realized through `Point.vcInvFun` as a
heterogeneous equality; `σ² + σ + 1 = 0`, `ι² = -1`, and neither is scalar on any
`p`-torsion for a prime `p ∣ M` (with `M` invertible in `L`).  The pin
`WeierstrassCurve.exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two`
verbatim (Silverman III.10.1 + Appendix A Prop. 1.2). -/
theorem exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]
    (w : Lˣ) (hw : (w : L) ^ 3 = 1) (hw1 : (w : L) ≠ 1) (M : ℕ) (hM : (M : L) ≠ 0) :
    ∃ σ ι : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point →+
        (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point,
      (∀ (k : ℕ) (P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point),
        HEq (Point.vcInvFun ((⟨w, 0, 0, 0⟩ : VariableChange L) ^ k)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine P) (σ^[k] P)) ∧
      (∀ (k : ℕ) (P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point),
        HEq (Point.vcInvFun ((⟨1, 1, 1, (w : L)⟩ : VariableChange L) ^ k)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine P) (ι^[k] P)) ∧
      (∀ P, σ (σ P) + σ P + P = 0) ∧ (∀ P, ι (ι P) = -P) ∧
      (∀ p : ℕ, p.Prime → p ∣ M →
        ∃ a : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point,
          addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) ∧
      (∀ p : ℕ, p.Prime → p ∣ M →
        ∃ a : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point,
          addOrderOf a = p ∧ ∀ k : ℕ, ι a ≠ k • a) :=
  main w hw hw1 M hM

end WeierstrassCurve
