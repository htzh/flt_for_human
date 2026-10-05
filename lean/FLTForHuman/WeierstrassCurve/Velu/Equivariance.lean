/-
The Vélu base-change / variable-change definition layer (V1-SET-2).

Statements are transcribed verbatim from the pinned FLT `aa2d8b3` sources:

* `Definitions/Def_WeierstrassCurve_VariableChangePointEquiv.lean` — the
  variable-change point transport `vcX`/`vcY`/`vcXInv`/`vcYInv`, `vcFun`,
  `vcInvFun` and `variableChangeEquiv`.  This is a strict prerequisite of the
  next file (`Def_WeierstrassCurve_VeluVariableChange` imports it) and is
  therefore carried here; SET-3's `VariableChangePoint.lean` order is amended
  accordingly (see the port log, `V1 SET-2`).
* `Definitions/Def_WeierstrassCurve_VeluVariableChange.lean` (112 lines, whole
  file) — `vcInvEmbedding` and `variableChange_velu{Gy,Gx,T,U,W,TSum,WSum}`.
* `Definitions/Def_WeierstrassCurve_VeluEquivariance.lean` lines 1–67 — the
  `map_velu{Gx,Gy,T,U,W}`/`map_veluTSum`/`map_veluWSum`/`map_veluQuotient` block.
  That block is **not** re-declared here: the port already carries all eight
  declarations in `Velu/Formula.lean` (transcribed there by the earlier H5/SET-1
  work, with identical statements), and a second declaration of the same names
  would be a silent cross-module duplicate. The pin file is still listed in
  `spec/check_flt_statements.py`'s `SOURCES`, so those eight are now verified
  against the pin's public source rather than its `private` dotted copy. The
  file's tail (12/13 declarations) and `Def_…_VeluBundledMap` (referenced 0/8)
  are not ported.

Only proof bodies are adapted to mathlib `v4.34.0`; no statement moves. The
port's `import Mathlib` is replaced by the specific modules the pin names.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluVariableChange.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluEquivariance.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.Defs
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

set_option autoImplicit false

noncomputable section

open Polynomial

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K]

section Formulas

variable (C : VariableChange K) (W : WeierstrassCurve.Affine K)

def vcX (x' : K) : K := (C.u : K) ^ 2 * x' + C.r

def vcY (x' y' : K) : K := (C.u : K) ^ 3 * y' + (C.u : K) ^ 2 * C.s * x' + C.t

def vcXInv (x : K) : K := ((C.u⁻¹ : Kˣ) : K) ^ 2 * (x - C.r)

def vcYInv (x y : K) : K := ((C.u⁻¹ : Kˣ) : K) ^ 3 * (y - C.t - C.s * (x - C.r))

variable {C W}

private lemma u_ne_zero : (C.u : K) ≠ 0 := C.u.ne_zero
private lemma u_pow_ne_zero (n : ℕ) : ((C.u : K)) ^ n ≠ 0 := pow_ne_zero n C.u.ne_zero

@[simp] lemma vcX_vcXInv (x : K) : vcX C (vcXInv C x) = x := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp] lemma vcY_vcYInv (x y : K) : vcY C (vcXInv C x) (vcYInv C x y) = y := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcY, vcXInv, vcYInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp] lemma vcXInv_vcX (x' : K) : vcXInv C (vcX C x') = x' := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcXInv, Units.val_inv_eq_inv_val]; field_simp; ring

@[simp] lemma vcYInv_vcY (x' y' : K) : vcYInv C (vcX C x') (vcY C x' y') = y' := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, vcYInv, Units.val_inv_eq_inv_val]; field_simp; ring

private lemma equation_aux (x' y' : K) :
    vcY C x' y' ^ 2 + W.a₁ * vcX C x' * vcY C x' y' + W.a₃ * vcY C x' y'
      - (vcX C x' ^ 3 + W.a₂ * vcX C x' ^ 2 + W.a₄ * vcX C x' + W.a₆)
    = (C.u : K) ^ 6 *
      (y' ^ 2 + (C • W).a₁ * x' * y' + (C • W).a₃ * y'
        - (x' ^ 3 + (C • W).a₂ * x' ^ 2 + (C • W).a₄ * x' + (C • W).a₆)) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma partialX_aux (x' y' : K) :
    W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄)
      + C.s * (2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃)
    = (C.u : K) ^ 4 *
      ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄)) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp; ring

private lemma partialY_aux (x' y' : K) :
    2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃
      = (C.u : K) ^ 3 * (2 * y' + (C • W).a₁ * x' + (C • W).a₃) := by
  have hu : (C.u : K) ≠ 0 := u_ne_zero
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp; ring

lemma equation_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Equation x' y' ↔ W.Equation (vcX C x') (vcY C x' y') := by
  rw [equation_iff', equation_iff', equation_aux x' y', mul_eq_zero,
    or_iff_right (u_pow_ne_zero 6)]

private lemma partials_zero_iff (x' y' : K) :
    ((C • W).a₁ * y' - (3 * x' ^ 2 + 2 * (C • W).a₂ * x' + (C • W).a₄) = 0
        ∧ 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0)
      ↔ (W.a₁ * vcY C x' y' - (3 * vcX C x' ^ 2 + 2 * W.a₂ * vcX C x' + W.a₄) = 0
        ∧ 2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃ = 0) := by
  constructor
  · rintro ⟨hX', hY'⟩
    have hY : 2 * vcY C x' y' + W.a₁ * vcX C x' + W.a₃ = 0 := by
      rw [partialY_aux x' y', hY', mul_zero]
    refine ⟨?_, hY⟩
    have hX := partialX_aux (C := C) (W := W) x' y'
    rw [hX', mul_zero, hY, mul_zero, add_zero] at hX
    exact hX
  · rintro ⟨hX, hY⟩
    have hY' : 2 * y' + (C • W).a₁ * x' + (C • W).a₃ = 0 := by
      have h := partialY_aux (C := C) (W := W) x' y'
      rw [hY] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (u_pow_ne_zero 3)
    refine ⟨?_, hY'⟩
    have h := partialX_aux (C := C) (W := W) x' y'
    rw [hX, hY, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (u_pow_ne_zero 4)

lemma nonsingular_variableChange_iff (x' y' : K) :
    (C • W).toAffine.Nonsingular x' y' ↔ W.Nonsingular (vcX C x') (vcY C x' y') := by
  rw [nonsingular_iff', nonsingular_iff', equation_variableChange_iff x' y']
  refine and_congr_right fun _ => not_iff_not.mp ?_
  push_neg
  exact partials_zero_iff x' y'

end Formulas

section PointEquiv

variable [DecidableEq K] (C : VariableChange K) (W : WeierstrassCurve.Affine K)

namespace Point

def vcFun : (C • W).toAffine.Point → W.Point
  | 0 => 0
  | .some x' y' h => .some (vcX C x') (vcY C x' y')
      ((nonsingular_variableChange_iff x' y').mp h)

def vcInvFun : W.Point → (C • W).toAffine.Point
  | 0 => 0
  | .some x y h => .some (vcXInv C x) (vcYInv C x y)
      ((nonsingular_variableChange_iff (vcXInv C x) (vcYInv C x y)).mpr
        (by rwa [vcX_vcXInv, vcY_vcYInv]))

variable {C W}

@[simp] lemma vcFun_zero : vcFun C W 0 = 0 := rfl
@[simp] lemma vcInvFun_zero : vcInvFun C W 0 = 0 := rfl

private lemma some_eq_some {W' : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W'.Nonsingular x₁ y₁} {h₂ : W'.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by subst hx hy; rfl

lemma vcFun_leftInverse : Function.LeftInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x', y', h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcXInv_vcX x') (vcYInv_vcY x' y')

lemma vcFun_rightInverse : Function.RightInverse (vcInvFun C W) (vcFun C W) := by
  rintro (_ | ⟨x, y, h⟩)
  · rfl
  · simp only [vcFun, vcInvFun]
    exact some_eq_some (vcX_vcXInv x) (vcY_vcYInv x y)

variable (C W) in

noncomputable def variableChangeEquiv : (C • W).toAffine.Point ≃ W.Point :=
  ⟨vcFun C W, vcInvFun C W, vcFun_leftInverse, vcFun_rightInverse⟩

noncomputable def equivOfVariableChangeEq {V : WeierstrassCurve.Affine K}
    (h : C • W = V) : V.Point ≃ W.Point := by
  subst h; exact variableChangeEquiv C W

end Point

end PointEquiv

end WeierstrassCurve.Affine
namespace WeierstrassCurve

variable {K : Type*} [Field K]

section Embedding

variable (C : VariableChange K)

def vcInvEmbedding : K × K ↪ K × K where
  toFun P := (Affine.vcXInv C P.1, Affine.vcYInv C P.1 P.2)
  inj' := by
    intro P P' h
    have h1 : Affine.vcXInv C P.1 = Affine.vcXInv C P'.1 := congrArg Prod.fst h
    have h2 : Affine.vcYInv C P.1 P.2 = Affine.vcYInv C P'.1 P'.2 := congrArg Prod.snd h
    have hx : P.1 = P'.1 := by
      have := congrArg (Affine.vcX C) h1
      simpa only [Affine.vcX_vcXInv] using this
    have hy : P.2 = P'.2 := by
      have := congrArg (Affine.vcY C (Affine.vcXInv C P.1)) h2
      rw [Affine.vcY_vcYInv, hx] at this
      simpa only [Affine.vcY_vcYInv] using this
    exact Prod.ext hx hy

@[simp] lemma vcInvEmbedding_apply (P : K × K) :
    vcInvEmbedding C P = (Affine.vcXInv C P.1, Affine.vcYInv C P.1 P.2) := rfl

end Embedding

section PerPoint

variable (C : VariableChange K) (W : WeierstrassCurve K)

lemma variableChange_veluGy (x y : K) :
    (C • W).veluGy (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 3 * W.veluGy x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluGx (x y : K) :
    (C • W).veluGx (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * (W.veluGx x y + C.s * W.veluGy x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluGx, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₂, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluT (x y : K) :
    (C • W).veluT (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * W.veluT x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluT, veluGx, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluU (x y : K) :
    (C • W).veluU (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * W.veluU x y := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluU, veluGy, Affine.vcXInv, Affine.vcYInv, variableChange_a₁,
    variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

lemma variableChange_veluW (x y : K) :
    (C • W).veluW (Affine.vcXInv C x) (Affine.vcYInv C x y)
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * (W.veluW x y - C.r * W.veluT x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  simp only [veluW, veluU, veluT, veluGx, veluGy, Affine.vcXInv, Affine.vcYInv,
    variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

end PerPoint

section Sums

variable (C : VariableChange K) (W : WeierstrassCurve K) (S : Finset (K × K))

lemma variableChange_veluTSum :
    (C • W).veluTSum (S.map (vcInvEmbedding C))
      = ((C.u⁻¹ : Kˣ) : K) ^ 4 * W.veluTSum S := by
  rw [veluTSum, veluTSum, Finset.sum_map, Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluT C W P.1 P.2

lemma variableChange_veluWSum :
    (C • W).veluWSum (S.map (vcInvEmbedding C))
      = ((C.u⁻¹ : Kˣ) : K) ^ 6 * (W.veluWSum S - C.r * W.veluTSum S) := by
  rw [veluWSum, Finset.sum_map]
  rw [show W.veluWSum S - C.r * W.veluTSum S
      = ∑ P ∈ S, (W.veluW P.1 P.2 - C.r * W.veluT P.1 P.2) by
    rw [veluWSum, veluTSum, Finset.mul_sum, ← Finset.sum_sub_distrib]]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simpa only [vcInvEmbedding_apply] using variableChange_veluW C W P.1 P.2

end Sums

end WeierstrassCurve
