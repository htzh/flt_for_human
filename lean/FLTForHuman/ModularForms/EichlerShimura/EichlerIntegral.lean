/-
Copyright (c) 2026 FLT-for-human contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT-for-human contributors
-/

import FLTForHuman.ModularForms.Analytic.CuspBoundedness
import FLTForHuman.ModularForms.EichlerShimura.BinaryForm
import FLTForHuman.ModularForms.EichlerShimura.CoeffCohomology
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# The line cocycle, `j`-factors and Eichler integrals

This module supplies the equivariance vocabulary through which the weight-`n`
binary-form representation of `BinaryForm.lean` sees the hyperbolic action:

* `linePow n τ` — the `n`-th power of the linear form `C τ * X 0 + X 1` as an
  element of `BinaryForm ℂ n`; `isHomogeneous_line`/`isHomogeneous_linePow`
  establish that the power is homogeneous;
* `jFactor g τ` — the classical automorphy factor `c τ + d`, identified with
  mathlib's `UpperHalfPlane.denom` of the induced real matrix (`jFactor_eq_denom`)
  and hence non-zero (`jFactor_ne_zero`);
* `binarySubst_line` — substitution of a linear form, and its representation
  consequence `binaryFormRepSL_linePow`: the line transforms by the `n`-th power
  of `jFactor`;
* `IsEquivariantPrimitiveWith ρ F` — `F` is equivariant up to a *constant*
  cocycle; its `cocycle γ = F (γ • I) - ρ γ (F I)`, the difference formula
  `sub_eq_cocycle`, the smul form `apply_smul` and the cocycle identity
  `cocycle_mem_coeffCocycles` (a genuine `coeffCocycles` element);
* `IsEichlerIntegral n f F` — `F : ℍ → BinaryForm ℂ n` is a primitive of `f`
  coefficientwise: `d/dτ` of each coefficient of `F` is the corresponding
  coefficient of `f · linePow n τ`.

## FLT source and pin

Pin `aa2d8b3`: `Definitions/Def_HeckeEis_EichlerIntegral.lean`, the `LinePow`,
`Equivariant` and `EichlerIntegral` blocks (lines 12–110),
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeEis_EichlerIntegral.lean#L12-L110>.
Every declaration is the pin's verbatim, names and signatures included.

## Divergence from the pin (playbook §7.4)

The pin's `EichlerIntegral` block continues with
`eichlerShimuraMap` (a `dif` on the existence of an Eichler integral admitting
an equivariant primitive with parabolic cocycle, falling back to `0`),
`eichlerShimuraMap_def` and `eichlerShimuraMap_of_not_exists` (lines 112–144).
**These are deliberately omitted.** The port replaces the `dif`ed map with a
structural `periodMap` in Tier 3, built from a chosen Eichler integral
(`Classical.choose` of `exists_isEichlerIntegral`) whose class is shown
independent of the choice; that makes linearity structural rather than a case
split and leaves the pin's two wrapper lemmas behind (topic §3 Tier 1).

## What this module assumes

`BinaryForm.lean` (`BinaryForm`, `binarySubst`, `binaryFormRepSL` and their
lemmas) and `CoeffCohomology.lean` (`coeffCocycles`); then mathlib:
`UpperHalfPlane.denom`, `UpperHalfPlane.coe_specialLinearGroup_apply` and the
`SL(2, ℤ)`-action on `ℍ` from
`Analysis.Complex.UpperHalfPlane.MoebiusAction`, and `HasDerivAt` from
`Analysis.Calculus.Deriv.Basic`. Nothing else from `FLTForHuman`.

## Adaptation notes (mathlib `v4.34.0`)

`MvPolynomial.coeff` is no longer reachable as a qualified name; the pin's
`MvPolynomial.coeff d p` is written `p.coeff d` in `IsEichlerIntegral`. Every
other statement is the pin's verbatim.
-/

noncomputable section

open UpperHalfPlane MvPolynomial
open scoped MatrixGroups UpperHalfPlane ModularForm

namespace HeckeEis

section LinePow

variable (n : ℕ)

theorem isHomogeneous_line (τ : ℂ) : (C τ * X 0 + X 1 : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
  ((isHomogeneous_X ℂ 0).C_mul τ).add (isHomogeneous_X ℂ 1)

theorem isHomogeneous_linePow (τ : ℂ) : ((C τ * X 0 + X 1 : MvPolynomial (Fin 2) ℂ) ^ n).IsHomogeneous n := by
  simpa using (isHomogeneous_line τ).pow n

/-- The `n`-th power of the linear form `C τ * X 0 + X 1`, as a binary form. -/
def linePow (τ : ℂ) : ↥(BinaryForm ℂ n) :=
  ⟨(C τ * X 0 + X 1) ^ n, (mem_homogeneousSubmodule n _).mpr (isHomogeneous_linePow n τ)⟩

@[simp] theorem coe_linePow (τ : ℂ) :
    ((linePow n τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = (C τ * X 0 + X 1) ^ n := rfl

/-- The automorphy factor `c τ + d` of `g = [[a, b], [c, d]]`. -/
def jFactor (g : SL(2, ℤ)) (τ : ℍ) : ℂ := ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) + ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)

theorem jFactor_eq_denom (g : SL(2, ℤ)) (τ : ℍ) :
    jFactor g τ = denom (Matrix.SpecialLinearGroup.mapGL ℝ g) (τ : ℂ) := by
  rw [jFactor, Matrix.SpecialLinearGroup.mapGL, MonoidHom.comp_apply,
    show (algebraMap ℤ ℝ) = Int.castRingHom ℝ from rfl, ModularGroup.denom_apply]

theorem jFactor_ne_zero (g : SL(2, ℤ)) (τ : ℍ) : jFactor g τ ≠ 0 := by
  rw [jFactor_eq_denom]
  exact denom_ne_zero _ τ

theorem coe_smul_mul_jFactor (g : SL(2, ℤ)) (τ : ℍ) :
    ((g • τ : ℍ) : ℂ) * jFactor g τ
      = ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (τ : ℂ) + ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) := by
  rw [coe_specialLinearGroup_apply]
  have hj := jFactor_ne_zero g τ
  simp only [jFactor, eq_intCast, Complex.ofReal_intCast] at hj ⊢
  rw [div_mul_cancel₀ _ hj]

theorem binarySubst_line (M : Matrix (Fin 2) (Fin 2) ℤ) (τ : ℂ) :
    binarySubst ℂ M (C τ * X 0 + X 1)
      = C ((M 0 0 : ℂ) * τ + (M 0 1 : ℂ)) * X 0 + C ((M 1 0 : ℂ) * τ + (M 1 1 : ℂ)) * X 1 := by
  simp only [map_add, map_mul, binarySubst_C, binarySubst_X, Fin.sum_univ_two, Fin.isValue]
  ring

theorem binaryFormRepSL_linePow (g : SL(2, ℤ)) (τ : ℍ) :
    binaryFormRepSL ℂ n g (linePow n (τ : ℂ)) = (jFactor g τ) ^ n • linePow n ((g • τ : ℍ) : ℂ) := by
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe, Submodule.coe_smul, coe_linePow, coe_linePow, map_pow, binarySubst_line,
    smul_eq_C_mul, map_pow, ← mul_pow]
  congr 1
  rw [mul_add, ← mul_assoc, ← map_mul, mul_comm (jFactor g τ), coe_smul_mul_jFactor]
  rfl

end LinePow

section Equivariant

variable {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]

/-- `F` is equivariant for `ρ` up to a locally constant (constant) cocycle. -/
def IsEquivariantPrimitiveWith (ρ : Representation K Γ V) (F : ℍ → V) : Prop :=
  ∀ γ : Γ, ∃ c : V, ∀ τ : ℍ, F ((γ : SL(2, ℤ)) • τ) - ρ γ (F τ) = c

namespace IsEquivariantPrimitiveWith

variable {ρ : Representation K Γ V} {F : ℍ → V}

/-- The obstruction cocycle of an equivariant primitive, evaluated at the base point `I`. -/
def cocycle (_hF : IsEquivariantPrimitiveWith ρ F) (γ : Γ) : V :=
  F ((γ : SL(2, ℤ)) • I) - ρ γ (F I)

theorem sub_eq_cocycle (hF : IsEquivariantPrimitiveWith ρ F) (γ : Γ) (τ : ℍ) :
    F ((γ : SL(2, ℤ)) • τ) - ρ γ (F τ) = hF.cocycle γ := by
  obtain ⟨c, hc⟩ := hF γ
  rw [cocycle, hc τ, hc I]

theorem apply_smul (hF : IsEquivariantPrimitiveWith ρ F) (γ : Γ) (τ : ℍ) :
    F ((γ : SL(2, ℤ)) • τ) = hF.cocycle γ + ρ γ (F τ) := by
  rw [← hF.sub_eq_cocycle γ τ, sub_add_cancel]

theorem cocycle_mem_coeffCocycles (hF : IsEquivariantPrimitiveWith ρ F) : hF.cocycle ∈ coeffCocycles ρ := by
  intro γ δ
  have h := hF.apply_smul (γ * δ) I
  rw [Subgroup.coe_mul, mul_smul, hF.apply_smul γ, hF.apply_smul δ, map_add, map_mul, Module.End.mul_apply] at h

  have := congrArg (fun v => v - ρ γ (ρ δ (F I))) h
  simp only [add_sub_cancel_right] at this
  rw [← this]
  abel

end IsEquivariantPrimitiveWith

end Equivariant

section EichlerIntegral

variable (n : ℕ)

/-- `F : ℍ → BinaryForm ℂ n` is an Eichler integral of `f` if each coefficient of
`F` has derivative the corresponding coefficient of `f · linePow n τ`. -/
def IsEichlerIntegral (f : ℍ → ℂ) (F : ℍ → ↥(BinaryForm ℂ n)) : Prop :=
  ∀ (d : Fin 2 →₀ ℕ) (τ : ℍ),
    HasDerivAt (fun z : ℂ => ((F (ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d)
      (f τ * ((linePow n (τ : ℂ) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d) (τ : ℂ)

end EichlerIntegral

/-! ## Tier 2 — the Eichler-integral leaves

The Tier-2 leaves of the general-weight Eichler–Shimura cone that live on
`IsEichlerIntegral`: it is closed under addition and scalar multiplication, it is
stable under the weight-`n + 2` slash action, two Eichler integrals of the same
form differ by a constant binary form, and the obstruction cocycles of two
equivariant primitives differing by a constant are cohomologous.

The two pin files `S_HeckeEis_IsEichlerIntegral_slash.lean` and
`S_HeckeEis_IsEichlerIntegral_exists_sub_eq_const.lean` carry a byte-identical
private helper block `EichlerIntegralAux`; it is transcribed **once** here as the
`private` block below (playbook §7 checklist item 7). The pin's
`apply_eq_apply_of_hasDerivAt_zero`, the ninth member of that block, is **not**
re-derived: it is already public in `ModularForms/Analytic/CuspBoundedness.lean`
as `UpperHalfPlane.apply_eq_apply_of_hasDerivAt_zero` and is used from there
(playbook §9).

The pin's `MvPolynomial.coeff d p` is written `p.coeff d` (mathlib `v4.34.0` no
longer exposes `coeff` as a qualified name), and `SL_slash_apply` is
`ModularForm.SL_slash_apply`. -/

section Tier2Aux

/-- The exponent pairs of a weight-`n` binary form, `(k, n - k)` for `k ≤ n`. -/
private def degExps (n : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  (Finset.range (n + 1)).image fun k => Finsupp.single 0 k + Finsupp.single 1 (n - k)

private theorem mem_degExps_iff (n : ℕ) (d : Fin 2 →₀ ℕ) : d ∈ degExps n ↔ d.degree = n := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp only [degExps, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp
    omega
  · intro h
    refine ⟨d 0, by omega, ?_⟩
    ext i
    fin_cases i <;> simp
    omega

private theorem coeff_eq_zero_of_not_mem_degExps {K : Type*} [CommRing K] {n : ℕ}
    {p : MvPolynomial (Fin 2) K} (hp : p ∈ BinaryForm K n) {d : Fin 2 →₀ ℕ}
    (hd : d ∉ degExps n) : p.coeff d = 0 :=
  ((mem_homogeneousSubmodule n p).mp hp).coeff_eq_zero (by rwa [mem_degExps_iff] at hd)

private theorem eq_sum_degExps {K : Type*} [CommRing K] {n : ℕ} {p : MvPolynomial (Fin 2) K}
    (hp : p ∈ BinaryForm K n) : p = ∑ e ∈ degExps n, monomial e (p.coeff e) := by
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hd : d ∈ degExps n
  · rw [Finset.sum_eq_single d (fun e _ hne => ite_eq_right hne) (fun h => (h hd).elim), ite_eq_left rfl]
  · rw [Finset.sum_eq_zero (fun e he => ite_eq_right (fun h : e = d => hd (h ▸ he))),
      coeff_eq_zero_of_not_mem_degExps hp hd]

private theorem coeff_binaryFormRepSL_eq_sum {K : Type*} [CommRing K] {n : ℕ}
    (g : SL(2, ℤ)) (v : ↥(BinaryForm K n)) (d : Fin 2 →₀ ℕ) :
    ((binaryFormRepSL K n g v : ↥(BinaryForm K n)) : MvPolynomial (Fin 2) K).coeff d
      = ∑ e ∈ degExps n, (v : MvPolynomial (Fin 2) K).coeff e
          * (binarySubst K (g : Matrix (Fin 2) (Fin 2) ℤ) (monomial e 1)).coeff d := by
  rw [binaryFormRepSL_apply_coe]
  conv_lhs => rw [eq_sum_degExps v.2, map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show monomial e ((v : MvPolynomial (Fin 2) K).coeff e) = (v : MvPolynomial (Fin 2) K).coeff e • monomial e (1 : K) by
      rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, coeff_smul, smul_eq_mul]

private theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1; try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

private theorem hasDerivAt_comp_smul {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (γ • ofComplex z))
      (g (γ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  have hfun : (fun z : ℂ => G (γ • ofComplex z))
      = (G ∘ ofComplex) ∘ (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (G ∘ ofComplex) (g (γ • τ))
      ((fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (γ • τ)
  have hcomp := houter.comp (↑τ : ℂ) (hasDerivAt_smul_ofComplex γ τ)
  rwa [← hfun] at hcomp

private theorem hasDerivAt_coeff_binaryFormRepSL {n : ℕ} {H : ℂ → ↥(BinaryForm ℂ n)}
    {w : ↥(BinaryForm ℂ n)} {z₀ : ℂ}
    (hH : ∀ e : Fin 2 →₀ ℕ, HasDerivAt (fun z : ℂ => (H z : MvPolynomial (Fin 2) ℂ).coeff e)
      ((w : MvPolynomial (Fin 2) ℂ).coeff e) z₀)
    (g : SL(2, ℤ)) (d : Fin 2 →₀ ℕ) :
    HasDerivAt
      (fun z : ℂ => ((binaryFormRepSL ℂ n g (H z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d)
      (((binaryFormRepSL ℂ n g w : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d) z₀ := by
  have hfun : (fun z : ℂ => ((binaryFormRepSL ℂ n g (H z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d)
      = fun z : ℂ => ∑ e ∈ degExps n,
          (H z : MvPolynomial (Fin 2) ℂ).coeff e
            * (binarySubst ℂ (g : Matrix (Fin 2) (Fin 2) ℤ) (monomial e 1)).coeff d :=
    funext fun z => coeff_binaryFormRepSL_eq_sum g (H z) d
  rw [hfun, coeff_binaryFormRepSL_eq_sum g w d]
  exact HasDerivAt.fun_sum fun e _ =>
    (hH e).mul_const ((binarySubst ℂ (g : Matrix (Fin 2) (Fin 2) ℤ) (monomial e 1)).coeff d)

end Tier2Aux

theorem IsEichlerIntegral.add {n : ℕ} {f g : UpperHalfPlane → ℂ}
    {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n g G) :
    HeckeEis.IsEichlerIntegral n (f + g) (F + G) := by
  intro d τ
  have h := (hF d τ).add (hG d τ)
  simp only [← add_mul] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem IsEichlerIntegral.smul {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (c : ℂ) :
    HeckeEis.IsEichlerIntegral n (c • f) (c • F) := by
  intro d τ
  have h := (hF d τ).const_mul c
  rw [← mul_assoc] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.smul_apply, Submodule.coe_smul, coeff_smul, smul_eq_mul]

theorem IsEichlerIntegral.slash {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (δ : SL(2, ℤ)) :
    HeckeEis.IsEichlerIntegral n (f ∣[((n : ℤ) + 2)] δ) (fun τ => HeckeEis.binaryFormRepSL ℂ n δ⁻¹ (F (δ • τ))) := by
  intro d τ

  set c : ℂ := f (δ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ δ) ↑τ ^ (-2 : ℤ) with hc
  have hH : ∀ e : Fin 2 →₀ ℕ, HasDerivAt
      (fun z : ℂ => (F (δ • ofComplex z) : MvPolynomial (Fin 2) ℂ).coeff e)
      ((((c • linePow n ((δ • τ : ℍ) : ℂ)) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff e) ↑τ := by
    intro e
    have h1 := hasDerivAt_comp_smul
      (G := fun w : ℍ => (F w : MvPolynomial (Fin 2) ℂ).coeff e)
      (g := fun w : ℍ => f w * (linePow n (w : ℂ) : MvPolynomial (Fin 2) ℂ).coeff e)
      (fun w => hF e w) δ τ
    refine h1.congr_deriv ?_
    rw [Submodule.coe_smul, coeff_smul, smul_eq_mul, hc]
    ring
  have h2 := hasDerivAt_coeff_binaryFormRepSL hH δ⁻¹ d
  refine h2.congr_deriv ?_

  have hJ : denom (Matrix.SpecialLinearGroup.mapGL ℝ δ) (τ : ℂ) ≠ 0 := denom_ne_zero _ _
  have hinv : binaryFormRepSL ℂ n δ⁻¹ (linePow n ((δ • τ : ℍ) : ℂ))
      = (jFactor δ τ ^ n)⁻¹ • linePow n (τ : ℂ) := by
    have h := congrArg (binaryFormRepSL ℂ n δ⁻¹) (binaryFormRepSL_linePow n δ τ)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_smul] at h
    rw [h, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (jFactor_ne_zero δ τ)), one_smul]
  have hslash : (f ∣[((n : ℤ) + 2)] δ) τ
      = f (δ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ δ) (τ : ℂ) ^ (-((n : ℤ) + 2)) :=
    ModularForm.SL_slash_apply _ _ _
  rw [map_smul, hinv, smul_smul, Submodule.coe_smul, coeff_smul, smul_eq_mul, hslash, jFactor_eq_denom, hc]
  congr 1
  rw [← zpow_natCast, ← zpow_neg, mul_assoc, ← zpow_add₀ hJ]
  congr 2
  ring

theorem IsEichlerIntegral.exists_sub_eq_const {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n f G) :
    ∃ v : ↥(HeckeEis.BinaryForm ℂ n), ∀ τ : UpperHalfPlane, F τ - G τ = v := by
  refine ⟨F I - G I, fun τ => ?_⟩
  apply Subtype.ext
  rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub]
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_sub, coeff_sub]
  have key : ∀ σ : ℍ, HasDerivAt
      (fun z : ℂ => (F (ofComplex z) : MvPolynomial (Fin 2) ℂ).coeff d
        - (G (ofComplex z) : MvPolynomial (Fin 2) ℂ).coeff d) 0 ↑σ :=
    fun σ => ((hF d σ).sub (hG d σ)).congr_deriv (sub_self _)
  have hc := UpperHalfPlane.apply_eq_apply_of_hasDerivAt_zero key τ I
  simpa only [ofComplex_apply] using hc

/-- Substitution commutes with evaluation: the row `v` is pushed into the matrix. -/
private theorem eval_binarySubst {K : Type*} [CommRing K] (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → K)
    (Q : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval v (binarySubst K M Q)
      = MvPolynomial.eval (fun j => ∑ i : Fin 2, ((M i j : ℤ) : K) * v i) Q := by
  have key : (MvPolynomial.eval v).comp
        (binarySubst K M : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K).toRingHom
      = MvPolynomial.eval (fun j => ∑ i : Fin 2, ((M i j : ℤ) : K) * v i) :=
    MvPolynomial.ringHom_ext (fun a => by simp) (fun j => by simp [binarySubst_X])
  exact RingHom.congr_fun key Q

/-- The determinant identity `ad - bc = 1` for `g ∈ SL(2, ℤ)` over `ℂ`. -/
private theorem det_entries_GL (g : SL(2, ℤ)) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ)
      - ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

theorem jFactor_pow_mul_eval_binaryFormRepSL (n : ℕ) (g : SL(2, ℤ)) (τ : UpperHalfPlane)
    (P : ↥(HeckeEis.BinaryForm ℂ n)) :
    HeckeEis.jFactor g τ ^ n * MvPolynomial.eval ![(1 : ℂ), -(((g • τ : UpperHalfPlane)) : ℂ)]
        ((HeckeEis.binaryFormRepSL ℂ n g P : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
      = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] (P : MvPolynomial (Fin 2) ℂ) := by
  rw [binaryFormRepSL_apply_coe, eval_binarySubst]
  have hj : jFactor g τ ≠ 0 := jFactor_ne_zero g τ
  have hJ : jFactor g τ = ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (τ : ℂ) + ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) := rfl
  have hmul := coe_smul_mul_jFactor g τ
  have hdet_entries := det_entries_GL g
  have hrow : ∀ j : Fin 2, jFactor g τ * (∑ i : Fin 2, (((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ)
        * (![(1 : ℂ), -(((g • τ : ℍ)) : ℂ)]) i) = (![(1 : ℂ), -(τ : ℂ)]) j := by
    intro j
    fin_cases j
    · simp only [Fin.sum_univ_two, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_one]
      linear_combination (-(((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℂ)) * hmul
        + (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℂ) * hJ + hdet_entries
    · simp only [Fin.sum_univ_two, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_one]
      linear_combination (-(((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℂ)) * hmul
        + (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℂ) * hJ - (τ : ℂ) * hdet_entries
  have hpt : (fun j : Fin 2 => ∑ i : Fin 2, (((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ)
        * (![(1 : ℂ), -(((g • τ : ℍ)) : ℂ)]) i)
      = (jFactor g τ)⁻¹ • ![(1 : ℂ), -(τ : ℂ)] := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, ← hrow j, ← mul_assoc, inv_mul_cancel₀ hj, one_mul]
  rw [hpt, eval_smul_of_isHomogeneous ((mem_homogeneousSubmodule n _).mp P.2), ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hj, one_pow, one_mul]

theorem IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries
    {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K Γ V} {F G : UpperHalfPlane → V}
    (hF : HeckeEis.IsEquivariantPrimitiveWith ρ F) (hG : HeckeEis.IsEquivariantPrimitiveWith ρ G)
    {v : V} (h : ∀ τ : UpperHalfPlane, F τ - G τ = v) :
    hF.cocycle - hG.cocycle ∈ HeckeEis.coeffCoboundaries ρ := by
  rw [mem_coeffCoboundaries_iff]
  refine ⟨-v, funext fun γ => ?_⟩
  change ρ γ (-v) - -v = (F ((γ : SL(2, ℤ)) • I) - ρ γ (F I)) - (G ((γ : SL(2, ℤ)) • I) - ρ γ (G I))
  rw [map_neg, sub_eq_iff_eq_add.mp (h ((γ : SL(2, ℤ)) • I)), sub_eq_iff_eq_add.mp (h I), map_add]
  abel

end HeckeEis
