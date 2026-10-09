/-
  B2 — the `N = 2` fibre: `fibrePoly phiTwo W.j` as a product over the Vélu quotients.

  For an elliptic Weierstrass curve `W` over a field of characteristic not `2`, with
  three points `P i` that are distinct, on `W`, of order two (`veluGy = 0`) and have
  elliptic order-two quotients, the fibre of the classical modular polynomial `Φ₂` at
  `j(W)` factors over those quotients:

    `fibrePoly phiTwo W.j = ∏ i, (X - C (j (W.veluQuotient2 (P i).1 (P i).2)))`.

  The proof is the pin's. Distinct points of order two have distinct `x`-coordinates, so
  those coordinates are the three roots of `Ψ₂Sq`; the small-degree root count then pins
  `b₂`, `b₄`, `b₆` (and `b₈`, through `b_relation`), whence `c₄` and `Δ` are the
  elementary-symmetric expressions in them. Comparing coefficients of the two cubics —
  `fibrePoly phiTwo` expanded and the three linear factors multiplied out — reduces the
  identity to three coefficient identities in `c₄/Δ` and the quotient data, each closed by
  `field_simp; ring`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean` (230 lines).
  The public statement is the `Theorems/` wrapper
  `Theorems/Thm_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean`, verbatim.

  ## Public / private

  Only `ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j` is public. The pin silo's
  six other declarations (`fibrePoly_phiTwo_eq`, `cubic_expand`, `coeff_two_identity`,
  `coeff_one_identity`, `coeff_zero_identity`, `main`) are `S_`-local — the pin suppresses
  them with `p2m_export` and no later pin file consumes them — so they are `private` here.
  The pin-private three-line `sixteen_ne_zero` is re-derived `private` locally.

  ## Assumptions

  `ModularCurve/Defs/ClassicalModularPolynomials.lean`'s `phiTwo`;
  `ModularCurve/Defs/FibrePoly.lean`'s `fibrePoly`;
  `WeierstrassCurve/Velu/Defs.lean`'s `veluGx`/`veluGy`/`veluT`/`veluU` with
  `veluT_eq`/`veluU_eq_Ψ₂Sq_eval`; `WeierstrassCurve/Velu/OrderTwo.lean`'s
  `veluQuotient2`/`velu2QuadDisc`/`veluQuotient2_j` and
  `isElliptic_veluQuotient2_of_isElliptic`; mathlib's `WeierstrassCurve.Ψ₂Sq`,
  `b_relation`, `c₄`, `Δ`, `j`, `natDegree_quadratic_le` and
  `eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`.

  Reference (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean>
-/
import FLTForHuman.ModularCurve.Defs.ClassicalModularPolynomials
import FLTForHuman.ModularCurve.Defs.FibrePoly
import FLTForHuman.WeierstrassCurve.Velu.Defs
import FLTForHuman.WeierstrassCurve.Velu.OrderTwo
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace ModularCurve

namespace VeluTwoSym

private theorem fibrePoly_phiTwo_eq {K : Type*} [Field K] (a : K) :
    fibrePoly phiTwo a
      = X ^ 3 + C (-a ^ 2 + 1488 * a - 162000) * X ^ 2
          + C (1488 * a ^ 2 + 40773375 * a + 8748000000) * X
          + C (a ^ 3 - 162000 * a ^ 2 + 8748000000 * a - 157464000000000) := by
  simp only [fibrePoly, phiTwo, phiTwoC2, phiTwoC1, phiTwoC0, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.coe_eval₂RingHom,
    eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_neg, eval₂_ofNat]

private theorem cubic_expand {K : Type*} [Field K] (u v w : K) :
    (X - C u) * (X - C v) * (X - C w)
      = X ^ 3 + C (-(u + v + w)) * X ^ 2 + C (u * v + u * w + v * w) * X + C (-(u * v * w)) := by
  simp only [map_neg, map_add, map_mul]
  ring

section identities

variable {K : Type*} [Field K] {x0 x1 x2 c4 Δ g0 g1 g2 d0 d1 d2 : K}

private theorem sixteen_ne_zero (h2 : (2 : K) ≠ 0) : (16 : K) ≠ 0 := by
  rw [show (16 : K) = 2 ^ 4 by norm_num]; exact pow_ne_zero _ h2

private theorem coeff_two_identity (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) (h2 : (2 : K) ≠ 0)
    (hc4 : c4 = 16 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 - x0 * x1 - x0 * x2 - x1 * x2))
    (hΔ : Δ = 16 * (x0 - x1) ^ 2 * (x0 - x2) ^ 2 * (x1 - x2) ^ 2)
    (hg0 : g0 = (x0 - x1) * (x0 - x2)) (hg1 : g1 = (x1 - x0) * (x1 - x2))
    (hg2 : g2 = (x2 - x0) * (x2 - x1))
    (hd0 : d0 = 16 * (x1 - x2) ^ 2) (hd1 : d1 = 16 * (x0 - x2) ^ 2) (hd2 : d2 = 16 * (x0 - x1) ^ 2) :
    -(c4 ^ 3 / Δ) ^ 2 + 1488 * (c4 ^ 3 / Δ) - 162000
      = -((c4 + 240 * g0) ^ 3 / (g0 * d0 ^ 2) + (c4 + 240 * g1) ^ 3 / (g1 * d1 ^ 2)
          + (c4 + 240 * g2) ^ 3 / (g2 * d2 ^ 2)) := by
  have h16 := sixteen_ne_zero h2
  have h01' := sub_ne_zero.mpr h01; have h02' := sub_ne_zero.mpr h02; have h12' := sub_ne_zero.mpr h12
  have h10' := sub_ne_zero.mpr h01.symm; have h20' := sub_ne_zero.mpr h02.symm
  have h21' := sub_ne_zero.mpr h12.symm
  subst hc4 hΔ hg0 hg1 hg2 hd0 hd1 hd2
  field_simp
  ring

private theorem coeff_one_identity (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) (h2 : (2 : K) ≠ 0)
    (hc4 : c4 = 16 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 - x0 * x1 - x0 * x2 - x1 * x2))
    (hΔ : Δ = 16 * (x0 - x1) ^ 2 * (x0 - x2) ^ 2 * (x1 - x2) ^ 2)
    (hg0 : g0 = (x0 - x1) * (x0 - x2)) (hg1 : g1 = (x1 - x0) * (x1 - x2))
    (hg2 : g2 = (x2 - x0) * (x2 - x1))
    (hd0 : d0 = 16 * (x1 - x2) ^ 2) (hd1 : d1 = 16 * (x0 - x2) ^ 2) (hd2 : d2 = 16 * (x0 - x1) ^ 2) :
    1488 * (c4 ^ 3 / Δ) ^ 2 + 40773375 * (c4 ^ 3 / Δ) + 8748000000
      = (c4 + 240 * g0) ^ 3 / (g0 * d0 ^ 2) * ((c4 + 240 * g1) ^ 3 / (g1 * d1 ^ 2))
        + (c4 + 240 * g0) ^ 3 / (g0 * d0 ^ 2) * ((c4 + 240 * g2) ^ 3 / (g2 * d2 ^ 2))
        + (c4 + 240 * g1) ^ 3 / (g1 * d1 ^ 2) * ((c4 + 240 * g2) ^ 3 / (g2 * d2 ^ 2)) := by
  have h16 := sixteen_ne_zero h2
  have h01' := sub_ne_zero.mpr h01; have h02' := sub_ne_zero.mpr h02; have h12' := sub_ne_zero.mpr h12
  have h10' := sub_ne_zero.mpr h01.symm; have h20' := sub_ne_zero.mpr h02.symm
  have h21' := sub_ne_zero.mpr h12.symm
  subst hc4 hΔ hg0 hg1 hg2 hd0 hd1 hd2
  field_simp
  ring

private theorem coeff_zero_identity (h01 : x0 ≠ x1) (h02 : x0 ≠ x2) (h12 : x1 ≠ x2) (h2 : (2 : K) ≠ 0)
    (hc4 : c4 = 16 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 - x0 * x1 - x0 * x2 - x1 * x2))
    (hΔ : Δ = 16 * (x0 - x1) ^ 2 * (x0 - x2) ^ 2 * (x1 - x2) ^ 2)
    (hg0 : g0 = (x0 - x1) * (x0 - x2)) (hg1 : g1 = (x1 - x0) * (x1 - x2))
    (hg2 : g2 = (x2 - x0) * (x2 - x1))
    (hd0 : d0 = 16 * (x1 - x2) ^ 2) (hd1 : d1 = 16 * (x0 - x2) ^ 2) (hd2 : d2 = 16 * (x0 - x1) ^ 2) :
    (c4 ^ 3 / Δ) ^ 3 - 162000 * (c4 ^ 3 / Δ) ^ 2 + 8748000000 * (c4 ^ 3 / Δ) - 157464000000000
      = -((c4 + 240 * g0) ^ 3 / (g0 * d0 ^ 2) * ((c4 + 240 * g1) ^ 3 / (g1 * d1 ^ 2))
          * ((c4 + 240 * g2) ^ 3 / (g2 * d2 ^ 2))) := by
  have h16 := sixteen_ne_zero h2
  have h01' := sub_ne_zero.mpr h01; have h02' := sub_ne_zero.mpr h02; have h12' := sub_ne_zero.mpr h12
  have h10' := sub_ne_zero.mpr h01.symm; have h20' := sub_ne_zero.mpr h02.symm
  have h21' := sub_ne_zero.mpr h12.symm
  subst hc4 hΔ hg0 hg1 hg2 hd0 hd1 hd2
  field_simp
  ring

end identities

private theorem main {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0) :
    fibrePoly phiTwo W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  classical

  have hy : ∀ i, (P i).2 = -(W.a₁ * (P i).1 + W.a₃) / 2 := by
    intro i
    have hg := hPgy i
    simp only [veluGy, neg_eq_zero] at hg
    rw [eq_div_iff h2]
    linear_combination hg
  have hroot : ∀ i, W.Ψ₂Sq.eval (P i).1 = 0 := by
    intro i
    rw [← veluU_eq_Ψ₂Sq_eval W (hPeq i)]
    simp [veluU, hPgy i]
  have hinjx : ∀ {i i' : ι}, (P i).1 = (P i').1 → i = i' := by
    intro i i' hx
    apply hP
    exact Prod.ext hx (by rw [hy i, hy i', hx])

  obtain ⟨e⟩ : Nonempty (ι ≃ Fin 3) := ⟨Fintype.equivFinOfCardEq hι⟩
  have hre : ∀ f : ι → K[X], ∏ i, f i = ∏ k : Fin 3, f (e.symm k) := fun f =>
    (Fintype.prod_equiv e.symm (fun k => f (e.symm k)) f (fun _ => rfl)).symm
  rw [hre, Fin.prod_univ_three]
  set x0 := (P (e.symm 0)).1 with hx0
  set y0 := (P (e.symm 0)).2 with hy0
  set x1 := (P (e.symm 1)).1 with hx1
  set y1 := (P (e.symm 1)).2 with hy1
  set x2 := (P (e.symm 2)).1 with hx2
  set y2 := (P (e.symm 2)).2 with hy2
  have h01 : x0 ≠ x1 := fun h => by have := e.symm.injective (hinjx h); exact absurd this (by decide)
  have h02 : x0 ≠ x2 := fun h => by have := e.symm.injective (hinjx h); exact absurd this (by decide)
  have h12 : x1 ≠ x2 := fun h => by have := e.symm.injective (hinjx h); exact absurd this (by decide)

  have hq : W.Ψ₂Sq - C 4 * ((X - C x0) * (X - C x1) * (X - C x2))
      = C (W.b₂ + 4 * (x0 + x1 + x2)) * X ^ 2 + C (2 * W.b₄ - 4 * (x0 * x1 + x0 * x2 + x1 * x2)) * X
        + C (W.b₆ + 4 * (x0 * x1 * x2)) := by
    rw [WeierstrassCurve.Ψ₂Sq]
    simp only [map_add, map_sub, map_mul, map_ofNat]
    ring
  have hq0 : C (W.b₂ + 4 * (x0 + x1 + x2)) * X ^ 2 + C (2 * W.b₄ - 4 * (x0 * x1 + x0 * x2 + x1 * x2)) * X
        + C (W.b₆ + 4 * (x0 * x1 * x2)) = 0 := by
    rw [← hq]
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ {x0, x1, x2}
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · rw [hx0]; simp [hroot (e.symm 0)]
      · rw [hx1]; simp [hroot (e.symm 1)]
      · rw [hx2]; simp [hroot (e.symm 2)]
    · rw [hq]
      refine lt_of_le_of_lt natDegree_quadratic_le ?_
      rw [Finset.card_insert_of_notMem (by simp [h01, h02]), Finset.card_insert_of_notMem (by simp [h12]),
        Finset.card_singleton]
      norm_num
  have hA : W.b₂ + 4 * (x0 + x1 + x2) = 0 := by
    have h := congrArg (fun q : K[X] => q.coeff 2) hq0
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at h
    simpa using h
  have hB : 2 * W.b₄ - 4 * (x0 * x1 + x0 * x2 + x1 * x2) = 0 := by
    have h := congrArg (fun q : K[X] => q.coeff 1) hq0
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at h
    simpa using h
  have hD : W.b₆ + 4 * (x0 * x1 * x2) = 0 := by
    have h := congrArg (fun q : K[X] => q.coeff 0) hq0
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at h
    simpa using h
  have hb2 : W.b₂ = -4 * (x0 + x1 + x2) := by linear_combination hA
  have hb4 : W.b₄ = 2 * (x0 * x1 + x0 * x2 + x1 * x2) := by
    apply mul_left_cancel₀ h2; linear_combination hB
  have hb6 : W.b₆ = -4 * (x0 * x1 * x2) := by linear_combination hD
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 ^ 2 by norm_num]; exact pow_ne_zero _ h2
  have hb8 : W.b₈ = 4 * (x0 + x1 + x2) * (x0 * x1 * x2) - (x0 * x1 + x0 * x2 + x1 * x2) ^ 2 := by
    apply mul_left_cancel₀ h4
    rw [b_relation, hb2, hb4, hb6]; ring

  have hc4 : W.c₄ = 16 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 - x0 * x1 - x0 * x2 - x1 * x2) := by
    rw [c₄, hb2, hb4]; ring
  have hΔ' : W.Δ = 16 * (x0 - x1) ^ 2 * (x0 - x2) ^ 2 * (x1 - x2) ^ 2 := by
    rw [WeierstrassCurve.Δ, hb2, hb4, hb6, hb8]; ring
  have hgx : ∀ i, W.veluGx (P i).1 (P i).2
      = (6 * (P i).1 ^ 2 + W.b₂ * (P i).1 + W.b₄) / 2 := by
    intro i
    have hT := veluT_eq W (P i).1 (P i).2
    rw [veluT, hPgy i, mul_zero, sub_zero] at hT
    rw [eq_div_iff h2, mul_comm, hT]
  have hg0 : W.veluGx x0 y0 = (x0 - x1) * (x0 - x2) := by
    rw [hx0, hy0, hgx, ← hx0, hb2, hb4, div_eq_iff h2]; ring
  have hg1 : W.veluGx x1 y1 = (x1 - x0) * (x1 - x2) := by
    rw [hx1, hy1, hgx, ← hx1, hb2, hb4, div_eq_iff h2]; ring
  have hg2 : W.veluGx x2 y2 = (x2 - x0) * (x2 - x1) := by
    rw [hx2, hy2, hgx, ← hx2, hb2, hb4, div_eq_iff h2]; ring
  have hd0 : W.velu2QuadDisc x0 = 16 * (x1 - x2) ^ 2 := by rw [velu2QuadDisc_def, hb2, hb4]; ring
  have hd1 : W.velu2QuadDisc x1 = 16 * (x0 - x2) ^ 2 := by rw [velu2QuadDisc_def, hb2, hb4]; ring
  have hd2 : W.velu2QuadDisc x2 = 16 * (x0 - x1) ^ 2 := by rw [velu2QuadDisc_def, hb2, hb4]; ring
  have hj : W.j = W.c₄ ^ 3 / W.Δ := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ', inv_mul_eq_div]

  have hJ0 : @WeierstrassCurve.j K _ (W.veluQuotient2 x0 y0) ⟨isUnit_iff_ne_zero.mpr (hΔ (e.symm 0))⟩
      = (W.c₄ + 240 * W.veluGx x0 y0) ^ 3 / (W.veluGx x0 y0 * W.velu2QuadDisc x0 ^ 2) :=
    veluQuotient2_j (hPeq (e.symm 0)) (hPgy (e.symm 0))
  have hJ1 : @WeierstrassCurve.j K _ (W.veluQuotient2 x1 y1) ⟨isUnit_iff_ne_zero.mpr (hΔ (e.symm 1))⟩
      = (W.c₄ + 240 * W.veluGx x1 y1) ^ 3 / (W.veluGx x1 y1 * W.velu2QuadDisc x1 ^ 2) :=
    veluQuotient2_j (hPeq (e.symm 1)) (hPgy (e.symm 1))
  have hJ2 : @WeierstrassCurve.j K _ (W.veluQuotient2 x2 y2) ⟨isUnit_iff_ne_zero.mpr (hΔ (e.symm 2))⟩
      = (W.c₄ + 240 * W.veluGx x2 y2) ^ 3 / (W.veluGx x2 y2 * W.velu2QuadDisc x2 ^ 2) :=
    veluQuotient2_j (hPeq (e.symm 2)) (hPgy (e.symm 2))
  rw [hJ0, hJ1, hJ2, fibrePoly_phiTwo_eq, hj, cubic_expand,
    coeff_two_identity h01 h02 h12 h2 hc4 hΔ' hg0 hg1 hg2 hd0 hd1 hd2,
    coeff_one_identity h01 h02 h12 h2 hc4 hΔ' hg0 hg1 hg2 hd0 hd1 hd2,
    coeff_zero_identity h01 h02 h12 h2 hc4 hΔ' hg0 hg1 hg2 hd0 hd1 hd2]

end VeluTwoSym

/-- The fibre of the level-two modular polynomial `Φ₂` at `j(W)` is the product of
`(X - C (j (W/⟨P i⟩)))` over three distinct order-two points `P i` with elliptic
quotients: `fibrePoly phiTwo W.j = ∏ i, (X - C (j (W.veluQuotient2 (P i).1 (P i).2)))`. -/
theorem fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j
    {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0) :
    fibrePoly phiTwo W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) :=
  VeluTwoSym.main h2 W hι P hP hPeq hPgy hΔ

end ModularCurve

end
