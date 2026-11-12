/-
  The transpose of a bivariate polynomial over `ℤ`, and the transposed evaluation.

  `swapBivar Φ` trades the two slots of `Φ ∈ ℤ[X][Y]`. The module reads the transpose three ways:

  * the evaluation identity `(swapBivar Φ)(x, y) = Φ(y, x)`, hence the equivalence of `EvalSymm`
    with `swapBivar Φ = Φ`;
  * the coefficient bookkeeping: a `Y ^ 0` coefficient that is monic of degree `d`, with every
    higher coefficient of degree `< d`, makes the transpose monic of degree `d` — the shape the
    minimal-polynomial step compares;
  * the q-expansion dictionary: a pole bound on a coefficient's `q`-expansion is a degree bound on
    the coefficient, in the three forms monicity, `degree ≤ D` and `degree < D`.

  The transposed evaluation sits at the end: the conjugate product has `j(q)` as a root, so
  `Φ(j(q ^ ℓ), j(q)) = 0` — the swapped relation the symmetry argument consumes, read in `K((q))`
  and brought back by the index-preserving coefficient embedding.
-/

import Mathlib.Algebra.Polynomial.Bivariate

import FLTForHuman.ModularCurve.Defs.BivariateEval
import FLTForHuman.ModularCurve.Defs.Fields
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.Defs.Polynomial
import FLTForHuman.ModularCurve.ModularEquation.Support.LevelEmbedding

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve

/-! ## The transpose as mathlib's `Bivariate.swap`

`swapBivar` is mathlib's `Bivariate.swap` as a ring hom on `ℤ[X][Y]`
(`swapBivar_eq_swap`). Keeping that single bridge lets the transpose and symmetry
proofs below cite mathlib's bivariate lemmas instead of re-deriving them, without
touching the `Defs` API. The coefficient-cast evaluation `ev` that mediates between
them, and the converse direction `swap_eq_of_evalSymm`, are in
`Defs/BivariateEval.lean`. -/

section SwapBivarGlue

/-- `swapBivar` is mathlib's `Bivariate.swap`, as ring homs. -/
private theorem swapBivar_eq_swap (Φ : Polynomial (Polynomial ℤ)) :
    swapBivar Φ = Bivariate.swap Φ := by
  have h : swapBivar = (Bivariate.swap (R := ℤ)).toAlgHom.toRingHom :=
    Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _)
      (by simp [Bivariate.swap_X])) (by simp [Bivariate.swap_Y])
  exact RingHom.congr_fun h Φ

end SwapBivarGlue

/-! ## The transpose engine: `swapBivar` of a coefficient-bounded polynomial -/

section SwapBivarEval

/-- The transpose commutes with evaluation: `(swapBivar Φ)(x, y) = Φ(y, x)`.
Mathlib's `Bivariate.aevalAeval_swap`, read through `swapBivar_eq_swap` and the
`ev = aevalAeval` bridge. -/
private theorem swapBivar_eval₂ (Φ : Polynomial (Polynomial ℤ)) (x y : LaurentSeries ℚ) :
    (swapBivar Φ).eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x := by
  rw [swapBivar_eq_swap, aeval_toRingHom_eq, aeval_toRingHom_eq]
  change ev (Bivariate.swap Φ) x y = ev Φ y x
  exact ev_swap Φ x y

/-- `swapBivar Φ = Φ` implies `EvalSymm Φ`. -/
theorem evalSymm_of_swapBivar_eq {Φ : Polynomial (Polynomial ℤ)} (h : swapBivar Φ = Φ) :
    EvalSymm Φ := fun x y => by
  conv_lhs => rw [← h]
  exact swapBivar_eval₂ Φ x y

end SwapBivarEval

namespace ModularPolynomialData

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

/-- The transposed `Φ` annihilates `j(q ^ N)` in `ℚ(j(q))[Y]` as soon as `Φ` does
under the swapped evaluation: `aeval (jqN N)` evaluates the transposed polynomial's `Y`-slot at
`j(q ^ N)`, and `swapBivar_eval₂` moves that vanishing back to the datum. -/
theorem aeval_jqN_transposeToAdjoin (hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0) :
    Polynomial.aeval (jqN N) ((swapBivar data.Φ).map evalAtJGen) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen,
    evalAtJ_def, swapBivar_eval₂, ← evalAtJqN_def]
  exact hswap

end ModularPolynomialData

/-! ## Degree bookkeeping for the transpose -/

section Engine

private theorem swapBivar_C (c : Polynomial ℤ) :
    swapBivar (Polynomial.C c) = c.map Polynomial.C := by
  rw [swapBivar_eq_swap]
  exact Bivariate.swap_C c

private theorem degree_swapBivar_lt {Ψ : Polynomial (Polynomial ℤ)} {D : ℕ}
    (h : ∀ k, (Ψ.coeff k).degree < (D : WithBot ℕ)) :
    (swapBivar Ψ).degree < (D : WithBot ℕ) := by
  conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow Ψ, map_sum]
  refine (Polynomial.degree_sum_le _ _).trans_lt
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe D)).2 fun k _ => ?_)
  rw [map_mul, map_pow, swapBivar_C, swapBivar_X, ← map_pow]
  refine lt_of_le_of_lt (le_trans (Polynomial.degree_mul_le _ _) ?_) (h k)
  calc ((Ψ.coeff k).map Polynomial.C).degree + (Polynomial.C (Polynomial.X ^ k)).degree
      ≤ (Ψ.coeff k).degree + 0 := by
        gcongr
        · exact le_of_eq (Polynomial.degree_map_eq_of_injective Polynomial.C_injective _)
        · exact Polynomial.degree_C_le
    _ = (Ψ.coeff k).degree := add_zero _

/-- A bivariate polynomial whose `Y ^ 0` coefficient is monic of degree `d` and
whose higher coefficients have degree `< d` has a monic transpose of degree `d`. -/
theorem swapBivar_monic_of_coeff_bounds {Φ : Polynomial (Polynomial ℤ)} {d : ℕ}
    (h0 : (Φ.coeff 0).Monic) (h0deg : (Φ.coeff 0).natDegree = d)
    (hk : ∀ k, k ≠ 0 → (Φ.coeff k).degree < (d : WithBot ℕ)) :
    (swapBivar Φ).Monic ∧ (swapBivar Φ).natDegree = d := by
  have hsplit : swapBivar Φ = Polynomial.C Polynomial.X * swapBivar Φ.divX
      + (Φ.coeff 0).map Polynomial.C := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add Φ]
    rw [map_add, map_mul, swapBivar_X, swapBivar_C]
  have hmap : ((Φ.coeff 0).map Polynomial.C).Monic := h0.map _
  have hmapdeg : ((Φ.coeff 0).map Polynomial.C).degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hmap.ne_zero, h0.natDegree_map, h0deg]
  have hsmall : (Polynomial.C Polynomial.X * swapBivar Φ.divX).degree
      < (d : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
    have hX : (Polynomial.C (Polynomial.X : Polynomial ℤ)).degree = 0 :=
      Polynomial.degree_C Polynomial.X_ne_zero
    rw [hX, zero_add]
    exact degree_swapBivar_lt fun k => by
      rw [Polynomial.coeff_divX]; exact hk (k + 1) (Nat.succ_ne_zero k)
  have hlt : (Polynomial.C Polynomial.X * swapBivar Φ.divX).degree
      < ((Φ.coeff 0).map Polynomial.C).degree := by rw [hmapdeg]; exact hsmall
  refine ⟨?_, ?_⟩
  · rw [hsplit]; exact hmap.add_of_right hlt
  · rw [hsplit, Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_add_eq_right_of_degree_lt hlt), h0.natDegree_map, h0deg]

end Engine

/-! ## Reading the pole bounds as coefficient bounds -/

section Dictionary

/-- A polynomial whose `q`-expansion vanishes from `-D` down has degree `< D`. -/
theorem degree_lt_of_evalAtJ_coeff_eq_zero {P : Polynomial ℤ} {D : ℕ}
    (h : ∀ m : ℕ, D ≤ m → (evalAtJ P).coeff (-(m : ℤ)) = 0) :
    P.degree < (D : WithBot ℕ) := by
  rcases eq_or_ne P 0 with rfl | hP0
  · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe D
  rw [← Polynomial.natDegree_lt_iff_degree_lt hP0]
  by_contra hle
  rw [not_lt] at hle
  have hQdeg : (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
  have hcoeff := coeff_aeval_jq_neg (P.map (Int.castRingHom ℚ)) (m := P.natDegree) hQdeg.le
  rw [← evalAtJ_eq_aeval_map, h P.natDegree hle, Polynomial.coeff_map,
    eq_intCast] at hcoeff
  have hlead : P.coeff P.natDegree = 0 := by exact_mod_cast hcoeff.symm
  exact hP0 (Polynomial.leadingCoeff_eq_zero.mp hlead)

/-- A polynomial of degree `≤ D` whose `q`-expansion is `1` at `q ^ (-D)` is
monic of degree `D`. -/
theorem monic_of_evalAtJ_coeff_eq_one {P : Polynomial ℤ} {D : ℕ}
    (hle : P.natDegree ≤ D) (h1 : (evalAtJ P).coeff (-(D : ℤ)) = 1) :
    P.Monic ∧ P.natDegree = D := by
  have hQdeg : (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
  have hcoeff := coeff_aeval_jq_neg (P.map (Int.castRingHom ℚ)) (m := D) (hQdeg.le.trans hle)
  rw [← evalAtJ_eq_aeval_map, h1, Polynomial.coeff_map, eq_intCast] at hcoeff
  have hPD : P.coeff D = 1 := by exact_mod_cast hcoeff.symm
  have hge : D ≤ P.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hPD]; exact one_ne_zero)
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one D hle hPD, le_antisymm hle hge⟩

/-- A polynomial whose `q`-expansion vanishes strictly below `-D` has degree `≤ D`. -/
theorem natDegree_le_of_evalAtJ_coeff_eq_zero {P : Polynomial ℤ} {D : ℕ}
    (h : ∀ m : ℕ, D < m → (evalAtJ P).coeff (-(m : ℤ)) = 0) :
    P.natDegree ≤ D := by
  rcases eq_or_ne P 0 with rfl | hP0
  · simp
  by_contra hlt
  rw [not_le] at hlt
  have hdeg := degree_lt_of_evalAtJ_coeff_eq_zero (P := P) (D := D + 1)
    (fun m hm => h m (by omega))
  rw [← Polynomial.natDegree_lt_iff_degree_lt hP0] at hdeg
  omega

end Dictionary

/-! ## The converse: evaluated symmetry forces `swapBivar Φ = Φ` -/

/-- Evaluated symmetry forces the transpose to be `Φ` itself. -/
theorem swapBivar_eq_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) :
    swapBivar Φ = Φ := by
  rw [swapBivar_eq_swap, swap_eq_of_evalSymm h]

/-! ## The transposed evaluation, read off the splitting

The datum's own relation `eval_eq_zero` is the unswapped pair `Φ(j(q), j(q ^ ℓ)) = 0`; the
symmetry argument needs the swapped one, `Φ(j(q ^ ℓ), j(q)) = 0`, because the transpose is a
polynomial in `Y` over `ℚ(j(q))` and must vanish at `Y = j(q ^ ℓ)`. The product supplies it: the
level substitution turns `Φ` into `∏ᵢ (Y - conj i)`, and `j(q)` is one of its roots
(`conj_succ_zero`). The vanishing is read in `K((q))`, whence the index-preserving coefficient
embedding `coeffEmb K` brings it back to `ℚ((q))`. -/

namespace PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

/-- The datum annihilates `j(q ^ ℓ)` under the swapped evaluation, read off the
splitting: the product has the root `j(q)` at the coset index `1`. The vanishing is
`Φ.eval₂ (evalAtJqN ℓ) jq = 0`, i.e. `X = j(q ^ ℓ)` and `Y = j(q)`, the datum's own relation
being the same with the two slots exchanged. -/
theorem eval_swap_eq_zero_of_splits (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ)) :
    data.Φ.eval₂ (evalAtJqN ℓ) jq = 0 := by
  have hcomp : (coeffEmb K).comp (evalAtJqN ℓ) = evalAtJK K ℓ := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    show coeffEmb K (evalAtJqN ℓ Polynomial.X) = evalAtJK K ℓ Polynomial.X
    simp only [evalAtJqN_X, evalAtJK_X, jqN, coeffEmb_qExpand]
  have h1 : data.Φ.eval₂ (evalAtJK K ℓ) (coeffEmb K jq) = 0 := by
    rw [← Polynomial.eval_map, hsplit, ← conj_succ_zero K ℓ ζ]
    exact phiProd_eval_conj ℓ (conj ℓ ζ) (0 : Fin ℓ).succ
  refine coeffEmb_injective K ?_
  rw [map_zero, Polynomial.hom_eval₂, hcomp, h1]

end PhiGen

end ModularCurve

end
