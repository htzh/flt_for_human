/-
  T12 — the properties, concluded: the irreducible symmetric datum.

  The module owns the **symmetry** argument: the transpose engine (`swapBivar` is
  mathlib's `Bivariate.swap`; a coefficient-bounded polynomial has a monic
  transpose of a computable degree), the q-expansion dictionary that reads pole
  bounds as those coefficient bounds, `EvalSymm` and its two conversions to the
  transpose identity, the transposed evaluation `Φ(j(q ^ ℓ), j(q)) = 0` read off the
  splitting, the descent dictionary that turns a descended family into that
  splitting and into the pole bounds, and the minimal polynomial of the transposed
  evaluation. On top of it sits `exists_phiIrreducible_evalSymm`, the cone's own
  construction: it chooses a primitive `ℓ`-th root in `CyclotomicField ℓ ℚ` (mathlib
  supplies one) and runs (a) descent (T11) → (b) integrality (T9) → (c) membership
  (T8) → T11's assembly → the splitting, which gives irreducibility, the transposed
  evaluation and — through T10's pole-bound exports
  (`phiProd_conj_coeff_zero_lead`, `phiProd_conj_coeff_eq_zero_of_le`) — the
  coefficient bounds. The dictionary turns those into
  `(swapBivar Φ).map evalAtJGen` being monic of degree `ψ(ℓ)`, and the datum
  annihilates `j(q ^ ℓ)`, so the transpose is `Φ` itself by uniqueness of the
  minimal polynomial. It is a join, not new mathematics, and it is T13's entry
  point.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean` (895 lines) for the
  transpose half, `P2M/Sol/S_ModularCurve_swapBivar_eq_of_evalSymm.lean` (95 lines)
  for the converse, `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean`
  (124 lines) and `P2M/Sol/S_ModularCurve_exists_phiIrreducible_evalSymm.lean` (62
  lines). The capstone's statement is the `Theorems/` wrapper of the last verbatim;
  the others contribute the engine and the symmetry argument, which the capstone
  proves.

  ## Assumptions

  `Defs/PhiGen`, `Defs/Polynomial`, `Defs/Fields`, `Defs/Jq`,
  `Defs/BivariateEval` (`ev`, `swap_eq_of_evalSymm`); T10's `PhiGenPoleBounds`;
  T11's `ModularPolynomialAssembly` (the assembly) and `PhiGenDescent`
  (`exists_phiGenDescends`); T9's `PhiGenIntegrality`; T8's
  `ModularForms/PhiGenDescends`; `ModularPolynomialIrreducible` (`phiIrreducible_of_splits`,
  `minpoly_jqN_eq`, `evalAtJGen_injective`, and the level embedding `qEmbedT` with
  `qEmbedT_injective`/`qEmbedT_jq`/`qEmbedT_jqN`, `qEmbedT_eq_coeffEmb_qExpand`, and the evaluation
  `evalAtJK` the splitting is stated with, `conj_succ_zero`).
  Checked by `spec/check_port.py` through the `spec-pin:` lines below; the module is
  not listed in `spec/old_check_stmts.py`.

  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean
  spec-pin: Theorems/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean
  spec-pin: Theorems/Thm_ModularCurve_swapBivar_eq_of_evalSymm.lean
  spec-pin: Theorems/Thm_ModularCurve_swapBivar_monic_of_coeff_bounds.lean
-/
import FLTForHuman.ModularCurve.ModularPolynomialIrreducible
import FLTForHuman.ModularCurve.ModularPolynomialAssembly
import FLTForHuman.ModularCurve.PhiGenDescent
import FLTForHuman.ModularCurve.PhiGenPoleBounds
import FLTForHuman.ModularForms.PhiGenDescends

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
under the swapped evaluation. -/
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
whose higher coefficients have degree `< d` has a monic transpose of degree `d`.
Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_swapBivar_monic_of_coeff_bounds.lean`. -/
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

/-- Evaluated symmetry forces the transpose to be `Φ` itself. Verbatim from the
pin wrapper `Theorems/Thm_ModularCurve_swapBivar_eq_of_evalSymm.lean`. -/
theorem swapBivar_eq_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) :
    swapBivar Φ = Φ := by
  rw [swapBivar_eq_swap, swap_eq_of_evalSymm h]

/-! ## The transposed evaluation, read off the splitting

The datum's own relation `eval_eq_zero` is the unswapped pair `Φ(j(q), j(q ^ ℓ)) = 0`; the
symmetry argument needs the swapped one, `Φ(j(q ^ ℓ), j(q)) = 0`, because the transpose is a
polynomial in `Y` over `ℚ(j(q))` and must vanish at `Y = j(q ^ ℓ)`. The product supplies it: the
level substitution turns `Φ` into `∏ᵢ (Y - conj i)`, and `j(q)` is one of its roots
(`conj_succ_zero`). The vanishing is read in `K((q))`, whence the injective level embedding
`qEmbedT` (`j(q) ↦ j(q ^ ℓ)`, `j(q ^ ℓ) ↦ j(q ^ (ℓ * ℓ))`) brings it back to `ℚ((q))`. -/

namespace PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

/-- The datum annihilates `j(q ^ ℓ)` under the swapped evaluation, read off the
splitting: the product has the root `j(q)` with multiplicity one. -/
theorem eval_swap_eq_zero_of_splits (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ)) :
    data.Φ.eval₂ (evalAtJqN ℓ) jq = 0 := by
  have h1 : data.Φ.eval₂ (evalAtJK K ℓ) (coeffEmb K jq) = 0 := by
    rw [← Polynomial.eval_map, hsplit, ← conj_succ_zero K ℓ ζ, phiProd, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin ℓ).succ)) (by simp)
  have h2 : data.Φ.eval₂ ((qExpand K ℓ).comp (evalAtJK K ℓ))
      (qExpand K ℓ (coeffEmb K jq)) = 0 := by
    have h := congrArg (qExpand K ℓ) h1
    rwa [Polynomial.hom_eval₂, map_zero] at h
  apply qEmbedT_injective K ℓ
  rw [map_zero, Polynomial.hom_eval₂, qEmbedT_jq]
  have hhom : (qEmbedT K ℓ).comp (evalAtJqN ℓ) = (qExpand K ℓ).comp (evalAtJK K ℓ) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    show qEmbedT K ℓ (evalAtJqN ℓ Polynomial.X) = qExpand K ℓ (evalAtJK K ℓ Polynomial.X)
    rw [evalAtJqN_X, evalAtJK_X, qEmbedT_jqN K ℓ ζ, conj_zero, qExpand_qExpand]
  rw [hhom]
  exact h2

end PhiGen

/-! ## The q-expansion dictionary of a descent -/

namespace PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}
  {c : ℕ → LaurentSeries ℚ}

/-- The level embedding creates and loses no coefficients: the coefficient of `q ^ (ℓ * m)` in
`qEmbedT`'s image is the embedding of the `q ^ m` coefficient. -/
private theorem coeff_qEmbedT (f : LaurentSeries ℚ) (m : ℤ) :
    (qEmbedT K ℓ f).coeff ((ℓ : ℤ) * m) = algebraMap ℚ K (f.coeff m) := by
  rw [qEmbedT_eq_coeffEmb_qExpand, coeffEmb_coeff, qExpand_coeff_mul]

/-- **A descent is a splitting**: a polynomial whose `X`-coefficients are the descended family's
is annihilated by the conjugates of `j(q)`. -/
theorem splits_of_descends (hc : PhiGenDescends ℓ ζ c) {Φ : Polynomial (Polynomial ℤ)}
    (hΦ : ∀ k, evalAtJ (Φ.coeff k) = c k) :
    Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ) := by
  refine Polynomial.ext fun k => ?_
  rw [Polynomial.coeff_map, evalAtJK_def, RingHom.comp_apply, hΦ k,
    qEmbedT_eq_coeffEmb_qExpand, ← hc k]

/-- The coefficient dictionary of a level substitution: a `q ↦ q ^ ℓ` substitution moves the
index by `ℓ` and nothing else, so the `m`-th coefficient of `Φ`'s `k`-th coefficient is the
`ℓ * m`-th coefficient of the conjugate product's. -/
private theorem coeff_eq_coeff_phiProd_of_splits {Φ : Polynomial (Polynomial ℤ)}
    (hsplit : Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ)) (k : ℕ) (m : ℤ) :
    algebraMap ℚ K ((evalAtJ (Φ.coeff k)).coeff m)
      = ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff ((ℓ : ℤ) * m) := by
  have hk : evalAtJK K ℓ (Φ.coeff k) = (phiProd ℓ (conj ℓ ζ)).coeff k := by
    rw [← Polynomial.coeff_map, ← hsplit]
  rw [← hk, evalAtJK_def, RingHom.comp_apply, coeff_qEmbedT]

/-- **The pole bounds of a splitting**: `Φ`'s coefficients have, coefficient by coefficient, the
`q`-expansion of a monic degree-`ψ(ℓ)` polynomial read through the transpose — `q ^ (-ψ(ℓ))`
carries a `1`, nothing sits below it, and every other coefficient vanishes at and below it.
T10's leading term `phiProd_conj_coeff_zero_lead` and vanishing bound
`phiProd_conj_coeff_eq_zero_of_le` are read at their `ℓ`-scaled index, and the constant
coefficient's tail from T10's uniform bound `ℓ * ℓ + ℓ`. -/
theorem coeff_poleBounds_of_splits (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {Φ : Polynomial (Polynomial ℤ)} (hsplit : Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ)) :
    (evalAtJ (Φ.coeff 0)).coeff (-(dedekindPsi ℓ : ℤ)) = 1 ∧
      (∀ m : ℕ, dedekindPsi ℓ < m → (evalAtJ (Φ.coeff 0)).coeff (-(m : ℤ)) = 0) ∧
      (∀ k, k ≠ 0 → ∀ m : ℕ, dedekindPsi ℓ ≤ m →
        (evalAtJ (Φ.coeff k)).coeff (-(m : ℤ)) = 0) := by
  have hψ := dedekindPsi_prime hℓ.out
  have hW : ∀ k, TPoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ) := fun k =>
    tPoleOrderLE_phiProd_coeff ℓ ζ (coeffEmb K jq) (conj ℓ ζ) (conj_zero ℓ ζ)
      (conj_succ ℓ ζ) jSimplePole_jqK k
  have hidx : ∀ m : ℕ, (ℓ : ℤ) * (-(m : ℤ)) = -((ℓ * m : ℕ) : ℤ) := by
    intro m; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · have h1 : algebraMap ℚ K (1 : ℚ) = 1 := map_one _
    refine (algebraMap ℚ K).injective ?_
    rw [h1, coeff_eq_coeff_phiProd_of_splits hsplit 0, hψ]
    have hidx' : (ℓ : ℤ) * (-((ℓ + 1 : ℕ) : ℤ)) = -((ℓ * ℓ + ℓ : ℕ) : ℤ) := by push_cast; ring
    rw [hidx']
    exact phiProd_conj_coeff_zero_lead ℓ ζ hζ
  · intro m hm
    have h0 : algebraMap ℚ K (0 : ℚ) = 0 := map_zero _
    refine (algebraMap ℚ K).injective ?_
    rw [h0, coeff_eq_coeff_phiProd_of_splits hsplit 0, hidx]
    exact hW 0 _ (by
      rw [hψ] at hm
      have hm' : (ℓ : ℤ) + 1 < (m : ℤ) := by exact_mod_cast hm
      have h2 : (2 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ.out.two_le
      push_cast
      nlinarith)
  · intro k hk0 m hm
    have h0 : algebraMap ℚ K (0 : ℚ) = 0 := map_zero _
    refine (algebraMap ℚ K).injective ?_
    rw [h0, coeff_eq_coeff_phiProd_of_splits hsplit k, hidx]
    exact phiProd_conj_coeff_eq_zero_of_le ℓ ζ k hk0 (ℓ * m)
      (by rw [hψ] at hm; nlinarith [hℓ.out.two_le])

end PhiGen

/-! ## Existence of an irreducible symmetric datum -/

/-- **The root the descent is run at**: `ℚ(ζ_ℓ)`'s primitive `ℓ`-th root (mathlib's), as a unit.
Naming it keeps the choice of where the descent happens — which is all the cyclotomic setup
amounts to — out of the existence proof, which then reads as the chain it is. -/
private theorem exists_primitiveRoot_cyclotomic (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    [hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ)] :
    ∃ ζ : (CyclotomicField ℓ ℚ)ˣ, IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ := by
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu := hz.isUnit hℓ.out.ne_zero
  exact ⟨hzu.unit, by rw [hzu.unit_spec]; exact hz⟩

/-- **There is an irreducible symmetric modular polynomial datum at every prime `ℓ`**: run the
descent at the cyclotomic field's primitive root, read off the coefficients' integrality (T9) and
their membership in the `j`-line (T8), assemble the datum (T11), conclude irreducibility, the
transposed evaluation and the pole bounds from the splitting, read the bounds through the
dictionary as the transpose's monic degree `ψ(ℓ)`, and identify the transpose with the datum by
uniqueness of the minimal polynomial of `j(q ^ ℓ)`. The statement is the pin wrapper's
`Theorems/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean`.

Two roles of `ℓ` meet in the statement, and only the first is about isogenies: `ℓ` is the order of
the modular polynomial (`Φ_ℓ`, `ψ(ℓ) = ℓ + 1` conjugates, the nome change `q ↦ q ^ ℓ`), and it is
also the level of the cyclotomic field the descent is run at, which is all the field setup below
amounts to — cyclotomic, hence finite and Galois, with a primitive `ℓ`-th root from
`exists_primitiveRoot_cyclotomic`. -/
theorem exists_phiIrreducible_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ := by
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  have : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_cyclotomic ℓ
  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends ℓ ζ hζ
  have hζ1 : ζ ^ ℓ = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  obtain ⟨data, hcoeff⟩ := PhiGen.exists_modularPolynomialData_coeff_eq hc
    (fun k => hc.intCoeffs hζ1 k)
    (fun k => PhiGen.mem_adjoin_jq_of_phiGenDescends ℓ ζ hζ c hc k)
  have hsplit := PhiGen.splits_of_descends hc hcoeff
  have hirr : PhiIrreducible data := PhiGen.phiIrreducible_of_splits ℓ ζ hζ data hsplit
  have hswap : data.Φ.eval₂ (evalAtJqN ℓ) jq = 0 :=
    PhiGen.eval_swap_eq_zero_of_splits ℓ ζ data hsplit
  obtain ⟨h0top, h0le, hk⟩ := PhiGen.coeff_poleBounds_of_splits hζ hsplit
  obtain ⟨h0monic, h0deg⟩ := monic_of_evalAtJ_coeff_eq_one
    (natDegree_le_of_evalAtJ_coeff_eq_zero h0le) h0top
  set ΦT := swapBivar data.Φ with hΦT
  obtain ⟨hTmonic, hTdeg⟩ := swapBivar_monic_of_coeff_bounds h0monic h0deg
    fun k hk0 => degree_lt_of_evalAtJ_coeff_eq_zero (hk k hk0)
  rw [← hΦT] at hTmonic hTdeg
  set T := ΦT.map evalAtJGen with hT
  have hTgen : T.Monic := hTmonic.map evalAtJGen
  have hann : Polynomial.aeval (jqN ℓ) T = 0 := data.aeval_jqN_transposeToAdjoin hswap
  have hdvd : data.toAdjoin ∣ T := by
    rw [← data.minpoly_jqN_eq hirr]
    exact minpoly.dvd _ _ hann
  have hTeq : T = data.toAdjoin :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le data.toAdjoin_monic hTgen hdvd (by
      rw [hT, hTmonic.natDegree_map, hTdeg,
        show data.toAdjoin = data.Φ.map evalAtJGen from rfl, data.monic.natDegree_map,
        data.natDegree_eq])
  have hsymm : ΦT = data.Φ :=
    Polynomial.map_injective evalAtJGen evalAtJGen_injective (by rw [← hT, hTeq]; rfl)
  exact ⟨data, hirr, evalSymm_of_swapBivar_eq (hΦT.symm.trans hsymm)⟩

end ModularCurve

end

