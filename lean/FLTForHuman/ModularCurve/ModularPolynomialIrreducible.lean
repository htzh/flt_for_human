/-
  T12 — the 895 block: irreducibility and symmetry of the datum.

  The block is FLT's single largest shared development: it ships in five pin files
  (the three graph nodes `phiIrreducible_of_splits`, `evalSymm_of_splits`,
  `transposeToAdjoin_monic_of_qExpansion`, plus the two hidden exports
  `swapBivar_monic_of_coeff_bounds` and `evalSymm_of_irreducible`), `5 × 895 ≈
  4,475` pin lines. This module is the block's irreducibility half, with the level
  embedding its proof shares: it exports the irreducibility headline, the prime
  non-membership, the datum's minimal-polynomial facts and the transposed
  evaluation. The block's transpose engine and q-expansion dictionary — everything
  the symmetry argument is built from — are in `ModularPolynomialProperties.lean`,
  beside the capstone that runs them.

  ## What it proves

  * `conj_injective` — the `ℓ + 1` conjugates are distinct (separated by their
    `q⁻¹` coefficients);
  * `jqN_not_mem_adjoin_jq` (private) — `j(q ^ ℓ)` is not a polynomial in `j(q)`, the
    prime non-membership: the twist-sum refutation, using `one_le_coeff_jq` at
    `n = ℓ`. The pin has it public (`aeval_jq_ne_jqN_of_isPrimitiveRoot`,
    `aeval_jq_ne_jqN`, `jqN_not_mem_adjoin_jq`) but no file outside the block's own
    copies cites any of the three, so the port keeps the statement and inlines the
    chain into one private fact (its only consumer is the irreducibility proof);
  * `phiIrreducible_of_splits` — the datum is irreducible over `ℚ(j)`, by the
    factor-counting argument: a nonzero `D ∈ ℚ[j(q)]` with `D(jq) = 0` has degree
    `≥ ℓ` (the conjugates are distinct), so one factor of any factorisation has
    degree `≤ 1`, and it is a unit because `j(q^ℓ) ∉ ℚ[j(q)]`;
  * `aeval_jqN_toAdjoin`, `minpoly_jqN_eq` — `data.toAdjoin` annihilates `j(q^ℓ)`,
    and is its minimal polynomial when the datum is irreducible;
  * `eval_swap_eq_zero_of_splits` — the transposed evaluation vanishes at
    `(j(q ^ ℓ), j(q))`, read off the splitting through the level embedding;
  * `evalAtJGen_injective` — the injectivity that lets the symmetry step be decided
    over `ℚ(j(q))`.

  ## Reuse (work order §3.1)

  The block's private `evalAtJ_injective` is T11's public one; its private
  `coeff_aeval_jq_neg` is T9's; its private `evalAtJ_eq_aeval_map_rat` is the
  `Defs/Jq.lean` promotion; its private `coeff_aeval_jq_of_lt` is
  `Defs/PhiGen.lean`'s `poleOrderLE_aeval_jq` and its private
  `coeff_aeval_jq_neg_natDegree` is `Defs/Jq.lean`'s `coeff_aeval_jq_neg` at
  `m = P.natDegree`; `evalAtJGen_injective` is derived from
  `evalAtJ_injective` through `algebraMap_comp_evalAtJGen` (the `eq_of_prime` file's
  two-line proof), and `conj_injective` is written once and exported.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean` (895 lines). The public
  statements are the `Theorems/` wrappers verbatim where a wrapper exists, and the
  `S_` file's own public declaration otherwise (`eval_swap_eq_zero_of_splits`).

  ## Assumptions

  `Defs/PhiGen`'s `conj`/`conj_zero`/`conj_succ`/`phiProd`/`phiProd_eval_conj`/
  `ModularPolynomialData`/`EvalSymm`/`PhiIrreducible`/`adjoinJq`/`jAdj`/
  `evalAtJAdj`/`swapBivar`; `Defs/Fields`'s `jGen`/`evalAtJGen`/
  `algebraMap_comp_evalAtJGen`/`toAdjoin`/`toAdjoin_monic`; `Defs/Jq`'s `jq`/
  `jqN`/`evalAtJ`/`evalAtJ_eq_aeval_map`/`coeff_aeval_jq_neg`/`transcendental_jq`/
  `dedekindPsi_prime`; `Defs/BivariateEval`'s `ev`/`ev_swap`/`ev_int`/`ev_sub`/
  `swap_eq_of_evalSymm`; T11's `PhiGen.evalAtJ_injective`; T12's `one_le_coeff_jq`.
  Checked by `spec/check_port.py` through the `spec-pin:` lines below; the module is
  not listed in `spec/old_check_stmts.py`.

  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq.lean
  spec-pin: Theorems/Thm_ModularCurve_PhiGen_conj_injective.lean
  spec-pin: Theorems/Thm_ModularCurve_PhiGen_phiIrreducible_of_splits.lean
  spec-pin: Theorems/Thm_ModularCurve_aeval_jqN_toAdjoin.lean
  spec-pin: Theorems/Thm_ModularCurve_evalAtJGen_injective.lean
-/
import FLTForHuman.ModularCurve.JqCoeffPositivity
import FLTForHuman.ModularCurve.PhiGenDescendsStructure
import FLTForHuman.ModularCurve.Defs.BivariateEval
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField

open scoped IntermediateField.algebraAdjoinAdjoin

namespace ModularCurve

/-! ## `j(q ^ N)`'s leading coefficients -/

section JqNLead

variable (N : ℕ) [NeZero N]

private theorem coeff_jqN_self : (jqN N).coeff (-(N : ℤ)) = 1 := by
  have h : (-(N : ℤ)) = (N : ℤ) * (-1) := by ring
  rw [jqN, h, qExpand_coeff_mul, coeff_jq_neg_one]

private theorem coeff_jqN_of_lt {m : ℤ} (hm : m < -(N : ℤ)) : (jqN N).coeff m = 0 := by
  rw [jqN]
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    refine coeff_jq_of_lt ?_
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    nlinarith
  · exact qExpand_coeff_of_not_dvd N jq hdvd

end JqNLead

/-- Evaluation at `jq` from `ℤ[X]` is injective, transported to `ℚ⟮jq⟯` through
`algebraMap_comp_evalAtJGen`. FLT's `eq_of_prime` file proves it this way; the
block's second coefficient argument is dropped. -/
theorem evalAtJGen_injective :
    Function.Injective (evalAtJGen : Polynomial ℤ →+* ↥ℚ⟮jq⟯) := by
  intro a b hab
  apply PhiGen.evalAtJ_injective
  rw [← algebraMap_comp_evalAtJGen, RingHom.comp_apply, RingHom.comp_apply, hab]

namespace PhiGen

/-! ## The conjugates are distinct -/

/-- The `q⁻¹` coefficient of the extra conjugate `j(q ^ (ℓ * ℓ))` vanishes (its
support is on the multiples of `ℓ * ℓ > 1`). -/
private theorem conj_zero_coeff_neg_one {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) :
    (conj ℓ ζ (0 : Fin (ℓ + 1))).coeff (-1 : ℤ) = 0 := by
  rw [conj_zero]
  refine qExpand_coeff_of_not_dvd _ _ ?_
  intro h
  have h1 : ((ℓ * ℓ : ℕ) : ℤ) ∣ 1 := dvd_neg.mp h
  have h2 : (ℓ * ℓ : ℕ) ∣ 1 := by exact_mod_cast h1
  have h3 : ℓ * ℓ = 1 := Nat.dvd_one.mp h2
  have h4 : 2 ≤ ℓ := hℓ.out.two_le
  nlinarith

/-- The `q⁻¹` coefficient of the `b`-th finite conjugate is `(ζ ^ b)⁻¹`. -/
private theorem conj_succ_coeff_neg_one {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (b : Fin ℓ) :
    (conj ℓ ζ b.succ).coeff (-1 : ℤ) = (((ζ ^ (b : ℕ))⁻¹ : Kˣ) : K) := by
  rw [conj_succ, qTwist_coeff, coeff_coeffEmb_jq_neg_one, mul_one, zpow_neg_one]

/-- The `ℓ + 1` conjugates are distinct: the extra root has `q⁻¹` coefficient `0`
and the finite roots have distinct `q⁻¹` coefficients `(ζ ^ b)⁻¹`. Verbatim from
the pin wrapper `Theorems/Thm_ModularCurve_PhiGen_conj_injective.lean`. -/
theorem conj_injective {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    Function.Injective (conj ℓ ζ (K := K)) := by
  have hne : ∀ b : Fin ℓ, (conj ℓ ζ (0 : Fin (ℓ + 1))).coeff (-1 : ℤ) ≠
      (conj ℓ ζ b.succ).coeff (-1 : ℤ) := by
    intro b
    rw [conj_zero_coeff_neg_one, conj_succ_coeff_neg_one]
    exact fun h => Units.ne_zero _ h.symm
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ b => exact absurd (congrArg (fun f => HahnSeries.coeff f (-1 : ℤ)) hij) (hne b)
  | succ b =>
    induction j using Fin.cases with
    | zero => exact absurd (congrArg (fun f => HahnSeries.coeff f (-1 : ℤ)) hij.symm) (hne b)
    | succ b' =>
      have hcoeff := congrArg (fun f => HahnSeries.coeff f (-1 : ℤ)) hij
      simp only [conj_succ_coeff_neg_one] at hcoeff
      have hu : (ζ ^ (b : ℕ))⁻¹ = (ζ ^ (b' : ℕ))⁻¹ := Units.ext hcoeff
      have hpow : (ζ : K) ^ (b : ℕ) = (ζ : K) ^ (b' : ℕ) := by
        have hv := congrArg Units.val (inv_injective hu)
        push_cast at hv
        exact hv
      exact congrArg Fin.succ (Fin.ext (hζ.pow_inj b.isLt b'.isLt hpow))

/-! ## Roots of the conjugate product -/

section ConjRoots

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

/-- The root count for the conjugate product: a vanishing value is one of the conjugates, a product
of `ℓ + 1` linear factors being zero only if one factor is. -/
private theorem exists_eq_conj_of_eval_phiProd_eq_zero {x : LaurentSeries K}
    (h : (phiProd ℓ (conj ℓ ζ)).eval x = 0) : ∃ i, x = conj ℓ ζ i := by
  simpa only [phiProd, Polynomial.eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero] using h

end ConjRoots

/-! ## The scalar embedding `ℚ → K((q))` -/

section ScalarEmbedding

variable (K : Type*) [Field K] [Algebra ℚ K]

private def ratC : ℚ →+* LaurentSeries K := (HahnSeries.C).comp (algebraMap ℚ K)

private theorem ratC_apply (c : ℚ) : ratC K c = HahnSeries.single 0 (algebraMap ℚ K c) :=
  rfl

private theorem coeff_ratC_of_ne (c : ℚ) {k : ℤ} (hk : k ≠ 0) : (ratC K c).coeff k = 0 := by
  rw [ratC_apply]
  exact HahnSeries.coeff_single_of_ne hk

private theorem coeffMap_jq : coeffMap (algebraMap ℚ K) jq = (coeffEmb K jq) := by
  ext k
  rfl

end ScalarEmbedding

/-! ## Pole order of `P(jq)` -/

section PoleOrder

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] {P : Polynomial ℚ}

private theorem ne_zero_of_aeval_jq_eq_jqN (h : Polynomial.aeval jq P = jqN ℓ) : P ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  have h1 := coeff_jqN_self ℓ
  rw [← h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

private theorem natDegree_eq_of_aeval_jq_eq_jqN (h : Polynomial.aeval jq P = jqN ℓ) :
    P.natDegree = ℓ := by
  have hP0 : P ≠ 0 := ne_zero_of_aeval_jq_eq_jqN ℓ h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : (Polynomial.aeval jq P).coeff (-(ℓ : ℤ)) = 0 :=
      poleOrderLE_aeval_jq P (-(ℓ : ℤ)) (by omega)
    rw [h, coeff_jqN_self] at h1
    exact one_ne_zero h1
  · have h1 := coeff_aeval_jq_neg P le_rfl
    rw [h, coeff_jqN_of_lt ℓ (by omega)] at h1
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp h1.symm)

private theorem monic_of_aeval_jq_eq_jqN (h : Polynomial.aeval jq P = jqN ℓ) : P.Monic := by
  have hd := natDegree_eq_of_aeval_jq_eq_jqN ℓ h
  have h1 := coeff_aeval_jq_neg P le_rfl
  rw [h, hd, coeff_jqN_self] at h1
  show P.coeff P.natDegree = 1
  rw [hd]
  exact h1.symm

end PoleOrder

/-! ## Transporting a relation `P(jq) = j(q ^ ℓ)` through the twist -/

section Transfer

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

omit [Algebra ℚ K] hℓ in

private theorem zeta_pow_zpow_eq_one (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : ℕ) :
    (ζ ^ b) ^ ((ℓ : ℕ) : ℤ) = (1 : Kˣ) := by
  rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, units_pow_eq_one_of_isPrimitiveRoot hζ,
    one_pow]

variable {P : Polynomial ℚ}

private theorem eval₂_ratC_jqK_of_aeval_jq_eq (h : Polynomial.aeval jq P = jqN ℓ) :
    P.eval₂ (ratC K) (coeffEmb K jq) = qExpand K ℓ (coeffEmb K jq) := by
  have h2 := congrArg (coeffMap (algebraMap ℚ K)) h
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, jqN, coeffMap_qExpand, coeffMap_jq,
    Subsingleton.elim ((coeffMap (algebraMap ℚ K)).comp (algebraMap ℚ (LaurentSeries ℚ)))
      (ratC K)] at h2
  exact h2

private theorem eval₂_ratC_conj_succ_of_aeval_jq_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (h : Polynomial.aeval jq P = jqN ℓ) (b : Fin ℓ) :
    P.eval₂ (ratC K) (conj ℓ ζ b.succ) = qExpand K ℓ (coeffEmb K jq) := by
  have h2 := congrArg (qTwist (ζ ^ (b : ℕ))) (eval₂_ratC_jqK_of_aeval_jq_eq ℓ h)
  rw [Polynomial.hom_eval₂,
    Subsingleton.elim ((qTwist (ζ ^ (b : ℕ))).comp (ratC K)) (ratC K),
    qTwist_qExpand, zeta_pow_zpow_eq_one ℓ ζ hζ, qTwist_one_apply, ← conj_succ] at h2
  exact h2

end Transfer

/-! ## Vieta: the finite conjugates sum to `-P.coeff (ℓ - 1)` -/

section Vieta

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)
variable {P : Polynomial ℚ}

/-- Vieta, as the identification of `P` itself: if `P(j(q)) = j(q ^ ℓ)` then `P` *is* the product of
the `ℓ` finite conjugate linear factors plus the constant `j(q ^ ℓ)`. -/
private theorem map_ratC_eq_prod_add_of_aeval_jq_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (h : Polynomial.aeval jq P = jqN ℓ) :
    P.map (ratC K)
      = (∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj ℓ ζ b.succ)))
        + Polynomial.C (qExpand K ℓ (coeffEmb K jq)) := by
  have hPdeg : P.natDegree = ℓ := natDegree_eq_of_aeval_jq_eq_jqN ℓ h
  have hPmonic : P.Monic := monic_of_aeval_jq_eq_jqN ℓ h
  set A : Polynomial (LaurentSeries K) := P.map (ratC K) with hA
  set B : Polynomial (LaurentSeries K) :=
    ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj ℓ ζ b.succ)) with hB
  have hAmonic : A.Monic := hPmonic.map _
  have hAdeg : A.natDegree = ℓ := by rw [hA, hPmonic.natDegree_map, hPdeg]
  have hBmonic : B.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hBdeg : B.natDegree = ℓ := by
    rw [hB, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have hinj : Function.Injective (fun b : Fin ℓ => conj ℓ ζ b.succ) := fun b b' hbb' =>
    Fin.succ_injective ℓ (conj_injective ℓ ζ hζ hbb')
  have key : A - B = Polynomial.C (qExpand K ℓ (coeffEmb K jq)) := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hinj (fun b => ?_) ?_
    · have hAev : A.eval (conj ℓ ζ b.succ) = qExpand K ℓ (coeffEmb K jq) := by
        rw [hA, Polynomial.eval_map]
        exact eval₂_ratC_conj_succ_of_aeval_jq_eq ℓ ζ hζ h b
      have hBev : B.eval (conj ℓ ζ b.succ) = 0 := by
        rw [hB, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp)
      simp only [Polynomial.eval_sub, Polynomial.eval_C, hAev, hBev, sub_zero]
    · rw [Fintype.card_fin]
      refine max_lt ?_ (by rw [Polynomial.natDegree_C]; exact hℓ.out.pos)
      by_cases hAB : A = B
      · rw [hAB, sub_self, Polynomial.natDegree_zero]
        exact hℓ.out.pos
      · refine lt_of_lt_of_eq
          (Polynomial.natDegree_lt_natDegree (sub_ne_zero.mpr hAB) ?_) hAdeg
        exact Polynomial.degree_sub_lt_left
          (by rw [Polynomial.degree_eq_natDegree hAmonic.ne_zero,
                Polynomial.degree_eq_natDegree hBmonic.ne_zero, hAdeg, hBdeg])
          hAmonic.ne_zero (by rw [hAmonic.leadingCoeff, hBmonic.leadingCoeff])
  calc A = (A - B) + B := (sub_add_cancel A B).symm
    _ = Polynomial.C (qExpand K ℓ (coeffEmb K jq)) + B := by rw [key]
    _ = B + Polynomial.C (qExpand K ℓ (coeffEmb K jq)) := add_comm _ _

/-- The consequence at degree `ℓ - 1`: the finite conjugates sum to `-P.coeff (ℓ - 1)`, a rational
number. -/
private theorem sum_conj_succ_eq_ratC_of_aeval_jq_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (h : Polynomial.aeval jq P = jqN ℓ) :
    ∑ b : Fin ℓ, conj ℓ ζ b.succ = ratC K (-(P.coeff (ℓ - 1))) := by
  have key := map_ratC_eq_prod_add_of_aeval_jq_eq ℓ ζ hζ h
  have hcoeff := congrArg (fun p => Polynomial.coeff p (ℓ - 1)) key
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  simp only [Polynomial.coeff_add, Polynomial.coeff_C,
    ite_eq_right (by omega : ¬(ℓ - 1 = 0)), add_zero] at hcoeff
  have hBcoeff : (∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj ℓ ζ b.succ))).coeff (ℓ - 1)
      = -∑ b : Fin ℓ, conj ℓ ζ b.succ := by
    have hv := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin ℓ))
      (fun b => conj ℓ ζ b.succ) (by simp [hℓ.out.pos])
    simpa using hv
  rw [Polynomial.coeff_map, hBcoeff] at hcoeff
  have hzero : ∑ b : Fin ℓ, conj ℓ ζ b.succ + ratC K (P.coeff (ℓ - 1)) = 0 := by
    rw [add_comm, hcoeff, neg_add_cancel]
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left hzero

end Vieta

/-! ## The refutation: `j(q ^ ℓ)` is not a polynomial in `j(q)` -/

section Refutation

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private theorem coeff_sum_conj_succ_self (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    (∑ b : Fin ℓ, conj ℓ ζ b.succ).coeff ((ℓ : ℕ) : ℤ) =
      (ℓ : K) * algebraMap ℚ K (jq.coeff ((ℓ : ℕ) : ℤ)) := by
  rw [HahnSeries.coeff_sum]
  have hterm : ∀ b : Fin ℓ, (conj ℓ ζ b.succ).coeff ((ℓ : ℕ) : ℤ) =
      algebraMap ℚ K (jq.coeff ((ℓ : ℕ) : ℤ)) := by
    intro b
    rw [conj_succ, qTwist_coeff, zeta_pow_zpow_eq_one ℓ ζ hζ, Units.val_one, one_mul,
      coeffEmb_coeff]
  rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

private theorem coeff_sum_conj_succ_ne_zero (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    (∑ b : Fin ℓ, conj ℓ ζ b.succ).coeff ((ℓ : ℕ) : ℤ) ≠ 0 := by
  rw [coeff_sum_conj_succ_self ℓ ζ hζ]
  refine mul_ne_zero ?_ ?_
  · rw [show ((ℓ : ℕ) : K) = algebraMap ℚ K ((ℓ : ℕ) : ℚ) from (map_natCast _ _).symm]
    intro hc
    exact (Nat.cast_ne_zero (R := ℚ)).mpr hℓ.out.ne_zero
      ((algebraMap ℚ K).injective (by rw [hc, map_zero]))
  · intro hc
    have h0 : jq.coeff ((ℓ : ℕ) : ℤ) = 0 :=
      (algebraMap ℚ K).injective (by rw [hc, map_zero])
    have h1 := one_le_coeff_jq ℓ
    rw [h0] at h1
    norm_num at h1

/-- The other half of the argument: the sum of the `ℓ` finite conjugates is *not* a rational
constant. It is fixed by every twist, so it is a series in `q ^ ℓ`, and its coefficient at the
twist-fixed exponent `ℓ` is `ℓ * jq.coeff ℓ ≠ 0`, whereas a rational constant vanishes there. -/
private theorem sum_conj_succ_ne_ratC (hζ : IsPrimitiveRoot (ζ : K) ℓ) (c : ℚ) :
    ∑ b : Fin ℓ, conj ℓ ζ b.succ ≠ ratC K c := by
  intro h
  refine coeff_sum_conj_succ_ne_zero ℓ ζ hζ ?_
  rw [h]
  exact coeff_ratC_of_ne K c (by exact_mod_cast hℓ.out.ne_zero)

end Refutation

section Headline

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

set_option linter.style.haveILetI false in
/-- The prime non-membership: `j(q ^ ℓ)` is not a polynomial in `j(q)` — two lines, and one
arithmetic input, which is derived here rather than assumed. The conjugate product's `Y ^ (ℓ - 1)`
coefficient is the sum of the `ℓ` finite conjugates, twist-invariant and with coefficient
`ℓ * jq.coeff ℓ ≠ 0` at the twist-fixed exponent `ℓ`, so it is never rational
(`sum_conj_succ_ne_ratC`, whose only input is `one_le_coeff_jq` at `n = ℓ`); while Vieta identifies
`P` with that product plus the constant `j(q ^ ℓ)`, forcing `P.coeff (ℓ - 1)` to be that same sum
(`sum_conj_succ_eq_ratC_of_aeval_jq_eq`). The statement takes no hypothesis. -/
private theorem jqN_not_mem_adjoin_jq : jqN ℓ ∉ Algebra.adjoin ℚ {jq} := by
  intro hmem
  obtain ⟨P, hP⟩ := Algebra.adjoin_mem_exists_aeval _ _ hmem
  haveI : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  haveI : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]
    exact hz
  exact sum_conj_succ_ne_ratC ℓ hzu.unit hζ _
    (sum_conj_succ_eq_ratC_of_aeval_jq_eq ℓ hzu.unit hζ hP)

end Headline

end PhiGen

/-! ## The fraction field `ℚ(j)` and the minimal polynomial -/

section FractionField

private scoped instance instUFMAdjoinJq : UniqueFactorizationMonoid adjoinJq :=
  transcendental_jq.uniqueFactorizationMonoid_adjoin

private theorem algebraMap_comp_evalAtJAdj :
    (algebraMap adjoinJq ℚ⟮jq⟯).comp evalAtJAdj = evalAtJGen := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  show algebraMap adjoinJq ℚ⟮jq⟯ (evalAtJAdj Polynomial.X) = evalAtJGen Polynomial.X
  rw [show evalAtJAdj Polynomial.X = jAdj from Polynomial.eval₂_X _ _,
    show evalAtJGen Polynomial.X = jGen from Polynomial.eval₂_X _ _]
  exact Subtype.ext rfl

namespace ModularPolynomialData

/-- `data.toAdjoin` annihilates `j(q ^ N)`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_aeval_jqN_toAdjoin.lean` (declared at the
`ModularCurve` level as the wrapper has it). -/
theorem _root_.ModularCurve.aeval_jqN_toAdjoin {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) : Polynomial.aeval (jqN N) data.toAdjoin = 0 := by
  rw [Polynomial.aeval_def, toAdjoin, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen]
  exact data.eval_eq_zero

/-- For an irreducible datum, `data.toAdjoin` is the minimal polynomial of
`j(q ^ N)`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq.lean`. -/
theorem minpoly_jqN_eq {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (hirr : PhiIrreducible data) :
    minpoly (↥ℚ⟮jq⟯) (jqN N) = data.toAdjoin :=
  (minpoly.eq_of_irreducible_of_monic hirr (aeval_jqN_toAdjoin data) data.toAdjoin_monic).symm

end ModularPolynomialData

end FractionField

namespace PhiGen

/-! ## The embedding `ℚ((q)) → K((q))` at level `ℓ` -/

section Embed

variable (K : Type*) [Field K] [Algebra ℚ K] (ℓ : ℕ) [NeZero ℓ]

private def qEmbedT : LaurentSeries ℚ →+* LaurentSeries K :=
  (qExpand K ℓ).comp (coeffMap (algebraMap ℚ K))

private theorem qEmbedT_apply (x : LaurentSeries ℚ) :
    qEmbedT K ℓ x = qExpand K ℓ (coeffMap (algebraMap ℚ K) x) := rfl

private theorem qEmbedT_injective : Function.Injective (qEmbedT K ℓ) :=
  (qEmbedT K ℓ).injective

private theorem qEmbedT_jq : qEmbedT K ℓ jq = qExpand K ℓ (coeffEmb K jq) := by
  rw [qEmbedT_apply, coeffMap_jq]

private theorem coeffEmb_comp_qExpand_comp_evalAtJ :
    ((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ = (qEmbedT K ℓ).comp evalAtJ := by
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply]
  rw [show qEmbedT K ℓ (evalAtJ p) = qExpand K ℓ (coeffEmb K (evalAtJ p)) from rfl]
  exact coeffEmb_qExpand K ℓ (evalAtJ p)

end Embed

section EmbedPrime

variable (K : Type*) [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private theorem qEmbedT_jqN : qEmbedT K ℓ (jqN ℓ) = conj ℓ ζ (0 : Fin (ℓ + 1)) := by
  rw [conj_zero, qEmbedT_apply, jqN, coeffMap_qExpand, coeffMap_jq, qExpand_qExpand]

private theorem qTwist_comp_qEmbedT (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : ℕ) :
    (qTwist (ζ ^ b)).comp (qEmbedT K ℓ) = qEmbedT K ℓ := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, qEmbedT_apply, qTwist_qExpand, zeta_pow_zpow_eq_one ℓ ζ hζ b,
    qTwist_one_apply]

private theorem conj_succ_zero : conj ℓ ζ (0 : Fin ℓ).succ = (coeffEmb K jq) := by
  rw [conj_succ, Fin.val_zero, pow_zero, qTwist_one_apply]

end EmbedPrime

/-! ## The factor-counting engine -/

section FactorAnalysis

variable (K : Type*) [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private def adjoinEmbedT : adjoinJq →+* LaurentSeries K :=
  (qEmbedT K ℓ).comp (algebraMap adjoinJq (LaurentSeries ℚ))

private theorem adjoinEmbedT_apply (x : adjoinJq) :
    adjoinEmbedT K ℓ x = qEmbedT K ℓ (x : LaurentSeries ℚ) := rfl

private theorem adjoinEmbedT_injective : Function.Injective (adjoinEmbedT K ℓ) :=
  fun _ _ h => Subtype.ext (qEmbedT_injective K ℓ h)


private theorem adjoinEmbedT_comp_evalAtJAdj :
    (adjoinEmbedT K ℓ).comp evalAtJAdj = (qEmbedT K ℓ).comp evalAtJ := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  show adjoinEmbedT K ℓ (evalAtJAdj Polynomial.X) = qEmbedT K ℓ (evalAtJ Polynomial.X)
  rw [show evalAtJAdj Polynomial.X = jAdj from Polynomial.eval₂_X _ _, evalAtJ_X]
  rfl

variable {K ℓ ζ}

/-- The descent that a vanishing at the extra conjugate forces: if the level-`ℓ` image of `x` is
`conj 0 = j(q ^ (ℓ * ℓ))` then `x` is `j(q ^ ℓ)`. `qEmbedT` is injective, and `qEmbedT_jqN`
identifies that conjugate with the image of `j(q ^ ℓ)` — so this is where a root of the conjugate
product comes back down to the non-membership `j(q ^ ℓ) ∉ ℚ[j(q)]`. -/
private theorem eq_jqN_of_adjoinEmbedT_eq_conj_zero {x : adjoinJq}
    (h : adjoinEmbedT K ℓ x = conj ℓ ζ 0) : (x : LaurentSeries ℚ) = jqN ℓ := by
  refine qEmbedT_injective K ℓ ?_
  calc qEmbedT K ℓ (x : LaurentSeries ℚ)
      = adjoinEmbedT K ℓ x := (adjoinEmbedT_apply K ℓ x).symm
    _ = conj ℓ ζ 0 := h
    _ = qEmbedT K ℓ (jqN ℓ) := (qEmbedT_jqN K ℓ ζ).symm

/-- The level-`ℓ` image of an element of `ℚ[j(q)]` has vanishing `q⁻¹` coefficient: it is a series
in `q ^ ℓ`, and `ℓ ∤ -1`. That is the slot in which the finite conjugates are separated, their
coefficient at `-1` being `(ζ ^ b)⁻¹ ≠ 0`. -/
private theorem coeff_neg_one_adjoinEmbedT (x : adjoinJq) :
    (adjoinEmbedT K ℓ x).coeff (-1 : ℤ) = 0 := by
  rw [adjoinEmbedT_apply, qEmbedT_apply]
  refine qExpand_coeff_of_not_dvd _ _ ?_
  intro hdvd
  have h1 : ((ℓ : ℕ) : ℤ) ∣ 1 := dvd_neg.mp hdvd
  exact hℓ.out.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast h1))

private theorem eval_map_conj_succ_eq_zero (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {D : Polynomial adjoinJq} (h : (D.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq) = 0)
    (b : Fin ℓ) : (D.map (adjoinEmbedT K ℓ)).eval (conj ℓ ζ b.succ) = 0 := by
  have hcomp : (qTwist (ζ ^ (b : ℕ))).comp (adjoinEmbedT K ℓ) = adjoinEmbedT K ℓ := by
    rw [adjoinEmbedT, ← RingHom.comp_assoc, qTwist_comp_qEmbedT K ℓ ζ hζ]
  have key : qTwist (ζ ^ (b : ℕ)) ((D.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq))
      = (D.map (adjoinEmbedT K ℓ)).eval (qTwist (ζ ^ (b : ℕ)) (coeffEmb K jq)) := by
    rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂, hcomp]
  rw [conj_succ, ← key, h, map_zero]

/-- A nonzero `D` over `ℚ[j(q)]` whose level-`ℓ` image vanishes at `j(q)` has degree at least `ℓ`:
that image vanishes at the `ℓ` distinct finite conjugates, and a nonzero polynomial cannot have `ℓ`
roots. -/
private theorem le_natDegree_of_eval_map_jqK_eq_zero (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {D : Polynomial adjoinJq} (hD : D ≠ 0)
    (h : (D.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq) = 0) : ℓ ≤ D.natDegree := by
  have hconj : Function.Injective fun b : Fin ℓ => conj ℓ ζ b.succ :=
    fun b b' hbb' => Fin.succ_injective ℓ (conj_injective ℓ ζ hζ hbb')
  have hroots : ∀ b : Fin ℓ, (D.map (adjoinEmbedT K ℓ)).eval (conj ℓ ζ b.succ) = 0 :=
    fun b => eval_map_conj_succ_eq_zero hζ h b
  have hDσ : D.map (adjoinEmbedT K ℓ) ≠ 0 := fun h0 =>
    hD (Polynomial.map_injective _ (adjoinEmbedT_injective K ℓ)
      (by rw [h0, Polynomial.map_zero]))
  have hdeg : ℓ ≤ (D.map (adjoinEmbedT K ℓ)).natDegree := by
    by_contra hlt
    rw [not_le] at hlt
    exact hDσ (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (f := fun b : Fin ℓ => conj ℓ ζ b.succ) hconj hroots (by rwa [Fintype.card_fin]))
  calc ℓ ≤ (D.map (adjoinEmbedT K ℓ)).natDegree := hdeg
    _ ≤ D.natDegree := Polynomial.natDegree_map_le

end FactorAnalysis

/-! ## A divisor of degree at most one of a rootless polynomial -/

section NoRootDivisor

/-- A divisor of a polynomial without roots is a unit, provided it has degree at most one and unit
leading coefficient: of degree `0` it is a unit constant, and of degree `1` it would have the root
`-u⁻¹ * p.coeff 0` for `u = p.leadingCoeff`, hence so would any polynomial it divides. -/
private theorem isUnit_of_dvd_of_natDegree_le_one {R : Type*} [CommRing R]
    {B P : Polynomial R} (hdvd : B ∣ P) (hlc : IsUnit B.leadingCoeff) (hdeg : B.natDegree ≤ 1)
    (hroot : ∀ x, P.eval x ≠ 0) : IsUnit B := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h0 | h1
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    exact Polynomial.isUnit_C.mpr (by rwa [Polynomial.leadingCoeff, h0] at hlc)
  · exfalso
    obtain ⟨u, hu⟩ := hlc
    obtain ⟨D, hD⟩ := hdvd
    have hu1 : (u : R) = B.coeff 1 := by rw [hu, Polynomial.leadingCoeff, h1]
    have hBev : ∀ x : R, B.eval x = B.coeff 1 * x + B.coeff 0 := fun x => by
      conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
    have hrootB : B.eval ((↑u⁻¹ : R) * -B.coeff 0) = 0 := by
      rw [hBev, ← hu1]
      linear_combination (-B.coeff 0) * u.mul_inv
    exact hroot _ (by rw [hD, Polynomial.eval_mul, hrootB, zero_mul])

end NoRootDivisor

/-! ## The splitting identity in `K((q))` -/

section Splitting

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

/-- The splitting hypothesis with `qEmbedT` in place of the composite
`(coeffEmb K).comp (qExpand ℚ ℓ)` that the pin spells out: the coefficients of `Φ`
evaluate in `K((q))` to the conjugate product. -/
private theorem map_qEmbedT_evalAtJ_eq_phiProd (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ)) :
    data.Φ.map ((qEmbedT K ℓ).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) := by
  rw [← coeffEmb_comp_qExpand_comp_evalAtJ K ℓ]
  exact hsplit

end Splitting

section Irreducibility

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

/-- The datum over the fraction field `ℚ(j(q))` is the image of `Φ` over `ℚ[j(q)]`. -/
private theorem toAdjoin_eq_map_evalAtJAdj {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) :
    data.toAdjoin = (data.Φ.map evalAtJAdj).map (algebraMap adjoinJq ℚ⟮jq⟯) := by
  rw [ModularPolynomialData.toAdjoin, Polynomial.map_map, algebraMap_comp_evalAtJAdj]

/-- Gauss: `Φ` is irreducible over `ℚ(j(q))` as soon as it is irreducible over
`ℚ[j(q)]`, `Φ.map evalAtJAdj` being monic. -/
private theorem phiIrreducible_iff_irreducible_map_evalAtJAdj {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) :
    PhiIrreducible data ↔ Irreducible (data.Φ.map evalAtJAdj) := by
  rw [PhiIrreducible, toAdjoin_eq_map_evalAtJAdj data]
  exact ((data.monic.map evalAtJAdj).irreducible_iff_irreducible_map_fraction_map).symm

/-- The datum whose coefficients split into the conjugate product is irreducible
over `ℚ(j)`. Over `K((q))` the image of `Φ` is the product of the `ℓ + 1`
conjugate linear factors, so by Gauss it suffices to factor `Φ = A · B` over
`ℚ[j(q)]`: evaluating at `j(q)` kills one factor, the `ℓ` distinct conjugates
force that factor to have degree `≥ ℓ`, and the other factor is then a unit
because a degree-`1` factor would have a root in `ℚ[j(q)]`, which
`j(q ^ ℓ) ∉ ℚ[j(q)]` forbids. The two levels are named in the proof: `Φ₀` is
`Φ(j(q), Y)` over `ℚ[j(q)]`, and `Φ₁` is its level-`ℓ` image `Φ(j(q ^ ℓ), Y)` over
`K((q))`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_PhiGen_phiIrreducible_of_splits.lean`. -/
theorem phiIrreducible_of_splits {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ)) : PhiIrreducible data := by
  set Φ₀ : Polynomial adjoinJq := data.Φ.map evalAtJAdj with hΦ₀
  set Φ₁ : Polynomial (LaurentSeries K) := Φ₀.map (adjoinEmbedT K ℓ) with hΦ₁
  have hsplit₁ : Φ₁ = phiProd ℓ (conj ℓ ζ) :=
    calc Φ₁ = data.Φ.map ((qEmbedT K ℓ).comp evalAtJ) := by
          rw [hΦ₁, hΦ₀, Polynomial.map_map, adjoinEmbedT_comp_evalAtJAdj]
      _ = phiProd ℓ (conj ℓ ζ) := map_qEmbedT_evalAtJ_eq_phiProd ℓ ζ data hsplit
  have hmonic : Φ₀.Monic := by
    rw [hΦ₀]
    exact data.monic.map _
  have hdeg : Φ₀.natDegree = ℓ + 1 := by
    rw [hΦ₀]
    calc (data.Φ.map evalAtJAdj).natDegree = data.Φ.natDegree := data.monic.natDegree_map _
      _ = dedekindPsi ℓ := data.natDegree_eq
      _ = ℓ + 1 := dedekindPsi_prime hℓ.out
  have hnoRoot : ∀ β : adjoinJq, Φ₀.eval β ≠ 0 := by
    intro β hβ
    have hβ₁ : (phiProd ℓ (conj ℓ ζ)).eval (adjoinEmbedT K ℓ β) = 0 := by
      rw [← hsplit₁, hΦ₁]
      exact Polynomial.IsRoot.map hβ
    obtain ⟨i, hi⟩ := exists_eq_conj_of_eval_phiProd_eq_zero ℓ ζ hβ₁
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨b, rfl⟩
    · exact jqN_not_mem_adjoin_jq ℓ
        (eq_jqN_of_adjoinEmbedT_eq_conj_zero hi ▸ β.2)
    · have hvan : (conj ℓ ζ b.succ).coeff (-1 : ℤ) = 0 := by
        rw [← hi]
        exact coeff_neg_one_adjoinEmbedT β
      rw [conj_succ_coeff_neg_one] at hvan
      exact Units.ne_zero _ hvan
  refine (phiIrreducible_iff_irreducible_map_evalAtJAdj data).mpr ?_
  rw [← hΦ₀]
  constructor
  · exact Polynomial.not_isUnit_of_natDegree_pos _ (by omega)
  · intro A B hAB
    have hA0 : A ≠ 0 := fun h => hmonic.ne_zero (by rw [hAB, h, zero_mul])
    have hB0 : B ≠ 0 := fun h => hmonic.ne_zero (by rw [hAB, h, mul_zero])
    have hlc : A.leadingCoeff * B.leadingCoeff = 1 :=
      calc A.leadingCoeff * B.leadingCoeff = (A * B).leadingCoeff :=
            (Polynomial.leadingCoeff_mul A B).symm
        _ = Φ₀.leadingCoeff := by rw [← hAB]
        _ = 1 := hmonic.leadingCoeff
    have hsum : A.natDegree + B.natDegree = ℓ + 1 :=
      calc A.natDegree + B.natDegree = (A * B).natDegree :=
            (Polynomial.natDegree_mul hA0 hB0).symm
        _ = Φ₀.natDegree := by rw [← hAB]
        _ = ℓ + 1 := hdeg
    have hlcA : IsUnit A.leadingCoeff := IsUnit.of_mul_eq_one _ hlc
    have hlcB : IsUnit B.leadingCoeff := IsUnit.of_mul_eq_one_right _ hlc
    have hAdvd : A ∣ Φ₀ := ⟨B, hAB⟩
    have hBdvd : B ∣ Φ₀ := ⟨A, hAB.trans (mul_comm A B)⟩
    have hzero : ((A.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq))
        * ((B.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq)) = 0 :=
      calc (A.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq)
            * (B.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq)
          = ((A * B).map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq) := by
              rw [← Polynomial.eval_mul, ← Polynomial.map_mul]
        _ = Φ₁.eval (coeffEmb K jq) := by rw [← hAB, ← hΦ₁]
        _ = (phiProd ℓ (conj ℓ ζ)).eval (coeffEmb K jq) := by rw [hsplit₁]
        _ = (phiProd ℓ (conj ℓ ζ)).eval (conj ℓ ζ (0 : Fin ℓ).succ) := by
              rw [← conj_succ_zero K ℓ ζ]
        _ = 0 := phiProd_eval_conj ℓ (conj ℓ ζ) _
    rcases mul_eq_zero.mp hzero with hAz | hBz
    · right
      have hAdeg : ℓ ≤ A.natDegree := le_natDegree_of_eval_map_jqK_eq_zero hζ hA0 hAz
      have hB1 : B.natDegree ≤ 1 := by omega
      exact isUnit_of_dvd_of_natDegree_le_one hBdvd hlcB hB1 hnoRoot
    · left
      have hBdeg : ℓ ≤ B.natDegree := le_natDegree_of_eval_map_jqK_eq_zero hζ hB0 hBz
      have hA1 : A.natDegree ≤ 1 := by omega
      exact isUnit_of_dvd_of_natDegree_le_one hAdvd hlcA hA1 hnoRoot

end Irreducibility

end PhiGen


namespace PhiGen

/-! ## Symmetry of the datum from its splitting -/

section Swap

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

/-- The datum annihilates `j(q ^ ℓ)` under the swapped evaluation, read off the
splitting: the product has the root `j(q)` with multiplicity one. -/
theorem eval_swap_eq_zero_of_splits (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ)) :
    data.Φ.eval₂ (evalAtJqN ℓ) jq = 0 := by
  have h1 : data.Φ.eval₂ ((qEmbedT K ℓ).comp evalAtJ) (coeffEmb K jq) = 0 := by
    rw [← Polynomial.eval_map, map_qEmbedT_evalAtJ_eq_phiProd ℓ ζ data hsplit,
      ← conj_succ_zero K ℓ ζ, phiProd, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin ℓ).succ)) (by simp)
  have h2 : data.Φ.eval₂ ((qExpand K ℓ).comp ((qEmbedT K ℓ).comp evalAtJ))
      (qExpand K ℓ (coeffEmb K jq)) = 0 := by
    have h := congrArg (qExpand K ℓ) h1
    rwa [Polynomial.hom_eval₂, map_zero] at h
  apply qEmbedT_injective K ℓ
  rw [map_zero, Polynomial.hom_eval₂, qEmbedT_jq]
  have hhom : (qEmbedT K ℓ).comp (evalAtJqN ℓ)
      = (qExpand K ℓ).comp ((qEmbedT K ℓ).comp evalAtJ) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    show qEmbedT K ℓ (evalAtJqN ℓ Polynomial.X)
      = qExpand K ℓ (qEmbedT K ℓ (evalAtJ Polynomial.X))
    rw [evalAtJqN_X, evalAtJ_X, qEmbedT_jq, qEmbedT_jqN K ℓ ζ, conj_zero, qExpand_qExpand]
  rw [hhom]
  exact h2

end Swap

end PhiGen

end ModularCurve

end

