/-
  T12 — the 895 block: irreducibility and symmetry of the datum.

  The block is FLT's single largest shared development: it ships in five pin files
  (the three graph nodes `phiIrreducible_of_splits`, `evalSymm_of_splits`,
  `transposeToAdjoin_monic_of_qExpansion`, plus the two hidden exports
  `swapBivar_monic_of_coeff_bounds` and `evalSymm_of_irreducible`), `5 × 895 ≈
  4,475` pin lines. The port writes it once.

  ## What it proves

  * `conj_injective` — the `ℓ + 1` conjugates are distinct (separated by their
    `q⁻¹` coefficients);
  * `aeval_jq_ne_jqN` / `jqN_not_mem_adjoin_jq` — `j(q ^ ℓ)` is not a polynomial in
    `j(q)` (the twist-sum refutation, using `one_le_coeff_jq` at `n = ℓ`);
  * `phiIrreducible_of_splits` — the datum is irreducible over `ℚ(j)`, by the
    factor-counting argument: a nonzero `D ∈ ℚ[j(q)]` with `D(jq) = 0` has degree
    `≥ ℓ` (the conjugates are distinct), so one factor of any factorisation has
    degree `≤ 1`, and it is a unit because `j(q^ℓ) ∉ ℚ[j(q)]`;
  * `swapBivar_monic_of_coeff_bounds`, `transposeToAdjoin_monic_of_qExpansion` —
    the transpose `swapBivar Φ` is monic of degree `ψ(ℓ)` from the pole bounds of
    the descended family;
  * `evalSymm_of_irreducible`, `evalSymm_of_splits` — symmetry, by uniqueness of
    the minimal polynomial: the transpose is monic, annihilates `j(q^ℓ)` and has
    the minimal degree, so it equals `Φ`;
  * `evalAtJGen_injective`, `swapBivar_eq_of_evalSymm` — the two auxiliary
    injectivity/symmetry transfers.

  ## Reuse (work order §3.1)

  The block's private `evalAtJ_injective` is T11's public one; its private
  `coeff_aeval_jq_neg` is T9's; its private `evalAtJ_eq_aeval_map_rat` is the
  `Defs/Jq.lean` promotion; `evalAtJGen_injective` is derived from
  `evalAtJ_injective` through `algebraMap_comp_evalAtJGen` (the `eq_of_prime` file's
  two-line proof), and `conj_injective` is written once and exported.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_splits.lean` (895 lines) for
  everything except `swapBivar_eq_of_evalSymm`, which is
  `P2M/Sol/S_ModularCurve_swapBivar_eq_of_evalSymm.lean` (95 lines). The public
  statements are the `Theorems/` wrappers verbatim where a wrapper exists, and the
  `S_` file's own public declarations otherwise (`aeval_jq_ne_jqN`,
  `jqN_not_mem_adjoin_jq`, `evalSymm_of_swapBivar_eq`, `eval_swap_eq_zero_of_splits`).

  ## Assumptions

  `Defs/PhiGen`'s `conj`/`conj_zero`/`conj_succ`/`phiProd`/`phiProd_eval_conj`/
  `ModularPolynomialData`/`EvalSymm`/`PhiIrreducible`/`adjoinJq`/`jAdj`/
  `evalAtJAdj`/`swapBivar`; `Defs/Fields`'s `jGen`/`evalAtJGen`/
  `algebraMap_comp_evalAtJGen`/`toAdjoin`/`toAdjoin_monic`; `Defs/Jq`'s `jq`/
  `jqN`/`evalAtJ`/`evalAtJ_eq_aeval_map`/`coeff_aeval_jq_neg`/`transcendental_jq`/
  `dedekindPsi_prime`; T11's `PhiGen.evalAtJ_injective`; T12's `one_le_coeff_jq`.
-/
import FLTForHuman.ModularCurve.JqCoeffPositivity
import FLTForHuman.ModularCurve.PhiGenDescendsStructure
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

section CoeffEmbJq

variable (K : Type*) [Field K] [Algebra ℚ K]

private theorem coeff_coeffEmb_jq_neg_one : (coeffEmb K jq).coeff (-1 : ℤ) = 1 := by
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]

end CoeffEmbJq

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

private theorem coeff_aeval_jq_of_lt (P : Polynomial ℚ) {m : ℤ}
    (hm : m < -(P.natDegree : ℤ)) : (Polynomial.aeval jq P).coeff m = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jq_pow_of_lt,
    mul_zero]
  have : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  omega

private theorem coeff_aeval_jq_neg_natDegree (P : Polynomial ℚ) :
    (Polynomial.aeval jq P).coeff (-(P.natDegree : ℤ)) = P.coeff P.natDegree := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
    Finset.sum_eq_single P.natDegree]
  · rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jq_pow_self,
      mul_one]
  · intro i hi hin
    have hilt : i < P.natDegree :=
      lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
    rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jq_pow_of_lt
      (by omega), mul_zero]
  · intro hn'
    exact absurd (Finset.self_mem_range_succ P.natDegree) hn'

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
      coeff_aeval_jq_of_lt P (by omega)
    rw [h, coeff_jqN_self] at h1
    exact one_ne_zero h1
  · have h1 := coeff_aeval_jq_neg_natDegree P
    rw [h, coeff_jqN_of_lt ℓ (by omega)] at h1
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp h1.symm)

private theorem monic_of_aeval_jq_eq_jqN (h : Polynomial.aeval jq P = jqN ℓ) : P.Monic := by
  have hd := natDegree_eq_of_aeval_jq_eq_jqN ℓ h
  have h1 := coeff_aeval_jq_neg_natDegree P
  rw [h, hd, coeff_jqN_self] at h1
  show P.coeff P.natDegree = 1
  rw [hd]
  exact h1.symm

end PoleOrder

/-! ## Transporting a relation `P(jq) = j(q ^ ℓ)` through the twist -/

section Transfer

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

omit [Algebra ℚ K] hℓ in

private theorem zeta_pow_eq_one (hζ : IsPrimitiveRoot (ζ : K) ℓ) : ζ ^ ℓ = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one])

omit [Algebra ℚ K] hℓ in

private theorem zeta_pow_zpow_eq_one (hζ : IsPrimitiveRoot (ζ : K) ℓ) (b : ℕ) :
    (ζ ^ b) ^ ((ℓ : ℕ) : ℤ) = (1 : Kˣ) := by
  rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, zeta_pow_eq_one ℓ ζ hζ, one_pow]

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

private theorem sum_conj_succ_eq_ratC_of_aeval_jq_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (h : Polynomial.aeval jq P = jqN ℓ) :
    ∑ b : Fin ℓ, conj ℓ ζ b.succ = ratC K (-(P.coeff (ℓ - 1))) := by
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
  have hcoeff := congrArg (fun p => Polynomial.coeff p (ℓ - 1)) key
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C,
    ite_eq_right (by omega : ¬(ℓ - 1 = 0))] at hcoeff
  have hBcoeff : B.coeff (ℓ - 1) = -∑ b : Fin ℓ, conj ℓ ζ b.succ := by
    have hv := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin ℓ))
      (fun b => conj ℓ ζ b.succ) (by simp [hℓ.out.pos])
    simpa using hv
  have hAcoeff : A.coeff (ℓ - 1) = ratC K (P.coeff (ℓ - 1)) := Polynomial.coeff_map _ _
  rw [hAcoeff, hBcoeff, sub_neg_eq_add, add_comm] at hcoeff
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left hcoeff

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

private theorem coeff_sum_conj_succ_ne_zero
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
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
    have h1 := hpos ℓ
    rw [h0] at h1
    norm_num at h1

theorem aeval_jq_ne_jqN_of_isPrimitiveRoot
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (P : Polynomial ℚ) : Polynomial.aeval jq P ≠ jqN ℓ := by
  intro h
  have h1 := sum_conj_succ_eq_ratC_of_aeval_jq_eq ℓ ζ hζ h
  have h2 := coeff_sum_conj_succ_ne_zero ℓ ζ hpos hζ
  rw [h1] at h2
  exact h2 (coeff_ratC_of_ne K _ (by exact_mod_cast hℓ.out.ne_zero))

end Refutation

section Headline

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]

set_option linter.style.haveILetI false in
/-- No polynomial in `j(q)` equals `j(q ^ ℓ)`. Uses `one_le_coeff_jq` at `n = ℓ`
for the nonvanishing of the `q ^ ℓ` coefficient of the twist-sum. -/
theorem aeval_jq_ne_jqN (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (P : Polynomial ℚ) :
    Polynomial.aeval jq P ≠ jqN ℓ := by
  haveI : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  haveI : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  refine aeval_jq_ne_jqN_of_isPrimitiveRoot ℓ hzu.unit hpos ?_ P
  rw [hzu.unit_spec]
  exact hz

/-- `j(q ^ ℓ)` is not in `ℚ[j(q)]`. -/
theorem jqN_not_mem_adjoin_jq (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) :
    jqN ℓ ∉ Algebra.adjoin ℚ {jq} := by
  intro hmem
  obtain ⟨P, hP⟩ := Algebra.adjoin_mem_exists_aeval _ _ hmem
  exact aeval_jq_ne_jqN ℓ hpos P hP

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

private theorem qEmbedT_eq_coeffEmb_qExpand (x : LaurentSeries ℚ) :
    qEmbedT K ℓ x = coeffEmb K (qExpand ℚ ℓ x) := by
  rw [coeffEmb_qExpand]
  rfl

private theorem coeffEmb_comp_qExpand_comp_evalAtJ :
    ((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ = (qEmbedT K ℓ).comp evalAtJ := by
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply]
  rw [qEmbedT_eq_coeffEmb_qExpand]

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

private theorem eval_map_conj_succ_eq_zero (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {D : Polynomial adjoinJq} (h : (D.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq) = 0)
    (b : Fin ℓ) : (D.map (adjoinEmbedT K ℓ)).eval (conj ℓ ζ b.succ) = 0 := by
  have hcomp : (qTwist (ζ ^ (b : ℕ))).comp (adjoinEmbedT K ℓ) = adjoinEmbedT K ℓ := by
    rw [adjoinEmbedT, ← RingHom.comp_assoc, qTwist_comp_qEmbedT K ℓ ζ hζ]
  have key : qTwist (ζ ^ (b : ℕ)) ((D.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq))
      = (D.map (adjoinEmbedT K ℓ)).eval (qTwist (ζ ^ (b : ℕ)) (coeffEmb K jq)) := by
    rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂, hcomp]
  rw [conj_succ, ← key, h, map_zero]

private theorem le_natDegree_of_eval_map_jqK_eq_zero (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    {D : Polynomial adjoinJq} (hD : D ≠ 0)
    (h : (D.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq) = 0) : ℓ ≤ D.natDegree := by
  have hmap : ℓ ≤ (D.map (adjoinEmbedT K ℓ)).natDegree := by
    by_contra hlt
    rw [not_le] at hlt
    have hzero : D.map (adjoinEmbedT K ℓ) = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
        (f := fun b : Fin ℓ => conj ℓ ζ b.succ)
        (fun b b' hbb' => Fin.succ_injective ℓ (conj_injective ℓ ζ hζ hbb'))
        (fun b => eval_map_conj_succ_eq_zero hζ h b)
        (by rwa [Fintype.card_fin])
    exact hD (Polynomial.map_injective _ (adjoinEmbedT_injective K ℓ)
      (by rw [hzero, Polynomial.map_zero]))
  exact le_trans hmap Polynomial.natDegree_map_le

private theorem eval_map_evalAtJAdj_ne_zero
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (data : ModularPolynomialData ℓ)
    (hsplit : (data.Φ.map evalAtJAdj).map (adjoinEmbedT K ℓ) = phiProd ℓ (conj ℓ ζ))
    (β : adjoinJq) : (data.Φ.map evalAtJAdj).eval β ≠ 0 := by
  intro heval
  have hmap : (phiProd ℓ (conj ℓ ζ)).eval (adjoinEmbedT K ℓ β) = 0 := by
    rw [← hsplit, Polynomial.eval_map, Polynomial.eval₂_at_apply, heval, map_zero]
  rw [phiProd, Polynomial.eval_prod] at hmap
  obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hmap
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hi
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨b, rfl⟩
  · rw [adjoinEmbedT_apply, ← qEmbedT_jqN K ℓ ζ] at hi
    have hβ : (β : LaurentSeries ℚ) = jqN ℓ := qEmbedT_injective K ℓ hi
    exact jqN_not_mem_adjoin_jq ℓ hpos (hβ ▸ β.2)
  · have h0 : (adjoinEmbedT K ℓ β).coeff (-1 : ℤ) = 0 := by
      rw [adjoinEmbedT_apply, qEmbedT_apply]
      refine qExpand_coeff_of_not_dvd _ _ ?_
      intro hdvd
      have h1 : ((ℓ : ℕ) : ℤ) ∣ 1 := dvd_neg.mp hdvd
      have h2 : ℓ ∣ 1 := by exact_mod_cast h1
      exact hℓ.out.one_lt.ne' (Nat.dvd_one.mp h2)
    rw [hi, conj_succ_coeff_neg_one] at h0
    exact Units.ne_zero _ h0

private theorem isUnit_of_dvd_of_natDegree_le_one
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (data : ModularPolynomialData ℓ)
    (hsplit : (data.Φ.map evalAtJAdj).map (adjoinEmbedT K ℓ) = phiProd ℓ (conj ℓ ζ))
    {B : Polynomial adjoinJq} (hdvd : B ∣ data.Φ.map evalAtJAdj)
    (hlc : IsUnit B.leadingCoeff) (hdeg : B.natDegree ≤ 1) : IsUnit B := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h0 | h1
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
    refine Polynomial.isUnit_C.mpr ?_
    have hc : B.coeff 0 = B.leadingCoeff := by rw [Polynomial.leadingCoeff, h0]
    rw [hc]
    exact hlc
  · exfalso
    obtain ⟨u, hu⟩ := hlc
    obtain ⟨D, hD⟩ := hdvd
    have hu1 : (u : adjoinJq) = B.coeff 1 := by rw [hu, Polynomial.leadingCoeff, h1]
    have hBev : ∀ x : adjoinJq, B.eval x = B.coeff 1 * x + B.coeff 0 := fun x => by
      conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
    have hroot : B.eval ((↑u⁻¹ : adjoinJq) * -B.coeff 0) = 0 := by
      rw [hBev, ← hu1]
      linear_combination (-B.coeff 0) * u.mul_inv
    refine eval_map_evalAtJAdj_ne_zero hpos data hsplit ((↑u⁻¹ : adjoinJq) * -B.coeff 0) ?_
    rw [hD, Polynomial.eval_mul, hroot, zero_mul]

end FactorAnalysis

section Irreducibility

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private theorem irreducible_map_evalAtJAdj_of_splits
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : (data.Φ.map evalAtJAdj).map (adjoinEmbedT K ℓ) = phiProd ℓ (conj ℓ ζ)) :
    Irreducible (data.Φ.map evalAtJAdj) := by
  have hmonic : (data.Φ.map evalAtJAdj).Monic := data.monic.map _
  have hdeg : (data.Φ.map evalAtJAdj).natDegree = ℓ + 1 := by
    rw [data.monic.natDegree_map, data.natDegree_eq, dedekindPsi_prime hℓ.out]
  constructor
  · exact Polynomial.not_isUnit_of_natDegree_pos _ (by omega)
  · intro A B hAB
    have hA0 : A ≠ 0 := fun h => hmonic.ne_zero (by rw [hAB, h, zero_mul])
    have hB0 : B ≠ 0 := fun h => hmonic.ne_zero (by rw [hAB, h, mul_zero])
    have hlcmul : A.leadingCoeff * B.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hAB]
      exact hmonic.leadingCoeff
    have hlcA : IsUnit A.leadingCoeff := IsUnit.of_mul_eq_one _ hlcmul
    have hlcB : IsUnit B.leadingCoeff := IsUnit.of_mul_eq_one_right _ hlcmul
    have hAdvd : A ∣ data.Φ.map evalAtJAdj := ⟨B, hAB⟩
    have hBdvd : B ∣ data.Φ.map evalAtJAdj := ⟨A, hAB.trans (mul_comm A B)⟩
    have hsum : A.natDegree + B.natDegree = ℓ + 1 := by
      rw [← Polynomial.natDegree_mul hA0 hB0, ← hAB, hdeg]
    have hzero : ((A.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq))
        * ((B.map (adjoinEmbedT K ℓ)).eval (coeffEmb K jq)) = 0 := by
      rw [← Polynomial.eval_mul, ← Polynomial.map_mul, ← hAB, hsplit,
        ← conj_succ_zero K ℓ ζ]
      exact phiProd_eval_conj ℓ _ _
    rcases mul_eq_zero.mp hzero with hAz | hBz
    · right
      have hAdeg : ℓ ≤ A.natDegree := le_natDegree_of_eval_map_jqK_eq_zero hζ hA0 hAz
      exact isUnit_of_dvd_of_natDegree_le_one hpos data hsplit hBdvd hlcB (by omega)
    · left
      have hBdeg : ℓ ≤ B.natDegree := le_natDegree_of_eval_map_jqK_eq_zero hζ hB0 hBz
      exact isUnit_of_dvd_of_natDegree_le_one hpos data hsplit hAdvd hlcA (by omega)

private theorem toAdjoin_eq_map_evalAtJAdj {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N) :
    data.toAdjoin = (data.Φ.map evalAtJAdj).map (algebraMap adjoinJq ℚ⟮jq⟯) := by
  rw [ModularPolynomialData.toAdjoin, Polynomial.map_map, algebraMap_comp_evalAtJAdj]

private theorem phiIrreducible_of_splits_aux
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ)) : PhiIrreducible data := by
  rw [coeffEmb_comp_qExpand_comp_evalAtJ K ℓ] at hsplit
  have hsplit' : (data.Φ.map evalAtJAdj).map (adjoinEmbedT K ℓ)
      = phiProd ℓ (conj ℓ ζ) := by
    rw [Polynomial.map_map, adjoinEmbedT_comp_evalAtJAdj]
    exact hsplit
  show Irreducible data.toAdjoin
  rw [toAdjoin_eq_map_evalAtJAdj]
  exact ((data.monic.map evalAtJAdj).irreducible_iff_irreducible_map_fraction_map).mp
    (irreducible_map_evalAtJAdj_of_splits ℓ ζ hpos hζ data hsplit')

/-- The datum whose coefficients split into the conjugate product is irreducible
over `ℚ(j)`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_PhiGen_phiIrreducible_of_splits.lean`. -/
theorem phiIrreducible_of_splits {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ)) : PhiIrreducible data :=
  phiIrreducible_of_splits_aux ℓ ζ one_le_coeff_jq hζ data hsplit

end Irreducibility

end PhiGen

/-! ## The transpose engine: `swapBivar` of a coefficient-bounded polynomial -/

section SwapBivarEval

private theorem swapBivar_eval₂ (Φ : Polynomial (Polynomial ℤ)) (x y : LaurentSeries ℚ) :
    (swapBivar Φ).eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x := by
  set h : Polynomial (Polynomial ℤ) →+* LaurentSeries ℚ :=
    Polynomial.eval₂RingHom (Polynomial.aeval (R := ℤ) x).toRingHom y with hh
  have key : h (swapBivar Φ) = Φ.eval₂ (h.comp swapInner) (h (Polynomial.C Polynomial.X)) :=
    Polynomial.hom_eval₂ Φ swapInner h (Polynomial.C Polynomial.X)
  have hCX : h (Polynomial.C Polynomial.X) = x := by
    rw [hh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, aeval_toRingHom_X]
  have hcomp : h.comp swapInner = (Polynomial.aeval (R := ℤ) y).toRingHom := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    show h (swapInner Polynomial.X) = (Polynomial.aeval (R := ℤ) y).toRingHom Polynomial.X
    rw [aeval_toRingHom_X]
    show h ((Polynomial.aeval (R := ℤ)
      (Polynomial.X : Polynomial (Polynomial ℤ))) Polynomial.X) = y
    rw [Polynomial.aeval_X, hh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  calc (swapBivar Φ).eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y
      = h (swapBivar Φ) := rfl
    _ = Φ.eval₂ (h.comp swapInner) (h (Polynomial.C Polynomial.X)) := key
    _ = Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x := by rw [hCX, hcomp]

/-- `swapBivar Φ = Φ` implies `EvalSymm Φ`. -/
theorem evalSymm_of_swapBivar_eq {Φ : Polynomial (Polynomial ℤ)} (h : swapBivar Φ = Φ) :
    EvalSymm Φ := fun x y => by
  conv_lhs => rw [← h]
  exact swapBivar_eval₂ Φ x y

end SwapBivarEval

namespace ModularPolynomialData

/-- The transpose of a datum's `Φ` annihilates `j(q ^ N)` as soon as `Φ` does
under the swapped evaluation. -/
private theorem aeval_jqN_transposeToAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0) :
    Polynomial.aeval (jqN N) ((swapBivar data.Φ).map evalAtJGen) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen,
    evalAtJ_def, swapBivar_eval₂, ← evalAtJqN_def]
  exact hswap

private theorem swapBivar_eq_of_irreducible {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (hirr : PhiIrreducible data)
    (hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0)
    (hTmonic : ((swapBivar data.Φ).map evalAtJGen).Monic)
    (hTdeg : ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ dedekindPsi N) :
    swapBivar data.Φ = data.Φ := by
  apply Polynomial.map_injective evalAtJGen evalAtJGen_injective
  show (swapBivar data.Φ).map evalAtJGen = data.toAdjoin
  have hdvd : data.toAdjoin ∣ (swapBivar data.Φ).map evalAtJGen := by
    rw [← data.minpoly_jqN_eq hirr]
    exact minpoly.dvd _ _ (data.aeval_jqN_transposeToAdjoin hswap)
  refine eq_of_monic_of_dvd_of_natDegree_le data.toAdjoin_monic hTmonic hdvd ?_
  rw [toAdjoin, data.monic.natDegree_map, data.natDegree_eq]
  exact hTdeg

/-- Symmetry of `Φ` from irreducibility: the transpose is monic, annihilates
`j(q ^ N)` and has the minimal degree, so it equals `Φ`. Verbatim from the pin
wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_irreducible.lean`. -/
theorem evalSymm_of_irreducible {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (hirr : PhiIrreducible data)
    (hswap : data.Φ.eval₂ (evalAtJqN N) jq = 0)
    (hTmonic : ((swapBivar data.Φ).map evalAtJGen).Monic)
    (hTdeg : ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ dedekindPsi N) :
    EvalSymm data.Φ :=
  evalSymm_of_swapBivar_eq (data.swapBivar_eq_of_irreducible hirr hswap hTmonic hTdeg)

end ModularPolynomialData

/-! ## Degree bookkeeping for the transpose -/

section Engine

private theorem swapBivar_C (c : Polynomial ℤ) :
    swapBivar (Polynomial.C c) = c.map Polynomial.C := by
  have hext : swapBivar.comp (Polynomial.C : Polynomial ℤ →+* Polynomial (Polynomial ℤ))
      = Polynomial.mapRingHom (Polynomial.C : ℤ →+* Polynomial ℤ) := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    show swapBivar (Polynomial.C Polynomial.X)
      = Polynomial.mapRingHom (Polynomial.C : ℤ →+* Polynomial ℤ) Polynomial.X
    rw [swapBivar_C_X, Polynomial.coe_mapRingHom, Polynomial.map_X]
  calc swapBivar (Polynomial.C c)
      = swapBivar.comp (Polynomial.C : Polynomial ℤ →+* Polynomial (Polynomial ℤ)) c := rfl
    _ = Polynomial.mapRingHom (Polynomial.C : ℤ →+* Polynomial ℤ) c := by rw [hext]
    _ = c.map Polynomial.C := rfl

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

private theorem degree_lt_of_evalAtJ_coeff_eq_zero {P : Polynomial ℤ} {D : ℕ}
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

private theorem monic_of_evalAtJ_coeff_eq_one {P : Polynomial ℤ} {D : ℕ}
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

private theorem natDegree_le_of_evalAtJ_coeff_eq_zero {P : Polynomial ℤ} {D : ℕ}
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

namespace ModularPolynomialData

private theorem transposeToAdjoin_monic_of_coeff_bounds {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N)
    (h0 : (data.Φ.coeff 0).Monic) (h0deg : (data.Φ.coeff 0).natDegree = dedekindPsi N)
    (hk : ∀ k, k ≠ 0 → (data.Φ.coeff k).degree < (dedekindPsi N : WithBot ℕ)) :
    ((swapBivar data.Φ).map evalAtJGen).Monic ∧
      ((swapBivar data.Φ).map evalAtJGen).natDegree = dedekindPsi N := by
  obtain ⟨hmonic, hdeg⟩ := swapBivar_monic_of_coeff_bounds h0 h0deg hk
  exact ⟨hmonic.map _, by rw [hmonic.natDegree_map, hdeg]⟩

/-- The pole bounds of the descended family make the datum's transpose monic of
degree `ψ(N)`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_transposeToAdjoin_monic_of_qExpansion.lean`. -/
theorem transposeToAdjoin_monic_of_qExpansion {N : ℕ} [NeZero N]
    (data : ModularPolynomialData N)
    (h0top : (evalAtJ (data.Φ.coeff 0)).coeff (-(dedekindPsi N : ℤ)) = 1)
    (h0le : ∀ m : ℕ, dedekindPsi N < m → (evalAtJ (data.Φ.coeff 0)).coeff (-(m : ℤ)) = 0)
    (hk : ∀ k, k ≠ 0 → ∀ m : ℕ, dedekindPsi N ≤ m →
      (evalAtJ (data.Φ.coeff k)).coeff (-(m : ℤ)) = 0) :
    ((swapBivar data.Φ).map evalAtJGen).Monic ∧
      ((swapBivar data.Φ).map evalAtJGen).natDegree = dedekindPsi N := by
  obtain ⟨h0monic, h0deg⟩ := monic_of_evalAtJ_coeff_eq_one
    (natDegree_le_of_evalAtJ_coeff_eq_zero h0le) h0top
  exact transposeToAdjoin_monic_of_coeff_bounds data h0monic h0deg
    fun k hk0 => degree_lt_of_evalAtJ_coeff_eq_zero (hk k hk0)

end ModularPolynomialData

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
  rw [coeffEmb_comp_qExpand_comp_evalAtJ K ℓ] at hsplit
  have h1 : data.Φ.eval₂ ((qEmbedT K ℓ).comp evalAtJ) (coeffEmb K jq) = 0 := by
    rw [← Polynomial.eval_map, hsplit, ← conj_succ_zero K ℓ ζ, phiProd,
      Polynomial.eval_prod]
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

private theorem evalSymm_of_splits_aux
    (hpos : ∀ n : ℕ, (1 : ℚ) ≤ jq.coeff (n : ℤ)) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ))
    (hTmonic : ((swapBivar data.Φ).map evalAtJGen).Monic)
    (hTdeg : ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ dedekindPsi ℓ) :
    EvalSymm data.Φ :=
  data.evalSymm_of_irreducible (phiIrreducible_of_splits_aux ℓ ζ hpos hζ data hsplit)
    (eval_swap_eq_zero_of_splits ℓ ζ data hsplit) hTmonic hTdeg

end Swap

end PhiGen

/-- The datum is symmetric as soon as its coefficients split into the conjugate
product and its transpose is monic of degree `ψ(ℓ)`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_PhiGen_evalSymm_of_splits.lean`. -/
theorem PhiGen.evalSymm_of_splits {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ)
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (data : ModularPolynomialData ℓ)
    (hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ))
    (hTmonic : ((swapBivar data.Φ).map evalAtJGen).Monic)
    (hTdeg : ((swapBivar data.Φ).map evalAtJGen).natDegree ≤ dedekindPsi ℓ) :
    EvalSymm data.Φ :=
  PhiGen.evalSymm_of_splits_aux ℓ ζ one_le_coeff_jq hζ data hsplit hTmonic hTdeg

/-! ## The converse: evaluated symmetry forces `swapBivar Φ = Φ` -/

section SepFibre

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The evaluated form of `Φ` in two variables of a commutative ring. -/
private def ev (Φ : Polynomial (Polynomial ℤ)) (x y : A) : A :=
  Φ.eval₂ (eval₂RingHom (Int.castRingHom A) x) y

private theorem aeval_toRingHom_eq [Algebra ℤ A] (x : A) :
    (Polynomial.aeval (R := ℤ) x).toRingHom = eval₂RingHom (Int.castRingHom A) x :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

private theorem ev_eq_evalEval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = (Φ.map (mapRingHom (Int.castRingHom A))).evalEval x y := by
  rw [ev, ← eval₂_eval₂RingHom_apply]

private theorem map_ev (φ : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    φ (ev Φ x y) = ev Φ (φ x) (φ y) := by
  rw [ev_eq_evalEval, ev_eq_evalEval, ← map_mapRingHom_evalEval φ, Polynomial.map_map,
    mapRingHom_comp,
    RingHom.ext_int (φ.comp (Int.castRingHom A)) (Int.castRingHom B)]

private theorem ev_eq_aevalAeval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = aevalAeval x y Φ := by
  have h : eval₂RingHom (eval₂RingHom (Int.castRingHom A) x) y
      = (aevalAeval (R := ℤ) x y).toRingHom := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_) ?_
    · simp
    · simp
  exact RingHom.congr_fun h Φ

private theorem ev_swap (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev (Bivariate.swap Φ) x y = ev Φ y x := by
  rw [ev_eq_aevalAeval, ev_eq_aevalAeval, Bivariate.aevalAeval_swap]

private theorem ev_int (Φ : Polynomial (Polynomial ℤ)) (a b : ℤ) : ev Φ a b = Φ.evalEval a b := by
  rw [ev_eq_evalEval]
  congr 1
  have h : mapRingHom (Int.castRingHom ℤ) = RingHom.id (Polynomial ℤ) := by
    rw [RingHom.ext_int (Int.castRingHom ℤ) (RingHom.id ℤ)]
    exact mapRingHom_id
  rw [h]
  exact Polynomial.map_id

private theorem ev_sub (Φ Ψ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev (Φ - Ψ) x y = ev Φ x y - ev Ψ x y := by
  rw [ev_eq_aevalAeval, map_sub, ← ev_eq_aevalAeval, ← ev_eq_aevalAeval]

end SepFibre

section SepFibreMain

private theorem swap_eq_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) :
    Bivariate.swap Φ = Φ := by
  set G : Polynomial (Polynomial ℤ) := Bivariate.swap Φ - Φ with hG

  have hL : ∀ x y : LaurentSeries ℚ, ev G x y = 0 := fun x y => by
    have hxy := h x y
    rw [aeval_toRingHom_eq, aeval_toRingHom_eq] at hxy
    rw [hG, ev_sub, ev_swap, sub_eq_zero]
    exact hxy.symm
  let ι : ℤ →+* LaurentSeries ℚ :=
    (algebraMap ℚ (LaurentSeries ℚ)).comp (Int.castRingHom ℚ)
  have hι : Function.Injective ι :=
    (algebraMap ℚ (LaurentSeries ℚ)).injective.comp Int.cast_injective
  have hZ : ∀ a b : ℤ, G.evalEval a b = 0 := fun a b =>
    hι (by rw [← ev_int, map_ev, hL, map_zero])

  have h1 : ∀ b : ℤ, G.eval (Polynomial.C b) = 0 := fun b =>
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun a : ℤ => a) (fun _ _ h => h) fun a => hZ a b)
  have h2 : G = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun b : ℤ => Polynomial.C b) (fun _ _ h => Polynomial.C_injective h) fun b => h1 b)
  exact sub_eq_zero.mp h2

private theorem swapBivar_eq_swap (Φ : Polynomial (Polynomial ℤ)) :
    swapBivar Φ = Bivariate.swap Φ := by
  have h : swapBivar = (Bivariate.swap (R := ℤ)).toAlgHom.toRingHom :=
    Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _)
      (by simp [Bivariate.swap_X])) (by simp [Bivariate.swap_Y])
  exact RingHom.congr_fun h Φ

end SepFibreMain

/-- Evaluated symmetry forces the transpose to be `Φ` itself. Verbatim from the
pin wrapper `Theorems/Thm_ModularCurve_swapBivar_eq_of_evalSymm.lean`. -/
theorem swapBivar_eq_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) :
    swapBivar Φ = Φ := by
  rw [swapBivar_eq_swap, swap_eq_of_evalSymm h]

end ModularCurve

end

#print axioms ModularCurve.evalAtJGen_injective
#print axioms ModularCurve.PhiGen.conj_injective
#print axioms ModularCurve.PhiGen.aeval_jq_ne_jqN
#print axioms ModularCurve.PhiGen.jqN_not_mem_adjoin_jq
#print axioms ModularCurve.aeval_jqN_toAdjoin
#print axioms ModularCurve.ModularPolynomialData.minpoly_jqN_eq
#print axioms ModularCurve.PhiGen.phiIrreducible_of_splits
#print axioms ModularCurve.evalSymm_of_swapBivar_eq
#print axioms ModularCurve.swapBivar_monic_of_coeff_bounds
#print axioms ModularCurve.ModularPolynomialData.evalSymm_of_irreducible
#print axioms ModularCurve.ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion
#print axioms ModularCurve.PhiGen.eval_swap_eq_zero_of_splits
#print axioms ModularCurve.PhiGen.evalSymm_of_splits
#print axioms ModularCurve.swapBivar_eq_of_evalSymm
