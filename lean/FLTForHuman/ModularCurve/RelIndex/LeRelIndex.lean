/-
The degeneracy-cover degree, norm side: `[A(Γ') : A(Γ)] ≤ [Γ : Γ']`.

For `Γ' ≤ Γ ≤ SL(2, ℤ)` with `T ∈ Γ'` and `Γ'.relIndex Γ ≠ 0`, and with `A(Δ)` the field
generated over `ℂ` by the ratios of `q`-expansions of modular forms on `Δ`, the relative
degree of `A(Γ') / A(Γ)` is bounded by the index of `Γ'` in `Γ`.

The proof is the norm argument.  Take the characteristic polynomial of
`c ↦ (c • g - f)` under the norm from `Γ'` to `Γ`, whose roots are the translates
`c * quotientFunc g q - quotientFunc f q` over the `Γ`-cosets `q` of `Γ'`; interpolate its
coefficients in the parameter `c` (`coeffForm`, a modular form on `Γ` of the top weight
`k * Nat.card`), and conclude by bounded degree, since every element of `A(Γ')` is a ratio
`qC f / qC g` and hence satisfies a polynomial over `A(Γ)` of degree at most the index.

Façade mode: one public declaration, the whole engine `private`.  The ground this module
stands on is frozen and is *not* re-proved here:

* `ModularCurve/Analytic/AnalyticAtCusp.lean` — the pin's `Nice` (`AnalyticAtCusp`) and its
  `qExpansion_{pow,sum}'` consequences, plus `analyticAtCusp_of_modularForm` for the pin's
  `nice_of_GG`/`nice_of_HH`;
* `ModularCurve/RelIndex/RatioField.lean` — `ratioSet`/`ratioField`, `mem_ratioSet`,
  `ratioSet_mono`, `qC_ne_zero_iff`, `qC_mul`, `mem_ratioSet_of_mem_adjoin`,
  `algebraMap_laurentSeries_eq_C`, `coe_finset_sum`, and `qC` itself
  (`ModularCurve.DiamondLift.qC`);
* `ModularCurve/RelIndex/LevelRaise.lean` — `one_mem_strictPeriods`.

The pin's whole `Ratio` section (`qC`, `ratioSet`, `restrictForm`, `ratioSet_mono`,
`qC_{mul,add,neg,const}`, `{mul,add,neg,inv}_mem_ratioSet`, `algebraMap_mem_ratioSet`,
`ratioField`, `mem_ratioSet_of_mem_adjoin`, `algebraMap_laurentSeries_eq_C`), its `Nice`
block and its `one_mem_strictPeriods` are therefore *not* transcribed, and the pin's
`coe_finset_sum` is the ground's; what is left here is the norm/characteristic-polynomial
engine, which is specific to this node.

References (public mirror, pinned `aa2d8b3`):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.lean>

spec-pin: Theorems/Thm_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.lean
spec-pin: P2M/Sol/S_ModularCurve_relrank_adjoin_qExpansion_div_le_relIndex.lean
-/
import FLTForHuman.ModularCurve.Analytic.AnalyticAtCusp
import FLTForHuman.ModularCurve.RelIndex.RatioField
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Perfect

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

open UpperHalfPlane ModularForm SlashInvariantForm Polynomial IntermediateField

namespace ModularCurve

open RelIndex

open DiamondLift (qC)

/-! ## The engine

Private: the node's public content is the headline at the bottom of the file. -/

namespace RelrankNormSol

/-! ## Setup: the two levels as subgroups of `GL(2, ℝ)`, and the coset space -/

private abbrev HH (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  (Γ : Subgroup (GL (Fin 2) ℝ))

private abbrev GG (Γ' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  (Γ' : Subgroup (GL (Fin 2) ℝ))

/-- The `Γ`-cosets of `Γ'`, i.e. `Γ' ⧸ (Γ' ⊓ Γ)`: the pin's `Cos`. -/
private abbrev Cos (Γ Γ' : Subgroup SL(2, ℤ)) : Type :=
  ↥(HH Γ) ⧸ (GG Γ').subgroupOf (HH Γ)

private theorem relIndex_GG_HH (Γ Γ' : Subgroup SL(2, ℤ)) :
    (GG Γ').relIndex (HH Γ) = Γ'.relIndex Γ :=
  Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective

private theorem natCard_cos (Γ Γ' : Subgroup SL(2, ℤ)) : Nat.card (Cos Γ Γ') = Γ'.relIndex Γ := by
  rw [← relIndex_GG_HH]
  rfl

private theorem isFiniteRelIndex (Γ Γ' : Subgroup SL(2, ℤ)) (hind : Γ'.relIndex Γ ≠ 0) :
    (GG Γ').IsFiniteRelIndex (HH Γ) :=
  Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr (by rwa [relIndex_GG_HH])

private instance (Γ Γ' : Subgroup SL(2, ℤ)) [(GG Γ').IsFiniteRelIndex (HH Γ)] :
    Fintype (Cos Γ Γ') := Fintype.ofFinite _

/-! ## The characteristic polynomial of `c ↦ c • g - f` under the norm -/

private theorem quotientFunc_smul_sub (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k)
    (c : ℂ) (q : Cos Γ Γ') :
    quotientFunc (c • g - f) q = c • quotientFunc g q - quotientFunc f q := by
  induction q using Quotient.inductionOn with
  | h r =>
    simp only [quotientFunc_mk]
    obtain ⟨γ, -, hγ⟩ := r.2
    have hr : (r.val)⁻¹ = ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by rw [← hγ, ← map_inv]; rfl
    rw [hr, ← ModularForm.SL_slash, ← ModularForm.SL_slash, ← ModularForm.SL_slash,
      FunLike.coe_sub, FunLike.coe_smul, sub_eq_add_neg, SlashAction.add_slash,
      SlashAction.neg_slash, ModularForm.SL_smul_slash, sub_eq_add_neg]

private theorem norm_smul_sub_apply (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k)
    (c : ℂ) (τ : ℍ) :
    (ModularForm.norm (HH Γ) (c • g - f)) τ =
      ∏ q : Cos Γ Γ', (c * quotientFunc g q τ - quotientFunc f q τ) := by
  have h := ModularForm.coe_norm (HH Γ) (c • g - f)
  rw [h, Finset.prod_apply]
  refine Fintype.prod_congr _ _ (fun q => ?_)
  rw [quotientFunc_smul_sub Γ f g]
  simp

private def charPolyAt (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k) (τ : ℍ) : ℂ[X] :=
  ∏ q : Cos Γ Γ', (C (quotientFunc g q τ) * X - C (quotientFunc f q τ))

private theorem eval_charPolyAt (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k)
    (c : ℂ) (τ : ℍ) :
    (charPolyAt Γ f g τ).eval c = (ModularForm.norm (HH Γ) (c • g - f)) τ := by
  rw [norm_smul_sub_apply, charPolyAt, eval_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  ring

private theorem natDegree_linear_le (a b : ℂ) : (C a * X - C b).natDegree ≤ 1 := by
  refine (natDegree_sub_le _ _).trans ?_
  refine max_le ?_ (by simp)
  exact (natDegree_C_mul_le _ _).trans (by simp)

private theorem card_cos (Γ Γ' : Subgroup SL(2, ℤ)) [(GG Γ').IsFiniteRelIndex (HH Γ)] :
    (Finset.univ : Finset (Cos Γ Γ')).card = Nat.card (Cos Γ Γ') := by
  rw [Nat.card_eq_fintype_card, Finset.card_univ]

private theorem natDegree_charPolyAt_le (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k) (τ : ℍ) :
    (charPolyAt Γ f g τ).natDegree ≤ Nat.card (Cos Γ Γ') := by
  rw [charPolyAt]
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum fun q _ => natDegree_linear_le
    (quotientFunc g q τ) (quotientFunc f q τ)).trans ?_
  rw [Finset.sum_const, smul_eq_mul, mul_one, card_cos]

private theorem coeff_charPolyAt_card (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k) (τ : ℍ) :
    (charPolyAt Γ f g τ).coeff (Nat.card (Cos Γ Γ')) = (ModularForm.norm (HH Γ) g) τ := by
  have hc : (Finset.univ : Finset (Cos Γ Γ')).card * 1 = Nat.card (Cos Γ Γ') := by
    rw [mul_one, card_cos]
  rw [charPolyAt]
  conv_lhs => rw [← hc, coeff_prod_of_natDegree_le (s := Finset.univ) (n := 1)
    (f := fun q : Cos Γ Γ' => C (quotientFunc g q τ) * X - C (quotientFunc f q τ))
    (h := fun q _ => natDegree_linear_le _ _)]
  rw [ModularForm.coe_norm, Finset.prod_apply]
  refine Fintype.prod_congr _ _ (fun q => ?_)
  simp

/-! ## Interpolating the coefficients -/

private def node (n : ℕ) (j : Fin (n + 1)) : ℂ := (j : ℕ)

private theorem node_injOn (n : ℕ) : Set.InjOn (node n) (Finset.univ : Finset (Fin (n + 1))) := by
  intro i _ j _ h
  simp only [node, Nat.cast_inj] at h
  exact Fin.ext h

private def lag (n : ℕ) (j : Fin (n + 1)) : ℂ[X] :=
  Lagrange.basis (Finset.univ : Finset (Fin (n + 1))) (node n) j

private theorem charPolyAt_eq_sum (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k) (τ : ℍ) :
    charPolyAt Γ f g τ = ∑ j : Fin (Nat.card (Cos Γ Γ') + 1),
      C ((ModularForm.norm (HH Γ) ((node _ j) • g - f)) τ) * lag (Nat.card (Cos Γ Γ')) j := by
  classical
  have hdeg : (charPolyAt Γ f g τ).degree <
      (Finset.univ : Finset (Fin (Nat.card (Cos Γ Γ') + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    exact_mod_cast Nat.lt_succ_of_le (natDegree_charPolyAt_le Γ f g τ)
  have h := Lagrange.eq_interpolate (f := charPolyAt Γ f g τ) (node_injOn (Nat.card (Cos Γ Γ')))
    hdeg
  rw [h, Lagrange.interpolate_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_charPolyAt]
  rfl

private def coeffForm (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k) (i : ℕ) :
    ModularForm (HH Γ) (k * Nat.card (Cos Γ Γ')) :=
  ∑ j : Fin (Nat.card (Cos Γ Γ') + 1),
    ((lag (Nat.card (Cos Γ Γ')) j).coeff i) •
      ModularForm.norm (HH Γ) ((node _ j) • g - f)

private theorem coeffForm_apply (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k)
    (i : ℕ) (τ : ℍ) : coeffForm Γ f g i τ = (charPolyAt Γ f g τ).coeff i := by
  rw [coeffForm, coe_finset_sum, Finset.sum_apply, charPolyAt_eq_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_apply, coeff_C_mul, smul_eq_mul, mul_comm]

private theorem coe_coeffForm_card (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k) :
    (coeffForm Γ f g (Nat.card (Cos Γ Γ')) : ℍ → ℂ) = ModularForm.norm (HH Γ) g := by
  funext τ
  rw [coeffForm_apply, coeff_charPolyAt_card]

/-! ## The homogenised identity -/

private theorem eval_homogenize_linear (a b x y : ℂ) :
    MvPolynomial.eval ![x, y] ((C a * X - C b).homogenize 1) = a * x - b * y := by
  rw [homogenize_sub, homogenize_C_mul, homogenize_X one_ne_zero, homogenize_C]
  simp

private theorem eval_homogenize_eq_sum (p : ℂ[X]) (n : ℕ) (x y : ℂ) :
    MvPolynomial.eval ![x, y] (p.homogenize n) =
      ∑ i ∈ Finset.range (n + 1), p.coeff i * x ^ i * y ^ (n - i) := by
  simp only [homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single, Finsupp.prod_add_index',
    Finsupp.prod_single_index, Finsupp.prod_single_index]
  · simp [mul_assoc]
  all_goals simp [pow_add]

private theorem sum_coeffForm_mul_pow_eq_zero (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k) (τ : ℍ) :
    ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      coeffForm Γ f g i τ * f τ ^ i * g τ ^ (Nat.card (Cos Γ Γ') - i) = 0 := by
  simp_rw [coeffForm_apply]
  rw [← eval_homogenize_eq_sum]
  have hcard : Nat.card (Cos Γ Γ') = ∑ _q ∈ (Finset.univ : Finset (Cos Γ Γ')), 1 := by
    simp [Nat.card_eq_fintype_card]
  rw [charPolyAt, hcard, homogenize_finsetProd (fun q _ => natDegree_linear_le _ _), map_prod]
  simp_rw [eval_homogenize_linear]
  refine Finset.prod_eq_zero (Finset.mem_univ (QuotientGroup.mk (1 : ↥(HH Γ)) : Cos Γ Γ')) ?_
  have h1 : ∀ (φ : ModularForm (GG Γ') k),
      quotientFunc φ (QuotientGroup.mk (1 : ↥(HH Γ)) : Cos Γ Γ') =
        (φ : ℍ → ℂ) ∣[k] ((1 : ↥(HH Γ)) : GL (Fin 2) ℝ)⁻¹ := fun φ => rfl
  rw [h1, h1]
  simp only [OneMemClass.coe_one, inv_one, SlashAction.slash_one]
  ring

/-! ## Analyticity at the cusp -/

private theorem nice_of_GG {Γ' : Subgroup SL(2, ℤ)} (hT' : ModularGroup.T ∈ Γ') {k' : ℤ}
    (h : ModularForm (GG Γ') k') : AnalyticAtCusp (h : ℍ → ℂ) :=
  analyticAtCusp_of_modularForm (one_mem_strictPeriods hT') h

private theorem nice_of_HH {Γ Γ' : Subgroup SL(2, ℤ)} (hT' : ModularGroup.T ∈ Γ')
    (hle : Γ' ≤ Γ) {k' : ℤ} (h : ModularForm (HH Γ) k') : AnalyticAtCusp (h : ℍ → ℂ) :=
  analyticAtCusp_of_modularForm (one_mem_strictPeriods (hle hT')) h

/-! ## The `q`-expansion identity and the non-vanishing of the top coefficient -/

private theorem sum_qExpansion_coeffForm_mul_pow_eq_zero (Γ : Subgroup SL(2, ℤ))
    {Γ' : Subgroup SL(2, ℤ)} [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ}
    (f g : ModularForm (GG Γ') k) (hT' : ModularGroup.T ∈ Γ') (hle : Γ' ≤ Γ) :
    ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      qExpansion 1 (coeffForm Γ f g i : ℍ → ℂ) * qExpansion 1 (f : ℍ → ℂ) ^ i *
        qExpansion 1 (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i) = 0 := by
  set R : ℍ → ℂ := ∑ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
    (coeffForm Γ f g i : ℍ → ℂ) * (f : ℍ → ℂ) ^ i * (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i)
    with hR
  have hR0 : R = 0 := by
    funext τ
    simp only [hR, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    exact sum_coeffForm_mul_pow_eq_zero Γ f g τ
  have hnice : ∀ i ∈ Finset.range (Nat.card (Cos Γ Γ') + 1),
      AnalyticAtCusp ((coeffForm Γ f g i : ℍ → ℂ) * (f : ℍ → ℂ) ^ i *
        (g : ℍ → ℂ) ^ (Nat.card (Cos Γ Γ') - i)) := fun i _ =>
    ((nice_of_HH hT' hle _).mul ((nice_of_GG hT' f).pow i)).mul
      ((nice_of_GG hT' g).pow _)
  have h := congrArg (qExpansion 1) hR0
  rw [qExpansion_zero, hR, qExpansion_sum' _ hnice] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qExpansion_mul ((nice_of_HH hT' hle _).mul ((nice_of_GG hT' f).pow i))
      ((nice_of_GG hT' g).pow _),
    qExpansion_mul (nice_of_HH hT' hle _) ((nice_of_GG hT' f).pow i),
    qExpansion_pow' (nice_of_GG hT' f), qExpansion_pow' (nice_of_GG hT' g)]

private theorem qExpansion_coeffForm_card_ne_zero (Γ : Subgroup SL(2, ℤ))
    {Γ' : Subgroup SL(2, ℤ)} [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ}
    (f g : ModularForm (GG Γ') k) (hT' : ModularGroup.T ∈ Γ') (hle : Γ' ≤ Γ)
    (hg : qExpansion 1 (g : ℍ → ℂ) ≠ 0) :
    qExpansion 1 (coeffForm Γ f g (Nat.card (Cos Γ Γ')) : ℍ → ℂ) ≠ 0 := by
  rw [coe_coeffForm_card]
  intro h
  rw [ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods (hle hT'))] at h
  refine ModularForm.norm_ne_zero (HH Γ) (f := g) ?_ h
  intro h0
  apply hg
  rw [h0, qExpansion_zero]

/-! ## Bounded degree: a polynomial over `A(Γ)` of degree at most the index -/

private theorem sum_div_pow_eq {K : Type*} [Field K] {n : ℕ} (a : ℕ → K) (F G : K) (hG : G ≠ 0)
    (h : ∑ i ∈ Finset.range (n + 1), a i * F ^ i * G ^ (n - i) = 0) :
    ∑ i ∈ Finset.range (n + 1), a i * (F / G) ^ i = 0 := by
  have key : (∑ i ∈ Finset.range (n + 1), a i * (F / G) ^ i) * G ^ n =
      ∑ i ∈ Finset.range (n + 1), a i * F ^ i * G ^ (n - i) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hG' : G ^ n = G ^ i * G ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
    rw [hG', div_pow]
    field_simp
  rw [h] at key
  rcases mul_eq_zero.mp key with h1 | h1
  · exact h1
  · exact absurd h1 (pow_ne_zero _ hG)

private theorem exists_polynomial (Γ : Subgroup SL(2, ℤ)) {Γ' : Subgroup SL(2, ℤ)}
    [(GG Γ').IsFiniteRelIndex (HH Γ)] {k : ℤ} (f g : ModularForm (GG Γ') k)
    (hT' : ModularGroup.T ∈ Γ') (hle : Γ' ≤ Γ) (hg : qExpansion 1 (g : ℍ → ℂ) ≠ 0) :
    ∃ p : (adjoin ℂ (ratioSet Γ))[X], p ≠ 0 ∧ p.natDegree ≤ Nat.card (Cos Γ Γ') ∧
      aeval (qC f / qC g) p = 0 := by
  classical
  set μ := Nat.card (Cos Γ Γ') with hμ
  set e : ℕ → ModularForm (HH Γ) (k * μ) := fun i => coeffForm Γ f g i with he
  have heμ : qExpansion 1 ((e μ) : ℍ → ℂ) ≠ 0 :=
    qExpansion_coeffForm_card_ne_zero Γ f g hT' hle hg
  have hqeμ : qC (e μ) ≠ 0 := qC_ne_zero_iff.mpr heμ
  have hmem : ∀ i, qC (e i) / qC (e μ) ∈ adjoin ℂ (ratioSet Γ) := fun i =>
    IntermediateField.subset_adjoin ℂ _ (mem_ratioSet (e i) (e μ) heμ)
  set c : ℕ → adjoin ℂ (ratioSet Γ) := fun i => ⟨qC (e i) / qC (e μ), hmem i⟩ with hc
  refine ⟨∑ i ∈ Finset.range (μ + 1), Polynomial.C (c i) * X ^ i, ?_, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun p : (adjoin ℂ (ratioSet Γ))[X] => p.coeff μ) h0
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at h1
    rw [Finset.sum_eq_single μ (fun j _ hj => ite_eq_right (Ne.symm hj))
      (fun h => absurd (Finset.mem_range.mpr (Nat.lt_succ_self μ)) h), ite_eq_left rfl] at h1
    have h2 := congrArg (fun z : adjoin ℂ (ratioSet Γ) => (z : LaurentSeries ℂ)) h1
    simp only [hc, ZeroMemClass.coe_zero] at h2
    exact absurd h2 (div_ne_zero hqeμ hqeμ)
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  · have hrel := sum_qExpansion_coeffForm_mul_pow_eq_zero Γ f g hT' hle
    have hrelC : ∑ i ∈ Finset.range (μ + 1), qC (e i) * qC f ^ i * qC g ^ (μ - i) = 0 := by
      have := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hrel
      simpa only [qC, map_sum, map_mul, map_pow, map_zero] using this
    have hqg : qC g ≠ 0 := qC_ne_zero_iff.mpr hg
    have hdiv := sum_div_pow_eq (fun i => qC (e i)) (qC f) (qC g) hqg hrelC
    rw [map_sum]
    have : ∑ i ∈ Finset.range (μ + 1), aeval (qC f / qC g) (Polynomial.C (c i) * X ^ i) =
        (qC (e μ))⁻¹ * ∑ i ∈ Finset.range (μ + 1), qC (e i) * (qC f / qC g) ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, aeval_C, aeval_X]
      change (qC (e i) / qC (e μ)) * _ = _
      ring
    rw [this, hdiv, mul_zero]

/-! ## The rank bound -/

private theorem finiteDimensional_of_forall_aeval_eq_zero {K V : Type*} [Field K] [Field V]
    [Algebra K V] [PerfectField K] (D : ℕ)
    (h : ∀ y : V, ∃ p : K[X], p ≠ 0 ∧ p.natDegree ≤ D ∧ aeval y p = 0) :
    FiniteDimensional K V := by
  have halg : Algebra.IsAlgebraic K V := ⟨fun y => by
    obtain ⟨p, hp0, -, hpy⟩ := h y
    exact ⟨p, hp0, hpy⟩⟩
  have hsep : Algebra.IsSeparable K V := Algebra.IsAlgebraic.isSeparable_of_perfectField
  by_contra hinf
  obtain ⟨L, hLfd, hlt⟩ := IntermediateField.exists_lt_finrank_of_infinite_dimensional hinf D
  have hLfdI : FiniteDimensional K L := hLfd
  have hsepL : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L V
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hdeg : (minpoly K α).natDegree = Module.finrank K L :=
    (Field.primitive_element_iff_minpoly_natDegree_eq K α).mp hα
  obtain ⟨p, hp0, hpD, hpy⟩ := h (α : V)
  have hmin : minpoly K α = minpoly K (α : V) := IntermediateField.minpoly_eq α
  have hle : (minpoly K (α : V)).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd (minpoly.dvd K _ hpy) hp0
  have : Module.finrank K L ≤ D := by
    rw [← hdeg, hmin]
    exact hle.trans hpD
  exact absurd hlt (not_lt.mpr this)

private theorem rank_le_of_forall_aeval_eq_zero {K V : Type*} [Field K] [Field V] [Algebra K V]
    [PerfectField K] (D : ℕ)
    (h : ∀ y : V, ∃ p : K[X], p ≠ 0 ∧ p.natDegree ≤ D ∧ aeval y p = 0) :
    Module.rank K V ≤ D := by
  have hfd : FiniteDimensional K V := finiteDimensional_of_forall_aeval_eq_zero D h
  have halg : Algebra.IsAlgebraic K V := ⟨fun y => by
    obtain ⟨p, hp0, -, hpy⟩ := h y
    exact ⟨p, hp0, hpy⟩⟩
  have hsep : Algebra.IsSeparable K V := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K V
  have hdeg : (minpoly K α).natDegree = Module.finrank K V :=
    (Field.primitive_element_iff_minpoly_natDegree_eq K α).mp hα
  obtain ⟨p, hp0, hpD, hpy⟩ := h α
  have hfin : Module.finrank K V ≤ D := by
    rw [← hdeg]
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd K _ hpy) hp0).trans hpD
  rw [← Module.finrank_eq_rank]
  exact_mod_cast hfin

end RelrankNormSol

open RelrankNormSol in
theorem relrank_adjoin_qExpansion_div_le_relIndex
    (Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hle : Γ' ≤ Γ)
    (hT : ModularGroup.T ∈ Γ') (hind : Γ'.relIndex Γ ≠ 0) :
    IntermediateField.relrank
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)}) ≤
      (Γ'.relIndex Γ : Cardinal) := by
  change relrank (adjoin ℂ (ratioSet Γ)) (adjoin ℂ (ratioSet Γ')) ≤ _
  have hfind : (GG Γ').IsFiniteRelIndex (HH Γ) := isFiniteRelIndex Γ Γ' hind
  have hKK' : adjoin ℂ (ratioSet Γ) ≤ adjoin ℂ (ratioSet Γ') :=
    adjoin.mono ℂ _ _ (ratioSet_mono hle)
  rw [relrank_eq_rank_of_le hKK']
  set K := adjoin ℂ (ratioSet Γ) with hK
  set V := extendScalars hKK' with hV
  have h := rank_le_of_forall_aeval_eq_zero (K := K) (V := V) (Nat.card (Cos Γ Γ')) (fun y => by
    have hy : (y : LaurentSeries ℂ) ∈ adjoin ℂ (ratioSet Γ') := y.2
    obtain ⟨k, f, g, hg, hyfg⟩ := mem_ratioSet_of_mem_adjoin hT hy
    obtain ⟨p, hp0, hpD, hpy⟩ := exists_polynomial Γ f g hT hle hg
    refine ⟨p, hp0, hpD, ?_⟩
    have h1 : Polynomial.aeval (y : LaurentSeries ℂ) p = 0 := by
      rw [hyfg]; exact hpy
    have h2 := Polynomial.aeval_algHom_apply V.val y p
    change Polynomial.aeval (y : LaurentSeries ℂ) p = V.val (Polynomial.aeval y p) at h2
    rw [h1] at h2
    exact (map_eq_zero_iff _ (RingHom.injective (V.val : V →+* LaurentSeries ℂ))).mp h2.symm)
  rwa [natCard_cos] at h

end ModularCurve
