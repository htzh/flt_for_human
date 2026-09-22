/-
  T10 — the pole bounds, the second half of the cone's (b).

  The candidate product `phiProd ℓ (conj ℓ ζ)` is `∏_i (Y - j(ζ ^ b q ^ a))`. Its
  degree-`0` coefficient has a pole of order exactly `ℓ * ℓ + ℓ` at `q = 0`, with
  residue `1` (`phiProd_conj_coeff_zero_lead`), and every non-constant
  coefficient is bounded by the same order (`phiProd_conj_coeff_eq_zero_of_le`).
  Together with T9's integrality (`FLTForHuman/ModularCurve/PhiGenIntegrality.lean`,
  the first half of (b)) this makes the descended family `c` a degree-`(ℓ + 1)`
  integer datum of pole order `≤ ℓ + 1` — what (d) assembles.

  ## The shared prelude

  The `TPoleOrderLE` closure this module consumes (`.mono`, `.zero`, `.one`,
  `.neg`, `.add`, `.mul`, `.qTwist`, `.qExpand`, `of_jSimplePole`, the conjugate
  bounds and the coefficient bounds) is **not** written here: it is public in
  `Defs/PhiGen.lean`, because the pin copies it into six files and T11's 328 block
  imports it too. This module is the distinctive part only: the leading-coefficient
  computation of the product and the sharp pole bound for `k ≠ 0`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean` (391
  lines; its twin `…_phiProd_conj_coeff_zero_lead.lean` is a byte-equivalent copy
  with the exported name flipped). The two public statements are verbatim from
  their `Theorems/` wrappers. The pin's ~180-line `TPoleOrderLE` prelude is not
  ported here (see above).

  ## Assumptions

  `LaurentSeries`, `HahnSeries`, `Polynomial`, `Finset`/`Fin` are mathlib's;
  `TPoleOrderLE`, `JSimplePole`, `phiProd`, `conj`, `conj_zero`, `conj_succ`,
  `jSimplePole_jqK` and the coefficient/order lemmas are the port's
  `Defs/PhiGen`; `qExpand`, `coeffEmb`, `qTwist` are the port's
  `Defs/Laurent`/`Defs/Twist`; `jq`, `coeff_jq_neg_one` the port's `Defs/Jq`.
-/
import FLTForHuman.ModularCurve.Defs.PhiGen
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Complex.Basic

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve
namespace PhiGen

/-! ## The leading coefficient of the product -/

/-- The `q ^ (-1)` coefficient of `coeffEmb K jq` is `1`. -/
private theorem coeff_coeffEmb_jq_neg_one {K : Type*} [Field K] [Algebra ℚ K] :
    (coeffEmb K jq).coeff (-1 : ℤ) = 1 := by
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]

/-- The pin's `phiProd_def`, restated here because the pin keeps it `private` in
the shared prelude and this module's proofs unfold `phiProd` through it. -/
private theorem phiProd_def {K : Type*} [Field K] (ℓ : ℕ)
    (conj : Fin (ℓ + 1) → LaurentSeries K) :
    phiProd ℓ conj = ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conj i)) := rfl

private theorem tPoleOrderLE_prod {K : Type*} [Field K] {ι : Type*} (s : Finset ι)
    (f : ι → LaurentSeries K) (n : ι → ℕ) (hf : ∀ i ∈ s, TPoleOrderLE (f i) (n i)) :
    TPoleOrderLE (∏ i ∈ s, f i) (∑ i ∈ s, n i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using tPoleOrderLE_one
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact (hf a (Finset.mem_cons_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_cons_of_mem hi))

private theorem coeff_mul_lead {K : Type*} [Field K] {f g : LaurentSeries K} {m n : ℕ}
    (hf : TPoleOrderLE f m) (hg : TPoleOrderLE g n) :
    (f * g).coeff (-((m + n : ℕ) : ℤ)) = f.coeff (-(m : ℤ)) * g.coeff (-(n : ℤ)) := by
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_single ((-(m : ℤ), -(n : ℤ))) ?_ ?_
  · rintro ⟨i, j⟩ hij hne
    obtain ⟨hi, hj, hsum⟩ := Finset.mem_antidiagonal.mp hij
    rw [HahnSeries.mem_support] at hi hj

    have him : ¬ i < -(m : ℤ) := fun h => hi (hf i h)
    have hjn : ¬ j < -(n : ℤ) := fun h => hj (hg j h)
    push_cast at hsum
    have hi' : i = -(m : ℤ) := by omega
    have hj' : j = -(n : ℤ) := by omega
    exact absurd (by rw [hi', hj']) hne
  · intro hni

    by_contra hne
    refine hni (Finset.mem_antidiagonal.mpr ⟨?_, ?_, by push_cast; ring⟩) <;>
      rw [HahnSeries.mem_support]
    · exact fun h0 => hne (by rw [h0, zero_mul])
    · exact fun h0 => hne (by rw [h0, mul_zero])

private theorem coeff_prod_lead {K : Type*} [Field K] {ι : Type*} (s : Finset ι)
    (f : ι → LaurentSeries K) (n : ι → ℕ) (hf : ∀ i ∈ s, TPoleOrderLE (f i) (n i)) :
    (∏ i ∈ s, f i).coeff (-((∑ i ∈ s, n i : ℕ) : ℤ)) =
      ∏ i ∈ s, (f i).coeff (-(n i : ℤ)) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons, Finset.prod_cons,
      coeff_mul_lead (hf a (Finset.mem_cons_self a s))
        (tPoleOrderLE_prod s f n fun i hi => hf i (Finset.mem_cons_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_cons_of_mem hi)]

/-- The product of the powers of a primitive `ℓ`-th root: the pin's *product*
fact. Mathlib has the *sum* fact (`IsPrimitiveRoot.geom_sum_eq_zero`); this is a
different statement, so the pin's case split on `ℓ = 2` versus `ℓ` odd is ported
whole. -/
private theorem pow_sum_range_isPrimitiveRoot {K : Type*} [Field K] {ℓ : ℕ}
    (hℓ : Nat.Prime ℓ) {z : K} (hz : IsPrimitiveRoot z ℓ) :
    z ^ (∑ i ∈ Finset.range ℓ, i) = (-1) ^ (ℓ + 1) := by
  rcases hℓ.eq_two_or_odd' with rfl | hodd
  ·
    rw [hz.eq_neg_one_of_two_right]
    norm_num [Finset.sum_range_succ]
  ·

    obtain ⟨m, hm⟩ := hodd
    have hsum : ∑ i ∈ Finset.range ℓ, i = ℓ * m := by
      have h2 := Finset.sum_range_id_mul_two ℓ
      have hℓ1 : ℓ - 1 = 2 * m := by omega
      rw [hℓ1, show ℓ * (2 * m) = ℓ * m * 2 by ring] at h2
      omega
    rw [hsum, pow_mul, hz.pow_eq_one, one_pow]
    exact (Even.neg_one_pow ⟨m + 1, by omega⟩).symm

private theorem prod_inv_pow_isPrimitiveRoot {K : Type*} [Field K] {ℓ : ℕ}
    (hℓ : Nat.Prime ℓ) {z : K} (hz : IsPrimitiveRoot z ℓ) :
    ∏ b : Fin ℓ, ((z ^ (b : ℕ))⁻¹ : K) = (-1) ^ (ℓ + 1) := by
  have hsum : (∑ b : Fin ℓ, (b : ℕ)) = ∑ i ∈ Finset.range ℓ, i :=
    Fin.sum_univ_eq_sum_range (fun i => i) ℓ
  rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, hsum,
    pow_sum_range_isPrimitiveRoot hℓ hz, ← inv_pow, inv_neg, inv_one]

private theorem phiProd_coeff_zero_eq_prod_neg {K : Type*} [Field K] {ℓ : ℕ}
    {conj : Fin (ℓ + 1) → LaurentSeries K} :
    (phiProd ℓ conj).coeff 0 = ∏ i : Fin (ℓ + 1), (-(conj i)) := by
  rw [phiProd_def, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]

private theorem conj_zero_coeff_lead {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J) (hJlead : J.coeff (-1 : ℤ) = 1) :
    (conj 0).coeff (-((ℓ * ℓ : ℕ) : ℤ)) = 1 := by
  rw [hconj0, show (-((ℓ * ℓ : ℕ) : ℤ)) = ((ℓ * ℓ : ℕ) : ℤ) * (-1 : ℤ) by ring,
    qExpand_coeff_mul, hJlead]

private theorem conj_succ_coeff_lead {K : Type*} [Field K] {ℓ : ℕ} {ζ : Kˣ}
    {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconjS : ∀ b : Fin ℓ, conj b.succ = qTwist (ζ ^ (b : ℕ)) J)
    (hJlead : J.coeff (-1 : ℤ) = 1) (b : Fin ℓ) :
    (conj b.succ).coeff (-(1 : ℤ)) = (((ζ : K) ^ (b : ℕ))⁻¹ : K) := by
  rw [hconjS b, qTwist_coeff, hJlead, mul_one, zpow_neg_one, ← Units.val_pow_eq_pow_val,
    ← Units.val_inv_eq_inv_val]

private theorem phiProd_coeff_zero_lead {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {ζ : Kˣ} {J : LaurentSeries K} {conj : Fin (ℓ + 1) → LaurentSeries K}
    (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = qTwist (ζ ^ (b : ℕ)) J)
    (hJ : JSimplePole J) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hJlead : J.coeff (-1 : ℤ) = 1) :
    ((phiProd ℓ conj).coeff 0).coeff (-((ℓ * ℓ + ℓ : ℕ) : ℤ)) = 1 := by

  rw [phiProd_coeff_zero_eq_prod_neg, ← sum_conjPoleBound ℓ,
    coeff_prod_lead Finset.univ _ (conjPoleBound ℓ)
      (fun i _ => (tPoleOrderLE_conj hconj0 hconjS hJ i).neg),
    Fin.prod_univ_succ]

  have h0 : (-(conj 0)).coeff (-((conjPoleBound ℓ 0 : ℕ) : ℤ)) = -1 := by
    rw [HahnSeries.coeff_neg, conjPoleBound_zero, conj_zero_coeff_lead hconj0 hJlead]
  have hS : ∀ b : Fin ℓ, (-(conj b.succ)).coeff (-((conjPoleBound ℓ b.succ : ℕ) : ℤ)) =
      -((((ζ : K) ^ (b : ℕ))⁻¹ : K)) := by
    intro b
    rw [HahnSeries.coeff_neg, conjPoleBound_succ, Nat.cast_one,
      conj_succ_coeff_lead hconjS hJlead b]
  rw [h0]
  simp only [hS]

  rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin,
    prod_inv_pow_isPrimitiveRoot hℓ.out hζ, ← pow_add, ← pow_succ']
  exact Even.neg_one_pow ⟨ℓ + 1, by ring⟩

/-! ## The sharp bound for the non-constant coefficients -/

private theorem tPoleOrderLE_coeff_prod_X_sub_C_card {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (a : ι → LaurentSeries K) (ha : ∀ i ∈ s, TPoleOrderLE (a i) 1) :
    ∀ k : ℕ, TPoleOrderLE ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff k)
      (s.card - k) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using tPoleOrderLE_one
    · rw [Finset.prod_empty, Polynomial.coeff_one, ite_eq_right (by omega)]
      exact tPoleOrderLE_zero _
  | cons a₀ s ha₀ ih =>
    intro k
    have hmem : ∀ i ∈ s, TPoleOrderLE (a i) 1 :=
      fun i hi => ha i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, Finset.card_cons]
    match k with
    | 0 =>

      rw [Polynomial.mul_coeff_zero]
      exact ((tPoleOrderLE_coeff_X_sub_C (ha a₀ (Finset.mem_cons_self a₀ s)) 0).mul
        (ih hmem 0)).mono (by omega)
    | (k + 1) =>

      rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
        sub_eq_add_neg]
      refine TPoleOrderLE.add ?_ (TPoleOrderLE.neg ?_)
      ·
        exact (ih hmem k).mono (by omega)
      ·

        by_cases hks : k + 1 ≤ s.card
        · exact ((ha a₀ (Finset.mem_cons_self a₀ s)).mul (ih hmem (k + 1))).mono
            (by omega)
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
          · exact tPoleOrderLE_zero _
          · rw [Polynomial.natDegree_prod_of_monic _ _
              (fun i _ => Polynomial.monic_X_sub_C (a i))]
            simp only [Polynomial.natDegree_X_sub_C, ← Finset.card_eq_sum_ones]
            omega

private theorem tPoleOrderLE_phiProd_coeff_of_ne_zero {K : Type*} [Field K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {J : LaurentSeries K}
    {conj : Fin (ℓ + 1) → LaurentSeries K} (hconj0 : conj 0 = qExpand K (ℓ * ℓ) J)
    (hconjS : ∀ b : Fin ℓ, conj b.succ = qTwist (ζ ^ (b : ℕ)) J)
    (hJ : JSimplePole J) (k : ℕ) (hk : k ≠ 0) :
    TPoleOrderLE ((phiProd ℓ conj).coeff k) (ℓ * ℓ + ℓ - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  have hsq : 4 ≤ ℓ * ℓ := Nat.mul_le_mul hℓ2 hℓ2

  rw [phiProd_def, Fin.prod_univ_succ, sub_mul, Polynomial.coeff_sub,
    Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, sub_eq_add_neg]

  have hR : ∀ j : ℕ, TPoleOrderLE
      ((∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (conj b.succ))).coeff j)
      (Finset.univ.card - j) :=
    tPoleOrderLE_coeff_prod_X_sub_C_card Finset.univ _
      (fun b _ => tPoleOrderLE_conj_succ hconjS hJ b)
  rw [Finset.card_univ, Fintype.card_fin] at hR
  refine TPoleOrderLE.add ?_ (TPoleOrderLE.neg ?_)
  ·
    exact (hR k).mono (by omega)
  ·
    exact ((tPoleOrderLE_conj_zero hconj0 hJ).mul (hR (k + 1))).mono (by omega)

/-! ## The two exported statements -/

/-- The leading coefficient of the constant term of `phiProd`: the pole of the
degree-`0` coefficient is exactly `q ^ (-(ℓ * ℓ + ℓ))`, with residue `1`.
Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead.lean`. -/
theorem phiProd_conj_coeff_zero_lead {K : Type*} [Field K] [Algebra ℚ K]
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    ((phiProd ℓ (conj ℓ ζ)).coeff 0).coeff (-((ℓ * ℓ + ℓ : ℕ) : ℤ)) = 1 :=
  phiProd_coeff_zero_lead (conj_zero ℓ ζ) (conj_succ ℓ ζ)
    (jSimplePole_jqK (K := K)) hζ (coeff_coeffEmb_jq_neg_one (K := K))

private theorem tPoleOrderLE_phiProd_conj_of_ne_zero {K : Type*} [Field K] [Algebra ℚ K]
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) :
    TPoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ - 1) :=
  tPoleOrderLE_phiProd_coeff_of_ne_zero (conj_zero ℓ ζ) (conj_succ ℓ ζ)
    (jSimplePole_jqK (K := K)) k hk

/-- Every non-constant coefficient of `phiProd` has pole order at most
`ℓ * ℓ + ℓ`, so its coefficients below `q ^ (-(ℓ * ℓ + ℓ))` vanish. Verbatim from
the pin wrapper
`Theorems/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean`. -/
theorem phiProd_conj_coeff_eq_zero_of_le {K : Type*} [Field K] [Algebra ℚ K]
    (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) (m : ℕ)
    (hm : ℓ * ℓ + ℓ ≤ m) : ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff (-(m : ℤ)) = 0 := by
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  exact tPoleOrderLE_phiProd_conj_of_ne_zero ℓ ζ k hk (-(m : ℤ)) (by omega)

/-! ## The wire test

Both statements take `hζ : IsPrimitiveRoot (ζ : K) ℓ` over an arbitrary field, so
they are instantiable: take `K = ℂ`, `ℓ = 2`, `ζ = -1`
(`IsPrimitiveRoot.neg_one`). The leading coefficient is `1` and the coefficient of
`q ^ (-6)` of `(phiProd …).coeff 1` vanishes. The module's public surface stays at
exactly the two wrappers; the instances are `private` but named. -/

private theorem wire_zero_lead :
    ((phiProd 2 (conj 2 (-1 : ℂˣ))).coeff 0).coeff (-((2 * 2 + 2 : ℕ) : ℤ)) = 1 :=
  phiProd_conj_coeff_zero_lead (K := ℂ) (ℓ := 2) (hℓ := ⟨Nat.prime_two⟩) (-1)
    (by simpa using IsPrimitiveRoot.neg_one (R := ℂ) 0 (by norm_num))

private theorem wire_eq_zero_of_le :
    ((phiProd 2 (conj 2 (-1 : ℂˣ))).coeff 1).coeff (-(6 : ℤ)) = 0 :=
  phiProd_conj_coeff_eq_zero_of_le (K := ℂ) (ℓ := 2) (hℓ := ⟨Nat.prime_two⟩) (-1) 1
    (by norm_num) 6 (by norm_num)

end PhiGen
end ModularCurve

end

#print axioms ModularCurve.PhiGen.phiProd_conj_coeff_zero_lead
#print axioms ModularCurve.PhiGen.phiProd_conj_coeff_eq_zero_of_le
