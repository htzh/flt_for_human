/-
  T11 — piece (d): assembling the modular-polynomial datum.

  With a descended family `c` in hand (`PhiGenDescends`, produced by
  `PhiGenDescendsStructure`'s interface and `PhiGen.exists_phiGenDescends`), the
  passage from a family of series to a genuine `ModularPolynomialData ℓ` is three
  steps, each an input already landed:

  1. `hmem : ∀ k, c k ∈ ℚ[jq]` (T8) gives `P k ∈ ℚ[X]` with `c k = P k (jq)`;
  2. `PhiGenDescends.poleOrderLE` bounds `deg (P k) ≤ ℓ + 1`;
  3. `hint : ∀ k, IntCoeffs (c k)` plus T9's `aeval_jq_intCoeffs_descent` forces
     `P k ∈ ℤ[X]` — this is `PhiGenDescends.exists_intPoly`.

  Then `Φ = ∑_{k ≤ ℓ+1} Q k (X) * Y^k` is the datum: `c_top` makes it monic,
  `c_eq_zero`/`hΦdeg` give degree `ℓ + 1 = ψ(ℓ)`, and
  `sum_mul_jqN_pow_eq_zero` is the vanishing at `j(q ^ ℓ)`. The same file carries
  the coefficient comparison `splits_of_coeff_evalAtJ_eq`, which turns the datum
  back into the conjugate product and is consumed by (e)/(f).

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean` (191
  lines). `splits_of_coeff_evalAtJ_eq` is public there; the assembly is `private`
  and exposed through its wrapper. Both port statements are the wrappers verbatim.

  ## Reuse

  The pin's private `coeff_aeval_jq_neg` is T9's public `Defs/Jq.lean` lemma, and
  the pin's private `evalAtJ_eq_aeval_map` is the public `Defs/Jq.lean` bridge
  (promoted by T12); both are imported rather than re-declared.

  ## Assumptions

  `evalAtJ`, `jq`, `jqN`, `coeff_aeval_jq_neg`, `dedekindPsi_prime` are the port's
  `Defs/Jq`; `PoleOrderLE`, `IntCoeffs`, `PhiGenDescends`, `conj`, `phiProd`,
  `ModularPolynomialData` the port's `Defs/PhiGen`/`Defs/Polynomial`;
  `aeval_jq_intCoeffs_descent` and `PhiGenDescends.intCoeffs` T9's
  `PhiGenIntegrality`; the five `PhiGenDescends.*`/`evalAtJ_injective` exports
  this topic's `PhiGenDescendsStructure`.
-/
import FLTForHuman.ModularCurve.PhiGenDescendsStructure
import FLTForHuman.ModularCurve.PhiGenIntegrality
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ModularCurve
namespace PhiGen

/-- A polynomial in `jq` of pole order `≤ n` has degree `≤ n`: the `q ^ (-d)`
coefficient of `P(jq)` is `P`'s top coefficient (`coeff_aeval_jq_neg`). -/
private theorem natDegree_le_of_poleOrderLE_aeval (P : Polynomial ℚ) {n : ℕ}
    (hn : PoleOrderLE (Polynomial.aeval jq P) n) : P.natDegree ≤ n := by
  by_contra h
  push Not at h
  have hP : P ≠ 0 := by
    rintro rfl
    simp at h
  have h0 := hn (-(P.natDegree : ℤ)) (by omega)
  rw [coeff_aeval_jq_neg P le_rfl] at h0
  exact (Polynomial.leadingCoeff_ne_zero.mpr hP) h0

/-- A series in `ℚ[jq]` of pole order `≤ n` is `P(jq)` for a `P` of degree
`≤ n`. -/
private theorem exists_aeval_jq_eq_of_mem_adjoin {f : LaurentSeries ℚ}
    (hf : f ∈ Algebra.adjoin ℚ {jq}) {n : ℕ}
    (hn : PoleOrderLE f n) : ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ f = Polynomial.aeval jq P := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hf
  obtain ⟨P, rfl⟩ := hf
  exact ⟨P, natDegree_le_of_poleOrderLE_aeval P hn, rfl⟩

section Exits

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}
variable {c : ℕ → LaurentSeries ℚ}

/-- The integer polynomial `Q` with `evalAtJ Q = c k`, of degree `≤ ℓ + 1`. -/
private theorem PhiGenDescends.exists_intPoly (hc : PhiGenDescends ℓ ζ c)
    (hint : ∀ k, IntCoeffs (c k)) (hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq}) (k : ℕ) :
    ∃ Q : Polynomial ℤ, Q.natDegree ≤ ℓ + 1 ∧ evalAtJ Q = c k := by

  obtain ⟨P, hPdeg, hP⟩ := exists_aeval_jq_eq_of_mem_adjoin (hmem k) (hc.poleOrderLE k)

  have hPint : ∀ n : ℕ, ∃ z : ℤ, P.coeff n = (z : ℚ) :=
    aeval_jq_intCoeffs_descent P (by rw [← hP]; exact hint k)

  have hlift : P ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨z, hz⟩ := hPint n
    exact ⟨z, by rw [eq_intCast]; exact hz.symm⟩
  obtain ⟨Q, hQ⟩ := hlift
  have hQmap : Q.map (Int.castRingHom ℚ) = P := hQ
  refine ⟨Q, ?_, ?_⟩
  · rw [← Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℚ)
      Int.cast_injective Q, hQmap]
    exact hPdeg
  · rw [evalAtJ_eq_aeval_map, hQmap, hP]

end Exits

/-- A datum whose coefficients evaluate to the descended family maps to the
conjugate product under `coeffEmb K ∘ qExpand ℚ ℓ ∘ evalAtJ`. Consumed by (e) and
(f). Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.lean`. -/
theorem splits_of_coeff_evalAtJ_eq {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ)
    (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) :
    data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) := by
  refine Polynomial.ext fun k => ?_
  rw [Polynomial.coeff_map, RingHom.comp_apply, RingHom.comp_apply, hcoeff k, hc k]

section StrongExistence

/-- The `m`-th coefficient of `∑_{k < n} C (Q k) * X ^ k` is `Q m` for `m < n`. -/
private theorem coeff_sum_C_mul_X_pow (Q : ℕ → Polynomial ℤ) (n m : ℕ) (hm : m < n) :
    (∑ k ∈ Finset.range n, Polynomial.C (Q k) * Polynomial.X ^ k).coeff m = Q m := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_left rfl, mul_one]
  · intro k _ hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right (Ne.symm hk), mul_zero]
  · intro hm'
    exact absurd (Finset.mem_range.mpr hm) hm'

end StrongExistence

/-- The assembled datum: `Φ = ∑_{k ≤ ℓ+1} Q k (X) Y^k`, monic of degree `ℓ+1` and
vanishing at `j(q^ℓ)`, with `evalAtJ (Φ.coeff k) = c k`. Verbatim from the pin
wrapper `Theorems/Thm_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq.lean`. -/
theorem exists_modularPolynomialData_coeff_eq {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (hint : ∀ k, IntCoeffs (c k))
    (hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq}) :
    ∃ data : ModularPolynomialData ℓ, ∀ k, evalAtJ (data.Φ.coeff k) = c k := by

  choose Q hQdeg hQeval using hc.exists_intPoly hint hmem

  have hQtop : Q (ℓ + 1) = 1 := by
    refine evalAtJ_injective ?_
    rw [hQeval (ℓ + 1), hc.c_top, map_one]

  set Φ : Polynomial (Polynomial ℤ) :=
    ∑ k ∈ Finset.range (ℓ + 2), Polynomial.C (Q k) * Polynomial.X ^ k with hΦ

  have hΦtop : Φ.coeff (ℓ + 1) = 1 := by
    rw [hΦ, coeff_sum_C_mul_X_pow Q (ℓ + 2) (ℓ + 1) (by omega), hQtop]

  have hΦdeg_le : Φ.natDegree ≤ ℓ + 1 := by
    rw [hΦ]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_X_pow]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hΦdeg : Φ.natDegree = ℓ + 1 :=
    le_antisymm hΦdeg_le
      (Polynomial.le_natDegree_of_ne_zero (by rw [hΦtop]; exact one_ne_zero))

  have hΦcoeff : ∀ k, evalAtJ (Φ.coeff k) = c k := by
    intro k
    by_cases hk : k < ℓ + 2
    · rw [hΦ, coeff_sum_C_mul_X_pow Q (ℓ + 2) k hk, hQeval k]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Φ.natDegree < k), map_zero,
        hc.c_eq_zero (by omega : ℓ + 1 < k)]

  refine ⟨⟨Φ, ?_, ?_, ?_⟩, hΦcoeff⟩
  ·
    show Φ.coeff Φ.natDegree = 1
    rw [hΦdeg]
    exact hΦtop
  ·
    rw [hΦdeg, dedekindPsi_prime hℓ.out]
  ·
    rw [Polynomial.eval₂_eq_sum_range' evalAtJ (n := ℓ + 2) (by rw [hΦdeg]; omega) (jqN ℓ)]
    have hterm : ∀ k ∈ Finset.range (ℓ + 2),
        evalAtJ (Φ.coeff k) * (jqN ℓ) ^ k = c k * (jqN ℓ) ^ k := by
      intro k _
      rw [hΦcoeff k]
    rw [Finset.sum_congr rfl hterm]
    exact hc.sum_mul_jqN_pow_eq_zero

end PhiGen
end ModularCurve

end

#print axioms ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq
#print axioms ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq
