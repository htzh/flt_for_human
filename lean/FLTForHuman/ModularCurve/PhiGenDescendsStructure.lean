/-
  T11 — the 328 block: the shape of a descended family.

  `PhiGenDescends ℓ ζ c` says the `X`-coefficients of the conjugate product
  `phiProd ℓ (conj ℓ ζ)` descend to series `c k ∈ ℚ((q))` along the level
  substitution `q ↦ q ^ ℓ`. This module reads the *shape* of `c` off the product,
  using only that the product is monic of degree `ℓ + 1` and T10's pole bound:

  * `PhiGenDescends.c_top` — `c (ℓ + 1) = 1` (the top coefficient);
  * `PhiGenDescends.c_eq_zero` — `c k = 0` above degree `ℓ + 1`;
  * `PhiGenDescends.poleOrderLE` — every `c k` has pole order `≤ ℓ + 1`;
  * `PhiGenDescends.sum_mul_jqN_pow_eq_zero` — the modular-equation relation
    `∑_{k ≤ ℓ+1} c k * j(q^ℓ)^k = 0`;
  * `evalAtJ_injective` — `P ↦ P(j(q))` from `ℤ[X]` to `ℚ((q))` is injective.

  The last is stated over `ℤ` but is really the triangularity of `jq`'s pole; it
  is what makes the descent faithful, and T12's 895 block consumes this public
  copy instead of carrying the pin's private one.

  ## The shared prelude is T10's

  The pin's file opens with the ~170-line `TPoleOrderLE` prelude; the port does
  not repeat it. `Defs/PhiGen.lean` carries it public (FLT ships it in twelve
  `S_` files), and the `poleOrderLE` proof below reads
  `tPoleOrderLE_phiProd_coeff` / `tPoleOrderLE_coeffEmb_iff` /
  `tPoleOrderLE_of_qExpand` straight from there.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_c_top.lean` (328 lines; the
  `c_eq_zero`/`poleOrderLE`/`sum_mul_jqN_pow_eq_zero`/`evalAtJ_injective` files
  are byte-equivalent copies). The five public statements are verbatim from their
  `Theorems/` wrappers.

  ## `evalAtJ_injective` by the mathlib route

  The pin proves it through a private 19-line `aeval_jq_eq_zero` (the `q ^ -d`
  coefficient reads off the leading coefficient). The port reuses the public
  `transcendental_jq` from `Defs/Jq.lean` via mathlib's
  `transcendental_iff_injective`, keeping only the six-line
  `evalAtJ_eq_aeval_map` bridge; the port's own `aeval_jq_eq_zero` stays public as
  the `Thm_ModularCurve_aeval_jq_eq_zero` interface. See the log for the spike.

  ## Assumptions

  `phiProd_monic`, `phiProd_natDegree`, `phiProd_eval_conj`, `conj_zero`,
  `conj_succ`, `PhiGenDescends`, `PoleOrderLE`/`TPoleOrderLE` and the prelude are
  the port's `Defs/PhiGen`; `coeffEmb`, `qExpand`, `coeffMap_qExpand`,
  `qExpand_qExpand` the port's `Defs/Laurent`; `jq`, `jqN`, `evalAtJ`,
  `transcendental_jq` the port's `Defs/Jq`.
-/
import FLTForHuman.ModularCurve.Defs.PhiGen

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve
namespace PhiGen

/-- The level substitution composed with the coefficient embedding is injective:
`coeffEmb` is (`coeffEmb_injective`) and `q ↦ q ^ ℓ` is (`qExpand_injective`). -/
private theorem coeffEmb_qExpand_injective {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] :
    Function.Injective (fun f : LaurentSeries ℚ => coeffEmb K (qExpand ℚ ℓ f)) :=
  (coeffEmb_injective K).comp (qExpand_injective (R := ℚ) ℓ)

/-- The descended family is monic: its top coefficient is `1`. -/
theorem PhiGenDescends.c_top {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) : c (ℓ + 1) = 1 := by
  refine coeffEmb_qExpand_injective (K := K) (ℓ := ℓ) ?_
  have h1 : (phiProd ℓ (conj ℓ ζ)).coeff (ℓ + 1) = 1 := by
    have h := (phiProd_monic ℓ (conj ℓ ζ)).coeff_natDegree
    rwa [phiProd_natDegree ℓ (conj ℓ ζ)] at h
  simp only [← hc (ℓ + 1), h1, map_one]

/-- The descended family vanishes above degree `ℓ + 1`. -/
theorem PhiGenDescends.c_eq_zero {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) {k : ℕ} (hk : ℓ + 1 < k) : c k = 0 := by
  refine coeffEmb_qExpand_injective (K := K) (ℓ := ℓ) ?_
  have h1 : (phiProd ℓ (conj ℓ ζ)).coeff k = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [phiProd_natDegree]; exact hk)
  simp only [← hc k, h1, map_zero]

/-- Every descended coefficient has pole order at most `ℓ + 1` at `q = 0`:
T10's bound `ℓ * ℓ + ℓ` in the expanded nome, divided by `ℓ` by
`tPoleOrderLE_of_qExpand`. -/
theorem PhiGenDescends.poleOrderLE {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (k : ℕ) : PoleOrderLE (c k) (ℓ + 1) := by
  have hW3 : TPoleOrderLE ((phiProd ℓ (conj ℓ ζ)).coeff k) (ℓ * ℓ + ℓ) :=
    tPoleOrderLE_phiProd_coeff ℓ ζ (coeffEmb K jq) (conj ℓ ζ) (conj_zero ℓ ζ) (conj_succ ℓ ζ)
      jSimplePole_jqK k
  rw [hc k, tPoleOrderLE_coeffEmb_iff] at hW3
  rw [← tPoleOrderLE_iff_poleOrderLE]
  exact tPoleOrderLE_of_qExpand (hW3.mono (le_of_eq (by ring)))

/-- The modular-equation relation in the descended family:
`∑_{k ≤ ℓ+1} c k * j(q^ℓ)^k = 0`. Applying the level substitution sends
`j(q^ℓ)` to the extra root `conj 0` and the product to its own root. -/
theorem PhiGenDescends.sum_mul_jqN_pow_eq_zero {K : Type*} [Field K] [Algebra ℚ K]
    {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) :
    ∑ k ∈ Finset.range (ℓ + 2), c k * (jqN ℓ) ^ k = 0 := by

  set F : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ ℓ) with hF
  have hFapp : ∀ f : LaurentSeries ℚ, F f = coeffEmb K (qExpand ℚ ℓ f) := fun f => rfl
  have hFinj : Function.Injective F := coeffEmb_qExpand_injective

  have hconj0 : conj ℓ ζ (0 : Fin (ℓ + 1)) = F (jqN ℓ) := by
    show conj ℓ ζ 0 = coeffMap (algebraMap ℚ K) (qExpand ℚ ℓ (jqN ℓ))
    rw [conj_zero, jqN, qExpand_qExpand, coeffMap_qExpand]
    rfl

  have hterm : ∀ k ∈ Finset.range (ℓ + 2),
      F (c k * (jqN ℓ) ^ k)
        = (phiProd ℓ (conj ℓ ζ)).coeff k * (conj ℓ ζ 0) ^ k := by
    intro k _
    rw [map_mul, map_pow, ← hconj0, hFapp, hc k]
  refine hFinj ?_
  rw [map_zero, map_sum, Finset.sum_congr rfl hterm]
  rw [← Polynomial.eval_eq_sum_range' (n := ℓ + 2) (by rw [phiProd_natDegree]; omega)]
  exact phiProd_eval_conj ℓ _ 0

/-- The bridge from the integer evaluation `evalAtJ` to mathlib's `ℚ`-algebra
evaluation `aeval jq` after the coefficient map `ℤ → ℚ`. Kept `private`; the
assembly module (which is downstream of this one and imports it) carries its own
copy because the pin's two files each do. -/
private theorem evalAtJ_eq_aeval_map (Q : Polynomial ℤ) :
    evalAtJ Q = Polynomial.aeval jq (Q.map (Int.castRingHom ℚ)) := by
  have hcomp : (algebraMap ℚ (LaurentSeries ℚ)).comp (Int.castRingHom ℚ)
      = algebraMap ℤ (LaurentSeries ℚ) := Subsingleton.elim _ _
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  rfl

/-- Evaluation at `jq` from `ℤ[X]` is injective — `jq` is transcendental. This is
the public entry point T12's 895 block imports. -/
theorem evalAtJ_injective : Function.Injective evalAtJ := by
  intro P Q hPQ
  have h' : Polynomial.aeval jq (P.map (Int.castRingHom ℚ))
      = Polynomial.aeval jq (Q.map (Int.castRingHom ℚ)) := by
    rw [← evalAtJ_eq_aeval_map, ← evalAtJ_eq_aeval_map]
    exact hPQ
  exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    ((transcendental_iff_injective.mp transcendental_jq) h')

end PhiGen
end ModularCurve

end

#print axioms ModularCurve.PhiGen.PhiGenDescends.c_top
#print axioms ModularCurve.PhiGen.PhiGenDescends.c_eq_zero
#print axioms ModularCurve.PhiGen.PhiGenDescends.poleOrderLE
#print axioms ModularCurve.PhiGen.PhiGenDescends.sum_mul_jqN_pow_eq_zero
#print axioms ModularCurve.PhiGen.evalAtJ_injective
