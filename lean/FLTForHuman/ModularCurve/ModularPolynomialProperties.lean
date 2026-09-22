/-
  T12 — the properties, concluded: symmetry from the coefficient family, and
  existence of an irreducible symmetric datum.

  `evalSymm_of_coeff_evalAtJ_eq` derives the three coefficient hypotheses of
  `ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion` from T10's two
  pole-bound exports (`phiProd_conj_coeff_zero_lead`,
  `phiProd_conj_coeff_eq_zero_of_le`) threaded through the descended family, and
  concludes `EvalSymm` via `evalSymm_of_splits`.
  `exists_phiIrreducible_evalSymm` is the cone's own construction: it chooses a
  primitive `ℓ`-th root in `CyclotomicField ℓ ℚ` (mathlib supplies one) and runs
  the whole chain (a) descent (T11) → (b) integrality (T9) → (c) membership (T8)
  → T11's assembly and splitting → this topic's `phiIrreducible_of_splits` and
  `evalSymm_of_coeff_evalAtJ_eq`. It is a join, not new mathematics, and it is
  T13's entry point.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean` (124 lines) and
  `P2M/Sol/S_ModularCurve_exists_phiIrreducible_evalSymm.lean` (62 lines). Both
  public statements are the `Theorems/` wrappers verbatim.

  ## Assumptions

  `Defs/PhiGen`, `Defs/Polynomial`, `Defs/Fields`, `Defs/Jq`; T10's
  `PhiGenPoleBounds`; T11's `ModularPolynomialAssembly` (the assembly and
  `splits_of_coeff_evalAtJ_eq`) and `PhiGenDescent` (`exists_phiGenDescends`);
  T9's `PhiGenIntegrality`; T8's `ModularForms/PhiGenDescends`; this topic's
  `ModularPolynomialIrreducible`.
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
namespace PhiGen

/-! ## The descended family's coefficients as those of `phiProd` -/

section Seam

private theorem PhiGenDescends.coeff_phiProd_coeff {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (k : ℕ) (m : ℤ) :
    ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff ((ℓ : ℤ) * m) = algebraMap ℚ K ((c k).coeff m) := by
  rw [hc k, coeffEmb_coeff, qExpand_coeff_mul]

/-- The leading `q ^ (-(ℓ + 1))` coefficient of `c 0` is `1` (T10's leading pole
coefficient, read through the level substitution). -/
private theorem PhiGenDescends.c_zero_coeff_lead {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    (c 0).coeff (-((ℓ + 1 : ℕ) : ℤ)) = 1 := by
  refine (algebraMap ℚ K).injective ?_
  rw [← PhiGenDescends.coeff_phiProd_coeff hc 0 (-((ℓ + 1 : ℕ) : ℤ)), map_one]
  have hidx : (ℓ : ℤ) * (-((ℓ + 1 : ℕ) : ℤ)) = -((ℓ * ℓ + ℓ : ℕ) : ℤ) := by push_cast; ring
  rw [hidx]
  exact phiProd_conj_coeff_zero_lead ℓ ζ hζ

/-- The deeper coefficients of `c 0` vanish (T10's pole bound). -/
private theorem PhiGenDescends.c_zero_coeff_eq_zero_of_lt {K : Type*} [Field K] [Algebra ℚ K]
    {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (m : ℕ) (hm : ℓ + 1 < m) :
    (c 0).coeff (-(m : ℤ)) = 0 :=
  hc.poleOrderLE 0 (-(m : ℤ)) (by push_cast; omega)

/-- Every coefficient of `c k` for `k ≠ 0` vanishes from `q ^ (-(ℓ + 1))` down
(T10's bound for the non-constant family). -/
private theorem PhiGenDescends.c_coeff_eq_zero_of_ne_zero {K : Type*} [Field K] [Algebra ℚ K]
    {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (k : ℕ) (hk : k ≠ 0) (m : ℕ) (hm : ℓ + 1 ≤ m) :
    (c k).coeff (-(m : ℤ)) = 0 := by
  refine (algebraMap ℚ K).injective ?_
  rw [← PhiGenDescends.coeff_phiProd_coeff hc k (-(m : ℤ)), map_zero]
  have hidx : (ℓ : ℤ) * (-(m : ℤ)) = -((ℓ * m : ℕ) : ℤ) := by push_cast; ring
  rw [hidx]
  exact phiProd_conj_coeff_eq_zero_of_le ℓ ζ k hk (ℓ * m) (by nlinarith [hℓ.out.two_le])

end Seam

/-! ## Symmetry from the coefficient family -/

section Symmetry

/-- The datum is symmetric when its coefficients are the descended family: T10's
pole bounds give the three hypotheses of
`transposeToAdjoin_monic_of_qExpansion`, and `evalSymm_of_splits` concludes.
Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean`. -/
theorem evalSymm_of_coeff_evalAtJ_eq {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) (hc : PhiGenDescends ℓ ζ c)
    (data : ModularPolynomialData ℓ) (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) :
    EvalSymm data.Φ := by

  have hsplit : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ)
      = phiProd ℓ (conj ℓ ζ) :=
    splits_of_coeff_evalAtJ_eq ζ hc data hcoeff

  have h0top : (evalAtJ (data.Φ.coeff 0)).coeff (-((dedekindPsi ℓ : ℕ) : ℤ)) = 1 := by
    rw [hcoeff 0, dedekindPsi_prime hℓ.out]
    exact PhiGenDescends.c_zero_coeff_lead hc hζ
  have h0le : ∀ m : ℕ, dedekindPsi ℓ < m →
      (evalAtJ (data.Φ.coeff 0)).coeff (-(m : ℤ)) = 0 := by
    intro m hm
    rw [hcoeff 0]
    exact PhiGenDescends.c_zero_coeff_eq_zero_of_lt hc m (by rwa [dedekindPsi_prime hℓ.out] at hm)
  have hk : ∀ k, k ≠ 0 → ∀ m : ℕ, dedekindPsi ℓ ≤ m →
      (evalAtJ (data.Φ.coeff k)).coeff (-(m : ℤ)) = 0 := by
    intro k hk0 m hm
    rw [hcoeff k]
    exact PhiGenDescends.c_coeff_eq_zero_of_ne_zero hc k hk0 m
      (by rwa [dedekindPsi_prime hℓ.out] at hm)

  obtain ⟨hTmonic, hTdeg⟩ := data.transposeToAdjoin_monic_of_qExpansion h0top h0le hk

  exact evalSymm_of_splits ℓ ζ hζ data hsplit hTmonic hTdeg.le

end Symmetry

end PhiGen

/-! ## Existence of an irreducible symmetric datum -/

set_option linter.style.haveILetI false in
/-- There is an irreducible symmetric modular polynomial datum at every prime
`ℓ`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean`. -/
theorem exists_phiIrreducible_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ := by

  haveI : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  haveI hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  haveI : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]
    exact hz
  have hζ1 : hzu.unit ^ ℓ = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]

  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends ℓ hzu.unit hζ

  have hint : ∀ k, PhiGen.IntCoeffs (c k) := fun k => hc.intCoeffs hζ1 k
  have hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq} :=
    fun k => PhiGen.mem_adjoin_jq_of_phiGenDescends ℓ hzu.unit hζ c hc k

  obtain ⟨data, hcoeff⟩ := PhiGen.exists_modularPolynomialData_coeff_eq hc hint hmem
  exact ⟨data,
    PhiGen.phiIrreducible_of_splits ℓ hzu.unit hζ data
      (PhiGen.splits_of_coeff_evalAtJ_eq hzu.unit hc data hcoeff),
    PhiGen.evalSymm_of_coeff_evalAtJ_eq hζ hc data hcoeff⟩

end ModularCurve

end

#print axioms ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq
#print axioms ModularCurve.exists_phiIrreducible_evalSymm
