/-
  The modular-polynomial interface tail: integrality and the canonical datum.

  Two statements that the rest of FLT consumes, downstream of the capstone:

  * `exists_monic_evalAtJ_jqN_eq_zero` — `j(q ^ N)` is integral over `ℤ[X]`: it
    has a monic annihilator in `Polynomial (Polynomial ℤ)` (via `evalAtJ`).
  * `nonempty_modularPolynomialData` — the canonical datum `dataMinpoly N`, whose
    `Φ` is `minpoly (Polynomial ℤ) (jqN N)`.

  The integrality is the modular equation read as a tower: `j(q ^ (a * p))` is a
  root of the monic `Φ_p(j(q ^ a), Y)`, hence integral over `ℤ[X][j(q ^ a)]`, and
  levels multiply by transitivity of integrality. The canonical datum is the
  integer minimal polynomial, compared with its image in `ℚ⟮jq⟯` across the
  fraction-ring structure `Polynomial ℤ → ℚ⟮jq⟯`.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`: the two `Theorems/` wrappers
  named in the wire below. Statements are the wrappers' verbatim; the canonical
  datum is the pin's fraction-ring computation.

  spec-pin: Theorems/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean
  spec-pin: Theorems/Thm_ModularCurve_nonempty_modularPolynomialData.lean

  Assumes the capstone's degree count `finrank_adjoin_jqN_eq_dedekindPsi` from
  `Capstone.lean`, `phiAtSeed` and its lemmas from `Defs/PhiAtSlot.lean`, and
  `ModularPolynomialData`/`PhiIrreducible` from `Defs/Polynomial.lean`.
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.ModularEquation.Existence
import Mathlib.Data.Nat.Factorization.Induction

set_option autoImplicit false
-- The proofs install algebra and integrality instances with `haveI`/`letI`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

local instance integralityAlgebra : Algebra (Polynomial ℤ) (LaurentSeries ℚ) := evalAtJ.toAlgebra
local instance jqGenAlgebra : Algebra (Polynomial ℤ) ↥ℚ⟮jq⟯ := evalAtJGen.toAlgebra

/-- Integrality is transitive through a singleton adjoin: if `x` is integral over
`R` and `y` is integral over `R[x]`, then `y` is integral over `R`. -/
private theorem isIntegral_trans_adjoin_singleton {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x y : A} (hx : IsIntegral R x)
    (hy : IsIntegral ↥(Algebra.adjoin R ({x} : Set A)) y) : IsIntegral R y := by
  haveI : Algebra.IsIntegral R ↥(Algebra.adjoin R ({x} : Set A)) :=
    Algebra.IsIntegral.adjoin fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hx
  exact isIntegral_trans y hy

/-- The `n = 1` base case: `j(q ^ 1) = j(q)` is the algebra map at `X`. -/
private theorem isIntegral_jqN_one [NeZero 1] : IsIntegral (Polynomial ℤ) (jqN 1) := by
  have hjq : jqN 1 = algebraMap (Polynomial ℤ) (LaurentSeries ℚ) Polynomial.X := by
    rw [jqN_one]
    exact evalAtJ_X.symm
  rw [hjq]
  exact isIntegral_algebraMap

/-- **`j(q ^ N)` is integral over `ℤ[X]`** (via `evalAtJ`): it has a monic
annihilator in `Polynomial (Polynomial ℤ)`. The prime step is the modular
equation: `j(q ^ (a * p))` is a root of the monic `Φ_p(j(q ^ a), Y)`, hence
integral over `ℤ[X][j(q ^ a)]`. Verbatim from
`Theorems/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean`. -/
theorem exists_monic_evalAtJ_jqN_eq_zero (N : ℕ) [NeZero N] :
    ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.eval₂ evalAtJ (jqN N) = 0 := by
  suffices h : ∀ (n : ℕ) [NeZero n], IsIntegral (Polynomial ℤ) (jqN n) by
    obtain ⟨P, hP, hval⟩ := h N
    exact ⟨P, hP, hval⟩
  intro n
  induction n using induction_on_primes with
  | zero => intro hn; exact absurd rfl hn.out
  | one => exact isIntegral_jqN_one
  | prime_mul p a hp ih =>
    intro hpa
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero a := ⟨fun h0 => hpa.out (by rw [h0, Nat.mul_zero])⟩
    have hstep : IsIntegral ↥(Algebra.adjoin (Polynomial ℤ) ({jqN a} : Set (LaurentSeries ℚ)))
        (jqN (a * p)) := by
      obtain ⟨data, -, -⟩ := exists_phiIrreducible_evalSymm p
      let A := Algebra.adjoin (Polynomial ℤ) ({jqN a} : Set (LaurentSeries ℚ))
      let x : A := ⟨jqN a, Algebra.self_mem_adjoin_singleton (Polynomial ℤ) (jqN a)⟩
      refine ⟨phiAtSeed data x, phiAtSeed_monic data x, ?_⟩
      calc
        Polynomial.eval₂ (algebraMap A (LaurentSeries ℚ)) (jqN (a * p)) (phiAtSeed data x)
            = (phiAtSeed data (jqN a)).eval (jqN (a * p)) := by
              rw [Polynomial.eval₂_eq_eval_map, phiAtSeed_map]
              rfl
        _ = 0 := phiAtSeed_jqN_eval p data a
    have hint := isIntegral_trans_adjoin_singleton ih hstep
    rwa [jqN_congr (Nat.mul_comm a p)] at hint

private theorem coe_evalAtJGen (g : Polynomial ℤ) :
    ((evalAtJGen g : ℚ⟮jq⟯) : LaurentSeries ℚ) = evalAtJ g :=
  RingHom.congr_fun algebraMap_comp_evalAtJGen g

private theorem aeval_map_intCast (g : Polynomial ℤ) :
    Polynomial.aeval jq (g.map (algebraMap ℤ ℚ)) = evalAtJ g := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

private theorem evalAtJ_C (b : ℤ) : evalAtJ (Polynomial.C b) = (b : LaurentSeries ℚ) := by
  simp [evalAtJ]

/-- **`ℚ⟮jq⟯` is the fraction ring of `ℤ[X]`** under `X ↦ jq`: every element is a
ratio of two integer polynomials evaluated at `jq`. The numerator and denominator
come from `ℚ[X]` by `mem_adjoin_simple_iff`; `integerNormalization` clears their
coefficients. -/
private instance isFractionRing_polynomial_jq : IsFractionRing (Polynomial ℤ) ↥ℚ⟮jq⟯ := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨y, hy⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hy
    refine isUnit_iff_ne_zero.mpr fun h0 => hy (evalAtJGen_injective ?_)
    rw [map_zero]
    exact h0
  · intro z
    by_cases hz : (z : LaurentSeries ℚ) = 0
    · refine ⟨(0, 1), ?_⟩
      have hz0 : z = 0 := Subtype.ext hz
      rw [hz0]
      simp
    · obtain ⟨r, s, hrs⟩ :=
        (IntermediateField.mem_adjoin_simple_iff ℚ (z : LaurentSeries ℚ)).mp z.2
      have hs0 : Polynomial.aeval jq s ≠ 0 := by
        intro h0
        apply hz
        rw [hrs, h0, div_zero]
      have hzs : (z : LaurentSeries ℚ) * Polynomial.aeval jq s = Polynomial.aeval jq r := by
        rw [hrs, div_mul_cancel₀ _ hs0]
      obtain ⟨br, hbr, hrn⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) r
      obtain ⟨bs, hbs, hsn⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) s
      rw [mem_nonZeroDivisors_iff_ne_zero] at hbr hbs
      have hrval : evalAtJ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) r) =
          br • Polynomial.aeval jq r := by
        rw [← aeval_map_intCast, hrn]
        exact map_zsmul _ br r
      have hsval : evalAtJ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) s) =
          bs • Polynomial.aeval jq s := by
        rw [← aeval_map_intCast, hsn]
        exact map_zsmul _ bs s
      have hs'0 : IsLocalization.integerNormalization (nonZeroDivisors ℤ) s ≠ 0 := by
        intro h0
        have h1 : evalAtJ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) s) = 0 := by
          rw [h0, map_zero]
        rw [hsval] at h1
        have h2 : (bs : LaurentSeries ℚ) * Polynomial.aeval jq s = 0 :=
          (zsmul_eq_mul (Polynomial.aeval jq s) bs).symm.trans h1
        rcases mul_eq_zero.mp h2 with hb | hss
        · apply hbs
          have h3 : algebraMap ℚ (LaurentSeries ℚ) ((bs : ℚ)) =
              algebraMap ℚ (LaurentSeries ℚ) 0 := by
            rw [map_intCast, map_zero]
            exact hb
          have h4 : (bs : ℚ) = 0 := (algebraMap ℚ (LaurentSeries ℚ)).injective h3
          exact_mod_cast h4
        · exact hs0 hss
      have hcoe : ∀ g : Polynomial ℤ,
          ((algebraMap (Polynomial ℤ) ℚ⟮jq⟯ g : ℚ⟮jq⟯) : LaurentSeries ℚ) = evalAtJ g :=
        fun g => coe_evalAtJGen g
      have key : (z : LaurentSeries ℚ) *
          evalAtJ (Polynomial.C br * IsLocalization.integerNormalization (nonZeroDivisors ℤ) s) =
          evalAtJ (Polynomial.C bs * IsLocalization.integerNormalization (nonZeroDivisors ℤ) r) := by
        rw [map_mul, map_mul, evalAtJ_C, evalAtJ_C, hrval, hsval, zsmul_eq_mul,
          zsmul_eq_mul, ← hzs]
        ring
      refine ⟨(Polynomial.C bs * IsLocalization.integerNormalization (nonZeroDivisors ℤ) r,
        ⟨Polynomial.C br * IsLocalization.integerNormalization (nonZeroDivisors ℤ) s,
          mem_nonZeroDivisors_of_ne_zero
            (mul_ne_zero (Polynomial.C_ne_zero.mpr hbr) hs'0)⟩), Subtype.ext ?_⟩
      show ((z * algebraMap (Polynomial ℤ) ℚ⟮jq⟯
          (Polynomial.C br * IsLocalization.integerNormalization (nonZeroDivisors ℤ) s) :
            ℚ⟮jq⟯) : LaurentSeries ℚ) =
        ((algebraMap (Polynomial ℤ) ℚ⟮jq⟯
          (Polynomial.C bs * IsLocalization.integerNormalization (nonZeroDivisors ℤ) r) :
            ℚ⟮jq⟯) : LaurentSeries ℚ)
      rw [MulMemClass.coe_mul, hcoe, hcoe]
      exact key
  · intro x y hxy
    exact ⟨1, by rw [evalAtJGen_injective hxy]⟩

/-- **The canonical modular-polynomial datum**: `Φ = minpoly (Polynomial ℤ) (jqN N)`.
Its degree is `ψ(N)` by comparing with the field minimal polynomial across the
fraction ring; it vanishes at `jqN N` by `minpoly.aeval`. -/
def dataMinpoly (N : ℕ) [NeZero N] : ModularPolynomialData N := by
  haveI tower : IsScalarTower (Polynomial ℤ) ↥ℚ⟮jq⟯ (LaurentSeries ℚ) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (RingHom.congr_fun algebraMap_comp_evalAtJGen x).symm
  have hx : IsIntegral (Polynomial ℤ) (jqN N) := by
    obtain ⟨P, hP, hval⟩ := exists_monic_evalAtJ_jqN_eq_zero N
    exact ⟨P, hP, hval⟩
  have hxQ : IsIntegral ↥ℚ⟮jq⟯ (jqN N) := hx.tower_top
  have hmin := minpoly.isIntegrallyClosed_eq_field_fractions' ↥ℚ⟮jq⟯ hx
  have hfinrank := finrank_adjoin_jqN_eq_dedekindPsi N
  rw [IntermediateField.adjoin.finrank hxQ] at hfinrank
  have hΦm : (minpoly (Polynomial ℤ) (jqN N)).Monic := minpoly.monic hx
  have hdeg : (minpoly (Polynomial ℤ) (jqN N)).natDegree = dedekindPsi N := by
    rw [← hΦm.natDegree_map (algebraMap (Polynomial ℤ) ↥ℚ⟮jq⟯), ← hmin]
    exact hfinrank
  have heval : (minpoly (Polynomial ℤ) (jqN N)).eval₂ evalAtJ (jqN N) = 0 := by
    have ha := minpoly.aeval (Polynomial ℤ) (jqN N)
    rw [Polynomial.aeval_def] at ha
    exact ha
  exact ⟨minpoly (Polynomial ℤ) (jqN N), hΦm, hdeg, heval⟩

/-- **The modular polynomial datum exists at every level**: the canonical
`dataMinpoly N`. Verbatim from
`Theorems/Thm_ModularCurve_nonempty_modularPolynomialData.lean`. -/
theorem nonempty_modularPolynomialData (N : ℕ) [NeZero N] :
    Nonempty (ModularPolynomialData N) :=
  ⟨dataMinpoly N⟩

end ModularCurve

end
