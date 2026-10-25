/-
  The `j`-constants over a general field: `jqModC`/`jqNModC`, the coefficient
  API at the cusp, the field `modularFunctionFieldC`, and the base-change facts
  `map_jqModC` / `jqModC_eq_map_intCast`.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_JqCoeff.lean` (83 lines).
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_JqCoeff.lean

  `Defs/Jq.lean` already has `jq`, `jqN`, `jNum`; the pin states these over a
  general `CommRing K` via `PowerSeries.map`, with `jqModC_rat` a `rfl`.

  ## The pole at the cusp (`jqModC_pow` and the `coeff_jqModC_*` trio)

  `j(q) = q⁻¹·u` with `u` a power series of constant coefficient `1`: the three
  pin headlines `coeff_jqModC_pow_self` / `coeff_jqModC_pow_of_lt` /
  `coeff_jqModC_neg_one` say exactly that (leading coefficient `1` at `q⁻ᵇ`, no
  coefficients below it, hence `j = q⁻¹ + …`), and `jqModC_pow` is the single
  structural form they read off. This is the valuation input to
  `Degree/PhiDegree.lean`'s `transcendental_jqModC` (the leading-coefficient
  argument) and to every degree/pole count downstream.

  **This is the trio's one home.** The three are pin headlines
  (`Theorems/Thm_ModularCurve_coeff_jqModC_{pow_self,pow_of_lt,neg_one}.lean`)
  and were previously only `private`, twice over, in
  `ModularPolynomialStarBank.lean` and `X0/FunctionFieldFull.lean`, with a fourth
  copy of `coeff_jqModC_neg_one` in `RelIndex/LeRelrank.lean` — the
  `CARRY-FORWARD.md` orphan-phantom row. They are now stated once here, beside
  the `jqModC` they are about, and the four modules import them. `jqModC_pow` was
  public in `X0/FunctionFieldFull.lean` and keeps its public name here;
  `constantCoeff_jNum_map` is pin-private, has no consumer, and stays `private`.

  spec-pin: Definitions/Def_ModularCurve_JqCoeff.lean
  spec-pin: Definitions/Def_ModularCurve_CoeffSemilinearAut.lean
  spec-pin: Theorems/Thm_ModularCurve_map_jqNModC.lean
  spec-pin: P2M/Sol/S_ModularCurve_map_jqNModC.lean
  spec-pin: Theorems/Thm_ModularCurve_coeff_jqModC_pow_self.lean
  spec-pin: Theorems/Thm_ModularCurve_coeff_jqModC_pow_of_lt.lean
  spec-pin: Theorems/Thm_ModularCurve_coeff_jqModC_neg_one.lean
  spec-pin: P2M/Sol/S_ModularCurve_coeff_jqModC_pow_self.lean
  spec-pin: Theorems/Thm_ModularCurve_order_jqModC.lean
  spec-pin: P2M/Sol/S_ModularCurve_order_jqModC.lean

-/
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.Defs.Fields

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

section JExpansion

variable (K : Type*) [CommRing K]

def jqModC : LaurentSeries K :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))

def jqNModC (N : ℕ) [NeZero N] : LaurentSeries K := qExpand K N (jqModC K)

@[simp]
theorem jqNModC_one : jqNModC K 1 = jqModC K := qExpand_one_apply _

theorem jqModC_rat : jqModC ℚ = jq := rfl

variable {K} in

theorem map_jqModC {K' : Type*} [CommRing K'] (f : K →+* K') :
    (jqModC K).map f = jqModC K' := by
  have hmul : ∀ x y : LaurentSeries K, (x * y).map f = x.map f * y.map f :=
    fun x y => HahnSeries.map_mul f.toNonUnitalRingHom
  have hsingle : (HahnSeries.single (-1 : ℤ) (1 : K)).map f = HahnSeries.single (-1 : ℤ) 1 := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single, apply_ite f,
      map_one, map_zero]
  have hseries : ∀ u : PowerSeries K,
      (HahnSeries.ofPowerSeries ℤ K u).map f = HahnSeries.ofPowerSeries ℤ K' (u.map f) := by
    intro u
    ext k
    rw [HahnSeries.map_coeff]
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  rw [jqModC, jqModC, hmul, hsingle, hseries,
    show (jNum.map (Int.castRingHom K)).map f = jNum.map (Int.castRingHom K') from by
      rw [show PowerSeries.map f (PowerSeries.map (Int.castRingHom K) jNum)
            = PowerSeries.map (f.comp (Int.castRingHom K)) jNum from
          (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom K) f)) jNum).symm,
        RingHom.ext_int (f.comp (Int.castRingHom K)) (Int.castRingHom K')]]

theorem jqModC_eq_map_intCast : jqModC K = (jqModC ℤ).map (Int.castRingHom K) :=
  (map_jqModC (Int.castRingHom K)).symm

section CoeffMap

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The pin's `coeffMap_jqModC`: `map_jqModC` read through `coeffMap`
(`Definitions/Def_ModularCurve_CoeffSemilinearAut.lean`'s general binder form; the
`X0ModL` section-`R` spelling is the same statement and is not restated). The four
`coeffMap`-form copies the port had grown — one public in `X0/FunctionFieldFull.lean`,
three `private` in `X1/` — are its instances and are gone. -/
theorem coeffMap_jqModC (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

end CoeffMap

/-- Coefficientwise maps commute with the `q`-substitution on `jqNModC`: naturality in
the coefficient ring of the `q`-expansion of `j(q^N)`.  This is the pin's
`map_jqNModC` (`Theorems/Thm_ModularCurve_map_jqNModC.lean`); the two `coeffMap`-form
copies that had grown in `X0/FunctionFieldFull.lean` (public) and in
`Degree/PhiData.lean` / `X1/IntegralityJqNModC.lean` (private) are its instances and
are gone. -/
theorem map_jqNModC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap φ (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, jqNModC, coeffMap_qExpand]
  exact congrArg (qExpand S N) (map_jqModC φ)

end JExpansion

/-! ## The pole at the cusp

`j(q) = q⁻¹ · u` with `u ∈ K[[q]]` of constant coefficient `1`. The structural
form is `jqModC_pow` — stated at the pin `S_` file's section-variable binders, as
that is the module the port transcribes it from — and the three coefficient facts
are the pin headlines, stated at their `Theorems/` wrappers' binders (the
wrapper is the checker's statement authority). `coeff_jqModC_neg_one` is the case
`b = 1`. -/

section PoleAtCusp

variable (K : Type*) [CommRing K]

/-- `j(q)^b` is the `q^(-b)` single term times a power series — the pole/unit
factorisation every coefficient fact below reads off. -/
theorem jqModC_pow (n : ℕ) :
    (jqModC K) ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

/-- The unit part `jNum` of `j` has constant coefficient `1` over any `K`. -/
private theorem constantCoeff_jNum_map :
    PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]

end PoleAtCusp

section PoleAtCuspCoefficients

/-- The leading coefficient of `j(q)^b` at `q^(-b)` is `1`. -/
theorem coeff_jqModC_pow_self (K : Type*) [CommRing K] (b : ℕ) :
    ((jqModC K) ^ b).coeff (-(b : ℤ)) = 1 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNum_map, one_pow]

/-- `j(q)^b` has no coefficient below `q^(-b)`: its order is exactly `-b`. -/
theorem coeff_jqModC_pow_of_lt (K : Type*) [CommRing K] {b : ℕ} {m : ℤ}
    (hm : m < -(b : ℤ)) : ((jqModC K) ^ b).coeff m = 0 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

/-- The `q⁻¹` coefficient of `j` is `1`: `j(q) = q⁻¹ + 196884 q + …`. -/
theorem coeff_jqModC_neg_one (K : Type*) [CommRing K] : (jqModC K).coeff (-1 : ℤ) = 1 := by
  simpa using coeff_jqModC_pow_self K 1

/-- `j` is nonzero over a nontrivial ring: its `q⁻¹` coefficient is `1`. -/
private theorem jqModC_ne_zero (K : Type*) [CommRing K] [Nontrivial K] : jqModC K ≠ 0 := by
  intro h
  have h1 : (jqModC K).coeff (-1 : ℤ) = 1 := coeff_jqModC_neg_one K
  rw [h, HahnSeries.coeff_zero] at h1
  exact zero_ne_one h1

/-- The order of `j` at the cusp is exactly `-1`: the pole is simple, and `j`
has no coefficient below `q⁻¹`. -/
theorem order_jqModC (K : Type*) [CommRing K] [Nontrivial K] : (jqModC K).order = -1 := by
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) ?_
  · rw [coeff_jqModC_neg_one]
    exact one_ne_zero
  · by_contra hlt
    rw [not_le] at hlt
    refine HahnSeries.coeff_order_eq_zero.not.mpr (jqModC_ne_zero K) ?_
    have h := coeff_jqModC_pow_of_lt K (b := 1) (m := (jqModC K).order) (by simpa using hlt)
    simpa using h

end PoleAtCuspCoefficients

section FunctionField

variable (K : Type*) [Field K]

def modularFunctionFieldC (N : ℕ) [NeZero N] :
    IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K {jqModC K, jqNModC K N}

theorem jqModC_mem (N : ℕ) [NeZero N] : jqModC K ∈ modularFunctionFieldC K N :=
  IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)

theorem jqNModC_mem (N : ℕ) [NeZero N] : jqNModC K N ∈ modularFunctionFieldC K N :=
  IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)

theorem modularFunctionFieldC_rat (N : ℕ) [NeZero N] :
    modularFunctionFieldC ℚ N = modularFunctionField N := rfl

theorem modularFunctionFieldC_one :
    modularFunctionFieldC K 1 = IntermediateField.adjoin K {jqModC K} := by
  unfold modularFunctionFieldC
  rw [jqNModC_one, Set.pair_eq_singleton]

end FunctionField

end ModularCurve

end
