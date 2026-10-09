/-
The `K`-general divisor-generated function field `modularFunctionFieldFullC`, after
FLT's `Definitions/Def_ModularCurve_X0ModL.lean` (156 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0ModL.lean>).

The pin generalises `Def_ModularCurve_X0.lean`'s `ℚ`-valued theory: `jqModC` in place of
`jq`, `qExpandAlgHomC` in place of `qExpandₐ`, and `divisorExpansionsC` /
`modularFunctionFieldFullC` in place of `divisorExpansions` /
`modularFunctionFieldFull`. `modularFunctionFieldFullC_rat` is the `rfl` bridge back to
the ported `modularFunctionFieldFull`.

Two dedups against the port, both recorded in `Frobenius/Defs.lean`'s own header (it
ported them early because its `qExp` carrier needs them):

* `coeffMap_ofPowerSeries` and `qExpandAlgHomC`/`qExpandAlgHomC_apply` are **not**
  restated here — they are imported from `ModularCurve/Frobenius/Defs.lean`, which
  already documents them as taken from this pin module;
* the pin's three imported
  `Theorems/Thm_ModularCurve_coeff_jqModC_{pow_self,pow_of_lt,neg_one}.lean`
  declarations exist in the port only `private` inside
  `ModularCurve/Degree/PhiDegree.lean`, so they are re-derived locally `private` here
  (no promotions); they are listed in the C2 completion report.

Statements are transcribed verbatim; the pin's `import Mathlib` is replaced by the
specific imports below.
-/
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Frobenius.Defs
import FLTForHuman.AlgebraicCurve.Defs.Divisor

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve

namespace ModularCurve

section JExpansion

variable (R : Type*) [CommRing R]

theorem jqNModC_rat (N : ℕ) [NeZero N] : jqNModC ℚ N = jqN N := rfl

variable {R} in

theorem coeffMap_jqModC {S : Type*} [CommRing S] (f : R →+* S) : coeffMap f (jqModC R) = jqModC S := by
  rw [jqModC, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries,
    ← RingHom.comp_apply (PowerSeries.map f) (PowerSeries.map (Int.castRingHom R)),
    ← PowerSeries.map_comp, RingHom.ext_int (f.comp (Int.castRingHom R)) (Int.castRingHom S)]
  rfl

variable {R} in
theorem coeffMap_jqNModC {S : Type*} [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, coeffMap_qExpand, coeffMap_jqModC, jqNModC]

variable {R} in

theorem coeff_jqModC_eq_intCast (k : ℤ) : (jqModC R).coeff k = (((jqModC ℤ).coeff k : ℤ) : R) := by
  conv_lhs => rw [← coeffMap_jqModC (Int.castRingHom R)]
  rfl

theorem jqModC_pow (n : ℕ) :
    jqModC R ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ R ((jNum.map (Int.castRingHom R)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

/-! ### Local `private` re-derivations of the pin-imported `coeff_jqModC_*` trio

The pin imports these three from `Theorems/Thm_ModularCurve_coeff_jqModC_{pow_self,
pow_of_lt,neg_one}.lean`; in the port they exist only `private` in
`ModularCurve/Degree/PhiDegree.lean`, so §3/§5 of the work order has them re-derived
here (no promotion, no hub edit). -/

private theorem constantCoeff_jNum_map (K : Type*) [CommRing K] :
    PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]

private theorem coeff_jqModC_pow_self (K : Type*) [CommRing K] (b : ℕ) :
    ((jqModC K) ^ b).coeff (-(b : ℤ)) = 1 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNum_map, one_pow]

private theorem coeff_jqModC_pow_of_lt (K : Type*) [CommRing K] {b : ℕ} {m : ℤ}
    (hm : m < -(b : ℤ)) : ((jqModC K) ^ b).coeff m = 0 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

private theorem coeff_jqModC_neg_one (K : Type*) [CommRing K] :
    (jqModC K).coeff (-1 : ℤ) = 1 := by
  simpa using coeff_jqModC_pow_self K 1

theorem coeff_jqModC_of_lt {k : ℤ} (hk : k < -1) : (jqModC R).coeff k = 0 := by
  simpa using coeff_jqModC_pow_of_lt R (b := 1) (m := k) (by simpa using hk)

theorem jqModC_ne_zero_of_nontrivial [Nontrivial R] : jqModC R ≠ 0 := fun h => by
  simpa [h] using coeff_jqModC_neg_one R

end JExpansion

section FunctionField

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def divisorExpansionsC : Set (LaurentSeries K) :=
  {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = qExpand K d (jqModC K)}

omit [NeZero N] in
theorem mem_divisorExpansionsC {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand K d (jqModC K) ∈ divisorExpansionsC K N :=
  ⟨d, ‹_›, hd, rfl⟩

def modularFunctionFieldFullC : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K (divisorExpansionsC K N)

omit [NeZero N] in

theorem modularFunctionFieldFullC_rat : modularFunctionFieldFullC ℚ N = modularFunctionFieldFull N :=
  rfl

omit [NeZero N] in
theorem jqModCd_mem_full {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand K d (jqModC K) ∈ modularFunctionFieldFullC K N :=
  subset_adjoin K _ (mem_divisorExpansionsC K N hd)

omit [NeZero N] in
theorem jqModC_mem_full : jqModC K ∈ modularFunctionFieldFullC K N := by
  simpa [qExpand_one_apply] using jqModCd_mem_full K N (one_dvd N)

theorem modularFunctionFieldC_le_full : modularFunctionFieldC K N ≤ modularFunctionFieldFullC K N := by
  rw [modularFunctionFieldC, adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact jqModC_mem_full K N
  · exact jqModCd_mem_full K N dvd_rfl

theorem full_degeneracyC_le {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) :
    modularFunctionFieldFullC K N ≤ modularFunctionFieldFullC K M := by
  rw [modularFunctionFieldFullC, adjoin_le_iff]
  rintro x ⟨d, hne, hdvd, rfl⟩
  have := hne
  exact jqModCd_mem_full K M (hdvd.trans h)

omit [NeZero N] in

theorem full_degeneracyC_map_le (ℓ : ℕ) [NeZero ℓ] :
    (modularFunctionFieldFullC K N).map (qExpandAlgHomC K ℓ) ≤ modularFunctionFieldFullC K (N * ℓ) := by
  rw [modularFunctionFieldFullC, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨d, hne, hdvd, rfl⟩, rfl⟩
  have := hne
  have : NeZero (ℓ * d) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne d)⟩
  show qExpandAlgHomC K ℓ (qExpand K d (jqModC K)) ∈ _
  rw [qExpandAlgHomC_apply, qExpand_qExpand]
  exact jqModCd_mem_full K (N * ℓ) ((mul_dvd_mul_left ℓ hdvd).trans (dvd_of_eq (mul_comm ℓ N)))

end FunctionField

section Jacobian

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

abbrev JZeroC : Type _ := Pic0 K (modularFunctionFieldFullC K N)

end Jacobian

end ModularCurve

end
