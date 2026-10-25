/-
The characteristic-`p` Frobenius form of `qExpand`: on the `j`-line, `q ↦ q ^ p`
*is* the `p`-th power map.

Two pin headlines:

* `map_intCast_pow_char_eq_qExpand` — for a commutative ring `K` of
  characteristic `ℓ` and any integral Laurent series `s`,
  `(s.map (Int.castRingHom K)) ^ ℓ = qExpand K ℓ (s.map (Int.castRingHom K))`.
* `qExpand_jqModC_eq_pow_unconditional` — the `j`-line case,
  `qExpand K ℓ (jqModC K) = (jqModC K) ^ ℓ`, for a commutative ring of
  characteristic `ℓ` (no field, no root of unity, no `CharZero`: hence
  "unconditional").

## The mathematics

`qExpand K ℓ` is the substitution `q ↦ q ^ ℓ` (`Defs/Laurent.lean`), so on
coefficients it is the identity and on exponents the multiplication by `ℓ`. If
every coefficient `c` of `s` is fixed by the `ℓ`-th power map (`c ^ ℓ = c`) then
the product of `ℓ` copies of `s` reindexes exactly as `qExpand` does — the
convolution sum collapses because `ℓ` is prime and the binomial coefficients
vanish in characteristic `ℓ`. The integral Laurent series are the case that
matters: their coefficients are integer casts, and `Int.cast` lands in the prime
subfield `ℤ/ℓ`, where `n ^ ℓ = n` (Fermat). `jqModC K` is by definition the
`Int.cast`-image of `jqModC ℤ`, which gives the second headline.

## Layering

The two statements are `Theorems/` headlines and are the pin's verbatim. The
machinery they read is already in the port and is imported, not restated:

* `qExpand` and its coefficient API (`qExpand_coeff_mul`,
  `qExpand_coeff_of_not_dvd`) — `Defs/Laurent.lean`;
* `jqModC`, `jqModC_eq_map_intCast` — `Defs/JqCoeff.lean`;
* the general Frobenius identity
  `pow_char_eq_coeffMap_frobenius_qExpand : s ^ p = coeffMap (frobenius R p)
  (qExpand R p s)` — `Frobenius/Defs.lean`, together with
  `pow_char_single_one_eq`, `pow_char_ofPowerSeries_eq` and
  `intCast_pow_char_eq`.

**Why two private copies.** Those `Frobenius/Defs.lean` lemmas are stated over
a field (`[Field K]`, the pin's `Def_ModularCurve_QExpFrobeniusModL.lean`
binder), because the same module's `qExpFrobeniusModL` acts on the function
field. The two headlines here are stated over a commutative ring (the pin's own
binder, and `ℤ/ℓ`-coefficient applications such as `ZMod p` are not fields of
that module's shape), so the two steps `Int.cast`-fixed ⇒ fixed coefficients and
fixed coefficients ⇒ `s ^ ℓ = qExpand` are re-proved here as `private` lemmas —
four lines each, the same proof as the field versions, and not declarations the
port owns.

Nothing is `sorry`; there are no `own:` declarations (the two public names are
the pin's).

FLT `anthropics/fermats-last-theorem@aa2d8b3`:
`P2M/Sol/S_ModularCurve_map_intCast_pow_char_eq_qExpand.lean` (176 lines) and
`P2M/Sol/S_ModularCurve_qExpand_jqModC_eq_pow_unconditional.lean` (105 lines),
with the statement authority of their `Theorems/` wrappers.
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_map_intCast_pow_char_eq_qExpand.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_qExpand_jqModC_eq_pow_unconditional.lean>

  spec-pin: Theorems/Thm_ModularCurve_map_intCast_pow_char_eq_qExpand.lean
  spec-pin: P2M/Sol/S_ModularCurve_map_intCast_pow_char_eq_qExpand.lean
  spec-pin: Theorems/Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional.lean
  spec-pin: P2M/Sol/S_ModularCurve_qExpand_jqModC_eq_pow_unconditional.lean
-/
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Frobenius.Defs

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

section FixedCoefficients

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]

/-- A Laurent series whose coefficients are fixed by the `p`-th power map is
fixed by `qExpand R p`: the pin's
`pow_char_eq_qExpand_of_coeff_fixed`, at the commutative-ring binder the two
headlines below need (the field copy is `Frobenius/Defs.lean`'s
`qExpand_eq_pow_of_coeff_fixed`). -/
private theorem pow_char_eq_qExpand_of_coeff_fixed (s : LaurentSeries R)
    (hfix : ∀ k : ℤ, (s.coeff k) ^ p = s.coeff k) : s ^ p = qExpand R p s := by
  rw [pow_char_eq_coeffMap_frobenius_qExpand p s]
  ext k
  rw [coeffMap_coeff, frobenius_def]
  by_cases hpk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hpk
    rw [qExpand_coeff_mul, hfix m]
  · rw [qExpand_coeff_of_not_dvd _ _ hpk, zero_pow (Fact.out : p.Prime).ne_zero]

/-- An integer cast is fixed by the `p`-th power map in a commutative ring of
characteristic `p`: Fermat in the prime subfield. The field copy is
`Frobenius/Defs.lean`'s `intCast_pow_char_eq`. -/
private theorem intCast_pow_char_eq' (n : ℤ) : ((n : R)) ^ p = (n : R) := by
  have h : (frobenius R p).comp (Int.castRingHom R) = Int.castRingHom R := RingHom.ext_int _ _
  exact (RingHom.congr_fun h n :)

end FixedCoefficients

/-- **The `ℓ`-power map on an integral Laurent series is `qExpand`.** Verbatim
from `Theorems/Thm_ModularCurve_map_intCast_pow_char_eq_qExpand.lean:6`. -/
theorem map_intCast_pow_char_eq_qExpand {K : Type*} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP K ℓ] (s : LaurentSeries ℤ) :
    (s.map (Int.castRingHom K)) ^ ℓ = qExpand K ℓ (s.map (Int.castRingHom K)) := by
  refine pow_char_eq_qExpand_of_coeff_fixed _ fun k => ?_
  rw [HahnSeries.map_coeff]
  exact intCast_pow_char_eq' _

/-- **`qExpand` is the Frobenius on the `j`-line**: for a commutative ring of
characteristic `ℓ`, `qExpand K ℓ (jqModC K) = (jqModC K) ^ ℓ`. Verbatim from
`Theorems/Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional.lean:6`. -/
theorem qExpand_jqModC_eq_pow_unconditional (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] :
    qExpand K ℓ (jqModC K) = (jqModC K) ^ ℓ := by
  rw [jqModC_eq_map_intCast K]
  exact (map_intCast_pow_char_eq_qExpand ℓ (jqModC ℤ)).symm

end ModularCurve

end
