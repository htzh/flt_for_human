/-
The `K`-general divisor-generated function field `modularFunctionFieldFullC`, after
FLT's `Definitions/Def_ModularCurve_X0ModL.lean` (156 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0ModL.lean>).

The pin generalises `Def_ModularCurve_X0.lean`'s `ℚ`-valued theory: `jqModC` in place of
`jq`, `qExpandAlg` in place of `qExpandₐ`, and `divisorExpansionsC` /
`modularFunctionFieldFullC` in place of `divisorExpansions` /
`modularFunctionFieldFull`. `modularFunctionFieldFullC_rat` is the `rfl` bridge back to
the ported `modularFunctionFieldFull`.

Two dedups against the port, both already homed elsewhere because the `qExp`
carrier needs them:

* `coeffMap_ofPowerSeries` is **not** restated here — it is imported from
  `ModularCurve/Frobenius/Defs.lean`, whose header records it as taken from this
  pin module; `qExpandAlg`/`qExpandAlg_apply` are **not** restated here either —
  they are `ModularCurve.qExpandAlg`/`qExpandAlg_apply`, whose one home is
  `ModularCurve/Defs/Laurent.lean`, beside `qExpand` itself (this pin file declares
  that general map too, under its `HomC`-suffixed name);
* the pin's three imported
  `Theorems/Thm_ModularCurve_coeff_jqModC_{pow_self,pow_of_lt,neg_one}.lean`
  declarations are pin headlines; their one home is `Defs/JqCoeff.lean` (the pole at
  the cusp, together with the `jqModC_pow` factorisation they read off), imported
  below. The `private` copies that had been re-derived here — and the fourth copy of
  `coeff_jqModC_neg_one` in `RelIndex/LeRelrank.lean` — are gone.

Statements are transcribed verbatim; the pin's `import Mathlib` is replaced by the
specific imports below.

**The index is general.** `divisorExpansionsC` and `modularFunctionFieldFullC` carry no
`NeZero N`: the pin's `S_` files that consume them
(`P2M/Sol/S_ModularCurve_relfinrank_fullC_mul_prime_pow.lean` 354–1145,
`P2M/Sol/S_ModularCurve_package_of_socket.lean` 365–475) state their lemmas at `L`, `L * n` and
`M * p ^ a` with no nonzeroness hypothesis on the index, and `[NeZero (L * n)]` is not synthesizable
from theirs. The binder was vestigial here (neither body uses it, and five of the section's lemmas
already `omit`ted it); the two lemmas whose statement does consume it,
`modularFunctionFieldC_le_full` and `full_degeneracyC_le`, carry it explicitly, the first through a
nested `variable [NeZero N]` section so that its printed statement keeps the pin's text.

  spec-pin: Definitions/Def_ModularCurve_X0ModL.lean

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

/- `coeffMap_jqModC` / `map_jqNModC` live in their one public home,
`Defs/JqCoeff.lean`; the copies here (and in `Degree/PhiData`, `X1/IntegralityJqNModC`,
`X1/FunctionFieldIsAlgClosed`, `X1/FunctionFieldResidue`) are gone. -/

variable {R} in

theorem coeff_jqModC_eq_intCast (k : ℤ) : (jqModC R).coeff k = (((jqModC ℤ).coeff k : ℤ) : R) := by
  conv_lhs => rw [← coeffMap_jqModC (Int.castRingHom R)]
  rfl

/-! ### The `coeff_jqModC_*` trio

The pin imports these three from `Theorems/Thm_ModularCurve_coeff_jqModC_{pow_self,
pow_of_lt,neg_one}.lean`; their one public home — with the pole/unit factorisation
`jqModC_pow` they read off — is `Defs/JqCoeff.lean` (the pole at the cusp), imported
above. The `private` re-derivations that used to live here are gone. -/

theorem coeff_jqModC_of_lt {k : ℤ} (hk : k < -1) : (jqModC R).coeff k = 0 := by
  simpa using coeff_jqModC_pow_of_lt R (b := 1) (m := k) (by simpa using hk)

theorem jqModC_ne_zero_of_nontrivial [Nontrivial R] : jqModC R ≠ 0 := fun h => by
  simpa [h] using coeff_jqModC_neg_one R

end JExpansion

section FunctionField

variable (K : Type*) [Field K] (N : ℕ)

def divisorExpansionsC : Set (LaurentSeries K) :=
  {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = qExpand K d (jqModC K)}

theorem mem_divisorExpansionsC {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand K d (jqModC K) ∈ divisorExpansionsC K N :=
  ⟨d, ‹_›, hd, rfl⟩

def modularFunctionFieldFullC : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K (divisorExpansionsC K N)

theorem modularFunctionFieldFullC_rat : modularFunctionFieldFullC ℚ N = modularFunctionFieldFull N :=
  rfl

theorem jqModCd_mem_full {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand K d (jqModC K) ∈ modularFunctionFieldFullC K N :=
  subset_adjoin K _ (mem_divisorExpansionsC K N hd)

theorem jqModC_mem_full : jqModC K ∈ modularFunctionFieldFullC K N := by
  simpa [qExpand_one_apply] using jqModCd_mem_full K N (one_dvd N)

section

variable [NeZero N]

theorem modularFunctionFieldC_le_full : modularFunctionFieldC K N ≤ modularFunctionFieldFullC K N := by
  rw [modularFunctionFieldC, adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact jqModC_mem_full K N
  · exact jqModCd_mem_full K N dvd_rfl

end

theorem full_degeneracyC_le {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) :
    modularFunctionFieldFullC K N ≤ modularFunctionFieldFullC K M := by
  rw [modularFunctionFieldFullC, adjoin_le_iff]
  rintro x ⟨d, hne, hdvd, rfl⟩
  have := hne
  exact jqModCd_mem_full K M (hdvd.trans h)

theorem full_degeneracyC_map_le (ℓ : ℕ) [NeZero ℓ] :
    (modularFunctionFieldFullC K N).map (qExpandAlg K ℓ) ≤ modularFunctionFieldFullC K (N * ℓ) := by
  rw [modularFunctionFieldFullC, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨d, hne, hdvd, rfl⟩, rfl⟩
  have := hne
  have : NeZero (ℓ * d) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne d)⟩
  show qExpandAlg K ℓ (qExpand K d (jqModC K)) ∈ _
  rw [qExpandAlg_apply, qExpand_qExpand]
  exact jqModCd_mem_full K (N * ℓ) ((mul_dvd_mul_left ℓ hdvd).trans (dvd_of_eq (mul_comm ℓ N)))

end FunctionField

section Jacobian

variable (K : Type*) [Field K] (N : ℕ)

abbrev JZeroC : Type _ := Pic0 K (modularFunctionFieldFullC K N)

end Jacobian

end ModularCurve

end
