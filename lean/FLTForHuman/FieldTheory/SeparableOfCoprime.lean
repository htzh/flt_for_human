/-
A finite extension is separable when its degree is coprime to the exponential
characteristic.

Canonical source: the pinned FLT `aa2d8b3` wrapper

* `Theorems/Thm_Algebra_IsSeparable_of_coprime_finrank_expChar.lean` (statement),

with its `S_` file
`P2M/Sol/S_Algebra_IsSeparable_of_coprime_finrank_expChar.lean` (24 lines, the whole
proof body).  The pin's proof is a short transcription and carries over to mathlib
`v4.34.0` unchanged: `q` is the exponential characteristic of `F`, so the
inseparable degree `finInsepDegree F E` is a power of `q` (`IsPurelyInseparable`
inside the separable closure) while `finSepDegree * finInsepDegree = finrank`; if
`finrank` is coprime to `q` then `q ^ n = 1`, so the inseparable degree is `1` and
`finSepDegree F E = finrank F E`, which is the separability criterion.

This module assumes nothing from the port: it imports only mathlib.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_Algebra_IsSeparable_of_coprime_finrank_expChar.lean>
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

namespace Algebra.IsSeparable

/-- **Separability from a coprime degree.**  Verbatim from
`Theorems/Thm_Algebra_IsSeparable_of_coprime_finrank_expChar.lean`; the proof is the
pin's `S_` `solution` (24 lines). -/
theorem of_coprime_finrank_expChar (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (q : ℕ) [ExpChar F q] (h : Nat.Coprime (Module.finrank F E) q) :
    Algebra.IsSeparable F E := by
  rw [← Field.finSepDegree_eq_finrank_iff]

  haveI : ExpChar (separableClosure F E) q :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F E)).injective q
  haveI : IsPurelyInseparable (separableClosure F E) E := separableClosure.isPurelyInseparable F E
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow (separableClosure F E) E q
  have hins : Field.finInsepDegree F E = q ^ n := hn
  have hmul := Field.finSepDegree_mul_finInsepDegree F E
  rw [hins] at hmul

  have hdvd : q ^ n ∣ Module.finrank F E := ⟨Field.finSepDegree F E, by rw [mul_comm]; exact hmul.symm⟩
  have hone : q ^ n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n h.symm) hdvd
  rw [hone, mul_one] at hmul
  exact hmul

end Algebra.IsSeparable
