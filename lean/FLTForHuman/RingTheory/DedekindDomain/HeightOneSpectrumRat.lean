/-
The height-one spectrum of `ℤ` is the set of primes.

`IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat`: every
height-one prime `v` of `𝓞 ℚ` is `span {p}` for a prime `p : ℕ`. Twenty pin lines, and the bridge
between `ℚ`'s spectrum and `ℕ`'s primes that the `ℚ`-side ray-class arguments need.

Home `RingTheory/DedekindDomain/` — the subject is the height-one spectrum of a Dedekind domain, and
the statement is `IsDedekindDomain`-namespaced.

## The rows

* `IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat` — 20 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat.lean>

spec-pin: Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat.lean
spec-pin: P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat.lean

## Port notes (order AF107F)

* **Surface = the pin's.** 1 declaration, 1 public / 0 private, against the pin's 2 entries
  (`Theorems/Thm_…` + `S_…`'s `solution`: the same statement twice). 2 − 1 = 1.
* **`check_port`**: 1 ok, 0 mismatch, 0 missing, 0 own, 0 kw.
* **Substitutions**: none, but one **import added**: the pin's proof uses
  `Rat.HeightOneSpectrum.natGenerator` / `prime_natGenerator` / `span_natGenerator` and
  `Rat.IsIntegralClosure.intEquiv`, which live in
  `Mathlib.NumberTheory.Padics.HeightOneSpectrum` — a module the scaffold's narrow list did not
  reach (the pin imported bare `Mathlib`). Added as a single `Mathlib.*` import; its `.olean`
  exists in this checkout.
* **API drift** (`v4.33.1` → `v4.34.0`): none; the pin's 20-line proof transcribes verbatim
  (`Ideal.map_of_equiv`, `Ideal.map_span`).
* **Axioms**: subset of `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe (recorded, never installed)**: passes the whole downward ladder —
  40000 / 20000 / 10000 / 5000 / **1000** all pass; module floor passes at 1000.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Tactic

open IsDedekindDomain NumberField

set_option autoImplicit false

theorem IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  refine ⟨Rat.HeightOneSpectrum.natGenerator v, Rat.HeightOneSpectrum.prime_natGenerator v, ?_⟩
  set e : 𝓞 ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) with he
  have h : Ideal.map (e : 𝓞 ℚ →+* ℤ) v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} :=
    (Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v).symm
  have h3 : Ideal.map (e.symm : ℤ →+* 𝓞 ℚ) (Ideal.map (e : 𝓞 ℚ →+* ℤ) v.asIdeal) = v.asIdeal :=
    Ideal.map_of_equiv e
  rw [← h3, h, Ideal.map_span, Set.image_singleton]
  congr 2
  simp
