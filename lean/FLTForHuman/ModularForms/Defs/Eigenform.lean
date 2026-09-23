/-
  The normalized eigenform predicate.

  A normalized eigenform is a weight-2 cusp form for `Γ₀(N)` whose `q`-expansion
  is `q + a₂q² + ⋯` (`qCoeff_one`), is multiplicative (`qCoeff_mul_of_coprime`),
  and whose coefficients at prime powers satisfy the `T_p`/`U_p` recursions
  (`qCoeff_prime_pow_of_not_dvd`, `qCoeff_prime_pow_of_dvd`). It is the object
  the FLT route attaches to a Galois representation.

  Transcribed verbatim from `Definitions/Def_FLTPrelim_Modularity.lean:26–40`
  (pinned `aa2d8b3`); the field names are load-bearing (downstream code
  pattern-matches on them). `ModularFormClass.qCoeff` itself was carried by SET-3
  T5 in `HeckeQCoeff.lean`.

  The dictionary between the structure and the Hecke operators is
  `HeckeEigenform.lean` (T8).
-/
import FLTForHuman.ModularForms.HeckeQCoeff

set_option autoImplicit false

noncomputable section

namespace CuspForm

open ModularFormClass

/-- The pin's `CuspForm.IsNormalizedEigenform`, verbatim. -/
structure IsNormalizedEigenform {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    Prop where

  qCoeff_one : qCoeff f 1 = 1

  qCoeff_mul_of_coprime : ∀ m n : ℕ, m.Coprime n →
    qCoeff f (m * n) = qCoeff f m * qCoeff f n

  qCoeff_prime_pow_of_not_dvd : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1)) - p * qCoeff f (p ^ r)

  qCoeff_prime_pow_of_dvd : ∀ p r : ℕ, p.Prime → p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1))

end CuspForm

end
