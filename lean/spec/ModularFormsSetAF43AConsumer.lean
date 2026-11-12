/-
  Consumer zone for `FLTForHuman/ModularForms/NebentypusSeparation.lean` (order AF43A).

  A `spec/` probe, not a library module: it *consumes* the two headlines in composition, never by
  `#check`, and it is checked by
  `lake env lean spec/ModularFormsSetAF43AConsumer.lean` (it never enters the build).

  The module's two headlines are a `Γ₁` level-lowering split and a multiplicity-one degeneracy
  statement. Both are stated at a general modulus, so both can be read at the smallest modulus that
  still fires them:

  * **Zone 1 — A1 at `N = ℓ` a prime.** `ℓ.primeFactors = {ℓ}`, so both divisor sums of the
    headline have one term, `∑_{p ∣ ℓ} = ` the `p = ℓ` term, and the level drop is
    `ℓ / ℓ = 1`. The conclusion then says that the *single* form `G ℓ` is fixed by all of
    `Γ₁(1) = SL(2, ℤ)` and equals `F ℓ`: the split has produced one `Γ₁(1)`-stable form out of the
    one `Γ₁(ℓ)`-form. This is the level-lowering statement in its degenerate (one-prime) case, and
    it is the shape the multiplicity-one argument consumes.

  * **Zone 2 — A2 at `n = 1`.** `Fin 1` has one index, so there is one eigenform `g`, one level
    `L 0 = M`, and `M / L 0 = M / M = 1` with `Nat.divisors 1 = {1}`: one divisor, hence a *single*
    degeneracy lift `G 0 1`. The conclusion `c 0 1 = 0` is the vanishing of the one coefficient of
    that one lift — the base case of multiplicity one.

  * **Zone 3 — A2 at `n = 2`.** Two eigenforms with `q`-coefficient separation and two divisor
    strings `Nat.divisors (M / L 0)`, `Nat.divisors (M / L 1)`. The conclusion is split into its two
    halves, i.e. both degeneracy strings vanish: the two families are linearly independent.

  The order's suggested reading of `n = 1` was "the vanishing of every coefficient of a single
  degeneracy lift". Taken literally that needs `Nat.divisors (M / L 0)` to be all of `ℕ`, which it is
  not: at `L 0 = M` the only divisor is `1` and the only coefficient available is `c 0 1`. The
  substitution made here is to read the headline at `L 0 = M` (`M / L 0 = 1`, so `Nat.divisors` is
  the singleton `{1}`) and to report the vanishing of *the* coefficient `c 0 1` of *the* lift
  `G 0 1`; the "every coefficient" form is then Zone 3's per-`d` statement. Nothing else about the
  order's suggestion is changed.
-/
import FLTForHuman.ModularForms.NebentypusSeparation

set_option autoImplicit false

open CongruenceSubgroup ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularFormsSetAF43AConsumer

/-! ## 1. A1 at a prime modulus: one term, and `Γ₁(1)`-stability -/

section PrimeLevel

variable (ℓ : ℕ) [NeZero ℓ] (k : ℤ)

/-- **Zone 1.** The level-lowering split `CuspForm.exists_sum_eq_forall_gamma1_div_slash_eq` at a
prime level `N = ℓ`.

Because `ℓ.primeFactors = {ℓ}`, the hypothesis `hF` is only asked at `p = ℓ` and the two divisor
sums of the conclusion collapse to their `p = ℓ` term. The dropped level is `ℓ / ℓ = 1`, so the
conclusion becomes: there is a form `g` at level `Γ₁(ℓ)`, fixed by every element of `Γ₁ 1`, whose
slash by `γ ∈ Γ₁ 1` is itself, and `g` *is* the given `F ℓ`. In other words the single summand
already descends to `Γ₁(1)`. -/
theorem exists_gamma1_one_stable_of_prime (hℓ : ℓ.Prime) (F : ℕ → CuspForm (Gamma ℓ) k)
    (hF : ∀ p ∈ ℓ.primeFactors,
      (⇑(F p) : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((ℓ / p : ℕ) : ℤ) * ModularGroup.S⁻¹) = ⇑(F p))
    (hsum : ∀ γ ∈ Gamma1 ℓ,
      (⇑(∑ p ∈ ℓ.primeFactors, F p) : ℍ → ℂ) ∣[k] γ = ⇑(∑ p ∈ ℓ.primeFactors, F p)) :
    ∃ g : CuspForm (Gamma ℓ) k,
      (∀ γ ∈ Gamma1 1, (⇑g : ℍ → ℂ) ∣[k] γ = ⇑g) ∧ g = F ℓ := by
  obtain ⟨G, hG, hsumG⟩ := CuspForm.exists_sum_eq_forall_gamma1_div_slash_eq ℓ k F hF hsum
  -- `ℓ.primeFactors` is the singleton `{ℓ}`, so `p = ℓ` is the only index that occurs.
  have hfac : ℓ.primeFactors = {ℓ} := by
    simpa using Nat.primeFactors_prime_pow (k := 1) one_ne_zero hℓ
  have hmem : ℓ ∈ ℓ.primeFactors := by rw [hfac]; exact Finset.mem_singleton_self ℓ
  -- the dropped level is `ℓ / ℓ = 1`
  have hone : ℓ / ℓ = 1 := Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne ℓ))
  refine ⟨G ℓ, ?_, ?_⟩
  · intro γ hγ
    have h1 := hG ℓ hmem
    rw [hone] at h1
    exact h1 γ hγ
  · rw [hfac] at hsumG
    simpa using hsumG

end PrimeLevel

/-! ## 2. A2 at one index: the single lift, and its coefficient -/

section OneEigenform

variable (M : ℕ) [NeZero M] (k : ℤ)

/-- **Zone 2.** The multiplicity-one statement
`CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne` at `n = 1` and at
the top level `L 0 = M`.

`Fin 1` is a single index, so `hsep` is vacuous, and `M / L 0 = M / M = 1` with
`Nat.divisors 1 = {1}`: there is exactly one divisor and hence exactly one degeneracy lift `G 1`.
The conclusion is the vanishing of its single coefficient `c 1`. -/
theorem one_eigenform_one_divisor
    (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) (hg : CuspForm.IsEigenformWith ε g)
    (G : ℕ → CuspForm (Gamma1 M) k)
    (hG : ∀ d : ℕ, d ∣ M / M → ∀ τ : ℍ, G d τ = g (ModularForm.heckeDiagMatrix d • τ))
    (c : ℕ → ℂ)
    (hc : (∑ _i : Fin 1, ∑ d ∈ Nat.divisors (M / M), c d • G d) = 0) :
    c 1 = 0 := by
  have h := CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne
    M k 1 (fun _ => M) (fun _ => dvd_rfl) (fun _ => ε) (fun _ => g) (fun _ => hg)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
    (fun _ => G) (fun _ d hd τ => hG d hd τ) (fun _ => c) hc
  have hdiv : M / M = 1 := Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne M))
  have hmem : 1 ∈ Nat.divisors (M / M) := by
    rw [hdiv, Nat.divisors_one]; exact Finset.mem_singleton_self 1
  exact h 0 1 hmem

end OneEigenform

/-! ## 3. A2 at two indices: both strings vanish -/

section TwoEigenforms

variable (M : ℕ) [NeZero M] (k : ℤ)

/-- **Zone 3.** The same headline at `n = 2`: two eigenforms `g 0`, `g 1` at levels `L 0`, `L 1`,
satisfying the separation hypothesis, and a vanishing combination of their two degeneracy strings.
The conclusion is split into its two `Fin 2` halves: every coefficient in *both* strings vanishes,
which is the linear independence of the two families. -/
theorem two_eigenforms_vanish (L : Fin 2 → ℕ) [∀ i, NeZero (L i)] (hL : ∀ i, L i ∣ M)
    (ε : (i : Fin 2) → DirichletCharacter ℂ (L i))
    (g : (i : Fin 2) → CuspForm (Gamma1 (L i)) k)
    (hg : ∀ i, CuspForm.IsEigenformWith (ε i) (g i))
    (hsep : ∀ i j : Fin 2, i ≠ j → ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧
      ModularFormClass.qCoeff (g i) p ≠ ModularFormClass.qCoeff (g j) p)
    (G : Fin 2 → ℕ → CuspForm (Gamma1 M) k)
    (hG : ∀ (i : Fin 2) (d : ℕ), d ∣ M / L i →
      ∀ τ : ℍ, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ))
    (c : Fin 2 → ℕ → ℂ)
    (hc : (∑ i, ∑ d ∈ Nat.divisors (M / L i), c i d • G i d) = 0) :
    (∀ d ∈ Nat.divisors (M / L 0), c 0 d = 0) ∧
      (∀ d ∈ Nat.divisors (M / L 1), c 1 d = 0) :=
  ⟨fun d hd => CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne
      M k 2 L hL ε g hg hsep G hG c hc 0 d hd,
   fun d hd => CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne
      M k 2 L hL ε g hg hsep G hG c hc 1 d hd⟩

end TwoEigenforms

end ModularFormsSetAF43AConsumer

end
