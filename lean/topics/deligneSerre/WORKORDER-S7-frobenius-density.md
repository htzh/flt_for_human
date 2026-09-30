# Work order — S7: Frobenius density and Frobenius elements (27 nodes)

**Status: ready; execute as three sequential dispatches, each reviewed before the
next — H and S1–S5 are closed (checker 2467/0/0).** Method handbook: `lean/porting-playbook.md` (§2.4, §3.1–§3.5, §4).
Mathematics: `math/019` §4 (the density input).

## 0. Scope and the three-way split

The qualitative Frobenius density theorem (Chebotarev) from the degree-one prime
asymptotic, plus the places/Frobenius vocabulary it is stated with. 27 nodes /
3,229 pin lines — the largest set. Do **not** give it to one agent: dispatch the
three sub-sets below in order, reviewing each.

| dispatch | subject | nodes | pin lines | homes |
|---|---|---:|---:|---|
| **S7-I** | place / Frobenius vocabulary | 8 | 818 | `NumberTheory/{ValuationAtPlace,FrobeniusAtPlace}.lean` (extend) + `NumberTheory/FrobeniusDensity/` |
| **S7-II** | zeta / coset / Möbius counting chain to `degOneAsymptotic` | 13 | 1,937 | `NumberTheory/FrobeniusDensity/` (imports the H1 `Basic.lean`) |
| **S7-III** | the density statement and its applications | 6 | 374 | `NumberTheory/FrobeniusDensity/` |

S7-I and S7-II are independent of S1–S5; S7-III needs S7-I and S7-II.

**Progress.** S7-I closed 7 of its 8 nodes (checker 2474/0/0):
`FrobeniusAtPlace.lean` extended, plus `ValuationSubringLocalization.lean`,
`FrobeniusLift.lean`, `KerRestrictNormalHom.lean`. The eighth,
`CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int`, is
**deferred to a short S7-I-tail dispatch after S7-II**, because its pin proof
consumes `FrobeniusDensity.degOneSum_add_log_isBigO` (S7-II). Recorded negative:
mathlib `v4.34` has no Chebotarev and no split-completely/degree-one infinitude, and
no elementary route avoiding the degree-one counting chain was found.

**S7-II closed all 13 nodes plus the two H1-deferred blocks**
(`sum_moebius_mem_zpowers`, `degOneSum_ne_top`), checker 2531/0/0, in seven new
modules (`MobiusZeta`, `IdealSum`, `PrimeSumSplit`, `PrimeSumAsymptotic`,
`DegOneSumAsymptotic`, `DegOneAsymptoticProof`, `DegreeOneCount`).
**Coset-engine finding (recorded negative):** the scout's PhiGen/Hecke coset ports
and even `FieldTheory/FiniteGroupAction.lean` / `WeilExchange/Bifibre.lean` are the
*wrong* geometry for these nodes — the pin's ideal-coset arguments want mathlib's
`Ideal` orbit API (`Ideal.exists_smul_eq_of_isGaloisGroup`, `IsArithFrobAt`,
`MulAction.stabilizer` on an ideal), which is what S7-II used. Do not send a future
worker to those modules for this material.

**Remaining S7 dispatch:** S7-III (6 nodes) **plus** the S7-I tail node
`CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int` in one
dispatch — both are unblocked by S7-II. In the
decided order S7 runs after S5 and before S6 (S6c consumes
`FrobeniusDensity.statement`). If S7-II proves too large for one agent, split it at
`primeSum_eq_degOneSum_add` (the analytic ideal-sum block first, the degree-one
count second) and dispatch the halves sequentially.

**Explicitly not this set:** the Group B lemmas and the ray-class continuation
(`PORTING-DeligneSerre.md` §7), and the density *applications* in S6/S8.

## 1. The public targets — statements verbatim from the pin wrappers

<!-- ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem -->
```lean
theorem ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem
    (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓQ : (ℓ : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hstab : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt)
    (hfrob : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ∀ x : AlgebraicClosure ℚ,
      x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a) :
    A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ := by p2m_exact_reverting
```

<!-- ValuationSubring.exists_liesOverPrime_algebraicClosure_rat -->
```lean
theorem ValuationSubring.exists_liesOverPrime_algebraicClosure_rat (p : Nat.Primes) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) := by p2m_exact_reverting
```

<!-- ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat -->
```lean
theorem ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
    {p : ℕ} (hp : p.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime p) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p := by p2m_exact_reverting
```

<!-- ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure -->
```lean
theorem ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
    (p : Nat.Primes) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      A.LiesOverPrime (p : ℕ) ∧ A.IsFrobeniusAt σ (p : ℕ) := by p2m_exact_reverting
```

<!-- NumberField.exists_valuationSubring_eq_localization -->
```lean
theorem NumberField.exists_valuationSubring_eq_localization
    (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal] :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), ∀ x : AlgebraicClosure ℚ,
      x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a := by p2m_exact_reverting
```

<!-- NumberField.exists_isFrobenius_lift_arithFrobAt -->
```lean
theorem NumberField.exists_isFrobenius_lift_arithFrobAt
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField E] [IsGalois ℚ E]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)]
    [Finite (𝓞 E ⧸ Q)] :
    ∃ (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) (_ : Qt.IsMaximal)
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      Qt.LiesOver Q ∧ AlgEquiv.restrictNormal τ E = arithFrobAt ℤ (E ≃ₐ[ℚ] E) Q ∧
      (∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt) ∧
      ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt := by p2m_exact_reverting
```

<!-- IsOpen.exists_numberField_ker_restrictNormalHom_le -->
```lean
theorem IsOpen.exists_numberField_ker_restrictNormalHom_le
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
      (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
      (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H := by p2m_exact_reverting
```

<!-- CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int -->
```lean
theorem CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [Module.Finite ℤ R] :
    {ℓ : ℕ | ℓ.Prime ∧ Nonempty (R →+* ZMod ℓ)}.Infinite := by p2m_exact_reverting
```

<!-- ArithmeticFunction.sum_moebius_filter_dvd -->
```lean
theorem ArithmeticFunction.sum_moebius_filter_dvd {n m : ℕ} (hn : n ≠ 0) (hm : m ∣ n) :
    ∑ f ∈ n.divisors, ArithmeticFunction.moebius (n / f) * (if m ∣ f then 1 else 0)
      = if m = n then 1 else 0 := by p2m_exact_reverting
```

<!-- FrobeniusDensity.sum_moebius_mul_pos -->
```lean
theorem FrobeniusDensity.sum_moebius_mul_pos {G : Type*} [Group G] [Finite G] (σ : G) :
    0 < ∑ f ∈ (orderOf σ).divisors,
      (ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) := by p2m_exact_reverting
```

<!-- FrobeniusDensity.weight_eq -->
```lean
theorem FrobeniusDensity.weight_eq {G : Type*} [Group G] [Finite G] (σ τ : G) :
    ∑ f ∈ (orderOf σ).divisors,
        (ArithmeticFunction.moebius (orderOf σ / f)) *
          ((f : ℤ) * ({x : G ⧸ Subgroup.zpowers (σ ^ (orderOf σ / f)) | τ • x = x}.ncard : ℤ))
      = ({g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard : ℤ) := by p2m_exact_reverting
```

<!-- FrobeniusDensity.idealSum_ne_top -->
```lean
theorem FrobeniusDensity.idealSum_ne_top
    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    FrobeniusDensity.idealSum K s ≠ ⊤ := by p2m_exact_reverting
```

<!-- FrobeniusDensity.tendsto_sub_one_mul_idealSum_test -->
```lean
theorem FrobeniusDensity.tendsto_sub_one_mul_idealSum_test
    (K : Type*) [Field K] [NumberField K] :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (FrobeniusDensity.idealSum K s).toReal)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by p2m_exact_reverting
```

<!-- FrobeniusDensity.summable_degOne_term -->
```lean
theorem FrobeniusDensity.summable_degOne_term
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
      (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) := by p2m_exact_reverting
```

<!-- FrobeniusDensity.ncard_degreeOne_primesOver_under -->
```lean
theorem FrobeniusDensity.ncard_degreeOne_primesOver_under
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {H : Subgroup (L ≃ₐ[ℚ] L)} {E : IntermediateField ℚ L} [IsGaloisGroup H E L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime]
    [Q₀.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] (hinertia : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    {𝔮 ∈ (FrobeniusDensity.ratPrimeIdeal ℓ).primesOver (𝓞 E) |
      Nat.card ((𝓞 E) ⧸ 𝔮) = ℓ}.ncard
      = {x : (L ≃ₐ[ℚ] L) ⧸ H |
          ∀ d ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q₀, d • x = x}.ncard := by p2m_exact_reverting
```

<!-- FrobeniusDensity.ncard_degreeOne_primesOver_eq_ncard_frobFixed -->
```lean
theorem FrobeniusDensity.ncard_degreeOne_primesOver_eq_ncard_frobFixed
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {H : Subgroup (L ≃ₐ[ℚ] L)} {E : IntermediateField ℚ L} [IsGaloisGroup H E L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime]
    [Q₀.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] (hinertia : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    haveI : Finite ((𝓞 L) ⧸ Q₀) :=
      FrobeniusDensity.finite_quotient_of_ne_bot
        (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    {𝔮 ∈ (FrobeniusDensity.ratPrimeIdeal ℓ).primesOver (𝓞 E) |
      Nat.card ((𝓞 E) ⧸ 𝔮) = ℓ}.ncard
      = {x : (L ≃ₐ[ℚ] L) ⧸ H | arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀ • x = x}.ncard := by p2m_exact_reverting
```

<!-- FrobeniusDensity.stabilizer_eq_zpowers_arithFrobAt -->
```lean
theorem FrobeniusDensity.stabilizer_eq_zpowers_arithFrobAt
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] (hinertia : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    haveI : Finite ((𝓞 L) ⧸ Q) :=
      FrobeniusDensity.finite_quotient_of_ne_bot
        (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    MulAction.stabilizer (L ≃ₐ[ℚ] L) Q
      = Subgroup.zpowers (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by p2m_exact_reverting
```

<!-- FrobeniusDensity.primeSum_eq_degOneSum_add -->
```lean
theorem FrobeniusDensity.primeSum_eq_degOneSum_add
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) (s : ℝ) :
    FrobeniusDensity.primeSum K s =
      FrobeniusDensity.degOneSum K S₀ s + FrobeniusDensity.cutSum K S₀ s +
      FrobeniusDensity.tailSum K s := by p2m_exact_reverting
```

<!-- FrobeniusDensity.primeSum_toReal_add_log_isBigO -->
```lean
theorem FrobeniusDensity.primeSum_toReal_add_log_isBigO
    (K : Type*) [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by p2m_exact_reverting
```

<!-- FrobeniusDensity.degOneSum_add_log_isBigO -->
```lean
theorem FrobeniusDensity.degOneSum_add_log_isBigO
    (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) :
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s))
      + Real.log (s - 1)) =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1 : ℝ)) := by p2m_exact_reverting
```

<!-- FrobeniusDensity.degOneAsymptotic -->
```lean
theorem FrobeniusDensity.degOneAsymptotic (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L := by p2m_exact_reverting
```

<!-- FrobeniusDensity.statement_of_degOneAsymptotic -->
```lean
theorem FrobeniusDensity.statement_of_degOneAsymptotic (L : Type*) [Field L] [NumberField L]
    [IsGalois ℚ L] (hL : FrobeniusDensity.DegOneAsymptotic L) :
    FrobeniusDensity.Statement L := by p2m_exact_reverting
```

<!-- FrobeniusDensity.statement -->
```lean
theorem FrobeniusDensity.statement (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.Statement L := by p2m_exact_reverting
```

<!-- FrobeniusDensity.exists_frobenius_conj_pow_of_statement -->
```lean
theorem FrobeniusDensity.exists_frobenius_conj_pow_of_statement
    (hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (S : Finset ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧
      ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (τ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (j : ℕ),
        A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧ ∀ x ∈ L, σ x = (γ * τ ^ j * γ⁻¹) x := by p2m_exact_reverting
```

<!-- FrobeniusDensity.frobeniusPowerDense_of_le_ker -->
```lean
theorem FrobeniusDensity.frobeniusPowerDense_of_le_ker (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H)
    (S : Finset ℕ) : FrobeniusPowerDense S H := by p2m_exact_reverting
```

<!-- FrobeniusDensity.ncard_conj_gen_ne_zero_iff -->
```lean
theorem FrobeniusDensity.ncard_conj_gen_ne_zero_iff {G : Type*} [Group G] [Finite G]
    (σ τ : G) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard ≠ 0
      ↔ ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) τ := by p2m_exact_reverting
```

<!-- Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen -->
```lean
theorem Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H := by p2m_exact_reverting
```

## 2. Route, dedup, risk

- **The H1 `NumberTheory/FrobeniusDensity/Basic.lean` home is the prelude.** Its
  blocks (`sum_moebius_mem_zpowers`, `mem_zpowers_pow_div_iff`, `tsum_normFiber`,
  `isBigO_sum_of_tendsto_div`, `exists_pow_coprime_eq_of_orderOf_eq`,
  `ncard_conj_mem_eq_card_mul_ncard`, `tendsto_sum_idealCount_div`,
  `card_le_of_forall_pow_eq`, `ncard_eq_sum_indicator`, `primeSum_le_idealSum`,
  `toReal_term`, `term_eq_ofReal_zetaTerm`, `degOneSum_ne_top`,
  `idealSum_eq_tsum_zetaTerm`, `orderOf_pow_orderOf_div`, `normFiberEquiv`,
  `LSeriesSummable_idealCount`, `summable_zetaTerm`, `zetaTerm_nonneg`, `tsum_equiv'`,
  `NormFiber`, `mono`) plus the **shared definitions** in the D modules
  (`Def_TaylorWiles_Primes` → `NumberTheory/FrobeniusDensity/TaylorWilesPrimes.lean`,
  `Def_FrobeniusDensity_{DegOneAsymptotic,BadPrimes,PrimeSums}`) are imported, not
  re-proved. `mono` is generic — reuse the port's if one exists. **Two of these
  were deferred by H1** (no `sorry`, noted in the module header): `sum_moebius_mem_zpowers`
  and `degOneSum_ne_top`, because their pin proofs call the S7-II headlines
  `ArithmeticFunction.sum_moebius_filter_dvd` and `FrobeniusDensity.idealSum_ne_top`.
  Port them once inside S7-II, at the pin names, and log the home.
- **Coset / orbit–stabilizer machinery is already ported — check it before
  re-proving.** The S7 coset arguments are Galois-group orbits on primes/places and
  quotient-group fixed-point counts, not the SL(2,ℤ) cosets. The existing engine:
  `NumberTheory/FrobeniusDensity/Basic.lean`'s `ncard_conj_mem_eq_card_mul_ncard`
  (the exact `{g | g⁻¹ τ g ∈ H}.ncard = Nat.card H · {x : G ⧸ H | τ • x = x}.ncard`
  count that `ncard_degreeOne_primesOver_under` needs),
  `FLTForHuman/FieldTheory/FiniteGroupAction.lean`'s
  `MulAction.ncard_orbit_inter_orbit_mul_card` and
  `Subgroup.exists_eq_mul_of_index_inf_eq`, and
  `FLTForHuman/AlgebraicCurve/WeilExchange/Bifibre.lean`'s place-orbit layer
  (`orbit_gal_eq`, `orbit_range_resHom_eq`, `index_range_resHom`,
  `card_range_resHom`). `#check` these against `MulAction.stabilizer` /
  `QuotientGroup` before transcribing the pin's private coset helpers. (The
  SL(2,ℤ)-specific coset ports — PhiGen's `ModularCurve/Defs/PrimCosetReps.lean` and
  the Hecke port's `ModularCurve/Analytic/Gamma0Cosets.lean` — are already consumed
  by H2/S2 and are not relevant to these Galois cosets.)
- Import the ported `NumberTheory/{ValuationAtPlace,FrobeniusAtPlace}.lean`
  (`ValuationSubring.exists_isFrobeniusAt_*` family already exists there) and extend,
  not duplicate.
- **S7-II is the risk** (1,937 lines of `tsum`/`IsBigO`/`ZMod` analysis). The pin's
  `p2m_*`/`P2M.Util` scaffolding is not ported; record a negative for any mathlib
  search that finds nothing, and stop rather than weaken a statement.
- Keep helpers `private`.

## 3. Verification, build discipline, closing

Per dispatch, as `WORKORDER-S1-eisenstein.md` §4: checker wiring appended last; edit
loop `timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
file-done `flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.<Dotted.Path>`;
one build per module; no bare whole-tree `lake build`; no `sorry`/`admit`/`axiom`;
no `import Mathlib`; `#print axioms` clean; friction log appended; no writing git
commands. A module is closed only when it builds green and the checker is 0/0.

---

## Appendix — per-file pin declaration inventory

### S7-I — 8 nodes

#### `ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem` — pin `S_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem.lean` (149 lines, 12 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `IsLoc` | def | 17 | 5 | yes |
| `coe_ne_zero_of_notMem` | theorem | 22 | 10 | yes |
| `coe_mem` | theorem | 32 | 3 | yes |
| `ψ` | def | 35 | 6 | yes |
| `isUnit_ψ` | theorem | 41 | 5 | yes |
| `ψ_mem_maximalIdeal` | theorem | 46 | 21 | yes |
| `liesOverPrime` | theorem | 67 | 14 | yes |
| `smul_mem` | theorem | 81 | 10 | yes |
| `mem_decompositionSubgroup` | theorem | 91 | 9 | yes |
| `smul_ψ` | theorem | 100 | 4 | yes |
| `smul_residue` | theorem | 104 | 34 | yes |
| `solution` | theorem | 138 | 12 |  |

#### `ValuationSubring.exists_liesOverPrime_algebraicClosure_rat` — pin `S_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat.lean` (33 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 6 | 28 |  |

#### `ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat` — pin `S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat.lean` (13 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 9 | 5 |  |

#### `ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure` — pin `S_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure.lean` (16 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 10 | 7 |  |

#### `NumberField.exists_valuationSubring_eq_localization` — pin `S_NumberField_exists_valuationSubring_eq_localization.lean` (109 lines, 8 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `carrier` | def | 20 | 3 |  |
| `mem_carrier` | theorem | 23 | 2 |  |
| `one_notMem` | theorem | 25 | 2 |  |
| `subring` | def | 27 | 20 |  |
| `comap_ne_bot` | theorem | 47 | 14 |  |
| `mem_or_inv_mem` | theorem | 61 | 38 |  |
| `valuationSubring` | def | 99 | 6 |  |
| `solution` | theorem | 105 | 5 |  |

#### `NumberField.exists_isFrobenius_lift_arithFrobAt` — pin `S_NumberField_exists_isFrobenius_lift_arithFrobAt.lean` (240 lines, 2 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `restrictNormal_restrictScalars` | theorem | 70 | 17 |  |
| `solution` | theorem | 87 | 154 |  |

#### `IsOpen.exists_numberField_ker_restrictNormalHom_le` — pin `S_IsOpen_exists_numberField_ker_restrictNormalHom_le.lean` (68 lines, 3 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `exists_numberField_ker_restrictNormalHom_le` | theorem | 10 | 37 |  |
| `exists_finiteDimensional_fixingSubgroup_le` | theorem | 47 | 12 |  |
| `solution` | theorem | 59 | 10 |  |

#### `CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int` — pin `S_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int.lean` (190 lines, 8 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `exists_int_ne_zero_eq_mul` | theorem | 13 | 28 |  |
| `charZero_fractionRing` | theorem | 41 | 3 |  |
| `finiteDimensional_fractionRing` | theorem | 44 | 48 |  |
| `numberField_fractionRing` | theorem | 92 | 11 |  |
| `nonempty_ringHom_zmod` | theorem | 103 | 17 |  |
| `tendsto_log_sub_one` | theorem | 120 | 11 |  |
| `infinite_setOf_degOneCount_ne_zero` | theorem | 131 | 32 |  |
| `solution` | theorem | 163 | 28 |  |

### S7-II — 13 nodes

#### `ArithmeticFunction.sum_moebius_filter_dvd` — pin `S_ArithmeticFunction_sum_moebius_filter_dvd.lean` (36 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 8 | 29 |  |

#### `FrobeniusDensity.sum_moebius_mul_pos` — pin `S_FrobeniusDensity_sum_moebius_mul_pos.lean` (182 lines, 7 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `mem_zpowers_pow_div_iff` | theorem | 22 | 30 | yes |
| `sum_moebius_mem_zpowers` | theorem | 52 | 39 | yes |
| `exists_pow_coprime_eq_of_orderOf_eq` | theorem | 91 | 19 | yes |
| `orderOf_pow_orderOf_div` | theorem | 110 | 8 | yes |
| `ncard_conj_mem_eq_card_mul_ncard` | theorem | 118 | 16 | yes |
| `ncard_eq_sum_indicator` | theorem | 134 | 14 | yes |
| `solution` | theorem | 148 | 35 |  |

#### `FrobeniusDensity.weight_eq` — pin `S_FrobeniusDensity_weight_eq.lean` (199 lines, 7 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `mem_zpowers_pow_div_iff` | theorem | 21 | 30 | yes |
| `sum_moebius_mem_zpowers` | theorem | 51 | 39 | yes |
| `exists_pow_coprime_eq_of_orderOf_eq` | theorem | 90 | 19 | yes |
| `orderOf_pow_orderOf_div` | theorem | 109 | 8 | yes |
| `ncard_conj_mem_eq_card_mul_ncard` | theorem | 117 | 16 | yes |
| `ncard_eq_sum_indicator` | theorem | 133 | 14 | yes |
| `solution` | theorem | 147 | 53 |  |

#### `FrobeniusDensity.idealSum_ne_top` — pin `S_FrobeniusDensity_idealSum_ne_top.lean` (129 lines, 12 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `zetaTerm_nonneg` | lemma | 17 | 6 |  |
| `tendsto_sum_idealCount_div` | lemma | 23 | 15 | yes |
| `isBigO_sum_of_tendsto_div` | lemma | 38 | 20 | yes |
| `LSeriesSummable_idealCount` | lemma | 58 | 6 | yes |
| `term_eq_ofReal_zetaTerm` | lemma | 64 | 9 | yes |
| `summable_zetaTerm` | lemma | 73 | 6 | yes |
| `NormFiber` | def | 79 | 3 | yes |
| `normFiberEquiv` | def | 82 | 7 | yes |
| `tsum_normFiber` | lemma | 89 | 22 | yes |
| `tsum_equiv'` | lemma | 111 | 5 | yes |
| `idealSum_eq_tsum_zetaTerm` | lemma | 116 | 8 | yes |
| `solution` | theorem | 124 | 6 |  |

#### `FrobeniusDensity.tendsto_sub_one_mul_idealSum_test` — pin `S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean` (148 lines, 14 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `zetaTerm_nonneg` | lemma | 18 | 6 |  |
| `tendsto_sum_idealCount_div` | lemma | 24 | 15 | yes |
| `isBigO_sum_of_tendsto_div` | lemma | 39 | 20 | yes |
| `LSeriesSummable_idealCount` | lemma | 59 | 6 | yes |
| `term_eq_ofReal_zetaTerm` | lemma | 65 | 9 | yes |
| `summable_zetaTerm` | lemma | 74 | 6 | yes |
| `NormFiber` | def | 80 | 3 | yes |
| `normFiberEquiv` | def | 83 | 7 | yes |
| `tsum_normFiber` | lemma | 90 | 22 | yes |
| `tsum_equiv'` | lemma | 112 | 5 | yes |
| `idealSum_eq_tsum_zetaTerm` | lemma | 117 | 6 | yes |
| `dedekindZeta_eq_ofReal_tsum` | lemma | 123 | 5 | yes |
| `idealSum_toReal_eq` | lemma | 128 | 11 | yes |
| `solution` | theorem | 139 | 10 |  |

#### `FrobeniusDensity.summable_degOne_term` — pin `S_FrobeniusDensity_summable_degOne_term.lean` (46 lines, 4 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `primeSum_le_idealSum` | lemma | 18 | 7 | yes |
| `degOneSum_ne_top` | lemma | 25 | 8 | yes |
| `toReal_term` | theorem | 33 | 10 | yes |
| `solution` | theorem | 43 | 4 |  |

#### `FrobeniusDensity.ncard_degreeOne_primesOver_under` — pin `S_FrobeniusDensity_ncard_degreeOne_primesOver_under.lean` (246 lines, 16 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `inertia_smul_eq_bot` | theorem | 24 | 16 | yes |
| `under_smul_of_mem` | theorem | 40 | 7 | yes |
| `isArithFrobAt_coe_of_card_eq` | theorem | 47 | 9 | yes |
| `exists_isArithFrobAt_mem` | theorem | 56 | 7 | yes |
| `mem_of_isArithFrobAt_of_card_eq` | theorem | 63 | 11 | yes |
| `le_card_quotient_under` | theorem | 74 | 13 | yes |
| `card_le_of_forall_pow_eq` | theorem | 87 | 12 | yes |
| `exists_isArithFrobAt'` | theorem | 99 | 5 | yes |
| `card_under_eq_of_stabilizer_le` | theorem | 104 | 23 | yes |
| `stabilizer_le_of_card_under_eq` | theorem | 127 | 12 | yes |
| `restrictPrime` | def | 139 | 7 | yes |
| `restrictPrime_mk` | theorem | 146 | 3 | yes |
| `mem_stabilizer_inv_smul_iff` | theorem | 149 | 7 | yes |
| `forall_smul_eq_iff_stabilizer_le` | theorem | 156 | 18 | yes |
| `exists_mem_smul_eq_of_under_eq` | theorem | 174 | 12 | yes |
| `solution` | theorem | 186 | 61 |  |

#### `FrobeniusDensity.ncard_degreeOne_primesOver_eq_ncard_frobFixed` — pin `S_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed.lean` (44 lines, 2 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `forall_mem_zpowers_smul_eq_iff` | theorem | 16 | 9 | yes |
| `solution` | theorem | 25 | 20 |  |

#### `FrobeniusDensity.stabilizer_eq_zpowers_arithFrobAt` — pin `S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt.lean` (122 lines, 5 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `card_le_of_forall_pow_eq` | theorem | 21 | 14 | yes |
| `IsArithFrobAt.mk_pow_smul'` | theorem | 35 | 14 | yes |
| `IsArithFrobAt.card_quotient_le_pow'` | theorem | 49 | 18 | yes |
| `isSeparable_residue'` | theorem | 67 | 18 | yes |
| `solution` | theorem | 85 | 38 |  |

#### `FrobeniusDensity.primeSum_eq_degOneSum_add` — pin `S_FrobeniusDensity_primeSum_eq_degOneSum_add.lean` (103 lines, 7 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `PrimeNormFiber` | def | 16 | 3 | yes |
| `primeNormFiberEquiv` | def | 19 | 14 | yes |
| `liesOver_of_absNorm_eq` | theorem | 33 | 7 | yes |
| `natCard_primeNormFiber` | theorem | 40 | 14 | yes |
| `tsum_reindex` | lemma | 54 | 5 | yes |
| `tsum_degOne_eq` | theorem | 59 | 26 | yes |
| `solution` | theorem | 85 | 19 |  |

#### `FrobeniusDensity.primeSum_toReal_add_log_isBigO` — pin `S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean` (474 lines, 48 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `tsum_equiv` | lemma | 20 | 9 | yes |
| `two_le_absNorm` | lemma | 29 | 5 |  |
| `one_le_cast_absNorm` | lemma | 34 | 4 |  |
| `normRpow_le_one` | lemma | 38 | 5 |  |
| `normRpow_ne_top` | lemma | 43 | 3 |  |
| `normRpow_pos` | lemma | 46 | 3 |  |
| `one_lt_cast_absNorm` | lemma | 49 | 4 |  |
| `normRpow_lt_one` | lemma | 53 | 4 |  |
| `normRpow_top` | lemma | 57 | 3 |  |
| `normRpow_mul` | lemma | 60 | 5 |  |
| `normRpow_pow` | lemma | 65 | 9 |  |
| `mem_primeFactors` | lemma | 74 | 4 |  |
| `isFactoredBy_primeFactors` | lemma | 78 | 6 |  |
| `_root_.FrobeniusDensity.IsFactoredBy.mono` | lemma | 84 | 7 | yes |
| `isFactoredBy_top` | lemma | 91 | 5 |  |
| `eq_top_of_isFactoredBy_empty` | lemma | 96 | 14 |  |
| `consFactored` | def | 110 | 12 |  |
| `consFactored_injective` | lemma | 122 | 19 |  |
| `consFactored_surjective` | lemma | 141 | 15 |  |
| `consFactoredEquiv` | def | 156 | 6 |  |
| `factoredSum_empty` | lemma | 162 | 8 |  |
| `factoredSum_cons` | lemma | 170 | 27 |  |
| `factoredSum_eq_prod` | lemma | 197 | 6 |  |
| `factoredSum_le_idealSum` | lemma | 203 | 10 |  |
| `idealSum_eq_iSup_factoredSum` | lemma | 213 | 27 |  |
| `primeSum_le_idealSum` | lemma | 240 | 6 |  |
| `primeSqSum_le_idealSum_two` | lemma | 246 | 9 |  |
| `one_le_idealSum` | lemma | 255 | 5 |  |
| `one_le_factoredSum` | lemma | 260 | 6 |  |
| `factoredSum_toReal_pos` | lemma | 266 | 5 |  |
| `primeSum_ne_top` | lemma | 271 | 3 |  |
| `idealSum_toReal_pos` | lemma | 274 | 4 |  |
| `one_le_idealSum_toReal` | lemma | 278 | 8 |  |
| `le_neg_log_one_sub` | lemma | 286 | 4 |  |
| `neg_log_one_sub_le` | lemma | 290 | 20 |  |
| `normRpow_toReal_nonneg` | lemma | 310 | 3 |  |
| `normRpow_toReal_le_half` | lemma | 313 | 16 |  |
| `normRpow_toReal_lt_one` | lemma | 329 | 4 |  |
| `toReal_eulerFactor` | lemma | 333 | 6 |  |
| `one_sub_normRpow_toReal_pos` | lemma | 339 | 4 |  |
| `log_factoredSum_toReal` | lemma | 343 | 10 |  |
| `sum_normRpow_toReal_le` | lemma | 353 | 9 |  |
| `sum_normRpow_sq_toReal_le` | lemma | 362 | 20 |  |
| `primeSum_toReal_le_log_idealSum` | theorem | 382 | 15 |  |
| `log_idealSum_le_primeSum_toReal` | theorem | 397 | 42 |  |
| `log_idealSum_add_log_isBigO` | lemma | 439 | 12 | yes |
| `primeSum_sub_log_idealSum_isBigO` | lemma | 451 | 19 | yes |
| `solution` | theorem | 470 | 5 |  |

#### `FrobeniusDensity.degOneSum_add_log_isBigO` — pin `S_FrobeniusDensity_degOneSum_add_log_isBigO.lean` (292 lines, 24 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `one_le_cast_absNorm` | lemma | 21 | 5 |  |
| `primeSum_le_idealSum` | lemma | 26 | 7 | yes |
| `primeSum_ne_top` | lemma | 33 | 3 | yes |
| `degOneSum_ne_top` | lemma | 36 | 7 | yes |
| `cutSum_ne_top` | lemma | 43 | 6 | yes |
| `tailSum_ne_top` | lemma | 49 | 6 | yes |
| `tailConst_ne_top` | theorem | 55 | 20 | yes |
| `absNorm_eq_pow_inertiaDeg_ratBelow` | theorem | 75 | 5 | yes |
| `sq_ratBelow_le_absNorm` | theorem | 80 | 15 | yes |
| `RatBelowFiber` | def | 95 | 3 | yes |
| `liesOver_of_ratBelow_eq` | theorem | 98 | 4 | yes |
| `ratBelowFiberEquiv` | def | 102 | 7 | yes |
| `isEmpty_ratBelowFiber` | theorem | 109 | 18 | yes |
| `natCard_ratBelowFiber_le` | theorem | 127 | 13 | yes |
| `tsum_reindex'` | lemma | 140 | 5 | yes |
| `tailSum_le` | theorem | 145 | 48 | yes |
| `cutSum_le` | theorem | 193 | 23 | yes |
| `sum_degOneCount_ne_top` | theorem | 216 | 5 | yes |
| `toReal_term` | theorem | 221 | 7 | yes |
| `term_ne_top` | theorem | 228 | 10 | yes |
| `degOneSum_toReal_eq` | theorem | 238 | 6 | yes |
| `tailSum_toReal_isBigO` | theorem | 244 | 12 | yes |
| `cutSum_toReal_isBigO` | theorem | 256 | 16 | yes |
| `solution` | theorem | 272 | 21 |  |

#### `FrobeniusDensity.degOneAsymptotic` — pin `S_FrobeniusDensity_degOneAsymptotic.lean` (16 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 11 | 6 |  |

### S7-III — 6 nodes

#### `FrobeniusDensity.statement_of_degOneAsymptotic` — pin `S_FrobeniusDensity_statement_of_degOneAsymptotic.lean` (165 lines, 3 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `tendsto_log_sub_one` | theorem | 20 | 8 | yes |
| `not_isBigO_one_of_tendsto_atBot` | theorem | 28 | 17 | yes |
| `solution` | theorem | 45 | 121 |  |

#### `FrobeniusDensity.statement` — pin `S_FrobeniusDensity_statement.lean` (12 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 10 | 3 |  |

#### `FrobeniusDensity.exists_frobenius_conj_pow_of_statement` — pin `S_FrobeniusDensity_exists_frobenius_conj_pow_of_statement.lean` (105 lines, 4 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `galoisLevel` | abbrev | 27 | 7 |  |
| `le_galoisLevel` | theorem | 34 | 4 |  |
| `exists_pow_pow_eq` | theorem | 38 | 17 |  |
| `solution` | theorem | 55 | 51 |  |

#### `FrobeniusDensity.frobeniusPowerDense_of_le_ker` — pin `S_FrobeniusDensity_frobeniusPowerDense_of_le_ker.lean` (47 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 12 | 36 |  |

#### `FrobeniusDensity.ncard_conj_gen_ne_zero_iff` — pin `S_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.lean` (17 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 8 | 10 |  |

#### `Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen` — pin `S_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen.lean` (28 lines, 1 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `solution` | theorem | 10 | 19 |  |
