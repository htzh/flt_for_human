# Ribet's level lowering in the FLT proof

This note is the sequel to [note 007](007-modularity-and-computation.md)
(modularity, computed) and [note 004](004-irreducible-and-cofixed-line.md)
(irreducibility of $`E_P[p]`$). Modularity attaches a weight-2 eigenform to the
Frey curve at some level; irreducibility makes the residual representation
$`\bar\rho_{E_P,p}`$ a genuine two-dimensional object. **Level lowering** is what
turns those two facts into a contradiction: it strips the level down to
$`\Gamma_0(2)`$, where there are no nonzero cusp forms at all.

The Lean chain is short to state and deep to prove. The statement lives in
[`Theorems/Thm_FreyPackage_level_lowering_to_two.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_to_two.lean#L131):

```lean
theorem FreyPackage.level_lowering_to_two (P : FreyPackage) (hmod : P.freyCurve.IsModular)
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 2) 2, f ≠ 0
```

and it is assembled from `P.modularRepOfConductorLevel`,
`P.level_lowering_to_two_of_conductorLevel` and
`ModularForm.S2_Gamma0_2_eq_zero`. Line numbers refer to
`anthropics/fermats-last-theorem@aa2d8b3` (main, 2026-09-03).

## 1. The shape of the statement

Everything is phrased residually. The objects are not representations but
*congruences of Fourier coefficients modulo a maximal ideal* $`\mathfrak{m}`$
above $`p`$ in the integral closure of $`\mathbb{Z}`$ in $`\mathbb{C}`$. From
[Def_FLTPrelim_ModularRep.lean, lines 62–69](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_ModularRep.lean#L62-L69):

```lean
def ModularRepOfLevel (P : FreyPackage) (N : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
      (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪
```

That is: there is a level-$`N`$ normalised eigenform $`f`$, an integral model
$`W`$ of the Frey curve, and a maximal ideal $`\mathfrak{m} \ni p`$ such that
$`a_\ell(f) \equiv a_\ell(W) \pmod{\mathfrak{m}}`$ for every good prime
$`\ell \nmid N`$, $`\ell \neq p`$. This is *not* an isomorphism of
representations and not even an equality of coefficients: it is exactly the
residual congruence that Ribet's theorem produces. The theorem used for the
level-$`N`$ version, with the conductor level built in, is
`FreyPackage.level_lowering_to_two_of_conductorLevel`
([line 91](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_to_two_of_conductorLevel.lean#L91)):

```lean
theorem FreyPackage.level_lowering_to_two_of_conductorLevel (P : FreyPackage)
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) {N : ℕ}
    (hcond : P.IsConductorLevel N) (hmod : P.ModularRepOfLevel N) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 2) 2, f ≠ 0
```

The extra hypothesis `hcond : P.IsConductorLevel N` is the whole point of §2: it
says the level is **squarefree** and supported on the primes of $`abc`$. That is
what makes the one-prime-at-a-time stripping of §4 possible.

## 2. Step zero: the conductor level is squarefree

From [Def_FreyPackage_IsConductorLevel.lean, lines 8–14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_IsConductorLevel.lean#L8-L14):

```lean
structure IsConductorLevel (P : FreyPackage) (N : ℕ) : Prop where
  pos : 0 < N
  squarefree : Squarefree N
  support : ∀ q : ℕ, q.Prime → q ∣ N → (q : ℤ) ∣ P.a * P.b * P.c
```

For the Frey curve this is not an extra assumption; it is forced by semistability.
The relevant facts are

```lean
theorem FreyPackage.dvd_freyCurveInt_discr_iff (P : FreyPackage) {q : ℕ} (hq : q.Prime) :
    (q : ℤ) ∣ P.freyCurveInt.Δ ↔ (q : ℤ) ∣ P.a * P.b * P.c

theorem FreyPackage.not_dvd_freyCurveInt_c4 (P : FreyPackage) {q : ℕ} (hq : q.Prime)
    (hqabc : (q : ℤ) ∣ P.a * P.b * P.c) : ¬ (q : ℤ) ∣ P.freyCurveInt.c₄

theorem FreyPackage.frey_isSemistableModel (P : FreyPackage) : P.freyCurveInt.IsSemistableModel
```

([dvd_freyCurveInt_discr_iff](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_dvd_freyCurveInt_discr_iff.lean#L6-L7),
[not_dvd_freyCurveInt_c4](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_not_dvd_freyCurveInt_c4.lean#L6-L7),
[frey_isSemistableModel](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_frey_isSemistableModel.lean#L8)).
The first says the bad primes are exactly the primes of $`abc`$; the second says
none of them divides $`c_4`$, which is semistability; the third packages it.

The formalisation then *derives* the conductor level from modularity, rather than
assuming it. `FreyPackage.modularRepOfConductorLevel`
([line 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_modularRepOfConductorLevel.lean#L131)):

```lean
theorem FreyPackage.modularRepOfConductorLevel (P : FreyPackage) :
    ∃ N : ℕ, P.IsConductorLevel N ∧ P.ModularRepOfLevel N
```

Its proof does not use `P.freyCurve.IsModular` at all. It goes through the
lifting theorems at $`p = 3, 5`$ to obtain
`Mlc1IsModularModelOfExactConductorLevel`
([Def_WeierstrassCurve_Mlc1RowStatement.lean, lines 9–11](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_Mlc1RowStatement.lean#L9-L11)):

```lean
def Mlc1IsModularModelOfExactConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ Squarefree N ∧
    (∀ q : ℕ, q.Prime → (q ∣ N ↔ (q : ℤ) ∣ W.Δ)) ∧
    W.IsModularModelOfLevel N
```

i.e. a squarefree level whose prime support is *exactly* the primes of $`\Delta`$,
with modularity at that level. So the level used downstream is
$`\mathrm{rad}(\Delta) = \mathrm{rad}(abc)`$. This is the sense in which
"the conductor is squarefree due to semistability": every bad prime is
multiplicative, so its conductor exponent is $`1`$ (see
[note 007 §3–4](007-modularity-and-computation.md)), and the true conductor and
the radical agree.

## 3. Where the Fermat exponent enters: $`v_q(\Delta) = 2p`$

The second thing that makes the Frey case work is that the discriminant's
valuation at a bad prime is *divisible by $`p`$*. The identity is
([S_FreyPackage_freyGaloisRep_isUnramifiedAt.lean, lines 104–105](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_FreyPackage_freyGaloisRep_isUnramifiedAt.lean#L104-L105))

$$\\Delta \\cdot 2^8 = (abc)^{2p},$$

which is the arithmetic content of $`\Delta = (abc)^{2p}/2^8`$ from
[note 002](002-frey-curve-model-and-discriminant.md). Taking valuations gives the
two theorems
([odd q](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_padicValInt_freyCurveInt_discr.lean#L6-L7),
[q = 2](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_padicValInt_two_freyCurveInt_discr.lean#L6-L7)):

```lean
theorem FreyPackage.padicValInt_freyCurveInt_discr (P : FreyPackage) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) :
    padicValInt q P.freyCurveInt.Δ = 2 * P.p * padicValInt q (P.a * P.b * P.c)

theorem FreyPackage.padicValInt_two_freyCurveInt_discr (P : FreyPackage) :
    padicValInt 2 P.freyCurveInt.Δ + 8 = 2 * P.p * padicValInt 2 (P.a * P.b * P.c)
```

A Frey package has $`\gcd(a,b) = \gcd(a,c) = \gcd(b,c) = 1`$ (`hgcdab`,
`hgcdac`, `hgcdbc`), so for a prime $`q \mid abc`$ the valuation
$`v_q(abc)`$ is $`1`$, and therefore

$$v_q(\\Delta) = 2p \\qquad (q \\neq 2,\\ q \\mid abc).$$

For $`q = 2`$ the extra $`2^8`$ shifts things, but $`p \mid v_2(\Delta) + 8`$, and
what matters below is only divisibility by $`p`$.

**Why divisibility by $`p`$ is the condition.** For a curve with multiplicative
reduction at $`q`$, the mod-$`p`$ representation is unramified at $`q`$ exactly
when $`p`$ divides the valuation of the discriminant. In Lean
([Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_multiplicativeReduction.lean, lines 12–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_multiplicativeReduction.lean#L12-L18)):

```lean
theorem WeierstrassCurve.galoisRepUnramifiedAt_of_multiplicativeReduction (W : WeierstrassCurve ℤ)
    {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) (hv : ℓ ∣ padicValInt q W.Δ) :
    GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) ℓ q
```

The intuition is the Tate curve: near $`q`$ the curve is
$`\mathbb{G}_m / \langle q_T \rangle`$ with $`q_T`$ of valuation
$`v_q(\Delta)`$. Its $`p`$-torsion is generated by a $`p`$-th root of unity
$`\zeta_p`$ together with $`q_T^{1/p}`$; the cyclotomic part is unramified at
$`q \neq p`$, and $`q_T^{1/p}`$ requires adjoining a $`p`$-th root of
$`q_T`$, which is unramified precisely when
$`p \mid v_q(q_T) = v_q(\Delta)`$. This is where "$`p`$ is a condition" enters the
Frey argument: $`v_q(\Delta) = 2p`$ is divisible by $`p`$, so
$`\bar\rho_{E_P,p}`$ is unramified at every odd $`q \mid abc`$ with
$`q \neq p`$. In Lean this is
[`FreyPackage.freyGaloisRep_isUnramifiedAt`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_freyGaloisRep_isUnramifiedAt.lean#L15):

```lean
theorem FreyPackage.freyGaloisRep_isUnramifiedAt (P : FreyPackage) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ P.p) : P.GaloisRepUnramifiedAt q
```

At the prime $`p`$ itself the same divisibility statement is named
"peu ramifiée"
([Def_WeierstrassCurve_PeuRamifiee.lean, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_PeuRamifiee.lean#L10)):

```lean
def IsPeuRamifieeAt (W : WeierstrassCurve ℚ) (p ℓ : ℕ) : Prop :=
  (p : ℤ) ∣ padicValRat ℓ W.Δ
```

## 4. The mechanism: strip one prime at a time

The headline theorem is proved by strong induction on the level. The skeleton of
[S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean, lines 113–148](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean#L113-L148),
abridged:

```lean
private theorem FreyPackage.exists_modularRepOfLevel_dvd_two_of_conductorLevel₁₆ (P : FreyPackage)
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) :
    ∀ N : ℕ, P.IsConductorLevel N → P.ModularRepOfLevel N →
      ∃ M : ℕ, 0 < M ∧ M ∣ 2 ∧ P.ModularRepOfLevel M := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hcond hmod
    by_cases hodd : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ≠ P.p ∧ q ∣ N
    ·
      obtain ⟨q, hq, hq2, hqp, hqN⟩ := hodd
      obtain ⟨M, hMN, hqM, hmodM⟩ :=
        P.level_lowering_odd_prime_of_conductorLevel hcond hq hq2 hqp hqN hirr hmod
          (P.freyGaloisRep_isUnramifiedAt hq hq2 hqp)
      ...
      exact ih M hMlt (hcond.of_dvd hMN hM0) hmodM
    · by_cases hpN : P.p ∣ N
      ·
        obtain ⟨M, hMN, hpM, hmodM⟩ := P.level_lowering_at_p_of_conductorLevel hcond hpN hirr hmod
        ...
        exact ih M hMlt (hcond.of_dvd hMN hM0) hmodM
      ·
        refine ⟨N, hcond.pos,
          dvd_two_of_squarefree_of_forall_prime_eq_two₁₆ hcond.squarefree ?_, hmod⟩
        intro q hq hqN
        by_contra hq2
        rcases eq_or_ne q P.p with rfl | hqp
        · exact hpN hqN
        · exact hodd ⟨q, hq, hq2, hqp, hqN⟩
```

The three cases are exactly the three possibilities for a prime dividing the
squarefree $`N`$:

1. an **odd** $`q \neq p`$: $`\bar\rho`$ is unramified at $`q`$ by §3, and Ribet's
   theorem removes it;
2. the prime **$`p`$**: removed by the $`p`$-adic step;
3. otherwise $`N`$ has no prime except possibly $`2`$, and since $`N`$ is
   squarefree, $`N \mid 2`$.

Each removal divides the level by a prime and therefore strictly decreases it, so
the strong induction terminates. The squarefree hypothesis is what lets a single
prime be removed cleanly: the theorem needs $`q \parallel M`$, i.e.
$`q \mid M`$ but $`q^2 \nmid M`$, which is `hcond.sq_not_dvd hq`.

### 4.1 Removing an odd $`q \neq p`$

The workhorse is
[`WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf.lean#L87-L99):

```lean
theorem WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf
    (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (_hΔ : W.Δ ≠ 0)
    (_hW : W.IsSemistableModel)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (_hirr : W.ModRepIsIrreducible p) (M q : ℕ) (hq : q.Prime) (hqp : q ≠ p)
    (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M) (hM : Squarefree M)
    (hunr : ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q)
    (hres : W.IsResiduallyModularOfLevel p M) :
    W.IsResiduallyModularOfLevel p (M / q)
```

This is Ribet's theorem in the form the argument needs: **if $`\bar\rho`$ is
residually modular at level $`M`$, $`q \parallel M`$, and $`\bar\rho`$ is
unramified at $`q`$, then $`\bar\rho`$ is residually modular at level
$`M/q`$.** Its proof splits into two cases on the residue of $`q`$ mod $`p`$:

- $`q \equiv 1 \pmod p`$:
  `isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf` — the
  case where the cyclotomic character is trivial at $`q`$, handled by the
  character-group / Eisenstein analysis;
- $`q \not\equiv 1 \pmod p`$:
  `R1ResModDivSqf.isResiduallyModularOfLevel_div_of_cast_ne_one_of_isUnramifiedAt`,
  which goes through
  [`ModularCurve.isResiduallyModularOfLevel_div_of_mazurFamilies`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_isResiduallyModularOfLevel_div_of_mazurFamilies.lean#L22-L59).

The geometric content sits in that last theorem. Its two big hypotheses are a
**Mazur realization family** and a **toric dichotomy**:

- *Mazur realization family*: for every level $`N`$ with $`q \nmid N`$ at which
  $`\bar\rho`$ is residually modular of level $`Nq`$, there is a maximal ideal
  $`\mathfrak{m}`$ (not "eventually Eisenstein") and a two-dimensional
  Galois-stable subspace $`V`$ of the $`p`$-torsion of the Jacobian
  $`J_0(Nq)`$, with inertia at $`q`$ acting trivially and Frobenius acting with
  determinant $`q`$. This is supplied by
  `ModularCurve.mazurRealizationFamily_of_modRepIsIrreducible_of_isUnramifiedAt`,
  using irreducibility and unramifiedness.
- *Toric dichotomy*: for every such $`\mathfrak{m}`$, every inertia-fixed element
  of the $`\mathfrak{m}`$-torsion of $`J_0(Nq)`$ either lies in a "toric"
  subspace or already exhibits **lower-level torsion** in $`J_0(N)`$
  ([`HasLowerLevelTorsion`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_MazurPrincipleCore.lean#L61-L66),
  [`IsToricDichotomyQGuarded`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ToricDichotomyData.lean#L15-L20)).
  This is supplied by
  [`ModularCurve.exists_toricDichotomyData_jZero`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_toricDichotomyData_jZero.lean#L45-L54),
  whose input is the geometry of the special fibre of $`X_0(Nq)`$ at $`q`$ — the
  Deligne–Rapoport description of the $`q`$-old part, with the $`q`$-new part
  uniformised by the torus (Čerednik–Drinfeld; PROOF-PATH.md records this step as
  "Ribet's theorem in the form needed (Čerednik-Drinfeld uniformisation,
  `CerednikDrinfeld` namespace)").

The classical reading of the two hypotheses is the $`q`$-old / $`q`$-new
decomposition: a residual representation that is unramified at $`q`$ cannot live
in the $`q`$-new part (where the $`q`$-adic uniformisation puts the ramification),
so it must come from the $`q`$-old part, i.e. from level $`N`$. The formalisation
splits the two possibilities as "the torsion point is toric" (the $`q`$-new side,
handled by the Frobenius-determinant computation) and "lower-level torsion
exists" (the $`q`$-old side, which is precisely the conclusion).

### 4.2 Removing $`p`$

At $`p`$ the same Tate-curve divisibility holds, but the geometric statement is
different because $`X_0(Np)`$ has bad reduction at $`p`$. The Lean interface is
`AtPNewLowering` ([Def_FreyPackage_AtPNewLowering.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_AtPNewLowering.lean#L18-L23)):

```lean
def AtPNewLowering (P : FreyPackage) : Prop :=
  ∀ N₀ : ℕ, 0 < N₀ → ¬ P.p ∣ N₀ →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.freyCurve.IsPeuRamifieeAt P.p P.p →
    P.ModularRepOfLevelNewAt (N₀ * P.p) P.p →
    P.ModularRepOfLevel N₀
```

and it is proved in `FreyPackage.atPNewLowering` from the uniform version
`atPNewLoweringAtUniform` plus `modularRepOfLevelNewAtPinned_of_newAt`, i.e. by
passing to the *new* part at $`p`$ and then descending. The wrapper is
`FreyPackage.level_lowering_at_p_of_conductorLevel`
([line 70](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_at_p_of_conductorLevel.lean#L70)):

```lean
theorem FreyPackage.level_lowering_at_p_of_conductorLevel (P : FreyPackage) {N : ℕ}
    (hcond : P.IsConductorLevel N) (hpN : P.p ∣ N)
    (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p)
    (hmod : P.ModularRepOfLevel N) :
    ∃ M : ℕ, M ∣ N ∧ ¬ P.p ∣ M ∧ P.ModularRepOfLevel M
```

and its proof supplies `P.freyCurve.IsPeuRamifieeAt P.p P.p` from
`FreyCurve.isPeuRamifieeAt_odd_of_integralForm` — again, from
$`p \mid v_p(\Delta)`$. PROOF-PATH.md calls this "the Mazur-Ribet step, using
that $`E_P[p]`$ is finite at $`p`$".

## 5. The endgame: $`\dim S_2(\Gamma_0(2)) = 0`$

Once the level has been reduced to a divisor $`M`$ of $`2`$, the representation
produces a nonzero weight-2 cusp form on $`\Gamma_0(M)`$ with $`M \in \{1, 2\}`$,
and both spaces are zero. The interesting case is level 2
([Thm_ModularForm_S2_Gamma0_2_eq_zero.lean, line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean#L13)):

```lean
theorem ModularForm.S2_Gamma0_2_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0
```

The proof is self-contained and worth spelling out, because it shows how a
statement about level 2 is reduced to the classical vanishing below weight 12.
Three ingredients:

1. **The index is 3.**
   [`Gamma0_two_index_eq_three`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L170-L174):

   ```lean
   theorem Gamma0_two_index_eq_three : (CongruenceSubgroup.Gamma0 2).index = 3
   ```

   proved by exhibiting an explicit bijection between $`SL_2(\mathbb{Z})/\Gamma_0(2)`$
   and the three nonzero vectors in $`(\mathbb{Z}/2)^2`$ (the first column mod 2),
   which is injective because a matrix in $`\Gamma_0(2)`$ has first column
   $`\equiv (1,0)`$, and surjective by three explicit coset representatives.

2. **The norm multiplies the weight by the index.** For a subgroup of finite
   index, mathlib's `CuspForm.norm` is the product of the translates over the
   cosets and lands in weight $`k \cdot [\Gamma(1) : \Gamma_0(2)]`$
   ([NormTrace.lean, line 64](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L64)).
   For $`k = 2`$ and index $`3`$ this is weight $`6`$. Crucially,
   [`ModularForm.norm_eq_zero_iff`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L130-L131)
   says the norm vanishes if and only if the form does, so a nonzero level-2
   form would give a nonzero level-1 form of weight 6.

3. **There are no weight-6 cusp forms at level 1.** Mathlib's
   [`CuspForm.rank_eq_zero_of_weight_lt_twelve`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L153-L155)
   says $`S_k(\Gamma(1)) = 0`$ for $`k < 12`$ (the first cusp form is
   $`\Delta`$ in weight 12), and $`6 < 12`$. In Lean this is
   `S6_levelOne_eq_zero`.

Assembled
([lines 195–206](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L195-L206)):

```lean
theorem S2_Gamma0_2_eq_zero' (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0 := by
  have hweight : (2 : ℤ) * Nat.card ((↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) ⧸
      (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ)).subgroupOf
        (↑(CongruenceSubgroup.Gamma 1))) = 6 := by
    rw [card_quotient_eq_three]; norm_num
  have hf0 : (f : ℍ → ℂ) = 0 :=
    (CuspForm.norm_eq_zero_iff (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) f).1
      (S6_levelOne_eq_zero' hweight
        (CuspForm.norm (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) f))
  exact DFunLike.coe_injective (hf0.trans CuspForm.coe_zero.symm)
```

Level 1 is the same argument with $`k = 2 < 12`$ directly
([`ModularForm.S2_Gamma0_one_eq_zero`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_one_eq_zero.lean#L13)),
and the two are combined in
`ModularForm.S2_Gamma0_eq_zero_of_dvd_two`. This closes the Frey argument: the
level-lowered representation cannot exist, so there is no Frey package
(`FreyPackage.no_frey_package`), hence no counterexample to Fermat.

## 6. Key-point → code map

| Step | Lean definition / theorem | Location (pinned `aa2d8b3`) |
|---|---|---|
| conductor level | `FreyPackage.IsConductorLevel` | [Def_FreyPackage_IsConductorLevel.lean 8–14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_IsConductorLevel.lean#L8-L14) |
| bad primes of the Frey curve | `dvd_freyCurveInt_discr_iff` | [Thm 6–7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_dvd_freyCurveInt_discr_iff.lean#L6-L7) |
| semistability | `not_dvd_freyCurveInt_c4`, `frey_isSemistableModel` | [c₄](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_not_dvd_freyCurveInt_c4.lean#L6-L7), [semistable](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_frey_isSemistableModel.lean#L8) |
| exact conductor level | `Mlc1IsModularModelOfExactConductorLevel` | [Def 9–11](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_Mlc1RowStatement.lean#L9-L11) |
| modularity at conductor level | `FreyPackage.modularRepOfConductorLevel` | [Thm 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_modularRepOfConductorLevel.lean#L131) |
| $`\Delta \cdot 2^8 = (abc)^{2p}`$ | `freyCurveInt_Δ_mul` | [S 104–105](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_FreyPackage_freyGaloisRep_isUnramifiedAt.lean#L104-L105) |
| $`v_q(\Delta) = 2p\,v_q(abc)`$ | `padicValInt_freyCurveInt_discr` | [Thm 6–7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_padicValInt_freyCurveInt_discr.lean#L6-L7) |
| $`v_2(\Delta) + 8 = 2p\,v_2(abc)`$ | `padicValInt_two_freyCurveInt_discr` | [Thm 6–7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_padicValInt_two_freyCurveInt_discr.lean#L6-L7) |
| unramified from multiplicative reduction | `galoisRepUnramifiedAt_of_multiplicativeReduction` | [Thm 12–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_multiplicativeReduction.lean#L12-L18) |
| $`\bar\rho`$ unramified at odd $`q \neq p`$ | `FreyPackage.freyGaloisRep_isUnramifiedAt` | [Thm 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_freyGaloisRep_isUnramifiedAt.lean#L15) |
| "peu ramifiée" at $`p`$ | `IsPeuRamifieeAt` | [Def 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_PeuRamifiee.lean#L10) |
| residual modularity | `ModularRepOfLevel`, `IsResiduallyModularOfLevel` | [Def 62–80](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_ModularRep.lean#L62-L80) |
| Ribet, remove one prime | `isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf` | [Thm 87–99](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf.lean#L87-L99) |
| Mazur families + toric dichotomy | `isResiduallyModularOfLevel_div_of_mazurFamilies` | [Thm 22–59](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_isResiduallyModularOfLevel_div_of_mazurFamilies.lean#L22-L59) |
| toric dichotomy data | `exists_toricDichotomyData_jZero` | [Thm 45–54](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_toricDichotomyData_jZero.lean#L45-L54) |
| lower-level torsion | `HasLowerLevelTorsion`, `IsToricDichotomyQGuarded` | [MazurPrincipleCore 61–66](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_MazurPrincipleCore.lean#L61-L66), [ToricDichotomyData 15–20](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ToricDichotomyData.lean#L15-L20) |
| remove odd $`q`$ | `FreyPackage.level_lowering_odd_prime_of_conductorLevel` | [Thm 90](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_odd_prime_of_conductorLevel.lean#L90) |
| remove $`p`$ | `AtPNewLowering`, `FreyPackage.level_lowering_at_p_of_conductorLevel` | [Def 18–23](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_AtPNewLowering.lean#L18-L23), [Thm 70](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_at_p_of_conductorLevel.lean#L70) |
| one at a time | `exists_modularRepOfLevel_dvd_two_of_conductorLevel₁₆` | [S 113–148](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_FreyPackage_level_lowering_to_two_of_conductorLevel.lean#L113-L148) |
| level lowering to two | `FreyPackage.level_lowering_to_two` | [Thm 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_to_two.lean#L131) |
| index 3 | `Gamma0_two_index_eq_three` | [S 170–174](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L170-L174) |
| norm kills nothing | `ModularForm.norm_eq_zero_iff` | [mathlib NormTrace 130–131](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L130-L131) |
| weight $`< 12`$ vanishes | `CuspForm.rank_eq_zero_of_weight_lt_twelve` | [mathlib DimensionFormula 153–155](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean#L153-L155) |
| $`\dim S_2(\Gamma_0(2)) = 0`$ | `ModularForm.S2_Gamma0_2_eq_zero` | [Thm 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean#L13) |
| no Frey package | `FreyPackage.no_frey_package` | [Thm 129](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_no_frey_package.lean#L129) |

## 7. What is proved, and what is assumed

The statement being proved is **not** Ribet's theorem in general. PROOF-PATH.md is
explicit:

> **Ribet.** Proved: level lowering for the Frey representation at squarefree
> conductor-supported levels, as a congruence of traces. Not proved: Ribet's
> theorem for a general modular mod-p representation.

Three consequences for reading the Lean:

- The output is a **congruence of traces** mod a maximal ideal above $`p`$
  (`ModularRepOfLevel`), not an isomorphism of residual representations. This is
  weaker than the classical "level lowering gives
  $`\bar\rho_f \cong \bar\rho_g`$", and it is all the FLT argument uses.
- The level hypothesis is $`\mathrm{rad}(\Delta)`$ — squarefree and supported on
  the bad primes — not the true conductor. As [note 007 §4](007-modularity-and-computation.md)
  explains, for a semistable curve the two agree, so nothing is lost here.
- `modularRepOfConductorLevel` re-derives modularity from the lifting theorems, so
  the `IsModular` hypothesis is formally unused: the proof of
  `level_lowering_to_two` binds `hmod : P.freyCurve.IsModular` and never
  references it
  ([S_FreyPackage_level_lowering_to_two.lean, lines 130–134](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_FreyPackage_level_lowering_to_two.lean#L130-L134)).
  The hypothesis stays in the headline statement because it is the natural
  interface with step 4 (modularity) of the FLT route.

The parts that are *not* formalised, and are the reason the theorem is stated for
the Frey representation only, are the general theory of Ribet: a general
modular mod-$`p`$ representation need not have multiplicative reduction with
$`p \mid v_q(\Delta)`$ at the primes being stripped, and the geometric input
(Mazur's realization family, the toric dichotomy) is set up specifically for the
$`q`$-old/$`q`$-new decomposition of $`J_0(Nq)`$ with the Frey hypotheses.

## 8. Links

Lean sources at the pinned sha `aa2d8b3`:

- [Def_FLTPrelim_ModularRep.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_ModularRep.lean) — `ModularRepOfLevel`, `IsResiduallyModularOfLevel`
- [Def_FreyPackage_IsConductorLevel.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_IsConductorLevel.lean) — `IsConductorLevel`
- [Def_FreyPackage_AtPNewLowering.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_AtPNewLowering.lean) — `AtPNewLowering`
- [Def_WeierstrassCurve_Mlc1RowStatement.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_Mlc1RowStatement.lean) — exact conductor level
- [Def_WeierstrassCurve_PeuRamifiee.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_PeuRamifiee.lean) — `IsPeuRamifieeAt`
- [Def_ModularCurve_MazurPrincipleCore.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_MazurPrincipleCore.lean) — `HasLowerLevelTorsion`
- [Def_ModularCurve_ToricDichotomyData.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ToricDichotomyData.lean) — `IsToricDichotomyQGuarded`
- [Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf.lean) — Ribet, one prime
- [Thm_ModularCurve_isResiduallyModularOfLevel_div_of_mazurFamilies.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_isResiduallyModularOfLevel_div_of_mazurFamilies.lean) — the geometric heart
- [Thm_ModularCurve_exists_toricDichotomyData_jZero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_toricDichotomyData_jZero.lean) — toric dichotomy
- [Thm_FreyPackage_freyGaloisRep_isUnramifiedAt.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_freyGaloisRep_isUnramifiedAt.lean) — unramified at odd $`q`$
- [Thm_FreyPackage_level_lowering_odd_prime_of_conductorLevel.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_odd_prime_of_conductorLevel.lean) — strip odd $`q`$
- [Thm_FreyPackage_level_lowering_at_p_of_conductorLevel.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_at_p_of_conductorLevel.lean) — strip $`p`$
- [Thm_FreyPackage_level_lowering_to_two.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_to_two.lean) — headline
- [Thm_ModularForm_S2_Gamma0_2_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean) — endgame
- [PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/PROOF-PATH.md) — the five-step route and exact strengths

Companion notes:

- [note 007 — Modularity and computation](007-modularity-and-computation.md) — minimal models, discriminants, conductors, traces
- [note 004 — Irreducibility and the cofixed line](004-irreducible-and-cofixed-line.md) — the `hirr` hypothesis
- [note 002 — The Frey curve, its model and discriminant](002-frey-curve-model-and-discriminant.md) — where $`\Delta = (abc)^{2p}/2^8`$ comes from
- [base note 002 — Modular forms basics](../base/002-modular-forms-basics.md) — `CuspForm`, `Γ₀(N)`, `qCoeff`

Background:

- K. Ribet, *On modular representations of $`\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})`$
  arising from modular forms*, Invent. Math. 100 (1990) — level lowering.
- B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977)
  — the Eisenstein-ideal and Mazur-principle inputs.
- H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, Current Developments
  in Mathematics 1995 — the level-lowering route in textbook form.
