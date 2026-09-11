# Modularity and computation

Companion to [note 002](002-frey-curve-model-and-discriminant.md) (the Frey curve
and its discriminant) and to
[base note 002](../base/002-modular-forms-basics.md) (modular forms, Hecke
operators and `IsNormalizedEigenform` at the mathlib level). Here we do the
opposite of those notes: instead of reading the Lean, we *compute* the objects the
modularity theorem consumes, and trace each computed quantity back to the
definition or theorem that uses it.

The companion app is
[**Modularity, computed**](https://htzh.github.io/flt_for_human/apps/modular/index.html)
(source in [`apps/modular/`](https://github.com/htzh/flt_for_human/tree/main/apps/modular)).
It takes a Weierstrass equation, finds a minimal model, computes the discriminant
and the conductor, counts points modulo a prime to get the traces of Frobenius,
and reconstructs the weight-2 eigenform coefficients from the Hecke recursions.

**We assume the full modularity theorem and do not check semistability.** The app
therefore computes the *input* to Wiles's theorem, not the theorem; §8 says
exactly what is and is not verified. Line numbers refer to
`anthropics/fermats-last-theorem@aa2d8b3` (main, 2026-09-03).

## 1. The theorem, as Lean states it

The whole arithmetic content of "E is modular" in this project is a matching of
Fourier coefficients. From
[Def_FLTPrelim_Modularity.lean, lines 93–102](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L93-L102):

```lean
def IsModularModelOfLevel (W : WeierstrassCurve ℤ) (N : ℕ) : Prop :=
  ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
    ∀ p : ℕ, p.Prime → W.IsGoodPrimeFor p → ¬ p ∣ N →
      ModularFormClass.qCoeff f p = (W.apOfModel p : ℂ)

def IsModularModel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ W.IsModularModelOfLevel N

def IsModular (E : WeierstrassCurve ℚ) : Prop :=
  ∃ W : WeierstrassCurve ℤ, W.IsIntegralModelOf E ∧ W.IsModularModel
```

Three things about this definition matter for the app:

- **It is an existential over levels.** `IsModular` asks for *some* integral model
  and *some* level `N`; it never says `N` is the conductor. The level enters only
  through the condition `¬ p ∣ N` on the primes where the match is required.
- **The match is at good primes only.** `IsGoodPrimeFor p` is
  `¬ (p : ℤ) ∣ W.Δ`
  ([lines 82–83](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L82-L83)),
  and `¬ p ∣ N` excludes the level's own primes. At a bad prime the eigenform's
  coefficient is *not* claimed to equal the naive point count (see §3).
- **`IsNormalizedEigenform` is a coefficient recursion**, not an operator
  statement — [lines 28–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L28-L40):

```lean
structure IsNormalizedEigenform {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    Prop where

  qCoeff_one : qCoeff f 1 = 1

  qCoeff_mul_of_coprime : ∀ m n : ℕ, m.Coprime n →
    qCoeff f (m * n) = qCoeff f m * qCoeff f n

  qCoeff_prime_pow_of_not_dvd : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1)) - p * qCoeff f (p ^ r)

  qCoeff_prime_pow_of_dvd : ∀ p r : ℕ, p.Prime → p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1))
```

The classical Hecke-operator derivation of these four clauses is in
[base note 002 §5–6](../base/002-modular-forms-basics.md); the app takes the four
clauses as the algorithm. This is why the app can produce a `q`-expansion from
point counts alone, with no modular forms anywhere in sight.

Wiles's theorem is then the one-line statement
([Thm_WeierstrassCurve_modularity_of_semistableModel.lean, line 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_modularity_of_semistableModel.lean#L131)):

```lean
theorem WeierstrassCurve.modularity_of_semistableModel (W : WeierstrassCurve ℤ)
    (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) : (W.map (Int.castRingHom ℚ)).IsModular
```

with `IsSemistableModel W := ∀ p, p.Prime → (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄`
([lines 85–87](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L85-L87)).
The app displays `v_p(Δ)`, the Kodaira type and `c_p` for every bad prime, so
semistability is visible, but it is not tested: the theorem is assumed.

## 2. The arithmetic side: reduction, points, traces

The elliptic-curve quantities the app computes are all in the same file. The
trace of Frobenius is a point count
([lines 61–80](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L61-L80)):

```lean
instance Point.instFinite [Finite R] : Finite W'.Point :=
  Finite.of_injective _ Point.toOptionPair_injective

def card : ℕ := Nat.card W.toAffine.Point

def traceOfFrobenius : ℤ := (Nat.card F : ℤ) + 1 - (W.card : ℤ)

def reductionMod (W : WeierstrassCurve ℤ) (p : ℕ) : WeierstrassCurve (ZMod p) :=
  W.map (Int.castRingHom (ZMod p))

def apOfModel (W : WeierstrassCurve ℤ) (p : ℕ) : ℤ :=
  (W.reductionMod p).traceOfFrobenius
```

So $`a_p`$ is literally $`p + 1 - \#E(\mathbb{F}_p)`$, where the point set is
mathlib's `W.toAffine.Point` (the nonsingular points plus the point at infinity),
made finite by injecting it into `Option (R × R)`. The app computes the same count
by brute force: reduce the minimal model modulo $`p`$, iterate over
$`(x, y) \in \mathbb{F}_p^2`$, test the equation, add one for the point at
infinity, and set $`a_p = p + 1 - \#E(\mathbb{F}_p)`$.

For `11a1 : y² + y = x³ − x² − 10x − 20` the counts begin

| $`p`$ | 2 | 3 | 5 | 7 | 11 | 13 |
|---|---|---|---|---|---|---|
| $`\#E(\mathbb{F}_p)`$ | 5 | 5 | 5 | 10 | 11 | 10 |
| $`a_p`$ | −2 | −1 | 1 | −2 | 1 | 4 |

At $`p = 11`$ the reduction is singular, and the naive count happens to give the
right value 1; in general it does not, which is why §3 separates the two.

## 3. Bad primes: reduction type and the local coefficient

`apOfModel` is defined at *every* prime, but `IsModularModelOfLevel` only compares
at good primes. The reason is that at a bad prime the eigenform's coefficient is a
*local L-factor*, not a point count on the singular fiber:

| reduction at $`p`$ | Kodaira type | $`a_p`$ (weight 2) | conductor exponent $`f_p`$ |
|---|---|---|---|
| good | $`I_0`$ | $`p + 1 - \#E(\mathbb{F}_p)`$ | 0 |
| multiplicative, split | $`I_n`$ | $`1`$ | 1 |
| multiplicative, non-split | $`I_n`$ | $`-1`$ | 1 |
| additive | $`II, III, IV, I_0^*, I_n^*, IV^*, III^*, II^*`$ | $`0`$ | $`\geq 2`$ |

The app obtains this table from **Tate's algorithm**, run at each prime dividing
$`\Delta`$ of the minimal model. The same run produces the Kodaira symbol, the
conductor exponent $`f_p`$, the Tamagawa number $`c_p`$, and the split/non-split
sign, so the conductor is

$$N = \prod_{p \mid \Delta} p^{f_p}.$$

For $`p \geq 5`$ every additive type has $`f_p = 2`$ exactly; the algorithm reads
it off as $`f_p = v_p(\Delta)`$ minus an offset fixed by the type ($`0`$ for
$`II`$, $`1`$ for $`III`$, $`2`$ for $`IV`$, $`4`$ for $`I_0^*`$,
$`n+4`$ for $`I_n^*`$, $`6`$ for $`IV^*`$, $`7`$ for $`III^*`$, $`8`$ for
$`II^*`$). At $`p = 2, 3`$ wild ramification can push $`f_p`$ up to 8, which is why
the app reports $`v_p(\Delta)`$ alongside the type. Tate's algorithm is also what
turns a non-minimal equation into a minimal one: when the model is non-minimal at
$`p`$ it divides the coefficients by $`p, p^2, p^3, p^4, p^6`$ and starts over.

## 4. The two conductors, and why the formalisation can use the small one

There are two different "levels" in play, and keeping them apart is the most
useful thing this note has to say.

- **The true conductor** $`N = \prod p^{f_p}`$, with the exponents above. This is
  what the app's Step 4 reports, and it is the classical level of the newform.
- **The formalisation's conductor level**, which is the *radical* of the
  discriminant
  ([Def_WeierstrassCurve_ConductorLevel.lean, lines 11–26](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_ConductorLevel.lean#L11-L26)):

```lean
def conductorLevel (W : WeierstrassCurve ℤ) : ℕ :=
  radical W.Δ.natAbs

theorem squarefree_conductorLevel (W : WeierstrassCurve ℤ) : Squarefree W.conductorLevel :=
  squarefree_radical

theorem prime_dvd_conductorLevel_iff (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {q : ℕ}
    (hq : q.Prime) : q ∣ W.conductorLevel ↔ (q : ℤ) ∣ W.Δ
```

and for the Frey package the abstract version is
[Def_FreyPackage_IsConductorLevel.lean, lines 8–14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_IsConductorLevel.lean#L8-L14):

```lean
structure IsConductorLevel (P : FreyPackage) (N : ℕ) : Prop where
  pos : 0 < N
  squarefree : Squarefree N
  support : ∀ q : ℕ, q.Prime → q ∣ N → (q : ℤ) ∣ P.a * P.b * P.c
```

This `N` is squarefree by construction and supported exactly on the bad primes;
it is *not* the true conductor when some $`f_p \geq 2`$. For a semistable curve —
in particular the Frey curve — every bad prime is multiplicative, so every
$`f_p = 1`$ and the two notions agree. For a general curve they do not, and the
app prints both side by side.

That the formalisation may use the squarefree level is a real theorem, not an
oversight: the modularity theorem is applied in its existential form, and the
level that level-lowering actually needs is any squarefree level supported on the
bad primes. PROOF-PATH.md states the division of labour: the level-lowering step
"re-derives modularity itself, so the `IsModular` hypothesis above is formally
unused". The relevant statement is
`FreyPackage.modularRepOfConductorLevel`
([line 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_modularRepOfConductorLevel.lean#L131)):

```lean
theorem FreyPackage.modularRepOfConductorLevel (P : FreyPackage) :
    ∃ N : ℕ, P.IsConductorLevel N ∧ P.ModularRepOfLevel N
```

where `ModularRepOfLevel`
([Def_FLTPrelim_ModularRep.lean, lines 62–69](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_ModularRep.lean#L62-L69))
is a *congruence of traces modulo a maximal ideal* $`\mathfrak{m} \ni p`$, not an
equality of coefficients — the residual statement that Ribet's theorem needs.

## 5. What the app computes, step by step

The app is a single page; the arithmetic lives in
[`apps/modular/ec.js`](https://github.com/htzh/flt_for_human/blob/main/apps/modular/ec.js).
Its pipeline is:

1. **Input.** Five integers $`a_1, a_2, a_3, a_4, a_6`$. The invariants are
   $`b_2 = a_1^2 + 4a_2`$, $`b_4 = 2a_4 + a_1 a_3`$,
   $`b_6 = a_3^2 + 4a_6`$,
   $`b_8 = a_1^2 a_6 + 4 a_2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 - a_4^2`$,
   $`c_4 = b_2^2 - 24 b_4`$, $`c_6 = -b_2^3 + 36 b_2 b_4 - 216 b_6`$, and

   $$\\Delta = -b_2^2 b_8 - 8 b_4^3 - 27 b_6^2 + 9 b_2 b_4 b_6.$$

   This is the same computation as [note 002 §3](002-frey-curve-model-and-discriminant.md).
   Everything is exact integer arithmetic (`BigInt`); the Frey curve's
   $`\Delta = (abc)^{2p}/2^8`$ is far beyond floating point.

2. **Minimal model.** For each prime $`p \mid \Delta`$, Tate's algorithm is run on
   the current model. When it reports a smaller $`v_p(\Delta)`$, the model is
   replaced; otherwise the input is kept. Example: `y² = x³ + 81x` has
   $`\Delta = -34012224 = -2^6 \cdot 3^{12}`$ and minimalises to `y² = x³ + x`
   with $`\Delta = -64`$ — the spurious $`3^{12}`$ is removed by the change
   $`u = 3`$, $`a_4 \mapsto a_4/3^4 = 1`$.

3. **Discriminant and conductor.** The minimal discriminant is factored
   (trial division, then Miller–Rabin + Pollard rho for large prime factors); the
   bad primes are its prime factors; Tate's algorithm gives the table of §3 and
   the conductor $`N`$. The app also prints
   $`\mathrm{rad}(|\Delta|)`$, the formalisation's `conductorLevel`.

4. **Traces.** For every prime $`p \leq 20`$, the app counts
   $`\#E(\mathbb{F}_p)`$ by brute force and reports $`a_p`$, marking whether the
   prime is good and, if not, which local value the recursion will use.

5. **Eigenform.** The $`a_p`$ are fed into the four clauses of
   `IsNormalizedEigenform`. Multiplicativity handles composite $`n`$; the two
   prime-power clauses handle $`p^e`$. The app prints, for each $`n \leq 20`$, the
   recursion that produced $`a_n`$.

6. **The check.** For `11a1` the app computes the eta product
   $`\eta(\tau)^2 \eta(11\tau)^2`$ — the newform `11.2.a.a` — *independently of
   the point counts*, and compares. This is a genuine check: two different
   computations (arithmetic point counts + Hecke recursion, versus a product
   expansion) agree coefficient by coefficient.

## 6. Worked example: `11a1`, and the newform it is modular by

Take $`E : y^2 + y = x^3 - x^2 - 10x - 20`$, with
$`\Delta = -11^5`$, $`c_4 = 496`$, $`c_6 = 20008`$. The app finds it already
minimal, with a single bad prime:

| $`p`$ | $`v_p(\Delta)`$ | Kodaira | reduction | $`f_p`$ | $`c_p`$ | $`a_p`$ |
|---|---|---|---|---|---|---|
| 11 | 5 | $`I_5`$ | multiplicative, split | 1 | 5 | 1 |

so $`N = 11`$. Point counts give $`a_2 = -2`$, $`a_3 = -1`$, $`a_5 = 1`$,
$`a_7 = -2`$, $`a_{13} = 4`$, $`a_{17} = -2`$, $`a_{19} = 0`$, and the local value
$`a_{11} = 1`$. The recursion then produces:

| $`n`$ | factorisation | $`a_n`$ | recursion applied |
|---|---|---|---|
| 1 | | 1 | normalisation |
| 2 | 2 | −2 | $`a_2 = 2 + 1 - \#E(\mathbb{F}_2)`$ |
| 3 | 3 | −1 | $`a_3 = 3 + 1 - \#E(\mathbb{F}_3)`$ |
| 4 | $`2^2`$ | 2 | $`a_4 = a_2^2 - 2`$ |
| 5 | 5 | 1 | $`a_5 = 5 + 1 - \#E(\mathbb{F}_5)`$ |
| 6 | $`2 \cdot 3`$ | 2 | $`a_6 = a_2 a_3`$ |
| 7 | 7 | −2 | $`a_7 = 7 + 1 - \#E(\mathbb{F}_7)`$ |
| 8 | $`2^3`$ | 0 | $`a_8 = a_2 a_4 - 2 a_2`$ |
| 9 | $`3^2`$ | −2 | $`a_9 = a_3^2 - 3`$ |
| 10 | $`2 \cdot 5`$ | −2 | $`a_{10} = a_2 a_5`$ |
| 11 | 11 | 1 | local factor at the bad prime 11 |
| 12 | $`2^2 \cdot 3`$ | −2 | $`a_{12} = a_4 a_3`$ |
| 13 | 13 | 4 | $`a_{13} = 13 + 1 - \#E(\mathbb{F}_{13})`$ |
| 14 | $`2 \cdot 7`$ | 4 | $`a_{14} = a_2 a_7`$ |
| 15 | $`3 \cdot 5`$ | −1 | $`a_{15} = a_3 a_5`$ |
| 16 | $`2^4`$ | −4 | $`a_{16} = a_2 a_8 - 2 a_4`$ |
| 17 | 17 | −2 | $`a_{17} = 17 + 1 - \#E(\mathbb{F}_{17})`$ |
| 18 | $`2 \cdot 3^2`$ | 4 | $`a_{18} = a_2 a_9`$ |
| 19 | 19 | 0 | $`a_{19} = 19 + 1 - \#E(\mathbb{F}_{19})`$ |
| 20 | $`2^2 \cdot 5`$ | 2 | $`a_{20} = a_4 a_5`$ |

The eta product $`\eta(\tau)^2\eta(11\tau)^2`$ expands to exactly this sequence
$`1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, -2, 4, 4, -1, -4, -2, 4, 0, 2`$.
So the app exhibits, for this curve, the conclusion of the modularity theorem: the
arithmetic $`a_p`$ *are* the coefficients of a normalised weight-2 eigenform on
$`\Gamma_0(11)`$. (This is the classical modularity of $`X_0(11)`$, known long
before Wiles; the point here is that the app derives it from point counts.)

## 7. Worked example: a Frey-shaped curve

The Frey curve is
$`E_P : y^2 + xy = x^3 + \frac{b^p - 1 - a^p}{4}x^2 - \frac{a^p b^p}{16}x`$
([Def_FLTPrelim_FreyPackage.lean, lines 83–95](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_FreyPackage.lean#L83-L95)),
an integral model of $`y^2 = x(x - a^p)(x + b^p)`$ with
$`\Delta = (abc)^{2p}/2^8`$ ([note 002](002-frey-curve-model-and-discriminant.md)).
A genuine Frey curve needs a genuine counterexample, which does not exist; the app
ships a *Frey-shaped* preset with $`a = 3`$, $`b = 2`$, $`p = 5`$:

$$E : y^2 + xy = x^3 - 53x^2 - 486x.$$

Here $`a^5 = 243`$, $`b^5 = 32`$, and $`a^5 + b^5 = 275 = 5^2 \cdot 11`$ is not a
fifth power, so this is not a counterexample — but it has the right shape. The app
finds it minimal with

| $`p`$ | $`v_p(\Delta)`$ | Kodaira | reduction | $`f_p`$ | $`a_p`$ |
|---|---|---|---|---|---|
| 2 | 2 | $`I_2`$ | multiplicative, non-split | 1 | −1 |
| 3 | 10 | $`I_{10}`$ | multiplicative, non-split | 1 | −1 |
| 5 | 4 | $`I_4`$ | multiplicative, non-split | 1 | −1 |
| 11 | 2 | $`I_2`$ | multiplicative, split | 1 | 1 |

so $`N = 2 \cdot 3 \cdot 5 \cdot 11 = 330`$: every bad prime is multiplicative,
$`N`$ is squarefree, and $`N = \mathrm{rad}(abc)`$ — exactly the situation Ribet's
theorem needs. The recursion gives
$`a_n = 1, -1, -1, 1, -1, 1, 0, -1, 1, 1, 1, -1, 2, 0, 1, 1, -2, -1, 8, -1`$
for $`n = 1, \dots, 20`$. This is the eigenform that Wiles's theorem attaches to
the curve and that Ribet's level-lowering then has to force down to level 2.

## 8. The route to Fermat, and what is assumed

With modularity in hand, the Frey argument is short:

1. $`E_P`$ is semistable, so `WeierstrassCurve.modularity_of_semistableModel`
   gives `P.freyCurve.IsModular`; its Frey specialization is
   `FreyPackage.frey_isModular`
   ([Thm_FreyPackage_frey_isModular.lean, line 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_frey_isModular.lean#L131)).
2. $`E_P[p]`$ is irreducible (Mazur; note 003 and 004), and level lowering
   ([Thm_FreyPackage_level_lowering_to_two.lean, line 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_to_two.lean#L131)) gives

   ```lean
   theorem FreyPackage.level_lowering_to_two (P : FreyPackage) (hmod : P.freyCurve.IsModular)
       (hirr : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) :
       ∃ f : CuspForm (CongruenceSubgroup.Gamma0 2) 2, f ≠ 0
   ```

3. But
   [Thm_ModularForm_S2_Gamma0_2_eq_zero.lean, line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean#L13)
   says every such form is zero:

   ```lean
   theorem ModularForm.S2_Gamma0_2_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0
   ```

   Contradiction. The proof of the vanishing is mathlib's level-one dimension
   formula plus an index computation, as in
   [base note 002 §7](../base/002-modular-forms-basics.md).

**What is assumed.** The app does not verify semistability (we assume the full
modularity theorem), does not verify the irreducibility of $`E_P[p]`$, and does
not implement level lowering. It computes the arithmetic input — minimal model,
$`\Delta`$, $`N`$, the $`a_p`$, and the eigenform — and prints the reduction types
so that the semistability hypothesis can be *seen* even though it is not checked.
The app is an illustration; the proof is the Lean.

## 9. Key-point → code map

| Computed in the app | Lean definition / theorem | Location (pinned `aa2d8b3`) |
|---|---|---|
| integral model | `WeierstrassCurve ℤ` | mathlib |
| minimal model | `IsIntegralModelOf` (existential over `VariableChange ℚ`) | [Def_FLTPrelim_Modularity.lean 88–90](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L88-L90) |
| discriminant $`\Delta`$ | `WeierstrassCurve.Δ` | mathlib `Affine/Basic.lean` |
| conductor level | `conductorLevel W := radical W.Δ.natAbs` | [Def_WeierstrassCurve_ConductorLevel.lean 11–26](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_ConductorLevel.lean#L11-L26) |
| Frey conductor level | `FreyPackage.IsConductorLevel` | [Def_FreyPackage_IsConductorLevel.lean 8–14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_IsConductorLevel.lean#L8-L14) |
| reduction mod $`p`$ | `reductionMod` | [Def_FLTPrelim_Modularity.lean 76–77](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L76-L77) |
| $`\#E(\mathbb{F}_p)`$ | `WeierstrassCurve.card`, `Point.instFinite` | [Def_FLTPrelim_Modularity.lean 61–70](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L61-L70) |
| trace $`a_p`$ | `traceOfFrobenius`, `apOfModel` | [Def_FLTPrelim_Modularity.lean 72–80](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L72-L80) |
| good prime | `IsGoodPrimeFor` | [Def_FLTPrelim_Modularity.lean 82–83](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L82-L83) |
| eigenform recursion | `IsNormalizedEigenform` | [Def_FLTPrelim_Modularity.lean 28–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L28-L40) |
| modularity match | `IsModularModelOfLevel`, `IsModular` | [Def_FLTPrelim_Modularity.lean 93–102](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L93-L102) |
| semistability (assumed) | `IsSemistableModel` | [Def_FLTPrelim_Modularity.lean 85–87](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L85-L87) |
| Wiles | `WeierstrassCurve.modularity_of_semistableModel` | [Thm, line 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_modularity_of_semistableModel.lean#L131) |
| Frey modularity | `FreyPackage.frey_isModular` | [Thm, line 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_frey_isModular.lean#L131) |
| conductor level from modularity | `FreyPackage.modularRepOfConductorLevel` | [Thm, line 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_modularRepOfConductorLevel.lean#L131) |
| level lowering | `FreyPackage.level_lowering_to_two` | [Thm, line 131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_to_two.lean#L131) |
| endgame | `ModularForm.S2_Gamma0_2_eq_zero` | [Thm, line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean#L13) |

## 10. Links

The app:

- [Modularity, computed](https://htzh.github.io/flt_for_human/apps/modular/index.html) — the running app
- [apps/modular/index.html](https://github.com/htzh/flt_for_human/blob/main/apps/modular/index.html) — the page
- [apps/modular/ec.js](https://github.com/htzh/flt_for_human/blob/main/apps/modular/ec.js) — the arithmetic engine (Tate's algorithm, point counts, Hecke recursion, eta product)

Lean sources at the pinned sha `aa2d8b3`:

- [Def_FLTPrelim_Modularity.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean) — `IsNormalizedEigenform`, `card`, `apOfModel`, `IsModular`
- [Def_WeierstrassCurve_ConductorLevel.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_ConductorLevel.lean) — `conductorLevel`
- [Def_FreyPackage_IsConductorLevel.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FreyPackage_IsConductorLevel.lean) — `IsConductorLevel`
- [Def_FLTPrelim_ModularRep.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_ModularRep.lean) — `ModularRepOfLevel`, `IsResiduallyModularOfLevel`
- [Def_FLTPrelim_FreyPackage.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_FreyPackage.lean) — the Frey curve
- [Thm_WeierstrassCurve_modularity_of_semistableModel.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_modularity_of_semistableModel.lean) — Wiles's theorem as used
- [Thm_FreyPackage_frey_isModular.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_frey_isModular.lean) — the Frey case
- [Thm_FreyPackage_modularRepOfConductorLevel.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_modularRepOfConductorLevel.lean) — conductor level
- [Thm_FreyPackage_level_lowering_to_two.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_FreyPackage_level_lowering_to_two.lean) — Ribet's step
- [Thm_ModularForm_S2_Gamma0_2_eq_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularForm_S2_Gamma0_2_eq_zero.lean) — the endgame

Annotated docs (viewable):

- [def/FLTPrelim_Modularity.html](https://tianyipeng.github.io/fermats-last-theorem/def/FLTPrelim_Modularity.html)
- [def/FLTPrelim_ModularRep.html](https://tianyipeng.github.io/fermats-last-theorem/def/FLTPrelim_ModularRep.html)
- [def/WeierstrassCurve_ConductorLevel.html](https://tianyipeng.github.io/fermats-last-theorem/def/WeierstrassCurve_ConductorLevel.html)
- [def/FreyPackage_IsConductorLevel.html](https://tianyipeng.github.io/fermats-last-theorem/def/FreyPackage_IsConductorLevel.html)
- [PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/PROOF-PATH.md) — the four-theorem skeleton

Background:

- J. Tate, *Algorithm for determining the type of a singular fiber in an elliptic
  pencil*, in Modular Functions of One Variable IV (1975) — Tate's algorithm.
- J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, III.9–10 —
  Tate's algorithm and Ogg's conductor formula.
- H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, Current Developments
  in Mathematics 1995 — the modularity and level-lowering route.
