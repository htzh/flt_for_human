# The χ₋₃ weight-one Eisenstein series and the hexagonal lattice

The series studied here is

$$1 + 6\sum_{n \ge 1} \sigma_\chi(n)\\,q^n,
\qquad
\sigma_\chi(n) = \sum_{d \mid n} \chi_{-3}(d),$$

where $`\chi_{-3}`$ is the nontrivial Dirichlet character modulo $`3`$. It is
the weight-one Eisenstein series $`E_1(1,\chi_{-3})`$ of level $`3`$, and it is
also the theta series of the hexagonal lattice: the coefficient of $`q^n`$ is
the number of integer solutions of $`x^2 + xy + y^2 = n`$, hence six times the
divisor sum. That coincidence of an arithmetic count with a divisor sum is the
content of the theorem, and it is why this particular series is worth
computing: it is the one weight-one form on $`\Gamma_1(3)`$ that is available
explicitly and with integral coefficients, and its coefficients are at the same
time representation numbers of a lattice (computable) and Hecke data
(modular).

**Why FLT computes it.** The series is the low-weight generator of the
$`\Gamma_1(N)`$ spaces in the integral-structure route (the trace route of
[013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md));
its coefficients are integral, divisible by $`6`$ in positive degree, and
congruent to $`1`$ modulo $`3`$, and that congruence powers the weight-two
mod-3 congruence lift. It is also the explicit form in FLT's weight-one
(Langlands–Tunnell) branch, whose analytic input is the Poisson-summation
functional equation proved here. The ported Lean module is
[`../lean/FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean`](../lean/FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean)
(3,828 lines); the mathematics is §1–§7 and the Lean technicalities are
summarized in §8. FLT is pinned at `aa2d8b3`; all citations are public URLs at
that commit. The port map and verification record are
[`../lean/topics/hecke/SET-6.md`](../lean/topics/hecke/SET-6.md); a companion
computation is [`../pymath/hexagonal_theta.py`](../pymath/hexagonal_theta.py).

## 1. The character and the series

Modulo $`3`$ the multiplicative group has order two, so there is a unique
nontrivial character. Written as a $`\mathbb{Z}`$-valued function on the
nonnegative integers,

$$\chi_{-3}(n) = \begin{cases} 1, & n \equiv 1 \pmod 3, \\\\ -1, & n \equiv 2 \pmod 3, \\\\ 0, & 3 \mid n. \end{cases}$$

It is completely multiplicative, vanishes exactly on the multiples of $`3`$, and
is **odd**: $`\chi_{-3}(-1) = \chi_{-3}(2) = -1`$, which is the character parity
required of a weight-one form (the element $`-1 \in \mathrm{SL}_2(\mathbb{Z})`$
acts on weight $`1`$ by $`(-1)^{-1} = -1`$). The divisor sum

$$\sigma_\chi(n) = \sum_{d \mid n} \chi_{-3}(d) = d_1(n) - d_2(n),$$

where $`d_1(n)`$ and $`d_2(n)`$ count the divisors of $`n`$ congruent to $`1`$
and $`2`$ modulo $`3`$, is multiplicative because $`\chi_{-3}`$ is: for
$`\gcd(m,n) = 1`$,

$$\sigma_\chi(mn) = \sigma_\chi(m)\\,\sigma_\chi(n),
\qquad
\sigma_\chi(p^k) = \sum_{j=0}^{k} \chi_{-3}(p)^j.$$

At a prime $`p \ne 3`$ this gives $`\sigma_\chi(p^k) = k+1`$ when $`p \equiv 1`$,
and $`1`$ or $`0`$ for even or odd $`k`$ when $`p \equiv 2`$; at $`p = 3`$ it is
$`1`$ for every $`k`$. The series is

$$e_1^{\chi_{-3}} \\;=\\; 1 + 6q + 6q^3 + 6q^4 + 12q^7 + 6q^9 + 12q^{13} + \cdots,$$

the first coefficients being $`\sigma_\chi(n) = 1,0,1,1,0,0,2,0,1,0,0,1,2`$ for
$`n = 1,\dots,13`$. FLT's interface states the modularity:

```lean
def E1Chi3IsModular : Prop :=
  ∃ f : ModularForm (Gamma1 3) 1, ∀ z : UpperHalfPlane,
    f z = ∑' n : ℕ, ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ))
```

([`Def_ModularForm_EisensteinChiNegThree.lean`, lines 20–24](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_EisensteinChiNegThree.lean#L20-L24)).
The whole file proves this one proposition.

## 2. The hexagonal form and the Eisenstein integers

Write

$$Q(x,y) = x^2 + xy + y^2 .$$

It is positive definite, because

$$4\\,Q(x,y) = (2x+y)^2 + 3y^2 ,$$

and its discriminant is $`b^2 - 4ac = 1 - 4 = -3`$. It is the norm form of the
ring of Eisenstein integers $`\mathbb{Z}[\zeta_6]`$, where
$`\zeta = e^{i\pi/3}`$ is a primitive sixth root of unity
($`\zeta^2 = \zeta - 1`$, $`\zeta^6 = 1`$): for $`z = x + y\zeta`$,

$$N(z) = z\\,\bar z = (x + y\zeta)(x + y\zeta^{-1}) = x^2 + xy + y^2 = Q(x,y) .$$

Equivalently, since $`\zeta_6 = -\zeta_3`$, one has
$`Q(x,y) = N(x - y\zeta_3)`$, the norm form of $`\mathbb{Z}[\zeta_3]`$ in the
standard coordinates: $`x + y\zeta_6 = x - y\zeta_3`$. Both descriptions are
the same lattice, the $`A_2`$ root lattice with its sixfold symmetry. The norm
is multiplicative and positive, and

$$z \cdot \bar z = N(z) \in \mathbb{Z},$$

so every element of norm $`n`$ gives a representation of $`n`$ by $`Q`$, and
conversely. Thus

$$r(n) \\;:=\\; \\#\\{(x,y) \in \mathbb{Z}^2 : Q(x,y) = n\\}$$

is the number of elements of $`\mathbb{Z}[\zeta_6]`$ of norm $`n`$ — with
$`r(0) = 1`$, the origin.

**The six units.** The norm-one elements are exactly the sixth roots of unity
$`\pm 1, \pm\zeta, \pm\zeta^2`$; multiplication by $`\zeta`$ acts on the pair
$`(x,y)`$ by the rotation $`(x,y) \mapsto (-y, x+y)`$, which visibly preserves
$`Q`$. This is why the factor $`6`$ appears everywhere below: for $`n \gt 0`$ the
six units act freely on the solutions of $`Q(x,y) = n`$, so every nonzero
solution lies in a six-element orbit and

$$6 \mid r(n) \qquad (n \ge 1).$$

The quotient $`r(n)/6`$ counts solutions *up to multiplication by a unit*.

**Unique factorization.** $`\mathbb{Z}[\zeta_6]`$ is Euclidean for the norm (the
nearest-lattice-point division algorithm: given $`y \ne 0`$, round
$`x\bar y / N(y)`$ coordinatewise to the nearest Eisenstein integer $`q`$; then
$`r = x - yq`$ has $`N(r) \lt N(y)`$). Hence it is a principal ideal domain, and
the arithmetic of the form is the arithmetic of the prime elements. The
classical fact behind the coefficient identity is that the quadratic field
$`\mathbb{Q}(\sqrt{-3})`$ has class number one, which is exactly this
Euclidean property.

## 3. The coefficient identity

> **Theorem.** For every $`n \ge 1`$, $`r(n) = 6\,\sigma_\chi(n)`$.

Equivalently $`r(n) = 6\,(d_1(n) - d_2(n))`$, and the theta series of the
hexagonal lattice is $`e_1^{\chi_{-3}}`$. The first values are

| $`n`$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $`r(n)`$ | 6 | 0 | 6 | 6 | 0 | 0 | 12 | 0 | 6 | 0 | 0 | 6 | 12 | 0 | 0 |
| $`6\sigma_\chi(n)`$ | 6 | 0 | 6 | 6 | 0 | 0 | 12 | 0 | 6 | 0 | 0 | 6 | 12 | 0 | 0 |

Several consequences are worth stating because they are the shape in which the
identity gets used.

- **Which $`n`$ are represented at all.** $`r(n) \ne 0`$ exactly when every
  prime $`p \equiv 2 \pmod 3`$ occurs in $`n`$ to an even power: those primes are
  inert, while $`3`$ and the primes $`p \equiv 1 \pmod 3`$ are represented.
  Equivalently, $`n`$ is a norm from $`\mathbb{Z}[\zeta_6]`$.
- **Integrality.** $`r(n)`$ is divisible by $`6`$, and $`e_1^{\chi_{-3}} - 1`$
  is divisible by $`6`$ coefficientwise, hence certainly by $`3`$. This is the
  congruence
  $`e_1^{\chi_{-3}} \equiv 1 \pmod 3`$ used by the mod-3 machinery (§7).
- **Multiplicativity.** $`n \mapsto r(n)/6 = \sigma_\chi(n)`$ is multiplicative
  on coprime arguments; equivalently
  $`6\,r(mn) = r(m)r(n)`$ for $`\gcd(m,n) = 1`$. Coprimality is essential:
  $`6\,r(4) = 36 \ne 0 = r(2)^2`$.

The proof is the content of §§4–5; §4 is the arithmetic and §5 the analysis.

## 4. The arithmetic half: three local behaviours

Because $`\mathbb{Z}[\zeta_6]`$ is a unique factorization domain, the count
$`r(n)`$ is determined by the prime factorization of $`n`$ and the way rational
primes factor in the ring. There are exactly three cases, indexed by the
residue of $`p`$ modulo $`3`$.

### 4.1 Ramified: $`p = 3`$

The element $`2 - \zeta = 1 - \zeta^2`$ has norm $`3`$, and
$`(2-\zeta)^2 = 3(1-\zeta)`$ with $`1-\zeta`$ a unit, so up to a unit
$`3 = (2-\zeta)^2`$: there is one prime element above $`3`$. If
$`3 \mid Q(x,y)`$ then $`x \equiv y \pmod 3`$, and the substitution

$$(u,v) \longmapsto (2u+v,\\; v-u)$$

is multiplication by the ramified prime $`2-\zeta`$, so it sends solutions of
$`Q(u,v) = m`$ bijectively onto solutions of
$`Q(2u+v, v-u) = 3\,Q(u,v) = 3m`$. Hence $`r(3m) = r(m)`$ and, inductively,
$`r(3^k) = 6`$. Since $`\sigma_\chi(3^k) = 1`$, this matches
$`6\sigma_\chi`$.

### 4.2 Inert: $`p \equiv 2 \pmod 3`$

Such a $`p`$ stays prime in $`\mathbb{Z}[\zeta_6]`$, with norm $`p^2`$, and the
residue field is $`\mathbb{F}_{p^2}`$; equivalently, the polynomial
$`T^2 + T + 1`$ has no root modulo $`p`$. It follows that

$$p \mid Q(x,y) \\;\Longrightarrow\\; p \mid x \text{ and } p \mid y
\\;\Longrightarrow\\; p^2 \mid Q(x,y) .$$

Indeed, if $`p \nmid y`$ one divides $`Q(x,y)`$ by $`y^2`$ and obtains a root
$`x/y`$ of $`T^2 + T + 1`$ modulo $`p`$, impossible. So no element has norm
$`p`$, and an element of norm $`p^k`$ must have $`k`$ even, in which case it is
a unit times $`p^{k/2}`$ and there are six such elements. Therefore

$$r(p^k) = \begin{cases} 6, & k \text{ even}, \\\\ 0, & k \text{ odd}, \end{cases}$$

which is $`6\sigma_\chi(p^k)`$ because $`\sigma_\chi(p^k)`$ is the alternating
sum $`1 - 1 + 1 - \cdots`$.

### 4.3 Split: $`p \equiv 1 \pmod 3`$

Here $`T^2 + T + 1`$ has a root $`t`$ modulo $`p`$ — a primitive cube root of
unity in $`\mathbb{F}_p`$ — and $`p`$ factors as $`p = \pi\bar\pi`$ with
$`N(\pi) = p`$. The existence of $`\pi`$ is not assumed but proved by a **Thue
lemma** count: among the $`(\lfloor\sqrt p\rfloor + 1)^2`$ pairs $`(a,b)`$ with
$`0 \le a,b \le \sqrt p`$, two have the same value of $`a - tb`$ modulo $`p`$
(there are more pairs than residues), and their difference $`(x,y)`$ satisfies

$$|x| \le \sqrt p, \qquad |y| \le \sqrt p, \qquad x \equiv ty \pmod p .$$

Then $`Q(x,y) \equiv y^2(t^2+t+1) \equiv 0 \pmod p`$, while
$`0 \lt Q(x,y) \lt 3p`$ by the bound. So $`Q(x,y) = p`$ or $`2p`$; the second is
impossible because $`2`$ is inert (§4.2), hence $`Q(x,y) = p`$ and $`x + y\zeta`$
is a prime element of norm $`p`$. Consequently $`r(p) = 12`$: the two prime
elements $`\pi, \bar\pi`$, each with six unit multiples.

For prime powers, every element of norm $`p^k`$ has a factorization
$`\pi^j \bar\pi^{k-j}`$ times a unit, with $`j = 0,\dots,k`$; the units act
freely, so there are $`k+1`$ unit-orbits and

$$r(p^k) = 6(k+1) = 6\\,\sigma_\chi(p^k) .$$

### 4.4 Assembly over the prime factorization

Let $`m, n`$ be coprime and let $`\gamma`$ run over elements of norm $`mn`$.
Writing $`\gamma = \alpha\beta`$ with $`N(\alpha) = m`$ and $`N(\beta) = n`$ is
possible (the prime factors of $`\gamma`$ split according to which of $`m,n`$
they divide), and two such factorizations differ by a unit: if
$`\alpha\beta = \alpha'\beta'`$, then $`\alpha' = u\alpha`$ and
$`\beta' = u^{-1}\beta`$ for a unit $`u`$, and coprimality is what makes the
comparison legal. Hence the map $`(\alpha,\beta) \mapsto \alpha\beta`$ has
six-element fibers and

$$r(m)\\,r(n) = 6\\,r(mn) \qquad (\gcd(m,n) = 1).$$

This is FLT's `OrbitCountMultiplicative`, and it is the multiplicativity of
$`\sigma_\chi`$ in disguise. Combining the three local laws with the coprime
law, and using that $`\sigma_\chi`$ is multiplicative and agrees with $`r/6`$ at
every prime power, gives $`r(n) = 6\sigma_\chi(n)`$ for all $`n`$. FLT packages
the local split law as `SplitPrimePowCount` and the assembly as an induction
over $`n`$ by prime factorization (`Nat.recOnPosPrimePosCoprime`), with the
three prime-power cases handled by §§4.1–4.3.

## 5. The analytic half: Poisson summation and modularity

The arithmetic half identifies the coefficients of the theta series

$$\theta(\sigma) = \sum_{x,y \in \mathbb{Z}} e^{2\pi i \sigma (x^2 + xy + y^2)},
\qquad \sigma \in \mathbb{H},$$

with $`6\sigma_\chi`$. The analytic half proves that $`\theta`$ is the
$`q`$-expansion of a modular form of weight $`1`$ on $`\Gamma_1(3)`$. The
absolute convergence on the upper half plane is Gaussian: since
$`x^2 + y^2 \le 2Q(x,y)`$,

$$\left|e^{2\pi i \sigma Q(x,y)}\right| \le e^{-\pi\\,\mathrm{Im}(\sigma)(x^2+y^2)},$$

summable over $`\mathbb{Z}^2`$ for $`\mathrm{Im}(\sigma) \gt 0`$; the same
dominating family gives local uniform convergence, hence holomorphy of
$`\theta`$ on $`\mathbb{H}`$.

**The Fricke functional equation.** Poisson summation applied twice, first in
$`x`$ and then in $`y`$, with the classical Gaussian identity
$`\sum_{m \in \mathbb{Z}} e^{-\pi a m^2 + 2\pi i b m} = a^{-1/2}\sum_{m \in \mathbb{Z}} e^{-\pi (m + ib)^2/a}`$
for $`\mathrm{Re}(a) \gt 0`$, turns $`\theta(\sigma)`$ into a multiple of
$`\theta(-1/(3\sigma))`$. The two square-root factors combine to $`-i\sqrt 3\,\sigma`$,
yielding

$$\theta\\!\left(-\frac{1}{3\sigma}\right) = -i\sqrt 3\\,\sigma\\,\theta(\sigma)
\qquad (\mathrm{Im}\\,\sigma \gt 0).$$

In FLT this is `hexTheta_eq_mul_self_neg_inv`, cleaned up to `hexTheta_fricke`;
its separate wrapper is
`HexagonalLattice.summable_thetaTerm_and_tsum_neg_inv_three_mul`
([lines 5–13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.lean#L5-L13)).
The multiplier $`-i\sqrt3\,\sigma`$ is exactly the automorphy factor of weight
$`1`$ for the Fricke involution $`\sigma \mapsto -1/(3\sigma)`$, whose square is
$`-1/3`$; the fixed point is $`\sigma = i/\sqrt3`$, and the equation is what
rules out the weight-**zero** alternative (the proof in fact shows the
weight-zero functional equation fails at that fixed point, using
$`\theta(i/\sqrt3) \ne 0`$).

**The two generators.** The series is plainly invariant under translation,

$$\theta(\sigma + 1) = \theta(\sigma),$$

and the Fricke equation combined with translation gives the second law

$$\theta\\!\left(\frac{\sigma}{1 - 3\sigma}\right) = (1 - 3\sigma)\\,\theta(\sigma),$$

corresponding to the element $`U_3 = [[1,0],[-3,1]] \in \Gamma_0(3)`$.
This is `hexTheta_U_law` (with `hexThetaH_slash_U` its slash form). The
concrete route is: $`-1/(3\sigma) + 1 = (1-3\sigma)/(-3\sigma)`$, so
$`\theta(-1/(3\sigma)+1) = \theta(-1/(3\sigma))`$ by translation, and applying
Fricke at the point $`-1/(3\sigma)+1`$ recovers the $`U_3`$ law after
rearranging.

**From the two laws to modularity.** One shows

$$\Gamma_0(3) = \langle T, U_3, -1 \rangle,$$

where $`T = [[1,1],[0,1]]`$; FLT proves this with
the Reidemeister–Schreier rewriting procedure (`GroupTheory.Schreier` in
mathlib) applied to the map $`\Gamma_0(3) \to (\mathbb{Z}/3)^\times`$
(`Gamma0Map`). The invariance of $`\theta`$ under $`T`$ and $`U_3`$ and the
weight-one multiplier for $`-1`$ then extend to a slash-equivariance under all
of $`\Gamma_0(3)`$:

$$\theta \mid_1 \gamma = \chi_3(\gamma)\\,\theta,
\qquad
\chi_3(\gamma) = \begin{cases} 1, & \gamma_{11} \equiv 1 \pmod 3, \\\\ -1, & \gamma_{11} \equiv 2 \pmod 3, \end{cases}$$

for $`\gamma \in \Gamma_0(3)`$. The character $`\chi_3`$ is exactly
$`\chi_{-3}`$ evaluated on the lower-right entry, it is trivial on
$`\Gamma_1(3)`$, and the $`-1`$ case is consistent because $`\chi_3(-1) = -1`$.
Hence $`\theta`$ is a **slash-invariant form on $`\Gamma_1(3)`$** of weight
$`1`$, with no nebentypus. Boundedness at every cusp follows from the Gaussian
bound together with the explicit formula for the finitely many coset
representatives (the transversal `repOfLabel`): each translate is a constant
times $`\theta((z+k)/3)`$ for a fixed $`k \in \{0,1,2\}`$, whose argument has
imaginary part bounded below by a positive constant once $`\mathrm{Im}(z)`$ is
large. Holomorphy is the local uniform convergence above; together these make
$`\theta`$ a modular form. Its $`q`$-expansion at $`\infty`$ is
$`\sum_n r(n)q^n`$ by construction, which the arithmetic half identifies with
`e1Chi3`. This is `e1Chi3IsModular_of_analytic_inputs` feeding the headline
`EisensteinWeightOne.e1Chi3IsModular`.

## 6. Where the two halves meet

The two halves answer different questions about the same series:

- the **arithmetic** half computes the coefficients: $`r(n) = 6\sigma_\chi(n)`$,
  a statement about representation numbers and divisor sums, proved by unique
  factorization in $`\mathbb{Z}[\zeta_6]`$;
- the **analytic** half proves the transformation law: the same $`\theta`$ is a
  weight-one form on $`\Gamma_1(3)`$, proved by Poisson summation and the
  structure of $`\Gamma_0(3)`$.

Neither alone gives the theorem. The arithmetic half alone gives an integral
$`q`$-series with no modularity; the analytic half alone gives a modular form
whose coefficients are representation counts, but says nothing about the
divisor sum. The identity $`r(n) = 6\sigma_\chi(n)`$ is the bridge, and the
modular form it produces is $`E_1(1,\chi_{-3})`$. In FLT the bridge is stated
separately as

```lean
theorem EisensteinWeightOne.tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal (σ : ℂ) (hσ : 0 < σ.im) :
    (∑' n : ℕ, ((PowerSeries.coeff n EisensteinWeightOne.e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * σ)) =
      ∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2))
```

([lines 8–12](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_EisensteinWeightOne_tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal.lean#L8-L12)),
and the coefficient identity itself as

```lean
theorem EisensteinWeightOne.coeff_e1Chi3 (n : ℕ) :
    (PowerSeries.coeff n) EisensteinWeightOne.e1Chi3 = if n = 0 then 1 else 6 * EisensteinWeightOne.sigmaChi n
```

([lines 7–8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_EisensteinWeightOne_coeff_e1Chi3.lean#L7-L8)).

One can also read the coefficients as Hecke data. Since $`\sigma_\chi`$ is
multiplicative and $`\sigma_\chi(p) = 1 + \chi_{-3}(p)`$, dividing the series by
its leading coefficient $`6`$ makes it an Eisenstein eigenform whose eigenvalue
at $`T_p`$ ($`p \nmid 3`$) is $`1 + \chi_{-3}(p)`$; this Hecke-eigenform reading
is the arithmetic shadow of the modularity proved in §5.

## 7. Why this series matters for FLT

1. **The weight-one generator of the integral-structure route.** In
   [013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md)
   the $`\Gamma_1(N)`$-spaces are shown to have integral bases built from an
   explicit Eisenstein family; $`E_1(1,\chi_{-3})`$ is the weight-one member
   that the low-weight range needs
   ([013, §3 and §6](013-integral-structure-gamma1-basis.md)). Its coefficients
   are integral (indeed in $`6\mathbb{Z}`$), which is exactly the property the
   lattice argument consumes.
2. **The mod-3 congruence.** In positive degree every coefficient of `e1Chi3`
   is divisible by $`6`$, so `e1Chi3` is congruent to $`1`$ modulo $`3`$. Hence
   for every power series $`g`$ and every $`n`$,

   $$3 \mid \mathrm{coeff}_n(g \cdot e_1^{\chi_{-3}}) - \mathrm{coeff}_n(g),$$

   FLT's `three_dvd_coeff_mul_e1Chi3_sub`
   ([lines 7–8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub.lean#L7-L8)).
   This is the ingredient that makes the weight-two mod-3 congruence lift of
   `CuspForm.WeightTwoModThreeCongruenceLift` go through, and it is used through
   the base-changed series `e1Chi3In R`
   ([`Def_ModularForm_EisensteinChiNegThree.lean`, lines 16–17](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_EisensteinChiNegThree.lean#L16-L17)).
3. **The weight-one branch.** FLT's No. 2 bridge (`FLT.No2BridgeWiring`) needs
   a weight-one $`\chi_{-3}`$-realized eigenform
   (`CuspForm.IsWeightOneChiNegThreeRealized`); the theta series is the explicit
   one, and its modularity is what the branch's `e1Chi3IsModular` provides. The
   analytic functional equation of §5 and the boundedness at the cusps are the
   weight-one modularity input, and the arithmetic identity supplies the
   integral $`q`$-expansion the branch compares against.
4. **It is cheap.** The FLT proof is self-contained (`closure 1` in the graph:
   it cites no other theorem node) and entirely computational; the port is a
   single 3,828-line module with one public headline. The measured route cost is
   in [route-c-prime-scout.md](../studies/route-c-prime-scout.md) §2–§3.

The numerical content of §§3–4 is reproduced by
[`../pymath/hexagonal_theta.py`](../pymath/hexagonal_theta.py), which computes
$`r(n)`$, $`\sigma_\chi(n)`$, the unit orbits, the three local laws and the
first coefficients of `e1Chi3`, and checks the functional equations of §5
numerically.

## 8. Lean technicalities (summary)

The port is a single file;
[`../lean/FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean`](../lean/FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean).
Its one public declaration is `EisensteinWeightOne.e1Chi3IsModular`; every other
declaration is `private`, and the vocabulary (`chiNegThree`, `sigmaChi`,
`e1Chi3`, `E1Chi3IsModular`) is imported from
[`../lean/FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean`](../lean/FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean),
matching FLT's definition module. There is no `sorry` and no placeholder.

- **Two copies of the count.** The analytic half defines `LatticeSum.hexForm` /
  `hexFormNat` / `repCount n` as the cardinality of the fiber of the form, while
  the arithmetic half defines `reprCount n` as the cardinality of an explicit
  finset of solutions (`reprSols n`, a filtered box). The port reconciles them
  with `repCount_eq_reprCount` and
  `representationCountAgrees_iff_reprCountEqCoeffE1Chi3`, so the q-expansion
  produced analytically has the coefficients computed arithmetically.
- **A custom Euclidean domain.** The ring $`\mathbb{Z}[\zeta_6]`$ is built as
  the structure `HexInt` (`re`, `im`), with hand-written `CommRing` and a
  Euclidean division `nearestDiv u n = (2u+n)/(2n)`; the norm is `hexForm`, the
  units are the six-element `unitFinset`, and the Euclidean-domain instance is
  assembled from `norm_mod_lt` and the multiplication inequality. The
  factorization inputs (`exists_dvd_norm_eq`, `exists_factorization`,
  `dvd_of_mul_eq_mul`, `eq_unit_mul_of_mul_eq_mul`) feed `card_fiber`, which is
  the six-element-fiber count of §4.4.
- **The residual decomposition.** The arithmetic proof is factored through two
  `Prop`s: `OrbitCountMultiplicative`
  ($`6r(mn)=r(m)r(n)`$ for coprime $`m,n`$) and `SplitPrimePowCount`
  ($`r(p^k)=6(k+1)`$ for $`p \equiv 1`$). The inert and ramified cases are
  proved directly (`reprCount_inert_pow`, `reprCount_three_pow`), the split
  case uses Thue's lemma (`thue_lemma`, `exists_hexForm_eq_prime`) and the
  union/dilate count (`reprSols_mul_eq_union`, `reprCount_mul_mul`), and
  `reprCountEqCoeffE1Chi3_of_residuals` assembles everything by the induction
  principle `Nat.recOnPosPrimePosCoprime`.
- **Poisson summation.** The analytic half reduces the rank-two sum to two
  one-dimensional sums and invokes mathlib's
  `Complex.tsum_exp_neg_quadratic`; `hexTheta_eq_mul_self_neg_inv` is the
  unsimplified functional equation and `hexTheta_fricke` the clean
  $`-i\sqrt3\,\sigma`$ form. The fixed-point argument
  (`not_hexTheta_eq_neg_multiplier_mul`) is what rules out the weight-zero law.
- **The group theory.** `Gamma0Three` sets up the coset representatives and the
  Schreier generators; mathlib's `GroupTheory.Schreier` gives
  `closure_schreierGens : Subgroup.closure schreierGens = Gamma0 3`, whence
  `closure_T_U_neg_one_eq`. The character `chi3` is defined on matrices and
  checked multiplicative on `Gamma0 3`; `slash_eq_chi3_smul` extends the T/U
  laws to all of `Gamma0 3` by subgroup induction, and
  `eq_zero_of_slashInvariant_gamma0` is the $`-1`$ (oddness) bookkeeping.
- **Packaging.** `slashInvariantForm_of_T_U` builds the `SlashInvariantForm`,
  and `e1Chi3IsModular_of_analytic_inputs` adds holomorphy
  (`mdifferentiable_hexThetaH`, from locally uniform convergence) and
  boundedness at every cusp (`hexThetaH_isBoundedAt_cusp`, from the Gaussian
  bound and the coset-translate formula `hexThetaH_slash_repOfLabel_apply`). The
  final extras `e1Chi3ModularForm`,
  `mulE1Chi3` and `exists_cuspForm_two_mul_e1Chi3` multiply a weight-one cusp
  form by the Eisenstein series to land in weight two.
- **Port drift.** The v4.34 adaptation renames `if_neg` to `ite_eq_right`,
  `if_pos` to `ite_eq_left`, and `Set.mem_setOf_eq` to `Set.mem_ofPred_eq`; the
  pin's local `set_option maxRecDepth 16384` on `reprCount_twentyone` is not
  transcribed. The mathematics is unchanged.

## 9. Declaration map

| mathematics | FLT declaration | pinned link |
|---|---|---|
| the character $`\chi_{-3}`$ | `EisensteinWeightOne.chiNegThree` | [Def, line 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_EisensteinChiNegThree.lean#L7-L8) |
| the divisor sum $`\sigma_\chi`$ | `EisensteinWeightOne.sigmaChi` | [Def, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_EisensteinChiNegThree.lean#L10-L11) |
| the $`q`$-series $`e_1^{\chi_{-3}}`$ | `EisensteinWeightOne.e1Chi3` | [Def, line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_EisensteinChiNegThree.lean#L13-L14) |
| its base change to $`R`$ | `EisensteinWeightOne.e1Chi3In` | [Def, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_EisensteinChiNegThree.lean#L16-L17) |
| the modularity statement | `EisensteinWeightOne.E1Chi3IsModular` | [Def, line 20](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_EisensteinChiNegThree.lean#L20-L24) |
| coefficient formula $`a_n`$ | `EisensteinWeightOne.coeff_e1Chi3` | [Thm, line 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_EisensteinWeightOne_coeff_e1Chi3.lean#L7-L8) |
| theta = `e1Chi3` (the bridge) | `…tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal` | [Thm, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_EisensteinWeightOne_tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal.lean#L8-L12) |
| mod-3 congruence | `EisensteinWeightOne.three_dvd_coeff_mul_e1Chi3_sub` | [Thm, line 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub.lean#L7-L8) |
| Fricke functional equation | `HexagonalLattice.summable_thetaTerm_and_tsum_neg_inv_three_mul` | [Thm, line 5](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_HexagonalLattice_summable_thetaTerm_and_tsum_neg_inv_three_mul.lean#L5-L13) |
| Poisson step | `hexTheta_eq_mul_self_neg_inv` | [Sol, line 641](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean#L641) |
| clean Fricke law | `hexTheta_fricke` | [Sol, line 752](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean#L752) |
| the $`U_3`$ law | `hexTheta_U_law` | [Sol, line 1377](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean#L1377) |
| $`\Gamma_0(3) = \langle T, U_3, -1\rangle`$ | `closure_T_U_neg_one_eq` | [Sol, line 1070](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean#L1070) |
| Thue / split prime represented | `exists_hexForm_eq_prime` | [Sol, line 3340](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean#L3340) |
| coprime multiplicativity | `HexInt.orbitCountMultiplicative_holds` | [Sol, line 3107](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean#L3107) |
| split prime-power count | `splitPrimePowCount` | [Sol, line 3704](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean#L3704) |
| $`r(n) = 6\sigma_\chi(n)`$ | `reprCountEqCoeffE1Chi3` | [Sol, line 3722](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean#L3722) |
| the headline | `EisensteinWeightOne.e1Chi3IsModular` | [Sol, line 3763](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean#L3763) |

## 10. Links

- FLT definition module:
  [`Definitions/Def_ModularForm_EisensteinChiNegThree.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_EisensteinChiNegThree.lean).
- FLT statement wrapper:
  [`Theorems/Thm_EisensteinWeightOne_e1Chi3IsModular.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_EisensteinWeightOne_e1Chi3IsModular.lean).
- FLT proof (3,816 lines):
  [`P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinWeightOne_e1Chi3IsModular.lean).
- Ported module:
  [`../lean/FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean`](../lean/FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean);
  ported vocabulary:
  [`../lean/FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean`](../lean/FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean).
- Companion computation:
  [`../pymath/hexagonal_theta.py`](../pymath/hexagonal_theta.py) and its
  [`expected output`](../pymath/hexagonal_theta.expected.txt).
- The integral-structure route:
  [013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md),
  [route-c-prime-scout.md](../studies/route-c-prime-scout.md).
- Port bookkeeping:
  [`../lean/topics/hecke/SET-6.md`](../lean/topics/hecke/SET-6.md),
  [`../lean/topics/hecke/TOPIC-route-c-prime-integral-structure.md`](../lean/topics/hecke/TOPIC-route-c-prime-integral-structure.md).
- Upstream lineage: this is the hexagonal/CM theta series; the general
  representation-number formula is the classical theorem of which
  `EisensteinWeightOne.e1Chi3IsModular` is the FLT instantiation, and the
  integral-slash use of the weight-one generator is Deligne–Serre,
  *Formes modulaires de poids 1*, Proposition 2.7 (as recorded in FLT's own
  documentation).
