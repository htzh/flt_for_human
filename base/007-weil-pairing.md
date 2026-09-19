# The Weil pairing

`base/` note. The Weil pairing is the canonical alternating form on the torsion of an
elliptic curve, and on the torsion of the Jacobian of a general curve. It is the reason
the mod-`n` Galois representation attached to a curve has determinant equal to the
cyclotomic character — hence the reason that representation is *odd*, which is one of the
hypotheses the FLT proof spends most of its energy satisfying. This note gives the
pairing, its two standard definitions, the characteristic-zero theory, the finite-field
shadow, the examples computed in [`../pymath/weil_pairing.py`](../pymath/weil_pairing.py),
and the shape the whole thing takes in the formalization.

Companions: [math/009](../math/009-hecke-jacobian-commute.md) builds the Jacobian `J₀(N)`
out of `Pic⁰` of a function field; [math/010](../math/010-function-field-generation.md)
supplies the function-field description of `X₀(N)`; [base/001](001-field-extensions-and-galois-basics.md)
fixes the Galois notation (`K ≃ₐ[S] K`, `AlgebraicClosure ℚ`); [base/005](005-cyclic-isogenies-and-level.md)
is the lattice/isogeny background used in §4.1. Citations are pinned to
`anthropics/fermats-last-theorem@aa2d8b3` and mathlib `v4.33.0`.

## 1. The pairing and its laws

Let $`E`$ be an elliptic curve over a field $`k`$ and let $`n`$ be invertible in
$`k`$. Write

- $`E[n] = \{T \in E(\bar k) : nT = O\}`$ for the $`n`$-torsion,
- $`\mu_n \subset \bar k^\times`$ for the $`n`$-th roots of unity.

Because $`n`$ is invertible, multiplication by $`n`$ is separable and
$`E[n] \cong (\mathbb{Z}/n)^2`$ as abelian groups. The Weil pairing is a canonical
perfect alternating pairing

$$e_n \colon E[n] \times E[n] \longrightarrow \mu_n .$$

Its defining properties are the following six. They are also literally how the
formalization states it: the elliptic-curve version,
`WeierstrassCurve.Affine.Point.IsWeilPairing`
([Def_GaloisRep_WeilPairing.lean, lines 18–33](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_WeilPairing.lean#L18-L33)),
has exactly the fields below, and existence is the existential
`HasWeilPairing` ([line 36](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_WeilPairing.lean#L36)).

| law | statement | Lean field |
|---|---|---|
| values | $`e_n(P,Q)^n = 1`$ | `mem_rootsOfUnity` |
| bilinear (left) | $`e_n(P+P',Q) = e_n(P,Q)e_n(P',Q)`$ | `add_left` |
| bilinear (right) | $`e_n(P,Q+Q') = e_n(P,Q)e_n(P,Q')`$ | `add_right` |
| alternating | $`e_n(P,P) = 1`$ | `alternate` |
| Galois equivariant | $`e_n(\sigma P, \sigma Q) = \sigma(e_n(P,Q))`$ | `equivariant` |
| nondegenerate | $`e_n \neq 1`$ as a form | `nondegenerate` |

Two remarks on the last two.

*Nondegeneracy* is stronger than the table suggests: the pairing is **perfect**. The
induced map $`E[n] \to \mathrm{Hom}(E[n], \mu_n)`$ is an isomorphism of $`(\mathbb{Z}/n)`$-modules.
Concretely, if $`P, Q`$ is a basis then $`\zeta = e_n(P,Q)`$ must be a primitive
$`n`$-th root of unity: if $`\zeta`$ had smaller order $`d`$, then every
$`e_n(aP+bQ, cP+dQ) = \zeta^{ad-bc}`$ would lie in $`\mu_d`$, and the pairing could not
see all of $`\mu_n`$ — so $`E[n] \to \mathrm{Hom}(E[n],\mu_n)`$, both sides of order
$`n^2`$, would fail to be injective. So nondegeneracy on a basis is exactly primitivity
of $`\zeta`$, which is what `../pymath/weil_pairing.py` checks as
`order(e_n(P,Q)) = n`.

*Equivariance* is the Galois-theoretic heart. Writing $`\chi_n \colon G_k \to (\mathbb{Z}/n)^\times`$
for the mod-$`n`$ cyclotomic character ($`\sigma(\zeta) = \zeta^{\chi_n(\sigma)}`$ for
$`\zeta \in \mu_n`$), equivariance reads

$$e_n(\sigma P, \sigma Q) = e_n(P,Q)^{\chi_n(\sigma)} .$$

## 2. Where the determinant comes from

The pairing is *why* the determinant of the mod-$`n`$ representation is the cyclotomic
character. The argument is two lines and worth spelling out, because every use in FLT
goes through it.

Fix a basis $`P, Q`$ of $`E[n]`$ and let $`\sigma`$ act by $`\sigma P = aP+bQ`$, $`\sigma Q = cP+dQ`$; write $`M`$ for its matrix in the basis, so $`\det M = ad-bc`$. Then bilinearity and alternation give

$$e_n(\sigma P, \sigma Q) = e_n(aP+bQ, cP+dQ) = e_n(P,Q)^{ad-bc} = e_n(P,Q)^{\det M}.$$

Compare with equivariance: if we write $`\zeta = e_n(P,Q)`$, then
$`e_n(\sigma P, \sigma Q) = \sigma(\zeta) = \zeta^{\chi_n(\sigma)}`$. Hence

$$\det \rho_{E,n}(\sigma) \equiv \chi_n(\sigma) \pmod n,$$

where $`\rho_{E,n} \colon G_k \to \mathrm{GL}_2(\mathbb{Z}/n)`$ is the representation on
$`E[n]`$. Two equivalent readings:

- the representation lands in the **symplectic similitudes**: the multiplier of the
  alternating form is the cyclotomic character,
  $`e_n(\rho(g)x, \rho(g)y) = \chi_n(g)e_n(x,y)`$;
- $`\det \rho_{E,n} = \chi_n`$, so the determinant is forced, not chosen.

For $`k = \mathbb{Q}`$ and $`n \gt 2`$, complex conjugation $`c`$ acts on
$`\mu_n`$ by inversion, $`\chi_n(c) = -1`$. So

$$\det \rho_{E,n}(c) = -1,$$

which is exactly the statement that $`\rho_{E,n}`$ is **odd**. This is where the
oddness hypothesis in Serre's conjecture comes from; the formalization names it
`ResidualGaloisRep.IsOdd`
([Def_GaloisRep_Residual.lean, line 57](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean#L57)):

```lean
def IsOdd (ρ : ResidualGaloisRep k) : Prop :=
  ∀ c : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, c * c = 1 → c ≠ 1 →
    LinearMap.det (ρ.ρ c) = -1
```

## 3. The divisorial definition, and Miller's algorithm

The theorem above is usually *proved* by constructing the pairing from functions. An
elliptic curve is a curve, and on a curve a degree-zero divisor is principal; the divisor
$`n[P] - n[O]`$ has degree $`0`$, so there is a rational function $`f_P`$ with

$$\mathrm{div}(f_P) = n[P] - n[O].$$

Then one sets

$$e_n(P,Q) = (-1)^n \frac{f_P(Q)}{f_Q(P)} .$$

The ratio is independent of the choices of $`f_P, f_Q`$ up to a constant — replacing
$`f_P`$ by $`cf_P`$ multiplies both sides consistently — and Weil reciprocity (the
identity $`f(\mathrm{div}\, g) = g(\mathrm{div}\, f)`$ for two functions on a curve) shows the
value is an $`n`$-th root of unity and depends only on the classes of $`P, Q`$. Miller's
algorithm evaluates $`f_P(Q)`$ with $`O(\log n)`$ group operations, by doubling and
adding and accumulating line/vertical functions; it is what
`../pymath/weil_pairing.py` calls `miller`.

This is the definition the FLT formalization uses, because it needs no intersection
theory of divisors on a scheme. The formalization's objects are function fields of
curves: `AlgebraicCurve.Place` (a DVR of the function field),
`AlgebraicCurve.Divisor := Place \to_0 \mathbb{Z}`, and `Pic⁰` as divisors of degree zero
modulo principal divisors
([Def_AlgebraicCurve_DivisorClassGroup.lean, lines 22, 179, 221–224](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L22)).
The pairing is a `WeilDatum`
([Def_AlgebraicCurve_WeilDatum.lean, lines 14–38](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_WeilDatum.lean#L14-L38)):
two divisors $`D_1, D_2`$ and two functions $`f_1, f_2`$ with
$`\mathrm{ord} f_i = n D_i`$, disjoint supports, rational places, and

```lean
def pairing : K :=
  Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁
```

which is the formula above with $`D_1 = [P] - [O]`$, $`D_2 = [Q] - [O]`$. The
existence and perfectness of the pairing on $`\mathrm{Pic}^0`$ of an arbitrary function
field is `AlgebraicCurve.Pic0.exists_weilPairing`
([Thm_AlgebraicCurve_Pic0_exists_weilPairing.lean, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_exists_weilPairing.lean#L16)),
and its nondegeneracy data is `WeilPairingData`
([Def_AlgebraicCurve_JacobianH1Autoduality.lean, line 170](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_JacobianH1Autoduality.lean#L170)).

## 4. Characteristic zero

### 4.1 Over $`\mathbb{C}`$: an explicit formula

Over $`\mathbb{C}`$ every elliptic curve is a complex torus: $`E(\mathbb{C}) = \mathbb{C}/\Lambda`$
for a lattice $`\Lambda = \mathbb{Z}\lambda_1 + \mathbb{Z}\lambda_2`$ with
$`\tau = \lambda_2/\lambda_1`$ in the upper half plane. Then

$$E[n] = \tfrac{1}{n}\Lambda / \Lambda \cong (\mathbb{Z}/n)^2,$$

and the Weil pairing has a closed form. Write $`u = a\lambda_1 + b\lambda_2`$ and
$`v = c\lambda_1 + d\lambda_2`$ with $`a,b,c,d \in \mathbb{Z}`$, and let
$`\zeta_n = e^{2\pi i/n}`$. Then

$$e_n\left(\frac{u}{n}, \frac{v}{n}\right) = \exp\left(\frac{2\pi i (ad-bc)}{n}\right) = \zeta_n^{ad-bc}.$$

The exponent is the determinant of the coordinate matrix of $`(u,v)`$ in the basis
$`(\lambda_1,\lambda_2)`$, i.e. the symplectic area form. All six laws of §1 are visible
in the formula: bilinearity and alternation are bilinearity and antisymmetry of the
determinant, and nondegeneracy is unimodularity of the lattice basis. Changing the basis
of $`\Lambda`$ by a matrix in $`\mathrm{SL}_2(\mathbb{Z})`$ (determinant one) leaves
the exponent unchanged modulo $`n`$, which is why the pairing is canonical rather than
basis-dependent. In the language of [base/005](005-cyclic-isogenies-and-level.md), the
exponent is the intersection number of the two $`n`$-division points on the torus.

**Worked example.** Take $`\Lambda = \mathbb{Z}[i] = \mathbb{Z} + \mathbb{Z}i`$,
$`\lambda_1 = 1`$, $`\lambda_2 = i`$, and $`n = 3`$. Then

$$e_3(a+bi, c+di) = \zeta_3^{ad-bc} \qquad (a,b,c,d \in \mathbb{Z}).$$

For instance $`e_3(1,i) = \zeta_3`$ (a primitive value, so nondegenerate),
$`e_3(1,1) = 1`$, $`e_3(i,i) = 1`$ (alternating), and
$`e_3(i,1) = \zeta_3^{-1} = \zeta_3^2`$, the required inverse relation.

### 4.2 Over a number field: Galois equivariance

Let $`K`$ be a number field and $`E/K`$ an elliptic curve. The absolute Galois group
$`G_K`$ acts on $`E[n]`$ and on $`\mu_n \subset \bar K`$, and the pairing is
equivariant: for $`\sigma \in G_K`$,

$$e_n(\sigma P, \sigma Q) = \sigma(e_n(P,Q)) = e_n(P,Q)^{\chi_n(\sigma)} .$$

That is the entire content of "the determinant is the cyclotomic character" from §2, now
over a number field. The formalization's cyclotomic character is
`TaylorWiles.cycloChar`
([Def_TaylorWiles_CyclotomicChar.lean, line 21](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_TaylorWiles_CyclotomicChar.lean#L21)):

```lean
noncomputable def cycloChar : (L ≃ₐ[ℚ] L) →* (ZMod m)ˣ
```

with the characteristic property `ζ ^ (cycloChar hζ σ).val = σ • ζ`.

For FLT the relevant curve is the Frey curve $`E_P`$, and the relevant statement is
about the mod-$`p`$ representation $`\bar\rho_{E,p} \colon G_{\mathbb{Q}} \to \mathrm{GL}_2(\mathbb{F}_p)`$:

$$\det \bar\rho_{E,p} = \chi_p, \qquad \text{hence } \bar\rho_{E,p} \text{ is odd.}$$

The formalization records the same two invariants in `ResidualGaloisRep.IsAttachedTo`
([line 48](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean#L48)): at a good prime $`\ell`$, the
characteristic polynomial of $`\rho(\mathrm{Frob}_\ell)`$ is

$$X^2 - a_\ell X + \ell,$$

whose constant term $`\ell`$ is the determinant $`\det\rho(\mathrm{Frob}_\ell) = \chi_p(\mathrm{Frob}_\ell) \equiv \ell`$ — the
Weil pairing again, this time reading off the determinant from the Frobenius polynomial.

### 4.3 The Tate module

Passing to $`\ell`$-power torsion and taking the inverse limit gives the Tate module
$`T_\ell E = \varprojlim_k E[\ell^k] \cong \mathbb{Z}_\ell^2`$. The pairings
$`e_{\ell^k}`$ assemble into a perfect alternating pairing

$$e_\ell \colon T_\ell E \times T_\ell E \longrightarrow \mathbb{Z}_\ell(1),$$

where $`\mathbb{Z}_\ell(1) = \varprojlim_k \mu_{\ell^k}`$ is the Tate twist. Equivariance
becomes the similitude relation

$$e_\ell(\rho_{E,\ell}(g)x, \rho_{E,\ell}(g)y) = \chi_\ell(g) e_\ell(x,y),$$

so $`\rho_{E,\ell}`$ is a Galois representation into $`\mathrm{GSp}_2(\mathbb{Z}_\ell)`$
with multiplier $`\chi_\ell`$, and $`\det \rho_{E,\ell} = \chi_\ell`$. This is what makes
$`T_\ell E`$ a *symplectic* Galois module, and it is the form in which the pairing is used
in deformation theory and $`R = T`$ arguments.

## 5. Finite fields: the Frobenius case

Over a finite field $`\mathbb{F}_q`$ the same theory holds, with $`G_{\mathbb{F}_q}`$
generated by the $`q`$-power Frobenius $`\pi`$. Equivariance for $`\pi`$ says

$$e_n(\pi P, \pi Q) = e_n(P,Q)^q,$$

and the determinant statement is $`\det \rho(\pi) \equiv q \pmod n`$. The characteristic
polynomial of $`\rho_{E,\ell}(\pi)`$ is $`T^2 - a_q T + q`$, so the pairing explains the
*constant term* $`q`$: it is the determinant, i.e. the multiplier of the alternating form.
Hasse's bound $`|a_q| \le 2\sqrt{q}`$ and the rank statements
$`T_\ell E \cong \mathbb{Z}_\ell^2`$ are the other half of the same picture.

This is exactly what the finite-field examples in §6 compute, and it is the honest
"warm-up" for the number-field case: the Frobenius matrix in $`\mathrm{GL}_2(\mathbb{Z}/n)`$
plays the role of $`\rho(\sigma)`$ of §4.2, and the two invariants one can read off are
the same, $`\det = q`$ and $`\mathrm{tr} = a_q`$.

## 6. The examples, worked

The numbers below are the golden output of
[`../pymath/weil_pairing.py`](../pymath/weil_pairing.py); here is the mathematics behind
each one. Elements of $`\mathbb{F}_{25}`$ are written in the basis
$`1, t`$ with $`t^2 + t + 1 = 0`$.

### 6.1 $`\mathbb{F}_7`$, $`n=3`$: full torsion over a prime field

$`E \colon y^2 = x^3 + 2`$ over $`\mathbb{F}_7`$ has $`9`$ points, so
$`E[3] = E(\mathbb{F}_7)`$: the entire 3-torsion is rational. Since
$`\#E[3] = 9 = 3^2`$, a basis exists; the canonical one chosen by the demo is

$$P = (0,3), \qquad Q = (3,1), \qquad \zeta = e_3(P,Q) = 4 \in \mathbb{F}_7.$$

Now $`4^3 = 64 \equiv 1`$ and $`4 \neq 1`$, so $`\zeta`$ is a primitive cube root of
unity — the pairing is nondegenerate. The whole table is $`e_3(aP,bQ) = 4^{ab}`$, and
the Gram matrix in the basis is

$$\begin{pmatrix} 1 & 4 \\\\ 2 & 1 \end{pmatrix},$$

with $`2 = 4^{-1}`$: zero diagonal (alternating) and off-diagonal primitive
(nondegenerate). This is the smallest example in which all six laws of §1 are visible.

### 6.2 $`\mathbb{F}_{41}`$, $`n=5`$: nothing special about $`3`$

$`E \colon y^2 = x^3 + 15x`$ over $`\mathbb{F}_{41}`$ has $`50`$ points, so
$`25 \mid \#E`$ and $`E[5] = (\mathbb{Z}/5)^2`$ is rational. The canonical basis pairs to
$`\zeta = 18`$, whose order is $`5`$ (since $`5 \mid 40`$ and $`18 \not\equiv 1`$). The
example exists to show the construction is uniform in $`n`$, and to separate "the pairing
exists" from any accident of $`n = 3`$.

### 6.3 $`\mathbb{F}_{25}`$: Frobenius and the determinant

Take $`E \colon y^2 = x^3 + 1`$ over $`\mathbb{F}_5`$. It has $`6`$ points, so
$`a_5 = 5 + 1 - 6 = 0`$. The 3-torsion of this curve is **not** rational over
$`\mathbb{F}_5`$; it first becomes rational over $`\mathbb{F}_{25} = \mathbb{F}_5[t]/(t^2+t+1)`$,
where $`\#E = 36`$. So we work over $`\mathbb{F}_{25}`$, pair a basis

$$P = (0,1), \qquad Q = (1, 2t+1), \qquad \zeta = e_3(P,Q) = 4t+4,$$

and let $`\pi`$ be the $`5`$-power Frobenius $`(x,y) \mapsto (x^5,y^5)`$. Because
$`E[3] \subset E(\mathbb{F}_{25})`$, we have $`\pi^2 = 1`$ on $`E[3]`$, and the matrix of
$`\pi`$ in the basis is diagonal:

$$\pi(P) = P, \qquad \pi(Q) = 2Q, \qquad \text{matrix } \begin{pmatrix} 1 & 0 \\\\ 0 & 2 \end{pmatrix}.$$

Reading off §2: $`\det = 2 \equiv 5 = p \pmod 3`$ (the cyclotomic character at $`p`$),
and $`\mathrm{tr} = 0 = a_5 \pmod 3`$. Equivariance also holds directly:
$`e_3(\pi P, \pi Q) = e_3(P,Q)^5 = \zeta^5 = \zeta^2 = t`$, and indeed
$`e_3(\pi P, \pi Q) = e_3(P, 2Q) = \zeta^2 = t`$. The characteristic polynomials
$`T^2 + 5`$ (for $`\pi`$) and $`T^2 + 10T + 25`$ (for $`\pi^2`$, with
$`a_{25} = 25 + 1 - 36 = -10`$) have constant terms $`5`$ and $`25`$: the
determinants $`p`$ and $`q`$ by which the pairing is multiplied.

### 6.4 Miller's function, explicitly

On the $`\mathbb{F}_7`$ curve with $`n = 3`$, Miller's algorithm computes the
divisorial formula of §3:

$$f_P(Q) = 5, \qquad f_Q(P) = 4, \qquad (-1)^3\frac{f_P(Q)}{f_Q(P)} = \frac{5}{4} \cdot (-1) = 4 = e_3(P,Q).$$

The values $`f_P(Q)`$ and $`f_Q(P)`$ depend on the normalization of $`f_P`$ (a
nonzero constant), but the quotient does not, which is the content of §3.

## 7. How the FLT project uses it

### 7.1 The formal shape

There are two formalizations of the pairing, matching the two settings:

- **Elliptic curves.** `IsWeilPairing` / `HasWeilPairing` on
  `Submodule.torsionBy ℤ (W'⁄K).Point n`
  ([Def_GaloisRep_WeilPairing.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_WeilPairing.lean#L18-L38)).
  The formalization does not construct the pairing; it *assumes its laws*
  existentially and proves things from the laws. This is why §1's table is not a
  pedagogical device but the actual interface.
- **Function fields / Jacobians.** The divisorial pairing on `Pic⁰` of any function field
  satisfying `IsCurveOver`: `WeilDatum`, `WeilPairingData`, `Pic0.exists_weilPairing`,
  and the divisorial Weil-pairing data in
  `Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean`. This is the setting used
  for `J₀(N)`, where the pairing is *constructed* rather than assumed.

### 7.2 The cyclotomic relation on $`J_0(N)`$

For the modular Jacobian the formalization proves the Tate-module form of §4.3 directly:
`ModularCurve.JZero.exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul`
([line 22](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_JZero_exists_tateModule_pairing_rep_eq_cyclotomicCharacter_mul.lean#L22))
produces a $`\mathbb{Z}_p`$-bilinear form $`B`$ on the Tate module of $`J_0(N)`$ that is nondegenerate in each variable and satisfies

$`B(\rho(\sigma)x, \rho(\sigma)y) = \chi_p(\sigma)\, B(x,y)`$

for every $`\sigma \in G_{\mathbb{Q}}`$. That is the ℓ-adic similitude relation of §4.3 for
the Jacobian, with the cyclotomic character appearing exactly as the multiplier. On the
same object, `Pic0.finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero`
([line 18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_finrank_rationalTateModule_eq_two_mul_genusFF_of_charZero.lean#L18))
gives $`\mathrm{rank}\,T_\ell \mathrm{Pic}^0 = 2g`$: the module is symplectic of rank
$`2g`$, the higher-genus form of $`T_\ell E \cong \mathbb{Z}_\ell^2`$.

### 7.3 Why the proof needs it

Three places in the argument depend on the pairing:

- **Oddness of the Frey representation.** $`\det\bar\rho_{E,p} = \chi_p`$ forces
  $`\bar\rho_{E,p}`$ odd (§2, §4.2). Serre's conjecture and the modularity-lifting
  theorems require an odd representation; without the pairing there would be no reason
  for the determinant to be $`\chi_p`$ at all. The formalization isolates this as
  `ResidualGaloisRep.IsOdd`.
- **The cofixed line in the reducibility argument.** If $`\bar\rho_{E,p}`$ is reducible,
  a Galois-stable line in $`E[p]`$ has a Galois-cofixed quotient line; Serre's observation
  is formalized as `FreyPackage.frey_reducible_hasCofixedLine`. The alternating form is
  what relates a stable submodule to its orthogonal complement and makes the dichotomy a
  statement about lines rather than arbitrary submodules.
- **The Tate module of $`J_0(N)`$.** The Galois representation on $`J_0(N)[p]`$,
  used in Mazur's Eisenstein-ideal argument and in the level-lowering steps, is a
  symplectic module with multiplier $`\chi_p`$ (§7.2). The rank-$`2g`$ and
  cyclotomic-multiplier facts are inputs to that machinery.

### 7.4 The mathlib vocabulary involved

The formal statements live in terms of a small amount of mathlib:

- `rootsOfUnity n K` — the values of the pairing (mathlib `NumberTheory/RootsOfUnity`);
- `Submodule.torsionBy ℤ M n` — the torsion subgroup $`M[n]`$, i.e. $`E[n]`$ or
  $`J[n]`$ (mathlib `LinearAlgebra/Torsion`);
- `ZMod n`, `(ZMod n)ˣ` — the coefficient ring and the cyclotomic character's target;
- `LinearMap.det` — the determinant in §2;
- `Module.finrank` — the rank $`2`$ or $`2g`$ statements.

## 8. Seeing it run

[`../pymath/weil_pairing.py`](../pymath/weil_pairing.py) computes §6 with sympy-backed
finite fields. Its output `weil_pairing.expected.txt` is written as an explanation, not
just a computation, and its 27 `check` lines correspond one-to-one to the laws of §1 and
the determinant statement of §2:

- `e_n(P,Q)^n = 1`, `order(e_n(P,Q)) = n`, `e_n(P,P) = 1`, `e_n(Q,P) = e_n(P,Q)^-1`,
  `bilinear`, `alternating on all of E[n]` — §1;
- `Galois equivariance`, `det(π) = p mod n`, `trace(π) = a_p mod n`, `π² fixes E[n]` — §2
  and §4.3;
- `Miller's formula reproduces the pairing` — §3.

The characteristic-zero formula of §4.1 is not yet in the demo; it would be a natural
second script, since the lattice $`\mathbb{Z}[i]`$ example is a finite computation over
Gaussian integers and needs no algebraic closure.

## References

- J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009,
  Ch. III §8 (the pairing, properties, the determinant/cyclotomic relation) and Ch. VII
  (the Tate module).
- J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151,
  Springer 1994, Ch. I §2 and Ch. II (the analytic pairing on $`\mathbb{C}/\Lambda`$,
  the Riemann form).
- J.-P. Serre and J. Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968),
  492–517 (the pairing on the Tate module of an abelian variety).
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005,
  §8 and §9 (Galois representations attached to elliptic curves and the cyclotomic
  determinant).
