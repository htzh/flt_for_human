# The T side of $`R = T`$: the definition layer

**Status.** Mathematical exposition of the definitions, pinned to the FLT pin
`aa2d8b3`. This note is about the *mathematics of the definitions*, in the order
the Lean import closure forces; the Lean inventory, the graph measurements and the
port plan live in
[../studies/r-equals-t-in-the-proof-base.md](../studies/r-equals-t-in-the-proof-base.md).
Companions: [../base/011-deformations-hecke-algebras-and-r-equals-t.md](../base/011-deformations-hecke-algebras-and-r-equals-t.md)
(the $`R = T`$ theorem and the deformation theory), [../base/014-hecke-operators.md](../base/014-hecke-operators.md)
and [009-hecke-jacobian-commute.md](009-hecke-jacobian-commute.md) (the Hecke
operators), [012-sturm-bound.md](012-sturm-bound.md) and
[013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md)
(the lattice and its finiteness), [015-weight-two-hecke-periods.md](015-weight-two-hecke-periods.md)
(the weight-two periods).

The subject is the **T side**: the ring $`T`$ together with the map from the Hecke
algebra and the Galois representation it carries. Everything below is the
definitional content that a candidate $`T`$ has to *be*, spelled out as
mathematics. The import closure of the T-side package is 16 definition modules
(1,755 pin lines); they are listed with their roles in §7.

## 0. What has to be defined

To state "$`T`$ is the Hecke algebra side of $`R = T`$" one has to be able to say:

1. what a **Galois representation** is, in the two forms used — residual (over the
   residue field of a local ring) and adic (over the local ring itself) — together
   with sameness of representations, ramification, and Frobenius elements;
2. what the **universal deformation ring** $`R`$ is (the partner, defined here
   because the T package is stated against the same Galois vocabulary);
3. what the **Hecke algebra** $`\mathbb{T}`$ is, as a ring of operators, and what
   its **integral lattice** and **lattice algebra** are;
4. what the **local Hecke algebra** $`T_\theta`$ at a residual eigensystem $`\theta`$
   is;
5. what **Hecke–Galois data** is — the package that equips $`T`$ with the map
   $`\pi : \mathbb{T} \to T`$ and the representation $`\rho`$;
6. what a **patching level** is (the Taylor–Wiles auxiliary structure).

The definitions are taken in that order below.

## 1. The Galois substrate

### 1.1 The group, and representations that are continuous for a finite level

Let

$$G_{\mathbb{Q}} \\;=\\; \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})
  \\;=\\; (\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}),$$

realized in Lean as `AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`. A homomorphism
$`\rho : G_{\mathbb{Q}} \to M`$ **factors through a finite level** when there is a
finite-dimensional intermediate field $`L/\mathbb{Q}`$ such that every
$`\sigma`$ fixing $`L`$ pointwise satisfies $`\rho(\sigma) = 1`$
(`GaloisFactorsThroughFiniteLevel`). Since $`G_{\mathbb{Q}}`$ is compact and the
target in the residual case is finite, this is exactly continuity; for an adic
target the same condition is imposed modulo $`\mathfrak{m}^n`$ (§1.5).

### 1.2 Residual representations

A **residual Galois representation** over a field $`k`$ (`ResidualGaloisRep k`) is

- a $`k`$-vector space $`V`$ of dimension $`2`$ (`finrank_eq : Module.finrank k V = 2`),
- a monoid homomorphism $`\rho : G_{\mathbb{Q}} \to \mathrm{End}_k(V)`$,
- a proof that $`\rho`$ factors through a finite level.

The structure is a $`2`$-dimensional representation of $`G_{\mathbb{Q}}`$ over
$`k`$ that is continuous for the discrete topology. Its five predicates are:

| predicate | mathematics |
|---|---|
| `IsIrreducible` | no nonzero proper $`G_{\mathbb{Q}}`$-stable subspace of $`V`$ |
| `IsAbsolutelyIrreducible` | $`V \otimes_k \bar{k}`$ is irreducible — the representation stays irreducible over the algebraic closure |
| `IsOdd` | for complex conjugation $`c`$ (so $`c^2 = 1`$, $`c \neq 1`$), $`\det \rho(c) = -1`$; equivalently $`\det \rho`$ is the cyclotomic character, the "odd" of Serre's conjecture |
| `IsUnramifiedAt q` | $`\rho`$ is trivial on the inertia subgroup at every place over $`q`$ |
| `IsAttachedTo f φ` | $`\rho`$ is the mod-$`k`$ representation attached to the eigenform $`f`$: for good $`\ell`$, $`\mathrm{charpoly}(\rho(\mathrm{Frob}_\ell)) = X^2 - \varphi(a_\ell)\,X + \ell`$ |

`IsAttachedTo` is the bridge from the modular side: $`f`$ is a weight-$`2`$ cusp
form on $`\Gamma_0(N)`$, $`\varphi : \overline{\mathbb{Z}} \to k`$ a character of
the coefficient ring, and $`a_\ell`$ the $`\ell`$-th $`q`$-coefficient of $`f`$.
Coefficient extension is `baseChange` ($`k \to k'`$) and `baseChangeAlong φ`.

The FLT application feeds in the representation that exists *a priori*: for a
Weierstrass curve $`W/\mathbb{Q}`$ and a prime $`p`$, the action of
$`G_{\mathbb{Q}}`$ on the $`p`$-torsion $`E[p] \subset E(\overline{\mathbb{Q}})`$
is a $`2`$-dimensional $`\mathbb{F}_p`$-representation once one knows
$`\#E[p] = p^2`$ and that the action factors through a finite level;
`WeierstrassCurve.residualGaloisRepOf` packages exactly that. The underlying
algebra — the action of $`G_{\mathbb{Q}}`$ on $`E(K)`$, its $`n`$-torsion
$`E[n]`$, stability of submodules (`IsGaloisStable`), irreducibility
(`GaloisRepIsIrreducible`), the action as a homomorphism
$`\mathrm{galoisRepModuleEnd} : G_{\mathbb{Q}} \to \mathrm{End}_{\mathbb{Z}/n}(E[n])`$
and its trace `galoisTrace` — is the content of `Def_FLTPrelim_GaloisRep` and
`Def_EllipticCurve_FrobeniusTrace`.

### 1.3 Sameness of representations

`Equiv ρ₁ ρ₂` is a $`G_{\mathbb{Q}}`$-equivariant linear isomorphism
$`\rho_1.V \simeq \rho_2.V`$; `IsEquiv` is `Nonempty (Equiv …)`. The groupoid laws
`refl`/`symm`/`trans` and compatibility with `baseChangeAlong` are proved. This is
the correct notion of "the same representation": not equality of the underlying
vector spaces, but $`G`$-equivariant isomorphism. Every statement about residual
representations in the R=T argument — "the residual representation of $`\rho`$ is
$`\bar\rho`$", "the two sides have the same reduction" — is an `IsEquiv`.

### 1.4 Places, inertia, and Frobenius

`ValuationSubring L` is a place of $`L`$ (a valuation ring with fraction field
$`L`$). For a rational prime $`q`$:

- `A.LiesOverPrime q` means $`q`$ is a nonunit of $`A`$, i.e. the place lies over
  $`q`$;
- `inertiaSubgroupIn` and the decomposition subgroup are the usual inertia and
  decomposition groups of the place, as subgroups of $`\mathrm{Gal}(L/K)`$;
- `IsFrobeniusAt A σ q` means $`\sigma`$ lies in the decomposition group and acts
  on the residue field by $`x \mapsto x^q`$ — an arithmetic Frobenius at the place.

`GaloisRepUnramifiedAt` for a curve is the pointwise statement that every inertia
element fixes the $`n`$-torsion; for a `FreyPackage` it is the same statement for
the Frey curve at the prime $`p`$ of the package.

### 1.5 Adic representations

For a commutative local ring $`A`$ with maximal ideal $`\mathfrak{m}`$, a
homomorphism $`\rho : G_{\mathbb{Q}} \to \mathrm{End}_A(V)`$ is **adically
continuous** (`GaloisActionIsAdicContinuous`) when for every $`n`$ there is a
finite $`L/\mathbb{Q}`$ such that every $`\sigma`$ fixing $`L`$ satisfies

$$\rho(\sigma) v - v \\;\in\\; \mathfrak{m}^n V
\qquad\text{for all } v \in V .$$

This is continuity of the action for the $`\mathfrak{m}`$-adic topology on
$`\mathrm{End}_A(V)`$ with discrete quotient at each level.

A **adic Galois representation** (`GaloisRepAdic A`) is then

- a free $`A`$-module $`V`$ of finite rank with `finrank_eq : Module.finrank A V = 2`,
- a representation $`\rho : G_{\mathbb{Q}} \to \mathrm{End}_A(V)`$,
- a proof of adic continuity.

From it one derives: `IsUnramifiedAt`, the determinant `det` (a homomorphism to
$`A^\times`$) and trace `trace`, base change `baseChangeAlong φ` along a local
homomorphism, and the **residual representation**

$$\rho \bmod \mathfrak{m} \\;=\\; V \otimes_A k, \qquad k = A/\mathfrak{m} =
\texttt{IsLocalRing.ResidueField A},$$

(`residual`), which is a `ResidualGaloisRep k` — adic continuity at level $`1`$
supplies the finite-level condition. `Equiv`/`IsEquiv` and `Equiv.residual` carry
isomorphism down to the reductions. When $`A = k`$ is a field the two notions
coincide: `ofResidualGaloisRep`/`toResidualGaloisRep` convert both ways.

This is the object $`\rho`$ in *both* structures of §2 and §4: the universal
deformation over $`R`$, and the representation carried by $`T`$.

### 1.6 The Frey package and the modularity vocabulary

The arithmetic inputs the route uses are also definitions here:

- `FreyPackage`: integers $`a, b, c \neq 0`$, a prime $`p \ge 5`$ with
  $`a^p + b^p = c^p`$, $`\gcd(a,b) = 1`$, $`a \equiv 3 \pmod 4`$,
  $`b \equiv 0 \pmod 2`$, together with the Frey curves `freyCurveInt`/`freyCurve`;
- `WeierstrassCurve.card`, `traceOfFrobenius`, `apOfModel`, `IsGoodPrimeFor`,
  `IsSemistableModel`, `IsIntegralModelOf`;
- `CuspForm.IsNormalizedEigenform`: $`a_1 = 1`$, multiplicativity at coprime
  indices, and the two prime-power recursions;
- `WeierstrassCurve.IsModularModelOfLevel N` / `IsModularModel` / `IsModular`:
  existence of a normalized eigenform on $`\Gamma_0(N)`$ whose $`q`$-coefficients
  match $`a_\ell(W)`$ at good primes.

## 2. The universal deformation ring $`R`$

Fix a complete discrete valuation ring $`\mathcal{O}`$ with residue field $`k`$, a
residual representation $`\bar\rho`$ over $`k`$, and a **deformation condition**
$`\mathcal{D}`$: a predicate on adic representations over local
$`\mathcal{O}`$-algebras (ordinary, flat, unramified outside a set $`S`$, …).

A **deformation** of $`\bar\rho`$ of type $`\mathcal{D}`$ over an
$`\mathcal{O}`$-algebra $`A`$ is an adic representation $`\rho_A`$ of type
$`\mathcal{D}`$ whose reduction is $`\bar\rho`$ up to equivalence. The universal
deformation ring represents the resulting functor.

`GaloisRep.DeformationRingData 𝒪 ρbar 𝒟` is the structure asserting that $`R`$ is
that representing object:

| field | mathematics |
|---|---|
| `R` with `CommRing`, `IsLocalRing`, `IsNoetherianRing`, `IsAdicComplete`, `Algebra 𝒪 R`, `IsLocalHom` | $`R`$ is a complete local Noetherian $`\mathcal{O}`$-algebra with local structure map |
| `residue_surjective` | the residue field of $`R`$ is generated by that of $`\mathcal{O}`$ |
| `absIrr` | $`\bar\rho`$ is absolutely irreducible (the hypothesis under which deformation theory is well behaved) |
| `ρ : GaloisRepAdic R`, `isOfType : 𝒟 ρ` | the universal deformation, of the prescribed type |
| `residual_isEquiv` | $`\rho \bmod \mathfrak{m}_R \cong \bar\rho \otimes k`$ |
| `universal` | for every test algebra $`A`$ and every deformation $`\rho_A`$ of type $`\mathcal{D}`$ reducing to $`\bar\rho`$, there is a **unique** local $`\mathcal{O}`$-algebra map $`R \to A`$ along which $`\rho`$ base-changes to $`\rho_A`$ |

The mathematics of this structure — Mazur's existence theorem, the tangent space,
and the numerical criterion — is [base/011](../base/011-deformations-hecke-algebras-and-r-equals-t.md)
§§1–2. Note that $`\mathcal{D}`$ is a *parameter*, which is how "ordinary",
"flat", "minimal" become data rather than hard-coded cases. The definition itself
imports no theorems: its closure is nine definition modules and mathlib.

## 3. The Hecke side

### 3.1 Hecke operators and the Hecke algebra

The operators are the slash averages over the $`\ell+1`$ cosets of
$`\Gamma_0(N\ell)/\Gamma_0(N)`$ and the $`q`$-power map: `heckeTLin` ($`T_\ell`$,
for $`\ell \nmid N`$) and `heckeULin` ($`U_q`$, for $`q \mid N`$), acting on
$`\mathrm{CuspForm}(\Gamma_0(N), k)`$. Their construction and commutation are the
subject of [../base/014](../base/014-hecke-operators.md) and
[009](009-hecke-jacobian-commute.md); here they matter only as the generators of
the ring.

The **Hecke algebra** is the $`\mathbb{Z}`$-subalgebra of the endomorphism ring
generated by the operators away from $`S`$:

```lean
def heckeAlgebra : Subalgebra ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :=
  Algebra.adjoin ℤ (heckeGenerators N k S)
```

with `heckeGenerators` the set of all $`T_\ell`$ ($`\ell`$ prime, $`\ell \nmid N`$,
$`\ell \notin S`$) and $`U_q`$ ($`q \mid N`$ prime, $`q \notin S`$). It is a
commutative ring (the operators commute), and `heckeAlgebra.T` / `heckeAlgebra.U`
are the distinguished elements. Because it is a `Subalgebra` of endomorphisms
rather than a quotient presentation, every algebraic identity about $`T_\ell`$ and
$`U_q`$ is a statement about these elements.

### 3.2 The integral lattice, and the algebra acting on it

$$L(N,k) \\;=\\; \mathrm{intLattice}(N,k) \\;=\\; \mathrm{span}_{\mathbb{Z}}
  \\{\\, f \in S_k(\Gamma_0(N)) \\;:\\; \text{all } q\text{-coefficients of } f
  \text{ lie in } \mathbb{Z} \\,\\},$$

a $`\mathbb{Z}`$-submodule of the complex cusp forms. `HasIntegralStructure N k`
says this lattice is a full lattice:

$$\mathrm{span}_{\mathbb{C}}\\, L(N,k) \\;=\\; S_k(\Gamma_0(N)).$$

The Hecke operators preserve the lattice, so each $`t \in \mathbb{T}`$ restricts
to a $`\mathbb{Z}`$-linear endomorphism of $`L(N,k)`$:
`latticeRestrict` produces the restriction, and `latticeActionHom` assembles them
into a ring homomorphism

$$\mathbb{T} = \texttt{heckeAlgebra} \\;\longrightarrow\\;
  \mathrm{End}_{\mathbb{Z}}\bigl(L(N,k)\bigr).$$

Its image is `heckeLatticeAlgebra`, a $`\mathbb{Z}`$-subalgebra of
$`\mathrm{End}_{\mathbb{Z}}(L(N,k))`$. It is a **finite free** $`\mathbb{Z}`$-module:
finiteness is the finite generation of the lattice (`intLattice_fg`, which rests on
the Sturm bound, [012](012-sturm-bound.md)), and freeness follows because
$`L(N,k)`$, and hence its endomorphism ring, is torsion-free. The homomorphism

$$\texttt{latticeRestrictHom} : \mathbb{T} \twoheadrightarrow
  \texttt{heckeLatticeAlgebra}$$

is surjective by construction and **bijective exactly when
`HasIntegralStructure` holds** (`latticeRestrictHom_bijective`): the integral
lattice determines the Hecke algebra when it is full. This is where the ported
integral-structure and finiteness work ([013](013-integral-structure-gamma1-basis.md))
sits.

### 3.3 The local Hecke algebra $`T_\theta`$

Fix a residual eigensystem: a ring homomorphism

$$\theta : \mathbb{T} \\;\longrightarrow\\; k = \mathcal{O}/\mathfrak{m}_{\mathcal{O}}$$

(sending $`T_\ell`$ to the residue of the $`\ell`$-th coefficient of a mod-$`k`$
eigenform). The local Hecke algebra is the localisation of the lattice algebra at
the kernel of $`\theta`$, base-changed to $`\mathcal{O}`$. Concretely:

1. `residualCharacter` is the composite
   $`\mathcal{O} \otimes_{\mathbb{Z}} \mathbb{T} \to \mathcal{O} \to k`$ extended
   by $`\theta`$ on the second factor;
2. `heckeCharKernel` is its kernel — a prime, in fact maximal, ideal;
3. `heckeBaseAlgebra` $`= \mathcal{O} \otimes_{\mathbb{Z}}`$
   `heckeLatticeAlgebra`, a finite free $`\mathcal{O}`$-algebra;
4. `latticeBaseChange` is the base change of `latticeRestrictHom`;
5. `heckeLocalSubmonoid` is the image under it of the complement of
   `heckeCharKernel`;
6. `heckeLocal` is the localisation of `heckeBaseAlgebra` at that submonoid, and
   `heckeLocalIdeal` is the image of `heckeCharKernel`;
7. `heckeLocal.π : 𝕋 → T_\theta` is the structure map from the Hecke algebra.

Mathematically $`T_\theta`$ is the local ring of the base-changed integral Hecke
algebra at the maximal ideal cut out by $`\theta`$: the local piece through which
the eigenform family with residual eigensystem $`\theta`$ factors. The structure
section proves that it is a **local Noetherian $`\mathcal{O}`$-algebra, finite free
over $`\mathcal{O}`$**, with local structure map $`\mathcal{O} \to T_\theta`$, and —
given `HasIntegralStructure` — **adically complete**. Finiteness and freeness are
proved by writing $`T_\theta`$ as the localisation of the finite free
`heckeBaseAlgebra` at a maximal ideal and using that a finite module over a
complete local ring is complete; the last input is the trio of algebra facts of
§6. The `IsLocalRing`/`IsAdicComplete`/`IsLocalHom` **instances** are stated under
`[Fact (HasIntegralStructure N 2)]`, the hypothesis that makes the lattice full.

## 4. Hecke–Galois data: the T package

`CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T` packages a candidate $`T`$. It has eight
fields; mathematically they say:

| field | mathematics |
|---|---|
| `π : heckeAlgebra N 2 S →+* T` | $`T`$ receives the Hecke algebra: the map $`\mathbb{T} \to T`$ that $`R \to T`$ is compared with |
| `residue_π` | $`\pi`$ reduces to $`\theta`$: mod $`\mathfrak{m}_T`$, every Hecke operator has the residual eigenvalue |
| `adjoin_range_π : Algebra.adjoin 𝒪 (Set.range π) = ⊤` | $`T`$ is generated over $`\mathcal{O}`$ by the Hecke operators — it is a Hecke algebra, not an arbitrary quotient |
| `exists_point` | every $`\mathcal{O}`$-valued eigensystem reducing to $`\theta`$ factors through $`T`$; the localisation property, i.e. $`T`$ sees all the classical points of its component |
| `residue_surjective` | the residue field of $`T`$ is generated by that of $`\mathcal{O}`$ |
| `ρ : GaloisRepAdic T` | $`T`$ carries the Galois representation of the eigenform family |
| `charpoly_frob` | Eichler–Shimura: at every good prime $`\ell \nmid N`$, $`\ell \notin S`$ and Frobenius $`\mathrm{Frob}_\ell`$, $`\mathrm{charpoly}(\rho(\mathrm{Frob}_\ell)) = X^2 - \pi(T_\ell) X + \ell`$ |
| `residual_absIrr` | the residual representation $`\rho \bmod \mathfrak{m}_T`$ is absolutely irreducible |

The datum is the exact shape the universal property of $`R`$ is applied to: it
supplies a test algebra $`T`$, a deformation $`\rho`$ of $`\bar\rho`$, and the
residual identification. It is deliberately stated *without* mentioning $`R`$, so
that it can instantiate both the concrete case $`T = T_\theta`$ and the abstract
case in the universal-property argument.

## 5. Patching levels

Taylor–Wiles patching replaces $`R`$ by a power-series ring and $`T`$ by a
quotient, in a way that makes the size comparison transparent. The definitions are
purely algebraic and import only mathlib.

A `PatchingLevel 𝒪 r R M` is a presentation of $`R`$ as a quotient of a power
series ring, compatible with the module $`M`$:

- a module $`N`$ over $`\mathcal{O}[[X_1,\dots,X_r]]`$;
- an $`\mathcal{O}`$-algebra endomorphism $`\varphi`$ of
  $`\mathcal{O}[[X_1,\dots,X_r]]`$ and a surjection
  $`\psi : \mathcal{O}[[X_1,\dots,X_r]] \twoheadrightarrow R`$ with
  $`\psi(\varphi(X_i)) = 0`$;
- a surjection $`\pi : N \twoheadrightarrow M`$ compatible with $`\psi`$;
- the kernel of $`\pi`$ is exactly the submodule generated by the
  $`\varphi(X_i)`$;
- a finite generating family $`b`$ of $`N`$ whose relations are a prescribed ideal
  $`J`$.

A `PatchingDatum 𝒪 ℓ r R M` is a family of levels indexed by $`n \in \mathbb{N}`$
with

$$J_n \\;=\\; \bigl((1+X_j)^{\ell^n} - 1 \\;:\\; j = 1,\dots,r\bigr).$$

The exponents $`\ell^n`$ are the Taylor–Wiles auxiliary-prime levels: patching
along $`n`$ and taking the limit $`n \to \infty`$ produces a ring in which the
relation ideal vanishes, which is what makes the patched module free and the
quotient map an isomorphism. The mathematics of how a patching datum is produced
(the numerical criterion, Selmer groups) is [base/011](../base/011-deformations-hecke-algebras-and-r-equals-t.md)
§4; the definitions above only fix the shape of the object.

## 6. The three algebra inputs the local Hecke algebra pulls in

Among the T-side definition modules, the one that pulls in *new* theorems is
`Def_CuspForm_HeckeLocal` — three commutative-algebra facts (the Hecke-algebra
definition modules pull in only already-ported Hecke theorems):

1. **`IsAdicComplete.of_module_finite`.** If $`R`$ is Noetherian, $`I`$ an ideal,
   $`R`$ is $`I`$-adically complete, and $`M`$ is a finite $`R`$-module, then
   $`M`$ is $`I`$-adically complete.
2. **`IsLocalRing.isAdicComplete_of_module_finite`.** If $`\mathcal{O}`$ is a
   complete local Noetherian ring and $`T`$ is a finite $`\mathcal{O}`$-algebra
   with local structure map, then $`T`$ is complete for its maximal-adic topology.
   (Used to conclude $`T_\theta`$ is adically complete.)
3. **`Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite`.**
   If $`A`$ is a finite $`\mathcal{O}`$-algebra over a complete local Noetherian
   $`\mathcal{O}`$, then $`\mathrm{MaxSpec}(A)`$ is finite, the natural map
   $$A \\;\longrightarrow\\; \prod_{I \in \mathrm{MaxSpec}(A)} A_I$$
   (product of localisations at maximal ideals) is bijective, every $`A_I`$ is a
   finite $`\mathcal{O}`$-module, and every $`A_I`$ is adically complete.

   This is the structure theorem for finite algebras over a complete local base:
   such an algebra is the product of its localisations at maximal ideals, and each
   local factor is again finite (hence complete) over the base. It is what upgrades
   "localisation of a finite free algebra at a maximal ideal" to "finite free over
   $`\mathcal{O}`$" for $`T_\theta`$.

These three are a single self-contained cluster: the third cites the other two, and
the whole cluster has a 3-node closure with no other unfinished premises.

## 7. Inventory

The import closure of the four T-side definition modules
(`Def_GaloisRep_DeformationRingData`, `Def_CuspForm_HeckeGaloisRepDatum`,
`Def_Algebra_PatchingDatum`, `Def_CuspForm_HeckeLocal`) is 16 definition modules,
1,755 lines. "Ported" means the declaration is mirrored in `lean/FLTForHuman/`.

| pin module | lines | mathematics | ported |
|---|---:|---|---|
| `Def_ModularForm_HeckeOperator` | 204 | the slash action and Hecke matrices | yes |
| `Def_ModularForm_HeckeOperatorForms` | 112 | `heckeTLin`, `heckeULin` on cusp forms | yes |
| `Def_CuspForm_HeckeAlgebra` | 93 | `heckeAlgebra = adjoin ℤ {T_ℓ, U_q}` | yes |
| `Def_CuspForm_IntegralStructure` | 8 | `intLattice`, `HasIntegralStructure` | yes |
| `Def_FLTPrelim_Modularity` | 106 | `qCoeff`, `IsNormalizedEigenform`, modularity predicates | partly |
| `Def_FLTPrelim_GaloisRep` | 83 | Galois action on torsion, stability, irreducibility | no |
| `Def_FLTPrelim_Ramification` | 52 | `LiesOverPrime`, inertia, unramified | no |
| `Def_EllipticCurve_FrobeniusTrace` | 66 | `galoisRepModuleEnd`, `galoisTrace`, `IsFrobeniusAt` | no |
| `Def_GaloisRep_Residual` | 105 | `ResidualGaloisRep` and its predicates | no |
| `Def_GaloisRep_ResidualEquiv` | 54 | `Equiv`/`IsEquiv` for residual representations | no |
| `Def_GaloisRep_Adic` | 207 | adic continuity, `GaloisRepAdic`, `residual`, base change | no |
| `Def_GaloisRep_DeformationRingData` | 46 | the universal deformation ring | no |
| `Def_FLTPrelim_FreyPackage` | 97 | `FreyPackage` and the Frey curves | no |
| `Def_CuspForm_HeckeGaloisRepDatum` | 38 | the T package | no |
| `Def_CuspForm_HeckeLocal` | 440 | `heckeLocal`, the local Hecke algebra | no |
| `Def_Algebra_PatchingDatum` | 44 | `PatchingLevel`, `PatchingDatum` | no |

The modules pull in 43 theorem modules; 40 are already ported (the entire Hecke
operator/analytic/`q`-coefficient layer, the Sturm bound, and `intLattice_fg`).
The three not yet ported are exactly the algebra cluster of §6
(495 + 148 + 149 = 792 proof lines). So the definition layer is not a new
mathematical development: it is the assembly of already-available Hecke material
around a compact new Galois/patching vocabulary.

## 8. Pointers

- [../base/011-deformations-hecke-algebras-and-r-equals-t.md](../base/011-deformations-hecke-algebras-and-r-equals-t.md)
  — deformation theory, the universal property, the criterion, and the dichotomy.
- [../studies/r-equals-t-in-the-proof-base.md](../studies/r-equals-t-in-the-proof-base.md)
  — the Lean objects, the exact $`R \cong T`$ line, the graph route, and the
  port-scope reading.
- [../base/014-hecke-operators.md](../base/014-hecke-operators.md),
  [009-hecke-jacobian-commute.md](009-hecke-jacobian-commute.md),
  [015-weight-two-hecke-periods.md](015-weight-two-hecke-periods.md) — the Hecke
  operators and their cohomological face.
- [012-sturm-bound.md](012-sturm-bound.md),
  [013-integral-structure-gamma1-basis.md](013-integral-structure-gamma1-basis.md)
  — the lattice, its finite generation, and the integral structure.
- Pin sources, all at `aa2d8b3`:
  [`Def_GaloisRep_Residual.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean),
  [`Def_GaloisRep_ResidualEquiv.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_ResidualEquiv.lean),
  [`Def_GaloisRep_Adic.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_Adic.lean),
  [`Def_GaloisRep_DeformationRingData.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_DeformationRingData.lean),
  [`Def_CuspForm_HeckeGaloisRepDatum.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean),
  [`Def_CuspForm_HeckeLocal.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeLocal.lean),
  [`Def_Algebra_PatchingDatum.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Algebra_PatchingDatum.lean),
  [`Def_FLTPrelim_Ramification.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean).
