# The integral structure of cusp forms from an integral Γ₁-basis

Let $`S_k(\Gamma_0(N))`$ be the space of weight-$`k`$ cusp forms on
$`\Gamma_0(N)`$, and let $`\mathrm{intLattice}(N,k)`$ be the $`\mathbb{Z}`$-span
of those whose $`q`$-expansion at $`\infty`$ has integral coefficients. The
**integral structure** statement is that this lattice is full-rank:

$$`\mathrm{span}_{\mathbb{C}}\bigl(\mathrm{intLattice}(N,k)\bigr) = S_k(\Gamma_0(N)).`$$

Equivalently, $`S_k(\Gamma_0(N))`$ has a $`\mathbb{C}`$-basis consisting of forms
with integral $`q`$-expansion. This is the hypothesis from which the Hecke algebra
acting on $`S_k(\Gamma_0(N))`$ becomes a finite (indeed free) $`\mathbb{Z}`$-module
— the finiteness half of the Hecke face of FLT.

The classical route to it is the Eichler–Shimura comparison: identify the cusp
space with a coherent-cohomology space carrying an evident integral structure via
the period lattice, and transport integrality across the comparison. This note
describes a different and cheaper route, which avoids the comparison entirely. It
rests on three independent facts:

1. $`S_k(\Gamma_1(N))`$ is **defined over $`\mathbb{Q}`$** — it is spanned by forms
   with rational $`q`$-coefficients;
2. such forms have **bounded denominators**, uniformly over the finitely many
   $`\Gamma_0(N)`$-translates;
3. the **trace** from $`\Gamma_1(N)`$ to $`\Gamma_0(N)`$ turns an integral
   $`\Gamma_1`$-basis into a spanning family of integral $`\Gamma_0`$-forms.

The integral-slash basis assembled from (1) and (2) is the content of
Deligne–Serre's Proposition 2.7; fact (3) is a short, apparently overlooked,
addition. The mathematics is §1–§7; the Lean declarations and the port map are
§8. Provenance: FLT pinned at `aa2d8b3`, the scout
[route-c-prime-scout.md](../studies/route-c-prime-scout.md), the work order
[TOPIC-route-c-prime-integral-structure.md](../lean/topics/hecke/TOPIC-route-c-prime-integral-structure.md).

## 1. The target and its classical cost

Write the $`q`$-expansion of a cusp form as $`f = \sum_{n \ge 1} a_n(f) q^n`$, and
call $`f`$ **integral** if all $`a_n(f) \in \mathbb{Z}`$. Then

$$`\mathrm{intLattice}(N,k) = \mathrm{span}_{\mathbb{Z}}\\{f \in S_k(\Gamma_0(N)) : f \text{ integral}\\},`$$

and the target is $`\mathrm{span}_{\mathbb{C}}(\mathrm{intLattice}(N,k)) = \top`$.

Nothing here is weight-specific: the statement is meaningful for every $`k \in
\mathbb{Z}`$, is vacuous for odd $`k`$ (where $`-1 \in \Gamma_0(N)`$ forces
$`f = 0`$), and is what makes
$`\mathrm{intLattice}(N,k)`$ a lattice of full rank in $`S_k(\Gamma_0(N))`$.

The classical proof compares $`S_k(\Gamma_0(N))`$ with the parabolic cohomology of
$`\Gamma_0(N)`$; the period pairing exhibits an integral lattice on the cohomology
side and Hecke-equivariance transports it. FLT's formalisation of that comparison
(`HeckeEis.*`, `Def_CuspForm_ModPForms`, `PeriodPair.*`) is a 657-node cone. The
route below never mentions cohomology.

## 2. Rational structure of the $`\Gamma_1`$-space

Let $`K = \mathbb{Q}(\zeta_N)`$ and let

$$`\mathrm{ratForms}(N,k) = \\{f \in S_k(\Gamma_1(N)) : a_n(f) \in \mathbb{Q} \quad \forall n\\}.`$$

The **rationality theorem** is that $`\mathrm{span}_{\mathbb{C}}(\mathrm{ratForms}(N,k))
= S_k(\Gamma_1(N))`$, i.e. $`S_k(\Gamma_1(N))`$ has a $`\mathbb{C}`$-basis with
rational $`q`$-coefficients. The mechanism is Galois averaging.

The $`q`$-expansion of a $`\Gamma_1(N)`$-form takes values in the cyclotomic field
$`K`$: this is the $`q`$-expansion principle for $`\Gamma_1`$, the statement that
the $`K`$-rational structure cut out by $`q`$-expansions already spans the space
over $`\mathbb{C}`$. For $`\sigma \in \mathrm{Gal}(K/\mathbb{Q})`$ there is then a
**conjugate form** $`f^\sigma`$, characterised by

$$`a_n(f^\sigma) = \sigma\bigl(a_n(f)\bigr) \qquad (n \ge 0),`$$

because the slash action and the $`q`$-expansion commute with the Galois action on
the coefficients (this is `CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply`).

For $`x \in K`$ form the averaged form

$$`T_x = \sum_{\sigma \in \mathrm{Gal}(K/\mathbb{Q})} \sigma(x)\\, f^\sigma .`$$

Its $`n`$-th coefficient is $`\sum_\sigma \sigma(x)\sigma(a_n(f)) =
\mathrm{Tr}_{K/\mathbb{Q}}\bigl(x\, a_n(f)\bigr) \in \mathbb{Q}`$. So every
$`T_x \in \mathrm{ratForms}(N,k)`$. As $`x`$ ranges over $`K`$, the $`T_x`$ span the
same space as the conjugates $`f^\sigma`$: the matrix $`(\sigma(x))_{x,\sigma}`$ is
invertible by Dedekind independence of the characters. Since $`f = f^{1}`$ is one of
the conjugates, $`f \in \mathrm{span}_{\mathbb{C}}\,\mathrm{ratForms}(N,k)`$. This
is the content of `CuspForm.mem_span_ratForms`; the resulting rational basis is
`CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`.

## 3. Bounded denominators

The second input is arithmetic, not linear algebra. Say a power series
$`q \in \mathbb{C}[[q]]`$ is **rational** if all its coefficients lie in
$`\mathbb{Q}`$ and **bounded-denominator** if there is $`0 \ne D \in \mathbb{Z}`$
with $`D q \in \mathbb{Z}[[q]]`$.

**Bounded-denominator theorem.** Let $`G`$ be a holomorphic function invariant
under the principal congruence subgroup $`\Gamma(N)`$, such that for some
$`m \ge 0`$ every translate $`\tau \mapsto G(\alpha\tau)\,\Delta(\tau)^m`$
($`\alpha \in \mathrm{SL}_2(\mathbb{Z})`$) is bounded at the cusps, and such that
the $`q`$-expansion of $`G\,\Delta^m`$ at width $`N`$ is rational. Then there is
$`0 \ne D \in \mathbb{Z}`$ with $`D\,G\,\Delta^m`$ having integral $`q`$-expansion
at width $`N`$.

Since $`\Gamma(N) \le \Gamma_1(N) \le \Gamma_0(N)`$, every $`\Gamma_1`$-form
qualifies; that specialisation is
`ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion`.

This is
`ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant`,
and it is where the real analytic content sits. The shape of the proof is
level-one reduction plus a monic relation:

- Multiplying by $`\Delta^m`$ raises the weight to a multiple of $`12`$, where the
  level-one structure theorem applies: every level-one form is a polynomial in
  $`E_4`$ and $`E_6`$, and the weight-$`12m`$ forms are exactly $`\Delta^m \cdot
  \mathbb{C}[j]`$ for the Hauptmodul $`j`$.
- A $`\Gamma(N)`$-invariant function is then controlled by the **fricke function**
  $`\varphi_N`$ and its conjugates; $`\varphi_N`$ satisfies a **monic** polynomial
  equation with coefficients in $`\mathbb{Z}[j]`$. Monicity is precisely what
  bounds the denominators of its $`q`$-expansion: the roots grow like the leading
  coefficient, and the power sums/coefficient recursions stay integral.
- Rational $`q`$-coefficients plus the monic relation give $`\mathrm{IsBdd}`$; a
  Galois-descent step passes from coefficients in $`\mathbb{Q}(\zeta_N)`$ to
  $`\mathbb{Q}`$ (the internal `BddK`/`BddQ`/`galois_descent`/`exists_int_multiple`
  block of the pin's `S_ModularCurve_exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant.lean`).

The weight-one **$`\chi_{-3}`$ Eisenstein series** $`E_1(1,\chi_{-3})`$ enters as the
low-weight generator of the $`\Gamma_1`$-space
(`EisensteinWeightOne.e1Chi3IsModular`, the pin's 3,816-line analytic lemma; its
mathematics is spelled out in
[014-chi-minus-3-eisenstein.md](014-chi-minus-3-eisenstein.md)); the
explicit Eisenstein family $`G : \mathbb{Z}/M \to M_k(\Gamma_1(M))`$ with integral
divisor-sum $`q`$-expansions and the slash-equivariance
$`G(c)\mid_k\gamma = G\bigl(c\,\gamma_{00}\bigr)`$ is
`ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq`.

For a **rational** $`\Gamma_1`$-form $`f`$ — the case used below — the theorem gives
$`D`$ with $`D f`$ integral. Applied to a translate $`f \mid_k \gamma`$, whose
$`q`$-expansion is again rational, it gives a clearing integer for that translate.

## 4. Uniform clearing over the finite quotient

Fix a rational $`\Gamma_1(N)`$-form $`f`$ and let $`\gamma \in \Gamma_0(N)`$. The
slash $`f \mid_k \gamma`$ is again a $`\Gamma_1(N)`$-form (because $`\Gamma_1
\trianglelefteq \Gamma_0`$, §5), and by
`ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0` its $`q`$-expansion is
again rational. So §3 applies to each translate separately.

The quotient $`\Gamma_0(N)/\Gamma_1(N) \cong (\mathbb{Z}/N)^\times`$ is **finite**,
of order $`r = [\Gamma_0(N) : \Gamma_1(N)]`$. Choosing representatives
$`\gamma_1, \dots, \gamma_r`$, let $`D_j`$ clear the denominators of
$`f \mid_k \gamma_j`$ (§3) and set

$$`D_f = D_1 D_2 \cdots D_r \ne 0 .`$$

Two translates whose group elements differ by an element of $`\Gamma_1(N)`$ have
**equal** $`q`$-expansions, so the finitely many $`D_j`$ cover every $`\gamma \in
\Gamma_0(N)`$; and a product of nonzero integers is nonzero. Hence

$$`D_f \cdot \bigl(f \mid_k \gamma\bigr) \quad \text{is integral for every } \gamma \in \Gamma_0(N).`$$

This is `CuspForm.exists_int_clearing_forall` (the per-coset `exists_int_clearing`
composed over the finite quotient, `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`).

Now start from the rational basis $`b_1, \dots, b_n`$ of §2 and scale each vector by
its clearing integer:

$$`b_i' = D_{b_i} \cdot b_i .`$$

Scaling by nonzero scalars preserves being a basis, and the slash is
$`\mathbb{C}`$-linear, so $`(b_i' \mid_k \gamma) = D_{b_i} (b_i \mid_k \gamma)`$ is
integral for every $`\gamma \in \Gamma_0(N)`$. Thus:

> **Integral-slash basis.** $`S_k(\Gamma_1(N))`$ has a $`\mathbb{C}`$-basis
> $`b_1', \dots, b_n'`$ such that every $`\Gamma_0(N)`$-translate of every basis
> vector has integral $`q`$-expansion.

## 5. The trace lemma: from $`\Gamma_1`$ to $`\Gamma_0`$

This is the new step. Let $`\Gamma_1 = \Gamma_1(N) \trianglelefteq \Gamma_0 =
\Gamma_0(N)`$ and fix representatives $`\gamma_1, \dots, \gamma_r`$ of
$`\Gamma_0/\Gamma_1`$, where $`r = [\Gamma_0 : \Gamma_1]`$. Define, for $`v \in
S_k(\Gamma_1(N))`$,

$$`T(v) = \sum_{j=1}^{r} v \mid_k \gamma_j .`$$

**Well-defined and $`\Gamma_0`$-valued.** For $`h \in \Gamma_1`$, $`v \mid_k h =
v`$, so changing representatives does not change $`T(v)`$; and for $`\delta \in
\Gamma_0`$, the elements $`\gamma_j \delta`$ run over the same coset
representatives, so

$$`T(v) \mid_k \delta = \sum_j v \mid_k (\gamma_j \delta) = \sum_j v \mid_k \gamma_j = T(v).`$$

Since a sum of holomorphic cusp forms vanishing at all cusps is again one,
$`T(v) \in S_k(\Gamma_0(N))`$. So $`T`$ is a $`\mathbb{C}`$-linear map
$`S_k(\Gamma_1(N)) \to S_k(\Gamma_0(N))`$.

**Surjective.** For $`w \in S_k(\Gamma_0(N))`$ one has $`w \mid_k \gamma_j = w`$
for every $`j`$, hence

$$`T(w) = \sum_{j=1}^{r} w = r\\, w, \qquad r = [\Gamma_0 : \Gamma_1] \ne 0 .`$$

So $`S_k(\Gamma_0(N)) \subseteq T(S_k(\Gamma_1(N)))`$, and $`T`$ is onto.

**Integral and spanning output.** Let $`b_1', \dots, b_n'`$ be the integral-slash
basis of §4. Each

$$`P_i = T(b_i') = \sum_{j=1}^{r} b_i' \mid_k \gamma_j`$$

is a finite sum of forms with integral $`q`$-expansion, hence integral itself; and
$`P_i \in S_k(\Gamma_0(N))`$. Since $`T`$ is onto and the $`b_i'`$ are a basis,
the $`P_i = T(b_i')`$ span $`S_k(\Gamma_0(N))`$. Therefore every element of
$`S_k(\Gamma_0(N))`$ is a $`\mathbb{C}`$-combination of integral $`\Gamma_0`$-forms:

$$`\mathrm{span}_{\mathbb{C}}\bigl(\mathrm{intLattice}(N,k)\bigr) = S_k(\Gamma_0(N)).`$$

**No Sturm bound is involved, and no weight restriction appears**: the statement
holds for every $`k \in \mathbb{Z}`$. The trace identity $`T(w) = r w`$ is exactly
the statement that $`S_k(\Gamma_0(N))`$ is the $`\Gamma_0/\Gamma_1`$-invariants of
$`S_k(\Gamma_1(N))`$, and $`T`$ is the corresponding transfer ("norm") map; the
only finiteness used is $`r \lt \infty`$.

## 6. Where the mathematics actually lives

The trace lemma is cheap bookkeeping; the analytic weight of the route is §2–§4:

| input | content | FLT declaration |
|---|---|---|
| rationality | $`q`$-expansion principle + Galois averaging, $`K = \mathbb{Q}(\zeta_N)`$ | `CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, `CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply` |
| bounded denominators | level-one Hauptmodul + fricke function monic relation, Galois descent | `ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant`, `ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational` |
| weight-one generator | $`E_1(1,\chi_{-3})`$ modularity | `EisensteinWeightOne.e1Chi3IsModular` |
| explicit Eisenstein family | divisor-sum $`q`$-expansions, slash-equivariance | `ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq` |
| span by $`E_4^aE_6^b`$ | level-one structure theorem lifted to $`\Gamma_1`$ | `CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top` |
| trace | §5, new | — (ours) |

The provenance of the integral-slash basis is **Deligne–Serre, *Formes modulaires
de poids 1*, Proposition 2.7**, as FLT's own documentation records. In that paper
the statement is used on the way to weight-one Galois representations and the
integrality of Hecke eigenvalues; here it is repurposed to produce the integral
structure of $`S_k(\Gamma_0(N))`$ directly.

## 7. Comparison with the Eichler–Shimura route

| | Eichler–Shimura (classical) | trace route (§2–§5) |
|---|---|---|
| mechanism | $`S_k(\Gamma_0) \cong H^1_{\mathrm{par}}`$ with periods; integral lattice from cohomology | rational $`\Gamma_1`$-structure + bounded denominators + finite trace |
| inputs | Hecke operators on cohomology, Eichler–Shimura comparison, period package | fricke/Hauptmodul analysis, $`\chi_{-3}`$ Eisenstein series |
| weight range | every $`k`$ | every $`k`$ |
| measured cone | 657 theorem nodes / 263,720 raw `S_` lines | 53 nodes / 33,719 lines, and every node lies in the endgame's weight-one branch (which FLT needs for `frey_isModular`) |

The two routes prove the same statement. The trace route's declarations are not a
duplicate of the classical route's: they are shared with FLT's weight-one
modularity work (`FLT.No2BridgeWiring → DeligneSerre → …`), so they are ported
regardless, and the trace lemma is a small addition on top. This is why the route
is not throwaway in the way a standalone $`k=2`$ finiteness proof is.

A third mechanism is FLT's standalone weight-two blob
(`S_CuspForm_moduleFinite_heckeAlgebra_two.lean`), which proves only the
$`k=2`$ finiteness statement, by a period-cocycle/triple-algebra argument rather
than by integral $`q`$-expansions. It is not this note's route; the mathematics
is in [015-weight-two-hecke-periods.md](015-weight-two-hecke-periods.md).

## 8. Lean technicalities and pointers

- **The two halves of the ingredient.** The working declaration is
  `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` (general $`k`$,
  $`\Gamma_0`$-slash integrality). Its weight-2, $`\gamma = 1`$ child is
  `CuspForm.exists_basis_gamma1_two_qCoeff_mem_range_intCast` — the slash condition
  is essential and the general-weight form removes any weight-raising step.
- **The trace lemma is ours**:
  `CuspForm.hasIntegralStructure_of_basis_gamma1`, proved by coset sums over
  `Subgroup.fintypeQuotientOfFiniteIndex`, the `CuspForm` structure constructor
  for the $`P_i`$, and `Submodule.subset_span`/`span_le` for integrality and
  spanning. The corollaries `CuspForm.hasIntegralStructure_of_two_le` and
  `CuspForm.hasIntegralStructure_two` are statement-verbatim from their wrappers
  but proved through it.
- **The port** is [../lean/topics/hecke/TOPIC-route-c-prime-integral-structure.md](../lean/topics/hecke/TOPIC-route-c-prime-integral-structure.md):
  eight modules under `FLTForHuman/ModularForms/WeightOne/`, ported in closure
  order; the definitions `CuspForm.intLattice`/`HasIntegralStructure` are already
  in `Defs/IntegralStructure.lean`.
- **Checker.** The 53 cone nodes all have `Theorems/` wrappers; `SOURCES`/`PORT_FILES`
  gain them, and the trace lemma is the only new `OWN_PROOFS` exemption.
- **Record.** [route-c-prime-scout.md](../studies/route-c-prime-scout.md) (the
  scout and measurements), [sturm-bound-port.md](../lean/logs/sturm-bound-port.md)
  (the neighbouring Sturm cone, whose vanishing lemmas are among the five
  already-ported nodes of this cone).
- **The other cheap $`k=2`$ route.** [015-weight-two-hecke-periods.md](015-weight-two-hecke-periods.md)
  — FLT's standalone period-cocycle proof of `moduleFinite_heckeAlgebra_two`
  (route B): finiteness from the integral group-cocycle lattice, no
  `HasIntegralStructure`, no general $`k`$.
