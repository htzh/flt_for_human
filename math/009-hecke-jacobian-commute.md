# The Hecke action on the Jacobian, and why it commutes

This is the ninth `math/` note, and the first on the *modular-curve side* of the
route — the machinery behind note
[008](008-ribet-level-lowering.md), whose geometric heart runs on $`J_0(N)`$ as a
module over a Hecke algebra and over $`\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})`$
*at the same time*. The theorem that makes both of those phrases meaningful is
`ModularCurve.heckeOperatorsCommuteBar`
([Thm_ModularCurve_heckeOperatorsCommuteBar.lean, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean#L9)):

```lean
theorem ModularCurve.heckeOperatorsCommuteBar (N : ℕ) [NeZero N] : ModularCurve.HeckeOperatorsCommuteBar N
```

Classically it says: the Hecke operators $`T_\ell`$ on $`J_0(N)`$ commute —
$`T_\ell T_{\ell'} = T_{\ell'} T_\ell`$ *for all primes* $`\ell, \ell'`$,
including the primes $`\ell \mid N`$ (the $`U_\ell`$ of Diamond–Shurman §5.2). The proof is too
big for one note; what we follow is its *construction stack*. The Lean proof
takes exactly four mathematical moves:

1. build $`J_0(N)`$ *from $`q`$-expansions alone*, as a divisor class group of a
   function field (§1–§2);
2. build $`T_\ell`$ as the correspondences $`\alpha_{\ast}\circ\beta^{\ast}`$ attached to
   the two degeneracy maps (§3);
3. reduce commutation to a single *exchange identity* for divisors in a
   "roof square", and unwind that identity to a local sum over valuations (§4);
4. discharge the square's field-theoretic inputs (generation, degree,
   separability) from the modular equation $`\Phi_\ell(j, j_\ell) = 0`$ (§5).

Sections 1–5 run in that order; §6 collects the two formal-only quirks (total
functions with junk branches); §7 says what the theorem buys downstream.

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; the one
mathlib citation is at tag v4.33.0. Where the prose and the Lean differ, the
Lean is right.

## 1. No schemes: $`X_0(N)`$ as a field inside $`\mathbb{Q}((q))`$

The modular curve $`X_0(N)`$ over $`\mathbb{Q}`$ is an algebraic curve of genus
$`g`$ which is positive for most $`N`$; it has no embedding into projective space
that one wants to compute with, and no scheme model is ever built in this
project. Instead the formalisation uses the fact that modular functions are
*computable Laurent series*. The $`j`$-invariant has the $`q`$-expansion

$$j(q) = q^{-1} + 744 + 196884q + \cdots,$$

formalised as an explicit Laurent series `jq : LaurentSeries ℚ` — literally
$`q^{-1}`$ times a power series with integer coefficients
([Def_ModularCurve_X0.lean, line 157](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L157)).
Substitution $`q \mapsto q^N`$ is the ring map
`qExpand : LaurentSeries R →+* LaurentSeries R`, defined by multiplying the
support of the series by $`N`$
([lines 25–29](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L25-L29)) — so
$`j(q^N)`$ is available as `qExpand ℚ N jq`, again a concrete series. Then
([Def_ModularCurve_X0.lean, lines 305–306](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L305-L306)):

```lean
def modularFunctionFieldFull : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ (divisorExpansions N)
```

is the subfield $`F_N^{\mathrm{full}} = \mathbb{Q}(\,j(q^d) : d \mid N\,)`$ of
$`\mathbb{Q}((q))`$: the function field of $`X_0(N)`$, realised *concretely*
inside Laurent series. Classically the whole field of weight-zero modular
functions is $`\mathbb{Q}(j, j(q^N))`$ — at level one, $`\mathbb{Q}(j)`$ — with
each $`j(q^d)`$ a rational function of those two. That classical statement is
not imported: mathlib has no modular $`j`$-invariant and no notion of
meromorphic modular function. The formalisation instead takes the adjoin above
as the *definition* of the curve and proves, from the modular equation, that the
two descriptions agree — `FunctionFieldGeneration N`, i.e. every $`j(q^d)`$ with
$`d \mid N`$ lies in $`\mathbb{Q}(j, j(q^N))`$
([Def_ModularCurve_X0.lean, line 233](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L233);
[Thm_ModularCurve_functionFieldGeneration.lean, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_functionFieldGeneration.lean#L8)),
equivalently `modularFunctionFieldFull N = modularFunctionField N`
([line 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_functionFieldGeneration_iff_full_eq.lean#L6)).
One definition, one proved collapse; there is no second theory of modular
functions to reconcile. Keeping all $`d \mid N`$ as named generators is what
makes every degeneracy map of §3 land *inside* an ambient field, so that they
compose as functions rather than as "maps between different curves". This is one
of the places where Lean's mechanics dictate a choice, and the choice happens to
be mathematically felicitous.

The geometric base is $`\bar{\mathbb{Q}}`$: `laurentBaseChange`
([Def_ModularCurve_LaurentCoeff.lean, line 103](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LaurentCoeff.lean#L103))
extends coefficients along $`\mathbb{Q} \to \bar{\mathbb{Q}}`$, and the working
field is
$`\bar F_N := \bar{\mathbb{Q}} \cdot F_N^{\mathrm{full}} \subset \bar{\mathbb{Q}}((q))`$,
named `modularFunctionFieldBar N`
([Def_ModularCurve_ArithmeticGalois.lean, lines 111–113](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean#L111-L113)).

In summary: a level is a natural number, a curve is a field, and a "point" of
the geometry is a *valuation* of that field. Everything in the rest of the note
is algebra on these objects.

## 2. The Jacobian as a divisor class group

Once curves are fields, the Jacobian is forced on us in its oldest form. For any
field $`L`$ and function field $`F/L`$ satisfying the standing hypothesis
`HasPrincipalDivisors L F` (every nonzero $`f \in F`$ has a well-defined,
degree-zero divisor $`\sum_v \mathrm{ord}_v(f)\,v`$; for
$`F = \bar F_N`$ this is proved, see §5), the project defines
([Def_AlgebraicCurve_DivisorClassGroup.lean, lines 223–226](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L223-L226)):

```lean
abbrev Pic : Type _ := Divisor K F ⧸ Divisor.principal (K := K) (F := F)

abbrev Pic0 : Type _ :=
  Divisor.degZero (K := K) (F := F) ⧸
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))
```

degree-zero divisors modulo principal divisors — and the Jacobian is
([Def_ModularCurve_ArithmeticGalois.lean, lines 115–116](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean#L115-L116)):

```lean
abbrev JZero : Type _ :=
  Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
```

Over $`\bar{\mathbb{Q}}`$ this is the group one classically writes
$`J_0(N)(\bar{\mathbb{Q}}) = \mathrm{Pic}^0(X_0(N))`$: on a smooth projective
curve the degree-zero divisor classes *are* the points of its Jacobian. No
variety is ever built here, so that identity is a reading of `JZero` rather than
a theorem about a constructed object; the honest substitute is the
Hecke-equivariant Abel–Jacobi injection into the analytic torus proved
downstream (§7).

One honest remark about what is gained. This $`J_0(N)`$ is an abelian *group*,
and that group is enormous — it contains $`J_0(N)(\mathbb{Q})`$, a finitely
generated group about which almost anything can be hard. So the formalisation
does *not* try to prove that $`J_0(N)`$ is an abelian variety and import
theorems about abelian varieties; it keeps the concrete divisor group and proves
the individual finiteness theorems it needs (e.g. the finiteness of
$`\mathfrak{m}`$-torsion used downstream, or the finite generation of Tate
modules in the co-input list of §7). Later notes will open those; here the point
is that the Hecke action is *defined* on the divisor group directly, with no
variety in sight.

## 3. Degeneracy maps, and the correspondence $`T_\ell = \alpha_{\ast}\circ\beta^{\ast}`$

Recall the classical picture. $`X_0(N)`$ parametrises (generically) cyclic
isogenies $`\varphi : E \to E'`$ of degree $`N`$. At prime level there are two
degeneracy maps

$$\alpha : X_0(N\ell) \to X_0(N), \qquad (E \xrightarrow{N\ell} E'') \mapsto (E \xrightarrow{(\times \ell)} E' \xrightarrow{N} E''),$$

the "forget $`\ell`$" map, and

$$\beta : X_0(N\ell) \to X_0(N), \qquad (E \xrightarrow{N\ell} E'') \mapsto (E' \xrightarrow{N} E''),$$

the "quotient by the $`\ell`$-part" map, which on functions is substitution
$`q \mapsto q^\ell`$. The correspondence
$`X_0(N) \leftarrow X_0(N\ell) \to X_0(N)`$ induces
$`T_\ell = \alpha_{\ast} \circ \beta^{\ast}`$ on divisors: pull a point back to the
$`(\ell+1)`$-point fibre of $`\beta`$, then push forward along $`\alpha`$. On
modular forms this is exactly the formula
$`T_\ell f = \ell^{k-1}\,\mathrm{tr}\,(\beta^{\ast} f)`$ of Diamond–Shurman §5.2,
transposed to divisors.

In the field model the two maps are two $`L`$-algebra maps out of the same
field into the level-$`N\ell`$ field
([Def_ModularCurve_HeckeOperator.lean, lines 66–70 and 98–104](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperator.lean#L66-L104)):

- `heckeAlphaBar L N ℓ` is the *inclusion*
  $`\bar F_N \hookrightarrow \bar F_{N\ell}`$ — genuine, because
  $`d \mid N \Rightarrow d \mid N\ell`$;
- `heckeBetaBar L N ℓ` is the substitution
  $`q \mapsto q^\ell`$ — it lands where claimed because
  $`d \mid N \Rightarrow \ell d \mid N\ell`$, so
  $`j(q^d) \mapsto j(q^{\ell d}) \in \bar F_{N\ell}`$.

Any two integral maps $`\varphi, \psi : F \to F'`$ define a *correspondence on
divisors*, $`\psi_{\ast} \circ \varphi^{\ast}`$
([Def_AlgebraicCurve_Correspondence.lean, line 137](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L137)),
where pullback and pushforward along $`\iota : F \to F'`$ are the two basic
operations of function-field arithmetic ([lines 67 and 99](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L67)):

$$\iota^{\ast}\big(\textstyle\sum_P n_P P\big) = \sum_P n_P \sum_{Q \mid P} e(Q/P)\\,Q, \qquad
  \iota_{\ast}\big(\textstyle\sum_Q m_Q Q\big) = \sum_Q m_Q\\, f(Q/\iota^{\ast}Q)\\, \iota^{\ast}Q,$$

pullback weighted by ramification indices $`e`$, pushforward by residue degrees
$`f`$. To *descend* this to $`\mathrm{Pic}^0`$, three facts are needed, each a
named hypothesis in the project:

- $`\iota^{\ast}`$ sends a principal divisor to a principal divisor
  (`isPrincipal_pullbackAlong`);
- $`\iota^{\ast}`$ multiplies degrees by $`[F' : F]`$ — the **fundamental identity**
  $`\sum_{Q \mid P} e(Q/P) f(Q/P) = [F' : F]`$, so degree-zero is preserved
  (`FundamentalIdentityAlong`);
- $`\iota_{\ast}`$ sends principal to principal: if $`D = \mathrm{div}(g)`$ then
  $`\iota_{\ast} D = \mathrm{div}(\mathrm{Norm}_{F'/F}\, g)`$ — the **norm formula**
  (`NormFormulaAlong`; `isPrincipal_pushforwardAlong`).

Bundled, these five bits of structure (integrality of each map, principal
divisors at level $`N\ell`$, the fundamental identity along $`\beta`$, the norm
formula along $`\alpha`$, plus finiteness) are the predicate `HeckeInputsAlong`
([Def_ModularCurve_HeckeOperatorTotal.lean, lines 13–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperatorTotal.lean#L13-L18)),
and the operator is ([lines 22–28](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperatorTotal.lean#L22-L28)):

```lean
def heckeOperatorAlong :
    Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  if h : HeckeInputsAlong L N ℓ then ...correspondence... else 0
```

the correspondence if its inputs exist, the zero map otherwise — a *total
function* (§6 collects why). At $`L = \bar{\mathbb{Q}}`$ its
$`\mathbb{Z}`$-linear form is `heckeOperatorBar N ℓ : Module.End ℤ (JZero N)`
([Def_ModularCurve_HeckeModule.lean, lines 16–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean#L16-L18)),
and the theorem of this note is that these commute:

```lean
def HeckeOperatorsCommuteBar : Prop :=
  ∀ ℓ ℓ' : Nat.Primes,
    heckeOperatorBar N ℓ * heckeOperatorBar N ℓ' = heckeOperatorBar N ℓ' * heckeOperatorBar N ℓ
```

([lines 25–27](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean#L25-L27)).

## 4. The exchange square, and the proof down to local fields

The classical proof that Hecke correspondences commute is a one-line diagram
chase on curves: at the "roof" level $`M = N\ell\ell'`$ the two squares of
degeneracy maps are *fibre products*, and push–pull across a fibre product
square is the same as pull–push in the other order. The whole task of the note's
theorem is to say this sentence in function-field arithmetic and then prove the
field-theoretic hypotheses.

**Step one: the commuting roof square.** Fix $`N`$ and distinct primes
$`\ell \ne \ell'`$, put $`M = N\ell\ell'`$, and draw four embeddings of $`L`$-algebras:

$$
\begin{matrix}
 & & L \cdot F_M & & \\\\
 & \nearrow \bar\alpha_{(\ell)} \quad & & \nearrow \beta\text{-sub}^{(\ell)} & \\\\
L \cdot F_{N\ell'} & & & & L \cdot F_{N\ell} \\\\
 & \nwarrow \bar\alpha_{(\ell')} \quad & & \nwarrow \bar\beta & \\\\
 & & L \cdot F_N & &
\end{matrix}
$$

— from the base: $`\bar\alpha_{(\ell')}`$ is the inclusion
$`\bar F_N \hookrightarrow \bar F_{N\ell'}`$ and $`\bar\beta`$ the substitution
$`q \mapsto q^\ell`$ into $`\bar F_{N\ell}`$; to the roof: the inclusion
$`\bar F_{N\ell} \hookrightarrow \bar F_M`$ (`towerInclBar`) and $`q \mapsto q^\ell`$
out of $`\bar F_{N\ell'}`$ followed by inclusion (`towerSubstBar`,
[Def_ModularCurve_DegeneracyTower.lean, lines 54–57](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean#L54-L57)).
The square commutes *definitionally*, because every leg, after coercion into
$`L((q))`$, is either the identity or multiplication of exponents by $`\ell`$ —
and $`L((q))`$ is one ambient set
([heckeSquareBar_commutes, lines 104–107](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean#L104-L107)).
This is the payoff of the §1 design: what is classically "these two moduli
interpretations agree" is here "both composites are $`f(q) \mapsto f(q^\ell)`$".

**Step two: exchange is the whole game.** Compositions of functors give
$`T_\ell \circ T_{\ell'} = \bar\alpha_{(\ell),\ast}\, \bar\beta^{\ast}\, \bar\alpha_{(\ell'),\ast}\, \bar\beta_{(\ell')}^{\ast}`$,
so the middle pair must be exchanged. Predicate-ised
([Def_ModularCurve_DegeneracyTower.lean, lines 121–132](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean#L121-L132)),
the requirement is: for every divisor $`D`$ on $`\bar F_{N\ell'}`$,

$$\bar\beta^{\ast}\\; \big(\bar\alpha_{(\ell'),\ast}\\; D\big) \quad=\quad \mathrm{incl}_{\ast}\\; \big(\mathrm{subst}^{\ast}\\; D\big),$$

pull-then-push down the left legs equals pull-then-push round the roof. The
reduction theorem `heckeOperatorsCommuteBar_of_heckeExchangeAt`
([Thm file, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean#L9))
says: principal divisors at every level $`+`$ this identity at every roof
$`\Rightarrow`$ $`T_\ell T_{\ell'} = T_{\ell'} T_\ell`$ on $`J_0(N)`$ (the case
$`\ell = \ell'`$ is $`T^2 = T^2`$, and degree-zero/principal preservation —
§3 — carries the identity from divisors down to $`\mathrm{Pic}^0`$).

**Step three: the general exchange lemma.** The geometric input is

```lean
theorem AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    ... (hsq : b'.comp b = a'.comp a) (hfin : FiniteAlong K (a'.comp a))
    (hsep : SeparableAlong K (a'.comp a))
    (hgen : Algebra.adjoin K (Set.range a' ∪ Set.range b') = ⊤)
    (hLD : finrankAlong K (a'.comp a) = finrankAlong K a * finrankAlong K b)
    (D : Divisor K A) :
    Divisor.pullbackAlong b hb (Divisor.pushforwardAlong a ha D)
      = Divisor.pushforwardAlong b' hb' (Divisor.pullbackAlong a' ha' D)
```

([Thm file, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean#L10)):
in a commuting square
$`F \to A \to E`$, $`F \to B \to E`$ with everything integral and separable, if
$`E`$ is *generated* by the images of $`A`$ and $`B`$ (`hgen`) and
$`[E:F] = [A:F]\cdot[B:F]`$ (`hLD` — over the algebraically closed base, these
two together are "the square is a fibre product", i.e. the fields are **linearly
disjoint**), then push–pull equals pull–push. The proof unwinds in two layers,
both worth seeing:

*Layer 1 (counting).* Both sides are additive in $`D`$, so check a single place
$`w_A`$ of $`A`$. If places $`w_A, w_B`$ restrict to *different* places of $`F`$,
both coefficients at $`w_B`$ are zero. If they restrict to the same $`v`$, the
left coefficient is $`\sum_{W : W|_A = w_A, W|_B = w_B} e(W/w_A)\, f(W/w_B)`$ and the right one is
$`e(w_B/v)\, f(w_A/v)`$ — and these agree. That is the entire mathematical
content of the exchange lemma.

*Layer 2 (the local identity, taken down to college level).* The place-by-place
identity is `Place.sum_ramificationIndex_mul_inertiaDeg_exchange`
([Thm file, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean#L10)),
proved as follows. Count the bi-fibre in two ways: places $`W`$ of $`E`$
restricting to both $`w_1`$ and $`w_2`$ are places of the tensor product
$`F_1 \otimes_F F_2`$ over $`v`$; for a finite *separable* extension this is
Étale, hence a product of local fields, and completion at $`v`$ gives

$$\widehat E_v \cong \widehat{F_1}_{w_1} \otimes_{\widehat F_v} \widehat{F_2}_{w_2}
\cong \prod_W \widehat E_W,$$

by the Chinese remainder theorem. Comparing $`\widehat{F_v}`$-dimensions shows
that the number of $`W`$ over a fixed pair times $`e f`$ is the local degree —
the identity $`r e f = [M : F']`$ of extension theory (the project proves it via
the Galois case, where $`ref = [L:K]`$ is the orbit-stabiliser count for the
decomposition group; the general case follows by passing to a separable closure
and back down via multiplicativity $`e, f`$ in towers —
`Place.ramificationIndexAlong_comp`, `Place.inertiaDegAlong_comp`). Summing the
bi-fibre count gives the exchange identity; nothing beyond the fundamental
equality of local fields has been used.

**Step four: the square's hypotheses are the modular equation.** Of the ledger
of hypotheses in step three, two are free (`hsep` — characteristic zero is
automatic, `separableAlong_of_charZero`; integrality of the legs — see §5), and
two have real content, both supplied by the modular polynomial:

- *Generation of the roof* (`heckeRoof_adjoin_range_union_eq_top`,
  [Thm file, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeRoof_adjoin_range_union_eq_top.lean#L8)):
  $`\bar F_M`$ is generated by the inclusion of $`\bar F_{N\ell}`$ and the
  $`q \mapsto q^\ell`$-image of $`\bar F_{N\ell'}`$. Reason: the two ranges
  contain $`j(q)`$ and $`j(q^{\ell \cdot \ell'})`$ (among others; the function
  field $`F_M^{\mathrm{full}}`$ is generated over $`\mathbb{Q}`$ by $`j`$ and
  $`j(q^M)`$ — `FunctionFieldGeneration M`, proved from the modular polynomial
  $`\Phi_M`$ and its degree (§5)), and $`j(q^{\ell'})`$ is *integral* over $`\bar F_{N\ell'}`$
  via the modular equation of §5, so adjoining it closes the field.
- *The degree match* (`finrankAlong_towerSubstBar_comp_heckeAlphaBar`,
  [Thm file, line 11](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar.lean#L11)):
  $`[\bar F_M : \bar F_N] = [\bar F_{N\ell'} : \bar F_N]\cdot\psi(\ell)`$,
  because classically $`[\mathbb{Q}(j, j(q^n)) : \mathbb{Q}(j)] = \psi(n) = n \prod_{p \mid n}(1 + 1/p)`$,
  the index of $`\Gamma_0(n)`$ up to $`\pm 1`$, and the two
  factorisations $`M = (N\ell)\ell' = (N\ell')\ell`$ of the roof level multiply
  the same indices in different orders. The project computes these degrees from
  the polynomials $`\Phi_\ell`$ of §5, not from group theory.

## 5. Two inputs: principal divisors and the modular equation

**Principal divisors.** The ledger repeatedly needs the class
`HasPrincipalDivisors L` $`(\bar F_M)`$: every nonzero function of the
$`q`$-expansion field has a finitely supported, degree-zero divisor. This is
*not* automatic for a random subfield of $`L((q))`$ — the point is that
$`\bar F_M`$ is a finite extension of the rational function field
$`\bar{\mathbb{Q}}(j(q))`$, hence a one-variable function field, where places are
valuations and the degree-of-divisor theorem holds (Stichtenoth Th. 1.4.11).
The project proves it generally for base changes of $`F_M^{\mathrm{full}}`$ to
any $`L \supset \mathbb{Q}`$ — the transcendence of the series $`j(q)`$ does the
work — and instantiates:
`hasPrincipalDivisors_modularFunctionFieldBar`
([Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean#L10)).

**The modular equation.** The deep existence statement is
`modularPolynomialFamily`
([Thm_ModularCurve_modularPolynomialFamily.lean, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_modularPolynomialFamily.lean#L8)):
for every prime $`\ell`$ there is $`\Phi_\ell \in \mathbb{Z}[X, Y]`$ with

- $`\Phi_\ell(j(q),\, j(q^\ell)) = 0`$ as a Laurent-series identity;
- $`\Phi_\ell`$ monic of degree $`\psi(\ell) = \ell + 1`$ as a polynomial in
  $`Y`$ — hence $`j(q^\ell)`$ is *integral* over $`\mathbb{Q}(j(q))`$, and the
  same integrality propagates to every extension of function fields built on
  it (this feeds `towerSubstBar_isIntegral` and the leg integrality
  `heckeAlphaBarIntegral_of_prime`, `heckeBetaBarIntegral_of_prime`);
- $`\Phi_\ell(X, Y) = \Phi_\ell(Y, X)`$ — the symmetry that reflects
  $`E \to E'`$ being degree-$`\ell`$ on both sides.

In the formalisation $`\Phi_N`$ is produced by `nonempty_modularPolynomialData`
as the *minimal polynomial* of $`j(q^N)`$ over $`\mathbb{Z}[X] = \mathbb{Z}[j]`$
([Thm_ModularCurve_nonempty_modularPolynomialData.lean, line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_nonempty_modularPolynomialData.lean#L8)):
$`\mathbb{Q}(j)`$ is the fraction field of $`\mathbb{Z}[X]`$, $`j(q^N)`$ is
integral over it, and its minimal polynomial is monic of degree
$`\psi(N) = [\mathbb{Q}(j, j(q^N)) : \mathbb{Q}(j)]`$. This is the Lean
replacement for the classical statements "the level-one modular functions are
$`\mathbb{Q}(j)`$" and "$`j(q^N)`$ is algebraic over $`\mathbb{Q}(j)`$"; the
generation collapse of §1 is read off from the same minimal polynomial.

Classically $`\Phi_\ell`$ exists because the functions
$`j((a\tau + b)/d)`$, $`ad = \ell`$, are permuted by
$`\mathrm{SL}_2(\mathbb{Z})`$, so their elementary symmetric functions are
modular of level one, hence polynomials in $`j`$ (Diamond–Shurman §5.2 works
this out); the formalisation feeds these data in as a packaged `ModularPolynomialFamily`
and derives $`q`$-expansion identities from them. The modular equation is the
single analytic input of the whole note: everything else is divisor-counting,
local fields, and universal algebra.

**Assembly.** With principal divisors at every level (hP) and the exchange
identity at every roof (hex, from §4 via the generation/degree facts above),
`heckeOperatorsCommuteBar_of_heckeExchangeAt` closes the theorem. Separately
the same inputs prove `heckeInputsAll`
([Thm_ModularCurve_heckeInputsAll.lean, line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeInputsAll.lean#L9))
— the per-prime input package exists for *every* $`\ell`$ — so all the
`heckeOperatorAlong` junk branches are *provably* never taken.

## 6. Lean detours (the narrative does not depend on these)

Two quirks are worth flagging honestly, then quarantining.

**(a) Total operators with a zero junk branch.** `heckeOperatorAlong` is defined
by decision: if the input package `HeckeInputsAlong` exists, it is the
correspondence; otherwise it is $`0`$. This is not a fake definition waiting to
be improved: it is how the project can *write down* $`T_\ell`$ before proving
any of its inputs, and how commutation can be *stated and used* as a hypothesis
(`hcomm : HeckeOperatorsCommuteBar N`) throughout the Hecke-module arc, with the
theorem of this note discharged where needed. By §5 the junk branch is never
taken for the modular fields — but the type-checker did not need to know that
to define the operators.

**(b) The fallback module.** The *module structure* of $`J_0(N)`$ over the
Hecke algebra is `heckeModuleBar N`
([Def_ModularCurve_HeckeModule.lean, lines 81–84](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean#L81-L84)):
if `HeckeOperatorsCommuteBar N` holds, evaluate polynomials via
$`X_\ell \mapsto T_\ell`$ (`heckeEvalBar`); otherwise evaluate at
$`X_\ell := 0`$ — the zero junk action. Similarly
`smulCommClass_JZero_of_heckeOperatorsCommuteBar` first packages the commuting
operators into the commutative algebra $`\mathbb{Z}[T_\ell, T_{\ell'}, \dots]`$
via `Algebra.isMulCommutative_adjoin`, then reduces Galois–Hecke commutation
for all of $`\mathbb{T}`$ to commutation on the generators
(`heckeAlg_smul_comm_of_forall_gen`): in the good branch the correspondence is
Galois-equivariant because $`\bar\alpha, \bar\beta`$ are built from
$`\mathbb{Q}`$-rational $`q`$-series (`heckePic0Bar_smul`,
[Thm file, line 5](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckePic0Bar_smul.lean#L5)),
and in the junk branch both sides are $`0`$. The theorem makes sure the
fallback branch is unreachable mathematics, not just unreachable code.

The reader can forget both quirks now: *as mathematics*, every operator in this
note is the genuine $`\alpha_{\ast}\beta^{\ast}`$ correspondence.

## 7. What it buys: the abstract Hecke algebra

Commutativity is what turns an indexed family of endomorphisms into a *ring
action*. The definition
([Def_HeckeGalois_EichlerShimura.lean, lines 13–16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L13-L16))

```lean
abbrev HeckeAlg : Type := MvPolynomial Nat.Primes ℤ

def heckeGen (ℓ : Nat.Primes) : MvPolynomial Nat.Primes ℤ := MvPolynomial.X ℓ
```

takes the free-commutative algebra
$`\mathbb{T} := \mathbb{Z}[X_\ell : \ell\ \text{prime}]`$ on *all* primes —
including $`\ell \mid N`$, so the algebra records the $`U_\ell`$ uniformly with
the $`T_\ell`$, which is exactly what the level-lowering machinery downstream
needs. Once $`\{T_\ell\}`$ commute, the universal property of
$`\mathbb{Z}`$-multivariate polynomials gives the evaluation hom
$`\mathbb{T} \to \mathrm{End}_{\mathbb{Z}}(J_0(N))`$ (in Lean,
`MvPolynomial.aeval`, [mathlib v4.33.0, line 593](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/MvPolynomial/Eval.lean#L593)),
making $`J_0(N)`$ a $`\mathbb{T}`$-module with
$`X_\ell \cdot x = T_\ell(x)`$; and the Galois group acts independently,
$`\sigma \cdot (T_\ell x) = T_\ell(\sigma x)`$, because the correspondences are
defined over $`\mathbb{Q}`$. Under these two roofs —
$`\mathbb{T}`$-linearity and Galois-equivariance — everything else in the arc is
built: $`\mathbb{T}`$-eigenvectors in Tate modules, the congruence
$`T_\ell \equiv \mathrm{Frob}_\ell + \ell \langle \ell \rangle`$ of
Eichler–Shimura, the maximal ideals $`\mathfrak m`$ and the
$`\mathfrak m`$-torsion of note 008's geometric heart. The theorem of this note
is the license to say "$`\mathbb{T}`$" at all.

One more comparison deserves naming, because it is the honest sense in which the
divisor-class $`J_0(N)`$ and the classical one coincide. Downstream the project
proves a *Hecke-equivariant injective* homomorphism into the analytic torus,
$$J_0(N)(\bar{\mathbb{Q}}) \hookrightarrow S_2(\Gamma_0(N))^\vee / \Lambda_N,$$
whose image contains all the torsion, where $`\Lambda_N`$ is the period lattice
of $`X_0(N)`$ and the correspondence-theoretic $`T_\ell`$ on the left is
intertwined with the transpose `dualHeckeRep N (heckeGen ℓ)` of the cusp-form
Hecke operator on the right
(`exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice`,
[Thm file, line 18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice.lean#L18)).
That is where the divisor-side and automorphic-side Hecke actions meet; nothing
in the commutation proof above depends on it.

## 8. Links

Lean sources at the pinned sha `aa2d8b3`:

- [Def_ModularCurve_X0.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean) — `jq`, `qExpand`, `modularFunctionFieldFull`
- [Def_ModularCurve_LaurentCoeff.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LaurentCoeff.lean) — `laurentBaseChange`
- [Def_AlgebraicCurve_DivisorClassGroup.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean) — `HasPrincipalDivisors`, `Pic`, `Pic0`
- [Def_ModularCurve_ArithmeticGalois.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ArithmeticGalois.lean) — `modularFunctionFieldBar`, `JZero`, the Galois action
- [Def_AlgebraicCurve_Correspondence.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean) — pull/push, the three descent facts, `correspondence`
- [Def_ModularCurve_HeckeOperator.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperator.lean) — `heckeAlphaBar`, `heckeBetaBar`, `heckePic0Bar`
- [Def_ModularCurve_HeckeOperatorTotal.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperatorTotal.lean) — `HeckeInputsAlong`, the total operator
- [Def_ModularCurve_DegeneracyTower.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_DegeneracyTower.lean) — `towerInclBar`/`towerSubstBar`, the commuting square, `HeckeExchangeAt`
- [Def_ModularCurve_HeckeModule.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean) — `heckeOperatorBar`, `HeckeOperatorsCommuteBar`, `heckeEvalBar`, `heckeModuleBar`
- [Def_HeckeGalois_EichlerShimura.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean) — `HeckeAlg`, `heckeGen`
- [Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean) — the exchange lemma
- [Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean) — the local identity
- [Thm_ModularCurve_heckeRoof_adjoin_range_union_eq_top.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeRoof_adjoin_range_union_eq_top.lean) — roof generation
- [Thm_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finrankAlong_towerSubstBar_comp_heckeAlphaBar.lean) — the degree match
- [Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean) — principal divisors
- [Thm_ModularCurve_modularPolynomialFamily.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_modularPolynomialFamily.lean) — `Φₗ` exists
- [Thm_ModularCurve_nonempty_modularPolynomialData.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_nonempty_modularPolynomialData.lean) — `Φ_N` as the minimal polynomial of `j(q^N)` over `ℤ[j]`
- [Thm_ModularCurve_functionFieldGeneration.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_functionFieldGeneration.lean) — `ℚ(j, j(q^N))` generates `F_N^full`
- [Thm_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar_of_heckeExchangeAt.lean) — the reduction
- [Thm_ModularCurve_heckeOperatorsCommuteBar.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean) — the headline
- [Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_smulCommClass_JZero_of_heckeOperatorsCommuteBar.lean) — Galois–Hecke commutation
- [Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice.lean) — the Abel–Jacobi comparison with `S₂(Γ₀(N))^∨/Λ_N`

Generated glosses (per-module English): the
[ModularCurve_HeckeModule def page](https://tianyipeng.github.io/fermats-last-theorem/def/ModularCurve_HeckeModule.html),
[HeckeOperatorTotal](https://tianyipeng.github.io/fermats-last-theorem/def/ModularCurve_HeckeOperatorTotal.html),
[DegeneracyTower](https://tianyipeng.github.io/fermats-last-theorem/def/ModularCurve_DegeneracyTower.html),
[AlgebraicCurve_Correspondence](https://tianyipeng.github.io/fermats-last-theorem/def/AlgebraicCurve_Correspondence.html).

Mathlib at v4.33.0:
[Mathlib/Algebra/MvPolynomial/Eval.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/MvPolynomial/Eval.lean)
(`MvPolynomial.aeval` — the universal-property evaluation);
[NumberTheory/ModularForms/LevelOne/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean#L109)
(`ModularForm.levelOne_weight_zero_rank_one` — the *holomorphic* weight-zero
level-one space is just the constants; the modular `j`-invariant is not in
mathlib).

Companion notes:

- [008 — Ribet's level lowering](008-ribet-level-lowering.md) — the Hecke-module downstream
- [base/002 — Modular forms basics](../base/002-modular-forms-basics.md) — the automorphic side
- [base/001 — Field extensions and Galois basics](../base/001-field-extensions-and-galois-basics.md) — the `Algebra`/tower vocabulary

Background:

- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005, §5.2 — the correspondence picture and $`\Phi_\ell`$.
- B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977) — the divisorial-operator treatment.
- H. Stichtenoth, *Algebraic Function Fields and Codes*, GTM 254, Springer 2009 — places, divisors, the fundamental identity.
- J.-P. Serre, *Local Fields*, GTM 67, Springer 1979, Ch. I — the $`ef`$ theory behind the exchange identity.
