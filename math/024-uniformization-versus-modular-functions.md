# Uniformization and the modular function field: two routes to the `j`-line

Twenty-fourth of the `math/` notes. [010](010-function-field-generation.md) proved the
generation theorem for `X₀(N)` — that $`j(q^d) \in \mathbb{Q}(j(q), j(q^N))`$ for every
$`d \mid N`$ — inside a fixed field of formal `q`-expansions;
[base/013](../base/013-riemann-existence-and-the-q-expansion-principle.md) isolated the
one genuinely analytic input it uses (the level-one `q`-expansion principle) and
explained why the rest is algebra. Neither note constructs an analytic model of an
elliptic curve: the port has no `℘`-function theory, no complex torus, no map
$`\mathbb{C}/\Lambda \to E(\mathbb{C})`$.

That missing theory is now visible on disk. The pin's `PeriodPair` uniformization
slice — 18 nodes, ~12 k `S_` lines, scoped as
[TOPIC-V5](../lean/topics/velu/TOPIC-V5-periodpair-uniformization.md) — supplies it, and
it is a prerequisite of a Mazur-step-three node the port still lacks. This note
answers the two questions that raises: **what does each theory actually construct, and
does either replace the other?**

The short answer, before the machinery:

- the two theories are **complementary, not interchangeable** — neither's theorems
  imply the other's (Verified in the pin's own dependency graph, §5);
- they are **two independent inputs to the same step**. Both
  `ModularCurve.functionFieldGeneration` (the `jq` theory) and
  `WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq` (the
  uniformization theory) lie in the closure of
  `WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`;
- and they are not even cleanly separable by subject: inside the uniformization slice,
  the surjectivity of $`j`$ — the one statement both theories can speak to — is proved
  by **modular forms**, i.e. with the `jq` theory's instruments (§4.2).

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
citations point at tag **v4.34.0**, the port's current pin (`lean/lake-manifest.json`).
Where the prose and the Lean differ, the Lean is right.

## 1. The two constructions

Both theories are about the same moduli problem — elliptic curves, their
$`j`$-invariant, and the cover $`X_0(N) \to X(1)`$ — but they build different objects and
prove different kinds of statement.

| | **J — modular functions** | **P — uniformization** |
|---|---|---|
| primary object | the function field $`\mathbb{Q}(j(q), j(q^N))`$ inside $`\mathbb{Q}(\!(q)\!)`$ | the complex torus $`\mathbb{C}/\Lambda`$ and the map $`\mathbb{C}/\Lambda \to E(\mathbb{C})`$ |
| medium | formal `q`-expansions (Laurent/Hahn series), the modular equation $`\Phi_N`$ | complex analysis: $`\wp`$, $`\wp'`$, analytic order, Liouville |
| headline | $`j(q^d) \in \mathbb{Q}(j(q), j(q^N))`$ for $`d \mid N`$ | $`\mathbb{C}/\Lambda \cong E(\mathbb{C})`$, and every $`j`$ is a lattice's |
| field of definition | $`\mathbb{Q}`$ (arithmetic) | $`\mathbb{C}`$ (transcendental) |
| what it gives the proof | the `X₀(N)`/`X₁(N)` tower, the modular polynomial, the Hecke/Jacobian layer | the `ℂ`-model of an elliptic curve, isogenies as sublattices, the `j`-diagonal step |

## 2. Theory J: the modular function field

### 2.1 The level-one input is analytic, and small

The port's theory J is the formalization of a classical exercise of Diamond–Shurman:
*generate the function field of $`X_0(N)`$ from $`j(q)`$ and $`j(q^N)`$*. The one
analytic input is the description of the base $`X(1)`$: it has genus zero and
$`j`$ is a Hauptmodul. In mathlib that is exactly

> `lemma ModularForm.eq_const_of_weight_zero [𝒢.IsArithmetic] (f : ModularForm 𝒢 0) :
    ∃ c, (f : ℍ → ℂ) = Function.const ℍ c` — a weight-zero modular form for an
> arithmetic group is constant
> ([NormTrace.lean, line 164](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L164)).

From it the port derives the two statements that make theory J run
([`QExpansionPrinciple.lean`](../lean/FLTForHuman/ModularForms/QExpansionPrinciple.lean),
[`Hauptmodul.lean`](../lean/FLTForHuman/ModularForms/Hauptmodul.lean)):

- **the `q`-expansion principle**: a holomorphic, $`\mathrm{SL}_2(\mathbb{Z})`$-invariant
  `q`-series is constant — the constancy kernel
  `coeff_eq_zero_of_hasSum_of_slash_invariant`;
- **the Hauptmodul form**: a pole-bounded, realized, invariant Laurent series is a
  *polynomial* in `jq` — `mem_adjoin_jq_of_hasSum_of_slash_invariant`. Equivalently,
  the level-one modular functions are exactly $`\mathbb{Q}(j)`$.

Both are analytic statements, but the analysis is confined to *one* theorem of
mathlib: bounded holomorphic invariant functions are constant. No elliptic curve, no
torus, no $`\wp`$.

### 2.2 Everything above level one is algebra

The rest of theory J is: the modular equation $`\Phi_N`$, the list of its roots
$`j(q^d)`$ over $`j(q^N)`$, a two-prime descent
($`j(q^d)`$ is the unique common root of $`\Phi_p`$ and $`\Phi_q`$ at the level-`N`
nome), and a strong induction on the divisors of $`N`$. The capstone
([`FunctionFieldGeneration/Capstone.lean`](../lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean))

```lean
theorem ModularCurve.functionFieldGeneration (N : ℕ) [NeZero N] : FunctionFieldGeneration N
```

is a statement about *fields of Laurent series over $`\mathbb{Q}`$*. Its corollaries
are the ones the FLT proof consumes:
`modularFunctionField_eq_full`, `finrank_adjoin_jqN_eq_dedekindPsi`,
`relfinrank_full_eq_dedekindPsi` — degree statements for the tower
$`X_0(Mp^a) \to X(1)`$, with $`\psi`$ the Dedekind psi function.

The medium matters as much as the content. There is no Riemann surface anywhere in
theory J: the field is fixed in advance and every step is formal. That is what makes
it portable to $`\mathbb{Q}`$ — and it is also its ceiling, §5.

## 3. Theory P: uniformization

### 3.1 The dictionary

[`Def_PeriodPair_Uniformization.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_PeriodPair_Uniformization.lean)
(144 lines, 20 declarations) attaches to a lattice `L : PeriodPair` — mathlib's pair of
$`\mathbb{R}`$-independent periods, whose $`\mathbb{Z}`$-span is `L.lattice`
(mathlib `Weierstrass.lean`, structure at line 60) — the objects that make it an
elliptic curve:

```lean
def weierstrassCurve : WeierstrassCurve ℂ            -- from g₂, g₃
def DiscriminantNeZero : Prop := L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0
def toPoint (h : L.DiscriminantNeZero) (z : ℂ) : L.weierstrassCurve.toAffine.Point
def IsUniformization (h : L.DiscriminantNeZero) : Prop
def jLattice : ℂ := 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)
def JSurjective : Prop := ∀ c : ℂ, ∃ L : PeriodPair, L.DiscriminantNeZero ∧ L.jLattice = c
```

`toPoint` is the classical map $`z \mapsto (\wp(z), \wp'(z)/2)`$ on the complement of
the lattice and $`0`$ on it; `weierstrassCurve` is the cubic curve it lands on; and

$$`\mathrm{IsUniformization}(h) \;=\; \bigl(\forall z\,w,\ \mathrm{toPoint}(z+w) = \mathrm{toPoint}(z) + \mathrm{toPoint}(w)\bigr) \wedge \mathrm{Surjective}(\mathrm{toPoint}) \wedge \bigl(\mathrm{toPoint}(z) = 0 \Rightarrow z \in \Lambda\bigr).`$$

In words: **`toPoint` is a surjective group homomorphism with kernel exactly the
lattice, so $`\mathbb{C}/\Lambda \cong E(\mathbb{C})`$** — the uniformization theorem.

### 3.2 The uniformization theorem and how it is proved

`PeriodPair.isUniformization_toPoint` (1,493 `S_` lines) is purely complex-analytic.
Its route
([`S_PeriodPair_isUniformization_toPoint.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean))
is exactly the classical one:

1. $`\wp`$ is *surjective onto* $`\mathbb{C}`$ — `kw_weierstrassP_surjective`, from
   $`\wp(z) \to \infty`$ at lattice points and the open mapping / Liouville argument;
2. the addition theorem — `kw_hasDerivAt_weierstrassP_add`, with the auxiliary
   functions `kwAddCoreE`, `kwAddCoreE₁`, `kwAddCoreE₂` and their vanishing derivatives
   at $`0`$, giving $`\mathrm{toPoint}(z+w) = \mathrm{toPoint}(z) + \mathrm{toPoint}(w)`$;
3. the kernel: `kw_toPoint_eq_zero_iff`, from the pole order of $`\wp - \wp(c)`$ at a
   non-lattice point (`kw_analyticOrderAt_weierstrassP_sub_self_ne_top`,
   `kw_weierstrassP_not_eventually_const`) and the identity theorem in the form
   `apply_eq_apply_of_differentiable_of_forall_periodic`, a differentiable periodic
   function with no poles is constant.

No modular form, no `q`-expansion, no Eisenstein series appears in this route. The
instruments are $`\wp`$, its derivative, analytic order at a point, and Liouville.

### 3.3 Surjectivity of $`j`$ — proved with modular forms

`PeriodPair.jLattice_surjective` (1,054 `S_` lines) is the statement
$`\forall c, \exists L, c = j(L)`$. It is *not* proved by uniformization. Its route
([`S_PeriodPair_jLattice_surjective.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_jLattice_surjective.lean))
is theory J's:

```lean
def kw_E4cube              : ModularForm 𝒮ℒ 12   -- E₄³
def kw_E6sq                : ModularForm 𝒮ℒ 12   -- E₆²
def kw_E4cube_sub_E6sq_cuspForm : CuspForm 𝒮ℒ 12
theorem kw_E4cube_ne_E6sq (τ : ℍ) : E₄ τ ^ 3 ≠ E₆ τ ^ 2
theorem kw_riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945
theorem kw_g₂_ofTau (τ : ℍ) : ...        -- g₂ of the lattice (τ, 1) is E₄(τ)/…
theorem kw_g₃_ofTau (τ : ℍ) : ...        -- g₃ is E₆(τ)/…
```

The argument is classical, and its first half is a **modular-forms identity**. $`E_4^3`$
and $`E_6^2`$ are level-one forms of weight 12 with the same constant term, so their
difference is a cusp form (`kw_E4cube_sub_E6sq_cuspForm`); the space of weight-12 cusp
forms is one-dimensional — **mathlib's**
`CuspForm.exists_smul_discriminant_of_weight_eq_twelve` — so

$$`E_4^3 - E_6^2 \;=\; c\,\Delta`$$

for a constant $`c`$, and the $`q^1`$-coefficient pins $`c`$ (it is $`1728`$,
`kw_E4cube_sub_E6sq_coeff_one`), hence $`c \neq 0`$ and the difference never vanishes
(`kw_E4cube_ne_E6sq`). The second half reads the lattice invariants off the Eisenstein
series: on the lattice $`(\tau, 1)`$,

$$`g_2 \;=\; \tfrac{4\pi^4}{3} E_4(\tau), \qquad g_3 \;=\; \tfrac{8\pi^6}{27} E_6(\tau)`$$

(`kw_g₂_ofTau`, `kw_g₃_ofTau`, the constants coming from $`\zeta(4)`$ and
$`\zeta(6)`$ — `kw_riemannZeta_six`). The scaling family $`L \mapsto L.\mathrm{scale}\,\beta`$
acts by $`g_2 \mapsto \beta^{-4}g_2`$, $`g_3 \mapsto \beta^{-6}g_3`$, which is what
makes the $`j`$-invariant of a lattice depend only on its shape; the file closes with
an explicit construction (`kwQepw123c_jH`, `…E₄cubeExt`, `…ΔExt`, `…pencil`,
`kw_JSurjective`). **The uniformization slice proves its own $`j`$-surjectivity with the
modular-forms instruments**, drawing on the same $`E_4, E_6`$, `CuspForm`, `discriminant`
and `qExpansion` vocabulary the port already possesses from
[base/004](../base/004-the-j-invariant.md) and its `ModularForm` layer.

### 3.4 What only theory P can say

From `toPoint` and `jLattice`, theory P derives the statements the FLT proof actually
consumes at this node:

- **classification of complex elliptic curves.** The 17-line
  `exists_variableChange_smul_weierstrassCurve_eq` says every elliptic $`E/\mathbb{C}`$
  is $`C \bullet L.\mathrm{weierstrassCurve}`$ for some lattice and some variable
  change; its six-line proof *is* `jLattice_surjective` plus
  `exists_variableChange_of_j_eq`. This is the statement "elliptic curves over
  $`\mathbb{C}`$ are lattices", and no amount of `q`-expansion gives it;
- **isogenies are sublattices.** `exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient`
  (2,021 lines): a finite isogeny between the two lattice curves corresponds to a
  $`\beta \in \mathbb{C}^\times`$ with $`(L'.\mathrm{scale}\,\beta).\mathrm{lattice} \subseteq L.\mathrm{lattice}`$,
  the degree equals the sublattice index `sublatticeIndex`, and a cyclic kernel means
  a cyclic quotient. Nothing here is algebraic: the proof needs the uniformization to
  identify the function-field map with a map of tori;
- **the analytic seam.** `exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`
  (2,673 lines): given a finite separable $`\iota`$ between function fields, there is a
  differentiable $`F : \mathbb{C} \to \mathbb{C}`$ with $`F(0) \in L'.\mathrm{lattice}`$
  and

  $$`L'.\mathrm{toPoint}\bigl(F(z)\bigr) \;=\; \mathrm{pointMapOfPushforward}\,\iota\,\cdots\,\bigl(L.\mathrm{toPoint}(z)\bigr),`$$

  i.e. *the algebraic pushforward is differentiable in uniformization coordinates*.
  Its `S_` file is the `KwD5BetweenCurves*` family — holomorphic lifts between curves.
  This is the largest single node in the slice and the one with no `jq` counterpart.

## 4. The interface: the `j`-line

### 4.1 Two different statements about the same object

Over $`\mathbb{C}`$ both theories describe the $`j`$-line, but they say different
things about it:

- **J** says the *field* of level-one modular functions is $`\mathbb{Q}(j)`$, and, at
  level $`N`$, that $`\mathbb{Q}(j(q), j(q^N))`$ contains every $`j(q^d)`$ —
  statements about *fields of definition*, meaningful over $`\mathbb{Q}`$ and
  transferable to arithmetic (Galois, reduction mod $`p`$, integral models);
- **P** says the *map* $`j : \mathbb{H}/\Gamma(1) \to \mathbb{C}`$ is onto, and that
  the fibre over any non-singular $`j`$ is a lattice model of the curve —
  statements about the *covering*, meaningful over $`\mathbb{C}`$ and supplying the
  torus.

Over $`\mathbb{C}`$ the two overlap at "X(1) is the $`j`$-line", and there uniformization
is cheaper: a bijection $`\mathbb{H}/\Gamma(1) \cong \mathbb{C}`$ gives the function
field in one step. But that is not the statement the FLT proof uses. Theory J's
consumers need generation *over $`\mathbb{Q}`$* of the $`X_0(N)`$ tower; theory P's
consumers need the torus. Each is silent exactly where the other is used.

### 4.2 Where the pin refuses to choose

The decisive evidence is the pin's own proof of `jLattice_surjective` (§3.3): inside
the *uniformization* slice, the surjectivity of $`j`$ is established by *modular
forms* — Eisenstein series, `CuspForm`, `qExpansion`, `riemannZeta 6`. The pin does
not prove it from $`\wp`$. So the theories are not even separated by their
statements: they share the $`j`$-line, and at that shared point the pin routes the
argument through the cheaper of the two, which is theory J's.

## 5. Do they replace each other?

**No.** The two implications both fail, and the failure is visible in the pin's
dependency graph.

**P does not give J.** Uniformization is a statement over $`\mathbb{C}`$ about a
covering; it says nothing about `q`-expansions, nothing about $`\mathbb{Q}`$, and
carries no modular equation. It cannot produce `functionFieldGeneration`, nor any of
its corollaries — the degree of $`X_0(Mp^a) \to X(1)`$ is a statement about
$`\psi(Mp^a)`$, not about a torus.

**J does not give P.** Theory J never constructs a map $`\mathbb{C}/\Lambda \to E`$. It
has no $`\wp`$, no addition theorem, no analytic order. It cannot produce
`IsUniformization`, `toPoint`'s surjectivity, the differentiable lift `F` of §3.4, or
the isogeny/sublattice dictionary — those are all statements about the torus.

The graph confirms it. Writing $`C(x)`$ for the pin's closure:

$$`\texttt{functionFieldGeneration} \;\not\ni\; \texttt{aeval\_j\_diag}, \qquad \texttt{aeval\_j\_diag} \;\not\ni\; \texttt{functionFieldGeneration},`$$

while both lie in $`C(\texttt{mazurStepThree\_not\_inZeroComponentAt})`$. So neither
*contains* the other, and neither is *contained* in the other: they are independent
inputs to the same step. A further measurement sharpens the point —
$`C(\texttt{modularPolynomial\_rootMultiplicity\_jQuotVelu\_eq\_one})`$ contains
`jLattice_surjective` but **not** `functionFieldGeneration`. The uniformization
slice's modular-forms half is therefore load-bearing on **both** Mazur-step-three
sub-routes, not only on the node that motivated
[V5](../lean/topics/velu/TOPIC-V5-periodpair-uniformization.md).

**Could a better-organized proof use only one of them?** Not for these statements.
The honest summary is that the FLT proof needs two facts about the $`j`$-line at two
different levels of generality — *which field*, and *which torus* — and the two
existing theories each supply one. What a shared theory would have to do is prove
$`\mathbb{C}/\Lambda \cong E(\mathbb{C})`$ in a way that also produces the
$`\mathbb{Q}`$-model of the modular curve; the pin does not attempt this, and neither
does mathlib.

## 6. What each theory is for, in the proof

Both are inputs to **Mazur's step three**
(`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`, in the chain
$`\to`$ `FreyPackage.frey_no_cofixed_large` $`\to`$ `Mazur_Frey` $`\to`$
`fermatLastTheoremFor_of_five_le`), and they enter it at different places:

- **J** supplies the function field of $`X_0(N)`$ and with it the modular polynomial
  layer: the roots of $`\Phi_N`$, their degrees, the roof generation used by the
  Hecke/Jacobian development of [009](009-hecke-jacobian-commute.md). In the Mazur
  branch it reaches `modularPolynomial_rootMultiplicity_jQuotVelu_eq_one` through the
  degree/counting side.
- **P** supplies the $`\mathbb{C}`$-model: `aeval_j_diag_eq_zero_of_finrankAlong_eq`
  (non-integral $`j`$ forces endomorphisms to be integer multiplication), which needs
  the lattice dictionary to see an isogeny as a sublattice inclusion, and — as just
  noted — `jLattice_surjective`, which the `jQuotVelu` root-multiplicity node also
  consumes.

The port has J (`functionFieldGeneration` landed) and lacks P. Since the two do not
imply each other and both are on the same step's path, the absence of P is a genuine
gap, not a redundancy to be refactored away.

## 7. What this means for the `PeriodPair` slice

The comparison splits
[V5](../lean/topics/velu/TOPIC-V5-periodpair-uniformization.md)'s 15,179-line closure
along a line the module names do not show:

| block | lines | nature | reuse prospect |
|---|---:|---|---|
| `jLattice_surjective` + the `E₄³ − E₆²` chain + `jLattice_ofTau` | ≈1,800 | **theory J's mathematics**, sitting in a `PeriodPair` file | high: the port already has `E₄`, `E₆`, `CuspForm`, `qExpansion`, the `jq` layer |
| `isUniformization_toPoint` | 1,493 | irreducibly **P** ($`\wp`$, addition theorem, Liouville) | none |
| the analytic seam (`exists_differentiable_toPoint_comp…`, `KwD5BetweenCurves*`) | 2,673 | irreducibly **P** | none |
| lattice/index dictionary (`sublatticeIndex`, `natCard_ker`, `primCosetReps`) | ≈3,800 | **P** arithmetic over the torus | partial (lattice API is mathlib's) |
| field descent and base change (`exists_intermediateField_countable…`, `exists_baseChange…`, `nonempty_functionField_algEquiv…`) | 4,760 | **neither** — generic `WeierstrassCurve` statements | shared with other frontier work |

So "we already did the `jq` theory" does not shorten the uniformization slice by much:
it can replace the ≈1,800 lines of `j`-surjectivity (which is also the part the
*existing* Mazur branch needs), but the uniformization map, the analytic seam and the
lattice dictionary are the part that is genuinely missing, and they are the majority.

That is the accounting *if* route P is taken. §8.4 gives the alternative: the pin also
carries an ≈1,000-line moduli-place vocabulary that might make the whole slice
unnecessary, at the price of a comparison theorem whose size is not yet measured.

## 8. Where this sits in the proof: Deligne–Serre and `R = T`

The pin's route ([PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/PROOF-PATH.md))
has four steps: reduce to $`p \ge 5`$; build the Frey package; **irreducibility**
(Mazur's Eisenstein-ideal argument); **modularity** (Wiles: Langlands–Tunnell, then
two `R = T` modularity-lifting theorems). The two theories sit on opposite sides of
that split.

**P is on step 3 only.** The uniformization slice enters the proof through
`aeval_j_diag_eq_zero_of_finrankAlong_eq`, whose only two consumers in the entire pin
are `IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j` and
`…_of_transcendental_j`; from there the path runs
`separable_map_eval2_of_not_isIntegral` $`\to`$
`modularPolynomial_rootMultiplicity_jQuotVelu_eq_one` $`\to`$
`moduliPointExists_jQuotVelu_of_mult_two` $`\to`$
`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt` $`\to`$
`FreyPackage.frey_no_cofixed_large`. That is step 3 — **irreducibility**: Mazur's
Eisenstein-ideal theorem carried out for this situation ($`p \ge 17`$, no Galois-stable
line in $`E[p]`$; not the modularity step), on $`X_0(N)`$, its Jacobian and Néron model,
the cuspidal subgroup, the Eisenstein quotient. The same Eisenstein-ideal machinery
underlies Mazur's torsion and rational-points theorems; those are not used here.

**J is on the same step, and on the modular-curve layer generally.**
`functionFieldGeneration` and its corollaries are the roof generation and degree match
of the $`X_0(N)`$ tower that [009](009-hecke-jacobian-commute.md) uses, i.e. the
geometry Mazur's argument runs on, and they are consumed by the mod-$`p`$
modular-curve layer (`ModularCurve/CharPModel/*`).

**Neither is on the `R = T` path, and neither is on the Deligne–Serre path.** Step 4's
source `S_WeierstrassCurve_modularity_of_semistableModel.lean` imports exactly nine
nodes — the residual-modularity node carrying the Deligne–Serre lifting, the two
`modularityLiftingAtConductor_threeFive_…` theorems, `modThreeOrFiveIrreducible`, the
`threeFiveSwitchCurve`, and the conductor-level reductions — and no `PeriodPair` and no
`functionFieldGeneration`. `S_FreyPackage_frey_isModular.lean` imports one node. The
$`R \twoheadrightarrow T`$ node itself,
`GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum`, is a
nine-line statement over the deformation-theory definitions.

**Deligne–Serre is on J's side of the split.** D-S is the *weight-one* input to step 4:
Langlands–Tunnell produces a weight-one form for the odd octahedral $`\bar\rho_3`$;
multiplying by the weight-one Eisenstein series $`E_1(1,\chi_{-3})`$ and applying the
Deligne–Serre lifting lemma produces a congruent weight-two eigenform, which is what
makes $`\bar\rho_3`$ residually modular and lets the `R = T` machinery start. Every
instrument in that step — Eisenstein series, Hecke operators on $`\Gamma_1(N)`$,
`q`-expansions, the Sturm bound, the $`\Gamma_1`$ integral basis — is J's universe (the
`CuspForm`/`ModularForm`/`EisensteinSeries` cone the port already has, and the very cone
whose preludes the D-S scout warned about). None of it is $`\wp`$-theory.

**Why this is forced.** `R = T` is a statement about deformation rings and Hecke
algebras over $`\mathcal{O}`$: its inputs are congruences, integrality and patching —
exactly the arithmetic of `q`-expansions. Uniformization is transcendental. The two
touch only at the *existence* of the modular curve and the shape of its `q`-expansions,
which is J's turf. So the intersection is one-sided in each case: P meets neither D-S
nor `R = T`; J meets both, but as *vocabulary and q-expansion input*, never as the
generation theorem, which stays on the step-3 side.

### 8.1 A measurement trap

The docs-site citation graph says the opposite. `frontier.closure` puts
`PeriodPair.isUniformization_toPoint`, `aeval_j_diag`, `functionFieldGeneration` and
`CerednikDrinfeld.Mumford.PeriodUniformization` inside the closure of
`modularity_of_semistableModel`, of the Langlands–Tunnell node, and of the
residual-modularity node — while correctly excluding `mazurStepThree` from the same
closures. Grepping the pin's files settles it: those names occur **zero** times in the
`solution` bodies and at most once in the whole file — on an
`attribute [-simp] PeriodPair.…` line, the artefact of the pin's `p2m_*` scaffolding
re-exporting the entire inlined prelude. The closure over the docs graph is inflated by
silo inlining exactly as `ucl` is, and by more; any claim that uniformization is on the
`R = T` path must be checked against the `S_` file's own imports and proof body, not the
graph.

### 8.2 "Uniformization" is not one theory

Three different uniformizations live in this area, and only the first is V5's:

1. **classical complex uniformization**, $`\mathbb{C}/\Lambda \cong E(\mathbb{C})`$ by
   the $`\wp`$-map — `PeriodPair`, V5, step 3;
2. **$`p`$-adic uniformization of Shimura curves** by the Bruhat–Tits tree —
   Cerednik–Drinfeld, Mumford (`CerednikDrinfeld.Mumford.PeriodUniformization`,
   `…ToricUniformization`). The names appear in the step-4 scaffolding, but the step-4
   sources do not use them; mathematically this is the natural companion of the 3–5
   switch;
3. **uniformization of the modular curve by the upper half plane**,
   $`X(1) = \mathbb{H}/\Gamma(1)`$ — implicit throughout J as the Hauptmodul statement,
   never constructed.

Confusing them is easy and consequential: a "uniformization is needed for
`R = T`" reading of the graph would be wrong on the first theory and, on the evidence
here, unmotivated for the second.

### 8.3 Why the transcendental existence is load-bearing

It is not Mazur's argument that reaches for uniformization. It is the **link between
two independently built models of the modular curve**, and only the uniformization
supplies that link.

The pin builds $`X_0(N)`$ twice.

- On the **`q`-expansion side** (J): a function field over $`\mathbb{Q}`$, the modular
  polynomial $`\Phi_N`$, the generation theorem.
- On the **moduli side**: [`Def_ModularCurve_ModuliPoint.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPoint.lean)
  defines a *synthetic* $`\Gamma_0(N)`$ moduli problem by explicit data —
  a structure `Gamma0Pair` carrying `toCurve : WeierstrassCurve L`,
  `isElliptic`, `gen : toCurve.toAffine.Point`, `addOrderOf_gen : addOrderOf gen = N`,
  and then `ModuliPoint N L := Quot (Gamma0Pair.Step …)`, with
  `ModuliPoint.j : ModuliPoint N L → L` the $`j`$-invariant. This is the side Mazur's
  Eisenstein-ideal argument consumes
([`Def_ModularCurve_MazurStepThreeInputs.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_MazurStepThreeInputs.lean),
`JZero`, the Eisenstein quotient, the cuspidal class). No scheme theory is needed for
this side: the moduli problem is a quotient of explicit pairs.

What joins the two is exactly `aeval_j_diag_eq_zero_of_finrankAlong_eq`: **an isogeny of
degree $`N`$ forces `aeval j Φ_N = 0`** — the statement that the `q`-expansion-defined
polynomial sees the synthetic moduli data.

**The generation theorem cannot supply it.** $`j(q^d) \in \mathbb{Q}(j(q), j(q^N))`$ is a
statement about *fields*: it identifies the function field of the modular curve, not
the curves themselves. Nothing in it says which elliptic curves with level structure
occur as fibres of the universal family — the *existence and parametrization* half of
the moduli interpretation. Over $`\mathbb{C}`$ the uniformization is precisely that
half: every $`E/\mathbb{C}`$ is $`L.\mathrm{weierstrassCurve}`$ up to variable change,
every isogeny is a sublattice inclusion, and its degree is the index. That is why the
proof of `aeval_j_diag` descends to a countable $`K_0`$, base-changes to $`\mathbb{C}`$,
and does the computation at a lattice rather than in a generic `q`-expansion — at which
point the moduli problem has become linear algebra over $`\mathbb{Z}`$.

So the "bridge from `jq`" one would want is the **algebraic moduli
interpretation** — that the `q`-expansion-defined $`X_0(N)`$ represents the moduli
problem of `Gamma0Pair` (Deligne–Rapoport). The uniformization is its analytic
substitute, and §8.4 asks whether the pin's own moduli vocabulary can stand in for it.
The two theories are the two halves of "the modular curve parametrizes elliptic
curves": J has the algebraic/`q`-expansion half, P has the existence half.

### 8.4 The alternative the pin already contains

The bridge does not have to be invented. The pin carries a moduli-place vocabulary for
it, and it is unported:

- [`Def_ModularCurve_ModuliPoint.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPoint.lean)
  (162 lines) — `Gamma0Pair`, `ModuliPoint`, `ModuliPoint.j`;
- [`Def_ModularCurve_ModuliPointMap.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPointMap.lean)
  (159) — its functoriality (`ModuliPoint.map`, `ModuliPoint.j_map`);
- [`Def_ModularCurve_ModuliPlace.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPlace.lean)
  (681) — **the comparison itself**: `ModuliTestDatum`,
  `IsModuliPlaceOf (x : ModuliPoint N K) (v : Place K (modularFunctionFieldFullC K N))`,
  `moduliPlaceOfPoint`, and
  `moduliPlace (E : WeierstrassCurve K) (C : AddSubgroup E.toAffine.Point)`.

So the pin can already say what it means for a place of the modular function field to
*be* the moduli point of a curve with level structure — in characteristic zero, with no
$`\wp`$ anywhere. The layer is ≈1,000 lines of definitions.

That makes the alternative concrete: instead of paying the 15,179-line closure of §1,
port that ≈1,000-line layer and re-derive `aeval_j_diag` by specialization through
`moduliPlace`, so that $`\Phi_N(j(E)) = 0`$ follows from the moduli comparison rather
than from a lattice computation over $`\mathbb{C}`$. If it works, the uniformization,
the analytic seam and the lattice/index dictionary all drop out of step 3.

Three cautions before treating that as the answer.

1. **The pin itself chose the $`\mathbb{C}`$ route.** Its `aeval_j_diag` `S_` file imports
   `Def_PeriodPair_Uniformization` and proves the statement by descending to
   $`\mathbb{C}`$; the moduli vocabulary is used elsewhere (Mazur's inputs). That is
   evidence — not proof — that the moduli-place route is harder, or is not stated in
   the shape `aeval_j_diag` needs.
2. **The two dictionaries are not the same problem.** `ModuliPoint N K` is a curve with
   a point of order *exactly* $`N`$ — a $`\Gamma_0(N)`$-level structure — whereas
   `aeval_j_diag` takes an `IsogenyEndDatum` of degree $`N`$ whose $`N`$ comes from a
   negative-discriminant binary quadratic form, not from a level structure. Passing
   between a cyclic $`N`$-isogeny and a point of order $`N`$ (via the kernel and the
   dual isogeny) is a real step, and it has to be priced.
3. **The comparison still needs its own existence content.** `IsModuliPlaceOf` and
   `moduliPlace` are definitions; the places that arise have to be *proved* to satisfy
   them. That proof is where the work goes, and no measurement here says how large it
   is.

**How to decide.** This is a scout question of exactly the kind §6 of
[V5](../lean/topics/velu/TOPIC-V5-periodpair-uniformization.md) prescribes, with one
item added: *port the ≈1,000-line moduli vocabulary into a scratch file, state the
comparison theorem needed to specialize `aeval_j_diag`, and report whether the pin
proves it anywhere or whether it would have to be built.* A yes at ≈1 k lines competes
very well with 15 k; a no leaves route P as the cheaper one.

## 9. Lean and formal technicalities

- **Where the objects live.** `PeriodPair`, `lattice`, `℘ = weierstrassP`, `℘'`, and
  `analyticOnNhd_weierstrassP` / `order_weierstrassP` are **mathlib** (`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`). `toPoint`, `IsUniformization`,
  `jLattice`, `JSurjective`, `weierstrassCurve`, `sublatticeIndex` are **the pin's**
  `Definitions/Def_PeriodPair_Uniformization.lean` — a 144-line definition module.
  Theory J's objects (`jq`, `qExpand`, the modular polynomial) are the pin's
  `Definitions/Def_ModularCurve_X0.lean`.
- **The port's two cones.** Theory J lives in `FLTForHuman/ModularForms/*` and
  `FLTForHuman/ModularCurve/*`. Theory P would import `IsogenyEndDatum/DualEndData`
  (as V5 explains), i.e. the H5 cone; the two cones are co-importable but P's slice is
  ~15 k pin lines against J's small, already-ported surface.
- **The one formal asymmetry worth naming.** Theory J has an *unusually* small
  analytic base: the port's `QExpansionPrinciple.lean` reduces the level-one input to
  the single mathlib theorem `ModularForm.eq_const_of_weight_zero`, everything else
  being `HasSum`/Laurent-series bookkeeping. Theory P's analytic base is the opposite:
  its 1,493 lines are a from-scratch development of $`\wp`$'s addition theorem and
  Liouville-type arguments that mathlib does not attempt.
- **Pricing.** The closure figures above come from `tools/deps/frontier.py`
  (`fr.closure` over the unported frontier) and `port_advise.py` / `port_plan.py`; the
  per-node attribution in §1 and §6 was read off the pin's `S_` files by grepping the
  `solution` bodies for the names they call. The method matters here because
  `port_advise`'s substitution test is name-anchored and cannot see that a pin name
  and a port name are the same theorem — the reason the `jLattice_surjective` route in
  §3.3 looks "new" to the tool while its instruments are already in the tree.

## Links

Pinned pin sources (`aa2d8b3`):

- [Definitions/Def_PeriodPair_Uniformization.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_PeriodPair_Uniformization.lean) — the dictionary: `toPoint` (line 57), `IsUniformization` (75), `jLattice` (80), `JSurjective` (90)
- [Definitions/Def_ModularCurve_X0.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean) — `jq`, `qExpand`, `FunctionFieldGeneration` (233–242)
- [P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean) — ℘-theory route
- [P2M/Sol/S_PeriodPair_jLattice_surjective.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_jLattice_surjective.lean) — modular-forms route
- [P2M/Sol/S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.lean) — the classification
- [P2M/Sol/S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient.lean) — isogenies as sublattices
- [P2M/Sol/S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint.lean) — the analytic seam
- [Theorems/Thm_ModularCurve_functionFieldGeneration.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_functionFieldGeneration.lean) — theory J's headline

mathlib (tag `v4.34.0`):

- [`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean) — `PeriodPair` (60), `lattice`, `weierstrassP`
- [`NumberTheory/ModularForms/NormTrace.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L164) — `ModularForm.eq_const_of_weight_zero`

The port:

- [math/010 — Function field generation for `X₀(N)`](010-function-field-generation.md) — theory J in full
- [base/013 — Riemann existence and the level-one `q`-expansion principle](../base/013-riemann-existence-and-the-q-expansion-principle.md) — J's analytic input
- [base/004 — The `j`-invariant](../base/004-the-j-invariant.md) — `jq`, its `q`-expansion, integrality
- [`lean/topics/velu/TOPIC-V5-periodpair-uniformization.md`](../lean/topics/velu/TOPIC-V5-periodpair-uniformization.md) — the uniformization slice's scope and measurements

Background:

- J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer 1994, Ch. I — uniformization, lattices, and the moduli interpretation.
- J.-P. Serre, *A Course in Arithmetic*, GTM 7, Springer 1973, Ch. VII — the modular function field, $`j`$ as a Hauptmodul.
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005, §5.2 and Ch. 1 exercises — the generation exercise theory J formalizes.
- S. Lang, *Elliptic Functions*, 2nd ed., GTM 112, Springer 1987, Ch. 5 — the modular equation and its roots.
