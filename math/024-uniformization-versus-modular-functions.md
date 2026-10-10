# Uniformization and the modular function field: two routes to the `j`-line

Twenty-fourth of the `math/` notes. [010](010-function-field-generation.md) proved the
generation theorem for `X₀(N)` — that $`j(q^d) \in \mathbb{Q}(j(q), j(q^N))`$ for every
$`d \mid N`$ — inside a fixed field of formal `q`-expansions;
[base/013](../base/013-riemann-existence-and-the-q-expansion-principle.md) isolated the
one genuinely analytic input it uses (the level-one `q`-expansion principle) and
explained why the rest is algebra. Neither note constructs an analytic model of an
elliptic curve: no `℘`-function theory, no complex torus, no map
$`\mathbb{C}/\Lambda \to E(\mathbb{C})`$.

The pin's proof does use such a theory, in its `PeriodPair` uniformization. This note
answers the two questions that raises: **what does each theory actually construct, and
does either replace the other?**

The short answer, before the machinery:

- the two theories are **complementary, not interchangeable** — neither's theorems
  imply the other's (§5);
- they are **two independent inputs to the same step**: both the generation theorem
  (the `jq` theory) and the $`j`$-diagonal statement
  `aeval_j_diag_eq_zero_of_finrankAlong_eq` (the uniformization theory) are used, by
  different routes, in Mazur's irreducibility argument for the Frey representation;
- and they are not even cleanly separable by subject: inside the theory of the
  uniformization, the surjectivity of $`j`$ — the one statement both theories can speak
  to — is proved by **modular forms**, i.e. with the `jq` theory's instruments (§4.2).

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
citations point at tag **v4.34.0**. Where the prose and the Lean differ, the Lean is
right.

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

Theory J is the classical exercise of Diamond–Shurman:
generate the function field of $`X_0(N)`$ from $`j(q)`$ and $`j(q^N)`$. The one
analytic input is the description of the base $`X(1)`$: it has genus zero and
$`j`$ is a Hauptmodul. In mathlib that is exactly

> `lemma ModularForm.eq_const_of_weight_zero [𝒢.IsArithmetic] (f : ModularForm 𝒢 0) :
    ∃ c, (f : ℍ → ℂ) = Function.const ℍ c` — a weight-zero modular form for an
> arithmetic group is constant
> ([NormTrace.lean, line 164](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/NormTrace.lean#L164)).

From it follow the two statements that make theory J run:

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

```lean
theorem ModularCurve.functionFieldGeneration (N : ℕ) [NeZero N] : FunctionFieldGeneration N
```

is a statement about *fields of Laurent series over* $`\mathbb{Q}`$. Its corollaries
give the degrees of the tower $`X_0(Mp^a) \to X(1)`$, with $`\psi`$ the Dedekind psi
function: `modularFunctionField_eq_full`, `finrank_adjoin_jqN_eq_dedekindPsi`,
`relfinrank_full_eq_dedekindPsi`.

The medium matters as much as the content. There is no Riemann surface anywhere in
theory J: the field is fixed in advance and every step is formal. That is what makes
it portable to $`\mathbb{Q}`$ — and it is also its ceiling, §5.

## 3. Theory P: uniformization

### 3.1 The dictionary

[`Def_PeriodPair_Uniformization.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_PeriodPair_Uniformization.lean)
attaches to a lattice `L : PeriodPair` — mathlib's pair of
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

`PeriodPair.isUniformization_toPoint` is purely complex-analytic.
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

`PeriodPair.jLattice_surjective` is the statement
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
`kw_JSurjective`). **Surjectivity of $`j`$ is established here with the modular-forms
instruments**, the same $`E_4, E_6`$, `CuspForm`, `discriminant` and `qExpansion`
vocabulary that [base/004](../base/004-the-j-invariant.md) already introduced.

### 3.4 What only theory P can say

From `toPoint` and `jLattice`, theory P derives the statements the FLT proof actually
consumes at this node:

- **classification of complex elliptic curves.**
  `exists_variableChange_smul_weierstrassCurve_eq` says every elliptic $`E/\mathbb{C}`$
  is $`C \bullet L.\mathrm{weierstrassCurve}`$ for some lattice and some variable
  change; its six-line proof *is* `jLattice_surjective` plus
  `exists_variableChange_of_j_eq`. This is the statement "elliptic curves over
  $`\mathbb{C}`$ are lattices", and no amount of `q`-expansion gives it;
- **isogenies are sublattices.**
  `exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient`:
  a finite isogeny between the two lattice curves corresponds to a
  $`\beta \in \mathbb{C}^\times`$ with $`(L'.\mathrm{scale}\,\beta).\mathrm{lattice} \subseteq L.\mathrm{lattice}`$,
  the degree equals the sublattice index `sublatticeIndex`, and a cyclic kernel means
  a cyclic quotient. Nothing here is algebraic: the proof needs the uniformization to
  identify the function-field map with a map of tori;
- **the analytic seam.** `exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`:
  given a finite separable $`\iota`$ between function fields, there is a
  differentiable $`F : \mathbb{C} \to \mathbb{C}`$ with $`F(0) \in L'.\mathrm{lattice}`$
  and

  $$`L'.\mathrm{toPoint}\bigl(F(z)\bigr) \;=\; \mathrm{pointMapOfPushforward}\,\iota\,\cdots\,\bigl(L.\mathrm{toPoint}(z)\bigr),`$$

  i.e. *the algebraic pushforward is differentiable in uniformization coordinates*.
  This is the statement with no `jq` counterpart.

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
consumers need generation *over* $`\mathbb{Q}`$ of the $`X_0(N)`$ tower; theory P's
consumers need the torus. Each is silent exactly where the other is used.

### 4.2 Where the pin refuses to choose

The decisive evidence is the pin's own proof of `jLattice_surjective` (§3.3): inside
the *uniformization* slice, the surjectivity of $`j`$ is established by *modular
forms* — Eisenstein series, `CuspForm`, `qExpansion`, `riemannZeta 6`. The pin does
not prove it from $`\wp`$. So the theories are not even separated by their
statements: they share the $`j`$-line, and at that shared point the pin routes the
argument through the cheaper of the two, which is theory J's.

## 5. Do they replace each other?

**No.** The two implications both fail, and the pin's own citations show it.

**P does not give J.** Uniformization is a statement over $`\mathbb{C}`$ about a
covering; it says nothing about `q`-expansions, nothing about $`\mathbb{Q}`$, and
carries no modular equation. It cannot produce `functionFieldGeneration`, nor any of
its corollaries — the degree of $`X_0(Mp^a) \to X(1)`$ is a statement about
$`\psi(Mp^a)`$, not about a torus.

**J does not give P.** Theory J never constructs a map $`\mathbb{C}/\Lambda \to E`$. It
has no $`\wp`$, no addition theorem, no analytic order. It cannot produce
`IsUniformization`, `toPoint`'s surjectivity, the differentiable lift `F` of §3.4, or
the isogeny/sublattice dictionary — those are all statements about the torus.

The pin's citations confirm it: the proof of `functionFieldGeneration` never invokes
`aeval_j_diag_eq_zero_of_finrankAlong_eq`, and the proof of the latter never invokes the
former, while Mazur's step uses both. They are independent inputs to the same step,
neither containing the other. A closer look sharpens the point:
`modularPolynomial_rootMultiplicity_jQuotVelu_eq_one` uses `jLattice_surjective` but not
`functionFieldGeneration` — so the modular-forms half of the uniformization theory is
load-bearing on **both** Mazur-step-three sub-routes, not only on the one that consumes
the $`\wp`$-theory.

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

Since the two imply neither each other nor a common generalization, a proof of one is
not a substitute for the other: the FLT proof needs both facts about the $`j`$-line —
*which field*, and *which torus* — and each theory supplies exactly one of them.

## 7. Where this sits in the proof: Deligne–Serre and `R = T`

The pin's route ([PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/PROOF-PATH.md))
has four steps: reduce to $`p \ge 5`$; build the Frey package; **irreducibility**
(Mazur's Eisenstein-ideal argument); **modularity** (Wiles: Langlands–Tunnell, then
two `R = T` modularity-lifting theorems). The two theories are used on opposite sides
of that split — P in step 3's irreducibility mechanism, J in step 4's modularity — but
the pin's citation cones do not keep them apart.

**P's shortest route to the root is step 3, but it is not step-3-only.** The
uniformization slice enters the proof through `aeval_j_diag_eq_zero_of_finrankAlong_eq`,
whose only two consumers in the entire pin are
`IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_not_isIntegral_j` and
`…_of_transcendental_j`. The first gives the shortest route: from it the path runs
`separable_map_eval2_of_not_isIntegral` $`\to`$
`modularPolynomial_rootMultiplicity_jQuotVelu_eq_one` $`\to`$
`moduliPointExists_jQuotVelu_of_mult_two` $`\to`$
`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt` $`\to`$
`FreyPackage.frey_no_cofixed_large`. That is step 3 — **irreducibility**: Mazur's
Eisenstein-ideal theorem carried out for this situation ($`p \ge 17`$, no Galois-stable
line in $`E[p]`$; not the modularity step), on $`X_0(N)`$, its Jacobian and Néron model,
the cuspidal subgroup, the Eisenstein quotient. The same Eisenstein-ideal machinery
underlies Mazur's torsion and rational-points theorems; those are not used here.

**The other consumer carries P into the step-4 cone.** `…_of_transcendental_j` is the
branch the modular side consumes, and it puts `aeval_j_diag` in the transitive cone of
step 4's source `S_WeierstrassCurve_modularity_of_semistableModel.lean` and of the
`DeligneSerre` capstone `exists_galoisRep_of_weightOne_qCoeff_hecke_eigen`. The route is
the **weight-one input**, not the relèvement: `isResiduallyModular_…` $`\to`$
`weightOneNewformExists_levelAtThree_not_cube_dvd` $`\to`$ `hasIntegralStructure_two`
$`\to`$ `linearIndependent_complex_of_linearIndependent_int` $`\to`$
`periodHomPair_range_eq_parabolicHoms` $`\to`$ `eichlerShimura_dim_parabolic` $`\to`$
`genusFormula_le_finrank_gamma0_weight_two` $`\to`$
`genus_modularFunctionFieldBar_eq_genusFormula` $`\to`$ `ord_jBar_dvd_three` $`\to`$
`mem_of_isRoot_map_j_of_transcendental` $`\to`$ `…_of_transcendental_j`. Every step is a
proof-level citation in the pin. So step 3 is P's shortest route to the root, not its
only one.

**J is on the same step, and its generation theorem also reaches the step-4 cone.**
`functionFieldGeneration` and its corollaries are the roof generation and degree match
of the $`X_0(N)`$ tower that [009](009-hecke-jacobian-commute.md) uses, i.e. the
geometry Mazur's argument runs on, and they are consumed by the mod-$`p`$
modular-curve layer (`ModularCurve/CharPModel/*`). They enter the step-4 cone too,
through the same weight-one branch: `genusFormula_le_finrank_gamma0_weight_two`
$`\to`$ `isCurveOver_modularFunctionFieldBar` $`\to`$ `functionFieldGeneration`. What
meets step 4 there is the generation theorem itself, not only the $`q`$-expansion
vocabulary.

**The relèvement and the `R = T` statement stay clean.** The Deligne–Serre lifting lemma
and the statement that names $`R = T`$ —
`FLT.AbstractIntegralStructure.exists_weight_two_eigenform_congruent_of_isLatticeRealized`
and `GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum` —
have cones containing neither `PeriodPair` nor `functionFieldGeneration`, and step 4's
source names neither among its direct cites. D-S is the *weight-one* input to step 4:
Langlands–Tunnell produces a weight-one form for the odd octahedral $`\bar\rho_3`$;
multiplying by the weight-one Eisenstein series $`E_1(1,\chi_{-3})`$ and applying the
lifting lemma produces a congruent weight-two eigenform, which is what makes
$`\bar\rho_3`$ residually modular and lets the `R = T` machinery start. Every instrument
in that step — Eisenstein series, Hecke operators on $`\Gamma_1(N)`$, `q`-expansions, the
Sturm bound, the $`\Gamma_1`$ integral basis — is J's universe. None of it is
$`\wp`$-theory.

**Why the entry is a route, not a necessity.** `R = T` is a statement about deformation
rings and Hecke algebras over $`\mathcal{O}`$: its inputs are congruences, integrality
and patching — exactly the arithmetic of `q`-expansions. Uniformization is
transcendental, and the relèvement's own cone confirms it is not needed there. Where the
pin does reach P from step 4 is in the proof of the $`\Gamma_1`$ integral-structure
input, which it routes through the genus formula and `ord_jBar_dvd_three`; that node
needs the $`j`$-line criterion `mem_of_isRoot_map_j_of_transcendental`, and that in turn
runs through the isogeny/Vélu machinery. So the two theories meet the step-4 cone
asymmetrically: P only through that $`j`$-line criterion, J both as `q`-expansion input
and as the generation theorem. Nothing in the mathematics of D-S or $`R = T`$ calls for
$`\wp`$-theory.

### 7.1 "Uniformization" is not one theory

Three different uniformizations live in this area, and only the first is the
uniformization of theory P:

1. **classical complex uniformization**, $`\mathbb{C}/\Lambda \cong E(\mathbb{C})`$ by
   the $`\wp`$-map — `PeriodPair`, step 3;
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

### 7.2 Why the transcendental existence is load-bearing

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
substitute, and §7.3 asks whether the pin's own moduli vocabulary can stand in for it.
The two theories are the two halves of "the modular curve parametrizes elliptic
curves": J has the algebraic/`q`-expansion half, P has the existence half.

### 7.3 The algebraic alternative

The bridge does not have to be the analytic one. The pin also carries a **moduli-place**
formulation of the same comparison, and it is purely algebraic.

- A `Gamma0Pair` over a field $`L`$ is an elliptic curve together with a point of order
  *exactly* $`N`$; `ModuliPoint N L` is the quotient of these by variable changes and
  the $`\Gamma_0(N)`$ relabelling, and `ModuliPoint.j : ModuliPoint N L \to L` is the
  $`j`$-invariant
  ([`Def_ModularCurve_ModuliPoint.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPoint.lean)).
- On top of it,
  [`Def_ModularCurve_ModuliPlace.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPlace.lean)
  defines what it means for a place $`v`$ of the modular function field to *be* the
  moduli point of such a pair — `IsModuliPlaceOf x v`, `moduliPlaceOfPoint`, and
  `moduliPlace E C` — over a general field, with no $`\wp`$ anywhere.

If that comparison can carry the argument, then $`\Phi_N(j(E)) = 0`$ for an
$`N`$-isogeny would follow by **specialization** through `moduliPlace` rather than by a
lattice computation over $`\mathbb{C}`$: the `q`-expansion-defined modular polynomial
would be compared with the synthetic moduli problem directly. That is the algebraic
moduli interpretation, and it is the form of bridge that theory J would need. It is
also exactly the half of the classical theory that theory J, as a statement about
function fields, leaves out.

Whether it can carry the argument is a separate question, and there are two reasons for
caution. The pin does not use this route for the $`j`$-diagonal statement — it descends
to $`\mathbb{C}`$ instead — which is evidence, though not proof, that the moduli-place
comparison is harder here, or is not stated in the shape that statement needs. And the
two moduli problems are not identical: `ModuliPoint N L` carries a point of order
exactly $`N`$, while the $`j`$-diagonal statement starts from an isogeny of degree
$`N`$ whose $`N`$ comes from a negative-discriminant binary quadratic form. Passing
between a cyclic $`N`$-isogeny and a point of order $`N`$ (kernel and dual) is a real
step.

## 8. Lean and formal technicalities

- **Where the objects live.** `PeriodPair`, `lattice`, $`\wp`$ = `weierstrassP`, $`\wp'`$,
  and `analyticOnNhd_weierstrassP` / `order_weierstrassP` are **mathlib**
  (`Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`). `toPoint`,
  `IsUniformization`, `jLattice`, `JSurjective`, `weierstrassCurve`, `sublatticeIndex`
  and `scale` are **the pin's**
  `Definitions/Def_PeriodPair_Uniformization.lean`. Theory J's objects (`jq`,
  `qExpand`, the modular polynomial) are the pin's
  `Definitions/Def_ModularCurve_X0.lean`.
- **The two are asymmetric in their analytic base.** Theory J rests on a single mathlib
  theorem, `ModularForm.eq_const_of_weight_zero`; everything else in it is
  `HasSum`/Laurent-series bookkeeping. Theory P is the opposite: $`\wp`$'s addition
  theorem, the analytic order at a lattice point, and the Liouville-type arguments are
  developed from scratch, and mathlib does not attempt them.
- **The $`j`$-diagonal statement is proved by descent to $`\mathbb{C}`$**, not inside a
  generic `q`-expansion. That is a choice of the pin's, not a shape forced by the
  statement — which is what §7.3 exploits.

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

Companion notes:

- [math/010 — Function field generation for `X₀(N)`](010-function-field-generation.md) — theory J in full
- [base/013 — Riemann existence and the level-one `q`-expansion principle](../base/013-riemann-existence-and-the-q-expansion-principle.md) — J's analytic input
- [base/004 — The `j`-invariant](../base/004-the-j-invariant.md) — `jq`, its `q`-expansion, integrality

Background:

- J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer 1994, Ch. I — uniformization, lattices, and the moduli interpretation.
- J.-P. Serre, *A Course in Arithmetic*, GTM 7, Springer 1973, Ch. VII — the modular function field, $`j`$ as a Hauptmodul.
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005, §5.2 and Ch. 1 exercises — the generation exercise theory J formalizes.
- S. Lang, *Elliptic Functions*, 2nd ed., GTM 112, Springer 1987, Ch. 5 — the modular equation and its roots.
