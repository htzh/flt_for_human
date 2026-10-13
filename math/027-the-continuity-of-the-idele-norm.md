# The continuity of the idele norm

Twenty-seventh of the `math/` notes. [base/012](../base/012-adeles-and-automorphic-representations.md)
introduced the adele ring and the adelic dictionary, and
[base/022](../base/022-haar-measure.md) the Haar measure the adelic integrals are taken
against. This note is about a single analytic fact those two layers both use without
proving: **the idele norm is continuous**, and so is the norm of the determinant on
$`\mathrm{GL}_2`$ over the adeles. The two statements are the smallest and most heavily
cited theorems of the `NumberField.TateGlobal` layer — 217 and 163 direct dependents in the
pin — and the proof is a clean illustration of why the *restricted*-product topology is the
right one.

The mathematics is §1–§4, the leverage is §5, and the Lean map is collected in §6.

## 1. The norm on the ideles

Let $`F`$ be a number field with ring of integers $`\mathfrak{o}_F`$, and let
$`v`$ run over the places of $`F`$. Write $`F_v`$ for the completion at $`v`$ and
$`\mathfrak{o}_v`$ for the ring of integers of $`F_v`$ at a finite place. The **adele ring**
is the restricted product

$$\mathbb{A}_F \;=\; \prod_{v \mid \infty} F_v \;\times\; \prod_{v \nmid \infty}{}' F_v ,$$

the second factor keeping only the tuples with $`x_v \in \mathfrak{o}_v`$ for almost all
finite $`v`$. The **ideles** are its unit group $`\mathbb{A}_F^\times`$.

Each place carries a *normalised* absolute value.

- At a finite place $`v`$, with maximal ideal $`\mathfrak{m}_v`$ and residue cardinality
  $`N(v) = \lvert \mathfrak{o}_v/\mathfrak{m}_v \rvert`$, one normalises so that a
  uniformiser has size $`N(v)^{-1}`$,

$$|x|_v = N(v)^{-\mathrm{ord}_v(x)}, \qquad |x|_v = 1 \ \text{ for } x \in \mathfrak{o}_v^\times .$$

- At an infinite place $`w`$, the completion is $`\mathbb{R}`$ or $`\mathbb{C}`$ and one
  takes the $`n_w`$-th power of the ordinary norm, where $`n_w = [F_w : \mathbb{R}]`$ is
  $`1`$ for a real place and $`2`$ for a complex one:

$$|z|_w = \lVert z \rVert^{n_w}, \qquad n_w \in \\{1, 2\\}.$$

The **idele norm** is the product of the local factors,

$$|x| \;=\; \prod_v |x_v|_v \qquad (x = (x_v)_v \in \mathbb{A}_F^\times),$$

which is a *finite* product: an idele is a unit at almost every finite place, and the local
factor there is $`1`$. It takes values in $`\mathbb{R}_{\gt 0}`$ because every local factor
does, and it is multiplicative,

$$|xy| = |x| \, |y|, \qquad |1| = 1 .$$

**The same object by measure.** The norm is not an ad hoc product: it is the scalar by which
multiplication by $`x`$ distorts additive Haar measure on $`\mathbb{A}_F`$. For a Haar
measure $`\mu`$ on $`\mathbb{A}_F`$ and a measurable set $`E`$,

$$\mu(x E) = |x| \, \mu(E) \qquad \text{for all } x \in \mathbb{A}_F^\times ,$$

and the scalar is independent of the choice of $`\mu`$. This is the **modulus character**
(distributive Haar character) of the multiplicative action of $`\mathbb{A}_F^\times`$ on
$`\mathbb{A}_F`$; mathlib defines it abstractly from Haar uniqueness, and the pin's
`ideleNorm` is its real-valued shadow. Additivity of the action — $`x(y+z) = xy + xz`$ — is
what makes the Haar measure transform by a single scalar, and multiplicativity of the norm
is exactly multiplicativity of that character.

**What the norm forgets.** The diagonal embedding $`F^\times \hookrightarrow \mathbb{A}_F^\times`$
lands in the kernel: the **product formula**

$$\prod_v |a|_v = 1 \qquad (a \in F^\times)$$

says $`|a| = 1`$ for every rational idele. Hence the norm descends to the **idele class
group** $`C_F = \mathbb{A}_F^\times / F^\times`$, and its kernel is the subgroup

$$\mathbb{A}_F^1 = \ker(| \cdot |) = \\{ x : |x| = 1 \\}$$

of **norm-one ideles**. The product formula is also the reason the archimedean factors are
included at all: with only finite places, the norm of a rational number would be
$`1/|\mathrm{N}_{F/\mathbb{Q}}(a)|`$. Two standard facts about this subgroup are used
downstream: $`F^\times \subset \mathbb{A}_F^1`$ is discrete and cocompact
(Fujisaki's compactness theorem, $`\mathbb{A}_F^1/F^\times`$ compact), so that the idele
class group $`C_F`$ is an extension of $`\mathbb{R}_{\gt 0}`$ by the compact group
$`\mathbb{A}_F^1/F^\times`$.

## 2. The topology the norm lives on

The adeles carry the restricted-product topology: a basis of open sets is given by choosing
open conditions in *finitely many* coordinates and requiring $`x_v \in \mathfrak{o}_v`$ in
all the others. The ideles $`\mathbb{A}_F^\times`$ are given the unit-group topology, i.e.
the subspace topology of

$$\mathbb{A}_F^\times \longrightarrow \mathbb{A}_F \times \mathbb{A}_F, \qquad
  x \longmapsto (x, x^{-1}).$$

This is *not* the subspace topology from $`\mathbb{A}_F`$ alone (the ideles are not closed
there); the inverse coordinate is what makes inversion continuous. With it,
$`\mathbb{A}_F^\times`$ is a locally compact abelian group.

Two features make the continuity of §1 non-formal, and both are consequences of the same
"almost everywhere" restriction.

1. **It is an infinite product.** $`|x|`$ is a product over all places. A pointwise product
   of infinitely many continuous functions need not be continuous — one needs the product to
   be *locally finite*, i.e. all but finitely many factors locally constant and equal to
   $`1`$.
2. **The restricted-product neighbourhoods are not product neighbourhoods.** A small
   neighbourhood of an idele is described by finitely many coordinates together with the
   constraint "all the rest are units"; it is not a box in the full product.

The two defects cancel, and that is the content of the proof: on the open pieces where the
relevant places are made explicit, the norm *is* a finite product.

## 3. The proof

Fix a finite set $`S`$ of finite places and put

$$\mathfrak{o}_F(S) = \\{ x \in \mathbb{A}_F : x_v \in \mathfrak{o}_v \ \text{ for all finite } v \notin S \\}, \qquad
  U_S = \mathfrak{o}_F(S) \cap \mathfrak{o}_F(S)^{-1} \subseteq \mathbb{A}_F^\times .$$

So $`U_S`$ is the set of ideles that are units at every place outside $`S`$. The proof has
four moves.

**Move 1 — the open cover.** Each $`U_S`$ is open in $`\mathbb{A}_F^\times`$, and

$$\mathbb{A}_F^\times = \bigcup_{S \ \text{finite}} U_S .$$

The inclusion is the "almost everywhere" condition made explicit: for a given idele $`x`$,
the coordinates of $`x`$ and of $`x^{-1}`$ fail to be integral at only finitely many places
(that is precisely what the restricted product permits), and the union of those two finite
sets is an $`S`$ with $`x \in U_S`$.

**Move 2 — coordinates on a piece.** On $`U_S`$ the idele decomposes into three independent
factors,

$$U_S \;\cong\; \Bigl( \prod_{w \mid \infty} F_w^\times \Bigr) \;\times\;
  \Bigl( \prod_{v \in S} F_v^\times \Bigr) \;\times\;
  \Bigl( \prod_{v \notin S} \mathfrak{o}_v^\times \Bigr),$$

the archimedean units, the units at the finitely many places of $`S`$, and the units at all
other places. The map from the product to $`U_S`$ (assembling an idele from its coordinates)
and its inverse (reading off the coordinates) are inverse homeomorphisms. The last factor is
a product of *compact* groups $`\mathfrak{o}_v^\times`$ — this is the payoff of the
restriction: outside $`S`$ nothing can run away.

**Move 3 — the norm on the coordinates is a finite product, hence continuous.** Writing a
point of the product as $`q = (q_\infty, q_S, q_{\notin S})`$, the norm becomes

$$\mathrm{normQ}(q) \;=\; \prod_{w \mid \infty} \lVert q_\infty(w) \rVert^{\,n_w}
  \;\cdot\; \prod_{v \in S} \lVert q_S(v) \rVert \;\cdot\; \prod_{v \notin S} 1 .$$

The last product is $`1`$ because $`|u|_v = 1`$ for $`u \in \mathfrak{o}_v^\times`$. What
remains is a product over the finitely many places in $`S`$ together with the finitely many
archimedean places, and each factor is continuous: $`\lVert \cdot \rVert`$ is continuous on
$`F_w^\times`$ and on $`F_v^\times`$, the exponent $`n_w`$ is a constant, and a finite
product of continuous real-valued functions is continuous.

**Move 4 — identify and glue.** The two descriptions of the norm agree on $`U_S`$,

$$|x| = \mathrm{normQ}(\mathrm{coord}(x)) \qquad (x \in U_S),$$

because both sides are multiplicative characters and they are computed on the same three
factors: the archimedean factor is $`\lVert z \rVert^{n_w}`$, the finite factor is
$`\lVert t \rVert`$, and the outside-$`S`$ factor is $`1`$ on both sides. So the norm
restricted to $`U_S`$ is a composite of continuous maps, hence continuous on $`U_S`$. Since
the $`U_S`$ form an open cover, continuity on each piece glues to continuity on all of
$`\mathbb{A}_F^\times`$.

**The moral.** Continuity of the idele norm is not an arithmetic statement (the product
formula plays no role); it is the statement that the restricted product turns an infinite
product of local characters into a *locally finite* one. The open cover by the pieces
$`U_S`$ is the combinatorial heart, and "every idele is integral outside a finite set" is the
only input.

## 4. The determinant and GL₂

The second theorem is the first one composed with the determinant. Let
$`G = \mathrm{GL}_2(\mathbb{A}_F)`$.

**The determinant is continuous.** $`\det : G \to \mathbb{A}_F^\times`$ is a polynomial
function of the four matrix entries; on the open set of invertible matrices its inverse is
given by the adjugate divided by the determinant, so $`\det`$ is a continuous homomorphism
from $`G`$ onto $`\mathbb{A}_F^\times`$. (Concretely, a convergent sequence of matrices has
convergent entries, the determinant is a polynomial in them, and the inverse matrix is
continuous on $`G`$.)

Composing with the norm gives the **determinant norm**

$$g \;\longmapsto\; |\det g| , \qquad \mathrm{GL}_2(\mathbb{A}_F) \longrightarrow \mathbb{R}_{\gt 0},$$

which is continuous: it is the composite of the continuous determinant and the continuous
idele norm. This is the second ported theorem.

**Why the centre.** The scalar matrices embed the ideles as the centre,

$$\mathbb{A}_F^\times \longrightarrow G, \qquad z \longmapsto z I = \begin{pmatrix} z & 0 \\\\ 0 & z \end{pmatrix},$$

and $`\det(zI) = z^2`$, so $`|\det(zI)| = |z|^2`$. Thus the two scalar parameters that
matter for the adelic theory are both read off from the determinant norm: the central
character of an automorphic representation is a character of $`\mathbb{A}_F^\times`$ whose
unitary part is the twist $`z \mapsto |z|^{it}`$, and the *weight* attached to a function on
$`G`$ under central scaling is a power of $`|z|`$ — i.e. of $`|\det|`$.

Two reductions recur. The **unitary locus** is $`|\det g| = 1`$, where the central action is
measure-preserving; and the **truncation bands** $`1 \le |\det g| \le T`$ cut $`G`$ into the
pieces on which the non-compactness of $`G/Z`$ is measured. Both are level sets (or
sublevel sets) of the continuous function $`|\det|`$, which is why its continuity precedes
everything built on top of them.

## 5. Why the two are leveraged

The continuity of $`|\cdot|`$ and of $`|\det|`$ is not used as a technicality; it is the
hypothesis that makes the analytic vocabulary of the automorphic layer well defined. Four
uses account for most of the citations.

1. **Unitary characters and normalisation.** A Hecke character $`\chi`$ is *unitary* when
   $`\lvert \chi(x) \rvert = 1`$ for all $`x`$. The standard normalisation of a general
   central character is $`\chi \mapsto \chi \cdot |\cdot|^{it}`$, whose unitary part is
   $`\chi_0`$; that $`x \mapsto |x|^{it}`$ is a *continuous* character, and that the twist
   preserves unitarity, is exactly a consequence of the continuity of the norm. The pin's
   package `isUnitaryChar_isIdeleClassChar_localChar_archLocalChar_mul_normPowChar` is the
   formal statement of this normalisation.
2. **Growth and decay estimates.** The standard bounds for cusp forms and their Whittaker
   coefficients are of the shape

$$\lvert f(g) \rvert \le M \, \lvert \det g \rvert^{\,w_0/2}, \qquad
   \lvert W(\mathrm{diag}(1, \cdot)) \rvert \le M \, \lvert \det \rvert^{\,\sigma},$$

   and the majorants on Siegel domains carry a factor $`|\det g|^{\sigma}`$. These are
   measurable/integrable statements about a continuous function of $`g`$; without continuity
   there is no Borel function to estimate.
3. **Truncation and fundamental domains.** Fujisaki's theory computes the volume of
   $`\mathbb{A}_F^1/F^\times`$ and of fundamental domains of the centre by slicing along
   $`|\det|`$. The sets $`\{ g : a \le |\det g| \le b \}`$ are the slices, the change of
   variables that turns the multiplicative measure into $`dt/t`$ is the modulus law
   $`\mu(xE) = |x|\mu(E)`$ of §1, and the class number and regulator appear as the measure of
   a fundamental domain. All of this starts from continuity of $`|\det|`$.
4. **The zeta integral and unfolding.** The Tate zeta integral

$$\zeta(f, \chi, s) = \int_{\mathbb{A}_F^\times} f(x) \, \chi(x) \, |x|^s \, d^\times x$$

   is built from the factor $`|x|^s`$; the Euler unfolding and the meromorphic continuation
   manipulate it as a function of $`x`$ and of $`s`$, again through the continuity and the
   multiplicativity of the norm.

Numbers, from the pin graph: `continuous_ideleNorm` has 217 direct dependents (111 in
`AutomorphicForm`, 71 in `LanglandsTunnell`, 28 in `NumberField`, the rest in the
twisted-unipotent and Whittaker layers); `continuous_ideleNorm_det` has 163 (126 and 30 in
the first two). Inside the Deligne–Serre target's closure they are cited by 15 and 33 nodes
directly, and 162 and 136 transitively. These are among the most cited declarations of the
`NumberField.TateGlobal` family, which is why they were ported before the rest of it.

## 6. Lean technicalities

The mathematical content is §§1–§5; this section records names, statement shapes and where
the objects live. Pin line numbers are for `aa2d8b3`, mathlib citations for tag `v4.34.0`,
and the port is the public `htzh/flt_for_human` tree.

**The definitions.** The vocabulary is the pin's
[`Definitions/Def_NumberField_TateGlobalZeta.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_TateGlobalZeta.lean),
homed whole in the port at
[`../lean/FLTForHuman/NumberTheory/NumberField/TateGlobal/Defs.lean`](../lean/FLTForHuman/NumberTheory/NumberField/TateGlobal/Defs.lean):

| Lean | pin line | mathematics |
|---|---|---|
| `ideleNorm F x : ℝ` | 19 | $`\lvert x \rvert`$, as `distribHaarChar` coerced to $`\mathbb{R}`$ |
| `normOneIdeles F` | 16 | $`\mathbb{A}_F^1 = \ker \lvert \cdot \rvert`$ |
| `ideleNorm_pos` | 24 | $`\lvert x \rvert \gt 0`$ |
| `ideleNorm_mul` | 73 | multiplicativity |
| `mem_normOneIdeles_iff` | 76 | $`x \in \mathbb{A}_F^1 \leftrightarrow \lvert x \rvert = 1`$ |
| `integralOutside S` | 64 | $`\mathfrak{o}_F(S)`$ of §3 |

The modulus character itself is mathlib's
[`MeasureTheory.distribHaarChar`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean#L44),
a monoid homomorphism $`G \to \mathbb{R}_{\ge 0}`$ defined from the Haar-measure scaling
scalar; `distribHaarChar_pos` is its positivity. mathlib supplies **no**
`continuous_distribHaarChar`, so the number-field case is proved by hand. The local degrees
are mathlib's
[`InfinitePlace.mult`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean#L275)
($`1`$ real, $`2`$ complex), and the adeles are mathlib's restricted product
([`Topology/Algebra/RestrictedProduct/`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean)).

**The proof.** It is the pin's
[`P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm.lean`](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm.lean)
(2,645 lines), whose unique content is the final `Fold_FujisakiC3d` section:

| Lean | pin line | §3 move |
|---|---|---|
| `exists_mem_unitsOutside` | 2578 | 1: $`\mathbb{A}_F^\times = \bigcup_S U_S`$ |
| `normQ` | 2599 | 3: the finite-product norm on the coordinates |
| `continuous_normQ` | 2603 | 3: continuity of the finite product |
| `ideleNorm_asm_eq_normQ` | 2610 | 4: $`\lvert x \rvert = \mathrm{normQ}(\mathrm{coord}\,x)`$ on $`U_S`$ |
| `continuousOn_ideleNorm` | 2619 | 4: continuity on one open piece |
| `continuous_ideleNorm` | 2628 | 4: glue over the cover |

The statements are the pin's `Theorems/` wrappers,
[`Thm_NumberField_TateGlobal_continuous_ideleNorm.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm.lean)
(9 lines) and
[`…_continuous_ideleNorm_det.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm_det.lean)
(11 lines). The `_det` theorem is proved by a 15-line `S_` file that composes the first
headline with `Matrix.GeneralLinearGroup.continuous_det`.

**What had to be reused.** Of the 171 private helpers in the pin's 2,645-line silo, **165
were already in the port** — the silo re-proves the T1 analytic core — so the port's own
contribution is 6 declarations and about 65 lines. Those helpers live in the port's T1
development (`TateGlobal/Coordinates.lean`, `…/Ideles.lean`, `…/ZetaIntegrand.lean`,
`…/IntLocalIntegrability.lean`, `…/NormIntegrable.lean`, and the rest); the moves of §3 are
the port's `asm`/`coord` homeomorphism (`Coordinates.lean`), `unitsOutside` and its openness
(`Ideles.lean`), and the two local-factor identities
`distribHaarChar_completion_eq_pow_mult` and `coe_distribHaarChar_adicCompletion_eq_norm`
(`IntLocalIntegrability.lean`, `NormIntegrable.lean`).

**The port structure.** One tier-3 engine and one thin listed façade:

| port module | role |
|---|---|
| [`…/TateGlobal/FujisakiC3.lean`](../lean/FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiC3.lean) | the six declarations above, public as `NumberField.TateGlobal.FujisakiC3.*`, unlisted (registered in `spec/UNWIRED-PUBLIC.md`) |
| [`…/NumberField/TateGlobalContinuousIdeleNorm.lean`](../lean/FLTForHuman/NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean) | the two checked headlines, at the pin names `NumberField.TateGlobal.continuous_ideleNorm` and `…_det` |

The façade imports only the engine, so a consumer of the idele norm's continuity does not
drag in the three T1 analytic-core caps. The statement checker reads **9542 identical / 0
mismatched / 0 missing**, a delta of exactly the two headlines; both depend only on
`[propext, Classical.choice, Quot.sound]`.

**Two build notes.**

1. `continuous_normQ`: the pin's `Units.continuous_val.comp continuous_fst` loses the
   `TopologicalSpace` instance, because `InfiniteAdeleRing` is a non-reducible `def` and its
   instance is keyed on the folded head, which the elaborator unfolds. Writing
   `Units.continuous_val (M := InfiniteAdeleRing F)` pins the base monoid and restores it.
   This is a proof adaptation; the statements are verbatim.
2. The `det` headline needs `Mathlib.Topology.Algebra.Group.Matrix` for
   `Matrix.GeneralLinearGroup.continuous_det`.

**What is not ported.** The pin's 2,645-line silo is one of nine sibling `S_` files that
re-prove the same `normQ` block; the port homes that block once, in the engine. The two
siblings that lie in the Deligne–Serre cone
(`exists_meromorphicOn_eq_partialEulerProduct`, `zetaIntegral_meromorphic_continuation_fe`)
are priced at 7,544 net-new lines together, and the other six add 2,826 on top; the
measurement, the block structure and the recommendation are in
[../lean/topics/numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md](../lean/topics/numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md).

## Links

Pin sources (`anthropics/fermats-last-theorem@aa2d8b3`):

- [`Definitions/Def_NumberField_TateGlobalZeta.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_TateGlobalZeta.lean) — `normOneIdeles` (16), `ideleNorm` (19), `ideleNorm_pos` (24), `integralOutside` (64), `ideleNorm_mul` (73), `mem_normOneIdeles_iff` (76)
- [`Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm.lean) — the statement of the first theorem
- [`Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm_det.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm_det.lean) — the statement of the determinant corollary
- [`P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm.lean`](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_continuous_ideleNorm.lean) — the proof: `exists_mem_unitsOutside` (2578), `normQ` (2599), `continuous_normQ` (2603), `ideleNorm_asm_eq_normQ` (2610), `continuousOn_ideleNorm` (2619), `continuous_ideleNorm` (2628)
- [`Theorems/Thm_NumberField_AdeleRing_distribHaarChar_algebraMap.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdeleRing_distribHaarChar_algebraMap.lean) — the product formula of §1
- [`Theorems/Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass.lean) — Fujisaki: $`\mathbb{A}_F^1/F^\times`$ is compact
- [`Definitions/Def_NumberField_NormPowChar.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_NormPowChar.lean) — `normPowChar`, the unitary twist $`x \mapsto |x|^{it}`$ (its continuity is the headline composed with the continuous map $`x \mapsto x^{it}`$)
- [`Definitions/Def_AutomorphicForm_AdelicLsXi.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_AdelicLsXi.lean#L24) — `IsUnitaryChar`

mathlib (tag `v4.34.0`):

- [`MeasureTheory/Measure/Haar/DistribChar.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean#L44) — `distribHaarChar`, the modulus character, and `distribHaarChar_pos`
- [`NumberTheory/NumberField/InfinitePlace/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean#L275) — `InfinitePlace.mult`
- [`Topology/Algebra/RestrictedProduct/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean) — the restricted product, and `RestrictedProduct/Units.lean` for its units
- [`Topology/Algebra/Group/Matrix.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Topology/Algebra/Group/Matrix.lean#L60) — `Matrix.GeneralLinearGroup.continuous_det`

Port:

- [`…/TateGlobal/FujisakiC3.lean`](../lean/FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiC3.lean) — the engine
- [`…/NumberField/TateGlobalContinuousIdeleNorm.lean`](../lean/FLTForHuman/NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean) — the two headlines
- [`…/TateGlobal/Defs.lean`](../lean/FLTForHuman/NumberTheory/NumberField/TateGlobal/Defs.lean) — `ideleNorm` and the definition layer
- [TOPIC-continuous-ideleNorm.md](../lean/topics/numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md) — the porting record and the sibling pricing

Companion notes:

- [base/012 — Adeles, automorphic representations, and the adelic dictionary](../base/012-adeles-and-automorphic-representations.md) — the adele ring, $`\mathrm{GL}_2(\mathbb{A}_F)`$ and the dictionary
- [base/022 — Haar measure](../base/022-haar-measure.md) — invariance, unimodularity and the modulus character on the adeles
- [math/019 — Deligne–Serre weight one](019-deligne-serre-weight-one.md) — one of the consumers of the determinant norm
- [PORTING-DeligneSerre.md](../lean/topics/PORTING-DeligneSerre.md) — the frontier that reaches these nodes

Background:

- J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Ch. II–III — adeles, ideles, the product formula, the norm-one subgroup.
- J. W. S. Cassels and A. Fröhlich, *Algebraic Number Theory*, Academic Press, 1967 — the idele class group and Fujisaki's compactness theorem.
- A. Weil, *Basic Number Theory*, 3rd ed., Springer, 1974, Ch. II–IV — the modulus character and Haar measure on adeles.
- D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields*, GTM 186, Springer, 1999, Ch. 2–3 — the restricted product topology and local absolute values.
