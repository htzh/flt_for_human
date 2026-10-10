# The index of $`\Gamma_0(N)`$, and the two functions that count it

Twentieth of the `base/` notes. [018](018-congruence-subgroups-and-invariance.md)
fixed the four congruence subgroups and, in its §4.3, quoted the lifting statement
the level theory leans on; [005](005-cyclic-isogenies-and-level.md) drew the lattice
picture behind $`\Gamma_0(N)`$ and stated the Dedekind count $`\psi(N)`$;
[013](013-riemann-existence-and-the-q-expansion-principle.md) used $`\psi(N)`$ as
the degree of the cover $`X_0(N) \to X(1)`$. This note is the *proof* the port
carries, written as mathematics:

$$[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] = \psi(N), \qquad
  \\#\\,\mathrm{primCosetReps}(N) = \psi(N),$$

the first through the coset bijection with the projective line over
$`\mathbb{Z}/N`$, the second through an independent count of explicit
representatives that never mentions the group at all.

It is also the right place to put Euler's $`\varphi`$ beside Dedekind's $`\psi`$,
because the index proof is exactly where they meet: mathlib has a finished totient
API and **no** $`\psi`$ anywhere, while the port's $`\psi`$ is proved from
$`\varphi`$ — on each prime power in §6.1, and as a count of reduced residues in
§8.2. §9 tabulates what is mathlib's and what is ours.

**Citations and how to read the Lean here.** Line numbers for the pin point at
`anthropics/fermats-last-theorem@aa2d8b3`; mathlib is cited at tag **v4.34.0**
(rev `5ed2965256`), the version this port builds against — one minor version on
from the pin's `v4.33.1` toolchain (whose mathlib is the `master-2026-08-10`
snapshot), so that the anchors match the copies the checked code was elaborated
against. (The anchors into `GroupTheory/Index.lean` and
`Data/Nat/Factorization/Induction.lean` sit at identical lines in both versions;
`Data/Nat/Totient.lean` shifted by a line or two, `Data/ZMod/Basic.lean` by four.)
Citations to the port's own Lean are **pinned to `htzh/flt_for_human@250e7c0`**,
the commit at which the statements and line numbers were read: unlike the pin, the
port is a working tree. Lean appears below only as *grounding* — the mathematics
is written in notation, and each section closes with the declarations that carry
it, followed by the declaration map of §10.

The plan:

1. the statement, the two arithmetic functions, and the closed form of the answer;
2. the shape of the argument: five moves, of which two are arithmetic;
3. step 1 — $`\Gamma_0(N)`$ is the preimage of the Borel subgroup;
4. step 2 — reduction is surjective, and lifting is Bezout arithmetic;
5. step 3 — the coset bijection
   $`\mathrm{SL}_2(R) \big/ B(R) \cong \mathbb{P}^1(R)`$;
6. step 4 — counting the projective line: the local case, the Chinese remainder,
   and the induction;
7. step 5 — assembling the headline;
8. the second, independent count: primitive coset representatives;
9. what mathlib supplies, and what has no counterpart there;
10. key point $`\to`$ declaration map;
11. links.

## 1. The statement, and the answer in closed form

Let

$$\Gamma_0(N) = \left\\{\begin{pmatrix} a & b \\\\ c & d\end{pmatrix} \in
  \mathrm{SL}_2(\mathbb{Z}) : c \equiv 0 \pmod N\right\\}$$

be the level-$`N`$ congruence subgroup — the stabiliser of a cyclic subgroup of
order $`N`$, as [018 §1.3](018-congruence-subgroups-and-invariance.md) computes —
and let $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)]`$ denote its index, the number of
cosets. Write

$$B(R) = \left\\{ M \in \mathrm{SL}_2(R) : M_{10} = 0 \right\\}$$

for the upper-triangular **Borel subgroup**. The two functions that count the cosets
are

$$\psi(N) = \sum_{d \mid N,\ d\ \text{squarefree}} \frac{N}{d}
  = N \prod_{p \mid N} \left(1 + \frac{1}{p}\right),$$

$$\varphi(N) = \\#\\{a \lt N : \gcd(a,N) = 1\\} = \\#(\mathbb{Z}/N)^{\times}
  = N \prod_{p \mid N} \left(1 - \frac{1}{p}\right).$$

On a prime power they are complementary,

$$\psi(p^k) = p^k + p^{k-1}, \qquad \varphi(p^k) = p^k - p^{k-1},
  \qquad \psi(p^k) + \varphi(p^k) = 2p^k,$$

with $`\psi(p) = p + 1`$, $`\varphi(p) = p - 1`$ and
$`\psi(1) = \varphi(1) = 1`$. This is the arithmetic shadow of the group theory:
$`\varphi(N)`$ is the index of $`\Gamma_1(N)`$ in $`\Gamma_0(N)`$ (the diamond
quotient $`\Gamma_0(N)/\Gamma_1(N) \cong (\mathbb{Z}/N)^{\times}`$), while
$`\psi(N)`$ is the index of $`\Gamma_0(N)`$ in the full group, so the two multiply
up the tower $`\Gamma(N) \subseteq \Gamma_1(N) \subseteq \Gamma_0(N) \subseteq
\mathrm{SL}_2(\mathbb{Z})`$.

**The two headlines.** The port proves

$$[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] = \psi(N) \quad (N \neq 0),
  \qquad \\#\\,\mathrm{primCosetReps}(N) = \psi(N) \quad (N \neq 0),$$

where

$$\mathrm{primCosetReps}(N) = \\{(a,b,d) : ad = N,\ 0 \le b \lt d,\ \gcd(a, \gcd(b,d)) = 1\\}$$

is the set of upper-triangular coset representatives of §8.1. The side condition
$`N \neq 0`$ is not decoration: the prime-power count of §6.1 needs a genuine
$`k \neq 0`$, the Chinese-remainder step needs nonzero factors, and the induction of
§6.3 splits off $`N = 0`$ explicitly. The pin states the same two theorems with the
same side conditions. At $`N = 2`$ both give $`3`$ — $`\psi(2) = 3`$, and there are
three lines in $`(\mathbb{Z}/2)^2`$.

*Grounding.* The two statements are verbatim Lean in the port
([`Gamma0Index.lean` L522 and L725](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L522)):

```lean
theorem Gamma0_index (N : ℕ) [NeZero N] : (CongruenceSubgroup.Gamma0 N).index = dedekindPsi N

theorem card_primCosetReps_eq_dedekindPsi (N : ℕ) (hN : N ≠ 0) :
    (primCosetReps N).card = dedekindPsi N
```

$`\psi`$ is [`NumberTheory/DedekindPsi.lean` L54](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L54)
with the prime-power and multiplicativity lemmas beside it
([L69](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L69),
[L139](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L139));
$`\varphi`$ is mathlib's `Nat.totient`
([Totient.lean, line 39, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/Nat/Totient.lean#L39)),
and $`\#(\mathbb{Z}/N)^{\times} = \varphi(N)`$ is
[`ZMod.card_units_eq_totient`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/Nat/Totient.lean#L113).
The index itself is `Subgroup.index`, which is by definition a cardinality
([Index.lean, line 348, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/GroupTheory/Index.lean#L348)).

**Why $`\psi`$ is the expected answer.** A coset of $`\Gamma_0(N)`$ should be a
*line* in $`(\mathbb{Z}/N)^2`$ (§5), and the lines can be counted before any of the
formal work: a unit acts freely on unimodular pairs (if $`ua = a`$, $`uc = c`$ and
$`xa + yc = 1`$ then $`u = 1`$), so

$$\\#\mathbb{P}^1(\mathbb{Z}/N) = \frac{\\#\\{\text{unimodular pairs}\\}}{\varphi(N)}
  = \frac{N^2 \prod_{p \mid N} (1 - p^{-2})}{N \prod_{p \mid N} (1 - p^{-1})}
  = N \prod_{p \mid N} \left(1 + \frac{1}{p}\right) = \psi(N).$$

The Lean proof does not take this route — it counts $`\mathbb{P}^1(\mathbb{Z}/p^k)`$
locally and multiplies by the Chinese remainder theorem (§6), getting $`\psi`$ from
$`\varphi`$ at each prime power. The display above is the one-line human summary of
the answer, not a formalized step.

## 2. The shape of the argument

Five moves, and only two of them are arithmetic:

```text
(1)  Γ₀(N) = B(ℤ/N) pulled back along reduction         Gamma0_eq_comap_borel
(2)  reduction is surjective                             sl2_surj
     ⟹ the cosets of Γ₀(N) are the cosets of B(ℤ/N)      index_comap_of_surjective
(3)  SL₂(R) / B(R) ≅ ℙ¹(R), by the first column          card_quotient_borel
(4)  #ℙ¹(ℤ/N) = ψ(N)                                     card_projectiveLine_zmod
(5)  index = cardinality of the coset space              index_eq_card
```

Move (3) is a statement about an arbitrary commutative ring and contains no
arithmetic; it is the *definition* of the coset space in coordinates. Move (4) is
where all the number theory is. Move (2) is where a reader expects arithmetic too,
and it is there — but its content is a lifting statement about matrices, not a count.
Moves (1) and (5) are bookkeeping: mathlib's $`\Gamma_0`$ is defined intrinsically, so
it must be *identified* with a preimage before the index lemma applies, and the
index must be identified with a cardinality.

## 3. Step 1: $`\Gamma_0(N)`$ is the preimage of the Borel subgroup

Let $`\pi : \mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/N)`$ be reduction
of entries modulo $`N`$. Then

$$\Gamma_0(N) = \pi^{-1}\bigl(B(\mathbb{Z}/N)\bigr),$$

because both sides say that the lower-left entry vanishes modulo $`N`$: the left by
definition, the right by the definition of $`B`$. The content of the statement is
that mathlib defines $`\Gamma_0`$ by a congruence on one matrix entry, whereas the
index machinery wants a preimage — and the preimage description is what composes
with the lemma of the next section.

*Grounding.*
[`Gamma0_eq_comap_borel`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L261)
(the pin keeps this helper `private` too);
$`B`$ is
[`borel`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean#L97)
with
[`mem_borel_iff`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean#L116),
and mathlib's group is `CongruenceSubgroup.Gamma0`.

## 4. Step 2: reduction is surjective, and lifting is Bezout arithmetic

### 4.1 The statement to prove

Reduction $`\pi`$ is **surjective**: every $`M \in \mathrm{SL}_2(\mathbb{Z}/N)`$ with
$`\det M = 1`$ in $`\mathbb{Z}/N`$ is the reduction of a matrix of determinant $`1`$
over $`\mathbb{Z}`$. Since $`\Gamma_0(N) = \pi^{-1}(B)`$ by §3, the map

$$A\\,\Gamma_0(N) \longmapsto \pi(A)\\,B(\mathbb{Z}/N)$$

is a bijection between the left-coset spaces — injective because
$`\pi(A)^{-1}\pi(A') \in B`$ forces $`A^{-1}A' \in \pi^{-1}(B) = \Gamma_0(N)`$, and
surjective because $`\pi`$ is — so the two indices are equal. In mathlib this is the
specialisation to a surjection of the general fact that a preimage has the same
index as its target ([Index.lean, lines 68–69, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/GroupTheory/Index.lean#L68-L69)).

The mathematics behind surjectivity is the standard approximation fact for
$`\mathrm{SL}_2`$, and the pin proves it by Bezout arithmetic. The pin's own prose
for this step is [018 §4.3](018-congruence-subgroups-and-invariance.md); what follows
is the construction those two declarations perform, in notation.

### 4.2 The naive lift does not work

It is tempting to lift the four entries independently: pick
$`a_0, b_0, c_0, d_0 \in \mathbb{Z}`$ reducing to $`a, b, c, d`$ and declare victory.
That does not give a matrix in $`\mathrm{SL}_2(\mathbb{Z})`$: the determinant condition
is only $`a_0 d_0 - b_0 c_0 \equiv 1 \pmod N`$, i.e.

$$N \mid a_0 d_0 - b_0 c_0 - 1,$$

whereas the integral matrix needs determinant *exactly* $`1`$. So the entries must
be *chosen*, not lifted.

### 4.3 Fix the second row: a coprime pair congruent to $`(c_0, d_0)`$

First observation: no prime divides $`c_0`$, $`d_0`$ and $`N`$ at once. For if
$`p \mid c_0`$, $`p \mid d_0`$ and $`p \mid N`$, then $`p`$ divides both
$`a_0 d_0 - b_0 c_0`$ and $`a_0 d_0 - b_0 c_0 - 1`$, hence $`p \mid 1`$, absurd.

Second, replace the second row by a **coprime** pair with the same residues.
With

$$\gamma = \begin{cases} c_0, & c_0 \neq 0, \\\\ N, & c_0 = 0,\end{cases}
  \qquad \delta = d_0 + \mathrm{primeSel}(\gamma, d_0) \cdot N, \qquad
  \mathrm{primeSel}(c,d) = \prod_{p \mid c,\ p \nmid d} p,$$

we have $`\gamma \equiv c_0`$ and $`\delta \equiv d_0 \pmod N`$, and
$`\gcd(\gamma, \delta) = 1`$. For a common prime $`p`$ either divides $`d_0`$ or not:
if $`p \mid d_0`$ then $`p \nmid \mathrm{primeSel}(\gamma, d_0)`$ (every prime of
$`\gamma`$ dividing $`d_0`$ contributes the factor $`1`$), so $`p \mid \delta`$ and
$`p \mid d_0`$ force $`p \mid N`$, against the first observation; if
$`p \nmid d_0`$ then $`p \mid \mathrm{primeSel}(\gamma, d_0)`$, and $`p \mid \delta`$
forces $`p \mid d_0`$, a contradiction. Either way no common prime exists.

### 4.4 Bezout, then slide the first row

A coprime second row makes the first one free. Bezout's identity
$`\mathrm{gcdA}(\gamma,\delta)\,\gamma + \mathrm{gcdB}(\gamma,\delta)\,\delta =
\gcd(\gamma,\delta) = 1`$ exhibits

$$\alpha_0 = \mathrm{gcdB}(\gamma,\delta), \qquad
  \beta_0 = -\mathrm{gcdA}(\gamma,\delta), \qquad
  \alpha_0 \delta - \beta_0 \gamma = 1,$$

so $`[[\alpha_0,\beta_0],[\gamma,\delta]] \in \mathrm{SL}_2(\mathbb{Z})`$ already.
Only its residues are wrong: $`\gamma \equiv c`$ and $`\delta \equiv d`$ by
construction, but $`(\alpha_0,\beta_0)`$ is some Bezout solution, not the target
$`(a,b)`$ — and the two pairs satisfy the same determinant relation modulo $`N`$.
The mismatch is therefore measured by

$$\lambda := b\\,\alpha_0 - a\\,\beta_0 \in \mathbb{Z}/N,$$

and sliding the first row along the second by any integer lift of $`\lambda`$,

$$(\alpha, \beta) := (\alpha_0, \beta_0) + \lambda\\,(\gamma, \delta),$$

leaves the determinant alone — the change is $`\lambda(\gamma\delta - \delta\gamma)
= 0`$ whatever the lift, so
$`(\alpha_0 + \lambda\gamma)\delta - (\beta_0 + \lambda\delta)\gamma =
\alpha_0\delta - \beta_0\gamma = 1`$ — and lands on the
target: the congruences $`\gamma \equiv c`$ and $`\delta \equiv d`$ turn
$`\lambda = b\alpha_0 - a\beta_0`$ and $`ad - bc = 1`$, i.e. $`1 + bc = ad`$, into

$$\alpha_0 + (b\alpha_0 - a\beta_0)c = \alpha_0(1 + bc) - a\beta_0c
  = \alpha_0\\,ad - a\beta_0c = a(\alpha_0 d - \beta_0 c) = a
  \qquad \text{in } \mathbb{Z}/N;$$

$`\alpha_0 d - \beta_0 c = 1`$ by reducing $`\alpha_0\delta - \beta_0\gamma = 1`$.
The computation for $`\beta`$ is the same
with the roles of $`(a,\alpha_0)`$ and $`(b,\beta_0)`$ swapped. Hence
$`[[\alpha,\beta],[\gamma,\delta]] \in \mathrm{SL}_2(\mathbb{Z})`$ reduces to
$`M`$, and $`\pi`$ is surjective.

*Grounding.* The construction is `exists_sl2_int_lift`
([L132](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L132)),
whose input is the determinant equation and whose output is the four integers; the
coprime lift is
[`exists_coprime_lift`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L90)
with
[`primeSel`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L68),
and the surjectivity statement is
[`sl2_surj`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L179).
The two `linear_combination` certificates that close §4.4 are
$`-(\alpha_0)\cdot h + a \cdot h_{\det}`$ and
$`-(\beta_0)\cdot h + b \cdot h_{\det}`$ at
[L170–175](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L170-L175).

## 5. Step 3: the coset bijection with the projective line

Now the group theory, over an arbitrary commutative ring $`R`$ — because
$`\mathbb{Z}/N`$ is one. A pair $`(a,c) \in R^2`$ is **unimodular** if it
generates the unit ideal,

$$\mathrm{unimodular}(a,c) :\iff \exists x, y \in R,\ xa + yc = 1,$$

and the **projective line** is

$$\mathbb{P}^1(R) = \\{\text{unimodular pairs}\\} \big/ R^{\times},$$

pairs modulo scaling by a unit — a homogeneous pair, not literally a row of any
matrix. Mathlib has the projective line only over a division
ring, and no Borel subgroup at all, so both are port vocabulary.

The bijection is by the first column. A matrix in $`\mathrm{SL}_2(R)`$ has a
unimodular first column $`(A_{00}, A_{10})`$, since $`\det A = 1`$ reads off
$`A_{11}A_{00} + (-A_{01})A_{10} = 1`$. Write $`[A] \in \mathbb{P}^1(R)`$ for the
line of that **pair, read as a column** (entries $`0`$ then $`1`$). The substance
is the equivalence

$$[A] = [B] \iff A^{-1}B \in B(R),$$

which is proved in two directions:

* if the first columns of $`A`$ and $`B`$ differ by a unit $`u`$, then the
  $`(1,0)`$-entry of $`A^{-1}B`$ is $`(-A_{10})(uA_{00}) + A_{00}(uA_{10}) = 0`$ —
  the two terms cancel;
* if $`C = A^{-1}B`$ is upper triangular of determinant $`1`$, then
  $`C_{00}C_{11} = 1`$, so $`C_{00}`$ is a unit, and $`B = AC`$ has first column
  $`C_{00}`$ times that of $`A`$ — the off-diagonal entry of $`C`$ contributes
  nothing to the first column of the product.

Surjectivity is the completing trick: a unimodular pair $`(a,c)`$ with
$`xa + yc = 1`$ is the first column of

$$\begin{pmatrix} a & -y \\\\ c & x \end{pmatrix}, \qquad
  \det = ax - (-y)c = ax + cy = 1,$$

whose rows are $`(a, -y)`$ and $`(c, x)`$. So the first-column map is a bijection,
and

$$\\#\bigl(\mathrm{SL}_2(R) \big/ B(R)\bigr) = \\#\mathbb{P}^1(R)$$

for every commutative ring $`R`$. Read with §4, this is the classical coset
bijection: because $`\Gamma_0(N) = \pi^{-1}(B)`$ and $`\pi`$ is onto, the cosets of
$`\Gamma_0(N)`$ correspond to the cosets of $`B(\mathbb{Z}/N)`$, which correspond to
the lines in $`(\mathbb{Z}/N)^2`$. The port proves the two cardinality equalities
separately and never exhibits the composed bijection.

*Grounding.*
[`IsUnimodularRow`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean#L37),
[`ProjectiveLine`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean#L66),
the equivalence as
[`firstColumnClass_eq_iff`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L208),
and the cardinality statement as
[`card_quotient_borel`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L236).
The two explicit matrix computations use mathlib's `Matrix.two_mul_expl` and
`SpecialLinearGroup.SL2_inv_expl`.

## 6. Step 4: counting the projective line

### 6.1 The local case: $`\mathbb{Z}/p^k`$ is a local ring

Let $`p`$ be prime and $`k \neq 0`$. Then $`\mathbb{Z}/p^k`$ is a local ring with
maximal ideal $`(p)`$, and two facts do all the work:

1. $`z \in \mathbb{Z}/p^k`$ is a unit if and only if its reduction modulo $`p`$ is
   nonzero — a unit maps to a unit, and $`0`$ is not one in the field
   $`\mathbb{Z}/p`$; conversely a non-unit is divisible by $`p`$;
2. hence a **unimodular pair has a unit entry**: if both entries reduced to $`0`$,
   then so would $`1 = xa + yc`$.

It follows that every line has exactly one representative of the form $`[1 : t]`$
(when the first entry is a unit) or $`[m : 1]`$ with $`m`$ a **non**-unit (when only
the second is), giving a bijection

$$\mathbb{Z}/p^k \\;\sqcup\\; \\{z : \mathbb{Z}/p^k \mid z \text{ not a unit}\\}
  \\;\xrightarrow{\ \sim\ }\\; \mathbb{P}^1(\mathbb{Z}/p^k).$$

The two sides are counted by the two functions of §1: the units number
$`\varphi(p^k) = p^{k-1}(p-1)`$, the non-units number $`p^{k-1}`$ because
$`\#\mathbb{Z}/p^k = p^k`$ and $`\varphi(p^k) + p^{k-1} = p^k`$. Hence

$$\\#\mathbb{P}^1(\mathbb{Z}/p^k) = \varphi(p^k) + p^{k-1} = p^k + p^{k-1}
  = \psi(p^k).$$

This is the one place where $`\psi`$ and $`\varphi`$ genuinely meet: both count
residues of $`\mathbb{Z}/p^k`$ — the units and the non-units — and their sum is twice
the ring.

### 6.2 Multiplicativity across coprime factors

For coprime $`M`$ and $`N`$ the Chinese remainder theorem is a ring equivalence
$`\mathbb{Z}/MN \cong \mathbb{Z}/M \times \mathbb{Z}/N`$
([Data/ZMod/Basic.lean, line 889, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/ZMod/Basic.lean#L889)),
and pushing a pair through the two projections sends lines to pairs of lines. The
induced map is bijective — injective by lifting representatives and gluing the two
units through the ring equivalence, surjective by gluing one pair from each factor,
whose unimodularity is componentwise — so

$$\\#\mathbb{P}^1(\mathbb{Z}/MN) = \\#\mathbb{P}^1(\mathbb{Z}/M) \cdot
  \\#\mathbb{P}^1(\mathbb{Z}/N) \qquad (\gcd(M,N) = 1).$$

### 6.3 The induction, and the headline of this section

Assembling the local computations along the factorization of $`N`$ is an induction
on the prime-power decomposition. Mathlib supplies exactly one tool for that shape
([Factorization/Induction.lean, lines 49–53, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/Nat/Factorization/Induction.lean#L49-L53)),
whose four cases here are:

* a prime power $`N = p^n`$: §6.1, with $`\psi(p^n) = p^n + p^{n-1}`$;
* $`N = 0`$: excluded by the hypothesis $`N \neq 0`$;
* $`N = 1`$: $`\mathbb{Z}/1`$ is the zero ring, every pair is the same line, and
  $`\#\mathbb{P}^1 = 1 = \psi(1)`$;
* a coprime product $`N = ab`$: §6.2 for the left-hand side and multiplicativity
  $`\psi(ab) = \psi(a)\psi(b)`$ for the right.

Therefore

$$\\#\mathbb{P}^1(\mathbb{Z}/N) = \prod_{p^k \parallel N} (p^k + p^{k-1})
  = N \prod_{p \mid N} \left(1 + \frac{1}{p}\right) = \psi(N) \qquad (N \neq 0).$$

*Grounding.*
[`card_projectiveLine_zmod`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L498)
is the assembled statement; its local input is
[`card_projectiveLine_prime_pow`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L347),
built from the unit criterion
([`isUnit_zmod_prime_pow_iff`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L274),
[`isUnit_or_isUnit`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L298)) and the non-unit count
([`card_not_isUnit_zmod_prime_pow`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L323),
from `ZMod.card_units_eq_totient` and `Nat.totient_prime_pow_succ`); the CRT step is
[`card_projectiveLine_mul`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L422).
The three $`\psi`$ facts the induction consumes —
$`\psi(1) = 1`$, $`\psi(p^k) = p^k + p^{k-1}`$,
$`\psi(ab) = \psi(a)\psi(b)`$ for coprime $`a,b`$ — are the ported module's
([`dedekindPsi_one`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L57),
[`dedekindPsi_prime_pow`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L69),
[`dedekindPsi_mul_of_coprime`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L139)),
imported and not re-proved here.

## 7. Step 5: the headline, assembled

The five moves compose into one chain of four equalities:

```text
[SL₂(ℤ) : Γ₀(N)]
  = [SL₂(ℤ) : B(ℤ/N)]              step 1 + step 2 (cosets correspond)
  = #(SL₂(ℤ/N) / B(ℤ/N))           index is the cardinality of the coset space
  = #ℙ¹(ℤ/N)                       step 3 (first-column bijection)
  = ψ(N)                           step 4 (local count + CRT)
```

Note what is *not* in the chain: no coset representative is exhibited, no Euclidean
algorithm appears, and no group acts on anything. The index theorem is a lifting
statement composed with a cardinality computation over a quotient.

*Grounding.*
[`Gamma0_index`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L522)
is the four rewrites; the middle equalities are mathlib's
[`index_eq_card`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/GroupTheory/Index.lean#L348)
and the port's `card_quotient_borel` and `card_projectiveLine_zmod` from §5–§6.

## 8. The second, independent count: primitive coset representatives

### 8.1 The set, and why its cardinality is the same number

The index set the $`q`$-expansion layer actually enumerates is not the projective
line but a set of upper-triangular matrices. Coset representatives of
$`\Gamma_0(N)`$ can be taken of the form

$$\begin{pmatrix} a & b \\\\ 0 & d\end{pmatrix}, \qquad ad = N, \qquad
  0 \le b \lt d, \qquad \gcd\bigl(a, \gcd(b,d)\bigr) = 1,$$

and the port records the index set as the triples in §1. Its cardinality is the
subject of this section, and the argument shares nothing with §§3–7: it never
mentions $`\mathrm{SL}_2`$, the Borel subgroup, or lifting. That is exactly why it is
worth having — two proofs of one number.

### 8.2 The fibre count is a totient count

Reindex the triples by their first and third entries: the set is the disjoint union,
over pairs $`(a,d)`$ with $`ad = N`$, of the $`b \lt d`$ coprime to $`\gcd(a,d)`$. Hence

$$\\#\mathrm{primCosetReps}(N)
  = \sum_{(a,d) \in \mathrm{divisorsAntidiagonal}(N)}
    \\#\\{b \lt d : \gcd(\gcd(a,d), b) = 1\\}.$$

Each inner count is a totient times a number of periods. Writing
$`g = \gcd(a,d)`$, the residues coprime to $`g`$ are $`g`$-periodic, so a block of
$`m`$ periods contains exactly $`m\varphi(g)`$ of them:

$$\\#\\{b \lt gm : \gcd(g,b) = 1\\} = m\\,\varphi(g), \qquad\text{and}\qquad
  \\#\\{b \lt d : \gcd(g,b) = 1\\} = \frac{d}{g}\\,\varphi(g).$$

The fibre value $`h(a,d) = \frac{d}{\gcd(a,d)}\,\varphi(\gcd(a,d))`$ is therefore the
$`\varphi`$-count that the $`\psi`$-count is built from.

### 8.3 Turning the sum into an arithmetic function

Define

$$G(n) := \sum_{(a,d) \in \mathrm{divisorsAntidiagonal}(n)} h(a,d),
  \qquad h = \text{the fibre value above}.$$

Then:

* $`G`$ is **multiplicative**, because the divisors-antidiagonal sum of a
  multiplicative two-variable function multiplies over coprime factorizations, and
  $`h`$ is multiplicative in the pair:
  $`h(a_1a_2, d_1d_2) = h(a_1,d_1)h(a_2,d_2)`$ for coprime products, by
  multiplicativity of $`\gcd`$ and of $`\varphi`$;
* on a prime power, $`h(p^{k-j}, p^j) = \varphi(p^j)`$ for $`1 \le j \le k-1`$ — both
  cases of the minimum collapse, by the definition of $`h`$ — while the two end terms
  contribute $`1`$ and $`p^k`$; summing the telescoping identity
  $`h(p^{k-j},p^j) + p^{j-1} = p^j`$ gives

$$G(p^k) = 1 + p^k + \sum_{j=1}^{k-1} \varphi(p^j)
  = 1 + p^k + (p^{k-1} - 1) = p^k + p^{k-1}.$$

Two multiplicative arithmetic functions that agree on prime powers are equal, so
$`G = \Psi`$, where $`\Psi`$ is the convolution presentation of $`\psi`$,

$$\Psi = \mu^2 \ast \mathrm{id}, \qquad \Psi(n) = \psi(n),$$

$`\mu^2`$ being the indicator of the squarefree numbers. Therefore
$`G(N) = \Psi(N) = \psi(N)`$, which is the second headline.

Note the shape of the reuse: $`\psi`$ is presented in the port **twice** — as the
divisor sum of §1 and as the convolution $`\Psi = \mu^2 * \mathrm{id}`$ — and this
proof is what makes the second presentation pay. The pin kept $`\Psi`$ and the
squarefree indicator `private` in two different files; the port promotes them once
([`NumberTheory/DedekindPsi.lean`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L119),
the move recorded in [level-port.md §7](../lean/logs/level-port.md)), and the pin's
`ModularCurve`-namespaced spelling survives as a one-line delegation module
([`ModularCurve/Defs/DedekindPsi.lean`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Defs/DedekindPsi.lean#L28)).

*Grounding.* The set is
[`primCosetReps`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Defs/PrimCosetReps.lean#L31);
the reindexing is
[`card_primCosetReps_eq_sum`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L537);
the fibre value is
[`dedekindPsiFibre`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L217)
with
[`card_fibre`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L221),
resting on the block count
[`card_filter_coprime_range_mul`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L201).
Multiplicativity is `sum_divisorsAntidiagonal_mul_of_coprime`, `h_mul` and
`isMultiplicative_G` ([L561](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L561),
[L619](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L619),
[L649](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L649));
the prime-power value is `h_prime_pow` and `G_prime_pow`
([L657](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L657),
[L702](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L702));
and the conclusion is `G_eq_Psi` with `Psi_apply`
([L713](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L713),
[L130](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L130)).

## 9. What mathlib supplies, and what has no counterpart there

**$`\varphi`$**: mathlib has the full theory of Euler's totient. In notation, with
the declaration names beside the statements:

* $`\varphi(n) = \#\{a \lt n : \gcd(a,n) = 1\}`$ and $`\gcd`$-multiplicativity,
  $`\varphi(mn) = \varphi(m)\varphi(n)`$ (`Nat.totient` line 39, `totient_mul`
  line 133);
* the divisor sum $`\sum_{d \mid n} \varphi(d) = n`$ (`sum_totient` line 165);
* the prime and prime-power values $`\varphi(p) = p-1`$ (line 216) and
  $`\varphi(p^k) = p^{k-1}(p-1)`$ (line 182);
* the bounds $`\varphi(n) \le n`$ and $`\varphi(n) \gt 0`$ for $`n \gt 0`$
  (lines 62, 75);
* the group-theoretic reading $`\#(\mathbb{Z}/n)^{\times} = \varphi(n)`$
  (`ZMod.card_units_eq_totient`, line 113);
* the Euler product $`\varphi(n) = n\prod_{p\mid n}(1 - 1/p)`$ over $`\mathbb{Q}`$
  (`totient_eq_mul_prod_factors`, line 316);
* the gcd identity
  $`\varphi(\gcd(a,b))\,\varphi(ab) = \varphi(a)\,\varphi(b)\,\gcd(a,b)`$ with
  super-multiplicativity $`\varphi(a)\varphi(b) \le \varphi(ab)`$ and
  $`a \mid b \Rightarrow \varphi(a) \mid \varphi(b)`$ (lines 331, 349, 358);
* the block count $`\#\{x \in [n, n+a) : \gcd(a,x) = 1\} = \varphi(a)`$ (line 80).

All line numbers are in [Totient.lean at v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/Nat/Totient.lean).

**$`\psi`$**: mathlib has nothing. A search for `dedekindPsi` (and for
`dedekind_psi`) over the whole of `Mathlib/` at v4.34.0 returns no declaration; the
`Dedekind` hits are cuts, domains and zeta, and every `Jordan` hit is Jordan–Hölder
or Jordan's inequality. The port's $`\psi`$ module therefore holds the definition,
the multiplicativity, the prime step in three shapes, positivity, the totient-based
block count, and the fibre value.

Three further gaps are worth naming, because they are why the port writes the
vocabulary itself:

* **no Borel subgroup** of $`\mathrm{SL}_2(R)`$ — the port's `borel`;
* **no projective line over a general commutative ring** — mathlib's `OnePoint`
  needs a division ring, and $`\mathbb{Z}/N`$ is full of zero divisors precisely when
  $`N`$ is composite, which is the interesting case here;
* **no index formula for $`\Gamma_0(N)`$**, and no $`\psi`$ to state it with.

Two honest caveats.

1. Mathlib's block count is stated at an *arbitrary* offset,
   $`\#\{x \in [n, n+a) : \gcd(a,x) = 1\} = \varphi(a)`$, while the port's
   `card_filter_coprime_range_mul` counts $`m`$ periods starting at $`0`$. The former
   looks strictly stronger, so the latter may be a short induction away from it — but
   that has **not been machine-checked** here, and no replacement is claimed; the
   port's proof uses `Nat.periodic_coprime` directly.
2. The port's totient-adjacent facts are the two the index proof needs. The pin's
   other $`\psi`$ facts are public there and unported here: the lower bound
   $`N \le \psi(N)`$ (`ModularCurve.le_dedekindPsi`, whose argument the port inlines
   inside `dedekindPsi_pos` without exporting the lemma), the product form of §1
   (`ModularCurve.dedekindPsi_eq_prod_primeFactors` and `dedekindPsi_of_squarefree` —
   stated in the ported module's docstring but not as a theorem), and
   `ModularCurve.card_quotient_gamma0_le_dedekindPsi`. None of them is needed by
   §§3–8.

## 10. Key point $`\to`$ declaration map

Port declarations are linked into the pinned tree `htzh/flt_for_human@250e7c0`;
pin sources are pinned to `aa2d8b3`.

| mathematics | port declaration | pin source |
|---|---|---|
| $`\Gamma_0(N)`$, $`[\mathrm{SL}_2 : \Gamma_0]`$ | mathlib `CongruenceSubgroup.Gamma0`, `Subgroup.index` | — |
| $`B(R)`$ upper triangular | [`borel`, `mem_borel_iff`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean#L97) | [Def_ModularCurve_ProjectiveLine.lean, lines 69, 88](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ProjectiveLine.lean#L69-L88) |
| unimodular pairs, $`\mathbb{P}^1(R)`$ | [`IsUnimodularRow`, `ProjectiveLine`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean#L37) | [same, lines 14–59](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ProjectiveLine.lean#L14-L59) |
| step 1: $`\Gamma_0(N) = \pi^{-1}(B)`$ | [`Gamma0_eq_comap_borel`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L261) | [S_ModularCurve_Gamma0_index.lean, lines 216–217](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L216-L217) |
| step 2: $`\pi`$ is onto | [`sl2_surj`, `exists_sl2_int_lift`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L179) | [same, lines 88–91, 137–138](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L137-L138) |
| step 2, the coprime second row | [`exists_coprime_lift`, `primeSel`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L90) | [same, lines 24–86](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L24-L86) |
| step 3: cosets are first columns | [`firstColumnClass_eq_iff`, `card_quotient_borel`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L208) | [same, lines 160–214](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L160-L214) |
| step 3: index $`=`$ cardinality of the quotient | mathlib `Subgroup.index_eq_card` | — |
| step 4, local: a pair has a unit | [`isUnit_zmod_prime_pow_iff`, `isUnit_or_isUnit`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L274) | [S_ModularCurve_card_projectiveLine_zmod.lean, lines 19–62](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean#L19-L62) |
| step 4, local: $`\#\mathbb{P}^1 = p^k + p^{k-1}`$ | [`card_not_isUnit_zmod_prime_pow`, `card_projectiveLine_prime_pow`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L323) | [same, lines 71–95](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean#L71-L95) |
| step 4, global: CRT multiplicativity | [`card_projectiveLine_mul`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L422) | [same, lines 156–246](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean#L156-L246) |
| $`\#\mathbb{P}^1(\mathbb{Z}/N) = \psi(N)`$ | [`card_projectiveLine_zmod`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L498) | [same, line 248](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean#L248) |
| $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] = \psi(N)`$ | [`Gamma0_index`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L522) | [S_ModularCurve_Gamma0_index.lean, line 227](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L227) |
| $`\psi`$: divisor sum, $`p^k + p^{k-1}`$, multiplicativity | [`dedekindPsi`, `dedekindPsi_prime_pow`, `dedekindPsi_mul_of_coprime`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L54) | [Thm_ModularCurve_dedekindPsi_prime_pow.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_dedekindPsi_prime_pow.lean), [Thm_ModularCurve_dedekindPsi_mul_of_coprime.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_dedekindPsi_mul_of_coprime.lean) |
| $`\Psi = \mu^2 * \mathrm{id}`$ | [`Psi`, `Psi_apply`, `isMultiplicative_Psi`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L119) | [S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean, lines 226–248](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L226-L248) |
| the fibre value $`(d/g)\,\varphi(g)`$ | [`dedekindPsiFibre`, `card_fibre`, `card_filter_coprime_range_mul`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/NumberTheory/DedekindPsi.lean#L201) | [same, lines 16–45](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L16-L45) |
| $`G`$ is multiplicative | `sum_divisorsAntidiagonal_mul_of_coprime`, `h_mul`, `isMultiplicative_G` ([L561](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L561), [L619](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L619), [L649](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L649)) | [same, lines 74–168](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L74-L168) |
| $`G(p^k) = p^k + p^{k-1}`$, $`G = \Psi`$ | `G_prime_pow`, `G_eq_Psi` ([L702](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L702), [L713](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L713)) | [same, lines 170–277](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L170-L277) |
| $`\#\mathrm{primCosetReps}(N) = \psi(N)`$ | [`card_primCosetReps_eq_dedekindPsi`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/FLTForHuman/ModularCurve/Gamma0Index.lean#L725) | [same, line 288](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L288) |

## 11. Links

* [005 — Cyclic isogenies, congruence level, and the j-invariant](005-cyclic-isogenies-and-level.md)
  — the lattice picture behind $`\Gamma_0(N)`$ and the first appearance of
  $`\psi(N)`$ in these notes.
* [013 — Riemann existence for modular curves](013-riemann-existence-and-the-q-expansion-principle.md)
  — $`\psi(N)`$ as the degree of $`X_0(N) \to X(1)`$, the use the index count is
  eventually put to.
* [018 — Congruence subgroups, level structures, and invariance](018-congruence-subgroups-and-invariance.md)
  — the four groups, §4.3 on the surjectivity of reduction and the choice of lift,
  and §5.2–5.3 on the torsion labels and the $`q`$-expansion coset representatives.
* [PORTING-Level.md](../lean/topics/PORTING-Level.md) — the SET-3 blueprint whose
  three headlines this note proves, and the module layout decision for
  `ModularCurve/`.
* [level-port.md §7](../lean/logs/level-port.md) — the record of moving the
  $`\psi`$ block out of `Defs/Jq.lean` into `NumberTheory/DedekindPsi.lean`, with
  the measured statement-checker delta.
* [LevelConsumer.lean at `250e7c0`](https://github.com/htzh/flt_for_human/blob/250e7c0/lean/spec/LevelConsumer.lean#L112)
  — the executed wire test: at $`N = 2`$ both routes give $`3`$, and the index is
  stated equal to the cardinality of the projective line.
* [S_ModularCurve_Gamma0_index.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean),
  [S_ModularCurve_card_projectiveLine_zmod.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean),
  [S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean)
  — the three pinned solution files the port transcribes.
