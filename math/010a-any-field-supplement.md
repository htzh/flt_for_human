# Supplement: the local arguments over an arbitrary field

*Supplement to [010](010-function-field-generation.md), §3–§4. Written 2026-11-08.*

The note's §3 (the roots of the modular equation) and §4 (descent by one prime) are
stated over $`\mathbb{Q}`$ with an auxiliary cyclotomic field $`K`$. The arguments
themselves are field-theoretic and characteristic-free; the only thing special to
$`\mathbb{Q}`$ is the bookkeeping of *where the primitive root of unity lives*. This
supplement separates the two. It states the local theorems over an arbitrary field
$`\kappa`$ that already contains the required root, shows that the $`\mathbb{Q}`$
statements are recovered by a base-change dictionary, and records the asymmetry that
decides which side of the two-polynomial argument carries the base change.

Everything here is mathematics; the dictionary's only new lemma is (5.4). The global
strong induction of the note's §7 is not touched — it is an induction over a base
field, and the any-field theorems enter it as its one-prime steps.

The shape of the argument is this. The note's §3–§4 use two different kinds of input:
*intrinsic* data (the modular relation, the splitting of the modular polynomial, the
unique-common-root principle) and *relative* data (the minimal polynomial over
$`\kappa(j(q))`$, its slot description, the degree and adjoin data). Only the relative
data is touched by the presence of an auxiliary field. So the local theorems can be
stated over the field where the roots live (§2), the intrinsic part of the descent can
be argued there without any base change (§3), and the relative part enters as one
theorem — the slot description (2.1) — plus the conclusion (§4). The $`\mathbb{Q}`$
statements are then a base change (§5), and the dictionary is where the only
characteristic-sensitive step of the whole assembly sits — in the trace, and only for
the field extension used to house the roots (§6).

## 1. Data, and the package

Let $`\kappa`$ be a field. Everything below happens inside $`\kappa((q))`$.

- $`j(q) = q^{-1} + 744 + 196884\,q + \cdots \in \mathbb{Z}((q)) \subset \kappa((q))`$,
  the $`q`$-expansion of the modular $`j`$-function reduced modulo the characteristic.
  Write $`j(q^N)`$ for the $`N`$-fold nome substitution.
- $`\Phi_n \in \mathbb{Z}[X,Y]`$, the modular polynomial of level $`n`$, with
  $`\Phi_n(j(q), j(q^n)) = 0`$; for prime $`n`$ it is symmetric and of degree $`n+1`$
  in either variable.
- $`\psi`$, the Dedekind psi function.
- $`F_0 = \kappa(j(q))`$, a rational function field; $`F_d = F_0(j(q^d))`$, the
  level-$`d`$ field; $`\bar F_d = \kappa(\{j(q^e) : e \mid d\})`$, the *full* divisor
  field.
- The **package** $`\mathrm{Pkg}(M)`$: for every $`d \mid M`$ one has
  $`[F_d : F_0] = \psi(d)`$ (degree) and $`F_d = \bar F_d`$ (generation).
- For a unit $`u \in \kappa^\times`$ and $`e \ge 1`$ put $`J_e(u) = j(u\,q^e)`$. The
  **slots** at level $`M`$ are the values
  $`J_{a^2}(\zeta^{ab}) = j(\zeta^{ab} q^{a^2})`$, indexed by the divisors $`a \mid M`$
  and the integers $`0 \le b < M/a`$ with $`\gcd(\gcd(a,b), M/a) = 1`$.
- For $`N \ge 1`$ let $`\nu_N`$ be the nome substitution $`q \mapsto q^N`$, acting on
  series and coefficientwise on polynomials over $`F_0 \subset \kappa((q))`$.

The data $`j`$, $`\Phi_n`$ and $`\psi`$ have integral coefficients, so all of it makes
sense in every characteristic. The modular relation $`\Phi_n(j(q), j(q^n)) = 0`$ is an
identity in $`\mathbb{Z}((q))`$ and hence holds in every $`\kappa((q))`$.

## 2. The local theorems

Throughout this section $`\kappa`$ is a field containing a primitive root of unity of
the order each statement requires: a primitive $`M`$-th root for (2.1), a primitive
$`(Mp)`$-th root for (2.2) and (2.3). The root is written $`\zeta`$ where a statement
names it. The three statements below are the $`\kappa`$-forms of the note's §3 and §4;
their proofs are the proofs of the note with the coefficient extension erased, and use
only the data of §1.

**(2.1) Slot description.** Let $`\zeta \in \kappa`$ be a primitive $`M`$-th root of
unity and assume $`\mathrm{Pkg}(M)`$. Then

$$\nu_M\bigl(\mathrm{minpoly}_{F_0}(j(q^M))\bigr)
  \\;=\\; \prod_{a \mid M}\\,\prod_{\substack{0 \le b < M/a \\\\ \gcd(\gcd(a,b),M/a)=1}}
  \bigl(Y - j(\zeta^{ab} q^{a^2})\bigr).$$

**(2.2) Prime non-membership.** Let $`p`$ be prime with $`p \nmid M`$, assume
$`\mathrm{Pkg}(M)`$ and $`j(q^p) \notin F_0`$. Then $`j(q^p) \notin F_M`$.

**(2.3) Descent by one prime.** Let $`p`$ be prime and assume $`\mathrm{Pkg}(M)`$. Then
$`j(q^M) \in F_{Mp}`$.

The root is a device of the proofs, and the three statements spend it differently.
(2.1) names it: the slots are the values $`j(\zeta^{ab} q^{a^2})`$, so the statement is
meaningless without it. (2.2) and (2.3) do not mention it, so neither needs the root in
its statement; both proofs do, and may adjoin it. What separates them is which side of
the implication pays for the base change. In (2.2) the *conclusion* is a non-membership,
and that direction is free: a membership ascends by (5.1), so a non-membership descends
by contrapositive. Its *hypothesis*, however, is a non-membership in the base field, and
lifting it from the small field to the big one is the special case of (5.4) with
$`F = F_0`$. In (2.3) the expensive side is the conclusion, which is a membership. So
the two statements are not just negations of one another: (2.2) costs the faithfulness
on its hypothesis, (2.3) on its conclusion.

Two further remarks on why one proof serves all characteristics. First, the splitting
input of the note's §3 is a statement about $`\Phi_p`$ over a field containing a
primitive $`p`$-th root: at a seed value $`j(u^p q^{pe})`$ the polynomial $`\Phi_p\bigl(j(u^p q^{pe}), Y\bigr)`$
factors over such a field as

$$\prod_{0 \le b < p}\bigl(Y - j(u\,\zeta^b q^e)\bigr) \cdot
  \bigl(Y - j(u^{p^2} q^{p^2 e})\bigr),$$

the $`p`$ twists and the extra conjugate. This is proved by writing $`\Phi_p`$ out at
the slot: polynomial arithmetic, with no separability hypothesis and no hypothesis on
the characteristic. Second, the induction of the note's §3 and the
unique-common-root argument of its §4 use only the tower law, the package, and the
arithmetic of the indices $`a, b`$. So neither the statements nor the proofs of (2.1),
(2.2), (2.3) see the characteristic.

## 3. The sharing argument: which polynomial is enumerated

The engine of the note's §4 is the principle: *let $`F \subset L`$ be fields, let $`A \in F[Y]`$
be monic, split over $`L`$ and with distinct roots, let $`B \in F[Y]`$, and let
$`x_0 \in L`$ be the unique common root of $`A`$ and $`B`$; then $`x_0 \in F`$.* In the
descent the two polynomials are

$`A`$, the level-$`p`$ modular equation at the seed,
$`A(Y) = \Phi_p\bigl(j(q^{Mp}), Y\bigr) \in F_{Mp}[Y]`$, and $`B`$, the base change to
$`F_{Mp}`$ of $`\mathrm{minpoly}_{F_0}(j(q^M))`$; the common root is
$`x_0 = j(q^M)`$. The principle is one line: the minimal polynomial of $`x_0`$ over
$`F`$ divides both $`A`$ and $`B`$; if it had degree $`> 1`$, its other roots would be
roots of $`A`$ and hence, $`A`$ splitting with distinct roots, would give a second
common root. The principle requires exactly one of the two to be the
**enumerated** polynomial — monic, split, with distinct roots — and the other to be a
*witness*: it must vanish at $`x_0`$, and its roots must be controlled only where the
argument needs them. This choice is the whole subtlety, because the two polynomials do
not supply the enumerated data on the same terms:

**(a) $`A = \Phi_p`$ enumerated.** $`A`$ is monic of degree $`p+1`$; it splits with
distinct roots over any field containing a primitive $`p`$-th root, and its root shape
is known: the extra conjugate $`j(q^{M^2p^3})`$ and the $`p`$ twists. $`x_0`$ is a root
of $`A`$ by the modular relation (the seed): $`\Phi_p(j(q), j(q^p)) = 0`$, substituted
$`q \mapsto q^M`$ and symmetrized with $`\Phi_p(X,Y) = \Phi_p(Y,X)`$. It is a root
of $`B`$ as the element whose minimal polynomial $`B`$ is. Uniqueness then needs exactly two facts about the roots of
$`B`$: the extra conjugate is not a root, and the only root of $`B`$ among the twists
is the untwisted one. Both are consequences of (2.1) — the slot list of $`B`$ — and
nothing more.

**(b) $`B`$ enumerated.** $`B`$ is monic, and it splits with distinct roots — but only
because (2.1) identifies it with the slot product; its root at $`x_0`$ is the top slot,
again (2.1). $`\Phi_p`$ is then the witness: its root shape supplies the case split,
and each case is compared against the slot list.

Both are correct proofs of the same statement, and they differ only in what (2.1) has
to supply: in (a) two exclusion facts about two special positions; in (b) the complete
root enumeration of $`B`$, including its splitting and squarefreeness. The root
bookkeeping of $`B`$ is the only *relative* input to the sharing argument, and (2.1) is
its only source (next section). So (a) confines the relative input to two exclusions
and keeps the sharing argument itself intrinsic, while (b) moves the whole relative
input into the sharing argument.

## 4. Intrinsic and relative statements

Call a statement about $`\kappa((q))`$ **intrinsic** if it is an identity among
$`j`$-values, the coefficients of the $`\Phi_n`$ and field operations — equivalently,
if it holds in every field containing the values it names and is preserved by every
map of fields. Call it **relative to $`F_0`$** if it mentions the minimal polynomial,
the degree or the adjoin over $`F_0`$.

With this vocabulary:

- *intrinsic*: the modular relations $`\Phi_n(j(q), j(q^n)) = 0`$; the splitting of
  $`\Phi_p`$ at a slot; the root shape of $`A`$; the coincidences among the slot values
  $`J_e(u)`$; the unique-common-root principle itself.
- *relative to $`F_0`$*: the transported minimal polynomial $`B`$; its slot
  description, i.e. (2.1); the package $`\mathrm{Pkg}(M)`$; the conclusion
  $`j(q^M) \in F_{Mp}`$.

A non-membership's *conclusion* base-changes for free: a membership ascends by (5.1),
so a non-membership descends by contrapositive. But a non-membership's *hypothesis* is a
non-membership in the base field, and lifting it from the small field to the big one
costs the same faithfulness as descending a membership. So the cost sits on different
sides of the two statements: on the hypothesis of (2.2), on the conclusion of (2.3).

The asymmetry of §3 is now a statement about this classification: the enumerated data
of $`A`$ is intrinsic, the enumerated data of $`B`$ is relative. The sharing argument
is intrinsic; only the root bookkeeping of the minimal polynomial is relative. This is
the precise sense in which the descent does not need a base change, while (2.1) does.

The same asymmetry explains the strength of the two-field form of the note's §4. The
statement "from the package over $`F_0`$, conclude the membership in the level field
over $`F_0`$, while the roots are read in an ambient field $`L`$" is stronger than its
special case $`L = \kappa((q))`$: it takes the relative hypothesis and returns the
relative conclusion, with the ambient field only a device for the roots. The
$`\mathbb{Q}`$ theorem of the note is an instance of the stronger form, with
$`\kappa = \mathbb{Q}`$ and $`L = K((q))`$; the char-$`p`$ statements are instances of
the weaker form with $`L = \kappa((q))`$.

## 5. The base-change dictionary

Now let $`\kappa_0 \subset \kappa`$ be an extension of fields, and let $`\mathrm{ext}`$
be the coefficient extension $`\kappa_0((q)) \hookrightarrow \kappa((q))`$. In the
application $`\kappa_0 = \mathbb{Q}`$ and $`\kappa = K = \mathbb{Q}(\zeta_{Mp})`$.
Assume the local theorems of §2 at $`\kappa`$. The $`\kappa_0`$-statements follow from
four facts.

**(5.1) Fields.** For every $`d`$, the compositum of $`\kappa`$ with the image of
$`F_d`$ is the $`\kappa`$-level field $`\kappa(j(q), j(q^d))`$. Indeed $`F_d`$ is
generated over $`\kappa_0`$ by $`j(q)`$ and $`j(q^d)`$, and coefficient extension is a
map of fields, so the images generate the corresponding field over $`\kappa`$; the same
argument applies to the divisor fields $`\bar F_d`$. Consequently the generation clause
of the package transports.

**(5.2) Degrees.** $`[\kappa\cdot F_d : \kappa\cdot F_0] = [F_d : F_0]`$. Choose an
$`F_0`$-basis $`v_1, \dots, v_{\psi(d)}`$ of $`F_d`$; it is a family of
$`\kappa_0`$-linearly independent series. A $`\kappa`$-linear relation among their
coefficient extensions, read coefficientwise against a $`\kappa_0`$-basis of $`\kappa`$,
yields $`\kappa_0`$-linear relations among the $`v_i`$; hence the extended family is
$`\kappa`$-linearly independent and spans the compositum over $`\kappa\cdot F_0`$. So
the degrees agree, and the degree clause of the package transports. Neither (5.1) nor
(5.2) needs any hypothesis on $`\kappa/\kappa_0`$.

**(5.3) Minimal polynomials.** The coefficient extension of
$`\mathrm{minpoly}_{F_0}(j(q^M))`$ is $`\mathrm{minpoly}_{\kappa\cdot F_0}(j(q^M))`$.
Write $`P`$ for the coefficient extension and $`Q`$ for the minimal polynomial over
$`\kappa\cdot F_0`$. Both are monic; $`P`$ kills the extended element, so $`Q`$ divides
$`P`$; by (5.2) their degrees agree, so $`P = Q`$. Again no hypothesis on the extension.

**(5.4) Faithfulness on the rational slice.** Assume $`\kappa/\kappa_0`$ finite and
$`[\kappa : \kappa_0] \neq 0`$ in $`\kappa_0`$. If $`x \in \kappa_0((q))`$ and
$`\mathrm{ext}(x) \in \kappa\cdot F`$ for a subfield
$`\kappa_0 \subseteq F \subseteq \kappa_0((q))`$, then $`x \in F`$. Equivalently,

$$\kappa\cdot F \\;\cap\\; \kappa_0((q)) \\;=\\; F \qquad \text{inside } \kappa((q)).$$

*Proof.* Since $`\kappa/\kappa_0`$ is finite, every element of the compositum is a
finite sum $`\sum_i c_i f_i`$ with $`c_i \in \kappa`$ and $`f_i \in F`$: fix a
$`\kappa_0`$-basis $`b_1, \dots, b_n`$ of $`\kappa`$; the compositum is the $`F`$-span
of the $`b_j`$, and every element is of that form. Let $`\mathrm{tr}`$ be the
trace of $`\kappa/\kappa_0`$, extended coefficientwise to a $`\kappa_0`$-linear map
$`\kappa((q)) \to \kappa_0((q))`$. On a spanning element $`c f`$ with $`c \in \kappa`$
and $`f \in F`$ one has $`\mathrm{tr}(cf) = \mathrm{tr}(c)\,f \in F`$,
because the coefficients of $`f`$ lie in $`\kappa_0`$; by linearity
$`\mathrm{tr}(\kappa\cdot F) \subseteq F`$. On the other hand
$`\mathrm{tr}(\mathrm{ext}(x)) = [\kappa : \kappa_0]\,x`$ for
$`x \in \kappa_0((q))`$. Hence if $`\mathrm{ext}(x) \in \kappa\cdot F`$ then
$`[\kappa : \kappa_0]\,x \in F`$, and since the degree is invertible in
$`\kappa_0`$, $`x \in F`$. $`\square`$

Fact (5.4) is the mathematical content of the note's phrase "strips the coefficient
extension". It is not a consequence of (5.1)–(5.3): it is a faithfulness statement,
equivalently the linear disjointness of $`\kappa`$ and $`\kappa_0((q))`$ over
$`\kappa_0`$ inside $`\kappa((q))`$. It is also the only place in the whole assembly
where a hypothesis on the extension enters, and for $`\mathbb{Q} \subset K`$ it is
automatic, the degree $`\varphi(Mp)`$ being non-zero in $`\mathbb{Q}`$.

## 6. Assembly: one proof, and its instances

**Theorem.** *The three local statements hold, with one proof and in every
characteristic, over any field containing a primitive root of unity of the order the
statement requires. The statements (2.2) and (2.3) do not mention the root; it is a
device of their proofs.*

**Corollary.** *Let $`\kappa/\kappa_0`$ be finite with $`[\kappa : \kappa_0]`$
invertible in $`\kappa_0`$, and assume the local statements at $`\kappa`$. Then the
$`\kappa_0`$-statements follow: the package by (5.1)–(5.2), the transported minimal
polynomial by (5.3), and the two non-trivial transports by (5.4) — the membership
conclusion of (2.3), and the base hypothesis of (2.2); the non-membership conclusion of
(2.2) is free, by the ascent (5.1).*

The two instances of the note are the two extremes:

- $`\mathbb{Q}`$: apply (2.1), (2.2), (2.3) at $`K = \mathbb{Q}(\zeta_{Mp})`$.
  (5.3) gives the $`\mathbb{Q}`$-form of (2.1) — the minimal polynomial over
  $`\mathbb{Q}(j(q))`$ is the base change of the one over $`K\cdot\mathbb{Q}(j(q))`$
  — and (5.4) lifts the base non-membership that (2.2) needs; its conclusion then comes
  down for free. For (2.3), (2.3) at $`K`$ says
  $`j(q^M) \in K(j(q), j(q^{Mp})) = K\cdot F_{Mp}`$ by (5.1), and (5.4) returns
  $`j(q^M) \in \mathbb{Q}(j(q), j(q^{Mp}))`$.
- characteristic $`p`$ (or any field already containing the root): take
  $`\kappa_0 = \kappa`$; the dictionary is the identity and the local statements are
  already the required ones.

The strong induction of the note's §7 lives at the base field and is unchanged. Its
inputs are the one-prime statements, each of which is now either a local theorem
(char $`p`$) or a local theorem plus the dictionary ($`\mathbb{Q}`$). Concretely, for
$`\mathbb{Q}`$ the induction consumes the descended (2.3) for $`\mathrm{Gen}`$, the
descended (2.2) for the prime-power tower, and its degree step, the note's §6, which is
already a statement over $`\mathbb{Q}`$; (2.1) is not consumed directly but inside the
proof of (2.3). In particular the induction is never transported: only its one-prime
inputs are.

## 7. What this changes in the reading of the note's §4

The note's §4 ends by noting that the proof strips the coefficient extension
$`\mathbb{Q} \to K`$ and lands back in $`\mathbb{Q}((q))`$. In the any-field
organization that strip splits into three separate base-change facts, and they are of
different weight:

1. the fields: (5.1), an adjoin-of-images computation;
2. the minimal polynomial: (5.3), a degree plus divisibility argument;
3. the two transports that cost something: (5.4) for the membership conclusion of
   (2.3) and for the base hypothesis of (2.2) — faithfulness of the base change on the
   rational slice, the one genuine addition, proved by the trace. A non-membership
   *conclusion* needs only the ascent (5.1) and is free.

The A-side data of the descent (the modular relations, the prime splitting, the seed
identities, the unique-common-root principle) needs none of them: it is intrinsic and
transports along any field map. So the extension is spent exactly on the B side (the
slot description of the transported minimal polynomial) and on the two transports of
item 3. That is the asymmetry of §§3–4, and it is why the descent can be argued without
a coefficient extension at all: choose the modular equation as the enumerated polynomial,
and the base change shrinks to the two root-exclusion facts that (2.1) supplies.
