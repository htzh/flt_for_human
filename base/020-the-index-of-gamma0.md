# The index of $`\Gamma_0(N)`$, and the two functions that count it

Twentieth of the `base/` notes. [018](018-congruence-subgroups-and-invariance.md)
fixed the four congruence subgroups and, in its §4.3, quoted the lifting statement
that the level theory leans on; [005](005-cyclic-isogenies-and-level.md) drew the
lattice picture behind $`\Gamma_0(N)`$ and stated the Dedekind count $`\psi(N)`$;
[013](013-riemann-existence-and-the-q-expansion-principle.md) used the number
$`\psi(N)`$ as the degree of the cover $`X_0(N) \to X(1)`$. This note is the
*proof* the port actually carries: the first headline of
[`Gamma0Index.lean`](../lean/FLTForHuman/ModularCurve/Gamma0Index.lean),

$$[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] = \psi(N),$$

step by step, together with the second and independent count
$`\#\,\mathrm{primCosetReps}(N) = \psi(N)`$ that the $`q`$-expansion layer uses as
its index set.

It is also the right place to put mathlib's Euler $`\varphi`$ next to the port's
Dedekind $`\psi`$, because the index proof is exactly where they meet. Mathlib has
a finished totient API and **no** $`\psi`$ anywhere; the port's $`\psi`$ is the
pin's, and its three counting lemmas are proved from $`\varphi`$ on each prime
power (§6.1) and from a $`\varphi`$-count of residues (§8.2). §9 tabulates what is
mathlib's and what is ours.

Line-number citations point at `anthropics/fermats-last-theorem@aa2d8b3`. Mathlib
declarations are cited at tag **v4.34.0** (rev `5ed2965256`), the version this port
builds against, one minor version on from the pin's own `v4.33.0` — so the anchors
below match the copies the checked code was elaborated against. The two mathlib
files this note leans on hardest, `GroupTheory/Index.lean` and
`RingTheory/ZMod/UnitsCyclic.lean`, sit at identical lines in both versions; the
totient file shifted by two lines, so a `v4.33.0` reader should expect a small
offset there. Both kinds of citation are rendered GitHub links carrying `#L`
anchors.

The plan:

1. the statement, the two functions, and the closed form of the answer;
2. the shape of the argument: four moves, of which one is arithmetic;
3. step 1 — $`\Gamma_0(N)`$ is the preimage of the Borel subgroup;
4. step 2 — reduction is surjective, and lifting is Bezout arithmetic;
5. step 3 — the coset bijection $`\mathrm{SL}_2 \big/ \mathrm{borel} \cong
   \mathbb{P}^1(\mathbb{Z}/N)`$;
6. step 4 — counting the projective line: the local case, the Chinese remainder,
   and the induction;
7. step 5 — assembling the headline;
8. the second, independent count: primitive coset representatives;
9. what mathlib supplies, and what has no counterpart there;
10. key point $`\to`$ declaration map;
11. links.

## 1. The statement, and the answer in closed form

Mathlib defines the level group by its congruence condition
([CongruenceSubgroups.lean, lines 79–80, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L79-L80)):

```lean
def Gamma0 : Subgroup SL(2, ℤ) where
  carrier := { g | (g 1 0 : ZMod N) = 0 }
```

with `Gamma0_mem` recording the same thing as a membership test. The *index* of a
subgroup is the number of its cosets, and in mathlib it is by definition the
cardinality of the quotient
([Index.lean, line 348, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/GroupTheory/Index.lean#L348)):

```lean
theorem index_eq_card : H.index = Nat.card (G ⧸ H)
```

The Dedekind $`\psi`$ function is the pin's, and lives in the port at
[`NumberTheory/DedekindPsi.lean`](../lean/FLTForHuman/NumberTheory/DedekindPsi.lean)
(lines 54 and 69):

```lean
def dedekindPsi (N : ℕ) : ℕ := ∑ d ∈ N.divisors with Squarefree d, N / d
```

the sum of $`N/d`$ over the *squarefree* divisors. Its closed form is the Euler
product with a plus sign,

$$\psi(N) = N \prod_{p \mid N} \left(1 + \frac{1}{p}\right),$$

and on prime powers it is $`\psi(p^k) = p^k + p^{k-1}`$ (`dedekindPsi_prime_pow`),
with $`\psi(p) = p + 1`$ (`dedekindPsi_prime`) and $`\psi(1) = 1`$
(`dedekindPsi_one`). The product form itself is **not** in the ported module; the
pin states it (`ModularCurve.dedekindPsi_eq_prod_primeFactors`) and §9 records it
as deferred.

The contrast with Euler's function is one sign. Mathlib's totient counts the
reduced residues
([Totient.lean, line 39, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/Nat/Totient.lean#L39)):

```lean
def totient (n : ℕ) : ℕ := #{a ∈ range n | n.Coprime a}
```

so $`\varphi(N) = N \prod_{p \mid N} (1 - 1/p) = \#(\mathbb{Z}/N)^{\times}`$ (the
last equality is `ZMod.card_units_eq_totient`,
[line 113](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/Nat/Totient.lean#L113)), while $`\psi(N) = N \prod_{p \mid N} (1 + 1/p)`$.
On a prime power they are complementary: $`\psi(p^k) = 2p^k - \varphi(p^k)`$. This
is the arithmetic shadow of the group theory: $`\varphi(N)`$ is the index of
$`\Gamma_1(N)`$ in $`\Gamma_0(N)`$ (the diamond quotient), and $`\psi(N)`$ is the
index of $`\Gamma_0(N)`$ in the full group, so the two multiply up the tower
$`\Gamma(N) \subseteq \Gamma_1(N) \subseteq \Gamma_0(N) \subseteq
\mathrm{SL}_2(\mathbb{Z})`$.

**Why $`\psi`$ is the expected answer.** A coset of $`\Gamma_0(N)`$ should be a
*line* in $`(\mathbb{Z}/N)^2`$ (§5), and the lines can be counted before any of the
formal work: units act freely on unimodular rows (if $`ua = a`$, $`uc = c`$ and
$`xa + yc = 1`$ then $`u = 1`$), so

$$\\#\mathbb{P}^1(\mathbb{Z}/N) = \frac{\\#\\{\text{unimodular rows}\\}}{\varphi(N)}
  = \frac{N^2 \prod_{p \mid N} (1 - p^{-2})}{N \prod_{p \mid N} (1 - p^{-1})}
  = N \prod_{p \mid N} \left(1 + \frac{1}{p}\right) = \psi(N).$$

The Lean proof does not take this route — it counts $`\mathbb{P}^1(\mathbb{Z}/p^k)`$
locally and multiplies by the Chinese remainder theorem (§6), and it gets
$`\psi`$ from $`\varphi`$ at each prime power. The display above is the one-line
human summary of the answer, not a formalized step.

Both headlines are public in the port
([`Gamma0Index.lean`](../lean/FLTForHuman/ModularCurve/Gamma0Index.lean), lines 522
and 725), transcribed verbatim from the pin's `Theorems/` wrappers:

```lean
theorem Gamma0_index (N : ℕ) [NeZero N] : (CongruenceSubgroup.Gamma0 N).index = dedekindPsi N

theorem card_primCosetReps_eq_dedekindPsi (N : ℕ) (hN : N ≠ 0) :
    (primCosetReps N).card = dedekindPsi N
```

The hypotheses are not decoration: the prime-power count of §6.1 needs a genuine
$`k \neq 0`$, the CRT step needs nonzero factors, and the induction of §6.3 splits
off $`N = 0`$ explicitly. The pin states the same two theorems with the same
side conditions.

## 2. The shape of the argument

Five moves, and only the second is arithmetic:

```text
(1)  Γ₀(N) = borel(ℤ/N).comap (reduction)              Gamma0_eq_comap_borel
(2)  reduction is surjective                           sl2_surj
     ⟹ (Γ₀ N).index = (borel (ℤ/N)).index              index_comap_of_surjective
(3)  SL₂(R) ⧸ borel(R) ≅ ℙ¹(R), by the first column    card_quotient_borel
(4)  #ℙ¹(ℤ/N) = ψ(N)                                   card_projectiveLine_zmod
(5)  index = Nat.card (G ⧸ H)                          index_eq_card
```

Move (3) is a statement about an arbitrary commutative ring, with no arithmetic
in it — it is the *definition* of the coset space in coordinates. Move (4) is where
all the number theory is. Move (2) is where a reader expects the arithmetic to be
too, and it is; but its content is a lifting statement about matrices, not a count.
Moves (1) and (5) are bookkeeping: mathlib's $`\Gamma_0`$ is defined intrinsically,
so it has to be *identified* with a preimage before the index lemma applies, and
the index has to be identified with a cardinality.

## 3. Step 1: $`\Gamma_0(N)`$ is the preimage of the Borel subgroup

The Borel subgroup of $`\mathrm{SL}_2(R)`$ is the upper-triangular one, and in the
port it is the subgroup cut out by the lower-left entry
([`ProjectiveLine.lean`, lines 97–117](../lean/FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean)):

```lean
def borel (R : Type*) [CommRing R] : Subgroup (SpecialLinearGroup (Fin 2) R) where
  carrier := { M | M.1 1 0 = 0 }

theorem mem_borel_iff {A : SpecialLinearGroup (Fin 2) R} : A ∈ borel R ↔ A.1 1 0 = 0 :=
  Iff.rfl
```

Mathlib has no Borel subgroup; the port supplies it once, beside the projective
line, because the two are the same object seen twice.

The bridge from mathlib's $`\Gamma_0`$ to that subgroup is a real theorem in the
port, not a `rfl` (lines 261–268):

```lean
private theorem Gamma0_eq_comap_borel (N : ℕ) :
    Gamma0 N = (borel (ZMod N)).comap
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  ext A
  rw [Gamma0_mem, Subgroup.mem_comap, mem_borel_iff]
```

The proof is an `ext` and a rewrite: both sides say that the lower-left entry of
$`A`$, read in $`\mathbb{Z}/N`$, vanishes. The work is in *knowing* that it is worth
saying: `Gamma0` is defined by a congruence on one matrix entry, and the preimage
description is what composes with the index lemma of the next section. The pin
keeps this helper `private` (lines 216–217) and the port does the same.

## 4. Step 2: reduction is surjective, and lifting is Bezout arithmetic

### 4.1 The statement to prove

Reduction of entries modulo $`N`$ is a group homomorphism
$`\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/N)`$, and the index of a
preimage under a surjection is the index of the subgroup
([Index.lean, lines 68–69, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/GroupTheory/Index.lean#L68-L69)):

```lean
theorem index_comap_of_surjective {f : G' →* G} (hf : Function.Surjective f) :
    (H.comap f).index = H.index
```

So the whole of step 2 is the surjectivity statement
([`Gamma0Index.lean`, lines 179–181](../lean/FLTForHuman/ModularCurve/Gamma0Index.lean)):

```lean
private theorem sl2_surj (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
```

The mathematics behind it is the standard strong-approximation fact for
$`\mathrm{SL}_2`$: reduction at level $`N`$ is onto. (The pin keeps the helper
`private` at lines 137–138; the port keeps it `private` too, and exposes only the
four-entry lifting lemma below. Section §9 lists what that costs a consumer.) The
pin's own prose for this step is [018 §4.3](018-congruence-subgroups-and-invariance.md),
which quotes the two statements and explains why a choice of lift is not
canonical: two lifts of one mod-$`N`$ matrix differ by an element of $`\Gamma(N)`$.

### 4.2 Why it is not formal: the naive lift fails

It is tempting to lift the four entries independently: pick $`a_0, b_0, c_0, d_0
\in \mathbb{Z}`$ reducing to $`a, b, c, d`$ and declare victory. That does not give
a matrix in $`\mathrm{SL}_2(\mathbb{Z})`$: the determinant condition is only
$`a_0d_0 - b_0c_0 \equiv 1 \pmod N`$, i.e.

$$N \mid a_0 d_0 - b_0 c_0 - 1,$$

and the integral matrix needs determinant *exactly* $`1`$. The pin's
`exists_sl2_int_lift` therefore chooses the entries rather than lifting them
(lines 132–135):

```lean
theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d := by
```

The construction has three parts.

### 4.3 Fix the second column: a coprime pair congruent to $`(c_0, d_0)`$

The first observation is that no prime may divide $`c_0`$, $`d_0`$ *and* $`N`$ at
once. If $`p \mid c_0`$, $`p \mid d_0`$ and $`p \mid N`$, then $`p`$ divides both
$`a_0d_0 - b_0c_0`$ and $`a_0d_0 - b_0c_0 - 1`$, hence $`p \mid 1`$, absurd. The
proof packages this as the hypothesis `H` of `exists_coprime_lift` (lines 90–93):

```lean
private theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by
```

It then *replaces* the second column by a coprime pair still congruent to
$`(c_0, d_0)`$. The device is `primeSel` (lines 68–69):

```lean
private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p
```

the product of the primes of $`c`$ that do not already divide $`d`$. Put
$`\gamma := c_0`$ (or $`N`$ if $`c_0 = 0`$, which is still $`\equiv 0`$ and keeps
$`\gamma \neq 0`$) and

$$\delta := d_0 + \mathrm{primeSel}(\gamma, d_0) \cdot N.$$

Then $`\delta \equiv d_0 \pmod N`$ and $`\gcd(\gamma, \delta) = 1`$: a common prime
$`p`$ satisfies $`p \mid d_0`$ or not. If $`p \mid d_0`$ then $`p \nmid
\mathrm{primeSel}(\gamma,d_0)`$ (every prime of $`\gamma`$ dividing $`d_0`$
contributes the factor $`1`$), so from $`p \mid \delta`$ and $`p \mid d_0`$ we get
$`p \mid N`$, against `H`. If $`p \nmid d_0`$ then $`p \mid
\mathrm{primeSel}(\gamma,d_0)`$ (it is a prime of $`\gamma`$), so $`p \mid \delta`$
gives $`p \mid d_0`$, a contradiction. Either way, no common prime exists; the two
lemmas `dvd_primeSel` and `not_dvd_primeSel` are exactly these two cases.

### 4.4 Bezout, then slide the first column

With a coprime second column in hand, the first column is free: Bezout's identity
$`\mathrm{gcdA}(\gamma,\delta)\,\gamma + \mathrm{gcdB}(\gamma,\delta)\,\delta =
\gcd(\gamma,\delta) = 1`$ makes

$$\alpha_0 := \mathrm{gcdB}(\gamma,\delta), \qquad \beta_0 := -\mathrm{gcdA}(\gamma,\delta)$$

a pair with $`\alpha_0 \delta - \beta_0 \gamma = 1`$ exactly, so
$`[[\alpha_0,\beta_0],[\gamma,\delta]] \in \mathrm{SL}_2(\mathbb{Z})`$ already. Only
its residues are wrong: $`\gamma \equiv c`$ and $`\delta \equiv d`$ by construction,
but $`(\alpha_0,\beta_0)`$ is some Bezout solution, not the target $`(a,b)`$.

The two columns satisfy the same determinant relation modulo $`N`$, namely
$`a d - b c = 1`$ and $`\alpha_0 d - \beta_0 c = 1`$, so the mismatch is measured by

$$\lambda := b\\,\alpha_0 - a\\,\beta_0 \in \mathbb{Z}/N,$$

and sliding the first column along the second,

$$(\alpha, \beta) := (\alpha_0, \beta_0) + \lambda\\,(\gamma, \delta),$$

leaves the determinant alone (it is an integer row operation) and lands on the
target:

$$\alpha_0 + (b\alpha_0 - a\beta_0)c = \alpha_0(1 + bc) - a\beta_0c
  = \alpha_0\\,ad - a\beta_0c = a(\alpha_0 d - \beta_0 c) = a,$$

using $`1 + bc = ad`$ from $`ad - bc = 1`$; the computation for $`\beta`$ is the same
with the roles swapped. In the Lean these are two `linear_combination` calls with
certificates $`-(\alpha_0)\cdot h + a \cdot h_{\det}`$ and
$`-(\beta_0)\cdot h + b \cdot h_{\det}`$ (lines 170–175). Finally `sl2_surj`
applies the lemma to the entries of the given matrix, using
$`M_{00}M_{11} - M_{01}M_{10} = 1`$ from `M.prop`, and checks the map is entrywise
the original (lines 179–190).

## 5. Step 3: the coset bijection with the projective line

Now the group theory. The port defines the projective line over an *arbitrary*
commutative ring, because that is what $`\mathbb{Z}/N`$ is
([`ProjectiveLine.lean`, lines 37–67](../lean/FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean)):

```lean
def IsUnimodularRow (a c : R) : Prop :=
  ∃ x y : R, x * a + y * c = 1

abbrev UnimodularRow (R : Type*) [CommRing R] := { v : R × R // IsUnimodularRow v.1 v.2 }

def ProjectiveLine (R : Type*) [CommRing R] : Type _ :=
  Quotient (unimodularRowSetoid R)
```

— unimodular rows modulo scaling by a unit, since a row generates the unit ideal.
Mathlib has the projective line only over a division ring (`OnePoint`), so this
too is vocabulary the port supplies.

The map that identifies the coset space with the lines takes a matrix to its
**first column**. It is well defined because a matrix in $`\mathrm{SL}_2`$ has a
unimodular first column: from $`\det A = 1`$ one reads off
$`A_{11}A_{00} + (-A_{01})A_{10} = 1`$ (`isUnimodularRow_firstCol`). The substance is
the equivalence (lines 208–209):

```lean
private theorem firstColumnClass_eq_iff (A B : SpecialLinearGroup (Fin 2) R) :
    firstColumnClass A = firstColumnClass B ↔ A⁻¹ * B ∈ borel R := by
```

*Forward*: if the first columns differ by a unit $`u`$, then the $`(1,0)`$-entry of
$`A^{-1}B`$ is $`(-A_{10})(uA_{00}) + A_{00}(uA_{10}) = 0`$ — the two terms cancel.
The Lean expands $`A^{-1}`$ with `SL2_inv_expl` and the product with
`Matrix.two_mul_expl`, then `ring`.
*Backward*: if $`C = A^{-1}B`$ is upper triangular of determinant $`1`$, then
$`C_{00}C_{11} = 1`$, so $`C_{00}`$ is a unit; and $`B = AC`$ has first column
$`C_{00}`$ times that of $`A`$, because the upper-triangular $`C`$ contributes
nothing through its second column to the first.

*Surjectivity* is the completing trick: a unimodular row $`(a,c)`$ with
$`xa + yc = 1`$ is the first column of

$$[[a, -y], [c, x]], \qquad \det = ax + cy = 1.$$

So the first-column map is a bijection, and `Nat.card_eq_of_bijective` turns it
into the cardinality statement, for every commutative ring (lines 236–238):

```lean
private theorem card_quotient_borel (R : Type*) [CommRing R] :
    Nat.card (SpecialLinearGroup (Fin 2) R ⧸ borel R) = Nat.card (ProjectiveLine R) := by
```

Read with §4, this is the classical coset bijection: because $`\Gamma_0(N)`$ is the
preimage of the Borel subgroup and reduction is onto, the cosets of
$`\Gamma_0(N)`$ are in bijection with the cosets of the Borel subgroup, and the
latter are in bijection with the lines in $`(\mathbb{Z}/N)^2`$. The port proves the
two cardinality equalities separately and never exhibits the composed bijection.

## 6. Step 4: counting the projective line

### 6.1 The local case: $`\mathbb{Z}/p^k`$ is a local ring

Over $`R = \mathbb{Z}/p^k`$ with $`k \neq 0`$ there is a maximal ideal $`(p)`$, and
two facts do all the work. First, an element is a unit exactly when it survives
reduction modulo $`p`$ (lines 274–275):

```lean
private theorem isUnit_zmod_prime_pow_iff {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (z : ZMod (p ^ k)) :
    IsUnit z ↔ ZMod.castHom (dvd_pow_self p hk) (ZMod p) z ≠ 0 := by
```

Second, a unimodular row therefore has at least one unit entry, since if both
entries reduced to $`0`$ then so would $`1 = xa + yc`$ (lines 298–299):

```lean
private theorem isUnit_or_isUnit {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    {a c : ZMod (p ^ k)} (h : IsUnimodularRow a c) : IsUnit a ∨ IsUnit c := by
```

Consequently every line has exactly one representative $`[1 : t]`$ (when the first
entry is a unit) or $`[m : 1]`$ with $`m`$ a **non**-unit (when only the second is).
That is a bijection

$$\mathbb{Z}/p^k \\;\sqcup\\; \\{z : \mathbb{Z}/p^k \mid z \text{ not a unit}\\}
  \\;\xrightarrow{\sim}\\; \mathbb{P}^1(\mathbb{Z}/p^k),$$

and the count follows from two cardinalities. The units number $`\varphi(p^k)`$,
by `ZMod.card_units_eq_totient`; the non-units number $`p^{k-1}`$, because
$`\#R = \#\{\text{units}\} + \#\{\text{non-units}\}`$ and
$`\varphi(p^k) + p^{k-1} = p^k`$ (lines 323–324):

```lean
private theorem card_not_isUnit_zmod_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    Nat.card { z : ZMod (p ^ k) // ¬IsUnit z } = p ^ (k - 1) := by
```

The totient input is `Nat.totient_prime_pow_succ`
([Totient.lean, line 182, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/Nat/Totient.lean#L182)),
and the whole arithmetic of the port's $`\psi`$ at prime powers follows from
exactly this pair of numbers (lines 347–348):

```lean
private theorem card_projectiveLine_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    Nat.card (ProjectiveLine (ZMod (p ^ k))) = p ^ k + p ^ (k - 1) := by
```

which is $`\psi(p^k)`$ by `dedekindPsi_prime_pow`. This is the one place where
$`\psi`$ and $`\varphi`$ genuinely meet: both count residues of $`\mathbb{Z}/p^k`$
— the units and the non-units — and their sum $`p^{k-1}(p-1) + p^{k-1}(p+1) =
2p^k`$ is twice the ring.

### 6.2 Multiplicativity across coprime factors

For coprime $`M`$ and $`N`$, the Chinese remainder theorem is a ring equivalence
$`\mathbb{Z}/MN \cong \mathbb{Z}/M \times \mathbb{Z}/N`$
([Data/ZMod/Basic.lean, line 889, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/ZMod/Basic.lean#L889)):

```lean
def chineseRemainder {m n : ℕ} (h : m.Coprime n) : ZMod (m * n) ≃+* ZMod m × ZMod n
```

Pushing a row through the two projections gives two rows, one over each factor, and
`ProjectiveLine.map` is functorial enough to send lines to lines. The port's
`card_projectiveLine_mul` (lines 422–423) shows the induced map on lines is
bijective: injective by lifting representatives and gluing the two units through
the ring equivalence (`e.symm (u₁, u₂)`), surjective by gluing a row from one factor
and a row from the other, whose unimodularity is componentwise:

```lean
private theorem card_projectiveLine_mul (M N : ℕ) [NeZero M] [NeZero N] (h : M.Coprime N) :
    Nat.card (ProjectiveLine (ZMod (M * N))) =
      Nat.card (ProjectiveLine (ZMod M)) * Nat.card (ProjectiveLine (ZMod N)) := by
```

### 6.3 The induction, and the headline of this section

Assembling the local computations along the factorization of $`N`$ is an induction
on the prime-power decomposition, for which mathlib has exactly one tool
([Factorization/Induction.lean, lines 49–53, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Data/Nat/Factorization/Induction.lean#L49-L53)):

```lean
def recOnPosPrimePosCoprime {motive : ℕ → Sort*}
    (prime_pow : ∀ p n : ℕ, Prime p → 0 < n → motive (p ^ n))
    (zero : motive 0) (one : motive 1)
    (coprime : ∀ a b, 1 < a → 1 < b → Coprime a b → motive a → motive b → motive (a * b)) :
    ∀ a, motive a
```

The four cases of
[`card_projectiveLine_zmod`](../lean/FLTForHuman/ModularCurve/Gamma0Index.lean)
(lines 498–516) are then:

* a prime power: §6.1, with `dedekindPsi_prime_pow` for the right-hand side;
* $`N = 0`$: excluded by the hypothesis `hN : N ≠ 0`;
* $`N = 1`$: $`\mathbb{Z}/1`$ is the zero ring, every row is the same line, so
  $`\#\mathbb{P}^1 = 1 = \psi(1)`$;
* a coprime product: §6.2, with `dedekindPsi_mul_of_coprime` and the two induction
  hypotheses.

```lean
theorem card_projectiveLine_zmod (N : ℕ) (hN : N ≠ 0) :
    Nat.card (ProjectiveLine (ZMod N)) = dedekindPsi N := by
  induction N using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      rw [card_projectiveLine_prime_pow p n hp hn.ne', dedekindPsi_prime_pow p n hp hn.ne']
  | zero => exact absurd rfl hN
  | one => …
  | coprime a b ha hb hab iha ihb =>
      haveI : NeZero a := ⟨by omega⟩
      haveI : NeZero b := ⟨by omega⟩
      rw [card_projectiveLine_mul a b hab, iha (by omega), ihb (by omega),
        dedekindPsi_mul_of_coprime a b hab]
```

Unfolding the product over the prime powers gives the closed form of §1, and the
three $`\psi`$ facts the induction consumes — `dedekindPsi_one`,
`dedekindPsi_prime_pow`, `dedekindPsi_mul_of_coprime` — are the ported module's,
imported from `NumberTheory/DedekindPsi.lean`, not re-proved here. The prime-power
identity is where the two functions are tied: it is proved from the totient
identity $`\varphi(p^k) + p^{k-1} = p^k`$.

## 7. Step 5: the headline, assembled

Everything now composes into four rewrites
([`Gamma0Index.lean`, lines 522–527](../lean/FLTForHuman/ModularCurve/Gamma0Index.lean)):

```lean
theorem Gamma0_index (N : ℕ) [NeZero N] : (CongruenceSubgroup.Gamma0 N).index = dedekindPsi N := by
  have h1 : (Gamma0 N).index = (borel (ZMod N)).index := by
    rw [Gamma0_eq_comap_borel]
    exact Subgroup.index_comap_of_surjective _ (sl2_surj N)
  rw [h1, Subgroup.index_eq_card, card_quotient_borel,
    card_projectiveLine_zmod N (NeZero.ne N)]
```

Read as a chain:

```text
(Γ₀ N).index
  = (borel (ℤ/N)).index                 step 1 + step 2, index_comap_of_surjective
  = Nat.card (SL₂(ℤ/N) ⧸ borel)          Subgroup.index_eq_card
  = Nat.card (ℙ¹(ℤ/N))                   card_quotient_borel   (step 3)
  = dedekindPsi N                        card_projectiveLine_zmod (step 4)
```

Note what is *not* in the chain: no coset representative is ever exhibited, no
Euclidean algorithm appears, and no group acts on anything. The index theorem is
the composition of a lifting statement with a cardinality computation over the
quotient, and the quotient itself is never more than `Nat.card` of a type.

## 8. The second, independent count: primitive coset representatives

### 8.1 The set, and why its cardinality is the same number

The index set the $`q`$-expansion layer actually enumerates is not the projective
line but a set of upper-triangular matrices. The representatives of the cosets of
$`\Gamma_0(N)`$ can be taken of the form $`[[a,b],[0,d]]`$ with $`ad = N`$, $`0 \le b
\lt d`$; the port records the index set as triples
([`Defs/PrimCosetReps.lean`, lines 26–31](../lean/FLTForHuman/ModularCurve/Defs/PrimCosetReps.lean)):

```lean
def primCosetReps (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.filter
    (fun t => t.1 * t.2.2 = N ∧ t.2.1 < t.2.2 ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1)
    (Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1))
```

The headline is `card_primCosetReps_eq_dedekindPsi` (quoted in §1). Its proof shares
nothing with §§3–7: it never mentions $`\mathrm{SL}_2`$, the Borel subgroup, or
lifting. It is a pure counting argument on `Finset`s and `ArithmeticFunction`s,
which is exactly why it is worth having — two proofs of one number.

### 8.2 The fibre count is a totient count

Reindex the triples by their first and third entries
(`card_primCosetReps_eq_sum`): the set is the sigma, over pairs $`(a,d)`$ with
$`ad = N`$, of the $`b \lt d`$ coprime to $`\gcd(a,d)`$. So its cardinality is

$$\\#\mathrm{primCosetReps}(N) = \sum_{(a,d) \in \mathrm{divisorsAntidiagonal}(N)}
  \\#\\{b \lt d : \gcd(\gcd(a,d), b) = 1\\},$$

and each inner count is the port's fibre value
([`NumberTheory/DedekindPsi.lean`, lines 217–221](../lean/FLTForHuman/NumberTheory/DedekindPsi.lean)):

```lean
abbrev dedekindPsiFibre (x : ℕ × ℕ) : ℕ :=
  (x.2 / Nat.gcd x.1 x.2) * Nat.totient (Nat.gcd x.1 x.2)

theorem card_fibre (a d : ℕ) :
    ((range d).filter (fun b => Nat.Coprime (Nat.gcd a d) b)).card =
      dedekindPsiFibre (a, d) := by
```

The value is $`\frac{d}{g}\varphi(g)`$ with $`g = \gcd(a,d)`$: the $`b`$ coprime to
$`g`$ are periodic in $`g`$, so a block of $`d = (d/g)\cdot g`$ consecutive residues
contains exactly $`(d/g)\varphi(g)`$ of them — that is the companion lemma
`card_filter_coprime_range_mul`, proved from mathlib's `Nat.periodic_coprime` and
`Nat.totient_eq_card_coprime`. This is Euler's function doing the counting inside
Dedekind's.

### 8.3 Turning the sum into an arithmetic function

The rest of the argument makes the sum multiplicative, which is where the
`ArithmeticFunction` machinery of the ported $`\psi`$ module is reused. Define

$$G(n) := \sum_{(a,d) \in \mathrm{divisorsAntidiagonal}(n)} h(a,d), \qquad h = \mathrm{dedekindPsiFibre},$$

as an `ArithmeticFunction ℕ` (lines 644–645). Then:

* $`G`$ is multiplicative (`isMultiplicative_G`), because the divisors-antidiagonal
  sum of a multiplicative two-variable function multiplies over coprime
  factorizations: `sum_divisorsAntidiagonal_mul_of_coprime`, fed the hypothesis
  `h_mul` that $`h(a_1a_2, d_1d_2) = h(a_1,d_1)h(a_2,d_2)`$ for coprime products —
  a four-way application of `Nat.Coprime.gcd_mul` and `Nat.totient_mul`;
* $`G(p^k) = p^k + p^{k-1}`$ (`G_prime_pow`), by telescoping: the summand is
  $`h(p^{k-j}, p^j) = \varphi(p^j)`$ for $`1 \le j \le k-1`$ (both cases of
  $`\min(k-j, j)`$ collapse to $`\varphi(p^j)`$ by the definition of
  `dedekindPsiFibre`), while the two end terms contribute $`1`$ and $`p^k`$; the
  telescoping step is `h_prime_pow`, $`h(p^i,p^j) + p^{j-1} = p^j`$, and
  `sum_h_prime_pow_partial` accumulates it.

Two multiplicative arithmetic functions agreeing on prime powers are equal
([ArithmeticFunction/Defs.lean, lines 565–567, v4.34.0](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean#L565-L567)):

```lean
theorem eq_iff_eq_on_prime_powers [CommMonoidWithZero R] (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) (g : ArithmeticFunction R) (hg : g.IsMultiplicative) :
    f = g ↔ ∀ p i : ℕ, Nat.Prime p → f (p ^ i) = g (p ^ i)
```

so `G_eq_Psi : G = Psi` (line 713), and `Psi_apply : Psi n = dedekindPsi n` converts
back to the $`\psi`$ of §1. The headline follows:

```lean
theorem card_primCosetReps_eq_dedekindPsi (N : ℕ) (hN : N ≠ 0) :
    (primCosetReps N).card = dedekindPsi N := by
  rw [PrimCosetCount.card_primCosetReps_eq_sum N hN, ← PrimCosetCount.G_apply,
    PrimCosetCount.G_eq_Psi]
  exact Psi_apply N
```

Note the shape of the reuse: the port defines $`\psi`$ *twice* — as the divisor sum
`dedekindPsi` and as the convolution `Psi = μ² ∗ id` of the squarefree indicator
with the identity — and this proof is what makes the second definition pay. The
pin had both `Psi` and the squarefree indicator `private` in two different files;
the port promotes them once ([`NumberTheory/DedekindPsi.lean`](../lean/FLTForHuman/NumberTheory/DedekindPsi.lean),
the move recorded in [level-port.md §7](../lean/logs/level-port.md)). The
`ModularCurve`-namespaced spelling of the pin's names survives as the one-line
delegation module
[`ModularCurve/Defs/DedekindPsi.lean`](../lean/FLTForHuman/ModularCurve/Defs/DedekindPsi.lean).

## 9. What mathlib supplies, and what has no counterpart there

**$`\varphi`$**: mathlib has the full theory —
`Nat.totient` and its scoped notation $`\varphi`$ (Totient.lean line 39), the
multiplicativity `totient_mul` (line 133), the divisor sum
`sum_totient : ∑_{d \mid n} \varphi(d) = n` (line 165), the prime and prime-power
values `totient_prime` (line 216) and `totient_prime_pow_succ` (line 182), the
bounds `totient_le` and `totient_pos` (lines 62, 75), the group-theoretic reading
`ZMod.card_units_eq_totient` (line 113), the Euler product
`totient_eq_mul_prod_factors` (line 289), the gcd identity
`totient_gcd_mul_totient_mul` (line 331) with `totient_super_multiplicative`
(line 349) and `totient_dvd_of_dvd` (line 358), and the block count
`filter_coprime_Ico_eq_totient` (line 80).

**$`\psi`$**: mathlib has nothing. A search for `dedekindPsi` (and for
`dedekind_psi`) over the whole of `Mathlib/` at v4.34.0 returns no declaration; the
`Dedekind` hits are cuts, domains, and zeta, and every `Jordan` hit is
Jordan–Hölder or Jordan's inequality. The port's $`\psi`$ module therefore holds
the definition, the multiplicativity, the prime step in three shapes, positivity,
the totient-based block count, and the fibre value.

Three further gaps are worth naming, because they are why the port had to write
the vocabulary itself:

* **no Borel subgroup** of $`\mathrm{SL}_2(R)`$ — the port's `borel`;
* **no projective line over a general commutative ring** — mathlib's `OnePoint`
  requires a division ring, and $`\mathbb{Z}/N`$ is full of zero divisors precisely
  when $`N`$ is composite, which is the interesting case here;
* **no index formula for $`\Gamma_0(N)`$** — and no `dedekindPsi` to state it with.

Two honest caveats.

1. Mathlib's `filter_coprime_Ico_eq_totient` says
   $`\#\{x \in [n, n+a) : \gcd(a,x) = 1\} = \varphi(a)`$ — a full period at an
   *arbitrary* offset — while the port's `card_filter_coprime_range_mul` counts
   $`m`$ periods starting at $`0`$. The former looks strictly stronger, so the latter
   may be a short induction away from it, but that has **not been machine-checked**
   and no replacement is claimed; the port's proof uses `Nat.periodic_coprime`
   directly.
2. The port's totient-adjacent statements are the two the index proof needs. The
   pin's other $`\psi`$ facts are public there and unported here:
   `ModularCurve.le_dedekindPsi` ($`N \le \psi(N)`$, whose argument the port inlines
   inside `dedekindPsi_pos` without exporting the lemma),
   `ModularCurve.dedekindPsi_eq_prod_primeFactors` and `dedekindPsi_of_squarefree`
   (the product form of §1 — stated in the module's docstring but not as a theorem),
   and `ModularCurve.card_quotient_gamma0_le_dedekindPsi`. None of them is needed by
   §§3–8.

## 10. Key point $`\to`$ declaration map

| mathematics | port declaration | pin source |
|---|---|---|
| $`\Gamma_0(N)`$ as a congruence condition | `CongruenceSubgroup.Gamma0`, `Gamma0_mem` (mathlib) | — |
| $`\mathrm{SL}_2(R)`$ upper triangular | `ModularCurve.borel`, `mem_borel_iff` | [Def_ModularCurve_ProjectiveLine.lean, lines 69, 88](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ProjectiveLine.lean#L69-L88) |
| unimodular rows, $`\mathbb{P}^1(R)`$ | `IsUnimodularRow`, `ProjectiveLine`, `ProjectiveLine.map` | [same, lines 14–59](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ProjectiveLine.lean#L14-L59) |
| step 1: $`\Gamma_0(N)`$ is a preimage | `Gamma0_eq_comap_borel` | [S_ModularCurve_Gamma0_index.lean, lines 216–217](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L216-L217) |
| step 2: reduction is onto | `sl2_surj`, `exists_sl2_int_lift` | [same, lines 88–91, 137–138](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L137-L138) |
| step 2, the coprime second column | `exists_coprime_lift`, `primeSel` | [same, lines 24–86](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L24-L86) |
| step 3: Borel cosets are the first columns | `firstColumnClass`, `firstColumnClass_eq_iff`, `card_quotient_borel` | [same, lines 160–214](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L160-L214) |
| step 3: index = cardinality of the quotient | `Subgroup.index_eq_card` (mathlib) | — |
| step 4, local: a row has a unit entry | `isUnit_zmod_prime_pow_iff`, `isUnit_or_isUnit` | [S_ModularCurve_card_projectiveLine_zmod.lean, lines 19–62](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean#L19-L62) |
| step 4, local: the count $`p^k + p^{k-1}`$ | `card_not_isUnit_zmod_prime_pow`, `card_projectiveLine_prime_pow` | [same, lines 71–95](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean#L71-L95) |
| step 4, global: CRT multiplicativity | `card_projectiveLine_mul` | [same, lines 156–246](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean#L156-L246) |
| $`\#\mathbb{P}^1(\mathbb{Z}/N) = \psi(N)`$ | `card_projectiveLine_zmod` | [same, line 248](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean#L248) |
| $`[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] = \psi(N)`$ | `Gamma0_index` | [S_ModularCurve_Gamma0_index.lean, line 227](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L227) |
| $`\psi(N) = N \prod (1 + 1/p)`$, multiplicativity | `dedekindPsi`, `dedekindPsi_prime_pow`, `dedekindPsi_mul_of_coprime` | [Thm_ModularCurve_dedekindPsi_prime_pow.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_dedekindPsi_prime_pow.lean), [Thm_ModularCurve_dedekindPsi_mul_of_coprime.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_dedekindPsi_mul_of_coprime.lean) |
| $`\psi = \mu^2 * \mathrm{id}`$ | `Psi`, `Psi_apply`, `isMultiplicative_Psi` | [S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean, lines 226–248](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L226-L248) |
| the fibre value $`(d/g)\varphi(g)`$ | `dedekindPsiFibre`, `card_fibre`, `card_filter_coprime_range_mul` | [same, lines 16–45](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L16-L45) |
| the sum $`G`$ is multiplicative | `sum_divisorsAntidiagonal_mul_of_coprime`, `h_mul`, `isMultiplicative_G` | [same, lines 74–168](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L74-L168) |
| $`G(p^k) = p^k + p^{k-1}`$, $`G = \Psi`$ | `h_prime_pow`, `G_prime_pow`, `G_eq_Psi` | [same, lines 170–277](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L170-L277) |
| $`\#\mathrm{primCosetReps}(N) = \psi(N)`$ | `card_primCosetReps_eq_dedekindPsi` | [same, line 288](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L288) |

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
* [`spec/LevelConsumer.lean`](../lean/spec/LevelConsumer.lean) — the executed wire
  test: at $`N = 2`$ both routes give $`3`$, and the index is stated equal to the
  cardinality of the projective line.
* [S_ModularCurve_Gamma0_index.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean),
  [S_ModularCurve_card_projectiveLine_zmod.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_projectiveLine_zmod.lean),
  [S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean)
  — the three pinned solution files the port transcribes.
