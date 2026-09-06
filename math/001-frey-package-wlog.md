# Why a Frey package is enough, WLOG, for every prime exponent p ≥ 5

This note walks through one small, self-contained step of the formalized proof:
the reduction that says *to rule out counterexamples to Fermat's Last Theorem
for a prime exponent p ≥ 5, it suffices to rule out normalized ones* — the
`FreyPackage`s. Mathematically this is elementary (a page of congruences), and
that is exactly why the generated documentation glosses it in one phrase
("permute and rescale to reach the normalisation"). Here we expand it.

Line numbers below refer to
`anthropics/fermats-last-theorem@aa2d8b3` (main, 2026-09-03).

## 1. What is actually claimed

The precise Lean statement
([Thm_FreyPackage_of_counterexample.lean, line 6](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_FreyPackage_of_counterexample.lean)):

```lean
theorem FreyPackage.of_counterexample
    (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p) :
    Nonempty FreyPackage
```

Note what this does **not** say: not "every counterexample is normalized" — a
hypothetical counterexample with $a \equiv 1 \pmod 4$ or with
$\gcd(a, b) > 1$ would not itself be a Frey package. It says: *from* an
arbitrary counterexample we can *manufacture* a normalized one. That is all
"without loss of generality" ever means, and the Lean statement makes it
honest: the conclusion is an existence claim (`Nonempty`), and the proof is an
explicit construction.

A `FreyPackage`
([Def_FLTPrelim_FreyPackage.lean, lines 17–38](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_FreyPackage.lean);
[annotated doc page](http://htmlpreview.github.io/?https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/html/def/FLTPrelim_FreyPackage.html))
bundles:

- nonzero **integers** $a, b, c$ — signs allowed, the fields are `≠ 0`, not `> 0`;
- a prime $p \ge 5$ and the equation $a^p + b^p = c^p$;
- the normalization: $\gcd(a,b) = 1$, $a \equiv 3 \pmod 4$, $b \equiv 0 \pmod 2$.

## 2. Where this sits in the proof

The chain from the headline statement down to this step
([route §1](https://github.com/anthropics/fermats-last-theorem/blob/main/html/route/s1.html),
viewable via
[previewer](http://htmlpreview.github.io/?https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/html/route/s1.html)):

1. `fermat_last_theorem` (over ℕ, any $n \ge 3$) is one call to
   `FLT.fermatLastTheorem : FermatLastTheorem`
   ([Thm_fermat_last_theorem.lean, line 128](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_fermat_last_theorem.lean)).
2. That applies Mathlib's `FermatLastTheorem.of_odd_primes`
   ([Mathlib/NumberTheory/FLT/Four.lean, line 276, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/FLT/Four.lean)):
   every $n \ge 3$ is divisible by 4 or by an odd prime; exponent 4 is settled
   (`fermatLastTheoremFour`), and FLT descends along divisibility of exponents
   (`FermatLastTheoremWith.mono`). So only odd prime exponents remain
   ([S_FLT_fermatLastTheorem.lean, lines 130–139](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_FLT_fermatLastTheorem.lean)).
   Odd primes below 5 are just $p = 3$, settled by Mathlib's
   `fermatLastTheoremThree`; the `interval_cases` branches $p = 2, 4$ are
   discharged by `decide` as not-odd / not-prime.
3. For $p \ge 5$,
   [S_FreyPackage_fermatLastTheoremFor_of_five_le.lean, lines 131–135](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean):

   ```lean
   rw [fermatLastTheoremFor_iff_int]
   intro a b c ha hb hc heq
   obtain ⟨P⟩ := FreyPackage.of_counterexample a b c ha hb hc p pp hp5 heq
   exact P.no_frey_package
   ```

   The first line is where **"a, b, c can be negative"** enters: Mathlib's
   `fermatLastTheoremFor_iff_int`
   ([Mathlib/NumberTheory/FLT/Basic.lean, line 148, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/FLT/Basic.lean))
   says the ℕ-statement is *equivalent* to the ℤ-statement (for even exponents
   powers forget signs; for odd exponents signs can always be shuffled to the
   right-hand side). We pass to the integers because the normalization needs
   the freedom to negate. The last two lines are the whole logical structure:
   any counterexample yields a Frey package (`of_counterexample`), and no Frey
   package exists (`no_frey_package` — the deep end: irreducibility, modularity,
   level lowering to $\Gamma_0(2)$, and the vanishing of weight-2 cusp forms of
   level 2; see
   [route §2](https://github.com/anthropics/fermats-last-theorem/blob/main/html/route/s2.html)).

## 3. Why these normalizing conditions (and not others)

The conditions are dictated by the Frey curve defined in the same file
(lines 83–95), the integral Weierstrass model

$$E_P:\ y^2 + xy = x^3 + \frac{b^p - 1 - a^p}{4}\x^2 - \frac{a^p b^p}{16}\x$$

an integral model of $y^2 = x(x - a^p)(x + b^p)$. For the coefficients to be
*integers*:

- $4 \mid b^p - 1 - a^p$: with $b$ even, $b^p \equiv 0 \pmod 4$ (already
  $p \ge 2$ suffices), so we need $a^p \equiv -1 \pmod 4$. For odd $a$ and odd
  $p$ one has $a^p \equiv a \pmod 4$, i.e. we need $a \equiv 3 \pmod 4$.
  **The case $a \equiv 1 \pmod 4$ is precisely the one that breaks integrality**
  — that is why the sign-flip step below must exist.
- $16 \mid a^p b^p$: with $b$ even, $2^p \mid b^p$, and $p \ge 5$ gives
  $32 \mid b^p$, more than enough. (For $p = 3$ this model would not be
  integral in general — one arithmetic reason $p = 3$ is handled separately.)

The annotated doc page notes the divisions "are exact under the normalisation
hypotheses, but the definition itself does not record this" — exactness is this
congruence computation, and it is used later when the 2-adic properties of
$E_P$ matter (semistability, conductor; route §2).

## 4. The toolkit: symmetries of the equation for odd p

Since $p$ is odd, $(-x)^p = -x^p$, so $a^p + b^p = c^p$ can be rewritten in the
symmetric form $a^p + b^p + (-c)^p = 0$. Hence all of the following send
solutions to solutions:

- **(swap)** $(a, b, c) \mapsto (b, a, c)$;
- **(negate)** $(a, b, c) \mapsto (-a, -b, -c)$;
- **(rotate)** $(a, b, c) \mapsto (a, -c, -b)$ — check:
  $a^p + (-c)^p = a^p - c^p = -b^p = (-b)^p$.

One lemma makes the symmetries respect coprimality
([Def_FLTPrelim_FreyPackage.lean, lines 49–67](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_FreyPackage.lean)):
given the equation and $p > 0$, $\gcd(a,b) = \gcd(a,c)$ — any common divisor of
two of $a, b, c$ divides the third through the equation. So under $\gcd(a,b)=1$
the triple is *pairwise* coprime, and swap/negate/rotate all preserve that.

## 5. The four steps of `of_counterexample`

The proof is
[S_FreyPackage_of_counterexample.lean, lines 12–66](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_FreyPackage_of_counterexample.lean),
three staged `have`s, each producing a better triple, then assembly.

**Step 1 — make $\gcd(a,b) = 1$** (lines 17–29).
Let $d = \gcd(a,b) > 0$ and write $a = d a'$, $b = d b'$ with
$\gcd(a', b') = 1$ (Mathlib's `Int.exists_gcd_one'`). Substituting,
$d^p(a'^p + b'^p) = c^p$, so $d^p \mid c^p$, hence $d \mid c$
(`Int.pow_dvd_pow_iff`, using $p \ne 0$); write $c = d c'$ and cancel the
nonzero $d^p$. Since $d > 0$, the signs of $a, b, c$ are untouched.

**Step 2 — make $b$ even** (lines 31–45), i.e. "WLOG $a, c$ odd, $b$ even".
Parity bookkeeping modulo 2: pairwise coprimality forbids *two* of $a, b, c$
being even, and reducing the equation mod 2 forbids *none* being even
($1 + 1 \equiv 0 \not\equiv 1$). So **exactly one of $a, b, c$ is even**, and we
move it into the $b$-slot:

- $b$ even: keep $(a, b, c)$ (line 35);
- $a$ even: swap to $(b, a, c)$ (line 37);
- $c$ even (i.e. $a, b$ both odd): rotate to $(a, -c, -b)$ (lines 39–45).
  Here $-c$ is even by `Int.even_pow` ($c^p = a^p + b^p$ is even, so $c$ is),
  and coprimality survives by the §4 lemma:
  $\gcd(a, -c) = \gcd(a, c) = \gcd(a, b) = 1$.

Afterwards $a$ is odd (it is coprime to the even $b$) and $c$ is odd
($c^p = a^p + b^p = \text{odd} + \text{even}$). Lean never states "$a, c$ odd"
as a separate fact — it falls out of the construction, and only the part that
is needed next ($a \not\equiv 0, 2 \pmod 4$) is re-derived in step 3.

**Step 3 — make $a \equiv 3 \pmod 4$** (lines 47–59), i.e. the
"$b^p \equiv 0 \pmod 4$, hence $a \equiv c \pmod 4$; if $a \equiv c \equiv 1$,
negate" step. First the key congruence, which the Lean proof uses but does not
isolate as a lemma:

> $b$ even and $p \ge 5$ give $b^p \equiv 0 \pmod{2^p}$, in particular
> $b^p \equiv 0 \pmod 4$. For odd $x$ and odd $p$,
> $x^p - x = x\bigl((x^2)^{\frac{p-1}{2}} - 1\bigr) \equiv 0 \pmod 4$ since
> $x^2 \equiv 1 \pmod 4$; so $x^p \equiv x \pmod 4$. Reducing the equation
> mod 4 therefore gives $a \equiv a^p \equiv c^p \equiv c \pmod 4$.

So $a, c$ are odd with $a \equiv c \pmod 4$, leaving two cases, which the proof
runs via `mod_cases a_mod : a % 4` (the cases $0, 2$ are killed by the local
lemma `a_odd'`, lines 50–52: $2 \mid a$ would contradict $\gcd(a,b) = 1$ as
$b$ is even):

- $a \equiv 1 \pmod 4$: negate everything, $(-a, -b, -c)$ (lines 55–57). The
  equation survives (negate, §4), $b$ stays even (`eb.neg`), the gcd survives
  (`Int.neg_gcd`, `Int.gcd_neg`), and $-a \equiv -1 \equiv 3 \pmod 4$
  (`a_mod.neg`). Then also $-c \equiv 3 \pmod 4$, since $a \equiv c$.
- $a \equiv 3 \pmod 4$: keep $(a, b, c)$ (line 59).

Note the division of labor: the package records only $a \equiv 3 \pmod 4$
(field `ha4`); the companion $c \equiv 3 \pmod 4$ follows mathematically from
$a \equiv c \pmod 4$ but is never needed downstream, so the formalization never
proves it.

**Step 4 — assemble the structure** (lines 61–66). The remaining work is
transport between equivalent formulations: `ha4 : (a : ZMod 4) = 3` from
$a \equiv 3\ [\text{ZMOD } 4]$ via `ZMod.intCast_eq_intCast_iff`;
`hb2 : (b : ZMod 2) = 0` from `Even b` via
`ZMod.intCast_zmod_eq_zero_iff_dvd`; and `hgcdab` by `simp [gcd, ab]`, which
bridges `Int.gcd` (ℕ-valued) and the ℤ-valued `gcd` of the GCD-monoid ℤ that
the structure uses.

## 6. Key-point → code map

| Key point | Mathematical content | Where in the code |
|---|---|---|
| a, b, c can be negative | packages live over ℤ; the ℕ⇔ℤ equivalence is nontrivial and is invoked before normalization | `fermatLastTheoremFor_iff_int`, rewrite at [S_FreyPackage_fermatLastTheoremFor_of_five_le.lean:132](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean); fields `ha0/hb0/hc0 : ≠ 0` in [Def_FLTPrelim_FreyPackage.lean:24–26](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_FreyPackage.lean) |
| WLOG a, c odd, b even | exactly one of a, b, c is even; swap/rotate it into the b-slot | step 2, [S_FreyPackage_of_counterexample.lean:31–45](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_FreyPackage_of_counterexample.lean); coprimality preserved via `gcdab_eq_gcdac`, [Def_FLTPrelim_FreyPackage.lean:49–67](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_FreyPackage.lean) |
| b ≡ 0 mod 4, therefore a ≡ c mod 4 | precisely: $b^p \equiv 0 \pmod 4$ (b even, p ≥ 2; in fact mod 32), and $x^p \equiv x \pmod 4$ for odd x, so $a \equiv c \pmod 4$ | not a standalone lemma — folded into the step-3 case analysis, [S_FreyPackage_of_counterexample.lean:47–59](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_FreyPackage_of_counterexample.lean) |
| a ≡ c ≡ 1 ⇒ negate; WLOG a ≡ c ≡ 3 mod 4 | negation sends x ≡ 1 to −x ≡ 3 mod 4 and preserves the equation (p odd) | the `a ≡ 1` branch, [S_FreyPackage_of_counterexample.lean:55–57](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_FreyPackage_of_counterexample.lean); the package keeps only a ≡ 3 (field `ha4`) |

## 7. Reading the Lean: a mini-glossary

- `have ⟨a, b, c, ...⟩ : ∃ ...` — *refine the goal by replacing the triple*:
  each stage ends with an explicit new triple and proofs of its properties; the
  old variables are shadowed, which is why every stage uses the same names.
- `mod_cases a_mod : a % 4` — splits into the four residue cases with
  hypotheses `a ≡ i [ZMOD 4]`, `i = 0..3`.
- `[ZMOD 4]` is `Int.ModEq`; `(a : ZMod 4) = 3` is the same fact stated as an
  equality in the finite ring, which is the form the structure fields take.
- `p2m_exact_reverting @...solution` in the `Theorems/Thm_*.lean` wrappers is
  the project's proof-management plumbing: the theorem file quotes the proof
  from `P2M/Sol/S_*.lean`, whose `import Theorems.Thm_…` lines are exactly its
  citations (see the repo's PROOF-PATH.md).

## 8. Links

Lean sources (raw; quote line numbers as above):

- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_FreyPackage.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_FreyPackage_of_counterexample.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_FreyPackage_of_counterexample.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_FreyPackage_fermatLastTheoremFor_of_five_le.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_FLT_fermatLastTheorem.lean>

Annotated docs (viewable):

- [Def page: FLTPrelim_FreyPackage](http://htmlpreview.github.io/?https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/html/def/FLTPrelim_FreyPackage.html)
- [Route §1: from the elementary statement to p ≥ 5](http://htmlpreview.github.io/?https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/html/route/s1.html)
- [Route §2: the Frey package and the four-way contradiction](http://htmlpreview.github.io/?https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/html/route/s2.html)

Mathlib v4.33.0:

- [`fermatLastTheoremFor_iff_int`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/FLT/Basic.lean) (line 148)
- [`FermatLastTheorem.of_odd_primes`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/FLT/Four.lean) (line 276)

Background: the file is ported from the Imperial College London FLT project
(header of Def_FLTPrelim_FreyPackage.lean cites blueprint §2.5–2.6); see the
[ICL FLT blueprint](https://imperialcollegelondon.github.io/FLT/blueprint/),
chapter
["First reductions of the problem"](https://imperialcollegelondon.github.io/FLT/blueprint/ch_reductions.html),
for the classical presentation.
