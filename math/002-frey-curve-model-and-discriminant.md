# The Frey curve: the $E_p$ model vs. the original form, and where the discriminant is computed

Companion to [note 001](001-frey-package-wlog.md) (the WLOG normalization).
Here: (1) how the integral model $E_p$ relates to the classical
Frey–Hellegouarch form $Y^2 = X(X - a^p)(X + b^p)$ via $x = X/4$,
$y = (Y - X)/8$; (2) where the discriminant is computed, with the intermediate
algebra expanded. Line numbers refer to
`anthropics/fermats-last-theorem@aa2d8b3` (main, 2026-09-03).

## 1. Two presentations of the same curve

**The original form is prose; only $E_p$ is code.** In the Lean sources the
curve $Y^2 = X(X - a^p)(X + b^p)$ never appears as a `WeierstrassCurve` — it
lives only in documentation ("the standard integral model of
$y^2 = x(x - a^p)(x + b^p)$",
[def page](https://tianyipeng.github.io/fermats-last-theorem/def/FLTPrelim_FreyPackage.html)).
Both Lean incarnations are defined *directly by their five coefficients*:
`FreyPackage.freyCurve` over ℚ and `FreyPackage.freyCurveInt` over ℤ
([Def_FLTPrelim_FreyPackage.lean, lines 83–95](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_FreyPackage.lean)).
Consequently **no change of variables to the original form is formalized
anywhere** — none is needed. The only *explicit* second model in the
`FreyPackage` namespace is `freyCurveInt`, identified with `freyCurve` by
`FreyPackage.freyCurveInt_map : P.freyCurveInt.map (Int.castRingHom ℚ) = P.freyCurve`,
the base change along ℤ ↪ ℚ with the *same* coefficients
([Thm_FreyPackage_freyCurveInt_map.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_freyCurveInt_map.lean);
proof in
[S_FreyPackage_freyCurveInt_map.lean, lines 17–46](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_freyCurveInt_map.lean)).
(Other integral models occur only abstractly, through the existential
`IsIntegralModelOf` discussed below.) The `freyCurveInt_map` proof is also
where the exactness of the integer divisions from note 001
§3 is consumed: casting `a₂` needs `4 ∣ b^p - 1 - a^p` (lines 22–36, using
`2 ∣ b` and `a^p ≡ (−1)^p ≡ −1 mod 4` from `ha4` and `p` odd), casting `a₄`
needs `16 ∣ a^p b^p` (lines 38–45, using `2^4 ∣ b^4 ∣ b^p` from `p ≥ 5`).

**The relationship, as pure algebra.** Start from $E_p$,
$y^2 + xy = x^3 + \frac{b^p - 1 - a^p}{4}x^2 - \frac{a^p b^p}{16}x$, and
substitute

$$X = 4x, \qquad Y = 8y + 4x \qquad\Big(\text{i.e. } x = X/4,\ y = (Y - X)/8\Big).$$

Then $Y^2 = 64y^2 + 64xy + 16x^2 = 64(y^2 + xy) + 16x^2$, and replacing
$64(y^2 + xy)$ by 64 times the right side of $E_p$ gives

$$Y^2 = 64x^3 + 16(b^p - 1 - a^p)x^2 - 4a^p b^p x + 16x^2
= 64x^3 + 16(b^p - a^p)x^2 - 4a^p b^p x.$$

Reading this back in $(X, Y)$ ($64x^3 = X^3$, $16x^2 = X^2$, $4x = X$):

$$Y^2 = X^3 + (b^p - a^p)X^2 - a^p b^p X = X(X - a^p)(X + b^p),$$

using $a^p + b^p = c^p$ nowhere — the factorization is formal:
$(X - a^p)(X + b^p) = X^2 + (b^p - a^p)X - a^p b^p$.
Note where the mysterious $-1$ in $a_2 = (b^p - 1 - a^p)/4$ goes: completing
the square on $y^2 + xy$ contributes an $x^2/4$ that moves to the right side;
the $-1$ is exactly what cancels it ($4a_2 + 1 = b^p - a^p$).

**The isomorphism is over ℚ.** The substitution is an admissible Weierstrass
change of variables $X = u^2 x + r$, $Y = u^3 y + s u^2 x + t$ with
$(u, r, s, t) = (2, 0, 1, 0)$. It is invertible only where $u = 2$ is a unit:
over ℚ (or ℤ[1/2]), **not over ℤ**. That failure of integrality is the whole
point — passing to $E_p$ divides the discriminant by $u^{12} = 2^{12}$
(§3 below), squeezing powers of 2 out of the model; $E_p$ is the
2-adically better integral model. Mathlib has the general machinery
(`WeierstrassCurve.variableChange_Δ : (C • W).Δ = C.u⁻¹ ^ 12 * W.Δ`,
[Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean, line 218, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean)),
and the project states "integral model of a ℚ-curve" in exactly these terms
(`IsIntegralModelOf`, an existential over `VariableChange ℚ`,
[Def_FLTPrelim_Modularity.lean, lines 88–90](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean))
— but the specific change to the roots form is never instantiated for the Frey
curve.

## 2. Where the discriminant is computed

The identity $\Delta = (abc)^{2p}/2^8$ is proved **three times, independently**,
a consequence of the project's architecture (each `Theorems/Thm_*.lean` module
is self-contained: its proof's `import` lines are exactly its citations):

1. `FreyCurve.Δ`,
   [Def_FreyCurve_Basic.lean, lines 9–15](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyCurve_Basic.lean)
   — the definition-module home, alongside the invariants `b₂`, `b₄`, `c₄`,
   `c₄'` and the `IsElliptic` instance (lines 18–39).
2. `FreyPackage.freyCurve_discriminant`,
   [Thm_FreyPackage_freyCurve_discriminant.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_freyCurve_discriminant.lean)
   + [S_FreyPackage_freyCurve_discriminant.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_freyCurve_discriminant.lean)
   — the citation-graph home; its proof does **not** import
   `Def_FreyCurve_Basic` but recomputes via a `key` identity + `ring`.
3. `FreyArith.freyCurve_Δ`,
   [S_FreyPackage_freyCurveInt_map.lean, lines 48–55](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_freyCurveInt_map.lean)
   — a local helper used to derive the **integral** version
   `FreyArith.freyCurveInt_Δ_mul : (freyCurveInt P).Δ * 2 ^ 8 = (P.a * P.b * P.c) ^ (2 * P.p)`
   (lines 105–117), by injectivity of ℤ ↪ ℚ through `freyCurveInt_map`. The
   same file derives `freyCurveInt_c₄` (lines 99–103),
   `not_dvd_c₄Int` (71–98), `freyCurveInt_Δ_ne_zero` (119–123),
   `dvd_abc_of_dvd_freyCurveInt_Δ` (125–129) and
   `padicValInt_freyCurveInt_Δ` (131–147).

The generated docs already annotate this well — statement, proof sketch and
context (Frey–Hellegouarch, $\Delta = 2^{-8}(ABC)^2$ with $A = a^p$ etc.):
[thm.html#FreyPackage.freyCurve_discriminant](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/html/thm.html#FreyPackage.freyCurve_discriminant)
([rendered](https://tianyipeng.github.io/fermats-last-theorem/thm.html#FreyPackage.freyCurve_discriminant)),
[def/FreyCurve_Basic.html](https://tianyipeng.github.io/fermats-last-theorem/def/FreyCurve_Basic.html),
and the index entry in
[areas/FreyPackage.html](https://tianyipeng.github.io/fermats-last-theorem/areas/FreyPackage.html)
("Discriminant of the Frey curve: (abc)²ᵖ/2⁸"). We don't repeat that here;
what follows is the algebra the `ring` tactic does silently.

## 3. The computation, expanded

Mathlib's discriminant of a Weierstrass curve $(a_1,\dots,a_6)$ is
$\Delta = -b_2^2 b_8 - 8 b_4^3 - 27 b_6^2 + 9 b_2 b_4 b_6$, where
$b_2 = a_1^2 + 4a_2$, $b_4 = 2a_4 + a_1 a_3$, $b_6 = a_3^2 + 4a_6$,
$b_8 = a_1^2 a_6 + 4 a_2 a_6 - a_1 a_3 a_4 + a_2 a_3^2 - a_4^2$.
For $E_p$ ($a_1 = 1$, $a_3 = a_6 = 0$) write $A = a^p$, $B = b^p$ for brevity:

$$b_2 = 1 + 4a_2 = B - A, \qquad b_4 = 2a_4 = -\frac{AB}{8}, \qquad
b_6 = 0, \qquad b_8 = -a_4^2 = -\frac{(AB)^2}{2^8}.$$

(The first two are
[`FreyCurve.b₂`, `FreyCurve.b₄`](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyCurve_Basic.lean),
lines 26–30.) Since $b_6 = 0$ and $b_8 = -a_4^2$, the four-term formula
collapses:

$$\Delta = -b_2^2 b_8 - 8 b_4^3 = a_4^2 (b_2^2 - 64 a_4).$$

Now the crux — the only step that uses the Fermat relation $a^p + b^p = c^p$:

$$b_2^2 - 64 a_4 = (B - A)^2 + 4AB = (A + B)^2 = (c^p)^2 = c^{2p}.$$

Assembling:

$$\Delta = a_4^2 \cdot c^{2p} = \frac{(AB)^2}{2^8} c^{2p}
= \frac{a^{2p} b^{2p} c^{2p}}{2^8} = \frac{(abc)^{2p}}{2^8}.$$

In the Lean proofs this whole paragraph is mechanized: the theorem proof
rewrites `(abc)^{2p}` to `(a^p)^2 (b^p)^2 (a^p + b^p)^2` via `hFLT` (the
explicit `key` step), then
`simp only [FreyPackage.freyCurve, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]; ring`;
the def-file proof instead goes `trans` + `field_simp` + the same
`simp [← P.hFLT, …]; ring`. Either way `ring` discharges
$(B-A)^2 + 4AB = (A+B)^2$ without comment, which is why the formal proofs look
effortless.

**Cross-check via the transform of §1.** For $Y^2 = \prod (X - r_i)$ the
classical formula is $\Delta = 16 \prod_{i < j} (r_i - r_j)^2$. The roots are
$0, a^p, -b^p$, with differences $\pm a^p$, $\pm b^p$, and
$a^p + b^p = c^p$ — hence $\Delta_{\text{orig}} = 16 (abc)^{2p}$. The change
$(u,r,s,t) = (2,0,1,0)$ divides $\Delta$ by $u^{12} = 2^{12}$:
$16(abc)^{2p} / 2^{12} = (abc)^{2p}/2^8$ ✓. The same scaling checks
$c_4$: the original form has
$c_4 = 16(a^{2p} + a^p b^p + b^{2p})$, and $c_4 \mapsto u^{-4} c_4$ gives
$c_4(E_p) = a^{2p} + a^p b^p + b^{2p}$, matching
[`FreyCurve.c₄`](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyCurve_Basic.lean)
(lines 32–34; `c₄'` rewrites it via the Fermat relation as
$c^{2p} - (ab)^p$). And $j = c_4^3/\Delta$ is isomorphism-invariant:
$j = 2^8 (a^{2p} + a^p b^p + b^{2p})^3 / (abc)^{2p}$ either way.

**Over ℤ.** Same value, but as an integer statement:
`FreyArith.freyCurveInt_Δ_mul` gives $\Delta_{\mathbb Z} \cdot 2^8 = (abc)^{2p}$,
i.e. $\Delta_{\mathbb Z} = (abc)^{2p}/2^8 \in \mathbb{Z}$ — divisibility holds
because $2 \mid b$ implies $2^{2p} \mid b^{2p}$ with $2p \ge 10 > 8$. Note the
direction: the integral identity is *derived from* the rational one (cast to ℚ,
use `freyCurveInt_map` + `freyCurve_Δ`, descend by injectivity), not recomputed.

## 4. What the discriminant is used for

- **Ellipticity**: $\Delta$ is a unit of ℚ because $abc \ne 0$ — the
  `IsElliptic` instance for `freyCurve`
  ([Def_FreyCurve_Basic.lean, lines 18–23](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyCurve_Basic.lean)),
  giving `Δ'` and the $j$-invariant in Mathlib's sense. Over ℤ:
  `FreyPackage.freyCurveInt_discr_ne_zero`.
- **Bad reduction = primes of abc**:
  `FreyPackage.dvd_freyCurveInt_discr_iff : (q : ℤ) ∣ P.freyCurveInt.Δ ↔ (q : ℤ) ∣ P.a * P.b * P.c`,
  and for *every* integral model,
  `FreyPackage.not_isGoodPrimeFor_of_isIntegralModelOf_freyCurve`.
- **Valuations**: for primes $q \ne 2$,
  `padicValInt_freyCurveInt_Δ`: $v_q(\Delta) = 2p \cdot v_q(abc)$; at 2,
  `FreyPackage.padicValInt_two_freyCurveInt_discr`:
  $v_2(\Delta) + 8 = 2p \cdot v_2(abc)$. So $\Delta$ is a perfect $p$-th power
  ($((abc)^2)^p$) up to the factor $2^8$ alone — the 2-adic defect that the
  normalization of note 001 has already minimized, and the arithmetic reason
  the level comes out to $2$ (rather than $1$).
- **Semistability**: `FreyPackage.frey_isSemistableModel : P.freyCurveInt.IsSemistableModel`,
  where `IsSemistableModel W := ∀ p prime, p ∣ W.Δ → ¬ p ∣ W.c₄`
  ([Def_FLTPrelim_Modularity.lean, lines 85–87](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean)).
  The arithmetic input is `FreyArith.not_dvd_c₄Int`
  ([S_FreyPackage_freyCurveInt_map.lean, lines 71–98](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_freyCurveInt_map.lean)):
  if a prime $q \mid abc$ divided $c_4 = a^{2p} + a^p b^p + b^{2p}$, then
  e.g. $q \mid a$ forces $q \mid b^{2p}$ (the other two terms contain $a$),
  contradicting $\gcd(a,b) = 1$; the $q \mid c$ case uses
  $c_4 = c^{2p} - (ab)^p$ (`c₄Int_eq_sub`) and pairwise coprimality
  (`hgcdac`, `hgcdbc` from note 001).

## 5. Links

Lean sources (raw; line numbers as above):

- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FreyCurve_Basic.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_FreyPackage.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_freyCurve_discriminant.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_freyCurve_discriminant.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_freyCurveInt_map.lean>

Annotated docs (viewable):

- [thm.html#FreyPackage.freyCurve_discriminant](https://tianyipeng.github.io/fermats-last-theorem/thm.html#FreyPackage.freyCurve_discriminant)
- [def/FreyCurve_Basic.html](https://tianyipeng.github.io/fermats-last-theorem/def/FreyCurve_Basic.html)
- [def/FLTPrelim_FreyPackage.html](https://tianyipeng.github.io/fermats-last-theorem/def/FLTPrelim_FreyPackage.html)
- [areas/FreyPackage.html](https://tianyipeng.github.io/fermats-last-theorem/areas/FreyPackage.html)

Mathlib v4.33.0:

- [`WeierstrassCurve.variableChange_Δ`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean) (line 218)
