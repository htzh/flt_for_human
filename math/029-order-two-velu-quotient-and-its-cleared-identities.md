# The order-two Vélu quotient: its point map and the cleared identities behind it

**Status.** Mathematical exposition, pinned to the FLT commit `aa2d8b3`. This note
explains the mathematics of the quotient of an elliptic curve by a rational
2-torsion point, the two *cleared identities* (tangent and secant) that make the
quotient's point map a morphism, and how the port's machine-generated
certificates for those identities were replaced by small ones. Readability is as
much the point as build cost: a proof whose term is a monomial list can be checked
by the kernel but not read as mathematics, and §6 states the mathematics the
rewritten proofs now display. The replacement is
port-local work with no counterpart in the pin; §7 records it in detail for both
modules — the build measurement that found the problem, why the certificates cost
what they did, the tangent and secant refactors of `Velu/OrderTwo.lean`, and the
four alignment rewrites of `Velu/OrderTwoMap.lean`. §6 supplies the mathematics of
the second module, whose point map is compared there with the quotient curve's own
group law, and §7.6 is the refactoring of its four heavy certificates: its `.olean`
falls to **60.3 MiB** from 391 MiB — an already-improved figure, the
pin-transcribed module having measured 568 MB. Sizes are the exact measure
throughout; the module and tree wall times quoted in §7 and §8 come from contended
4-thread builds and are read as magnitudes only (§7.1). The pin's giant certificate
is cited only indirectly: its content is a brute-force expansion, and reproducing
it would add nothing. The Lean statements are collected in §9. Method and
measurements: the work note
[../lean/topics/velu/TOPIC-order-two-tangent-direct.md](../lean/topics/velu/TOPIC-order-two-tangent-direct.md).

Companions: [023-velu-isogenies-and-endomorphism-ring.md](023-velu-isogenies-and-endomorphism-ring.md)
(the general Vélu isogeny and its endomorphism ring),
[../notes/lean-build-cost.md](../notes/lean-build-cost.md) (why certificate size
drives build cost).

## 1. The quotient by a rational 2-torsion point

Let $`E`$ be an elliptic curve in Weierstrass form

$$E:\quad y^2 + a_1xy + a_3y \\;=\\; x^3 + a_2x^2 + a_4x + a_6 ,$$

and let $`Q = (x_0,y_0) \in E`$ be a point of order $`2`$. Since $`-Q = Q`$ and
$`-(x,y) = (x, -y-a_1x-a_3)`$, this is the single condition

$$2y_0 + a_1x_0 + a_3 \\;=\\; 0 ,$$

i.e. $`\mathrm{veluGy}\,x_0\,y_0 = 0`$ in the port's vocabulary. Write

$$G \\;:=\\; \mathrm{veluGx}\\,x_0\\,y_0 \\;=\\; 3x_0^2 + 2a_2x_0 + a_4 - a_1y_0 .$$

For $`Q`$ on $`E`$ this is exactly $`\Psi_2`$-related data: $`x_0`$ is a root of the
2-division polynomial, and $`G`$ is Vélu's $`g^x_Q`$.

The quotient $`E' = E/\langle Q\rangle`$ is again an elliptic curve, and with the
normalisation of the pin it is the Weierstrass curve

$$E':\quad a_1' = a_1,\quad a_2' = a_2,\quad a_3' = a_3,\quad
a_4' = a_4 - 5G,\quad a_6' = a_6 - b_2G - 7x_0G ,$$

where $`b_2 = a_1^2+4a_2`$ (`veluQuotient2`). The quotient map, in the
2-torsion case, is the classical single-point Vélu formula

$$\pi(x,y) \\;=\\; \Bigl(x + \frac{G}{x-x_0},\\;\\;
y - \frac{G\\,\bigl(a_1(x-x_0) + y - y_0\bigr)}{(x-x_0)^2}\Bigr),$$

which is `velu2X x₀ y₀ x` and `velu2Y x₀ y₀ x y` in the port.

## 2. What has to be checked

Vélu's construction gives the curve and the formula; the work is to show that
$`\pi`$ is a homomorphism. In coordinates this means that $`\pi`$ respects the
chord-and-tangent group law: if a line meets $`E`$ at $`P_1, P_2`$ and a third
point, then the line through $`\pi(P_1), \pi(P_2)`$ meets $`E'`$ at the image of
that third point. The verification splits into the

* **tangent case** $`P_1 = P_2 = P`$, and the
* **secant case** $`P_1 \ne P_2`$ with $`x_1 \ne x_2`$,

and in each case into an $`x`$-coordinate statement (`addX` compatibility) and a
$`y`$-coordinate statement (`negAddY` compatibility, since negating a point
flips the sign of the $`y`$-coordinate).

After clearing denominators, each of these is a polynomial identity

$$\Phi(x_1,y_1,x_2,y_2,x_0,y_0) \\;=\\; 0$$

on the variety cut out by the two curve equations, the 2-torsion condition and
the slope relation. Two families of them are the subject of this note, one per
module:

* on $`E`$ itself, the two `negAddY` identities —
  `velu2_tangent_negAddY_cleared_identity` and
  `velu2_secant_negAddY_cleared_identity` — proved in `Velu/OrderTwo.lean`; they
  dominate the build, and §3–§5 are their algebra; and
* against the quotient curve's own group law, the four *alignment* identities of
  §6, proved in `Velu/OrderTwoMap.lean`; each of them reduces to the first family.

## 3. Shifted coordinates

Put $`Q`$ at the origin: $`u_i = x_i-x_0`$, $`v_i = y_i-y_0`$, and

$$\beta \\;=\\; a_2+3x_0,\qquad G \\;=\\; \mathrm{veluGx}\\,x_0\\,y_0 .$$

The two curve equations become the single *shifted curve*

$$\text{curve}:\quad v^2 + a_1uv \\;=\\; u^3 + \beta u^2 + Gu ,$$

and the slope relation is linear: if $`m = (v_1-v_2)/(u_1-u_2)`$ is the secant
slope (and in the tangent case $`m`$ is the tangent slope), then

$$m\\,(u_1-u_2) \\;=\\; v_1-v_2 .$$

The third intersection of the line $`v = mu+c`$ with the curve has
$`u`$-parameter

$$u_R \\;=\\; m^2 + a_1m - \beta - u_1 - u_2 ,$$

and the $`y`$-displacement from $`Q`$ to the image of that point is

$$w \\;=\\; v_1 + m\\,(u_R-u_1) .$$

Two Vieta facts control everything. Substituting $`v = mu+c`$ into the shifted
curve gives $`u\bigl(u^2 + (\beta-m^2-a_1m)u - (G-a_1c-2mc)\bigr) = c^2`$-shaped
relations; in particular

* when the line passes through $`Q`$ ($`c = 0`$, the *tangent-from-the-origin*
  case), the two nonzero roots $`u_1,u_2`$ of the chord through $`Q`$ satisfy
  $`u_1u_2 = G`$ and $`u_1+u_2 = m^2+a_1m-\beta`$;
* for a general chord $`c \ne 0`$, the roots $`u_1,u_2,u_R`$ sum to
  $`m^2+a_1m-\beta`$ and their product is $`c^2`$.

## 4. The tangent identity

With $`D = 2v+a_1u`$, $`E = 3u^2+2\beta u+G-a_1v`$ and the tangent slope
$`m_P`$ tied to them by

$$m_P\\,D \\;=\\; E ,$$

the tangent case of the `negAddY` compatibility is

$$T \\;:=\\; uu_R(u-u_R)v - u\bigl((a_1u+v)u_R^2 - (a_1u_R+w)u^2\bigr)
\quad + G\bigl(u_Rv - uw\bigr) \\;=\\; 0 ,$$

where now $`u_R = m_P^2+a_1m_P-\beta-2u`$ and $`w = v+m_P(u_R-u)`$.

Its content is visible once one divides by $`u\,u_R`$ and writes $`m = v/u`$ and
$`m_R = w/u_R`$ for the slopes of the chords from $`Q`$ to $`P`$ and from $`Q`$ to
its double:

$$T \\;=\\; u\\,u_R\Bigl[u^2(a_1+m+m_R) - u\\,u_R\\,(a_1+2m) + G\\,(m-m_R)\Bigr] .$$

This is a *chord–tangent compatibility*: it relates the slope of the chord from
$`Q`$ through $`P`$ to the slope of the chord from $`Q`$ through $`2P`$, using the
product relation $`u_1u_2 = G`$ for chords through the 2-torsion point $`Q`$.

## 5. The secant identity

The secant case has two distinct points and no simplification from $`c = 0`$: the
chord through $`P_1,P_2`$ does not pass through $`Q`$. Write the chord as
$`v = mu+c`$, so that its intercept is
$`c = v_1-mu_1 = v_2-mu_2`$ (the second equality is the slope relation), and with
$`d = u_1-u_2`$, $`u_R = m^2+a_1m-\beta-u_1-u_2`$ and $`w = v_1+m(u_R-u_1) = c+mu_R`$,
the identity is

$$T_{\text{sec}} \\;=\\; u_2u_R(u_2-u_R)v_1
\quad - u_1\bigl((a_1u_2+v_2)u_R^2 - (a_1u_R+w)u_2^2\bigr)
\quad + G\bigl(u_Rv_2 - u_2w\bigr) \\;=\\; 0 .$$

Its content is again Vieta's theorem. Substituting $`v = mu+c`$ into the shifted
curve gives the cubic

$$u^3 - (m^2+a_1m-\beta)u^2 + \bigl(G-c(2m+a_1)\bigr)u - c^2 ,$$

whose roots must be exactly $`u_1,u_2,u_R`$, the three intersections of the chord
with $`E`$. Hence

$$u_1u_2 + u_1u_R + u_2u_R \\;=\\; G - c(2m+a_1),\qquad
u_1u_2u_R \\;=\\; c^2 .$$

The statement factors through those two relations. With
$`\sigma_2 := u_1u_2+u_1u_R+u_2u_R`$,

$$T_{\text{sec}} \\;=\\; (u_2-u_R)\Bigl[c\\,(\sigma_2-G) + (2m+a_1)\\,u_1u_2u_R\Bigr],$$

and the bracket rewrites as
$`c\,(\sigma_2-G+c(2m+a_1)) + (2m+a_1)(u_1u_2u_R-c^2)`$, which the two Vieta
relations kill. Both identities are proved from the shifted curve equations and
the slope relation; nothing else is used. The factorization is a polynomial
identity with $`u_R`$ a *free* variable, so no elimination and no case split on
the characteristic is needed.

## 6. The quotient curve and its point map

The point map $`\pi`$ of §1 has to be shown to be a morphism of curves before it
can be a homomorphism of groups. Three statements do that, and all three are the
arithmetic of §3's shift written out. The first two, §6.1 and §6.2, are the
`Velu/OrderTwo.lean` facts that $`\pi`$ lands on $`E'`$ and that the
discriminants behave; the rest, §6.3–§6.7, are the `Velu/OrderTwoMap.lean`
comparisons of $`\pi`$ with the group law that $`E'`$ itself carries, which the
headline `exists_addMonoidHom_coe_eq_veluPointMap2` needs.

Section 2 fixed the algebraic target: after clearing denominators, "the point map
is a homomorphism" is a polynomial identity on the curve, the 2-torsion condition
and the slope relation, and §4–§5 prove the two `negAddY` instances of it that
dominate the build. The alignment comparisons split exactly as in §2, into the
**tangent** pair `kw_velu2_tanX_align`, `kw_velu2_tanY_negAddY_align` and the
**secant** pair `kw_velu2_secX_align`, `kw_velu2_secY_negAddY_align`, one
$`x`$-statement and one $`y`$-statement each. Every one of the four is again a
cleared polynomial identity in the raw $`x,y,x_0,y_0`$, and every one says the
same geometric thing: the image under $`\pi`$ of a chord-and-tangent configuration
on $`E`$ is the corresponding configuration on $`E'`$. Each therefore reduces to
the shifted facts of §3 together with one of the two identities of §4–§5. Making
them cheap is §7.6's story.

### 6.1 The image of the point map lies on the quotient curve

Before any group law, $`\pi`$ must land on $`E'`$: at
$`(\mathrm{velu2X},\mathrm{velu2Y})`$ the quotient equation holds
(`velu2_map_equation`, through the cleared form `velu2_equation_cleared_four`).
The mathematics is §3's shift, used once. Put $`u = x-x_0`$, $`v = y-y_0`$,
$`G = \mathrm{veluGx}\,x_0\,y_0`$ and $`\beta = a_2+3x_0`$; subtracting the
equation at $`Q`$ from the one at $`P`$ and using $`2y_0+a_1x_0+a_3 = 0`$ leaves
the shifted curve

$$\text{curve}:\quad v^2+a_1uv \\;=\\; u^3+\beta u^2+Gu .$$

The image coordinates are $`X/u^2`$ and $`Y/u^3`$ with
$`X = u^2(x_0+u)+Gu`$ and $`Y = u^3(y_0+v)-Gu(a_1u+v)`$, and clearing the
denominators of the quotient equation by $`u^6`$ leaves

$$4\Bigl(Y^2+a_1uXY+a_3u^3Y\Bigr) \\;=\\;
4\Bigl(X^3+a_2u^2X^2+(a_4-5G)u^4X+(a_6-b_2G-7x_0G)u^6\Bigr).$$

The difference of the two sides is *identically*

$$4u^2(u^2-G)^2\cdot\text{curve} \\;+\\; 4u^6\cdot h_Q
  \\;+\\; \bigl(4a_1u^5G-4u^4(u^2-G)v\bigr)\cdot h_{\text{ord}},$$

where $`h_Q`$ is the curve equation at $`Q`$ — it carries the $`a_6`$ data that
the shifted curve has lost — and $`h_{\text{ord}} = 0`$ is the 2-torsion
condition. Three named factors, each a product of visible ones: the proof *is*
that display, and it is why this declaration reads as the statement it proves
instead of as three unreadable monomial lists.

### 6.2 The discriminant of the quotient

The other two `OrderTwo.lean` statements that dominate the build are the
discriminant side of the same shift. The $`x`$-coordinates of the three 2-torsion
points are the roots of the 2-division cubic
$`\Psi_2(T) = 4T^3+b_2T^2+2b_4T+b_6`$, so at a root $`x_0`$ the cubic is
$`(T-x_0)`$ times

$$4T^2+(b_2+4x_0)T+(2b_4+b_2x_0+4x_0^2),$$

whose discriminant is exactly `velu2QuadDisc x₀`; and the 2-torsion condition
gives $`2\,\mathrm{veluGx}\,x_0\,y_0 = 6x_0^2+b_2x_0+b_4`$. Reading $`\Delta`$ as
the discriminant of $`\Psi_2`$ through that factorization gives, at a 2-torsion
point,

$$W.\Delta \\;=\\; \bigl(\mathrm{veluGx}\\,x_0\\,y_0\bigr)^2
  \cdot \mathrm{velu2QuadDisc}\\,x_0 ,$$

and the same computation for the quotient curve $`W' = E/\langle Q\rangle`$ gives

$$(W').\Delta \\;=\\; \mathrm{veluGx}\\,x_0\\,y_0
  \cdot \bigl(\mathrm{velu2QuadDisc}\\,x_0\bigr)^2 .$$

These are `Delta_eq_veluGx_sq_mul_velu2QuadDisc` and `veluQuotient2_Delta_eq`; the
$`N = 2`$ fibre of the modular polynomial later consumes them as the relation
$`\Delta = g_i^2\,d_i`$. Unlike §6.1 they do *not* compress into a short
certificate — the natural shorter route would divide by 4, which the statements'
`CommRing` does not allow — so their proofs keep the ported certificates with a
comment recording this reading (§7.7).

### 6.3 The secant images are collinear

Let $`P_1,P_2 \in E`$ have $`x_1 \ne x_2`$, and let $`R = (x_A,y_A)`$ be the third
point in which the chord through $`P_1,P_2`$ meets $`E`$, so that $`P_1+P_2 = -R`$.
The group law on $`E'`$ wants $`\pi(P_1)+\pi(P_2) = -\pi(R)`$, and the whole
content of the comparison is that the three images are collinear:

$$(\pi_x(P_2)-\pi_x(P_1))\\,(\pi_y(R)-\pi_y(P_1)) \\;=\\; (\pi_x(R)-\pi_x(P_1))\\,(\pi_y(P_2)-\pi_y(P_1)).$$

With the shifted atoms of §3, $`u_i = x_i-x_0`$, $`v_i = y_i-y_0`$,
$`U = x_A-x_0`$, $`V = y_A-y_0`$, $`G = \mathrm{veluGx}\,x_0\,y_0`$ and

$$Z_i \\;:=\\; v_iu_i^2 - G(a_1u_i+v_i),\qquad Q \\;:=\\; VU^2 - G(a_1U+V),$$

the four differences are single fractions:

$$\pi_x(P_2)-\pi_x(P_1) = \frac{(u_1-u_2)(G-u_1u_2)}{u_1u_2},\qquad
\pi_x(R)-\pi_x(P_1) = \frac{(u_1-U)(G-u_1U)}{u_1U},$$

$$\pi_y(R)-\pi_y(P_1) = \frac{Qu_1^2-Z_1U^2}{U^2u_1^2},\qquad
\pi_y(P_2)-\pi_y(P_1) = \frac{Z_2u_1^2-Z_1u_2^2}{u_1^2u_2^2}.$$

Clearing $`u_1^3u_2^2U^2`$ turns the collinearity into the 30-term polynomial

$$T \\;=\\; u_2\\,(G-u_1u_2)(u_1-u_2)\\,(Qu_1^2-Z_1U^2) \\;-\\; U\\,(u_1-U)(G-u_1U)\\,(Z_2u_1^2-Z_1u_2^2).$$

Two facts kill it, and only two. The first is the secant cleared identity of §5,
read with the third point's parameters free ($`u_R = U`$, $`w = V`$),

$$h_{SIY} \\;=\\; u_2U(u_2-U)v_1 - u_1\bigl((a_1u_2+v_2)U^2-(a_1U+V)u_2^2\bigr) + G\\,(Uv_2-u_2V) \\;=\\; 0 ;$$

the second is the chord relation

$$h_{RY} \\;=\\; (u_1-u_2)(V-v_1) - (v_1-v_2)(U-u_1) \\;=\\; 0 .$$

The certificate is a **4 + 4 monomial** identity,

$$T \\;=\\; G\\,u_1(u_1-U)(u_1-u_2)\\,h_{SIY}
 \\;-\\; U\\,u_1u_2(Uu_1-G)(u_1u_2-G)\\,h_{RY} .$$

This is
[`hColQ`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L889-L940)
in
[`kw_velu2_secY_negAddY_align`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L869-L943):
collinearity of the images is a consequence of the preimage chord facts alone.

### 6.4 The tangent `addX` alignment and $`\Sigma = a_1D+2E`$

For
[`kw_velu2_tanX_align`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L1032-L1072)
the cleared goal is killed by the single input
`velu2_tangent_addX_cleared_identity`, with certificate $`-G\,h_{Npp}`$; the
certificate was already one term, and the statement is short. In the atoms

$$u = x-x_0,\quad D = 2y+a_1x+a_3 = 2v+a_1u,\quad
E = 3x^2+2a_2x+a_4-a_1y = 3u^2+2\beta u+G-a_1v,$$

$$A = a_1^2(x-x_0)+4\bigl(x^2+xx_0+x_0^2+a_2(x+x_0)+a_4-a_1y_0\bigr) = a_1^2u+4(u^2+\beta u+G),$$

the identity is short. Its one algebraic content beyond §4 is a shape fact: the
cleared goal carries $`a_1D+2E`$, while $`h_{Npp}`$ carries

$$\Sigma \\;:=\\; 6x^2+(4a_2+a_1^2)x+2a_4+a_1a_3 .$$

These are the same polynomial,

$$\Sigma \\;=\\; a_1D + 2E ,$$

since
$`a_1D+2E = a_1(2y+a_1x+a_3)+2(3x^2+2a_2x+a_4-a_1y) = 6x^2+(a_1^2+4a_2)x+2a_4+a_1a_3`$
(the $`a_1y`$-terms cancel). Nothing else about this alignment is special: its
cost is entirely in the normalisation, which is §7.6(b)'s story.

### 6.5 The tangent `negAddY` alignment

[`kw_velu2_tanY_negAddY_align`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L1095-L1168)
is the tangent counterpart of §6.3: the two preimage points coincide, the "chord"
is the tangent at $`P`$, and the third intersection is the doubled point, so its
parameters are tied to $`P`$ by the doubling relation. Writing
$`d_2 = x_{2P}-x`$, $`U_2 = x_{2P}-x_0`$,
$`V_d = y-\mathrm{negY}\,x\,y = D`$, and $`h_{SIYt}`$, $`h_{x2P}`$,
$`h_{nAY}`$, $`h_{SI2c}`$ for the four tangent inputs (the tangent cleared
identity of §4, the doubled-point relation, the tangent `negAddY` relation, and
the shifted identity `tanY_SI2c_shifted` of §6.7), it is

$$T_{\text{tanY}} \\;=\\; -G(u^2-G)V_d^3\\,h_{SIYt}
 \quad - G\\,d_2(uU_2-G)A\\,u^2\\,h_{x2P}
 \quad + uV_d^2(u^2-G)(uU_2-G)(uU_2+G)\\,h_{nAY}
 \quad - G\\,d_2(uU_2-G)\\,h_{SI2c} .$$

As in §6.3 the content is that the images of the chord and of its third point are
collinear, and the certificate is a consequence of the preimage relations alone.
The atomisation that makes it cheap is §7.6(c).

### 6.6 The secant `addX` alignment

[`kw_velu2_secX_align`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L825-L868)
is the $`x`$-half of the secant alignment: like §6.3–§6.5 it compares the cleared
point map with the quotient curve's own `addX`, and what remains is a pair of
shifted chord identities —
[`kw_velu2_secX_SI2`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L369-L382)
and
[`kw_velu2_secX_SI3`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L384-L402)
— each of which is itself a small `linear_combination` over the curve equations
and the 2-torsion condition, i.e. over §3 alone. What is special about this one is
not its algebra but its *shape*. The comparison is divided by the difference
$`d = u_1-u_2`$, so it is sound only while $`d`$ is literally the same subterm
throughout, and its certificate — unlike the other three — is syntactic rather
than algebraic; the consequences are §7.6(d).

### 6.7 The `tanY` relation in shifted form

The tangent $`y`$-alignment of §6.5 consumes one further identity,
`kw_velu2_tanY_SI2c`. Its raw statement is a long explicit polynomial; in the
shifted variables of §3 it is 18 $`(u,v)`$-monomials and a **nine-term** multiple
of the shifted curve $`v^2+a_1uv = u^3+\beta u^2+Gu`$. It is therefore again a
Vieta statement of the kind §3 collects, with the shifted curve as its only input.
The helper that holds it is
[`tanY_SI2c_shifted`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L433-L444);
§7.6(e) gives the four `ring` rewrites that put the raw statement into that form.

## 7. From machine-generated certificates to small ones

The pin proves the identities of §4–§5, and the alignments of §6 with them, by
`linear_combination` with certificates written out monomial by monomial — for
the tangent identity a single argument runs to tens of thousands of characters,
and the pin itself needs `maxHeartbeats 16000000` and `maxRecDepth 8000` for it.
The port transcribed those certificates verbatim. Everything in this section
replaces that: it is port-local work with no counterpart in the pin, and it is
what takes `Velu/OrderTwo.lean` from a 36-minute, 276 MB module to a 23-second,
29.3 MiB one (§7.2–§7.5) and `Velu/OrderTwoMap.lean`, the module of §6, from
568 MB to 60.3 MiB (§7.6). Line references are pinned to
[`htzh/flt_for_human@c46cb57`](https://github.com/htzh/flt_for_human/tree/c46cb57),
the commit that landed the `OrderTwoMap` alignment rewrites; `OrderTwo.lean` is
identical between it and the Vieta-secant commit
[`129e571`](https://github.com/htzh/flt_for_human/tree/129e571) it descends from.

### 7.1 The measurement that found the hog

A full tree build at four jobs (`LEAN_NUM_THREADS=4 lake build`) ran in 3290.5 s
wall and rebuilt 596 modules. The per-module ranking it produced had two entries
that no earlier log contained, both of them minutes of wall time in that build:
`FLTForHuman.WeierstrassCurve.Velu.OrderTwo` at 2168 s and
`FLTForHuman.WeierstrassCurve.Velu.OrderTwoMap` at 728 s, against 171 s for the
next module (`WeightOne.Gamma1Basis`). Ranked by `.olean`:

| module | `.olean` |
|---|---:|
| `FLTForHuman.WeierstrassCurve.Velu.OrderTwo` | **263 MB** |
| `FLTForHuman.WeierstrassCurve.Velu.OrderTwoMap` | **568 MB** |
| next (`WeightOne.Gamma1Basis`) | 7.6 MB |

**Reading these numbers.** An `.olean` size is exact and is the measure this note
compares: for a given source the file is byte-identical however many jobs ran.
(The source logs do not always label MB and MiB consistently — `OrderTwo`'s
ported `.olean` appears below as both 263 MB and 276 MB — so sizes are compared
within a measurement, or in bytes, rather than across units.) A wall time is not
exact. It moves with the job count and with contention from any other build on
the same tree. The same module, `OrderTwoMap`, is recorded at 728 s in this
4-thread tree wall and at 1070 s in a later one, while a clean single-module
compile of it — by then already reduced — gives 459 s. The pre-refactor figures
come from one such tree build, so they are quoted here as a magnitude — minutes,
not seconds — rather than as a time to reproduce. The improvement is real and
large; its exact factor is not known to better than that.

`OrderTwoMap` imports `OrderTwo`, so the pair was a serial 48-minute chain inside
a 55-minute build, and the port's 1.1 GB of `.olean` was 831 MB of it. At the
time of the measurement both modules carried the ported certificates of the two
`negAddY` identities. `OrderTwo` also carries three that are still ported today —
`velu2_equation_cleared_four`, `Delta_eq_veluGx_sq_mul_velu2QuadDisc` and
`veluQuotient2_Delta_eq` — and they are now its largest declarations.

### 7.2 Why an explicit certificate costs minutes

`linear_combination` puts its arguments **into the proof term**, and the term is
what the kernel checks and what the `.olean` serialises. On a scratch copy the
cost decomposes as: the port's preprocessing (`rw`, `simp only`, `field_simp`)
3.9 s; `ring1` on the cleared goal alone 71 s, and failing, because the
hypotheses are needed; elaborating *just* the three certificate coefficients over
235 s (timed out). `polyrith` is not an option — it relied on an external service
that has been shut down — and `nlinarith` fails in 4 s. The fix therefore had to
be a different proof, not a better search.

`set_option profiler true` on a 2 kB direct certificate shows where the time
goes: `ring` takes 300 ms, but **typeclass inference takes 19–32 s**. Elaborating
an explicit polynomial that long over a `Field` variable is the cost — every
`*`, `+` and `^` resolves a typeclass instance — not the ring normalisation.
`[CommRing F]` still costs 19 s; `[CommSemiring F]` drops to 5 s but cannot
express subtraction. A certificate of at most twenty terms elaborates in
milliseconds.

The decisive observation is that a private lemma's **statement** costs the same
way: it too is a long explicit polynomial elaborated over `F`. Removing the
certificates is therefore not enough — the big polynomial must also be kept out
of the statements of the helper lemmas. The first secant refactor did the former
and not the latter, which is why it *raised* the module build (see §7.4).

### 7.3 Tangent: one 28,925-character certificate becomes two 19-term ones

Shift the 2-torsion point to the origin as in §3: $`u = x-x_0`$, $`v = y-y_0`$,
$`\beta = a_2+3x_0`$, $`G = \mathrm{veluGx}\,x_0\,y_0`$; the curve becomes
$`v^2+a_1uv = u^3+\beta u^2+Gu`$ and the 2-torsion condition `hord` is consumed.
With $`D = 2v+a_1u`$, $`E = 3u^2+2\beta u+G-a_1v`$ and the tangent slope $`m_P`$
tied to them by $`m_P D = E`$, the first attempt was a single certificate

$$T\cdot D^3 = C_1\cdot\text{curve} + q\cdot g_2 ,$$

with $`C_1`$ 570 characters and $`q`$ an **irreducible** 1,532-character
polynomial. The identity is true, but elaborating it costs the 19–32 s of §7.2,
so it fits no 200,000-heartbeat budget; it was discarded.

The landed proof avoids it with three facts. First,
$`(2m_P+a_1)\cdot D = F + 2g_2`$ where $`F := 2E+a_1D`$ and $`g_2 := m_P D - E`$;
since $`D \ne 0`$ (it is $`y-\mathrm{negY}\,x\,y`$, nonzero by the theorem's
hypothesis together with `hord`), $`F \ne 0`$ is equivalent to $`2m_P+a_1 \ne 0`$.
Second, in the branch $`F \ne 0`$ a single certificate, with a 12-term $`B`$, a
6-term $`S`$ and $`u_R = m_P^2+a_1m_P-\beta-2u`$,

$$T\\,(2m_P+a_1) = -(u-u_R)\bigl((2m_P+a_1)^2\cdot\text{curve} + S\cdot g_2\bigr) + B\cdot g_2 ,$$

gives $`T(2m_P+a_1) = 0`$ and hence $`T = 0`$. Third, in the branch $`F = 0`$
(where $`2m_P+a_1 = 0`$) the integer certificate

$$2^5\\,T = P_1F + 2Q\\,(2m_P+a_1)$$

does it, with $`P_1`$ of 4 terms and $`Q`$ of 19: if $`2 = 0`$ then
$`F = a_1D \ne 0`$, contradicting the branch, so $`2 \ne 0`$ and $`2^5T = 0`$
give $`T = 0`$. The powers of two clear the halves of
the elimination, so no division is introduced and the argument is valid in every
characteristic. The largest polynomial anywhere in the proof has 19 terms. In
Lean the core is
[`velu_tangent_core`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L433-L475)
and the public theorem
[`velu2_tangent_negAddY_cleared_identity`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L477-L518).
The tangent `addX` identity was handled the same way a little earlier, through
the three-hypothesis assembler
[`velu2TangentAddX_assemble`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L279-L282),
whose certificates are of a few terms. With the tangent `negAddY` proof alone the
module already built in **55 s** with a **68 MB** `.olean` (from 2168 s / 276 MB);
that is the baseline the secant work started from.

### 7.4 Secant: three branches, then Vieta

The secant case was first refactored along the lines of the tangent one, in
shifted coordinates and with a split on $`A := d(a_1+2m)`$, $`d = u_1-u_2`$:

* branch $`A \ne 0`$: $`d\,A\,T = \alpha_1c_1+\alpha_2c_2+\alpha_3g_2`$ with 9-,
  9- and 23-term $`\alpha`$;
* branch $`A = 0`$, $`2 \ne 0`$: $`32\,d\,T^{(s)} = 4B\,P_2 + M(2m+a_1)`$ after
  reducing $`v_2`$;
* characteristic $`2`$ (where $`A = d\,a_1`$, so the remaining case is
  $`a_1 = 0`$): the mod-2 certificate
  $`d\,T = \mu_0g_2+\mu_2\hat R+2E+a_1F`$, whose essential factor is the unit
  $`d = u_1-u_2 \ne 0`$.

That is a genuine theorem about the shifted relations — without the $`d`$ factor
the mod-2 reduction of $`T`$ is *not* in the polynomial ideal generated by them
(a Gröbner reduction needs a non-unit denominator) — and it
shrank the certificate text 14,355 → 7,066 characters and the proof term
40.4 → 15.3 MB. But the module build went *up*, 55 → 69 s: the proof had nine
private lemmas (`secant_branchA`, `secant_T_sub`, `secant_L_eq`, `secant_degen_key`,
`secant_degen`, `secant_c2s_zero`, `secant_Rhat_zero`, `secant_char2_key`,
`secant_char2`), and the several that restated the expanded $`T_{\text{sec}}`$ of
§5 dominated their small certificates. This is exactly the statement cost of §7.2.

The Vieta proof of §5 removes the elimination entirely, and with it the case
split: it is two private lemmas,
[`secant_factor`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L335-L342)
(the factorization, a ring identity with $`u_R`$ a free variable) and
[`velu_secant_core`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L345-L384).
The public statement
[`velu2_secant_negAddY_cleared_identity`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L386-L424)
is unchanged. The case split, in hindsight, was an artefact of eliminating
$`v_1`$ first: that is what singled out the degenerate locus $`2m+a_1 = 0`$ and
its characteristic-$`2`$ corner.

### 7.5 How the new proofs were found

The techniques that produced §7.3, §7.4 and §7.6, roughly in the order they
mattered:

1. **Move to shifted coordinates first.** Statements, hypotheses and multipliers
   all become short, and the underlying algebra becomes visible. The ported
   certificates act on raw differences in $`x,y,x_0,y_0`$, so even a small *text*
   expands to large *terms* — and the terms, not the text, are what the kernel
   and the elaborator pay for.
2. **Ask what the identity means geometrically before searching.** Both `negAddY`
   identities are Vieta statements about a line meeting the curve: the tangent
   one is "the chord through $`Q`$ has $`u_1u_2 = G`$", the secant one is "the
   chord's cubic has $`u_1,u_2,u_R`$ as its roots". That suggested the exact
   factorizations the Lean proof then certifies, and it is what collapsed the
   secant three-branch proof into a short, branch-free argument.
3. **Find small certificates with a CAS, but watch what the CAS optimises.** For
   the tangent case the elimination $`v \mapsto m_P`$ was carried out by hand and
   re-checked with `sympy`. For the secant case a Gröbner basis of
   $`(c_1,c_2,sl)`$ over the rational-function field showed that $`T`$ reduces
   with the single denominator
   $`D_0' = 4G+(a_1^2+4\beta)(u_1+u_2)+4(u_1^2+u_1u_2+u_2^2)`$, and the resultant
   $`\mathrm{Res}_{v_1}(c_1,c_2^s) = d^2E`$ exposed exactly where the elimination
   degenerates — the locus $`2m+a_1 = 0`$. That diagnosed the branch structure;
   the final proof came not from the Gröbner basis but from recognising the
   cubic.
4. **Keep every certificate at twenty terms or fewer.** At that size elaboration
   is milliseconds, the port's global cap of 4,000,000 heartbeats is never
   approached, and a local `maxHeartbeats 200000` can serve as a regression
   guard.
5. **Keep the big polynomial out of helper statements when it is the problem.**
   `velu_secant_core` states its conclusion with `let`-bound $`u_R, v_R`$, and
   `secant_factor` keeps $`u_R`$ free; neither has the expanded
   $`T_{\text{sec}}`$ of §5 in its type. The tangent core can afford an explicit
   statement because its polynomial is short, but the secant statement of §5 is
   not.
6. **Check the algebra before writing Lean, and measure after.** Each identity is
   re-derived from scratch by `tools/deps/warnings/velu_refactor_check.py`
   (tangent) and `velu_secant_check.py` (secant). Builds are measured per module;
   prefix compiles with `lean -o` attribute a module's size to individual
   declarations; and `set_option profiler true` reports the typeclass-inference
   total, which was the metric that mattered (62.9 s → 5.4 s across the secant
   pass).
7. **Read the residual, and normalise shape before atomising.** Replacing the
   `linear_combination` normaliser by `(norm := skip)` and printing the goal
   shows exactly what `ring` must prove; when a coordinate change makes that
   residual nonzero, factoring it in a CAS names the relation the change has
   severed — for the tangent `addX` identity, $`\Sigma = a_1D+2E`$ of §6.4.
   Atomising a compound is sound only if *every* occurrence of it is the same
   subterm: one and the same factor written $`\Sigma`$ in a hypothesis and
   $`a_1D+2E`$ in the goal is enough to break the substitution.

### 7.6 `Velu/OrderTwoMap.lean`: the four alignment certificates

The mathematics of the four alignment statements is §6; this is how they were made
cheap. Isolating the module's declarations (all theorem bodies replaced by `sorry`
except one, so that a single compile's `.olean` increment is one declaration's
proof term) shows that its whole 391 MiB is concentrated in four declarations. That
391 MiB is **not** the pin's starting point: the pin-transcribed module measured
568 MB (§7.1), and two of the rewrites below — `kw_velu2_secX_align` in (d) and
`kw_velu2_tanY_SI2c` in (e) — had already landed when the isolation was taken:

| declaration | `.olean` |
|---|---:|
| `kw_velu2_tanX_align` | 242.1 MB |
| `kw_velu2_tanY_negAddY_align` | 71.7 MB |
| `kw_velu2_secY_negAddY_align` | 67.9 MB |
| `kw_velu2_secX_align` | 15.1 MB |
| everything else | $`\le 2.3`$ MB |

Every one of those costs is in the final `linear_combination`: for `tanX_align`
the whole `rw`/`simp`/`field_simp` setup is 0.6 MB and the single
`linear_combination -G·hNpp` is the other 242 MB. The certificate *text* is not
the problem; the problem is `ring` normalising the residual identity over the raw
presentation. The statements of §6 in shifted coordinates are short, and the four
rewrites below are their shifted presentations. The residual that `ring` must
close is read off directly with `linear_combination (norm := skip)` plus
`trace_state`; when it does not vanish, factoring it in a CAS names the relation
the coordinate change has severed (this is how the $`\Sigma-a_1D-2E`$ residual of
(b) was found).

**(a) `kw_velu2_secY_negAddY_align`.** The collinearity of §6.3 is certified by
[`hColQ`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L889-L940):
factoring the four point-map differences into the single fractions of §6.3 makes
`field_simp` produce exactly $`T`$, so the **4 + 4 monomial** certificate of §6.3
applies. The ported certificate used three terms, its middle coefficient running
to some seventy monomials, and listed the `addX` relation $`h_{RA}`$ as a third
input, which the identity does not need.

**(b) `kw_velu2_tanX_align`.** The certificate of §6.4 is already one term and the
goal is short; what costs is the normalisation. Atomising it is sound only if
$`\Sigma`$ and $`a_1D+2E`$ are the *same subterm* everywhere: if $`D,E`$ are
generalised before $`\Sigma`$ is rewritten, the residual is a nonzero multiple of
$`\Sigma-a_1D-2E`$, because one and the same factor is written $`\Sigma`$ there and
$`a_1D+2E`$ in the goal. Rewriting $`\Sigma`$ into $`a_1D+2E`$ as a `ring` identity,
and only then generalising $`A,D,E,G,u`$ *after* `simp only [velu2X, …]` has
exposed them, makes the residual vanish and drops the declaration from 242 MB to
about 1 MB. The order matters: generalising
$`\mathrm{veluGx}\,x_0\,y_0`$ *before* unfolding `velu2X`/`velu2Y` leaves the
freshly created occurrences raw, and the residual is nonzero again.

**(c) `kw_velu2_tanY_negAddY_align`.** The four-term certificate of §6.5 is
already small, but its atoms are not all free: only $`A,E,G`$ are generalised
(again after the `velu2X`/`velu2Y` unfolding), while $`u`$, $`d_2`$, $`U_2`$,
$`V_d`$ stay raw. Generalising those would sever the relations tying them to
$`x,x_0,x_{2P}`$ and the `set`-bound $`x_{2P},nAY`$, and the residual would no
longer be an identity in the free atoms. The declaration falls from 71.7 MB to
about 22 MB.

**(d) `kw_velu2_secX_align`.** The certificate is genuinely *syntactic*, for the
shape reason of §6.6: it verifies only while $`x_1-x_0`$, $`x_2-x_0`$,
$`x_1-x_2`$ and $`\mathrm{veluGx}\,x_0\,y_0`$ are the literal subterms, which is
why atomising the goal (or `set`ting the atoms as local definitions, which `ring`
then unfolds) either fails the ring check or stays slow. `generalize … at *` names
the four subterms $`u_1,u_2,d,G`$ in the goal *and* in the pin's `SI2`/`SI3`
hypotheses, at the cost of dropping the definitional relation $`d = u_1-u_2`$; a
port-local `hrel : d = u₁-u₂` restores it, and the certificate gains a third term
whose coefficient is a 208-monomial polynomial. That takes the declaration from
$`\gt 150`$ s to about 10 s, and leaves 15.1 MB — the largest of the four now.

**(e) `kw_velu2_tanY_SI2c`.** This is the direct case: a 4.8 kB raw-monomial
certificate, 15.9 MB and about 11 s of the module on its own. The shifted identity
of §6.7 replaces it, by the technique of §7.3: a port-local helper
[`tanY_SI2c_shifted`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L433-L444)
holds it, and four short `ring` rewrites —
$`2y+a_1x+a_3 = 2v+a_1u`$ (from `hord`), $`3x^2+2a_2x+a_4-a_1y = E`$,
$`a_1^2(x-x_0)+4(x^2+xx_0+x_0^2+\cdots) = a_1^2u+4(u^2+\beta u+G)`$ and
$`a_2+2x+x_0 = \beta+2u`$ — put the raw statement into that form, at which point
the helper applies definitionally. The declaration went 15.89 MB / 15.1 s to
**1.21 MB / ~1.3 s**.

**Result.** With (a)–(e) landed, `Velu/OrderTwoMap.lean` holds a **60.3 MiB**
(63,207,200 B) `.olean` and a contended `lake build` of it reports 49 s
(4-thread wall; §7.1). The 391.2 MiB / 459 s it started from is **not** the
pin's figure (§7.1): the pin-transcribed module measured 568 MB, and the
`secX_align` and `tanY_SI2c` rewrites of §7.6(d)–(e) had already landed before
that starting measurement. The remaining weight is `kw_velu2_secX_align`
(15.1 MB), `kw_velu2_tan_quotSlope_eq` (9.6 MB) and
`kw_velu2_tanY_negAddY_align` (~22 MB).

### 7.7 The last three certificates of `OrderTwo.lean`

Isolating `Velu/OrderTwo.lean`'s declarations puts the residual 29.3 MiB in three
of them: `velu2_equation_cleared_four` (14.9 MiB), `veluQuotient2_Delta_eq`
(4.8 MiB) and `Delta_eq_veluGx_sq_mul_velu2QuadDisc` (1.7 MiB), all still
carrying ported monomial certificates. The first is now §6.1's display: a named
shifted-curve hypothesis `hC`, obtained from `hP - hQ + (y-y₀)·hgy`, and three
factored terms. Its proof term falls 14.9 → 12.6 MiB and the module's `.olean`
29.28 → 26.98 MiB (28,287,888 B), but the point is readability, not the
megabytes: `ring` still normalises the same three-variable identity, so size
follows a change of coordinates, not certificate editing (as in §7.3–§7.4).
The other two are §6.2's factorization; they keep their certificates, with a
`-- Reading.` comment, because the compact route needs a division by 4 that the
statements' `CommRing` does not have. The three declarations still account for
~19 MiB of the module, and the obstruction — not a smaller certificate — is the
recorded outcome. Certificates and measurements:
[../lean/topics/velu/TOPIC-order-two-tangent-direct.md](../lean/topics/velu/TOPIC-order-two-tangent-direct.md)
§10.

## 8. What this bought

Measured on `FLTForHuman.WeierstrassCurve.Velu.OrderTwo` (the module holding both
identities), 4 threaded, `lake build`:

| | ported | branch certificate | Vieta proof |
|---|---:|---:|---:|
| tangent certificate (text) | 28,925 chars in one argument | 19 terms | 19 terms |
| secant certificate (text) | 14,355 chars | 7,066 chars | two short identities |
| secant proof term | 40.4 MB | 15.3 MB | well under 1 MB |
| `OrderTwo.olean` | 276 MB | 45.8 MB | **29.3 MiB** (30,697,960 B) |

The `.olean` row is the comparison to trust; the module builds behind it — 2168 s
for the ported certificate, 69 s for the three-branch refactor, 23 s for the
Vieta proof — are contended 4-thread wall times and are quoted only to say that a
minutes-long module became a seconds-long one (§7.1). The ported figure in
particular is one tree build, never an idle-machine measurement: the improvement
is real, but the baseline is a magnitude, not a number. A later rewrite of the
module's last three certificates (§7.7) brings `OrderTwo.olean` to **27.0 MiB**
(28,287,888 B).

The earlier three-branch secant refactor is the middle column: it shrank the proof
term $`2.6\times`$ yet pushed the module build *up* (55 s → 69 s), because nine
private lemmas each restated the expanded $`T_{\text{sec}}`$. The Vieta proof
replaces all of them by two short-statement lemmas (`secant_factor`,
`velu_secant_core`), and the module's typeclass inference fell from 62.9 s to
5.4 s (profiler, single-threaded `lake env lean`: 60.8 s → 16.6 s).

The residual is no longer the secant identity. Isolating the module's
declarations attributes it to `velu2_equation_cleared_four` (14.9 MiB before
§7.7's rewrite, 12.6 MiB after), `veluQuotient2_Delta_eq` (4.8 MiB) and
`Delta_eq_veluGx_sq_mul_velu2QuadDisc` (1.7 MiB). The first is §6.1's three
factored terms; the other two are §6.2's discriminant factorization, and their
certificates stay.

`Velu/OrderTwoMap.lean` carried four heavy certificates of its own, all now
rewritten in the shifted coordinates of §3–§5 (§6, §7.6). Its `.olean` falls from
391.2 MiB to **60.3 MiB** (63,207,200 B) — and the 391.2 MiB is itself the
already-improved figure, the pin-transcribed module having measured 568 MB
(§7.6). `kw_velu2_secX_align` (15.1 MB) is the largest of the four
remaining.

## 9. The Lean statements

Transcribed from the pin, statements unchanged (only proofs rewritten):

* `WeierstrassCurve.velu2_tangent_negAddY_cleared_identity`
  — [OrderTwo.lean](../lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean)
  (pin `Theorems/Thm_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean`;
  body from `P2M/Sol/S_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean`).
* `WeierstrassCurve.velu2_secant_negAddY_cleared_identity` — same file
  (`Theorems/…velu2_secant_negAddY_cleared_identity.lean`).
* The shifted cores are private port-local lemmas: `velu_tangent_core`, and
  `velu_secant_core` with its single helper `secant_factor` (the factorization of
  §5). They are proof-local, so the public surface is unchanged.
* `Velu/OrderTwoMap.lean`'s public headline,
  `WeierstrassCurve.exists_addMonoidHom_coe_eq_veluPointMap2`, is likewise
  unchanged; the four rewritten alignments are private, and their mathematics is
  §6. In the pinned commit
  [`c46cb57`](https://github.com/htzh/flt_for_human/tree/c46cb57):
  [`kw_velu2_secX_align`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L825-L868),
  [`kw_velu2_secY_negAddY_align`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L869-L943)
  with the collinearity lemma `hColQ`
  ([#L889-L940](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L889-L940)),
  [`kw_velu2_tanX_align`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L1032-L1072)
  and
  [`kw_velu2_tanY_negAddY_align`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L1095-L1168);
  the shifted secant-`tanY` helper is
  [`tanY_SI2c_shifted`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L433-L444)
  with [`kw_velu2_tanY_SI2c`](https://github.com/htzh/flt_for_human/blob/c46cb57/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwoMap.lean#L449-L484).
* The one relation introduced for the tangent `addX` atomisation is
  $`\Sigma = a_1D+2E`$ of §6.4, i.e.
  $`6x^2+(4a_2+a_1^2)x+2a_4+a_1a_3 = a_1(2y+a_1x+a_3)+2(3x^2+2a_2x+a_4-a_1y)`$.
* The other three statements of `OrderTwo.lean` are §6.1–§6.2: the cleared
  point-map equation `WeierstrassCurve.velu2_equation_cleared_four` (proof
  rewritten to §6.1's display), and the discriminant factorization
  `Delta_eq_veluGx_sq_mul_velu2QuadDisc` / `veluQuotient2_Delta_eq` (statements
  and certificates unchanged, §7.7). Statements are unaffected throughout.
* Statement faithfulness: `spec/check_flt_statements.py` reports 9792 identical
  statements, with the port-local cores exempted as own-proof declarations.
* The certificate derivations are re-checked from scratch by
  [../tools/deps/warnings/velu_refactor_check.py](../tools/deps/warnings/velu_refactor_check.py)
  and [../tools/deps/warnings/velu_secant_check.py](../tools/deps/warnings/velu_secant_check.py).
