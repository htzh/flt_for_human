# The order-two Vélu quotient: its point map and the cleared identities behind it

**Status.** Mathematical exposition, pinned to the FLT commit `aa2d8b3`. This note
explains the mathematics of the quotient of an elliptic curve by a rational
2-torsion point, the two *cleared identities* (tangent and secant) that make the
quotient's point map a morphism, and how the port's machine-generated
certificates for those identities were replaced by small ones. The pin's giant
certificate is cited only indirectly (§6): its content is a brute-force
expansion, and reproducing it would add nothing. The Lean statements are
collected in §8. Method and measurements: the work note
[../lean/topics/velu/TOPIC-order-two-tangent-direct.md](../lean/topics/velu/TOPIC-order-two-tangent-direct.md).

Companions: [023-velu-isogenies-and-endomorphism-ring.md](023-velu-isogenies-and-endomorphism-ring.md)
(the general Vélu isogeny and its endomorphism ring),
[../notes/lean-build-cost.md](../notes/lean-build-cost.md) (why certificate size
drives build cost).

## 1. The quotient by a rational 2-torsion point

Let $`E`$ be an elliptic curve in Weierstrass form

$$E:\quad y^2 + a_1xy + a_3y \;=\; x^3 + a_2x^2 + a_4x + a_6 ,$$

and let $`Q = (x_0,y_0) \in E`$ be a point of order $`2`$. Since $`-Q = Q`$ and
$`-(x,y) = (x, -y-a_1x-a_3)`$, this is the single condition

$$2y_0 + a_1x_0 + a_3 \;=\; 0 ,$$

i.e. $`\mathrm{veluGy}\,x_0\,y_0 = 0`$ in the port's vocabulary. Write

$$G \;:=\; \mathrm{veluGx}\,x_0\,y_0 \;=\; 3x_0^2 + 2a_2x_0 + a_4 - a_1y_0 .$$

For $`Q`$ on $`E`$ this is exactly $`\Psi_2`$-related data: $`x_0`$ is a root of the
2-division polynomial, and $`G`$ is Vélu's $`g^x_Q`$.

The quotient $`E' = E/\langle Q\rangle`$ is again an elliptic curve, and with the
normalisation of the pin it is the Weierstrass curve

$$E':\quad a_1' = a_1,\quad a_2' = a_2,\quad a_3' = a_3,\quad
a_4' = a_4 - 5G,\quad a_6' = a_6 - b_2G - 7x_0G ,$$

where $`b_2 = a_1^2+4a_2`$ (`veluQuotient2`). The quotient map, in the
2-torsion case, is the classical single-point Vélu formula

$$\pi(x,y) \;=\; \Bigl(x + \frac{G}{x-x_0},\;\;
y - \frac{G\,\bigl(a_1(x-x_0) + y - y_0\bigr)}{(x-x_0)^2}\Bigr),$$

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

$$\Phi(x_1,y_1,x_2,y_2,x_0,y_0) \;=\; 0$$

on the variety cut out by the two curve equations, the 2-torsion condition and
the slope relation. This note is about the two `negAddY` identities —
`velu2_tangent_negAddY_cleared_identity` and
`velu2_secant_negAddY_cleared_identity` — which are the ones that dominate the
build.

## 3. Shifted coordinates

Put $`Q`$ at the origin: $`u_i = x_i-x_0`$, $`v_i = y_i-y_0`$, and

$$\beta \;=\; a_2+3x_0,\qquad G \;=\; \mathrm{veluGx}\,x_0\,y_0 .$$

The two curve equations become the single *shifted curve*

$$\text{curve}:\quad v^2 + a_1uv \;=\; u^3 + \beta u^2 + Gu ,$$

and the slope relation is linear: if $`m = (v_1-v_2)/(u_1-u_2)`$ is the secant
slope (and in the tangent case $`m`$ is the tangent slope), then

$$m\,(u_1-u_2) \;=\; v_1-v_2 .$$

The third intersection of the line $`v = mu+c`$ with the curve has
$`u`$-parameter

$$u_R \;=\; m^2 + a_1m - \beta - u_1 - u_2 ,$$

and the $`y`$-displacement from $`Q`$ to the image of that point is

$$w \;=\; v_1 + m\,(u_R-u_1) .$$

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

$$m_P\,D \;=\; E ,$$

the tangent case of the `negAddY` compatibility is

$$T \;:=\; uu_R(u-u_R)v - u\bigl((a_1u+v)u_R^2 - (a_1u_R+w)u^2\bigr)
\quad + G\bigl(u_Rv - uw\bigr) \;=\; 0 ,$$

where now $`u_R = m_P^2+a_1m_P-\beta-2u`$ and $`w = v+m_P(u_R-u)`$.

Its content is visible once one divides by $`u\,u_R`$ and writes $`m = v/u`$ and
$`m_R = w/u_R`$ for the slopes of the chords from $`Q`$ to $`P`$ and from $`Q`$ to
its double:

$$T \;=\; u\,u_R\Bigl[u^2(a_1+m+m_R) - u\,u_R\,(a_1+2m) + G\,(m-m_R)\Bigr] .$$

This is a *chord–tangent compatibility*: it relates the slope of the chord from
$`Q`$ through $`P`$ to the slope of the chord from $`Q`$ through $`2P`$, using the
product relation $`u_1u_2 = G`$ for chords through the 2-torsion point $`Q`$.

## 5. The secant identity

The secant case has two distinct points and no simplification from $`c = 0`$: the
chord through $`P_1,P_2`$ does not pass through $`Q`$. With
$`d = u_1-u_2`$, $`u_R = m^2+a_1m-\beta-u_1-u_2`$ and $`w = v_1+m(u_R-u_1)`$, the
identity is

$$T_{\text{sec}} \;=\; u_2u_R(u_2-u_R)v_1
\quad - u_1\bigl((a_1u_2+v_2)u_R^2 - (a_1u_R+w)u_2^2\bigr)
\quad + G\bigl(u_Rv_2 - u_2w\bigr) \;=\; 0 .$$

Both identities are proved from the shifted curve equations and the slope
relation; nothing else is used.

## 6. From a machine-generated certificate to small ones

The pin proves these identities by `linear_combination` with certificates written
out monomial by monomial — for the tangent identity a single argument runs to
tens of thousands of characters, and the pin needs `maxHeartbeats 16000000` and
`maxRecDepth 8000` for it. The port transcribed those certificates verbatim,
which is what made the modules `Velu/OrderTwo.lean` and `Velu/OrderTwoMap.lean`
the most expensive files in the tree: the proof term is the certificate, and the
kernel checks it.

The refactor keeps the statements and replaces the certificates. Working in the
shifted coordinates of §3 (where the hypotheses are small and the expressions
short), each identity is certified by a handful of polynomials of tens of terms:

* **tangent**: split on $`F := 2E+a_1D`$. When $`F \ne 0`$,
  $`T(2m_P+a_1) = -(u-u_R)\bigl((2m_P+a_1)^2\,\text{curve} + S\,g_2\bigr) + B\,g_2`$
  (at most 19 terms); when $`F = 0`$ the branch satisfies
  $`2^5T = P_1F + 2Q(2m_P+a_1)`$ (at most 19 terms). Since
  $`(2m_P+a_1)D = F + 2g_2`$ and $`D \ne 0`$, the two branches cover everything,
  in every characteristic.
* **secant**: split on $`A := d(a_1+2m)`$. For $`A \ne 0`$,
  $`d\,A\,T_{\text{sec}} = \alpha_1c_1+\alpha_2c_2+\alpha_3g_2`$; for $`A = 0`$ with
  $`2 \ne 0`$, $`32\,d\,T_{\text{sec}}^{(s)} = 4B\,P_2 + M(2m+a_1)`$ after reducing
  $`v_2`$; and in characteristic $`2`$ (where $`A = d\,a_1`$, so the remaining
  case is $`a_1 = 0`$) the useful certificate is
  $`d\,T_{\text{sec}} = \mu_0g_2 + \mu_2\hat R + 2E + a_1F`$ — here the factor
  $`d = u_1-u_2 \ne 0`$ is essential: without it the mod-2 reduction of
  $`T_{\text{sec}}`$ is *not* in the ideal generated by the shifted relations.

Two lessons worth recording. First, the certificate's *text* shrank only about
twofold, but the *proof term* shrank $`2.6\times`$: the old multipliers act on the
raw hypothesis differences in $`x,y,x_0,y_0`$, so each `ring` verification
expands enormous polynomials, while the shifted multipliers act on short
expressions. Second, the tangent identity reduces in every characteristic, but
the secant one does not: the shift consumes the curve equation at $`Q`$ and the
2-torsion condition, and in characteristic $`2`$ the reduced relation set is
strictly weaker, so that corner genuinely needs the extra $`d`$ factor.

## 7. What this bought

Measured on `FLTForHuman.WeierstrassCurve.Velu.OrderTwo` (the module holding both
identities), 4 threaded, `lake build`:

| | before | after |
|---|---:|---:|
| tangent certificate (text) | 28,925 chars in one argument | 19 terms |
| secant certificate (text) | 14,355 chars | 7,066 chars |
| `OrderTwo.olean` | 276 MB | **45.8 MB** |
| module build | 2168 s | **69 s** |

The secant proof term fell from 40.4 MB to 15.3 MB; the module build time went
*up* slightly (55 s → 69 s) because the refactored proof has more declarations
with large polynomial statements. `Velu/OrderTwoMap.lean` (569 MB, 728 s) carries
its own certificates and is the remaining hog.

## 8. The Lean statements

Transcribed from the pin, statements unchanged (only proofs rewritten):

* `WeierstrassCurve.velu2_tangent_negAddY_cleared_identity`
  — [OrderTwo.lean](../lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean)
  (pin `Theorems/Thm_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean`;
  body from `P2M/Sol/S_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean`).
* `WeierstrassCurve.velu2_secant_negAddY_cleared_identity` — same file
  (`Theorems/…velu2_secant_negAddY_cleared_identity.lean`).
* The shifted cores are private port-local lemmas: `velu_tangent_core`, and
  `velu_secant_core` with its helpers `secant_branchA`, `secant_degen`,
  `secant_char2`, … They are proof-local, so the public surface is unchanged.
* Statement faithfulness: `spec/check_flt_statements.py` reports 9791 identical
  statements, with the port-local cores exempted as own-proof declarations.
* The certificate derivations are re-checked from scratch by
  [../tools/deps/warnings/velu_refactor_check.py](../tools/deps/warnings/velu_refactor_check.py)
  and [../tools/deps/warnings/velu_secant_check.py](../tools/deps/warnings/velu_secant_check.py).
