# The order-two Vélu quotient: its point map and the cleared identities behind it

**Status.** Mathematical exposition, pinned to the FLT commit `aa2d8b3`. This note
explains the mathematics of the quotient of an elliptic curve by a rational
2-torsion point, the two *cleared identities* (tangent and secant) that make the
quotient's point map a morphism, and how the port's machine-generated
certificates for those identities were replaced by small ones. That replacement is
port-local work with no counterpart in the pin; §6 records it in detail — the
build measurement that found the problem, why the certificates cost what they did,
the tangent and secant refactors, and the techniques that found the new proofs.
The pin's giant certificate is cited only indirectly: its content is a brute-force
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

## 6. From machine-generated certificates to small ones

The pin proves these identities by `linear_combination` with certificates written
out monomial by monomial — for the tangent identity a single argument runs to
tens of thousands of characters, and the pin itself needs
`maxHeartbeats 16000000` and `maxRecDepth 8000` for it. The port transcribed those
certificates verbatim. Everything in this section replaces that: it is port-local
work with no counterpart in the pin, and it is what takes `Velu/OrderTwo.lean`
from a 36-minute, 276 MB module to a 23-second, 29.3 MiB one. Line references are
pinned to [`htzh/flt_for_human@129e571`](https://github.com/htzh/flt_for_human/tree/129e571),
the commit that landed the Vieta secant proof.

### 6.1 The measurement that found the hog

A full tree build at four jobs (`LEAN_NUM_THREADS=4 lake build`) ran in 3290.5 s
wall and rebuilt 596 modules. The per-module ranking it produced had two entries
that no earlier log contained:

| module | build | `.olean` |
|---|---:|---:|
| `FLTForHuman.WeierstrassCurve.Velu.OrderTwo` | **2168 s** | **263 MB** |
| `FLTForHuman.WeierstrassCurve.Velu.OrderTwoMap` | **728 s** | **568 MB** |
| next (`WeightOne.Gamma1Basis`) | 171 s | 7.6 MB |

`OrderTwoMap` imports `OrderTwo`, so the pair was a serial 48-minute chain inside
a 55-minute build, and the port's 1.1 GB of `.olean` was 831 MB of it. At the
time of the measurement both modules carried the ported certificates of the two
`negAddY` identities. `OrderTwo` also carries three that are still ported today —
`velu2_equation_cleared_four`, `Delta_eq_veluGx_sq_mul_velu2QuadDisc` and
`veluQuotient2_Delta_eq` — and they are now its largest declarations.

### 6.2 Why an explicit certificate costs minutes

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
and not the latter, which is why it *raised* the module build (see §6.4).

### 6.3 Tangent: one 28,925-character certificate becomes two 19-term ones

Shift the 2-torsion point to the origin as in §3: $`u = x-x_0`$, $`v = y-y_0`$,
$`\beta = a_2+3x_0`$, $`G = \mathrm{veluGx}\,x_0\,y_0`$; the curve becomes
$`v^2+a_1uv = u^3+\beta u^2+Gu`$ and the 2-torsion condition `hord` is consumed.
With $`D = 2v+a_1u`$, $`E = 3u^2+2\beta u+G-a_1v`$ and the tangent slope $`m_P`$
tied to them by $`m_P D = E`$, the first attempt was a single certificate

$$T\cdot D^3 = C_1\cdot\text{curve} + q\cdot g_2 ,$$

with $`C_1`$ 570 characters and $`q`$ an **irreducible** 1,532-character
polynomial. The identity is true, but elaborating it costs the 19–32 s of §6.2,
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
[`velu_tangent_core`](https://github.com/htzh/flt_for_human/blob/129e571/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L433-L475)
and the public theorem
[`velu2_tangent_negAddY_cleared_identity`](https://github.com/htzh/flt_for_human/blob/129e571/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L477-L518).
The tangent `addX` identity was handled the same way a little earlier, through
the three-hypothesis assembler
[`velu2TangentAddX_assemble`](https://github.com/htzh/flt_for_human/blob/129e571/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L279-L282),
whose certificates are of a few terms. With the tangent `negAddY` proof alone the
module already built in **55 s** with a **68 MB** `.olean` (from 2168 s / 276 MB);
that is the baseline the secant work started from.

### 6.4 Secant: three branches, then Vieta

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
§5 dominated their small certificates. This is exactly the statement cost of §6.2.

The Vieta proof of §5 removes the elimination entirely, and with it the case
split: it is two private lemmas,
[`secant_factor`](https://github.com/htzh/flt_for_human/blob/129e571/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L335-L342)
(the factorization, a ring identity with $`u_R`$ a free variable) and
[`velu_secant_core`](https://github.com/htzh/flt_for_human/blob/129e571/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L345-L384).
The public statement
[`velu2_secant_negAddY_cleared_identity`](https://github.com/htzh/flt_for_human/blob/129e571/lean/FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L386-L424)
is unchanged. The case split, in hindsight, was an artefact of eliminating
$`v_1`$ first: that is what singled out the degenerate locus $`2m+a_1 = 0`$ and
its characteristic-$`2`$ corner.

### 6.5 How the new proofs were found

The techniques that produced §6.3 and §6.4, roughly in the order they mattered:

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

## 7. What this bought

Measured on `FLTForHuman.WeierstrassCurve.Velu.OrderTwo` (the module holding both
identities), 4 threaded, `lake build`:

| | ported | branch certificate | Vieta proof |
|---|---:|---:|---:|
| tangent certificate (text) | 28,925 chars in one argument | 19 terms | 19 terms |
| secant certificate (text) | 14,355 chars | 7,066 chars | two short identities |
| secant proof term | 40.4 MB | 15.3 MB | well under 1 MB |
| `OrderTwo.olean` | 276 MB | 45.8 MB | **29.3 MiB** (30,697,960 B) |
| module build | 2168 s | 69 s | **23 s** |

The earlier three-branch secant refactor is the middle column: it shrank the proof
term $`2.6\times`$ yet pushed the module build *up* (55 s → 69 s), because nine
private lemmas each restated the expanded $`T_{\text{sec}}`$. The Vieta proof
replaces all of them by two short-statement lemmas (`secant_factor`,
`velu_secant_core`), and the module's typeclass inference fell from 62.9 s to
5.4 s (profiler, single-threaded `lake env lean`: 60.8 s → 16.6 s).

The residual 29.3 MiB is no longer the secant identity. A prefix build attributes
it to `velu2_equation_cleared_four` (≈ 16 MB / 11 s of the module), then
`veluQuotient2_Delta_eq` (≈ 4.7 MB) and
`Delta_eq_veluGx_sq_mul_velu2QuadDisc` (≈ 2.5 MB) — all three still carry their
ported certificates, and are the next candidates for the same treatment.
`Velu/OrderTwoMap.lean` (569 MB, 728 s) similarly carries its own and remains the
tree's hog.

## 8. The Lean statements

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
* Statement faithfulness: `spec/check_flt_statements.py` reports 9791 identical
  statements, with the port-local cores exempted as own-proof declarations.
* The certificate derivations are re-checked from scratch by
  [../tools/deps/warnings/velu_refactor_check.py](../tools/deps/warnings/velu_refactor_check.py)
  and [../tools/deps/warnings/velu_secant_check.py](../tools/deps/warnings/velu_secant_check.py).
