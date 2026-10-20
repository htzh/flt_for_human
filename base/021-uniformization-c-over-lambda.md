# Uniformization: the isomorphism $`\mathbb{C}/\Lambda \cong E(\mathbb{C})`$

Twenty-first of the `base/` notes. [005](005-cyclic-isogenies-and-level.md) treated a
complex torus as a lattice and read the moduli of $`j`$ off it; that note, and
[007](007-weil-pairing.md) after it, used without proof that the lattice model
$`\mathbb{C}/\Lambda`$ and the Weierstrass model $`E_\Lambda`$ describe the same elliptic
curve. This note proves that fact in the form the pin needs:

> the map $`z \mapsto (\wp(z), \wp'(z)/2)`$ from $`\mathbb{C}`$ to the Weierstrass cubic
> $`E_\Lambda`$ is a surjective group homomorphism with kernel exactly $`\Lambda`$, hence
> descends to an isomorphism of additive groups
> $`\mathbb{C}/\Lambda \cong E_\Lambda(\mathbb{C})`$.

The proof is the pin's `PeriodPair.isUniformization_toPoint`. It is **purely
complex-analytic**: one differential equation, Liouville's theorem, and two algebraic
addition identities. There is no Riemann-surface theory, no modular form and no
$`q`$-expansion in it. That is worth recording, because the other route to the
$`j`$-line in this project
([math/024](../math/024-uniformization-versus-modular-functions.md)) does use modular
forms, and the level-$`N`$ theory
([math/026](../math/026-weierstrass-p-division-values-and-level-n.md)) is built on top of
the theorem proved here.

The mathematics is §1–§10; the Lean map is §11.

## 1. Statement

Let $`\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2 \subset \mathbb{C}`$ with
$`\omega_1, \omega_2`$ $`\mathbb{R}`$-linearly independent. The Weierstrass function and
its derivative are

$$\wp(z) = \frac{1}{z^2} + \sum_{l \in \Lambda \setminus \\{0\\}}
  \left(\frac{1}{(z-l)^2} - \frac{1}{l^2}\right), \qquad
  \wp'(z) = -2 \sum_{l \in \Lambda} \frac{1}{(z-l)^3},$$

and the associated constants are

$$g_2 = 60 \sum_{l \in \Lambda \setminus \\{0\\}} \frac{1}{l^4}, \qquad
  g_3 = 140 \sum_{l \in \Lambda \setminus \\{0\\}} \frac{1}{l^6}.$$

Consider the plane cubic

$$E_\Lambda : \quad y^2 = 4x^3 - g_2 x - g_3,$$

whose discriminant is $`\Delta = g_2^3 - 27g_3^2`$. For a genuine lattice $`\Delta \neq 0`$
(§5), so $`E_\Lambda`$ is a nonsingular cubic, i.e. an elliptic curve with its
chord-and-tangent group law and origin the point at infinity.

Define the **uniformization map**

$$\Phi : \mathbb{C} \longrightarrow E_\Lambda(\mathbb{C}), \qquad
  \Phi(z) = \begin{cases} (\wp(z),\\, \wp'(z)/2), & z \notin \Lambda, \\ 0, & z \in \Lambda, \end{cases}$$

where $`0`$ denotes the origin of $`E_\Lambda`$.

**Theorem (uniformization).** $`\Phi`$ is $`\Lambda`$-periodic, additive,
surjective, and $`\Phi(z) = 0`$ if and only if $`z \in \Lambda`$. Consequently $`\Phi`$
descends to an isomorphism

$$\mathbb{C}/\Lambda \\;\xrightarrow{\ \sim\ }\\; E_\Lambda(\mathbb{C})$$

of additive groups, and it is in fact an isomorphism of complex Lie groups.

Two comments on conventions.

- The factor $`1/2`$ on $`\wp'`$ is the substitution $`(x,y) \mapsto (x, y/2)`$, which
  carries the classical model $`y^2 = 4x^3 - g_2x - g_3`$ to the short Weierstrass model
  $`Y^2 = x^3 - (g_2/4)x - (g_3/4)`$. This is the model the pin uses
  (`PeriodPair.weierstrassCurve` has $`a_4 = -g_2/4`$, $`a_6 = -g_3/4`$), and it is why
  the $`y`$-coordinate in $`\Phi`$ is $`\wp'/2`$ rather than $`\wp'`$.
- The "additive group" structure on $`E_\Lambda(\mathbb{C})`$ is the chord-and-tangent
  law. The whole content of the theorem is that the analytic map $`\Phi`$ matches it:
  surjectivity and the kernel are comparatively cheap once the group law is known, and
  the group law is where the work is (§7).

## 2. The four inputs

Everything below rests on exactly four facts.

1. **The Weierstrass differential equation**
   $`\wp'^2 = 4\wp^3 - g_2\wp - g_3`$ (§4). This is what puts $`\Phi(z)`$ on the curve.
2. **Periodicity and parity.** $`\wp(z+l) = \wp(z)`$, $`\wp'(z+l) = \wp'(z)`$ for
   $`l \in \Lambda`$; $`\wp(-z) = \wp(z)`$, $`\wp'(-z) = -\wp'(z)`$ (§3).
3. **Liouville for elliptic functions.** A holomorphic $`\Lambda`$-periodic function on
   $`\mathbb{C}`$ is constant (§3). This is used four times: for $`\Phi`$'s surjectivity,
   and once for each of the three vanishing identities of §7.
4. **The two addition laws** for $`\wp`$ and $`\wp'`$ (§7), which say that $`\Phi`$ is a
   homomorphism.

The rest is bookkeeping with removable singularities and one countability argument to
remove the degenerate cases.

## 3. Elliptic functions and Liouville

A function $`f : \mathbb{C} \to \mathbb{C}`$ is **elliptic** for $`\Lambda`$ if it is
meromorphic and $`f(z+l) = f(z)`$ for all $`l \in \Lambda`$; equivalently, it is a
meromorphic function on the torus $`\mathbb{C}/\Lambda`$. Both $`\wp`$ and $`\wp'`$ are
elliptic, with poles exactly at $`\Lambda`$.

**Liouville's theorem for elliptic functions.** *A holomorphic elliptic function is
constant.*

*Proof.* Let $`D = \{a\omega_1 + b\omega_2 : 0 \le a, b \lt 1\}`$ be the fundamental
parallelogram. Its closure is compact and $`\mathbb{C} = D + \Lambda`$, so by periodicity
$`f(\mathbb{C}) = f(\overline{D})`$, which is compact, hence bounded. A bounded entire
function is constant. $`\square`$

The pin uses the sharpened *entire* form directly: if $`f : \mathbb{C} \to \mathbb{C}`$ is
differentiable and $`\Lambda`$-periodic, then $`f`$ is constant
(`apply_eq_apply_of_differentiable_of_forall_periodic`). Its uses in the proof all have
the same shape:

> **Extension principle.** Suppose $`H`$ is meromorphic and $`\Lambda`$-periodic on a
> domain $`U`$ whose complement is contained in $`\Lambda \cup (-w + \Lambda)`$. If the
> singularities of $`H`$ along $`\Lambda`$ and $`-w + \Lambda`$ are removable, then $`H`$
> extends to an entire $`\Lambda`$-periodic function, hence is constant; if moreover
> $`H`$ vanishes at one point of $`U`$, then $`H \equiv 0`$.

Removability is decided by the Laurent expansion: a meromorphic function has a removable
singularity at $`a`$ precisely when its Laurent expansion at $`a`$ has no negative powers.
The computations of §7 are exactly computations of the leading terms of such expansions.

## 4. The Weierstrass differential equation

**Theorem.** For all $`z \notin \Lambda`$,

$$\wp'(z)^2 = 4\wp(z)^3 - g_2\wp(z) - g_3.$$

*Proof.* Put

$$F = \wp'^2 - 4\wp^3 + g_2\wp + g_3.$$

Because $`\wp, \wp'`$ are $`\Lambda`$-periodic and meromorphic with poles only at
$`\Lambda`$, so is $`F`$. Use the Laurent expansions at $`0`$,

$$\wp(z) = \frac{1}{z^2} + 3G_4 z^2 + 5G_6 z^4 + O(z^6), \qquad
  \wp'(z) = -\frac{2}{z^3} + 6G_4 z + 20G_6 z^3 + O(z^5),$$

where $`G_k = \sum_{l \ne 0} l^{-k}`$ and $`g_2 = 60G_4`$, $`g_3 = 140G_6`$. A direct
expansion gives

$$\wp'(z)^2 = 4z^{-6} - 24G_4 z^{-2} - 80G_6 + O(z^2), \qquad
  4\wp(z)^3 - g_2\wp(z) - g_3 = 4z^{-6} - 24G_4 z^{-2} - 80G_6 + O(z^2),$$

so $`F = O(z^2)`$ at $`0`$: all negative powers cancel, and the constant term as well.
Thus $`F`$ extends holomorphically to $`0`$, and by periodicity to all of $`\Lambda`$.
The extension is entire and $`\Lambda`$-periodic, hence constant by Liouville; since
$`F(0) = 0`$, it is $`0`$. $`\square`$

The expansion of $`\wp`$ has **no constant term**, and that is what makes the constant
terms of the two sides agree; it is the same cancellation that fixes $`g_2 = 60G_4`$ and
$`g_3 = 140G_6`$. (The expansion of $`\wp`$ follows from
$`1/(z-l)^2 - 1/l^2 = \sum_{k \ge 1}(k+1)z^k/l^{k+2}`$, whose odd $`k`$ terms cancel in
pairs $`l \leftrightarrow -l`$.)

## 5. The curve is nonsingular, and the map is well defined

The discriminant $`\Delta = g_2^3 - 27g_3^2`$ does not vanish. For the lattice
$`\Lambda_\tau = \mathbb{Z}\tau + \mathbb{Z}`$ this is the classical identity
$`\Delta(\Lambda_\tau) = (2\pi)^{12}\Delta_{\mathrm{mod}}(\tau)`$ with
$`\Delta_{\mathrm{mod}}(\tau) = q\prod_{n\ge1}(1-q^n)^{24} \neq 0`$ on
$`\mathbb{H}`$; for a general lattice $`\Lambda = \alpha\Lambda_\tau`$ it follows from the
scaling $`\Delta(\alpha\Lambda) = \alpha^{-12}\Delta(\Lambda)`$. The pin proves it
separately as `PeriodPair.discriminant_ne_zero`.

Given the differential equation, for $`z \notin \Lambda`$,

$$\left(\frac{\wp'(z)}{2}\right)^2
  = \wp(z)^3 - \frac{g_2}{4}\wp(z) - \frac{g_3}{4},
  \qquad\text{i.e.}\qquad
  \left(\frac{\wp'(z)}{2}\right)^2 = \wp(z)^3 + a_4\wp(z) + a_6$$

with $`a_4 = -g_2/4`$, $`a_6 = -g_3/4`$. So the pair $`(\wp(z), \wp'(z)/2)`$ satisfies the
short Weierstrass equation of $`E_\Lambda`$. Since $`\Delta \neq 0`$ the point is
nonsingular, hence an affine point of $`E_\Lambda`$; this is the pin's
`equation_weierstrassP` followed by `equation_iff_nonsingular_of_Δ_ne_zero`. This makes
$`\Phi`$ well defined, and it makes the "kernel" direction of the theorem easy: the
affine point $`(\wp(z), \wp'(z)/2)`$ is never the origin, so $`\Phi(z) = 0`$ forces the
defining case $`z \in \Lambda`$ (`toPoint_eq_zero_iff`).

## 6. Surjectivity of ℘

**Theorem.** *The map* $`\wp : \mathbb{C} \setminus \Lambda \to \mathbb{C}`$ *is
surjective.*

*Proof.* Let $`c \in \mathbb{C}`$ and suppose $`\wp(z) \neq c`$ for all
$`z \notin \Lambda`$. Define

$$G(z) = \begin{cases} (\wp(z)-c)^{-1}, & z \notin \Lambda, \\ 0, & z \in \Lambda. \end{cases}$$

Then $`G`$ is $`\Lambda`$-periodic, because $`\wp`$ is. It is differentiable everywhere:
off $`\Lambda`$ it is the reciprocal of a nowhere-zero analytic function, and at
$`l \in \Lambda`$ it is continuous with value $`0`$, because $`\wp - c`$ has a pole of
order $`2`$ at $`l`$ (mathlib's `order_weierstrassP`: $`\mathrm{meromorphicOrderAt}\,
\wp\, l = -2`$), so $`(\wp-c)^{-1} \to 0`$ as $`z \to l`$. By Liouville for entire
$`\Lambda`$-periodic functions, $`G`$ is constant. But $`G(0) = 0`$ while
$`G(\omega_1/2) = (\wp(\omega_1/2)-c)^{-1} \neq 0`$ (as $`\omega_1/2 \notin \Lambda`$).
Contradiction. $`\square`$

The classical phrasing is the same argument with the roles of zero and pole exchanged:
$`\wp - c`$ has a double pole at $`0`$; if it had no zero, then $`1/(\wp-c)`$ would be a
holomorphic elliptic function, hence constant, hence $`\wp`$ constant, absurd.

Two immediate corollaries.

- **$`\Phi`$ is surjective** (`toPoint_surjective`). Given $`P = (x_0,y_0)`$ on
  $`E_\Lambda`$, choose $`z \notin \Lambda`$ with $`\wp(z) = x_0`$; then
  $`(\wp'(z)/2)^2 = y_0^2`$ by §5, so $`\wp'(z)/2 = \pm y_0`$. If the sign is wrong,
  replace $`z`$ by $`-z`$, using $`\wp(-z) = \wp(z)`$ and $`\wp'(-z) = -\wp'(z)`$.
- **The level sets of $`\wp`$ are countable** (`countable_weierstrassP_eq`). The
  function $`\wp - c`$ is analytic and not identically zero, so its zero set is discrete,
  and a discrete subset of the Lindelöf space $`\mathbb{C}`$ is countable. This is used
  only in §8, to know that the "bad" values to avoid form a countable set.

## 7. The addition theorem

Fix $`w \notin \Lambda`$. The addition law on $`E_\Lambda`$ is the chord-and-tangent
formula. Write $`P_z = (\wp(z), \wp'(z)/2)`$ for $`z \notin \Lambda`$. If
$`\wp(z) \neq \wp(w)`$, the slope of the chord through $`P_z`$ and $`P_w`$ is

$$\lambda = \frac{\wp'(w)/2 - \wp'(z)/2}{\wp(w) - \wp(z)}
  = \frac{\wp'(z) - \wp'(w)}{2(\wp(z) - \wp(w))},$$

and the sum $`P_z + P_w = (\wp(z+w), \wp'(z+w)/2)`$ has, by the group law,

$$\wp(z+w) = \lambda^2 - \wp(z) - \wp(w), \qquad
  \frac{\wp'(z+w)}{2} = \lambda\\,(\wp(z) - \wp(z+w)) - \frac{\wp'(z)}{2}.$$

The theorem is that these two equations hold. They are equivalent to the vanishing of two
explicit elliptic functions, and both are proved with the same Liouville pattern.

### 7.1 The $`x`$-coordinate

Define

$$\Phi_w(z) = 4(\wp(z)-\wp(w))^2\bigl(\wp(z+w) + \wp(z) + \wp(w)\bigr) -
  (\wp'(z)-\wp'(w))^2.$$

**Claim.** $`\Phi_w \equiv 0`$.

Rearranged, $`\Phi_w(z) = 0`$ reads

$$\wp(z+w) = \frac{1}{4}\left(\frac{\wp'(z)-\wp'(w)}{\wp(z)-\wp(w)}\right)^2 -
  \wp(z) - \wp(w) = \lambda^2 - \wp(z) - \wp(w),$$

which is the $`x`$-coordinate formula. So the claim is exactly the first half of the
addition law.

*Proof of the claim.*

1. **$`\Phi_w`$ is $`\Lambda`$-periodic.** Each of $`\wp(z)`$, $`\wp(z+w)`$, $`\wp'(z)`$,
   $`\wp'(z+w)`$ is unchanged by $`z \mapsto z + l`$ with $`l \in \Lambda`$ (the last
   because $`z + l + w = (z+w) + l`$). So $`\Phi_w`$ descends to a function of
   $`z \bmod \Lambda`$.
2. **$`\Phi_w`$ is analytic on** $`U_w = \{z : z \notin \Lambda,\ z+w \notin \Lambda\}`$.
   The only possible poles are where $`\wp(z)`$ or $`\wp(z+w)`$ has one, and $`U_w`$
   excludes both.
3. **$`\Phi_w`$ has removable singularities at** $`0`$ **and at** $`-w`$.
   At $`z = 0`$, the leading terms are
   $$(\wp(z)-\wp(w))^2 = z^{-4} - 2\wp(w) z^{-2} + O(1),$$
   $$\wp(z+w) + \wp(z) + \wp(w) = z^{-2} + 2\wp(w) + z\,\wp'(w) + O(z^2),$$
   where the key point is again that $`\wp`$ has no constant term at $`0`$. Hence
   $$4(\wp(z)-\wp(w))^2\bigl(\wp(z+w)+\wp(z)+\wp(w)\bigr) = 4z^{-6} + 4\wp'(w)z^{-3} + O(1),$$
   while
   $$(\wp'(z)-\wp'(w))^2 = (-2z^{-3} - \wp'(w) + O(z))^2 = 4z^{-6} + 4\wp'(w)z^{-3} + O(1).$$
   The two expansions agree through order $`-3`$, so $`\Phi_w(z) = O(1)`$: the singularity
   is removable. At $`z = -w`$, the factor $`(\wp(z)-\wp(w))^2`$ vanishes to order $`2`$
   (since $`\wp(-w) = \wp(w)`$), which kills the double pole of
   $`\wp(z+w)`$; the second term is analytic there. So $`\Phi_w`$ is bounded, hence
   removable.
4. **$`\Phi_w(w) = 0`$.** Both terms vanish: $`\wp(w)-\wp(w) = 0`$ and
   $`\wp'(w)-\wp'(w) = 0`$.

Now extend $`\Phi_w`$ across the removable singularities, by periodicity across all of
$`\Lambda`$ and $`-w+\Lambda`$. The extension is entire and $`\Lambda`$-periodic, hence
constant (Liouville). Its value at $`w`$ is $`0`$ (this is where $`2w \notin \Lambda`$ is
needed: then $`w \in U_w`$, so the extension agrees with $`\Phi_w`$ there). Therefore the
extension is $`\equiv 0`$, and $`\Phi_w \equiv 0`$ on $`U_w`$. $`\square`$

The rearrangement is the pin's `weierstrassP_add_eq_addX`:

$$\wp(z+w) = \mathrm{addX}\bigl(\wp(z), \wp(w), \mathrm{slope}(\wp(z),\wp(w),\wp'(z)/2,\wp'(w)/2)\bigr),$$

i.e. the $`x`$-coordinate of the group-law sum.

### 7.2 The $`y`$-coordinate

Define

$$\Psi_w(z) = (\wp(z)-\wp(w))\\,\wp'(z+w) + (\wp'(z)-\wp'(w))\\,\wp(z+w) +
  \wp(z)\wp'(w) - \wp(w)\wp'(z).$$

**Claim.** $`\Psi_w \equiv 0`$.

This is the $`y`$-coordinate of the addition law. Its proof is the same four steps.

1. $`\Psi_w`$ is $`\Lambda`$-periodic, term by term.
2. It is analytic on $`U_w`$.
3. It is removable at $`0`$: the expansions give $`\Psi_w(z) = O(1)`$ — the $`z^{-3}`$,
   $`z^{-2}`$ and $`z^{-1}`$ coefficients cancel, using
   $`\wp(z) = z^{-2} + O(z^2)`$ and $`\wp'(z) = -2z^{-3} + O(z)`$. At $`-w`$ it is removable
   by **odd symmetry**:
   $$\Psi_w(-z-w) = -\Psi_w(z),$$
   which follows from $`\wp(-u) = \wp(u)`$ and $`\wp'(-u) = -\wp'(u)`$; so the removable
   behaviour at $`0`$ transports to $`-w`$.
4. $`\Psi_w(w) = 0`$, directly.

Liouville then gives $`\Psi_w \equiv 0`$, and the rearrangement is
`derivWeierstrassP_add_eq_addY`:

$$\frac{\wp'(z+w)}{2} = \mathrm{addY}\bigl(\wp(z),\wp(w),\wp'(z)/2,
  \mathrm{slope}(\wp(z),\wp(w),\wp'(z)/2,\wp'(w)/2)\bigr).$$

### 7.3 The group law, generically

Combining 7.1 and 7.2, in the **generic case**

$$w \notin \Lambda, \quad 2w \notin \Lambda, \quad z \notin \Lambda, \quad
  z+w \notin \Lambda, \quad \wp(z) \neq \wp(w),$$

the two coordinates of $`\Phi(z+w)`$ equal those of $`P_z + P_w`$, and since the points are
affine and have distinct $`x`$-coordinates, mathlib's `Affine.Point.add_of_X_ne` applies
and gives

$$\Phi(z+w) = \Phi(z) + \Phi(w).$$

This is `toPoint_add_generic`. The remaining work is to remove the five hypotheses.

## 8. Removing the degenerate cases

Three of the hypotheses are handled directly, and the two "distinct $`x`$" conditions by
a perturbation.

**Trivial cases.** If $`z \in \Lambda`$ then $`\Phi(z+w) = \Phi(w) = 0 + \Phi(w)`$; if
$`w \in \Lambda`$ the same with the roles exchanged; if $`z+w \in \Lambda`$ then
$`\Phi(z+w) = 0`$ and $`\Phi(w) = \Phi(-z) = -\Phi(z)`$, so
$`\Phi(z) + \Phi(w) = 0`$. All three use only periodicity and parity
(`toPoint_add_mem`, `toPoint_neg`).

**The perturbation.** Suppose $`z, w, z+w \notin \Lambda`$. Choose $`u`$ outside the
exceptional set

$$S = \Lambda \cup \\{u : 2u \in \Lambda\\} \cup \\{u : z+u \in \Lambda\\}
  \cup \\{u : w+u \in \Lambda\\} \cup \\{u : z+w+u \in \Lambda\\}
  \cup \\{u : 2(w+u) \in \Lambda\\}
  \cup \\{u \notin \Lambda : \wp'(u) = 0\\}
  \cup \\{u : w+u \notin \Lambda,\ \wp'(w+u) = 0\\}
  \cup \\{u \notin \Lambda : \wp(u) \in \\{\wp(z), \wp(w), \wp(z+w)\\}\\}
  \cup \\{u : w+u \notin \Lambda,\ \wp(w+u) = \wp(z)\\},$$

where each set is understood off $`\Lambda`$ as in §6. Every piece is a translate or a
dilate of $`\Lambda`$, of the zero set of $`\wp'`$, or of a level set $`\wp = c`$; the
last two are countable by §6, the lattice is countable, and countable unions of countable
sets are countable. Since $`\mathbb{C}`$ is uncountable, $`S \neq \mathbb{C}`$:
**a good $`u`$ exists.** This is `exists_generic_perturbation`.

For such a $`u`$, all of $`u`$, $`2u`$, $`z+u`$, $`w+u`$, $`z+w+u`$, $`2(w+u)`$ avoid
$`\Lambda`$, and the three pairs $`(z+w,u)`$, $`(z,w+u)`$, $`(w,u)`$ are generic in the
sense of 7.3. Applying the generic identity three times,

$$\Phi(z+w+u) = \Phi(z+w) + \Phi(u) = \Phi(z) + \Phi(w+u) = \Phi(z) + \Phi(w) + \Phi(u),$$

using $`z+w+u = z+(w+u)`$; cancelling $`\Phi(u)`$ gives $`\Phi(z+w) = \Phi(z)+\Phi(w)`$.

This is `toPoint_add`, and with it additivity holds for **all** $`z, w \in \mathbb{C}`$.

## 9. The isomorphism

Putting the pieces together:

- $`\Phi`$ is $`\Lambda`$-periodic (`toPoint_add_mem`), so it factors through the quotient
  $`\mathbb{C} \to \mathbb{C}/\Lambda`$;
- $`\Phi`$ is additive (`toPoint_add`) and $`\Phi(0) = 0`$, so it is a group
  homomorphism;
- $`\Phi`$ is surjective (`toPoint_surjective`);
- $`\Phi(z) = 0 \iff z \in \Lambda`$ (`toPoint_eq_zero_iff`), which is exactly the
  kernel condition.

Hence the induced map $`\mathbb{C}/\Lambda \to E_\Lambda(\mathbb{C})`$ is a surjective
homomorphism with trivial kernel, i.e. an isomorphism of additive groups. The pin states
the three conjuncts together as `PeriodPair.IsUniformization`:

```lean
def IsUniformization (h : L.DiscriminantNeZero) : Prop :=
  (∀ z w, L.toPoint h (z + w) = L.toPoint h z + L.toPoint h w) ∧
    Function.Surjective (L.toPoint h) ∧
      ∀ z, L.toPoint h z = 0 → z ∈ L.lattice
```

In the port the descended isomorphism is packaged explicitly, as
`PeriodPair.toPointAddEquiv : (ℂ ⧸ Λ) ≃+ E(ℂ)`.

## 10. What the proof does not use

It is worth stating plainly what is absent from the argument, because it locates the
result relative to the rest of the project.

- **No modular forms, no $`q`$-expansions, no Eisenstein series.** The surjectivity of
  $`j`$ — the other place one meets $`\mathbb{C}/\Lambda`$ in this project — is *not*
  proved here; in the pin it is proved from $`E_4`$, $`E_6`$, $`\Delta`$ and the
  one-dimensionality of weight-12 cusp forms (see
  [math/024 §3.3](../math/024-uniformization-versus-modular-functions.md) and
  [math/026 §5](../math/026-weierstrass-p-division-values-and-level-n.md)). The two
  arguments are independent.
- **No algebraic geometry of $`E`$ beyond the chord-and-tangent law.** The group law on
  a nonsingular Weierstrass cubic is an algebraic fact, taken as given; the analytic work
  is entirely in matching $`\Phi`$ to it.
- **No Riemann surface.** The torus $`\mathbb{C}/\Lambda`$ is used only through the
  periodicity of $`\wp`$ and the compactness of a fundamental parallelogram; the
  "quotient" is present only as the $`\Lambda`$-periodicity, and the descended map of §9 is
  immediate.
- **No level structure.** Everything here is level one. The $`N`$-division points and the
  Fricke coordinates, which turn this isomorphism into the level-$`N`$ modular curve, are
  [math/026](../math/026-weierstrass-p-division-values-and-level-n.md); they use §5 and
  §7 unchanged.

## 11. Lean technicalities

The mathematics is above. This section maps it to the formalisation: what mathlib
supplies, what the pin builds, and the names. The pin's proof is one file,
`P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean` (1,493 lines); its headline is
re-exported by `Theorems/Thm_PeriodPair_isUniformization_toPoint.lean`, whose whole body
is

```lean
theorem PeriodPair.isUniformization_toPoint (L : PeriodPair) (h : L.DiscriminantNeZero) :
    L.IsUniformization h := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_isUniformization_toPoint.solution
```

and the definitions it is about live in `Definitions/Def_PeriodPair_Uniformization.lean`
(`weierstrassCurve`, `DiscriminantNeZero`, `toPoint`, `IsUniformization`).

**What mathlib supplies.** mathlib has the analytic theory of $`\wp`$ but not the
addition theorem or the uniformization. Concretely, in
[`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean):
`PeriodPair` (line 60), `weierstrassPExcept` (219), `weierstrassP` (268),
`order_weierstrassP` (921), `derivWeierstrassP_sq` (1075), together with the periodicity
`weierstrassP_add_coe` / `derivWeierstrassP_add_coe`, the parity `weierstrassP_neg` /
`derivWeierstrassP_neg`, and analyticity away from the lattice. The differential equation
is itself proved in mathlib by the §4 strategy: the private `relation` is shown analytic
everywhere (removable at the lattice), periodic, hence constant, hence zero
(`relation_eq_zero`). Note that `weierstrassPExcept` is the technical device that makes the
Laurent computations of §7.1 rigorous: `℘[L - l₀]` is $`\wp`$ with the $`l_0`$-term deleted,
so `weierstrassPExcept_add` writes $`\wp(z) = (z-l_0)^{-2} + \wp[L-l_0](z) + \text{const}`$
and separates the pole from the regular part.

The other mathlib inputs are Liouville in its bounded-entire form
([`Analysis/Complex/Liouville.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/Complex/Liouville.lean#L114),
`apply_eq_apply_of_bounded`), the fundamental domain and its boundedness
([`Algebra/Module/ZLattice/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Algebra/Module/ZLattice/Basic.lean#L92)),
the chord-and-tangent group law
([`AlgebraicGeometry/EllipticCurve/Affine/Point.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean#L711),
`add_of_X_ne`), and for the countability argument the isolated-zeros principle
([`Analysis/Analytic/IsolatedZeros.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/Analytic/IsolatedZeros.lean#L219),
`eqOn_zero_or_eventually_ne_zero_of_preconnected`) and Lindelöf discreteness
([`Topology/Compactness/Lindelof.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Topology/Compactness/Lindelof.lean#L571),
`countable_of_Lindelof_of_discrete`). mathlib has no addition theorem, no surjectivity of
$`\wp`$, and no uniformization statement; all of §4–§9 beyond the differential equation is
the pin's.

**The proof, step by step, in Lean.** The port's internal names are stripped of the pin's collision prefix and
are `private`; the line numbers are for `aa2d8b3`.

| Lean (port) | pin line | mathematics |
|---|---|---|
| `apply_eq_apply_of_differentiable_of_forall_periodic` | 155 | §3, Liouville for differentiable $`\Lambda`$-periodic functions |
| `toPoint_add_mem` | 185 | $`\Phi`$ is $`\Lambda`$-periodic |
| `toPoint_neg` | 198 | $`\Phi(-z) = -\Phi(z)`$ |
| `weierstrassP_surjective` | 367 | §6, $`\wp`$ is onto |
| `toPoint_eq_zero_iff` | 429 | $`\Phi(z)=0 \iff z \in \Lambda`$ |
| `toPoint_surjective` | 437 | §6 corollary, $`\Phi`$ is onto |
| `addΦ` | 795 | the $`x`$-addition expression $`\Phi_w`$ |
| `addΦ_diffEq` | 801 | rewrite $`\Phi_w`$ using the ODE |
| `addBridge_identity` | 812 | $`z^4\Phi_w(z) = E(z) + R(z)`$, the removability decomposition |
| `addCoreE_order_ge_four` | 679 | $`E`$ has order $`\ge 4`$ at $`0`$ |
| `addBridgeR_order_ge_four` | 762 | $`R`$ has order $`\ge 4`$ at $`0`$ |
| `elliptic_Liouville_zero` | 984 | the extension principle of §3, in full generality |
| `addΦ_eq_zero` | 1098 | §7.1, $`\Phi_w \equiv 0`$ |
| `weierstrassP_add_eq_addX` | 1107 | the $`x`$-coordinate formula |
| `addΨ` | 1120 | the $`y`$-addition expression $`\Psi_w`$ |
| `addΨ_neg_sub` | 1150 | $`\Psi_w(-z-w) = -\Psi_w(z)`$ |
| `addΨ_eq_zero` | 1304 | §7.2, $`\Psi_w \equiv 0`$ |
| `derivWeierstrassP_add_eq_addY` | 1313 | the $`y`$-coordinate formula |
| `toPoint_add_generic` | 1332 | §7.3, additivity in the generic case |
| `exists_generic_perturbation` | 1394 | §8, existence of the good $`u`$ |
| `toPoint_add` | 1435 | §8, additivity in all cases |
| `isUniformization_toPoint` | 1478 | §9, the three conjuncts |

The final assembly is four lines:

```lean
theorem solution (L : PeriodPair) (h : L.DiscriminantNeZero) : L.IsUniformization h :=
  L.isUniformization_toPoint
```

with `isUniformization_toPoint` built from `toPoint_add`, `toPoint_surjective` and
`toPoint_eq_zero_iff`.

**Two statement-shape notes.** First, `IsUniformization` is stated for
`toPoint : ℂ → E(ℂ)`, not for a map $`\mathbb{C}/\Lambda \to E(\mathbb{C})`$: the
descended isomorphism is not a separate declaration in the pin. It is made explicit in
the port (below) as `toPointAddEquiv`. Second, the removability computations are not done
by hand on Laurent coefficients: the pin defines explicit auxiliary functions
(`addCoreE`, `addBridgeT`, `addBridgeR`, `addCoreE₁`, `addCoreE₂`,
`addΨCoreE`, `addΨTail`) whose `analyticOrderAt` at `0` is bounded below by
`natCast_le_analyticOrderAt` / `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero`, and
then the removability of $`\Phi_w`$ and $`\Psi_w`$ follows from an algebraic bridge
identity. That is the formal counterpart of "the negative powers cancel" in §7.

**The port.** This file has been ported, with the pin's collision prefix dropped and the
helpers named for content, at
[`lean/FLTForHuman/Elliptic/PeriodPair/Uniformization.lean`](https://github.com/htzh/flt_for_human/blob/34f235a/lean/FLTForHuman/Elliptic/PeriodPair/Uniformization.lean)
(commit `34f235a`). Its header carries the full pin-name mapping. The headline is

```lean
theorem isUniformization_toPoint (L : PeriodPair) (h : L.DiscriminantNeZero) :
    L.IsUniformization h :=
  ⟨L.toPoint_add h, L.toPoint_surjective h, fun z => (L.toPoint_eq_zero_iff h z).mp⟩
```

at line 1238, and the same file promotes the descended isomorphism to first-class
declarations: `toPointHom : ℂ →+ E(ℂ)` (1263), `ker_toPointHom` (1273), and

```lean
noncomputable def toPointAddEquiv :
    (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (L.weierstrassCurve.toAffine).Point
```

at line 1281 — the additive group isomorphism of this note, as an `AddEquiv`. The pin's
own copy of that packaging is `PeriodPair.toPointAddEquiv`, private and exported from
`S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean`
(line 950), used by the isogeny/Vélu files of
[math/023](../math/023-velu-isogenies-and-endomorphism-ring.md).

**Citation convention.** FLT citations are pinned to `aa2d8b3`, this repository's at
`34f235a`, and mathlib to `v4.34.0` (the tag the port is elaborated against in this
working tree; the pin's own is `v4.33.0`, where these declarations have the same names and
slightly different line numbers).

## Links

Pinned pin sources (`aa2d8b3`):

- [`Definitions/Def_PeriodPair_Uniformization.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_PeriodPair_Uniformization.lean) — `weierstrassCurve`, `equation_weierstrassP` (37), `DiscriminantNeZero` (48), `toPoint` (57), `IsUniformization` (75)
- [`Theorems/Thm_PeriodPair_isUniformization_toPoint.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PeriodPair_isUniformization_toPoint.lean#L6) — the headline
- [`P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean) — the proof; `addΦ` (795), `addΦ_eq_zero` (1098), `addΨ` (1120), `addΨ_eq_zero` (1304), `toPoint_add` (1435), `isUniformization_toPoint` (1478)
- [`Theorems/Thm_PeriodPair_discriminant_ne_zero.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PeriodPair_discriminant_ne_zero.lean#L6) — $`\Delta \neq 0`$
- [`P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean#L950) — `toPointAddEquiv`

This repository (`34f235a`):

- [`lean/FLTForHuman/Elliptic/PeriodPair/Uniformization.lean`](https://github.com/htzh/flt_for_human/blob/34f235a/lean/FLTForHuman/Elliptic/PeriodPair/Uniformization.lean) — the port; `isUniformization_toPoint` (1238), `toPointHom` (1263), `ker_toPointHom` (1273), `toPointAddEquiv` (1281)
- [`lean/FLTForHuman/Elliptic/PeriodPair/Basic.lean`](https://github.com/htzh/flt_for_human/blob/34f235a/lean/FLTForHuman/Elliptic/PeriodPair/Basic.lean) — the surrounding period-pair dictionary

mathlib (tag `v4.34.0`):

- [`Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean) — `PeriodPair` (60), `weierstrassPExcept` (219), `weierstrassP` (268), `order_weierstrassP` (921), `derivWeierstrassP_sq` (1075)
- [`Analysis/Complex/Liouville.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/Complex/Liouville.lean#L114) — `apply_eq_apply_of_bounded`
- [`Algebra/Module/ZLattice/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Algebra/Module/ZLattice/Basic.lean#L92) — `fundamentalDomain`, and `fundamentalDomain_isBounded` (245)
- [`AlgebraicGeometry/EllipticCurve/Affine/Point.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean#L711) — `add_of_X_ne`, the chord-and-tangent group law
- [`Analysis/Analytic/IsolatedZeros.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Analysis/Analytic/IsolatedZeros.lean#L219) — `eqOn_zero_or_eventually_ne_zero_of_preconnected`
- [`Topology/Compactness/Lindelof.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/Topology/Compactness/Lindelof.lean#L571) — `countable_of_Lindelof_of_discrete`

Companion notes:

- [base/005 — Cyclic isogenies, congruence level, and the j-invariant](005-cyclic-isogenies-and-level.md) — tori as lattices, the moduli reading of $`j`$, and the isogeny dictionary this theorem underwrites
- [base/007 — The Weil pairing](007-weil-pairing.md) — the pairing on $`E[n]`$, whose characteristic-zero formula $`e_n(u/n,v/n) = \zeta_n^{ad-bc}`$ is computed on $`\mathbb{C}/\Lambda`$
- [base/013 — Riemann existence and the q-expansion principle](013-riemann-existence-and-the-q-expansion-principle.md) — the other analytic input of the project, the level-one $`q`$-expansion principle
- [math/024 — Uniformization versus modular functions](../math/024-uniformization-versus-modular-functions.md) — the two routes to the $`j`$-line, and where this theorem is used
- [math/026 — ℘-division values and the level-N modular curve](../math/026-weierstrass-p-division-values-and-level-n.md) — the Fricke functions, built on this theorem

Background:

- L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw–Hill, 1979, Ch. 7 — elliptic functions and Liouville.
- J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer, 1994, Ch. I — uniformization, and the moduli interpretation of the isomorphism.
- E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed., Cambridge, 1927, Ch. XX — the Weierstrass functions and the addition theorem.
- S. Lang, *Elliptic Functions*, 2nd ed., GTM 112, Springer, 1987, Ch. 1–2 — the same material with the modular parametrization developed alongside.
