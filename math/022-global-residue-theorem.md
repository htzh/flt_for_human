# The global residue theorem over an algebraically closed field

Twenty-second of the `math/` notes. [math/021](021-tate-residue.md) opened the
*local* input — Tate's commutator definition of the residue at one place and the
agreement theorem identifying its trace with the trace of the local residue.
This note opens the *global* theorem built on top of it: the statement
`residueTheoremK_of_isAlgClosed`
([Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean)),
which proves that the sum of the residues of a meromorphic differential over an
arbitrary algebraically closed field is zero. It is the algebraic replacement for
the contour proof over $`\mathbb{C}`$, and it is the "analytic" input of the
Riemann–Roch route measured in
[studies/riemann-roch-strategy.md](../studies/riemann-roch-strategy.md) §3 and
consumed by the engine of
[base/019](../base/019-stichtenoth-genus-and-the-adelic-index.md).

The shape of the proof is worth stating up front, because it is the reason the
formalization is split across two enormous files (8,121 and 13,170 lines). The
theorem is proved first for the **rational function field** $`K(X)`$, where it is
an explicit partial-fractions computation; then a general curve $`F/K`$ is
related to $`K(X)`$ by a finite separable map, and the theorem descends along
that map through the **fibre-integration formula**: the sum of the residues over
a fibre equals the residue of the *trace*. The fibre formula is where the local
theory of [math/021](021-tate-residue.md) enters, through
`residueTraceCompletionCommute` and the completion trace sum.

Math first: §§1–5 are the mathematics, §6 summarizes the Lean encoding. Line
numbers point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib declarations
are named at tag **v4.33.0**. The pin citations are rendered GitHub links
carrying `#L` anchors.

The plan:

1. the statement, and the residue functional it is about;
2. the base case: partial fractions on $`\mathbb{P}^1`$;
3. fibre integration: descending from $`\mathbb{P}^1`$ to a general curve;
4. the local input, and how the local and global pieces compose;
5. characteristic $`p`$;
6. the Lean encoding and the key-point map.

## 1. The statement, and the residue functional

Let $`K`$ be algebraically closed and $`F/K`$ a curve. For a nonzero Kähler
differential $`\omega \in \Omega_{F/K}`$ define the **residue functional**

$$\rho_\omega(f) \\;=\\; \sum_{v} \mathrm{Tr}_{k(v)/K}\bigl(\mathrm{Res}_v(f\\,\omega)\bigr), \qquad f \in F .$$

The sum is finite: $`f\omega`$ has a pole at only finitely many places, and at a
place where the order is non-negative the residue vanishes. The **global residue
theorem** is the statement

$$\mathrm{ResidueTheoremK}: \quad \forall\\, \omega \ne 0,\ \forall f \in F, \qquad \rho_\omega(f) = 0 .$$

The pin states it as the vanishing of the adelic functional
$`\mathrm{weilOfKaehlerK}`$ on the diagonal,

```lean
def ResidueTheoremK : Prop :=
  ∀ (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) [HasPrincipalDivisors K F]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (f : F),
    weilOfKaehlerK Rfam hω ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ = 0
```

([Def_AlgebraicCurve_LocalResidue.lean, lines 297–300](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_LocalResidue.lean#L297-L300)),
with
$`\mathrm{weilOfKaehlerK}(\omega)(\alpha) = \sum_v \mathrm{kaehlerResidueTerm}(\omega, \alpha, v)`$
([lines 264–290](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_LocalResidue.lean#L264-L290)).
The residue term is the trace to $`K`$ of the local residue,
$`\mathrm{kaehlerResidueTerm}(\omega, \alpha, v) = \mathrm{Tr}_{k(v)/K}(\mathrm{Res}_v(\alpha_v\,\mathrm{coeff}_v(\omega)))`$
([line 111](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_LocalResidue.lean#L111)),
and the local residue is the object of [math/021](021-tate-residue.md).

Two elementary reductions structure every proof below. First, $`\rho`$ is
$`F`$-linear in the differential in the sense

$$\rho_{g\\,\omega}(f) \\;=\\; \rho_\omega(g f),$$

because $`\mathrm{coeff}_v(g\omega) = g \cdot \mathrm{coeff}_v(\omega)`$ and the
residue term only sees the product
(`kaehlerResidueTermKFam_smul_diagonal`). Since $`\Omega_{F/K}`$ is
one-dimensional over $`F`$, this reduces the theorem for *every* $`\omega`$ to
the theorem for a single generator: if $`\omega_0 \ne 0`$ is a generator then
$`\omega = c\,\omega_0`$ and $`\rho_\omega(f) = \rho_{\omega_0}(c f)`$. Second,
the sum may be regrouped by a finite map $`F \to E`$, i.e. by swapping the order
of summation in

$$\sum_{w} g(w) \\;=\\; \sum_{v} \sum_{w \mid v} g(w),$$

which is `finsum_place_eq_finsum_fiber_sum` and is what makes descent possible.

## 2. The base case: partial fractions on $`\mathbb{P}^1`$

Take $`F = K(X)`$, with the standard generator $`\mathrm{d}X`$ (nonzero because
$`\Omega_{K(X)/K}`$ is one-dimensional and $`X`$ is transcendental). By §1 it
suffices to prove $`\rho_{\mathrm{d}X}(h) = 0`$ for all $`h \in K(X)`$.

The places of $`K(X)/K`$ are the monic irreducible polynomials $`p \in K[X]`$
(together with the place at infinity), and the residue field at the finite place
$`p`$ is $`K[X]/(p)`$. The computation rests on the **partial-fraction
decomposition**

$$K(X) \\;=\\; \mathrm{span}_K\Bigl( \\{X^n : n \ge 0\\} \\;\cup\\; \\{ c/p^m : p \text{ monic irreducible},\ \deg c \lt \deg p,\ m \ge 1 \\} \Bigr),$$

`p1PartialFractionSpan_eq_top`
([S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean, line 2729](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L2729)),
where the summand $`c/p^m`$ is a **principal-part atom** (`p1PrincipalPartAtom`,
[line 2053](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L2053)).
It is enough to check $`\rho_{\mathrm{d}X} = 0`$ on each generator. There are
three cases, all of them classical:

* **Polynomials.** For $`h = X^n`$, $`h\,\mathrm{d}X`$ has no pole at any finite
  place. At infinity, in the coordinate $`t = 1/X`$,
  $`X^n\,\mathrm{d}X = -t^{-(n+2)}\,\mathrm{d}t`$, whose $`t^{-1}`$
  coefficient is zero; so both residues are $`0`$
  (`kaehlerResidueFunctionalK_dX_X_pow`,
  [line 11836](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L11836)).
* **Simple poles.** For $`h = c/p`$ with $`p`$ monic irreducible and
  $`\deg c \lt \deg p`$, the differential $`(c/p)\,\mathrm{d}X`$ has poles only
  at $`p`$ and at infinity, and the two residues cancel after the traces to
  $`K`$:

$$\mathrm{Tr}_{k(p)/K}\bigl(\mathrm{Res}_p(c/p\\,\mathrm{d}X)\bigr) + \mathrm{Tr}_{k(\infty)/K}\bigl(\mathrm{Res}_\infty(c/p\\,\mathrm{d}X)\bigr) = 0 .$$

  This is the **simple-pole cancellation**, the heart of the theorem for
  $`\mathbb{P}^1`$ (`p1PrincipalPartMOneSimplePoleCancel_of_simplePoleCoordIndep`,
  [line 9911](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L9911),
  assembled into the two-place sum
  `kaehlerResidueTermKFam_atom_mOne_two_place_sum`,
  [line 11900](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L11900)).
  Over an algebraically closed field $`p = X - a`$ is linear with $`p' = 1`$, so
  the finite residue is $`c(a)`$ and the infinite residue is $`-c(a)`$; that is
  the familiar "the residues of a rational function sum to zero".
* **Higher poles.** For $`m \ge 2`$, both $`\mathrm{Res}_p(c/p^m\,\mathrm{d}X)`$
  and $`\mathrm{Res}_\infty(c/p^m\,\mathrm{d}X)`$ vanish: only the simple pole
  contributes a residue. The finite-place statement for general $`p`$ is the
  "higher-degree trace" row
  `p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg`
  ([line 7876](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L7876)),
  which is discharged from algebraic closedness.

Assembling the three cases (`kaehlerResidueFunctionalK_dX_atom`,
`kaehlerResidueFunctionalK_dX_eq_zero`,
[line 11918](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L11918),
[line 11946](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L11946)),
the residue functional of $`\mathrm{d}X`$ vanishes on the spanning set, hence on
all of $`K(X)`$:

$$\boxed{\ \mathrm{ResidueTheoremK}\ K\ (K(X))\ }$$

`residueTheoremK_ratFunc_of_subrows` and
`residueTheoremK_ratFunc_of_isAlgClosed_main`
([line 11968](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L11968),
[line 12000](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L12000)).
The four "subrows" it is assembled from are exactly: well-definedness of the
order of a differential (`ordDifferentialWellDefined_ratFunc`), independence of
the residue from the Kähler coordinate
(`canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed`),
independence from the simple-pole coordinate
(`canonicalLocalResidueKSimplePoleCoordIndep_ratFunc`), and the higher-degree
trace row above
([line 6608](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L6608),
[line 10843](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L10843),
[line 10779](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L10779),
[line 7876](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L7876)).

## 3. Fibre integration: from $`\mathbb{P}^1`$ to a general curve

Now let $`K`$ be algebraically closed and $`F/K`$ an arbitrary curve in the
sense of `IsCurveOver`. Choose a separating element $`X`$, so that
$`E := K(X)`$ is a subfield and $`F/E`$ is finite separable; this is the
separating-transcendental input used already in
[base/019 §5](../base/019-stichtenoth-genus-and-the-adelic-index.md). Pull
differentials back along $`E \subseteq F`$:

$$\mathrm{pullback} : \Omega_{E/K} \longrightarrow \Omega_{F/K}, \qquad \omega_E \mapsto \omega_E \otimes 1 ,$$

`kaehlerPullback`
([Def_AlgebraicCurve_TateResidueCurrency.lean, line 102](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L102)).
The pullback of $`\mathrm{d}X`$ is nonzero because $`F/E`$ is separable
(`kaehlerCotrace_dX_ne_zero_of_isSeparable`), so it is a generator of
$`\Omega_{F/K}`$ over $`F`$.

The descent rests on one identity, the **fibre-integration formula** (the pin's
`FiberKaehlerCotraceResidueIdentity`): for a nonzero $`\omega_E`$ whose pullback
is nonzero, and every $`f \in F`$,

$$\sum_{w \mid v} \mathrm{kaehlerResidueTerm}\bigl(\mathrm{pullback}\\,\omega_E,\ f,\ w\bigr) \\;=\\; \mathrm{kaehlerResidueTerm}\bigl(\omega_E,\ \mathrm{Tr}_{E/F} f,\ v\bigr),$$

for a suitable residue family on $`E`$
([S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean, line 4278](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L4278),
[Def_AlgebraicCurve_TateResidueCurrency.lean, lines 399–407](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L399-L407)).
This is the residue-theoretic form of fibre integration: summing the residues of
the pulled-back differential over the points of a fibre, then tracing to $`K`$,
is the same as taking the residue at the base point of the differential paired
with the field trace $`\mathrm{Tr}_{E/F}`$. It is the exact analogue of
$`\int_{f^{-1}(p)} f^*\omega = \int_p \omega`$ for a finite map of curves, with
the trace replacing the degree-weighted sum over the fibre.

The identity is needed in a **localized** form as well: if $`f`$ has a pole at
only one point $`w`$ of the fibre $`v`$, the sum on the left has a single
nonzero term
(`CotraceResidueIdentityOnFiberLocalized`,
[line 5024](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L5024),
[Def_AlgebraicCurve_TateResidueCurrency.lean, lines 432–443](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L432-L443)).
This is the form in which the generator-by-generator computation of §2 can be
transported to $`F`$.

With the base case and the fibre formula, the descent is formal. Given the
residue theorem for $`E = K(X)`$ and a generator $`\omega_{E,0}`$ with nonzero
pullback, the general theorem follows
(`residueTheoremK_of_cotraceResidueIdentityK`,
[S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean, line 5578](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L5578)):

* write $`\omega_F = c \cdot \mathrm{pullback}\,\omega_{E,0}`$ for some
  $`c \in F`$ (possible because $`\Omega_{F/K}`$ is one-dimensional over $`F`$
  and the pullback is nonzero);
* by the $`F`$-linearity of §1,
  $`\rho^F_{\omega_F}(f) = \rho^F_{\mathrm{pullback}\,\omega_{E,0}}(c f)`$;
* regroup the sum over $`\mathrm{Place}(F)`$ into fibres over
  $`\mathrm{Place}(E)`$;
* apply the fibre formula to replace each fibre sum by the residue term of
  $`\omega_{E,0}`$ against $`\mathrm{Tr}_{E/F}(c f)`$ at $`v`$;
* apply the residue theorem for $`E`$.

The last two lines are the content: $`\rho^F_{\omega_F}(f) = \rho^E_{\omega_{E,0}}(\mathrm{Tr}_{E/F}(cf)) = 0`$.
At $`E = K(X)`$ the fibre formula and the base case combine into the curve-level
statement
`residueTheoremK_of_cotraceResidueIdentityK_ratFunc_isAlgClosed`
([line 5666](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L5666)),
and with the localized form this is
`residueTheoremK_of_rowAK_ratFunc_isAlgClosed`
([line 6332](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L6332)).

## 4. The local input, and how the pieces compose

It remains to produce the fibre-integration formula. This is the point at which
the local Tate theory of [math/021](021-tate-residue.md) enters, through two
inputs.

**The completion trace sum.** For a finite separable extension of function
fields $`E \subseteq F`$ and a place $`v`$ of $`E`$, the trace down to the
completion at $`v`$ decomposes over the fibre:

$$\mathrm{algebraMap}\bigl(\mathrm{Tr}_{E/F}(g)\bigr) \\;=\\; \sum_{w \mid v} \mathrm{completionTraceAt}_w(g) \qquad \text{in } \hat E_v ,$$

`KwHgfV352CompletionTraceSum`
([Def_AlgebraicCurve_TateResidueCurrency.lean, lines 237–241](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L237-L241)),
where $`\mathrm{completionTraceAt}_w`$ is the trace of the local extension
$`\hat E_v \subseteq \hat F_w`$
([lines 197–200](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L197-L200)).
This is the standard local-field trace formula across a fibre. Its proof is a
semilocal decomposition: the completed tensor product
$`\hat E_v \otimes_E F`$ is the product of the completions $`\hat F_w`$ over the
finitely many $`w \mid v`$,

$$ \hat E_v \otimes_E F \\;\\cong\\; \prod_{w \mid v} \hat F_w ,$$

and under this isomorphism the trace becomes the sum of the local traces. The pin
proves the identification through the semilocal Chinese-remainder map
`kwF4R1V384a_semilocalDiag`
([line 7263](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L7263)),
its bijectivity for distinct maximal ideals
(`kwF4R1V384a_completionSemilocalBij_of_distinctKernels_finrankEF`,
[line 7401](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L7401)),
and the trace comparison
(`kwF4R1V384a_completionTraceSum_of_distinctKernels_finrankEF`,
[line 7488](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L7488));
separability of $`E \subseteq F`$ makes the local extension separable and the
comparison compatible with the traces
(`kwF4R1V386a_completionTraceSum_of_isSeparable`,
[line 7879](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L7879)).

**The residue-trace completion commutation (RTCC).** At each $`w \mid v`$, the
local residue term of the pulled-back differential equals the trace of the
completion trace:

$$\mathrm{kaehlerResidueTerm}\bigl(\mathrm{pullback}\\,\mathrm{d}\pi_v,\ g,\ w\bigr) \\;=\\; \mathrm{Tr}_{k(v)/K}\Bigl(\mathrm{Res}_v\bigl(\mathrm{completionTraceAt}_w(g)\bigr)\Bigr),$$

`KwF4R1V391aResidueTraceCompletionCommute`
([Def_AlgebraicCurve_TateResidueCurrency.lean, lines 368–376](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L368-L376)).
This is [math/021 §7](021-tate-residue.md): it is assembled from the agreement
theorem, the chain rule for the residue, and the compatibility of the Tate
residue with the completion trace.

**Composition.** Summing RTCC over the fibre and applying the completion trace
sum turns the fibre sum of local residue terms into the residue term of the
trace, which is exactly the fibre-integration formula. The pin packages this as
`kw_es_fiberKaehlerCotraceResidueIdentity_of_RTCC_CTS`
([line 7929](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L7929)).
Then the whole chain

```text
residueTheoremK_ratFunc_of_isAlgClosed        (base case, §2)
        + residueTraceCompletionCommute       (local input, math/021)
        + completionTraceSum                  (semilocal trace formula)
        -> FiberKaehlerCotraceResidueIdentity (fibre integration, §3)
        -> ResidueTheoremK K F                (descent)
```

is `kw_es_residueTheoremK_of_RTCC_isAlgClosed`
([line 7985](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L7985)),
and the headline is
`kwTateRR3_residueTheoremK_of_isAlgClosed`
([line 8082](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L8082)).

## 5. Characteristic $`p`$

The base case of §2 is characteristic-free as mathematics, but two of the
subrows it is assembled from — well-definedness of the order of a differential
and independence from the simple-pole coordinate — are formalized under
`[CharZero K]`
([line 6608](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L6608),
[line 10779](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L10779)).
The pin closes the gap with a second, characteristic-$`p`$ computation of the
same base case:
The pin closes the gap with a second, characteristic-$`p`$ computation of the
same base case:

* the residue is independent of the Kähler coordinate used to write the
  differential, proved by reducing to a uniformizer change and using the
  vanishing of $`\mathrm{Res}\bigl(\mathrm{coeff}(\mathrm{d}\pi')\cdot(\pi')^{-(n+1)}\bigr)`$
  for $`n \ge 1`$
  (`p0n22_cpf_canonicalLocalResidueKDifferentialCoordIndep_ratFunc_of_isAlgClosed`,
  [line 13117](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L13117));
* this coordinate independence is exactly the missing "subrow", and it yields
  `ResidueTheoremK K (K(X))` in characteristic $`p`$
  (`p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_of_charP`,
  [line 13125](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L13125)).

The two branches are combined by casing on the characteristic of $`K`$:
`p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_main`
([line 13132](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L13132)).
Since the FLT curve layer is used over $`\bar{\mathbb{Q}}`$, the characteristic-$`0`$
branch is the one that matters for the proof; the characteristic-$`p`$ branch is
the mathematically complete statement.

## 6. How the formalization writes it

The two files are organized as a supply chain of `Prop`-valued rows, each
stating one functoriality property, with the huge line counts coming from the
row-by-row verifications rather than from one long argument.

**The base case is a spanning argument.** `kaehlerResidueFunctionalK` is the
residue functional of the fixed generator $`\mathrm{d}X`$
([S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean, line 11735](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L11735)),
and the proof that it vanishes is `Submodule.span_le`: the partial-fraction
generators span everything, and the functional is checked on each generator
(`kaehlerResidueFunctionalK_dX_eq_zero`,
[line 11946](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean#L11946)).
The generator checks are where the residue computations live.

**The descent is an `F`-linearity computation.** The proof of
`residueTheoremK_of_cotraceResidueIdentityK` rewrites $`\omega_F`$ as a multiple
of the pulled-back generator using `differentialCoeff` and then uses
`kaehlerResidueTermKFam_smul_diagonal` to move the multiplier onto $`f`$, before
regrouping the sum into fibres and applying the fibre identity. The two
regrouping lemmas are `finsum_place_eq_finsum_fiber_sum` and the fibre identity
itself.

**The local input is imported, not reproved.** The descent file imports
`Theorems.Thm_AlgebraicCurve_residueTraceCompletionCommute` and
`Theorems.Thm_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed`, so the
8,121-line node is genuinely a composition of the local Tate theory, a semilocal
trace formula, and the $`\mathbb{P}^1`$ base case
([imports, lines 17–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L17-L18)).
This is the opposite of the pattern we found in
[studies/riemann-roch-strategy.md](../studies/riemann-roch-strategy.md) §3.1 for
the analytic Riemann–Roch node: here nothing is duplicated, and the residue
theorem really is the composition its name suggests.

### Key points, and where they are formalized

| mathematical point | Lean declaration | file |
|---|---|---|
| the statement | `ResidueTheoremK` | `Def_AlgebraicCurve_LocalResidue.lean:297` |
| the residue functional | `weilOfKaehlerK`, `kaehlerResidueFunctionalK` | `Def_AlgebraicCurve_LocalResidue.lean:264`; `S_..._ratFunc_of_isAlgClosed.lean:11735` |
| $`F`$-linearity in the differential | `kaehlerResidueTermKFam_smul_diagonal` | `S_..._of_isAlgClosed.lean:5470` |
| regroup a sum by fibres | `finsum_place_eq_finsum_fiber_sum` | `S_..._of_isAlgClosed.lean:2693` |
| partial fractions on $`\mathbb{P}^1`$ | `P1PartialFractionGenerators`, `p1PartialFractionSpan_eq_top` | `S_..._ratFunc_of_isAlgClosed.lean:1315`, `:2729` |
| principal-part atom $`c/p^m`$ | `p1PrincipalPartAtom` | `S_..._ratFunc_of_isAlgClosed.lean:2053` |
| polynomials have zero residue | `kaehlerResidueFunctionalK_dX_X_pow` | `S_..._ratFunc_of_isAlgClosed.lean:11836` |
| simple-pole cancellation | `p1PrincipalPartMOneSimplePoleCancel...`, `kaehlerResidueTermKFam_atom_mOne_two_place_sum` | `S_..._ratFunc_of_isAlgClosed.lean:9911`, `:11900` |
| higher poles have zero residue | `p1FinitePlaceCanonicalResidueAtomMGeTwoTraceHigherDeg` | `S_..._ratFunc_of_isAlgClosed.lean:7876` |
| base case $`\mathbb{P}^1`$ | `residueTheoremK_ratFunc_of_isAlgClosed` | `Thm_..._ratFunc_of_isAlgClosed.lean:16` |
| pullback of differentials | `kaehlerPullback` | `Def_AlgebraicCurve_TateResidueCurrency.lean:102` |
| fibre integration | `FiberKaehlerCotraceResidueIdentityK` | `Def_AlgebraicCurve_TateResidueCurrency.lean:399` |
| localized fibre form | `CotraceResidueIdentityOnFiberLocalizedK` | `Def_AlgebraicCurve_TateResidueCurrency.lean:432` |
| descent from $`\mathbb{P}^1`$ | `residueTheoremK_of_cotraceResidueIdentityK_ratFunc_isAlgClosed` | `S_..._of_isAlgClosed.lean:5666` |
| completion trace sum | `KwHgfV352CompletionTraceSum`, `..._of_isSeparable` | `Def_..._TateResidueCurrency.lean:237`; `S_..._of_isAlgClosed.lean:7879` |
| semilocal tensor decomposition | `kwF4R1V384a_semilocalDiag`, `..._completionSemilocalBij...` | `S_..._of_isAlgClosed.lean:7263`, `:7401` |
| local residue = completion trace | `KwF4R1V391aResidueTraceCompletionCommute` | `Def_..._TateResidueCurrency.lean:368` |
| fibre integration from RTCC | `kw_es_fiberKaehlerCotraceResidueIdentity_of_RTCC_CTS` | `S_..._of_isAlgClosed.lean:7929` |
| the headline | `residueTheoremK_of_isAlgClosed` | `Thm_..._of_isAlgClosed.lean:16` |
| characteristic $`p`$ base case | `p0n22_cpf_residueTheoremK_ratFunc_of_isAlgClosed_of_charP` | `S_..._ratFunc_of_isAlgClosed.lean:13125` |

## 7. What this note does not cover

* **The complex-analytic proof.** The theorem over $`\mathbb{C}`$ has a contour
  proof; this note is about the algebraic proof that works over any algebraically
  closed field. [math/021](021-tate-residue.md) explains why the algebraic
  residue agrees with the analytic one where both exist.
* **The Riemann–Roch consequences.** `residueTheoremK_of_isAlgClosed` is an input
  to the analytic / Tate route to Riemann–Roch and to the differentials layer;
  the Riemann–Roch engine itself is
  [base/019](../base/019-stichtenoth-genus-and-the-adelic-index.md), and the two
  routes are compared in
  [studies/riemann-roch-strategy.md](../studies/riemann-roch-strategy.md).
* **The non-analytic residue-theorem alternatives.** The pin also contains
  `residueTheorem_of_perfectField`, `residueTheorem_ratFunc_of_perfectField` and
  `residueTheorem_functionField_of_smoothOfRelativeDimension_one`, which are
  outside the Deligne–Serre cone and are not on the route described here.
* **The applications.** The differentials ↔ cusp-forms transport and the other
  per-file uses of the residue theorem are later phases.

## Links

* [math/021 — The Tate residue, and the agreement theorem](021-tate-residue.md)
  — the local input: the commutator definition of the residue, the agreement
  theorem, and the composition into `residueTraceCompletionCommute`.
* [base/009 — Differentials, residues, and Riemann–Roch](../base/009-differentials-residues-riemann-roch.md)
  — the residue theorem as a fact, and the differential theory it lives in.
* [base/015 — Places and their extensions](../base/015-places-and-extensions.md)
  — the fibre, ramification and inertia vocabulary behind the sum over $`w \mid v`$.
* [base/017 — The rational function field and principal divisors](../base/017-rational-function-field-and-principal-divisors.md)
  — the $`K(X)`$ model, its places, and the order function used in §2.
* [base/019 — Stichtenoth's genus and the adelic index](../base/019-stichtenoth-genus-and-the-adelic-index.md)
  — the engine that consumes the residue theorem.
* [studies/riemann-roch-strategy.md](../studies/riemann-roch-strategy.md) — the
  route measurement, and where `residueTheoremK_of_isAlgClosed` sits.
* FLT at the pinned sha `aa2d8b3`:
  [`S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean),
  [`S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean),
  [`Def_AlgebraicCurve_LocalResidue.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_LocalResidue.lean),
  [`Def_AlgebraicCurve_TateResidueCurrency.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean).
* J. Tate, *Residues of differentials on curves*, Annales scientifiques de
  l'École Normale Supérieure (4) **1** (1968), 149–159,
  [numdam](https://www.numdam.org/articles/10.24033/asens.1162/).
