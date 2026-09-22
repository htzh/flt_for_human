# Hecke operators: cosets, q-expansions, and the two matrices

This is the fourteenth `base/` note, and the third on the automorphic layer after
[002](002-modular-forms-basics.md) (what a `ModularForm` is in mathlib, and the
inventory of what mathlib lacks) and [004](004-the-j-invariant.md) (the
`j`-invariant). It exists because the project has now *reached* a Hecke operator:
[`FLTForHuman/ModularForms/Defs/HeckeOperator.lean`](../lean/FLTForHuman/ModularForms/Defs/HeckeOperator.lean)
defines two matrices and their action on `ℍ`, and the PhiGen segment consumes
them. A reader who opens that file — 114 lines, two `def`s and two `coe_*_smul`
theorems — is entitled to ask what the mathematical object is and why those two
matrices are the whole operator. This note answers that, then does two more
things: it works out the one place the formal proof already uses the matrices
(the Hecke-coset polynomial of the PhiGen segment), and it looks forward to where
the route is headed, where the same operators act on `J₀(N)` as correspondences
([math/009](../math/009-hecke-jacobian-commute.md)).

The one-sentence answer: **a Hecke operator is an average of slash actions over
the `ℓ+1` representatives of a double coset**
$`\Gamma_0(N)\begin{pmatrix}\ell&0\\0&1\end{pmatrix}\Gamma_0(N)`$; the two
matrices are the diagonal representative and the `ℓ` unipotent representatives;
and in the PhiGen segment they are used not to define eigenforms but to make a
*symmetric function* of `ℓ+1` translates invariant under all of
$`\mathrm{SL}_2(\mathbb{Z})`$.

Line numbers pin `anthropics/fermats-last-theorem@aa2d8b3`; mathlib citations
point at tag v4.33.0 (the port runs v4.34.0, where the cited declarations sit at
the same lines). Port modules are linked relatively: they are tracked in this
repository. The conventions of [001](001-field-extensions-and-galois-basics.md)
(`Algebra` towers, the `R → S → K` vocabulary) are assumed where a Lean statement
is quoted.

## 1. The double coset, and the two substitutions

**The slash action.** Fix a weight $`k \in \mathbb{Z}`$. For
$`g = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{GL}_2^+(\mathbb{Q})`$
(positive determinant, rational entries) and a function
$`f : \mathbb{H} \to \mathbb{C}`$, the weight-`k` slash action is

$$(f \mid_k g)(\tau) \\;=\\; (\det g)^{k-1}\\,(c\tau+d)^{-k}\\,f(g\tau).$$

In mathlib this is
[`ModularForm.slash_apply`](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L143),
stated for $`g \in \mathrm{GL}_2(\mathbb{R})`$ with a `σ g` twist for the
sign of the determinant and $`|\det g|`$ in place of $`\det g`$; on the
upper-triangular matrices below both agree with the display. The scoped notation
is `f ∣[k] g`, and the slash of a sum/product is the sum/product of the slashes,
which is what makes the finite averages below linear.

**The double coset.** Let

$$\Gamma_0(N) \\;=\\; \left\\{\begin{pmatrix}a&b\\c&d\end{pmatrix} \in
  \mathrm{SL}_2(\mathbb{Z}) \\;:\\; c \equiv 0 \pmod N\right\\}.$$

The Hecke operator at a prime $`\ell`$ is attached to the double coset

$$\Gamma_0(N)\begin{pmatrix}\ell&0\\\\0&1\end{pmatrix}\Gamma_0(N).$$

Its right cosets have $`\ell + 1`$ representatives, of two shapes:

$$\gamma_b \\;=\\; \begin{pmatrix}1&b\\\\0&\ell\end{pmatrix}
  \quad (0 \le b \le \ell-1), \qquad
  \gamma_\infty \\;=\\; \begin{pmatrix}\ell&0\\\\0&1\end{pmatrix}.$$

On $`\mathbb{H}`$ these act by the two substitutions that name the port's two
matrices:

$$\tau \\;\longmapsto\\; \frac{\tau+b}{\ell}
  \qquad\text{and}\qquad
  \tau \\;\longmapsto\\; \ell\tau .$$

Define the **unipotent sum** $`U_\ell`$ and the full **Hecke operator**
$`T_\ell`$ by averaging the slash over these representatives:

$$U_\ell f \\;=\\; \sum_{b=0}^{\ell-1} f \mid_k \gamma_b,
  \qquad
  T_\ell f \\;=\\; U_\ell f \\;+\\; f \mid_k \gamma_\infty .$$

Substituting the slash formula and the determinant $`\det\gamma_b = \ell`$,
$`\det\gamma_\infty = \ell`$:

$$U_\ell f(\tau) \\;=\\; \frac{1}{\ell}\sum_{b=0}^{\ell-1}
    f\\!\left(\frac{\tau+b}{\ell}\right),
  \qquad
  T_\ell f(\tau) \\;=\\; U_\ell f(\tau) \\;+\\; \ell^{\\,k-1} f(\ell\tau).$$

This is exactly Diamond–Shurman §5.2's normalisation; the code's
`slash_heckeMatrix_apply` and `slash_heckeDiagMatrix_apply` are the two
normalised pieces, and `heckeT = heckeU + slash heckeDiagMatrix` is the
definition. For a general integer $`n`$ the same construction with
$`\mathrm{diag}(n,1)`$ gives $`T_n`$; the prime operators generate.

**The level split, $`p \nmid N`$ versus $`p \mid N`$.** For
$`p \nmid N`$ the diagonal term $`f \mid_k \mathrm{diag}(p,1)`$ preserves
$`\Gamma_0(N)`$-invariance, and the full $`T_p`$ acts on $`M_k(\Gamma_0(N))`$
and $`S_k(\Gamma_0(N))`$. For $`p \mid N`$ it does not, and one keeps only
$`U_p`$, the unipotent sum — the operator that lowers the level and drives
newform/oldform theory. The FLT wrappers encode the split in the hypothesis of
the bundled linear map: `heckeTLin` takes `hpN : ¬ p ∣ N`, `heckeULin` takes
`hpN : p ∣ N`. The mathematical distinction is the same one
[008](../math/008-ribet-level-lowering.md) spends downstream, where the
$`U_\ell`$ at $`\ell \mid N`$ are what move between levels.

**The geometry.** The $`\ell+1`$ representatives are the labels of the
$`\ell`$-isogenies: the $`\ell+1`$ cyclic subgroups of order $`\ell`$ in
$`E[\ell]`$, equivalently the lines of $`\mathbb{F}_\ell^2`$, i.e. the points
of $`\mathbb{P}^1(\mathbb{F}_\ell)`$. The diagonal $`\gamma_\infty`$ is the
line at infinity, the $`\gamma_b`$ the finite slopes. This is the dictionary of
[005 §2](005-cyclic-isogenies-and-level.md) and
[006 §5](006-the-modular-equation.md); its $`q`$-expansion shadow is the slot
list $`j(u\zeta_\ell^{\,b}q^{e})`$ with the denominator-square exponent
$`a^2`$ of [006 §3](006-the-modular-equation.md). The code's `heckeRep` uses
`OnePoint (ZMod p)` for the label set, with `∞ ↦ heckeDiagMatrix` and
`j ↦ heckeMatrix j.val`.

## 2. The q-expansion action

Let $`q = e^{2\pi i\tau}`$ and $`f = \sum_{m \ge 0} a_m q^m`$ (the
nonnegative powers are holomorphy at the cusp). The two substitutions move the
nome by

$$\tau \mapsto \frac{\tau+b}{\ell}: \quad q \mapsto
    e^{2\pi i b/\ell} q^{1/\ell};
  \qquad
  \tau \mapsto \ell\tau: \quad q \mapsto q^{\ell}.$$

The $`\ell`$-term sum in $`U_\ell`$ is a root-of-unity filter. Because
$`\sum_{b=0}^{\ell-1} e^{2\pi i bm/\ell}`$ is $`\ell`$ when
$`\ell \mid m`$ and $`0`$ otherwise,

$$U_\ell f \\;=\\; \sum_{m \ge 0} a_{m\ell}\\,q^m,
  \qquad
  T_\ell f \\;=\\; \sum_{m \ge 0}\left(a_{m\ell} + \ell^{\\,k-1}a_{m/\ell}\right)q^m,$$

where $`a_{m/\ell}`$ is read as $`0`$ unless $`\ell \mid m`$. These two
coefficient rules are the whole arithmetic content of the operator: $`U_\ell`$
substitutes the index, $`T_\ell`$ adds the dilation term. The code states them
as `coeffHeckeU` and `coeffHeckeT`.

**The eigenform recursion.** Iterating gives
$`T_{\ell^{r+1}} = T_\ell T_{\ell^r} - \ell^{k-1}T_{\ell^{r-1}}`$. A normalised
eigenform ($`a_1 = 1`$, $`T_\ell f = \lambda_\ell f`$) then has
$`\lambda_\ell = a_\ell`$ and

$$a_{\ell^{r+2}} \\;=\\; a_\ell\\,a_{\ell^{r+1}} - \ell^{\\,k-1}a_{\ell^r},
  \qquad
  a_{\ell^{r+2}} \\;=\\; a_\ell\\,a_{\ell^{r+1}}\ \ (\ell \mid N),$$

the first for $`\ell \nmid N`$ and the second for $`\ell \mid N`$. Together
with $`a_{mn} = a_ma_n`$ for $`\gcd(m,n)=1`$, these are exactly the four clauses
of FLT's `IsNormalizedEigenform`
([Def_FLTPrelim_Modularity.lean, lines 28–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L28-L40)):
the Hecke operators themselves never appear in the structure. To use a modularity
hypothesis in this project one unfolds to coefficient recursions — that is
[002 §6](002-modular-forms-basics.md), and §5 below records where the operator
itself is still needed.

**Commutativity.** For the operators, $`T_mT_n = T_{mn}`$ when
$`(m,n) = 1`$, and $`T_mT_n = T_nT_m`$ in general (both follow from the
double-coset formalism). Commutativity is exactly what makes "simultaneous
eigenform" meaningful, and it is *proved*, not assumed, in the project: the
`heckeAlgebra` of §3 comes with an `IsMulCommutative` instance
([Def_CuspForm_HeckeAlgebra.lean, line 59](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean#L59)).
On the divisor side the same commutativity is the subject of
[math/009](../math/009-hecke-jacobian-commute.md).

## 3. The Lean encoding

### 3.1 The two matrices, in the port

The port's `Defs/HeckeOperator.lean` keeps exactly the two substitutions, as
elements of `GL (Fin 2) ℝ` built from an upper-triangular matrix:

```lean
-- FLTForHuman/ModularForms/Defs/HeckeOperator.lean, lines 53 and 57
def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ := ...    -- !![1, j; 0, p]
def heckeDiagMatrix (p : ℕ) : GL (Fin 2) ℝ := ...  -- !![p, 0; 0, 1]
```

$`\mathrm{diag}(p,1)`$ has $`1`$ in the lower-right corner, not $`p`$; the
$`p^{k-1}`$ factor of the dilation is carried by the slash normalisation
rather than by the matrix. The `if p = 0 then 1` branch is a junk value: it keeps
the definitions total without a `NeZero` hypothesis, exactly the pattern
`UpperHalfPlane`'s action wants, and every interesting theorem assumes
`hp : p ≠ 0`.

The action on $`\mathbb{H}`$ is two theorems:

```lean
-- lines 101 and 107
theorem coe_heckeMatrix_smul (hp : p ≠ 0) (j : ℕ) (τ : UpperHalfPlane) :
    ((heckeMatrix p j • τ : UpperHalfPlane) : ℂ) = ((τ : ℂ) + j) / p
theorem coe_heckeDiagMatrix_smul (hp : p ≠ 0) (τ : UpperHalfPlane) :
    ((heckeDiagMatrix p • τ : UpperHalfPlane) : ℂ) = (p : ℂ) * (τ : ℂ)
```

These are §1's $`\tau \mapsto (\tau+j)/p`$ and $`\tau \mapsto p\tau`$. They
are proved from `UpperHalfPlane.coe_smul_of_det_pos` plus the determinant and
denominator lemmas (`det_heckeMatrix`, `denom_heckeMatrix`, …); the positivity of
the determinant is `det_heckeMatrix_pos`, and it is what selects the identity
`σ`-branch of the action.

### 3.2 The operators, in FLT

`heckeU` and `heckeT` are the averages of §1
([Def_ModularForm_HeckeOperator.lean, lines 93 and 96](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean#L93-L96)):

```lean
def heckeU (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j

def heckeT (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p
```

so the classical double-coset average is, literally, a `Finset.range p` sum of
slash actions by the explicit matrices. `slash_heckeMatrix_apply` and
`slash_heckeDiagMatrix_apply` spell out the two normalised terms, `heckeT_apply`
is the display of §1, and `coeffHeckeT`/`coeffHeckeU` are §2's coefficient
formulas. The bundled endomorphisms, with the level split of §1, are
`heckeTLin`/`heckeULin` on `ModularForm` and on `CuspForm`
([Def_ModularForm_HeckeOperatorForms.lean, lines 20 and 34](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperatorForms.lean#L20-L34)),
and the Hecke algebra is

```lean
-- Def_CuspForm_HeckeAlgebra.lean, lines 14 and 18
def heckeGenerators : Set (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :=
  {T | ∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S ∧ T = heckeTLin k hℓ hℓN} ∪
    {U | ∃ (q : ℕ) (hqN : q ∣ N), q.Prime ∧ q ∉ S ∧ U = heckeULin k hqN}

def heckeAlgebra : Subalgebra ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) :=
  Algebra.adjoin ℤ (heckeGenerators N k S)
```

with commutativity as the instance cited above. `heckeAlgebra.T`/`.U` are the
generators as elements of the algebra.

### 3.3 What the port kept, and the mathlib gap

The port is deliberately a *subset*. `heckeMatrix`, `heckeDiagMatrix` and the two
`coe_*_smul` facts are public; `upperTriangularGL`, the `val_*`/`det_*`/`denom_*`
helpers and the zero-branch lemmas are private. Everything else FLT defines —
`heckeU`, `heckeT`, `coeffHeckeT`, `coeffHeckeU`, the `slash_hecke*` and
`σ_hecke*` families — is **dropped**: the T8 survey found 0 occurrences in its
five pin files, and elsewhere only in the doc-site toolchain's
`attribute [-simp] ModularForm.heckeU_zero …` pragma, never mathematically. A
later cone piece that needs the operators extends the module then. The header of
`Defs/HeckeOperator.lean` records this with counts; the note is the mathematics
behind the choice.

**mathlib has no Hecke operator on modular forms.** It has a generic,
group-theoretic Hecke-pair layer — `HeckeCoset`, `HeckeCosetModule`, the diagonal
`HeckeRing` `𝕋` in
[NumberTheory/HeckeRing/Defs.lean, lines 157, 183, 193](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/HeckeRing/Defs.lean#L157-L193)
— but it imports nothing about modular forms, has no action on them, and never
mentions a Hecke *algebra* of operators. The gap is the one
[002 §4](002-modular-forms-basics.md) inventories; it is why this project writes
the matrices itself.

## 4. The Hecke-coset polynomial in the PhiGen segment

This is the heart of the note: the one place the formal proof has already used
the Hecke matrices, and the reason they were worth porting at all.

### 4.1 What the segment proves, and where invariance enters

The PhiGen cone constructs the level-$`\ell`$ modular polynomial inside the
$`q`$-expansion field and proves the splitting

$$\Phi_\ell\bigl(j(q^{\ell}),\\, Y\bigr) \\;=\\;
  \bigl(Y - j(q^{\ell^2})\bigr)\prod_{b=0}^{\ell-1}
  \bigl(Y - j(\zeta_\ell^{\\,b}q)\bigr),$$

which is `PhiGen.splits_prime_at_slot`
([Thm file, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean#L10)).
The route ([base/013 §4](013-riemann-existence-and-the-q-expansion-principle.md),
[math/010](../math/010-function-field-generation.md)) builds the conjugate product

$$\prod_{i=0}^{\ell}\bigl(X - \mathrm{conj}_i\bigr),
  \qquad
  \mathrm{conj}_0 = j(q^{\ell^2}), \quad
  \mathrm{conj}_{b+1} = j(\zeta_\ell^{\\,b}q),$$

shows its coefficients descend to $`\mathbb{Q}((q))`$ (the twist plus Galois
invariance), are integral, and satisfy a pole bound, and then proves each
descended coefficient $`c_k`$ is a *polynomial in $`j`$* before assembling
the datum. The $`q`$-expansion of the slots is the code's `PhiGen.conj`:
`conj 0 = qExpand K (ℓ*ℓ) (coeffEmb K jq)` and
`conj (b+1) = qTwist (ζ^b) (coeffEmb K jq)`.

The third step — membership in $`\mathbb{Q}[j]`$ — is the level-one
q-expansion principle R1 of [base/013 §3](013-riemann-existence-and-the-q-expansion-principle.md).
Its hypothesis is not just that $`c_k`$ is a Laurent series: it is that $`c_k`$
is **realized** on $`\mathbb{H}`$ by a function invariant under
$`\mathrm{SL}_2(\mathbb{Z})`$. The formal conjugate product alone gives no such
function — its coefficients are formal Laurent series over the level-$`\ell`$
field. The Hecke operator supplies the realizing function, and it is the
*symmetric* product over the $`\ell+1`$ translates, not any individual
translate, that is invariant.

### 4.2 The coset polynomial

The realizing function is the **Hecke-coset polynomial**

$$C_\ell(\tau, X) \\;=\\;
  \bigl(X - j(\ell\tau)\bigr)
  \prod_{b=0}^{\ell-1}\bigl(X - j((\tau+b)/\ell)\bigr),$$

whose roots are the images of $`j`$ under the two substitutions of §1 — the
diagonal Hecke matrix and the $`\ell`$ unipotent ones. Its $`X`$-coefficients
are functions of $`\tau`$; the claim that makes the segment work is:

> **$`C_\ell`$ is invariant under $`\mathrm{SL}_2(\mathbb{Z})`$.**

This is `cosetPoly_smul`
([Thm file, line 5](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_cosetPoly_smul.lean#L5)),
and its proof is a statement about how $`\mathrm{SL}_2(\mathbb{Z})`$ permutes
the $`\ell+1`$ substitutions. That permutation is the Hecke operator's group
theory, and it is what §4.3 reads off.

### 4.3 The permutation of the cosets

The code labels the $`\ell+1`$ representatives by the points of
$`\mathbb{P}^1(\mathbb{F}_\ell)`$ (`heckeRep`), and the key commutation is
`heckeRep_mul`: for every $`g \in \mathrm{SL}_2(\mathbb{Z})`$ and every label
$`x`$ there are $`g' \in \mathrm{SL}_2(\mathbb{Z})`$ and a label $`x'`$ — the
image of $`x`$ under the permutation `redMatrix g` of the labels — with

$$\gamma_x \cdot g \\;=\\; g' \cdot \gamma_{x'}.$$

So right-multiplication by $`g`$ carries a coset representative to another coset
representative, up to a left $`\mathrm{SL}_2(\mathbb{Z})`$-factor. Since the
base function $`F`$ is left-$`\mathrm{SL}_2(\mathbb{Z})`$-invariant,

$$F\bigl(\gamma_x \cdot g \cdot \tau\bigr) \\;=\\;
  F\bigl(\gamma_{x'} \cdot \tau\bigr),$$

and as $`x`$ runs over all labels, $`x'`$ does too: **the multiset of the
$`\ell+1`$ translates is permuted.** Hence every symmetric function of the
roots is invariant, and in particular every coefficient of $`C_\ell`$. The
proof is `Equiv.prod_comp` over the finite label set, with the four
`heckeMatrix_mul_of_eq`/`heckeDiagMatrix_mul_of_eq` lemmas supplying the four
cases of the commutation (diagonal times diagonal, diagonal times unipotent,
unipotent times diagonal, unipotent times unipotent) by explicit matrix algebra
and a divisibility hypothesis; `redMatrix` is the induced permutation of the
labels.

For $`\ell = 2`$ the smallest case is visible: the product is
$`(X - j(2\tau))(X - j(\tau/2))(X - j((\tau+1)/2))`$, and the generator
$`\tau \mapsto \tau+1`$ fixes $`j(2\tau)`$ and swaps the two finite
translates, so it permutes the factors. The other generator
$`\tau \mapsto -1/\tau`$ is the nontrivial case, and it is exactly what the four
commutation lemmas verify; [006 §3](006-the-modular-equation.md) runs the
analogue for $`p = 3`$ with the four sheets and twelve loops.

### 4.4 The q-expansion face: the two Hecke translates

The invariance above is about evaluation on $`\mathbb{H}`$. To feed R1, one also
needs that the *descended series* $`c_k`$ is the $`q`$-expansion of the
$`k`$-th coefficient of $`C_\ell`$. That is where the two Hecke translations
of the nome are used, and it is why `RealL` is stated for a general period.

- **`heckeMatrix`**: $`\tau \mapsto (\tau+b)/\ell`$. Then
  $`q(\tau') = e^{2\pi i b/\ell}q^{1/\ell}`$, so the translate's $`q`$-expansion
  is the coefficient twist $`A_m \mapsto e^{2\pi i bm/\ell}A_m`$ at **period
  $`\ell`$**. This is `hasSum_qParam_heckeMatrix_smul`
  ([port, line 37](../lean/FLTForHuman/ModularForms/HeckeQExpansion.lean)).
- **`heckeDiagMatrix`**: $`\tau \mapsto \ell\tau`$. Then $`q(\tau') = q^{\ell}`$,
  which in the period-$`\ell`$ nome is $`q \mapsto q^{\ell^2}`$ — the ring map
  `qExpand ℂ (ℓ*ℓ)`. This is `hasSum_qParam_heckeDiagMatrix_smul`
  ([port, line 69](../lean/FLTForHuman/ModularForms/HeckeQExpansion.lean)).

These are the "analytic face of the Hecke action"
([base/013 §5.2](013-riemann-existence-and-the-q-expansion-principle.md)), and
they are pure algebra of the disc $`0 \lt |q| \lt 1`$: nothing compact is used.
In the port's T8 file the pieces are composed as follows. `realL_conjC_zero`
realizes the series `conjC 0 = qExpand ℂ (ℓ*ℓ) jqC` by
$`jt(\mathrm{heckeDiagMatrix}\,\ell \cdot \tau)`$, and `realL_conjC_succ`
realizes `conjC (b+1) = qTwist (ζ^b) jqC` by
$`jt(\mathrm{heckeMatrix}\,\ell\,b \cdot \tau)`$; `RealL.coeff_prod_X_sub_C`
takes the product; `realL_one_of_realL_qExpansion` reduces the period from
$`\ell`$ to $`1`$; and the headline applies T7's
`mem_adjoin_jq_of_hasSum_of_slash_invariant`. The result is

```lean
-- FLTForHuman/ModularForms/PhiGenDescends.lean, line 498
theorem mem_adjoin_jq_of_phiGenDescends ... (k : ℕ) :
    c k ∈ Algebra.adjoin ℚ {jq}
```

the cone's (c), proved by combining `hasSum_coeff_of_phiGenDescends` (the
realization) with `cosetPoly_smul` (the invariance).

### 4.5 Why this is the point: no level-`N` q-expansion principle

Classically the conjugate product's coefficients are modular functions on
$`X_0(\ell)`$; one could try to invoke the **level-$`\ell`$** q-expansion
principle. But that is R2's territory: it needs the compactness and connectedness
of $`X_0(\ell)`$, which [base/013 §4.3](013-riemann-existence-and-the-q-expansion-principle.md)
shows the formal proof specifically avoids. The Hecke-coset construction upgrades
the invariance to **level one**: $`C_\ell`$ is a symmetric function of the
Hecke translates, and the translates are permuted by all of
$`\mathrm{SL}_2(\mathbb{Z})`$, so its coefficients are level-one invariant and
R1 applies directly. The Hecke operator is thus the device that buys the whole
cone the right to use the cheap, already-isolated analytic input.

This also resolves the compression flagged in
[PORTING-PhiGen §7](../lean/PORTING-PhiGen.md): base/006 §6.3's "the pole bound
together with holomorphy makes each coefficient a polynomial in $`j(q)`$" is
really two facts. The pole bound bounds the *degree* of the witnessing polynomial;
the *membership* $`c_k \in \mathbb{Q}[j]`$ is R1, and R1's hypothesis is
supplied by the Hecke-coset invariance of this section. The Hecke matrices are not
decoration in the PhiGen segment — they are the reason the analysis stays at level
one.

## 5. The Hecke algebra, and the roadmap to $`J_0(N)`$

### 5.1 The algebra of operators

Commutativity (§2) turns the operators into a ring action. On a fixed space
$`S_k(\Gamma_0(N))`$, the **Hecke algebra** is the $`\mathbb{Z}`$-subalgebra
of $`\mathrm{End}`$ generated by the $`T_p`$ ($`p \nmid N`$) and $`U_q`$
($`q \mid N`$), encoded as `heckeAlgebra = Algebra.adjoin ℤ heckeGenerators`
and commutative by `heckeAlgebra.instIsMulCommutative`. An eigenform is a
simultaneous eigenvector; its eigenvalue system is a ring homomorphism to the
coefficient ring, and the kernel is the eigenideal. The abstract form of this,
used on the Galois side, is the free polynomial algebra

```lean
-- Def_HeckeGalois_EichlerShimura.lean, lines 14 and 16
abbrev HeckeAlg : Type := MvPolynomial Nat.Primes ℤ
def heckeGen (ℓ : Nat.Primes) : HeckeAlg := MvPolynomial.X ℓ
```

([base/011 §3](011-deformations-hecke-algebras-and-r-equals-t.md)), one generator
per prime — uniformly for $`T_\ell`$ and $`U_\ell`$, which is exactly what the
level-lowering machinery needs.

### 5.2 The faces of the same operator

The single double coset of §1 appears in the project in several formal guises.
They are the same operator, and a reader should not mistake the guises for
different mathematics.

| face | what it acts on | declarations |
|---|---|---|
| slash / coset | functions $`\mathbb{H} \to \mathbb{C}`$ | `heckeMatrix`, `heckeDiagMatrix`, `heckeU`, `heckeT`, `heckeTLin`, `heckeULin` |
| bundled algebra | $`M_k(\Gamma_0(N))`$, $`S_k(\Gamma_0(N))`$ | `heckeGenerators`, `heckeAlgebra` |
| $`q`$-expansion | coefficient sequences | `coeffHeckeT`, `coeffHeckeU`, `IsNormalizedEigenform` |
| divisor correspondence | $`\mathrm{Pic}^0 = J_0(N)`$ | `heckeAlphaBar`, `heckeBetaBar`, `heckeOperatorBar` |
| abstract Hecke algebra | a $`\mathbb{T}`$-module | `HeckeAlg`, `heckeGen` |
| adelic | fixed vectors of an automorphic rep | `HeckeOperator`, `heckeSubmodule`/`HeckeAlgebra` ([base/012 §6](012-adeles-and-automorphic-representations.md)) |

The first three are the automorphic face this note is about; the
divisor-correspondence row is where the route is headed (§5.3), and the abstract
and adelic rows are the encodings the other notes own. The automorphic definition
by slash averages and the geometric definition by correspondences are related by
duality: under the Abel–Jacobi comparison of §5.3 the cusp-form Hecke operator is
intertwined with the *transpose* of the divisor-side operator.

### 5.3 Where this is going: $`T_\ell`$ on $`J_0(N)`$

[math/009](../math/009-hecke-jacobian-commute.md) is the note for the modular-curve
side, and it is worth stating its shape here so the forward reference is precise.
There the curve is a field, a point is a valuation, and the Jacobian is the
degree-zero divisor class group

```lean
-- Def_ModularCurve_ArithmeticGalois.lean, lines 115–116
abbrev JZero : Type _ := Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
```

The operator is built from the two degeneracy maps
$`\alpha : X_0(N\ell) \to X_0(N)`$ and $`\beta : X_0(N\ell) \to X_0(N)`$
(the forget map and the $`q \mapsto q^\ell`$ map) as the correspondence

$$T_\ell \\;=\\; \alpha_{\ast} \circ \beta^{\ast},$$

pull back to the $`(\ell+1)`$-point fibre, push forward along the other leg
([Def_ModularCurve_HeckeOperator.lean, lines 66–70 and 98–104](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperator.lean#L66-L104)).
On modular forms this is the same normalisation
$`T_\ell f = \ell^{k-1}\mathrm{tr}(\beta^*f)`$ of Diamond–Shurman §5.2,
transposed to divisors. The headline theorem is that these correspondences
commute for all primes — including the $`\ell \mid N`$ cases, where the note's
$`U_\ell`$ appears —

```lean
-- Thm_ModularCurve_heckeOperatorsCommuteBar.lean, line 9
theorem ModularCurve.heckeOperatorsCommuteBar (N : ℕ) [NeZero N] : ...
```

and commutation is what licenses the $`\mathbb{T}`$-module structure
`heckeModuleBar` and the Galois-equivariance
`smulCommClass_JZero_of_heckeOperatorsCommuteBar`. Downstream that is the input
to the Eichler–Shimura congruence, the maximal ideals $`\mathfrak{m}`$ and the
$`\mathfrak{m}`$-torsion of [008](../math/008-ribet-level-lowering.md). Finally,
the honest comparison between the divisor-class $`J_0(N)`$ and the classical
analytic one is a Hecke-equivariant Abel–Jacobi injection

$$J_0(N)(\bar{\mathbb{Q}}) \\;\hookrightarrow\\; S_2(\Gamma_0(N))^{\vee} / \Lambda_N,$$

which is where the operator of this note and the correspondence meet.

## 6. Key point → declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| slash action, $`f \mid_k g`$ | `SlashAction.map`, `ModularForm.slash_apply` | [mathlib v4.33.0, line 143](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L143) |
| the diagonal Hecke matrix $`\mathrm{diag}(p,1)`$ | `heckeDiagMatrix` | [port line 57](../lean/FLTForHuman/ModularForms/Defs/HeckeOperator.lean) |
| the unipotent Hecke matrices $`\begin{pmatrix}1&j\\0&p\end{pmatrix}`$ | `heckeMatrix` | [port line 53](../lean/FLTForHuman/ModularForms/Defs/HeckeOperator.lean) |
| $`\mathrm{diag}(p,1) \cdot \tau = p\tau`$ | `coe_heckeDiagMatrix_smul` | [port line 107](../lean/FLTForHuman/ModularForms/Defs/HeckeOperator.lean) |
| $`\begin{pmatrix}1&j\\0&p\end{pmatrix} \cdot \tau = (\tau+j)/p`$ | `coe_heckeMatrix_smul` | [port line 101](../lean/FLTForHuman/ModularForms/Defs/HeckeOperator.lean) |
| the average defining $`U_p`$ | `heckeU` | [FLT line 93](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean#L93) |
| $`T_p = U_p + [\mathrm{diag}(p,1)]`$ | `heckeT` | [FLT line 96](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean#L96) |
| $`U_p`$ on coefficients: $`a_{mp}`$ | `coeffHeckeU` | [FLT line 165](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean#L165) |
| $`T_p`$ on coefficients: $`a_{mp} + p^{k-1}a_{m/p}`$ | `coeffHeckeT` | [FLT line 162](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean#L162) |
| bundled $`T_p`$, $`p \nmid N`$ | `heckeTLin` | [FLT line 20](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperatorForms.lean#L20) |
| bundled $`U_p`$, $`p \mid N`$ | `heckeULin` | [FLT line 34](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperatorForms.lean#L34) |
| the Hecke algebra as an `Algebra.adjoin` | `heckeAlgebra` | [FLT line 18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean#L18) |
| it is commutative | `heckeAlgebra.instIsMulCommutative` | [FLT line 59](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean#L59) |
| eigenform as four coefficient recursions | `IsNormalizedEigenform` | [FLT lines 28–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean#L28-L40) |
| abstract Hecke algebra $`\mathbb{T}`$ | `HeckeAlg`, `heckeGen` | [FLT lines 14, 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L14-L16) |
| the coset polynomial is $`\mathrm{SL}_2(\mathbb{Z})`$-invariant | `cosetPoly_smul` | [port line 298](../lean/FLTForHuman/ModularForms/PhiGenDescends.lean) |
| the $`(\tau+b)/\ell`$ translate at period $`\ell`$ | `hasSum_qParam_heckeMatrix_smul` | [port line 37](../lean/FLTForHuman/ModularForms/HeckeQExpansion.lean) |
| the $`\ell\tau`$ translate gives $`q \mapsto q^{\ell^2}`$ | `hasSum_qParam_heckeDiagMatrix_smul` | [port line 69](../lean/FLTForHuman/ModularForms/HeckeQExpansion.lean) |
| realization predicate with general period | `RealL` | [port line 230](../lean/FLTForHuman/ModularForms/Hauptmodul.lean) |
| R1: level-one invariant realisation lies in $`\mathbb{Q}[j]`$ | `mem_adjoin_jq_of_hasSum_of_slash_invariant` | [port line 452](../lean/FLTForHuman/ModularForms/Hauptmodul.lean) |
| the cone's (c): descended coefficients lie in $`\mathbb{Q}[j]`$ | `mem_adjoin_jq_of_phiGenDescends` | [port line 498](../lean/FLTForHuman/ModularForms/PhiGenDescends.lean) |
| $`T_\ell = \alpha_\ast\beta^\ast`$ on $`J_0(N)`$ | `heckeOperatorBar` | [FLT lines 16–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean#L16-L18) |
| all $`T_\ell`$ commute on $`J_0(N)`$ | `heckeOperatorsCommuteBar` | [FLT line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean#L9) |

## 7. Links

Port modules in this repository (tracked):

- [`lean/FLTForHuman/ModularForms/Defs/HeckeOperator.lean`](../lean/FLTForHuman/ModularForms/Defs/HeckeOperator.lean) — `heckeMatrix`, `heckeDiagMatrix`, the two `coe_*_smul` facts
- [`lean/FLTForHuman/ModularForms/HeckeQExpansion.lean`](../lean/FLTForHuman/ModularForms/HeckeQExpansion.lean) — the two Hecke translates on the $`q`$-expansion
- [`lean/FLTForHuman/ModularForms/PhiGenDescends.lean`](../lean/FLTForHuman/ModularForms/PhiGenDescends.lean) — `cosetPoly_smul`, `mem_adjoin_jq_of_phiGenDescends`
- [`lean/FLTForHuman/ModularForms/Hauptmodul.lean`](../lean/FLTForHuman/ModularForms/Hauptmodul.lean) — `RealL`, the R1 headline
- [`lean/FLTForHuman/ModularCurve/Defs/PhiGen.lean`](../lean/FLTForHuman/ModularCurve/Defs/PhiGen.lean) — `cosetSubst`, `cosetA`/`cosetB`, `conj`, `phiProd`, `PhiGenDescends`

FLT sources at the pinned sha `aa2d8b3`:

- [Definitions/Def_ModularForm_HeckeOperator.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean) — the matrices, the averages, the coefficient maps
- [Definitions/Def_ModularForm_HeckeOperatorForms.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperatorForms.lean) — `heckeTLin`, `heckeULin` and the level split
- [Definitions/Def_CuspForm_HeckeAlgebra.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeAlgebra.lean) — `heckeGenerators`, `heckeAlgebra`, commutativity
- [Definitions/Def_FLTPrelim_Modularity.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_Modularity.lean) — `IsNormalizedEigenform`
- [Definitions/Def_HeckeGalois_EichlerShimura.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean) — `HeckeAlg`, `heckeGen`
- [P2M/Sol/S_ModularCurve_cosetPoly_smul.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_cosetPoly_smul.lean) — the $`\mathrm{SL}_2(\mathbb{Z})`$-invariance of the coset polynomial
- [Definitions/Def_ModularCurve_PhiGen.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PhiGen.lean) — `cosetSubst`, `conj`, `phiProd`, `PhiGenDescends`
- [Definitions/Def_ModularCurve_HeckeOperator.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeOperator.lean) — `heckeAlphaBar`, `heckeBetaBar`
- [Definitions/Def_ModularCurve_HeckeModule.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_HeckeModule.lean) — `heckeOperatorBar`, `HeckeOperatorsCommuteBar`, `heckeModuleBar`
- [Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorsCommuteBar.lean) — the divisor-side headline

mathlib at tag `v4.33.0`:

- [NumberTheory/ModularForms/SlashActions.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L143) — `SlashAction`, `ModularForm.slash_apply`
- [NumberTheory/HeckeRing/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/HeckeRing/Defs.lean#L157-L193) — `HeckeCoset`, `HeckeCosetModule`, `HeckeRing` (no action on modular forms)

Companion notes:

- [002 — Modular forms at the mathlib level](002-modular-forms-basics.md) — the automorphic definitions and the FLT-layer Hecke inventory (§§4–6)
- [005 — Cyclic isogenies, congruence level, and the j-invariant](005-cyclic-isogenies-and-level.md) — the $`\ell+1`$ subgroups, the two substitutions, the coset table
- [006 — The modular equation](006-the-modular-equation.md) — the cover, the twist/diamond, and the Hecke labels (§5), with the $`p=3`$ example
- [base/013 — Riemann existence and the level-one q-expansion principle](013-riemann-existence-and-the-q-expansion-principle.md) — R1, R2, and the Hecke-coset application (§§4.3, 5.2, 5.6)
- [base/011 — Deformations, Hecke algebras, and $`R = T`$](011-deformations-hecke-algebras-and-r-equals-t.md) — the Hecke algebra on the Galois side
- [base/012 — Adeles and automorphic representations](012-adeles-and-automorphic-representations.md) — the local/adelic Hecke operators
- [math/008 — Ribet's level lowering](../math/008-ribet-level-lowering.md) — the $`\mathfrak{m}`$-torsion Hecke-module downstream
- [math/009 — The Hecke action on the Jacobian](../math/009-hecke-jacobian-commute.md) — the divisor-side operator, $`T_\ell = \alpha_\ast\beta^\ast`$, and its commutativity
- [math/010 — Function field generation](../math/010-function-field-generation.md) — the conjugate-product route the PhiGen segment takes

Background:

- F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005, §5.2 — the double-coset definition, the $`T_p`$/$`U_p`$ split, the modular equation.
- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton 1971, Ch. 3 — the Hecke ring and its action.
- J.-P. Serre, *A Course in Arithmetic*, GTM 7, Springer 1973, Ch. VII — the $`q`$-expansion recursions.
