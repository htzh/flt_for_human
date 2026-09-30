# The Tate residue, and the agreement theorem

Twenty-first of the `math/` notes. [base/009](../base/009-differentials-residues-riemann-roch.md)
introduced differentials, their orders and divisors, the local residue, and the
residue theorem, and [base/019](../base/019-stichtenoth-genus-and-the-adelic-index.md)
opened the adelic / Stichtenoth engine that consumes them. This note opens up one
step of that route: the algebraic definition of the residue over a field that is
not $`\mathbb{C}`$, and the theorem that ties it to the classical analytic
residue. The declaration is `tateAgreement`
([Thm_AlgebraicCurve_tateAgreement.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_tateAgreement.lean)),
and its content is John Tate's 1968 construction of residues as *traces of
commutators* in the completion of the function field at a place.

The point of the construction, and the reason it belongs in the main proof route
rather than in `base/`, is that it replaces the complex topology. The classical
residue is the contour integral $`\frac{1}{2\pi i}\oint`$; the FLT curve layer
runs over an arbitrary field — the Stichtenoth engine and the analytic / Tate
route to Riemann–Roch are both stated for an arbitrary algebraically closed field
$`K`$, and the arithmetic side works over finite fields. Over a general field
there is no contour, but the *coefficient of* $`\pi^{-1}`$ in the Laurent
expansion at a uniformizer is a perfectly algebraic quantity. Tate's
contribution is a canonical way to extract it with no choices, as the trace of a
commutator, together with the functoriality (change of variables, traces in
extensions) that makes it usable. `tateAgreement` is the formalized statement
that this commutator trace computes the trace of the local residue; it is what
makes `residueTheoremK_of_isAlgClosed` a theorem about arbitrary algebraically
closed fields rather than about $`\mathbb{C}`$.

Math first: §§1–7 are the mathematics, §8 summarizes the Lean encoding. Line
numbers point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib declarations
are named at tag **v4.33.0**. The pin citations are rendered GitHub links
carrying `#L` anchors.

The plan:

1. what a residue is, and what fails over a general field;
2. the local arithmetic: the completion at a place, its integers, and the
   uniformizer;
3. the local residue, axiomatically, and the trace down to $`K`$;
4. Tate's commutator residue, and why a commutator is the right shape;
5. the agreement theorem $`\mathrm{TateRes}(f) = \mathrm{Tr}(\mathrm{Res}(f))`$;
6. how it is proved, by a Cohen–Laurent expansion of the completion;
7. from one place to the global residue theorem, and on to Riemann–Roch;
8. the Lean encoding and the key-point map.

## 1. What a residue is, and what fails over a general field

Let $`X`$ be a smooth projective curve over a field $`K`$, with function field
$`F`$. At a closed point $`v`$ choose a local uniformizer $`\pi`$; then a
Kähler differential $`\omega \in \Omega_{F/K}`$ can be written
$`\omega = f\,\mathrm{d}\pi`$ near $`v`$ for a unique $`f \in F`$ (the single
dimension of $`\Omega`$ recalled in
[base/009 §1](../base/009-differentials-residues-riemann-roch.md)). Over
$`K = \mathbb{C}`$ the **residue** of $`\omega`$ at $`v`$ is

$$\mathrm{Res}_v(\omega) \\;=\\; \frac{1}{2\pi i}\oint_{|z|=r} \omega ,$$

and writing the Laurent expansion $`f = \sum_{j \ge -N} a_j \pi^j`$ one has
$`\mathrm{Res}_v(\omega) = a_{-1}`$. The **residue theorem** is the global
statement

$$\sum_{v} \mathrm{Res}_v(\omega) \\;=\\; 0 ,$$

and its proof over $`\mathbb{C}`$ is a contour argument: cut the surface into
regions with boundary, and the boundary integrals cancel.

For the FLT proof neither the integral nor the cancellation is available. The
curve layer is stated for an arbitrary algebraically closed field
(`[IsAlgClosed K]`, not `K = ℂ`) and for perfect fields such as finite fields;
the Stichtenoth engine of
[base/019](../base/019-stichtenoth-genus-and-the-adelic-index.md) needs the
residue theorem only through its divisor and duality consequences. What survives
over a general field is the *algebraic* content of the residue: the coefficient
$`a_{-1}`$ of the Laurent expansion, and the fact that it is antisymmetric,
$`\mathrm{Res}_v(f\,\mathrm{d}g) + \mathrm{Res}_v(g\,\mathrm{d}f) = 0`$ (because
$`\mathrm{d}(fg)`$ has no residue). What has to be rebuilt is a **canonical**
definition — one that does not depend on a choice of Laurent representatives —
together with the trace and change-of-variable properties, and the global
cancellation.

The pin's target is the statement `ResidueTheorem` / `ResidueTheoremK`: for a
nonzero $`\omega`$ and every $`f \in F`$,

$$\sum_{v} \mathrm{Tr}_{k(v)/K}\bigl(\mathrm{Res}_v(f\\,\omega)\bigr) \\;=\\; 0 ,$$

equivalently that the adelic functional
$`\alpha \mapsto \sum_v \mathrm{Tr}_{k(v)/K}(\mathrm{Res}_v(\alpha_v\,\omega))`$
vanishes on the diagonal
([Def_AlgebraicCurve_WeilOfKaehler.lean, lines 78–109](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_WeilOfKaehler.lean#L78-L109)).
The trace $`\mathrm{Tr}_{k(v)/K}`$ is present because the residue naturally lives
in the residue field $`k(v)`$, which is a finite extension of $`K`$; tracing it
down to $`K`$ is what makes the global sum an element of $`K`$. This note is about the local object
$`\mathrm{Res}_v`$ and the identity that computes
$`\mathrm{Tr}_{k(v)/K}(\mathrm{Res}_v(-))`$ as a commutator trace in the
completion.

## 2. The local arithmetic: the completion at a place

Fix a perfect field $`K`$, a curve $`L/K`$ in the sense of
`IsCurveOver` ([base/019 §1](../base/019-stichtenoth-genus-and-the-adelic-index.md)),
and a place $`u`$ of $`L/K`$. Attached to $`u`$ are:

* the **completion** $`\hat L_u`$, the adic completion of $`L`$ at the maximal
  ideal of the valuation ring,
  ([Def_AlgebraicCurve_PlaceCompletion.lean, lines 31–34](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean#L31-L34));
  it is a complete discrete valuation ring;
* its **integers** $`\hat{\mathcal O}_u`$, the valuation ring of the completion;
* the **residue field** $`k(u)`$, which is finite-dimensional over $`K`$ by the
  curve hypothesis (the pin's `FiniteResidue`);
* a **uniformizer** $`\pi = u.\mathrm{uniformizer}`$, of order one, so that
  $`u.\mathrm{ord}(\pi) = 1`$
  ([Def_ModularCurve_CanonicalDivisor.lean, lines 15–33](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_CanonicalDivisor.lean#L15-L33)).

The field $`L`$ embeds densely in $`\hat L_u`$
(`denseRange_algebraMap`), so every element of the completion can be
approximated by an element of $`L`$ modulo any power of $`\pi`$. The completion
splits, as a $`K`$-vector space, into its integers and a space of **principal
parts**:

$$\hat L_u = \hat{\mathcal O}_u \oplus B , \qquad B \text{ a complement spanned by negative powers of } \pi .$$

The splitting is not canonical: the integers are not a canonical direct summand,
and different complements $`B`$ give different projections onto
$`\hat{\mathcal O}_u`$. That non-canonicity is the technical heart of Tate's
definition and of the agreement theorem.

## 3. The local residue, axiomatically

The residue is the coefficient of $`\pi^{-1}`$. The pin packages the properties
it must have as a structure rather than as a formula:

```lean
structure LocalResidueData where
  res : F →ₗ[K] v.ResidueField
  res_of_mem : ∀ f : F, f ∈ v.toValuationSubring → res f = 0
  res_simplePole : ∀ (f : F) (hf : v.uniformizer * f ∈ v.toValuationSubring),
    res f = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩
```

([Def_AlgebraicCurve_LocalResidue.lean, lines 20–27](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_LocalResidue.lean#L20-L27)),
together with the vanishing of all other negative monomials,

```lean
structure CanonicalLocalResidueDataK extends v.LocalResidueData where
  res_higherPoleMonomial : ∀ (n : ℕ), 1 ≤ n → res (v.uniformizer ^ (n + 1))⁻¹ = 0
```

([lines 29–31](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_LocalResidue.lean#L29-L31)).
These are exactly the properties of $`a_{-1}`$: `res` is $`K`$-linear, vanishes
on the valuation ring, and reads off the simple pole, while the powers
$`\pi^{-(n+1)}`$, $`n \ge 1`$, have residue zero. The residue of a general
element is obtained from these by linearity and the Laurent decomposition; the
axioms are the interface, and `localResidue` is the chosen datum
([lines 71–88](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_LocalResidue.lean#L71-L88)).

Two facts about this residue are used everywhere. It vanishes whenever the order
is non-negative, $`u.\mathrm{ord}(f) \ge 0 \Rightarrow \mathrm{Res}_u(f) = 0`$,
and on the uniformizer's inverse it is one,
$`\mathrm{Res}_u(\pi^{-1}) = 1`$
([lines 90–105](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_LocalResidue.lean#L90-L105)).
The **residue term** of a differential times an adele is then the trace to $`K`$,

$$\mathrm{kaehlerResidueTerm}(\omega, \alpha, v) \\;=\\; \mathrm{Tr}_{k(v)/K}\bigl(\mathrm{Res}_v(\alpha_v \cdot \mathrm{coeff}_v(\omega))\bigr),$$

where $`\mathrm{coeff}_v(\omega)`$ is the coefficient of $`\omega`$ against the
local coordinate $`\mathrm{d}\pi`$
([line 111](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_LocalResidue.lean#L111)).
The global residue theorem is the statement that the sum of these terms over all
places vanishes on principal adeles
([Def_AlgebraicCurve_WeilOfKaehler.lean, lines 107–109](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_WeilOfKaehler.lean#L107-L109)),
and it is proved by reducing it to the local identity of §5.

Over a perfect field an instance of this residue exists canonically, and the
construction is instructive for §6: a primitive element of the finite separable
extension $`k(u)/K`$ is lifted to a root of its minimal polynomial in the
completion (Hensel), producing a $`K`$-algebra section
$`\sigma : k(u) \hookrightarrow \hat{\mathcal O}_u`$; the residue is then read off
from the resulting Laurent expansion
([lines 2005–2060](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean#L2005-L2060),
[lines 2137–2156](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean#L2137-L2156)).
The section $`\sigma`$ is exactly the **Cohen section** used again in §6.

## 4. Tate's commutator residue

Tate's observation
([J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS (4) **1** (1968), 149–159](https://www.numdam.org/articles/10.24033/asens.1162/))
is that the residue can be computed as the trace of a commutator of operators on
the completion. The intuition is the antisymmetry of §1: the residue pairing
$`(f,g) \mapsto \mathrm{Res}(f\,\mathrm{d}g)`$ is antisymmetric, and
antisymmetric pairings are what commutators produce. Concretely, with $`V`$ a
Laurent-series space, $`A \subseteq V`$ the power series (the integers), and
$`p_A`$ a projection of $`V`$ onto $`A`$, the operator
$`p_A \circ m_f \circ p_A`$ is an "approximation" of multiplication by $`f`$
that lands in the integers; the commutator

$$T_{f,g} \\;=\\; p_A m_f p_A m_g - p_A m_g p_A m_f$$

is the antisymmetric correction, and its trace is the residue of
$`f\,\mathrm{d}g`$. The definition is well posed because changing the projection
changes each approximation by an operator of finite-dimensional image, and the
commutator of such a correction with the other approximation is again of
finite-dimensional image, hence has trace zero. This is the "trace class"
reasoning behind the well-definedness.

The pin formalizes exactly this. The projection onto the integers is
`tateProj`, built from an arbitrary complement of the integers,

```lean
def tateProj : u.adicCompletion →ₗ[K] u.adicCompletion :=
  letI B := Classical.choose (Submodule.exists_isCompl (adicIntegersKSubmod u))
  (adicIntegersKSubmod u).subtype ∘ₗ
    Submodule.projectionOnto (adicIntegersKSubmod u) B (Classical.choose_spec ...)
```

([Def_AlgebraicCurve_TateResidueCurrency.lean, lines 274–278](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L274-L278)).
The commutator and the trace of its restriction to the integers are

```lean
def tateComm (pA φ ψ : V →ₗ[K] V) : V →ₗ[K] V :=
  pA ∘ₗ φ ∘ₗ pA ∘ₗ ψ - pA ∘ₗ ψ ∘ₗ pA ∘ₗ φ

def tateCommTrace (pA φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ ψ))] : K :=
  finrankTrace (tateCommRestrict pA φ ψ)
```

([lines 38–61](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L38-L61)),
and the **Tate residue** of $`fh \in \hat L_u`$ at the place $`u`$, with the
uniformizer as the second operator, is

$$\mathrm{tateRes}_u(fh) \\;=\\; \mathrm{tateCommTrace}\bigl(\mathrm{tateProj}_u,\ m_{fh},\ m_{\pi}\bigr)$$

([lines 286–292](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L286-L292)).
Three mathematical points are built into this definition:

* **The trace is taken on the range of the commutator.** The completion is
  infinite-dimensional over $`K`$, so the trace of the whole operator is not
  defined; the commutator, however, has finite-dimensional image. `finrankTrace`
  defines the trace of an operator by restricting to its range
  ([lines 28–30](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L28-L30)),
  and the hypothesis that this range is finite-dimensional is the separate
  atom `KwF4gRRTateCommFinite`
  ([line 300](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L300)).
  It holds because the commutator's image is confined to a bounded pole window
  and the quotients $`\hat{\mathcal O}_u/\pi^M`$ are finite-dimensional over
  $`K`$ when the residue field is finite
  ([S_AlgebraicCurve_tateCommFinite.lean, lines 971–1050](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean#L971-L1050),
  [lines 1234–1252](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean#L1234-L1252)).
* **The commutator is antisymmetric**, $`T_{f,g} = -T_{g,f}`$
  ([lines 48–50](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L48-L50)),
  matching the antisymmetry $`\mathrm{Res}(f\,\mathrm{d}g) = -\mathrm{Res}(g\,\mathrm{d}f)`$.
* **The value does not depend on the projection.** Two idempotent projections
  with the same range (the integers) differ by an operator with image in a
  finite-dimensional space, so the commutator traces agree; this is the pin's
  `KwF4gRRTateProjectorIndep` / `SameRangeIdemProjectors`
  ([S_AlgebraicCurve_tateAgreement.lean, lines 1831–1886 and 2844](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L1831-L1886)).

On monomials the definition reproduces the residue: for the truncated shift
operators $`S(a)`$, $`S(b)`$ approximating multiplication by $`t^a`$, $`t^b`$,
the commutator has finitely many nonzero entries, all on the diagonal
$`i = j + a + b`$, so its trace is $`b`$ when $`a + b = 0`$ and $`0`$ otherwise —
exactly $`\mathrm{Res}(t^a\,\mathrm{d}(t^b))`$.

## 5. The agreement theorem

`tateAgreement` states that the commutator trace is the trace of the local
residue. For every place $`u`$ and every $`fh \in \hat L_u`$,

$$\mathrm{tateRes}_u(fh) \\;=\\; \mathrm{Tr}_{k(u)/K}\bigl(\mathrm{Res}_u(fh)\bigr),$$

where $`\mathrm{Res}_u`$ is extended to the completion by choosing, for
$`fh \in \hat L_u`$, an element $`x \in L`$ with $`x - fh \in \hat{\mathcal O}_u`$
and setting $`\mathrm{Res}_u(fh) = \mathrm{Res}_u(x)`$; the choice does not matter
because the residue vanishes on the integers
([Def_AlgebraicCurve_PlaceCompletion.lean, lines 477–495](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean#L477-L495),
[Def_AlgebraicCurve_TateResidueCurrency.lean, lines 185–188 and 307–311](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L185-L188)).
The formal statement is the `Prop`

```lean
def KwF4gRRTateAgreement (hfin : KwF4gRRTateCommFinite K L) : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (fh : u.adicCompletion),
    tateRes u fh (algebraMap L u.adicCompletion u.uniformizer)
      = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh)
```

([Def_AlgebraicCurve_TateResidueCurrency.lean, lines 307–311](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L307-L311)),
with the theorem `tateAgreement` supplying it for a curve over a perfect field
([Thm_AlgebraicCurve_tateAgreement.lean, line 19](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_tateAgreement.lean#L19)).

Over $`K = \mathbb{C}`$, or any algebraically closed field, the residue field
$`k(u)`$ is $`K`$ itself (every closed point has degree one), so the trace on the
right is the identity and the theorem reads
$`\mathrm{tateRes}_u(f) = \mathrm{Res}_u(f)`$: the commutator trace *is* the
classical residue. This is the precise sense in which Tate's theorem generalizes
the contour definition, and it is why the pin can state the residue theorem over
an arbitrary algebraically closed field.

## 6. How the agreement is proved: a Cohen–Laurent expansion

The agreement is not formal from the definitions: the left side is computed with
an arbitrary projection $`p_A`$, the right side with the axiomatic residue, and
the bridge is an explicit resolution of the completion. The proof has the
following shape.

**A canonical projector.** The arbitrary projection is replaced by one built
from a **Cohen section** $`\sigma : k(u) \to \hat{\mathcal O}_u`$, a
$`K`$-algebra section of the residue map,
([Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean, lines 956–963](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean#L956-L963)).
Such a section exists over a perfect field: the finite extension $`k(u)/K`$ is
separable, a primitive element generates it, and Hensel's lemma lifts the root of
its minimal polynomial to the completion
(`completionSection_nonempty_generic`,
[lines 2137–2146](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean#L2137-L2146)).
This is where `[PerfectField K]` is used; over an inseparable residue extension
there need not be a section.

**The Laurent expansion.** With $`\sigma`$ fixed, every element of the completion
has a convergent expansion

$$x \\;=\\; \sum_{j=-N}^{\infty} \sigma(a_j)\\,\pi^{\\,j}, \qquad a_j \in k(u),$$

and the map sending a finitely supported family $`\delta`$ to the negative part
$`\sum_j \sigma(\delta_j)\,\pi^{-(j+1)}`$ spans a complement
$`B = \mathrm{range}(\mathrm{cohen}\Phi)`$ of the integers, with
$`\hat L_u = \hat{\mathcal O}_u \oplus B`$
([S_AlgebraicCurve_tateAgreement.lean, lines 4462–4476](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L4462-L4476),
[lines 4748–4762](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L4748-L4762)).
The key normalization is

$$\mathrm{Res}_u\bigl(\sigma(\delta_0)\\,\pi^{-1} + \text{higher negative powers}\bigr) = \delta_0 ,$$

i.e. the residue reads off the $`\pi^{-1}`$ coefficient of the expansion
(`locResCompl_cohenΦ`, [lines 4518–4540](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L4518-L4540)).

**The kernel computation.** The pair (projector, Cohen–Laurent complement) is
packaged as `KwTateRR3CohenLaurentCompl` and then as a `TateCohenKernelData`:
a projector `pC` with the same range as the integers, together with a $`K`$-linear
injection `liftκ` of the residue field into that range such that the commutator
acts on the embedded copy of $`k(u)`$ as multiplication by the residue,

```lean
tateComm_liftκ : ∀ (fh : u.adicCompletion) (c : u.ResidueField),
  tateCommRestrict pC (lmulK u fh) (lmulK u uniformizerHat) (liftκ c)
    = liftκ (kwHgfV352_localResidueCompletion u fh * c)
```

([S_AlgebraicCurve_tateAgreement.lean, lines 3053–3072](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L3053-L3072)).
The trace of the commutator is then the trace of multiplication by
$`\mathrm{Res}_u(fh)`$ on $`k(u)`$, which is by definition
$`\mathrm{Tr}_{k(u)/K}(\mathrm{Res}_u(fh))`$. The computation is the short chain
of trace identities in `tateCommTrace_of_kernelData`
([lines 3091–3117](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L3091-L3117)):
the commutator's range lies in the finite-dimensional image of `liftκ`; on that
space it is conjugate to multiplication by $`\mathrm{Res}_u(fh)`$; and the trace
is invariant under conjugation (`LinearMap.trace_conj'`).

**Independence of the projector.** Since the arbitrary `tateProj` and the
canonical `pC` have the same range, their commutator traces agree
(`kwF4gRRTate_projectorIndep`, [line 2844](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L2844)),
so the agreement proved for `pC` transfers to the definition of `tateRes`.
Assembling the pieces, `kwTateRR3_cohenKernelDataExists` produces the kernel
data at every place
([line 4790](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L4790)),
and the top-level `solution` concludes `KwF4gRRTateAgreement`
([line 4809](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L4809)).

## 7. From one place to the global residue theorem

The agreement is local. The global residue theorem is assembled from it together
with three further Tate atoms, each a functoriality statement about
$`\mathrm{tateRes}`$:

* `tateCommFinite`, that the commutator ranges are finite-dimensional, so the
  traces exist
  ([Thm_AlgebraicCurve_tateCommFinite.lean, line 20](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_tateCommFinite.lean#L20));
* `tateChainRule`, the change-of-variables formula: since the pulled-back
  $`\mathrm{d}\pi_v`$ is the coefficient times $`\mathrm{d}\pi_w`$, the Tate
  residue of $`f`$ against $`\pi_v`$ equals the Tate residue of
  $`f \cdot \mathrm{coeff}`$ against $`\pi_w`$
  ([Def_AlgebraicCurve_TateResidueCurrency.lean, lines 317–329](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L317-L329));
* `tateTraceCompat_of_isSeparable`, that the Tate residue is compatible with the
  completion trace of a finite separable extension $`E \subseteq F`$ along a
  place $`w \mid v`$
  ([lines 331–343](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L331-L343)).

These four are combined in `residueTraceCompletionCommute` (RTCC), which proves
that the Kähler residue term at a place $`w`$ of the extension equals the trace
of the completion trace down to the base place $`v`$
([Def_AlgebraicCurve_TateResidueCurrency.lean, lines 368–376](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L368-L376),
[S_AlgebraicCurve_residueTraceCompletionCommute.lean, lines 1053–1092](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTraceCompletionCommute.lean#L1053-L1092)).
RTCC is then fed — together with the rational-function-field residue theorem
`residueTheoremK_ratFunc_of_isAlgClosed` — into
`residueTheoremK_of_isAlgClosed`, which proves `ResidueTheoremK` for every
algebraically closed field
([Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean#L16)).
That is the "analytic" input of the Riemann–Roch route of
[studies/riemann-roch-strategy.md](../studies/riemann-roch-strategy.md) §3, and
the reason its statement is over `[IsAlgClosed K]` rather than $`K = \mathbb{C}`$:
the residue is computed by algebra in the completion, not by a contour.

Two consequences are worth stating. First, over a perfect field the local
residue itself *exists* canonically, via the Cohen section of §6, so
`HasCanonicalLocalResidueKStar` is an instance rather than a hypothesis
([Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean, lines 2149–2156](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean#L2149-L2156)).
Second, the agreement is what lets the Riemann–Roch engine of
[base/019](../base/019-stichtenoth-genus-and-the-adelic-index.md) use the residue
in the form it needs: the conditional node
`exists_linearEquiv_regularDifferentials_omegaSpace_zero` is stated over
`ResidueTheorem`, and `tateAgreement` is the theorem that supplies that
hypothesis over a general field.

## 8. How the formalization writes it

The Lean development is a chain of `Prop`-valued atoms, each a precise
functoriality or agreement statement, so that the analytic input is isolated from
the Riemann–Roch assembly.

**The completion and its trace.** `u.adicCompletion` is mathlib's
`HeightOneSpectrum.adicCompletion` of the function field at the place, and the
integers are its `adicCompletionIntegers`
([Def_AlgebraicCurve_PlaceCompletion.lean, lines 31–34](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean#L31-L34)).
The **completion trace** of a finite extension is `Algebra.trace` over the base
completion, transported to a $`K`$-linear map on the field,

```lean
abbrev kw_ffgc_completionTrace [FiniteDimensional F F'] :
    W.adicCompletion →ₗ[(W.restrict F).adicCompletion] (W.restrict F).adicCompletion :=
  Algebra.trace (W.restrict F).adicCompletion W.adicCompletion

def kw_ffgc_completionTraceF' [FiniteDimensional F F'] : F' →ₗ[F] (W.restrict F).adicCompletion
```

([lines 390–398](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean#L390-L398)).
This is the trace that RTCC relates to the local residue.

**The trace of an infinite-dimensional operator.** `finrankTrace` is the trace of
the restriction to the range, which is how a trace-class operator on an
infinite-dimensional space gets a trace
([Def_AlgebraicCurve_TateResidueCurrency.lean, lines 28–30](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean#L28-L30)).
The companion lemma `finrankTrace_eq_trace_on_superspace` lets the trace be
computed on any finite-dimensional stable superspace of the range
([S_AlgebraicCurve_tateAgreement.lean, line 1980](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean#L1980)),
which is what makes the conjugation argument of §6 work.

**The atoms as hypotheses.** `KwF4gRRTateAgreement` is stated with the
finiteness atom as an argument, `KwF4gRRTateAgreement K L hfin`, and the four
atoms are supplied separately: `tateCommFinite`, `tateAgreement`,
`tateChainRule`, `tateTraceCompat_of_isSeparable`. RTCC then takes all four as
hypotheses, and only the final wrapper
`residueTheoremK_of_isAlgClosed` discharges them. This is the same
isolation-of-inputs pattern as the phase plan of
[PORTING-RR](../lean/topics/PORTING-RR.md): the analytic content is a small set
of named `Prop`s, and the algebra around it is reusable.

**The hypotheses, and where each is used.** `[PerfectField K]` is used exactly
for the separability of $`k(u)/K`$ and hence the Hensel-lifted Cohen section
(§6); `[∀ u, u.FiniteResidue]` makes the residue field trace finite and the
commutator trace class; `[IsCurveOver K L]` supplies the divisor theory,
principal divisors and the single dimension of $`\Omega`$; and
`[Algebra.IsSeparable E F]` is what makes the extension trace in RTCC behave.
None of them mentions $`\mathbb{C}`$.

### Key points, and where they are formalized

| mathematical point | Lean declaration | file |
|---|---|---|
| completion at a place, its integers | `adicCompletion`, `adicCompletionIntegers` | `Def_AlgebraicCurve_PlaceCompletion.lean:31`, `:33` |
| trace of a finite extension of completions | `kw_ffgc_completionTrace`, `kw_ffgc_completionTraceF'` | `Def_AlgebraicCurve_PlaceCompletion.lean:390`, `:394` |
| extension of the residue to the completion | `kwHgfV352_localResidueCompletion` | `Def_AlgebraicCurve_TateResidueCurrency.lean:185` |
| the local residue axioms | `LocalResidueData`, `CanonicalLocalResidueDataK` | `Def_AlgebraicCurve_LocalResidue.lean:20`, `:29` |
| residue term, traced to $`K`$ | `kaehlerResidueTerm` | `Def_AlgebraicCurve_LocalResidue.lean:111` |
| projection onto the integers | `tateProj` | `Def_AlgebraicCurve_TateResidueCurrency.lean:274` |
| the commutator, and its trace | `tateComm`, `tateCommTrace` | `Def_AlgebraicCurve_TateResidueCurrency.lean:38`, `:59` |
| the Tate residue | `tateRes` | `Def_AlgebraicCurve_TateResidueCurrency.lean:289` |
| trace class: finite-dimensional commutator range | `KwF4gRRTateCommFinite`, `tateCommFinite` | `Def_AlgebraicCurve_TateResidueCurrency.lean:300`; `Thm_AlgebraicCurve_tateCommFinite.lean:20` |
| independence of the projection | `KwF4gRRTateProjectorIndep`, `kwF4gRRTate_projectorIndep` | `S_AlgebraicCurve_tateAgreement.lean:1867`, `:2844` |
| the agreement | `KwF4gRRTateAgreement`, `tateAgreement` | `Def_AlgebraicCurve_TateResidueCurrency.lean:307`; `Thm_AlgebraicCurve_tateAgreement.lean:19` |
| Cohen section (Hensel) | `Lg37CompletionSection`, `completionSection_nonempty_generic` | `Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean:956`, `:2137` |
| Cohen–Laurent complement and kernel data | `KwTateRR3CohenLaurentCompl`, `TateCohenKernelData` | `S_AlgebraicCurve_tateAgreement.lean:4330`, `:3053` |
| commutator acts as multiplication by the residue | `tateComm_liftκ` | `S_AlgebraicCurve_tateAgreement.lean:3069` |
| change of variables for the residue | `KwF4gRRTateChainRule`, `tateChainRule` | `Def_AlgebraicCurve_TateResidueCurrency.lean:317`; `Thm_AlgebraicCurve_tateChainRule.lean:18` |
| compatibility with the extension trace | `KwF4gRRTateTraceCompat`, `tateTraceCompat_of_isSeparable` | `Def_AlgebraicCurve_TateResidueCurrency.lean:331`; `Thm_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean:18` |
| local → global: RTCC | `KwF4R1V391aResidueTraceCompletionCommute`, `residueTraceCompletionCommute` | `Def_AlgebraicCurve_TateResidueCurrency.lean:368`; `Thm_AlgebraicCurve_residueTraceCompletionCommute.lean:21` |
| the residue theorem over any algebraically closed field | `ResidueTheoremK`, `residueTheoremK_of_isAlgClosed` | `Def_AlgebraicCurve_LocalResidue.lean:297`; `Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean:16` |

## 9. What this note does not cover

Three neighbouring subjects are deliberately out of scope.

* **The complex-analytic residue theorem.** This note explains the algebraic
  substitute, not the proof over $`\mathbb{C}`$. The agreement theorem shows
  that the substitute computes the same residue, so the two are interchangeable
  where both exist.
* **The global assembly and its use for Riemann–Roch.** The `tateAgreement` /
  `residueTraceCompletionCommute` chain that ends in
  `residueTheoremK_of_isAlgClosed`, and the way the Riemann–Roch engine consumes
  it, are only sketched in §7; the engine itself is the subject of
  [base/019](../base/019-stichtenoth-genus-and-the-adelic-index.md), and the
  route measurement is in
  [studies/riemann-roch-strategy.md](../studies/riemann-roch-strategy.md).
* **The local class field theory reading of the Tate trace.** The same
  commutator trace is the reciprocity/tame-symbol construction in local class
  field theory; that circle of ideas is not needed for the residue theorem and
  is not formalized in the pin.

## Links

* [base/009 — Differentials, residues, and Riemann–Roch](../base/009-differentials-residues-riemann-roch.md)
  — the differentials, the residue theorem as a fact, and the two inequalities
  the residue feeds.
* [base/019 — Stichtenoth's genus and the adelic index](../base/019-stichtenoth-genus-and-the-adelic-index.md)
  — the engine that consumes the residue theorem, and the conditional node
  `exists_linearEquiv_regularDifferentials_omegaSpace_zero`.
* [studies/riemann-roch-strategy.md](../studies/riemann-roch-strategy.md) — the
  two routes to Riemann–Roch, and where the residue theorem sits.
* [math/011 — The Tate module, and the Galois representations attached to
  elliptic curves and modular forms](011-tate-module.md) — the other "Tate"
  construction in the proof, unrelated to the residue beyond the name.
* FLT at the pinned sha `aa2d8b3`:
  [`Def_AlgebraicCurve_TateResidueCurrency.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean),
  [`Def_AlgebraicCurve_PlaceCompletion.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PlaceCompletion.lean),
  [`Def_AlgebraicCurve_LocalResidue.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_LocalResidue.lean),
  [`Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean),
  [`S_AlgebraicCurve_tateAgreement.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean).
* J. Tate, *Residues of differentials on curves*, Annales scientifiques de
  l'École Normale Supérieure (4) **1** (1968), 149–159,
  [numdam](https://www.numdam.org/articles/10.24033/asens.1162/).
* J.-P. Serre, *Groupes algébriques et corps de classes*, Hermann, 1959, for the
  residue and the trace in the function-field setting.
