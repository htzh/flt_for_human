# Congruence subgroups, level structures, and invariance

Eighteenth of the `base/` notes. [002](002-modular-forms-basics.md) introduced
the analytic objects (`SlashInvariantForm`, `ModularForm`, `CuspForm`) and the
three congruence subgroups as they appear in mathlib; [004](004-the-j-invariant.md)
used them at level one and [005](005-cyclic-isogenies-and-level.md) drew the
classical lattice/quotient picture behind $`\Gamma_0(N)`$. This note is the one
that fixes what the colloquial texts usually leave implicit: **which group acts
on which object**, what "invariant" means as a stabiliser condition, and — the
point that causes the most confusion — **when the matrix is multiplied over
$`\mathbb{Z}`$ and when only its reduction modulo $`N`$ is used**.

The four objects the note is about are the familiar moduli problems

$$E, \qquad (E, \langle C\rangle), \qquad (E, P), \qquad (E, (P,Q)),$$

i.e. an elliptic curve; an elliptic curve with a cyclic subgroup of order
$`N`$; with a point of exact order $`N`$; with a full basis of $`E[N]`$. Their
stabilisers in $`\mathrm{SL}_2(\mathbb{Z})`$ are the three congruence subgroups
$`\Gamma_0(N)`$, $`\Gamma_1(N)`$, $`\Gamma(N)`$ (plus $`\Gamma(1)`$ for the bare
curve), and the FLT project's fourth family $`\Gamma_H`$ interposes between
$`\Gamma_0`$ and $`\Gamma_1`$.

Two disciplines are enforced throughout. First, **the word "lattice" is used
only for the classical analytic model**: the FLT definitions of the arithmetic
objects use point groups (`AddCommGroup`), additive subgroups
(`AddSubgroup.zmultiples`), and $`(\mathbb{Z}/N)`$-modules, and where the Lean
develops those we say so. Second, **a matrix over $`\mathbb{Z}`$ and a matrix
over $`\mathbb{Z}/N`$ are different objects**, related by a reduction map that is
surjective but not injective, and most of the technical content of the level
theory is in keeping track of which one a given formula uses.

Line numbers point at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib at tag
**v4.33.0**. Both kinds of citation are rendered GitHub links carrying `#L`
anchors.

The plan:

1. the four moduli problems and the four groups, with the stabiliser computation,
   and the bridge identifying the $`\tau`$-action with a relabelling of the
   torsion labels (§1.5);
2. the groups as Lean objects, including the $`\Gamma_H`$ family;
3. invariance: the slash action, and the three matrices hiding behind one letter;
4. $`\mathbb{Z}`$-matrix multiplication versus $`\mathbb{Z}/N`$-matrix multiplication;
5. torsion labels and coset representatives;
6. the moduli data in Lean, and what is *not* formalised;
7. key point $`\to`$ declaration map;
8. Lean detours (not mathematics);
9. links.

## 1. The four moduli problems and the four groups

### 1.1 The objects

Fix $`N \ge 1`$ and an elliptic curve $`E`$ over a field $`F`$ in which $`N`$ is
invertible. Write $`E[N]`$ for the $`N`$-torsion subgroup; it is an abelian group
isomorphic to $`(\mathbb{Z}/N)^2`$, written additively. The four level data are:

| datum | name | what is remembered |
|---|---|---|
| $`E`$ | no level | the curve alone |
| $`(E, C)`$ | cyclic level | a cyclic subgroup $`C \le E`$ of order $`N`$ |
| $`(E, P)`$ | point level | a point $`P \in E`$ of exact order $`N`$ |
| $`(E, (P,Q))`$ | full level | a pair with $`E[N] = \langle P\rangle \oplus \langle Q\rangle`$ |

The forgetful maps run

$$(E,(P,Q)) \longrightarrow (E,P) \longrightarrow (E,\langle P\rangle)
   \longrightarrow E,$$

so the full level is the finest datum and the bare curve the coarsest. Each
forgetful map has a finite fibre: $`(E,P)`$ remembers which generator of $`C`$ is
chosen (a class in $`(\mathbb{Z}/N)^\times`$), and $`(E,(P,Q))`$ remembers the
basis, not just the two subgroups.

### 1.2 The action on a full level structure

Let $`(P,Q)`$ be a basis of $`E[N]`$ and let
$`\sigma = [[a, b], [c, d]] \in \mathrm{SL}_2(\mathbb{Z})`$.
The **row convention** used by FLT is right multiplication of the row $`(P,Q)`$:

$$(P,Q) \\;\longmapsto\\; (P,Q)\\,\sigma
   \\;=\\; \bigl(aP + cQ,\\; bP + dQ\bigr).$$

So the new first point is $`P' = aP + cQ`$ and the new second point is
$`Q' = bP + dQ`$. The Lean instance of this is literally
`LevelPData.relabel` ([Def_ModularCurve_LevelRelabelling.lean, lines 29–34](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelRelabelling.lean#L29-L34)):

```lean
def LevelPData.relabel (g : Matrix (Fin 2) (Fin 2) ℤ) (D : ModularCurve.LevelPData T) : ModularCurve.LevelPData T :=
  let P := toPoint W D.xP D.yP
  let Q := toPoint W D.xQ D.yQ
  let P' := ofPoint W (g 0 0 • P + g 1 0 • Q)
  let Q' := ofPoint W (g 0 1 • P + g 1 1 • Q)
  ⟨P'.1, P'.2, Q'.1, Q'.2⟩
```

The formal-group analogue is `FormalGroup.baseAct`
([Def_FormalGroup_DrinfeldBasis.lean, lines 21–22](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FormalGroup_DrinfeldBasis.lean#L21-L22)), with the same convention.

> **Convention warning.** Many textbooks write the basis as a *column* and the
> action as $`\sigma`$ acting on the left, $`(P,Q)^{\mathsf T} \mapsto
> \sigma\,(P,Q)^{\mathsf T}`$, i.e. $`(P',Q') = (aP+bQ,\;cP+dQ)`$. That is the
> transpose of the convention above; the two differ only by transposing the
> matrix, and one must not mix them. FLT uses the row/right convention
> throughout, so in this note $`\sigma`$ acts by
> $`(P,Q)\mapsto(P,Q)\sigma`$.

The action is a genuine action: `relabel h (relabel g D) = relabel (g*h) D`,
`relabel 1 D = D`, and it factors through the reduction to $`\mathbb{Z}/N`$ —
all three are one theorem,
[Thm_ModularCurve_IsLevelPStructure_relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq.lean, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_IsLevelPStructure_relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq.lean#L16).
That last clause is the first appearance of the mod-$`N`$ reduction:
$`\sigma`$ and $`\sigma'`$ give the same relabelling as soon as their images in
$`\mathrm{SL}_2(\mathbb{Z}/N)`$ agree.

### 1.3 The stabiliser computation

Everything about the correspondence "level datum $`\leftrightarrow`$ subgroup of
$`\mathrm{SL}_2(\mathbb{Z})`$" is the following one computation. With
$`P' = aP + cQ`$:

* $`P' = P`$ and $`Q' = Q`$ require $`a \equiv 1`$, $`b \equiv 0`$, $`c \equiv 0`$,
  $`d \equiv 1`$ mod $`N`$ — because $`(P,Q)`$ is a basis of $`E[N]`$, and congruences
  are exactly equality of the induced endomorphisms of $`E[N]`$. So the
  stabiliser of the *pair* is
  $$\Gamma(N) = \\{\sigma : \sigma \equiv I \bmod N\\}`.$$
* $`P' \in \langle P\rangle`$ forces $`c \equiv 0 \bmod N`$ (the $`Q`$-component of
  $`P'`$ must vanish, and $`\langle P\rangle \cap \langle Q\rangle = 0`$); then
  $`P' = aP`$ with $`a`$ a unit mod $`N`$ because $`a d - b c = 1`$ and
  $`c \equiv 0`$ give $`a d \equiv 1`$. So $`\langle P'\rangle = \langle P\rangle`$
  and the stabiliser of the *cyclic subgroup* is
  $$\Gamma_0(N) = \Bigl\\{\sigma : c \equiv 0 \bmod N\Bigr\\}`.$$
* $`P' = P`$ additionally forces $`a \equiv 1`$; then $`d \equiv 1`$ as well. The
  stabiliser of the *point* is
  $$\Gamma_1(N) = \Bigl\\{\sigma : a \equiv d \equiv 1,\\; c \equiv 0 \bmod N\Bigr\\}`.$$
* The stabiliser of the bare curve is all of
  $`\Gamma(1) = \mathrm{SL}_2(\mathbb{Z})`$.

In particular the containments

$$\Gamma(N) \\;\subseteq\\; \Gamma_1(N) \\;\subseteq\\; \Gamma_0(N) \\;\subseteq\\; \Gamma(1)$$

mirror the forgetful maps of §1.1, and the index of each in $`\Gamma(1)`$ counts
the choices forgotten: $`[\Gamma(1):\Gamma_0(N)]`$ is the number of cyclic
subgroups of order $`N`$ in $`(\mathbb{Z}/N)^2`$, the Dedekind function
$`\psi(N)`$ of [005 §2](005-cyclic-isogenies-and-level.md).

**This is what "invariance" means.** A function $`f`$ on the upper half plane is
a modular form of weight $`k`$ and level $`\Gamma`$ when

$$f \mid_k \gamma = f \qquad \text{for all } \gamma \in \Gamma,$$

and the moduli reading is that $`f`$ is a function of the *level datum* rather
than of the marking: it cannot tell apart two marked curves that differ by an
element of $`\Gamma`$, i.e. two markings of isomorphic data. The quotient
$`\Gamma\backslash\mathbb{H}`$ is the moduli space, and the stabiliser computation
above identifies which data the quotient parametrises:
$`\Gamma_0(N)\backslash\mathbb{H}`$ classifies $`(E,C)`$,
$`\Gamma_1(N)\backslash\mathbb{H}`$ classifies $`(E,P)`$,
$`\Gamma(N)\backslash\mathbb{H}`$ classifies $`(E,(P,Q))`$.

### 1.4 The lattice picture, and why we do not lean on it

Classically one writes $`\Lambda_\tau = \mathbb{Z} + \mathbb{Z}\tau`$ and
$`E_\tau = \mathbb{C}/\Lambda_\tau`$, and the marking is the choice of basis
$`(1,\tau)`$. Changing the marking by $`\gamma`$ changes $`\tau`$ to
$`\gamma\tau`$ and leaves the torus isomorphic, so the quotient by
$`\mathrm{SL}_2(\mathbb{Z})`$ is isomorphism classes of elliptic curves —
[005 §1](005-cyclic-isogenies-and-level.md) develops this carefully. The word
"lattice" belongs to this analytic model. It is a *computational presentation*:
the moduli problem is about $`(E,\text{level structure})`$, and the lattice is
how one writes an elliptic curve down over $`\mathbb{C}`$.

The FLT definitions of the arithmetic objects never use a lattice. They use:

* the point group $`E(F)`$ as an `AddCommGroup` (mathlib), with
  `addOrderOf` for exact order and `AddSubgroup.zmultiples` for a cyclic
  subgroup ([Def_ModularCurve_EMD.lean, lines 36–39](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_EMD.lean#L36-L39));
* $`E[N]`$ as the submodule `Submodule.torsionBy ℤ E.Point N`, carrying a
  $`\mathbb{Z}/N`$-module structure. FLT installs the instance itself
  ([Def_FLTPrelim_GaloisRep.lean, lines 60–64](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L60-L64));
  mathlib's generic version is `torsionBy.zmodModule`
  ([Algebra/Module/Torsion/Basic.lean, lines 1009–1012, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Torsion/Basic.lean#L1009-L1012));
* the Jacobian torsion `Pic0.torsion K F n` as a `Submodule.torsionBy`
  ([Def_AlgebraicCurve_DivisorClassGroup.lean, line 244](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean#L244)),
  again with a $`\mathbb{Z}/n`$-module structure and a
  `torsionRep : SemilinearAut K F →* Module.End (ZMod n) _`
  ([Def_AlgebraicCurve_BaseChangeGalois.lean, line 346](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean#L346)).

So in the arithmetic (as opposed to analytic) setting, "a $`\mathbb{Z}`$-module"
or "additive subgroup" is the honest word, and this note uses it. The only
occurrence of the word *lattice* as a Lean identifier in this circle of ideas is
`twoCuspLattice`, a plain `Submodule`
([Def_CuspForm_TwoCuspLattice.lean, lines 86–87](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_TwoCuspLattice.lean#L86-L87)),
where it is the module-theoretic lattice of an integral structure, unrelated to
$`\mathbb{C}/\Lambda`$.

### 1.5 The bridge to the upper half plane

Sections 1.1–1.3 do everything inside the torsion group
$`E[N] \cong (\mathbb{Z}/N)^2`$, where what acts is the reduction of an integer
matrix modulo $`N`$. But $`\mathrm{SL}_2(\mathbb{Z})`$ is classically introduced
as the group of Möbius transformations of the upper half plane,

$$\tau \longmapsto \gamma\tau = \frac{a\tau + b}{c\tau + d},
   \qquad \gamma = \begin{pmatrix} a & b \\\\ c & d \end{pmatrix}
   \in \mathrm{SL}_2(\mathbb{Z}),$$

and the congruence subgroups are classically *defined* by the same entrywise
conditions on $`\gamma`$. The dictionary between the two descriptions is a
linear-algebra statement over $`\mathbb{Z}`$ and $`\mathbb{Z}/N`$: on the standard
torsion labels, the Möbius action is the reduction of an explicit matrix
$`M_\gamma`$ which is **not** $`\gamma`$ but a signed conjugate of it. Every
statement below is a matrix computation in one of those two rings; the only
analytic inputs are the standard torsion basis and the Möbius formula, and the
computations are checked in
[`LevelTauBridge.lean`](../lean/Reserve/ModularCurve/Analytic/LevelTauBridge.lean).
The one ingredient that is not a matrix computation is the choice of
isomorphism $`E_\tau \to E_{\gamma\tau}`$; it is named below, because "the same
curve modulo isomorphism" is meaningful only once the isomorphism is fixed.

**The standard labels.** For $`\tau \in \mathbb{H}`$ write
$`E_\tau = \mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)`$. The classes of
$`\frac{1}{N}`$ and $`\frac{\tau}{N}`$ are a $`(\mathbb{Z}/N)`$-basis of the
$`N`$-torsion $`E_\tau[N]`$, so every $`N`$-torsion point has a unique pair of
coordinates $`(m,n) \in (\mathbb{Z}/N)^2`$ — the torsion labels of §5.1.

**The matrix induced on the labels.** Classically the marking change
$`E_\tau \to E_{\gamma\tau}`$ is the isomorphism $`z \mapsto \frac{z}{c\tau+d}`$.
On the standard generators of $`E_\tau[N]`$ it acts by

$$\frac{1}{N} \longmapsto \frac{a - c\\,\gamma\tau}{N},
   \qquad \frac{\tau}{N} \longmapsto \frac{d\\,\gamma\tau - b}{N},$$

by the two identities $`\frac{1}{c\tau+d} = a - c\,\gamma\tau`$ and
$`\frac{\tau}{c\tau+d} = d\,\gamma\tau - b`$ in $`\mathbb{C}`$. Read in the
standard basis $`(\frac{1}{N}, \frac{\gamma\tau}{N})`$ of $`E_{\gamma\tau}[N]`$,
the images are therefore

$$a\cdot\frac{1}{N} - c\cdot\frac{\gamma\tau}{N},
   \qquad -b\cdot\frac{1}{N} + d\cdot\frac{\gamma\tau}{N},$$

so the induced relabelling matrix is

$$M_\gamma = \begin{pmatrix} a & -b \\\\ -c & d \end{pmatrix}
   = D\\,\gamma\\,D^{-1}, \qquad D = \begin{pmatrix} 1 & 0 \\\\ 0 & -1 \end{pmatrix}.$$

(These are `image_P_eq`, `image_Q_eq`, `torsionMatrix`, `torsionMatrix_eq_conj`
in [`LevelTauBridge.lean`](../lean/Reserve/ModularCurve/Analytic/LevelTauBridge.lean).)

**The linear algebra over $`\mathbb{Z}/N`$.** The determinant is
$`\det M_\gamma = ad - bc = 1`$, so $`M_\gamma \in \mathrm{SL}_2(\mathbb{Z})`$ and
its reduction lies in $`\mathrm{SL}_2(\mathbb{Z}/N)`$ (`torsionMatrix_det`). The
twist $`D`$ only flips the signs of the off-diagonal entries, and a sign is
invisible to vanishing and to $`1`$ modulo $`N`$:

$$c \equiv 0 \pmod N \iff -c \equiv 0 \pmod N, \qquad
   (a, d, c) \equiv (1, 1, 0) \iff (a, d, -c) \equiv (1, 1, 0),$$

and likewise for all four entries. Hence the entrywise congruence conditions on
$`M_\gamma`$ and on $`\gamma`$ select the same subgroup:

$$\gamma \in \Gamma_0(N) \iff M_\gamma \in \Gamma_0(N), \qquad
   \gamma \in \Gamma_1(N) \iff M_\gamma \in \Gamma_1(N), \qquad
   \gamma \in \Gamma(N) \iff M_\gamma \in \Gamma(N)$$

(`gamma0_iff_torsionMatrix`, `gamma1_iff_torsionMatrix`,
`Gamma_iff_torsionMatrix`). This is the missing link: the subgroup selected by
the $`\tau`$-action is the subgroup computed in §1.3 from the abstract label
action, so "invariance under $`\Gamma`$" and "the level datum is remembered" are
one congruence condition on one integer matrix.

Two remarks, both about the identification itself. First, the appearance of
$`M_\gamma`$ rather than $`\gamma`$ is the transpose/sign convention of §1.2:
with the FLT row convention $`(P,Q) \mapsto (P,Q)\gamma`$, the marking change is
`relabel` by $`M_\gamma`$, not by $`\gamma`$, so reading a level-datum statement
as one about $`\gamma`$ requires this identification. Second,
$`M_\gamma = D\gamma D^{-1}`$ is conjugation by a matrix of determinant $`-1`$,
an outer twist of $`\mathrm{SL}_2(\mathbb{Z})`$; it is invisible above because the
conditions are unchanged when either coordinate of $`(\mathbb{Z}/N)^2`$ is
negated.

**Why the FLT code does not close this.** The reason is a matter of scope, not
an oversight. FLT's `LevelPData.relabel` (§1.2) is the Katz–Mazur algebraic
action on the labels: it is defined on Weierstrass coordinates and division
polynomials, and it never mentions $`\mathbb{H}`$ or $`\mathbb{C}/\Lambda`$. The
algebraic side is in fact complete — `relabel` is a right
$`\mathrm{GL}_2(\mathbb{Z}/N)`$-action
([Thm_..._relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq.lean, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_IsLevelPStructure_relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq.lean#L16)),
the level structures on a fixed curve are a single $`\mathrm{GL}_2(\mathbb{Z}/\ell)`$-orbit
([Thm_..._exists_eq_nsmul_add_nsmul_of_isLevelPStructure.lean, line 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_IsLevelPStructure_exists_eq_nsmul_add_nsmul_of_isLevelPStructure.lean#L15)),
the action is natural in the curve and base ring
([Thm_..._exists_natural_relabel_levelPData.lean, line 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelRelabelling_exists_natural_relabel_levelPData.lean#L15)),
the $`\Gamma(N_0)`$-transitivity with fixed Weil pairing is proved
([Thm_..._exists_mem_Gamma_relabel_eq_of_weilPairing0_eq.lean, line 18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_LevelRelabelling_exists_mem_Gamma_relabel_eq_of_weilPairing0_eq.lean#L18)),
and the reduction is surjective
([Thm_ModularCurve_surjective_specialLinearGroup_map_zmod.lean, line 6](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_surjective_specialLinearGroup_map_zmod.lean#L6)).
None of these touches the upper half plane. On the analytic side the only
$`\mathbb{H}`$-facing declarations are the slash action and the Hecke operators
(§3); and mathlib, while it has both the Möbius action
(`UpperHalfPlane.coe_specialLinearGroup_apply`) and the congruence subgroups,
has no theorem identifying $`\Gamma\backslash\mathbb{H}`$ with a moduli functor
— that is uniformization plus Riemann existence, cf. [013](013-riemann-existence-and-the-q-expansion-principle.md).
So there is nowhere in either codebase where the two actions *could* meet, and
the bridge is a mathematical dictionary rather than a missing proof step. The
module [`LevelTauBridge.lean`](../lean/Reserve/ModularCurve/Analytic/LevelTauBridge.lean)
checks the matrix computations above — the two complex identities, the induced
matrix, and the three stabiliser equivalences; the identification of the
resulting quotient with a moduli space stays outside both developments.

## 2. The groups as Lean objects

### 2.1 Mathlib's three subgroups

Mathlib defines the three groups in
[ModularForms/CongruenceSubgroups.lean, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean)).
The reduction map is a **local notation**, not a definition:

```lean
local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))
```

([lines 29–30](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L29-L30)), with `SL_reduction_mod_hom_val`
([line 33](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L33)) recording that it is entrywise reduction of an integer matrix.

| Lean | Mathematics | Line |
|---|---|---|
| `CongruenceSubgroup.Gamma N`, scoped `Γ(N)` | $`\ker(\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/N))`$ | [41](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L41) |
| `Gamma_mem` | all four entries congruent to the identity | [50](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L50) |
| `CongruenceSubgroup.Gamma0 N` | $`c \equiv 0 \bmod N`$ (defined entrywise) | [79](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L79) |
| `Gamma0_mem` | $`A \in \Gamma_0(N) \leftrightarrow (A_{10} : \mathbb{Z}/N) = 0`$ | [90](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L90) |
| `Gamma0Map N : Gamma0 N →* ZMod N` | $`A \mapsto A_{11}`$ (the lower-right entry) | [95](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L95) |
| `Gamma1' N` | $`\ker(\Gamma_0(N) \to \mathbb{Z}/N)`$ | [105](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L105) |
| `Gamma1 N` | the image of `Gamma1'` in $`\mathrm{SL}_2(\mathbb{Z})`$ | [131](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L131) |
| `Gamma1_mem` | $`a \equiv 1`$, $`d \equiv 1`$, $`c \equiv 0`$ | [135](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L135) |
| `IsCongruenceSubgroup Γ` | $`\exists N \ne 0,\,\Gamma(N) \le \Gamma`$ | [163](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L163) |

Two remarks that save time later. `Gamma0` is **not** a kernel: only `Gamma` is
defined as `SLMOD(N).ker`, while `Gamma0` is defined by the entrywise condition
$`A_{10} = 0`$ and `Gamma1` is a `Subgroup.map`. And `Gamma0Map` lands in the
*monoid* $`\mathbb{Z}/N`$, not its unit group, so it is not directly a
group-theoretic quotient map; §2.2 upgrades it.

### 2.2 The $`\Gamma_H`$ family

The FLT project needs a group that interpolates between $`\Gamma_0`$ and
$`\Gamma_1`$, and it builds it from the lower-right entry
([Def_CohCarrier_Level.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean)):

```lean
def gamma0Units : Gamma0 M →* (ZMod M)ˣ where
  toFun γ :=
    { val := Gamma0Map M γ
      inv := ((γ.1 0 0 : ℤ) : ZMod M)
      val_inv := Gamma0_d_mul_a M γ
      inv_val := by rw [mul_comm]; exact Gamma0_d_mul_a M γ }
  ...

def GammaH (H : Subgroup (ZMod M)ˣ) : Subgroup SL(2, ℤ) :=
  (H.comap (gamma0Units M)).map (Gamma0 M).subtype
```

([lines 121–134](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L121-L134)). The unit structure is won from the
determinant: inside $`\Gamma_0(M)`$ one has $`a d \equiv 1 \bmod M`$
(`Gamma0_d_mul_a`, [lines 111–119](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L111-L119)), so the lower-right
entry is a unit with inverse the upper-left one. Hence

$$\Gamma_H = \\{\gamma \in \Gamma_0(M) : d(\gamma) \in H\\}, \qquad d(\gamma) = \gamma_{11} \bmod M,$$

and the specialisations are

| Lean | Mathematics | Location |
|---|---|---|
| `GammaH M ⊤ = Gamma0 M` | $`\Gamma_{\mathrm{all}} = \Gamma_0`$ | [XH 151–154](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XH.lean#L151-L154) |
| `GammaH M ⊥ = Gamma1 M` | $`\Gamma_{1} = \Gamma_1`$ | [XH 46–60](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XH.lean#L46-L60) |
| `Gamma1_le_GammaH` | $`\Gamma_1(M) \le \Gamma_H`$ | [XH 32–44](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XH.lean#L32-L44) |
| `GammaH_le_Gamma0` | $`\Gamma_H \le \Gamma_0(M)`$ | [Level 146–149](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L146-L149) |
| `Gamma_le_GammaH` | $`\Gamma(M) \le \Gamma_H`$ | [FormsGammaH 18–30](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean#L18-L30) |
| `mem_GammaH_iff` | $`\gamma \in \Gamma_H \leftrightarrow \gamma \in \Gamma_0 \wedge d(\gamma) \in H`$ | [Level 138–144](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L138-L144) |

The classical role of this family is the *Nebentypus*: $`\Gamma_H`$ is the
subgroup of $`\Gamma_0`$ whose diamond character lands in $`H`$, so forms on
$`\Gamma_H`$ carry a character of $`(\mathbb{Z}/M)^\times/H`$. Their indices
multiply in the expected way — `(GammaH M H).index = (Gamma0 M).index * H.index`
(`CohCarrier.index_gammaH_eq_index_gamma0_mul_index`,
[Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index.lean, lines 8–9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index.lean#L8-L9)),
the extra factor being the further identification of level data that the character
forgets. The point for the present note is structural: $`\Gamma_H`$ is a **pullback along the reduction
mod $`M`$**, and $`H`$ is a subgroup of $`(\mathbb{Z}/M)^\times`$. `GammaH` is
normal in $`\Gamma_0`$ — `GammaH_normal_in_Gamma0`
([lines 261–273](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L261-L273)) — so conjugation by
$`\Gamma_0`$ acts on it, which is the group-theoretic source of the diamond
operator (§4.5).

### 2.3 The Hecke-compatible subgroup

One more subgroup recurs in the Hecke theory. The coset representatives of the
Hecke double coset for $`\ell`$ are upper triangular, and the subgroups one needs
are the matrices whose *upper-right* entry is divisible by $`\ell`$:

```lean
def Gamma0Upper (ℓ : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g | (g 0 1 : ZMod ℓ) = 0 }
```

([Def_CohCarrier_Level.lean, lines 90–105](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L90-L105)), and `GammaHUpper := (Gamma0Upper ℓ).subgroupOf (GammaH M H)`
([line 210](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L210)). Its index is the number of Hecke
cosets: $`[\Gamma_H : \Gamma_H^{\mathrm{upper}}] = \ell + 1`$ for a good prime
$`\ell`$ ([Thm_CohCarrier_index_GammaHUpper_of_prime.lean, lines 7–9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CohCarrier_index_GammaHUpper_of_prime.lean#L7-L9)), or
$`\ell`$ when $`\ell \mid M`$. This is the group-theoretic form of the $`T_\ell`$/`U_\ell` split of [014](014-hecke-operators.md).

## 3. Invariance: the slash action, and three matrices behind one letter

### 3.1 The level is a subgroup of $`\mathrm{GL}_2(\mathbb{R})`$

Mathlib's modular forms are functions on $`\mathbb{H}`$ invariant under a
subgroup of $`\mathrm{GL}(2,\mathbb{R})`$:

```lean
structure SlashInvariantForm where
  toFun : ℍ → ℂ
  slash_action_eq' : ∀ γ ∈ Γ, toFun ∣[k] γ = toFun
```

([SlashInvariantForms.lean, lines 34–36, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean#L34-L36)); `ModularForm` and
`CuspForm` extend it with holomorphy and boundedness/vanishing at the cusps
([Basic.lean, lines 80–87, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/Basic.lean#L80-L87)). The arithmetic subgroup
$`\Gamma \le \mathrm{SL}_2(\mathbb{Z})`$ is pushed into
$`\mathrm{GL}_2(\mathbb{R})`$ by `Matrix.SpecialLinearGroup.mapGL ℝ`
([Def_CuspForm_Gamma1HeckeOperators.lean, lines 82–84](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L82-L84)), and the slash
action on $`\mathrm{SL}_2(\mathbb{Z})`$ is the $`\mathrm{GL}`$ one pulled back
along it:

```lean
instance SLAction : SlashAction ℤ SL(2, ℤ) (ℍ → ℂ) :=
  monoidHomSlashAction (Matrix.SpecialLinearGroup.mapGL ℝ)
```

([SlashActions.lean, lines 152–153, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L152-L153)).

### 3.2 The two formulas

The $`\mathrm{GL}`$ slash carries a determinant factor and a sign character; the
$`\mathrm{SL}`$ one is the classical $`(\text{denominator})^{-k}`$. With
$`\mathrm{denom}(g,z) = g_{10} z + g_{11}`$
([MoebiusAction.lean, line 33, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean#L33)), one has

$$(f \mid_k g)(\tau) = \sigma(g)\\, f(g\cdot\tau)\\, |\det g|^{k-1}\\,
   \mathrm{denom}(g,\tau)^{-k}$$

for $`g \in \mathrm{GL}_2(\mathbb{R})`$
([slash_apply, line 143, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L143)), which restricts for
$`\gamma \in \mathrm{SL}_2(\mathbb{Z})`$ to the clean

$$(f \mid_k \gamma)(\tau) = f(\gamma\cdot\tau)\\, (c\tau + d)^{-k},
   \qquad \gamma = \begin{pmatrix} a & b \\\\ c & d\end{pmatrix},$$

because $`\sigma(\gamma) = 1`$ and $`\det\gamma = 1`$
([SL_slash_apply, line 162, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L162)). Here
$`\gamma\cdot\tau = (a\tau+b)/(c\tau+d)`$. It is this formula, and only this
formula, that uses the honest integer (equivalently, real) matrix: `denom` sees
$`c`$ and $`d`$, not $`c \bmod N`$ and $`d \bmod N`$.

### 3.3 Three matrices, one letter

Every "$`\gamma`$" in this theory is one of three objects, and conflating them is
the source of the confusion:

1. **the integer matrix** $`\gamma \in \mathrm{SL}_2(\mathbb{Z})`$ — the thing a
   congruence subgroup is a subset of, and the index of which is what
   $`\Gamma(N) \le \Gamma`$ constrains;
2. **its real image** `mapGL ℝ γ`, the actual element of
   $`\mathrm{GL}_2(\mathbb{R})`$ that acts on $`\mathbb{H}`$ and on functions;
3. **its reduction** `SLMOD(N) γ`, an element of
   $`\mathrm{SL}_2(\mathbb{Z}/N)`$, which is what acts on the level data, i.e.
   on $`E[N]`$ and its subgroups/lines.

The reduction (3) is a function of (1), and (2) is a function of (1); there is
no direct map $`\mathrm{SL}_2(\mathbb{R}) \to \mathrm{SL}_2(\mathbb{Z}/N)`$. The
membership conditions of §1.3 live entirely in (3); the slash invariance
$`f\mid_k\gamma = f`$ of §3.2 lives entirely in (2); and the group structure,
indices and cosets live in (1). The next section is about moving between them.

## 4. $`\mathbb{Z}`$-matrix multiplication versus $`\mathbb{Z}/N`$-matrix multiplication

### 4.1 Only the reduction acts on the level data

Because the level data are built from $`N`$-torsion, an integer matrix and any
other with the same reduction act identically on them. In Lean this is not a
remark but the factoring clause of the relabelling action: if
$`\sigma`$ and $`\sigma'`$ have equal images under
`Int.castRingHom (ZMod ℓ)` then `relabel σ D = relabel σ' D`
([Thm_..._relabel_eq_of_map_eq, line 16](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_IsLevelPStructure_relabel_relabel_and_relabel_one_and_relabel_eq_of_map_eq.lean#L16)).
The same is true of every quotient of the level data: the cyclic subgroup
$`\langle P\rangle`$ and the point $`P`$ depend only on the components of the
labels in $`\mathbb{Z}/N`$. Hence:

> **Principle.** A statement that mentions only the level datum, the torsion
> labels, or a coset representative may be proved by multiplying matrices in
> $`\mathrm{SL}_2(\mathbb{Z}/N)`$. A statement that mentions the value of a
> function on $`\mathbb{H}`$ must use the integer matrix.

The canonical example of the first kind is the stabiliser computation of §1.3:
$`\sigma \in \Gamma_0(N)`$ is exactly "$`c = 0`$ in $`\mathbb{Z}/N`$",
a statement about `SLMOD(N) σ` alone. The canonical example of the second is the
slash formula of §3.2.

### 4.2 Where "only mod $`N`$" fails

Reduction is not injective, and the failure is exactly $`\Gamma(N)`$: two
integer matrices have the same reduction iff they differ by an element of
$`\Gamma(N)`$. Concretely

$$\begin{pmatrix}1 & 0 \\\\ N & 1\end{pmatrix}
   \equiv I \pmod N, \qquad\text{but}\qquad
   \begin{pmatrix}1 & 0 \\\\ N & 1\end{pmatrix} \ne I,$$

and on $`\mathbb{H}`$ the left matrix sends $`\tau`$ to $`\tau/(N\tau+1)`$, not to
$`\tau`$. So it is *not* legitimate to replace an integer matrix by its
reduction inside the slash action; one may do so only after restricting to a
space annihilated by $`\Gamma(N)`$, i.e. to forms of level containing
$`\Gamma(N)`$. That single observation resolves most of the "which
multiplication?" confusion: the mod-$`N`$ statement is the statement about the
level datum, and the integer statement is the statement about the function, and
the bridge is invariant theory for $`\Gamma(N)`$.

### 4.3 Reduction is surjective, and lifting is arithmetic

Moving from a mod-$`N`$ matrix back to an integer one is possible but not
canonical. The reduction
$`\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/N)`$ is surjective:

```lean
private theorem sl2_surj (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N)))
```

([S_ModularCurve_Gamma0_index.lean, lines 137–138](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L137-L138)). The proof is Bezout arithmetic:
a solution $`(\alpha,\beta,\gamma,\delta)`$ over $`\mathbb{Z}`$ of the reduced
determinant equation is produced by `Int.gcdA`/`Int.gcdB`

```lean
private theorem exists_sl2_int_lift {N : ℕ} [NeZero N] {a b c d : ZMod N}
    (h : a * d - b * c = 1) :
    ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧
      (α : ZMod N) = a ∧ (β : ZMod N) = b ∧ (γ : ZMod N) = c ∧ (δ : ZMod N) = d
```

([lines 88–91](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L88-L91)). The ambiguity is
$`\Gamma(N)`$ again: if $`\sigma, \sigma'`$ lift the same mod-$`N`$ matrix then
$`\sigma^{-1}\sigma' \in \Gamma(N)`$. The code packages a choice of lift for the
diamond operator as `gammaLift`:

```lean
def gammaLift (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : Gamma0 M :=
  Classical.choose (CohCarrier.gamma0Units_surjective M d)

theorem gamma0Units_gammaLift (d : (ZMod M)ˣ) : CohCarrier.gamma0Units M (gammaLift M d) = d
```

([Def_CuspForm_HeckeOperatorFormsGammaH.lean, lines 36–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean#L36-L40)), resting on the
surjectivity of $`\gamma_0`$-units `gamma0Units_surjective`
([Def_CohCarrier_Inst.lean, lines 39–53](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Inst.lean#L39-L53)), whose witness is the explicit integer matrix
$`[[u^{-1}, k], [M, u]]`$.

### 4.4 Multiplication inside $`\Gamma_0`$ and the lower-right character

For $`\gamma_1, \gamma_2 \in \Gamma_0(N)`$, the integer product is again in
$`\Gamma_0(N)`$ (mathlib), and its lower-right entry is the product of the two
lower-right entries reduced mod $`N`$:

```lean
theorem d_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ CongruenceSubgroup.Gamma0 N)
    (h₂ : γ₂ ∈ CongruenceSubgroup.Gamma0 N) :
    (((γ₁ * γ₂) 1 1 : ℤ) : ZMod N) = ((γ₁ 1 1 : ℤ) : ZMod N) * ((γ₂ 1 1 : ℤ) : ZMod N)
```

([Def_CuspForm_Gamma1HeckeOperators.lean, lines 225–229](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L225-L229)); this is the
statement that the *mod-$`N`$* multiplication of the lower-right entries is the
shadow of the *integer* multiplication of the matrices. Its companion is the
determinant congruence

```lean
theorem det_mod (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1
```

([lines 231–234](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L231-L234)), i.e. $`a`$ and $`d`$
are inverse units mod $`N`$; the same identity over $`\mathbb{Z}`$ is
`Gamma0_d_mul_a` ([Def_CohCarrier_Level.lean, lines 111–119](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L111-L119)). The
translation between a congruence and a divisibility is the lemma
`ZMod.intCast_zmod_eq_zero_iff_dvd`
([Data/ZMod/Basic.lean, line 513, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Data/ZMod/Basic.lean#L513)), which is used
whenever a mod-$`N`$ vanishing has to be turned into an integer factor (for
instance throughout `heckeRep_mul`, §4.6).

### 4.5 The diamond operator: a choice of lift, proved independent

The diamond operator is the cleanest illustration of the whole
mod-$`N`$/integer relationship. Define the lifts of a unit $`d`$:

```lean
def IsDiamondLift (d : ℕ) (γ : SL(2, ℤ)) : Prop :=
  γ ∈ Gamma0 M ∧ ((γ 1 1 : ℤ) : ZMod M) = (d : ZMod M)

theorem exists_isDiamondLift_of_coprime {d : ℕ} (h : Nat.Coprime d M) :
    ∃ γ : SL(2, ℤ), IsDiamondLift M d γ
```

([Def_CuspForm_Gamma1HeckeOperators.lean, lines 469–480](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L469-L480)); the explicit lift is
$`[[u, -v], [M, d]]`$ from a Bezout pair $`ud + vM = 1`$.
Two lifts of the *same* $`d`$ differ by an element of $`\Gamma_1(M)`$:

```lean
theorem slash_eq_slash_of_isDiamondLift {d : ℕ} {γ γ' : SL(2, ℤ)} (hγ : IsDiamondLift M d γ)
    (hγ' : IsDiamondLift M d γ') (f : CuspForm (Γ₁ℝ M) k) :
    ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ')
```

([lines 556–558](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L556-L558)), so on forms invariant
under $`\Gamma_1(M)`$ the slash by a lift of $`d`$ depends only on $`d`$, and the
diamond operator is well defined:

```lean
def diamondLinOne (d : ℕ) : CuspForm (Γ₁ℝ M) k →ₗ[ℂ] CuspForm (Γ₁ℝ M) k :=
  if h : ∃ γ : SL(2, ℤ), IsDiamondLift M d γ then slashLinOfMemGamma0 M k h.choose_spec.1
  else LinearMap.id
```

([lines 592–594](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L592-L594)); the general $`\Gamma_H`$ version is
`diamondLinH` ([Def_CuspForm_HeckeOperatorFormsGammaH.lean, lines 132–134](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean#L132-L134)).
The shape of the argument is the general one:

$$\underbrace{d \in (\mathbb{Z}/M)^\times}_{\text{mod-}M\text{ object}}
   \\;\longleftarrow\\; \underbrace{\gamma \in \Gamma_0(M)}_{\text{integer lift}}
   \\;\longrightarrow\\; \underbrace{f \mid_k \gamma}_{\text{function-level operator}},$$

and the well-definedness is invariance under the kernel $`\Gamma_1(M)`$ of the
map $`d`$. This is why $`\Gamma_H`$ is built as a pullback: the character
$`d`$ is the mod-$`M`$ object, and the subgroup is its kernel preimage.

### 4.6 The Hecke coset representatives: both multiplications in one statement

The Hecke operator $`T_p`$ for $`p \nmid N`$ is an average of slash actions over
the $`p+1`$ representatives $`[[p, 0], [0, 1]]`$ and
$`[[1, j], [0, p]]`$, and FLT indexes them by the
projective line $`\mathbb{P}^1(\mathbb{Z}/p)`$:

```lean
def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeMatrix p j.val)
```

([Def_CuspForm_Gamma1HeckeOperators.lean, lines 186–187](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L186-L187)). The *label*
$`x`$ is a mod-$`p`$ object; the *representative* is a real matrix. The matrix
that acts on the labels is the reduction of the integer matrix with its entries
read in reverse order:

```lean
def redMatrix (g : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((g 1 1 : ℤ) : ZMod p), ((g 0 1 : ℤ) : ZMod p); ((g 1 0 : ℤ) : ZMod p), ((g 0 0 : ℤ) : ZMod p)]
    ...
```

([lines 254–263](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L254-L263)); its determinant is
nonzero mod $`p`$ because the determinant of $`g`$ is $`1`$ over $`\mathbb{Z}`$,
reduced. The bridge between the integer conjugation and the label permutation is
the lemma

```lean
theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      ((g' 1 1 : ℤ) : ZMod N) * wt N p x = ((g 1 1 : ℤ) : ZMod N) * wt N p (redMatrix p g • x) ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x)
```

([lines 281–285](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L281-L285)). Read it as three
statements in the two arithmetics at once: the integer conjugation of the
representative is again a representative (the real-matrix identity on the third
line); the label moves by the mod-$`p`$ matrix `redMatrix p g`; and the diamond
weight `wt` transforms by the mod-$`N`$ multiplication on the second line. The
proof repeatedly converts $`(g_{10} : \mathbb{Z}/N) = 0`$ into
$`(N : \mathbb{Z}) \mid g_{10}`$ via `ZMod.intCast_zmod_eq_zero_iff_dvd` to
produce the integer lift $`g'`$. This single lemma is the most compact statement
in the code base of *when* each multiplication is used.

## 5. Torsion labels and coset representatives

### 5.1 Torsion labels

Fix a basis $`(P,Q)`$ of $`E[N]`$; every element of $`E[N]`$ is uniquely
$`mP + nQ`$ with $`(m,n) \in (\mathbb{Z}/N)^2`$. These coordinates are the
**torsion labels**. What can act on them is $`\mathrm{GL}_2(\mathbb{Z}/N)`$;
the elements coming from $`\mathrm{SL}_2(\mathbb{Z})`$ form
$`\mathrm{SL}_2(\mathbb{Z}/N)`$. The matrices that act are therefore genuinely
matrices over $`\mathbb{Z}/N`$, and the mod-$`N`$ multiplication is the natural
one here. In the $`\ell`$-adic Hecke theory this is exactly `redMatrix p g`
(§4.6).

A second, finer set of labels is the **set of cyclic subgroups** (or "lines") of
order $`N`$: the cyclic subgroups of $`(\mathbb{Z}/N)^2`$, equivalently the
primitive vectors up to units. These are the points of the projective line:

```lean
def IsUnimodularRow (a c : R) : Prop := ∃ x y : R, x * a + y * c = 1
...
def ProjectiveLine (R : Type*) [CommRing R] : Type _ :=
  Quotient (unimodularRowSetoid R)
```

([Def_ModularCurve_ProjectiveLine.lean, lines 14–15 and 41–42](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ProjectiveLine.lean#L14-L42)). The
subgroup of $`\mathrm{SL}_2(\mathbb{Z}/N)`$ that preserves the first line is the
Borel subgroup

```lean
def borel (R : Type*) [CommRing R] : Subgroup (SpecialLinearGroup (Fin 2) R) where
  carrier := { M | M.1 1 0 = 0 }
```

([lines 69–73](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ProjectiveLine.lean#L69-L73)), i.e. the mod-$`N`$
image of $`\Gamma_0(N)`$ — precisely the statement

```lean
private theorem Gamma0_eq_comap_borel (N : ℕ) :
    Gamma0 N = (borel (ZMod N)).comap
      (SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N)))
```

([S_ModularCurve_Gamma0_index.lean, lines 216–218](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L216-L218)). So the moduli picture
and the group theory meet at one sentence: **the coset space
$`\Gamma_0(N)\backslash\mathrm{SL}_2(\mathbb{Z})`$ is the set of lines in
$`(\mathbb{Z}/N)^2`$, i.e. the set of cyclic subgroups of order $`N`$** — which
is the level datum of $`(E,C)`$. The bijection is by the first column,

```lean
private theorem card_quotient_borel (R : Type*) [CommRing R] :
    Nat.card (SpecialLinearGroup (Fin 2) R ⧸ borel R) = Nat.card (ProjectiveLine R)
```

([lines 191–192](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L191-L192)), and counting the lines gives
the index:

$$[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] = \\#\mathbb{P}^1(\mathbb{Z}/N)
   = \psi(N),$$

which is the FLT theorem `ModularCurve.card_projectiveLine_zmod`
([line 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_card_projectiveLine_zmod.lean#L9)) combined with
`ModularCurve.Gamma0_index`
([Thm_ModularCurve_Gamma0_index.lean, line 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_Gamma0_index.lean#L10)).

### 5.2 The worked case $`N = 2`$

For $`N = 2`$ the lines in $`(\mathbb{Z}/2)^2`$ are the three nonzero vectors,
and the three cosets are exhibited concretely. The private block of
`S_ModularForm_S2_Gamma0_2_eq_zero.lean` reduces the first column
([lines 94–95](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L94-L95)), observes that
right multiplication by $`\Gamma_0(2)`$ does not change it
([lines 120–127](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L120-L127)), and builds the
bijection `cosetToProj` onto the three nonzero vectors
([lines 129–136](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L129-L136)), with explicit
representatives $`S = [[0, -1], [1, 0]]`$, $`1`$, and
$`[[1, 0], [1, 1]]`$ for the three classes. Hence

```lean
theorem Gamma0_two_index_eq_three : (CongruenceSubgroup.Gamma0 2).index = 3
```

([line 170](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean#L170)). This is the coset
count behind [003](003-no-level-2-weight-2-cusp-forms.md).

### 5.3 The q-expansion coset representatives

The cosets that appear in the $`q`$-expansion are the upper-triangular
representatives $`[[a, b], [0, d]]`$ with
$`ad = N`$ and $`\gcd(a,b,d) = 1`$:

```lean
def primCosetReps (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.filter
    (fun t => t.1 * t.2.2 = N ∧ t.2.1 < t.2.2 ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1)
    (Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1))
```

([Def_ModularCurve_PrimCosetReps.lean, lines 8–11](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PrimCosetReps.lean#L8-L11)). Its cardinality is
$`\psi(N)`$ (`card_primCosetReps_eq_dedekindPsi`,
[line 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean#L8)) — the same
number as $`[\Gamma(1):\Gamma_0(N)]`$, but proved by a different count. The
$`q`$-expansion shadow of the representative $`[[a, b], [0, d]]`$
is

```lean
def cosetSubst (ζ : Kˣ) (a b : ℕ) [NeZero a] : LaurentSeries K →+* LaurentSeries K :=
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne a)⟩
  (qExpand K (a * a)).comp (qTwist (ζ ^ (a * b)))
```

([Def_ModularCurve_PhiGen.lean, lines 111–114](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PhiGen.lean#L111-L114)), i.e.
$`q \mapsto \zeta^{ab} q^{a^2}`$ with the $`a^2`$ coming from the modulus of the
coset. The roots of the modular polynomial are indexed by these representatives
in `cosetTwoVarPoly`
([Def_ModularCurve_PrimCosetReps.lean, lines 44–45](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PrimCosetReps.lean#L44-L45)), the formal-model
counterpart of the classical slot formula of [006 §3](006-the-modular-equation.md).

## 6. The moduli data in Lean, and what is *not* formalised

### 6.1 What exists

| moduli datum | Lean | Location |
|---|---|---|
| bare curve | `WeierstrassCurve.j`, `WeierstrassCurve.ofJ` | mathlib `ModelsWithJ.lean` (see [005 §1](005-cyclic-isogenies-and-level.md)) |
| $`(E,C)`$, $`\Gamma_0`$ | `Gamma0Pair` (`toCurve`, `isElliptic`, `gen`, `addOrderOf_gen`) | [ModuliPoint 15–25](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPoint.lean#L15-L25) |
| the quotient | `Gamma0Pair.Step`, `ModuliPoint`, `ModuliPoint.j` | [ModuliPoint 29–41](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPoint.lean#L29-L41) |
| the cyclic subgroup | `CycSub`, `SameOrbit`, `EMD` | [EMD 36–49](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_EMD.lean#L36-L49) |
| a chosen generator | `CycSubH`, `cycSubGen`, `addOrderOf_cycSubGen` | [TatePoint 29–31](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_TatePoint.lean#L29-L31), [CycSubRootBridge 43–52](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_CycSubRootBridge.lean#L43-L52) |
| $`(E,P)`$, $`\Gamma_1`$ | `IsGamma1Point` (a `LevelPData` with $`Q = P`$) | [WeierstrassGamma1Pow 10–18](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_WeierstrassGamma1Pow.lean#L10-L18) |
| the kernel polynomial | `IsCyclicGenKernel`, `IsTwoKernel` | [Gamma0Pow 23–29](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_WeierstrassGamma0Pow.lean#L23-L29), [Gamma0Sqf 22–26](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_WeierstrassGamma0Sqf.lean#L22-L26) |
| $`(E,(P,Q))`$, $`\Gamma(N)`$ | `LevelPData`, `IsLevelPStructure` | [KatzLevelP 42–51 and 104–117](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_KatzLevelP.lean#L42-L117) |
| the relabelling action | `LevelPData.relabel`, `RawDrinfeldPair.relabel` | [LevelRelabelling 29–34 and 53–57](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelRelabelling.lean#L29-L57) |
| Drinfeld basis | `IsDrinfeldBasis`, `RawDrinfeldPair`, `IsDrinfeldLevel` | [DrinfeldBasisGlobal 46–65](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_DrinfeldBasisGlobal.lean#L46-L65) |
| formal-group matrix action | `FormalGroup.baseAct` | [DrinfeldBasis 21–22](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FormalGroup_DrinfeldBasis.lean#L21-L22) |
| a generator over a quaternion order | `FullLevel` (single point, `generates`, `annihilator`) | [QMFineModuli 23–35](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CerednikDrinfeld_QMFineModuli.lean#L23-L35) |
| abstract moduli framework | `LevelModuliDatum`, `ProblemAut` | [LevelModuliPackage 9–37](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelModuliPackage.lean#L9-L37) |

The `IsLevelPStructure` predicate is worth reading in full, because it is the
formal content of "a basis of $`E[N]`$":

```lean
structure IsLevelPStructure {A : Type u} [CommRing A] (W : WeierstrassCurve A) (p : ℕ)
    (D : LevelPData A) : Prop where
  equation_P : W.toAffine.Equation D.xP D.yP
  equation_Q : W.toAffine.Equation D.xQ D.yQ
  preΨ_P : (W.preΨ p).eval D.xP = 0
  preΨ_Q : (W.preΨ p).eval D.xQ = 0
  isUnit_indepElt_PQ : IsUnit (indepElt W p D.xP D.xQ)
  isUnit_indepElt_QP : IsUnit (indepElt W p D.xQ D.xP)
```

([KatzLevelP 104–117](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_KatzLevelP.lean#L104-L117)): the two points lie on
the curve, are killed by the $`p`$-division polynomial `preΨ p` (so are
$`p`$-torsion), and the independence polynomial `indepElt` is a unit — which is
the Weil-pairing/linear-independence condition that upgrades "$`p`$-torsion
pair" to "basis". Both conditions are exactly what they should be: $`n`$-torsion is the vanishing of the division polynomial
(`nsmul_some_eq_zero_iff_eval_prePsi`,
[Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi.lean, line 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi.lean#L15)),
and `indepElt` vanishes precisely when the second point lies in the cyclic subgroup
generated by the first (`indepElt_eq_zero_iff_mem_zmultiples`,
[Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples.lean, lines 18–21](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples.lean#L18-L21)),
so requiring it to be a unit is exactly independence. The pairing is indeed primitive:
`IsPrimitiveRoot ((weilPairing0 W K ℓ P Q : Kˣ) : K) ℓ`
([Thm_..._isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure.lean, lines 186–192](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_isPrimitiveRoot_weilPairing0_toPoint_of_isLevelPStructure.lean#L186-L192)),
and the set of full level structures on a fixed curve is a
$`\mathrm{GL}_2(\mathbb{Z}/\ell)`$-torsor
([Thm_ModularCurve_natCard_levelPData_isLevelPStructure_eq_natCard_GL_of_isAlgClosed.lean, line 22](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_natCard_levelPData_isLevelPStructure_eq_natCard_GL_of_isAlgClosed.lean#L22)).

### 6.2 What is not formalised

It is as important to know the gaps. As of `aa2d8b3`:

* **There is no `Module.Basis (Fin 2) (ZMod N) E[N]`.** The closest statements
  are the injective additive map $`(\mathbb{Z}/p)^2 \hookrightarrow E`$ of
  `Thm_ModularCurve_IsLevelPStructure_exists_injective_addMonoidHom_zmod_prod.lean`
  ([line 13](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_IsLevelPStructure_exists_injective_addMonoidHom_zmod_prod.lean#L13))
  plus the cardinality counts. In the quaternionic (Cerednik–Drinfeld) setting
  there *is* an additive isomorphism
  $`\mathbb{Z}/N \times \mathbb{Z}/N \simeq \{P : \text{killed by } N\}`$
  ([Def_CerednikDrinfeld_QMModuli.lean, line 143](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CerednikDrinfeld_QMModuli.lean#L143)).
* **There is no group-action statement of the naive form
  $`\mathrm{SL}_2(\mathbb{Z}/N) \to^* \mathrm{Equiv}(E[N]\times E[N])`$.** The
  action is encoded by `LevelPData.relabel` (an integer matrix, factoring
  through $`\mathbb{Z}/N`$), by `FormalGroup.baseAct`, and by the
  $`\mathrm{SL}_2(\mathbb{Z}/q)`$-actions on the Drinfeld coordinate ring
  (`slAction`, [Def_DrinfeldCurve_CoordRing.lean, lines 149–166](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DrinfeldCurve_CoordRing.lean#L149-L166)) and on the
  Jacobian/Tate module (`redQ`, `slJac`, `gl2Jac`,
  [Def_ModularCurve_FullLevelJacobian.lean, lines 230–262](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_FullLevelJacobian.lean#L230-L262)).
* **Mathlib's elliptic-curve library has no torsion module, no Weil pairing and
  no level structure.** All of these are FLT's own definitions.
* **There is no moduli *scheme* $`X(N)`$ identified with the $`(P,Q)`$-functor.**
  The moduli interpretation is carried by the Katz level-$`p`$ forms and the
  rigid Weierstrass data, not by a scheme-level theorem.
* **There is no analytic dictionary between `LevelPData.relabel` and the
  $`\tau`$-action.** Nothing in FLT relates the Katz–Mazur relabelling action to
  the Möbius action of $`\mathrm{SL}_2(\mathbb{Z})`$ on $`\mathbb{H}`$; the two
  live in disjoint parts of the development, and the only $`\mathbb{H}`$-facing
  declarations are the slash action and the Hecke operators. §1.5 states the
  dictionary — the induced relabelling matrix and the agreement of the three
  congruence conditions — and
  [`LevelTauBridge.lean`](../lean/Reserve/ModularCurve/Analytic/LevelTauBridge.lean)
  checks it. The remaining step — the identification of
  $`\Gamma\backslash\mathbb{H}`$ with the level-data functor, i.e.
  uniformization plus Riemann existence — is present in neither FLT nor
  mathlib.
* **`IsGamma1Point` does not enforce exact order.** It only asks that
  $`(W.\mathrm{pre}\Psi\,\ell)(P) = 0`$, i.e. that $`P`$ is $`\ell`$-torsion;
  exact order is asserted by `addOrderOf_gen = N` in `Gamma0Pair` and by the
  Cerednik–Drinfeld `FullLevel`'s `annihilator`.
* **`FullLevel` is a one-point generator, not a two-point basis.** The two-point
  full level is `LevelPData`/`IsLevelPStructure` and `RawDrinfeldPair`.

One caveat about the naming of `Gamma0Pair`: the structure records a *point*
`gen` of exact order $`N`$, but the quotient `ModuliPoint` identifies two
generators when they differ by a unit $`k`$ coprime to $`N`$
([ModuliPoint 29–31](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPoint.lean#L29-L31)). So `Gamma0Pair` is the
generator-level presentation and `ModuliPoint` is the subgroup-level moduli
problem — consistent with the name, and the reason [005 §1](005-cyclic-isogenies-and-level.md)
reads it as the $`\mathcal{C}`$ of $`X_0(N)`$.

## 7. Key point $`\to`$ declaration map

| Mathematics | Lean declaration | Location |
|---|---|---|
| reduction $`\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{SL}_2(\mathbb{Z}/N)`$ | `SLMOD(N)` (local notation) | [mathlib 29–30](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L29-L30) |
| reduction is entrywise | `SL_reduction_mod_hom_val` | [mathlib 33](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L33) |
| $`\Gamma(N)`$ | `CongruenceSubgroup.Gamma N` | [mathlib 41](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L41) |
| $`\Gamma_0(N)`$ | `CongruenceSubgroup.Gamma0 N` | [mathlib 79](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L79) |
| lower-right entry | `Gamma0Map N` | [mathlib 95](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L95) |
| $`\Gamma_1(N)`$ | `Gamma1 N` | [mathlib 131](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L131) |
| slash formula over $`\mathrm{SL}`$ | `SL_slash_apply` | [mathlib SlashActions 162](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean#L162) |
| $`\mathrm{denom}`$ | `UpperHalfPlane.denom` | [mathlib MoebiusAction 33](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean#L33) |
| invariance field | `SlashInvariantForm.slash_action_eq'` | [mathlib 34–36](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean#L34-L36) |
| mod-$`N`$ image of $`\Gamma_0`$ is the Borel | `Gamma0_eq_comap_borel` | [S file 216–218](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L216-L218) |
| reduction surjective, lifts by Bezout | `sl2_surj`, `exists_sl2_int_lift` | [S file 137 and 88](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean#L88-L91) |
| lower-right is multiplicative mod $`N`$ | `d_mul`, `det_mod` | [Gamma1Hecke 225 and 231](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L225-L234) |
| lower-right is a unit | `gamma0Units` | [CohCarrier_Level 121–131](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L121-L131) |
| $`\Gamma_H`$ | `GammaH` | [CohCarrier_Level 133–134](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L133-L134) |
| $`\Gamma_H = \Gamma_1`$ at $`H = \bot`$ | `GammaH_bot` | [XH 46–60](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XH.lean#L46-L60) |
| $`\Gamma_H`$ normal in $`\Gamma_0`$ | `GammaH_normal_in_Gamma0` | [CohCarrier_Level 261–273](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L261-L273) |
| index of $`\Gamma_H`$ | `CohCarrier.index_gammaH_eq_index_gamma0_mul_index` | [Thm 8–9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index.lean#L8-L9) |
| $`n`$-torsion is `preΨ` vanishing | `nsmul_some_eq_zero_iff_eval_prePsi` | [Thm 15](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi.lean#L15) |
| `indepElt` vanishing is cyclic membership | `indepElt_eq_zero_iff_mem_zmultiples` | [Thm 18–21](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples.lean#L18-L21) |
| chosen lift of a unit | `gammaLift` | [FormsGammaH 36–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean#L36-L40) |
| diamond well-definedness | `IsDiamondLift`, `slash_eq_slash_of_isDiamondLift` | [Gamma1Hecke 469 and 556](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L469-L558) |
| mod-$`p`$ label matrix | `redMatrix` | [Gamma1Hecke 254–263](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L254-L263) |
| integer conjugation $`\leftrightarrow`$ label move | `heckeRep_mul` | [Gamma1Hecke 281–285](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L281-L285) |
| matrix action on $`(P,Q)`$ | `LevelPData.relabel` | [LevelRelabelling 29–34](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelRelabelling.lean#L29-L34) |
| full level structure | `LevelPData`, `IsLevelPStructure` | [KatzLevelP 42 and 104](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_KatzLevelP.lean#L42-L117) |
| $`(E,P)`$ exact order | `Gamma0Pair.gen`, `addOrderOf_gen` | [ModuliPoint 15–25](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPoint.lean#L15-L25) |
| cyclic subgroup moduli | `CycSub`, `EMD` | [EMD 36–49](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_EMD.lean#L36-L49) |
| cosets are lines | `ProjectiveLine`, `borel` | [ProjectiveLine 41 and 69](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ProjectiveLine.lean#L41-L73) |
| index $`\psi(N)`$ | `Gamma0_index`, `card_projectiveLine_zmod` | [Thm 10](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_Gamma0_index.lean#L10), [Thm 9](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_card_projectiveLine_zmod.lean#L9) |
| $`q`$-expansion coset reps | `primCosetReps`, `cosetSubst` | [PrimCosetReps 8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PrimCosetReps.lean#L8-L11), [PhiGen 111](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PhiGen.lean#L111-L114) |
| $`E[N]`$ as $`\mathbb{Z}/N`$-module | `instModuleZModTorsionBy`, `torsionBy.zmodModule` | [FLTPrelim_GaloisRep 60](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean#L60-L64), [mathlib 1009](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Torsion/Basic.lean#L1009-L1012) |
| Möbius formula with integer entries | `coe_smul_eq` | [Bridge 132](../lean/Reserve/ModularCurve/Analytic/LevelTauBridge.lean#L132) |
| torsion images $`a - c\,\gamma\tau`$, $`d\,\gamma\tau - b`$ | `image_P_eq`, `image_Q_eq` | [Bridge 208 and 215](../lean/Reserve/ModularCurve/Analytic/LevelTauBridge.lean#L208-L215) |
| analytic relabelling matrix $`D\gamma D`$ | `torsionMatrix`, `torsionMatrix_eq_conj`, `torsionMatrix_det` | [Bridge 93–104](../lean/Reserve/ModularCurve/Analytic/LevelTauBridge.lean#L93-L104) |
| analytic stabilisers are the congruence subgroups | `gamma0_iff_torsionMatrix`, `gamma1_iff_torsionMatrix`, `Gamma_iff_torsionMatrix` | [Bridge 226–239](../lean/Reserve/ModularCurve/Analytic/LevelTauBridge.lean#L226-L239) |

## 8. Lean detours (not mathematics)

* **`GammaH` is a `comap`/`map`, not a set-builder.** The definition
  `(H.comap (gamma0Units M)).map (Gamma0 M).subtype` exists so that the group
  structure is inherited; the readable form is `mem_GammaH_iff`. The same is
  true of mathlib's `Gamma1`, which is a `Subgroup.map` rather than the
  entrywise set (the entrywise form is `Gamma1_mem`).
* **`gamma0Units` is a repair.** `Gamma0Map` lands in the monoid
  $`\mathbb{Z}/N`$; to take a kernel one needs a group-valued map, and
  `gamma0Units` supplies the unit structure using the determinant identity
  `Gamma0_d_mul_a`. This is why $`\Gamma_H`$ can be a pullback at all.
* **Classical choice in the diamond operators.** `diamondLinOne`, `diamondLinH`
  and `diamondAut` are of the form
  `if h : ∃ …, then h.choose … else LinearMap.id`. The `else` branch is a junk
  value; the mathematics is in the lemmas
  (`coe_diamondLinOne_apply`, `slash_eq_slash_of_isDiamondLift`) that compute the
  operator on the good locus.
* **The torsion module is not a lattice.** `Submodule.torsionBy ℤ E.Point n` is
  a $`\mathbb{Z}`$-submodule of the point group, and the $`\mathbb{Z}/n`$-module
  structure is installed by hand (`instModuleZModTorsionBy`) or by mathlib
  (`torsionBy.zmodModule`). Nothing here is a lattice in $`\mathbb{C}`$.
* **`IsGamma1Point` reuses `LevelPData`.** Instead of a separate one-point
  structure, the code takes a `LevelPData` and forces $`x_Q = x_P`$,
  $`y_Q = y_P`$; the field is the full-level record with the second point
  collapsed.
* **`FullLevel` (Cerednik–Drinfeld) is a one-point generator.** Its `generates`
  and `annihilator` fields say the single point generates the $`m`$-torsion as a
  module over a quaternion order, which is the $`(E,P)`$ side, not the
  $`(E,(P,Q))`$ side. The two-point side is `LevelPData`/`RawDrinfeldPair`.
* **`indepElt` is a polynomial, not a matrix.** The linear-independence
  condition in `IsLevelPStructure` is encoded by the non-vanishing (unit-ness)
  of an explicit product of division-polynomial values; the matrix language of
  §5.1 is the human translation, not the Lean one.
* **The analytic bridge is our own module, not a port.** FLT has no counterpart
  to compare `LevelTauBridge.lean` against, so §1.5's dictionary is stated and
  proved from scratch. It lives in `lean/Reserve/` because nothing in
  `FLTForHuman` consumes it: it verifies the note's reasoning rather than
  advancing the critical-path port. It is phrased with the `ℤ`-cast denominator
  `denomC γ τ = cτ + d` rather than mathlib's `algebraMap`-based
  `UpperHalfPlane.denom (mapGL ℝ γ)`, so that the torsion arithmetic and
  `torsionMatrix` use one coercion system; reconciling the two is the single
  private lemma `algebraMap_intCast_complex`.
* **`lat` is a `ℤ`-submodule, not a complex lattice.** In `LevelTauBridge.lean`
  the object is `lat τ = Submodule.span ℤ ({1, τ} : Set ℂ)`, a `Submodule ℤ ℂ`;
  so the marking change is the `ℤ`-module statement
  `Submodule.map (mulBy (cτ + d)) (lat (γ • τ)) = lat τ` (`lat_smul_moebius`).
  The factor `cτ + d` — rather than an isomorphism of complex lattices — is
  exactly what makes the two identities `1/(cτ+d) = a - c·γτ` and
  `τ/(cτ+d) = d·γτ - b` (`inv_denom_eq`, `tau_div_denom_eq`) available; those
  identities are the actual content of the label change that §1.5 computes.
  This is the step that prose cannot state unambiguously without naming the map:
  "equal up to the marking change" is only a `ℤ`-module equality once `cτ + d`
  is written down.

## 9. Links

FLT sources at the pinned sha `aa2d8b3`:

* [Def_CohCarrier_Level.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean) — `gamma0Units`, `GammaH`, `mem_GammaH_iff`, `GammaH_normal_in_Gamma0`, `Gamma0Upper`, `GammaHUpper`
* [Def_ModularCurve_XH.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XH.lean) — `GammaH_bot`, `Gamma1_le_GammaH`, `xHFunctionFieldC`
* [Def_CuspForm_HeckeOperatorFormsGammaH.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean) — `Gamma_le_GammaH`, `gammaLift`, `diamondLinH`
* [Def_CuspForm_Gamma1HeckeOperators.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean) — `redMatrix`, `heckeRep`, `IsDiamondLift`, `slash_eq_slash_of_isDiamondLift`, `diamondLinOne`
* [Def_ModularCurve_ProjectiveLine.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ProjectiveLine.lean) — `IsUnimodularRow`, `ProjectiveLine`, `borel`
* [Def_ModularCurve_PrimCosetReps.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PrimCosetReps.lean) — `primCosetReps`
* [Def_ModularCurve_ModuliPoint.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ModuliPoint.lean) — `Gamma0Pair`, `ModuliPoint`
* [Def_ModularCurve_EMD.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_EMD.lean) — `CycSub`, `SameOrbit`, `EMD`
* [Def_ModularCurve_KatzLevelP.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_KatzLevelP.lean) — `LevelPData`, `IsLevelPStructure`
* [Def_ModularCurve_LevelRelabelling.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelRelabelling.lean) — `LevelPData.relabel`
* [Def_ModularCurve_WeierstrassGamma1Pow.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_WeierstrassGamma1Pow.lean) — `IsGamma1Point`
* [Def_ModularCurve_LevelModuliPackage.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LevelModuliPackage.lean) — `LevelModuliDatum`, `ProblemAut`
* [S_ModularCurve_Gamma0_index.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_Gamma0_index.lean) — `sl2_surj`, `exists_sl2_int_lift`, `Gamma0_eq_comap_borel`, `card_quotient_borel`
* [Thm_ModularCurve_Gamma0_index.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_Gamma0_index.lean), [Thm_ModularCurve_card_projectiveLine_zmod.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_card_projectiveLine_zmod.lean) — the index count
* [Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index.lean) — the index of $`\Gamma_H`$
* [Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples.lean) and [Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi.lean) — the exact meaning of `indepElt` and `preΨ`

Own Lean sources (this repository):

* [`Reserve/ModularCurve/Analytic/LevelTauBridge.lean`](../lean/Reserve/ModularCurve/Analytic/LevelTauBridge.lean) — the matrix computations of §1.5: `image_P_eq`, `image_Q_eq`, `torsionMatrix`, `torsionMatrix_eq_conj`, `torsionMatrix_det`, `gamma0_iff_torsionMatrix`, `gamma1_iff_torsionMatrix`, `Gamma_iff_torsionMatrix`, on the `denomC` identities `coe_smul_eq`, `inv_denom_eq`, `tau_div_denom_eq`

Mathlib at tag `v4.33.0`:

* [CongruenceSubgroups.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean) — `Gamma`, `Gamma0`, `Gamma1`, `Gamma0Map`, `SLMOD`, `IsCongruenceSubgroup`
* [SlashInvariantForms.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean) and [SlashActions.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/ModularForms/SlashActions.lean) — the slash action and its two instances
* [MoebiusAction.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean) — `denom`, the Möbius action on $`\mathbb{H}`$
* [Module/Torsion/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Torsion/Basic.lean) — `Submodule.torsionBy`, `torsionBy.zmodModule`
* [GroupTheory/Index.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/GroupTheory/Index.lean) and [GroupTheory/Transfer.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/GroupTheory/Transfer.lean) — `Subgroup.index`, `Subgroup.LeftTransversal`, `MonoidHom.transfer`

Companion notes:

* [002 — Modular forms at the mathlib level](002-modular-forms-basics.md) — the analytic objects and mathlib's inventory
* [004 — The j-invariant](004-the-j-invariant.md) — the level-one case
* [005 — Cyclic isogenies, congruence level, and the j-invariant](005-cyclic-isogenies-and-level.md) — the lattice/analytic picture and the monodromy computation
* [006 — The modular equation](006-the-modular-equation.md) — the coset slots in the q-expansion
* [014 — Hecke operators](014-hecke-operators.md) — the coset representatives in action

Background:

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228, Springer 2005, Ch. 1 — congruence subgroups, the moduli problems, and $`X_0(N)`$.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton 1971, Ch. 1 — the classical correspondence between congruence subgroups and level structures.
* J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, Springer 1994, Ch. I — torsion, level structures and the Weil pairing.
