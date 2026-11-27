# The abstract double-coset Hecke calculus (taken from the GRH proof)

**Status: Stage A landed; the classical layer consolidated; the `Γ_H` family retargeted and its
old module deleted (2026-11-26).**
`RepTheory/DoubleCosetHecke.lean` (the calculus) and `ModularForms/HeckeCosetSum.lean` (the
classical layer) build on mathlib `v4.34.0`, no warnings, no `sorry`. The classical layer has one
object (`HeckeCoset.Transversal`: the three geometric facts that say "these are the cosets of `K` in
`K g K`") and four statements it buys — the level invariance (`slash_invariant`), the independence
of the transversal (`sum_eq_sum`), the operator identity (`sum_eq_doubleCosetOperator`) and the
period theorem (`sum_sub_eq_cocycle`). The family-facing object is stated in `GL (Fin 2) ℝ` with no
coset quotient, no opposite group, no `GL(2,ℝ)⁺` positivity hypothesis and no representation.

The `Γ_H(M)` family is retargeted whole: `ModularForms/HeckeCosetGammaH.lean` now carries the level
pair, the **two** transversals — `ZMod q` for `q ∣ M`, the projective line `ℙ¹(ℤ/ℓ)` for `ℓ ∤ M` —
and the pin's own `beta` family, and `ModularForms/HeckeCosetDecomposition.lean` is deleted (its
pin source is carried by a header-only file in `Reserve/`). Both consumers
(`HeckeInvariance`, `ModularCurve/Period/PeriodMapHecke`) are re-proved through the new module;
§5.6 is the record. The first cut of the carrier (`HeckeSlashRep.lean`) stays archived in
`Reserve/HeckeCosetCalculus/`, dead.

Corrections to the earlier text of this note. (i) The two adapter theorems the earlier §4 called
"remaining" and "blocked" were landed in the first cut, and its §4 friction was worked around
rather than removed. (ii) Its price for a family's coset system counted unrelated machinery; the
measured cost is in §4.3. (iii) §4.4 explains why rebuilding the calculus is not one of the
options, and §4.2 why the side (left or right cosets) is a convention.

**Audience.** A fresh session continuing the Hecke refactor. Read [refactor.md](../refactor.md)
for the standard this order is written against, and [PORTING-Hecke.md](../PORTING-Hecke.md)
§§1–3 for the port's Hecke inventory.

## 0. The finding this order acts on

The port has two Hecke infrastructures and they do not meet:

| layer | modules | lines |
|---|---|---:|
| adelic abstract | `RepTheory/AbstractHeckeOperator`, `RepTheory/LocalLanglands/{HeckePair,HeckeCosetSystem}`, `RepTheory/AntiInvolutionHaar` | 1,825 |
| classical | `ModularForms/Hecke*`, `ModularForms/Defs/Hecke{Operator,Representatives,FormalHeckeOperators,Gamma1HeckeOperators}`, `ModularForms/Analytic/PeterssonHecke*` | 8,908 |

The abstract side has the operator, the coset system and the convolution algebra; the classical
side has the mathematics but re-derives the coset bookkeeping per level. The missing piece is an
operator *calculus*: representative-independence stated for an operator on a vector rather than
for a sum of values, transport along a group hom, left translation, composition as convolution,
and a character-twisted level space. That calculus exists, proved, in the GRH development, and it
is 420 lines with mathlib as its only dependency.

## 1. The source

`lsernau/grh-lean`, pinned `72fead1`, `grh/src/Lib/Adelic/Hecke/Basic.lean` (420 lines). The file's
own `Lib.Base` import is a mathlib instantiation-speed setup (`Lib.Speed`); it is **not** part of
what is ported. Nothing else in the file is GRH-specific: no number field, no `GL₂`, no adeles.

| source declaration | line | the mathematics |
|---|---:|---|
| `rightRegular` | 54 | the right regular representation `(g·F)(x) = F(xg)` |
| `levelSpace π K χ` | 63 | `{v \| π k v = χ k • v}`: the character-twisted fixed points |
| `heckeFun π K f` | 73 | `∑ᶠ q : G ⧸ K, f q.out • π q.out` — the operator **of a function `f`** |
| `heckeCoset π K g` | 77 | `heckeFun` of the indicator of the double coset `K g K` |
| `classAut Γ K g` | 80 | `Γ ⊓ g K g⁻¹` — the stabiliser of the coset `gK` in `Γ` |
| `mem_levelSpace`, `map_mem_levelSpace_of_commute` | 88, 93 | the eliminator, and linear maps commuting with `π` preserve it |
| `classSum`, `classSum_eq_finsum_of_rep`, `card_classAut_mul_mul` | 132, 149, 136 | the weighted class sum over `Γ \ G / K`; not taken (§3.3) |
| `isLocallyConstant_of_eventually_mul` | 168 | right-invariance near `1` gives local constancy |
| `finite_quotient_image_of_isCompact`, `IsCompact.relIndex_ne_zero` | 178, 186 | a compact set meets finitely many `H`-cosets |
| `relIndex_mul_measure_inf`, `measure_inter_eq_inv_relIndex` | 194, 214 | `[K : H ⊓ K] · μ(H ⊓ K) = μ K` |
| `HasFiniteCosets K f`, `IsHeckeFunction K f` | 241, 244 | `f` lives on finitely many cosets; bi-invariant and finite |
| `heckeFun_eq_sum_toFinset`, `map_heckeFun` | 250, 258 | the finite sum over an explicit `Finset`; an intertwining `L` transports the operator |
| `levelSpace_anti` | 262 | `K ≤ K'` gives `levelSpace K' ≤ levelSpace K` |
| `isHeckeFunction_doubleCoset` | 267 | `1_{KgK}` is a Hecke function (`K` compact open) — not taken (§3.1) |
| **`heckeFun_eq_sum`** | 285 | **any representative system** `s` gives the operator |
| **`heckeFun_eq_sum_pullback`** | 307 | the same for `θ : G' → G` inducing `G' ⧸ J ↪ G ⧸ K` |
| `HasFiniteCosets.comp_inv_mul` | 348 | a left translate keeps `HasFiniteCosets` |
| **`heckeFun_comp_inv_mul`** | 361 | `heckeFun` of `x ↦ f (x⁻¹ * g)` is `π x` of `heckeFun f` |
| `heckeFun_comp` | 330 | transport along a surjective hom with `a ⁻¹K = J` |
| **`heckeFun_heckeFun`** | 378 | composition of operators = operator of the convolution |
| **`heckeFun_mem_levelSpace`** | 395 | a bi-invariant `f` sends `levelSpace (K,χ)` into `levelSpace (K',χ')` |
| `IsHeckeFunction.heckeFun_mem` | 410 | the trivial-character case, the invariance theorem |

The bold rows are the calculus; the rest is definition side or the compact-open/measure layer.

## 2. What landed

### Stage A — `FLTForHuman/RepTheory/DoubleCosetHecke.lean` (green)

The calculus of §1, namespace `DoubleCosetHecke`, statements as in the source:

`levelSpace` (with its character and the `mem_levelSpace` eliminator),
`map_mem_levelSpace_of_commute`, `levelSpace_anti`, `heckeFun`, `heckeCoset`,
`HasFiniteCosets`, `IsHeckeFunction`, `heckeFun_eq_sum_toFinset`, `heckeFun_apply` (added: the
value at a vector as a coset sum), `map_heckeFun`, `heckeFun_eq_sum`,
`heckeFun_eq_sum_pullback`, `heckeFun_comp`, `HasFiniteCosets.comp_inv_mul`,
`heckeFun_comp_inv_mul`, `HasFiniteCosets.convolution` (added: the convolution of two Hecke
functions lives on finitely many cosets, the hypothesis `heckeFun_heckeFun` needs),
`heckeFun_heckeFun`, `heckeFun_mem_levelSpace`, `IsHeckeFunction.heckeFun_mem`, plus the local
`sum_apply_end` (evaluation of a finite sum of endomorphisms; mathlib's `Finset.sum_apply` does
not apply to `Module.End`).

**mathlib v4.34 vs the source's `56a0058`.** Two renames and nothing else:
`finsum_eq_sum_of_support_subset` is `finsum_eq_finsetSum_of_support_subset` (a `Finset`
argument, not a `Set`), and `fun_smul_left`/`fun_smul_right` (used only inside
`heckeFun_heckeFun`) are replaced by `finsum_sum_comm`/`sum_finsum_comm` + `smul_finsum'`.
`heckeFun_heckeFun` is proved by taking both sides to the double sum
`∑ q ∈ s, ∑ᶠ p, (f' q · f (q⁻¹ p)) • π p • v`; the finiteness needed for the interchange is
`HasFiniteCosets.comp_inv_mul`. `rfl`-level detail: `smul_smul` in v4.34 is the iterated-action
lemma, the scalar-multiplication one is `mul_smul`.

The module is **group-agnostic**: it is stated for an arbitrary `Group G` and an arbitrary
`Representation A G W`, and it contains no `MulOpposite` and no `.op` (measured, §7). This matters
for §4.4.

### Stage B — `FLTForHuman/ModularForms/HeckeCosetSum.lean` (green)

The classical layer is now one module, with one object and one invariance statement. It supersedes
the first cut (`ModularForms/HeckeSlashRep.lean`), which carried the same mathematics in the
opposite group; that file is archived to `Reserve/HeckeCosetCalculus/ModularForms/HeckeSlashRep.lean`
because it still holds the one piece this module does not have yet (below), and its `op`-form
statements are the reference for re-proving it.

* **`Transversal K g ι`** — a finite family of representatives of the **left** cosets of `K` in
  `K g K`, as three fields in `GL (Fin 2) ℝ` with no quotient, no opposite group and no
  representation:
  `mem : ∀ i, r i ∈ K g K`; `distinct : ∀ i j, r i * (r j)⁻¹ ∈ K → i = j`;
  `cover : ∀ x ∈ K g K, ∃ i, x * (r i)⁻¹ ∈ K`.
  This is the whole of a family's concrete input, and it is the mathematics: the three statements
  *are* "these are the cosets".
* **`Transversal.slash_invariant`** — the level invariance of the coset sum, derived from the three
  fields: right multiplication by `γ ∈ K` moves `r i` into the coset of another representative,
  `r i * γ = κ i * r (σ i)` with `κ i ∈ K`, and the permutation `σ` and the cocycle `κ` are
  constructed inside the proof (`Classical.choose` on `cover`, injectivity from `distinct`). A
  family therefore never states a cocycle, a permutation, a quotient computation or a reindexing:
  it states its cosets once.
* The carrier, for the operator identity: the slash action as a representation of `GL(2,ℝ)⁺` itself
  (`SlashAction` instance, `slash_coe`, `slashLin`, `slashRep`, `slashRep_apply`) and the level-space
  dictionary `mem_levelSpace_slashRep` (`F ∈ levelSpace (slashRep k) K ↔ ∀ γ ∈ K, F ∣[k] γ = F`).
  `slashRep` is the **inverse action** `γ ↦ slash(γ⁻¹)` — the equivalent genuine left action of
  §4.2 — so `MulOpposite` appears nowhere in the module.

**The operator identity** (`Transversal.sum_eq_doubleCosetOperator`): for a transversal of `K g K`
whose elements have positive determinant — derived from `mem` together with the positivity of `K`
and of `g` — the coset sum *is* the abstract double-coset operator,
`∑ i, F ∣[k] T.r i = doubleCosetOperator k K g hg F`. The label of the operator is `g⁻¹`
(`invPos`), because `slashRep` is the inverse action: the two inversions cancel, so the operator of
the coset sum over the left cosets of `K g K` is the operator of `K g K`. The bridge is one lemma,
`mem_doubleCoset_levelPos_iff` (membership in a double coset of `GL(2,ℝ)⁺` is membership in the
double coset of its image, and the converse lifts the two level elements — that is the only place
the determinant positivity is used). With this, the abstract calculus has a live consumer again, and
a family that states its three geometric facts gets both the invariance and the operator identity
without writing a coset quotient.

**Still not independently validated.** The operator identity is now used — `sum_eq_sum` compares two
transversals through it — but a wrong label would cancel between the two uses, so it is still not
checked against an independently proved concrete formula. The check is a family whose *operator*
(not just its sum) is compared with a pin formula: `sum_beta_eq_heckeU` for `Γ_H` is such a
formula, and it is reached through `sum_eq_sum`, so it does not validate the label either. What
would is a direct computation of `doubleCosetOperator` against `heckeU_eq_sum_zmod` /
`heckeT_eq_sum_onePoint` (`Γ₀`), which no family has attempted.

**One finding that shaped both carrier and module** (mathematics, not Lean friction): the slash
action is **σ-semilinear** — `smul_slash` carries `σ g`, which is conjugation for `det g \lt 0` —
so it is `ℂ`-linear only on `GL(2,ℝ)⁺`, where the Hecke operators live (`heckeMatrix`/
`heckeDiagMatrix` have determinant `p \gt 0`, the congruence subgroups determinant `1`). That is
why `slashRep` is on `GL(2,ℝ)⁺` and why the family-facing `Transversal` is stated in
`GL (Fin 2) ℝ` instead: the positivity enters only the operator identity.

### Stage C — started

The `Γ_H` family is retargeted whole and its old module deleted (§5.6). The other four files of the
replacement set are untouched; §6 is the order they go in.

## 3. What stays out, and why

3.1 **Compact open → commensurable.** The source's `isHeckeFunction_doubleCoset` derives
finiteness from `K` compact open. Our `K` is discrete, so the hypothesis has to be finite right
index of `K ⊓ g K g⁻¹` in `K`. Not ported: no consumer needs it, because a concrete coset system
supplies finiteness through `heckeFun_eq_sum`'s covering hypothesis. If it is ever wanted, the proof
is the orbit-stabilizer bijection `{k g K : k ∈ K} ≃ K ⧸ (K ⊓ g K g⁻¹)` plus
`Subgroup.fintypeQuotientOfFiniteIndex`.

3.2 **The measure layer** (`relIndex_mul_measure_inf`, `measure_inter_eq_inv_relIndex`,
`isLocallyConstant_of_eventually_mul`): the adelic measure bookkeeping behind the `1/#aut`
weights. The port has the analytic counterparts in `AutomorphicForm/Adelic`.

3.3 **`classSum`/`classIntegral`/orbit unfolding/`compactMean`**: the trace-formula and averaging
layer. Two statements are worth remembering rather than porting: `smul_classSum_mem` (integrality
of a weighted class sum when every stabiliser order divides `M`) and `classSum_le_card_mul` (a
bound by the number of classes). Both are analogues of statements the port proves by coefficients
(`mem_intLattice_of_mem_heckeAlgebra`, the Sturm bound).

3.4 **Gelfand's trick** (`Lib/General/LinearAlgebra/IntegralLattices.lean:297–470`:
`heckeFun_adjoint`, `heckeFun_comm`) is out of scope for the classical retarget, for a
mathematical reason: it rests on Gelfand's condition $`g^{\mathsf T} = (k^{\mathsf T})^{-1} g k`$
with $`k \in GL_n(O)`$, $`O`$ a valuation subring — a property of the pair $`(G,K)`$ that holds
for the maximal compact of a local field and fails for $`K = \Gamma_0(N)`$, $`N \gt 1`$ (the
involution multiplies $`\det`$ by $`(\det g)^{-2}`$, and the Weyl element is not in
$`\Gamma_0(N)`$). That is exactly why the classical adjoint of $`T_p`$ at $`\Gamma_1(N)`$ is
$`T_p`$ only up to $`\overline{\varepsilon(p)}`$ — the diagonal summand is the correction, see
`Analytic/PeterssonHeckeTheorems`. If the adelic side wants a measure-free Gelfand theorem,
`HeckePair.conv` already is a `finsum` convolution and the port is ~50 lines; it would supersede
the `IsHaarMeasure`/`map θ = ν` hypotheses of `AntiInvolutionHaar.convKer_comm`. Separate order.

## 4. The representation convention

This section is the part of the note that a fresh session most needs: it separates what the
carrier's opposite group costs from what it does not, and it prices the adapter.

### 4.1 Why the carrier is an opposite group

Slash is a right action: $`F \mid_k (\gamma\delta) = (F \mid_k \gamma) \mid_k \delta`$. A right
action on a linear space is a monoid hom $`G \to (\mathrm{End} W)^{\mathrm{op}}`$, which mathlib
spells as an action of `Gᵐᵒᵖ`; hence `slashRep k : Representation ℂ (GL(2,ℝ)⁺)ᵐᵒᵖ (ℍ → ℂ)`.

The calculus is stated for a left action and indexes by `G ⧸ K`, which in mathlib is the set of
**right** cosets $`\{xK\}`$ (`Mathlib/GroupTheory/Coset/Defs.lean:66`: $`x^{-1}y \in K`$), with
`G` acting on the left. A left action pairs with right cosets, and a right action pairs with left
cosets: for a right action $`\rho`$ and a vector fixed by $`\rho k`$ for $`k \in K`$,

* $`\rho(k x) v = (\rho x)(\rho k) v = \rho x \, v`$ — well defined on the left coset $`Kx`$;
* $`\rho(x k) v = (\rho k)(\rho x) v`$ — not controlled, so not well defined on $`xK`$.

So the well-defined coset sum for slash is the **left**-coset sum, and the classical Hecke sums are
exactly that. Each family's coset action has the shape

> $`r_i \gamma = k_i \, r_{\sigma i}`$ with $`k_i`$ in the level group and $`\sigma`$ a
> permutation of the index set,

i.e. right multiplication by a level element permutes the left cosets $`K r_i`$
(`heckeMatrix_mul_of_dvd`, `heckeRep_mul`, `mapGL_conjL_mul_heckeMatrix`, `exists_cocycle` at
`HeckeULevel.lean:59`); the diagonal level-change family is the degenerate instance, a singleton
index set with $`\sigma = \mathrm{id}`$ and $`k_i`$ the level change (`HeckeDiagDegeneracy`'s
`exists_cocycle`). `Gᵐᵒᵖ` is the cheapest way to get a group whose right-coset quotient is the
left-coset space of `G`: $`\mathrm{op}(x) \cdot K^{\mathrm{op}} = \mathrm{op}(Kx)`$. That is the
whole justification of the carrier, and it is correct: the operator the adapter computes is the
operator the classical side means.

### 4.2 The side is a convention, not a constraint

The pairing above is asymmetric only because *the representation* was fixed first. The two
pairings — (right action, left cosets) and (left action, right cosets) — carry the same
mathematics, and the dictionary between them is inversion, the anti-automorphism
$`g \mapsto g^{-1}`$, i.e. the group isomorphism $`G^{\mathrm{op}} \cong G`$. In particular

$$\pi'(\gamma) = \mathrm{slash}(\gamma^{-1})$$

is a genuine **left** action of the same group on the same functions
($`\mathrm{slash}((\gamma\delta)^{-1}) = \mathrm{slash}(\gamma^{-1}) \circ \mathrm{slash}(\delta^{-1})`$),
so the calculus of §2 applies to it verbatim — with no opposite group anywhere. Its index
`G ⧸ K` is the right-coset space, whose representatives are the inverses of a left-coset
transversal, and its level space is again the set of functions fixed by every $`k \in K`$ under
slash, since $`k`$ and $`k^{-1}`$ range over the same subgroup.

Two things move and one thing does not. What moves: the family's representatives arrive inverted
($`r_i^{-1}`$ where the classical proof has $`r_i`$), and the double-coset label arrives inverted
— the indicator's support is $`K g^{-1} K`$, since $`(KgK)^{-1} = Kg^{-1}K`$ — so the wrapper
passes $`g^{-1}`$ as the double-coset label. The two inversions cancel, so the operator computed
is the same one as in §4.1. What does not move: the *coset conditions*. Distinctness of the
classes of $`r_i^{-1}`$ modulo $`K`$ is distinctness of the left cosets $`K r_i`$ of the family's
own representatives, and exhaustion is the same statement; both are plain `G`-language. So the
choice of side is a convention in the strong sense — either side is available, and the one that
removes `MulOpposite` from the statements costs a $`(-)^{-1}`$ on the data, not a different
theorem.

It is worth being precise about what *is* arbitrary and what is not, because the two are easy to
confuse. The classical literature uses both conventions (some texts sum over a left transversal of
$`\Gamma g \Gamma`$, others over a right one, with the index normalisation attached accordingly);
the two sums are genuinely different operators in general, being the two normalisations of the
same double-coset operator, and the conventions are exchanged by $`g \mapsto g^{-1}`$. So nothing
forces a side *a priori* — that is the arbitrariness — but once the pin's formulas fix
`heckeU`, `heckeT` and the q-expansions, the side is fixed for the port too, and a carrier on the
other side would be computing a different operator. The freedom is real but it has to be spent
consistently.

**This is the implemented choice.** `HeckeCoset.slashRep` is $`\gamma \mapsto \mathrm{slash}(\gamma^{-1})`$
on `GL(2,ℝ)⁺`, with `MulOpposite` nowhere in the module, and the family-facing `HeckeCoset.Transversal`
is stated in `GL (Fin 2) ℝ` — the group the families' matrices live in — so the positivity of the
determinants is confined to the operator identity that lifts them.

### 4.3 What the adapter costs, measured per family

A family's input to `CosetTransversal` is three statements, and their price is not the same:

* **membership** — the representatives lie in $`K g K`$. Usually visible from the definitions:
  $`\mathrm{heckeMatrix}\, p\, j = \alpha v_j`$ with $`v_j`$ the unipotent upper-triangular
  representative, and likewise $`\beta c = \alpha c^{-1}`$, $`\alpha\, \mathrm{rr}(i)`$;
* **distinctness** — distinct left cosets. This reduces to the **stabiliser identity**
  $`\Gamma \sqcap \alpha^{-1}\Gamma\alpha = \Gamma \sqcap \{q \mid b\}`$ — the (0,1) entry of
  $`\alpha x \alpha^{-1}`$ is $`b/q`$, so $`\alpha x \alpha^{-1} \in \Gamma`$ costs exactly
  $`q \mid b`$. In every one of the five families that stabiliser is the (0,1)-level subgroup,
  i.e. exactly the port's `Gamma0Upper`/`GammaHUpper`, which is the subgroup whose cosets the
  family *already* indexes by (`Fin q`, `ZMod p`, `OnePoint (ZMod p)`, `Option (Fin ℓ)`,
  `Γ₁(N) ⧸ Lam` with `Lam = Γ₁ ⊓ Gamma0Upper`). Consequences: for `Γ_H` distinctness is
  immediate, because the index subgroup and the stabiliser are the same subgroup; and for `Γ₀` it
  is a one-line entry computation (the (0,1) entry of $`v_j v_{j'}^{-1}`$ is $`j - j'`$, and
  $`q \mid j - j'`$ iff the classes agree);
* **exhaustion** — every element of $`K g K`$ is left-`K`-equivalent to a representative. This is
  the only real work: it is the solvability of a linear congruence, with the Weyl/`∞`
  representative covering the degenerate case. For $`K = \Gamma_0(N)`$, $`\alpha = \mathrm{diag}(1,p)`$:
  one must solve $`a j \equiv b \pmod p`$, so at $`p \mid N`$ the congruence is always solvable
  (because $`c \equiv 0 \pmod p`$ forces $`ad \equiv 1`$, hence $`p \nmid a`$); at $`p \nmid N`$
  the proof branches on whether $`a`$ is invertible mod $`p`$, and the `∞` representative takes
  over when it is not — the shape of `exists_rr_mul_mem`, which the port already has in
  `Analytic/PeterssonHecke.lean:232`, next to its distinctness twin `rr_mul_rr_inv_mem` (`:290`)
  and `rr_mem` (`:225`). Those three lemmas are this data for one family, written before the
  adapter existed.

So a family's new obligation is **~20–30 lines**, not the ~100 that the two Petersson lemmas and
their surrounding machinery suggest when read as a block. On top of that there is a one-time
**carrier bridge** of ~30 lines: the level subgroup re-declared in `GLPos` (membership is
$`\det = 1`$), the representatives lifted ($`\det = p`$ via `val_heckeMatrix`), and the
`slash_coe` rewrites. No such bridge exists in the port yet: outside `HeckeCosetSum.lean`,
`Matrix.GLPos` occurs only in docstrings about mathlib's `IsGLPos` scalar action.

### 4.4 Why rebuilding the abstract theory does not help

1. **There is no anti-action in the theory to remove.** `DoubleCosetHecke` is stated for an
   arbitrary group and an arbitrary `Representation A G W`; it has zero occurrences of
   `MulOpposite` or `.op` (measured, §7). The opposite group is a choice made by the *carrier*
   when it instantiates `G`. Rebuilding the theory would re-derive statements that never mentioned
   the problem.
2. **Any restatement still picks a side, and the sides are isomorphic.** By §4.2 the alternative
   is $`g \mapsto g^{-1}`$: the rebuilt theory would read `x⁻¹` where the current one reads
   `op x`. That is a change of variable, not a simplification — the same lemmas, the same
   hypotheses, the same proof obligations.
3. **It does not touch the actual cost.** §4.3 locates the work in the *concrete* double coset:
   membership, distinctness, exhaustion. Those are statements about a specific $`\alpha`$ and
   $`K`$; no choice of representation convention moves them by a single line.
4. **It forks proven code.** 317 lines re-proved against the same mathlib, losing the external
   check that the GRH development proves the same statements, the `#print axioms` record, and the
   single point where a mathlib rename has to be absorbed. It would also leave the port with two
   calculi, or force the archived comparison set to be re-pointed.
5. **The stated goal — no adapter in the statements — is cheaper by another route.** It is 20
   lines in the carrier (§4.2, Option B), not 400. If the objection is to reading `op` in a
   family's proof, the fix is the carrier's convention plus one constructor in `G`-language; the
   calculus is not implicated.

The same argument disposes of a weaker variant: "keep the calculus but state its family-facing
adapter in `G`-language". That is not a rebuild at all, it is a constructor (Option A's first
step), and it works because the *hypotheses* of `heckeFun_eq_sum`/`heckeFun_eq_sum_pullback` are
already `G`-language ($`\theta : G' \to G`$, $`(\theta a)^{-1}\theta b \in K \iff a^{-1}b \in J`$);
only the instantiation at `G = GLPosᵐᵒᵖ` needs the `op`.

## 5. The three options

All three assume the same non-negotiables: the pin's definitions stay concrete (`heckeU_def`,
`heckeT`, `heckeRep`, `beta`, `redMatrix`), no tree build, and no edit to the checker's statements
in this phase. They differ in *where* the family-facing interface lives.

### Option A — finish the adapter

*State: next. The object is landed (`HeckeCoset.Transversal`); what is left is one transversal per
family and the operator identity in the module.*

**What.** Three steps, in order. (1) A one-time boundary layer: a `CosetTransversal` constructor
taking the three conditions in `G`-language — $`r_i \in K g K`$; $`r_i r_j^{-1} \in K \Rightarrow i = j`$;
$`x \in K g K \Rightarrow \exists i,\ x\, r_i^{-1} \in K`$ — and deriving the `op`-form fields
internally; a `slashCosetOperator k K g` name so the headline never spells
`heckeCoset (slashRep k) K.op (op g)`; the `GLPos`/level bridge; and the deletion in §2 (use
`HeckePair.doubleCoset_mul_mem` instead of `mem_doubleCoset_mul_*`). (2) Per family, the
transversal of §4.3. (3) Retarget the headlines: invariance via
`IsHeckeFunction.heckeFun_mem`, the operator identity via `sum_slash_eq_heckeCoset`.

**Buys.** One place for representative-independence; the identity "the double-coset operator is the
sum over any transversal" as a theorem, so that the concrete sum stops being the only definition of
`T`; and the two things the port does not have at all — composition (`heckeFun_heckeFun`,
replacing the q-coefficient comparison in `HeckeCommute.lean`) and level transport
(`heckeFun_comp`, `heckeFun_comp_inv_mul`).

**Costs.** §4.3: ~30 lines one-time, ~20–30 per family. **Risks.** The invariance headline does
not need exhaustion (§4.1: it needs only the cocycle relation and level-invariance), so a family
whose exhaustion fights would hold hostage a statement that never used it. Mitigation: land the
invariance separately (Option C), the operator identity second.

### Option B — re-base the carrier on the equivalent left action

*State: landed. `slashRep` is the inverse action; no `MulOpposite` in the live tree.*

**What.** Keep `DoubleCosetHecke` untouched; change `HeckeSlashRep` to

```lean
def slashRep' (k : ℤ) : Representation ℂ (Matrix.GLPos (Fin 2) ℝ) (ℍ → ℂ)
```

with $`\gamma \mapsto \mathrm{slash}(\gamma^{-1})`$ (the `map_mul'` field is
$`\mathrm{slash}`$'s anti-multiplicativity read backwards), `mem_levelSpace_slashRep'` unchanged
in content, and — this is the point — no `MulOpposite` in any statement: `K` instead of `K.op`,
`doubleCoset g K K` in `G`, `r : ι → GLPos` instead of `op ∘ r`, and the wrapper
`heckeCoset (slashRep' k) K (g⁻¹)`.

**Buys.** The whole adapter surface of the statements disappears: a family's obligations are
$`r_i r_j^{-1} \in K`$-type conditions, and the two indicator lemmas of §2 are simply not needed.
Measured, the file gets shorter: ~50 lines of `op` plumbing go, ~15 lines of inverted-index
bookkeeping arrive.

**Costs.** A $`(-)^{-1}`$ on the double-coset label and on the representatives, which a reader can
mistake for a different operator unless the docstring says that the representation is of the
inverse action; and it churns a landed, green module for a presentational gain, so it should be
done once, together with the first family that consumes it, not before.

**Risks.** Low mathematically — but the inverse-action form is *not* the textbook form, and "the
operator of the double coset of $`g^{-1}`$" is exactly the sort of off-by-inversion that a reader
must be able to check. The counterweight is that a $`\sigma`$-semilinear slash on the *whole* of
`GL (Fin 2) ℝ` would need a σ-twisted calculus, which is a different order; `GLPos` is forced
either way.

### Option C — split the family-facing API by the strength each headline needs

*State: landed, and it is now the module's core: `Transversal.slash_invariant` needs no carrier at
all, and the three geometric fields are the whole family-facing interface for invariance.*

**What.** One lemma in the classical layer, in `G`, with no carrier at all:

```lean
theorem sum_slash_invariant {ι : Type} [Fintype ι] {r : ι → GL (Fin 2) ℝ}
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ K) (σ : Equiv.Perm ι) (κ : ι → K)
    (h : ∀ i, r i * γ = (κ i : GL (Fin 2) ℝ) * r (σ i))
    {F : ℍ → ℂ} (hF : ∀ γ ∈ K, F ∣[k] γ = F) :
    (∑ i, F ∣[k] r i) ∣[k] γ = ∑ i, F ∣[k] r i
```

Ten lines: `SlashAction.sum_slash`, `SlashAction.slash_mul`, the level-fixedness hypothesis, and
`Fintype.sum_bijective`. No `GLPos`, no `op`, no quotient, no double coset, no `levelSpace`, and
no linearity of the slash — the argument never leaves the function level.

**Buys.** The five invariance headlines in three lines each, and — the real value — it is exactly
the argument the five proofs already contain, so it makes the *input* the five families must
supply identical to their existing cocycle lemmas (`heckeMatrix_mul_of_dvd`, `heckeRep_mul`,
`mapGL_conjL_mul_heckeMatrix`, `exists_cocycle`, `stretchSlash`) with the permutation
(`affinePerm`, `MulAction.toPerm (redMatrix p g)`, `(g'⁻¹ • ·)`, `perm`). It is also a probe: if a
family cannot state its permutation and cocycle, its exhaustion will not be provable either.

**Costs.** A second entry point on the classical side, and it is the trivial-character form (the
character-twisted version needs the twist trivial on the cocycles — true for `Γ₁`/`Γ_H`, not free
in general); it does not give the operator identity or composition. **Risk.** Two abstraction
layers to explain; mitigated by positioning it as *the* invariance statement and the calculus as
*the* operator/composition statement, in one docstring each.

### 5.4 Recommendation, and where the work stands

The order is **C → B → A**, and two of the three are landed:

1. **C — done.** `Transversal.slash_invariant` (in `HeckeCosetSum.lean`) is the invariance statement
   the five families need, and it needs no carrier, no `GLPos`, no `op`, no quotient and no
   `levelSpace`. What a family supplies is the three geometric fields of `Transversal`.
2. **B — done.** The carrier is the inverse action `gamma ↦ slash(gamma⁻¹)` on `GL(2,ℝ)⁺`
   (`HeckeCoset.slashRep`), so no `MulOpposite` survives in the live tree; the level-space dictionary
   `mem_levelSpace_slashRep` is stated for a subgroup of `GL(2,ℝ)⁺`, and the family-facing object is
   in `GL (Fin 2) ℝ`.
3. **A — under way.**
   * `Transversal.sum_eq_doubleCosetOperator` — **landed.** The last piece the archived carrier held
     is now re-proved against the new object.
   * The `Γ_H` family — **landed, both halves** (§5.6): `heckeUTransversal` over `ZMod q` and
     `heckeTTTransversal` over `ℙ¹(ℤ/ℓ)`, with the pin's `beta` family and both sums identified by
     `sum_eq_sum`.
   * The remaining families, one `Transversal` each, then the headline in one line. `Γ₀` next:
     `mem` is definitional (`beta c = g * (c.out)⁻¹`), `distinct` is the stabiliser identity
     $`\Gamma_H \sqcap \alpha^{-1}\Gamma_H\alpha = \Gamma_HUpper`$, `cover` is the congruence
     $`a j \equiv b \pmod q`$ — and `conjUpperMat` (`Defs/CohCarrierLevel.lean:126`) already
     builds the `SL(2,ℤ)` witness `!![A 0 0, A 0 1 / ℓ; A 1 0 * ℓ, A 1 1]` for the conjugate, so
     the two directions of the stabiliser lemma are one matrix-entry computation each.
   * Then the families where composition and level transport pay (`T_p` at good level, then the
     Γ₁/level-change pair, which want `heckeFun_comp_inv_mul`/`heckeFun_comp`).

A genuine rebuild of the calculus is not on the list (§4.4). Keep the definitions concrete: the
calculus identifies the operator only on the level space (that is what `heckeFun_eq_sum`'s
$`v \in \mathrm{levelSpace}`$ buys), so `heckeU_eq_sum_zmod` and `heckeT_eq_sum_onePoint` — which
hold for an arbitrary function — cannot be replaced and must stay. Do not touch `HeckeCommute` or
the checker's statements in this phase.

**The first family attempt, and what it taught (2026-11-17, reverted).** `U_p` at `p ∣ M` was
attempted as a `Transversal` of `{!![1, x; 0, p] : x ∈ ZMod p}`: the stabiliser lemma, the shear
`heckeMatrix p j = heckeMatrix p 0 * T^j`, `det_pos_of_mem_Gamma0`, and the three fields — about
185 lines. The three fields *state* cleanly but their proofs are dominated by coercion plumbing
(`mapGL_coe_matrix` has `↑(SL.map f g)` on the right, so `coe_T_zpow` does not fire; `(b * d⁻¹).val`
elaborates as `↑↑(…)`, so the `ZMod` cast lemmas miss). The lesson was not "the plumbing is hard"
but "the formulation was wrong": the three fields were being proved for a *chosen* coset system
instead of being derived from the level pair.

### 5.5 The redesign: families are level quotients

The failure above has a clean fix, and it is now in the module:
**`Transversal.ofLevel`** (the constructor the earlier text called `ofQuotient`; it now takes the
family's *own* index and level pair). For any group `G`, any `K ≤ G`, any `g : G`, any finite index
`ι` and any `u : ι → ↥K` with `∀ a : ↥K, ∃! i, a * (u i)⁻¹ ∈ stabiliser K g`, the family
`r i = g * u i` is a `Transversal K g`. The three fields are three lines each and hold for *every*
family at once:

* `mem`: `1 * g * u i` lies in `K g K` by construction;
* `distinct`: `u i * (u j)⁻¹ ∈ K ⊓ g⁻¹Kg` is *the same coset*, and the `∃!` hypothesis makes `i = j`;
* `cover`: every `z = a g b` is `a * (g * (b (u i)⁻¹) * g⁻¹) * (g * u i)` with `b (u i)⁻¹` in the
  stabiliser, which is the `∃!` hypothesis again.

Two instantiations cover the port's families: the theory's quotient with `u c = c.out⁻¹` (then
`r c = g * c.out⁻¹`, the `Γ_H` `beta` family and the archived `ofQuotient`) and the family's own
matrices with `u x = transl x` (then `r x = !![1,x;0,q]`, i.e. `heckeU`'s own summands).

So **a family no longer proves membership, distinctness or exhaustiveness at all.** What is left
per family is exactly the two statements that carry the mathematics of that family:

| what | how it is stated | size |
|---|---|---|
| the level subgroup | a **subgroup identity** `K ⊓ g⁻¹Kg = <the port's subgroup>` | 2–3 lines (the (0,1) entry of `α x α⁻¹` is `b/q`) |
| the index (`Γ₀`, `Γ₁`) | the `∃!` hypothesis: every `a ∈ K` is `s * u i` for exactly one `i` (for `Γ₀`: `u x = T^x`) | ~15 lines: uniqueness = the subgroup identity applied to `x - y`, existence = solve `a j ≡ b (mod p)` |
| the operator | `Transversal.ofLevel u hu` | 1 line |
| the invariance | `T.slash_invariant hγ hF` | 1 line |
| the operator identity | `T.sum_eq_doubleCosetOperator hF hK hg` | 1 line |

For `Γ_H` the index *is* already the quotient (`bijective_transl : Fin q ≃ Γ_H ⧸ Γ_HUpper`), so the
family needs only the subgroup identity — and that identity is the two-line computation the old
`sum_slash_beta_slash_eq` spent 47 lines approximating. For the diagonal level change the index is a
singleton and `stabiliser K g = K`: nothing to prove.

**`Γ_H` is landed, and it validates the theory** (2026-11-17). The family's level pair is
`K = Γ_H(M)`'s image in `GL(2,ℝ)` and `g = !![1, 0; 0, q]`. The module now has

- `levelGroup`, `levelEquiv` (+`coe_levelEquiv`) — the image of `Γ_H(M)` in `GL(2,ℝ)` and its
  isomorphism to `Γ_H(M)`;
- `dvd_of_conj_mem` + `stabiliser_eq` — the level-pair identity `K ⊓ g⁻¹Kg = Γ_HUpper(M,H,q)`,
  i.e. the (0,1)-entry computation `b/q`, and it needs **no** `q ∣ M`;
- `conj_mem_of_mem_GammaHUpper` — conjugating a level element stays in the level group;
- **`betaTransversal`** — the family's `Transversal`, over **its own** index `Γ_H ⧸ Γ_HUpper`, now
  the generic `Transversal.ofLevel` on the level pair (`stabiliser_eq`): the three geometric fields
  are not proved per family (§5.6);
- `sum_slash_beta_slash_eq` — `(betaTransversal …).slash_invariant hγ hf`, **47 lines → 2**, and
  its statement (the pin) is unchanged;
- `sum_slash_beta_eq_doubleCosetOperator` — **new**: `…sum_eq_doubleCosetOperator …`, two lines. The
  concrete coset sum *is* the abstract operator, which is the semantics check the earlier slices
  could not provide.

Measured: `HeckeCosetDecomposition` **+172/−40**; `HeckeInvariance` and `HeckeOperatorForms` build
without proof changes; `#print axioms` clean on both headlines and on `betaTransversal`.

**The API change made, and the one not made.** The change is: *every family exposes a `Transversal`
over its own index*, and the theory's theorems are then one-liners. The level-quotient
identification lives inside the object (`stabiliser_eq`, used in `distinct`), not in the family's
theorems — which is what "design around the theory" means here, because the family's index is the
one its concrete coset sum uses (`ZMod p`, `Fin q`, `OnePoint`, `Option (Fin ℓ)`), the index the
q-expansion layer needs.

The other candidate — retyping `beta` to the *theory's* quotient `K ⧸ (K ⊓ g⁻¹Kg)` — was measured
and rejected for now: it forces reworking the two concrete-sum identities
(`sum_slash_beta_eq_heckeU`; `…_add`, 83 lines) because their `out`-manipulations happen in the `SL`
quotient, and it would deregister the pinned statements of `HeckeCosetDecomposition`. It buys
nothing that `betaTransversal` does not already give, unless one wants the concrete sums themselves
indexed by the `GL` quotient. Reversible if so. (The `q ∣ M` half of the first identity has since
been re-proved by representative-independence, §5.6, so of the two only `…_add` still carries the
reindexing.)

**What that changes downstream.** The `_mapGL` lemmas (`heckeU_slash_mapGL`, `heckeT_slash_mapGL`)
are stated with `g : SL(2,ℤ)` and `mapGL ℝ g`, which is where the coercion plumbing comes from — and
they are *not* the pinned API: the pinned headlines (`HeckeInvariance`'s five) are already stated at
`γ : GL (Fin 2) ℝ`, `γ ∈ K`, and only reach the `_mapGL` form through `obtain ⟨g, hg, rfl⟩`. So the
retarget restates the family lemmas at `γ ∈ K`, and:

* `HeckeInvariance` loses the `obtain ⟨g, hg, rfl⟩` and all `mapGL` rewriting: each headline becomes
  `rw [concrete_sum]; exact (XTransversal).slash_invariant hγ hf`, i.e. two lines;
* the `_div` headline's inlined 12-line copy of the Γ₀ reindexing disappears the same way (one
  GL-level lemma instantiated at `M = N / p`);
* `heckeMatrix_mul_of_dvd` (37 lines) loses its only live consumer and dies;
* `heckeRep_mul`'s cocycle half stops being needed for invariance (it survives for
  `PhiGenDescends`/`Gamma1HeckeOperators`), and `HeckeCosetDecomposition`'s `sum_slash_beta_slash_eq`
  becomes one application of `slash_invariant`;
* nothing changes for `HeckeOperatorForms`/`HeckeStability`: the pinned statements are untouched.

The two statements that *cannot* be discharged by `ofLevel` are the subgroup identity and (for
`Γ₀`/`Γ₁`) the index bijection. Those are the irreducible mathematics of each family, and they are
the same computations the port already performs inside the old invariance proofs — so the retarget
moves them rather than inventing them.

**What can be changed, given that the API is not sacred.** (i) The `_mapGL` lemmas: replace by
GL-level ones (no pin). (ii) `heckeU`'s index: the concrete sum is over `ZMod p` only because
`heckeU_def` and `qCoeff_heckeU` are; if a caller does not need q-expansions it should be given
`doubleCosetOperator` instead of the sum, and the index bijection is then needed only where the
q-expansion bridge is. (iii) The level groups: the port carries `CongruenceSubgroup.Gamma0 N` both
as a subgroup of `SL(2,ℤ)` and as its image in `GL (Fin 2) ℝ`; `ofLevel` wants the `GL` one, so
the `mapGL`-image form should be the primary spelling and the `SL` form derived.

**What the consolidation cost, measured.** The live classical layer is 311 lines: one object
(`Transversal`), its two theorems, the bridging lemmas, and the carrier (the `SlashAction` instance, `slash_coe`,
`slashLin`, `slashRep`, `slashRep_apply`, `mem_levelSpace_slashRep`). It replaces a
231-line module whose object (`CosetTransversal`) was stated in `Gᵐᵒᵖ` and whose invariance theorem
went through `levelSpace`. The invariance theorem is *shorter* (10 lines of argument), the
family-facing statements lost `op`, `K.op`, `doubleCoset (op g) K.op K.op` and the positivity
hypotheses, and the module gained the operator identity, which the archived file was the only
holder of. Its first consumer is now retargeted (§5.6).

## 5.6 The retarget of `Γ_H`, landed: both halves, one module (2026-11-26)

**What the consumer actually needs.** `PeriodMapHecke` proves
`periodMapOf (U_q f) = heckeT (periodMapOf f)` in three steps: the primitive
`Φ z = ∑_c F (β_c • z)` is `Γ_H`-equivariant with period `heckeT (periodHom F)`; its derivative is
the Hecke operator applied to `f`; and `periodMapOf_def` reads the period map off the primitive. The
middle step is analysis and the last is bookkeeping. The first step is the only one the coset
calculus owns, and the old proof computed it from scratch — reindex the coset sum by `γ • ·`, rewrite
each summand against the cocycle (`hbeta`), apply the period hom (`hcob`).

**The mathematics is two statements, and they are independent.**

1. `HeckeCoset.sum_sub_eq_cocycle` (in `HeckeCosetSum`): if `F` is equivariant along a monoid
   homomorphism `m : H →* GL(2,ℝ)` with period `φ`, and the representatives carry a permutation `σ`
   of the index set and a cocycle `κ : ι → H` with `r (σ i) * x = m (κ i) * r i`, then
   `∑ i, F (r i • x • z) - ∑ i, F (r i • z) = ∑ i, φ (κ i)`. It is the period-level counterpart of
   `slash_invariant`, and takes `σ`/`κ` as an input: the consumer reads them off its own model of the
   double coset.
2. `Γ_H`'s cocycle *is* the transfer's: `β (γ • d) * γ = conjL (transferAux γ d) * β d` is
   `transferAux`'s definition rearranged, with `conjL t * g = g * t`
   (`mapGL_conjL_mul_heckeMatrix`). So the sum is `heckeT φ γ` by `heckeT_apply_eq_sum`, and the
   consumer's period step is that theorem applied to `Φ`; the reindexing and the per-summand period
   argument disappear into `sum_sub_eq_cocycle`, and what stays is `hcoc`, the group identity.

**The family, in one module.** `HeckeCosetGammaH` states the two cosets systems the operators are
*defined* by, both as `Transversal.ofLevel` on the level pair `stabiliser_eq`:

* `q ∣ M`: the `q` matrices `!![1,x;0,q]` are `g · T^x`, and `T^x` runs over a transversal of
  `Γ_HUpper` exactly when `q ∣ M` (`transl_transversal_stab`, the linear congruence
  `a 1 1 · x ≡ a 0 1`). The transversal is `heckeUTransversal`, and its sum is `U_q`'s definition.
* `ℓ ∤ M`: the cosets are the projective line `ℙ¹(ℤ/ℓ)`. The point `x` is `!![1,x;0,ℓ]` and `∞` is
  `ρ_∞ · diag ℓ`, with `ρ_∞ = !![u,v;-M,ℓ]` the Bézout matrix of `uℓ + vM = 1`. The count is the
  complementary pair of congruences `a 0 1 ≡ x · a 0 0 (mod ℓ)` (unique `x` iff `a 0 0` is a unit)
  and `a 0 0 ≡ 0` (`∞`), which is `onePoint_eq`; the transversal is `heckeTTTransversal`, and its sum
  is the pin's `U_ℓ + (·) ∣ (ρ · diag ℓ)` (`heckeU_add_slash_eq_sum`). The one place the *pin's*
  `ρ` enters is the identification of the `∞` summand: `ρ · diag ℓ` and `ρ_∞ · diag ℓ` differ by
  `ρ ρ_∞⁻¹`, which is in `Γ_H` because `ρ 1 1 ≡ ℓ ≡ ρ_∞ 1 1 (mod M)`
  (`mul_rhoInf_inv_mem_GammaH`), so `f`'s `Γ_H`-invariance passes between them.

The pin's own index `Γ_H(M) ⧸ Γ_HUpper(M,H,q)` with representative `beta c = g · (c.out)⁻¹` is
`betaTransversal`, and both sums are identified with the concretely indexed ones by
`Transversal.sum_eq_sum`: **the index bijection is representative-independence**, so no sum is
reindexed term by term (`sum_beta_eq_heckeU` was 37 lines and is now a three-step `calc`;
`sum_beta_eq_heckeU_add` was 83 lines plus `bijective_option`'s 80 and is now the same three steps).
`bijective_transl`, `exists_add_neg_eq_mul`, `heckeMatrix_zero_mul_mapGL_T_zpow_neg`, `bijective_option`
and the Bézout `out`-map computations are gone.

**What is gone, and how the pin is held.** `HeckeCosetDecomposition` is deleted; its pin source
`P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean` is carried by a header-only file in
`Reserve/ModularForms/`, which keeps the source marked *ported* for `frontier.py` while declaring
nothing (the mechanism of `Reserve/ModularForms/PortOwnedSpecPins.lean`). The pin's formulas are
stated in `HeckeCosetGammaH` under the family's names (`sum_beta_eq_heckeU`,
`sum_beta_eq_heckeU_add`, `sum_beta_slash_eq`, `sum_beta_eq_doubleCosetOperator`); the consumers'
own pinned statements are untouched and still diffed (`HeckeInvariance` 5 ok, `PeriodMapHecke` 4 ok,
0 missing).

Measured (against the commit before the retarget): `HeckeCosetDecomposition` 674 → 0,
`HeckeCosetGammaH` 327 → 827 (both halves, the pin surface and the consumer-facing bridges),
`HeckeCosetSum` 387 → 427, `HeckeInvariance` 155 (unchanged net), `PeriodMapHecke` 488 → 482. So the
subject is one module of 827 lines instead of 674 + 327 duplicated, with no `variable` block whose
instances need `omit` (the section variables are the ones each lemma uses), and the `ℓ ∤ M` half is
a projective-line count plus the pin's `ρ` leg, not a quotient computation. What it is *not* is a
smaller proof than the pin's: the two counts (`ZMod q`, `ℙ¹`) are the mathematics and are about the
same length as before. What changed is that they are stated once, as transversals, and that every
*sum* identification is `sum_eq_sum`.
`#print axioms` on `sum_sub_eq_cocycle`, `sum_beta_eq_heckeU`, `sum_beta_eq_heckeU_add`,
`heckeU_add_slash_eq_sum` and both `Γ_H` headlines of `PeriodMapHecke`:
`[propext, Classical.choice, Quot.sound]`. No tree build.

## 6. Stage C: the retarget, family by family

The `Γ_H` row is retired: both halves are retargeted, both consumers are re-proved, and the old
module is deleted (§5.6). The remaining four rows are untouched, and each is one `Transversal` plus
`Transversal.sum_eq_sum`, as `Γ_H` was. The `Γ_H` row is kept in the table as the template.

The calculus pays out on the reindexing half of five classical files; the coset *count* stays,
because that is the mathematics:

| family | current home | what the calculus replaces | what must stay |
|---|---|---|---|
| Γ₀ `U_p` | `Defs/HeckeRepresentatives` (`heckeU_eq_sum_zmod`, `heckeMatrix_mul_of_dvd`, `heckeU_slash_mapGL`) | the sum-invariance reindexing in `heckeU_slash_mapGL` | the coset action and the count |
| Γ₀ `T_p` | same (`heckeT_eq_sum_onePoint`, `heckeRep_mul`, `redMatrix`, `heckeT_slash_mapGL`) | the reindexing in `heckeT_slash_mapGL` | `redMatrix`/`dvd_conjugate`, the count |
| Γ_H `U_q`, `ℓ ∤ M` | `HeckeCosetGammaH` (`beta` + both transversals + the pin's sums) — **retargeted**, §5.6; the old `HeckeCosetDecomposition` is deleted | every reindexing: both sums are `sum_eq_sum` | the level pair `stabiliser_eq`, the two counts (`ZMod q` congruence, `ℙ¹` pair of congruences) and the pin's `ρ` leg |
| Γ₁ `U_ℓ` | `HeckeULevel` (`exists_cocycle`, `heckeMatrix_mul_eq`, `perm`, `heckeU_slash_eq_smul`) | the sum-invariance half, via `heckeFun_comp_inv_mul` | the cocycle construction |
| diagonal level change | `HeckeDiagDegeneracy` (`exists_cocycle`, `heckeDiagMatrix_mul_eq`, `stretchSlash`) | the transport, via `heckeFun_comp` | the stretch map and its level bookkeeping |

**The obstruction, stated once.** To identify a concrete sum
$`\sum_{j \in \mathrm{Finset.range}\, p} f \mid_k \mathrm{heckeMatrix}\, p\, j`$ with
`DoubleCosetHecke.heckeCoset`, one must supply §4.3's three conditions. The port never states
them: they are implicit in the `Finset.sum_congr` + `Equiv.sum_comp` reindexing inside each
invariance proof. **Each family therefore needs one new lemma before anything can be retired** —
and, per §4.3, that lemma is cheap because its distinctness half *is* the subgroup the family
already indexes by, and its exhaustion half is the congruence the family's coset action already
solves.

The family that was done first is `Γ_H`: its representatives are
$`\beta c = \alpha c^{-1}`$ over $`c \in \Gamma_H(M) \bmod \Gamma_HUpper(M,H,q)`$, the stabiliser
is $`\Gamma_H \sqcap \alpha^{-1}\Gamma_H\alpha = \Gamma_HUpper`$ (a two-line matrix computation, the
(0,1) entry of $`\alpha x \alpha^{-1}`$ is $`b/q`$), so distinctness is the statement that the
family's index subgroup *is* the stabiliser, exhaustion is unpacking
$`\Gamma_H \alpha \Gamma_H`$, and `bijective_transl` / `bijective_option` already give the index
bijection. Its invariance proof
(`sum_slash_beta_slash_eq`, 45 lines) was the smallest complete retirement unit, and both halves
have since landed. The Γ₀ families
need the exhaustion lemma first; their distinctness is the one-line entry computation of §4.3.

**Retirement mechanics.** Once a family's headline is re-proved through the calculus and its
consumers compile unchanged, the superseded private helpers go to `Reserve/` with
`tools/deps/move_dead.py --copy` (the shelf imports only the port's public API), and the public
declarations the pin's checker holds stay in place until the whole family is retargeted — a
half-moved family is worse than a duplicated one. Overlap between the shelf and the live module is
expected and accepted. The pin statements themselves are not negotiable in this phase: the
consumers (`ModularCurve/Period/PeriodMapHecke`, `HeckeStability`, and `HeckeOperatorForms`, which
takes its `slash_action_eq'` fields from the invariance headlines) hold the interface.

**The shelf is taken, and it is organized by argument, not by file.** The eight modules of the
replacement set — `Defs/HeckeRepresentatives`, `Defs/Gamma1HeckeOperators`, `HeckeInvariance`,
`HeckeCosetDecomposition`, `HeckeULevel`, `HeckeDiagDegeneracy`, `HeckeFricke`,
`HeckeFrickeTrace`; 3,409 lines — are archived whole in `Reserve/HeckeCosetCalculus/`, all eight
building. Structures are not archived: the matrices, `heckeRep`/`redMatrix`/`wt`/`affinePerm`, the
level groups and `heckeU`/`heckeT` stay live and are imported, because they have consumers outside
the replacement set (`Gamma1CuspStructure` uses `affinePerm` and `heckeU_eq_sum_zmod`,
`PhiGenDescends` uses `redMatrix`/`heckeRep`/`wt`). The rule the shelf follows:

> archive the copy of an argument the archived proof **calls**; import live anything that
> **survives** the retarget.

So the invariance chain is self-contained (the archived `HeckeInvariance` imports the archived
`HeckeRepresentatives`, `HeckeFricke`, `HeckeCosetDecomposition`, because those arguments are
themselves replaced), while the Γ₁ pair imports live `HeckePrelude`/`HeckeQCoeff`/
`Gamma1Vanishing` and takes `affinePerm`, `heckeU_eq_sum_zmod` and the matrices from
`FLTForHuman`. No module reaches both copies of a name; if a live structure the Γ₁ pair leans on
is later retired, it is copied in then.

**Why nothing moved out of the live tree yet.** A retirement needs the replacement in place;
Stage B's core is a carrier, not a replacement. Moving anything today would leave a live consumer
(or the pin's statement check) pointing at a shelf. The correct handoff is §5.4's sequence and the
`Γ_H` family above; the shelf is the record to diff against when it lands.

## 7. Verification (as measured)

- `lake build FLTForHuman.RepTheory.DoubleCosetHecke` → 1,693 jobs, no warnings.
- `lake build FLTForHuman.ModularForms.HeckeCosetSum` → 2,323 jobs, no warnings, no `sorry`
  (311 lines: `Transversal`, `slash_invariant`, `sum_eq_doubleCosetOperator`, the carrier, and the
  four bridging lemmas `invPos`/`levelPos`/`mem_levelPos`, `doubleCoset_inv`,
  `indicator_doubleCoset_mul`, `mem_doubleCoset_levelPos_iff`; the generic level-pair transversal
  `Transversal.stabiliser`/`mem_stabiliser`/`ofLevel`).
- `lake build Reserve.HeckeCosetCalculus.ModularForms.HeckeSlashRep` → 2,321 jobs, no warnings
  (the archived first cut still builds).
- `#print axioms` on `heckeFun_eq_sum`, `heckeFun_heckeFun`, `heckeFun_mem_levelSpace`,
  `IsHeckeFunction.heckeFun_mem`, and on `Transversal.slash_invariant`,
  `Transversal.sum_eq_doubleCosetOperator`, `Transversal.ofLevel`, `slashRep`,
  `mem_levelSpace_slashRep`, `mem_doubleCoset_levelPos_iff`:
  `[propext, Classical.choice, Quot.sound]`.
- `grep -c 'MulOpposite\|\.op\b' RepTheory/DoubleCosetHecke.lean` → `0`: the calculus is
  group-agnostic (§4.4, item 1). `GLPos` occurs in the live tree only in `HeckeCosetSum.lean`
  (the carrier); no family-facing statement mentions it.
- `grep -c MulOpposite` over the live classical layer is `0`: the archived carrier is the only
  file that mentions the opposite group.
- **After the `Γ_H` retarget (2026-11-26):** `lake build` of
  `HeckeCosetSum`/`HeckeCosetGammaH`/`HeckeInvariance`/`PeriodMapHecke`/`HeckeOperatorForms`/
  `HeckeStability`, no warnings from those modules and no `sorry`; `spec/check_port.py` 4 ok on
  `PeriodMapHecke` and 5 ok on `HeckeInvariance`, 0 missing; `HeckeCosetDecomposition` is deleted,
  its pin source carried by `Reserve/ModularForms/HeckeCosetDecompositionDropped.lean`; the consumer
  module `PeriodMapHecke` imports `HeckeCosetGammaH` (which imports `HeckeCosetSum`), so the
  calculus is no longer unused.
- No `sorry`, no `maxHeartbeats` raise, no tree build.
- Neither module declares a `spec-pin:`: the source is not FLT, so there is no pin to diff
  against. They are tier 3 (public, unchecked) by construction; if a register wants them, they
  belong with the port's own statements, not with the checker's pin map.

## 8. Attribution

The source is Apache-2.0, Copyright 2026 Anthropic, PBC (`grh/NOTICE`,
`https://github.com/lsernau/grh-lean` at `72fead1`). Both new modules carry that notice in their
headers, as the `Reserve` shelves do for their pins. The source's own `ATTRIBUTION.md` records that
`New.levelSpace` adapts mathlib's `Representation.invariants`; the port's `levelSpace` is a
`Submodule` of the character-fixed points and does not use it.
