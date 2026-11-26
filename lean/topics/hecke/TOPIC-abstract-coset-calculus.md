# The abstract double-coset Hecke calculus (taken from the GRH proof)

**Status: Stage A landed, Stage B landed, Stage C not started (2026-11-17).**
`RepTheory/DoubleCosetHecke.lean` (the calculus, 317 lines) and `ModularForms/HeckeSlashRep.lean`
(the carrier, 231 lines) build on mathlib `v4.34.0`, `#print axioms` clean, no warnings, no
`sorry`. Stage B is complete as specified — `CosetTransversal` and its four statements are in the
file. Nothing consumes either module, nothing is retired, and the interface of the classical side
is still free: §5 prices the three ways forward and §4.4 says why rebuilding the calculus is not
one of them.

This version of the note corrects two claims of the earlier text. (i) The two adapter theorems
that the earlier §4 called "remaining" and "blocked" are landed (§2); what remains is per-family
data, and the friction the earlier §4 described was worked around rather than removed (§2, last
paragraph). (ii) The earlier note's price for a family's coset system was inflated by counting
unrelated machinery; the measured cost is in §4.3.

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

### Stage B — `FLTForHuman/ModularForms/HeckeSlashRep.lean` (green, complete)

* `ModularForm.SlashHecke` instance `SlashAction ℤ (GL(2,ℝ)⁺) (ℍ → ℂ)` (via
  `monoidHomSlashAction (Subgroup.subtype _)`), `slash_coe`, `slashLin`, `slashRep` and
  `slashRep_apply`: the weight-`k` slash action as a `Representation ℂ (GL(2,ℝ)⁺)ᵐᵒᵖ (ℍ → ℂ)`.
* `mem_levelSpace_slashRep`: `F ∈ levelSpace (slashRep k) K.op ↔ ∀ γ ∈ K, F ∣[k] γ = F`.
* The adapter proper, packaged as one object: **`CosetTransversal K g`** — a finite family of
  representatives of `K g K` whose right `K`-cosets (in `Gᵐᵒᵖ`, i.e. the left `K`-cosets of `G`,
  §4.1) are distinct and exhaust it. Its API is the four statements a level family needs, and it is
  the whole of a family's concrete input: `hasFiniteCosets` (the transversal is what makes the
  double coset finite modulo `K`), `sum_slash_eq_heckeCoset` (the concrete slash sum *is*
  `heckeCoset`), `sum_slash_eq_sum_slash` (two transversals give the same operator — the statement
  that replaces a bespoke `Finset.sum_congr`/`Equiv.sum_comp` reindexing), and `slash_invariant`
  (the operator keeps `K`-fixed functions `K`-fixed).
* The underlying lemmas it is built from: `mem_doubleCoset_mul_left`/`_right`,
  `indicator_doubleCoset_mul_left`/`_right`.

**Two findings that shaped the carrier** (both are mathematics, not Lean friction):

1. The slash action is an **anti**-action (`F ∣ (g*h) = (F ∣ g) ∣ h`), so the representation lives
   on `Gᵐᵒᵖ`. §4 is about what that costs and what it does not cost.
2. The slash action is **σ-semilinear**: `smul_slash` carries `σ g`, which is conjugation for
   `det g \lt 0`. It is `ℂ`-linear only on `GL(2,ℝ)⁺` — and that is where the Hecke operators live
   (`heckeMatrix`/`heckeDiagMatrix` have determinant `p \gt 0`, the congruence subgroups have
   determinant `1`). So the carrier is `GL(2,ℝ)⁺`, not `GL (Fin 2) ℝ`.

**One cleanup left in this file.** `mem_doubleCoset_mul_left`/`_right` (lines 90–146, with the two
indicator lemmas, ~55 lines) convert between the two witness shapes of mathlib's
`DoubleCoset.mem_doubleCoset`. The port already has this arithmetic in `G`, without the opposite
group: `HeckePair.mem_doubleCoset_iff` (`HeckePair.lean:446`, the triple-product form) and
`HeckePair.doubleCoset_mul_mem` (`:462`, `x ∈ U g U → u ∈ U → x * u ∈ U g U`), with
`HeckePair.doubleCoset g = (U : Set G) * {g} * U` definitionally mathlib's
`DoubleCoset.doubleCoset g U U`. The earlier §4 recommended exactly this replacement and it was
not applied; it is a deletion, not a rewrite, and should happen when the file is next touched.

### Stage C — not started

Nothing is retired. See §6 for why that is the correct state, not an omission.

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
`slash_coe` rewrites. `GLPos` currently appears *nowhere else* in the port, so this bridge does
not exist yet.

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

### Option A — finish the adapter as landed

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

### 5.4 Recommendation

Sequence **C → B → A**, with one correction to the earlier plan:

1. **C first.** ~10 lines, no new module, no bridge, and it re-proves the five invariance
   headlines (the largest readability win per line spent). It also measures, family by family,
   whether the cocycle+permutation data is available in the form the transversals will need.
2. **B with the first family** (Γ_H, per §4.3: membership is visible, distinctness is the
   coincidence of the index subgroup with the stabiliser, exhaustion is unpacking the double coset).
   Re-basing the carrier while a consumer exists is the only way to check that the $`(-)^{-1}`$
   convention is not error-prone; doing it later means churning a module twice.
3. **A family by family**, for the families where the operator identity and composition pay
   (`Γ_H`, then `T_p` at good level, then the Γ₁/level-change pair, which want
   `heckeFun_comp_inv_mul`/`heckeFun_comp`).

A genuine rebuild of the calculus is not on the list (§4.4). Keep the definitions concrete: the
calculus identifies the operator only on the level space (that is what `heckeFun_eq_sum`'s
$`v \in \mathrm{levelSpace}`$ buys), so `heckeU_eq_sum_zmod` and `heckeT_eq_sum_onePoint` — which
hold for an arbitrary function — cannot be replaced and must stay. Do not touch `HeckeCommute` or
the checker's statements in this phase.

## 6. Stage C: the retarget, and why nothing is retired yet

The calculus pays out on the reindexing half of five classical files; the coset *count* stays,
because that is the mathematics:

| family | current home | what the calculus replaces | what must stay |
|---|---|---|---|
| Γ₀ `U_p` | `Defs/HeckeRepresentatives` (`heckeU_eq_sum_zmod`, `heckeMatrix_mul_of_dvd`, `heckeU_slash_mapGL`) | the sum-invariance reindexing in `heckeU_slash_mapGL` | the coset action and the count |
| Γ₀ `T_p` | same (`heckeT_eq_sum_onePoint`, `heckeRep_mul`, `redMatrix`, `heckeT_slash_mapGL`) | the reindexing in `heckeT_slash_mapGL` | `redMatrix`/`dvd_conjugate`, the count |
| Γ_H `U_q` | `HeckeCosetDecomposition` (`beta`, `sum_slash_beta_eq_heckeU`, `sum_slash_beta_slash_eq`) | `sum_slash_beta_slash_eq` (the invariance, 45 lines) | `bijective_transl`, `bijective_option`, the Bezout model |
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

The family to start with is `Γ_H` (`HeckeCosetDecomposition`): its representatives are
$`\beta c = \alpha c^{-1}`$ over $`c \in \Gamma_H(M) \bmod \Gamma_HUpper(M,H,q)`$, the stabiliser
is $`\Gamma_H \sqcap \alpha^{-1}\Gamma_H\alpha = \Gamma_HUpper`$ (a two-line matrix computation, the
(0,1) entry of $`\alpha x \alpha^{-1}`$ is $`b/q`$), so distinctness is the statement that the
family's index subgroup *is* the stabiliser, exhaustion is unpacking
$`\Gamma_H \alpha \Gamma_H`$, and `bijective_transl` / `bijective_option` already give the index
bijection. Its invariance proof
(`sum_slash_beta_slash_eq`, 45 lines) is the smallest complete retirement unit. The Γ₀ families
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
- `lake build FLTForHuman.ModularForms.HeckeSlashRep` → 2,321 jobs, no warnings.
- `#print axioms` on `heckeFun_eq_sum`, `heckeFun_heckeFun`, `heckeFun_mem_levelSpace`,
  `IsHeckeFunction.heckeFun_mem`, `slashRep`, `mem_levelSpace_slashRep`:
  `[propext, Classical.choice, Quot.sound]`.
- `grep -c 'MulOpposite\|\.op\b' RepTheory/DoubleCosetHecke.lean` → `0`: the calculus is
  group-agnostic (§4.4, item 1). `grep -rn GLPos FLTForHuman` hits only `HeckeSlashRep.lean`
  (§4.3: the bridge does not exist).
- No consumer: neither module is imported anywhere in `FLTForHuman` (the `SlashHecke` hit in
  `ModularCurve/Period/HeckeStability.lean` is `ModularForms.CuspFormSlashHecke`, unrelated).
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
