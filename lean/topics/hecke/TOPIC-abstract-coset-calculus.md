# The abstract double-coset Hecke calculus (taken from the GRH proof)

**Status: Stage A landed, Stage B half landed, Stage C not started (2026-11-17).**
`RepTheory/DoubleCosetHecke.lean` (the calculus) and `ModularForms/HeckeSlashRep.lean` (the
carrier adapter) build on mathlib `v4.34.0`, `#print axioms` clean, no warnings. Nothing is
retired yet: the calculus has no classical consumer until the coset-system adapter of §4 is
finished, so there is no dead code to move to `Reserve/` — see §5.

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
| `classSum`, `classSum_eq_finsum_of_rep`, `card_classAut_mul_mul` | 132, 149, 136 | the weighted class sum over `Γ \ G / K`; not taken (§3.4) |
| `isLocallyConstant_of_eventually_mul` | 168 | right-invariance near `1` gives local constancy |
| `finite_quotient_image_of_isCompact`, `IsCompact.relIndex_ne_zero` | 178, 186 | a compact set meets finitely many `H`-cosets |
| `relIndex_mul_measure_inf`, `measure_inter_eq_inv_relIndex` | 194, 214 | `[K : H ⊓ K] · μ(H ⊓ K) = μ K` |
| `HasFiniteCosets K f`, `IsHeckeFunction K f` | 241, 244 | `f` lives on finitely many cosets; bi-invariant and finite |
| `heckeFun_eq_sum_toFinset`, `map_heckeFun` | 250, 258 | the finite sum over an explicit `Finset`; an intertwining `L` transports the operator |
| `levelSpace_anti` | 262 | `K ≤ K'` gives `levelSpace K' ≤ levelSpace K` |
| `isHeckeFunction_doubleCoset` | 267 | `1_{KgK}` is a Hecke function (`K` compact open) — not taken (§3.3) |
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

| source (v4.35) | v4.34 |
|---|---|
| `finsum_eq_sum_of_support_subset` | `finsum_eq_finsetSum_of_support_subset` (a `Finset` argument, not a `Set`) |
| `fun_smul_left`/`fun_smul_right` (in `heckeFun_heckeFun`'s proof) | `finsum_sum_comm`/`sum_finsum_comm` + `smul_finsum'` |

`heckeFun_heckeFun` is proved by taking both sides to the double sum
`∑ q ∈ s, ∑ᶠ p, (f' q · f (q⁻¹ p)) • π p • v`; the finiteness needed for the interchange is
`HasFiniteCosets.comp_inv_mul`. `rfl`-level detail: `smul_smul` in v4.34 is the iterated-action
lemma, the scalar-multiplication one is `mul_smul`.

### Stage B — `FLTForHuman/ModularForms/HeckeSlashRep.lean` (green, complete)

* `ModularForm.SlashHecke` instance `SlashAction ℤ (GL(2,ℝ)⁺) (ℍ → ℂ)` (via
  `monoidHomSlashAction (Subgroup.subtype _)`), `slash_coe`, `slashLin`, `slashRep` and
  `slashRep_apply`: the weight-`k` slash action as a `Representation ℂ (GL(2,ℝ)⁺)ᵐᵒᵖ (ℍ → ℂ)`.
* `mem_levelSpace_slashRep`: `F ∈ levelSpace (slashRep k) K.op ↔ ∀ γ ∈ K, F ∣[k] γ = F`.
* The adapter proper, packaged as one object: **`CosetTransversal K g`** — a finite family of
  representatives of `K g K` whose right `K`-cosets are distinct and exhaust it. Its API is the
  four statements a level family needs, and it is the whole of a family's concrete input:
  `hasFiniteCosets` (the transversal is what makes the double coset finite modulo `K`),
  `sum_slash_eq_heckeCoset` (the concrete slash sum *is* `heckeCoset`),
  `sum_slash_eq_sum_slash` (**two transversals give the same operator** — the statement that
  replaces a bespoke `Finset.sum_congr`/`Equiv.sum_comp` reindexing), and `slash_invariant`
  (the operator keeps `K`-fixed functions `K`-fixed).
  The underlying lemmas it is built from: `mem_doubleCoset_mul_left`/`_right`,
  `indicator_doubleCoset_mul_left`/`_right`.
* Why the object: refactor.md's first prescription for a proof-step API is to stop threading the
  context through the layers. A family used to pass `hpN`, `f`, `hf`, `g`, `hg` into a helper that
  proved a sum identity; now it constructs a `CosetTransversal` and applies one of the four
  statements. The `p`-coset bridge is the family's only remaining obligation.

**Two findings that shaped the carrier** (both are mathematics, not Lean friction):

1. The slash action is an **anti**-action (`f ∣ (g*h) = (f ∣ g) ∣ h`), so the representation
   lives on `Gᵐᵒᵖ`. Every coset/double-coset statement on the classical side therefore has to be
   transported to the opposite group; for a double coset the *sets* agree
   (`K.op · op g · K.op = op '' (K g K)`), but a right-coset transversal on `G` is a *left*-coset
   transversal on `Gᵐᵒᵖ`. §4 records this as the first thing a retarget must handle.
2. The slash action is **σ-semilinear**: `smul_slash` carries `σ g`, which is conjugation for
   `det g < 0`. It is `ℂ`-linear only on `GL(2,ℝ)⁺` — and that is where the Hecke operators live
   (`heckeMatrix`/`heckeDiagMatrix` have determinant `p > 0`, the congruence subgroups have
   determinant `1`). So the carrier is `GL(2,ℝ)⁺`, not `GL (Fin 2) ℝ`.

### Stage C — not started

Nothing is retired. See §5 for why that is the correct state, not an omission.

## 3. What stays out, and why

3.1 **Compact open → commensurable.** The source's `isHeckeFunction_doubleCoset` derives
finiteness from `K` compact open. Our `K` is discrete, so the hypothesis has to be finite right
index of `K ⊓ g K g⁻¹` in `K`. Not ported: no consumer needs it, because a concrete coset system
supplies finiteness through `heckeFun_eq_sum`'s covering hypothesis (Stage B's `sum_slash_*`,
§4). If it is ever wanted, the proof is the orbit-stabilizer bijection
`{k g K : k ∈ K} ≃ K ⧸ (K ⊓ g K g⁻¹)` plus `Subgroup.fintypeQuotientOfFiniteIndex`.

3.2 **The measure layer** (`relIndex_mul_measure_inf`, `measure_inter_eq_inv_relIndex`,
`isLocallyConstant_of_eventually_mul`): it is the adelic measure bookkeeping behind the
`1/#aut` weights. The port has the analytic counterparts in `AutomorphicForm/Adelic`.

3.3 **`classSum`/`classIntegral`/orbit unfolding/`compactMean`**: the trace-formula and averaging
layer. Two statements are worth remembering rather than porting: `smul_classSum_mem` (integrality
of a weighted class sum when every stabiliser order divides `M`) and `classSum_le_card_mul` (a
bound by the number of classes). Both are analogues of statements the port proves by coefficients
(`mem_intLattice_of_mem_heckeAlgebra`, the Sturm bound).

3.4 **Gelfand's trick** (`Lib/General/LinearAlgebra/IntegralLattices.lean:297–470`: `heckeFun_adjoint`,
`heckeFun_comm`) is out of scope for the classical retarget, for a mathematical reason: it rests
on Gelfand's condition $g^{\mathsf T} = (k^{\mathsf T})^{-1} g k$ with $k \in GL_n(O)$, $O$ a
valuation subring — a property of the pair $(G,K)$ that holds for the maximal compact of a local
field (a Smith-normal-form diagonal is transpose-invariant and $GL_n(O)$ contains the Weyl
element) and fails for $K = \Gamma_0(N)$, $N>1$ (the involution multiplies $\det$ by
$(\det g)^{-2}$, and the Weyl element is not in $\Gamma_0(N)$). That is exactly why the classical
adjoint of $T_p$ at $\Gamma_1(N)$ is $T_p$ only up to $\overline{\varepsilon(p)}$ — the diagonal
summand is the correction, see `Analytic/PeterssonHeckeTheorems`. If the adelic side wants a
measure-free Gelfand theorem, `HeckePair.conv` already is a `finsum` convolution and the port is
~50 lines; it would supersede the `IsHaarMeasure`/`map θ = ν` hypotheses of
`AntiInvolutionHaar.convKer_comm`. Separate order.

## 4. Stage B, the rest: the coset-system adapter

The two theorems that remain are the ones a retarget needs, and they are blocked on the
opposite-group transport of §2(B)(1), not on the calculus. The recipe:

| theorem | statement | proof |
|---|---|---|
| `sum_slash_eq_heckeCoset` | for `r : ι → GL(2,ℝ)⁺`, `g`, `K`: if `op (r i) ∈ K.op · op g · K.op`, the right `K.op`-cosets of the `r i` are distinct and exhaust it, and `F` is `K`-fixed, then `∑ i, F ∣[k] r i = heckeCoset (slashRep k) K.op (op g) F` | `heckeFun_eq_sum` with `f = indicator (K.op · op g · K.op) 1`; the indicator is right-`K.op`-invariant by `x * y ∈ D ↔ x ∈ D` |
| `slash_invariant_heckeCoset` | the operator of that transversal, applied to a `K`-fixed `F`, is `K`-fixed | `IsHeckeFunction.heckeFun_mem` + `mem_levelSpace_slashRep`; the Hecke-function condition's finiteness half is the transversal theorem's conclusion, its bi-invariance is the same `x * y ∈ D ↔ x ∈ D` |

**What actually stopped this slice (measured).** Not the indicator: probed in isolation,
`(1 : α → ℂ) a = 1` is `rfl`, and `rw [Set.indicator_of_mem h]` followed by `simp` closes
`D.indicator 1 (x * y) = 1`. The friction is `DoubleCoset.doubleCoset`'s witness API: the shape of
`mem_doubleCoset.mp` (`∃ a ∈ H * {g}, ∃ b ∈ K, a * b = x`) is not the triple-product shape
`mem_doubleCoset.mpr` consumes (`∃ a ∈ H, ∃ b ∈ K, a * g * b = x`), so the two invariance lemmas
have to convert between them by a `Set.mem_mul`/`Set.mem_singleton` unpacking per direction.
That is a one-time bookkeeping layer of ~40 lines, but it is a layer, not a rewrite.

Better route, and the recommendation: do not go through `DoubleCoset.mem_doubleCoset` at all.
The port already has `HeckePair.doubleCoset_mul_mem` (`HeckePair.lean`) for exactly these two
statements — `x ∈ U g U → u ∈ U → x * u ∈ U g U` — and `HeckePair.doubleCoset g =
(U : Set G) * {g} * U` is mathlib's `DoubleCoset.doubleCoset g U U` unfolded, so the bridge is
`Iff.rfl` (or one `rfl`-level `show`). Use that, plus `u⁻¹` for the converse direction, and the
two invariance lemmas are three lines each.

## 5. Stage C: the retarget, and why nothing is retired yet

The calculus pays out on the reindexing half of five classical files; the coset *count* stays,
because that is the mathematics:

| family | current home | what the calculus replaces | what must stay |
|---|---|---|---|
| Γ₀ `U_p` | `Defs/HeckeRepresentatives` (`heckeU_eq_sum_zmod`, `heckeMatrix_mul_of_dvd`, `heckeU_slash_mapGL`) | the sum-invariance reindexing in `heckeU_slash_mapGL` | the coset action and the count |
| Γ₀ `T_p` | same (`heckeT_eq_sum_onePoint`, `heckeRep_mul`, `redMatrix`, `heckeT_slash_mapGL`) | the reindexing in `heckeT_slash_mapGL` | `redMatrix`/`dvd_conjugate`, the count |
| Γ_H `U_q` | `HeckeCosetDecomposition` (`beta`, `sum_slash_beta_eq_heckeU`, `sum_slash_beta_slash_eq`) | `sum_slash_beta_slash_eq` (the invariance, 45 lines) | `bijective_transl`, `bijective_option`, the Bezout model |
| Γ₁ `U_ℓ` | `HeckeULevel` (`exists_cocycle`, `heckeMatrix_mul_eq`, `perm`, `heckeU_slash_eq_smul`) | the sum-invariance half, via `heckeFun_comp_inv_mul` | the cocycle construction |
| diagonal level change | `HeckeDiagDegeneracy` (`exists_cocycle`, `heckeDiagMatrix_mul_eq`, `stretchSlash`) | the transport, via `heckeFun_comp` | the stretch map and its level bookkeeping |

**The obstruction, stated once.** To identify a concrete sum `∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j`
with `DoubleCosetHecke.heckeCoset`, one must supply the transversal hypotheses of §4 — that the
`p` (or `p+1`) representatives are distinct mod `K` and exhaust the double coset. The port never
states that: it is implicit in the `Finset.sum_congr` + `Equiv.sum_comp` reindexing inside each
invariance proof. **Each family therefore needs one new lemma before anything can be retired** —
the coset system as a covering statement, e.g. for `T_p` at good level
`Γ₀(N) · diag(1,p) · Γ₀(N) = ⋃_{x : OnePoint (ZMod p)} heckeRep p x · Γ₀(N)`, and the
`GL(2,ℝ)⁺`/`Γ₀(N) ≤ GL(2,ℝ)⁺` restriction of the level group.

The family to start with is `Γ_H` (`HeckeCosetDecomposition`): it *proves* its representative
families bijective onto the coset space (`bijective_transl`, `bijective_option`), so the covering
hypothesis is already available, and its invariance proof (`sum_slash_beta_slash_eq`, 45 lines) is
the smallest complete retirement unit. The Γ₀ families need the covering lemma first.

**Retirement mechanics.** Once a family's headline is re-proved through the calculus and its
consumers compile unchanged, the superseded private helpers go to `Reserve/` with
`tools/deps/move_dead.py --copy` (the shelf imports only the port's public API), and the public
declarations the pin's checker holds stay in place until the whole family is retargeted — a
half-moved family is worse than a duplicated one. Overlap between the shelf and the live module is
expected and accepted. The pin statements themselves are not negotiable in this phase: the
consumers (`ModularCurve/Period/PeriodMapHecke`, `HeckeStability`) hold the interface.

**The shelf is taken, and it is organized by argument, not by file.** The eight modules of the
replacement set — `Defs/HeckeRepresentatives`, `Defs/Gamma1HeckeOperators`, `HeckeInvariance`,
`HeckeCosetDecomposition`, `HeckeULevel`, `HeckeDiagDegeneracy`, `HeckeFricke`,
`HeckeFrickeTrace`; 3,409 lines — are archived whole in
[`Reserve/HeckeCosetCalculus/`](../Reserve/HeckeCosetCalculus/README.md), all eight building.
Structures are not archived: the matrices, `heckeRep`/`redMatrix`/`wt`/`affinePerm`, the level
groups and `heckeU`/`heckeT` stay live and are imported, because they have consumers outside the
replacement set (`Gamma1CuspStructure` uses `affinePerm` and `heckeU_eq_sum_zmod`,
`PhiGenDescends` uses `redMatrix`/`heckeRep`/`wt`). The rule the shelf follows:

> archive the copy of an argument the archived proof **calls**; import live anything that
> **survives** the retarget.

So the invariance chain is self-contained (the archived `HeckeInvariance` imports the archived
`HeckeRepresentatives`, `HeckeFricke`, `HeckeCosetDecomposition`, because those arguments are
themselves replaced), while the Γ₁ pair imports live `HeckePrelude`/`HeckeQCoeff`/
`Gamma1Vanishing` and takes `affinePerm`, `heckeU_eq_sum_zmod` and the matrices from
`FLTForHuman`. No module reaches both copies of a name; if a live structure the Γ₁ pair leans on
is later retired, it is copied in then.

An earlier cut put only six files in the shelf, on the assumption that a shelf must be
self-contained per file; that assumption made the Γ₁ pair unbuildable and was wrong. The
`Γ₁` arguments need no archived sibling.

**Why nothing moved out of the live tree yet.** A retirement needs the replacement in place;
Stage B's core is a carrier, not a replacement. Moving anything today would leave a live consumer
(or the pin's statement check) pointing at a shelf. The correct handoff is §4 and the `Γ_H` family
above; the shelf is the record to diff against when it lands.

## 6. Verification (as measured)

- `lake build FLTForHuman.RepTheory.DoubleCosetHecke` → 1,693 jobs, 3.2 s, no warnings.
- `lake build FLTForHuman.ModularForms.HeckeSlashRep` → 2,321 jobs, 3.2 s, no warnings.
- `#print axioms` on `heckeFun_eq_sum`, `heckeFun_heckeFun`, `heckeFun_mem_levelSpace`,
  `IsHeckeFunction.heckeFun_mem`, `slashRep`, `mem_levelSpace_slashRep`:
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, no `maxHeartbeats` raise, no tree build.
- Neither module declares a `spec-pin:`: the source is not FLT, so there is no pin to diff
  against. They are tier 3 (public, unchecked) by construction; if a register wants them, they
  belong with the port's own statements, not with the checker's pin map.

## 7. Attribution

The source is Apache-2.0, Copyright 2026 Anthropic, PBC (`grh/NOTICE`,
`https://github.com/lsernau/grh-lean` at `72fead1`). Both new modules carry that notice in their
headers, as the `Reserve` shelves do for their pins. The source's own `ATTRIBUTION.md` records that
`New.levelSpace` adapts mathlib's `Representation.invariants`; the port's `levelSpace` is a
`Submodule` of the character-fixed points and does not use it.
