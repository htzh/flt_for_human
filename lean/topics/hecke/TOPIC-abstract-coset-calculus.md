# The abstract double-coset Hecke calculus (taken from the GRH proof)

**Status: in progress (2026-11-17).** Stage A (the calculus module) and Stage B (the
`SlashAction` adapter) are the sets of this order; Stage C (retarget) is measured in §5 and
is the reason the order exists.

**Audience.** A fresh coding session continuing the Hecke refactor. Read
[refactor.md](../refactor.md) for the standard this order is written against, and
[PORTING-Hecke.md](../PORTING-Hecke.md) §§1–3 for the port's Hecke inventory.

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
| `DoubleCosets Γ K` | 83 | `DoubleCoset.Quotient Γ K` |
| `mem_levelSpace`, `map_mem_levelSpace_of_commute` | 88, 93 | the eliminator, and `A`-linear maps commuting with `π` preserve it |
| `exists_eq_map_mul_rep_mul`, `eq_and_eq_one_of_doubleCoset_rep` | 104, 116 | a double coset transversal `e(Δ) \ G / K`, and freeness at a representative |
| `classSum`, `classSum_eq_finsum_of_rep`, `card_classAut_mul_mul` | 132, 149, 136 | the weighted class sum over `Γ \ G / K`; not taken (§4) |
| `isLocallyConstant_of_eventually_mul` | 168 | right-invariance near `1` gives local constancy |
| `finite_quotient_image_of_isCompact`, `IsCompact.relIndex_ne_zero` | 178, 186 | a compact set meets finitely many `H`-cosets; open ⊂ compact has finite index |
| `relIndex_mul_measure_inf`, `measure_inter_eq_inv_relIndex` | 194, 214 | `[K : H ⊓ K] · μ(H ⊓ K) = μ K`, hence the `1/[K : H ⊓ K]` weight |
| `HasFiniteCosets K f`, `IsHeckeFunction K f` | 241, 244 | `f` lives on finitely many cosets; bi-invariant and finite |
| `heckeFun_eq_sum_toFinset`, `map_heckeFun` | 250, 258 | the finite sum over an explicit `Finset`; an intertwining `L` transports the operator |
| `levelSpace_anti` | 262 | `K ≤ K'` gives `levelSpace K' ≤ levelSpace K` |
| `isHeckeFunction_doubleCoset` | 267 | `1_{KgK}` is a Hecke function (`K` compact open) |
| **`heckeFun_eq_sum`** | 285 | **any representative system** `s` gives the operator |
| **`heckeFun_eq_sum_pullback`** | 307 | the same for `θ : G' → G` inducing `G'/J ↪ G/K` |
| `HasFiniteCosets.comp_inv_mul` | 348 | a left translate keeps `HasFiniteCosets` |
| **`heckeFun_comp_inv_mul`** | 361 | `heckeFun` of `x ↦ f (x⁻¹ * g)` is `π x` of `heckeFun f` |
| `heckeFun_comp` | 330 | transport along a surjective hom with `a ⁻¹K = J` |
| **`heckeFun_heckeFun`** | 378 | composition of operators = operator of the convolution |
| **`heckeFun_mem_levelSpace`** | 395 | a bi-invariant `f` sends `levelSpace (K,χ)` into `levelSpace (K',χ')` |
| `IsHeckeFunction.heckeFun_mem` | 410 | the trivial-character case, the invariance theorem |

The bold rows are the calculus; the rest is definition side or the compact-open/measure layer.

## 2. Where it lands

Two modules, no consumer edit in Stages A and B:

| module | role | imports |
|---|---|---|
| `FLTForHuman/RepTheory/DoubleCosetHecke.lean` | the calculus of §1, statements as in the source, namespace `DoubleCosetHecke` | mathlib only (`Finprod`, `DoubleCoset`, `RepresentationTheory.Basic`, `GroupTheory.Index`) |
| `FLTForHuman/ModularForms/HeckeSlashRep.lean` | the adapter: `slashRep k : Representation ℂ (GL (Fin 2) ℝ)ᵐᵒᵖ (ℍ → ℂ)`, and the `heckeU`/`heckeT` instance lemmas that become available once a coset system is supplied | `DoubleCosetHecke` + `Defs/HeckeOperator` |

Namespace: `DoubleCosetHecke` because `HeckeCoset` (in `HeckeCosetDecomposition.lean`) and
`AbstractHeckeOperator`, `HeckePair`, `HeckeIntegralSeam` are taken. The operator keeps the source's
name `heckeFun`; the adapter refers to it qualified.

Why not extend `RepTheory/AbstractHeckeOperator.lean`: that module is the pin's
`Def_AbstractHeckeOperator.lean` under the checker, indexed by one double coset's data; the new
module is a different role (the calculus of an operator indexed by `f`) and is not pinning
anything. A file and a directory of the same name would also collide under the lake globs.

## 3. Adaptations

1. **mathlib v4.34 vs the source's `56a0058`.** The source is on `v4.35.0`. Names that moved:
   `finsum_eq_sum_of_support_subset` → `finsum_eq_finset_sum_of_support_subset`;
   `fun_smul_left`/`fun_smul_right` are not in v4.34 (their occurrences are in
   `heckeFun_heckeFun`'s proof only, and are replaced by `finsum_smul'`/`Finset.sum_smul` steps);
   `Set.Finite.toFinset`/`toFinite` are unchanged. If a name is genuinely absent, the fallback is to
   read v4.35's text from the GRH directory's mathlib cache — do not download a toolchain for a
   rename.
2. **`Representation`, not `SlashAction`, in the abstract module.** mathlib's slash action is an
   *anti*-action (`SlashAction.slash_mul : map k (g*h) a = map k h (map k g a)`), i.e. a
   `DistribMulAction Gᵐᵒᵖ`. The adapter turns it into a genuine `Representation` on the opposite
   group; the abstract module never mentions modular forms.
3. **Compact open → commensurable** in `isHeckeFunction_doubleCoset`. Our `K` is a discrete
   congruence subgroup, so the source's `IsOpen`+`CompactSpace` hypothesis has to be replaced by
   finite right index of `K ⊓ g K g⁻¹` in `K`. That is the only place compactness enters; every
   calculus lemma is compactness-free. If the finite-index proof fights, the lemma is deferred —
   nothing in Stages B/C consumes it, because a concrete coset system supplies the finiteness
   through `heckeFun_eq_sum`'s covering hypothesis.
4. **No `classSum`/`classIntegral`/`compactMean`.** The weighted class sums, the `vol K = 1` mean,
   the orbit unfolding and the mean over a compact subgroup serve the trace formula; the port has
   the adelic analytic counterparts in `AutomorphicForm/Adelic`. Two of their statements are worth
   remembering rather than porting: `smul_classSum_mem` (integrality of a weighted class sum when
   every stabiliser order divides `M`) and `classSum_le_card_mul` (a bound by the number of
   classes).

## 4. Why not Gelfand's trick

`Lib/General/LinearAlgebra/IntegralLattices.lean` (same pin) proves `f' * f = f * f'` of the
double-coset operators — `heckeFun_comm` at `:405`, resting on `heckeFun_adjoint` at `:337` and
`exists_invTransposeGL_inv_eq` at `:312` — from Gelfand's condition: $g^{\mathsf T} = (k^{\mathsf
T})^{-1} g k$ with $k \in GL_n(O)$, $O$ a valuation subring. That is a property of the *pair*
$(G,K)$: it holds for the maximal compact of a local field because a Smith-normal-form diagonal is
transpose-invariant and $GL_n(O)$ contains the Weyl element. It fails for $K = \Gamma_0(N) \subset
GL_2(\mathbb Q)^+$, $N>1$: the involution multiplies $\det$ by $(\det g)^{-2}$, and the Weyl element
is not in $\Gamma_0(N)$. This is not a proof artefact — it is why the classical adjoint of $T_p$ at
$\Gamma_1(N)$ is $T_p$ only up to $\overline{\varepsilon(p)}$ (the diagonal summand is the
correction); see `Analytic/PeterssonHeckeTheorems`.

So the adjoint/commutation half is **out of scope** for the classical retarget. It is in scope as a
separate, small order for the adelic side: `HeckePair.conv` is already a measure-free convolution,
and a Gelfand theorem for it would supersede the `IsHaarMeasure`/`map θ = ν` hypotheses of
`AntiInvolutionHaar.convKer_comm`. Not part of this order.

## 5. Stage C: the retarget, measured

The calculus pays out on the reindexing half of five files; the coset *count* stays, because that
is the mathematics. Per family:

| family | current home | what the calculus replaces | what must stay |
|---|---|---|---|
| Γ₀ `U_p` | `Defs/HeckeRepresentatives` (`heckeU_eq_sum_zmod`, `heckeMatrix_mul_of_dvd`, `heckeU_slash_mapGL`) | the sum-invariance reindexing in `heckeU_slash_mapGL` | the coset action (`heckeMatrix_mul_of_dvd`) and the count |
| Γ₀ `T_p` | same (`heckeT_eq_sum_onePoint`, `heckeRep_mul`, `redMatrix`, `heckeT_slash_mapGL`) | the reindexing in `heckeT_slash_mapGL` | `redMatrix`/`dvd_conjugate`, the count |
| Γ_H `U_q` | `HeckeCosetDecomposition` (`beta`, `sum_slash_beta_eq_heckeU`, `sum_slash_beta_slash_eq`) | `sum_slash_beta_slash_eq` (the invariance, 45 lines) | `bijective_transl`, `bijective_option`, the Bezout model |
| Γ₁ `U_ℓ` | `HeckeULevel` (`exists_cocycle`, `heckeMatrix_mul_eq`, `perm`, `heckeU_slash_eq_smul`) | the sum-invariance half, via `heckeFun_comp_inv_mul` | the cocycle construction |
| diagonal level change | `HeckeDiagDegeneracy` (`exists_cocycle`, `heckeDiagMatrix_mul_eq`, `stretchSlash`) | the transport, via `heckeFun_comp` | the stretch map and its level bookkeeping |

**The obstruction to a full retarget, stated once.** To *identify* a concrete sum
`∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j` with `DoubleCosetHecke.heckeFun` one must supply
`heckeFun_eq_sum`'s covering hypothesis, i.e. that the `p` (or `p+1`) right `K`-cosets of the
representatives exhaust the double coset. The port never states that: it is implicit in the
`Finset.sum_congr` + `Equiv.sum_comp` reindexing inside each invariance proof. **Stage C therefore
needs one new lemma per family before anything can be retired** — the coset system as a
`Set.Finite`/covering statement, e.g. for `T_p` at good level
`Γ₀(N) · diag(1,p) · Γ₀(N) = ⋃_{x : OnePoint (ZMod p)} heckeRep p x · Γ₀(N)`.

Consequence for this session: the retarget proceeds family by family, starting with the one whose
covering statement is already available (`HeckeCosetDecomposition` proves `bijective_transl` /
`bijective_option`, i.e. its reps *are* a bijection onto the coset space), and nothing is retired
before its replacement is green.

**Retirement mechanics.** Once a family's headline is re-proved through the calculus and its
consumers compile unchanged, the superseded private helpers go to `Reserve/` with
`tools/deps/move_dead.py --copy` (the shelf imports only the port's public API), and the public
declarations that the pin's checker holds stay in place until the whole family is retargeted — a
half-moved family is worse than a duplicated one. Overlap between the shelf and the live module is
expected and accepted.

## 6. Verification

- Each new module builds individually: `cd lean && lake build FLTForHuman.RepTheory.DoubleCosetHecke`,
  `lake build FLTForHuman.ModularForms.HeckeSlashRep`. No tree build (workspace rule).
- No `sorry`, no `maxHeartbeats` raise, `#print axioms` clean on the headlines.
- The new modules declare no `spec-pin:` — they are not pinning an FLT file — so
  `spec/check_port.py` builds them without statement-diffing them. That is deliberate: the source
  is not FLT, and a pin wire to a repository the checker does not know would be a fiction.
- Stage C: after each retarget, the *consumers* are the check (playbook §4, second phase): every
  call site compiles unchanged.

## 7. Attribution

The source is Apache-2.0, Copyright 2026 Anthropic, PBC (`grh/NOTICE`,
`https://github.com/lsernau/grh-lean` at `72fead1`). The ported modules carry that notice in their
headers, as `Reserve` and the FLT modules do for their pins. The source's own `ATTRIBUTION.md`
records that `New.levelSpace` adapts mathlib's `Representation.invariants`; the port's `levelSpace`
should keep that in mind when choosing between a restatement and a mathlib reuse.
