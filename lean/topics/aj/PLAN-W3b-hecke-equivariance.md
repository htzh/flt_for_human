# W3b — the Hecke-equivariance layer of the period map

Next wave of the aj subject, 2026-10-26 — the **Hecke-equivariance layer**, and under the A-only ordering
the wave that follows W2 directly. Its nominal companion,
[PLAN-W3-honest-integral.md](PLAN-W3-honest-integral.md) (the honest charted-surface integral), is built
and green but shelved in `Reserve/`: its only consumers are the two definitional decisions the A-only
ordering defers, and [TOPIC-translation-a-b.md](TOPIC-translation-a-b.md) §9 settles that the merged
theory they serve is a dictionary rather than a bridge. The two waves share no file and neither blocks
the other, so the shelving changes nothing here. Parent note:
[../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md) (§1's comparison
(ii), §10.4, §13). Predecessors: [PLAN-W1-stokes.md](PLAN-W1-stokes.md) (landed),
[PLAN-W2-parabolic-homs.md](PLAN-W2-parabolic-homs.md) (landed). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

**Decision.** W3b is the layer in which `ModularCurve.periodMapOf` is proved **Hecke-equivariant** —
under `T_ℓ` (through `heckeU` + the slash leg), under the diamond operators, and the three
`CuspForm.Stable{T,U,D}` statements that supply the hypotheses — together with the two engine lemmas
it rides on (corestriction = transfer; a period hom is determined by its primitive). Measured on the
current frontier: **12 pin nodes / 2,366 lines**, closed (their union demand is themselves plus two
definition tails), and **7 of the 9 unported direct premises of A's mouth**.

**Why this block comes first under the A-only ordering.** The subject is ordered by
[§10.4](../TOPIC-abel-jacobi-port-structure.md#104-the-criterion-is-simplicity-not-verification)'s
simplicity, not by distance to A's mouth: definitional survivors first, consumers after. With the merged
theory deferred, the only survivor decision still open is outside A — the honest integral, which is B's
— so A's own last definitional layer is this one. It is also the largest **no-regret** block in the
subject: it commits to no side of any survivor decision (§12), it is the last cheap thing standing
between the port and a mouth whose remaining demand is two multi-thousand-line silos, and 7 of the
mouth's 9 unported direct premises are in it. The facts below (12 nodes / 2,366 lines, closed) are why it
is worth dispatching; the mouth's premise list is why it is next.

**Status: checkpoint A landed.** `StableD`/`StableU`/`StableT` are in
`FLTForHuman/ModularForms/Defs/GammaH.lean` (§"Hecke stability"), completing the pin
`Def_CuspForm_HeckeOperatorFormsGammaH.lean`'s tail in the module that already hosts its lines 18–70.
The module is now wired (`spec-pin:` × 4; `check_port` **28 ok / 0 mismatch / 0 missing**) and removed
from `spec/old_check_stmts.py`; the three bodies are hand-diffed against the pin (D5) and match.
`lake build FLTForHuman.ModularForms.Defs.GammaH` is 6 s and one dependent
(`ModularForms.CuspFormSlashHecke`) 9 s, so the two added imports (`ModularForms.Basic` for `CuspForm`,
`Defs.HeckeOperator` for `heckeU`/`heckeDiagMatrix`) cost nothing.

**Status: checkpoints B and C landed.** `GroupTheory/Corestriction.lean` (162 lines, Mathlib-only —
`grep -c '^import FLTForHuman'` = 0) carries `resHom`/`transferAux`/`coresHom` and node 10, `check_port`
8 ok / 0 mismatch; the pin's `letI := H.fintypeQuotientOfFiniteIndex` is load-bearing there (`letI`
inlines, and that is what makes the coset sum definitionally the transfer), so the module keeps the same
`linter.style.haveILetI false` exemption as `HeckeInvariance.lean`. Nodes 11, 12 and 7 are green with the
two homing corrections recorded in §4 and §5 below (12 in `PeriodOf.lean` with the `periodAlongOf_eq_sub`
prelude moved down to it; 7 in `ExistsEquivariantPrimitive.lean`, since `PeriodOf` sits below its only
proof). Four modules left `spec/old_check_stmts.py`.

**Status: checkpoints D and E landed.** `ModularForms/HeckeCosetDecomposition.lean` (511 lines) is the shared
block written once from the 19 duplicated private names, taken from
`S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean:14–468` (byte-identical to the same range of the
node-9 file, which differs only in its last nineteen lines), in the pin's namespace `HeckeCoset`, and
deliberately **unwired** — it has no pin statement, and the seven `omit [NeZero M] in` binders would make
its statements differ textually from the pin's unused-section-variable copies; the provenance line range
is in the header instead. Nodes 8 and 9 in `ModularForms/HeckeInvariance.lean` (+62) are nine-line `rw`
wrappers: the 970 pin lines are the shared coset computation, `check_port` 5 ok / 0 mismatch (all five
headlines of that module, whose `PORT_FILES` line is gone).

**Status: checkpoints F and G landed — all twelve headlines are in.** `HeckeStability.lean` (90 lines)
carries 6, 5, 4, each a 3–5 line unfolding over already-ported lemmas; `PeriodMapHecke.lean` (389 lines)
carries 1, 3, 2, and after the dedup they cost 78, 128 and **62** written lines against the pin's 357, 158
and **591** — node 2's 591 is the two coset sums, which are the prelude's `ℍ → ℂ` lemmas at `k = 2` plus
`SlashInvariantFormClass.slash_action_eq f`, not new mathematics. Two findings to keep:

* the three predicates are `CuspForm.Stable*`, not `CohCarrier.Stable*` (pin
  `Def_CuspForm_HeckeOperatorFormsGammaH.lean:12`), and `check_port` could not see the difference because
  it matches declarations by unqualified name — namespace fidelity on this wire is a manual check;
* **D4 is settled empirically**: all fifteen of the pin's `attribute [-instance]`/`[-simp]` lines were
  dropped and **none was needed** — no proof in the wave mentions an instance or simp lemma of `heckeT`,
  `conjL` or `heckeUpper`. The only `v4.34` friction was `if_pos` → `ite_eq_left` and two
  `tac1 <;> tac2` → `tac1; tac2`.

`Corestriction.lean` grew to 186 lines: node 1 needs `HeckeEis.pullbackHom`, so the pin's Pullback
section (7 lines, Mathlib-only) is transcribed there too — D4's "the wave defines neither `heckeUpper`,
`resHom` nor `pullbackHom`" is now wrong about `pullbackHom` and `resHom`, both of which landed. All
twelve `#print axioms` are `[propext, Classical.choice, Quot.sound]`.

**Status: the wave is complete and green.** Fourth sibling kept (it needed neither an `omit` nor an
explicit instance, so D4's negative holds for it too). Final verification: nine wired modules
**90 ok / 0 mismatch / 0 missing / 0 own / 0 kw**; five modules released from
`spec/old_check_stmts.py`; `dedup.py` 0 clusters / 0 removable lines on the wave's five modules;
`move_dead.py` 0 dead declarations; every module 2.6–18 s, zero warnings.

**What it cost, and where the estimate was wrong.** **1,586 written against the pin's 2,366** (0.67×, net
1,514) — the plan priced 2,600–3,000 from a written ÷ content ratio of 1.07. The miss is entirely the
dedup, and it is instructive for the next pricing: the shared prelude is one copy of ~460 pin lines rather
than the ≈900 the plan assumed (its own 1.07 would have held on the transcription alone), nodes 8 and 9
collapse to 9-line `rw` wrappers once the prelude exists, and nodes 2 / 1 / 3 lose their prelude halves —
591 → 62, 357 → 78, 158 → 128. So a **dedup-first** wave prices at ≈0.67 × pin, and the ratio to carry to
W4 is the one this wave measured, not W1's. Node 2 is the single largest proof of the wave and is now 62
lines of genuine content.

**The mouth's demand after this wave.** `needed(653)` is **156 nodes / 55,470 lines**, and the 653 has
**exactly two** unported direct premises: the injectivity / Abel–Jacobi silo
(`…exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf`, 522 nodes / sub 161) and
the rank silo (`…exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup`,
174 nodes / sub 24 / 6,218 lines). Nothing else unported at depth 1. The cheap one is the basis silo by a
wide margin, and it is also §9.2 of the parent's borrowed-rank coupling — so W4 should be the rank/basis
silo, not the smoothed cluster, and the latter is a sub-block of the other silo.

**One checker limitation is now on the record, and it has two halves.** `check_port` matches a
declaration to the pin by **unqualified name** but compares its **statement text verbatim**. So the
original `CohCarrier.Stable*` homing passed at 28 ok, while a body spelling `StableT` where the pin writes
`CuspForm.StableT` — the same proposition inside `namespace CuspForm` — is a mismatch. Namespace fidelity
is therefore a manual reading of the pin, and D3's "spell the pin's qualified names inside a namespace" is
load-bearing rather than stylistic. Both halves were observed on this wave: the first by reading the pin,
the second by a mutation test on `CuspForm.stableT` that was interrupted mid-run and reverted by hand.

**No mutation sweep.** One spot check was made (node 2, `∣[(2 : ℤ)]` → `∣[(3 : ℤ)]`, caught and
reverted), which is enough given the above: the wire compares statement text verbatim, so a wrong
statement is a mismatch by construction. A twelve-row sweep would re-establish what the comparison
already does.

**Naming.** The shared block was first called `HeckeCosetPrelude`; that names its role in a proof, not the
mathematics, and it was renamed **`ModularForms/HeckeCosetDecomposition.lean`** with the namespace
`HeckeCoset` (was `HeckeGammaH`). What the module is: the coset decomposition of `Γ_HUpper(M,ℓ)` over
`Γ_H(M)` — the index, explicit representatives, and the two coset sums that read `U_q` and
`U_ℓ + (·) ∣ (ρ · diag ℓ)` off them, i.e. the concrete case of the object the adelic column abstracts as
`IsHeckeCosetSystem`. Its header now states the mathematics first and the provenance second.

**No `maxHeartbeats` raise.** The pin's `set_option maxHeartbeats 6400000` was inherited and is not
needed on mathlib `v4.34.0`: it is removed, and the module compiles at the default limit. Measured cold
build times of the ten wave modules (2026-10-26, this machine): Corestriction 3.3 s, `GammaH` 4.2,
`PeriodPrimitive` 4.2, `PeriodOf` 4.0, `HeckeCosetDecomposition` 6.6, `ExistsEquivariantPrimitive` 4.8,
`HeckeInvariance` 3.5, `HeckeStability` 3.9, `PeriodLatticeSpan` 5.5, `PeriodMapHecke` 6.7 — 19.7 s wall
for all ten, worst single module 6.7 s. Nothing in the wave is near the 40 s line.

## 1. Where the wave sits, measured

A's mouth `ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf`
(653) has **nine unported direct premises** on the current frontier (`needed` 168 nodes / 57,836
lines). They fall into exactly three blocks:

| block | nodes | lines | what it is |
|---|---:|---:|---|
| injectivity / Abel–Jacobi | `…exists_injective_…jH_quotient_periodLatticeOf` 302 | sub 161 / 55,688 | the curve-side mouth: descent, the place dictionary, Abel's theorem |
| lattice rank and discreteness | `…exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_…` 267 | sub 24 / 6,218 | the basis theorem, with the RR dimension chain under it |
| **Hecke equivariance and packaging** | **7 nodes, 1,181 lines** | **sub 3 or less each** | **this wave** |

So this wave is the third block: after it the mouth has **two** unported premises, both of them
multi-thousand-line bodies. That is the whole argument for the order — the wave is not on the
critical *path* in lines, it is the last cheap thing standing between the port and a mouth whose
remaining demand is two silos.

## 2. Scope

Twelve pin nodes, 2,366 raw lines. The seven that are the mouth's premises, then the five they
need:

| # | pin node | lines | content |
|---|---|---:|---|
| 1 | `ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU` | 357 | `g = U_q f ⇒ periodMapOf g = heckeT q (periodMapOf f)`: `T`-equivariance through the `U` leg |
| 2 | `ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash` | 591 | the same with the slash leg `(ρ · diag ℓ)` added — the prime case `ℓ ∤ M` |
| 3 | `ModularCurve.periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash` | 158 | `g = f ∣[2] σ ⇒ periodMapOf g = diamondRaw σ (periodMapOf f)`: the diamond operator |
| 4 | `CuspForm.stableT` | 24 | `StableT`: for `ρ ∈ Γ₀(M)` with `ρ₁₁ ≡ ℓ (mod M)`, the sum `U_ℓ f + f ∣ (ρ · diag ℓ)` is a cusp form of `Γ_H` |
| 5 | `CuspForm.stableU` | 19 | `StableU`: `U_q f` is a cusp form of `Γ_H` (invariant, differentiable, cuspidal) |
| 6 | `CuspForm.stableD` | 13 | `StableD`: for `σ ∈ Γ₀(M)`, `f ∣ σ` is still cuspidal at every cusp |
| 7 | `ModularCurve.periodMapOf_apply_eq_periodOf` | 19 | the period map's value on `γ` is `periodOf γ f` — the bridge to the lattice |
| — | | | *support* |
| 8 | `ModularForm.heckeU_slash_eq_self_of_mem_GammaH` | 481 | `U_q f` is `Γ_H`-invariant |
| 9 | `ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH` | 489 | the `U_q f + f ∣ (ρ · diag ℓ)` combination is `Γ_H`-invariant |
| 10 | `HeckeEis.coresHom_eq_transfer` | 59 | the pin's coset-sum corestriction equals `MonoidHom.transfer` |
| 11 | `ModularCurve.Period.IsEquivariantPrimitive.periodHom_eq_of_hasDerivAt` | 63 | two equivariant primitives with the same derivative have the same period hom |
| 12 | `ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf` | 93 | `periodOf γ f = F (γ • I) − F I` for a primitive `F` |

Numbers 1–3 are the mathematics; 4–6 are the cusp-form stability statements the mouth takes as
premises *independently* of 1–3 (the pin cites neither half from the other); 8–9 are the two slash
computations the `Stable` predicates are built on and the two largest proofs in the wave; 7 and 10–12
are the engine, each two or three lines of statement around a real computation.

So the wave has **two independent halves** — the equivariance trio on the engine, and the stability
trio on the slash lemmas — which is what makes it two-implementer work from the first module.

**Definition tails (not nodes, but this wave's, ~75 lines).** Three of the pin's concepts are not in
the port and the statements cannot be written without them:

* `CuspForm.StableD/U/T` — the tail of
  [`Def_CuspForm_HeckeOperatorFormsGammaH.lean:72–96`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean#L72-L96),
  a definition module the port has **already transcribed its lines 18–70** from
  (`ModularForms/Defs/GammaH.lean`). The tail is 25 lines including docstrings.
* `HeckeEis.transferAux` / `coe_transferAux` / `transferAux_mul` / `coresHom` / `coresHom_apply` —
  [`Def_Gamma0HeckeOperatorHom.lean:216–263`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Gamma0HeckeOperatorHom.lean#L216-L263),
  from a module the port has not opened at all (`coresHom` is the only thing in it this wave
  needs). ~48 lines. `MonoidHom.transfer` itself is mathlib
  (`Mathlib/GroupTheory/Transfer.lean:148`).

**One optional companion, recommended (+105 lines).**
`ModularCurve.periodMapOf_gammaH_eq_comp_of_coe_eq_slash` is the fourth sibling of the same family
(105 lines: two prelude lemmas and a 59-line proof). It is **not** in the 653 cone — its four citers
are the newform / Tate-level-automorphy column — but it shares node 11's prelude (`hasDerivAt_comp_smul`
is in this file too), it completes the family in one home, and its outbound indegree is 4. Take it as
set 3 or record the omission; do not leave it to be re-opened by the next wave that touches the
family.

## 3. Order

```
defs:  StableD/U/T ─────────────────────────────┬─ 6 (13)
       coresHom ── 10 (59) ─┐                    │
                            ├─ 1 (357)   8 (481) ┴─ 5 (19)
       11 (63) ─────────────┘  2 (591)   9 (489) ─── 4 (24)
       12 (93) ─ 7 (19) ─────── 3 (158)
```

The pin's own citation graph, not a reading: 1 and 2 cite exactly 10 and 11; 3 cites 7 and 12; 5
cites 8; 4 cites 9; 6 cites nothing. The two halves never meet.

* **layer 0 — definitions.** `StableD/U/T`, then `coresHom`. Nothing else elaborates without them.
* **layer 1 — ready now.** 6, 8, 9, 10, 11, 12: all six are on the current premise-ready shelf
  (`needed = 1`). 8 and 9 are the two 480-line proofs and take their own checkpoints.
* **layer 2 — the small bridges.** 5 (needs 8), 4 (needs 9), 7 (needs 12).
* **layer 3 — the three equivariance statements.** 1 and 2 (both just 10 + 11), then 3 (needs 7 and
  12). 2 is more than a quarter of the wave and gets its own checkpoint.

Checkpoints, each a green module: **A** = defs, **B** = 11 + 10, **C** = 12 + 7, **D** = 6, **E** = 8,
**F** = 9, **G** = 5 + 4, **H** = 1, **I** = 3, **J** = 2. Two implementers from layer 0 on: one on
the stability half (D, E, F, G — 1,026 lines) and one on the engine and equivariance half (B, C, H,
I, J — 1,340 lines, of which 591 is node 2).

## 4. Homing

Homing follows the statement (the rule [WORKORDER-W2-parabolic-homs.md](WORKORDER-W2-parabolic-homs.md)
§10 sets). No new top-level directory: three new modules, and four existing modules gain a headline or a
definition tail:

| module | nodes | why it is the natural home |
|---|---|---|
| `FLTForHuman/GroupTheory/Corestriction.lean` (new) | 10 + `coresHom`'s definition | the statement mentions no modular vocabulary at all — `(H : Subgroup G)`, `Additive H →+ A`, `MonoidHom.transfer`. It imports **Mathlib only**, which is the layering rule: a `GroupTheory/` module must not import `ModularForms/` (the inversion `GroupTheory/ModularGroup/FreeProduct.lean` objects to and W2b had to fix). |
| `FLTForHuman/ModularForms/Defs/GammaH.lean` (+25) | `StableD/U/T` definitions | the module already hosts the same pin file's lines 18–70 and its header says so; appending the tail completes the transcription of one pin definition module in one home. |
| `FLTForHuman/ModularForms/HeckeInvariance.lean` (+2 headlines) | 8, 9 | it is the `Γ_H` case of the file's own subject: the `Γ₀(N)` trio `heckeU_slash_eq_self_of_mem_Gamma0` / `heckeT_…` / `…_Gamma0_div` is already there with its private workhorses. |
| `FLTForHuman/ModularCurve/Period/PeriodMapHecke.lean` (new) | 1, 2, 3 (+ optional `comp`) | the `ModularCurve.periodMapOf` statements are period-lattice content and `ModularCurve/Period/` is the subject's directory (W2's two modules are there). |
| `FLTForHuman/ModularCurve/Period/HeckeStability.lean` (new) | 4, 5, 6 | the `CuspForm.Stable*` theorems are one-line unfoldings of the definitions plus nodes 8–9; keeping them out of `HeckeInvariance.lean` keeps that module's "statements about `U_p`/`T_p` themselves" scope. |
| `FLTForHuman/ModularForms/EichlerShimura/PeriodPrimitive.lean` (+1) | 11 | it is the home of `IsEquivariantPrimitive` and `periodHom`; the lemma is about those two objects only. |
| `FLTForHuman/ModularForms/EichlerShimura/PeriodOf.lean` (+1) | 12, and the `periodAlongOf_eq_sub` prelude (`periodAlongOf_eq_sub`, `hasDerivAt_affine`, `segmentPoint_eq_of_mem`), moved down here from `PeriodLatticeSpan` | `periodOf` and `periodMapOf` are defined there, so the unfolding lemma and its prelude are below everything that speaks about them. `PeriodLatticeSpan` imports `ExistsEquivariantPrimitive` → `PeriodOf`, so it cannot be the home of a lemma `PeriodOf` needs. |
| `FLTForHuman/ModularForms/EichlerShimura/ExistsEquivariantPrimitive.lean` (+1) | 7 | node 7's only proof is `ModularCurve.exists_hasEquivariantPrimitiveOf`, which lives here; `PeriodOf` is below it, so the statement cannot be made there. Pin statement unchanged. |

The coset decomposition (§5) has no pin statement and belongs beside its consumers:
`FLTForHuman/ModularForms/HeckeCosetDecomposition.lean`, public where two modules need it and `private` inside
it otherwise. It must not go in `GroupTheory/` — it is about `GammaHUpper` cosets — and it must not go
under `ModularCurve/Period/`, although nodes 1–3 live there: node 8 and 9's consumer
(`ModularForms/HeckeInvariance.lean`) is the *lower* of the two, and `ModularCurve/Period/` is above
`ModularForms/` (`PeriodLatticeSpan` imports `ModularForms/EichlerShimura/ExistsEquivariantPrimitive`).
Homing it beside nodes 1–3 would have made the wave's one upward import. The twenty
`ModularForms → ModularCurve` imports already in the port are mostly `ModularCurve/Defs/*`, a lower
layer that merely lives under that directory, so they are not a licence for `ModularCurve/Period/`.

## 5. Dedup before coding — the pin copies one coset block into four files

Measured on the twelve `S_` files (the pre-port view, `private` declarations included): **19 names
are proved in two or more of them, ≈1,031 removable lines**, and the two strongest factoring pairs
are inside this wave:

| prelude name | copies | removable | the pair |
|---|---:|---:|---|
| `sum_slash_beta_eq_heckeU_add` | 3 | 91 | 8 ↔ 9 |
| `bijective_option` | 3 | 158 | 8 ↔ 9 |
| `bijective_transl` | 4 | 153 | 8/9/1/2 |
| `sum_slash_beta_eq_heckeU` | 4 | 98 | 8/9/1/2 |
| `periodMapOf_eq_heckeT_of_apply_eq_sum` | 2 | 82 | 1 ↔ 2 |
| `mapGL_conjL_mul_heckeMatrix` | 4 | 75 | 8/9/1/2 |
| `sum_slash_beta_slash_eq` | 2 | 58 | 8 ↔ 9 |
| `heckeMatrix_zero_mul_mapGL_T_zpow_neg` | 4 | 57 | 8/9/1/2 |
| `hasDerivAt_comp_smul` | 3 | 47 | 1/2/+`comp` |
| `heckeMatrix_zero_mul_mapGL_gammaInf_inv` | 3 | 40 | 8/9/2 |
| `transl`, `gammaInf`, `Gamma_le_GammaH`, `exists_add_neg_eq_mul`, `exists_bezoutData`, `beta`, `BezoutData`, `rhoInf`, `rhoInf_apply_11`, `coe_transl` | 3–4 each | 36 + 28 + 28 + 21 + 16 + 12 + 8 + 10 + 4 + 6 | the `GammaHUpper` coset model |

That is the whole reason nodes 8, 9, 1, 2 are 481 + 489 + 357 + 591 lines: they are one coset
computation and one slash computation, each shipped four times. Written once, the wave's content is
≈1,300 lines rather than 2,366.

**The port already has 12 of the target declarations** (≈153 lines not to re-prove): `transl` is
`CohCarrier.uElt` up to binder spelling; `periodAlongOf_eq_sub`, `hasDerivAt_affine` and
`segmentPoint_eq_of_mem` are public in `ModularCurve/Period/PeriodOf.lean` (they had to move down from
`PeriodLatticeSpan`, which sits above `PeriodOf`); `apply_eq_apply_of_hasDerivAt_zero` in
`ModularForms/Analytic/CuspBoundedness.lean`; `hasDerivAt_comp_smul` is
`ModularCurve.PrimitiveConstructionOf.hasDerivAt_comp_smul` in
`ModularForms/EichlerShimura/ExistsEquivariantPrimitive.lean` (same name, different binder skeleton — read
both texts, do not assume); and `sub_eq_const_of_forall_hasDerivAt` exists in the port only as a
**`private`** declaration in that same module, and promotion is impossible (it is the same cycle), so it
is re-proved privately in `PeriodPrimitive.lean` in six lines over the public
`apply_eq_apply_of_hasDerivAt_zero`. Import, do not transcribe.

## 6. Budget

2,366 raw pin lines → −1,031 (shared prelude, net of its own ~900-line home) → ≈1,335 of content
+ ≈75 of definition tails + 105 for the optional sibling; at W1's measured written ÷ pin of 1.07 over
the **content**, expect **1,700–2,100 written lines** in the three new subject modules plus four
appended headlines, and **≈900 more** for `HeckeCosetDecomposition.lean`: **≈2,600–3,000 written in total**.
Node 2 (591) is the single large item; 8 and 9 are the two 480-line proofs; everything else is under
160.

This is the same shape as W1 and W2 — the pin lines say 2,366, the wave writes 2.6–3.0k, and most of
what it writes is the prelude once instead of four times.

## 7. Decisions

* **D1 (inherited).** Pinned statements are transcribed verbatim; local abbreviations never enter
  them. Headlines public at the pin's names, helpers `private` unless two modules need them.
* **D2 (new) — `coresHom` may be defined by the transfer, but only if the statement still
  elaborates.** The pin defines `HeckeEis.coresHom` as an explicit coset sum over `transferAux` and
  then proves it equals `MonoidHom.transfer` (node 10). The port's `ModularForms/Defs/CohCarrierLevel.lean`
  already has the transfer spelling (`coresAdd`). Two options: (a) transcribe the coset sum and keep
  node 10 as the pin has it (faithful, ~48 extra lines); (b) define `coresHom := coresAdd H` and let
  node 10 be near-definitional. **(a) is recommended**: (b) makes the `GroupTheory/` module import
  `ModularForms/`, which is the inversion §4 forbids, so (b) would force the module under
  `ModularForms/` and put a group-theory lemma in the modular layer. Take (b) only if the checker
  shows the pin's statement does not elaborate against the coset sum — and record the finding.
  *Measured:* `coresAdd` and its `coresAdd_zero`/`_add`/`_smul` are already in the transfer section of
  `ModularForms/Defs/CohCarrierLevel.lean`, so (a) does create two spellings of one object — the coset
  sum and the transfer — with node 10 as the named bridge between them, which is the pin's own
  arrangement. The new module's header must say so, and no third spelling is to be added.
* **D3 (new) — the `haveI : NeZero` in the statements is part of the statement.** Nodes 1 and 2
  state `haveI : NeZero q := ⟨hq.ne_zero⟩` before their conclusion. Keep it: the checker is
  text-level, and W2's statement-qualification lesson applies (inside a namespace, a statement must
  still spell the pin's qualified names — `ModularCurve.periodMapOf`, `CohCarrier.heckeT`,
  `CohCarrier.GammaH` — however the module's own `namespace` is set).
* **D4 (new) — drop the pin's instance/simp walls, and expect friction.** *Settled: all fifteen dropped,
  none needed (see the status note above).* Two of the twelve
  `Theorems/` wrappers — nodes 1 and 2, the only two whose proofs go through `heckeUpper` — open with
  `attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper` and a fourteen-entry `attribute [-simp]`
  list (`heckeConjMat_apply_one_one`, `coe_heckeConjSL`, `mem_heckeUpperSL`, `resHom_apply`,
  `coe_transferAux`, …). These are proof engineering for `heckeUpper`'s instance — the parent note's
  §5/§6 item, here on the `HeckeEis` side rather than the charted-space side. The port drops all
  fifteen and must not add them back: the wave does not define `heckeUpper`, `resHom` or
  `pullbackHom`, so most have no subject in the port at all. If a proof does not go through without
  one, record which and prefer a local `include`/`omit` or an explicit instance argument over
  re-adding a global `[-simp]`.
* **D5 (new) — `Stable*` predicates stay `def … : Prop`.** The pin states them as `def`, not
  `structure`; the checker compares a `def`'s type, which for `def foo : Prop := P` is just `Prop`
  (playbook §2.4's named false-positive), so their **bodies must be diffed by hand** against the pin
  before the wave is called green. Same for `BezoutData`.
* **D6 (new) — the optional fourth sibling.** Include
  `ModularCurve.periodMapOf_gammaH_eq_comp_of_coe_eq_slash` (+105) unless a reviewer objects. It is
  out of the 653 cone, so it is not *demanded*; it is recommended because it shares node 11's
  prelude, has four outbound citers, and leaving it out means the next wave re-opens this family.

## 8. Verification

Same wire as W2:

* `spec-pin:` headers for the twelve headlines (`Theorems/Thm_<…>` + `P2M/Sol/S_<…>`), with node 11's
  `Period_`-segmented path spelled exactly as the pin spells it — trust the pin's file names, not the
  pattern (W2's §3 correction);
* `spec/check_port.py` per module at `0 mismatch / 0 missing`, with no `SOURCES`/`PORT_FILES` edit to
  `spec/old_check_stmts.py`;
* `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all twelve;
* `#print axioms` on all twelve — and no mutation sweep: the wire compares statement text verbatim
  (`check_port`), one spot check suffices;
* `FLTForHuman/GroupTheory/Corestriction.lean` has **no `FLTForHuman` import** — a layering assertion,
  checkable with one `grep '^import FLTForHuman'`;
* the definition tails get a manual body diff against the pin (D5), since the checker sees `Prop`;
* `dedup.py` on the new `HeckeCosetDecomposition` module and `port_graph.py` after, not before, the modules
  close.

No new `Complex.*` node, no charted space, no analysis: this wave's risk is instance/simp friction
(D4) and statement spelling (D3), not mathematics.

## 9. Why not the smoothed-fundamental-set cluster — the deferred W4a

[PLAN-W2-parabolic-homs.md](PLAN-W2-parabolic-homs.md) §7 named the smoothed-fundamental-set / UHP
cluster as the natural W3, on the correct ground that it is where W1's `∂̄` layer is *consumed*.
Measured now, it is the largest premise-ready cluster (**13 nodes / 6,308 lines** around
`…exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental` 874) and it has 25 outbound
citers, three of them large (`eventually_abelFibreSumOf_sub_mem_periodLatticeOf` 1,547,
`HeckeEis.range_eichlerShimuraMap_inf_range_conj_eq_bot` 1,325,
`integral_petersson_gammaFundamentalSet_eq_sum_conj_periodOf_mul_edgeIntegral` 693). It is a real
gateway and it must be ported.

It is **not** the next wave, for two measured reasons — and the first draft of this section gave a
third that measurement has since retired, which is recorded rather than deleted because the
correction is the useful part.

1. **It is not a premise of the mouth.** It reaches the mouth through the winding-pairing / H₁
   generation chain (parent §10.1 row 2), i.e. *below* the two silos that stand between the port and
   the mouth (161 + 24 nodes). This block removes 7 of the mouth's 9 unported premises; the smoothed
   cluster removes none of them.
2. **It needs a definition module first.** `ModularCurve.smoothedFundamental` is
   [`Def_ModularCurve_SmoothedFundamental.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_SmoothedFundamental.lean)
   (187 lines), absent from the port entirely (`grep -r smoothedFundamental FLTForHuman/` is empty).
   The cluster is definition-first, and its definition is a bump-profile construction over the
   `GammaHUpper` cosets — the same coset model this block's `HeckeCosetDecomposition.lean` is about, so
   **W3b's prelude is the natural home for part of W4a's work, and that is a second reason to dispatch
   the two together**.

**Retired reason: "it carries a twin decision".** The cluster looks like it carries two `…Of…` / plain
twins (606 vs 606, 874 vs 926) needing the pre-code decision of parent §10.5 and playbook §2.4.
Measured on the cone, it does not: the **general-`Γ`** members are the ones in `needed(653)` (the
`…Of…` 606 and 874, both needed) and the **`Γ₀(N)`** instances are outside it (606 and 926, not
needed). A's port therefore writes the general family only and never transcribes the 1,532-line
`Γ₀(N)` pair — a scope fact, not a decision to take. What *is* open in that cluster is a different
thing: it is where [§10.4 item 3's rewire](#12-the-parents-104-deletions-and-why-this-block-is-neutral-to-them)
would land. That paragraph is the right home for it.

So the order is **W3b (this block) → W4a** (the smoothed/winding cluster, with the `smoothedFundamental`
definition module), and W3 stays shelved with the merged theory. The cluster's re-cut into W4a and W4b is
[PLAN-W3-honest-integral.md](PLAN-W3-honest-integral.md) §7: W4a is analysis that survives every decision,
and W4b — A's row-2, ≈4,025 — was the rewire surface, held until the reconciliation existed. With that
reconciliation deferred there is no rewire, so W4b is not held: it is an ordinary transcription of the
pin's proofs, taken after W4a and costed at its pin size. Deferring the cluster costs nothing either way:
its outbound citers are all still unported, so nothing waits on it.

## 10. What the wave unlocks

Measured outbound indegree (citers outside the 653 cone), which is the playbook's gain proxy:

| node | cone citers | project citers | first outside consumer |
|---|---:|---:|---|
| `CuspForm.stableD` | 3 | **54** | the X₁/diamond column |
| `CuspForm.stableU` | 2 | **26** | the `U_p`/newform column |
| `CuspForm.stableT` | 2 | **22** | the Hecke-degeneracy column |
| node 2 (591) | 1 | 11 | `…exists_injective_…periodLatticeOf_levelAut` and the Tate-level siblings |
| node 3 (158) | 1 | 8 | the diamond/Tate chain |
| node 1 (357) | 1 | 6 | the char-poly comparison column |
| node 12 (93) | 15 | 1 | the period-lattice span chain |
| nodes 10, 11 | 2 | 3–4 | `periodHom` consumers |

So the wave is not only A's: the three `Stable*` statements are among the most consumed nodes in the
port's remaining demand, and they are 13–24 lines each. It also fires, without satisfying, the
trigger [CARRY-FORWARD.md](../../CARRY-FORWARD.md) records on the deferred
`Def_ModularCurve_PeriodLattice.lean` `Hecke` section (`PeriodLatticeHeckeStable`,
`periodLatticeModule`): the Hecke-stability *consumers* are still unported, so that section stays
deferred — this wave states the equivariance of the period map, not the module structure on the
lattice.

## 11. First moves

1. `ModularForms/Defs/GammaH.lean` — append `StableD/U/T` (25 lines), manual body diff (D5). Nothing
   elaborates without this and it is a checkpoint by itself.
2. `GroupTheory/Corestriction.lean` — `transferAux`/`coresHom` and node 10 (D2 (a)), Mathlib-only
   imports; checkpoint B.
3. `PeriodPrimitive.lean` (11), then `PeriodOf.lean` (12, then 7) — the engine: four two-line
   statements over ported mathematics, completing checkpoints B and C. This is the natural first
   *dispatch*: it is small, it unblocks nodes 1, 2 and 3, and it exercises the statement spelling (D3)
   before the big ones.
4. `HeckeCosetDecomposition.lean` — the shared block, written **once**, from the 19 duplicated names; then
   nodes 8 and 9 in `HeckeInvariance.lean` against it (checkpoints E, F). Do not transcribe either
   480-line file before the prelude exists.
5. `HeckeStability.lean` (6, 5, 4 — checkpoints D and G), then `PeriodMapHecke.lean` (1, 3, then 2 —
   checkpoints H, I, J).
6. Optional: the fourth sibling (D6); then re-measure the mouth (`needed` should read 156 nodes and
   two unported direct premises) and re-price W4 with the measured written ÷ content ratio.

## 12. The parent's §10.4 deletions, and why this block is neutral to them

The four duplications §10.4 prices, read against `needed(653)` and against the corrected ordering
([PLAN-W3-honest-integral.md](PLAN-W3-honest-integral.md) §6):

| # | duplication | survivor | owner of the decision | does it touch W3b? |
|---|---|---|---|---|
| 1 | path integral | A's honest integral | **W3** (the general charted form; A's instance is ported) | no — none of the twelve names `pathIntegral` |
| 2 | period lattice | A's `periodLatticeOf` | already the port's shape | no — the twelve name `periodOf`/`periodMapOf`, not the lattice object |
| 3 | reciprocity / H₁ generation | B's general form | **W3's successor**: bridge + reconciliation + B's reciprocity | no — the twelve are the Hecke action on the period map |
| 4 | the genus | RR via `IsCurveOver` | already the port's shape (267) | no — no rank appears in the twelve |

So this block is **decision-neutral**, and here that is a positive property rather than an absence of
conflict: the subject still has two open definitional decisions (items 1 and 3, and their shared bridge),
and they are now deferred rather than scheduled, so a block that no outcome of them can invalidate is
exactly what the A-only port should write next.

**Two claims from this plan's first draft are withdrawn, and the corrections are recorded because they
are the substance of the rethink, not an erratum:**

* "**Item 3 is a P2 decision**" — withdrawn. It came from reading the citation cone: A's five row-2
  nodes are all `needed = True` (810, 1052, 596, 874, 693) and B's two (2,388 + 1,240) are
  `needed = False`. The measurement is right; the conclusion is not, because the subject is ordered by
  *definitions before consumers*, not by the cone. A's row-2 proofs are exactly what the bridge would
  rewrite, so item 3 is a **design** decision gated on the honest integral plus the reconciliation — and
  it is prior to A's row-2 even though no edge points at it.
* "**The bridge is a pre-B wave, not a pre-A one**" — withdrawn for the same reason: "no A-cone
  consumer" is a citation-graph fact, while the question is a writing-order fact. The bridge is prior to
  **both** halves' item-1/item-3 consumers.

What survives from that draft and still belongs in W4's plan:

* **Write the general-`Γ` statement and not the instance.** The members of `needed(653)` are the `…Of…`
  general ones; the `Γ₀(N)` pair (606 + 926) is outside the cone, so A's port never transcribes those
  1,532 lines. A scope fact, not a saving.
* **Label the rewire surface.** Inside W4's cluster three nodes are A's row-2 family
  (`exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom` 810, the
  winding-pairing 874, the Petersson 693 — 2,377 lines), and two more sit just outside (1052, 596 —
  1,648). Those five are what a B-shaped reciprocity rewrites; W4's header must say so.
* **Item 1's positive half.** A's `periodOf`/`periodAlongOf` is the survivor, which is why W1's analysis
  — and W4a's ∂̄-over-the-domain computation — are worth writing at all.
