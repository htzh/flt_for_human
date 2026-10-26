# W3b — the Hecke-equivariance layer of the period map

Companion to the third wave of the aj subject, 2026-10-26 — **W3b, dispatchable in parallel with W3**
([PLAN-W3-honest-integral.md](PLAN-W3-honest-integral.md), the honest charted-surface integral). The two
share no file and neither blocks the other. Parent note:
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

**Why this block is in the third wave at all, under the corrected criterion.** The subject is ordered
by [§10.4](../TOPIC-abel-jacobi-port-structure.md#104-the-criterion-is-simplicity-not-verification)'s
simplicity, not by distance to A's mouth: definitional survivors first, consumers after. W3 is the one
missing survivor (the honest integral, [PLAN-W3-honest-integral.md](PLAN-W3-honest-integral.md)). This
block is the third wave's *second set* because it is the largest premise-ready block that is
**no-regret** — it commits to no side of any survivor decision (§12), so the scout that W3 must run
cannot invalidate it, and it can be transcribed while that scout runs. The facts below (12 nodes /
2,366 lines, closed, 7 of the mouth's 9 unported direct premises) are why it is worth dispatching, not
why it is third.

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
| `FLTForHuman/ModularForms/EichlerShimura/PeriodOf.lean` (+2) | 7, 12 | `periodOf` and `periodMapOf` are defined there; both are their unfolding lemmas. |

The shared coset/Bezout prelude (§5) has no pin statement and belongs beside its consumers:
`FLTForHuman/ModularCurve/Period/HeckeCosetPrelude.lean`, public where two modules need it and
`private` inside it otherwise. It must not go in `GroupTheory/` — it is about `GammaHUpper` cosets.

## 5. Dedup before coding — the pin copies one prelude into four files

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
`segmentPoint_eq_of_mem` are public in `ModularCurve/Period/PeriodLatticeSpan.lean`;
`apply_eq_apply_of_hasDerivAt_zero` in `ModularForms/Analytic/CuspBoundedness.lean`;
`hasDerivAt_comp_smul` is `ModularCurve.PrimitiveConstructionOf.hasDerivAt_comp_smul` in
`ModularForms/EichlerShimura/ExistsEquivariantPrimitive.lean` (same name, different binder skeleton — read
both texts, do not assume); and `sub_eq_const_of_forall_hasDerivAt` exists in the port only as a
**`private`** declaration in that same module, so it must be promoted or re-proved. Import, do not
transcribe.

## 6. Budget

2,366 raw pin lines → −1,031 (shared prelude, net of its own ~900-line home) → ≈1,335 of content
+ ≈75 of definition tails + 105 for the optional sibling; at W1's measured written ÷ pin of 1.07 over
the **content**, expect **1,700–2,100 written lines** in the three new subject modules plus four
appended headlines, and **≈900 more** for `HeckeCosetPrelude.lean`: **≈2,600–3,000 written in total**.
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
* **D3 (new) — the `haveI : NeZero` in the statements is part of the statement.** Nodes 1 and 2
  state `haveI : NeZero q := ⟨hq.ne_zero⟩` before their conclusion. Keep it: the checker is
  text-level, and W2's statement-qualification lesson applies (inside a namespace, a statement must
  still spell the pin's qualified names — `ModularCurve.periodMapOf`, `CohCarrier.heckeT`,
  `CohCarrier.GammaH` — however the module's own `namespace` is set).
* **D4 (new) — drop the pin's instance/simp walls, and expect friction.** Two of the twelve
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
* one mutation test per headline (statement-level, reverted, hash verified);
* `FLTForHuman/GroupTheory/Corestriction.lean` has **no `FLTForHuman` import** — a layering assertion,
  checkable with one `grep '^import FLTForHuman'`;
* the definition tails get a manual body diff against the pin (D5), since the checker sees `Prop`;
* `dedup.py` on the new `HeckeCosetPrelude` module and `port_graph.py` after, not before, the modules
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
   `GammaHUpper` cosets — the same coset model this block's `HeckeCosetPrelude.lean` is about, so
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

So the order is W3 (the honest integral) ∥ W3b (this block) → W4a (the smoothed/winding cluster, with
the `smoothedFundamental` definition module). The cluster's re-cut into W4a and a *held* W4b is
[PLAN-W3-honest-integral.md](PLAN-W3-honest-integral.md) §7, and it is the honest integral that decides
it: W4a is analysis that survives every decision, W4b (A's row-2, ≈4,025) is the rewire surface and is
not scheduled until the reconciliation exists. Deferring the cluster costs nothing: its outbound citers
are all still unported, so nothing waits on it.

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
4. `HeckeCosetPrelude.lean` — the shared block, written **once**, from the 19 duplicated names; then
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
and a block that no outcome of those decisions can invalidate is the right thing to dispatch beside
W3's scout.

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
