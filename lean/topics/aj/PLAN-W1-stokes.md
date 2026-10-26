# W1 — the shared ∂̄/Stokes layer, as a mathlib supplement

First wave of the aj subject, 2026-10-26. Parent note:
[../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md) (§10.2, §10.4, §12.2).
Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

**Decision.** Port this layer first, before either half of the subject, and build it as a **mathlib
supplement**. Its statements quantify over an arbitrary open `U ⊆ ℂ`, a `C¹` (or `C²`) compactly
supported test function and a locally meromorphic `F` — no curve, no place, no chart, no dissection
(parent §12.2). So it homes under `FLTForHuman/Analysis/Complex/`, not under `AlgebraicCurve/` or
`ModularCurve/`, and it is the one block of the subject that is upstreamable as written.

**Why first, on the parent's own criterion.** Parent §10.4 prices a node by the definitions it deletes.
Three of the subject's four duplications — the path integral, the period lattice, the reciprocity
family — need this layer as their bridge: it is what replaces B's primitive-based `pathIntegral`
(§10.2, ≈8.9k pin lines) and what A's lattice statements are written against. Building it inside P1 is
not an optimisation; a definition transcribed against cannot be deleted later (§10.5).

**Status: W1 is landed and tidied (2026-10-26).** All nine headlines green in five new modules, **2,768
written lines** for 2,624 pin lines (`check_port.py --all`: 5845 ok, 0 mismatch, 0 missing, 266 modules;
`#print axioms` clean on all nine). Written ÷ pin came in at **1.07**, above the 2,300–2,600 estimate
below: this wave bought structure, not lines — the pin's 2,624 lines were spread over nine silos with
duplicated private preludes, and the port has five deduped, mathlib-shaped modules with 19 public
declarations and 140 private helpers. The eight glue helpers the two modules had duplicated live once,
publicly, in `Dbar.lean` (the ∂̄/`tsupport` API); `dedup.py` over the three modules reports 0 clusters,
0 removable lines.

## 1. Scope and measurement

The nine `Complex.*` nodes both mouths reach: 2,624 raw pin lines (`frontier` union frontier, 1,212
ported nodes). **Their union demand is exactly themselves** — each needs 1–4 new nodes, and no other
pin node is pulled in.

| # | pin node | lines | content | home |
|---|---|---:|---|---|
| 1 | `locallyIntegrableOn_of_simplePoles` | 74 | `F =ᶠ[𝓝[≠] a] c a/(z−a) + analytic` at every `a ∈ U` ⇒ `LocallyIntegrableOn F U` | `DbarPompeiu` |
| 2 | `integral_mul_dbar_eq_zero_of_differentiableOn` | 90 | `G` holomorphic on open `V`, `tsupport h ⊆ V`, `h` C¹: `∫ G·∂̄h = 0` | `DbarPompeiu` |
| 3 | `integral_inv_sub_mul_dbar_eq_neg_pi_mul` | 463 | `∫ (z−a)⁻¹·∂̄h = −π·h a` — Cauchy kernel, the fundamental solution of ∂̄ | `DbarPompeiu` |
| 4 | `integral_mul_dbar_eq_neg_pi_mul_finsum_residue` | 306 | simple poles, residues `c a`: `∫ F·∂̄h = −π·∑ᶠ a, c a * h a` | `DbarPompeiu` |
| 5 | `integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum` | 98 | `F` meromorphic: `∫ E·(deriv F/F)·∂̄h = −π·∑ᶠ a, ordₐF · E a · h a` | `DbarResidue` |
| 6 | `integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv` | 643 | `Φ = (z−τ)^{n τ}·Ψ`: integrability of both integrands **and** the identity | `DbarResidue` |
| 7 | `integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt` | 639 | Green over the modular region; boundary = two vertical rays + the arc `e^{iθ}`, θ ∈ [π/3, 2π/3] | `ModularCurve/Analytic` |
| 8 | `circleIntegral_eq_sum_residue_of_simplePole` | 142 | the residue formula in `circleIntegral` form | `CircleResidue` |
| 9 | `hasDerivAt_circleIntegral_mul_deriv_div_sub` | 169 | `z ↦ circleIntegral` of `f'/(f−z)` is differentiable | `CircleResidue` |

Nodes 8–9 are B0's and are in this wave because they are the same content in the circle-integral
setting — together with 1–7 they are exactly the parent's "9 `Complex.*` nodes / 2,624 lines" (§5) and
the analytic half of the A∩B prelude (§9.2).

## 2. Order

```
2 (90) ── 3 (463) ─┬─ 4 (306) ── 5 (98)
                   └─ 6 (643)
1 (74)   independent leaf — consumed by the 1,383-line residue lemma, not by 4
7 (639)  independent — the region, not the ∂̄ identity
8, 9     independent of 1–7 and of each other (circleIntegral only)
```

(The pin's own citation graph, not a reading: `4` cites `2` and `3`, `5` cites `4`, `6` cites `3`,
`3` cites `2`; `1` and `7` cite nothing in the cluster.)

Checkpoints, each a green module: **A** = 1 + 2, **B** = 3, **C** = 4 + 5, **D** = 6, **E** = 7,
**F** = 8 + 9. D (643) is more than half the wave's lines and should not share a checkpoint with
anything else.

## 3. Mathlib gap (recorded)

Has: `circleIntegral` and the Cauchy theorem / integral formula
(`Mathlib/Analysis/Complex/CauchyIntegral.lean`), `fderiv`, `ContDiff`, `HasCompactSupport`/`tsupport`,
`MeromorphicAt`/`meromorphicOrderAt`, `deriv`, the 2-D Lebesgue measure on `ℂ`, `intervalIntegral`,
`ModularGroup.𝒟` and `truncatedFundamentalDomain` (`NumberTheory/Modular.lean`).

Does **not** have (searched 2026-10-26): any ∂̄/Wirtinger derivative or Pompeiu identity — no
`dbar`/`Pompeiu`/`Wirtinger` occurrence anywhere in `Mathlib/`; no local integrability of simple poles;
no divergence theorem for the modular region; no residue formula in `circleIntegral` form. The wave is
therefore new *statements* for mathlib built entirely from existing mathlib objects, which is what makes
"supplement" the correct homing rather than a courtesy.

## 4. Homing — by subject, not by silo

The nine statements are analysis; they are homed where mathlib homes the subject they extend, never in
a module named after the pin's chapter or after A/B:

| module | nodes | why it is the natural home |
|---|---|---|
| `FLTForHuman/Analysis/Complex/Dbar.lean` | — (vocabulary) | the `∂̄` operator itself, `dbar h z = (fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2`; no pin node, no wire. Lands first, manager-written. |
| `FLTForHuman/Analysis/Complex/Pompeiu.lean` | 1–4 | extends the subject of mathlib's `Analysis/Complex/CauchyIntegral.lean`: ∂̄ and its `1/(z−a)` kernel. Statements quantify over an arbitrary open `U ⊆ ℂ`; no FLT name is in scope. |
| `FLTForHuman/Analysis/Complex/MeromorphicResidue.lean` | 5–6 | the log-derivative / `meromorphicOrderAt` form of the same identity: it belongs with mathlib's meromorphic API, not with a curve. |
| `FLTForHuman/Analysis/Complex/CircleIntegralResidue.lean` | 8–9 | the `∮` (`circleIntegral`) residue formulas — a supplement to `CauchyIntegral.lean` itself. |
| `FLTForHuman/ModularForms/FundamentalDomainStokes.lean` | 7 | the only one whose hypothesis is a *domain* rather than an arbitrary `U`: the modular fundamental domain. The port already keeps its upper-half-plane analysis under `ModularForms/`, and the region is the object integrated over. |

Naming rule: paths are mathematical (`Pompeiu`, `MeromorphicResidue`, `CircleIntegralResidue`,
`FundamentalDomainStokes`); no `W1`/`aj`/`FLT`/pin-chapter token in a path or a declaration name.
Traceability to the pin lives in the `spec-pin:` header line, not in the directory.

**Completeness, not consumers.** These are mathlib-shaped modules, so they may house a theorem that
has no port-side consumer yet — `move_dead.py` would shelve exactly the statements the wave exists for.
The modules of this wave are **exempt from the strict `move_dead` pass**: run `dedup.py`, do not run
`move_dead.py` on them, and treat a zero-citer residue formula as completeness rather than dead
content.

The `dbar` abbreviation (`dbar h z = (fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2`) is the one new
definition, and by D1 it appears only in port-internal lemmas — never in a `spec-pin`ed statement.

## 5. Budget

2,624 raw pin lines → ≈1,900 content at the parent's written ÷ content ratio; expect **2,300–2,600
written lines** over the five modules, of which the unpinned `Dbar.lean` is organisation only
(≈120–200). Node 6 (643) is the single large item; nodes 1, 2, 5, 8 are small.

## 6. Decisions to take before coding

* **D1 — no new definition inside a pinned statement.** The pin spells `∂̄` inline as
  `(fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2`. The nine statements are ported verbatim so the
  `spec-pin:` diff is byte-comparable; `dbar` is used only in port-internal lemmas. If a later wave
  wants `dbar` in statements, the checker's statement normalisation must be extended first (playbook §4).
* **D2 — `finsum` support.** Nodes 4–6 sum over all `a : ℂ` with no support hypothesis, so the identity
  is only informative when the support is finite. Keep the pinned statement unchanged and add
  *unpinned* `Finset`-restricted corollaries for the consumers (they always instantiate with a finite
  divisor).
* **D3 — "wedge" is a determinant.** Node 6's integrand is
  `fderiv Φ 1 * fderiv h I − fderiv Φ I * fderiv h 1`, a 2×2 Jacobian determinant, not a differential
  form. Port as written; keep the pin's name for the wire.
* **D4 — node 7's region.** The pin spells the fundamental domain by inequalities
  (`|z.re| ≤ 1/2`, `1 ≤ ‖z‖`, `0 < z.im`), i.e. `ModularGroup.𝒟` in ℂ coordinates. State the pin's
  version (the wire needs it), record the correspondence with `𝒟` in the module comment, and do not
  restate against `𝒟`.
* **D5 — `deriv` vs `HasDerivAt`.** Nodes 5 and 9 use `deriv` and `HasDerivAt` respectively; keep each
  as the pin has it rather than normalising.

## 7. Verification

* each of the nine modules carries `spec-pin: P2M/Sol/S_Complex_<name>.lean` for its headline (all nine
  `S_` files exist; the statements are the `Theorems/Thm_Complex_<name>.lean` wrappers);
* `spec/check_port.py` at `0 mismatch / 0 missing` per module;
* `#print axioms` = `[propext, Classical.choice, Quot.sound]` on every headline;
* **upstreamability check**: grep each of the nine statements for pin-local vocabulary
  (`ComplexPlaceDictionary`, `periodAlongOf`, `periodLatticeOf`, `UpperHalfPlane`); nodes 1–6, 8–9 must
  be free of it, node 7 may mention only the region. A hit means the statement is not
  mathlib-supplemental after all and has to move.

## 8. What the wave unlocks (measured consumers)

| node | citers | first consumer |
|---|---:|---|
| 7 (639) | 6 | `ModularCurve.integral_petersson_gammaFundamentalSet_eq_sidePairing` 841, `HeckeEis.range_eichlerShimuraMap_inf_range_conj_eq_bot` 1,325 |
| 6 (643) | 3 | `ModularCurve.exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental` 874 |
| 5 (98) | 2 | `ModularCurve.exists_mem_periodLatticeOf_sum_periodAlongOf_add_petersson_eq_of_multiplier_eq_…` 606 |
| 4 (306) | 1 | `UpperHalfPlane.levelOne_sum_residue_div_card_stabilizer_eq_zero` 1,383 |
| 3 (463) | 0 | internal only |
| 2 (90) | 2 | the two 606 Petersson/multiplier lemmas |
| 1 (74) | 1 | the 1,383 residue lemma |
| 8 (142) | 5 | `ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf` 1,547, B's `eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice` 1,115 |
| 9 (169) | 4 | the same two, plus `AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_…` 1,340 |

So the wave is the gate on the Petersson/side-pairing chain, the winding-pairing chain, and both
halves' Abel–Jacobi well-definedness lemmas — i.e. on everything the period theory does.

## 9. First moves

1. `Dbar.lean` — operator, vanishing criterion, `tsupport`/`ContDiff` transfer; no wire.
2. Node 2 (90) and node 1 (74) — both leaves, checkpoint A (node 1 does not feed node 4; it is kept
   here because it is the same local-analysis vocabulary and is separately consumed).
3. Node 3 (463) — the Cauchy kernel, checkpoint B; it is the technical centre of the wave.
4. Node 4 (306), then node 5 (98) — checkpoint C.
5. Node 6 (643) alone — checkpoint D.
6. Node 7 (639) in `ModularCurve/Analytic/` — the only item that can run in parallel with 2–5 (it is
   independent of the ∂̄ identity), checkpoint E.
7. Nodes 8–9 — the safe tail, checkpoint F.
