# WORKORDER-D2 — the period map of a finite-index subgroup

**Status: ready to dispatch.** Second of the two remaining subject sets off the `ModularCurve`
ready shelf (the other is [WORKORDER-D1](WORKORDER-D1-petersson.md)). **New files only**; no
existing Lean module is edited; no new definition layer (the period API is already ported).

| order | module | headline | `S_` file |
|---|---|---|---|
| 1 | `FLTForHuman/ModularCurve/Period/PeriodLatticeSpan.lean` | `ModularCurve.addSubgroupClosure_range_periodAlongOf_eq_top` | 263 |
| 2 | `FLTForHuman/ModularCurve/Period/PeriodLatticeBoundary.lean` | `ModularCurve.sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero` | 237 |
| 3 | `FLTForHuman/ModularCurve/Period/ParabolicHoms.lean` | `ModularCurve.periodMapOf_mem_parabolicHoms` | 91 |
| 4 | `FLTForHuman/ModularCurve/Period/QExpansionDerivative.lean` | `ModularCurve.coe_qExpansion_normalizedDerivOfComplex` | 247 |

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Checker baseline
**7371 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 37 own (7408 checked)**.
Target: `+4` identical, helpers `private`, `0 mismatched / 0 missing`.

## 1. The mathematics

The four headlines are the period-map layer of a finite-index `Γ ≤ SL(2, ℤ)`:

* the periods `periodAlongOf Γ τ₁ τ₂` of `S₂(Γ)` span the whole dual — the period pairing is
  non-degenerate;
* an integer combination of periods whose boundary sum vanishes lies in the period lattice
  `periodLatticeOf Γ`;
* `periodMapOf Γ f` lands in the parabolic cocycles `Period.parabolicHoms ℂ Γ ℂ`;
* the `q`-expansion of the normalized derivative of a periodic, holomorphic, bounded-at-`i∞`
  function is `thetaL` applied to its `q`-expansion.

One story in one layer: the period map and its lattice. If the set runs long, orders 1+2 and 3+4
are the natural halves, but they share the period API and one wave each.

## 2. The statements (verbatim from the wrappers)

```lean
theorem ModularCurve.addSubgroupClosure_range_periodAlongOf_eq_top
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    AddSubgroup.closure
        (Set.range fun p : UpperHalfPlane × UpperHalfPlane =>
          ModularCurve.periodAlongOf Γ p.1 p.2) =
      (⊤ : AddSubgroup (Module.Dual ℂ (CuspForm Γ 2)))

theorem ModularCurve.sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (Z : (ℍ × ℍ) →₀ ℤ)
    (hZ : ∀ τ : ℍ, Z.sum (fun e m => ...) = 0) :
    (Z.sum fun e m => m • ModularCurve.periodAlongOf Γ e.1 e.2) ∈
      ModularCurve.periodLatticeOf Γ

theorem ModularCurve.periodMapOf_mem_parabolicHoms (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2) :
    ModularCurve.periodMapOf Γ f ∈ ModularCurve.Period.parabolicHoms ℂ Γ ℂ

theorem ModularCurve.coe_qExpansion_normalizedDerivOfComplex (F : ℍ → ℂ)
    (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) :
    ((UpperHalfPlane.qExpansion 1 (Derivative.normalizedDerivOfComplex F) : PowerSeries ℂ) :
        LaurentSeries ℂ) =
      ModularCurve.thetaL ℂ ((UpperHalfPlane.qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ)
```

Read the wrappers for the exact text of the boundary condition in the second theorem and for
`theorem solution`; transcribe verbatim, including `ℍ` vs `UpperHalfPlane`.

## 3. Premise homes

| pin premise | port home |
|---|---|
| `periodAlongOf` | `ModularForms/EichlerShimura/PeriodOf.lean` |
| `periodLatticeOf`, `periodMapOf`, `Period.parabolicHoms` | `ModularForms/EichlerShimura/PeriodPrimitive.lean` |
| `Derivative.normalizedDerivOfComplex`, `UpperHalfPlane.petersson` | mathlib (`NumberTheory/ModularForms/{Derivative,Petersson}.lean`) |

**Correction (found during implementation; the original §3 was wrong).** `ModularCurve.thetaL`,
`thetaL_apply` and `theta_coeff` are **not** ported — a declaration grep settles it;
`IntegralWeightOneForm.lean` contains only the unrelated private `thetaLikeSeries`, which a
substring search had mistaken for the real name. Their pin homes are
`Definitions/Def_ModularCurve_QExpansionDiff.lean` (§`Theta`) and
`Theorems/Thm_ModularCurve_theta_coeff.lean`, both unported, so order 4 does carry a small
definition layer: port the pin's `Def_ModularCurve_QExpansionDiff.lean` **whole** — its three
subjects are the `thetaL` pair (homed in `Period/QExpansionDerivative.lean`), the
`QExpansionDiff` pair (`Period/QExpansionDiff.lean`) and the `TraceDiff` pair
(`AlgebraicCurve/Differential/TraceDiff.lean`) — and add
`Definitions/Def_ModularCurve_QExpansionDiff.lean` plus
`Theorems/Thm_ModularCurve_theta_coeff.lean` to `SOURCES`.

`port_advise` reports **no substitutions and no suspect `def`-`Prop` rows** for this set. Three
shared names inside it are public because orders 1 and 2 are separate modules: `hasDerivAt_affine`,
`segmentPoint_eq_of_mem` and `periodAlongOf_eq_sub` (the last is order 2's differently-named
`periodAlong_eq_sub`, invisible to `port_advise`'s last-name matching). Order 4's
`coe_qExpansion_normalizedDerivOfComplex` is its own headline — write it once, publicly, at its
pin name.

## 4. Build discipline

`lake env lean <file>` is the edit loop; `lake build <module>` when a file is done; **no whole-tree
build**. Bound everything: `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false
<file>`, `flock .lake/flt_build.lock timeout 300 lake build <module>`. Never raise
`maxHeartbeats`/`maxRecDepth`; on a timeout quarantine and bisect, and tell a blow-up from
contention by CPU time. Serial builds only. Do not commit.

## 5. The hub prohibition

**Do not edit any existing Lean module.** If a needed helper is `private` in a hub (`Gamma1`-related
helpers may sit `private` in `ModularForms/WeightOne/Gamma1IntegralBasis.lean`), re-derive it
locally as `private` and report it. If a promotion seems genuinely required, **stop and report**
with the declaration, host, reason and `python3 tools/deps/build_ladder.py --edit <host>` — the
manager decides.

## 6. Wiring

Append to `SOURCES` each target's `Theorems/Thm_ModularCurve_<stem>.lean` and
`P2M/Sol/S_ModularCurve_<stem>.lean`; append each new module to `PORT_FILES`; both last. Run the
checker as soon as each module is written (text-only, no build) and reconcile the `identical`
delta to the new public surface before building; mutation-test each headline and revert.

## 7. Stop and report

If a statement cannot be matched without moving the pin's text; if a premise home in §3 is wrong
(report the real host); if a helper is genuinely needed publicly and is `private` in a hub; or if a
build exceeds its bound and bisecting does not settle it.

## 8. Completion report

Module paths and line counts; public/`private` counts; tier-0 warnings (target **0**) and wall/CPU;
tier-1 result; every local `private` re-derivation with its host; the checker before → after with
the `identical` delta reconciled and a mutation result per headline; `#print axioms` for each
headline (`[propext, Classical.choice, Quot.sound]`); `git status --porcelain` showing only the
set's files; anything you could not match, quoted.

## 9. Outcome (landed; manager-reviewed and wired)

Six new modules, **1,274 lines** — the four period modules from the implementer plus the two
that complete `Def_ModularCurve_QExpansionDiff`; no existing Lean module edited, nothing committed.

| module | lines | public | private |
|---|---:|---:|---:|
| `ModularCurve/Period/PeriodLatticeSpan.lean` | 317 | 4 | 11 |
| `ModularCurve/Period/PeriodLatticeBoundary.lean` | 206 | 1 | 13 |
| `ModularCurve/Period/ParabolicHoms.lean` | 118 | 1 | 5 |
| `ModularCurve/Period/QExpansionDerivative.lean` | 316 | 4 | 9 |
| `ModularCurve/Period/QExpansionDiff.lean` (manager) | 42 | 2 | 0 |
| `AlgebraicCurve/Differential/TraceDiff.lean` (manager) | 38 | 2 | 0 |

All six elaborate at tier 0 with **0 errors and 0 warnings**; the implementer's four built at
tier 1 in 3–5 s. Combined checker **7417 → 7431 identical** (+10 for the set, +4 for the node
completion), 0 mismatched, 0 missing; a statement mutation on each of the four headlines was
caught and reverted. `#print axioms` on all four headlines:
`[propext, Classical.choice, Quot.sound]`. Milestone whole-tree build green (**9,370 jobs**).

**The §3 correction was real and is now recorded there.** The implementer caught that `thetaL`
was unported (my substring grep had matched `thetaLikeSeries`), transcribed the `thetaL` pair and
`theta_coeff`, and flagged it rather than aborting. The manager then completed the node: the
pin's `Def_ModularCurve_QExpansionDiff.lean` is ported whole across its three subjects, and
`Algebra.trace` needed an explicit `Mathlib.RingTheory.Trace.Defs` import (not transitive here).

**Whole-node lesson for the next cut.** The `thetaL` half of a definition module looked like the
whole prerequisite; the `QExpansionDiff` and `TraceDiff` halves had no consumer in this set but do
have pin consumers, so the node is only ported when all three are in — exactly the partial-port
failure mode §2.3 of the playbook warns about, and `port_advise`'s per-target view does not show
it. Check the whole pin `Def_*` file against the port, not just the imported names.
