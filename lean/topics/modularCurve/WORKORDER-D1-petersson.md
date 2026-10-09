# WORKORDER-D1 — the Petersson pairing is perfect

**Status: ready to dispatch.** First of the two remaining subject sets off the `ModularCurve`
ready shelf (the other is [WORKORDER-D2](WORKORDER-D2-period-map.md)). **New files only**; no
existing Lean module is edited. The set has two phases: its definition layer, then the pair.

| phase | modules | headline(s) |
|---|---|---|
| 1 | `FLTForHuman/AutomorphicForm/{HyperbolicMeasure,FundamentalDomainVolume,SiegelSetCover,Gamma0FundamentalSet}.lean` | the pin's four `Definitions/Def_AutomorphicForm_*` modules, whole |
| 2 | `FLTForHuman/ModularCurve/Analytic/PeterssonPairing.lean` | `ModularCurve.exists_cuspForm_petersson_eq_gammaH`, `ModularCurve.exists_cuspForm_petersson_eq_of_finiteIndex` |

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Checker baseline
**7371 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 37 own (7408 checked)**.
Target: `+2` identical (one per headline) with the helpers `private`.

## 1. Phase 1 — the definition layer (port whole, no promotions)

The pin's `Def_AutomorphicForm_Gamma0FundamentalSet.lean` (123 lines) is unported, and so are its
three dependencies; none has a port counterpart. Port all four **whole**:

| pin module | lines | namespace | imports |
|---|---:|---|---|
| `Definitions/Def_AutomorphicForm_HyperbolicMeasure.lean` | 129 | `FLT.HyperbolicMeasure` | `Mathlib` |
| `Definitions/Def_AutomorphicForm_FundamentalDomainVolume.lean` | 178 | `FLT.FundamentalDomainVolume` | HyperbolicMeasure |
| `Definitions/Def_AutomorphicForm_SiegelSetCover.lean` | 113 | `FLT.SiegelSetCover` | HyperbolicMeasure |
| `Definitions/Def_AutomorphicForm_Gamma0FundamentalSet.lean` | 123 | `FLT.Gamma0FundamentalSet` | both |

Keep the pin's namespaces (`FLT.…`) even though the port has no `FLT/` area yet; the file path and
the namespace need not agree. Statements verbatim; adapt proof bodies to `v4.34.0`. The pin's
`import Mathlib` becomes specific imports. `Def_AutomorphicForm_Gamma0FundamentalSet` supplies
`gammaFundamentalSet`, `truncatedGammaFundamentalSet` and their volume/compactness lemmas, which
phase 2 names in its headline.

## 2. Phase 2 — the pair

**The mathematics.** The Petersson inner product on `CuspForm Γ 2` makes the period pairing
`f ↦ (g ↦ I * ∫_{gammaFundamentalSet Γ} petersson 2 f g)` an antilinear isomorphism onto the dual:
every continuous functional is represented by a cusp form. The two headlines are the same
statement for `Γ = Γ_H(M)` and for a general finite-index `Γ`.

**Statements (verbatim from the wrappers).**

```lean
theorem ModularCurve.exists_cuspForm_petersson_eq_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)) :
    ∃ f : CuspForm (CohCarrier.GammaH M H) 2,
      ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = ℓ g

theorem ModularCurve.exists_cuspForm_petersson_eq_of_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (ℓ : Module.Dual ℂ (CuspForm Γ 2)) : ∃ f : CuspForm Γ 2, ∀ g : CuspForm Γ 2,
      Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = ℓ g
```

*(Read the wrappers for the exact binder text of the second theorem; the first is quoted from
`Theorems/Thm_ModularCurve_exists_cuspForm_petersson_eq_gammaH.lean`.)*

**Shared prelude — write once, before either headline.** `port_advise` reports 21 shared names,
≈216 removable lines, all in this pair: `Bform`, `B_self_eq`, `B_add_left`, `B_add_right`,
`B_smul_left`, `B_smul_right`, `B_sum_conj_smul_left`, `B_sum_smul_right`,
`petersson_two_self_apply`, `integrable_petersson`, `gram`, `gram_injective`,
`eq_zero_of_B_self_eq_zero`, plus the Hermitian-form algebra around them. Write them once,
`private`, in the phase-2 module (or a small `private` namespace inside it).
There are **no substitutions** (`port_advise` reports none for this set) and no suspect
`def`-`Prop` rows.

## 3. Build discipline

`lake env lean <file>` is the edit loop; `lake build <module>` when a file is done; **no whole-tree
build**. Bound everything: `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false
<file>`, `flock .lake/flt_build.lock timeout 300 lake build <module>`. Never raise
`maxHeartbeats`/`maxRecDepth`; on a timeout quarantine and bisect, and tell a blow-up from
contention by CPU time. Serial builds only. Do not commit.

## 4. The hub prohibition

**Do not edit any existing Lean module.** Phase 1 creates new files; if a needed helper is
`private` in a hub, re-derive it locally as `private` and report it. If a promotion seems
genuinely required, **stop and report** with the declaration, host, reason and
`python3 tools/deps/build_ladder.py --edit <host>` — the manager decides.

## 5. Wiring

Append to `SOURCES` the pin source(s) each new module ports (the `Theorems/` wrapper and the
`S_` file for the two headlines; the `Definitions/Def_AutomorphicForm_*.lean` files for phase 1).
Append each new module to `PORT_FILES`. Both last. Run the checker after each phase; phase 1
should leave the `identical` count unchanged only if its declarations are named like the pin's —
check the delta against the pin `Definitions/` files and reconcile it.

## 6. Stop and report

If a statement cannot be matched without moving the pin's text; if a phase-1 module's proof needs
an unported `Definitions/` module beyond the four listed (report the import verbatim); if a helper
is genuinely needed publicly and is `private` in a hub; or if a build exceeds its bound and
bisecting does not settle it.

## 7. Completion report

Module paths and line counts; public/`private` counts; tier-0 warnings (target **0**) and wall/CPU;
tier-1 result; every local `private` re-derivation with its host; the checker before → after with
the `identical` delta reconciled and a mutation result per headline; `#print axioms` for both
headlines (`[propext, Classical.choice, Quot.sound]`); `git status --porcelain` showing only the
set's files; anything you could not match, quoted.

## 8. Outcome (landed; manager-reviewed and wired)

Five new modules, **893 lines**, no existing Lean module edited, nothing committed. The
implementer did not return a report, so the review was done by the manager.

| module | lines | public | private |
|---|---:|---:|---:|
| `AutomorphicForm/HyperbolicMeasure.lean` | 147 | pin's declarations | 7 |
| `AutomorphicForm/FundamentalDomainVolume.lean` | 195 | pin's declarations | 5 |
| `AutomorphicForm/SiegelSetCover.lean` | 129 | pin's declarations | 1 |
| `AutomorphicForm/Gamma0FundamentalSet.lean` | 139 | pin's declarations | 0 |
| `ModularCurve/Analytic/PeterssonPairing.lean` | 283 | 2 headlines | 20 |

All five elaborate at tier 0 with **0 errors and 0 warnings**. Checker **7371 → 7417
identical** (+46: the four definition modules whole plus the two headlines), 0 mismatched,
0 missing. One-token mutation on the `gammaH` headline gave 7416/1/0 and the revert restored
7417/0/0. Tier-1 build green (3,776 jobs). `#print axioms` on both headlines:
`[propext, Classical.choice, Quot.sound]`.

**Reading for the handover:** phase 1 was pure new-file transcription with no promotions and no
hub edit; the `FLT.*` namespaces were kept even though the port has no `FLT/` area, so the file
paths sit under `AutomorphicForm/` while the declarations keep their pin names.
