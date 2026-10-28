# WORKORDER MC-4a — `periodLatticeOf_gammaH_heckeDiamondStable`

**SET**: [SET-MC4.md](SET-MC4.md) §0–§5. **Story**: M6. **Silk**: 464. **Net**: ≈416.
**Home**: `lean/FLTForHuman/ModularCurve/Period/HeckeStability.lean` — **insert** (the module already
hosts `CuspForm.stableT`/`stableU`/`stableD`, which the row consumes).
**Module after the touch**: same file, one new public declaration (its engine may be `private`).

## The declaration

Pin wrapper `Theorems/Thm_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable.lean`:

```
theorem ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) ∧
      (∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
        (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
```

Pin proof: `P2M/Sol/S_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable.lean` (464 lines), whose
`theorem solution` is the three-fold assembly over `periodLatticeOf_stable_heckeTLinH`,
`_stable_heckeULinH`, `_stable_diamondLinH`. Transcribe the pin's engine
(`PeriodLatticeHStableProof`: `IsPrimitive`, the derivative/period dictionary, the slash invariance)
and the three assemblies; keep the engine `private` if the wire has no statement for it (it does not
— only the headline is pin-public), and say so in a header note.

## Port vocabulary you must use (do not restate)

- `ModularCurve.periodOf`, `periodAlongOf`, `periodAlongOf_apply`, `periodLatticeOf`,
  `periodOf_mem_periodLatticeOf` — `ModularForms/EichlerShimura/PeriodOf.lean` (already imported by
  the home module's closure via `ModularCurve/Period/*`).
- `clamp01`, `clamp01_of_mem`, `segmentPoint`, `segmentPath`, `continuous_segmentPath`,
  `periodAlong` — `ModularForms/EichlerShimura/PeriodIntegral.lean`.
- `CuspForm.heckeTLinH`/`heckeULinH`/`diamondLinH` and their `_eq`/`coe_*` lemmas —
  `ModularForms/Defs/GammaH.lean` (the def wave's D1; the home module already imports it for
  `StableT`/`StableU`/`StableD`).
- `ModularForm.heckeU_slash_eq_self_of_mem_GammaH`, `ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH`
  — `ModularForms/HeckeInvariance.lean`; `CuspForm.stableT`/`stableU`/`stableD` — this module.

## Traps

1. The pin's `p2m_export`/`p2m_open` lines are P2M scaffolding, not Lean — do not transpose them.
2. `IsPrimitive` is local scaffolding; the port has no such name and must not grow one as public.
3. The three `Stable*` theorems are this module's own declarations, already `ok` against their
   wires; do not re-prove, import is not needed (same file).
4. The row's `v` ranges over the *ambient* `Module.Dual ℂ (CuspForm (GammaH M H) 2)` and membership
   in `periodLatticeOf` is `Submodule.span` membership; the pin's engine goes through `periodAlong`
   and the cusp form's slash invariance, not through `LinearMap.dualMap` algebra.

## Gates

1. `cd lean && lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/Period/HeckeStability.lean`
   → silent, zero warnings.
2. `flock /tmp/lean-build.lock lake build FLTForHuman.ModularCurve.Period.HeckeStability` → success.
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/Period/HeckeStability.lean` → the new
   headline `ok`; 0 mismatch / 0 missing; the pre-existing rows stay `ok`.
4. `#print axioms ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable` →
   `[propext, Classical.choice, Quot.sound]`.
5. Add exactly two `spec-pin:` lines for this row:
   `Theorems/Thm_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable.lean` and
   `P2M/Sol/S_ModularCurve_periodLatticeOf_gammaH_heckeDiamondStable.lean`.
6. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option maxHeartbeats`, no linter
   suppression, no `spec/decl_markers.tsv` edit, no other Lean file, no git, no whole-tree build.
   Every shell command must finish in under 2 minutes.
