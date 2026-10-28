# WORKORDER MC-4b — the period lattice is the ℤ-dual of the parabolic homs

**SET**: [SET-MC4.md](SET-MC4.md) §0–§5. **Story**: M6. **Silk**: 350. **Net**: ≈286.
**Home**: `lean/FLTForHuman/ModularCurve/Period/PeriodLatticeBasis.lean` — **insert** (it hosts the
`ℤ`-basis theorem, one of the row's premises, and imports the other five premise modules).
**Module after the touch**: same file, one new public declaration (the pin's `CpairK2Of` engine may
be `private` — the wire has no statement for it).

## The declaration

Pin wrapper `Theorems/Thm_ModularCurve_exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup.lean`:

```
theorem ModularCurve.exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
    (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ EV : ModularCurve.Period.parabolicHoms ℤ Γ ℤ ≃ₗ[ℤ] Module.Dual ℤ (ModularCurve.periodLatticeOf Γ),
      ∀ (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (δ : Γ),
        EV ψ ⟨ModularCurve.periodOf Γ δ, ModularCurve.periodOf_mem_periodLatticeOf Γ δ⟩ =
          (ψ : Additive Γ →+ ℤ) (Additive.ofMul δ)
```

Pin proof: `P2M/Sol/S_ModularCurve_exists_linearEquiv_parabolicHoms_…lean` (350 lines), whose
`solution` is `haveI : Γ.FiniteIndex := hΓ.finiteIndex; exact ModularCurve.CpairK2Of.main Γ hΓ` —
so the work is the `CpairK2Of` engine in that file (the dual-pairing construction and its
`periodOf` evaluation). Transcribe the engine (private unless the wire names it) and the assembly.

## Port vocabulary you must use (do not restate)

- `ModularCurve.periodOf`, `periodLatticeOf`, `periodOf_mem_periodLatticeOf` —
  `ModularForms/EichlerShimura/PeriodOf.lean`.
- `ModularCurve.Period.parabolicHoms` and its API — `ModularCurve/Period/ParabolicHoms.lean`
  (and `…Basis.lean` for the two basis headlines).
- `periodMapOf_mem_parabolicHoms`, `periodMapOf_apply_eq_periodOf` — `Period/ParabolicHoms.lean` and
  `ModularForms/EichlerShimura/ExistsEquivariantPrimitive.lean`.
- `CuspForm.finiteDimensional_of_isArithmetic` — `ModularForms/WeightOne/Basic.lean`.
- `exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup` — this
  module's own headline (already `ok`).

## Traps

1. The statement is the pin's `∃ EV …` verbatim, including the subtype term
   `⟨periodOf Γ δ, periodOf_mem_periodLatticeOf Γ δ⟩`; do not restate it as a `LinearEquiv` with a
   different argument order.
2. The pin's wrapper and `S_` file carry `attribute [-instance] …` / `attribute [-simp] …` preludes:
   **do not reproduce them** (the port keeps those global — see
   `ModularForms/CohCarrier/CommTriplet.lean`'s header). They are not part of the statement.
3. `hΓ.finiteIndex` is how the pin starts; if the port's `IsCongruenceSubgroup` API does not expose
   `.finiteIndex` by that name, find the right projection rather than adding a hypothesis.
4. The engine's names must not collide with existing port declarations (`CpairK2Of` is new); keep it
   inside a module-level namespace if the pin does.

## Gates

1. `cd lean && lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/Period/PeriodLatticeBasis.lean` → silent, zero warnings.
2. `flock /tmp/lean-build.lock lake build FLTForHuman.ModularCurve.Period.PeriodLatticeBasis` → success.
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/Period/PeriodLatticeBasis.lean` → the
   new headline `ok`, 0 mismatch / 0 missing, the pre-existing headline still `ok`.
4. `#print axioms` on the headline → `[propext, Classical.choice, Quot.sound]`.
5. Add exactly two `spec-pin:` lines (its `Thm_` wrapper and `S_` copy).
6. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option maxHeartbeats`, no linter
   suppression, no `spec/decl_markers.tsv` edit, no other Lean file, no git, no whole-tree build;
   every shell command under 2 minutes.
