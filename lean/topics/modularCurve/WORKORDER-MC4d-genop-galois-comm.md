# WORKORDER MC-4d — `genOpH` and `heckeOperatorHAlong` commute with the Galois and diamond actions

**SET**: [SET-MC4.md](SET-MC4.md) §0–§5. **Story**: M5. **Silk**: 292 (265 + 27). **Net**: ≈224.
**Home**: `lean/FLTForHuman/ModularCurve/XH/Operators.lean` — **insert** (the module that defines
`genOpH` and `diamondHBar`, which the statements name).
**Module after the touch**: same file, **two** new public declarations (the pin's engines may be
private).

## The declarations

Pin wrappers `Theorems/Thm_ModularCurve_galois_smul_genOpH_comm.lean` and
`Thm_ModularCurve_heckeOperatorHAlong_diamondHBar_comm.lean`:

```
theorem ModularCurve.galois_smul_genOpH_comm (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CohCarrier.Gen M S)
    (P : ModularCurve.JH M H) :
    σ • (ModularCurve.genOpH M H S g P) = ModularCurve.genOpH M H S g (σ • P)

theorem ModularCurve.heckeOperatorHAlong_diamondHBar_comm (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime] (d : (ZMod M)ˣ) (P : ModularCurve.JH M H) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ (ModularCurve.diamondHBar M H d P) =
      ModularCurve.diamondHBar M H d
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ P)
```

Pin proofs: `P2M/Sol/S_ModularCurve_galois_smul_genOpH_comm.lean` (265) and
`S_ModularCurve_heckeOperatorHAlong_diamondHBar_comm.lean` (27). The 265 row is by cases on
`CohCarrier.Gen` (the pin's file has a `genOpH` block with the `T`/`U`/`dia` cases); the 27-line row
is the `β`-correspondence interchange through
`exists_algEquiv_intertwinesAlong_diamondAutHBar` + `pic0_correspondence_smul`, with the
`¬ HeckeInputsHAlong` case discharged by `simp` (see the module's `diamondHBar_apply`).

## Port vocabulary you must use (do not restate)

- `ModularCurve.genOpH`, `genOpH_T`, `genOpH_U`, `genOpH_dia`, `diamondHBar`, `diamondHBar_apply`,
  `diamondHBar_of_not` — **this module** (the def wave's D3).
- `CohCarrier.Gen` — `ModularForms/CohCarrier/Inst.lean` (imported by this module).
- `ModularCurve.heckeOperatorHAlong`, `_eq`, `_of_not`, `HeckeInputsHAlong`, `heckeAlphaHBar`,
  `heckeBetaHBar` — `XH/HeckeOperator.lean`.
- `exists_algEquiv_intertwinesAlong_diamondAutHBar` — `XH/DiamondLift.lean`.
- `AlgebraicCurve.SemilinearAut.pic0_correspondence_smul` —
  `AlgebraicCurve/WeilExchange/GaloisRamification.lean` (add the import).
- `ModularCurve.JH` — `XH/FunctionField.lean` (imported through `XH/HeckeOperator`).

## Traps

1. The pin passes the `heckeBetaHBar`/`heckeAlphaHBar` pair to `pic0_correspondence_smul` in the
   order **beta first** (φ = beta, ψ = alpha) — the port's signature is `(φ ψ : …) (hφ hψ) (hFI)
   (hfin) (hN) (hgφ) (hgψ) (c)`.
2. `Fact ℓ.Prime` gives `[NeZero ℓ]` by `⟨(Fact.out : ℓ.Prime).ne_zero⟩`; do not restate the
   hypothesis.
3. The 265 row's statement quantifies `σ • P`; `σ` acts by the port's `DistribMulAction` on `JH`.
   The `dia` case needs `diamondHBar_apply`'s `SemilinearAut.ofAlgAut … • x` spelling.
4. The 27-line row's pin file carries an `attribute [-simp] ModularForm.…` prelude: **not**
   reproduced.
5. Both rows land in this one module: add **four** `spec-pin:` lines (each row's `Thm_` wrapper and
   `S_` copy), no more — in particular do not wire `Def_ModularCurve_XHOperators` again (already
   there).

## Gates

1. `cd lean && lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/XH/Operators.lean` → silent, zero warnings.
2. `flock /tmp/lean-build.lock lake build FLTForHuman.ModularCurve.XH.Operators` → success.
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/XH/Operators.lean` → both new
   headlines `ok`; 0 mismatch / 0 missing; the 14 pre-existing rows stay `ok`.
4. `#print axioms` on both headlines → `[propext, Classical.choice, Quot.sound]`.
5. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option maxHeartbeats`, no linter
   suppression, no `spec/decl_markers.tsv` edit, no other Lean file, no git, no whole-tree build;
   every shell command under 2 minutes.
