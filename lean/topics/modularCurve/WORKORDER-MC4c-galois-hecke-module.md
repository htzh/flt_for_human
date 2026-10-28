# WORKORDER MC-4c — the Galois action commutes with the `HeckeAlgOne`-module structure

**SET**: [SET-MC4.md](SET-MC4.md) §0–§5. **Story**: M5. **Silk**: 272. **Net**: ≈220.
**Home**: `lean/FLTForHuman/ModularCurve/X1/HeckeModule.lean` — **insert** (the module that defines
`HeckeAlgOne` and `heckeModuleOneBar`, which the statement names).
**Module after the touch**: same file, one new public declaration (the pin's engine may be private).

## The declaration

Pin wrapper `Theorems/Thm_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.lean`:

```
theorem ModularCurve.JOne.galois_smul_heckeAlgOne_smul (M : ℕ) [NeZero M]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : ModularCurve.HeckeAlgOne)
    (x : ModularCurve.JOne M) :
    letI := ModularCurve.heckeModuleOneBar M
    σ • (t • x) = t • (σ • x)
```

Pin proof: `P2M/Sol/S_ModularCurve_JOne_galois_smul_heckeAlgOne_smul.lean` (272 lines): the
`JOneGaloisHeckeComm` engine (`coeffMap_qExpand_comm`, the α/β intertwining lemmas, the `JOne`-level
`galois_smul_heckeOperatorOneBar`/`galois_smul_diamondOneBar`) and the `MvPolynomial.induction_on`
assembly over `heckeModuleOneBar_smul_def`. Keep the engine `private` (the wire has only the
headline).

## Port vocabulary you must use (do not restate)

- `ModularCurve.HeckeAlgOne`, `heckeModuleOneBar`, `heckeModuleOneBar_smul_def`,
  `_heckeGenOne_smul`, `_diamondGen_smul`, `_smul_of_not`, `heckeEvalOneBar*` — **this module**
  (the def wave's D2).
- `ModularCurve.heckeOperatorOneBar_apply`, `diamondOneBar_apply` — `X1/HeckeModule.lean` and
  `X1/Diamond.lean`.
- `AlgebraicCurve.SemilinearAut.pic0_correspondence_smul` —
  `AlgebraicCurve/WeilExchange/GaloisRamification.lean` (add the import if the engine uses it).
- `ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutBar` — `X1/DiamondLift.lean`; if you need
  it, add `import FLTForHuman.ModularCurve.X1.DiamondLift` (acyclic: `DiamondLift` imports
  `X1/HeckeModule`, not the reverse — so **do not** put this row in `DiamondLift`).
- `heckeOperatorOneAlong_eq`/`_of_not`, `HeckeInputsOneAlong` — `X1/HeckeOperator.lean`.

## Traps

1. **Instance sensitivity.** The statement's `letI := heckeModuleOneBar M` is part of the statement
   text: transcribe it as a `letI` (the pin does). Inside the proof, `heckeModuleOneBar`'s
   `if h : HeckeDiamondCommuteBar M` means the `simp`/`rw` steps must go through
   `heckeModuleOneBar_smul_def` (hypothesis case) or `_smul_of_not`, never through `rfl`/`show`
   that would unfold the `if` wrongly.
2. The pin's `p2m_export`/`p2m_open` lines are scaffolding, not Lean.
3. The `attribute [-simp] ModularForm.…` prelude of the `S_` file is **not** reproduced (port keeps
   those global).
4. `NeZero (ℓ : ℕ)` for `ℓ : Nat.Primes` is `⟨ℓ.2.ne_zero⟩`; the engine's `omit [NeZero ℓ] in`s are
   the pin's and are not suppressions.
5. If a proof needs the `ℓ`-torsion/`JOne` Galois action, it is `arithmeticGalois` +
   `SemilinearAut.torsionRep` — both ported (`X1/Defs.lean`, `AlgebraicCurve/Defs/SemilinearAut.lean`).

## Gates

1. `cd lean && lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/X1/HeckeModule.lean` → silent, zero warnings.
2. `flock /tmp/lean-build.lock lake build FLTForHuman.ModularCurve.X1.HeckeModule` → success.
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/X1/HeckeModule.lean` → the new
   headline `ok`; 0 mismatch / 0 missing; the 28 pre-existing rows stay `ok`.
4. `#print axioms ModularCurve.JOne.galois_smul_heckeAlgOne_smul` →
   `[propext, Classical.choice, Quot.sound]`.
5. Add exactly two `spec-pin:` lines (its `Thm_` wrapper and `S_` copy).
6. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option maxHeartbeats`, no linter
   suppression, no `spec/decl_markers.tsv` edit, no other Lean file, no git, no whole-tree build;
   every shell command under 2 minutes.
