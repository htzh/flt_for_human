# SET-H-B — the diamond-lift pair, written once

Work order for SET-H-B of
[TOPIC-xH-hecke-diamond-inputs.md](TOPIC-xH-hecke-diamond-inputs.md) §5, dispatched
to one agent. Pin `aa2d8b3`, port mathlib `v4.34.0`. SET-H-A (the `X_H(M)`
definition layer) is landed; see [logs/xh-hecke-set-a.md](../../logs/xh-hecke-set-a.md).

## 1. Subject and scope

Port the two ready nodes

| node | pin `S_` file (raw) | wrapper |
|---|---:|---|
| `ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutHBar` | `P2M/Sol/S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.lean` (1,188) | `Theorems/Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.lean` |
| `ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutBar` | `P2M/Sol/S_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.lean` (1,178) | `Theorems/Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar.lean` |

as **one development**: the general-`Γ` engine once, the two headlines as its two
level specialisations (the topic's §3 item 1). `port_plan.py` measures 2,366 raw `S_`
lines → 1,498 once-cost → 95 in port → **1,403 net new math lines**; the two files
share a 785-line / 75-declaration block and differ only in the level-specific layer.

**Target statements (verbatim from the two wrappers).**

```lean
theorem ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutHBar (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ τ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))
        ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)),
      AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutHBar M H d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) ∧
        AlgebraicCurve.SemilinearAut.IntertwinesAlong
          (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutHBar M H d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ)

theorem ModularCurve.exists_algEquiv_intertwinesAlong_diamondAutBar (M : ℕ) [NeZero M] (ℓ : ℕ)
    [NeZero ℓ] (d : ℕ) :
    ∃ τ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))
        ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ)),
      AlgebraicCurve.SemilinearAut.IntertwinesAlong (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar M d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ) ∧
        AlgebraicCurve.SemilinearAut.IntertwinesAlong (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ).toRingHom
          (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar M d))
          (AlgebraicCurve.SemilinearAut.ofAlgAut τ)
```

The two `Theorems/` wrappers, not the `S_` files, are the comparable copies for
these two statements (the `S_` files carry the same statement as an inner
`theorem solution` in `namespace P2MW.…`; the wrapper name is `ModularCurve.…`).
Both `S_` files are **already in `SOURCES`** (SET-H-A added them, to verify the
promotions); the two wrappers must be appended now, beside them.

## 2. Module layout

| module | namespace | role |
|---|---|---|
| `FLTForHuman/ModularCurve/XH/DiamondLiftPrelude.lean` | `ModularCurve.DiamondLift` | the general-`Γ` engine, written once, **public** (both consumers import it) |
| `FLTForHuman/ModularCurve/XH/DiamondLift.lean` | `ModularCurve.DiamondLift.XH` | the `X_H` specialisation and the H headline |
| `FLTForHuman/ModularCurve/X1/DiamondLift.lean` | `ModularCurve.DiamondLift.X1` | the `X₁` specialisation and the X₁ headline |

`PORT_FILES`: append the three modules. `SOURCES`: append
`Theorems/Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAut{H,}Bar.lean`
after the two `S_` files already there. No `OWN_PROOFS` entry is expected: every
public port declaration must resolve by last name.

## 3. Route

### 3.1 What goes in the prelude (general in `Γ`, `Δ`)

Transcribe, **verbatim in statement and with the pin's proofs**, the sections of
the H `S_` file (lines 22–340, 567–740 and the generic half of 741–900) that are
*identical* between the two `S_` files — `port_advise.py` reports **97 shared
declarations with byte-identical statements**:

* `class IsLevel` (`T_mem`) and `class Normalizes` (`conj_mem`), both public;
* `section QExp` — `qC`, `one_mem_strictPeriods`, `qC_mul`, `qC_coe_mul`, `qC_add`,
  `qC_neg`, `qC_smul`, `qC_zero`, `qC_one`, `qC_coe_zero`, `qC_coe_one`, `hasSum_qC`,
  `coe_eq_of_qC_eq`, `qC_eq_zero_iff`;
* `section Slash` — `isBoundedAt_slash`, `slashForm`, `coe_slashForm`,
  `coe_slashForm_SL`, `slash_inv_slash`, `slash_slash_inv`, `slashForm_ne_zero`;
* `section Ratio` — `IsRatio`, `isRatio_of_eq`, `qC_coe_one_ne_zero`, `isRatio_zero`,
  `isRatio_one`, `IsRatio.add/.neg/.mul/.inv`, `isRatio_C`, `ratioField`,
  `qC_slash_ne_zero`, `cross`, `pull`, `pull_eq`, `pull_one`, `pull_zero`,
  `pull_mul`, `pull_add`, `pullHom`, `pull_mem`, `pull_pull_inv`;
* `section Rational` — `toC`, `toC_injective`, `toC_intSeriesC`, `toC_ratio`,
  `qC_ne_zero_of_intSeriesC_ne_zero`, `toC_algebraMap`, `toC_mem_ratioField`,
  `iota`, `coe_iota`, `jC`, `jC_apply`, `jC_injective`, `RationalSlash`, `psi`,
  `psi_apply`, `exists_psi_generator_eq`, `exists_psi_eq`, `psi_mem_range`, `eC`,
  `jC_eC_symm`, `sigma0`, `jC_sigma0`, `sigma0_injective`, `sigma0_surjective`,
  `sigma`, `sigma_apply`, `toC_sigma`, `toC_sigma_generator`;
* `section Stretch` — `stretchSlash`, `coe_stretchSlash`, `stretchSlash_apply`,
  `stretch`, `coe_stretch_eq_smul`, `stretch_apply`, `coe_stretch`, `stretch_slash`,
  `qCoeff_stretch`, `ofPowerSeries_eq_qExpand`, `qC_stretch`, `isIntegralQExp_stretch`
  (the pin's `private mapGL_coe_eq` stays private);
* the generic half of `section Level` — `Gamma0_mul_le`, `neZero_mul`,
  `exists_coprime_lift`, `exists_gammas`, `ringHom_ext_adjoin`.

### 3.2 What stays in the two consumers (level-specific)

`cocycle`, `rationalSlash_level`, `FB`, `FT`, `FB_le_FT`, `toC_qExpand` (Bar has it,
H does not), `conj_mem_Gamma1` (Bar) / `conj_mem_GammaH` (H), the `scoped instance
isLevel_*`, the `Genuine` block (`toC_sigma0_generator`/`tau0_incl*`/`exists_tau0`
for Bar; `genH`/`witness`/`coeffEmb_injective'`/`tau0_incl_generator`/
`tau0_qExpand_generator` for H), `isBaseChangeAutOf_diamondAutBar` (Bar) /
`laurentBaseChange_eq_adjoin_ratios` (H), `comp_alpha_eq`, `comp_beta_eq`, the inner
`main`, and the public headline.

These have the **same last names but different statements** in the two files, so
each consumer keeps its own copy in its own namespace; the checker's `find`
disambiguates by statement (both pin candidates are in `SOURCES`). The inner
helpers may be `private` — only the two headlines must be public.

### 3.3 Statement-fidelity traps (these are why the engine must be transcribed, not reused)

1. **`GL↑` and `ℚbar` are `local notation` in the `S_` files** (`GL↑` at line 20 of
   both; `ℚbar` at line 918 / 917). The checker diffs *text*, not elaborated terms.
   Every module here must declare the same two local notations, verbatim:
   ```lean
   local notation "GL↑(" Γ ")" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
   local notation "ℚbar" => AlgebraicClosure ℚ
   ```
2. **The stretch block is NOT reusable from `X1/QExpandStretch.lean`.** Measured:
   the port's copies take `(hΓ' : …)` and `(hT : ModularGroup.T ∈ Γ)` as *explicit
   binders*, while the pin's take them as *section variables* / an `[IsLevel Γ]`
   instance, and the port spells `(Γ : Subgroup (GL (Fin 2) ℝ))` where the pin
   spells `GL↑(Γ)`. Promoting them is therefore a `MISMATCH`, not a promotion
   (this is the same failure mode `logs/xh-hecke-set-a.md` §3 recorded for `qC_*`).
   **Write the pin-style copies in the prelude; do not edit `X1/QExpandStretch.lean`.**
   Their bodies may call the already-public `ModularCurve.expandPS`,
   `coeff_expandPS`, `intSeriesC_expandPS`, `heckeDiagMatrix_mul_eq`,
   `isCusp_heckeDiagMatrix_smul` and mathlib; the ~110 lines of the block are the
   only intentional duplication, and it is recorded here.
3. **Already public — import, never restate.** The engine's pin copies of these are
   statement-identical to the port's and are in the file named:
   `ModularCurve.X1DiamondPullback.{IsRatio, ratioField, toC_injective,
   toC_algebraMap, qC_zero, qC_one, slash_inv_slash, slash_slash_inv}` and
   `ModularCurve.{expandPS, coeff_expandPS, intSeriesC_expandPS,
   heckeDiagMatrix_mul_eq, isCusp_heckeDiagMatrix_smul}`. But note the pin's engine
   declares them **generic in `Γ`** and the port's promoted copies are
   `Γ₁(M)`-specialised — so a `Γ`-general `qC_zero : qC (1 : ℍ → ℂ) = 1` may be
   shared only where the statement text has no `Γ` in it. Where the pin's statement
   *does* mention `GL↑(Γ)` (`qC_coe_zero`, `qC_mul`, `coe_slashForm`, …) the prelude
   must declare its own general copy; where it does not (`qC_zero`, `qC_one`,
   `slash_inv_slash`, `slash_slash_inv`, `toC_injective`, `toC_algebraMap`,
   `IsRatio`, `ratioField`, `expandPS`, `coeff_expandPS`, `intSeriesC_expandPS`,
   `heckeDiagMatrix_mul_eq`, `isCusp_heckeDiagMatrix_smul`) it must **reuse** the
   ported one by import (a second declaration of the same last name in another
   namespace is legal but would be an unchecked duplicate — do not write one).
4. **`coeffEmb_qExpand`** is public in `Defs/Laurent.lean` with binder `n`, the pin's
   `S_` copy with `ℓ`; reuse the port's, do not restate (the pin's copy then simply
   has no port counterpart, which the checker does not see).
5. **`conj_mem_Gamma1`** is public at `ModularForms/WeightOne/Gamma0Integral.lean`
   and `CohCarrier.conj_mem_GammaH` at `ModularForms/Defs/GammaH.lean`; reuse them.
6. The pin's `set_option linter.unusedSectionVars false` and
   `set_option synthInstance.maxHeartbeats 1600000` should be carried; the topic's
   §6 risk 2 (the `cocycle`/`!![…]`–`SL(2,ℤ)` coercion needing
   `backward.isDefEq.respectTransparency.types false`) will bite — transcribe the
   pin's `set_option`, do not restructure.

### 3.4 Reuse map (all ported, all importable)

`XH/FunctionField.lean` (`xHFunctionFieldC`, `xHTopFunctionFieldC`,
`xHFunctionFieldBar`), `XH/HeckeOperator.lean` (`heckeAlphaHBar`/`heckeBetaHBar`/
`HeckeBetaHDefined`), `XH/Operators.lean` (`IsDiamondAutHBar`/`diamondAutHBar`/
`isDiamondAutHBar_diamondAutHBar`/`diamondAutHBar_of_not`), `X1/Defs.lean`
(`x1FunctionFieldC`, `x1x0FunctionFieldC`), `X1/HeckeOperator.lean`
(`heckeAlphaOneBar`/`heckeBetaOneBar`/`HeckeBetaOneDefined`), `X1/Diamond.lean`
(`IsDiamondAut`, `diamondAut`, `diamondAutBar`, `IsBaseChangeAutOf`), and
`X1/BaseChangeCover.lean` `ModularCurve.exists_algEquiv_laurentBaseChange_cover`
(both `main`s use it). `X1/DiamondAut.lean`'s `exists_isIntegralQExp_smul_slash_of_mem_Gamma0`
and `restrictForm` are used by the Bar `rationalSlash_level`.

### 3.5 Explicitly out of scope

The input bundle `HeckeDiamondInputsHAll` and `heckeInputsHAlong` (SET-H-C; the
capstone is manager-reserved); `JH`/`genOpH`/`diamondHBar`; any edit to
`X1/QExpandStretch.lean`, `X1/DiamondAut.lean` or `X1/FunctionField.lean` beyond
what SET-H-A already did; `Def_ModularCurve_XHDRModelAtP.lean`.

## 4. Build discipline

* Edit loop: `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`.
* `flock .lake/flt_build.lock timeout 600 lake build <module>` when a file is done;
  **one** `flock .lake/flt_build.lock timeout 900 lake build` for the whole tree at
  the end. Never a bare whole-tree build inside the work; never raise
  `maxHeartbeats`.
* A new module needs `lake build FLTForHuman.<Module>` before a dependent module's
  `lake env lean` can see it (the `.olean` must exist).
* Time builds with wall **and** user/sys.

## 5. Verification

1. Checker: `python3 spec/check_flt_statements.py`; target `0 mismatched /
   0 missing`. Baseline before this set is `6365 identical (312 promoted,
   83 renamed), 0 mismatched, 0 missing, 36 own (6401 checked)`; the expected delta
   is the engine's public declarations plus the two headlines. Reconcile every
   count. Verify with a one-token mutation (expect exactly one more `mismatched`)
   and revert.
2. `python3 spec/check_flt_statements.py --prop-bodies` (advisory): the prelude's
   `def … : Prop` bodies (`IsLevel`, `Normalizes`, `RationalSlash`) should diff
   identical.
3. Consumer: extend `spec/XHConsumer.lean` with a Zone XH-D `[xh-diamondlift]`:
   instantiate both headlines at `M = 2`, `ℓ = 2` (H at `H = ⊥`, `d = 1`), and
   destructure the `∃ τ` into a real `laurentBaseChange … ≃ₐ[…] …` with both
   `IntertwinesAlong` conjuncts. `lake env lean spec/XHConsumer.lean` must stay at
   `0` errors / `0` warnings, and the zone must delete-fail. Delete-fail probe:
   rename the two headline calls in a copy under `tmp/` and count errors.
4. `#print axioms` on the two headlines: expect
   `[propext, Classical.choice, Quot.sound]`; no `sorry` anywhere.
5. Whole-tree `lake build` green.

## 6. Staging (checkpoint after each phase)

* **P1** — `XH/DiamondLiftPrelude.lean`; build the module, run the checker.
* **P2** — `XH/DiamondLift.lean` (the H specialisation + headline); build, checker.
* **P3** — `X1/DiamondLift.lean` (the X₁ specialisation + headline); build, checker,
  consumer, axioms, whole tree.

If the budget runs short, **stop at a phase boundary with the tree green** and
report which phases landed; the manager continues with a follow-up order rather
than inheriting a red tree.
