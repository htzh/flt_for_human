# SET-R-B — the `X_H` relative-degree bound

**Status: done and verified (2026-10-08).** Second coding set of the qexp head.
Authorizes exactly **one new module**. Planning record:
[TOPIC-qexp-rationality-degree-head.md](TOPIC-qexp-rationality-degree-head.md)
§1 (target 2), §3 (SET-H-C reuse), §5, §7 items 2–5, §8.

**Deliverable.** `FLTForHuman/ModularCurve/XH/Relrank.lean`: the relative-degree
headline and its engine.

| headline | wrapper | proof source |
|---|---|---|
| `ModularCurve.le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd` | `Theorems/Thm_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.lean` | `P2M/Sol/S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.lean` (1,221) |

Statement (verbatim from the wrapper; the wrapper is the authority):

```lean
theorem ModularCurve.le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    ((ℓ + 1 : ℕ) : Cardinal) ≤ IntermediateField.relrank (xHFunctionField M H)
      (xHTopFunctionFieldC ℚ M H (M * ℓ))
```

**Reserved for the manager (do not start).** SET-R-C. If a proof needs it, stop
and report.

## 0a. Carry-over from SET-R-A (do this first)

SET-R-A's module re-derived three helpers locally that the dispatch report flagged
as *public* in the port. The manager has ruled: **use the public ones.** Clean
them up in `ModularForms/WeightOne/RationalityDvd.lean` before starting SET-R-B,
then re-verify the module.

| local `private` (RationalityDvd) | public declaration | expected action |
|---|---|---|
| `cw_ne_zero` (line ~83) | `cw_ne_zero` in `Gamma0Rationality.lean:1137`, namespace `WLightS10.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.X1DiamondRational` | delete the local copy; `open` that deep namespace (or fully qualify) and use the public one — same statement over the public `cw` |
| `kN_eq` (line ~51) | `kN_eq` in `Gamma1Basis.lean:2835`, namespace `WLightS11.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.GammaOneGaloisEven` | the public theorem ranges over that namespace's own `private kN`, which is *definitionally* the same adjoin; try `exact`/`simpa` with the deep name. If it does not go through by defeq, keep the local copy and report the exact error |
| `mdifferentiable_jf` (line ~78) | `mdifferentiable_jf` in `LevelN.lean:1266` (`include hjf`) | the public theorem is *conditional* on `hjf : ∀ τ, jf τ = E₄ τ ^ 3 / Δ τ`, which is `rfl` for the port's concrete `jf`; instantiate and supply it. If the instantiation is larger than the local proof, keep the local copy and report |

Do not edit the hub modules themselves — consumer-side change only. The other 11
local re-derivations are genuinely `private` in the hubs and stay. Re-run the
checker after the cleanup: the module's public surface does not change, so it must
stay **0 mismatched / 0 missing** with `identical` unchanged.

**Outcome (2026-10-08).** `cw_ne_zero` deleted, both use sites now call the public
deep-namespace declaration. `kN_eq` and `mdifferentiable_jf` are kept as local
declarations whose **bodies delegate** to the public theorems
(`GammaOneGaloisEven.kN_eq N`, and
`FrickeTransport.mdifferentiable_jf jf jf_spec`) — the hub forms are not drop-ins
(`kN_eq` ranges over a private `kN`; the public `mdifferentiable_jf` carries the
`hjf` binder), so per the manager these are not forced. `RationalityDvd.lean` is
50 public / 13 private; checker unchanged at 6652 / 0 / 0.

## 0. What is already in the port

* **SET-H-C inputs** (`ModularCurve/XH/HeckeInputs.lean`, 8 public rows):
  `conjMat`, `conjSL`, `heckeDiag_mul_mul_inv`, `inf_le_conj`,
  `intSeriesC_expandInt`, … Import; do not re-port.
* `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul` — the single theorem-level
  premise of the headline (`next5_advise` target-2 cone: 2 nodes).
* The `XH` definition layer (`Def_ModularCurve_XH`, `XH/FunctionField.lean`,
  `XH/Operators.lean`, `XH/DiamondLift.lean`, `XH/Inputs.lean`) is ported.
* Checker baseline: **6602 identical (312 promoted, 83 renamed), 0/0**. The
  relrank `S_` file and wrapper are **not** in `SOURCES` yet (§4).

## 1. Source of truth

Pin `anthropics/fermats-last-theorem@aa2d8b3`; statement = the wrapper, proof =
the `S_` file. The `S_` file declares its helpers publicly; the `next5_plan`
block for this file is **227 once / 94 in-port / 26 declarations** — the largest
new items are `intSeriesC_expandInt` (already in port as
`HeckeInputsHAll.intSeriesC_expandInt`), and among the genuinely new ones
`core` (~83 lines) and `linearIndependent_pow_y` (~65).

Reuse: `tools/deps/build/next5_advise.txt` §1 (264 substitution rows) and the
target-2 entries; the `XH` layer's public API.

## 2. Build discipline

As SET-R-A §2. Bounds: `timeout 300 lake env lean -DmaxHeartbeats=4000000
-DautoImplicit=false <file>`; `flock .lake/flt_build.lock timeout 300 lake build
<module>`; no whole-tree build; no commits; serial builds only.

## 3. The hub prohibition

**Do not edit any existing module.** If a helper you need is `private` elsewhere,
re-derive it in `Relrank.lean` and report it. The one known case:

* **`zetaU`** — the headline's proof uses the pin's `zetaU (ℓ : ℕ)` (a `ℂˣ` unit
  built from `zeta ℓ`). The port has only `DeligneSerre.zetaUnit`, **and it is not
  the pin's declaration**: it lives in the section
  `variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (ℓ - 1))` (note `ℓ - 1`), i.e. it is
  generalised over an arbitrary primitive root. **Do not promote or rename it.**
  Write a local `private` `zetaU` in `Relrank.lean` in the pin's form
  (`Units.mk0 (zeta ℓ) …`) or instantiate `zetaUnit` with the explicit root.
  Report which you did.

If you believe a promotion elsewhere is genuinely required, **stop and report**
with the declaration, host, reason, and `python3 tools/deps/build_ladder.py
--edit <host>`.

## 4. Wiring

In `lean/spec/check_flt_statements.py`:

* append to `SOURCES` **last**: the relrank `S_` file
  (`P2M/Sol/S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.lean`)
  and the wrapper (`Theorems/Thm_…`), with a comment;
* append `"FLTForHuman/ModularCurve/XH/Relrank.lean"` to `PORT_FILES` **last**.

Target **0 mismatched, 0 missing**; mutation-test one headline and revert.

## 5. Risks specific to this set

* **The `generalise` rows** (topic §7 item 3): 31 binder-only and 50
  statement-different names in the pool, dominated by level-`N` threading
  (`fricke N v` vs `fricke v`, `conj_mem_Gamma N`, `redN (N : ℕ)`, …). Read both
  statements before importing; never "fix" a port spelling to the pin's without
  checking its consumers.
* **Suspect `def` substitutions** (topic §7 item 4): `tauPair`, `SField`, the
  `E4`/`E6`/`A12`/`D12` family, `fricke`, `expandInt`. Each is a `def` whose
  *type* matches and whose body may not.
* Import-only definitions (topic §7 item 5): `--ready` does not see them;
  hand-check the import list.

## 6. Stop and report

Same conditions as SET-R-A §6, plus any declaration whose proof pulls in
`HeckeEis.*`/`ModPForms.*` (that is route A bleeding in — this target does not
need it).

## 7. Completion report

As SET-R-A §7, plus: the local `zetaU` decision; the `generalise` rows you had to
resolve; and the statement-different names you read against both copies.

## 8. Outcome (2026-10-08, landed and manager-verified)

`ModularCurve/XH/Relrank.lean`, 1,153 lines: **146 public** (the pin's `S_`
surface re-hosted at the pin names) and **2 private** (`gammaB_apply`,
`deltaB_apply`, local coercion glue — mathlib `v4.34.0` will not push the
`SL(2,ℤ) → GL(2,ℝ)` coercion through the structure literals with `simp`).
Headline verbatim at `ModularCurve.le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd`.
Checker **6652 → 6798 identical, 0 mismatched, 0 missing** (+146); mutation test
gave exactly `1 mismatched` and was reverted. Tier 0 green 7.0 s, tier 1 green
10.4 s (4,252 jobs); `#print axioms` clean.

**`zetaU`:** written fresh in the module at the pin's form
(`def zetaU : ℂˣ := Units.mk0 (zeta ℓ) (zeta_ne_zero ℓ)`) and left **public**,
because the pin's public statements (`val_zetaU`, `ofPowerSeries_qExpansion_twistFn`,
`rel_qTwist`) mention it; `DeligneSerre.zetaUnit` was neither promoted nor renamed
and `Lifting.lean` was not edited.

**Substitutions:** no parser substitution was applied where the pin's spelling had
to survive. `expandInt` reused the ported `HeckeInputsHAll.expandInt`; `AΓ`/`BΓ`,
`SField`, `tauPair`, `fricke`, `E4cube`/`E6sq` were transcribed at the pin's own
names after reading both copies. Binder-spelling rows (`levelRaise`, `coeffMap_qExpand`,
`coeffEmb_intSeriesC`, `isIntegralQExp_const`, `one_mem_strictPeriods`) took the
pin's binders. Working tree: `Relrank.lean` added, `RationalityDvd.lean` cleaned,
`spec/check_flt_statements.py` +24 wiring; no hub edited, nothing committed.
