# WORKORDER-MC7b — the diamond correspondence on the X₁ function field

Status: **landed 2026-10-27** (SET [MC-7](SET-MC7.md), order MC-7b). Module:
`lean/FLTForHuman/ModularCurve/X1/DiamondCorrespondence.lean`, **778 lines**, declarations in
`ModularCurve.DiamondCorrespondence` (nested: the pin's `coeffMap_algebraMap` would collide with
`Defs/Laurent.lean`'s).  Manager-reviewed on the same tree: `check_port --force` **71 ok / 0
mismatch / 0 missing / 0 own**, headline at the wrapper `:11`, `main` at `S_:790`; axioms
`[propext, Classical.choice, Quot.sound]`; module build 73 s, silent; `dedup` 0 clusters;
25 of the 96 pin declarations imported (the `AutTrace` five from the shared module, the
`P4`/`P6`/E₄-E₆ block from `RelrankSol`, the maps from `Defs/Laurent`/`Frobenius/Defs`/
`JqIntegralRatios`/`X1/AtkinLehnerExchange`/`ModularForm.Level`), **none re-proved**.  Reviewer hygiene edit: the module's `haveILetI` suppression is gone (three `haveI` → `have`);
zero warnings, option-free.  Two accepted
deviations: `D12top`/`N12top` as one-line aliases of `RelrankSol.AF`/`BF` (packaging; the pin's
statements name them — MC-7d D4 owns the naming sweep), and two 2-line `one_mem_strictPeriods*`
lemmas over mathlib because the port's copies do not carry the pin's statement text.

| node | pin `S_` | pin lines | declares | frontier |
|---|---|---:|---|---|
| `ModularCurve.coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne` | `P2M/Sol/S_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean` | 934 | 92 | needed 1, cone consumers 1 / project 2 |

Read [SET-MC7.md](SET-MC7.md) first — §0.2 (**this row has no definition gate**), §0.3 (the
934↔868 shared block), §5 (this order's traps).

**Pin**: `/home/haitao/proj/fermats-last-theorem` at `aa2d8b3`.
**Port**: `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean`.

## 1. What the mathematics is

For `M` with `[NeZero M]`, `d : ℕ`, `σ` a diamond automorphism of `x1FunctionField M` and
`σ'` its base change to `Qb = AlgebraicClosure ℚ` on `x1FunctionFieldBar M`, an embedding
`ι₀ : Qb →+* ℂ`, a Kähler differential `ω` on `x1FunctionFieldBar M`, and
`f : CuspForm Γ₁(M) 2` with `coeffMap ι₀ (diffQExp ω) = qExpansion f`:

```
coeffMap ι₀ (diffQExp (correspondence (diamondAutBar M d).toAlgHom id ω))
  = qExpansion (CuspForm.diamondLinOne M 2 d f).
```

The pin's proof (`namespace R1G1Hd`) is a nine-section development; the assembly `main` is
`S_:790–906`:

| section | content | reuse |
|---|---|---|
| `AutTrace` | `pullbackAlong_pullbackAlong`, `pullbackAlong_id`, `separableAlong_algEquiv`, `trace_one_along_algEquiv`, `traceAlong_algEquiv`, `correspondence_algEquiv_id` | the 934↔868 shared block (§0.3): 6 names, ~70 lines; **this module keeps its own copy** |
| `Laurent` | `coeffMap_injective`, `ofPowerSeries_coeff_negSucc`, `coeffMap_ofPowerSeries`, `coeffMap_qEuler`, `qEuler_ofPowerSeries`, `qEuler_div_mul_sq` | `coeffMap_injective`, `coeffMap_ofPowerSeries` ported (`Defs/Laurent`, `Frobenius/Defs`) |
| `LevelOne` | `P4`, `P6`, `isIntegralQExp_E4/_E6`, `D12top`, `N12top`, `qExpansion_D12top/_N12top`, `slash_top_eq`, `one_mem_strictPeriods_of`, `exists_RCtop` (Rankin–Cohen) | `P4`/`P6`/`D12top`/`N12top`/the `P4` coefficients and `_E4/_E6` are ported (`X1/FunctionField`, `XH/Relrank`); `exists_RCtop` is a wrapper over `ModularForm.exists_rankinCohen_one_qExpansion_eq` (`ModularForms/QCoeffLevelOne.lean`) |
| `Forms` | the `Γ₁`/`Gamma0` conjugation API (`conjForm`, `QQ`, `QQ_mul/add/neg/smul/one`, `eq_of_QQ_eq`, `QQ_eq_zero_iff`, `conjForm_ne_zero`, `coeGL_mul`, `conjForm_mul`, `toMF`, …) | `conj_mem_Gamma1` ported; the `QQ` algebra is new |
| `Ratios` | `intSeriesC_*`, `isIntegralQExp_*`, `A12M`/`B12M`, `xq = E₆²/E₄³`, `coeffMap_xq`, `slash_A12M/_B12M`, `qEuler_ratio_ne_zero` | `intSeriesC_ne_zero_of_constantCoeff`, `intSeriesC_P4_cube_ne_zero`, `intSeriesC_eq_zero_iff` ported |
| `Dictionary` | `PairProp` and its closure (`pair_const/zero/mul/add/neg/inv`), `pair_gen`, `pair_all` | new; the heart of the `main` proof |
| `Assembly` | `isCurveOver_bar`, `charZero_bar`, `x0`, `coeff_x0`, `coeffEmb_intSeriesC`, `D_x0_ne_zero`, `sigma_x0`, `main` | `isCurveOver_of_isAlgClosed_of_transcendental`, `JOneES.exists_transcendental_…`, `IsCurveOver.finrank_kaehler` ported |

## 2. Module plan — one new module

**`lean/FLTForHuman/ModularCurve/X1/DiamondCorrespondence.lean`**, imports (as needed by the
premise check of SET-MC7 §4):

```lean
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.ModularCurve.X1.DiamondAut
import FLTForHuman.ModularCurve.X1.DiamondLift
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.Defs.HeckeDifferential
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularForms.QCoeffLevelOne
import FLTForHuman.ModularForms.Defs.Gamma1HeckeOperators
import FLTForHuman.ModularForms.Level.Diamond
import FLTForHuman.ModularForms.HeckeNebentypus
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.Differential.PushPull
import FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegular
import FLTForHuman.AlgebraicCurve.Differential.Hurwitz
```

Wire (leading `/- … -/` block), exactly two lines:

```
spec-pin: Theorems/Thm_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean
spec-pin: P2M/Sol/S_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean
```

Statement authority: the `Theorems/` wrapper (29 lines) — take its binder block verbatim for the
headline (`M`, `[NeZero M]`, `d`, `hσ`, `hσ'`, `ι₀`, `ω`, `f`, `hω`). The pin's `solution` at
`S_:913` is the same statement; the wrapper is the authority.

**Namespace.** The pin uses `namespace R1G1Hd` (a search label, not mathematics) — do **not**
transcribe it. Use `namespace ModularCurve` and the declaration names the pin uses (the checker
matches the pin wire by name/hash; the pin's names are unqualified inside `R1G1Hd`, so any
namespace works as long as the last names match). The two internal names that would collide with
the port are handled by the local namespace: none of the 934 names clashes today.

## 3. What the port already has — import, do not restate

`port_advise --nodes ModularCurve.coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne`
(16 declarations / ≈139 lines): `mem_intFormRatiosC_of_mem` (`X1/AtkinLehnerExchange.lean`,
`A2K1A.X1x0.mem_Sb_of_mem` — the same statement under another name), `conj_mem_Gamma1`
(`ModularForms/WeightOne/Gamma0Integral.lean`), `isIntegralQExp_E4` (`XH/Relrank.lean`),
`isIntegralQExp_E6`/`intSeriesC_ne_zero_of_constantCoeff`/`intSeriesC_add`/`coeff_one_P6`/
`constantCoeff_P6` (`X1/FunctionField.lean`), `D12top`/`N12top` (`XH/Relrank.lean`),
`coeff_one_P4`/`constantCoeff_P4`/`intSeriesC_P4_cube_ne_zero` (`XH/Relrank.lean`),
`intSeriesC_eq_zero_iff` (`JqIntegralRatios.lean`), `coeffMap_injective` (`Defs/Laurent.lean`),
`one_mem_strictPeriods_of` (`RelIndex/LevelRaise.lean`, a `RelIndex` copy of the pin's
`one_mem_strictPeriods` — **check the statement before using it**; the pin's 934 text is the
authority).

**Do not restate a substituted declaration at a different binder shape**: the checker diffs the
statement, and a near-copy is a `MISMATCH`, not a free import. Where the port's copy is at a
different binder, write the module's own declaration at the **pin's** text shape (the checker
accepts a faithful re-spelling by content hash).

**The shared block with MC-7c — written once, not twice.** `trace_one_along_algEquiv`,
`correspondence_algEquiv_id`, `traceAlong_algEquiv`, `separableAlong_algEquiv`,
`pullbackAlong_id` and (the wrapper) `pullbackAlong_pullbackAlong` live once in
`FLTForHuman/AlgebraicCurve/Differential/AutTrace.lean` (landed by the manager, namespace
`AlgebraicCurve.Differential`); import them. The `P4`/`P6`/`isIntegralQExp_E4/_E6`/coefficient
block lives once in the port (`XH/Relrank.lean`, `X1/FunctionField.lean`); import it. **Do not
copy a proof of any of these.** Packaging duplication (a one-line wrapper at the pin's binder
shape) is fine; a second proof of the same lemma is not — this is the set's standing rule, and
[WORKORDER-MC7d-rectify-engine-homes.md](WORKORDER-MC7d-rectify-engine-homes.md) is the audit
that enforces it.

## 4. Gates

1. `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` on the file → **silent, zero
   warnings**. The pin sets `synthInstance.maxHeartbeats 1600000` and `maxHeartbeats 3200000`;
   **neither is transcribed**. If a step blows the cap, use the playbook §6 probe ladder and
   report the classification — do not add a module `set_option maxHeartbeats`;
2. `flock /tmp/dsh-lake.lock timeout 600 lake build FLTForHuman.ModularCurve.X1.DiamondCorrespondence`
   → builds, `.olean` present; no tree build, no dependents;
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/X1/DiamondCorrespondence.lean` →
   **0 mismatch, 0 missing**;
4. `#print axioms` on the headline (probe in `lean/tmp/probe-mc7b.lean`) →
   `[propext, Classical.choice, Quot.sound]`;
5. `python3 ../tools/deps/dedup.py --module …` and `move_dead.py`; the 934↔868 cluster is the
   recorded exception (SET-MC7 §0.3) — report what dedup says, do not "fix" it by moving code;
6. no `sorry`/`admit`/`axiom`/`native_decide`; no `spec/decl_markers.tsv` row; no edits outside
   this module; do not commit or push.

## 5. Report back

`check_port`'s summary line, the axioms line, the build log's last two lines, the final line
count, the declarations kept `private` and why, the pin declarations you had to skip (and why —
a skipped pin declaration is allowed, an unfaithful one is not), and any trap that cost a probe.
