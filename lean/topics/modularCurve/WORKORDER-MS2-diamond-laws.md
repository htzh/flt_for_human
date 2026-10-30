# WORKORDER MS-2 — the Hecke–diamond laws on `J_1` and `J_H`

**SET**: [TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md) §0.4 U7, §2, §3, §4. **Story**: U7.
**Silo**: 438 (410 + 28). **Net**: ≈318.
**Home**: **new** `lean/FLTForHuman/ModularCurve/HeckeDiamondCommute.lean` — top level, the diamond
sibling of `ModularCurve/HeckeCommuteBar.lean` (which hosts `heckeOperatorsCommuteBar`).

Imports (verified: the union's closure contains every module both rows name):

```lean
import FLTForHuman.ModularCurve.XH.Operators
import FLTForHuman.ModularCurve.XH.Inputs
import FLTForHuman.ModularCurve.X1.CoeffMap
import FLTForHuman.ModularCurve.X1.DiamondCorrespondence
import FLTForHuman.ModularCurve.X1.DiamondLift
import FLTForHuman.ModularCurve.X1.HeckeCommute
import FLTForHuman.ModularCurve.X1.HeckeModule
```

## The declarations

Both wrappers, verbatim.

`Theorems/Thm_ModularCurve_diamondHBar_mul.lean` (410 silo):

```
theorem ModularCurve.diamondHBar_mul (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (d d' : (ZMod M)ˣ) (x : ModularCurve.JH M H) :
    ModularCurve.diamondHBar M H (d * d') x =
      ModularCurve.diamondHBar M H d (ModularCurve.diamondHBar M H d' x)
```

`Theorems/Thm_ModularCurve_heckeDiamondCommuteBar.lean` (28 silo):

```
theorem ModularCurve.heckeDiamondCommuteBar (M : ℕ) [NeZero M] :
    ModularCurve.HeckeDiamondCommuteBar M
```

## The pin proofs

**410** — `P2M/Sol/S_ModularCurve_diamondHBar_mul.lean` (410 lines / 33 declarations) in
`namespace P2MW.S_…` then `namespace XHDiaMul`, five sections:

| section | pin lines | content |
|---|---|---|
| `Laurent` | 23–83 | `coeffMap_injective`, `ofPowerSeries_coeff_negSucc`, `coeffMap_ofPowerSeries`, `coeffMap_intSeriesC`, `intSeriesC_eq_zero_iff`, `intSeriesC_add`, `intSeriesC_C`, `intSeriesC_eq_of_isIntegralQExp` |
| `Group` | 85–136 | `exists_gamma0`, `_root_.XHDiaMul.conj_mem_GammaH`, `gammaH_le_conj`, `coeGL_mul`, `entry_inv_mul`, `one_mem_strictPeriods` |
| `Forms` | 138–209 | `conjForm`/`coe_conjForm`, `slashQ`/`slashQ_eq_conjForm`, `qexp_mul`, `eq_of_qexp_eq`, `ne_zero_of_isIntegralQExp`, `conjForm_ne_zero`, `slashQ_ne_zero`, `ofPowerSeries_qexp_ne_zero` |
| `Ratios` | 211–219 | `mem_intFormRatiosC_of_mem` |
| `Diamond` | 221–397 | `gen`, `isDiamondAutHBar_apply`, `coeffEmb_injective`, `algEquiv_ext_of_ratios`, `isDiamondAutHBar_unique`, `isDiamondAutHBar_trans`, `diamondAutHBar_mul`, `solution` |

**28** — `P2M/Sol/S_ModularCurve_heckeDiamondCommuteBar.lean` (28 lines, **one** declaration,
`solution`). `HeckeDiamondCommuteBar M` is `∀ i j : Nat.Primes ⊕ ℕ, heckeDiamondGenBar M i *
heckeDiamondGenBar M j = heckeDiamondGenBar M j * heckeDiamondGenBar M i` (public in
`X1/HeckeModule.lean:124`), and `heckeDiamondGenBar = Sum.elim heckeOperatorOneBar diamondOneBar`
(`X1/HeckeModule.lean:114`). The pin's proof is the four-case assembly from the three ported
commutations; transcribe it, do not re-prove a commutation.

## Vocabulary (all ported — import, never re-derive)

- `ModularCurve.JH`, `diamondHBar`, `IsDiamondAutHBar`, `diamondAutHBar`, `genOpH` —
  `XH/Operators.lean` (`JH` through `XH/FunctionField.lean`).
- `ModularCurve.HeckeDiamondInputsHAll` — `XH/Inputs.lean`.
- `ModularCurve.coeffMap`, `intSeriesC` — `Defs/Laurent.lean`; `mem_intFormRatiosC_…` —
  `X1/CoeffMap.lean`.
- `ModularCurve.HeckeDiamondCommuteBar`, `heckeDiamondGenBar`, `heckeOperatorOneBar`,
  `diamondOneBar` — `X1/HeckeModule.lean`.
- `heckeOperatorOneBar_comm` — `X1/HeckeCommute.lean`; `heckeOperatorOneBar_comm_diamondOneBar` —
  `X1/DiamondLift.lean`; `diamondOneBar_comm` — `X1/DiamondCorrespondence.lean`.
- `CohCarrier.GammaH` — `ModularForms/Defs/GammaH.lean`.

## Traps

1. **`28` is one line of Lean and 28 of assembly.** Its four cases are covered by three ported
   lemmas; the work is the `Sum`-case analysis of `heckeDiamondGenBar` (`Sum.inl`/`Sum.inr`), not
   new commutation mathematics. Read `X1/HeckeModule.lean:112–128` first.
2. The module holds **one `J_1` row and one `J_H` row**: `HeckeDiamondCommuteBar` is about
   `JOne M` (`X1/HeckeModule.lean`), `diamondHBar_mul` about `JH M H`. Do not unify the two
   carriers and do not add a `J_H` version of the `Prop`.
3. `28` must **prove** `HeckeDiamondCommuteBar M`, so it must import `X1/HeckeModule.lean` (the
   definition's home) without assuming it; `heckeDiamondCommuteBar` is not available as a
   hypothesis anywhere.
4. **Keep the pin's file-local namespace** `_root_.XHDiaMul.conj_mem_GammaH`: it is the pin's, it
   is used by the pin's own proof, and folding it into `ModularCurve` would collide with the X_H
   side.
5. Never transcribe `p2m_open`/`p2m_export`, the `P2MW.S_` namespace, `attribute [-simp]` /
   `attribute [-instance]` preludes, or `set_option`s (410's wrapper carries none; 28's carries
   none either).
6. The `Laurent` section's four `coeffMap_*` lemmas exist in the port (`Defs/Laurent.lean`,
   `X1/CoeffMap.lean`): check them before writing (FR-0069).
7. `isDiamondAutHBar_trans` and `algEquiv_ext_of_ratios` are the two engine lemmas of 410's
   `Diamond` section; `diamondAutHBar_mul` (the `AlgEquiv` law) is proved **before** the
   headline's pointwise law — keep that order.

## Gates

1. Edit loop: `cd lean && timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000
   FLTForHuman/ModularCurve/HeckeDiamondCommute.lean` → silent, zero warnings.
2. `flock tmp/lean-build.lock timeout 90 lake build FLTForHuman.ModularCurve.HeckeDiamondCommute`
   → success (serialize; other agents share the lock).
3. `python3 spec/check_port.py --force FLTForHuman/ModularCurve/HeckeDiamondCommute.lean` → both
   headlines `ok`, **0 mismatch / 0 missing**.
4. `#print axioms` on both → `[propext, Classical.choice, Quot.sound]`.
5. Exactly **four** `spec-pin:` lines: the two `Thm_` wrappers and their two `S_` copies.
6. `cd tools/deps && python3 dedup.py --targets <module-stem> --within --tier shape` (dry run, report only; `move_dead.py` is optional here).
7. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option`, no linter suppression, no other
   file touched, no git, no tree build; every command under 2 minutes.
8. Report: declarations added (public/private), lines, checker line, axioms, build result, and
   every deviation from this brief.
