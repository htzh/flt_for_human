# SET MS-3 — the j-order at τ, the coset translate, and `qExpansionDiffAlong`

**Status: landed (2026-10-28), third order of wave 1.** Ready shelf 1
([TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md)) §0.4 **U9 + U10 + U11**, §2, §3, §4; brief
[WORKORDER-MS3-jorder-coset-diffqexp.md](WORKORDER-MS3-jorder-coset-diffqexp.md). Three rows, three
insertions, no new module, no manager lane.

| row | story | silo | host | checker | lines added |
|---|---|---:|---|---:|---:|
| `meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two` | U9 | 611 | `TateSlots/Invariants.lean` | 91 → **92** | +614 |
| `qExpansion_cosetTranslate_eq_cosetSubst` | U10 | 144 | `ModularPolynomialCoset.lean` | 16 → **17** | +149 |
| `qExpansionDiffAlong_val_eq_diffQExp` | U11 | 62 | `Period/QExpansionDiff.lean` | 3 → **4** | +42 |

| figure | priced | measured |
|---|---:|---:|
| rows / silo | 3 / 817 | 3 / 817 |
| net new math lines | ≈734 | **734** (the three hosts' declaration lines, in-port 0) |
| declarations | 63 + 4 + 6 pin | **3 public + 69 private** (U9 1+63, U10 1+4, U11 1+2) |
| migrations | none | none |

## 0. What landed

- **U9** — the whole pin `JMultiplicity` engine (63 declarations: `jf`, the `E₄`/`E₆`/`Δ` slash
  calculus, `natCard_stabilizer_I`/`_smul`/`_eq_two`, `orbit_trichotomy`, the level-14 witnesses
  `g14`/`e14` and `finrank_fourteen`, the order comparison `deriv_jf_eq` → `order_deriv_add_one` →
  `case_E₄_eq_zero`/`case_E₆_eq_zero`/`case_generic` → `order_and_card` → `main`) is `private` in
  `ModularCurve.JMultiplicity`; the public headline is the pin's own one-line wrapper over `main`.
  That is the pin's `main`/`solution` shape and it is what keeps the checker at exactly +1.
- **U10** — `cosetPt` (+`coe_cosetPt`, `cosetPt_im`) and `hasSum_laurent` `private` in
  `ModularCurve.CosetTranslate`; the public 4-clause conjunction verbatim (both `ℍ` binders and the
  `τ'` name kept, the bare `qExpansion` spelling of the wrapper).
- **U11** — the headline plus two private helpers (`qEuler_eq_thetaL`,
  `isQExpansionDiffAlong_restrictScalars`); the pin's two private `…Bar` specialisations are **not**
  transcribed (no consumer; the port's `diffQExpBar` already carries that content), so 3 declarations
  instead of the pin's 6.

Each host got its two `spec-pin:` lines; U10 and U11 each got one new import (the two named in the
note §3), both acyclic.

## 1. Gates, as measured

| gate | result |
|---|---|
| `check_port --force` | **92 / 17 / 4 ok**, each `0 mismatch / 0 missing / 0 own` |
| `#print axioms` | all three `[propext, Classical.choice, Quot.sound]` |
| builds (workspace lock) | Invariants 4,109 jobs; Coset 3,648; QExpansionDiff 4,029 — all `exit=0` |
| edit loop (200k cap) | silent, zero warnings, all three |
| `dedup.py --within --tier shape` | Coset **0**, DiffQExp **0**, Invariants **1 cluster / 14 lines** (the pin's own `main`↔`solution` statement pair — the deliberate wrapper-over-engine shape, kept and recorded here) |
| `move_dead.py --dry-run` | one false positive, see §2 |

## 2. The one tool defect this order hit (FR-0073)

`move_dead.py` reported `Δ_smul` (6 lines) as dead in `Invariants.lean`; it is cited at lines 980 and
1244. The tokeniser's identifier class drops non-ASCII names, so every `Δ`/`Γ`/`ζ`-named declaration
reads as absent from the bodies that use it. Recorded as FR-0073; nothing was moved.

## 3. Deviations from the brief

1. **U9 did need imports** — the brief said "no new import" on the strength of the shelf's needmods
   scan, and that was wrong: the host's *closure* has the port's `TateSlots`/`X1` API but not
   mathlib's derivative and analytic-order modules. Added, all mathlib leaves, no cycle:
   `Mathlib.Analysis.Analytic.Order` (`analyticOrderAt_deriv_add_one`,
   `analyticOrderAt_ne_top_of_isPreconnected`, `analyticOrderAt_sub_eq_one_of_deriv_ne_zero`),
   `Mathlib.NumberTheory.ModularForms.Derivative` (`D = normalizedDerivOfComplex`),
   `Mathlib.Analysis.Real.Pi.Bounds` (`Real.pi_gt_three`). The lesson for the next brief: the
   needmods scan covers *port* modules, not the mathlib surface a proof adds.
2. U10's engine is `private` although the pin's `CosetTranslateAux` is public in its `S_` namespace
   (required for 16 → 17); its `@[scoped simp]` attribute is dropped because no scope is opened and
   the proofs cite it by name.
3. mathlib v4.34.0 adaptations: `analyticOrderAt_ne_top_of_isPreconnected` →
   `AnalyticOnNhd.…`; `ENat.coe_inj` → `ENat.natCast_inj`; `Set.mem_setOf_eq` →
   `Set.mem_ofPred_eq`; two now-redundant `change` lines dropped in `denom_TinvS_ρ`.
4. U11's headline was first written inside an aux namespace and renamed to the pin's root-level
   `ModularCurve.` name.
5. Build logistics: a build launched from the repo root failed with
   `error: Read-only file system (os error 30)` — `lake` needs the `lean/` cwd, and the lock must be
   the workspace's (FR-0072).

## 4. What these rows unlock

- U9's 611 opens the ramification block: `ComplexPlaceDictionaryOf.two_mul_ramification_eq_card_stabilizer`
  (1,115), `…arithmeticGalois…`-sibling (1,112), `LevelN.exists_place_ord_jGen_le_two_three_level`
  (**303 — ready now**, see the shelf re-read), `…_eq_three_two_and_stabilizer_subset_zpowers` (750).
- U10's 144 opens the slot dictionary: `exists_algHom_qExpFunctionFieldC_gammaH_eq_slot_and_diamondPullbackModL_eq_qTwist`
  (1,181), `…_cuspZero_apply_eq_and_apply_div_pow_eq` (929), `exists_algHom_slot_mul_qExpansion_slash_eq`
  (745), and `ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex`
  (**347 — ready now**).
- U11's 62 opens the Frobenius-difference/cotangent block: `le_span_setOf_logarithmic_of_frobPushDiffModL_surjOn`
  (962), `…_of_forall_mem_regularDifferentials_…` (866), `exists_coeffMap_qExpansionDiffAlong_…` (587).
- The consumer zone ([spec/ModularCurveReady1Consumer.lean](../../spec/ModularCurveReady1Consumer.lean)
  zone C) consumes the two small ones in the direction their consumers need: `diffQExp` from
  `qExpansionDiffAlong` (the `Period` rows speak the former, the algebraic engine the latter), and
  the trivial coset translate `(a, b, d) = (1, 0, 1)`, which fixes the level-1 q-expansion.
