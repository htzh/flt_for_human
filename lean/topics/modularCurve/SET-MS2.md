# SET MS-2 — the Hecke–diamond laws on `J₁` and `J_H`

**Status: landed (2026-10-28), second order of wave 1.** Ready shelf 1
([TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md)) §0.4 **U7**, §2, §3, §4; brief
[WORKORDER-MS2-diamond-laws.md](WORKORDER-MS2-diamond-laws.md). Two rows, one new module, no manager
lane.

| figure | priced | measured |
|---|---:|---:|
| rows | 2 | 2 |
| silo | 438 (410 + 28) | 438 |
| net new math lines | ≈318 | **318** (declaration lines 396 − in-port 78) |
| module | **new** `ModularCurve/HeckeDiamondCommute.lean` | 468 lines, 23 declarations |
| declarations | 33 pin (410) + 1 pin (28) | **2 public + 21 private** (33 − 11 reused, + 1 headline) |
| definition gate | none | none |

## 0. What landed

`ModularCurve/HeckeDiamondCommute.lean` — the diamond sibling of `ModularCurve/HeckeCommuteBar.lean`,
top level:

- `ModularCurve.diamondHBar_mul` (410 pin lines), statement verbatim, proved from the pin's
  `XHDiaMul` five-section engine (`Laurent`, `Group`, `Forms`, `Ratios`, `Diamond`), with the
  `AlgEquiv` law `diamondAutHBar_mul` proved **before** the pointwise headline (the pin's order).
- `ModularCurve.heckeDiamondCommuteBar` (28 pin lines): pure assembly — four `Sum` cases over
  `heckeDiamondGenBar` from `heckeOperatorOneBar_comm`, `heckeOperatorOneBar_comm_diamondOneBar`
  (with `.symm` in the swapped case) and `diamondOneBar_comm`. Nothing was re-proved.

The engine is `private`, in the pin's file-local root namespace `XHDiaMul` (kept, not folded into
`ModularCurve`). Header carries the four `spec-pin:` lines (two wrappers, two `S_` copies) and the
private/public split.

## 1. Gates, as measured

| gate | result |
|---|---|
| `check_port --force` | **2 ok / 0 mismatch / 0 missing / 0 own** |
| `#print axioms` | both headlines `[propext, Classical.choice, Quot.sound]` |
| module build | `Build completed successfully (4505 jobs)`, module's own compile 7.6 s, `EXIT:0` |
| edit loop (200k cap) | silent, zero warnings |
| `dedup.py --within --tier shape` (= `--cross`) | **0 duplicate clusters** |
| `set_option` | only the project-universal `autoImplicit false` |

## 2. The reuse audit — 11 of the pin's 33 declarations were imported, not restated

The whole pin `Laurent` section is already in the port, and this module's reuse is the reason its
468 lines cover 438 silo:

| pin declaration | port home |
|---|---|
| `coeffMap_injective`, `coeffEmb_injective` | `Defs/Laurent.lean` (the general forms) |
| `ofPowerSeries_coeff_negSucc`, `coeffMap_intSeriesC`, `intSeriesC_C`, `intSeriesC_eq_of_isIntegralQExp`, `coeGL_mul`, `entry_inv_mul` | `X1/DiamondCorrespondence.lean` |
| `coeffMap_ofPowerSeries` | `Frobenius/Defs.lean` |
| `intSeriesC_eq_zero_iff` | `JqIntegralRatios.lean` |
| `intSeriesC_add` | `X1/CoeffMap.lean` |

Three of those (`intSeriesC_add`, `intSeriesC_C`, `coeffEmb_injective`) are **dead in the pin too**
(their only occurrence is the declaration) — the pin's `p2m_export` surface, not its proof. A future
`dedup.py --api` pass can drop them from the port's public surface if nothing else uses them.

## 3. Deviations from the brief

1. `algEquiv_ext_of_ratios`: statements are the pin's, but its second (`adjoin ℚ̄`) induction carries
   the subtype membership through a local `hbar : w ∈ laurentBaseChange … → w ∈ xHFunctionFieldBar …`
   coercion. Reason (recorded at the site): the pin's bare `⟨x, hx⟩` subtype elements are well typed
   only at `.all` transparency (the pin's lakefile), while v4.34 `rw` checks at `implicit`, where
   `xHFunctionFieldBar` does not unfold to `adjoin`. `hbar hx` is the same proof — no statement
   change; the ℚ-level induction is the pin's text verbatim.
2. Two port-spelling adaptations: `FunLike.coe_zero`/`coe_sub` for the pin's
   `ModularForm.coe_zero`/`coe_sub`; `change DiamondCorrespondence.QQ ⇑g ≠ 0` in
   `ofPowerSeries_qexp_ne_zero` (the ported `intSeriesC_eq_of_isIntegralQExp` is stated with the `QQ`
   abbrev).
3. `exists_gamma0` needed no adaptation: the pin's `rfl` survives because `CohCarrier.gamma0Units`'s
   `inv` field is the upper-left entry (checked, not assumed).
4. Engine `private` by design (the wire is the two headlines); every engine statement is the pin's,
   so a later promotion needs only dropping `private`.

## 4. The build-lock friction this order found (FR-0072)

The playbook's `flock /tmp/lean-build.lock` serializes nothing under the harness (`/tmp` is
per-call), so this order's first build replayed and rebuilt its whole 4,505-job dependency closure
because two other agents were writing in the same tree. Recorded as FR-0072; the wave-2 briefs use
the workspace lock (`flock tmp/lean-build.lock`) and repo-local build logs.

## 5. What this row unlocks

- `heckeDiamondCommuteBar` (28 silo, 29 project consumers) is the **`hcomm` hypothesis** of the
  unstatable Tate-module row `rep_tateModule_jOne_comm` and of the whole `…_tateModule_jOne_…` block
  (1,586 / 1,468 / 1,327 / 1,283 / 1,214 …). It is now a theorem, so that block no longer carries a
  hypothesis.
- `diamondHBar_mul` (12 project consumers) feeds the `jH` Tate block
  (`exists_decompositionCharacters_…_of_ordinary`, 1,457).
- The consumer zone ([spec/ModularCurveReady1Consumer.lean](../../spec/ModularCurveReady1Consumer.lean)
  zone B) consumes both: the law as a `Function.comp` statement and iterated over a triple, and the
  `Prop` as the hypothesis of `heckeEvalOneBar`, giving a ring map `HeckeAlgOne →+* End (J₁(M))`
  whose images commute.
