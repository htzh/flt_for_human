# SET-AF31 — the determinant-window cover and the archimedean unit's norm bound

**Status: LANDED 2026-11-07** — one order, one new module, two headlines; §4 is the forecast and
§5 records the landing. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
AF28/AF29 left (AF30 in flight). It is the **thirty-first** `AutomorphicForm`-serving set, and it is
cut on the return column, not on size.

**2 rows / 1,007 silo / 746 net new math lines (`port_plan`) / 53 declaration groups**, of which 158
lines are already in the port.

| row (`AutomorphicForm.` dropped) | silo | prem | block | what it says |
|---|---|---:|---|---|
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 0 | leaf | the centre-cut Siegel cover transfers from the window `[d₁, d₂]` to `[e₁, e₂]` (`e₁ ≤ e₂`, `0 < e₂`) |
| `norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre` | 871 | 1 | *off-shelf* | on a square-integrable automorphic function under such a cover, the archimedean central unit is a **strict contraction** (`‖·‖ < 1`) |

## 0. The read

After AF28 and AF29 landed (and with AF30's four `spec-pin`-wired scaffold declarations counted, per
FR-0114):

| figure | value |
|---|---|
| `needed [F terminal]` | **771 nodes / 323,794 lines** |
| `needed [literal]` | 783 / 327,259 |
| frontier F | 1,645 / 803,582 |
| ready block | **64 / 17,622** — 36 `AutomorphicForm` rows / 11,483 |
| leaves block | 205 / 52,847 |
| `AutomorphicForm` demand | 281 / 123,638 |

The read decomposes exactly: AF28 −3 nodes / −1,535 lines, AF29 −3 / −2,343, AF30's scaffold −4 /
−2,203 — ten nodes and 6,081 lines off SET-AF27's 781 / 329,875, which is what the shelf now shows.

## 1. Why this cut — the return column's last leader

`build/af-return.py` on the fresh read:

| row | silo | readies | ratio |
|---|---:|---:|---:|
| **`coversModCentre_iUnion_centreCutSiegelSet_of_detWindow`** | **136** | **871** | **6.4** |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 552 | 1.0 |
| `integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn` | 635 | 210 | 0.3 |

So this set is the shelf's own instruction: the 136-line cover **readies** the 871-line contraction, and
the pair is one subject — the determinant-window cover the `L²` estimates are stated against, and the
strict contraction that makes them converge. It is a gate-and-door cut in the SET-AF23/AF25 sense, and
it is the natural continuation of AF30 (in flight): AF30 lands the ample cover, this one lands the
window form of it that the norm bound consumes.

It is **below the recipe's 1,100–1,400-line band** and the brief says so (SET-AF10's precedent): 746 net
lines, justified by the return ratio and the pairing. The alternative was the isotypic/arch-type block
(2,171 silo / 1,598 net) — a bigger but slower-payoff cut, and it is named for the next pass (§5).

## 2. The price

| figure | value |
|---|---|
| raw `S_` lines | 1,007 |
| declaration lines | 965 |
| — duplicate copies | 61 |
| — boilerplate | 42 |
| distinct declaration groups | 53 |
| already in the port (vetted) | 158 |
| **net new math lines** | **746** |

13 trusted substitutions, 0 suspect. No definition gate (`gate_scan` over
`Def_AutomorphicForm_SiegelCovering` and `_AdelicLsXi`: 0 missing). `twin_scan`: `new` twice.

## 3. Home

**One new module, `Adelic/Siegel/DetWindowCover.lean`**, sibling to AF30's `Siegel/CentreCutCover.lean`
and above `Siegel/Covering.lean`, `WindowedSiegel/CentreCutSet.lean`, `ProductionPinsGeneral.lean`,
`Adelic/LsXi.lean` and SET-AF26's `Adelic/LsXiBound.lean` (the `∫⁻` bound the 871 row consumes).

## 4. Forecast

| figure | before | after |
|---|---|---|
| `needed [F terminal]` | 771 / 323,794 | **769 / 323,048** |
| `needed [literal]` | 783 / 327,259 | **781 / 326,513** |
| frontier F | 1,645 / 803,582 | **1,647 / 804,328** |
| ready block | 64 / 17,622 | **64 / 17,622** (untouched: the 136 row is a leaf, the 871 is off-shelf) |
| leaves block | 205 / 52,847 | **204 / 52,711** (1 leaf out) |
| `AutomorphicForm` demand | 281 / 123,638 | **279 / 122,631** |
| rows readied | — | **0** (the door was taken with the gate) |

## 5. The landing (2026-11-07)

`Adelic/Siegel/DetWindowCover.lean` — **1,058 lines / 58 declarations** (2 headlines + the pin's 51
helpers public + 5 port-local `private`), one order, one dispatch.

| gate | result |
|---|---|
| `check_port --force` | **53 ok / 0 mismatch / 0 missing / 0 own** |
| build (single module, flock) | success, 3,623 jobs, 9.5 s |
| axioms (2 headlines) | `[propext, Classical.choice, Quot.sound]` each |
| `dedup --within` | 58 declarations, **0 clusters / 0 removable** |
| `move_dead` | 0 declarations / 0 lines |
| consumer `spec/AutomorphicFormSetAF31Consumer.lean` | **0 errors / 0 warnings** (154 lines, five composition zones) |

**The surface was faithful from the start** — the brief asked for the pin's helpers public and the
worker delivered 51 of them `ok` at the pin's names, with exactly 5 `private` and all five port-local
(`archDetNorm_centralScalar`, `utAdeleVal_mul_entry_00/01/10/11`) — so this set needed no surface gate.
That is the contrast with AF30, where the same instruction produced a `private` module.

**The gate-and-door return was real but not via SET-AF26.** The 871 row's two `∫⁻` facts are the pin's
own: finiteness is five lines from the row's own `hL2 : MemLp φ 2 (μ.restrict D)`, and non-vanishing is
the pin's 178-line `setLIntegral_enorm_sq_ne_zero` (an *open* subset of the cover of positive Haar
measure, not a mass estimate). So `Adelic/LsXiBound.lean` — which my scaffold imported — is referenced by
no proof term here; I removed it and three other idle imports (`LsXi`, `ProductionPinsGeneral`,
`TateGlobal.Defs`) after verifying the build, leaving five specific imports. Lesson: a scaffold's import
block is a guess, and the order should say so.

**A dedup finding to carry.** The pin's four shared helpers (`archDetNorm_mul`, `centralScalar_mul_comm`,
`exists_norm_eq`, `archDetNorm_centralScalar_mul'`) existed in the port **only as private copies** — in
`Siegel/SlabCovering.lean`, `Siegel/CentreCutCover.lean`, `Adelic/LsXiBound.lean` and
`Adelic/PeterssonSlabPairing.lean` — so the worker declared them at the pin's names rather than reusing
a private one (FR-0115's shape, five modules now). A promotion of those four out of `SlabCovering.lean`
would be the next dedup pass's first item.

Deviations (bodies only; 53 statements checker-verified): the pin's `utAdeleVal_mul` entry computation
no longer closes by `rfl` at v4.34 (the adele ring is a semireducible `def`), so it is four private
pair-form lemmas closed by `exact` at default transparency; `if_pos`/`if_neg`, `Set.mem_setOf_eq`,
`mul_le_one₀` deprecations answered; `haveI`/`letI` → `have`/`let`; one new import
(`Cusp/CentreCutEngine`, for the pin's `u = 0` case, whose engine is already public there).

## 6. What this set does not do

- **The isotypic/arch-type block** — `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` (1,043),
  `exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates` (390),
  `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` (242, leverage 2/27),
  `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` (214),
  `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` (282): **2,171 silo / 1,598 net /
  449 already in the port**, all ready. Priced and named — the next set.
- **`exists_sum_prod_mul_of_rightTranslatesSpanFinite`** (576, readies 552) — the span-of-translates
  block, the return column's runner-up.
- The Weyl intertwining pair stays blocked on FR-0151's two statement-spelling decisions; the
  cusp-constituent cluster remains a 94-node / 21,595-silo chain head.
