# SET-AF30 — the centre-cut Siegel set as a cover modulo the centre

**Status: LANDED 2026-11-07** — one order, one new module, four headlines; §4 is the forecast and
§5 records the landing. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF27 left. It is the **thirtieth** `AutomorphicForm`-serving set.

**4 rows / 2,203 silo / 1,737 net new math lines (`port_plan`) / 166 declaration groups**, of which 386
lines are already in the port. All four rows are on the ready block with complete closures.

| row | silo | prem | what it says |
|---|---|---:|---|
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 0 | for an *ample* centre-cut Siegel set, the finite union of its right translates by a class-representative set covers `GL₂(𝔸_K)` modulo the centre |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 0 | with `u = 0` the same union does not cover — the threshold hypothesis is not vacuous |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 0 | the union has finite `L²` mass against the determinant-window density |
| `exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat` | 905 | 0 | a nonnegative, conjugation-invariant, *flat* archimedean test factor with prescribed support |

## 0. The read

SET-AF27's post-landing read (see [SET-AF27.md](SET-AF27.md) §6): `needed` **781 / 329,875**, ready
**69 / 22,193**, leaves 208 / 54,145, `AutomorphicForm` demand 291 / 129,719, `--selfcheck` PASS.

## 1. Why this cut

These four are the only remaining *coherent* block on the ready shelf whose declarations are all
present: the covering theorem's quantitative core — the cover itself (and its non-vacuity), the finite
mass of the cover, and the smoothing factor the covering argument convolves with. Together they are what
`exists_forall_setLIntegral_…_of_coversModCentre` (SET-AF26's 1,361 row) takes as *hypothesis*
(`CoversModCentre`) and as *input* (the finite mass) — so this set closes the loop on the block AF26
landed: the covering hypothesis becomes a theorem.

The alternatives at this point in the shelf are chains, not blocks: the cusp-constituent cluster is a
94-node / 21,595-silo closure, and the Weyl pair is blocked on FR-0151's two statement-spelling
decisions.

## 2. The price

| figure | value |
|---|---|
| raw `S_` lines | 2,203 |
| distinct declaration groups | 166 |
| already in the port (vetted) | 386 |
| **net new math lines** | **1,737** |

No definition gate (`gate_scan` over `Def_AutomorphicForm_SiegelCovering`,
`Def_AutomorphicForm_FactorizableTestFn`, `Def_NumberField_AdelicHaar`: 0 missing). `twin_scan`: `new`
four times.

## 3. Home

**One new module, `Adelic/Siegel/CentreCutCover.lean`**, above `Siegel/Covering.lean` (the
`CoversModCentre` predicate), `WindowedSiegel/CentreCutSet.lean` and `CentreCutSiegelSetAmple.lean` (the
set and its ampleness inequalities), `ProductionPinsGeneral.lean` (`classRepSiegelSet`) and
`FactorizableTestFnArchSmoothLeft.lean` (`IsArchTestFactor`). It is the covering theorem's consumer
module, cascade-free.

## 4. Forecast

*(relative to SET-AF27's read; AF28/AF29 shift the absolute figures, not the deltas)*

| figure | before | after |
|---|---|---|
| `needed [F terminal]` | 781 / 329,875 | **777 / 327,672** |
| `needed [literal]` | 793 / 333,340 | **789 / 331,137** |
| frontier F | 1,635 / 797,501 | **1,639 / 799,704** |
| ready block | 69 / 22,193 | **65 / 19,990** (4 rows out; 0 in) |
| leaves block | 208 / 54,145 | **208 / 54,145** |
| `AutomorphicForm` demand | 291 / 129,719 | **287 / 127,516** |
| rows readied | — | see review |

## 5. The landing (2026-11-07), and the surface gate

`Adelic/Siegel/CentreCutCover.lean` — **1,961 lines**, four headlines plus the pin's helpers, one order,
one dispatch.

| gate | as dispatched | **after the surface gate** |
|---|---|---|
| `check_port --force` | 5 ok / 0 / 0 | **143 ok / 0 mismatch / 0 missing / 0 own** |
| build (single module, flock) | 29 s | 35 s |
| axioms (4 headlines) | clean | `[propext, Classical.choice, Quot.sound]` each |
| `dedup --within` | 0 clusters | 0 clusters / 0 removable |
| `move_dead` | **4 declarations / 18 lines** dead, needing `Ent` | **0 / 0** |
| consumer `spec/AutomorphicFormSetAF30Consumer.lean` | 0 errors | **0 errors / 0 warnings** |

**The surface gate was needed and it paid 137 declarations.** The worker landed the 128 helpers
`private`, citing `Siegel/SlabCovering.lean`'s private-prelude precedent — but in *this* set the pin
states them publicly (`grep` over the four `S_` files: 103 / 20 / 17 public and 0 private in the first
three, 1 public + 19 private in the fourth). One experiment — strip `private`, elaborate, re-run the
checker — gave **142 ok, 1 mismatch, 0 missing**, so the promoted statements are pin-faithful and the
module's checked surface went from 5 to 142 declarations. The one `MISMATCH` that appeared was the worker's reported re-spelling
(`integralFiniteAdeles` → `AdelicLevel.integralFiniteAdeles`), forced by the port opening both
`AdelicLevel` and `AdelicHaar/PlaceMeasure`, which define the name. It was **fixed rather than
privatised**: `NumberField.AdelicBox` was dropped from the header's `open` line (the module uses
nothing from it), so the pin's bare `integralFiniteAdeles` resolves and the statement reads `ok` — the
surface is **143 ok with nothing private** (`grep -c private` = 0). The promotion also emptied
`move_dead`'s 4-declaration / 18-line finding: those declarations were "dead" only while private.

The surface accounting is now complete: 4 headlines + `BumpAux` 104 + `Ws1.Cover` 19 + `Ws23.V2E` 16.
Two pin declarations are deliberately *absent* rather than private: `BumpAux.properSpace_completion'`
(905:755, already landed as `WindowedSiegel.properSpace_completion`) and the `not_coversModCentre…`
engine (already landed **public** at `Cusp/CentreCutEngine.lean:417-749`, from the sibling `S_` file
where the pin states them publicly — the reverse of the pin's visibility for the `of_eq_zero` file, and
left as landed).

**Composition findings.** The `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` row (346) is a
**one-line proof** — `exact CentreCutEngine.not_coversModCentre_of_u_eq_zero (K := F) T` — because its
whole engine is already public in the port (`Cusp/CentreCutEngine.lean:417-749`, ported from the
byte-identical block of a sibling `S_` file). That is this column's cheapest row to date.
`exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat` (905) is the opposite:
genuinely new mathematics (the `BumpAux` construction — `Real.smoothTransition`, the Hilbert-Schmidt
distance to the identity, the `1/16` threshold forcing `U = {det ≠ 0}`, the determinant weight and the
flatness identity), sharing with `FactorizableTestFnArchSmooth*` only the predicate it concludes and
`dedup --within` finding nothing. And the whole module fits the default 200,000-heartbeat budget where
the pin needed 800,000 / 1,600,000.

Deviations (bodies only; 142 statements checker-verified): the pin's `letI glBorel`/`haveI IsHaarMeasure`
blocks dropped in favour of the module's `attribute [local instance]` lines; v4.34's `MemLp` = `eLpNorm < ∞`
so the `⟨hφm.restrict, ?_⟩` pairs became explicit `show`s; `archCentralUnit`'s unfolded Pi type forces
one `show` respelling (pin :129-139); `properSpace_completion'` and `archUnitIdele` reuse ported
declarations rather than re-transcribing them; five deprecations answered; four new imports, reported.

## 6. What this set does not do

- **`exists_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre`** and its
  siblings (786, 1,231, 1,863) are the *boundedness* counterpart of this cover — the next block up, and
  the one whose gateway is this set's cover theorem.
- The cusp-constituent cluster and the Weyl pair stay open as above.
